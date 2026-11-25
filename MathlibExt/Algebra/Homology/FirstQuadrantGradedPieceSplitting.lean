/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPieceCokernelMap

/-!
# Splitting data for consecutive horizontal filtration stages

For an ℕ-indexed downward bicomplex in a preadditive category with a zero
object and finite coproducts, the inclusion from horizontal stage `p` to
stage `p+1` has a retraction in each total degree. In total degree `p+1+q`,
the top-column projection has its canonical section.

The lower-coordinate and top-coordinate projectors sum to the identity.
Consequently, the consecutive-stage short complex is split and exact, and
the top-column projection is a cokernel of the preceding-stage inclusion.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- Retraction from filtration stage `p+1` onto stage `p` in a fixed total
degree. -/
noncomputable def horizontalFilteredSuccRetraction (p n : ℕ) :
    horizontalFilteredTotalObj K (p + 1) n ⟶
      horizontalFilteredTotalObj K p n :=
  horizontalFilteredTotalToTotal K (p + 1) n ≫
    totalToHorizontalFilteredTotal K p n

omit [HasZeroObject C] in
@[reassoc (attr := simp)]
theorem horizontalFilteredTotalMap_succ_retraction (p n : ℕ) :
    horizontalFilteredTotalMap K (Nat.le_succ p) n ≫
      horizontalFilteredSuccRetraction K p n = 𝟙 _ := by
  unfold horizontalFilteredSuccRetraction
  rw [horizontalFilteredTotalMap_toTotal_assoc]
  exact horizontalFilteredTotalToTotal_comp_retraction K p n

/-- Section of the top-column projection in total degree `p+1+q`. -/
noncomputable def horizontalFilteredTopSection (p q : ℕ) :
    (K.X (p + 1)).X q ⟶
      horizontalFilteredTotalObj K (p + 1) (p + 1 + q) :=
  horizontalFilteredTotalι K (p + 1) (p + 1 + q)
    (horizontalFilteredTopIndex (p + 1) q)

omit [HasZeroObject C] in
@[reassoc (attr := simp)]
theorem horizontalFilteredTopSection_projection (p q : ℕ) :
    horizontalFilteredTopSection K p q ≫
      horizontalFilteredTopProjection K (p + 1) q = 𝟙 _ :=
  horizontalFilteredTopι_topProjection K (p + 1) q

/-- Consecutive filtration stage followed by projection to the new column. -/
noncomputable def horizontalFilteredSuccShortComplex (p q : ℕ) :
    ShortComplex C :=
  ShortComplex.mk
    (horizontalFilteredTotalMap K (Nat.le_succ p) (p + 1 + q))
    (horizontalFilteredTopProjection K (p + 1) q)
    (horizontalFilteredTotalMap_succ_topProjection K p q)

omit [HasZeroObject C] in
@[reassoc]
theorem horizontalFilteredTotalι_succRetraction
    (p n : ℕ) (idx : DownNatHorizontalFilteredFiber n (p + 1)) :
    horizontalFilteredTotalι K (p + 1) n idx ≫
        horizontalFilteredSuccRetraction K p n =
      if h : idx.val.val.1 ≤ p then
        horizontalFilteredTotalι K p n ⟨idx.1, h⟩
      else 0 := by
  unfold horizontalFilteredSuccRetraction
  have hto := horizontalFilteredTotalι_toTotal K (p + 1) n idx
  calc
    _ = (horizontalFilteredTotalι K (p + 1) n idx ≫
          horizontalFilteredTotalToTotal K (p + 1) n) ≫
        totalToHorizontalFilteredTotal K p n :=
      (Category.assoc _ _ _).symm
    _ = K.ιTotal (ComplexShape.down ℕ) idx.val.val.1 idx.val.val.2 n
          idx.val.property ≫ totalToHorizontalFilteredTotal K p n :=
      congrArg
        (fun z : (K.X idx.val.val.1).X idx.val.val.2 ⟶
            (K.total (ComplexShape.down ℕ)).X n =>
          z ≫ totalToHorizontalFilteredTotal K p n) hto
    _ = _ := ιTotal_totalToHorizontalFilteredTotal K p n _ _ _

omit [HasZeroObject C] in
/-- The lower-coordinate projector plus the top-coordinate projector is the
identity on filtration stage `p+1`. -/
theorem horizontalFilteredSucc_complementary_id (p q : ℕ) :
    horizontalFilteredSuccRetraction K p (p + 1 + q) ≫
          horizontalFilteredTotalMap K (Nat.le_succ p) (p + 1 + q) +
        horizontalFilteredTopProjection K (p + 1) q ≫
          horizontalFilteredTopSection K p q =
      𝟙 _ := by
  let F : DownNatHorizontalFilteredFiber (p + 1 + q) (p + 1) → C :=
    fun idx => (K.X idx.val.val.1).X idx.val.val.2
  change horizontalFilteredSuccRetraction K p (p + 1 + q) ≫
        horizontalFilteredTotalMap K (Nat.le_succ p) (p + 1 + q) +
      horizontalFilteredTopProjection K (p + 1) q ≫
        horizontalFilteredTopSection K p q = 𝟙 (∐ F)
  apply Sigma.hom_ext
  intro idx
  change horizontalFilteredTotalι K (p + 1) (p + 1 + q) idx ≫
        (horizontalFilteredSuccRetraction K p (p + 1 + q) ≫
            horizontalFilteredTotalMap K (Nat.le_succ p) (p + 1 + q) +
          horizontalFilteredTopProjection K (p + 1) q ≫
            horizontalFilteredTopSection K p q) =
      horizontalFilteredTotalι K (p + 1) (p + 1 + q) idx ≫ 𝟙 _
  simp only [Preadditive.comp_add]
  by_cases ha : idx.val.val.1 ≤ p
  · let idxLow : DownNatHorizontalFilteredFiber (p + 1 + q) p :=
      ⟨idx.1, ha⟩
    have hret := horizontalFilteredTotalι_succRetraction
      K p (p + 1 + q) idx
    rw [dite_eq_left ha] at hret
    have hmap := horizontalFilteredTotalι_map K (Nat.le_succ p)
      (p + 1 + q) idxLow
    have hfirst :
        horizontalFilteredTotalι K (p + 1) (p + 1 + q) idx ≫
            (horizontalFilteredSuccRetraction K p (p + 1 + q) ≫
              horizontalFilteredTotalMap K (Nat.le_succ p) (p + 1 + q)) =
          horizontalFilteredTotalι K (p + 1) (p + 1 + q) idx :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg
          (fun z : (K.X idx.val.val.1).X idx.val.val.2 ⟶
              horizontalFilteredTotalObj K p (p + 1 + q) =>
            z ≫ horizontalFilteredTotalMap K (Nat.le_succ p) (p + 1 + q))
          hret).trans hmap)
    have hproj := horizontalFilteredTotalι_topProjection_of_lt
      K (p + 1) q idx (Nat.lt_succ_of_le ha)
    have hsecond :
        horizontalFilteredTotalι K (p + 1) (p + 1 + q) idx ≫
            (horizontalFilteredTopProjection K (p + 1) q ≫
              horizontalFilteredTopSection K p q) = 0 :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg
          (fun z : (K.X idx.val.val.1).X idx.val.val.2 ⟶ (K.X (p + 1)).X q =>
            z ≫ horizontalFilteredTopSection K p q) hproj).trans
          zero_comp)
    have hsum := congrArg₂ (· + ·) hfirst hsecond
    exact hsum.trans ((add_zero _).trans (Category.comp_id _).symm)
  · obtain ⟨⟨⟨a, b⟩, hab⟩, hap⟩ := idx
    change a ≤ p + 1 at hap
    change ¬a ≤ p at ha
    have ha' : a = p + 1 := by omega
    subst a
    have hb : b = q := by
      change p + 1 + b = p + 1 + q at hab
      omega
    subst b
    let idx' : DownNatHorizontalFilteredFiber (p + 1 + q) (p + 1) :=
      ⟨⟨(p + 1, q), hab⟩, hap⟩
    have hnot : ¬idx'.val.val.1 ≤ p := by simp [idx']
    have hret := horizontalFilteredTotalι_succRetraction
      K p (p + 1 + q) idx'
    rw [dite_eq_right hnot] at hret
    have hfirst :
        horizontalFilteredTotalι K (p + 1) (p + 1 + q) idx' ≫
            (horizontalFilteredSuccRetraction K p (p + 1 + q) ≫
              horizontalFilteredTotalMap K (Nat.le_succ p) (p + 1 + q)) = 0 :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg
          (fun z : (K.X (p + 1)).X q ⟶ horizontalFilteredTotalObj K p (p + 1 + q) =>
            z ≫ horizontalFilteredTotalMap K (Nat.le_succ p) (p + 1 + q))
          hret).trans zero_comp)
    have hidx : idx' = horizontalFilteredTopIndex (p + 1) q := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    cases hidx
    have hproj := horizontalFilteredTopSection_projection K p q
    have hsecond :
        horizontalFilteredTopSection K p q ≫
            (horizontalFilteredTopProjection K (p + 1) q ≫
              horizontalFilteredTopSection K p q) =
          horizontalFilteredTopSection K p q :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg
          (fun z : (K.X (p + 1)).X q ⟶ (K.X (p + 1)).X q =>
            z ≫ horizontalFilteredTopSection K p q) hproj).trans
          (Category.id_comp _))
    have hsum := congrArg₂ (· + ·) hfirst hsecond
    exact hsum.trans ((zero_add _).trans (Category.comp_id _).symm)

/-- The consecutive-stage short complex is split. -/
noncomputable def horizontalFilteredSuccSplitting (p q : ℕ) :
    (horizontalFilteredSuccShortComplex K p q).Splitting := by
  let S : ShortComplex C := horizontalFilteredSuccShortComplex K p q
  let r : S.X₂ ⟶ S.X₁ := horizontalFilteredSuccRetraction K p (p + 1 + q)
  let s : S.X₃ ⟶ S.X₂ := horizontalFilteredTopSection K p q
  have hfr : S.f ≫ r = 𝟙 S.X₁ :=
    horizontalFilteredTotalMap_succ_retraction K p (p + 1 + q)
  have hsg : s ≫ S.g = 𝟙 S.X₃ := horizontalFilteredTopSection_projection K p q
  have hid : r ≫ S.f + S.g ≫ s = 𝟙 S.X₂ := horizontalFilteredSucc_complementary_id K p q
  exact { r := r, s := s, f_r := hfr, s_g := hsg, id := hid }

theorem horizontalFilteredSuccShortComplex_exact (p q : ℕ) :
    (horizontalFilteredSuccShortComplex K p q).Exact :=
  (horizontalFilteredSuccSplitting K p q).exact

/-- The top-column projection is the cokernel of the preceding-stage
inclusion in total degree `p+1+q`. -/
noncomputable def horizontalFilteredTopProjectionIsCokernel (p q : ℕ) :
    IsColimit (CokernelCofork.ofπ
      (horizontalFilteredTopProjection K (p + 1) q)
      (horizontalFilteredTotalMap_succ_topProjection K p q)) :=
  (horizontalFilteredSuccSplitting K p q).gIsCokernel

end HomologicalComplex₂

end
