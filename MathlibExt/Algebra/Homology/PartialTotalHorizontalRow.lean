/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalHorizontal
public import MathlibExt.Algebra.Homology.PartialTotalSuccessor

/-!
# Degree-lowering maps between adjacent signed rows

Let `B` be a first-quadrant bicomplex in a preadditive category with finite coproducts. The
horizontal component between rows `m + 1` and `m` gives a map from `(B.totalRow (m + 1)).X (n
+ 1)` to `(B.totalRow m).X n`.

Include the new row in its partial-total stage, apply the total differential, retract to the
preceding stage, and project onto row `m`. At `n = m + q`, this composite is the horizontal
bicomplex differential at vertical degree `q`, expressed through the two row-coordinate
isomorphisms. It vanishes when `n < m`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- Horizontal row component from the partial-total splitting.

The map from `(B.totalRow (m + 1)).X (n + 1)` to `(B.totalRow m).X n` is the new-row section
followed by the differential of `B.partialTotal (m + 1)`, the retraction to `B.partialTotal
m`, and the row-`m` quotient projection. -/
noncomputable def partialTotalHorizontalRowF (m n : ℕ) :
    (B.totalRow (m + 1)).X (n + 1) ⟶ (B.totalRow m).X n :=
  B.partialTotalRowQuotientSectionF (m + 1) (n + 1) ≫
    (B.partialTotal (m + 1)).d (n + 1) n ≫
    B.partialTotalSuccRetractionF m n ≫
    B.partialTotalRowQuotientF m n

set_option backward.isDefEq.respectTransparency false in
/-- Horizontal row component in bicomplex coordinates.

At total degree `m + q`, `B.partialTotalHorizontalRowF m (m + q)` is the source row-coordinate
map, followed by `(B.d (m + 1) m).f q`, followed by the inverse target row-coordinate map. The
source row has total degree `m + q + 1`, and the target has degree `m + q`. -/
theorem partialTotalHorizontalRowF_eq (m q : ℕ) :
    B.partialTotalHorizontalRowF m (m + q) =
      (B.totalRowXIso (m + 1) q (m + q + 1) (by omega)).hom ≫
        (B.d (m + 1) m).f q ≫
        (B.totalRowXIso m q (m + q) rfl).inv := by
  let K := B.firstStupidTrunc (m + 1)
  have h₁ :
      B.partialTotalRowQuotientSectionF (m + 1) (m + q + 1) ≫
          K.D₁ (ComplexShape.down ℕ) (m + q + 1) (m + q) ≫
          B.partialTotalSuccRetractionF m (m + q) ≫
          B.partialTotalRowQuotientF m (m + q) =
        (B.totalRowXIso (m + 1) q (m + q + 1) (by omega)).hom ≫
          (B.d (m + 1) m).f q ≫
          (B.totalRowXIso m q (m + q) rfl).inv := by
    rw [B.partialTotalRowQuotientSectionF_eq
      (m + 1) q (m + q + 1) (by omega)]
    have hι₁ := HomologicalComplex₂.ι_D₁ K (ComplexShape.down ℕ)
      (m + q + 1) (m + q) (m + 1) q (by
        change (m + 1) + q = m + q + 1
        omega)
    slice_lhs 3 4 => rw [hι₁]
    rw [d₁_succ_eq_horizontal K m q]
    slice_lhs 4 5 =>
      rw [B.ιTotal_partialTotalSuccRetractionF m
        ⟨m, Nat.lt_succ_self m⟩ q (m + q) rfl]
    rw [Category.assoc,
      B.ιTotal_partialTotalRowQuotientF m q (m + q) rfl]
    have hcentral :
        (B.partialTotalLastRowIso (m + 1)).inv.f q ≫
          (K.d (m + 1) m).f q ≫
        (B.partialTotalSuccOldRowIso m ⟨m, Nat.lt_succ_self m⟩).inv.f q ≫
          (B.partialTotalLastRowIso m).hom.f q =
          (B.d (m + 1) m).f q := by
      let iSrc : Fin (m + 2) := ⟨m + 1, by omega⟩
      have hiSrc :
          (ComplexShape.embeddingDownNatInitialSegment (m + 1)).f iSrc = m + 1 := rfl
      let eSrc := B.stupidTruncXIso
        (ComplexShape.embeddingDownNatInitialSegment (m + 1))
        (i := iSrc) hiSrc
      let iMid : Fin (m + 2) := ⟨m, by omega⟩
      have hiMid :
          (ComplexShape.embeddingDownNatInitialSegment (m + 1)).f iMid = m := rfl
      let eMid := B.stupidTruncXIso
        (ComplexShape.embeddingDownNatInitialSegment (m + 1))
        (i := iMid) hiMid
      have hSrc := congrArg (fun f ↦ f.f q) eSrc.inv_hom_id
      have hMid := congrArg (fun f ↦ f.f q) eMid.inv_hom_id
      simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hSrc hMid
      dsimp only [K, firstStupidTrunc, partialTotalLastRowIso,
        partialTotalSuccOldRowIso, partialTotalRowIsoAt]
      rw [HomologicalComplex.stupidTrunc_d_eq B
        (ComplexShape.embeddingDownNatInitialSegment (m + 1))
        (i := iSrc) (j := iMid)
        (i' := m + 1) (j' := m) hiSrc hiMid]
      simp only [Iso.trans_inv, Iso.symm_inv, HomologicalComplex.comp_f]
      slice_lhs 1 2 => rw [hSrc]
      slice_lhs 3 4 => rw [hMid]
      simp only [Category.id_comp]
      let iTgt : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
      have hiTgt : (ComplexShape.embeddingDownNatInitialSegment m).f iTgt = m := rfl
      let eTgt := B.stupidTruncXIso
        (ComplexShape.embeddingDownNatInitialSegment m)
        (i := iTgt) hiTgt
      have hTgt := congrArg (fun f ↦ f.f q) eTgt.inv_hom_id
      simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hTgt
      have hc := congrArg (fun k ↦ (B.d (m + 1) m).f q ≫ k) hTgt
      simp only [Category.comp_id] at hc
      convert hc using 1
    slice_lhs 2 5 => rw [hcentral]
  have h₂ :
      B.partialTotalRowQuotientSectionF (m + 1) (m + q + 1) ≫
          K.D₂ (ComplexShape.down ℕ) (m + q + 1) (m + q) ≫
          B.partialTotalSuccRetractionF m (m + q) ≫
          B.partialTotalRowQuotientF m (m + q) = 0 := by
    rw [B.partialTotalRowQuotientSectionF_eq
      (m + 1) q (m + q + 1) (by omega)]
    have hι₂ := HomologicalComplex₂.ι_D₂ K (ComplexShape.down ℕ)
      (m + q + 1) (m + q) (m + 1) q (by
        change (m + 1) + q = m + q + 1
        omega)
    slice_lhs 3 4 => rw [hι₂]
    cases q with
    | zero =>
        simp only [Nat.add_zero]
        rw [HomologicalComplex₂.d₂_eq_zero K (ComplexShape.down ℕ)
          (m + 1) 0 m (by simp), zero_comp, zero_comp, comp_zero, comp_zero]
    | succ r =>
        rw [HomologicalComplex₂.d₂_eq K (ComplexShape.down ℕ)
          (m + 1) (show (ComplexShape.down ℕ).Rel (r + 1) r from rfl)
          (m + (r + 1)) (by
            change (m + 1) + r = m + (r + 1)
            omega),
          Linear.units_smul_comp, Category.assoc,
          B.ιTotal_partialTotalSuccRetractionF_eq_zero
            m (m + 1) r (m + (r + 1)) (by omega) (by omega),
          comp_zero, smul_zero, zero_comp, comp_zero, comp_zero]
  dsimp only [partialTotalHorizontalRowF, partialTotal, K]
  rw [HomologicalComplex₂.total_d]
  slice_lhs 1 2 => rw [Preadditive.comp_add]
  rw [Preadditive.add_comp,
    Preadditive.add_comp]
  simp only [Category.assoc]
  rw [h₁, h₂, add_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Horizontal row component after specifying the target degree.

For an equality `m + q = n`, the component `B.partialTotalHorizontalRowF m n` is the
horizontal differential `(B.d (m + 1) m).f q` transported from source row degree `n + 1` to
target row degree `n` through the corresponding row-coordinate isomorphisms. -/
theorem partialTotalHorizontalRowF_eqAt
    (m q n : ℕ) (h : m + q = n) :
    B.partialTotalHorizontalRowF m n =
      (B.totalRowXIso (m + 1) q (n + 1) (by omega)).hom ≫
        (B.d (m + 1) m).f q ≫
        (B.totalRowXIso m q n h).inv := by
  let K := B.firstStupidTrunc (m + 1)
  have h₁ :
      B.partialTotalRowQuotientSectionF (m + 1) (n + 1) ≫
          K.D₁ (ComplexShape.down ℕ) (n + 1) n ≫
          B.partialTotalSuccRetractionF m n ≫
          B.partialTotalRowQuotientF m n =
        (B.totalRowXIso (m + 1) q (n + 1) (by omega)).hom ≫
          (B.d (m + 1) m).f q ≫
          (B.totalRowXIso m q n h).inv := by
    rw [B.partialTotalRowQuotientSectionF_eq
      (m + 1) q (n + 1) (by omega)]
    have hι₁ := HomologicalComplex₂.ι_D₁ K (ComplexShape.down ℕ)
      (n + 1) n (m + 1) q (by
        change (m + 1) + q = n + 1
        omega)
    slice_lhs 3 4 => rw [hι₁]
    have hd₁ :
        K.d₁ (ComplexShape.down ℕ) (m + 1) q n =
          (K.d (m + 1) m).f q ≫
            K.ιTotal (ComplexShape.down ℕ) m q n h := by
      have hε₁ : (ComplexShape.down ℕ).ε₁ (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (m + 1, q) = 1 := rfl
      rw [HomologicalComplex₂.d₁_eq K (ComplexShape.down ℕ)
        (show (ComplexShape.down ℕ).Rel (m + 1) m by rfl)
        q n h, hε₁, one_smul]
    rw [hd₁]
    slice_lhs 4 5 =>
      rw [B.ιTotal_partialTotalSuccRetractionF m
        ⟨m, Nat.lt_succ_self m⟩ q n h]
    rw [Category.assoc,
      B.ιTotal_partialTotalRowQuotientF m q n h]
    have hcentral :
        (B.partialTotalLastRowIso (m + 1)).inv.f q ≫
          (K.d (m + 1) m).f q ≫
        (B.partialTotalSuccOldRowIso m ⟨m, Nat.lt_succ_self m⟩).inv.f q ≫
          (B.partialTotalLastRowIso m).hom.f q =
          (B.d (m + 1) m).f q := by
      let iSrc : Fin (m + 2) := ⟨m + 1, by omega⟩
      have hiSrc :
          (ComplexShape.embeddingDownNatInitialSegment (m + 1)).f iSrc = m + 1 := rfl
      let eSrc := B.stupidTruncXIso
        (ComplexShape.embeddingDownNatInitialSegment (m + 1))
        (i := iSrc) hiSrc
      let iMid : Fin (m + 2) := ⟨m, by omega⟩
      have hiMid :
          (ComplexShape.embeddingDownNatInitialSegment (m + 1)).f iMid = m := rfl
      let eMid := B.stupidTruncXIso
        (ComplexShape.embeddingDownNatInitialSegment (m + 1))
        (i := iMid) hiMid
      have hSrc := congrArg (fun f ↦ f.f q) eSrc.inv_hom_id
      have hMid := congrArg (fun f ↦ f.f q) eMid.inv_hom_id
      simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hSrc hMid
      dsimp only [K, firstStupidTrunc, partialTotalLastRowIso,
        partialTotalSuccOldRowIso, partialTotalRowIsoAt]
      rw [HomologicalComplex.stupidTrunc_d_eq B
        (ComplexShape.embeddingDownNatInitialSegment (m + 1))
        (i := iSrc) (j := iMid)
        (i' := m + 1) (j' := m) hiSrc hiMid]
      simp only [Iso.trans_inv, Iso.symm_inv, HomologicalComplex.comp_f]
      slice_lhs 1 2 => rw [hSrc]
      slice_lhs 3 4 => rw [hMid]
      simp only [Category.id_comp]
      let iTgt : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
      have hiTgt : (ComplexShape.embeddingDownNatInitialSegment m).f iTgt = m := rfl
      let eTgt := B.stupidTruncXIso
        (ComplexShape.embeddingDownNatInitialSegment m)
        (i := iTgt) hiTgt
      have hTgt := congrArg (fun f ↦ f.f q) eTgt.inv_hom_id
      simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hTgt
      have hc := congrArg (fun k ↦ (B.d (m + 1) m).f q ≫ k) hTgt
      simp only [Category.comp_id] at hc
      exact hc
    slice_lhs 2 5 => rw [hcentral]
  have h₂ :
      B.partialTotalRowQuotientSectionF (m + 1) (n + 1) ≫
          K.D₂ (ComplexShape.down ℕ) (n + 1) n ≫
          B.partialTotalSuccRetractionF m n ≫
          B.partialTotalRowQuotientF m n = 0 := by
    rw [B.partialTotalRowQuotientSectionF_eq
      (m + 1) q (n + 1) (by omega)]
    have hι₂ := HomologicalComplex₂.ι_D₂ K (ComplexShape.down ℕ)
      (n + 1) n (m + 1) q (by
        change (m + 1) + q = n + 1
        omega)
    slice_lhs 3 4 => rw [hι₂]
    cases q with
    | zero =>
        rw [HomologicalComplex₂.d₂_eq_zero K (ComplexShape.down ℕ)
          (m + 1) 0 n (by simp), zero_comp, zero_comp, comp_zero, comp_zero]
    | succ r =>
        rw [HomologicalComplex₂.d₂_eq K (ComplexShape.down ℕ)
          (m + 1) (show (ComplexShape.down ℕ).Rel (r + 1) r from rfl)
          n (by
            change (m + 1) + r = n
            omega),
          Linear.units_smul_comp, Category.assoc,
          B.ιTotal_partialTotalSuccRetractionF_eq_zero
            m (m + 1) r n (by omega) (by omega),
          comp_zero, smul_zero, zero_comp, comp_zero, comp_zero]
  dsimp only [partialTotalHorizontalRowF, partialTotal, K]
  rw [HomologicalComplex₂.total_d]
  slice_lhs 1 2 => rw [Preadditive.comp_add]
  rw [Preadditive.add_comp,
    Preadditive.add_comp]
  simp only [Category.assoc]
  rw [h₁, h₂, add_zero]

/-- Horizontal row component vanishes below target-row support.

If `n < m`, then `B.partialTotalHorizontalRowF m n = 0`. The target term `(B.totalRow m).X n`
is zero because row `m` starts in total degree `m`. -/
theorem partialTotalHorizontalRowF_eq_zero_of_lt (m n : ℕ) (h : n < m) :
    B.partialTotalHorizontalRowF m n = 0 :=
  (B.totalRow_isZero_X m n h).eq_of_tgt _ _

end HomologicalComplex₂

end
