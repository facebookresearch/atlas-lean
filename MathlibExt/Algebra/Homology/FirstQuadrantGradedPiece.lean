/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPage

/-!
# Horizontal graded-piece ingredients

For a first-quadrant bicomplex, the `p`th horizontal graded piece is the
`p`th vertical column placed in total degree `p+q`.  After chain-to-cochain
reindexing this is the column shifted by `p`; Mathlib's cochain shift supplies
the required constant sign `(-1)^p` on its differential.

This file constructs that shifted column, its canonical degree objects, and
the top-summand projections from finite filtration stages.  It also proves
that the preceding stage is annihilated degreewise.  Assembly into the
cokernel comparison chain map is carried out in the subsequent
`FirstQuadrantGradedPiece*` modules.
-/

@[expose] public section

open CategoryTheory Limits CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The `p`th vertical column, reindexed as a cochain complex and shifted so
that column degree `q` lies in cochain degree `-(p+q)`. -/
noncomputable def horizontalColumnCochain (p : ℕ) :
    CochainComplex C ℤ :=
  (shiftFunctor (CochainComplex C ℤ) (p : ℤ)).obj
    ((K.X p).extend ComplexShape.embeddingDownNat)

/-- The canonical degree identification for the shifted horizontal column. -/
noncomputable def horizontalColumnCochainXIso (p q : ℕ) :
    (horizontalColumnCochain K p).X (-(p : ℤ) - q) ≅
      (K.X p).X q :=
  CochainComplex.shiftFunctorObjXIso
      ((K.X p).extend ComplexShape.embeddingDownNat)
      (p : ℤ) (-(p : ℤ) - q) (-(q : ℤ)) (by omega) ≪≫
    (K.X p).extendXIso ComplexShape.embeddingDownNat (by simp)

omit [HasFiniteCoproducts C] in
/-- The shifted `p`th column is zero in cochain degrees strictly above `-p`. -/
theorem horizontalColumnCochain_isZero_X_of_lt
    (p : ℕ) (i : ℤ) (hi : -(p : ℤ) < i) :
    IsZero ((horizontalColumnCochain K p).X i) := by
  apply IsZero.of_iso
    ((K.X p).isZero_extend_X ComplexShape.embeddingDownNat (i + p)
      (fun q hq => by
        simp only [ComplexShape.embeddingDownNat_f] at hq
        lia))
    (CochainComplex.shiftFunctorObjXIso
      ((K.X p).extend ComplexShape.embeddingDownNat)
      (p : ℤ) i (i + p) rfl)

/-- At every nonnegative upper first-page index, the complete filtration
subobject is the corresponding natural filtration subobject. -/
theorem horizontalCompleteFilteredTotalMonoOver_upper (p : ℕ) :
    horizontalCompleteFilteredTotalMonoOver K
        (horizontalFirstPageUpperIndex p) =
      (horizontalTotalFiltration K).toMonoOver.obj p := by
  unfold horizontalCompleteFilteredTotalMonoOver horizontalFirstPageUpperIndex
  simp only [WithBotTop.rec_coe]
  rw [ite_eq_left (show 0 ≤ (p : ℤ) by omega)]
  congr 2

/-- Identification of a nonnegative complete upper-stage filtration
subobject with its natural-stage presentation. -/
noncomputable def horizontalCompleteFilteredTotalMonoOverUpperIso (p : ℕ) :
    horizontalCompleteFilteredTotalMonoOver K
        (horizontalFirstPageUpperIndex p) ≅
      (horizontalTotalFiltration K).toMonoOver.obj p :=
  eqToIso (horizontalCompleteFilteredTotalMonoOver_upper K p)

/-- The upper-stage subobject identification after forgetting and applying
chain-to-cochain extension. -/
noncomputable def horizontalCompleteFiltrationCochainMonoUpperIso (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) ≅
      (ComplexShape.embeddingDownNat.extendFunctor C).obj
        ((horizontalTotalFiltration K).toMonoOver.obj p).obj.left :=
  (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
    ((MonoOver.forget _ ⋙ Over.forget _).mapIso
      (horizontalCompleteFilteredTotalMonoOverUpperIso K p))

/-- The nonnegative complete-filtration stage `p`, after cochain reindexing,
is the cochain extension of the original finite stage.  The factorization
through the natural filtration subobject makes stage coherence explicit. -/
noncomputable def horizontalCompleteFiltrationCochainUpperIso (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) ≅
      (horizontalFilteredTotalComplex K p).extend
        ComplexShape.embeddingDownNat :=
  horizontalCompleteFiltrationCochainMonoUpperIso K p ≪≫
    (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
      (eqToIso (horizontalTotalFiltration_diagram_obj K p))

/-- In bidegree `(p,q)`, projection of filtration stage `p` onto its top
summand, transported through chain-to-cochain reindexing and the column shift. -/
noncomputable def horizontalColumnProjectionComponent (p q : ℕ) :
    ((horizontalCompleteFiltrationCochainDiagram K).obj
      (horizontalFirstPageUpperIndex p)).X (-(p : ℤ) - q) ⟶
        (horizontalColumnCochain K p).X (-(p : ℤ) - q) :=
  (horizontalCompleteFiltrationCochainUpperIso K p).hom.f (-(p : ℤ) - q) ≫
    ((horizontalFilteredTotalComplex K p).extendXIso
      ComplexShape.embeddingDownNat
      (i := p + q) (i' := -(p : ℤ) - q) (by simp; omega)).hom ≫
    Sigma.π
      (fun pq : DownNatHorizontalFilteredFiber (p + q) p =>
        (K.X pq.val.val.1).X pq.val.val.2)
      ⟨⟨(p, q), by simp⟩, by simp⟩ ≫
    (horizontalColumnCochainXIso K p q).inv

/-- The top-column index in filtration stage `p` and total degree `p+q`. -/
def horizontalFilteredTopIndex (p q : ℕ) :
    DownNatHorizontalFilteredFiber (p + q) p :=
  ⟨⟨(p, q), by simp⟩, by simp⟩

/-- Projection of filtration stage `p` in total degree `p+q` onto its
top-column summand. -/
noncomputable def horizontalFilteredTopProjection (p q : ℕ) :
    horizontalFilteredTotalObj K p (p + q) ⟶ (K.X p).X q :=
  Sigma.π
    (fun pq : DownNatHorizontalFilteredFiber (p + q) p =>
      (K.X pq.val.val.1).X pq.val.val.2)
    (horizontalFilteredTopIndex p q)

omit [HasZeroObject C] in
@[reassoc]
theorem horizontalFilteredTotalι_topProjection
    (p q : ℕ) (pq : DownNatHorizontalFilteredFiber (p + q) p) :
    horizontalFilteredTotalι K p (p + q) pq ≫
        horizontalFilteredTopProjection K p q =
      if h : pq = horizontalFilteredTopIndex p q then
        eqToHom (congrArg
          (fun x : DownNatHorizontalFilteredFiber (p + q) p =>
            (K.X x.val.val.1).X x.val.val.2) h)
      else 0 := by
  exact Sigma.ι_π _ _ _

omit [HasZeroObject C] in
@[reassoc (attr := simp)]
theorem horizontalFilteredTopι_topProjection (p q : ℕ) :
    horizontalFilteredTotalι K p (p + q)
        (horizontalFilteredTopIndex p q) ≫
      horizontalFilteredTopProjection K p q = 𝟙 _ := by
  rw [horizontalFilteredTotalι_topProjection, dite_eq_left rfl]
  rfl

omit [HasZeroObject C] in
@[reassoc (attr := simp)]
theorem horizontalFilteredTotalι_topProjection_of_lt
    (p q : ℕ) (pq : DownNatHorizontalFilteredFiber (p + q) p)
    (h : pq.val.val.1 < p) :
    horizontalFilteredTotalι K p (p + q) pq ≫
      horizontalFilteredTopProjection K p q = 0 := by
  have hne : pq ≠ horizontalFilteredTopIndex p q := by
    intro hpq
    subst pq
    dsimp [horizontalFilteredTopIndex] at h
    omega
  rw [horizontalFilteredTotalι_topProjection, dite_eq_right hne]
  rfl

omit [HasZeroObject C] in
/-- The inclusion of stage `p` into stage `p+1` is annihilated by projection
onto the new top column. -/
@[reassoc (attr := simp)]
theorem horizontalFilteredTotalMap_succ_topProjection (p q : ℕ) :
    horizontalFilteredTotalMap K (Nat.le_succ p) (p + 1 + q) ≫
      horizontalFilteredTopProjection K (p + 1) q = 0 := by
  apply Sigma.hom_ext
  intro pq
  have hmap := horizontalFilteredTotalι_map K (Nat.le_succ p) (p + 1 + q) pq
  change Sigma.ι
      (fun pq : DownNatHorizontalFilteredFiber (p + 1 + q) p =>
        (K.X pq.val.val.1).X pq.val.val.2) pq ≫
      horizontalFilteredTotalMap K (Nat.le_succ p) (p + 1 + q) =
        Sigma.ι
          (fun pq : DownNatHorizontalFilteredFiber (p + 1 + q) (p + 1) =>
            (K.X pq.val.val.1).X pq.val.val.2)
          (horizontalFilteredTotalIndexMap
            (n := p + 1 + q) (Nat.le_succ p) pq) at hmap
  have hproj := horizontalFilteredTotalι_topProjection_of_lt
    K (p + 1) q
      (horizontalFilteredTotalIndexMap
        (n := p + 1 + q) (Nat.le_succ p) pq)
      (Nat.lt_succ_of_le pq.2)
  change Sigma.ι
      (fun pq : DownNatHorizontalFilteredFiber (p + 1 + q) (p + 1) =>
        (K.X pq.val.val.1).X pq.val.val.2)
      (horizontalFilteredTotalIndexMap
        (n := p + 1 + q) (Nat.le_succ p) pq) ≫
      horizontalFilteredTopProjection K (p + 1) q = 0 at hproj
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ horizontalFilteredTopProjection K (p + 1) q) hmap).trans
      (hproj.trans comp_zero.symm))

/-- The vertical column degree represented by a supported cochain degree. -/
def horizontalColumnDegree (p : ℕ) (i : ℤ) : ℕ :=
  (-(p : ℤ) - i).toNat

theorem horizontalColumnDegree_spec (p : ℕ) (i : ℤ)
    (hi : i ≤ -(p : ℤ)) :
    i = -(p : ℤ) - horizontalColumnDegree p i := by
  have hq := Int.toNat_of_nonneg (show 0 ≤ -(p : ℤ) - i by lia)
  unfold horizontalColumnDegree
  omega

/-- Degreewise top-column projection in an arbitrary cochain degree.  It is
zero above the support of the shifted column. -/
noncomputable def horizontalColumnProjection (p : ℕ) (i : ℤ) :
    ((horizontalCompleteFiltrationCochainDiagram K).obj
      (horizontalFirstPageUpperIndex p)).X i ⟶
        (horizontalColumnCochain K p).X i := by
  by_cases hi : i ≤ -(p : ℤ)
  · exact eqToHom (congrArg
      (fun j => ((horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p)).X j)
          (horizontalColumnDegree_spec p i hi)) ≫
      horizontalColumnProjectionComponent K p (horizontalColumnDegree p i) ≫
      eqToHom (congrArg
        (fun j => (horizontalColumnCochain K p).X j)
          (horizontalColumnDegree_spec p i hi).symm)
  · exact 0

theorem horizontalColumnProjection_eq_of_le (p : ℕ) (i : ℤ)
    (hi : i ≤ -(p : ℤ)) :
    horizontalColumnProjection K p i =
      eqToHom (congrArg
        (fun j => ((horizontalCompleteFiltrationCochainDiagram K).obj
          (horizontalFirstPageUpperIndex p)).X j)
            (horizontalColumnDegree_spec p i hi)) ≫
        horizontalColumnProjectionComponent K p (horizontalColumnDegree p i) ≫
        eqToHom (congrArg
          (fun j => (horizontalColumnCochain K p).X j)
            (horizontalColumnDegree_spec p i hi).symm) := by
  unfold horizontalColumnProjection
  rw [dite_eq_left hi]

theorem horizontalColumnProjection_eq_zero_of_lt (p : ℕ) (i : ℤ)
    (hi : -(p : ℤ) < i) :
    horizontalColumnProjection K p i = 0 := by
  unfold horizontalColumnProjection
  rw [dite_eq_right (by lia)]

/-- Projection of the full total degree `p+q` onto bidegree `(p,q)`. -/
noncomputable def horizontalTotalTopProjection (p q : ℕ) :
    (K.total (ComplexShape.down ℕ)).X (p + q) ⟶ (K.X p).X q :=
  K.totalDesc (fun a b h =>
    if hp : a = p then
      eqToHom (by
        subst a
        have hb : b = q := by
          change p + b = p + q at h
          omega
        subst b
        rfl)
    else 0)

omit [HasZeroObject C] in
@[reassoc]
theorem ιTotal_horizontalTotalTopProjection
    (p q a b : ℕ) (h : a + b = p + q) :
    K.ιTotal (ComplexShape.down ℕ) a b (p + q) h ≫
        horizontalTotalTopProjection K p q =
      if hp : a = p then
        eqToHom (by
          subst a
          have hb : b = q := by
            omega
          subst b
          rfl)
      else 0 := by
  exact K.ι_totalDesc _ a b h

omit [HasZeroObject C] in
@[reassoc]
theorem horizontalFilteredTotalToTotal_totalTopProjection (p q : ℕ) :
    horizontalFilteredTotalToTotal K p (p + q) ≫
        horizontalTotalTopProjection K p q =
      horizontalFilteredTopProjection K p q := by
  apply Sigma.hom_ext
  intro idx
  obtain ⟨⟨⟨a, b⟩, hab⟩, hap⟩ := idx
  let idx' : DownNatHorizontalFilteredFiber (p + q) p :=
    ⟨⟨(a, b), hab⟩, hap⟩
  have hto := horizontalFilteredTotalι_toTotal K p (p + q) idx'
  change Sigma.ι
      (fun pq : DownNatHorizontalFilteredFiber (p + q) p =>
        (K.X pq.val.val.1).X pq.val.val.2) idx' ≫
      horizontalFilteredTotalToTotal K p (p + q) =
        K.ιTotal (ComplexShape.down ℕ) a b (p + q) hab at hto
  have hlhs :
      Sigma.ι
          (fun pq : DownNatHorizontalFilteredFiber (p + q) p =>
            (K.X pq.val.val.1).X pq.val.val.2) idx' ≫
        (horizontalFilteredTotalToTotal K p (p + q) ≫
          horizontalTotalTopProjection K p q) =
      K.ιTotal (ComplexShape.down ℕ) a b (p + q) hab ≫
        horizontalTotalTopProjection K p q :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun z => z ≫ horizontalTotalTopProjection K p q) hto)
  by_cases hpa : a = p
  · subst a
    have hb : b = q := by
      change p + b = p + q at hab
      omega
    subst b
    have hfull := ιTotal_horizontalTotalTopProjection K p q p q hab
    rw [dite_eq_left rfl] at hfull
    have hfiltered := horizontalFilteredTopι_topProjection K p q
    change Sigma.ι
        (fun pq : DownNatHorizontalFilteredFiber (p + q) p =>
          (K.X pq.val.val.1).X pq.val.val.2)
        (horizontalFilteredTopIndex p q) ≫
        horizontalFilteredTopProjection K p q = 𝟙 _ at hfiltered
    exact hlhs.trans (hfull.trans hfiltered.symm)
  · have halt : a < p := lt_of_le_of_ne hap hpa
    have hfull := ιTotal_horizontalTotalTopProjection K p q a b hab
    rw [dite_eq_right hpa] at hfull
    have hfiltered := horizontalFilteredTotalι_topProjection_of_lt
      K p q idx' halt
    change Sigma.ι
        (fun pq : DownNatHorizontalFilteredFiber (p + q) p =>
          (K.X pq.val.val.1).X pq.val.val.2) idx' ≫
        horizontalFilteredTopProjection K p q = 0 at hfiltered
    exact hlhs.trans (hfull.trans hfiltered.symm)

omit [HasZeroObject C] in
theorem d₁_horizontalTotalTopProjection_of_le
    (p q a b : ℕ) (htotal : a + b = p + q + 1) (ha : a ≤ p) :
    K.d₁ (ComplexShape.down ℕ) a b (p + q) ≫
      horizontalTotalTopProjection K p q = 0 := by
  cases a with
  | zero =>
      rw [K.d₁_eq_zero (ComplexShape.down ℕ) 0 b (p + q) (by simp),
        zero_comp]
  | succ a =>
      have hab : a + b = p + q := by omega
      rw [K.d₁_eq (ComplexShape.down ℕ)
        (ComplexShape.down_mk (a + 1) a rfl) b (p + q) hab]
      simp only [Linear.units_smul_comp, Category.assoc]
      rw [ιTotal_horizontalTotalTopProjection, dite_eq_right (by omega),
        comp_zero, smul_zero]

omit [HasZeroObject C] in
theorem d₂_horizontalTotalTopProjection_top (p q : ℕ) :
    K.d₂ (ComplexShape.down ℕ) p (q + 1) (p + q) ≫
        horizontalTotalTopProjection K p q =
      ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (p, q + 1) • (K.X p).d (q + 1) q := by
  rw [K.d₂_eq (ComplexShape.down ℕ) p
    (ComplexShape.down_mk (q + 1) q rfl) (p + q) (by simp)]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [ιTotal_horizontalTotalTopProjection, dite_eq_left rfl]
  simp

omit [HasZeroObject C] in
theorem d₂_horizontalTotalTopProjection_of_lt
    (p q a b : ℕ) (htotal : a + b = p + q + 1) (ha : a < p) :
    K.d₂ (ComplexShape.down ℕ) a b (p + q) ≫
      horizontalTotalTopProjection K p q = 0 := by
  cases b with
  | zero =>
      rw [K.d₂_eq_zero (ComplexShape.down ℕ) a 0 (p + q) (by simp),
        zero_comp]
  | succ b =>
      have hab : a + b = p + q := by omega
      rw [K.d₂_eq (ComplexShape.down ℕ) a
        (ComplexShape.down_mk (b + 1) b rfl) (p + q) hab]
      simp only [Linear.units_smul_comp, Category.assoc]
      rw [ιTotal_horizontalTotalTopProjection, dite_eq_right (by omega),
        comp_zero, smul_zero]

omit [HasZeroObject C] in
theorem ιTotal_d_horizontalTotalTopProjection_top (p q : ℕ) :
    K.ιTotal (ComplexShape.down ℕ) p (q + 1) (p + q + 1)
        (by change p + (q + 1) = p + q + 1; omega) ≫
        (K.total (ComplexShape.down ℕ)).d (p + q + 1) (p + q) ≫
        horizontalTotalTopProjection K p q =
      ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (p, q + 1) • (K.X p).d (q + 1) q := by
  change K.ιTotal (ComplexShape.down ℕ) p (q + 1) (p + q + 1)
      (by change p + (q + 1) = p + q + 1; omega) ≫
      (K.D₁ (ComplexShape.down ℕ) (p + q + 1) (p + q) +
        K.D₂ (ComplexShape.down ℕ) (p + q + 1) (p + q)) ≫
      horizontalTotalTopProjection K p q = _
  simp only [Preadditive.comp_add, Preadditive.add_comp,
    K.ι_D₁_assoc, K.ι_D₂_assoc]
  rw [d₁_horizontalTotalTopProjection_of_le K p q p (q + 1) (by omega) le_rfl,
    d₂_horizontalTotalTopProjection_top K p q, zero_add]

omit [HasZeroObject C] in
theorem ιTotal_d_horizontalTotalTopProjection_of_lt
    (p q a b : ℕ) (htotal : a + b = p + q + 1) (ha : a < p) :
    K.ιTotal (ComplexShape.down ℕ) a b (p + q + 1) htotal ≫
        (K.total (ComplexShape.down ℕ)).d (p + q + 1) (p + q) ≫
        horizontalTotalTopProjection K p q = 0 := by
  change K.ιTotal (ComplexShape.down ℕ) a b (p + q + 1) htotal ≫
      (K.D₁ (ComplexShape.down ℕ) (p + q + 1) (p + q) +
        K.D₂ (ComplexShape.down ℕ) (p + q + 1) (p + q)) ≫
      horizontalTotalTopProjection K p q = 0
  simp only [Preadditive.comp_add, Preadditive.add_comp,
    K.ι_D₁_assoc, K.ι_D₂_assoc]
  rw [d₁_horizontalTotalTopProjection_of_le K p q a b htotal ha.le,
    d₂_horizontalTotalTopProjection_of_lt K p q a b htotal ha, zero_add]

omit [HasZeroObject C] in
/-- On the top column of a filtered stage, the filtered differential is the
signed vertical differential; every lower-column contribution vanishes. -/
theorem horizontalFilteredTotalD_topProjection (p q : ℕ) :
    horizontalFilteredTotalD K p (p + q + 1) (p + q) ≫
        horizontalFilteredTopProjection K p q =
      horizontalFilteredTopProjection K p (q + 1) ≫
        (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (p, q + 1) • (K.X p).d (q + 1) q) := by
  have hfactor := horizontalFilteredTotalToTotal_totalTopProjection K p q
  have hD := horizontalFilteredTotalD_toTotal K p (p + q)
  have hglobal :
      horizontalFilteredTotalD K p (p + q + 1) (p + q) ≫
          horizontalFilteredTopProjection K p q =
        horizontalFilteredTotalToTotal K p (p + q + 1) ≫
          (K.total (ComplexShape.down ℕ)).d (p + q + 1) (p + q) ≫
          horizontalTotalTopProjection K p q := by
    calc
      horizontalFilteredTotalD K p (p + q + 1) (p + q) ≫
          horizontalFilteredTopProjection K p q =
        horizontalFilteredTotalD K p (p + q + 1) (p + q) ≫
          (horizontalFilteredTotalToTotal K p (p + q) ≫
            horizontalTotalTopProjection K p q) :=
        congrArg
          (fun z => horizontalFilteredTotalD K p (p + q + 1) (p + q) ≫ z)
          hfactor.symm
      _ = (horizontalFilteredTotalD K p (p + q + 1) (p + q) ≫
          horizontalFilteredTotalToTotal K p (p + q)) ≫
            horizontalTotalTopProjection K p q :=
        (Category.assoc _ _ _).symm
      _ = (horizontalFilteredTotalToTotal K p (p + q + 1) ≫
          (K.total (ComplexShape.down ℕ)).d (p + q + 1) (p + q)) ≫
            horizontalTotalTopProjection K p q :=
        congrArg (fun z => z ≫ horizontalTotalTopProjection K p q) hD
      _ = horizontalFilteredTotalToTotal K p (p + q + 1) ≫
          (K.total (ComplexShape.down ℕ)).d (p + q + 1) (p + q) ≫
            horizontalTotalTopProjection K p q :=
        Category.assoc _ _ _
  apply Sigma.hom_ext
  intro idx
  obtain ⟨⟨⟨a, b⟩, hab⟩, hap⟩ := idx
  let idx' : DownNatHorizontalFilteredFiber (p + q + 1) p :=
    ⟨⟨(a, b), hab⟩, hap⟩
  have hι := horizontalFilteredTotalι_toTotal K p (p + q + 1) idx'
  change Sigma.ι
      (fun pq : DownNatHorizontalFilteredFiber (p + q + 1) p =>
        (K.X pq.val.val.1).X pq.val.val.2) idx' ≫
      horizontalFilteredTotalToTotal K p (p + q + 1) =
        K.ιTotal (ComplexShape.down ℕ) a b (p + q + 1) hab at hι
  have hlhs :
      Sigma.ι
          (fun pq : DownNatHorizontalFilteredFiber (p + q + 1) p =>
            (K.X pq.val.val.1).X pq.val.val.2) idx' ≫
        (horizontalFilteredTotalD K p (p + q + 1) (p + q) ≫
          horizontalFilteredTopProjection K p q) =
      K.ιTotal (ComplexShape.down ℕ) a b (p + q + 1) hab ≫
        (K.total (ComplexShape.down ℕ)).d (p + q + 1) (p + q) ≫
          horizontalTotalTopProjection K p q := by
    calc
      _ = Sigma.ι
          (fun pq : DownNatHorizontalFilteredFiber (p + q + 1) p =>
            (K.X pq.val.val.1).X pq.val.val.2) idx' ≫
        (horizontalFilteredTotalToTotal K p (p + q + 1) ≫
          (K.total (ComplexShape.down ℕ)).d (p + q + 1) (p + q) ≫
            horizontalTotalTopProjection K p q) :=
        congrArg (fun z => Sigma.ι
          (fun pq : DownNatHorizontalFilteredFiber (p + q + 1) p =>
            (K.X pq.val.val.1).X pq.val.val.2) idx' ≫ z) hglobal
      _ = (Sigma.ι
          (fun pq : DownNatHorizontalFilteredFiber (p + q + 1) p =>
            (K.X pq.val.val.1).X pq.val.val.2) idx' ≫
        horizontalFilteredTotalToTotal K p (p + q + 1)) ≫
          (K.total (ComplexShape.down ℕ)).d (p + q + 1) (p + q) ≫
            horizontalTotalTopProjection K p q :=
        (Category.assoc _ _ _).symm
      _ = _ := by rw [hι]
  by_cases hpa : a = p
  · subst a
    have hb : b = q + 1 := by
      change p + b = p + q + 1 at hab
      omega
    subst b
    have htot := ιTotal_d_horizontalTotalTopProjection_top K p q
    have hidx : idx' = horizontalFilteredTopIndex p (q + 1) := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    cases hidx
    have hproj := horizontalFilteredTopι_topProjection K p (q + 1)
    have hcomp := congrArg
      (fun z => z ≫
        (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (p, q + 1) • (K.X p).d (q + 1) q)) hproj
    have hcomp' := hcomp.trans (Category.id_comp _)
    have hcompRight :=
      (Category.assoc _ _ _).symm.trans hcomp'
    exact hlhs.trans (htot.trans (by
      exact hcompRight.symm))
  · have halt : a < p := lt_of_le_of_ne hap hpa
    have htot := ιTotal_d_horizontalTotalTopProjection_of_lt
      K p q a b hab halt
    have hproj := horizontalFilteredTotalι_topProjection_of_lt
      K p (q + 1) idx' halt
    change Sigma.ι
        (fun pq : DownNatHorizontalFilteredFiber (p + q + 1) p =>
          (K.X pq.val.val.1).X pq.val.val.2) idx' ≫
        Sigma.π
          (fun pq : DownNatHorizontalFilteredFiber (p + q + 1) p =>
            (K.X pq.val.val.1).X pq.val.val.2)
          (horizontalFilteredTopIndex p (q + 1)) = 0 at hproj
    have hcomp := congrArg
      (fun z => z ≫
        (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (p, q + 1) • (K.X p).d (q + 1) q)) hproj
    have hcomp' := hcomp.trans zero_comp
    have hcompRight :=
      (Category.assoc _ _ _).symm.trans hcomp'
    exact hlhs.trans (htot.trans hcompRight.symm)

end HomologicalComplex₂

end
