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
# Shifted vertical columns and horizontal graded-piece projections

Let `K` be a first-quadrant bicomplex in a preadditive category with a zero object and finite
coproducts. Horizontal filtration stage `p` retains columns `0,…,p`. Its top-column quotient
has vertical degree `q` in total degree `p+q`.

Extend column `p` from chain to cochain degrees and shift by `p`, placing its degree `q` at
`-p-q`. The shifted differential has sign `(-1)^p`. Top-summand projections kill every
preceding-column summand and every preceding filtration stage. They vanish in cochain degrees
above `-p`, and their projected boundary is the signed vertical differential.
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

/-- The shifted cochain presentation of a vertical column.

Extend vertical column `p` to integer cochain degrees and shift by `p`, so vertical degree `q`
lies at `-p-q` with differential sign `(-1)^p`. -/
noncomputable def horizontalColumnCochain (p : ℕ) :
    CochainComplex C ℤ :=
  (shiftFunctor (CochainComplex C ℤ) (p : ℤ)).obj
    ((K.X p).extend ComplexShape.embeddingDownNat)

/-- The degree-object comparison of a shifted vertical column.

The shifted column object at cochain degree `-p-q` is isomorphic to `K_(p,q)`. -/
noncomputable def horizontalColumnCochainXIso (p q : ℕ) :
    (horizontalColumnCochain K p).X (-(p : ℤ) - q) ≅
      (K.X p).X q :=
  CochainComplex.shiftFunctorObjXIso
      ((K.X p).extend ComplexShape.embeddingDownNat)
      (p : ℤ) (-(p : ℤ) - q) (-(q : ℤ)) (by omega) ≪≫
    (K.X p).extendXIso ComplexShape.embeddingDownNat (by simp)

omit [HasFiniteCoproducts C] in
/-- The upper support bound of a shifted vertical column.

The column cochain object is zero whenever the cochain degree is strictly above `-p`. -/
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

/-- The finite-stage subobject at a nonnegative complete upper index.

The complete upper filtration subobject for column `p` is the natural horizontal filtration
subobject at stage `p`. -/
theorem horizontalCompleteFilteredTotalMonoOver_upper (p : ℕ) :
    horizontalCompleteFilteredTotalMonoOver K
        (horizontalFirstPageUpperIndex p) =
      (horizontalTotalFiltration K).toMonoOver.obj p := by
  unfold horizontalCompleteFilteredTotalMonoOver horizontalFirstPageUpperIndex
  simp only [WithBotTop.rec_coe]
  rw [ite_eq_left (show 0 ≤ (p : ℤ) by omega)]
  congr 2

/-- The upper-subobject comparison with a natural filtration stage.

The equality of the complete upper subobject and natural stage gives their canonical
isomorphism. -/
noncomputable def horizontalCompleteFilteredTotalMonoOverUpperIso (p : ℕ) :
    horizontalCompleteFilteredTotalMonoOver K
        (horizontalFirstPageUpperIndex p) ≅
      (horizontalTotalFiltration K).toMonoOver.obj p :=
  eqToIso (horizontalCompleteFilteredTotalMonoOver_upper K p)

/-- The cochain comparison of a complete upper filtration subobject.

Forget the subobject comparison and apply chain-to-cochain extension to identify the upper
complete stage with the extended natural stage. -/
noncomputable def horizontalCompleteFiltrationCochainMonoUpperIso (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) ≅
      (ComplexShape.embeddingDownNat.extendFunctor C).obj
        ((horizontalTotalFiltration K).toMonoOver.obj p).obj.left :=
  (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
    ((MonoOver.forget _ ⋙ Over.forget _).mapIso
      (horizontalCompleteFilteredTotalMonoOverUpperIso K p))

/-- The finite filtered-complex presentation of a complete upper stage.

The complete upper stage for column `p` is isomorphic to the cochain extension of finite
filtered stage `p`. -/
noncomputable def horizontalCompleteFiltrationCochainUpperIso (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) ≅
      (horizontalFilteredTotalComplex K p).extend
        ComplexShape.embeddingDownNat :=
  horizontalCompleteFiltrationCochainMonoUpperIso K p ≪≫
    (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
      (eqToIso (horizontalTotalFiltration_diagram_obj K p))

/-- The top-column projection at a supported cochain degree.

At degree `-p-q`, transport the projection from finite stage `p` to bidegree `(p,q)` into the
shifted-column cochain presentation. -/
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

/-- The top bidegree index of a finite filtered total.

In total degree `p+q` and stage `p`, the top-column summand is indexed by `(p,q)`. -/
def horizontalFilteredTopIndex (p q : ℕ) :
    DownNatHorizontalFilteredFiber (p + q) p :=
  ⟨⟨(p, q), by simp⟩, by simp⟩

/-- The top-summand projection of a finite filtered total.

Project stage `p` in total degree `p+q` onto the bidegree `(p,q)` object. -/
noncomputable def horizontalFilteredTopProjection (p q : ℕ) :
    horizontalFilteredTotalObj K p (p + q) ⟶ (K.X p).X q :=
  Sigma.π
    (fun pq : DownNatHorizontalFilteredFiber (p + q) p =>
      (K.X pq.val.val.1).X pq.val.val.2)
    (horizontalFilteredTopIndex p q)

omit [HasZeroObject C] in
/-- The summand formula for a filtered top-column projection.

A summand inclusion followed by the top projection is the degree identification for the top
index and zero for every other index. -/
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
/-- The identity on the top filtered summand.

The top bidegree inclusion followed by its projection is the identity. -/
@[reassoc (attr := simp)]
theorem horizontalFilteredTopι_topProjection (p q : ℕ) :
    horizontalFilteredTotalι K p (p + q)
        (horizontalFilteredTopIndex p q) ≫
      horizontalFilteredTopProjection K p q = 𝟙 _ := by
  rw [horizontalFilteredTotalι_topProjection, dite_eq_left rfl]
  rfl

omit [HasZeroObject C] in
/-- Vanishing of a lower-column summand under top projection.

A summand with horizontal index below `p` is killed by projection to the stage-`p` top column. -/
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
/-- Vanishing of a preceding filtration stage under the next top projection.

The inclusion of stage `p` into stage `p+1` followed by its new top-column projection is zero. -/
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

/-- The vertical degree of a supported shifted-column coordinate.

For column `p` and cochain degree `i`, use `(-p-i).toNat` as the vertical-degree coordinate. -/
def horizontalColumnDegree (p : ℕ) (i : ℤ) : ℕ :=
  (-(p : ℤ) - i).toNat

/-- The degree identity on the support of a shifted column.

If `i ≤ -p`, then `i = -p - horizontalColumnDegree(p,i)`. -/
theorem horizontalColumnDegree_spec (p : ℕ) (i : ℤ)
    (hi : i ≤ -(p : ℤ)) :
    i = -(p : ℤ) - horizontalColumnDegree p i := by
  have hq := Int.toNat_of_nonneg (show 0 ≤ -(p : ℤ) - i by lia)
  unfold horizontalColumnDegree
  omega

/-- The top-column projection in every cochain degree.

Use the supported component projection when `i ≤ -p`, and the zero map when `i>-p`. -/
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

/-- The supported formula for an arbitrary-degree column projection.

For `i ≤ -p`, the projection is the component at vertical degree `(-p-i).toNat`, transported
by the corresponding degree equalities. -/
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

/-- The zero projection above shifted-column support.

If `i>-p`, the arbitrary-degree top-column projection is zero. -/
theorem horizontalColumnProjection_eq_zero_of_lt (p : ℕ) (i : ℤ)
    (hi : -(p : ℤ) < i) :
    horizontalColumnProjection K p i = 0 := by
  unfold horizontalColumnProjection
  rw [dite_eq_right (by lia)]

/-- The full-total projection onto a fixed bidegree.

Project total degree `p+q` onto bidegree `(p,q)`, killing all other total summands. -/
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
/-- The summand formula for a full-total bidegree projection.

A total inclusion from `(a,b)` with `a+b=p+q` projects to the degree identification when
`a=p`, and to zero otherwise. -/
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
/-- Compatibility of filtered and full-total top projections.

The finite-stage inclusion into the full total followed by its top bidegree projection equals
the filtered top projection. -/
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
/-- Vanishing of lower horizontal boundary terms under top projection.

A horizontal boundary from a total summand with first index at most `p` cannot reach the
projected column `p`, so its projection is zero. -/
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
/-- The signed vertical boundary in the top projected column.

The vertical total-boundary component from `(p,q+1)` projects to `ε₂(p,q+1) • d_vertical`,
with the standard sign `(-1)^p`. -/
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
/-- Vanishing of lower vertical boundary terms under top projection.

The vertical boundary of a summand with first index below `p` is killed by projection to
column `p`. -/
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
/-- The full total boundary of a top-column summand after projection.

The boundary from `(p,q+1)` followed by projection to `(p,q)` is the vertical map with total
sign `ε₂(p,q+1)`. -/
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
/-- The projected total boundary of a lower-column summand.

A total summand with first index below `p` has zero boundary component after projection to
`(p,q)`. -/
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
/-- The filtered top-column differential identity.

The finite-stage boundary followed by top projection equals the previous top projection
followed by the vertical boundary with sign `ε₂(p,q+1)`. -/
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
