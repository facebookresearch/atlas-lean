/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.Grp.Zero

public import MathlibExt.Algebra.Homology.ChainComplex.HomZeroSource
public import MathlibExt.Algebra.Homology.ChainComplex.HomCycles
public import MathlibExt.Algebra.Homology.ChainComplex.HomUniversalCoefficient
public import MathlibExt.Algebra.Homology.ShortComplex.ChangeObjects
public import MathlibExt.Algebra.Category.Grp.AddCommGrpProduct
public import MathlibExt.Algebra.Homology.HomologicalComplex.HomologyProjection
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Hom cochains with a fixed coefficient object

For an integer chain complex `P` and an object `M`, the fixed-coefficient
Hom complex has degree-`n` group `P.X n ⟶ M`; its differential is
precomposition with the differential of `P`. It is identified with the full
Hom cochain product whose target is concentrated in degree zero.

These coordinates identify the cycle restrictions and the kernel and
cokernel maps in the fixed-coefficient universal coefficient sequence.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.Abelian
open HomologicalComplex

namespace ChainComplex

universe u v

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

omit [HasZeroObject C] in
/-- Native positive-precomposition Hom of the original integer chain complex. -/
def homFixedCoefficient (P : ChainComplex C ℤ) (M : C) : CochainComplex AddCommGrpCat.{v} ℤ :=
  ((preadditiveYoneda.obj M).mapHomologicalComplex (ComplexShape.up ℤ)).obj P.op

omit [HasZeroObject C] in
/-- The degree object is the original morphism group, without a grading bound. -/
lemma homFixedCoefficient_X (P : ChainComplex C ℤ) (M : C) (n : ℤ) :
    (homFixedCoefficient P M).X n = AddCommGrpCat.of (P.X n ⟶ M) := rfl

omit [HasZeroObject C] in
/-- The fixed coefficient differential is the original positive precomposition map. -/
lemma homFixedCoefficient_d_apply (P : ChainComplex C ℤ) (M : C) (n m : ℤ)
    (f : P.X n ⟶ M) :
    ((homFixedCoefficient P M).d n m).hom f = P.d m n ≫ f := rfl

omit [HasZeroObject C] in
private lemma differential_index_transport (P : ChainComplex C ℤ)
    (i i' j j' : ℤ) (hi : i = i') (hj : j = j') :
    (P.XIsoOfEq hi).inv ≫ P.d i j ≫ (P.XIsoOfEq hj).hom = P.d i' j' := by
  subst i'
  subst j'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id]

/-- Actual target-single coordinates identify all full cochains with the fixed coefficient group. -/
def homFixedCoefficientCochainEquiv (P : ChainComplex C ℤ) (M : C) (n : ℤ) :
    CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P)
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) n ≃+
        (P.X n ⟶ M) := by
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let e : Q.X (n - n) ≅ M :=
    HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M (n - n) (by omega)
  let E : (∀ p : ℤ, P.X p ⟶ Q.X (n - p)) ≃+ (P.X n ⟶ M) :=
    { toFun f := f n ≫ e.hom
      invFun k p := if hp : p = n then
          (P.XIsoOfEq hp).hom ≫ k ≫
            (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M
              (n - p) (by omega)).inv
        else 0
      left_inv f := by
        funext p
        dsimp only
        by_cases hp : p = n
        · subst p
          rw [dif_pos rfl]
          change (𝟙 (P.X n)) ≫ ((f n ≫ e.hom) ≫ e.inv) = f n
          exact (Category.id_comp ((f n ≫ e.hom) ≫ e.inv)).trans
            ((Category.assoc (f n) e.hom e.inv).trans
              ((congrArg (fun a => f n ≫ a) e.hom_inv_id).trans (Category.comp_id (f n))))
        · rw [dif_neg hp]
          exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M
            (n - p) (by omega)).eq_of_tgt _ _
      right_inv k := by
        dsimp only
        rw [dif_pos rfl]
        change ((𝟙 (P.X n)) ≫ k ≫ e.inv) ≫ e.hom = k
        exact (congrArg (fun a : P.X n ⟶ Q.X (n - n) => a ≫ e.hom)
          (Category.id_comp (k ≫ e.inv))).trans
            ((Category.assoc k e.inv e.hom).trans
              ((congrArg (fun a => k ≫ a) e.inv_hom_id).trans (Category.comp_id k)))
      map_add' f g := by
        change (f n + g n) ≫ e.hom = f n ≫ e.hom + g n ≫ e.hom
        exact Preadditive.add_comp (P.X n) (Q.X (n - n)) M (f n) (g n) e.hom }
  exact (homCochainPhysicalPiEquiv P Q n).trans E

/-- The forward comparison is the actual physical degree-n component and target single iso. -/
lemma homFixedCoefficientCochainEquiv_apply (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P)
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) n) :
    homFixedCoefficientCochainEquiv P M n z =
      homCochainComponent P ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)
        n z n ≫ (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M
          (n - n) (by omega)).hom := rfl

private lemma targetSingleComponent_transport (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P)
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) n)
    (r q : ℤ) (h : r + n = q) (hq : q = 0) :
    z.v r q h ≫ (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M q hq).hom =
      z.v r 0 (by omega) ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom := by
  subst hq
  rfl

/-- The comparison evaluates the original native (-n,0) component, with no degree unit. -/
lemma homFixedCoefficientCochainEquiv_apply_zero (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P)
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) n) :
    homFixedCoefficientCochainEquiv P M n z =
      (P.XIsoOfEq (Int.neg_neg n)).inv ≫ z.v (-n) 0 (by omega) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom := by
  let A : CochainComplex C ℤ := (cochainComplexEquivalence C).functor.obj P
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let a : P.X n ⟶ A.X (-n) := (P.XIsoOfEq (Int.neg_neg n)).inv
  let v : A.X (-n) ⟶ Q.X (n - n) := z.v (-n) (n - n) (by omega)
  let v₀ : A.X (-n) ⟶ Q.X 0 := z.v (-n) 0 (by omega)
  let e : Q.X (n - n) ≅ M :=
    HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M (n - n) (by omega)
  let e₀ : Q.X 0 ≅ M := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M
  have h : v ≫ e.hom = v₀ ≫ e₀.hom :=
    targetSingleComponent_transport P M n z (-n) (n - n) (by omega) (by omega)
  change (a ≫ v) ≫ e.hom = a ≫ v₀ ≫ e₀.hom
  exact (Category.assoc a v e.hom).trans
    (congrArg (fun t : A.X (-n) ⟶ M => a ≫ t) h)

omit [HasZeroObject C] in
private lemma reindexedPrecomposition_transport (P : ChainComplex C ℤ)
    (Q : CochainComplex C ℤ) (n m r : ℤ) (hr : r = -n)
    (z : CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) Q n) :
    (P.XIsoOfEq (Int.neg_neg m)).inv ≫ P.d (-(-m)) (-r) ≫ z.v r 0 (by omega) =
      P.d m n ≫ (P.XIsoOfEq (Int.neg_neg n)).inv ≫ z.v (-n) 0 (by omega) := by
  subst r
  let a : P.X m ⟶ P.X (-(-m)) := (P.XIsoOfEq (Int.neg_neg m)).inv
  let b : P.X (-(-n)) ≅ P.X n := P.XIsoOfEq (Int.neg_neg n)
  let d₀ : P.X (-(-m)) ⟶ P.X (-(-n)) := P.d (-(-m)) (-(-n))
  let d : P.X m ⟶ P.X n := P.d m n
  let v : P.X (-(-n)) ⟶ Q.X 0 := z.v (-n) 0 (by omega)
  have hd : a ≫ d₀ ≫ b.hom = d :=
    differential_index_transport P (-(-m)) m (-(-n)) n (Int.neg_neg m) (Int.neg_neg n)
  have h : a ≫ d₀ = d ≫ b.inv := by
    apply (cancel_mono b.hom).1
    have hLeft : (a ≫ d₀) ≫ b.hom = d := (Category.assoc a d₀ b.hom).trans hd
    have hRight : (d ≫ b.inv) ≫ b.hom = d :=
      (Category.assoc d b.inv b.hom).trans
        ((congrArg (fun t => d ≫ t) b.inv_hom_id).trans (Category.comp_id d))
    exact hLeft.trans hRight.symm
  change a ≫ d₀ ≫ v = d ≫ b.inv ≫ v
  exact (Category.assoc a d₀ v).symm.trans
    ((congrArg (fun t : P.X m ⟶ P.X (-(-n)) => t ≫ v) h).trans
      (Category.assoc d b.inv v))

/-- The genuine target single differential leaves the original positive precomposition. -/
lemma homFixedCoefficientCochainEquiv_d (P : ChainComplex C ℤ) (M : C)
    (n m : ℤ) (hnm : n + 1 = m)
    (z : CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P)
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) n) :
    homFixedCoefficientCochainEquiv P M m
        (((homCochainComplex P
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)).d n m).hom z) =
      P.d m n ≫ homFixedCoefficientCochainEquiv P M n z := by
  let A : CochainComplex C ℤ := (cochainComplexEquivalence C).functor.obj P
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P Q
  let a : P.X m ⟶ A.X (-m) := (P.XIsoOfEq (Int.neg_neg m)).inv
  let aₙ : P.X n ⟶ A.X (-n) := (P.XIsoOfEq (Int.neg_neg n)).inv
  let w : A.X (-m + 1) ⟶ Q.X 0 := z.v (-m + 1) 0 (by omega)
  let v : A.X (-n) ⟶ Q.X 0 := z.v (-n) 0 (by omega)
  let u : A.X (-m) ⟶ Q.X (-1) := z.v (-m) (-1) (by omega)
  let d₀ : A.X (-m) ⟶ A.X (-m + 1) := A.d (-m) (-m + 1)
  let e : Q.X 0 ≅ M := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M
  let δz : CochainComplex.HomComplex.Cochain A Q m := (H.d n m).hom z
  have hQ : Q.d (-1) 0 = 0 :=
    HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 M (-1) 0
  have hz : u ≫ Q.d (-1) 0 = (0 : A.X (-m) ⟶ Q.X 0) :=
    (congrArg (fun t : Q.X (-1) ⟶ Q.X 0 => u ≫ t) hQ).trans
      (CategoryTheory.Limits.comp_zero (f := u))
  have hδ : δz.v (-m) 0 (by omega) = d₀ ≫ w + m.negOnePow • (u ≫ Q.d (-1) 0) :=
    homCochainComplex_d_v P Q n m hnm z (-m) 0 (by omega)
  have hδ₀ : δz.v (-m) 0 (by omega) = d₀ ≫ w :=
    hδ.trans ((congrArg (fun t : A.X (-m) ⟶ Q.X 0 => d₀ ≫ w + m.negOnePow • t) hz).trans
      ((congrArg (fun t : A.X (-m) ⟶ Q.X 0 => d₀ ≫ w + t)
        (smul_zero m.negOnePow)).trans (add_zero (d₀ ≫ w))))
  have hP : a ≫ d₀ ≫ w = P.d m n ≫ aₙ ≫ v :=
    reindexedPrecomposition_transport P Q n m (-m + 1) (by omega) z
  have hE : homFixedCoefficientCochainEquiv P M m δz =
      a ≫ δz.v (-m) 0 (by omega) ≫ e.hom :=
    homFixedCoefficientCochainEquiv_apply_zero P M m δz
  have hEn : homFixedCoefficientCochainEquiv P M n z = aₙ ≫ v ≫ e.hom :=
    homFixedCoefficientCochainEquiv_apply_zero P M n z
  change homFixedCoefficientCochainEquiv P M m δz =
    P.d m n ≫ homFixedCoefficientCochainEquiv P M n z
  exact hE.trans
    ((congrArg (fun t : A.X (-m) ⟶ Q.X 0 => a ≫ t ≫ e.hom) hδ₀).trans
      ((Category.assoc a (d₀ ≫ w) e.hom).symm.trans
        ((congrArg (fun t : P.X m ⟶ Q.X 0 => t ≫ e.hom) hP).trans
          ((Category.assoc (P.d m n) (aₙ ≫ v) e.hom).trans
            ((congrArg (fun t : P.X n ⟶ M => P.d m n ≫ t)
              (Category.assoc aₙ v e.hom)).trans
                (congrArg (fun t : P.X n ⟶ M => P.d m n ≫ t) hEn.symm))))))

/-- The actual full-product target-single Hom complex is native positive-precomposition Hom. -/
def homFixedCoefficientIso (P : ChainComplex C ℤ) (M : C) :
    homCochainComplex P ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) ≅
      homFixedCoefficient P M := by
  let A : CochainComplex C ℤ := (cochainComplexEquivalence C).functor.obj P
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P Q
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let e (n : ℤ) : H.X n ≅ K.X n := by
    let X : AddCommGrpCat.{v} := AddCommGrpCat.of
      (CochainComplex.HomComplex.Cochain A Q n)
    let Y : AddCommGrpCat.{v} := AddCommGrpCat.of (P.X n ⟶ M)
    change X ≅ Y
    exact AddEquiv.toAddCommGrpIso (X := X) (Y := Y) (homFixedCoefficientCochainEquiv P M n)
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro n m h
  have hnm : n + 1 = m := h
  apply AddCommGrpCat.ext
  intro z
  let z₀ : CochainComplex.HomComplex.Cochain A Q n := z
  let δz : CochainComplex.HomComplex.Cochain A Q m := (H.d n m).hom z₀
  have he : (e n).hom.hom z = homFixedCoefficientCochainEquiv P M n z₀ := rfl
  have he' : (e m).hom.hom δz = homFixedCoefficientCochainEquiv P M m δz := rfl
  have hLeft : ((e n).hom ≫ K.d n m).hom z =
      P.d m n ≫ homFixedCoefficientCochainEquiv P M n z₀ :=
    (AddCommGrpCat.comp_apply (e n).hom (K.d n m) z).trans
      ((congrArg (K.d n m).hom he).trans
        (homFixedCoefficient_d_apply P M n m (homFixedCoefficientCochainEquiv P M n z₀)))
  have hRight : (H.d n m ≫ (e m).hom).hom z =
      homFixedCoefficientCochainEquiv P M m δz :=
    (AddCommGrpCat.comp_apply (H.d n m) (e m).hom z).trans he'
  exact hLeft.trans
    ((homFixedCoefficientCochainEquiv_d P M n m hnm z₀).symm.trans hRight.symm)

/-- The complex comparison retains the actual degreewise full-cochain coordinate map. -/
lemma homFixedCoefficientIso_hom_f_apply (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P)
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) n) :
    ((homFixedCoefficientIso P M).hom.f n).hom z =
      homFixedCoefficientCochainEquiv P M n z := rfl

private lemma targetSingleValue_naturality {M M' : C} (b : M ⟶ M') (q : ℤ)
    (hq : q = 0) :
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b).f q ≫
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M' q hq).hom =
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M q hq).hom ≫ b := by
  subst q
  have h := (HomologicalComplex.singleCompEvalIsoSelf C (ComplexShape.up ℤ) 0).hom.naturality b
  change ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b).f 0 ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M').hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom ≫ b at h
  exact h

/-- The fixed-cochain coordinate comparison retains both actual original variable maps. -/
lemma homFixedCoefficientCochainEquiv_map {P P' : ChainComplex C ℤ} {M M' : C}
    (f : P' ⟶ P) (b : M ⟶ M') (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P)
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) n) :
    homFixedCoefficientCochainEquiv P' M' n
        (((homCochainComplexMap f
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b)).f n).hom z) =
      f.f n ≫ homFixedCoefficientCochainEquiv P M n z ≫ b := by
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let Q' : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M'
  let g : Q ⟶ Q' := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b
  let z' : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P') Q' n :=
    ((homCochainComplexMap f g).f n).hom z
  let v : P.X n ⟶ Q.X (n - n) := homCochainComponent P Q n z n
  let v' : P'.X n ⟶ Q'.X (n - n) := homCochainComponent P' Q' n z' n
  let e : Q.X (n - n) ≅ M :=
    HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M (n - n) (by omega)
  let e' : Q'.X (n - n) ≅ M' :=
    HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M' (n - n) (by omega)
  let a : P'.X n ⟶ P.X n := f.f n
  let t : Q.X (n - n) ⟶ Q'.X (n - n) := g.f (n - n)
  have hv : v' = a ≫ v ≫ t := homCochainComponent_map f g n n z
  have ht : t ≫ e'.hom = e.hom ≫ b := targetSingleValue_naturality b (n - n) (by omega)
  change v' ≫ e'.hom = a ≫ (v ≫ e.hom) ≫ b
  exact (congrArg (fun x : P'.X n ⟶ Q'.X (n - n) => x ≫ e'.hom) hv).trans
    ((Category.assoc a (v ≫ t) e'.hom).trans
      (congrArg (fun x : P.X n ⟶ M' => a ≫ x)
        ((Category.assoc v t e'.hom).trans
          ((congrArg (fun x : Q.X (n - n) ⟶ M' => v ≫ x) ht).trans
            (Category.assoc v e.hom b).symm))))

omit [HasZeroObject C] in
/-- The earned target-single comparison transports the actual native two-variable Hom map. -/
def homFixedCoefficientMap {P P' : ChainComplex C ℤ} {M M' : C}
    (f : P' ⟶ P) (b : M ⟶ M') : homFixedCoefficient P M ⟶ homFixedCoefficient P' M' :=
  ((preadditiveYoneda.obj M).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((HomologicalComplex.opFunctor C (ComplexShape.down ℤ)).map f.op) ≫
    ((preadditiveYoneda.map b).mapHomologicalComplex (ComplexShape.up ℤ)).app P'.op

/-- Simultaneous naturality is a square of the actual computed cochain maps. -/
lemma homFixedCoefficientIso_naturality {P P' : ChainComplex C ℤ} {M M' : C}
    (f : P' ⟶ P) (b : M ⟶ M') :
    homCochainComplexMap f ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b) ≫
        (homFixedCoefficientIso P' M').hom =
      (homFixedCoefficientIso P M).hom ≫ homFixedCoefficientMap f b := by
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.ext
  intro z
  let g := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b
  let a := homCochainComplexMap f g
  change homFixedCoefficientCochainEquiv P' M' n ((a.f n).hom z) =
    (f.f n ≫ homFixedCoefficientCochainEquiv P M n z) ≫ b
  exact (homFixedCoefficientCochainEquiv_map f b n z).trans
    (Category.assoc (f.f n) (homFixedCoefficientCochainEquiv P M n z) b).symm

omit [HasZeroObject C] in
/-- Every map component is the original source precomposition and coefficient postcomposition. -/
lemma homFixedCoefficientMap_f_apply {P P' : ChainComplex C ℤ} {M M' : C}
    (f : P' ⟶ P) (b : M ⟶ M') (n : ℤ) (k : P.X n ⟶ M) :
    ((homFixedCoefficientMap f b).f n).hom k = f.f n ≫ k ≫ b := by
  change (f.f n ≫ k) ≫ b = f.f n ≫ k ≫ b
  exact Category.assoc (f.f n) k b

omit [HasZeroObject C] in
/-- Original identity maps induce the identity fixed-coefficient Hom map. -/
lemma homFixedCoefficientMap_id (P : ChainComplex C ℤ) (M : C) :
    homFixedCoefficientMap (𝟙 P) (𝟙 M) = 𝟙 (homFixedCoefficient P M) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.ext
  intro k
  change ((homFixedCoefficientMap (𝟙 P) (𝟙 M)).f n).hom k = k
  exact (homFixedCoefficientMap_f_apply (𝟙 P) (𝟙 M) n k).trans
    ((Category.id_comp (k ≫ 𝟙 M)).trans (Category.comp_id k))

omit [HasZeroObject C] in
/-- Composition retains the contravariant original source and covariant coefficient order. -/
lemma homFixedCoefficientMap_comp {P P' P'' : ChainComplex C ℤ} {M M' M'' : C}
    (f : P' ⟶ P) (f' : P'' ⟶ P') (b : M ⟶ M') (b' : M' ⟶ M'') :
    homFixedCoefficientMap (f' ≫ f) (b ≫ b') =
      homFixedCoefficientMap f b ≫ homFixedCoefficientMap f' b' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.ext
  intro k
  let a : P'.X n ⟶ P.X n := f.f n
  let a' : P''.X n ⟶ P'.X n := f'.f n
  let m := (homFixedCoefficientMap f b).f n
  let m' := (homFixedCoefficientMap f' b').f n
  have hLeft : ((homFixedCoefficientMap (f' ≫ f) (b ≫ b')).f n).hom k =
      (a' ≫ a) ≫ k ≫ (b ≫ b') := homFixedCoefficientMap_f_apply (f' ≫ f) (b ≫ b') n k
  have hFirst : m.hom k = a ≫ k ≫ b := homFixedCoefficientMap_f_apply f b n k
  have hSecond : m'.hom (m.hom k) = a' ≫ m.hom k ≫ b' :=
    homFixedCoefficientMap_f_apply f' b' n (m.hom k)
  have hRight : (m ≫ m').hom k = a' ≫ (a ≫ k ≫ b) ≫ b' :=
    (AddCommGrpCat.comp_apply m m' k).trans
      (hSecond.trans (congrArg (fun x : P'.X n ⟶ M' => a' ≫ x ≫ b') hFirst))
  have hAssoc : (a' ≫ a) ≫ k ≫ (b ≫ b') = a' ≫ (a ≫ k ≫ b) ≫ b' := by
    let k₀ : P.X n ⟶ M := k
    change (a' ≫ a) ≫ k₀ ≫ (b ≫ b') = a' ≫ (a ≫ k₀ ≫ b) ≫ b'
    have hFirst : (a' ≫ a) ≫ k₀ ≫ (b ≫ b') =
        a' ≫ (a ≫ k₀ ≫ (b ≫ b')) :=
      Category.assoc a' a (k₀ ≫ (b ≫ b'))
    have hMiddle : a' ≫ (a ≫ k₀ ≫ (b ≫ b')) =
        a' ≫ (a ≫ ((k₀ ≫ b) ≫ b')) :=
      congrArg (fun t : P.X n ⟶ M'' => a' ≫ a ≫ t)
        (Category.assoc k₀ b b').symm
    have hLast : a' ≫ (a ≫ ((k₀ ≫ b) ≫ b')) =
        a' ≫ (a ≫ k₀ ≫ b) ≫ b' :=
      congrArg (fun t : P'.X n ⟶ M'' => a' ≫ t)
        (Category.assoc a (k₀ ≫ b) b').symm
    exact hFirst.trans (hMiddle.trans hLast)
  exact hLeft.trans (hAssoc.trans hRight.symm)

end Preadditive

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual Hom of the homology complex has zero differential in every integer degree. -/
lemma homFixedCoefficient_homologyZeroComplex_d (P : ChainComplex C ℤ) (M : C) (i j : ℤ) :
    (homFixedCoefficient (homologyZeroComplex P) M).d i j = 0 := by
  apply AddCommGrpCat.ext
  intro f
  change (homologyZeroComplex P).d j i ≫ f = 0
  exact Limits.zero_comp

/-- Native cycle and homology quotient isos compute the actual zero-source Hom cohomology. -/
def homFixedCoefficientHomologyZeroIso (P : ChainComplex C ℤ) (M : C) (n : ℤ) :
    (homFixedCoefficient (homologyZeroComplex P) M).homology n ≅
      AddCommGrpCat.of (P.homology n ⟶ M) := by
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient (homologyZeroComplex P) M
  change K.homology n ≅ K.X n
  exact (K.isoHomologyπ ((ComplexShape.up ℤ).prev n) n rfl
    (homFixedCoefficient_homologyZeroComplex_d P M _ _)).symm ≪≫
      K.iCyclesIso n ((ComplexShape.up ℤ).next n) rfl
        (homFixedCoefficient_homologyZeroComplex_d P M _ _)

/-- The computed Hom cohomology comparison is the original cycle inclusion after the quotient. -/
@[reassoc]
lemma homFixedCoefficientHomologyZeroIso_π (P : ChainComplex C ℤ) (M : C) (n : ℤ) :
    (homFixedCoefficient (homologyZeroComplex P) M).homologyπ n ≫
        (homFixedCoefficientHomologyZeroIso P M n).hom =
      (homFixedCoefficient (homologyZeroComplex P) M).iCycles n := by
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient (homologyZeroComplex P) M
  let π : K.cycles n ⟶ K.homology n := K.homologyπ n
  let a : K.cycles n ≅ K.homology n :=
    K.isoHomologyπ ((ComplexShape.up ℤ).prev n) n rfl
      (homFixedCoefficient_homologyZeroComplex_d P M _ _)
  let e : K.cycles n ≅ K.X n :=
    K.iCyclesIso n ((ComplexShape.up ℤ).next n) rfl
      (homFixedCoefficient_homologyZeroComplex_d P M _ _)
  have ha : π ≫ a.inv = 𝟙 (K.cycles n) :=
    K.isoHomologyπ_hom_inv_id ((ComplexShape.up ℤ).prev n) n rfl
      (homFixedCoefficient_homologyZeroComplex_d P M _ _)
  change π ≫ (a.inv ≫ e.hom) = K.iCycles n
  exact (Category.assoc π a.inv e.hom).symm.trans
    ((congrArg (fun f : K.cycles n ⟶ K.cycles n => f ≫ e.hom) ha).trans
      (Category.id_comp e.hom))

/-- The zero-source comparison retains the actual original coefficient map. -/
lemma homFixedCoefficientHomologyZeroIso_naturality (P : ChainComplex C ℤ) {M M' : C}
    (b : M ⟶ M') (n : ℤ) :
    homologyMap (homFixedCoefficientMap (𝟙 (homologyZeroComplex P)) b) n ≫
        (homFixedCoefficientHomologyZeroIso P M' n).hom =
      (homFixedCoefficientHomologyZeroIso P M n).hom ≫
        (homFixedCoefficientMap (𝟙 (homologyZeroComplex P)) b).f n := by
  let Z : ChainComplex C ℤ := homologyZeroComplex P
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient Z M
  let L : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient Z M'
  let a : K ⟶ L := homFixedCoefficientMap (𝟙 Z) b
  let e : K.homology n ≅ K.X n := homFixedCoefficientHomologyZeroIso P M n
  let e' : L.homology n ≅ L.X n := homFixedCoefficientHomologyZeroIso P M' n
  let π : K.cycles n ⟶ K.homology n := K.homologyπ n
  let π' : L.cycles n ⟶ L.homology n := L.homologyπ n
  let z : K.cycles n ⟶ L.cycles n := cyclesMap a n
  let m : K.homology n ⟶ L.homology n := homologyMap a n
  let u : K.X n ⟶ L.X n := a.f n
  have hm : π ≫ m = z ≫ π' := homologyπ_naturality a n
  have he : π ≫ e.hom = K.iCycles n := homFixedCoefficientHomologyZeroIso_π P M n
  have he' : π' ≫ e'.hom = L.iCycles n := homFixedCoefficientHomologyZeroIso_π P M' n
  have hz : z ≫ L.iCycles n = K.iCycles n ≫ u := cyclesMap_i a n
  apply (cancel_epi π).1
  change π ≫ (m ≫ e'.hom) = π ≫ (e.hom ≫ u)
  calc
    _ = (π ≫ m) ≫ e'.hom := (Category.assoc π m e'.hom).symm
    _ = (z ≫ π') ≫ e'.hom := congrArg (fun f => f ≫ e'.hom) hm
    _ = z ≫ (π' ≫ e'.hom) := Category.assoc z π' e'.hom
    _ = z ≫ L.iCycles n := congrArg (fun f => z ≫ f) he'
    _ = K.iCycles n ≫ u := hz
    _ = (π ≫ e.hom) ≫ u := congrArg (fun f => f ≫ u) he.symm
    _ = π ≫ (e.hom ≫ u) := Category.assoc π e.hom u

/-- Outgoing-image projectivity lifts Hom on homology to actual fixed-coefficient cycles. -/
def homFixedCoefficientCycleLift (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p)))) :
    AddCommGrpCat.of (P.homology n ⟶ M) ⟶ (homFixedCoefficient P M).cycles n := by
  let Z : ChainComplex C ℤ := homologyZeroComplex P
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient Z M
  let q : P ⟶ Z := homologyProjection P hI
  let e : K.cycles n ≅ K.X n :=
    K.iCyclesIso n ((ComplexShape.up ℤ).next n) rfl
      (homFixedCoefficient_homologyZeroComplex_d P M _ _)
  exact e.inv ≫ cyclesMap (homFixedCoefficientMap q (𝟙 M)) n

/-- The native cycle inclusion gives precisely the actual Hom of the chosen projection. -/
@[reassoc]
lemma homFixedCoefficientCycleLift_i (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p)))) :
    homFixedCoefficientCycleLift P M n hI ≫ (homFixedCoefficient P M).iCycles n =
      (homFixedCoefficientMap (homologyProjection P hI) (𝟙 M)).f n := by
  let Z : ChainComplex C ℤ := homologyZeroComplex P
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient Z M
  let L : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let q : P ⟶ Z := homologyProjection P hI
  let a : K ⟶ L := homFixedCoefficientMap q (𝟙 M)
  let e : K.cycles n ≅ K.X n :=
    K.iCyclesIso n ((ComplexShape.up ℤ).next n) rfl
      (homFixedCoefficient_homologyZeroComplex_d P M _ _)
  have he : e.inv ≫ K.iCycles n = 𝟙 (K.X n) := e.inv_hom_id
  have ha : cyclesMap a n ≫ L.iCycles n = K.iCycles n ≫ a.f n := cyclesMap_i a n
  change (e.inv ≫ cyclesMap a n) ≫ L.iCycles n = a.f n
  calc
    _ = e.inv ≫ (cyclesMap a n ≫ L.iCycles n) := Category.assoc _ _ _
    _ = e.inv ≫ (K.iCycles n ≫ a.f n) := congrArg (fun f => e.inv ≫ f) ha
    _ = (e.inv ≫ K.iCycles n) ≫ a.f n := (Category.assoc _ _ _).symm
    _ = (𝟙 (K.X n)) ≫ a.f n := congrArg (fun f => f ≫ a.f n) he
    _ = a.f n := Category.id_comp _

/-- The representative is the original qₙ followed by the original morphism Hₙ(P)→M. -/
lemma homFixedCoefficientCycleLift_apply (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p))))
    (f : P.homology n ⟶ M) :
    ((homFixedCoefficient P M).iCycles n).hom
        ((homFixedCoefficientCycleLift P M n hI).hom f) =
      (homologyProjection P hI).f n ≫ f := by
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let q : P ⟶ homologyZeroComplex P := homologyProjection P hI
  let l : AddCommGrpCat.of (P.homology n ⟶ M) ⟶ K.cycles n :=
    homFixedCoefficientCycleLift P M n hI
  let a := (homFixedCoefficientMap q (𝟙 M)).f n
  have h : l ≫ K.iCycles n = a := homFixedCoefficientCycleLift_i P M n hI
  exact (AddCommGrpCat.comp_apply l (K.iCycles n) f).symm.trans
    ((ConcreteCategory.congr_hom h f).trans
      ((homFixedCoefficientMap_f_apply q (𝟙 M) n f).trans
        (congrArg (fun g : P.homology n ⟶ M => q.f n ≫ g) (Category.comp_id f))))

/-- The chosen image retractions construct the genuine cohomology class represented by qₙ≫f. -/
def homFixedCoefficientCohomologyLift (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p)))) :
    AddCommGrpCat.of (P.homology n ⟶ M) ⟶ (homFixedCoefficient P M).homology n :=
  homFixedCoefficientCycleLift P M n hI ≫ (homFixedCoefficient P M).homologyπ n

/-- This class is the actual cohomology map of Hom(q,M), after the computed zero-source iso. -/
lemma homFixedCoefficientCohomologyLift_eq (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p)))) :
    homFixedCoefficientCohomologyLift P M n hI =
      (homFixedCoefficientHomologyZeroIso P M n).inv ≫
        homologyMap (homFixedCoefficientMap (homologyProjection P hI) (𝟙 M)) n := by
  let Z : ChainComplex C ℤ := homologyZeroComplex P
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient Z M
  let L : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let q : P ⟶ Z := homologyProjection P hI
  let a : K ⟶ L := homFixedCoefficientMap q (𝟙 M)
  let e : K.cycles n ≅ K.X n :=
    K.iCyclesIso n ((ComplexShape.up ℤ).next n) rfl
      (homFixedCoefficient_homologyZeroComplex_d P M _ _)
  let h : K.homology n ≅ K.X n := homFixedCoefficientHomologyZeroIso P M n
  have hπ : K.homologyπ n ≫ h.hom = K.iCycles n :=
    homFixedCoefficientHomologyZeroIso_π P M n
  have hi : e.inv ≫ K.homologyπ n = h.inv := by
    apply (cancel_mono h.hom).1
    change (e.inv ≫ K.homologyπ n) ≫ h.hom = h.inv ≫ h.hom
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f : K.cycles n ⟶ K.X n => e.inv ≫ f) hπ).trans
        (e.inv_hom_id.trans h.inv_hom_id.symm))
  have ha : K.homologyπ n ≫ homologyMap a n = cyclesMap a n ≫ L.homologyπ n :=
    homologyπ_naturality a n
  change (e.inv ≫ cyclesMap a n) ≫ L.homologyπ n = h.inv ≫ homologyMap a n
  calc
    _ = e.inv ≫ (cyclesMap a n ≫ L.homologyπ n) := Category.assoc _ _ _
    _ = e.inv ≫ (K.homologyπ n ≫ homologyMap a n) :=
      congrArg (fun f => e.inv ≫ f) ha.symm
    _ = (e.inv ≫ K.homologyπ n) ≫ homologyMap a n := (Category.assoc _ _ _).symm
    _ = h.inv ≫ homologyMap a n := congrArg (fun f => f ≫ homologyMap a n) hi

/-- The constructed class is natural in M for the same fixed choice of the original q. -/
lemma homFixedCoefficientCohomologyLift_naturality (P : ChainComplex C ℤ) {M M' : C}
    (b : M ⟶ M') (n : ℤ)
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p)))) :
    (homFixedCoefficientMap (𝟙 (homologyZeroComplex P)) b).f n ≫
        homFixedCoefficientCohomologyLift P M' n hI =
      homFixedCoefficientCohomologyLift P M n hI ≫
        homologyMap (homFixedCoefficientMap (𝟙 P) b) n := by
  let Z : ChainComplex C ℤ := homologyZeroComplex P
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient Z M
  let K' : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient Z M'
  let L : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let L' : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M'
  let q : P ⟶ Z := homologyProjection P hI
  let a : K ⟶ L := homFixedCoefficientMap q (𝟙 M)
  let a' : K' ⟶ L' := homFixedCoefficientMap q (𝟙 M')
  let z : K ⟶ K' := homFixedCoefficientMap (𝟙 Z) b
  let l : L ⟶ L' := homFixedCoefficientMap (𝟙 P) b
  let e : K.homology n ≅ K.X n := homFixedCoefficientHomologyZeroIso P M n
  let e' : K'.homology n ≅ K'.X n := homFixedCoefficientHomologyZeroIso P M' n
  let u : K.X n ⟶ K'.X n := z.f n
  let m : K.homology n ⟶ K'.homology n := homologyMap z n
  let v : K.homology n ⟶ L.homology n := homologyMap a n
  let v' : K'.homology n ⟶ L'.homology n := homologyMap a' n
  let t : L.homology n ⟶ L'.homology n := homologyMap l n
  have hMaps : z ≫ a' = a ≫ l := by
    have hLeft : z ≫ a' = homFixedCoefficientMap q b :=
      (homFixedCoefficientMap_comp (𝟙 Z) q b (𝟙 M')).symm.trans
        (congrArg₂ (fun (f : P ⟶ Z) (g : M ⟶ M') => homFixedCoefficientMap f g)
          (Category.comp_id q) (Category.comp_id b))
    have hRight : a ≫ l = homFixedCoefficientMap q b :=
      (homFixedCoefficientMap_comp q (𝟙 P) (𝟙 M) b).symm.trans
        (congrArg₂ (fun (f : P ⟶ Z) (g : M ⟶ M') => homFixedCoefficientMap f g)
          (Category.id_comp q) (Category.id_comp b))
    exact hLeft.trans hRight.symm
  have hm : m ≫ v' = v ≫ t :=
    (homologyMap_comp z a' n).symm.trans
      ((congrArg (fun f : K ⟶ L' => homologyMap f n) hMaps).trans
        (homologyMap_comp a l n))
  have he : m ≫ e'.hom = e.hom ≫ u :=
    homFixedCoefficientHomologyZeroIso_naturality P b n
  have hi : u ≫ e'.inv = e.inv ≫ m := by
    apply (cancel_mono e'.hom).1
    have hLeft : (u ≫ e'.inv) ≫ e'.hom = u :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun f : K'.X n ⟶ K'.X n => u ≫ f) e'.inv_hom_id).trans
          (Category.comp_id u))
    have hRight : (e.inv ≫ m) ≫ e'.hom = u :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun f : K.homology n ⟶ K'.X n => e.inv ≫ f) he).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun f : K.X n ⟶ K.X n => f ≫ u) e.inv_hom_id).trans
              (Category.id_comp u))))
    exact hLeft.trans hRight.symm
  have hLift : homFixedCoefficientCohomologyLift P M n hI = e.inv ≫ v :=
    homFixedCoefficientCohomologyLift_eq P M n hI
  have hLift' : homFixedCoefficientCohomologyLift P M' n hI = e'.inv ≫ v' :=
    homFixedCoefficientCohomologyLift_eq P M' n hI
  let r : K.X n ⟶ L.homology n := homFixedCoefficientCohomologyLift P M n hI
  let r' : K'.X n ⟶ L'.homology n := homFixedCoefficientCohomologyLift P M' n hI
  change u ≫ r' = r ≫ t
  have hFirst : u ≫ r' = u ≫ (e'.inv ≫ v') :=
    congrArg (fun f : K'.X n ⟶ L'.homology n => u ≫ f) hLift'
  have hAssoc₁ : u ≫ (e'.inv ≫ v') = (u ≫ e'.inv) ≫ v' :=
    (Category.assoc u e'.inv v').symm
  have hMap : (u ≫ e'.inv) ≫ v' = (e.inv ≫ m) ≫ v' :=
    congrArg (fun f : K.X n ⟶ K'.homology n => f ≫ v') hi
  have hAssoc₂ : (e.inv ≫ m) ≫ v' = e.inv ≫ (m ≫ v') :=
    Category.assoc e.inv m v'
  have hSquare : e.inv ≫ (m ≫ v') = e.inv ≫ (v ≫ t) :=
    congrArg (fun f : K.homology n ⟶ L'.homology n => e.inv ≫ f) hm
  have hAssoc₃ : e.inv ≫ (v ≫ t) = (e.inv ≫ v) ≫ t :=
    (Category.assoc e.inv v t).symm
  have hLast : (e.inv ≫ v) ≫ t = r ≫ t :=
    congrArg (fun f : K.X n ⟶ L.homology n => f ≫ t) hLift.symm
  exact hFirst.trans (hAssoc₁.trans (hMap.trans
    (hAssoc₂.trans (hSquare.trans (hAssoc₃.trans hLast)))))

/-- The actual target single has native homology M in the earned degree-zero coordinate. -/
def homFixedCoefficientTargetHomologyIso (M : C) (i : ℤ) (hi : i = 0) :
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).homology i ≅ M :=
  eqToIso (congrArg
    (fun j : ℤ => ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).homology j) hi) ≪≫
      HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M

/-- Its degree transport retains the original native coefficient homology map. -/
lemma homFixedCoefficientTargetHomologyIso_naturality {M M' : C} (b : M ⟶ M')
    (i : ℤ) (hi : i = 0) :
    homologyMap ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b) i ≫
        (homFixedCoefficientTargetHomologyIso M' i hi).hom =
      (homFixedCoefficientTargetHomologyIso M i hi).hom ≫ b := by
  subst i
  simp only [homFixedCoefficientTargetHomologyIso, eqToIso_refl, Iso.trans_hom,
    Iso.refl_hom, Category.id_comp]
  exact HomologicalComplex.singleObjHomologySelfIso_hom_naturality (ComplexShape.up ℤ) 0 b

/-- The target homology quotient agrees with actual evaluation on its native degree-zero cycle. -/
@[reassoc]
lemma homFixedCoefficientTargetHomologyIso_π (M : C) (i : ℤ) (hi : i = 0) :
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).homologyπ i ≫
        (homFixedCoefficientTargetHomologyIso M i hi).hom =
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).iCycles i ≫
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M i hi).hom := by
  subst i
  simp only [homFixedCoefficientTargetHomologyIso, eqToIso_refl, Iso.trans_hom,
    Iso.refl_hom, Category.id_comp]
  exact (HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom
    (ComplexShape.up ℤ) 0 M).trans
      (HomologicalComplex.singleObjCyclesSelfIso_hom (ComplexShape.up ℤ) 0 M)

/-- The full Hom product has one surviving factor because the actual target single is exact
away from zero. No support restriction on the original integer complex is imposed. -/
def homFixedCoefficientHomologyProductEquiv (P : ChainComplex C ℤ) (M : C) (n : ℤ) :
    (∀ p : ℤ, P.homology p ⟶
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).homology (n - p)) ≃+
        (P.homology n ⟶ M) := by
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let e : Q.homology (n - n) ≅ M :=
    homFixedCoefficientTargetHomologyIso M (n - n) (by omega)
  exact
    { toFun f := f n ≫ e.hom
      invFun k p := if hp : p = n then by
          subst p
          exact k ≫ e.inv
        else 0
      left_inv f := by
        funext p
        dsimp only
        by_cases hp : p = n
        · subst p
          rw [dif_pos rfl]
          change (f n ≫ e.hom) ≫ e.inv = f n
          exact (Category.assoc (f n) e.hom e.inv).trans
            ((congrArg (fun a : Q.homology (n - n) ⟶ Q.homology (n - n) => f n ≫ a)
              e.hom_inv_id).trans (Category.comp_id (f n)))
        · rw [dif_neg hp]
          exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M
            (n - p) (by omega)).eq_of_tgt _ _
      right_inv k := by
        dsimp only
        rw [dif_pos rfl]
        change (k ≫ e.inv) ≫ e.hom = k
        exact (Category.assoc k e.inv e.hom).trans
          ((congrArg (fun a : M ⟶ M => k ≫ a) e.inv_hom_id).trans (Category.comp_id k))
      map_add' f g := by
        change (f n + g n) ≫ e.hom = f n ≫ e.hom + g n ≫ e.hom
        exact Preadditive.add_comp (P.homology n) (Q.homology (n - n)) M
          (f n) (g n) e.hom }

/-- The ordinary Hom endpoint evaluates the actual physical source degree n. -/
lemma homFixedCoefficientHomologyProductEquiv_apply (P : ChainComplex C ℤ) (M : C)
    (n : ℤ)
    (f : ∀ p : ℤ, P.homology p ⟶
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).homology (n - p)) :
    homFixedCoefficientHomologyProductEquiv P M n f = f n ≫
      (homFixedCoefficientTargetHomologyIso M (n - n) (by omega)).hom := rfl

/-- The endpoint collapse retains both the original contravariant P map and the coefficient map. -/
lemma homFixedCoefficientHomologyProductEquiv_naturality {P P' : ChainComplex C ℤ}
    {M M' : C} (f : P' ⟶ P) (b : M ⟶ M') (n : ℤ)
    (z : ∀ p : ℤ, P.homology p ⟶
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).homology (n - p)) :
    homFixedCoefficientHomologyProductEquiv P' M' n
        (fun p => homologyMap f p ≫ z p ≫
          homologyMap ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b) (n - p)) =
      homologyMap f n ≫ homFixedCoefficientHomologyProductEquiv P M n z ≫ b := by
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let Q' : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M'
  let e : Q.homology (n - n) ≅ M :=
    homFixedCoefficientTargetHomologyIso M (n - n) (by omega)
  let e' : Q'.homology (n - n) ≅ M' :=
    homFixedCoefficientTargetHomologyIso M' (n - n) (by omega)
  let a : P'.homology n ⟶ P.homology n := homologyMap f n
  let v : P.homology n ⟶ Q.homology (n - n) := z n
  let t : Q.homology (n - n) ⟶ Q'.homology (n - n) :=
    homologyMap ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b) (n - n)
  have ht : t ≫ e'.hom = e.hom ≫ b :=
    homFixedCoefficientTargetHomologyIso_naturality b (n - n) (by omega)
  change (a ≫ v ≫ t) ≫ e'.hom = a ≫ (v ≫ e.hom) ≫ b
  exact (Category.assoc a (v ≫ t) e'.hom).trans
    (congrArg (fun x : P.homology n ⟶ M' => a ≫ x)
      ((Category.assoc v t e'.hom).trans
        ((congrArg (fun x : Q.homology (n - n) ⟶ M' => v ≫ x) ht).trans
          (Category.assoc v e.hom b).symm)))

end Abelian

section Restriction

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A fixed-coefficient cocycle restricts to a map on P's cycles that kills its true boundaries. -/
lemma toCycles_homFixedCoefficientCycleValue (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    [P.HasHomology n] (z : (homFixedCoefficient P M).cycles n) :
    (P.sc n).toCycles ≫ (P.iCycles n ≫ ((homFixedCoefficient P M).iCycles n).hom z) = 0 := by
  let S : ShortComplex C := P.sc n
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let j : ℤ := (ComplexShape.down ℤ).prev n
  let ι : K.cycles n ⟶ K.X n := K.iCycles n
  let d : K.X n ⟶ K.X j := K.d n j
  let f : P.X n ⟶ M := ι.hom z
  have hz : d.hom f = 0 :=
    (AddCommGrpCat.comp_apply ι d z).symm.trans
      ((ConcreteCategory.congr_hom (K.iCycles_d n j) z).trans
        (show (0 : K.cycles n ⟶ K.X j).hom z = 0 from rfl))
  have hf : S.f ≫ f = 0 := (homFixedCoefficient_d_apply P M n j f).symm.trans hz
  have hi : S.toCycles ≫ S.iCycles = S.f := S.toCycles_i
  change S.toCycles ≫ (S.iCycles ≫ f) = 0
  exact (Category.assoc S.toCycles S.iCycles f).symm.trans
    ((congrArg (fun a : S.X₁ ⟶ S.X₂ => a ≫ f) hi).trans hf)

/-- Native homology descent constructs the cycle-level restriction with no projectivity premise. -/
def homFixedCoefficientCycleRestriction (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    [P.HasHomology n] :
    (homFixedCoefficient P M).cycles n ⟶ AddCommGrpCat.of (P.homology n ⟶ M) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun z => (P.sc n).descHomology
      (P.iCycles n ≫ ((homFixedCoefficient P M).iCycles n).hom z)
      (toCycles_homFixedCoefficientCycleValue P M n z)) (by
    intro z z'
    let S : ShortComplex C := P.sc n
    let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
    let c : K.cycles n →+ (S.cycles ⟶ M) :=
      (Preadditive.compHom S.iCycles).comp (K.iCycles n).hom
    let r (w : K.cycles n) : S.homology ⟶ M :=
      S.descHomology (c w) (toCycles_homFixedCoefficientCycleValue P M n w)
    have hLeft : S.homologyπ ≫ r (z + z') = c (z + z') := S.π_descHomology _ _
    have hRight : S.homologyπ ≫ (r z + r z') = c z + c z' :=
      (Preadditive.comp_add S.cycles S.homology M S.homologyπ (r z) (r z')).trans
        (congrArg₂ (fun f g : S.cycles ⟶ M => f + g)
          (S.π_descHomology _ _) (S.π_descHomology _ _))
    apply (cancel_epi S.homologyπ).1
    change S.homologyπ ≫ r (z + z') = S.homologyπ ≫ (r z + r z')
    exact hLeft.trans ((c.map_add z z').trans hRight.symm)))

/-- Its homology representative is the original cycle restriction in C. -/
@[reassoc]
lemma homFixedCoefficientCycleRestriction_π (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    [P.HasHomology n] (z : (homFixedCoefficient P M).cycles n) :
    P.homologyπ n ≫ (homFixedCoefficientCycleRestriction P M n).hom z =
      P.iCycles n ≫ ((homFixedCoefficient P M).iCycles n).hom z := by
  let S : ShortComplex C := P.sc n
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let f : P.X n ⟶ M := (K.iCycles n).hom z
  change S.homologyπ ≫ S.descHomology (S.iCycles ≫ f)
    (toCycles_homFixedCoefficientCycleValue P M n z) = S.iCycles ≫ f
  exact S.π_descHomology _ _

/-- An actual fixed-Hom coboundary restricts to zero on homology, without a projectivity premise. -/
@[reassoc]
lemma toCycles_homFixedCoefficientCycleRestriction (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    [P.HasHomology n] :
    ((homFixedCoefficient P M).sc n).toCycles ≫
      homFixedCoefficientCycleRestriction P M n = 0 := by
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let T : ShortComplex AddCommGrpCat.{v} := K.sc n
  let j : ℤ := (ComplexShape.up ℤ).prev n
  let b : T.X₁ ⟶ T.cycles := T.toCycles
  let ι : T.cycles ⟶ T.X₂ := T.iCycles
  let r : T.cycles ⟶ AddCommGrpCat.of (P.homology n ⟶ M) :=
    homFixedCoefficientCycleRestriction P M n
  have hb : b ≫ ι = T.f := T.toCycles_i
  apply AddCommGrpCat.ext
  intro z
  let z₀ : P.X j ⟶ M := z
  let γ : K.cycles n := b.hom z
  let f : P.X n ⟶ M := ι.hom γ
  have hValue : f = P.d n j ≫ z₀ :=
    (AddCommGrpCat.comp_apply b ι z).symm.trans
      ((ConcreteCategory.congr_hom hb z).trans (homFixedCoefficient_d_apply P M j n z₀))
  have hZero : P.iCycles n ≫ f = 0 :=
    (congrArg (fun g : P.X n ⟶ M => P.iCycles n ≫ g) hValue).trans
      ((Category.assoc (P.iCycles n) (P.d n j) z₀).symm.trans
        ((congrArg (fun g : P.cycles n ⟶ P.X j => g ≫ z₀) (P.iCycles_d n j)).trans
          Limits.zero_comp))
  have hr : r.hom γ = 0 := by
    apply (cancel_epi (P.homologyπ n)).1
    exact (homFixedCoefficientCycleRestriction_π P M n γ).trans
      (hZero.trans (Limits.comp_zero (f := P.homologyπ n)).symm)
  change (b ≫ r).hom z = 0
  exact (AddCommGrpCat.comp_apply b r z).trans hr

/-- Native homology descent gives the canonical right restriction on Hom cohomology. -/
def homFixedCoefficientRestriction (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    [P.HasHomology n] :
    (homFixedCoefficient P M).homology n ⟶ AddCommGrpCat.of (P.homology n ⟶ M) :=
  ((homFixedCoefficient P M).sc n).descHomology
    (homFixedCoefficientCycleRestriction P M n)
    (toCycles_homFixedCoefficientCycleRestriction P M n)

/-- The actual canonical restriction on cohomology has the original cycle representative. -/
@[reassoc]
lemma homologyπ_homFixedCoefficientRestriction (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    [P.HasHomology n] :
    (homFixedCoefficient P M).homologyπ n ≫ homFixedCoefficientRestriction P M n =
      homFixedCoefficientCycleRestriction P M n :=
  ((homFixedCoefficient P M).sc n).π_descHomology _ _

private lemma homFixedCoefficientCycleRestriction_naturality {P P' : ChainComplex C ℤ}
    {M M' : C} (f : P' ⟶ P) (b : M ⟶ M') (n : ℤ)
    [P.HasHomology n] [P'.HasHomology n] :
    cyclesMap (homFixedCoefficientMap f b) n ≫ homFixedCoefficientCycleRestriction P' M' n =
      homFixedCoefficientCycleRestriction P M n ≫
        ((preadditiveYoneda.obj M).map (homologyMap f n).op ≫
          (preadditiveYoneda.map b).app (op (P'.homology n))) := by
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let K' : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P' M'
  let a : K ⟶ K' := homFixedCoefficientMap f b
  let c : K.cycles n ⟶ K'.cycles n := cyclesMap a n
  let r : K.cycles n ⟶ AddCommGrpCat.of (P.homology n ⟶ M) :=
    homFixedCoefficientCycleRestriction P M n
  let r' : K'.cycles n ⟶ AddCommGrpCat.of (P'.homology n ⟶ M') :=
    homFixedCoefficientCycleRestriction P' M' n
  let t : AddCommGrpCat.of (P.homology n ⟶ M) ⟶
      AddCommGrpCat.of (P'.homology n ⟶ M') :=
    (preadditiveYoneda.obj M).map (homologyMap f n).op ≫
      (preadditiveYoneda.map b).app (op (P'.homology n))
  have hC : c ≫ K'.iCycles n = K.iCycles n ≫ a.f n := cyclesMap_i a n
  apply AddCommGrpCat.ext
  intro z
  let γ : K'.cycles n := c.hom z
  let v : P.X n ⟶ M := (K.iCycles n).hom z
  let v' : P'.X n ⟶ M' := (K'.iCycles n).hom γ
  let i : P.cycles n ⟶ P.X n := P.iCycles n
  let i' : P'.cycles n ⟶ P'.X n := P'.iCycles n
  let π : P.cycles n ⟶ P.homology n := P.homologyπ n
  let π' : P'.cycles n ⟶ P'.homology n := P'.homologyπ n
  let d : P'.homology n ⟶ P.homology n := homologyMap f n
  let k : P'.cycles n ⟶ P.cycles n := cyclesMap f n
  let x : P.homology n ⟶ M := r.hom z
  let x' : P'.homology n ⟶ M' := r'.hom γ
  have hv : v' = (f.f n ≫ v) ≫ b :=
    (AddCommGrpCat.comp_apply c (K'.iCycles n) z).symm.trans
      ((ConcreteCategory.congr_hom hC z).trans
        ((AddCommGrpCat.comp_apply (K.iCycles n) (a.f n) z).trans
          ((homFixedCoefficientMap_f_apply f b n v).trans (Category.assoc (f.f n) v b).symm)))
  have hi : k ≫ i = i' ≫ f.f n := cyclesMap_i f n
  have hπ : π' ≫ d = k ≫ π := homologyπ_naturality f n
  have hx : π ≫ x = i ≫ v := homFixedCoefficientCycleRestriction_π P M n z
  have hx' : π' ≫ x' = i' ≫ v' := homFixedCoefficientCycleRestriction_π P' M' n γ
  have hValue : x' = t.hom x := by
    apply (cancel_epi π').1
    have ht : t.hom x = (d ≫ x) ≫ b := rfl
    change π' ≫ x' = π' ≫ t.hom x
    calc
      _ = i' ≫ v' := hx'
      _ = i' ≫ ((f.f n ≫ v) ≫ b) := congrArg (fun w => i' ≫ w) hv
      _ = (i' ≫ f.f n) ≫ v ≫ b := by simp only [Category.assoc]
      _ = (k ≫ i) ≫ v ≫ b := congrArg (fun w => w ≫ v ≫ b) hi.symm
      _ = k ≫ (i ≫ v) ≫ b := by simp only [Category.assoc]
      _ = k ≫ (π ≫ x) ≫ b := congrArg (fun w => k ≫ w ≫ b) hx.symm
      _ = (k ≫ π) ≫ x ≫ b := by simp only [Category.assoc]
      _ = (π' ≫ d) ≫ x ≫ b := congrArg (fun w => w ≫ x ≫ b) hπ.symm
      _ = π' ≫ ((d ≫ x) ≫ b) := by simp only [Category.assoc]
      _ = π' ≫ t.hom x := congrArg (fun w => π' ≫ w) ht.symm
  change (c ≫ r').hom z = (r ≫ t).hom z
  exact (AddCommGrpCat.comp_apply c r' z).trans
    (hValue.trans (AddCommGrpCat.comp_apply r t z).symm)

/-- The canonical cohomology restriction is natural in both original variables, without
projectivity assumptions on P or its homology. -/
lemma homFixedCoefficientRestriction_naturality {P P' : ChainComplex C ℤ} {M M' : C}
    (f : P' ⟶ P) (b : M ⟶ M') (n : ℤ) [P.HasHomology n] [P'.HasHomology n] :
    homologyMap (homFixedCoefficientMap f b) n ≫ homFixedCoefficientRestriction P' M' n =
      homFixedCoefficientRestriction P M n ≫
        ((preadditiveYoneda.obj M).map (homologyMap f n).op ≫
          (preadditiveYoneda.map b).app (op (P'.homology n))) := by
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let K' : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P' M'
  let a : K ⟶ K' := homFixedCoefficientMap f b
  let c : K.cycles n ⟶ K'.cycles n := cyclesMap a n
  let m : K.homology n ⟶ K'.homology n := homologyMap a n
  let π : K.cycles n ⟶ K.homology n := K.homologyπ n
  let π' : K'.cycles n ⟶ K'.homology n := K'.homologyπ n
  let r : K.cycles n ⟶ AddCommGrpCat.of (P.homology n ⟶ M) :=
    homFixedCoefficientCycleRestriction P M n
  let r' : K'.cycles n ⟶ AddCommGrpCat.of (P'.homology n ⟶ M') :=
    homFixedCoefficientCycleRestriction P' M' n
  let g : K.homology n ⟶ AddCommGrpCat.of (P.homology n ⟶ M) :=
    homFixedCoefficientRestriction P M n
  let g' : K'.homology n ⟶ AddCommGrpCat.of (P'.homology n ⟶ M') :=
    homFixedCoefficientRestriction P' M' n
  let t : AddCommGrpCat.of (P.homology n ⟶ M) ⟶
      AddCommGrpCat.of (P'.homology n ⟶ M') :=
    (preadditiveYoneda.obj M).map (homologyMap f n).op ≫
      (preadditiveYoneda.map b).app (op (P'.homology n))
  have hm : π ≫ m = c ≫ π' := homologyπ_naturality a n
  have hg : π ≫ g = r := homologyπ_homFixedCoefficientRestriction P M n
  have hg' : π' ≫ g' = r' := homologyπ_homFixedCoefficientRestriction P' M' n
  have hCycle : c ≫ r' = r ≫ t := homFixedCoefficientCycleRestriction_naturality f b n
  apply (cancel_epi π).1
  change π ≫ (m ≫ g') = π ≫ (g ≫ t)
  calc
    _ = (π ≫ m) ≫ g' := (Category.assoc _ _ _).symm
    _ = (c ≫ π') ≫ g' := congrArg (fun w => w ≫ g') hm
    _ = c ≫ (π' ≫ g') := Category.assoc _ _ _
    _ = c ≫ r' := congrArg (fun w => c ≫ w) hg'
    _ = r ≫ t := hCycle
    _ = (π ≫ g) ≫ t := congrArg (fun w => w ≫ t) hg.symm
    _ = π ≫ (g ≫ t) := Category.assoc _ _ _

end Restriction

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The chosen image-projective lift is a genuine section of the canonical right map. -/
lemma homFixedCoefficientCohomologyLift_restriction (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p)))) :
    homFixedCoefficientCohomologyLift P M n hI ≫ homFixedCoefficientRestriction P M n =
      𝟙 (AddCommGrpCat.of (P.homology n ⟶ M)) := by
  let A : AddCommGrpCat.{v} := AddCommGrpCat.of (P.homology n ⟶ M)
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let l : A ⟶ K.cycles n := homFixedCoefficientCycleLift P M n hI
  let r : K.cycles n ⟶ A := homFixedCoefficientCycleRestriction P M n
  let π : K.cycles n ⟶ K.homology n := K.homologyπ n
  let s : A ⟶ K.homology n := homFixedCoefficientCohomologyLift P M n hI
  let g : K.homology n ⟶ A := homFixedCoefficientRestriction P M n
  let q : P ⟶ homologyZeroComplex P := homologyProjection P hI
  have hg : π ≫ g = r := homologyπ_homFixedCoefficientRestriction P M n
  have hMap : s ≫ g = l ≫ r :=
    (Category.assoc l π g).trans (congrArg (fun f => l ≫ f) hg)
  have hId : l ≫ r = 𝟙 A := by
    apply AddCommGrpCat.ext
    intro f
    let γ : K.cycles n := l.hom f
    have hCycle : (K.iCycles n).hom γ = q.f n ≫ f :=
      homFixedCoefficientCycleLift_apply P M n hI f
    have hr : r.hom γ = f := by
      apply (cancel_epi (P.homologyπ n)).1
      have hπ : P.homologyπ n ≫ r.hom γ = P.iCycles n ≫ (K.iCycles n).hom γ :=
        homFixedCoefficientCycleRestriction_π P M n γ
      exact hπ.trans
        ((congrArg (fun a : P.X n ⟶ M => P.iCycles n ≫ a) hCycle).trans
          ((Category.assoc (P.iCycles n) (q.f n) f).symm.trans
            (congrArg (fun a : P.cycles n ⟶ P.homology n => a ≫ f)
              (iCycles_homologyProjection_f P hI n))))
    change (l ≫ r).hom f = f
    exact (AddCommGrpCat.comp_apply l r f).trans hr
  change s ≫ g = 𝟙 A
  exact hMap.trans hId

/-- The actual full-Hom cycle restriction, followed by native target-single homology evaluation. -/
def homFixedCoefficientCyclesComparison (P : ChainComplex C ℤ) (M : C) (n : ℤ) :
    (homCochainComplex P
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)).homology n ⟶
        AddCommGrpCat.of (P.cycles n ⟶ M) :=
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let Z : ChainComplex C ℤ := cyclesZeroComplex P
  let e : Q.homology (n - n) ≅ M :=
    homFixedCoefficientTargetHomologyIso M (n - n) (by omega)
  HomologicalComplex.homologyMap (homCyclesSequence P Q).g n ≫
    homZeroSourceCohomologyComparison Z Q n (by intro i j; rfl) ≫
      AddCommGrpCat.ofHom
        (Pi.evalAddMonoidHom (fun p : ℤ => Z.X p ⟶ Q.homology (n - p)) n) ≫
          (preadditiveCoyoneda.obj (op (P.cycles n))).map e.hom

private lemma homFixedCoefficientCyclesValue (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (z : (homCochainComplex P
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)).cycles n) :
    (homZeroSourceCycleComponent (cyclesZeroComplex P)
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) n
      (by intro i j; rfl)
      ((HomologicalComplex.cyclesMap (homCyclesSequence P
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)).g n).hom z) n ≫
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).homologyπ (n - n)) ≫
          (homFixedCoefficientTargetHomologyIso M (n - n) (by omega)).hom =
      P.iCycles n ≫ ((homFixedCoefficient P M).iCycles n).hom
        ((HomologicalComplex.cyclesMap (homFixedCoefficientIso P M).hom n).hom z) := by
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let Z : ChainComplex C ℤ := cyclesZeroComplex P
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P Q
  let L : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex Z Q
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let g : H ⟶ L := (homCyclesSequence P Q).g
  let e : H ≅ K := homFixedCoefficientIso P M
  let a : H.cycles n ⟶ L.cycles n := HomologicalComplex.cyclesMap g n
  let b : H.cycles n ⟶ K.cycles n := HomologicalComplex.cyclesMap e.hom n
  let zL : L.cycles n := a.hom z
  let zK : K.cycles n := b.hom z
  let γ : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n := (H.iCycles n).hom z
  let γL : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj Z) Q n := (L.iCycles n).hom zL
  let κ : P.cycles n ⟶ Q.cycles (n - n) :=
    homZeroSourceCycleComponent Z Q n (by intro i j; rfl) zL n
  let v : P.X n ⟶ Q.X (n - n) := homCochainComponent P Q n γ n
  let φ : P.X n ⟶ M := (K.iCycles n).hom zK
  let eH : Q.homology (n - n) ≅ M :=
    homFixedCoefficientTargetHomologyIso M (n - n) (by omega)
  let eX : Q.X (n - n) ≅ M :=
    HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M (n - n) (by omega)
  have hγL : γL = (g.f n).hom γ :=
    (AddCommGrpCat.comp_apply a (L.iCycles n) z).symm.trans
      ((ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i g n) z).trans
        (AddCommGrpCat.comp_apply (H.iCycles n) (g.f n) z))
  let iP : Z ⟶ P := (cyclesComplexInclusion (C := C) (c := ComplexShape.down ℤ)).app P
  have hg : g = homCochainComplexMap iP (𝟙 Q) := rfl
  have hγMap : γL = ((homCochainComplexMap iP (𝟙 Q)).f n).hom γ :=
    hγL.trans (congrArg (fun t : H ⟶ L => (t.f n).hom γ) hg)
  have hI : iP.f n = P.iCycles n := rfl
  have hId : (𝟙 Q : Q ⟶ Q).f (n - n) = 𝟙 (Q.X (n - n)) := rfl
  have hPost : iP.f n ≫ v ≫ (𝟙 Q : Q ⟶ Q).f (n - n) = P.iCycles n ≫ v :=
    (congrArg₂ (fun s t => s ≫ v ≫ t) hI hId).trans
      (congrArg (fun t : P.X n ⟶ Q.X (n - n) => P.iCycles n ≫ t)
        (Category.comp_id v))
  have hPhysical : homCochainComponent Z Q n γL n = P.iCycles n ≫ v :=
    (congrArg (fun η : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj Z) Q n =>
        homCochainComponent Z Q n η n) hγMap).trans
          ((homCochainComponent_map iP (𝟙 Q) n n γ).trans hPost)
  have hκ : κ ≫ Q.iCycles (n - n) = homCochainComponent Z Q n γL n :=
    homZeroSourceCycleComponent_i Z Q n (by intro i j; rfl) zL n
  have hφ : φ = v ≫ eX.hom :=
    ((AddCommGrpCat.comp_apply b (K.iCycles n) z).symm.trans
      ((ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i e.hom n) z).trans
        (AddCommGrpCat.comp_apply (H.iCycles n) (e.hom.f n) z))).trans
          ((homFixedCoefficientIso_hom_f_apply P M n γ).trans
            (homFixedCoefficientCochainEquiv_apply P M n γ))
  have hπ : Q.homologyπ (n - n) ≫ eH.hom = Q.iCycles (n - n) ≫ eX.hom :=
    homFixedCoefficientTargetHomologyIso_π M (n - n) (by omega)
  change (κ ≫ Q.homologyπ (n - n)) ≫ eH.hom = P.iCycles n ≫ φ
  exact (Category.assoc κ (Q.homologyπ (n - n)) eH.hom).trans
    ((congrArg (fun t : Q.cycles (n - n) ⟶ M => κ ≫ t) hπ).trans
      ((Category.assoc κ (Q.iCycles (n - n)) eX.hom).symm.trans
        ((congrArg (fun t : P.cycles n ⟶ Q.X (n - n) => t ≫ eX.hom) hκ).trans
          ((congrArg (fun t : P.cycles n ⟶ Q.X (n - n) => t ≫ eX.hom) hPhysical).trans
            ((Category.assoc (P.iCycles n) v eX.hom).trans
              (congrArg (fun t : P.X n ⟶ M => P.iCycles n ≫ t) hφ.symm))))))

/-- The genuine cycle comparison differs from canonical restriction by the native triangular unit.
This is a map identity for arbitrary P; projectivity is needed only in subsequent exactness. -/
lemma homFixedCoefficientCyclesComparison_eq (P : ChainComplex C ℤ) (M : C) (n : ℤ) :
    homFixedCoefficientCyclesComparison P M n =
      HomologicalComplex.homologyMap (homFixedCoefficientIso P M).hom n ≫
        homFixedCoefficientRestriction P M n ≫
          (preadditiveYoneda.obj M).map (P.homologyπ n).op ≫
            (DistribMulAction.toAddEquiv (AddCommGrpCat.of (P.cycles n ⟶ M))
              (Int.triangularSign n)).toAddCommGrpIso.hom := by
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let Z : ChainComplex C ℤ := cyclesZeroComplex P
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P Q
  let L : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex Z Q
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let A : AddCommGrpCat.{v} := AddCommGrpCat.of (P.homology n ⟶ M)
  let B : AddCommGrpCat.{v} := AddCommGrpCat.of (P.cycles n ⟶ M)
  let T : AddCommGrpCat.{v} :=
    AddCommGrpCat.of (∀ p : ℤ, Z.X p ⟶ Q.homology (n - p))
  let V : AddCommGrpCat.{v} := AddCommGrpCat.of (P.cycles n ⟶ Q.homology (n - n))
  let g : H ⟶ L := (homCyclesSequence P Q).g
  let e : H ≅ K := homFixedCoefficientIso P M
  let m : H.homology n ⟶ L.homology n := HomologicalComplex.homologyMap g n
  let c : L.homology n ⟶ T :=
    homZeroSourceCohomologyComparison Z Q n (by intro i j; rfl)
  let ev : T ⟶ V := AddCommGrpCat.ofHom
    (Pi.evalAddMonoidHom (fun p : ℤ => Z.X p ⟶ Q.homology (n - p)) n)
  let eH : Q.homology (n - n) ≅ M :=
    homFixedCoefficientTargetHomologyIso M (n - n) (by omega)
  let q : V ⟶ B := (preadditiveCoyoneda.obj (op (P.cycles n))).map eH.hom
  let h : H.homology n ⟶ K.homology n := HomologicalComplex.homologyMap e.hom n
  let r : K.homology n ⟶ A := homFixedCoefficientRestriction P M n
  let a : A ⟶ B := (preadditiveYoneda.obj M).map (P.homologyπ n).op
  let θ : B ≅ B :=
    (DistribMulAction.toAddEquiv B (Int.triangularSign n)).toAddCommGrpIso
  let π : H.cycles n ⟶ H.homology n := H.homologyπ n
  apply (cancel_epi π).1
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  let zL : L.cycles n := (HomologicalComplex.cyclesMap g n).hom z
  let zK : K.cycles n := (HomologicalComplex.cyclesMap e.hom n).hom z
  let φ : P.X n ⟶ M := (K.iCycles n).hom zK
  let κ : P.cycles n ⟶ Q.cycles (n - n) :=
    homZeroSourceCycleComponent Z Q n (by intro i j; rfl) zL n
  have hm : m.hom (π.hom z) = (L.homologyπ n).hom zL :=
    (AddCommGrpCat.comp_apply π m z).symm.trans
      ((ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality g n) z).trans
        (AddCommGrpCat.comp_apply (HomologicalComplex.cyclesMap g n) (L.homologyπ n) z))
  have hHomology : h.hom (π.hom z) = (K.homologyπ n).hom zK :=
    (AddCommGrpCat.comp_apply π h z).symm.trans
      ((ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality e.hom n) z).trans
        (AddCommGrpCat.comp_apply (HomologicalComplex.cyclesMap e.hom n) (K.homologyπ n) z))
  have hc : ev.hom (c.hom ((L.homologyπ n).hom zL)) =
      Int.triangularSign n • (κ ≫ Q.homologyπ (n - n)) :=
    homZeroSourceCohomologyComparison_apply Z Q n (by intro i j; rfl) zL n
  have hq (v : V) : q.hom v = v ≫ eH.hom := rfl
  have hκ : (κ ≫ Q.homologyπ (n - n)) ≫ eH.hom = P.iCycles n ≫ φ :=
    homFixedCoefficientCyclesValue P M n z
  have hLeft : ((π ≫ (m ≫ c ≫ ev ≫ q)).hom z) =
      Int.triangularSign n • (P.iCycles n ≫ φ) :=
    (AddCommGrpCat.comp_apply π (m ≫ c ≫ ev ≫ q) z).trans
      ((AddCommGrpCat.comp_apply m (c ≫ ev ≫ q) (π.hom z)).trans
        ((congrArg (c ≫ ev ≫ q).hom hm).trans
          ((AddCommGrpCat.comp_apply c (ev ≫ q) ((L.homologyπ n).hom zL)).trans
            ((AddCommGrpCat.comp_apply ev q (c.hom ((L.homologyπ n).hom zL))).trans
              ((congrArg q.hom hc).trans
                ((hq _).trans ((Linear.units_smul_comp (Int.triangularSign n)
                  (κ ≫ Q.homologyπ (n - n)) eH.hom).trans
                    (congrArg (fun v : P.cycles n ⟶ M => Int.triangularSign n • v) hκ))))))))
  have hr : r.hom ((K.homologyπ n).hom zK) =
      (homFixedCoefficientCycleRestriction P M n).hom zK :=
    (AddCommGrpCat.comp_apply (K.homologyπ n) r zK).symm.trans
      (ConcreteCategory.congr_hom (homologyπ_homFixedCoefficientRestriction P M n) zK)
  have ha (v : A) : a.hom v = P.homologyπ n ≫ v := rfl
  have hπ : P.homologyπ n ≫ (homFixedCoefficientCycleRestriction P M n).hom zK =
      P.iCycles n ≫ φ := homFixedCoefficientCycleRestriction_π P M n zK
  have hθ (v : B) : θ.hom.hom v = Int.triangularSign n • v := rfl
  have hRight : ((π ≫ (h ≫ r ≫ a ≫ θ.hom)).hom z) =
      Int.triangularSign n • (P.iCycles n ≫ φ) :=
    (AddCommGrpCat.comp_apply π (h ≫ r ≫ a ≫ θ.hom) z).trans
      ((AddCommGrpCat.comp_apply h (r ≫ a ≫ θ.hom) (π.hom z)).trans
        ((congrArg (r ≫ a ≫ θ.hom).hom hHomology).trans
          ((AddCommGrpCat.comp_apply r (a ≫ θ.hom) ((K.homologyπ n).hom zK)).trans
            ((congrArg (a ≫ θ.hom).hom hr).trans
              ((AddCommGrpCat.comp_apply a θ.hom
                ((homFixedCoefficientCycleRestriction P M n).hom zK)).trans
                  ((congrArg θ.hom.hom (ha _)).trans
                    ((hθ _).trans
                      (congrArg (fun v : P.cycles n ⟶ M => Int.triangularSign n • v) hπ))))))))
  change (π ≫ (m ≫ c ≫ ev ≫ q)).hom z = (π ≫ (h ≫ r ≫ a ≫ θ.hom)).hom z
  exact hLeft.trans hRight.symm

section Ext

universe w
variable [HasExt.{w} C]

/-- The genuine degree-one Ext product collapses only the actual zero target homology factors.
The Ext universe is independent of the object and Hom universes. -/
def homFixedCoefficientExtProductEquiv (P : ChainComplex C ℤ) (M : C) (n : ℤ) :
    (∀ p : ℤ, Ext.{w} (P.homology p)
      (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).homology (n - 1 - p)) 1) ≃+
        Ext.{w} (P.homology (n - 1)) M 1 := by
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let e : Q.homology (n - 1 - (n - 1)) ≅ M :=
    homFixedCoefficientTargetHomologyIso M (n - 1 - (n - 1)) (by omega)
  let F : C ⥤ AddCommGrpCat.{w} := extFunctorObj (P.homology (n - 1)) 1
  let E : Ext.{w} (P.homology (n - 1)) (Q.homology (n - 1 - (n - 1))) 1 ≃+
      Ext.{w} (P.homology (n - 1)) M 1 := (F.mapIso e).addCommGroupIsoToAddEquiv
  exact
    { toFun z := E (z (n - 1))
      invFun x p := if hp : p = n - 1 then by
          subst p
          exact E.symm x
        else 0
      left_inv z := by
        funext p
        dsimp only
        by_cases hp : p = n - 1
        · subst p
          rw [dif_pos rfl]
          exact E.symm_apply_apply (z (n - 1))
        · rw [dif_neg hp]
          let G : C ⥤ AddCommGrpCat.{w} := extFunctorObj (P.homology p) 1
          have hQ : IsZero (Q.homology (n - 1 - p)) :=
            HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M
              (n - 1 - p) (by omega)
          have hG : IsZero (G.obj (Q.homology (n - 1 - p))) := G.map_isZero hQ
          letI : Subsingleton (Ext.{w} (P.homology p) (Q.homology (n - 1 - p)) 1) :=
            AddCommGrpCat.subsingleton_of_isZero hG
          exact Subsingleton.elim _ _
      right_inv x := by
        dsimp only
        rw [dif_pos rfl]
        exact E.apply_symm_apply x
      map_add' z z' := by
        change E (z (n - 1) + z' (n - 1)) = E (z (n - 1)) + E (z' (n - 1))
        exact E.map_add _ _ }

/-- The Ext endpoint uses the actual native Ext functor on the target single homology iso. -/
lemma homFixedCoefficientExtProductEquiv_apply (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (z : ∀ p : ℤ, Ext.{w} (P.homology p)
      (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).homology (n - 1 - p)) 1) :
    homFixedCoefficientExtProductEquiv P M n z =
      ((extFunctorObj (P.homology (n - 1)) 1).map
        (homFixedCoefficientTargetHomologyIso M (n - 1 - (n - 1)) (by omega)).hom).hom
          (z (n - 1)) := rfl

/-- The Ext endpoint retains both native actions under the earned single-factor collapse. -/
lemma homFixedCoefficientExtProductEquiv_naturality {P P' : ChainComplex C ℤ} {M M' : C}
    (f : P' ⟶ P) (b : M ⟶ M') (n : ℤ)
    (z : ∀ p : ℤ, Ext.{w} (P.homology p)
      (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).homology (n - 1 - p)) 1) :
    homFixedCoefficientExtProductEquiv P' M' n
      (fun p =>
        ((show Ext.{w} (P'.homology p) (P.homology p) 0 from
          Ext.mk₀ (homologyMap f p)).comp (z p) (zero_add 1)).comp
          (show Ext.{w}
              (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).homology
                (n - 1 - p))
              (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M').homology
                (n - 1 - p)) 0 from
            Ext.mk₀ (homologyMap ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b)
              (n - 1 - p))) (add_zero 1)) =
      ((show Ext.{w} (P'.homology (n - 1)) (P.homology (n - 1)) 0 from
        Ext.mk₀ (homologyMap f (n - 1))).comp
          (homFixedCoefficientExtProductEquiv P M n z) (zero_add 1)).comp
            (show Ext.{w} M M' 0 from Ext.mk₀ b) (add_zero 1) := by
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let Q' : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M'
  let i : ℤ := n - 1
  let q : ℤ := n - 1 - i
  let a : P'.homology i ⟶ P.homology i := homologyMap f i
  let g : Q.homology q ⟶ Q'.homology q :=
    homologyMap ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b) q
  let e : Q.homology q ≅ M :=
    homFixedCoefficientTargetHomologyIso M q (by dsimp [q, i]; omega)
  let e' : Q'.homology q ≅ M' :=
    homFixedCoefficientTargetHomologyIso M' q (by dsimp [q, i]; omega)
  let α : Ext.{w} (P'.homology i) (P.homology i) 0 := Ext.mk₀ a
  let x : Ext.{w} (P.homology i) (Q.homology q) 1 := z i
  let β : Ext.{w} (Q.homology q) (Q'.homology q) 0 := Ext.mk₀ g
  let γ : Ext.{w} (Q'.homology q) M' 0 := Ext.mk₀ e'.hom
  let δ : Ext.{w} (Q.homology q) M 0 := Ext.mk₀ e.hom
  let ε : Ext.{w} M M' 0 := Ext.mk₀ b
  let z' : ∀ r : ℤ, Ext.{w} (P'.homology r) (Q'.homology (n - 1 - r)) 1 := fun r =>
    ((show Ext.{w} (P'.homology r) (P.homology r) 0 from
      Ext.mk₀ (homologyMap f r)).comp (z r) (zero_add 1)).comp
        (show Ext.{w} (Q.homology (n - 1 - r)) (Q'.homology (n - 1 - r)) 0 from
          Ext.mk₀ (homologyMap ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b)
            (n - 1 - r))) (add_zero 1)
  have ht : g ≫ e'.hom = e.hom ≫ b :=
    homFixedCoefficientTargetHomologyIso_naturality b q (by dsimp [q, i]; omega)
  have hCollapse : homFixedCoefficientExtProductEquiv P M n z =
      x.comp δ (add_zero 1) := by
    have h := homFixedCoefficientExtProductEquiv_apply P M n z
    change homFixedCoefficientExtProductEquiv P M n z =
      ((extFunctorObj (P.homology i) 1).map e.hom).hom x at h
    have hMap : ((extFunctorObj (P.homology i) 1).map e.hom).hom x =
        x.comp δ (add_zero 1) := by
      rw [extFunctorObj_map]
      rfl
    exact h.trans hMap
  have hCollapse' : homFixedCoefficientExtProductEquiv P' M' n z' =
      ((α.comp x (zero_add 1)).comp β (add_zero 1)).comp γ (add_zero 1) := by
    have h := homFixedCoefficientExtProductEquiv_apply P' M' n z'
    change homFixedCoefficientExtProductEquiv P' M' n z' =
      ((extFunctorObj (P'.homology i) 1).map e'.hom).hom (z' i) at h
    have hMap : ((extFunctorObj (P'.homology i) 1).map e'.hom).hom (z' i) =
        (z' i).comp γ (add_zero 1) := by
      rw [extFunctorObj_map]
      rfl
    exact h.trans hMap
  have hG : β.comp γ (zero_add 0) =
      (show Ext.{w} (Q.homology q) M' 0 from Ext.mk₀ (g ≫ e'.hom)) :=
    Ext.mk₀_comp_mk₀ g e'.hom
  have hB : δ.comp ε (zero_add 0) =
      (show Ext.{w} (Q.homology q) M' 0 from Ext.mk₀ (e.hom ≫ b)) :=
    Ext.mk₀_comp_mk₀ e.hom b
  have hTargets : β.comp γ (zero_add 0) = δ.comp ε (zero_add 0) :=
    hG.trans
      ((congrArg (fun h : Q.homology q ⟶ M' =>
        (show Ext.{w} (Q.homology q) M' 0 from Ext.mk₀ h)) ht).trans hB.symm)
  have hAssociatePost :
      ((α.comp x (zero_add 1)).comp β (add_zero 1)).comp γ (add_zero 1) =
        (α.comp x (zero_add 1)).comp (β.comp γ (zero_add 0)) (add_zero 1) :=
    Ext.comp_assoc_of_second_deg_zero (α.comp x (zero_add 1)) β γ (add_zero 1)
  have hUnassociatePost :
      (α.comp x (zero_add 1)).comp (δ.comp ε (zero_add 0)) (add_zero 1) =
        ((α.comp x (zero_add 1)).comp δ (add_zero 1)).comp ε (add_zero 1) :=
    (Ext.comp_assoc_of_second_deg_zero (α.comp x (zero_add 1)) δ ε (add_zero 1)).symm
  have hAssociatePre :
      (α.comp x (zero_add 1)).comp δ (add_zero 1) =
        α.comp (x.comp δ (add_zero 1)) (zero_add 1) :=
    Ext.comp_assoc_of_third_deg_zero α x δ (zero_add 1)
  have hRaw :
      ((α.comp x (zero_add 1)).comp β (add_zero 1)).comp γ (add_zero 1) =
        (α.comp (x.comp δ (add_zero 1)) (zero_add 1)).comp ε (add_zero 1) :=
    hAssociatePost.trans
      ((congrArg (fun v : Ext.{w} (Q.homology q) M' 0 =>
        (α.comp x (zero_add 1)).comp v (add_zero 1)) hTargets).trans
          (hUnassociatePost.trans
            (congrArg (fun v : Ext.{w} (P'.homology i) M 1 =>
              v.comp ε (add_zero 1)) hAssociatePre)))
  change homFixedCoefficientExtProductEquiv P' M' n z' =
    (α.comp (homFixedCoefficientExtProductEquiv P M n z) (zero_add 1)).comp ε (add_zero 1)
  exact hCollapse'.trans
    (hRaw.trans
      (congrArg (fun v : Ext.{w} (P.homology i) M 1 =>
        (α.comp v (zero_add 1)).comp ε (add_zero 1)) hCollapse.symm))

/-- The actual fixed-target coordinates use the same native endpoint unit and unweighted middle.
The tuple is computed without projectivity; both endpoint units come from the cycle comparison. -/
def homFixedCoefficientUCTCoordinates (P : ChainComplex C ℤ) (M : C) (n : ℤ) :
    (AddCommGrpCat.of (∀ p : ℤ, ULift.{v, w}
      (Ext.{w} (P.homology p)
        (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).homology
          (n - 1 - p)) 1)) ≅
      AddCommGrpCat.uliftFunctor.{v, w}.obj
        (AddCommGrpCat.of (Ext.{w} (P.homology (n - 1)) M 1))) ×
    (AddCommGrpCat.uliftFunctor.{w, v}.obj
      ((homCochainComplex P
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)).homology n) ≅
      AddCommGrpCat.uliftFunctor.{w, v}.obj ((homFixedCoefficient P M).homology n)) ×
    (AddCommGrpCat.of (∀ p : ℤ, ULift.{w, v} (P.homology p ⟶
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).homology (n - p))) ≅
      AddCommGrpCat.uliftFunctor.{w, v}.obj (AddCommGrpCat.of (P.homology n ⟶ M))) := by
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let V := AddCommGrpCat.uliftFunctor.{v, w}
  let E (p : ℤ) : AddCommGrpCat.{w} :=
    AddCommGrpCat.of (Ext.{w} (P.homology p) (Q.homology (n - 1 - p)) 1)
  let H (p : ℤ) : AddCommGrpCat.{v} :=
    AddCommGrpCat.of (P.homology p ⟶ Q.homology (n - p))
  let EL : AddCommGrpCat.{max v w} := V.obj
    (AddCommGrpCat.of (Ext.{w} (P.homology (n - 1)) M 1))
  let HR : AddCommGrpCat.{max v w} := U.obj (AddCommGrpCat.of (P.homology n ⟶ M))
  let eE : AddCommGrpCat.of (∀ p : ℤ, V.obj (E p)) ≅ EL :=
    (AddCommGrpCat.uliftPiIso.{0, w, v} E).symm ≪≫
      V.mapIso (homFixedCoefficientExtProductEquiv P M n).toAddCommGrpIso
  let eH : AddCommGrpCat.of (∀ p : ℤ, U.obj (H p)) ≅ HR :=
    (AddCommGrpCat.uliftPiIso.{0, v, w} H).symm ≪≫
      U.mapIso (homFixedCoefficientHomologyProductEquiv P M n).toAddCommGrpIso
  let θE : EL ≅ EL :=
    (DistribMulAction.toAddEquiv EL (Int.triangularSign n)).toAddCommGrpIso
  let θH : HR ≅ HR :=
    (DistribMulAction.toAddEquiv HR (Int.triangularSign n)).toAddCommGrpIso
  let eM : (homCochainComplex P Q).homology n ≅ (homFixedCoefficient P M).homology n :=
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n).mapIso
      (homFixedCoefficientIso P M)
  exact ⟨eE ≪≫ θE.symm, U.mapIso eM, eH ≪≫ θH.symm⟩

/-- The middle coordinate is exactly the native homology map of physical component evaluation. -/
lemma homFixedCoefficientUCTCoordinates_middle_apply (P : ChainComplex C ℤ) (M : C)
    (n : ℤ)
    (x : (homCochainComplex P
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)).homology n) :
    (homFixedCoefficientUCTCoordinates P M n).2.1.hom (ULift.up x) =
      ULift.up ((HomologicalComplex.homologyMap (homFixedCoefficientIso P M).hom n).hom x) := rfl

/-- The right coordinate removes exactly the unit earned from native cycle evaluation. -/
lemma homFixedCoefficientUCTCoordinates_right_apply (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (k : ∀ p : ℤ, ULift.{w, v} (P.homology p ⟶
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).homology (n - p))) :
    (homFixedCoefficientUCTCoordinates P M n).2.2.hom k =
      ULift.up ((Int.triangularSign n)⁻¹ •
        homFixedCoefficientHomologyProductEquiv P M n (fun p : ℤ => (k p).down)) := rfl

private lemma homFixedCoefficientUCT_right_raw (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p (p - 1)))) :
    (homUniversalCoefficientSequenceEngine.{u, v, w} P
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) n hP hI).g ≫
        (homFixedCoefficientUCTCoordinates P M n).2.2.hom =
      (homFixedCoefficientUCTCoordinates P M n).2.1.hom ≫
        AddCommGrpCat.uliftFunctor.{w, v}.map (homFixedCoefficientRestriction P M n) := by
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let Z : ChainComplex C ℤ := cyclesZeroComplex P
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P Q
  let L : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex Z Q
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let A : AddCommGrpCat.{v} := AddCommGrpCat.of (P.homology n ⟶ M)
  let B : AddCommGrpCat.{v} := AddCommGrpCat.of (P.cycles n ⟶ M)
  let G : AddCommGrpCat.{v} :=
    AddCommGrpCat.of (∀ p : ℤ, P.cycles p ⟶ Q.homology (n - p))
  let V : AddCommGrpCat.{v} := AddCommGrpCat.of (P.cycles n ⟶ Q.homology (n - n))
  let S : ShortComplex AddCommGrpCat.{max v w} :=
    homUniversalCoefficientSequenceEngine.{u, v, w} P Q n hP hI
  let T₁ : AddCommGrpCat.{max v w} :=
    AddCommGrpCat.of (∀ p : ℤ, ULift.{w, v} (P.cycles p ⟶ Q.homology (n - p)))
  let hOut (p : ℤ) : Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p))) := by
    rw [(ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk p (p - 1) (by omega))]
    exact hI p
  let hZ (p : ℤ) : Projective (P.cycles p) := by
    letI : Projective (P.X p) := hP p
    letI : Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p))) := hOut p
    exact HomologicalComplex.projective_cycles P p
  let hCycles (p : ℤ) : Projective (Z.X p) := by
    change Projective (P.cycles p)
    exact hZ p
  let m : H.homology n ⟶ L.homology n :=
    HomologicalComplex.homologyMap (homCyclesSequence P Q).g n
  let c : L.homology n ⟶ G :=
    homZeroSourceCohomologyComparison Z Q n (by intro i j; rfl)
  let d : L.homology n ≅ G :=
    homZeroSourceCohomologyIso Z Q n (by intro i j; rfl) hCycles
  let eC₀ := homUctCyclesCohomologyIso P Q n hZ
  change U.obj (L.homology n) ≅ T₁ at eC₀
  let eC : U.obj (L.homology n) ≅ T₁ := eC₀
  let κ₀ := homUctHomKernelInclusion P (fun p => Q.homology (n - p))
  change S.X₃ ⟶ T₁ at κ₀
  let κ : S.X₃ ⟶ T₁ := κ₀
  let ev : G ⟶ V := AddCommGrpCat.ofHom
    (Pi.evalAddMonoidHom (fun p : ℤ => P.cycles p ⟶ Q.homology (n - p)) n)
  let eH : Q.homology (n - n) ≅ M :=
    homFixedCoefficientTargetHomologyIso M (n - n) (by omega)
  let q : V ⟶ B := (preadditiveCoyoneda.obj (op (P.cycles n))).map eH.hom
  let f : H.homology n ⟶ K.homology n :=
    HomologicalComplex.homologyMap (homFixedCoefficientIso P M).hom n
  let r : K.homology n ⟶ A := homFixedCoefficientRestriction P M n
  let a : A ⟶ B := (preadditiveYoneda.obj M).map (P.homologyπ n).op
  let θ : B ≅ B :=
    (DistribMulAction.toAddEquiv B (Int.triangularSign n)).toAddCommGrpIso
  let e₂ : S.X₂ ≅ U.obj (K.homology n) :=
    (homFixedCoefficientUCTCoordinates P M n).2.1
  let e₃ : S.X₃ ≅ U.obj A := (homFixedCoefficientUCTCoordinates P M n).2.2
  let X₂ : AddCommGrpCat.{max v w} := U.obj (H.homology n)
  let X₃ : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{w, v} (P.homology p ⟶ Q.homology (n - p)))
  let g₀ := S.g
  change X₂ ⟶ X₃ at g₀
  let sg : X₂ ⟶ X₃ := g₀
  let κ' : X₃ ⟶ T₁ := κ
  let mc : X₂ ⟶ U.obj (L.homology n) := U.map m
  have hRep : sg ≫ κ' = mc ≫ eC.hom :=
    homUniversalCoefficientSequenceEngine_right_representative P Q n hP hI
  have hd : d.hom = c :=
    homZeroSourceCohomologyIso_hom Z Q n (by intro i j; rfl) hCycles
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  cases z with
  | up x =>
    let x₀ : H.homology n := x
    let xC : L.homology n := m.hom x₀
    let k : ∀ p : ℤ, ULift.{w, v} (P.homology p ⟶ Q.homology (n - p)) :=
      S.g.hom (ULift.up x₀)
    let γ : P.homology n ⟶ M := r.hom (f.hom x₀)
    have hU : (U.map m).hom (ULift.up x₀) = ULift.up xC := rfl
    have heEval : eC.hom.hom (ULift.up xC) n = ULift.up (d.hom.hom xC n) := rfl
    have heValue : eC.hom.hom (ULift.up xC) n = ULift.up (c.hom xC n) :=
      heEval.trans (congrArg (fun v : L.homology n ⟶ G => ULift.up (v.hom xC n)) hd)
    let xU : X₂ := ULift.up x₀
    have hk : sg.hom xU = k := rfl
    have hBefore : (sg ≫ κ').hom xU = κ.hom k :=
      (AddCommGrpCat.comp_apply sg κ' xU).trans (congrArg κ'.hom hk)
    have hEq : (sg ≫ κ').hom xU = (mc ≫ eC.hom).hom xU :=
      congrArg (fun a : X₂ ⟶ T₁ => a.hom xU) hRep
    have hAfter : (mc ≫ eC.hom).hom xU = eC.hom.hom ((U.map m).hom (ULift.up x₀)) :=
      AddCommGrpCat.comp_apply mc eC.hom xU
    have hSquare : κ.hom k = eC.hom.hom ((U.map m).hom (ULift.up x₀)) :=
      hBefore.symm.trans (hEq.trans hAfter)
    have hκ : κ.hom k n = ULift.up (P.homologyπ n ≫ (k n).down) := rfl
    have hPoint : ULift.up (P.homologyπ n ≫ (k n).down) = ULift.up (c.hom xC n) :=
      hκ.symm.trans ((congrArg (fun v : T₁ => v n) hSquare).trans
        ((congrArg (fun v : U.obj (L.homology n) => eC.hom.hom v n) hU).trans heValue))
    have hDown : P.homologyπ n ≫ (k n).down = c.hom xC n :=
      congrArg (fun v : ULift.{w, v} (P.cycles n ⟶ Q.homology (n - n)) => v.down) hPoint
    let cmp : H.homology n ⟶ B := homFixedCoefficientCyclesComparison P M n
    have hCmpPack : cmp = m ≫ c ≫ ev ≫ q := rfl
    have hq (v : V) : q.hom v = v ≫ eH.hom := rfl
    have hCmpValue : cmp.hom x₀ = c.hom xC n ≫ eH.hom :=
      (ConcreteCategory.congr_hom hCmpPack x₀).trans
        ((AddCommGrpCat.comp_apply m (c ≫ ev ≫ q) x₀).trans
          ((AddCommGrpCat.comp_apply c (ev ≫ q) xC).trans
            ((AddCommGrpCat.comp_apply ev q (c.hom xC)).trans (hq _))))
    have hCmp : cmp = f ≫ r ≫ a ≫ θ.hom := homFixedCoefficientCyclesComparison_eq P M n
    have hCmpPoint : cmp.hom x₀ = Int.triangularSign n • (P.homologyπ n ≫ γ) :=
      (ConcreteCategory.congr_hom hCmp x₀).trans (by rfl)
    have hRaw : homFixedCoefficientHomologyProductEquiv P M n
        (fun p : ℤ => (k p).down) = Int.triangularSign n • γ := by
      apply (cancel_epi (P.homologyπ n)).1
      change P.homologyπ n ≫
          homFixedCoefficientHomologyProductEquiv P M n (fun p : ℤ => (k p).down) =
        P.homologyπ n ≫ (Int.triangularSign n • γ)
      exact (congrArg (fun v : P.homology n ⟶ M => P.homologyπ n ≫ v)
        (homFixedCoefficientHomologyProductEquiv_apply P M n (fun p : ℤ => (k p).down))).trans
          ((Category.assoc (P.homologyπ n) ((k n).down) eH.hom).symm.trans
            ((congrArg (fun v : P.cycles n ⟶ Q.homology (n - n) => v ≫ eH.hom) hDown).trans
              (hCmpValue.symm.trans
                (hCmpPoint.trans ((Linear.comp_units_smul (P.homologyπ n)
                  (Int.triangularSign n) γ).symm)))))
    have hLeft : (S.g ≫ e₃.hom).hom (ULift.up x₀) = ULift.up γ :=
      (AddCommGrpCat.comp_apply S.g e₃.hom (ULift.up x₀)).trans
        ((homFixedCoefficientUCTCoordinates_right_apply P M n k).trans
          ((congrArg (fun v : P.homology n ⟶ M =>
            ULift.up ((Int.triangularSign n)⁻¹ • v)) hRaw).trans
              (congrArg ULift.up (inv_smul_smul (Int.triangularSign n) γ))))
    have hTarget : (U.map r).hom (ULift.up (f.hom x₀)) = ULift.up γ := rfl
    have hRight : (e₂.hom ≫ U.map r).hom (ULift.up x₀) = ULift.up γ :=
      (AddCommGrpCat.comp_apply e₂.hom (U.map r) (ULift.up x₀)).trans
        ((congrArg (U.map r).hom
          (homFixedCoefficientUCTCoordinates_middle_apply P M n x₀)).trans hTarget)
    change (S.g ≫ e₃.hom).hom (ULift.up x₀) = (e₂.hom ≫ U.map r).hom (ULift.up x₀)
    exact hLeft.trans hRight.symm

/-- The fixed-coefficient sequence uses the actual native Ext/Hom sequence and computed coordinates.
Its projective-term and image hypotheses are the printed hypotheses.
Homology projectivity is unnecessary. -/
def homFixedCoefficientUniversalCoefficientSequence (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p (p - 1)))) :
    ShortComplex AddCommGrpCat.{max v w} := by
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let S : ShortComplex AddCommGrpCat.{max v w} :=
    homUniversalCoefficientSequenceEngine.{u, v, w} P Q n hP hI
  let c := homFixedCoefficientUCTCoordinates P M n
  exact S.changeObjects c.1 c.2.1 c.2.2

/-- The coordinate change is the native short-complex isomorphism of the constructed sequence. -/
def homFixedCoefficientUniversalCoefficientSequenceIso (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p (p - 1)))) :
    homUniversalCoefficientSequenceEngine.{u, v, w} P
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) n hP hI ≅
        homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P M n hP hI := by
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let S : ShortComplex AddCommGrpCat.{max v w} :=
    homUniversalCoefficientSequenceEngine.{u, v, w} P Q n hP hI
  let c := homFixedCoefficientUCTCoordinates P M n
  exact S.changeObjectsIso c.1 c.2.1 c.2.2

/-- The full integer fixed-coefficient sequence is short exact under the printed inputs. -/
lemma homFixedCoefficientUniversalCoefficientSequence_shortExact
    (P : ChainComplex C ℤ) (M : C) (n : ℤ) (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p (p - 1)))) :
    (homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P M n hP hI).ShortExact :=
  ShortComplex.shortExact_of_iso
    (homFixedCoefficientUniversalCoefficientSequenceIso P M n hP hI)
    (homUniversalCoefficientSequenceEngine_shortExact P
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) n hP hI)

/-- The actual fixed-target right arrow is canonical homology restriction under native lifting. -/
lemma homFixedCoefficientUniversalCoefficientSequence_g (P : ChainComplex C ℤ) (M : C)
    (n : ℤ) (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p (p - 1)))) :
    (homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P M n hP hI).g =
      AddCommGrpCat.uliftFunctor.{w, v}.map (homFixedCoefficientRestriction P M n) := by
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let S : ShortComplex AddCommGrpCat.{max v w} :=
    homUniversalCoefficientSequenceEngine.{u, v, w} P Q n hP hI
  let T : ShortComplex AddCommGrpCat.{max v w} :=
    homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P M n hP hI
  let c := homFixedCoefficientUCTCoordinates P M n
  let e₂ : S.X₂ ≅ T.X₂ := c.2.1
  let e₃ : S.X₃ ≅ T.X₃ := c.2.2
  let r : T.X₂ ⟶ T.X₃ := U.map (homFixedCoefficientRestriction P M n)
  have h : S.g ≫ e₃.hom = e₂.hom ≫ r :=
    homFixedCoefficientUCT_right_raw P M n hP hI
  change e₂.inv ≫ (S.g ≫ e₃.hom) = r
  exact (congrArg (fun a : S.X₂ ⟶ T.X₃ => e₂.inv ≫ a) h).trans (e₂.inv_hom_id_assoc r)

/-- Image-projective retractions give the noncanonical splitting of the fixed-M cohomology sequence.
Its section is the actual cohomology map represented by qₙ followed by a morphism Hₙ(P)→M. -/
def homFixedCoefficientUniversalCoefficientSplitting (P : ChainComplex C ℤ) (M : C)
    (n : ℤ) (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p (p - 1)))) :
    (homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P M n hP hI).Splitting := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let S : ShortComplex AddCommGrpCat.{max v w} :=
    homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P M n hP hI
  let A : AddCommGrpCat.{v} := AddCommGrpCat.of (P.homology n ⟶ M)
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let hOut (p : ℤ) : Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p))) := by
    rw [(ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk p (p - 1) (by omega))]
    exact hI p
  let σ : A ⟶ K.homology n := homFixedCoefficientCohomologyLift P M n hOut
  let Γ : K.homology n ⟶ A := homFixedCoefficientRestriction P M n
  let s : S.X₃ ⟶ S.X₂ := U.map σ
  have hS : S.ShortExact := homFixedCoefficientUniversalCoefficientSequence_shortExact P M n hP hI
  have hg : S.g = U.map Γ := homFixedCoefficientUniversalCoefficientSequence_g P M n hP hI
  have hσ : σ ≫ Γ = 𝟙 A := homFixedCoefficientCohomologyLift_restriction P M n hOut
  have hs : s ≫ S.g = 𝟙 S.X₃ :=
    (congrArg (fun a : S.X₂ ⟶ S.X₃ => s ≫ a) hg).trans
      ((U.map_comp σ Γ).symm.trans
        ((congrArg (fun a : A ⟶ A => U.map a) hσ).trans
          (CategoryTheory.Functor.map_id U A)))
  exact ShortComplex.Splitting.ofExactOfSection S hS.exact s hs hS.mono_f

/-- The left coordinate removes the endpoint unit after actual native Ext target evaluation. -/
lemma homFixedCoefficientUCTCoordinates_left_apply (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (e : ∀ p : ℤ, ULift.{v, w} (Ext.{w} (P.homology p)
      (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).homology
        (n - 1 - p)) 1)) :
    (homFixedCoefficientUCTCoordinates P M n).1.hom e =
      ULift.up ((Int.triangularSign n)⁻¹ •
        homFixedCoefficientExtProductEquiv P M n (fun p : ℤ => (e p).down)) := rfl

/-- The positive native extension class comes from the original boundary/cycles sequence.
The representative includes the earned image and target-degree transports before evaluation at M. -/
def homFixedCoefficientPositiveExtClass (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (z : (homCochainComplex (outgoingImageZeroComplex P)
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)).cycles n) :
    Ext.{w} (P.homology (n - 1)) M 1 :=
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let I : ChainComplex C ℤ := outgoingImageZeroComplex P
  let p : ℤ := n - 1
  let eI : (homUctBoundaryPresentation P p).X₁ ≅ I.X (p + 1) := eqToIso (by
    change Abelian.image (P.d (p + 1) p) =
      Abelian.image (P.d (p + 1) ((ComplexShape.down ℤ).next (p + 1)))
    exact congrArg (fun i : ℤ => Abelian.image (P.d (p + 1) i))
      ((ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk (p + 1) p (by omega))).symm)
  let eQ : Q.homology (n - (p + 1)) ≅ Q.homology (n - 1 - p) :=
    eqToIso (congrArg (fun i : ℤ => (Q.homology i : C)) (by dsimp only [p]; omega))
  let eM : Q.homology (n - 1 - p) ≅ M :=
    homFixedCoefficientTargetHomologyIso M (n - 1 - p) (by dsimp only [p]; omega)
  let κ : I.X (p + 1) ⟶ Q.cycles (n - (p + 1)) :=
    homZeroSourceCycleComponent I Q n (by intro i j; rfl) z (p + 1)
  let v : (homUctBoundaryPresentation P p).X₁ ⟶ Q.homology (n - 1 - p) :=
    eI.hom ≫ κ ≫ Q.homologyπ (n - (p + 1)) ≫ eQ.hom
  ((extFunctorObj (P.homology p) 1).map eM.hom).hom
    ((homUctBoundaryPresentation_shortExact P p).extClass.comp (Ext.mk₀ v) (add_zero 1))

private lemma homFixedCoefficientUCT_left_positive (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p (p - 1))))
    (z : (homCochainComplex (outgoingImageZeroComplex P)
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)).cycles n) :
    (homFixedCoefficientUCTCoordinates P M n).1.hom
      ((homUctProductPresentation P (fun p =>
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).homology
          (n - 1 - p))).g.hom
            ((homUctImagesCohomologyIso P
              ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)
                (n - 1) n (by omega) hI).hom.hom
                  (ULift.up ((homCochainComplex (outgoingImageZeroComplex P)
                    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)).homologyπ n z)))) =
      ULift.up (homFixedCoefficientPositiveExtClass P M n z) := by
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let I : ChainComplex C ℤ := outgoingImageZeroComplex P
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex I Q
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let V := AddCommGrpCat.uliftFunctor.{v, w}
  let p : ℤ := n - 1
  let G : AddCommGrpCat.{v} :=
    AddCommGrpCat.of (∀ r : ℤ, I.X r ⟶ Q.homology (n - r))
  let A₂ : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ r : ℤ, ULift.{w, v} (Abelian.image (P.d (r + 1) r) ⟶ Q.homology (n - 1 - r)))
  let A₃ : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ r : ℤ, ULift.{v, w} (Ext.{w} (P.homology r) (Q.homology (n - 1 - r)) 1))
  let X : AddCommGrpCat.{w} :=
    AddCommGrpCat.of (Ext.{w} (P.homology p) (Q.homology (n - 1 - p)) 1)
  let Y : AddCommGrpCat.{w} := AddCommGrpCat.of (Ext.{w} (P.homology p) M 1)
  let T : AddCommGrpCat.{max v w} := V.obj Y
  let hOut (r : ℤ) : Projective (I.X r) := by
    change Projective (Abelian.image (P.d r ((ComplexShape.down ℤ).next r)))
    rw [(ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk r (r - 1) (by omega))]
    exact hI r
  let d : H.homology n ≅ G :=
    homZeroSourceCohomologyIso I Q n (by intro i j; rfl) hOut
  let t₀ := homUctImageProductIso P Q (n - 1) n (by omega)
  change U.obj G ≅ A₂ at t₀
  let t : U.obj G ≅ A₂ := t₀
  let b₀ := homUctImagesCohomologyIso P Q (n - 1) n (by omega) hI
  change U.obj (H.homology n) ≅ A₂ at b₀
  let b : U.obj (H.homology n) ≅ A₂ := b₀
  let g₀ := (homUctProductPresentation P (fun r => Q.homology (n - 1 - r))).g
  change A₂ ⟶ A₃ at g₀
  let g : A₂ ⟶ A₃ := g₀
  let eLeft₀ := (homFixedCoefficientUCTCoordinates P M n).1
  change A₃ ≅ T at eLeft₀
  let eLeft : A₃ ≅ T := eLeft₀
  let k : G := fun r : ℤ =>
    homZeroSourceCycleComponent I Q n (by intro i j; rfl) z r ≫ Q.homologyπ (n - r)
  let ν : A₂ := t.hom.hom (ULift.up k)
  let a : Y := homFixedCoefficientPositiveExtClass P M n z
  have hd : d.hom.hom ((H.homologyπ n).hom z) = Int.triangularSign n • k := by
    funext r
    exact homZeroSourceCohomologyIso_apply I Q n (by intro i j; rfl) hOut z r
  have hbValue : b.hom.hom (ULift.up ((H.homologyπ n).hom z)) =
      t.hom.hom (ULift.up (d.hom.hom ((H.homologyπ n).hom z))) := rfl
  have htUnit : t.hom.hom (ULift.up (Int.triangularSign n • k)) =
      Int.triangularSign n • ν := by
    change t.hom.hom ((Int.triangularSign n : ℤ) • (ULift.up k : U.obj G)) =
      (Int.triangularSign n : ℤ) • t.hom.hom (ULift.up k)
    exact t.hom.hom.map_zsmul (Int.triangularSign n : ℤ) (ULift.up k)
  have hB : b.hom.hom (ULift.up ((H.homologyπ n).hom z)) = Int.triangularSign n • ν :=
    hbValue.trans ((congrArg (fun x : G => t.hom.hom (ULift.up x)) hd).trans htUnit)
  let eI : (homUctBoundaryPresentation P p).X₁ ≅ I.X (p + 1) := eqToIso (by
    change Abelian.image (P.d (p + 1) p) =
      Abelian.image (P.d (p + 1) ((ComplexShape.down ℤ).next (p + 1)))
    exact congrArg (fun i : ℤ => Abelian.image (P.d (p + 1) i))
      ((ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk (p + 1) p (by omega))).symm)
  let eQ : Q.homology (n - (p + 1)) ≅ Q.homology (n - 1 - p) :=
    eqToIso (congrArg (fun i : ℤ => (Q.homology i : C)) (by dsimp only [p]; omega))
  let eM : Q.homology (n - 1 - p) ≅ M :=
    homFixedCoefficientTargetHomologyIso M (n - 1 - p) (by dsimp only [p]; omega)
  let κ : I.X (p + 1) ⟶ Q.cycles (n - (p + 1)) :=
    homZeroSourceCycleComponent I Q n (by intro i j; rfl) z (p + 1)
  let v : (homUctBoundaryPresentation P p).X₁ ⟶ Q.homology (n - 1 - p) :=
    eI.hom ≫ κ ≫ Q.homologyπ (n - (p + 1)) ≫ eQ.hom
  let F : C ⥤ AddCommGrpCat.{w} := extFunctorObj (P.homology p) 1
  let eval₀ := F.map eM.hom
  change X ⟶ Y at eval₀
  let eval : X ⟶ Y := eval₀
  let y : X :=
    (homUctBoundaryPresentation_shortExact P p).extClass.comp (Ext.mk₀ v) (add_zero 1)
  have ha : a = eval.hom y := rfl
  have hνRaw : ν p = ULift.up (eI.hom ≫ k (p + 1) ≫ eQ.hom) :=
    homUctImageProductIso_hom_up P Q (n - 1) n (by omega) k p
  have hνComp : eI.hom ≫ k (p + 1) ≫ eQ.hom = v :=
    congrArg (fun x : I.X (p + 1) ⟶ Q.homology (n - 1 - p) => eI.hom ≫ x)
      (Category.assoc κ (Q.homologyπ (n - (p + 1))) eQ.hom)
  have hν : ν p = ULift.up v := hνRaw.trans (congrArg ULift.up hνComp)
  have hνDown : (ν p).down = v :=
    congrArg (fun x : ULift.{w, v} ((homUctBoundaryPresentation P p).X₁ ⟶
      Q.homology (n - 1 - p)) => x.down) hν
  have hg : g.hom ν p = ULift.up y := by
    have h := homUctProductPresentation_g_apply P (fun r => Q.homology (n - 1 - r)) ν p
    change g.hom ν p = ULift.up
      ((homUctBoundaryPresentation_shortExact P p).extClass.comp (Ext.mk₀ (ν p).down)
        (add_zero 1)) at h
    exact h.trans (congrArg (fun x : (homUctBoundaryPresentation P p).X₁ ⟶
      Q.homology (n - 1 - p) =>
        ULift.up ((homUctBoundaryPresentation_shortExact P p).extClass.comp (Ext.mk₀ x)
          (add_zero 1))) hνDown)
  have hgDown : (g.hom ν p).down = y :=
    congrArg (fun x : ULift.{v, w}
      (Ext.{w} (P.homology p) (Q.homology (n - 1 - p)) 1) => x.down) hg
  let E := homFixedCoefficientExtProductEquiv P M n
  let η : A₃ := g.hom ν
  have hExt : E (fun r : ℤ => (η r).down) = a := by
    have h := homFixedCoefficientExtProductEquiv_apply P M n (fun r : ℤ => (η r).down)
    change E (fun r : ℤ => (η r).down) = eval.hom ((g.hom ν p).down) at h
    exact h.trans ((congrArg eval.hom hgDown).trans ha.symm)
  let input : A₃ := g.hom (b.hom.hom (ULift.up ((H.homologyπ n).hom z)))
  have hgUnit : g.hom (Int.triangularSign n • ν) = Int.triangularSign n • η := by
    change g.hom ((Int.triangularSign n : ℤ) • ν) =
      (Int.triangularSign n : ℤ) • g.hom ν
    exact g.hom.map_zsmul (Int.triangularSign n : ℤ) ν
  have hInput : input = Int.triangularSign n • η :=
    (congrArg g.hom hB).trans hgUnit
  have hFamily : (fun r : ℤ => (input r).down) =
      Int.triangularSign n • (fun r : ℤ => (η r).down) := by
    funext r
    exact congrArg (fun x : A₃ => (x r).down) hInput
  have hEUnit : E (Int.triangularSign n • (fun r : ℤ => (η r).down)) =
      Int.triangularSign n • E (fun r : ℤ => (η r).down) := by
    change E ((Int.triangularSign n : ℤ) • (fun r : ℤ => (η r).down)) =
      (Int.triangularSign n : ℤ) • E (fun r : ℤ => (η r).down)
    exact E.toAddMonoidHom.map_zsmul (Int.triangularSign n : ℤ) (fun r : ℤ => (η r).down)
  have hExtInput : E (fun r : ℤ => (input r).down) = Int.triangularSign n • a :=
    (congrArg E hFamily).trans
      (hEUnit.trans (congrArg (fun x : Y => Int.triangularSign n • x) hExt))
  have hCompute := homFixedCoefficientUCTCoordinates_left_apply P M n input
  change eLeft.hom.hom input =
    ULift.up ((Int.triangularSign n)⁻¹ • E (fun r : ℤ => (input r).down)) at hCompute
  change eLeft.hom.hom input = ULift.up a
  exact hCompute.trans
    ((congrArg (fun x : Y => ULift.up ((Int.triangularSign n)⁻¹ • x)) hExtInput).trans
      (congrArg ULift.up (inv_smul_smul (Int.triangularSign n) a)))

/-- The actual left injection sends the original positive Ext representative to the Hom image class.
The image comparison in degree n supplies its unit, which the computed left coordinate removes. -/
lemma homFixedCoefficientUniversalCoefficientSequence_left_representative
    (P : ChainComplex C ℤ) (M : C) (n : ℤ) (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p (p - 1))))
    (z : (homCochainComplex (outgoingImageZeroComplex P)
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)).cycles n) :
    (homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P M n hP hI).f
        (ULift.up (homFixedCoefficientPositiveExtClass P M n z)) =
      (homFixedCoefficientUCTCoordinates P M n).2.1.hom
        (AddCommGrpCat.uliftFunctor.{w, v}.map
          (HomologicalComplex.homologyMap (homCyclesSequence P
            ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)).f n)
              (ULift.up ((homCochainComplex (outgoingImageZeroComplex P)
                ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)).homologyπ n z))) := by
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex (outgoingImageZeroComplex P) Q
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let V := AddCommGrpCat.uliftFunctor.{v, w}
  let S : ShortComplex AddCommGrpCat.{max v w} :=
    homUniversalCoefficientSequenceEngine.{u, v, w} P Q n hP hI
  let T : ShortComplex AddCommGrpCat.{max v w} :=
    homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P M n hP hI
  let A₂ : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{w, v} (Abelian.image (P.d (p + 1) p) ⟶ Q.homology (n - 1 - p)))
  let X₁ : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{v, w} (Ext.{w} (P.homology p) (Q.homology (n - 1 - p)) 1))
  let X₂ : AddCommGrpCat.{max v w} := U.obj ((homCochainComplex P Q).homology n)
  let Y₁ : AddCommGrpCat.{max v w} :=
    V.obj (AddCommGrpCat.of (Ext.{w} (P.homology (n - 1)) M 1))
  let Y₂ : AddCommGrpCat.{max v w} := U.obj (K.homology n)
  let b₀ := homUctImagesCohomologyIso P Q (n - 1) n (by omega) hI
  change U.obj (H.homology n) ≅ A₂ at b₀
  let b : U.obj (H.homology n) ≅ A₂ := b₀
  let g₀ := (homUctProductPresentation P (fun p => Q.homology (n - 1 - p))).g
  change A₂ ⟶ X₁ at g₀
  let g : A₂ ⟶ X₁ := g₀
  let s₀ := S.f
  change X₁ ⟶ X₂ at s₀
  let s : X₁ ⟶ X₂ := s₀
  let t₀ := T.f
  change Y₁ ⟶ Y₂ at t₀
  let t : Y₁ ⟶ Y₂ := t₀
  let e₁₀ := (homFixedCoefficientUCTCoordinates P M n).1
  change X₁ ≅ Y₁ at e₁₀
  let e₁ : X₁ ≅ Y₁ := e₁₀
  let e₂₀ := (homFixedCoefficientUCTCoordinates P M n).2.1
  change X₂ ≅ Y₂ at e₂₀
  let e₂ : X₂ ≅ Y₂ := e₂₀
  let i : U.obj (H.homology n) ⟶ X₂ :=
    U.map (HomologicalComplex.homologyMap (homCyclesSequence P Q).f n)
  have hLeft : b.hom ≫ g ≫ s = i :=
    homUniversalCoefficientSequenceEngine_left_representative P Q n hP hI
  have hf : t = e₁.inv ≫ s ≫ e₂.hom := rfl
  have hCancel : e₁.hom ≫ t = s ≫ e₂.hom :=
    (congrArg (fun a : Y₁ ⟶ Y₂ => e₁.hom ≫ a) hf).trans
      (e₁.hom_inv_id_assoc (s ≫ e₂.hom))
  have hMap : b.hom ≫ g ≫ e₁.hom ≫ t = i ≫ e₂.hom :=
    (congrArg (fun a : X₁ ⟶ Y₂ => b.hom ≫ g ≫ a) hCancel).trans
      ((Category.assoc b.hom g (s ≫ e₂.hom)).symm.trans
        ((Category.assoc (b.hom ≫ g) s e₂.hom).symm.trans
          (congrArg (fun a : U.obj (H.homology n) ⟶ X₂ => a ≫ e₂.hom)
            ((Category.assoc b.hom g s).trans hLeft))))
  let x : U.obj (H.homology n) := ULift.up ((H.homologyπ n).hom z)
  let y : Y₁ := ULift.up (homFixedCoefficientPositiveExtClass P M n z)
  have hy : e₁.hom.hom (g.hom (b.hom.hom x)) = y :=
    homFixedCoefficientUCT_left_positive P M n hI z
  have hPoint : (b.hom ≫ g ≫ e₁.hom ≫ t).hom x = t.hom y :=
    (AddCommGrpCat.comp_apply b.hom (g ≫ e₁.hom ≫ t) x).trans
      ((AddCommGrpCat.comp_apply g (e₁.hom ≫ t) (b.hom.hom x)).trans
        ((AddCommGrpCat.comp_apply e₁.hom t (g.hom (b.hom.hom x))).trans
          (congrArg t.hom hy)))
  change t.hom y = e₂.hom.hom (i.hom x)
  exact hPoint.symm.trans
    ((ConcreteCategory.congr_hom hMap x).trans (AddCommGrpCat.comp_apply i e₂.hom x))

end Ext

end Abelian

end ChainComplex
