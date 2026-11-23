/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.MapLeftSumNaturality
public import MathlibExt.KTheory.Exact.Quillen.UnderlyingIso
public import Mathlib.CategoryTheory.EqToHom

/-!
# The literal quotient of the original mapped left-sum comparison

The actual comparison has identity third row component. Its original
extension target is the underlying-Iso lift of that third component.
The given quotient object views and public projection formulas identify
both directions with the identity, without supplying a target square.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD

namespace AlgebraicKTheory.ExtensionCategory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

private theorem originalTargetMapHEq
    {A B A' B' : ExtensionCategory D} (hA : A = A') (hB : B = B')
    {a : A ⟶ B} {b : A' ⟶ B'} (h : HEq a b) :
    HEq ((target (C := D)).map a) ((target (C := D)).map b) := by
  cases hA
  cases hB
  cases h
  exact HEq.rfl

private theorem originalUnderlyingHomId {A B Z : D} (hA : A = Z) (hB : B = Z)
    (e : A ≅ B) (h : HEq e.hom (𝟙 Z)) :
    HEq (QuillenQ.underlyingIso e).hom (𝟙 (⟨Z⟩ : QuillenQ D)) := by
  cases hA
  cases hB
  have he : e = Iso.refl _ := Iso.ext (eq_of_heq h)
  cases he
  exact heq_of_eq (congrArg Iso.hom (QuillenQ.underlyingIso_refl _))

private theorem originalIsoInverseId {A B Z : QuillenQ D} (hA : A = Z) (hB : B = Z)
    (e : A ≅ B) (h : HEq e.hom (𝟙 Z)) : HEq e.inv (𝟙 Z) := by
  cases hA
  cases hB
  have he : e = Iso.refl _ := Iso.ext (eq_of_heq h)
  cases he
  exact HEq.rfl

variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem originalMappedQuotient (E : ExtensionCategory C) :
    ((mapFunctor F).obj E).row.X₃ = F.obj E.row.X₃ :=
  (congrArg (fun A : ExtensionCategory D => A.row.X₃) (mapFunctor_obj F E)).trans
    (mapObject_components F E).2.2

private theorem originalRowComparisonTargetHomComputed (T : Core C) (E : ExtensionCategory C) :
    HEq ((target (C := D)).map (mapLeftSumIso F T E).hom)
      (𝟙 (⟨F.obj E.row.X₃⟩ : QuillenQ D)) := by
  let e := mapLeftSumRowIso F T E
  let q := (ShortComplex.π₃ (C := D)).mapIso e
  let p := mapLeftSum_object_views F T E
  have hs : (ShortComplex.π₃ (C := D)).obj (mapObject F (leftSumObj T E)).row =
      F.obj E.row.X₃ :=
    (ShortComplex.π₃_obj _).trans p.2.2.1
  have ht : (ShortComplex.π₃ (C := D)).obj
      (leftSumObj (F.core.obj T) (mapObject F E)).row = F.obj E.row.X₃ :=
    (ShortComplex.π₃_obj _).trans p.2.2.2.2.2
  have hq : HEq q.hom e.hom.τ₃ := by
    simp only [q, Functor.mapIso_hom, ShortComplex.π₃_map]
    exact HEq.rfl
  have hThird : HEq q.hom (𝟙 (F.obj E.row.X₃)) :=
    hq.trans (mapLeftSumRowIso_components F T E).2.2.2.2.1
  have hTarget : (target (C := D)).map (mapLeftSumIso F T E).hom =
      (QuillenQ.underlyingIso q).hom := by
    have h := congrArg Iso.hom (mapLeftSumIso_target F T E)
    simpa only [Functor.mapIso_hom] using h
  exact (heq_of_eq hTarget).trans (originalUnderlyingHomId hs ht q hThird)

private theorem originalActionTargetHomComputed (T : Core C) (E : ExtensionCategory C) :
    HEq ((target (C := D)).map ((mapLeftSumNaturalityIso F).app (T, E)).hom)
      (𝟙 (⟨F.obj E.row.X₃⟩ : QuillenQ D)) := by
  have hs := mapFunctor_obj F (leftSumObj T E)
  have ht := congrArg (fun M : ExtensionCategory D => leftSumObj (F.core.obj T) M)
    (mapFunctor_obj F E)
  have h := originalTargetMapHEq hs ht (mapLeftSumNaturalityIso_app_hom_heq F T E)
  exact h.trans (originalRowComparisonTargetHomComputed F T E)

/-- The actual action comparison retains the identity on the given image quotient. -/
public theorem mapLeftSumNaturalityIso_target_hom_heq (T : Core C) (E : ExtensionCategory C) :
    HEq ((target (C := D)).map ((mapLeftSumNaturalityIso F).app (T, E)).hom)
      (𝟙 (⟨F.obj E.row.X₃⟩ : QuillenQ D)) :=
  originalActionTargetHomComputed F T E

private theorem originalActionTargetInverseComputed (T : Core C) (E : ExtensionCategory C) :
    HEq ((target (C := D)).map ((mapLeftSumNaturalityIso F).app (T, E)).inv)
      (𝟙 (⟨F.obj E.row.X₃⟩ : QuillenQ D)) := by
  let G := mapFunctor F
  let e := (mapLeftSumNaturalityIso F).app (T, E)
  let q := (target (C := D)).mapIso e
  have hOriginal : (leftSumObj T E).row.X₃ = E.row.X₃ := rfl
  have hs : (target (C := D)).obj (G.obj (leftSumObj T E)) =
      (⟨F.obj E.row.X₃⟩ : QuillenQ D) :=
    (target_obj (G.obj (leftSumObj T E))).trans
      (congrArg (fun X : D => (⟨X⟩ : QuillenQ D))
        ((originalMappedQuotient F (leftSumObj T E)).trans (congrArg F.obj hOriginal)))
  have ht : (target (C := D)).obj (leftSumObj (F.core.obj T) (G.obj E)) =
      (⟨F.obj E.row.X₃⟩ : QuillenQ D) :=
    (leftSumObj_target (F.core.obj T) (G.obj E)).trans
      ((target_obj (G.obj E)).trans
        (congrArg (fun X : D => (⟨X⟩ : QuillenQ D)) (originalMappedQuotient F E)))
  have hLeftObject : (leftSumFunctor (C := C) ⋙ G).obj (T, E) =
      G.obj (leftSumObj T E) := rfl
  have hRightObject : (F.core.prod G ⋙ leftSumFunctor (C := D)).obj (T, E) =
      leftSumObj (F.core.obj T) (G.obj E) := rfl
  have hSource : (target (C := D)).obj ((leftSumFunctor (C := C) ⋙ G).obj (T, E)) =
      (⟨F.obj E.row.X₃⟩ : QuillenQ D) :=
    (congrArg (target (C := D)).obj hLeftObject).trans hs
  have hTarget : (target (C := D)).obj
      ((F.core.prod G ⋙ leftSumFunctor (C := D)).obj (T, E)) =
        (⟨F.obj E.row.X₃⟩ : QuillenQ D) :=
    (congrArg (target (C := D)).obj hRightObject).trans ht
  have hh : q.hom = (target (C := D)).map e.hom := rfl
  have hq : HEq q.hom (𝟙 (⟨F.obj E.row.X₃⟩ : QuillenQ D)) :=
    (heq_of_eq hh).trans (mapLeftSumNaturalityIso_target_hom_heq F T E)
  have hi := originalIsoInverseId hSource hTarget q hq
  have hv : q.inv = (target (C := D)).map e.inv := rfl
  exact (heq_of_eq hv.symm).trans hi

/-- Its actual inverse retains the same identity given-quotient map. -/
public theorem mapLeftSumNaturalityIso_target_inv_heq (T : Core C) (E : ExtensionCategory C) :
    HEq ((target (C := D)).map ((mapLeftSumNaturalityIso F).app (T, E)).inv)
      (𝟙 (⟨F.obj E.row.X₃⟩ : QuillenQ D)) :=
  originalActionTargetInverseComputed F T E

end AlgebraicKTheory.ExtensionCategory

end
