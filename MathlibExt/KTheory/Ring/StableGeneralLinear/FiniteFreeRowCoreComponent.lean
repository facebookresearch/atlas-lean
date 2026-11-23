/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowGroupCompletion
public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Groupoid

/-!
# The actual core component represented by an original finite GL stage

In the original projective core, the connected component of a free object
is precisely its isomorphism class. The original opposite-row finite-GL
functor lifts to this literal component and is an equivalence there.
Its full original core map is retained after forgetting the component.

A Grothendieck grade can contain several such core components; the later
finite-free stabilization argument handles that broader passage.
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The literal free-object isomorphism class is the actual connected
component of that object in the original projective core. -/
public theorem finiteFreeRowCore_isoclass_iff_component (n : ℕ)
    (Z : Core (FGProjectiveCat.IdempotentModel R)) :
    Nonempty (((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) ≅ Z.of) ↔
      (CategoryTheory.ConnectedComponents.mk
        (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))).objectProperty Z := by
  let P := (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n
  let c := CategoryTheory.ConnectedComponents.mk (Core.mk P)
  constructor
  · rintro ⟨e⟩
    let f : Z ⟶ Core.mk P := (Core.isoMk e).inv
    change CategoryTheory.ConnectedComponents.mk Z = CategoryTheory.ConnectedComponents.mk (Core.mk P)
    exact Quotient.sound' (Zigzag.of_hom f)
  · intro h
    let Z₀ : c.Component := ⟨Core.mk P, rfl⟩
    let Z₁ : c.Component := ⟨Z, h⟩
    letI : Groupoid c.Component :=
      Groupoid.ofFullyFaithfulToGroupoid (CategoryTheory.ConnectedComponents.ι c)
        c.objectProperty.fullyFaithfulι
    obtain ⟨f⟩ := nonempty_hom_of_preconnected_groupoid Z₀ Z₁
    exact ⟨((CategoryTheory.ConnectedComponents.ι c).map f).iso⟩

/-- The SAME original opposite-row functor, with its codomain restricted
only to the computed connected component of the literal rank-n free object. -/
public def finiteFreeRowCoreComponentFunctor (n : ℕ) :
    SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ⥤
      (CategoryTheory.ConnectedComponents.mk
        (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))).Component :=
  ObjectProperty.lift
    (CategoryTheory.ConnectedComponents.mk
      (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))).objectProperty
    (finiteFreeRowCoreModelFunctor R n)
    (fun X => (finiteFreeRowCore_isoclass_iff_component R n _).mp
      ⟨(eqToIso (finiteFreeRowCoreModelFunctor_obj R n X)).symm⟩)

/-- Forgetting the computed component retains the whole original finite
row functor, with every original matrix arrow unchanged. -/
public theorem finiteFreeRowCoreComponentFunctor_comp_inclusion (n : ℕ) :
    finiteFreeRowCoreComponentFunctor R n ⋙
        CategoryTheory.ConnectedComponents.ι
          (CategoryTheory.ConnectedComponents.mk
            (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))) =
      finiteFreeRowCoreModelFunctor R n := by
  unfold finiteFreeRowCoreComponentFunctor
  rfl

private instance rowCoreComponentFunctorIsEquivalence (n : ℕ) :
    (finiteFreeRowCoreComponentFunctor R n).IsEquivalence where
  faithful := by
    letI : (finiteFreeRowCoreModelFunctor R n).Faithful :=
      (finiteFreeRowCoreFullyFaithful R n).faithful
    change (ObjectProperty.lift _ (finiteFreeRowCoreModelFunctor R n) _).Faithful
    infer_instance
  full := by
    letI : (finiteFreeRowCoreModelFunctor R n).Full :=
      (finiteFreeRowCoreFullyFaithful R n).full
    change (ObjectProperty.lift _ (finiteFreeRowCoreModelFunctor R n) _).Full
    infer_instance
  essSurj :=
    { mem_essImage Z := by
        obtain ⟨e⟩ := (finiteFreeRowCore_isoclass_iff_component R n Z.obj).mpr Z.property
        refine ⟨SingleObj.star _, ⟨?_⟩⟩
        exact ObjectProperty.isoMk _ (Core.isoMk
          (eqToIso (finiteFreeRowCoreModelFunctor_obj R n (SingleObj.star _)) ≪≫ e)) }

/-- The ORIGINAL opposite finite general-linear category is equivalent to
the literal free-object core component. The arrows and inverse are derived
from the established row action and actual component membership. -/
public def finiteFreeRowCoreComponentEquivalence (n : ℕ) :
    SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ≌
      (CategoryTheory.ConnectedComponents.mk
        (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))).Component :=
  (finiteFreeRowCoreComponentFunctor R n).asEquivalence

/-- The derived equivalence has the SAME actual component-restricted row
functor as its forward map. -/
private theorem finiteFreeRowCoreComponentEquivalence_functor_computation07 (n : ℕ) :
    (finiteFreeRowCoreComponentEquivalence R n).functor =
      finiteFreeRowCoreComponentFunctor R n := by
  unfold finiteFreeRowCoreComponentEquivalence
  rfl

public theorem finiteFreeRowCoreComponentEquivalence_functor (n : ℕ) :
    (finiteFreeRowCoreComponentEquivalence R n).functor =
      finiteFreeRowCoreComponentFunctor R n :=
  finiteFreeRowCoreComponentEquivalence_functor_computation07 R n

end AlgebraicKTheory.StableGL
