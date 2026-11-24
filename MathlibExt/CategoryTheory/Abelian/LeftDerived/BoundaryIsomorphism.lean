/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Isomorphism
public import MathlibExt.CategoryTheory.Abelian.DerivedDeltaFunctor

/-!
# Natural isomorphisms of the left-derived boundary families

An isomorphism of additive functors induces an isomorphism of their homological delta functors.
Its degree maps are exactly `NatIso.leftDerived`, and its boundaries are the canonical
`LeftDerivedDelta.LDdelta` maps.

Only the source functor's additivity is required as a premise. The target's additivity is obtained
from the supplied natural isomorphism. Neither functor is assumed right exact; the degree-zero
term remains the left-derived zero functor. Source and target category universes are independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u₂ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {F G : C ⥤ D} [F.Additive]

/--
Coefficient maps lift a natural isomorphism to the full left-derived  delta-functor family,
including its connecting maps.
-/
def NatIso.leftDerivedDeltaFunctor (e : F ≅ G) :
    letI := Functor.additive_of_iso e
    F.leftDerivedDeltaFunctor ≅ G.leftDerivedDeltaFunctor := by
  letI := Functor.additive_of_iso e
  exact (leftDerivedDeltaFunctorFamily C D).mapIso
    (ObjectProperty.isoMk (additiveFunctor C D) e : AdditiveFunctor.of F ≅ AdditiveFunctor.of G)

/-- The forward degree map is the canonical derived isomorphism map. -/
@[simp]
theorem NatIso.leftDerivedDeltaFunctor_hom_app (e : F ≅ G) (n : ℕ) :
    letI := Functor.additive_of_iso e
    HomologicalDeltaFunctor.Hom.app (NatIso.leftDerivedDeltaFunctor e).hom n =
      (NatIso.leftDerived e n).hom := rfl

/-- The inverse degree map is the canonical derived inverse map. -/
@[simp]
theorem NatIso.leftDerivedDeltaFunctor_inv_app (e : F ≅ G) (n : ℕ) :
    letI := Functor.additive_of_iso e
    HomologicalDeltaFunctor.Hom.app (NatIso.leftDerivedDeltaFunctor e).inv n =
      (NatIso.leftDerived e n).inv := rfl

/-- Degree evaluation recovers the canonical derived natural isomorphism. -/
@[simp]
theorem NatIso.leftDerivedDeltaFunctor_evaluation (e : F ≅ G) (n : ℕ) :
    letI := Functor.additive_of_iso e
    (HomologicalDeltaFunctor.evaluation C D n).mapIso
        (NatIso.leftDerivedDeltaFunctor e) = NatIso.leftDerived e n := by
  let := Functor.additive_of_iso e
  apply Iso.ext
  rfl

/-- The delta-functor isomorphism preserves identity. -/
@[simp]
theorem NatIso.leftDerivedDeltaFunctor_refl :
    NatIso.leftDerivedDeltaFunctor (Iso.refl F) = Iso.refl F.leftDerivedDeltaFunctor := by
  change (leftDerivedDeltaFunctorFamily C D).mapIso
    (Iso.refl (AdditiveFunctor.of F)) =
      Iso.refl ((leftDerivedDeltaFunctorFamily C D).obj (AdditiveFunctor.of F))
  exact (leftDerivedDeltaFunctorFamily C D).mapIso_refl (AdditiveFunctor.of F)

/-- Reversing the coefficient isomorphism reverses its delta-functor isomorphism. -/
@[simp]
theorem NatIso.leftDerivedDeltaFunctor_symm (e : F ≅ G) :
    letI := Functor.additive_of_iso e
    NatIso.leftDerivedDeltaFunctor e.symm = (NatIso.leftDerivedDeltaFunctor e).symm := by
  let := Functor.additive_of_iso e
  let a : AdditiveFunctor.of F ≅ AdditiveFunctor.of G := ObjectProperty.isoMk (additiveFunctor C D) e
  change (leftDerivedDeltaFunctorFamily C D).mapIso a.symm =
    ((leftDerivedDeltaFunctorFamily C D).mapIso a).symm
  exact (leftDerivedDeltaFunctorFamily C D).mapIso_symm a

/-- Delta-functor isomorphisms preserve coefficient-isomorphism composition. -/
@[simp]
theorem NatIso.leftDerivedDeltaFunctor_trans {H : C ⥤ D}
    (e : F ≅ G) (e' : G ≅ H) :
    letI := Functor.additive_of_iso e
    letI := Functor.additive_of_iso e'
    NatIso.leftDerivedDeltaFunctor (e ≪≫ e') =
      NatIso.leftDerivedDeltaFunctor e ≪≫ NatIso.leftDerivedDeltaFunctor e' := by
  let := Functor.additive_of_iso e
  let := Functor.additive_of_iso e'
  let a : AdditiveFunctor.of F ≅ AdditiveFunctor.of G := ObjectProperty.isoMk (additiveFunctor C D) e
  let b : AdditiveFunctor.of G ≅ AdditiveFunctor.of H := ObjectProperty.isoMk (additiveFunctor C D) e'
  change (leftDerivedDeltaFunctorFamily C D).mapIso (a ≪≫ b) =
    (leftDerivedDeltaFunctorFamily C D).mapIso a ≪≫
      (leftDerivedDeltaFunctorFamily C D).mapIso b
  exact (leftDerivedDeltaFunctorFamily C D).mapIso_trans a b

/--
The forward canonical derived isomorphism commutes with the boundary of every original short exact
sequence.
-/
@[reassoc]
theorem NatIso.leftDerived_hom_LDdelta (e : F ≅ G) (n : ℕ)
    (S : ShortComplex C) (hS : S.ShortExact) :
    letI := Functor.additive_of_iso e
    (NatIso.leftDerived e (n + 1)).hom.app S.X₃ ≫ LeftDerivedDelta.LDdelta G n S hS =
      LeftDerivedDelta.LDdelta F n S hS ≫ (NatIso.leftDerived e n).hom.app S.X₁ := by
  let := Functor.additive_of_iso e
  exact LeftDerivedDelta.LDdelta_natural_functor e.hom n S hS

/-- The inverse canonical derived isomorphism commutes with that same boundary. -/
@[reassoc]
theorem NatIso.leftDerived_inv_LDdelta (e : F ≅ G) (n : ℕ)
    (S : ShortComplex C) (hS : S.ShortExact) :
    letI := Functor.additive_of_iso e
    (NatIso.leftDerived e (n + 1)).inv.app S.X₃ ≫ LeftDerivedDelta.LDdelta F n S hS =
      LeftDerivedDelta.LDdelta G n S hS ≫ (NatIso.leftDerived e n).inv.app S.X₁ := by
  let := Functor.additive_of_iso e
  exact LeftDerivedDelta.LDdelta_natural_functor e.inv n S hS

/-- The target boundary is conjugated by the canonical derived degree isomorphisms. -/
theorem NatIso.LDdelta_eq_leftDerived_inv_comp (e : F ≅ G) (n : ℕ)
    (S : ShortComplex C) (hS : S.ShortExact) :
    letI := Functor.additive_of_iso e
    LeftDerivedDelta.LDdelta G n S hS =
      (NatIso.leftDerived e (n + 1)).inv.app S.X₃ ≫
        LeftDerivedDelta.LDdelta F n S hS ≫ (NatIso.leftDerived e n).hom.app S.X₁ := by
  let := Functor.additive_of_iso e
  calc
    LeftDerivedDelta.LDdelta G n S hS =
        (LeftDerivedDelta.LDdelta G n S hS ≫ (NatIso.leftDerived e n).inv.app S.X₁) ≫
          (NatIso.leftDerived e n).hom.app S.X₁ := by
      rw [Category.assoc, (NatIso.leftDerived e n).inv_hom_id_app, Category.comp_id]
    _ = ((NatIso.leftDerived e (n + 1)).inv.app S.X₃ ≫
        LeftDerivedDelta.LDdelta F n S hS) ≫ (NatIso.leftDerived e n).hom.app S.X₁ :=
      congrArg (fun f => f ≫ (NatIso.leftDerived e n).hom.app S.X₁)
        (NatIso.leftDerived_inv_LDdelta e n S hS).symm
    _ = _ := Category.assoc _ _ _

/--
The sequence-map and coefficient-isomorphism squares compose to the same boundary square in both
variables.
-/
@[reassoc]
theorem NatIso.leftDerived_hom_map_LDdelta (e : F ≅ G) (n : ℕ)
    {S T : ShortComplex C} (φ : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact) :
    letI := Functor.additive_of_iso e
    (NatIso.leftDerived e (n + 1)).hom.app S.X₃ ≫
        (G.leftDerived (n + 1)).map φ.τ₃ ≫ LeftDerivedDelta.LDdelta G n T hT =
      LeftDerivedDelta.LDdelta F n S hS ≫ (F.leftDerived n).map φ.τ₁ ≫
        (NatIso.leftDerived e n).hom.app T.X₁ := by
  let := Functor.additive_of_iso e
  rw [LeftDerivedDelta.LDdelta_natural G n T S φ hT hS]
  rw [← Category.assoc, NatIso.leftDerived_hom_LDdelta e n S hS,
    Category.assoc, ← (NatIso.leftDerived e n).hom.naturality φ.τ₁]

end CategoryTheory

end
