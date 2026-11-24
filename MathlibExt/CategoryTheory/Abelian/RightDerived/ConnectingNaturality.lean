/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.DeltaFunctor
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ParameterMap

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v u' v'

namespace CategoryTheory.Functor.RightDerived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/--
The single canonical derived connector is natural in the additive functor, through the unchanged
endpoint horseshoe.
-/
theorem canonicalConnecting_naturality_functor {F G : C ⥤ D}
    [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ)
    (S : ShortComplex.ShortExactSequences C) :
    (Functor.rightDerivedConnecting F n).app S ≫ (NatTrans.rightDerived α (n + 1)).app S.obj.X₁ =
      (NatTrans.rightDerived α n).app S.obj.X₃ ≫ (Functor.rightDerivedConnecting G n).app S := by
  exact (HorseshoeData.ofEndpoints S.obj S.property
    (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃)).delta_naturality_functor
      α n (n + 1) rfl

end CategoryTheory.Functor.RightDerived

namespace CategoryTheory.NatTrans

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Right-derived degree maps form a morphism of the derived δ-functors. -/
def rightDerivedDeltaFunctorMap {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) :
    F.rightDerivedDeltaFunctor ⟶ G.rightDerivedDeltaFunctor := by
  refine CohomologicalDeltaFunctor.homMk C D (fun n => NatTrans.rightDerived α n) ?_
  intro n S
  rw [F.rightDerivedDeltaFunctor_connecting_app,
    G.rightDerivedDeltaFunctor_connecting_app]
  rw [RightDerivedDelta.RDdelta_eq_ofEndpoints F n S.obj S.property
        (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃),
      RightDerivedDelta.RDdelta_eq_ofEndpoints G n S.obj S.property
        (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃)]
  exact Functor.RightDerived.HorseshoeData.delta_naturality_functor
    (Functor.RightDerived.HorseshoeData.ofEndpoints S.obj S.property
      (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃)) α n (n + 1) rfl

/-- Every degree of the δ-functor map is the literal right-derived transformation. -/
@[simp]
theorem rightDerivedDeltaFunctorMap_app {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (n : ℕ) :
    CohomologicalDeltaFunctor.Hom.app (NatTrans.rightDerivedDeltaFunctorMap α) n =
      NatTrans.rightDerived α n := rfl

end CategoryTheory.NatTrans

end
