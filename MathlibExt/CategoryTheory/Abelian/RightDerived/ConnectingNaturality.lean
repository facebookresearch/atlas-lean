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

/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F,G : C → D` additive, and `α : F → G`. For short exact `S : X₁ → X₂ → X₃`, the canonical connecting
maps satisfy `δ_F,n ≫ R^(n+1)α_(X₁) = R^nα_(X₃) ≫ δ_G,n`. -/
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

/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F,G : C → D` additive, and `α : F → G`. The transformations `R^nα` and their connecting squares form
a morphism from the right-derived cohomological delta-functor of `F`
to that of `G`. -/
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

/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F,G : C → D` additive, and `α : F → G`. The degree-`n` component of the induced cohomological
delta-functor morphism is the natural transformation `R^nα`. -/
@[simp]
theorem rightDerivedDeltaFunctorMap_app {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (n : ℕ) :
    CohomologicalDeltaFunctor.Hom.app (NatTrans.rightDerivedDeltaFunctorMap α) n =
      NatTrans.rightDerived α n := rfl

end CategoryTheory.NatTrans

end
