/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.LongExact
public import MathlibExt.CategoryTheory.Abelian.Injective.HorseshoeComparison
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Effaceable
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The universal cohomological delta-functor of right derivation

Let `C,D` be abelian categories, with injective resolutions in `C`,
and let `F : C → D` be additive. The functors `R^nF`, with the
horseshoe connecting maps `R^nF(X₃) → R^(n+1)F(X₁)` on short exact
sequences, form a cohomological delta-functor. Each positive degree is
effaceable by the mono coaugmentation of an injective resolution.
Consequently this delta-functor has the outgoing universal property:
a transformation in degree zero extends uniquely to a delta-functor
morphism. Identifying `R⁰F` with `F` additionally requires preservation
of finite limits.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

namespace Functor.RightDerived.HorseshoeData

/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. For a short exact `S : X₁ → X₂ → X₃` and
injective horseshoe data for `S`, the induced map
`R⁰F(X₁) → R⁰F(X₂)` is a monomorphism. -/
theorem mono_rightDerived_map_f_zero {S : ShortComplex C} {hS : S.ShortExact}
    (H : Functor.RightDerived.HorseshoeData S hS) (F : C ⥤ D) [F.Additive] :
    Mono ((F.rightDerived 0).map S.f) := by
  have hMF := H.mapped_shortExact F
  have : Mono (H.mapped F).f := hMF.mono_f
  have : Mono (HomologicalComplex.homologyMap (H.mapped F).f 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel _ 0 (by
      intro i hi
      simp only [ComplexShape.up_Rel] at hi
      exact Nat.succ_ne_zero i hi)
  let e : Arrow.mk ((F.rightDerived 0).map S.f) ≅
      Arrow.mk (HomologicalComplex.homologyMap (H.mapped F).f 0) :=
    Arrow.isoMk (H.res₁.isoRightDerivedObj F 0) (H.res₂.isoRightDerivedObj F 0) (by
      change (H.res₁.isoRightDerivedObj F 0).hom ≫
          HomologicalComplex.homologyMap
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map H.φf) 0 =
        (F.rightDerived 0).map S.f ≫ (H.res₂.isoRightDerivedObj F 0).hom
      exact (InjectiveResolution.isoRightDerivedObj_hom_naturality S.f H.res₁ H.res₂
        H.φf H.lift_f F 0).symm)
  exact ((MorphismProperty.monomorphisms D).arrow_mk_iso_iff e).mpr
    (MorphismProperty.monomorphisms.infer_property _)

end Functor.RightDerived.HorseshoeData

namespace Functor

/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. The degree-`n` horseshoe boundaries define a
natural transformation `R^nF(X₃) → R^(n+1)F(X₁)` on the category
of short exact sequences `X₁ → X₂ → X₃`. -/
def rightDerivedConnecting (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (ShortComplex.isShortExact C).ι ⋙ ShortComplex.π₃ ⋙ F.rightDerived n ⟶
      (ShortComplex.isShortExact C).ι ⋙ ShortComplex.π₁ ⋙ F.rightDerived (n + 1) where
  app S := RightDerivedDelta.RDdelta F n S.obj S.property
    (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃)
  naturality {S S'} φ := by
    change (F.rightDerived n).map φ.hom.τ₃ ≫
        RightDerivedDelta.RDdelta F n S'.obj S'.property
          (injectiveResolution S'.obj.X₁) (injectiveResolution S'.obj.X₃) =
      RightDerivedDelta.RDdelta F n S.obj S.property
          (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃) ≫
        (F.rightDerived (n + 1)).map φ.hom.τ₁
    obtain ⟨e⟩ := RightDerived.HorseshoeData.nonempty_hom_ofEndpoints
      S.property S'.property
      (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃)
      (injectiveResolution S'.obj.X₁) (injectiveResolution S'.obj.X₃) φ.hom
      (InjectiveResolution.descHom φ.hom.τ₁
        (injectiveResolution S.obj.X₁) (injectiveResolution S'.obj.X₁))
      (InjectiveResolution.descHom φ.hom.τ₃
        (injectiveResolution S.obj.X₃) (injectiveResolution S'.obj.X₃))
    exact (e.val.delta_naturality F n (n + 1) rfl).symm

/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. The degree functors `R^nF` and their canonical
horseshoe connecting maps form a cohomological delta-functor from
`C` to `D`. -/
def rightDerivedDeltaFunctor (F : C ⥤ D) [F.Additive] : CohomologicalDeltaFunctor C D where
  T n := F.rightDerived n
  additive _ := inferInstance
  connecting := F.rightDerivedConnecting
  exactLeft n S := RightDerivedDelta.RDexact_A F n S.obj S.property
    (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃)
  exactMiddle n S := RightDerivedDelta.RDexact_B F n S.obj S.property
    (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃)
  exactRight n S := RightDerivedDelta.RDexact_C F n S.obj S.property
    (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃)
  monoZero S := RightDerived.HorseshoeData.mono_rightDerived_map_f_zero
    (RightDerived.HorseshoeData.ofEndpoints S.obj S.property
      (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃)) F

/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. The degree-`n` functor of its cohomological
delta-functor is exactly `R^nF`. -/
@[simp]
theorem rightDerivedDeltaFunctor_T (F : C ⥤ D) [F.Additive] (n : ℕ) :
    F.rightDerivedDeltaFunctor.T n = F.rightDerived n := rfl

/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. On a short exact sequence `S`, the connecting
map of the derived delta-functor is the horseshoe boundary computed
from the chosen injective resolutions of `S.X₁` and `S.X₃`. -/
theorem rightDerivedDeltaFunctor_connecting_app (F : C ⥤ D) [F.Additive]
    (n : ℕ) (S : ShortComplex.ShortExactSequences C) :
    (F.rightDerivedDeltaFunctor.connecting n).app S =
      RightDerivedDelta.RDdelta F n S.obj S.property
        (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃) := rfl

/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. For every `n`, the functor `R^(n+1)F` is
effaceable: the mono `X → I(X)⁰` from an injective resolution kills
the induced degree-`n+1` map for each object `X`. -/
theorem isEffaceable_rightDerived_succ (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.rightDerived (n + 1)).IsEffaceable := by
  intro X
  let I : C := (injectiveResolution X).cocomplex.X 0
  let ι : X ⟶ I := (injectiveResolution X).ι.f 0
  have : Injective I := by
    dsimp [I]
    infer_instance
  have hι : Mono ι := by
    dsimp [ι]
    exact mono_of_isLimit_fork (injectiveResolution X).isLimitKernelFork
  have hI : IsZero ((F.rightDerived (n + 1)).obj I) :=
    F.isZero_rightDerived_obj_injective_succ n I
  exact ⟨I, ι, hι, hI.eq_of_tgt _ _⟩

/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. Its right-derived delta-functor is universal:
for any cohomological delta-functor `T`, every natural transformation
`R⁰F → T⁰` extends uniquely to a morphism of cohomological
delta-functors. -/
theorem isUniversal_rightDerivedDeltaFunctor (F : C ⥤ D) [F.Additive] :
    CohomologicalDeltaFunctor.IsUniversal C D F.rightDerivedDeltaFunctor := by
  apply CohomologicalDeltaFunctor.isUniversal_of_effaceable
  intro n
  change (F.rightDerived (n + 1)).IsEffaceable
  exact F.isEffaceable_rightDerived_succ n

end Functor
end CategoryTheory

end
