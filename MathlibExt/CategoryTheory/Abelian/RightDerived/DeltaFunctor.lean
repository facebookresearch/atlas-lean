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
# The universal cohomological δ-functor of the right-derived family

The degree functors are exactly `F.rightDerived n`. Connecting maps on the category of short exact
sequences are the existing `RightDerivedDelta.RDdelta` for the chosen endpoint resolutions.
Naturality follows from the existing horseshoe comparison and its boundary square.

Positive effaceability uses the degree-zero injective object and mono augmentation of the chosen
resolution. No global reverse instance for enough injectives is introduced. The resulting
universal property is outgoing, in the cohomological direction.

This construction concerns `R⁰F` itself. Identifying `R⁰F` with `F` additionally requires
finite-limit preservation.
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

/-- The derived degree-zero subobject map is mono, without exactness of `F`. -/
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

/-- The existing canonical horseshoe boundary is natural on short exact sequences. -/
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

/-- The cohomological δ-functor with the right-derived degrees and boundaries. -/
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

/-- Every degree of the bundle is the right-derived functor. -/
@[simp]
theorem rightDerivedDeltaFunctor_T (F : C ⥤ D) [F.Additive] (n : ℕ) :
    F.rightDerivedDeltaFunctor.T n = F.rightDerived n := rfl

/-- The bundle uses the existing `RDdelta` without an intervening boundary choice. -/
theorem rightDerivedDeltaFunctor_connecting_app (F : C ⥤ D) [F.Additive]
    (n : ℕ) (S : ShortComplex.ShortExactSequences C) :
    (F.rightDerivedDeltaFunctor.connecting n).app S =
      RightDerivedDelta.RDdelta F n S.obj S.property
        (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃) := rfl

/-- Every positive right-derived functor is effaceable by a resolution augmentation. -/
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

/-- The right-derived bundle is universal in the cohomological, outgoing direction. -/
theorem isUniversal_rightDerivedDeltaFunctor (F : C ⥤ D) [F.Additive] :
    CohomologicalDeltaFunctor.IsUniversal C D F.rightDerivedDeltaFunctor := by
  apply CohomologicalDeltaFunctor.isUniversal_of_effaceable
  intro n
  change (F.rightDerived (n + 1)).IsEffaceable
  exact F.isEffaceable_rightDerived_succ n

end Functor
end CategoryTheory

end
