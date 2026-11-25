/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import MathlibExt.CategoryTheory.Abelian.RightDerived.Linear

/-!
# Primary-component functors with independent scalar and module universes

Objects and maps are `Ideal.primaryComponent` and
`Ideal.primaryComponent.map`. The scalar ring and module carriers have
independent universes; Noetherianity and finiteness are not required.

The functor is additive, scalar-linear and preserves finite limits.
Right derivation uses injective resolutions in the chosen module category.
Enough injectives is an explicit hypothesis at an arbitrary coefficient
universe; the category at `max u v` has the Mathlib construction.

The finite-limit proof adapts the exact-kernel argument of Weibel §4.6 in
FormalizedTextbooks.WeibelHomologicalAlgebra.Chapter04.Section06.TorsionFunctor,
attributed there to @toskua and Avocado.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat.Torsion

variable {R : Type u} [CommRing R]

/-- The actual primary-component endofunctor in the original coefficient world. -/
def functor (I : Ideal R) : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R (Ideal.primaryComponent (M : Type v) I)
  map f := ModuleCat.ofHom (Ideal.primaryComponent.map I f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    rfl

/-- The native restricted map has exactly the original map on underlying elements. -/
theorem map_val (I : Ideal R) {M N : ModuleCat.{v} R} (f : M ⟶ N)
    (a : (functor I).obj M) :
    (((functor I).map f).hom a).val = f.hom a.val := rfl

/-- The functor includes naturally into the original coefficient module. -/
def inclusion (I : Ideal R) : functor I ⟶ 𝟭 (ModuleCat.{v} R) where
  app M := ModuleCat.ofHom (Ideal.primaryComponent (M : Type v) I).subtype
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    ext a
    rfl

/-- Membership is annihilation by every scalar in one power of the ideal. -/
theorem mem_obj_iff (I : Ideal R) (M : ModuleCat.{v} R) (a : M) :
    a ∈ Ideal.primaryComponent (M : Type v) I ↔
      ∃ n : ℕ, ∀ r : R, r ∈ I ^ n → r • a = 0 := by
  constructor
  · intro ha
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem (M : Type v) I a).mp ha
    refine ⟨n, ?_⟩
    intro r hr
    exact ((Submodule.mem_torsionBySet_iff _ _).mp hn) ⟨r, hr⟩
  · rintro ⟨n, hn⟩
    apply (Ideal.primaryComponent_mem (M : Type v) I a).mpr
    refine ⟨n, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    exact fun r => hn r r.property

/-- Additivity of actual restricted maps, without a new global instance. -/
theorem functor_additive (I : Ideal R) :
    (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    rfl

/-- The scalar action on morphisms is retained by the native restriction. -/
theorem functor_linear (I : Ideal R) :
    (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Linear R where
  map_smul := by
    intro M N f r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    rfl

/-- Primary components preserve finite limits in every coefficient universe. -/
theorem functor_preservesFiniteLimits (I : Ideal R) :
    PreservesFiniteLimits (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R) := by
  let : (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Additive :=
    functor_additive I
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  have hinj : Function.Injective S.f := hS.injective_f
  refine ⟨?_, ?_⟩
  · rw [ShortComplex.moduleCat_exact_iff]
    have hexact := (ShortComplex.moduleCat_exact_iff S).mp hS.exact
    intro b hb
    have hb' : S.g b.val = 0 := congrArg Subtype.val hb
    obtain ⟨a, ha⟩ := hexact b.val hb'
    obtain ⟨n, hn⟩ := (mem_obj_iff I S.X₂ b.val).mp b.property
    refine ⟨⟨a, (mem_obj_iff I S.X₁ a).mpr ⟨n, fun r hr => ?_⟩⟩, ?_⟩
    · apply hinj
      change S.f (r • a) = S.f 0
      rw [map_smul, ha, hn r hr, map_zero]
    · apply Subtype.ext
      change S.f a = b.val
      exact ha
  · rw [ModuleCat.mono_iff_injective]
    intro a b hab
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val hab

section RightDerived

variable [HasInjectiveResolutions (ModuleCat.{v} R)]

/-- Actual right-derived torsion, using native injective resolutions and homology. -/
def localCohomologyFunctor (I : Ideal R) (q : ℕ) :
    ModuleCat.{v} R ⥤ ModuleCat.{v} R :=
  letI : (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Additive :=
    functor_additive I
  (functor I).rightDerived q

/-- Native right derivation retains the earned scalar linearity. -/
theorem localCohomologyFunctor_linear (I : Ideal R) (q : ℕ) :
    (localCohomologyFunctor I q : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Linear R := by
  let : (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Additive :=
    functor_additive I
  let : (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Linear R :=
    functor_linear I
  change ((functor I).rightDerived q).Linear R
  infer_instance

/-- The actual native degree-zero comparison, with no supplied inverse equation. -/
def toLocalCohomologyZero (I : Ideal R) :
    (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R) ⟶ localCohomologyFunctor I 0 :=
  letI : (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Additive :=
    functor_additive I
  (functor I).toRightDerivedZero

/-- Earned left exactness makes the native zero-degree comparison invertible. -/
def localCohomologyZeroIso (I : Ideal R) :
    localCohomologyFunctor I 0 ≅ (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R) :=
  letI : (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Additive :=
    functor_additive I
  letI : PreservesFiniteLimits (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R) :=
    functor_preservesFiniteLimits I
  (functor I).rightDerivedZeroIsoSelf

/-- The native zero-degree maps cancel on the actual primary-component functor. -/
theorem toLocalCohomologyZero_comp_zeroIso (I : Ideal R) :
    (toLocalCohomologyZero I :
      (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R) ⟶ localCohomologyFunctor I 0) ≫
      (localCohomologyZeroIso I).hom = 𝟙 (functor I) := by
  let : (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Additive :=
    functor_additive I
  let : PreservesFiniteLimits (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R) :=
    functor_preservesFiniteLimits I
  exact (functor I).rightDerivedZeroIsoSelf_inv_hom_id

end RightDerived

end ModuleCat.Torsion
