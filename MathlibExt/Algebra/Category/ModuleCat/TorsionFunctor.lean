/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Avocado
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import MathlibExt.CategoryTheory.Abelian.RightDerived.Linear

/-!
# Power-torsion functors and local cohomology

Let `R : Type u` be a commutative ring and `I` an ideal. For `M : ModuleCat.{v} R`, the power-
torsion module `Γ_I(M)` consists of elements annihilated by every scalar in `I^n` for some
natural `n`. Restriction of module maps gives an additive, `R`-linear functor with a natural
inclusion in the identity functor.

The functor preserves finite limits. Given injective resolutions in the chosen module
category, its right-derived functors define `H_I^q(-)`. Degree-zero local cohomology is
naturally `Γ_I`, and the canonical map to the zeroth derived functor is inverse to this
comparison. Scalar and module-carrier universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat.Torsion

variable {R : Type u} [CommRing R]

/-- Power-torsion module as a functor.

For an ideal `I`, the functor takes `M` to `Ideal.primaryComponent M I` and restricts each
module map to this submodule. It acts on `ModuleCat.{v} R` with ring universe `u` independent
of `v`. -/
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

/-- Power-torsion functor map retains the underlying module map.

For `f : M ⟶ N` and `a : Γ_I(M)`, the underlying element of `Γ_I(f)(a)` is `f(a.val)`. -/
theorem map_val (I : Ideal R) {M N : ModuleCat.{v} R} (f : M ⟶ N)
    (a : (functor I).obj M) :
    (((functor I).map f).hom a).val = f.hom a.val := rfl

/-- Natural inclusion of power torsion in its module.

The subtype maps `Γ_I(M) ⟶ M` form a natural transformation from the power-torsion functor to
the identity on the module category. -/
def inclusion (I : Ideal R) : functor I ⟶ 𝟭 (ModuleCat.{v} R) where
  app M := ModuleCat.ofHom (Ideal.primaryComponent (M : Type v) I).subtype
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    ext a
    rfl

/-- Power-torsion membership is annihilation by a whole ideal power.

An element `a : M` belongs to `Γ_I(M)` exactly when some natural `n` satisfies `r • a = 0` for
every `r ∈ I^n`. -/
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

/-- Power-torsion functor preserves addition of morphisms.

For an ideal `I`, the restricted power-torsion maps preserve sums of `R`-linear module
morphisms. -/
theorem functor_additive (I : Ideal R) :
    (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    rfl

/-- Power-torsion functor is linear over the scalar ring.

For an ideal `I`, the power-torsion functor preserves `R`-scalar multiplication of module
morphisms. -/
theorem functor_linear (I : Ideal R) :
    (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Linear R where
  map_smul := by
    intro M N f r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    rfl

/-- Power-torsion functor is left exact.

The power-torsion functor preserves finite limits in `ModuleCat.{v} R`, including kernels and
finite products. -/
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

/-- Local cohomology as the right-derived power-torsion functor.

Assuming injective resolutions in `ModuleCat.{v} R`, the degree-`q` right-derived functor of
`Γ_I` defines `localCohomologyFunctor I q` on that same module category. -/
def localCohomologyFunctor (I : Ideal R) (q : ℕ) :
    ModuleCat.{v} R ⥤ ModuleCat.{v} R :=
  letI : (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Additive :=
    functor_additive I
  (functor I).rightDerived q

/-- Local cohomology functors are linear over the scalar ring.

Under the injective-resolution hypothesis, each degree-`q` local cohomology functor preserves
`R`-scalar multiplication of morphisms. -/
theorem localCohomologyFunctor_linear (I : Ideal R) (q : ℕ) :
    (localCohomologyFunctor I q : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Linear R := by
  let : (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Additive :=
    functor_additive I
  let : (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Linear R :=
    functor_linear I
  change ((functor I).rightDerived q).Linear R
  infer_instance

/-- Canonical map from power torsion to zeroth local cohomology.

Under the injective-resolution hypothesis, the right-derived degree-zero transformation gives
`Γ_I ⟶ H_I^0`. -/
def toLocalCohomologyZero (I : Ideal R) :
    (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R) ⟶ localCohomologyFunctor I 0 :=
  letI : (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Additive :=
    functor_additive I
  (functor I).toRightDerivedZero

/-- Zeroth local cohomology is the power-torsion functor.

Since `Γ_I` is left exact, its degree-zero right-derived functor is naturally isomorphic to
`Γ_I`, assuming the chosen module category has injective resolutions. -/
def localCohomologyZeroIso (I : Ideal R) :
    localCohomologyFunctor I 0 ≅ (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R) :=
  letI : (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R).Additive :=
    functor_additive I
  letI : PreservesFiniteLimits (functor I : ModuleCat.{v} R ⥤ ModuleCat.{v} R) :=
    functor_preservesFiniteLimits I
  (functor I).rightDerivedZeroIsoSelf

/-- Power-torsion comparison with degree-zero local cohomology is inverse.

The canonical map `Γ_I ⟶ H_I^0` followed by the forward map of `localCohomologyZeroIso I` is
the identity transformation of `Γ_I`. -/
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
