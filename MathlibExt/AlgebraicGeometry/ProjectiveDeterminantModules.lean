/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from AxiomMath/Stacks (https://github.com/AxiomMath/Stacks),
revision c496df0d9beea9deaeabcea8492605f9a0a2313b, licensed under the Apache License,
Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0). The source files carry no
individual copyright or author notice.

* `StacksFrontier/Algebra/Module/Projective/Determinant/Basic/RankStrata.lean`
* `StacksFrontier/Algebra/Module/Projective/Determinant/Basic/Det.lean`
* `StacksFrontier/Homology/TwoTermComplex/DeterminantLine/SurjectiveQuasiIso.lean`

Modifications: the source's exterior-annihilator description is used as the literal native
module, with actual exterior-algebra maps.
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import MathlibExt.LinearAlgebra.ExteriorPowerSemilinear

/-!
# Actual projective determinant modules and exact-sequence normalization

For a finite projective module, the source proves that its rank-stratum
determinant is the submodule of the exterior algebra annihilated by wedge
multiplication by every vector. We use that actual module, retaining the
exterior inclusion, actual maps, and the ordered kernel/quotient wedge law.
Neither a freely assigned line nor a scalar trivialization replaces it.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ProjectiveDeterminantModules

universe u v w

variable (R : Type u) [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M]

/-- The actual exterior-annihilator submodule, source-equal to the
rank-stratum determinant for finite projective modules. -/
def determinantSubmodule : Submodule R (ExteriorAlgebra R M) :=
  ⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))

/-- The determinant module retains its actual exterior-algebra inclusion. -/
abbrev determinantModule := ↥(determinantSubmodule R M)

variable {R M}

/-- A surjection carries the actual exterior annihilator into the target annihilator. -/
theorem map_mem_of_surjective {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) (x : determinantModule R M) :
    ExteriorAlgebra.map f x.val ∈ determinantSubmodule R N := by
  simp only [determinantSubmodule, Submodule.mem_iInf, LinearMap.mem_ker]
  intro n
  obtain ⟨m, rfl⟩ := hf n
  have hx := x.property
  simp only [determinantSubmodule, Submodule.mem_iInf, LinearMap.mem_ker] at hx
  have hm := congrArg (ExteriorAlgebra.map f) (hx m)
  simpa only [LinearMap.mulLeft_apply, map_mul, ExteriorAlgebra.map_apply_ι, map_zero] using hm

/-- The actual induced determinant map of a surjective module map. -/
def surjectiveMap {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    determinantModule R M →ₗ[R] determinantModule R N :=
  ((ExteriorAlgebra.map f).toLinearMap.comp (determinantSubmodule R M).subtype).codRestrict
    (determinantSubmodule R N) (map_mem_of_surjective f hf)

/-- The induced determinant equivalence is computed from the actual exterior maps. -/
def determinantEquiv {N : Type w} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    determinantModule R M ≃ₗ[R] determinantModule R N :=
  LinearEquiv.ofLinearMap (surjectiveMap e.toLinearMap e.surjective)
    (surjectiveMap e.symm.toLinearMap e.symm.surjective) (by
      ext x
      change ExteriorAlgebra.map e.toLinearMap
        (ExteriorAlgebra.map e.symm.toLinearMap x.val) = x.val
      rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
      simp) (by
      ext x
      change ExteriorAlgebra.map e.symm.toLinearMap
        (ExteriorAlgebra.map e.toLinearMap x.val) = x.val
      rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
      simp)

/-- The proposition that the determinant module of a finite projective module $M$ over a
commutative ring $R$ is invertible: `determinantModule R M`, the submodule of the exterior algebra
of $M$ annihilated by left multiplication by every vector of $M$, is an invertible $R$-module. -/
structure InvertibleDeterminant [Module.Finite R M] [Module.Projective R M] : Prop where
  invertible : Module.Invertible R (determinantModule R M)

/-- The source exact-sequence producer is fixed by the ordered exterior
product of the actual kernel inclusion and every lift from the quotient. -/
structure ShortExactDeterminant {N : Type w} [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) where
  comparison : TensorProduct R (determinantModule R (LinearMap.ker f))
    (determinantModule R N) ≃ₗ[R] determinantModule R M
  normalization : ∀ (x : determinantModule R (LinearMap.ker f))
    (y : determinantModule R N) (z : ExteriorAlgebra R M),
    ExteriorAlgebra.map f z = y.val →
      (comparison (x ⊗ₜ[R] y)).val =
        ExteriorAlgebra.map (LinearMap.ker f).subtype x.val * z

/-- The actual scalar-extension universal property of a fixed semilinear map. -/
def IsScalarExtension {S : Type w} [CommRing S]
    {N : Type w} [AddCommGroup N] [Module S N]
    (φ : R →+* S) (f : M →ₛₗ[φ] N) : Prop :=
  ∀ P : ModuleCat.{w} S, Function.Bijective (fun g : N →ₗ[S] P => g.comp f)

/-- Base change of determinant modules along a ring map $\varphi : R \to S$: for a finite projective
$R$-module $M$, a finite projective $S$-module $N$ and a $\varphi$-semilinear map $f : M \to N$
exhibiting $N$ as the scalar extension of $M$ (`IsScalarExtension`), a $\varphi$-semilinear map from
the determinant module of $M$ to that of $N$ that agrees on every element with the
exterior-algebra map induced by $f$ and itself exhibits the determinant module of $N$ as the
scalar extension of that of $M$. The determinant module is `determinantModule`, the submodule of
the exterior algebra annihilated by left multiplication by every vector. -/
structure BaseChangeDeterminant {S : Type w} [CommRing S]
    {N : Type w} [AddCommGroup N] [Module S N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite S N] [Module.Projective S N]
    (φ : R →+* S) (f : M →ₛₗ[φ] N) (h : IsScalarExtension φ f) where
  map : determinantModule R M →ₛₗ[φ] determinantModule S N
  normalization : ∀ x : determinantModule R M,
    (map x).val = ExteriorAlgebra.mapₛₗ φ f x.val
  scalarExtension : IsScalarExtension φ map

end MathlibExt.AlgebraicGeometry.ProjectiveDeterminantModules
