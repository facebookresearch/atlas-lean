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

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.GradedCoordinates
public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.MultiplicativeCoordinates
public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# PBW coordinates in every homogeneous degree

For a chosen ordered basis, each enveloping filtration quotient identifies linearly with the
homogeneous polynomial module of the same degree. Degree zero is the scalar filtration stage
modulo zero.

The homogeneous comparisons assemble into a linear equivalence from the direct sum of all
graded quotients to the polynomial algebra.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped DirectSum

namespace UniversalEnvelopingAlgebra.PBW

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- The lower stage, considered inside the degree stage. -/
def gradedLowerStage : (n : ℕ) → Submodule R (UniversalEnvelopingAlgebra.degreeFiltration R L n)
  | 0 => ⊥
  | q + 1 => (UniversalEnvelopingAlgebra.degreeFiltration R L q).comap
      (UniversalEnvelopingAlgebra.degreeFiltration R L (q + 1)).subtype

/-- The enveloping algebra filtration quotient in every degree. -/
abbrev GradedLayer (n : ℕ) :=
  UniversalEnvelopingAlgebra.degreeFiltration R L n ⧸ gradedLowerStage R L n

variable {R L} {I : Type w} [LinearOrder I]

/-- The computed leading projection on every filtration stage. -/
def completeGradedProjection (b : Module.Basis I R L) (n : ℕ) :
    UniversalEnvelopingAlgebra.degreeFiltration R L n →ₗ[R]
      MvPolynomial.homogeneousSubmodule I R n where
  toFun u := ⟨MvPolynomial.homogeneousComponent n (polynomialCoordinates b u.val),
    MvPolynomial.homogeneousComponent_mem n _⟩
  map_add' u v := by
    apply Subtype.ext
    change MvPolynomial.homogeneousComponent n (polynomialCoordinates b (u.val + v.val)) =
      MvPolynomial.homogeneousComponent n (polynomialCoordinates b u.val) +
        MvPolynomial.homogeneousComponent n (polynomialCoordinates b v.val)
    simp only [map_add]
  map_smul' r u := by
    apply Subtype.ext
    change MvPolynomial.homogeneousComponent n (polynomialCoordinates b (r • u.val)) =
      (RingHom.id R) r • MvPolynomial.homogeneousComponent n (polynomialCoordinates b u.val)
    simp only [map_smul, RingHom.id_apply]

/-- The lower stage is the kernel, including the zero lower stage at degree zero. -/
theorem completeGradedProjection_ker (b : Module.Basis I R L) (n : ℕ) :
    LinearMap.ker (completeGradedProjection b n) = gradedLowerStage R L n := by
  cases n with
  | zero =>
      ext u
      change completeGradedProjection b 0 u = 0 ↔ u = 0
      have hself : MvPolynomial.homogeneousComponent 0 (polynomialCoordinates b u.val) =
          polynomialCoordinates b u.val :=
        MvPolynomial.homogeneousComponent_zero_eq_self_of_mem_degree_zero
          ((polynomialCoordinates_mem_degree_iff b 0 u.val).mpr u.property)
      constructor
      · intro hu
        apply Subtype.ext
        apply (polynomialCoordinates b).injective
        change polynomialCoordinates b u.val = polynomialCoordinates b (0 : UniversalEnvelopingAlgebra R L)
        rw [map_zero]
        exact hself.symm.trans (congrArg Subtype.val hu)
      · intro hu
        subst u
        exact (completeGradedProjection b 0).map_zero
  | succ q =>
      simpa only [completeGradedProjection, gradedProjection, gradedLowerStage] using
        gradedProjection_ker b q

/-- Every homogeneous polynomial has a preimage in the enveloping algebra stage. -/
theorem completeGradedProjection_surjective (b : Module.Basis I R L) (n : ℕ) :
    Function.Surjective (completeGradedProjection b n) := by
  intro p
  let u := (polynomialCoordinates b).symm p.val
  have hu : u ∈ UniversalEnvelopingAlgebra.degreeFiltration R L n := by
    apply (polynomialCoordinates_mem_degree_iff b n u).mp
    rw [show polynomialCoordinates b u = p.val from (polynomialCoordinates b).apply_symm_apply p.val]
    exact MvPolynomial.IsHomogeneous.mem_restrictTotalDegree p.property
  refine ⟨⟨u, hu⟩, ?_⟩
  apply Subtype.ext
  change MvPolynomial.homogeneousComponent n (polynomialCoordinates b u) = p.val
  rw [show polynomialCoordinates b u = p.val from (polynomialCoordinates b).apply_symm_apply p.val]
  exact MvPolynomial.homogeneousComponent_eq_self p.property

/-- The quotient equivalence in every degree. -/
def completeGradedEquiv (b : Module.Basis I R L) (n : ℕ) :
    GradedLayer R L n ≃ₗ[R] MvPolynomial.homogeneousSubmodule I R n :=
  (Submodule.quotEquivOfEq _ _ (completeGradedProjection_ker b n).symm).trans
    ((completeGradedProjection b n).quotKerEquivOfSurjective
      (completeGradedProjection_surjective b n))

theorem completeGradedEquiv_mk (b : Module.Basis I R L) (n : ℕ)
    (u : UniversalEnvelopingAlgebra.degreeFiltration R L n) :
    completeGradedEquiv b n ((gradedLowerStage R L n).mkQ u) =
      completeGradedProjection b n u := by
  simp only [completeGradedEquiv, LinearEquiv.trans_apply, Submodule.mkQ_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

variable (R L) in
/-- The direct sum of the enveloping algebra graded quotients, with finite support. -/
abbrev GradedModule := ⨁ n, GradedLayer R L n

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The graded-module PBW equivalence, assembled from all quotients and the polynomial
decomposition. -/
def completeGradedModuleEquiv (b : Module.Basis I R L) :
    GradedModule R L ≃ₗ[R] MvPolynomial I R :=
  (DirectSum.congrLinearEquiv (completeGradedEquiv b)).trans
    (DirectSum.decomposeLinearEquiv (MvPolynomial.homogeneousSubmodule I R)).symm

@[simp]
theorem completeGradedModuleEquiv_lof (b : Module.Basis I R L) (n : ℕ)
    (x : GradedLayer R L n) :
    completeGradedModuleEquiv b (DirectSum.lof R ℕ (GradedLayer R L) n x) =
      (completeGradedEquiv b n x).val := by
  change (DirectSum.decomposeLinearEquiv (MvPolynomial.homogeneousSubmodule I R)).symm
    (DirectSum.lmap (fun n => (completeGradedEquiv b n).toLinearMap)
      (DirectSum.lof R ℕ (GradedLayer R L) n x)) = _
  rw [DirectSum.lmap_lof, DirectSum.decomposeLinearEquiv_symm_lof]
  rfl

end UniversalEnvelopingAlgebra.PBW
