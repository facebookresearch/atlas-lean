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
# PBW coordinates on every degree quotient

Let R be a commutative ring and L an R-Lie algebra, with degree filtration D_n on U_R(L).
Define D_{<0}=0 and D_{<n+1}=D_n inside D_{n+1}, and put G_n=D_n/D_{<n}.

For an ordered basis b : Basis I R L, the degree-n homogeneous component of the PBW polynomial
coordinate is a surjective map D_n → MvPolynomial_homogeneous(n) with kernel D_{<n}. It gives
G_n ≃ₗ[R] MvPolynomial_homogeneous(n), including degree zero. These equivalences assemble over
all n into ⊕_n G_n ≃ₗ[R] MvPolynomial I R.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped DirectSum

namespace UniversalEnvelopingAlgebra.PBW

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- For an R-Lie algebra L over a commutative ring R, let D_n ⊆ U_R(L) be the degree filtration.
Define a submodule of D_n by D_{<0}=0 and D_{<q+1}={u ∈ D_{q+1} | u ∈ D_q}. Equivalently, at
q+1 it is the inverse image of D_q under the subtype inclusion D_{q+1} → U_R(L). This defines
the lower denominator in every degree without natural-number truncation at degree zero. -/
def gradedLowerStage : (n : ℕ) → Submodule R (UniversalEnvelopingAlgebra.degreeFiltration R L n)
  | 0 => ⊥
  | q + 1 => (UniversalEnvelopingAlgebra.degreeFiltration R L q).comap
      (UniversalEnvelopingAlgebra.degreeFiltration R L (q + 1)).subtype

/-- Let R be a commutative ring, L an R-Lie algebra, and n ∈ ℕ. Define G_n = D_n/D_{<n}, where D_n
is the degree filtration of U_R(L), D_{<0}=0, and D_{<q+1} is D_q considered inside D_{q+1}.
Thus G_0 is D_0 modulo zero and G_{q+1} is the adjacent quotient D_{q+1}/D_q. -/
abbrev GradedLayer (n : ℕ) :=
  UniversalEnvelopingAlgebra.degreeFiltration R L n ⧸ gradedLowerStage R L n

variable {R L} {I : Type w} [LinearOrder I]

/-- Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L with LinearOrder I. For n
∈ ℕ define D_n →ₗ[R] MvPolynomial.homogeneousSubmodule I R n by u ↦
homogeneousComponent_n(polynomialCoordinates_b(u)). The polynomial coordinate is the R-linear
PBW coordinate of the enveloping element, and the displayed projection retains only its
homogeneous degree-n part. -/
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

/-- Let b : Basis I R L be an ordered basis of an R-Lie algebra over a commutative ring R. For
every n ∈ ℕ, the kernel of u ↦ homogeneousComponent_n(polynomialCoordinates_b(u)) on D_n is
exactly D_{<n}. At n=0 this kernel is zero; at n=q+1 it is the preceding filtration stage D_q
inside D_{q+1}. -/
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

/-- Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L with LinearOrder I. For
every n ∈ ℕ, the map D_n → MvPolynomial.homogeneousSubmodule I R n given by the degree-n
homogeneous PBW coordinate is surjective. Thus every homogeneous polynomial of degree n is the
top coordinate of an enveloping element lying in filtration stage n. -/
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

/-- For an ordered basis b : Basis I R L of an R-Lie algebra over a commutative ring R and n ∈ ℕ,
the top PBW projection induces an R-linear equivalence G_n=D_n/D_{<n} ≃ₗ[R]
MvPolynomial.homogeneousSubmodule I R n. It sends the class of u ∈ D_n to
homogeneousComponent_n(polynomialCoordinates_b(u)). Its well-definedness and bijectivity use
the lower-stage kernel identity and surjectivity of this projection. -/
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
/-- Let R be a commutative ring and L an R-Lie algebra. Define the graded R-module GradedModule R
L to be ⊕_{n∈ℕ} G_n, where G_n=D_n/D_{<n} is the degree-n quotient of the enveloping degree
filtration. Its elements have finite support in the degree index. The quotient layers include
degree zero with denominator zero. -/
abbrev GradedModule := ⨁ n, GradedLayer R L n

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L with LinearOrder I. The
degreewise quotient equivalences G_n ≃ₗ[R] MvPolynomial.homogeneousSubmodule I R n assemble
into an R-linear equivalence ⊕_n G_n ≃ₗ[R] MvPolynomial I R. It applies the homogeneous
coordinate map to each finite-support layer and sums the resulting homogeneous polynomials. -/
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
