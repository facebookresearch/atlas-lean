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

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.FilteredCoordinates
public import MathlibExt.RingTheory.MvPolynomial.HomogeneousVariable
public import MathlibExt.LinearAlgebra.Filtration.Exactness
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Coordinates on positive adjacent enveloping quotients

For an R-Lie algebra L over a commutative ring R and an ordered basis b : Basis I R L, the
highest homogeneous PBW projection on D_{q+1} has kernel D_q inside that stage and is
surjective onto homogeneous polynomials of degree q+1.

It therefore induces an R-linear equivalence D_{q+1}/D_q ≃ MvPolynomial_homogeneous(q+1) for
every q ∈ ℕ. The quotient is the positive adjacent filtration layer, with the degree index q+1
retained explicitly.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "P" => MvPolynomial I R

/-- Let R be a commutative ring, L an R-Lie algebra, b : Basis I R L with LinearOrder I, and q ∈
ℕ. Define the R-linear map D_{q+1} → MvPolynomial.homogeneousSubmodule I R (q+1) by taking the
degree-(q+1) homogeneous component of the PBW polynomial coordinate. This is the top-degree
projection on that positive filtration stage. -/
def gradedProjection (b : Module.Basis I R L) (q : ℕ) :
    UniversalEnvelopingAlgebra.degreeFiltration R L (q + 1) →ₗ[R]
      MvPolynomial.homogeneousSubmodule I R (q + 1) where
  toFun u := ⟨MvPolynomial.homogeneousComponent (q + 1) (polynomialCoordinates b u.val),
    MvPolynomial.homogeneousComponent_mem (q + 1) _⟩
  map_add' u v := by
    apply Subtype.ext
    change MvPolynomial.homogeneousComponent (q + 1)
        (polynomialCoordinates b (u.val + v.val)) =
      MvPolynomial.homogeneousComponent (q + 1) (polynomialCoordinates b u.val) +
        MvPolynomial.homogeneousComponent (q + 1) (polynomialCoordinates b v.val)
    simp only [map_add]
  map_smul' r u := by
    apply Subtype.ext
    change MvPolynomial.homogeneousComponent (q + 1) (polynomialCoordinates b (r • u.val)) =
      (RingHom.id R) r • MvPolynomial.homogeneousComponent (q + 1) (polynomialCoordinates b u.val)
    simp only [map_smul, RingHom.id_apply]

/-- For an ordered basis b : Basis I R L of an R-Lie algebra over a commutative ring R and q ∈ ℕ,
the kernel of the degree-(q+1) PBW projection on D_{q+1} is {u ∈ D_{q+1} | u ∈ D_q}. It is the
inverse image of D_q under the subtype inclusion D_{q+1} → U_R(L), so the kernel is expressed
in the upper-stage carrier. -/
theorem gradedProjection_ker (b : Module.Basis I R L) (q : ℕ) :
    LinearMap.ker (gradedProjection b q) =
      (UniversalEnvelopingAlgebra.degreeFiltration R L q).comap
        (UniversalEnvelopingAlgebra.degreeFiltration R L (q + 1)).subtype := by
  ext u
  change gradedProjection b q u = 0 ↔
    u.val ∈ UniversalEnvelopingAlgebra.degreeFiltration R L q
  have hupper : polynomialCoordinates b u.val ∈ MvPolynomial.restrictTotalDegree I R (q + 1) :=
    (polynomialCoordinates_mem_degree_iff b (q + 1) u.val).mpr u.property
  constructor
  · intro hu
    have hzero : MvPolynomial.homogeneousComponent (q + 1) (polynomialCoordinates b u.val) = 0 :=
      congrArg Subtype.val hu
    apply (polynomialCoordinates_mem_degree_iff b q u.val).mp
    exact (MvPolynomial.mem_restrictTotalDegree_iff_highestComponent_zero q _ hupper).mpr hzero
  · intro hu
    apply Subtype.ext
    exact (MvPolynomial.mem_restrictTotalDegree_iff_highestComponent_zero q _ hupper).mp
      ((polynomialCoordinates_mem_degree_iff b q u.val).mpr hu)

/-- Let R be a commutative ring, L an R-Lie algebra, b : Basis I R L with LinearOrder I, and q ∈
ℕ. Every homogeneous polynomial of degree q+1 in MvPolynomial I R is the degree-(q+1)
homogeneous PBW coordinate of some u ∈ D_{q+1}. Thus the highest-coordinate projection on this
positive stage is surjective. -/
theorem gradedProjection_surjective (b : Module.Basis I R L) (q : ℕ) :
    Function.Surjective (gradedProjection b q) := by
  intro p
  let u : U := (polynomialCoordinates b).symm p.val
  have hu : u ∈ UniversalEnvelopingAlgebra.degreeFiltration R L (q + 1) := by
    apply (polynomialCoordinates_mem_degree_iff b (q + 1) u).mp
    rw [show polynomialCoordinates b u = p.val from (polynomialCoordinates b).apply_symm_apply p.val]
    exact MvPolynomial.IsHomogeneous.mem_restrictTotalDegree p.property
  refine ⟨⟨u, hu⟩, ?_⟩
  apply Subtype.ext
  change MvPolynomial.homogeneousComponent (q + 1) (polynomialCoordinates b u) = p.val
  rw [show polynomialCoordinates b u = p.val from (polynomialCoordinates b).apply_symm_apply p.val]
  exact MvPolynomial.homogeneousComponent_eq_self p.property

/-- For an ordered basis b : Basis I R L over a commutative ring R and q ∈ ℕ, the top PBW
projection induces D_{q+1}/D_q ≃ₗ[R] MvPolynomial.homogeneousSubmodule I R (q+1). The
denominator is considered inside D_{q+1}, as in Submodule.FiltrationLayer. The equivalence
sends a representative to its degree-(q+1) homogeneous polynomial coordinate. -/
def gradedEquiv (b : Module.Basis I R L) (q : ℕ) :
    Submodule.FiltrationLayer (UniversalEnvelopingAlgebra.degreeFiltration R L) q ≃ₗ[R]
      MvPolynomial.homogeneousSubmodule I R (q + 1) :=
  (Submodule.quotEquivOfEq _ _ (gradedProjection_ker b q).symm).trans
    ((gradedProjection b q).quotKerEquivOfSurjective (gradedProjection_surjective b q))

end UniversalEnvelopingAlgebra.PBW
