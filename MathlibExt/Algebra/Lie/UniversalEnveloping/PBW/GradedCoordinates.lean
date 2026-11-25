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
# Coordinates on adjacent PBW filtration quotients

For a chosen ordered basis, the highest homogeneous PBW coordinate projection on filtration
degree q + 1 has the preceding filtration stage as its kernel.

The induced linear equivalence identifies the adjacent filtration quotient with homogeneous
polynomials of degree q + 1.
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

/-- The highest homogeneous polynomial projection on a enveloping algebra stage. -/
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

/-- The highest component kernel is exactly the previous filtration stage, inside the upper-stage
carrier. -/
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

/-- Every homogeneous polynomial has an enveloping algebra preimage in the degree stage. -/
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

/-- The linear equivalence from the adjacent enveloping filtration quotient to homogeneous
polynomials of degree q + 1. -/
def gradedEquiv (b : Module.Basis I R L) (q : ℕ) :
    Submodule.FiltrationLayer (UniversalEnvelopingAlgebra.degreeFiltration R L) q ≃ₗ[R]
      MvPolynomial.homogeneousSubmodule I R (q + 1) :=
  (Submodule.quotEquivOfEq _ _ (gradedProjection_ker b q).symm).trans
    ((gradedProjection b q).quotKerEquivOfSurjective (gradedProjection_surjective b q))

end UniversalEnvelopingAlgebra.PBW
