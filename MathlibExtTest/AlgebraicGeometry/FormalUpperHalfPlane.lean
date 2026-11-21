/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalUpperHalfPlane

@[expose] public section

noncomputable section

open CerednikDrinfeld FormalOmega LT.LatticeTree

-- The vertex chart ring corepresents the vertex chart functor.
example (R : Type) [CommRing R] (q : ℕ) (B : Type) [CommRing B] [Algebra R B] :
    (chartVRing R q →ₐ[R] B) ≃ (chartV R q).obj B :=
  chartVRing.corepEquiv R q B

-- The edge chart ring corepresents the edge chart functor.
example (R : Type) [CommRing R] (π : R) (q : ℕ) (B : Type) [CommRing B] [Algebra R B] :
    (chartERing R π q →ₐ[R] B) ≃ (chartE R π q).obj B :=
  chartERing.corepEquiv R π q B

-- Unfolding: the point of the vertex chart ring has coordinate `ζ` with unit discriminant.
example (R : Type) [CommRing R] (q : ℕ) :
    IsUnit (chartVRing.ζ R q ^ q - chartVRing.ζ R q) :=
  chartVRing.isUnit_ζ_pow_sub R q

-- A nontrivial instance: over `ℤ`, the element `2` lies in the `q = 3` vertex chart
-- since `2 ^ 3 - 2 = 6` is not a unit, so use `ζ = -1`: `(-1) ^ 2 - (-1) = 2`, also not
-- a unit; instead the chart-ring point itself is the universal instance.
example (q : ℕ) : (chartV ℤ q).obj (chartVRing ℤ q) :=
  chartVRing.point ℤ q

-- The standard lattice is a full lattice, giving a vertex of the datum side.
example (R : Type*) [CommRing R] (K : Type*) [Field K] [Algebra R K] :
    FullLattice R K :=
  ⟨stdLattice R K, isFullLattice_stdLattice⟩
