/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.BalancedTropicalCycles
public import MathlibExt.AlgebraicGeometry.TropicalCycleIntersections

/-!
# Balanced cycles, subdivision and the stable product

Osserman--Payne, 1007.1314v3, sections 2.4--2.7 and 5.2;
Fulton--Sturmfels, alg-geom/9403002v1, Theorem 3.2.
All sums, normals, weight subgroups and subdivision maps are actual native
constructions. Their closure and choice independence are the requested results.
Multiplicity comparisons are requested only at regular points (`RegularPoint`), which lie in the
relative interior of a cell of the common refinement of at least the expected dimension; at a new
vertex of a subdivision the raw displacement sum changes (for instance from one to two when a
line is cut into two rays).
Product comparison uses common refinements of nonzero weighted facets.
Extra zero cells impose no covering condition.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.BalancedTropicalCyclesWanted

open MathlibExt.AlgebraicGeometry.FiniteToricCoordinates
open MathlibExt.AlgebraicGeometry.IntegralTropicalCycles
open MathlibExt.AlgebraicGeometry.BalancedTropicalCycles
open MathlibExt.AlgebraicGeometry.TropicalCycleIntersections

def_wanted normal_data (n : ℕ) (C : Complex n) : NormalData C

theorem_wanted subdivision_balanced (n : ℕ) (A : WeightedComplex n)
    (N : NormalData A.complex) (_balanced : Balanced A N) (S : Subdivision A)
    (M : NormalData (subdivide S).complex) : Balanced (subdivide S) M

theorem_wanted refinement_multiplicity (n : ℕ) (A B : WeightedComplex n)
    (N : NormalData A.complex) (M : NormalData B.complex)
    (_balanced_A : Balanced A N) (_balanced_B : Balanced B M)
    (S : Subdivision A) (T : Subdivision B) (w v : RealSpace n)
    (_regular : RegularPoint A B w)
    (_regular_refined : RegularPoint (subdivide S) (subdivide T) w)
    (_generic : GenericDisplacement A B w v)
    (_generic_refined : GenericDisplacement (subdivide S) (subdivide T) w v) :
    stableMultiplicity (subdivide S) (subdivide T) w v = stableMultiplicity A B w v

theorem_wanted displacement_independent (n : ℕ) (A B : WeightedComplex n)
    (N : NormalData A.complex) (M : NormalData B.complex)
    (_balanced_A : Balanced A N) (_balanced_B : Balanced B M)
    (w u v : RealSpace n) (_regular : RegularPoint A B w)
    (_generic_u : GenericDisplacement A B w u)
    (_generic_v : GenericDisplacement A B w v) :
    stableMultiplicity A B w u = stableMultiplicity A B w v

def_wanted stable_product (n : ℕ) (A B : WeightedComplex n)
    (N : NormalData A.complex) (M : NormalData B.complex)
    (_balanced_A : Balanced A N) (_balanced_B : Balanced B M)
    (_dimension_A : A.dimension ≤ n) (_dimension_B : B.dimension ≤ n)
    (_proper_degree : n ≤ A.dimension + B.dimension) :
    {P : StableProduct A B // ∃ N : NormalData P.cycle.complex, Balanced P.cycle N}

def_wanted commutative_product_refinement (n : ℕ) (A B : WeightedComplex n)
    (N : NormalData A.complex) (M : NormalData B.complex)
    (_balanced_A : Balanced A N) (_balanced_B : Balanced B M)
    (_dimension_A : A.dimension ≤ n) (_dimension_B : B.dimension ≤ n)
    (_proper_degree : n ≤ A.dimension + B.dimension)
    (P : StableProduct A B) (Q : StableProduct B A) : CommonSubdivision P.cycle Q.cycle

def_wanted associative_product_refinement (n : ℕ) (A B C : WeightedComplex n)
    (N : NormalData A.complex) (M : NormalData B.complex) (L : NormalData C.complex)
    (_balanced_A : Balanced A N) (_balanced_B : Balanced B M) (_balanced_C : Balanced C L)
    (_dimension_A : A.dimension ≤ n) (_dimension_B : B.dimension ≤ n)
    (_dimension_C : C.dimension ≤ n)
    (_proper_degree : 2 * n ≤ A.dimension + B.dimension + C.dimension)
    (AB : StableProduct A B) (BC : StableProduct B C)
    (P : StableProduct AB.cycle C) (Q : StableProduct A BC.cycle) :
    CommonSubdivision P.cycle Q.cycle

def_wanted balanced_presentation (K : Type) [Field K] [Valued K NNReal]
    [IsAlgClosed K] [CompleteSpace K] (_nontrivial : NontrivialValuation K)
    (n : ℕ) (I : Ideal (MathlibExt.AlgebraicGeometry.ValuativeTropicalization.CoordinateRing K n))
    (P : Presentation K n I) :
    {N : NormalData P.cycle.complex // Balanced P.cycle N}

end WantedExt.AlgebraicGeometry.BalancedTropicalCyclesWanted
