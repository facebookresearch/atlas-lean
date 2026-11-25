/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IntegralTropicalCycles
public import MathlibExt.AlgebraicGeometry.ValuativeTropicalization
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Analysis.Convex.Intrinsic

/-!
# Weighted presentations of the existing valued tropicalization

The support is the actual valuation-vector closure already constructed in
I3. Facet weights are fixed by generic-stalk lengths of its actual initial
degenerations. Constants lie in the working field's value group. The working
field can be a genuine nontrivially valued extension of an originally trivial
valued field; no change of the existing I3 initial/support primitives occurs.

Proper intersection is tested by the actual affine dimensions of the intersections of the
nonzero weighted facets through the point. This is the input of Osserman--Payne,
*Lifting Tropical Intersections*, 1007.1314v3, Theorems 1.1 and 5.1.1.
The latter's weighted Tor equality is distinct from general scheme
multiplicity equality, which only holds with its additional CM hypotheses.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.TropicalCycleIntersections

open _root_.AlgebraicGeometry TopologicalSpace
open FiniteToricCoordinates IntegralTropicalCycles ValuativeTropicalization

variable (K : Type) [Field K] [Valued K NNReal] (n : ℕ)

def NontrivialValuation : Prop :=
  ∃ a : Kˣ, (Valued.v : Valuation K NNReal) (a : K) ≠ 1

def PureDimension (I : Ideal (ValuativeTropicalization.CoordinateRing K n)) (d : ℕ) : Prop :=
  ∀ Z ∈ irreducibleComponents (subscheme I).left,
    topologicalKrullDim Z = ((d : ℕ∞) : WithBot ℕ∞)

/-- A presentation is tied to the exact initial/support construction. -/
structure Presentation (I : Ideal (ValuativeTropicalization.CoordinateRing K n)) where
  cycle : WeightedComplex n
  dimension_le : cycle.dimension ≤ n
  pure : PureDimension K n I cycle.dimension
  support : cycle.support = tropicalizationOver (L := K) I
  constants : ∀ i j, ∃ a : Kˣ,
    (cycle.complex.cell i).constant j = -Real.log
      ((Valued.v : Valuation K NNReal) (a : K) : ℝ)
  initialNoetherian : ∀ t : Fin n → Kˣ, IsNoetherian (geometricInitialScheme I t).left
  weight_normalization : ∀ i (t : Fin n → Kˣ),
    weightVector t ∈ intrinsicInterior ℝ (cycle.complex.cell i).carrier →
    (cycle.complex.cell i).dimension = cycle.dimension →
      letI : IsNoetherian (geometricInitialScheme I t).left := initialNoetherian t
      cycle.weight i = tropicalMultiplicity I t
  positive : ∀ i, (cycle.complex.cell i).carrier.Nonempty →
    (cycle.complex.cell i).dimension = cycle.dimension → 0 < cycle.weight i

def intersectionDimension (P Q : Polyhedron n) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (P.carrier ∩ Q.carrier)).direction

/-- The supports of `A` and `B` meet properly at `w`: every pair of nonzero weighted facets
through `w` meets in at most the expected dimension. Cells of weight zero are not part of the
supports and are ignored, so the condition does not depend on the presentation. -/
def ProperAt (A B : WeightedComplex n) (w : RealSpace n) : Prop :=
  w ∈ A.support ∩ B.support ∧ n ≤ A.dimension + B.dimension ∧
    ∀ i j, A.weight i ≠ 0 → B.weight j ≠ 0 →
      w ∈ (A.complex.cell i).carrier → w ∈ (B.complex.cell j).carrier →
      intersectionDimension n (A.complex.cell i) (B.complex.cell j) ≤
        A.dimension + B.dimension - n

def intersectionIdeal (I J : Ideal (ValuativeTropicalization.CoordinateRing K n)) := I ⊔ J

end MathlibExt.AlgebraicGeometry.TropicalCycleIntersections
