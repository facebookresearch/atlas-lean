/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BalancedTropicalCycles
public import MathlibExt.AlgebraicGeometry.TropicalTorIntersection

/-!
# Proper tropical intersections inside a general ambient variety

The ambient point is in the relative interior of an actual multiplicity-one
facet. Displacement occurs in that facet's direction space, and the index is
computed inside its actual integral lattice. Component weights are the
existing initial-scheme lengths; coefficients are the local Tor construction.
Only actual minimal-prime components whose tropicalizations contain the face
participate in the sum.

Reference: Osserman--Payne, *Lifting Tropical Intersections*, 1007.1314v3,
Definition 2.3.2, Theorems 1.2 and 5.1.1, Corollary 5.1.3, Appendix A.4.
Native quotient, localization, minimal-prime and Tor operations are credited
in `TropicalTorIntersection`. No regularity, CM or higher-Tor conclusion is
folded into the properness or simple-point definitions.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralAmbientTropicalIntersections

open FiniteToricCoordinates IntegralTropicalCycles TropicalCycleIntersections
open TropicalTorIntersection ValuativeTropicalization
open scoped BigOperators

variable {n : ℕ}

structure SimplePoint (Y : WeightedComplex n) (w : RealSpace n) where
  facet : Fin Y.complex.count
  interior : w ∈ intrinsicInterior ℝ (Y.complex.cell facet).carrier
  dimension : (Y.complex.cell facet).dimension = Y.dimension
  multiplicity_one : Y.weight facet = 1

/-- The supports of `A` and `B` meet properly at `w` inside `Y`: every pair of nonzero weighted
facets through `w` meets in at most the expected dimension `dim A + dim B - dim Y`. Cells of
weight zero are ignored. -/
def ProperIn (Y A B : WeightedComplex n) (w : RealSpace n) : Prop :=
  w ∈ A.support ∩ B.support ∧ Y.dimension ≤ A.dimension + B.dimension ∧
    ∀ i j, A.weight i ≠ 0 → B.weight j ≠ 0 →
      w ∈ (A.complex.cell i).carrier → w ∈ (B.complex.cell j).carrier →
      TropicalCycleIntersections.intersectionDimension n (A.complex.cell i)
        (B.complex.cell j) ≤ A.dimension + B.dimension - Y.dimension

structure IntersectionFacet (Y A B : WeightedComplex n) (tau : Polyhedron n) where
  nonempty : tau.carrier.Nonempty
  dimension : tau.dimension = A.dimension + B.dimension - Y.dimension
  support : tau.carrier ⊆ A.support ∩ B.support
  cell_intersection : ∃ i j,
    tau.carrier = (A.complex.cell i).carrier ∩ (B.complex.cell j).carrier

variable {Y A B : WeightedComplex n} {w : RealSpace n} (S : SimplePoint Y w)

def ambientDirection : Submodule ℝ (RealSpace n) :=
  (affineSpan ℝ (Y.complex.cell S.facet).carrier).direction

def ambientLattice : AddSubgroup (Lattice n) := (Y.complex.cell S.facet).lattice

/-- A displacement `v` inside the ambient direction is generic relative to `A` and `B` at `w`: it
avoids the direction sum of every pair of cells through `w` that does not contain the ambient
direction (Osserman--Payne, Theorem 5.1.1, take the generic vector in the ambient facet's
direction). Only cells inside the weighted supports count, and pairs whose direction sum contains
the ambient direction impose no condition, so padding cells of weight zero never constrain the
displacement. -/
def RelativeGeneric (A B : WeightedComplex n) (v : RealSpace n) : Prop :=
  v ∈ ambientDirection S ∧
    ∀ i j, (A.complex.cell i).carrier ⊆ A.support → (B.complex.cell j).carrier ⊆ B.support →
      w ∈ (A.complex.cell i).carrier → w ∈ (B.complex.cell j).carrier →
      ¬ ambientDirection S ≤ (affineSpan ℝ (A.complex.cell i).carrier).direction ⊔
        (affineSpan ℝ (B.complex.cell j).carrier).direction →
      v ∉ (affineSpan ℝ (A.complex.cell i).carrier).direction ⊔
        (affineSpan ℝ (B.complex.cell j).carrier).direction

def relativeIndex (P Q : Polyhedron n) : ℤ :=
  (((P.lattice.comap (ambientLattice S).subtype ⊔
    Q.lattice.comap (ambientLattice S).subtype).index) : ℤ)

def relativeMultiplicity (A B : WeightedComplex n) (v : RealSpace n) : ℤ := by
  classical
  exact ∑ i, ∑ j,
    if w ∈ (A.complex.cell i).carrier ∧ w ∈ (B.complex.cell j).carrier ∧
      (A.complex.cell i).dimension = A.dimension ∧
      (B.complex.cell j).dimension = B.dimension ∧
      starsMeet (A.complex.cell i) (B.complex.cell j) w v then
        relativeIndex S (A.complex.cell i) (B.complex.cell j) * A.weight i * B.weight j
    else 0

variable (K : Type) [Field K] [Valued K NNReal] (n : ℕ)
  (P : AmbientIdeals K n)

def componentIdeal (Z : P.Component) : Ideal (TropicalTorIntersection.CoordinateRing K n) :=
  Z.val.comap (Ideal.Quotient.mk P.ambient)

def RelevantComponent (tau : Polyhedron n) :=
  {Z : P.Component // tau.carrier ⊆ tropicalizationOver (L := K) (componentIdeal K n P Z)}

variable [IsNoetherianRing P.ambientRing]

instance componentFinite : Finite P.Component :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing P.ambientRing P.intersectionIdeal).to_subtype

instance relevantFinite (tau : Polyhedron n) : Finite (RelevantComponent K n P tau) := by
  let : Finite P.Component := componentFinite K n P
  exact Finite.of_injective (fun Z : RelevantComponent K n P tau ↦ Z.val) Subtype.val_injective

/-- Serre's alternating Tor coefficients of the relevant components, times their tropical
multiplicities. -/
def weightedTorSum (tau : Polyhedron n) (t : Fin n → Kˣ)
    (T : ∀ Z : RelevantComponent K n P tau, P.LocalTor Z.val)
    (C : ∀ Z : RelevantComponent K n P tau,
      _root_.AlgebraicGeometry.IsNoetherian
        (geometricInitialScheme (componentIdeal K n P Z.val) t).left) : ℤ := by
  classical
  letI := Fintype.ofFinite (RelevantComponent K n P tau)
  exact ∑ Z : RelevantComponent K n P tau,
    letI := C Z
    P.componentCoefficient Z.val (T Z) * tropicalMultiplicity (componentIdeal K n P Z.val) t

/-- The sum of the local length coefficients `length(O_Z / (I + J))` times the tropical
multiplicities. Each length is converted with `ENat.toNat`, so this is the intended sum only when
every local length is finite, as it is when the local Tor modules have finite length
(`weightedSum_of_higherTor_zero`). -/
def weightedSchemeSum (tau : Polyhedron n) (t : Fin n → Kˣ)
    (C : ∀ Z : RelevantComponent K n P tau,
      _root_.AlgebraicGeometry.IsNoetherian
        (geometricInitialScheme (componentIdeal K n P Z.val) t).left) : ℤ := by
  classical
  letI := Fintype.ofFinite (RelevantComponent K n P tau)
  exact ∑ Z : RelevantComponent K n P tau,
    letI := C Z
    (P.componentSchemeCoefficient Z.val).toNat *
      tropicalMultiplicity (componentIdeal K n P Z.val) t

/-- With actual higher-Tor vanishing, equality of the two literal sums is proved. -/
theorem weightedSum_of_higherTor_zero (tau : Polyhedron n) (t : Fin n → Kˣ)
    (T : ∀ Z : RelevantComponent K n P tau, P.LocalTor Z.val)
    (C : ∀ Z : RelevantComponent K n P tau,
      _root_.AlgebraicGeometry.IsNoetherian
        (geometricInitialScheme (componentIdeal K n P Z.val) t).left)
    (h : ∀ Z : RelevantComponent K n P tau,
      HigherTorZero (P.LocalRing Z.val) (P.localLeft Z.val) (P.localRight Z.val)) :
    weightedTorSum K n P tau t T C = weightedSchemeSum K n P tau t C := by
  classical
  unfold weightedTorSum weightedSchemeSum
  apply Finset.sum_congr rfl
  intro Z _
  dsimp [AmbientIdeals.componentCoefficient, AmbientIdeals.componentSchemeCoefficient]
  rw [coefficient_of_higherTor_zero _ (T Z) (h Z)]

end MathlibExt.AlgebraicGeometry.GeneralAmbientTropicalIntersections
