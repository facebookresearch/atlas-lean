/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.CriticalReduction
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.CoarseGeometry

/-!
# Transport of subcritical exponential decay between periodic graphs

Exponential decay of the wired two-point function transfers from one periodic graph to another
under a comparison of connection probabilities along a coarsely distance-preserving map; applied
to the triangular and hexagonal lattices.

## i. Overview

`SubcriticalTwoPointComparison P Q q pcP pcQ` says that for each `p < pcQ` there is `pP < pcP`, a
constant `K` and a map `f` from `Q` to `P` with `φ_Q,p(x ↔ y) ≤ K φ_P,pP(f x ↔ f y)` and
`a d_Q(x, y) ≤ d_P(f x, f y) + b`. Under it, subcritical exponential decay on `P` implies
subcritical exponential decay on `Q` (`subcriticalTwoPointExponentialDecay_of_comparison`,
unconditional). For the triangular and hexagonal lattices, the distance half of the comparison is
supplied by `CoarseGeometry` through `hexToTriAnchor`, so the probability comparison
`TriHexGlobalProbabilityComparison` alone yields the decay transfer
`TriHexSubcriticalDecayTransfer`.

Fidelity: `TriHexGlobalProbabilityComparison` (domination of hexagonal by triangular two-point
functions at some subcritical triangular parameter) is an assumption that is not proved anywhere
in the library. The critical conclusions `triHexCriticalConclusion_of_exactDualThreshold_of_…`
are conditional on it (or on `TriHexGlobalTwoPointComparison`), on
`TriangularCriticalPhaseBoundary` (which assumes the triangular critical value, see
`CriticalReduction`) and on triangular subcritical decay, which is also returned unchanged as a
conclusion.

## ii. Key results

- `subcriticalTwoPointExponentialDecay_of_comparison` : decay transfer under a comparison.
  Unconditional.
- `triHexSubcriticalDecayTransfer_of_probabilityComparison` : triangular-to-hexagonal decay
  transfer. Conditional on `TriHexGlobalProbabilityComparison`.
- `triHexCriticalConclusion_of_exactDualThreshold_of_probabilityComparison` : critical cubics and
  decay on both lattices. Conditional on the probability comparison, the triangular phase boundary
  (the triangular critical value) and triangular decay.

## iii. Table of contents

- A. Comparison of two-point functions
- B. Triangular and hexagonal lattices

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §§5.6, 6.6.
-/

@[expose] public section

open Set SimpleGraph

namespace StatMech
namespace FK
namespace PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-! ## A. Comparison of two-point functions -/

/-- Comparison hypothesis: below `pcQ`, the wired two-point function of `Q` is dominated by a
constant times that of `P` at a parameter below `pcP`, along a map that distorts graph distance at
most affinely. -/
def SubcriticalTwoPointComparison
    [Countable V] [Countable W]
    (P : PeriodicGraph V) (Q : PeriodicGraph W)
    (q pcP pcQ : Real) : Prop :=
  ∀ p ∈ Ioo (0 : Real) pcQ,
    ∃ pP ∈ Ioo (0 : Real) pcP,
      ∃ K a b : Real, 0 < K ∧ 0 < a ∧ 0 ≤ b ∧
        ∃ f : W → V,
          (∀ x y : W,
            Q.wiredTwoPointProbability p q x y ≤
              K * P.wiredTwoPointProbability pP q (f x) (f y)) ∧
          (∀ x y : W,
            a * (Q.graph.dist x y : Real) ≤
              (P.graph.dist (f x) (f y) : Real) + b)

lemma subcriticalTwoPointExponentialDecay_of_comparison
    [Countable V] [Countable W]
    {P : PeriodicGraph V} {Q : PeriodicGraph W}
    {q pcP pcQ : Real}
    (hcompare : SubcriticalTwoPointComparison P Q q pcP pcQ)
    (hdecay : SubcriticalTwoPointExponentialDecay P q pcP) :
    SubcriticalTwoPointExponentialDecay Q q pcQ := by
  intro p hp
  obtain ⟨pP, hpP, K, a, b, hK, ha, hb, f, hprob, hdist⟩ :=
    hcompare p hp
  obtain ⟨c, C, hc, hC, hsource⟩ := hdecay pP hpP
  refine ⟨c * a, K * C * Real.exp (c * b), mul_pos hc ha,
    mul_pos (mul_pos hK hC) (Real.exp_pos _), ?_⟩
  intro x y
  have hexp :
      Real.exp (-c * (P.graph.dist (f x) (f y) : Real)) ≤
        Real.exp (c * b) *
          Real.exp (-(c * a) * (Q.graph.dist x y : Real)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hd := hdist x y
    nlinarith
  calc
    Q.wiredTwoPointProbability p q x y ≤
        K * P.wiredTwoPointProbability pP q (f x) (f y) := hprob x y
    _ ≤ K * (C * Real.exp
        (-c * (P.graph.dist (f x) (f y) : Real))) := by
      gcongr
      exact hsource (f x) (f y)
    _ ≤ K * (C * (Real.exp (c * b) *
        Real.exp (-(c * a) * (Q.graph.dist x y : Real)))) := by
      gcongr
    _ = (K * C * Real.exp (c * b)) *
        Real.exp (-(c * a) * (Q.graph.dist x y : Real)) := by ring

/-! ## B. Triangular and hexagonal lattices -/

/-- The two-point comparison from the triangular to the hexagonal lattice. -/
def TriHexGlobalTwoPointComparison (q pcTri pcHex : Real) : Prop :=
  SubcriticalTwoPointComparison triangular hexagonal q pcTri pcHex

/-- Probability comparison hypothesis: below `pcHex`, hexagonal two-point functions are dominated by
a constant times triangular two-point functions of the anchors at some parameter below `pcTri`. -/
def TriHexGlobalProbabilityComparison (q pcTri pcHex : Real) : Prop :=
  ∀ p ∈ Ioo (0 : Real) pcHex,
    ∃ pTri ∈ Ioo (0 : Real) pcTri,
      ∃ K : Real, 0 < K ∧
        ∀ u v : HexVertex,
          hexagonal.wiredTwoPointProbability p q u v ≤
            K * triangular.wiredTwoPointProbability pTri q
              (hexToTriAnchor u) (hexToTriAnchor v)

lemma triHexGlobalTwoPointComparison_of_probabilityComparison
    {q pcTri pcHex : Real}
    (hprob : TriHexGlobalProbabilityComparison q pcTri pcHex) :
    TriHexGlobalTwoPointComparison q pcTri pcHex := by
  intro p hp
  obtain ⟨pTri, hpTri, K, hK, hcompare⟩ := hprob p hp
  refine ⟨pTri, hpTri, K, (1 / 2 : Real), 1, hK, by norm_num,
    by norm_num, hexToTriAnchor, hcompare, ?_⟩
  intro u v
  exact half_hexagonal_dist_le_triangular_anchor_dist_add_one u v

lemma triHexSubcriticalDecayTransfer_of_globalComparison
    {q pcTri pcHex : Real}
    (hcompare : TriHexGlobalTwoPointComparison q pcTri pcHex) :
    TriHexSubcriticalDecayTransfer q pcTri pcHex := by
  intro hdecay
  exact subcriticalTwoPointExponentialDecay_of_comparison hcompare hdecay

lemma triHexSubcriticalDecayTransfer_of_probabilityComparison
    {q pcTri pcHex : Real}
    (hprob : TriHexGlobalProbabilityComparison q pcTri pcHex) :
    TriHexSubcriticalDecayTransfer q pcTri pcHex :=
  triHexSubcriticalDecayTransfer_of_globalComparison
    (triHexGlobalTwoPointComparison_of_probabilityComparison hprob)

lemma triHexCriticalConclusion_of_exactDualThreshold_of_globalComparison
    {q pcTri pcHex : Real}
    (hq : 0 < q)
    (hpcTri : pcTri ∈ Ioo (0 : Real) 1)
    (hdual : BeffaraDC.dualParam pcTri q = pcHex)
    (hphase : TriangularCriticalPhaseBoundary q pcTri)
    (hdecayTri : SubcriticalTwoPointExponentialDecay triangular q pcTri)
    (hcompare : TriHexGlobalTwoPointComparison q pcTri pcHex) :
    (FrontierA.triangularFKCriticalPolynomial q
          (FrontierA.fkEdgeOdds pcTri) = 0 ∧
        FrontierA.hexagonalFKCriticalPolynomial q
          (FrontierA.fkEdgeOdds pcHex) = 0) ∧
      SubcriticalTwoPointExponentialDecay triangular q pcTri ∧
      SubcriticalTwoPointExponentialDecay hexagonal q pcHex := by
  exact triHexCriticalConclusion_of_exactDualThreshold hq hpcTri hdual
    hphase hdecayTri
    (triHexSubcriticalDecayTransfer_of_globalComparison hcompare)

lemma triHexCriticalConclusion_of_exactDualThreshold_of_probabilityComparison
    {q pcTri pcHex : Real}
    (hq : 0 < q)
    (hpcTri : pcTri ∈ Ioo (0 : Real) 1)
    (hdual : BeffaraDC.dualParam pcTri q = pcHex)
    (hphase : TriangularCriticalPhaseBoundary q pcTri)
    (hdecayTri : SubcriticalTwoPointExponentialDecay triangular q pcTri)
    (hprob : TriHexGlobalProbabilityComparison q pcTri pcHex) :
    (FrontierA.triangularFKCriticalPolynomial q
          (FrontierA.fkEdgeOdds pcTri) = 0 ∧
        FrontierA.hexagonalFKCriticalPolynomial q
          (FrontierA.fkEdgeOdds pcHex) = 0) ∧
      SubcriticalTwoPointExponentialDecay triangular q pcTri ∧
      SubcriticalTwoPointExponentialDecay hexagonal q pcHex := by
  exact triHexCriticalConclusion_of_exactDualThreshold hq hpcTri hdual
    hphase hdecayTri
    (triHexSubcriticalDecayTransfer_of_probabilityComparison hprob)

end PeriodicPlanar
end FK
end StatMech
