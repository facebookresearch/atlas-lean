/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WiredBoxDifferential

/-!
# Differential inequality for the weighted wired box

The crossing probability of the wired box with inhomogeneous couplings `J` and its OSSS differential
inequality in `β`.

## i. Overview

`weightedWiredActiveTheta` is the probability that the origin is connected to the boundary of the
box of radius `n` under the wired random-cluster measure with parameters `1 - exp(-β J e)`.
`weighted_wired_box_differential_inequality` gives `c θ / D ≤ θ'` for some `c > 0`, unconditionally
for `q ≥ 1`, `J > 0` and `β ≤ β₀`. The `Weighted*` files extend the OSSS sharpness argument to
random-cluster models with inhomogeneous, periodic couplings `J` on `ℤ^d`. A phase map `phase : Site
d → P` to a finite set of phases, with `PhaseCovariant J phase phaseJ`, describes how translates of
the box see the couplings. The final results are
`WeightedPhaseCommonCritical.covariant_weighted_phase_common_critical` (all phases share one
critical point) and
`WeightedThreshold.weightedThreshold_eq_selectedPhaseCritical_of_highBetaWitness` (sharp threshold),
together with subcritical exponential decay.

## ii. Key results

- `weighted_wired_box_differential_inequality`: `c θ / D ≤ ∂θ/∂β` (unconditional).

## iii. Table of contents

- A. Weighted wired box

## iv. References

* H. Duminil-Copin, A. Raoufi, V. Tassion, *Sharp phase transition for the random-cluster and Potts
  models via decision trees*, Ann. of Math. 189 (2019).
-/

@[expose] public section

open scoped BigOperators
open Finset Set

namespace StatMech
namespace OSSS
namespace FKSharpnessWeighted

open StatMech.Lattice RevealmentConstruction AdaptiveCovLowerGeom
open ActiveBoundaryDifferential WiredBoxDifferential
open ActiveEdgeDifferential
open FK RevealmentTranslation

/-! ## A. Weighted wired box -/

/-- The probability, under the wired random-cluster measure on the box with couplings `J`, that the
  origin is connected to the boundary. -/
noncomputable def weightedWiredActiveTheta
    (d n : ℕ) (J : Sym2 (boxVerts d n) → ℝ) (q beta : ℝ) : ℝ :=
  Lindeberg.mean
    (FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
      (FK.betaParams J beta) q)
    (crossIndG (boxActiveEdge d n) 0 n)

/-- The OSSS denominator: four times the maximal summed connection probability from a box site. -/
noncomputable def weightedWiredActiveDenom
    (d n : ℕ) (J : Sym2 (boxVerts d n) → ℝ) (q beta : ℝ) : ℝ := by
  classical
  exact 4 * (StatMech.Percolation.boxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩
      (fun x => ∑ j ∈ Finset.range n,
        Lindeberg.mean
          (FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
            (FK.betaParams J beta) q)
          (fun omega => if ConnectedToSet d
            (liftCfg (boxActiveEdge d n) omega) x (centeredBoundary x j)
            then (1 : ℝ) else 0)) / (n : ℝ)

lemma weighted_wired_box_hasDerivAt
    (d n : ℕ)
    (J : Sym2 (boxVerts d n) → ℝ) (hJ : ∀ e, 0 < J e)
    (q beta : ℝ) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    HasDerivAt
      (fun b => FK.activeBCMean (boxGraph d n)
        (wiredBoxBoundaryGraph d n) (FK.betaParams J b) q
        (crossIndG (boxActiveEdge d n) 0 n))
      (∑ e : (boxGraph d n).edgeSet,
        (J e.1 / (1 - Real.exp (-(beta * J e.1)))) *
          FK.activeBCCov (boxGraph d n) (wiredBoxBoundaryGraph d n)
            (FK.betaParams J beta) q
            (crossIndG (boxActiveEdge d n) 0 n) (Lindeberg.coord e)) beta := by
  exact FK.hasDerivAt_activeBCMean_beta_sum
    (boxGraph d n) (wiredBoxBoundaryGraph d n) hJ hbeta
      (zero_lt_one.trans_le hq) (crossIndG (boxActiveEdge d n) 0 n)

/-- `c θ / D ≤ ∂θ/∂β` (unconditional). -/
theorem weighted_wired_box_differential_inequality
    (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (J : Sym2 (boxVerts d n) → ℝ) (hJ : ∀ e, 0 < J e)
    (q beta beta0 : ℝ) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (hbeta0 : beta ≤ beta0) :
    ∃ c : ℝ, 0 < c ∧
      c * (weightedWiredActiveTheta d n J q beta /
        weightedWiredActiveDenom d n J q beta) ≤
      deriv (fun b => FK.activeBCProbOf (boxGraph d n)
        (wiredBoxBoundaryGraph d n) (FK.betaParams J b) q
        (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) beta := by
  classical
  let : Nonempty (boxGraph d n).edgeSet :=
    boxGraph_edgeSet_nonempty d n hd hn
  let Lambda := StatMech.Percolation.boxFinset d n
  have hne : Lambda.Nonempty := ⟨0, origin_mem_osssBoxFinset d n⟩
  let disc0 : ℕ → Finset (Site d) := osssBoundaryFinset d
  let C := wiredBoxBoundaryGraph d n
  have hinj := boxActiveEdge_injective d n
  have hcoh := boxActiveEdge_eq_endpoints d n
  have hadj := boxActiveEnd_adj d n
  have hl : ∀ e : (boxGraph d n).edgeSet,
      e ∈ (Finset.univ : Finset (boxGraph d n).edgeSet).toList := by
    simp
  have hdisc0sub : ∀ k, ∀ x ∈ disc0 k, x ∈ vertexBoundary d k := by
    intro k x hx
    simpa [disc0] using hx
  have hdisc0sup : ∀ k, ∀ x ∈ vertexBoundary d k, x ∈ disc0 k := by
    intro k x hx
    simpa [disc0] using hx
  have hoB : ∀ k, (0 : Site d) ∉ disc0 k := by
    intro k
    exact origin_not_mem_osssBoundaryFinset d k
  have ho : ∀ k : ℕ, 1 ≤ k → (0 : Site d) ∈ box d (k - 1) := by
    intro k hk i
    simp
  have hLu : ∀ e : (boxGraph d n).edgeSet,
      boxActiveEndU d n e ∈ Lambda := boxActiveEndU_mem d n
  have hLv : ∀ e : (boxGraph d n).edgeSet,
      boxActiveEndV d n e ∈ Lambda := boxActiveEndV_mem d n
  have hUbox : ∀ e : (boxGraph d n).edgeSet,
      boxActiveEndU d n e ∈ box d n := fun e => e.1.out.1.property
  have hVbox : ∀ e : (boxGraph d n).edgeSet,
      boxActiveEndV d n e ∈ box d n := fun e => e.1.out.2.property
  have hmain := activeBC_fk_differential_inequality
    (boxGraph d n) C J hJ q beta beta0 hq hbeta hbeta0 hinj hcoh hadj
    (0 : Site d) (Finset.univ : Finset (boxGraph d n).edgeSet).toList hl
    disc0 hdisc0sub hdisc0sup hoB ho n hn Lambda hne hLu hLv hUbox hVbox
  simpa [weightedWiredActiveTheta, weightedWiredActiveDenom,
    C, Lambda, disc0] using hmain

lemma weightedWiredActiveDenom_pos
    (d n : ℕ) (hn : 1 ≤ n)
    (J : Sym2 (boxVerts d n) → ℝ) (hJ : ∀ e, 0 < J e)
    (q beta : ℝ) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    0 < weightedWiredActiveDenom d n J q beta := by
  classical
  let mu := FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
    (FK.betaParams J beta) q
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0 omega).le
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  simpa [weightedWiredActiveDenom, mu] using
    geometricDenom_pos mu hmu0 hmu1 (boxActiveEdge d n) n hn
      (StatMech.Percolation.boxFinset d n) ⟨0, origin_mem_osssBoxFinset d n⟩

end FKSharpnessWeighted
end OSSS
end StatMech
