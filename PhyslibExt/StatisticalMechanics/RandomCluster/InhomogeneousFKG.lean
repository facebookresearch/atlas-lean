/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.RussoDerivativeBeta
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKG
public import MathlibExt.Probability.OSSS.Monotonic
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.HorizontalBridgeDecay

/-!
# The FKG inequality for the inhomogeneous random-cluster model

For edge-dependent parameters `p(e) ∈ (0, 1)` and `q ≥ 1`, the finite-volume random-cluster measure
satisfies the FKG lattice condition and is a monotonic measure.

## i. Overview

The Bernoulli edge product `∏ₑ p(e)^{ω(e)} (1 - p(e))^{1 - ω(e)}` is log-modular, and the cluster
count is supermodular, so for `q ≥ 1` the inhomogeneous FK weight is log-supermodular. After
normalization this is the FKG lattice condition, which implies that the measure is monotonic
(its single-edge conditional probabilities increase with the boundary configuration). Both results
are proved unconditionally, under only `0 < p(e) < 1` and `1 ≤ q`. The file also records that
flipping an edge outside the graph does not change the measure.

## ii. Key results

- `fkProbW_FKGLatticeCondition` : the inhomogeneous FK measure satisfies the FKG lattice condition
  for `q ≥ 1`.
- `fkProbW_isMonotonic` : the inhomogeneous FK measure is a monotonic measure for `q ≥ 1`.
- `fkProbW_flipE_off` : flipping an edge outside the graph leaves the measure unchanged.

## iii. Table of contents

- A. Log-supermodularity of the weight
- B. The FKG lattice condition and monotonicity

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 3.8.
- C. M. Fortuin, P. W. Kasteleyn, and J. Ginibre, *Correlation inequalities on some partially
  ordered sets*, Comm. Math. Phys. 22 (1971).
-/

@[expose] public section

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech
namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Log-supermodularity of the weight -/

/-- The inhomogeneous Bernoulli edge product is log-modular. -/
lemma edgeProductW_logModular (pf : Sym2 V → ℝ)
    (a b : ConfigSpace (Sym2 V)) :
    edgeProductW G pf a * edgeProductW G pf b =
      edgeProductW G pf (a ⊔ b) * edgeProductW G pf (a ⊓ b) := by
  unfold edgeProductW
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  have hsup : (a ⊔ b) e = (a e || b e) := rfl
  have hinf : (a ⊓ b) e = (a e && b e) := rfl
  rw [hsup, hinf]
  cases a e <;> cases b e <;>
    simp only [Bool.or_self, Bool.or_false, Bool.or_true, Bool.and_self,
      Bool.and_false, Bool.and_true, ite_true, mul_comm]

/-- For `q ≥ 1` the inhomogeneous FK weight is log-supermodular. -/
lemma fkWeightW_logSupermodular {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 1 ≤ q) (a b : ConfigSpace (Sym2 V)) :
    fkWeightW G pf q a * fkWeightW G pf q b ≤
      fkWeightW G pf q (a ⊔ b) * fkWeightW G pf q (a ⊓ b) := by
  have hcluster :
      q ^ numClusters G a * q ^ numClusters G b ≤
        q ^ numClusters G (a ⊔ b) * q ^ numClusters G (a ⊓ b) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hq (numClusters_supermodular G a b)
  have hedge := edgeProductW_logModular G pf a b
  have hprod : 0 ≤ edgeProductW G pf (a ⊔ b) * edgeProductW G pf (a ⊓ b) :=
    mul_nonneg (edgeProductW_pos G hpf hpf1 _).le
      (edgeProductW_pos G hpf hpf1 _).le
  unfold fkWeightW
  calc
    edgeProductW G pf a * q ^ numClusters G a *
          (edgeProductW G pf b * q ^ numClusters G b) =
        (edgeProductW G pf a * edgeProductW G pf b) *
          (q ^ numClusters G a * q ^ numClusters G b) := by ring
    _ = (edgeProductW G pf (a ⊔ b) * edgeProductW G pf (a ⊓ b)) *
          (q ^ numClusters G a * q ^ numClusters G b) := by rw [hedge]
    _ ≤ (edgeProductW G pf (a ⊔ b) * edgeProductW G pf (a ⊓ b)) *
          (q ^ numClusters G (a ⊔ b) * q ^ numClusters G (a ⊓ b)) :=
      mul_le_mul_of_nonneg_left hcluster hprod
    _ = edgeProductW G pf (a ⊔ b) * q ^ numClusters G (a ⊔ b) *
          (edgeProductW G pf (a ⊓ b) * q ^ numClusters G (a ⊓ b)) := by ring

/-! ## B. The FKG lattice condition and monotonicity -/

/-- The inhomogeneous FK measure is a probability mass function. -/
lemma fkProbW_sum_eq_one {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) :
    ∑ ω, fkProbW G pf q ω = 1 := by
  unfold fkProbW fkZW
  rw [← Finset.sum_div]
  exact div_self (fkZW_ne_zero G hpf hpf1 hq)

/-- For `0 < p(e) < 1` and `q ≥ 1`, the inhomogeneous FK measure satisfies the FKG lattice
condition. -/
theorem fkProbW_FKGLatticeCondition {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 1 ≤ q) :
    FKGLatticeCondition (fkProbW G pf q) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hZ : 0 < fkZW G pf q := fkZW_pos G hpf hpf1 hq0
  intro a b
  unfold fkProbW
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos hZ hZ)).mpr
    (fkWeightW_logSupermodular G hpf hpf1 hq a b)

/-- For `0 < p(e) < 1` and `q ≥ 1`, the inhomogeneous FK measure is monotonic: the conditional
probability that an edge is open increases with the rest of the configuration. -/
theorem fkProbW_isMonotonic {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 1 ≤ q) :
    OSSS.Monotonic.IsMonotonicMeasure (fkProbW G pf q) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact OSSS.Monotonic.fkg_implies_monotonic
    (fun ω => div_pos (fkWeightW_pos G hpf hpf1 hq0 ω)
      (fkZW_pos G hpf hpf1 hq0))
    (fkProbW_FKGLatticeCondition G hpf hpf1 hq)

/-- Flipping an edge that is not in the graph leaves the inhomogeneous FK measure unchanged. -/
lemma fkProbW_flipE_off (pf : Sym2 V → ℝ) (q : ℝ)
    {e : Sym2 V} (he : e ∉ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    fkProbW G pf q (OSSS.HBridgeClose.flipE e ω) = fkProbW G pf q ω := by
  unfold fkProbW fkWeightW edgeProductW
  congr 2
  · apply Finset.prod_congr rfl
    intro e' he'
    have hne : e' ≠ e := by rintro rfl; exact he he'
    rw [OSSS.HBridgeClose.flipE_of_ne hne]
  · rw [numClusters_congr_openSub G (OSSS.HBridgeClose.openSub_flipE G he ω)]

end FK
end StatMech
