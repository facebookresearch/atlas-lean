/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.ActiveEdges
public import PhyslibExt.StatisticalMechanics.RandomCluster.FinitePatternEnergy

/-!
# The random-cluster measure on active edges with boundary wiring

The random-cluster measure on the edges of a subgraph `G`, with clusters counted after joining a
boundary wiring graph `C`, is FKG, has open marginals at most `p_e`, and has a Russo-type
`β`-derivative.

## i. Overview

The active measure weights a configuration `ω` on `E(G)` by the Bernoulli edge product of its
extension (closed off `G`) times `q^{k_C(ω)}`, where `k_C` counts the clusters of the open subgraph
joined with `C`. The cluster count is supermodular, so for `q ≥ 1` the weight is log-supermodular
and the measure satisfies the FKG lattice condition. Closing one edge never decreases `k_C`, which
bounds each open marginal by `p_e`; combined with FKG this gives the lower bound `∏_{e ∈ S} (1 -
p_e) ≤ P(all edges of S closed)`. Under `p_e = 1 - exp(-β J_e)` the derivative in `β` of any event
probability is a weighted sum of covariances with the edge indicators. All three key results are
proved unconditionally: they take only the parameter-range hypotheses `0 < p_e < 1` (or `0 < J_e`,
`0 < β`) and `1 ≤ q` (or `0 < q`).

## ii. Key results

- `activeBCProb_FKGLatticeCondition` : the boundary-wired active measure satisfies the FKG lattice
  condition for `q ≥ 1`.
- `activeBC_prod_closed_param_le` : `∏_{e ∈ S} (1 - p_e)` is at most the probability that every edge
  of `S` is closed.
- `hasDerivAt_activeBCProbOf_beta_sum` : the Russo-type formula for the `β`-derivative of an event
  probability.

## iii. Table of contents

- A. The active measure with boundary wiring
- B. The FKG lattice condition
- C. Open marginals and closed-edge products
- D. The `β`-derivative

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorems 3.8 and 3.12.
-/

@[expose] public section

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech
namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (C : SimpleGraph V) [DecidableRel C.Adj]

/-! ## A. The active measure with boundary wiring -/

/-- The unnormalized active weight: the edge product of the extended configuration times `q` to the
number of clusters under the boundary wiring `C`. -/
noncomputable def activeBCWeight (pf : Sym2 V -> Real) (q : Real)
    (omega : ConfigSpace G.edgeSet) : Real :=
  edgeProductW G pf (extendActive G omega) *
    q ^ numClustersBC G C (extendActive G omega)

/-- The partition function of the boundary-wired active measure. -/
noncomputable def activeBCZ (pf : Sym2 V -> Real) (q : Real) : Real :=
  ∑ omega : ConfigSpace G.edgeSet, activeBCWeight G C pf q omega

/-- The boundary-wired active random-cluster measure on configurations of `E(G)`. -/
noncomputable def activeBCProb (pf : Sym2 V -> Real) (q : Real)
    (omega : ConfigSpace G.edgeSet) : Real :=
  activeBCWeight G C pf q omega / activeBCZ G C pf q

/-- The expectation of `f` under the boundary-wired active measure. -/
noncomputable def activeBCMean (pf : Sym2 V -> Real) (q : Real)
    (f : ConfigSpace G.edgeSet -> Real) : Real :=
  ∑ omega, f omega * activeBCProb G C pf q omega

/-- The covariance of `f` and `g` under the boundary-wired active measure. -/
noncomputable def activeBCCov (pf : Sym2 V -> Real) (q : Real)
    (f g : ConfigSpace G.edgeSet -> Real) : Real :=
  activeBCMean G C pf q (fun omega => f omega * g omega) -
    activeBCMean G C pf q f * activeBCMean G C pf q g

/-- The unnormalized expectation `∑ ω, f ω * w(ω)` for the boundary-wired active weight. -/
noncomputable def activeBCNumer (pf : Sym2 V -> Real) (q : Real)
    (f : ConfigSpace G.edgeSet -> Real) : Real :=
  ∑ omega, f omega * activeBCWeight G C pf q omega

/-- The probability of the event `A` under the boundary-wired active measure. -/
noncomputable def activeBCProbOf (pf : Sym2 V -> Real) (q : Real)
    (A : Set (ConfigSpace G.edgeSet)) : Real :=
  activeBCMean G C pf q (A.indicator fun _ => (1 : Real))

lemma activeBCWeight_pos {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (omega : ConfigSpace G.edgeSet) :
    0 < activeBCWeight G C pf q omega := by
  unfold activeBCWeight
  exact mul_pos (edgeProductW_pos G hpf hpf1 _) (pow_pos hq _)

lemma activeBCZ_pos {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) : 0 < activeBCZ G C pf q := by
  unfold activeBCZ
  exact Finset.sum_pos' (fun omega _ =>
    (activeBCWeight_pos G C hpf hpf1 hq omega).le)
    <| by
      refine ⟨fun _ => false, Finset.mem_univ _, ?_⟩
      exact activeBCWeight_pos G C hpf hpf1 hq _

lemma activeBCProb_pos {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (omega : ConfigSpace G.edgeSet) :
    0 < activeBCProb G C pf q omega := by
  exact div_pos (activeBCWeight_pos G C hpf hpf1 hq omega)
    (activeBCZ_pos G C hpf hpf1 hq)

lemma activeBCProb_sum_eq_one {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) :
    ∑ omega, activeBCProb G C pf q omega = 1 := by
  unfold activeBCProb activeBCZ
  rw [<- Finset.sum_div]
  exact div_self (activeBCZ_pos G C hpf hpf1 hq).ne'

/-! ## B. The FKG lattice condition -/

lemma activeBCWeight_logSupermodular {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) (omega eta : ConfigSpace G.edgeSet) :
    activeBCWeight G C pf q omega * activeBCWeight G C pf q eta <=
      activeBCWeight G C pf q (omega ⊔ eta) *
        activeBCWeight G C pf q (omega ⊓ eta) := by
  have hcluster :
      q ^ numClustersBC G C (extendActive G omega) *
          q ^ numClustersBC G C (extendActive G eta) <=
        q ^ numClustersBC G C (extendActive G (omega ⊔ eta)) *
          q ^ numClustersBC G C (extendActive G (omega ⊓ eta)) := by
    rw [extendActive_sup, extendActive_inf, <- pow_add, <- pow_add]
    have h := mixed_supermodular_bc G C C le_rfl
      (extendActive G omega) (extendActive G eta)
    simpa [add_comm] using pow_le_pow_right₀ hq h
  have hedge := edgeProductW_logModular G pf
    (extendActive G omega) (extendActive G eta)
  have hprod : 0 <=
      edgeProductW G pf (extendActive G (omega ⊔ eta)) *
        edgeProductW G pf (extendActive G (omega ⊓ eta)) :=
    mul_nonneg (edgeProductW_pos G hpf hpf1 _).le
      (edgeProductW_pos G hpf hpf1 _).le
  rw [← extendActive_sup, ← extendActive_inf] at hedge
  unfold activeBCWeight
  calc
    (edgeProductW G pf (extendActive G omega) *
          q ^ numClustersBC G C (extendActive G omega)) *
        (edgeProductW G pf (extendActive G eta) *
          q ^ numClustersBC G C (extendActive G eta)) =
      (edgeProductW G pf (extendActive G omega) *
          edgeProductW G pf (extendActive G eta)) *
        (q ^ numClustersBC G C (extendActive G omega) *
          q ^ numClustersBC G C (extendActive G eta)) := by ring
    _ = (edgeProductW G pf (extendActive G (omega ⊔ eta)) *
          edgeProductW G pf (extendActive G (omega ⊓ eta))) *
        (q ^ numClustersBC G C (extendActive G omega) *
          q ^ numClustersBC G C (extendActive G eta)) := by rw [hedge]
    _ <= (edgeProductW G pf (extendActive G (omega ⊔ eta)) *
          edgeProductW G pf (extendActive G (omega ⊓ eta))) *
        (q ^ numClustersBC G C (extendActive G (omega ⊔ eta)) *
          q ^ numClustersBC G C (extendActive G (omega ⊓ eta))) :=
      mul_le_mul_of_nonneg_left hcluster hprod
    _ = (edgeProductW G pf (extendActive G (omega ⊔ eta)) *
          q ^ numClustersBC G C (extendActive G (omega ⊔ eta))) *
        (edgeProductW G pf (extendActive G (omega ⊓ eta)) *
          q ^ numClustersBC G C (extendActive G (omega ⊓ eta))) := by ring

/-- For `q ≥ 1` the boundary-wired active measure satisfies the FKG lattice condition. -/
theorem activeBCProb_FKGLatticeCondition {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) :
    FKGLatticeCondition (activeBCProb G C pf q) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hZ := activeBCZ_pos G C hpf hpf1 hq0
  intro omega eta
  unfold activeBCProb
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos hZ hZ)).mpr
    (activeBCWeight_logSupermodular G C hpf hpf1 hq omega eta)

/-! ## C. Open marginals and closed-edge products -/

lemma activeBCWeight_open_closed_comparison {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) (e : G.edgeSet)
    (omega : ConfigSpace G.edgeSet) :
    (1 - pf e.1) * activeBCWeight G C pf q (setOpen e omega) <=
      pf e.1 * activeBCWeight G C pf q (setClosed e omega) := by
  unfold activeBCWeight
  rw [extendActive_setOpen, extendActive_setClosed,
    edgeProductW_setOpen, edgeProductW_setClosed]
  let R := ∏ a ∈ G.edgeFinset.erase e.1,
    if extendActive G omega a then pf a else 1 - pf a
  have hR : 0 <= R := by
    unfold R
    apply Finset.prod_nonneg
    intro a _
    split
    · exact (hpf a).le
    · linarith [hpf1 a]
  have hpow :
      q ^ numClustersBC G C (setOpen e.1 (extendActive G omega)) <=
        q ^ numClustersBC G C (setClosed e.1 (extendActive G omega)) :=
    pow_le_pow_right₀ hq
      (numClustersBC_setOpen_bounds G C e.1 (extendActive G omega)).1
  have hp : 0 <= pf e.1 * (1 - pf e.1) :=
    mul_nonneg (hpf _).le (by linarith [hpf1 e.1])
  nlinarith [mul_le_mul_of_nonneg_left hpow (mul_nonneg hR hp)]

lemma activeBC_openMarginal_le_param {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) (e : G.edgeSet) :
    openMarginal (activeBCProb G C pf q) e <= pf e.1 := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  apply openMarginal_le_of_close_pair _
    (activeBCProb_sum_eq_one G C hpf hpf1 hq0) e
  intro psi
  unfold activeBCProb
  have hZ := activeBCZ_pos G C hpf hpf1 hq0
  rw [show (1 - pf e.1) *
      (activeBCWeight G C pf q (setOpen e psi) / activeBCZ G C pf q) =
      ((1 - pf e.1) * activeBCWeight G C pf q (setOpen e psi)) /
        activeBCZ G C pf q by ring]
  rw [show pf e.1 *
      (activeBCWeight G C pf q (setClosed e psi) / activeBCZ G C pf q) =
      (pf e.1 * activeBCWeight G C pf q (setClosed e psi)) /
        activeBCZ G C pf q by ring]
  exact (div_le_div_iff_of_pos_right hZ).2
    (activeBCWeight_open_closed_comparison G C hpf hpf1 hq e psi)

/-- For `q ≥ 1`, the probability that every edge of `S` is closed is at least `∏_{e ∈ S} (1 - p_e)`.
-/
theorem activeBC_prod_closed_param_le {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) (S : Finset G.edgeSet) :
    S.prod (fun e => 1 - pf e.1) <=
      ∑ omega, activeBCProb G C pf q omega * closedProd S omega := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hmu0 : 0 <= activeBCProb G C pf q :=
    fun omega => (activeBCProb_pos G C hpf hpf1 hq0 omega).le
  have hmu1 := activeBCProb_sum_eq_one G C hpf hpf1 hq0
  have hFKG := activeBCProb_FKGLatticeCondition G C hpf hpf1 hq
  refine (Finset.prod_le_prod₀ (fun e he => by linarith [hpf1 e.1]) ?_).trans
    (prod_one_sub_openMarginal_le_closedProd _ hmu0 hmu1 hFKG S)
  intro e he
  linarith [activeBC_openMarginal_le_param G C hpf hpf1 hq e]

/-! ## D. The `β`-derivative -/

lemma hasDerivAt_activeBCWeight_beta {J : Sym2 V -> Real}
    (hJ : forall e, 0 < J e) {beta : Real} (hbeta : 0 < beta) (q : Real)
    (omega : ConfigSpace G.edgeSet) :
    HasDerivAt (fun b => activeBCWeight G C (betaParams J b) q omega)
      (activeBCWeight G C (betaParams J beta) q omega *
        activeBetaScore G J beta omega) beta := by
  have h := (hasDerivAt_edgeProductW_beta G hJ hbeta
    (extendActive G omega)).mul_const
      (q ^ numClustersBC G C (extendActive G omega))
  refine h.congr_deriv ?_
  rw [betaScore_extendActive]
  unfold activeBCWeight
  ring

lemma hasDerivAt_activeBCNumer_beta {J : Sym2 V -> Real}
    (hJ : forall e, 0 < J e) {beta : Real} (hbeta : 0 < beta) (q : Real)
    (f : ConfigSpace G.edgeSet -> Real) :
    HasDerivAt (fun b => activeBCNumer G C (betaParams J b) q f)
      (activeBCNumer G C (betaParams J beta) q
        (fun omega => f omega * activeBetaScore G J beta omega)) beta := by
  unfold activeBCNumer
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun omega _ =>
      (hasDerivAt_activeBCWeight_beta G C hJ hbeta q omega).const_mul (f omega))
  refine hsum.congr_deriv ?_
  apply Finset.sum_congr rfl
  intro omega _
  ring

lemma activeBCNumer_one (pf : Sym2 V -> Real) (q : Real) :
    activeBCNumer G C pf q (fun _ => 1) = activeBCZ G C pf q := by
  simp [activeBCNumer, activeBCZ]

lemma activeBCMean_eq_div (pf : Sym2 V -> Real) (q : Real)
    (f : ConfigSpace G.edgeSet -> Real) :
    activeBCMean G C pf q f = activeBCNumer G C pf q f / activeBCZ G C pf q := by
  unfold activeBCMean activeBCNumer activeBCProb
  rw [show (fun omega => f omega *
      (activeBCWeight G C pf q omega / activeBCZ G C pf q)) =
      (fun omega => (f omega * activeBCWeight G C pf q omega) /
        activeBCZ G C pf q) by funext omega; ring]
  rw [<- Finset.sum_div]

lemma activeBCMean_add (pf : Sym2 V -> Real) (q : Real)
    (f g : ConfigSpace G.edgeSet -> Real) :
    activeBCMean G C pf q (fun omega => f omega + g omega) =
      activeBCMean G C pf q f + activeBCMean G C pf q g := by
  unfold activeBCMean
  rw [<- Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun omega _ => by ring

lemma activeBCMean_const_mul (pf : Sym2 V -> Real) (q c : Real)
    (f : ConfigSpace G.edgeSet -> Real) :
    activeBCMean G C pf q (fun omega => c * f omega) =
      c * activeBCMean G C pf q f := by
  unfold activeBCMean
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun omega _ => by ring

lemma activeBCMean_sum (pf : Sym2 V -> Real) (q : Real)
    {I : Type*} [Fintype I] (g : I -> ConfigSpace G.edgeSet -> Real) :
    activeBCMean G C pf q (fun omega => ∑ i, g i omega) =
      ∑ i, activeBCMean G C pf q (g i) := by
  classical
  unfold activeBCMean
  rw [<- Finset.sum_comm]
  exact Finset.sum_congr rfl fun omega _ => by rw [Finset.sum_mul]

lemma activeBCCov_const_mul_right (pf : Sym2 V -> Real) (q c : Real)
    (f g : ConfigSpace G.edgeSet -> Real) :
    activeBCCov G C pf q f (fun omega => c * g omega) =
      c * activeBCCov G C pf q f g := by
  unfold activeBCCov
  rw [activeBCMean_const_mul]
  have hprod : (fun omega => f omega * (c * g omega)) =
      (fun omega => c * (f omega * g omega)) := by funext omega; ring
  rw [hprod, activeBCMean_const_mul]
  ring

lemma activeBCCov_sum_right (pf : Sym2 V -> Real) (q : Real)
    (f : ConfigSpace G.edgeSet -> Real) {I : Type*} [Fintype I]
    (g : I -> ConfigSpace G.edgeSet -> Real) :
    activeBCCov G C pf q f (fun omega => ∑ i, g i omega) =
      ∑ i, activeBCCov G C pf q f (g i) := by
  classical
  unfold activeBCCov
  rw [show (fun omega => f omega * ∑ i, g i omega) =
      (fun omega => ∑ i, f omega * g i omega) by
        funext omega; rw [Finset.mul_sum]]
  rw [activeBCMean_sum, activeBCMean_sum, Finset.mul_sum,
    <- Finset.sum_sub_distrib]

lemma activeBCCov_sub_const {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (f g : ConfigSpace G.edgeSet -> Real) (c : Real) :
    activeBCCov G C pf q f (fun omega => g omega - c) =
      activeBCCov G C pf q f g := by
  have hone : activeBCMean G C pf q
      (fun _ : ConfigSpace G.edgeSet => (1 : Real)) = 1 := by
    simpa [activeBCMean] using activeBCProb_sum_eq_one G C hpf hpf1 hq
  unfold activeBCCov
  rw [show (fun omega => f omega * (g omega - c)) =
      (fun omega => f omega * g omega + (-c) * f omega) by funext omega; ring]
  rw [activeBCMean_add, activeBCMean_const_mul]
  rw [show (fun omega : ConfigSpace G.edgeSet => g omega - c) =
      (fun omega => g omega + (-c) * 1) by funext omega; ring]
  rw [activeBCMean_add, activeBCMean_const_mul, hone]
  ring

lemma hasDerivAt_activeBCMean_beta_sum {J : Sym2 V -> Real}
    (hJ : forall e, 0 < J e) {beta : Real} (hbeta : 0 < beta)
    {q : Real} (hq : 0 < q) (f : ConfigSpace G.edgeSet -> Real) :
    HasDerivAt (fun b => activeBCMean G C (betaParams J b) q f)
      (∑ e : G.edgeSet, (J e.1 / betaParams J beta e.1) *
        activeBCCov G C (betaParams J beta) q f (OSSS.Lindeberg.coord e)) beta := by
  have hN := hasDerivAt_activeBCNumer_beta G C hJ hbeta q f
  have hZraw := hasDerivAt_activeBCNumer_beta G C hJ hbeta q (fun _ => 1)
  have hZ : HasDerivAt (fun b => activeBCZ G C (betaParams J b) q)
      (activeBCNumer G C (betaParams J beta) q (activeBetaScore G J beta)) beta := by
    simpa only [activeBCNumer_one, one_mul] using hZraw
  have hZne : activeBCZ G C (betaParams J beta) q ≠ 0 :=
    (activeBCZ_pos G C (betaParams_pos hJ hbeta)
      (betaParams_lt_one J beta) hq).ne'
  rw [show (fun b => activeBCMean G C (betaParams J b) q f) =
      (fun b => activeBCNumer G C (betaParams J b) q f /
        activeBCZ G C (betaParams J b) q) by
          funext b; exact activeBCMean_eq_div G C _ _ _]
  refine (hN.div hZ hZne).congr_deriv ?_
  have hscore :
      activeBCCov G C (betaParams J beta) q f (activeBetaScore G J beta) =
        ∑ e : G.edgeSet, (J e.1 / betaParams J beta e.1) *
          activeBCCov G C (betaParams J beta) q f (OSSS.Lindeberg.coord e) := by
    unfold activeBetaScore
    rw [activeBCCov_sum_right]
    apply Finset.sum_congr rfl
    intro e _
    rw [activeBCCov_const_mul_right]
    rw [activeBCCov_sub_const G C (betaParams_pos hJ hbeta)
      (betaParams_lt_one J beta) hq]
  rw [<- hscore]
  unfold activeBCCov
  rw [activeBCMean_eq_div, activeBCMean_eq_div, activeBCMean_eq_div]
  field_simp

/-- Russo-type formula: under `p_e = 1 - exp(-β J_e)`, the `β`-derivative of `P(A)` is `∑_e (J_e /
p_e) Cov(𝟙_A, ω_e)`. -/
theorem hasDerivAt_activeBCProbOf_beta_sum {J : Sym2 V -> Real}
    (hJ : forall e, 0 < J e) {beta : Real} (hbeta : 0 < beta)
    {q : Real} (hq : 0 < q) (A : Set (ConfigSpace G.edgeSet)) :
    HasDerivAt (fun b => activeBCProbOf G C (betaParams J b) q A)
      (∑ e : G.edgeSet,
        (J e.1 / (1 - Real.exp (-(beta * J e.1)))) *
          activeBCCov G C (betaParams J beta) q
            (A.indicator fun _ => (1 : Real)) (OSSS.Lindeberg.coord e)) beta := by
  simpa [activeBCProbOf, betaParams] using
    hasDerivAt_activeBCMean_beta_sum G C hJ hbeta hq
      (A.indicator fun _ => (1 : Real))

end FK
end StatMech
