/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedPeriodic
public import PhyslibExt.StatisticalMechanics.RandomCluster.MonoBC

/-!
# Boundary-conditioned random-cluster measures with edge-dependent parameters

The random-cluster measure on a finite graph with a boundary graph `C` and edge-dependent parameters
`pf`, its monotonicity in `C`, conditional measures, and domain-Markov domination of inner boxes.

## i. Overview

`bcProbW G C pf q` is the random-cluster measure whose clusters are counted in `G ⊔ C`. It is
stochastically increasing in `C` (`bcProbW_mono_bc`), and so are its conditionals given the edges
outside `F` (`condBcProbW_mono_bc`). Embedding an inner graph into an outer one (`ocd_AdjMatch`),
the outer measure decomposes over outer configurations. Its inner marginal lies between the free and
wired inner measures (`ocd_free_inner_dominated_bcProbW`, `ocd_wired_inner_dominated_bcProbW`). All
results are unconditional under `0 < pf < 1` and `q ≥ 1`.

## ii. Key results

- `bcProbW_mono_bc`: monotonicity in the boundary graph.
- `ocd_wired_inner_dominated_bcProbW`: inner marginals are dominated by the wired inner measure.
- `weighted_transShellEvent_domain_dominated`: domination of translated shell events.

## iii. Table of contents

- A. Weighted boundary-conditioned measures
- B. Conditional measures
- C. Active-edge factorization
- D. Inner and outer graphs
- E. Domination

## iv. References

* G. R. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapter 4.
-/

@[expose] public section

open scoped BigOperators
open Finset Set


namespace StatMech
namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (C : SimpleGraph V) [DecidableRel C.Adj]

/-! ## A. Weighted boundary-conditioned measures -/

/-- The random-cluster weight with edge-dependent parameters `pf` and boundary graph `C`: the edge
  product times `q` to the number of clusters of the open graph joined with `C`. -/
noncomputable def bcWeightW (pf : Sym2 V -> Real) (q : Real)
    (omega : ConfigSpace (Sym2 V)) : Real :=
  edgeProductW G pf omega * q ^ numClustersBC G C omega

/-- The partition function of the weighted boundary-conditioned measure. -/
noncomputable def bcZW (pf : Sym2 V -> Real) (q : Real) : Real :=
  ∑ omega, bcWeightW G C pf q omega

/-- The weighted boundary-conditioned random-cluster probability of a configuration. -/
noncomputable def bcProbW (pf : Sym2 V -> Real) (q : Real)
    (omega : ConfigSpace (Sym2 V)) : Real :=
  bcWeightW G C pf q omega / bcZW G C pf q

omit [DecidableEq V] in
lemma bcWeightW_pos {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (omega : ConfigSpace (Sym2 V)) :
    0 < bcWeightW G C pf q omega := by
  exact mul_pos (edgeProductW_pos G hpf hpf1 omega) (pow_pos hq _)

omit [DecidableEq V] in
lemma bcWeightW_nonneg {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (omega : ConfigSpace (Sym2 V)) :
    0 <= bcWeightW G C pf q omega :=
  (bcWeightW_pos G C hpf hpf1 hq omega).le

lemma bcZW_pos {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) : 0 < bcZW G C pf q := by
  unfold bcZW
  exact Finset.sum_pos (fun omega _ => bcWeightW_pos G C hpf hpf1 hq omega)
    Finset.univ_nonempty

lemma bcProbW_nonneg {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (omega : ConfigSpace (Sym2 V)) :
    0 <= bcProbW G C pf q omega := by
  exact div_nonneg (bcWeightW_nonneg G C hpf hpf1 hq omega)
    (bcZW_pos G C hpf hpf1 hq).le

lemma bcProbW_sum_eq_one {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) :
    ∑ omega, bcProbW G C pf q omega = 1 := by
  unfold bcProbW bcZW
  rw [← Finset.sum_div]
  exact div_self (bcZW_pos G C hpf hpf1 hq).ne'

open Classical in
omit [DecidableEq V] in
lemma bcWeightW_cross_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) (a b : ConfigSpace (Sym2 V)) :
    bcWeightW G C pf q a * bcWeightW G C' pf q b <=
      bcWeightW G C pf q (a ⊓ b) * bcWeightW G C' pf q (a ⊔ b) := by
  have hcluster :
      q ^ numClustersBC G C a * q ^ numClustersBC G C' b <=
        q ^ numClustersBC G C (a ⊓ b) *
          q ^ numClustersBC G C' (a ⊔ b) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hq (mixed_supermodular_bc G C C' hCC' a b)
  have hedge := edgeProductW_logModular G pf a b
  have hedge0 : 0 <=
      edgeProductW G pf (a ⊓ b) * edgeProductW G pf (a ⊔ b) :=
    mul_nonneg (edgeProductW_pos G hpf hpf1 _).le
      (edgeProductW_pos G hpf hpf1 _).le
  unfold bcWeightW
  calc
    (edgeProductW G pf a * q ^ numClustersBC G C a) *
          (edgeProductW G pf b * q ^ numClustersBC G C' b) =
        (edgeProductW G pf a * edgeProductW G pf b) *
          (q ^ numClustersBC G C a * q ^ numClustersBC G C' b) := by ring
    _ = (edgeProductW G pf (a ⊓ b) * edgeProductW G pf (a ⊔ b)) *
          (q ^ numClustersBC G C a * q ^ numClustersBC G C' b) := by
        rw [hedge]
        ring
    _ <= (edgeProductW G pf (a ⊓ b) * edgeProductW G pf (a ⊔ b)) *
          (q ^ numClustersBC G C (a ⊓ b) *
            q ^ numClustersBC G C' (a ⊔ b)) :=
        mul_le_mul_of_nonneg_left hcluster hedge0
    _ = (edgeProductW G pf (a ⊓ b) *
          q ^ numClustersBC G C (a ⊓ b)) *
        (edgeProductW G pf (a ⊔ b) *
          q ^ numClustersBC G C' (a ⊔ b)) := by ring

lemma bcProbW_cross_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) (a b : ConfigSpace (Sym2 V)) :
    bcProbW G C pf q a * bcProbW G C' pf q b <=
      bcProbW G C pf q (a ⊓ b) * bcProbW G C' pf q (a ⊔ b) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hZ : 0 < bcZW G C pf q := bcZW_pos G C hpf hpf1 hq0
  have hZ' : 0 < bcZW G C' pf q := bcZW_pos G C' hpf hpf1 hq0
  unfold bcProbW
  rw [div_mul_div_comm, div_mul_div_comm,
    div_le_div_iff_of_pos_right (mul_pos hZ hZ')]
  exact bcWeightW_cross_bc G C C' hCC' hpf hpf1 hq a b

lemma bcProbW_mono_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW G C pf q omega) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW G C' pf q omega := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact fun omega => bcProbW_nonneg G C hpf hpf1 hq0 omega
  · exact fun omega => bcProbW_nonneg G C' hpf hpf1 hq0 omega
  · rw [bcProbW_sum_eq_one G C hpf hpf1 hq0,
      bcProbW_sum_eq_one G C' hpf hpf1 hq0]
  · exact fun a b => bcProbW_cross_bc G C C' hCC' hpf hpf1 hq a b

/-! ## B. Conditional measures -/

/-- The partition function of configurations agreeing with `psi` off `F`. -/
noncomputable def inducedBcZW (pf : Sym2 V -> Real) (q : Real)
    (F : Finset (Sym2 V)) (psi : ConfigSpace (Sym2 V)) : Real :=
  ∑ rho ∈ condFibre F psi, bcWeightW G C pf q rho

lemma inducedBcZW_pos {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (F : Finset (Sym2 V))
    (psi : ConfigSpace (Sym2 V)) : 0 < inducedBcZW G C pf q F psi := by
  unfold inducedBcZW
  exact Finset.sum_pos (fun rho _ => bcWeightW_pos G C hpf hpf1 hq rho)
    ⟨psi, self_mem_condFibre F psi⟩

/-- The weighted boundary-conditioned probability conditioned on agreeing with `psi` off `F`. -/
noncomputable def condBcProbW (pf : Sym2 V -> Real) (q : Real)
    (F : Finset (Sym2 V)) (psi omega : ConfigSpace (Sym2 V)) : Real :=
  if AgreesOff F psi omega then
    bcWeightW G C pf q omega / inducedBcZW G C pf q F psi
  else 0

lemma condBcProbW_nonneg {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (F : Finset (Sym2 V))
    (psi : ConfigSpace (Sym2 V)) :
    (0 : ConfigSpace (Sym2 V) -> Real) <= condBcProbW G C pf q F psi := by
  intro omega
  unfold condBcProbW
  split
  · exact div_nonneg (bcWeightW_nonneg G C hpf hpf1 hq omega)
      (inducedBcZW_pos G C hpf hpf1 hq F psi).le
  · rfl

lemma condBcProbW_sum_eq_one {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (F : Finset (Sym2 V))
    (psi : ConfigSpace (Sym2 V)) :
    ∑ omega, condBcProbW G C pf q F psi omega = 1 := by
  unfold condBcProbW
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.sum_div]
  exact div_self (inducedBcZW_pos G C hpf hpf1 hq F psi).ne'

lemma condBcProbW_cross_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) (F : Finset (Sym2 V))
    (psi a b : ConfigSpace (Sym2 V)) :
    condBcProbW G C pf q F psi a * condBcProbW G C' pf q F psi b <=
      condBcProbW G C pf q F psi (a ⊓ b) *
        condBcProbW G C' pf q F psi (a ⊔ b) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hright : 0 <=
      condBcProbW G C pf q F psi (a ⊓ b) *
        condBcProbW G C' pf q F psi (a ⊔ b) :=
    mul_nonneg (condBcProbW_nonneg G C hpf hpf1 hq0 F psi _)
      (condBcProbW_nonneg G C' hpf hpf1 hq0 F psi _)
  unfold condBcProbW
  by_cases ha : AgreesOff F psi a
  · by_cases hb : AgreesOff F psi b
    · rw [ite_eq_left ha, ite_eq_left hb, ite_eq_left (agreesOff_inf ha hb),
        ite_eq_left (agreesOff_sup ha hb), div_mul_div_comm, div_mul_div_comm,
        div_le_div_iff_of_pos_right
          (mul_pos (inducedBcZW_pos G C hpf hpf1 hq0 F psi)
            (inducedBcZW_pos G C' hpf hpf1 hq0 F psi))]
      exact bcWeightW_cross_bc G C C' hCC' hpf hpf1 hq a b
    · rw [ite_eq_right hb, mul_zero]
      simpa only [condBcProbW] using hright
  · rw [ite_eq_right ha, zero_mul]
    simpa only [condBcProbW] using hright

lemma condBcProbW_mono_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) (F : Finset (Sym2 V))
    (psi : ConfigSpace (Sym2 V))
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        condBcProbW G C pf q F psi omega) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        condBcProbW G C' pf q F psi omega := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact condBcProbW_nonneg G C hpf hpf1 hq0 F psi
  · exact condBcProbW_nonneg G C' hpf hpf1 hq0 F psi
  · rw [condBcProbW_sum_eq_one G C hpf hpf1 hq0 F psi,
      condBcProbW_sum_eq_one G C' hpf hpf1 hq0 F psi]
  · exact fun a b =>
      condBcProbW_cross_bc G C C' hCC' hpf hpf1 hq F psi a b

lemma activeBCProb_mono_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q)
    {A : Set (ConfigSpace G.edgeSet)} (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        activeBCProb G C pf q omega) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        activeBCProb G C' pf q omega := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact fun omega => (activeBCProb_pos G C hpf hpf1 hq0 omega).le
  · exact fun omega => (activeBCProb_pos G C' hpf hpf1 hq0 omega).le
  · rw [activeBCProb_sum_eq_one G C hpf hpf1 hq0,
      activeBCProb_sum_eq_one G C' hpf hpf1 hq0]
  · intro a b
    have hcluster :
        q ^ numClustersBC G C (extendActive G a) *
            q ^ numClustersBC G C' (extendActive G b) <=
          q ^ numClustersBC G C (extendActive G (a ⊓ b)) *
            q ^ numClustersBC G C' (extendActive G (a ⊔ b)) := by
      rw [extendActive_inf, extendActive_sup, ← pow_add, ← pow_add]
      exact pow_le_pow_right₀ hq
        (mixed_supermodular_bc G C C' hCC' (extendActive G a) (extendActive G b))
    have hedge := edgeProductW_logModular G pf
      (extendActive G a) (extendActive G b)
    have hedge' : edgeProductW G pf (extendActive G a) *
        edgeProductW G pf (extendActive G b) =
          edgeProductW G pf (extendActive G (a ⊓ b)) *
            edgeProductW G pf (extendActive G (a ⊔ b)) := by
      rw [hedge, extendActive_inf, extendActive_sup]
      ring
    have hedge0 : 0 <= edgeProductW G pf (extendActive G (a ⊓ b)) *
        edgeProductW G pf (extendActive G (a ⊔ b)) :=
      mul_nonneg (edgeProductW_pos G hpf hpf1 _).le
        (edgeProductW_pos G hpf hpf1 _).le
    have hweight : activeBCWeight G C pf q a * activeBCWeight G C' pf q b <=
        activeBCWeight G C pf q (a ⊓ b) * activeBCWeight G C' pf q (a ⊔ b) := by
      unfold activeBCWeight
      calc
        (edgeProductW G pf (extendActive G a) *
              q ^ numClustersBC G C (extendActive G a)) *
            (edgeProductW G pf (extendActive G b) *
              q ^ numClustersBC G C' (extendActive G b)) =
          (edgeProductW G pf (extendActive G a) *
              edgeProductW G pf (extendActive G b)) *
            (q ^ numClustersBC G C (extendActive G a) *
              q ^ numClustersBC G C' (extendActive G b)) := by ring
        _ = (edgeProductW G pf (extendActive G (a ⊓ b)) *
              edgeProductW G pf (extendActive G (a ⊔ b))) *
            (q ^ numClustersBC G C (extendActive G a) *
              q ^ numClustersBC G C' (extendActive G b)) := by
            rw [hedge']
        _ <= (edgeProductW G pf (extendActive G (a ⊓ b)) *
              edgeProductW G pf (extendActive G (a ⊔ b))) *
            (q ^ numClustersBC G C (extendActive G (a ⊓ b)) *
              q ^ numClustersBC G C' (extendActive G (a ⊔ b))) :=
            mul_le_mul_of_nonneg_left hcluster hedge0
        _ = (edgeProductW G pf (extendActive G (a ⊓ b)) *
              q ^ numClustersBC G C (extendActive G (a ⊓ b))) *
            (edgeProductW G pf (extendActive G (a ⊔ b)) *
              q ^ numClustersBC G C' (extendActive G (a ⊔ b))) := by ring
    have hZ : 0 < activeBCZ G C pf q := activeBCZ_pos G C hpf hpf1 hq0
    have hZ' : 0 < activeBCZ G C' pf q := activeBCZ_pos G C' hpf hpf1 hq0
    unfold activeBCProb
    rw [div_mul_div_comm, div_mul_div_comm,
      div_le_div_iff_of_pos_right (mul_pos hZ hZ')]
    exact hweight

/-! ## C. Active-edge factorization -/

open Classical in
omit [DecidableEq V] in
lemma bcWeightW_eq_of_edges (pf : Sym2 V -> Real) (q : Real)
    (omega eta : ConfigSpace (Sym2 V))
    (h : forall e, e ∈ G.edgeFinset -> omega e = eta e) :
    bcWeightW G C pf q omega = bcWeightW G C pf q eta := by
  unfold bcWeightW
  rw [numClustersBC_eq_of_edges G C omega eta h]
  congr 1
  unfold edgeProductW
  exact Finset.prod_congr rfl (fun e he => by rw [h e he])

open Classical in
omit [DecidableEq V] in
lemma bcWeightW_activeSplitEquiv_symm (pf : Sym2 V -> Real) (q : Real)
    (eta : ConfigSpace G.edgeSet)
    (xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet}) :
    bcWeightW G C pf q ((activeSplitEquiv G).symm (eta, xi)) =
      activeBCWeight G C pf q eta := by
  apply bcWeightW_eq_of_edges G C
  intro e he
  have heSet : e ∈ G.edgeSet := by
    rwa [← SimpleGraph.mem_edgeFinset]
  rw [show ((activeSplitEquiv G).symm (eta, xi)) e = eta ⟨e, heSet⟩ by
    simp [activeSplitEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, heSet]]
  exact (extendActive_apply G eta ⟨e, heSet⟩).symm

lemma activeBCZW_factorization (pf : Sym2 V -> Real) (q : Real) :
    bcZW G C pf q = 2 ^ ecz_NE G * activeBCZ G C pf q := by
  rw [bcZW, ← Equiv.sum_comp (activeSplitEquiv G).symm
    (fun omega => bcWeightW G C pf q omega), Fintype.sum_prod_type]
  have key : forall eta : ConfigSpace G.edgeSet,
      (∑ xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet},
        bcWeightW G C pf q ((activeSplitEquiv G).symm (eta, xi))) =
      2 ^ ecz_NE G * activeBCWeight G C pf q eta := by
    intro eta
    rw [Finset.sum_congr rfl (fun xi _ =>
      bcWeightW_activeSplitEquiv_symm G C pf q eta xi)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_inactive_config G]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun eta _ => key eta), ← Finset.mul_sum]
  rfl

lemma activeBCNumerW_factorization (pf : Sym2 V -> Real) (q : Real)
    (f : ConfigSpace G.edgeSet -> Real) :
    (∑ omega : ConfigSpace (Sym2 V),
      f (restrictActive G omega) * bcWeightW G C pf q omega) =
      2 ^ ecz_NE G * activeBCNumer G C pf q f := by
  rw [← Equiv.sum_comp (activeSplitEquiv G).symm
    (fun omega => f (restrictActive G omega) * bcWeightW G C pf q omega),
    Fintype.sum_prod_type]
  have key : forall eta : ConfigSpace G.edgeSet,
      (∑ xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet},
        f (restrictActive G ((activeSplitEquiv G).symm (eta, xi))) *
          bcWeightW G C pf q ((activeSplitEquiv G).symm (eta, xi))) =
      2 ^ ecz_NE G * (f eta * activeBCWeight G C pf q eta) := by
    intro eta
    rw [Finset.sum_congr rfl (fun xi _ => by
      rw [restrictActive_activeSplitEquiv_symm,
        bcWeightW_activeSplitEquiv_symm G C pf q eta xi])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_inactive_config G]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun eta _ => key eta), ← Finset.mul_sum]
  rfl

lemma activeBCMean_eq_bcProbW_lift {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (f : ConfigSpace G.edgeSet -> Real) :
    activeBCMean G C pf q f =
      ∑ omega : ConfigSpace (Sym2 V),
        f (restrictActive G omega) * bcProbW G C pf q omega := by
  have htwo : (2 : Real) ^ ecz_NE G ≠ 0 := by positivity
  have hZactive : activeBCZ G C pf q ≠ 0 :=
    (activeBCZ_pos G C hpf hpf1 hq).ne'
  rw [activeBCMean_eq_div]
  unfold bcProbW
  rw [show (fun omega : ConfigSpace (Sym2 V) =>
      f (restrictActive G omega) *
        (bcWeightW G C pf q omega / bcZW G C pf q)) =
      (fun omega =>
        (f (restrictActive G omega) * bcWeightW G C pf q omega) /
          bcZW G C pf q) by funext omega; ring]
  rw [← Finset.sum_div, activeBCNumerW_factorization G C,
    activeBCZW_factorization G C]
  field_simp

variable {Vin Vout : Type*} [Fintype Vin] [Fintype Vout]
variable [DecidableEq Vin] [DecidableEq Vout]
variable (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]
variable (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
variable (iota : Vin -> Vout)
variable (bdryOut : Vout -> Prop) [DecidablePred bdryOut]

/-! ## D. Inner and outer graphs -/

/-- The inner parameters agree with the outer parameters along the embedding. -/
def ocd_ParamCompatible (pfIn : Sym2 Vin -> Real)
    (pfOut : Sym2 Vout -> Real) : Prop :=
  forall e, pfIn e = pfOut (ocd_innerEdge iota e)

/-- The edge-product factor of the outer configuration `psi` on edges outside the inner graph. -/
noncomputable def ocd_psiEdgeFactorW (pfOut : Sym2 Vout -> Real)
    (psi : ConfigSpace (Sym2 Vout)) : Real :=
  ∏ e ∈ Gout.edgeFinset.filter
      (fun e => e ∉ Set.range (ocd_innerEdge iota)),
    if psi e then pfOut e else 1 - pfOut e

omit [DecidableEq Vin] in
lemma ocd_psiEdgeFactorW_pos {pfOut : Sym2 Vout -> Real}
    (hpf : forall e, 0 < pfOut e) (hpf1 : forall e, pfOut e < 1)
    (psi : ConfigSpace (Sym2 Vout)) :
    0 < ocd_psiEdgeFactorW Gout iota pfOut psi := by
  unfold ocd_psiEdgeFactorW
  apply Finset.prod_pos
  intro e he
  split
  · exact hpf e
  · linarith [hpf1 e]

omit [DecidableEq Vin] in
lemma ocd_edgeProductW_psiExt (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (psi : ConfigSpace (Sym2 Vout)) (omega : ConfigSpace (Sym2 Vin)) :
    edgeProductW Gout pfOut (ocd_psiExt iota psi omega) =
      edgeProductW Gin pfIn omega *
        ocd_psiEdgeFactorW Gout iota pfOut psi := by
  classical
  unfold edgeProductW ocd_psiEdgeFactorW
  rw [← Finset.prod_filter_mul_prod_filter_not Gout.edgeFinset
    (fun e => e ∈ Set.range (ocd_innerEdge iota))]
  congr 1
  · rw [← ocd_innerEdge_image_edgeFinset hiota hadjm,
      Finset.prod_image
        (fun a _ b _ h => ocd_innerEdge_injective iota hiota h)]
    refine Finset.prod_congr rfl (fun e he => ?_)
    rw [ocd_psiExt_innerEdge hiota, ← hparam e]
  · refine Finset.prod_congr rfl (fun e he => ?_)
    rw [Finset.mem_filter] at he
    rw [ocd_psiExt_eq_psi_of_not_range psi omega he.2]

/-- The weight shift contributed by the outer configuration `psi`. -/
noncomputable def ocd_psiShiftW (pfOut : Sym2 Vout -> Real)
    (psi : ConfigSpace (Sym2 Vout)) (q : Real) : Real :=
  ocd_psiEdgeFactorW Gout iota pfOut psi *
    q ^ ocd_outsideShift Gout iota bdryOut psi

lemma ocd_psiShiftW_pos {pfOut : Sym2 Vout -> Real}
    (hpf : forall e, 0 < pfOut e) (hpf1 : forall e, pfOut e < 1)
    {q : Real} (hq : 0 < q) (psi : ConfigSpace (Sym2 Vout)) :
    0 < ocd_psiShiftW Gout iota bdryOut pfOut psi q := by
  exact mul_pos (ocd_psiEdgeFactorW_pos Gout iota hpf hpf1 psi)
    (pow_pos hq _)

lemma ocd_bcWeightW_psiExt (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (psi : ConfigSpace (Sym2 Vout)) (omega : ConfigSpace (Sym2 Vin))
    (q : Real) :
    bcWeightW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q
        (ocd_psiExt iota psi omega) =
      bcWeightW Gin (ocd_inducedWiring Gout iota bdryOut psi) pfIn q omega *
        ocd_psiShiftW Gout iota bdryOut pfOut psi q := by
  rw [bcWeightW, ocd_numClustersBC_psiExt hiota hadjm,
    ocd_edgeProductW_psiExt Gin Gout iota hiota hadjm hparam,
    bcWeightW, ocd_psiShiftW, pow_add]
  ring

lemma ocd_inducedBcZW_psi (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (psi : ConfigSpace (Sym2 Vout)) (q : Real) :
    inducedBcZW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q
        (ocd_innerEdgeFinset (Vin := Vin) iota) psi =
      bcZW Gin (ocd_inducedWiring Gout iota bdryOut psi) pfIn q *
        ocd_psiShiftW Gout iota bdryOut pfOut psi q := by
  rw [inducedBcZW, ocd_condFibre_eq_image_psiExt hiota,
    Finset.sum_image (fun a _ b _ h => by
      have hab := congrArg (ocd_innerRestrict iota) h
      rwa [ocd_innerRestrict_psiExt hiota,
        ocd_innerRestrict_psiExt hiota] at hab),
    bcZW, Finset.sum_mul]
  exact Finset.sum_congr rfl
    (fun omega _ => ocd_bcWeightW_psiExt Gin Gout iota bdryOut
      hiota hadjm hparam psi omega q)

lemma ocd_condBcProbW_psiExt_eq_bcProbW
    (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1) {q : Real} (hq : 0 < q)
    (psi : ConfigSpace (Sym2 Vout)) (omega : ConfigSpace (Sym2 Vin)) :
    condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q
        (ocd_innerEdgeFinset (Vin := Vin) iota) psi
        (ocd_psiExt iota psi omega) =
      bcProbW Gin (ocd_inducedWiring Gout iota bdryOut psi) pfIn q omega := by
  rw [condBcProbW, ite_eq_left (ocd_agreesOff_psiExt psi omega),
    ocd_bcWeightW_psiExt Gin Gout iota bdryOut hiota hadjm hparam,
    ocd_inducedBcZW_psi Gin Gout iota bdryOut hiota hadjm hparam,
    bcProbW,
    mul_div_mul_right _ _
      (ocd_psiShiftW_pos Gout iota bdryOut hpfOut hpfOut1 hq psi).ne']

lemma ocd_condBcProbW_psiExt_sum_eq_inducedBox
    (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1) {q : Real} (hq : 0 < q)
    (psi : ConfigSpace (Sym2 Vout))
    (B : Set (ConfigSpace (Sym2 Vout))) :
    (∑ rho, B.indicator (fun _ => (1 : Real)) rho *
        condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q
          (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho) =
      ∑ omega : ConfigSpace (Sym2 Vin),
        (ocd_psiExt iota psi ⁻¹' B).indicator (fun _ => (1 : Real)) omega *
          bcProbW Gin (ocd_inducedWiring Gout iota bdryOut psi)
            pfIn q omega := by
  classical
  have hsupp : forall rho, rho ∉
      condFibre (ocd_innerEdgeFinset (Vin := Vin) iota) psi ->
      B.indicator (fun _ => (1 : Real)) rho *
        condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q
          (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho = 0 := by
    intro rho hrho
    rw [mem_condFibre] at hrho
    unfold condBcProbW
    rw [ite_eq_right hrho, mul_zero]
  rw [← Finset.sum_subset
    (Finset.subset_univ
      (condFibre (ocd_innerEdgeFinset (Vin := Vin) iota) psi))
    (fun rho _ hrho => hsupp rho hrho)]
  rw [ocd_condFibre_eq_image_psiExt hiota]
  rw [Finset.sum_image (fun a _ b _ hab => by
    have h := congrArg (ocd_innerRestrict iota) hab
    rwa [ocd_innerRestrict_psiExt hiota,
      ocd_innerRestrict_psiExt hiota] at h)]
  apply Finset.sum_congr rfl
  intro omega homega
  rw [ocd_condBcProbW_psiExt_eq_bcProbW Gin Gout iota bdryOut
    hiota hadjm hparam hpfOut hpfOut1 hq psi omega]
  by_cases hB : ocd_psiExt iota psi omega ∈ B
  · rw [Set.indicator_of_mem hB,
      Set.indicator_of_mem (Set.mem_preimage.mpr hB)]
  · rw [Set.indicator_of_notMem hB,
      Set.indicator_of_notMem (fun h => hB (Set.mem_preimage.mp h))]

lemma ocd_condBcProbW_psiExt_dominated
    (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    (bdryIn : Vin -> Prop) [DecidablePred bdryIn]
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (hpfIn : forall e, 0 < pfIn e) (hpfIn1 : forall e, pfIn e < 1)
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1)
    {q : Real} (hq : 1 <= q) (psi : ConfigSpace (Sym2 Vout))
    (hwire : ocd_inducedWiring Gout iota bdryOut psi <=
      Lattice.boundaryCliqueGraph bdryIn)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q
          (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW Gin (Lattice.boundaryCliqueGraph bdryIn) pfIn q omega := by
  rw [ocd_condBcProbW_psiExt_sum_eq_inducedBox Gin Gout iota bdryOut
    hiota hadjm hparam hpfOut hpfOut1 (zero_lt_one.trans_le hq) psi]
  have hpre : ocd_psiExt iota psi ⁻¹'
      (ocd_innerRestrict iota ⁻¹' A) = A := by
    ext omega
    simp only [Set.mem_preimage, ocd_innerRestrict_psiExt hiota]
  rw [hpre]
  exact bcProbW_mono_bc Gin
    (ocd_inducedWiring Gout iota bdryOut psi)
    (Lattice.boundaryCliqueGraph bdryIn) hwire hpfIn hpfIn1 hq hA

lemma ocd_free_le_condBcProbW_innerRestrict
    (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (hpfIn : forall e, 0 < pfIn e) (hpfIn1 : forall e, pfIn e < 1)
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1)
    {q : Real} (hq : 1 <= q) (psi : ConfigSpace (Sym2 Vout))
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW Gin ⊥ pfIn q omega) <=
      ∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q
          (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho := by
  rw [ocd_condBcProbW_psiExt_sum_eq_inducedBox Gin Gout iota bdryOut
    hiota hadjm hparam hpfOut hpfOut1 (zero_lt_one.trans_le hq) psi]
  have hpre : ocd_psiExt iota psi ⁻¹'
      (ocd_innerRestrict iota ⁻¹' A) = A := by
    ext omega
    simp only [Set.mem_preimage, ocd_innerRestrict_psiExt hiota]
  rw [hpre]
  exact bcProbW_mono_bc Gin (⊥ : SimpleGraph Vin)
    (ocd_inducedWiring Gout iota bdryOut psi)
    (bot_le : (⊥ : SimpleGraph Vin) <=
      ocd_inducedWiring Gout iota bdryOut psi)
    hpfIn hpfIn1 hq hA

/-! ## E. Domination -/

lemma bcProbW_eq_fibreMass_mul_condBcProbW
    {pf : Sym2 V -> Real} (hpf : forall e, 0 < pf e)
    (hpf1 : forall e, pf e < 1) {q : Real} (hq : 0 < q)
    (F : Finset (Sym2 V)) (omega : ConfigSpace (Sym2 V)) :
    bcProbW G C pf q omega =
      (∑ rho ∈ condFibre F omega, bcProbW G C pf q rho) *
        condBcProbW G C pf q F omega omega := by
  unfold condBcProbW
  rw [ite_eq_left (agreesOff_self F omega)]
  unfold bcProbW inducedBcZW bcZW
  have hZ : 0 < ∑ eta, bcWeightW G C pf q eta :=
    bcZW_pos G C hpf hpf1 hq
  have hI : 0 < ∑ rho ∈ condFibre F omega,
      bcWeightW G C pf q rho := by
    exact Finset.sum_pos
      (fun rho _ => bcWeightW_pos G C hpf hpf1 hq rho)
      ⟨omega, self_mem_condFibre F omega⟩
  rw [show (∑ rho ∈ condFibre F omega,
      bcWeightW G C pf q rho / ∑ eta, bcWeightW G C pf q eta) =
      (∑ rho ∈ condFibre F omega, bcWeightW G C pf q rho) /
        (∑ eta, bcWeightW G C pf q eta) by rw [Finset.sum_div]]
  field_simp

omit [DecidableEq Vin] in
lemma ocd_bcProbW_decompose (hiota : Function.Injective iota)
    {pfOut : Sym2 Vout -> Real}
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1) {q : Real} (hq : 0 < q)
    (B : Set (ConfigSpace (Sym2 Vout))) :
    (∑ rho, B.indicator (fun _ => (1 : Real)) rho *
        bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q rho) =
      ∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        (∑ sigma ∈ condFibre
            (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
          bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma) *
        (∑ rho, B.indicator (fun _ => (1 : Real)) rho *
          condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q
            (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho) := by
  classical
  let F := ocd_innerEdgeFinset (Vin := Vin) iota
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := ocd_outProj iota)
    (t := Finset.univ.filter (fun psi => ocd_outProj iota psi = psi))
    (fun rho _ => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ocd_outProj_idem hiota rho⟩)]
  apply Finset.sum_congr rfl
  intro psi hpsi
  rw [Finset.mem_filter] at hpsi
  rw [ocd_filter_outProj_eq_condFibre hiota psi hpsi.2]
  have hsupp : (∑ rho, B.indicator (fun _ => (1 : Real)) rho *
      condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q F psi rho) =
      ∑ rho ∈ condFibre F psi,
        B.indicator (fun _ => (1 : Real)) rho *
          condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut)
            pfOut q F psi rho := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro rho hrho hnot
    rw [mem_condFibre] at hnot
    unfold condBcProbW
    rw [ite_eq_right hnot, mul_zero]
  rw [hsupp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [mem_condFibre] at hrho
  have hfibre : condFibre F rho = condFibre F psi := by
    ext sigma
    rw [mem_condFibre, mem_condFibre,
      agreesOff_congr (agreesOff_symm hrho)]
  have hcond : condBcProbW Gout
      (Lattice.boundaryCliqueGraph bdryOut) pfOut q F rho rho =
      condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut)
        pfOut q F psi rho := by
    unfold condBcProbW inducedBcZW
    rw [ite_eq_left (agreesOff_self F rho), ite_eq_left hrho, hfibre]
  have hfac := bcProbW_eq_fibreMass_mul_condBcProbW Gout
    (Lattice.boundaryCliqueGraph bdryOut) hpfOut hpfOut1 hq F rho
  rw [hfibre, hcond] at hfac
  rw [hfac]
  ring

open Classical in
omit [DecidableEq Vin] in
lemma ocd_sum_fibreMassW_eq_one
    (hiota : Function.Injective iota)
    {pfOut : Sym2 Vout -> Real}
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1)
    {q : Real} (hq : 0 < q) :
    (∑ psi ∈ Finset.univ.filter
        (fun psi => ocd_outProj iota psi = psi),
      ∑ sigma ∈ condFibre
          (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
        bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut)
          pfOut q sigma) = 1 := by
  rw [show (∑ psi ∈ Finset.univ.filter
      (fun psi => ocd_outProj iota psi = psi),
    ∑ sigma ∈ condFibre
        (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
      bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma) =
    ∑ psi ∈ Finset.univ.filter
      (fun psi => ocd_outProj iota psi = psi),
    ∑ sigma ∈ Finset.univ.filter
        (fun rho => ocd_outProj iota rho = psi),
      bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma by
    apply Finset.sum_congr rfl
    intro psi hpsi
    rw [Finset.mem_filter] at hpsi
    rw [ocd_filter_outProj_eq_condFibre hiota psi hpsi.2]]
  rw [Finset.sum_fiberwise_of_maps_to
    (fun rho _ => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ocd_outProj_idem hiota rho⟩)]
  exact bcProbW_sum_eq_one Gout
    (Lattice.boundaryCliqueGraph bdryOut) hpfOut hpfOut1 hq

lemma ocd_free_inner_dominated_bcProbW
    (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (hpfIn : forall e, 0 < pfIn e) (hpfIn1 : forall e, pfIn e < 1)
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1)
    {q : Real} (hq : 1 <= q)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW Gin ⊥ pfIn q omega) <=
      ∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut)
          pfOut q rho := by
  let c := ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
    bcProbW Gin ⊥ pfIn q omega
  rw [ocd_bcProbW_decompose Gout iota bdryOut hiota hpfOut hpfOut1
    (zero_lt_one.trans_le hq) (ocd_innerRestrict iota ⁻¹' A)]
  calc
    c = (∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        ∑ sigma ∈ condFibre
            (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
          bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut)
            pfOut q sigma) * c := by
      rw [ocd_sum_fibreMassW_eq_one Gout iota bdryOut hiota
        hpfOut hpfOut1 (zero_lt_one.trans_le hq), one_mul]
    _ = ∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        (∑ sigma ∈ condFibre
            (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
          bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut)
            pfOut q sigma) * c := by
      rw [Finset.sum_mul]
    _ <= ∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        (∑ sigma ∈ condFibre
            (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
          bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut)
            pfOut q sigma) *
          (∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator
              (fun _ => (1 : Real)) rho *
            condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut)
              pfOut q (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho) := by
      apply Finset.sum_le_sum
      intro psi _
      apply mul_le_mul_of_nonneg_left
      · exact ocd_free_le_condBcProbW_innerRestrict
          Gin Gout iota bdryOut hiota hadjm hparam
          hpfIn hpfIn1 hpfOut hpfOut1 hq psi hA
      · exact Finset.sum_nonneg (fun sigma _ =>
          bcProbW_nonneg Gout (Lattice.boundaryCliqueGraph bdryOut)
            hpfOut hpfOut1 (zero_lt_one.trans_le hq) sigma)

lemma ocd_wired_inner_dominated_bcProbW
    (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    (bdryIn : Vin -> Prop) [DecidablePred bdryIn]
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (hpfIn : forall e, 0 < pfIn e) (hpfIn1 : forall e, pfIn e < 1)
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1)
    {q : Real} (hq : 1 <= q)
    (hwire : forall psi : ConfigSpace (Sym2 Vout),
      ocd_inducedWiring Gout iota bdryOut psi <=
        Lattice.boundaryCliqueGraph bdryIn)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q rho) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW Gin (Lattice.boundaryCliqueGraph bdryIn) pfIn q omega := by
  let c := ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
    bcProbW Gin (Lattice.boundaryCliqueGraph bdryIn) pfIn q omega
  rw [ocd_bcProbW_decompose Gout iota bdryOut hiota hpfOut hpfOut1
    (zero_lt_one.trans_le hq) (ocd_innerRestrict iota ⁻¹' A)]
  calc
    _ <= ∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        (∑ sigma ∈ condFibre
            (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
          bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma) * c := by
      apply Finset.sum_le_sum
      intro psi hpsi
      apply mul_le_mul_of_nonneg_left
      · exact ocd_condBcProbW_psiExt_dominated Gin Gout iota bdryOut
          hiota hadjm bdryIn hparam hpfIn hpfIn1 hpfOut hpfOut1 hq
          psi (hwire psi) hA
      · exact Finset.sum_nonneg (fun sigma hsigma =>
          bcProbW_nonneg Gout (Lattice.boundaryCliqueGraph bdryOut)
            hpfOut hpfOut1 (zero_lt_one.trans_le hq) sigma)
    _ = (∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        ∑ sigma ∈ condFibre
            (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
          bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma) * c := by
      rw [Finset.sum_mul]
    _ = c := by
      rw [show (∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        ∑ sigma ∈ condFibre
            (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
          bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma) = 1 by
        rw [show (∑ psi ∈ Finset.univ.filter
            (fun psi => ocd_outProj iota psi = psi),
          ∑ sigma ∈ condFibre
              (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
            bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma) =
          ∑ psi ∈ Finset.univ.filter
            (fun psi => ocd_outProj iota psi = psi),
          ∑ sigma ∈ Finset.univ.filter
              (fun rho => ocd_outProj iota rho = psi),
            bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma by
          apply Finset.sum_congr rfl
          intro psi hpsi
          rw [Finset.mem_filter] at hpsi
          rw [ocd_filter_outProj_eq_condFibre hiota psi hpsi.2]]
        rw [Finset.sum_fiberwise_of_maps_to
          (fun rho _ => Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, ocd_outProj_idem hiota rho⟩)]
        exact bcProbW_sum_eq_one Gout
          (Lattice.boundaryCliqueGraph bdryOut) hpfOut hpfOut1
            (zero_lt_one.trans_le hq), one_mul]

lemma ocd_latticeWired_inner_dominatedW
    {d : Nat} {Sin Sout : Set (Lattice.Site d)}
    [Fintype Sin] [Fintype Sout]
    (iota : {y : Lattice.Site d // y ∈ Sin} ->
      {y : Lattice.Site d // y ∈ Sout})
    (hiotaVal : forall x, (iota x : Lattice.Site d) = (x : Lattice.Site d))
    (hiota : Function.Injective iota)
    (bdryOut : {y : Lattice.Site d // y ∈ Sout} -> Prop)
    [DecidablePred bdryOut]
    (bdryIn : {y : Lattice.Site d // y ∈ Sin} -> Prop)
    [DecidablePred bdryIn]
    (hmargin : forall x : {y : Lattice.Site d // y ∈ Sin},
      ¬ bdryOut (iota x))
    (hbdryIn : forall (x : {y : Lattice.Site d // y ∈ Sin})
      (z : Lattice.Site d), Lattice.NearestNeighbour d (x : Lattice.Site d) z ->
        z ∉ Sin -> bdryIn x)
    {pfIn : Sym2 {y : Lattice.Site d // y ∈ Sin} -> Real}
    {pfOut : Sym2 {y : Lattice.Site d // y ∈ Sout} -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (hpfIn : forall e, 0 < pfIn e) (hpfIn1 : forall e, pfIn e < 1)
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1)
    {q : Real} (hq : 1 <= q)
    {A : Set (ConfigSpace (Sym2 {y : Lattice.Site d // y ∈ Sin}))}
    (hA : IsIncreasing A) :
    (∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        bcProbW (SimpleGraph.comap Subtype.val (Lattice.hypercubicLattice d))
          (Lattice.boundaryCliqueGraph bdryOut) pfOut q rho) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW (SimpleGraph.comap Subtype.val (Lattice.hypercubicLattice d))
          (Lattice.boundaryCliqueGraph bdryIn) pfIn q omega := by
  let Gin : SimpleGraph {y : Lattice.Site d // y ∈ Sin} :=
    SimpleGraph.comap Subtype.val (Lattice.hypercubicLattice d)
  let Gout : SimpleGraph {y : Lattice.Site d // y ∈ Sout} :=
    SimpleGraph.comap Subtype.val (Lattice.hypercubicLattice d)
  have hadjm : ocd_AdjMatch Gin Gout iota :=
    ocd_latticeAdjMatch iota hiotaVal
  have hwire := fun psi => ocd_latticeInducedWiring_le
    iota hiotaVal hiota bdryOut bdryIn hmargin hbdryIn psi
  exact ocd_wired_inner_dominated_bcProbW Gin Gout iota bdryOut hiota
    hadjm bdryIn hparam hpfIn hpfIn1 hpfOut hpfOut1 hq hwire hA

end FK
end StatMech

namespace StatMech
namespace OSSS
namespace FKSharpnessWeightedDomain

open StatMech.Lattice FK
open WiredBoxOffCentre FKSharpnessWeightedPeriodic

lemma weighted_transShellEvent_domain_dominated
    (d R k : Nat) (x : Site d)
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (hsub : fvs_transBox d (2 * k) x ⊆ box d R)
    (hmargin : forall y : fvs_transBoxVerts d (2 * k) x,
      ¬ boxBoundary d R (flc_incl hsub y))
    (hk : 1 <= k) (beta q : Real) (hbeta : 0 < beta) (hq : 1 <= q) :
    (∑ rho,
      (ocd_innerRestrict (flc_incl hsub) ⁻¹' transShellEvent d k x).indicator
          (fun _ => (1 : Real)) rho *
        bcProbW (boxGraph d R) (Lattice.boundaryCliqueGraph (boxBoundary d R))
          (FK.betaParams (boxCoupling J R) beta) q rho) <=
      ∑ eta,
        (transShellEvent d k x).indicator (fun _ => (1 : Real)) eta *
          bcProbW (fvs_transBoxGraph d (2 * k) x)
            (Lattice.boundaryCliqueGraph
              (fvs_transBoxBoundary d (2 * k) x))
            (FK.betaParams (transBoxCoupling J (2 * k) x) beta) q eta := by
  let pfIn := FK.betaParams (transBoxCoupling J (2 * k) x) beta
  let pfOut := FK.betaParams (boxCoupling J R) beta
  have hparam : ocd_ParamCompatible (flc_incl hsub) pfIn pfOut := by
    intro e
    unfold pfIn pfOut FK.betaParams transBoxCoupling boxCoupling
    congr 3
    simp [ocd_innerEdge, Sym2.map_map, flc_incl_val, Function.comp_def]
  have hpfIn : forall e, 0 < pfIn e :=
    FK.betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta
  have hpfIn1 : forall e, pfIn e < 1 :=
    FK.betaParams_lt_one _ beta
  have hpfOut : forall e, 0 < pfOut e :=
    FK.betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta
  have hpfOut1 : forall e, pfOut e < 1 :=
    FK.betaParams_lt_one _ beta
  have hdom := ocd_latticeWired_inner_dominatedW
    (Sin := fvs_transBox d (2 * k) x) (Sout := box d R)
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    (boxBoundary d R) (fvs_transBoxBoundary d (2 * k) x)
    hmargin (flc_hbdryIn_transBox (show 1 <= 2 * k by omega) x)
    hparam hpfIn hpfIn1 hpfOut hpfOut1 hq
    (A := transShellEvent d k x) (transShellEvent_increasing d k x)
  exact hdom

end FKSharpnessWeightedDomain
end OSSS
end StatMech
