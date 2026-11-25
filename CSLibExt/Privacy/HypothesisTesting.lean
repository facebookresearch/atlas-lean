/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.ApproximateDifferentialPrivacy
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

open scoped BigOperators
open scoped ENNReal

/-!
# Differential privacy as hypothesis testing

Finite-discrete formalization of the Kairouz-Oh-Viswanath (KOV) equivalence
between approximate differential privacy and hypothesis-testing tradeoffs,
plus f-DP basics and post-processing. All reasoning is over finite types with
explicit real-valued sums; no measure theory is used.

## Primary references

Kairouz, Oh and Viswanath, *The Composition Theorem for Differential
Privacy* (ICML 2015; journal version, *IEEE Transactions on Information
Theory*, 2017; arXiv:1311.0776): the pair of tradeoff inequalities is
`KOVpair` (their Theorem 2.1, Eq. 1); the equivalence between the pair
condition and the ordered DP event bounds is `kovpair_iff_event_bounds`;
the mechanism-level equivalence is `isApproxDPFin_iff_forall_kovpair` and
`isApproxDP_iff_forall_kovpair` (Theorem 2.1, region form in Corollary 2.3).

Dong, Roth and Su, *Gaussian Differential Privacy* (*Journal of the Royal
Statistical Society: Series B*, 2022; arXiv:1905.02383): the tradeoff
function `T(P, Q)` is `tradeoff` (their Definition 2.1, with `IsTest`,
`alphaOf` and `betaOf`); the `(eps, delta)` bound function is `fEpsDelta`
(their `f_{eps,delta}`); its lower bound on the tradeoff is
`kovpair_forward_tradeoff_ge` with converse `kovpair_of_tradeoff_ge` (the
two directions of Proposition 2.5); post-processing is `tradeoff_postprocess`
(Lemma 2.9, mechanism form in Proposition 2.8; also Theorem 2.4 of KOV).
-/

@[expose] public section

namespace CSLibExt.Privacy.HypothesisTesting

/-! ## Private wrappers around order and `ENNReal` lemmas -/

private lemma mul_le_mul_left_real {a b c : ℝ} (h : b ≤ c) (ha : 0 ≤ a) :
    a * b ≤ a * c := by
  exact mul_le_mul_of_nonneg_left h ha

private lemma mul_le_mul_right_real {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) :
    a * c ≤ b * c := by
  exact mul_le_mul_of_nonneg_right h hc

private lemma mul_nonneg_real {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  exact mul_nonneg ha hb

private lemma mul_nonpos_real {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  exact mul_nonpos_of_nonneg_of_nonpos ha hb

private lemma max_le_real {a b c : ℝ} (h1 : a ≤ c) (h2 : b ≤ c) : max a b ≤ c := by
  exact max_le h1 h2

private lemma le_max_left_real {a b : ℝ} : a ≤ max a b := by
  exact le_max_left _ _

private lemma le_max_right_real {a b : ℝ} : b ≤ max a b := by
  exact le_max_right _ _

private lemma max_eq_right_real {a b : ℝ} (h : a ≤ b) : max a b = b := by
  exact max_eq_right h

private lemma max_eq_left_real {a b : ℝ} (h : b ≤ a) : max a b = a := by
  exact max_eq_left h

private lemma toReal_ofReal_eq {x : ℝ} (hx : 0 ≤ x) :
    (ENNReal.ofReal x).toReal = x := by
  exact ENNReal.toReal_ofReal hx

private lemma toReal_nonneg_real {x : ℝ≥0∞} : 0 ≤ x.toReal := by
  exact ENNReal.toReal_nonneg

private lemma mul_ne_top_real {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    x * y ≠ ⊤ := by
  exact ENNReal.mul_ne_top hx hy

private lemma pmf_ne_top (Ω : Type*) [Fintype Ω] (P : PMF Ω) (w : Ω) :
    (P w : ℝ≥0∞) ≠ ⊤ := by
  exact PMF.apply_ne_top P w

private lemma exp_log_three (h3 : (0 : ℝ) < 3) : Real.exp (Real.log 3) = 3 := by
  exact Real.exp_log h3

/-! ## Finite-sum helpers -/

private lemma sum_zero_eq (Ω : Type*) [Fintype Ω] (s : Finset Ω) :
    ∑ _w ∈ s, (0 : ℝ) = 0 := by
  exact Finset.sum_const_zero

private lemma sum_singleton_eq (Ω : Type*) [Fintype Ω] (f : Ω → ℝ) (a : Ω) :
    ∑ w ∈ ({a} : Finset Ω), f w = f a := by
  exact Finset.sum_singleton f a

private lemma sum_empty_eq (Ω : Type*) [Fintype Ω] (f : Ω → ℝ) :
    ∑ w ∈ (∅ : Finset Ω), f w = 0 := by
  exact Finset.sum_empty

lemma sum_add_compl_eq (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (f : Ω → ℝ) (S : Finset Ω) :
    (∑ w ∈ S, f w) + (∑ w ∈ Sᶜ, f w) = ∑ w, f w := by
  rw [Finset.compl_eq_univ_sdiff, add_comm]
  apply Finset.sum_sdiff
  exact Finset.subset_univ S

/-! ## Total mass of a `PMF` in real form -/

lemma pmf_toReal_sum (Ω : Type*) [Fintype Ω] (P : PMF Ω) :
    ∑ w, (P w).toReal = 1 := by
  have hsum : (∑ w, (P w : ℝ≥0∞)) = 1 := by
    have h := P.tsum_coe
    rw [tsum_fintype] at h
    exact h
  have htr : (∑ w, (P w : ℝ≥0∞)).toReal = (1 : ℝ≥0∞).toReal :=
    congrArg ENNReal.toReal hsum
  have hpush : (∑ w, (P w : ℝ≥0∞)).toReal = ∑ w, (P w).toReal := by
    apply ENNReal.toReal_sum
    intro w _
    exact pmf_ne_top Ω P w
  rw [hpush] at htr
  rw [ENNReal.toReal_one] at htr
  exact htr

lemma pmf_sum_add_compl (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (P : PMF Ω) (S : Finset Ω) :
    (∑ w ∈ S, (P w).toReal) + (∑ w ∈ Sᶜ, (P w).toReal) = 1 := by
  have hsplit : (∑ w ∈ S, (P w).toReal) + (∑ w ∈ Sᶜ, (P w).toReal)
      = ∑ w, (P w).toReal :=
    sum_add_compl_eq Ω (fun w => (P w).toReal) S
  rw [hsplit]
  exact pmf_toReal_sum Ω P

/-! ## H1: the KOV pair condition and event bounds -/

/-- Type-I error (false positive mass) of the rejection set `S`. -/
noncomputable def typeI (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (P : PMF Ω) (S : Finset Ω) : ℝ :=
  ∑ w ∈ S, (P w).toReal

/-- Type-II error (false negative mass) of the rejection set `S`. -/
noncomputable def typeII (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (Q : PMF Ω) (S : Finset Ω) : ℝ :=
  ∑ w ∈ Sᶜ, (Q w).toReal

/-- The KOV pair condition: for every rejection set, type-I and type-II error
satisfy both tradeoff inequalities. -/
def KOVpair (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (P Q : PMF Ω) (eps delta : ℝ) : Prop :=
  ∀ S : Finset Ω,
    typeI Ω P S + Real.exp eps * typeII Ω Q S ≥ 1 - delta ∧
      Real.exp eps * typeI Ω P S + typeII Ω Q S ≥ 1 - delta

/-- Approximate differential privacy of a mechanism on finite outputs, with
global nonnegative real budgets as in `DifferentialPrivacy.IsApproxDP`. -/
def IsApproxDPFin (D Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (M : D → PMF Ω) (adj : D → D → Prop) (eps delta : ℝ) : Prop :=
  0 ≤ eps ∧ 0 ≤ delta ∧ ∀ d d2 : D, adj d d2 → ∀ S : Finset Ω,
    (∑ w ∈ S, ((M d) w).toReal)
      ≤ Real.exp eps * (∑ w ∈ S, ((M d2) w).toReal) + delta

lemma typeI_nonneg (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (P : PMF Ω) (S : Finset Ω) : 0 ≤ typeI Ω P S := by
  simp only [typeI]
  apply Finset.sum_nonneg
  intro w _
  exact toReal_nonneg_real

lemma typeI_le_one (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (P : PMF Ω) (S : Finset Ω) : typeI Ω P S ≤ 1 := by
  have hsplit := pmf_sum_add_compl Ω P S
  have hnn : 0 ≤ ∑ w ∈ Sᶜ, (P w).toReal := by
    apply Finset.sum_nonneg
    intro w _
    exact toReal_nonneg_real
  have heq : typeI Ω P S = ∑ w ∈ S, (P w).toReal := rfl
  rw [heq]
  linarith [hsplit, hnn]

/-- H1 pair lemma: the KOV condition holds iff the DP event bounds hold in
both orders at every event. -/
theorem kovpair_iff_event_bounds (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (P Q : PMF Ω) (eps delta : ℝ) :
    KOVpair Ω P Q eps delta ↔
      ∀ S : Finset Ω,
        (∑ w ∈ S, (P w).toReal)
            ≤ Real.exp eps * (∑ w ∈ S, (Q w).toReal) + delta ∧
        (∑ w ∈ S, (Q w).toReal)
            ≤ Real.exp eps * (∑ w ∈ S, (P w).toReal) + delta := by
  constructor
  · intro hKov S
    have hsplitP := pmf_sum_add_compl Ω P S
    have hsplitQ := pmf_sum_add_compl Ω Q S
    constructor
    · have hA := (hKov Sᶜ).1
      simp only [typeI, typeII, compl_compl] at hA
      linarith [hA, hsplitP]
    · have hB := (hKov S).2
      simp only [typeI, typeII] at hB
      linarith [hB, hsplitQ]
  · intro hev S
    have hsplitP := pmf_sum_add_compl Ω P S
    have hsplitQ := pmf_sum_add_compl Ω Q S
    constructor
    · have hP := (hev Sᶜ).1
      simp only [typeI, typeII]
      linarith [hP, hsplitP]
    · have hQ := (hev S).2
      simp only [typeI, typeII]
      linarith [hQ, hsplitQ]

/-- One-sided ordered lemma: DP in both adjacent orders gives the pair
condition, with no global symmetry hypothesis. -/
theorem kovpair_of_isApproxDPFin_of_swap (D Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (M : D → PMF Ω) (adj : D → D → Prop) (eps delta : ℝ) (d d2 : D)
    (hdp : IsApproxDPFin D Ω M adj eps delta) (h12 : adj d d2) (h21 : adj d2 d) :
    KOVpair Ω (M d) (M d2) eps delta := by
  rw [kovpair_iff_event_bounds Ω (M d) (M d2) eps delta]
  intro S
  exact ⟨hdp.2.2 d d2 h12 S, hdp.2.2 d2 d h21 S⟩

/-- One-sided ordered lemma: the pair condition at every adjacent pair gives
DP, with no symmetry hypothesis. -/
theorem isApproxDPFin_of_forall_kovpair (D Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (M : D → PMF Ω) (adj : D → D → Prop) (eps delta : ℝ)
    (hε : 0 ≤ eps) (hδ : 0 ≤ delta)
    (hkov : ∀ d d2 : D, adj d d2 → KOVpair Ω (M d) (M d2) eps delta) :
    IsApproxDPFin D Ω M adj eps delta := by
  refine ⟨hε, hδ, fun d d2 hadj S => ?_⟩
  exact ((kovpair_iff_event_bounds Ω (M d) (M d2) eps delta).mp
    (hkov d d2 hadj) S).1

/-- H1 mechanism theorem: for symmetric adjacency and nonnegative budgets,
approximate DP is equivalent to the KOV pair condition at every adjacent
pair. Only the forward direction needs symmetry: ordered DP at `(d, d2)`
supplies just one of the two event bounds, so the reverse bound comes from
DP at `(d2, d)` via symmetry. The converse needs none: the pair condition
at each ordered adjacent pair already yields the ordered DP bound there. -/
theorem isApproxDPFin_iff_forall_kovpair (D Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (M : D → PMF Ω) (adj : D → D → Prop) (eps delta : ℝ)
    (hε : 0 ≤ eps) (hδ : 0 ≤ delta) (hsym : Symmetric adj) :
    IsApproxDPFin D Ω M adj eps delta ↔
      ∀ d d2 : D, adj d d2 → KOVpair Ω (M d) (M d2) eps delta := by
  constructor
  · intro hdp d d2 hadj
    exact kovpair_of_isApproxDPFin_of_swap D Ω M adj eps delta d d2 hdp hadj
      (hsym hadj)
  · intro hkov
    exact isApproxDPFin_of_forall_kovpair D Ω M adj eps delta hε hδ hkov

/-! ## Bridge to the event-form predicate -/

lemma toOuterMeasure_eq_sum_filter (Ω : Type*) [Fintype Ω]
    (p : PMF Ω) (s : Set Ω) [DecidablePred (· ∈ s)] :
    p.toOuterMeasure s
      = ∑ w ∈ Finset.univ.filter (fun w => w ∈ s), (p w : ℝ≥0∞) := by
  rw [PMF.toOuterMeasure_apply, tsum_fintype, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : w ∈ s
  · rw [Set.indicator_of_mem hw, ite_eq_left hw]
  · rw [Set.indicator_of_notMem hw, ite_eq_right hw]

lemma toOuterMeasure_toReal (Ω : Type*) [Fintype Ω]
    (p : PMF Ω) (s : Set Ω) [DecidablePred (· ∈ s)] :
    (p.toOuterMeasure s).toReal
      = ∑ w ∈ Finset.univ.filter (fun w => w ∈ s), (p w).toReal := by
  rw [toOuterMeasure_eq_sum_filter]
  exact ENNReal.toReal_sum fun w _ => pmf_ne_top Ω p w

lemma toOuterMeasure_le_one (Ω : Type*) (p : PMF Ω) (s : Set Ω) :
    p.toOuterMeasure s ≤ 1 := by
  rw [PMF.toOuterMeasure_apply, ← p.tsum_coe]
  exact ENNReal.tsum_le_tsum fun a => Set.indicator_le_self s p a

lemma toOuterMeasure_ne_top (Ω : Type*) (p : PMF Ω) (s : Set Ω) :
    p.toOuterMeasure s ≠ ⊤ := by
  exact ne_of_lt ((toOuterMeasure_le_one Ω p s).trans_lt ENNReal.one_lt_top)

/-- The finite-sum predicate agrees with the event-form predicate on finite
outputs. Both sides carry their own nonnegative-budget invariants. -/
theorem isApproxDPFin_iff_isApproxDP (D Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (M : D → PMF Ω) (adj : D → D → Prop) (eps delta : ℝ) :
    IsApproxDPFin D Ω M adj eps delta ↔
      DifferentialPrivacy.IsApproxDP M adj eps delta := by
  classical
  have hE0 : 0 ≤ Real.exp eps := (Real.exp_pos eps).le
  have htop : ∀ (p : PMF Ω) (s : Set Ω),
      ENNReal.ofReal (Real.exp eps) * p.toOuterMeasure s
        + ENNReal.ofReal delta ≠ ⊤ := by
    intro p s hcon
    rcases ENNReal.add_eq_top.mp hcon with h1 | h2
    · exact mul_ne_top_real ENNReal.ofReal_ne_top
        (toOuterMeasure_ne_top Ω p s) h1
    · exact ENNReal.ofReal_ne_top h2
  constructor
  · rintro ⟨hε, hδ, hFin⟩
    refine ⟨hε, hδ, fun d d' hadj s => ?_⟩
    have hS := hFin d d' hadj (Finset.univ.filter fun w => w ∈ s)
    have hto : ((M d).toOuterMeasure s).toReal
        ≤ (ENNReal.ofReal (Real.exp eps) * (M d').toOuterMeasure s
          + ENNReal.ofReal delta).toReal := by
      rw [toOuterMeasure_toReal Ω (M d) s,
        ENNReal.toReal_add
          (mul_ne_top_real ENNReal.ofReal_ne_top
            (toOuterMeasure_ne_top Ω (M d') s))
          ENNReal.ofReal_ne_top,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal hE0,
        toOuterMeasure_toReal Ω (M d') s, ENNReal.toReal_ofReal hδ]
      exact hS
    exact (ENNReal.toReal_le_toReal (toOuterMeasure_ne_top Ω (M d) s)
      (htop (M d') s)).mp hto
  · rintro ⟨hε, hδ, hEvent⟩
    refine ⟨hε, hδ, fun d d' hadj S => ?_⟩
    have h := hEvent d d' hadj (↑S)
    have hto := ENNReal.toReal_mono (htop (M d') (↑S)) h
    rw [toOuterMeasure_toReal, ENNReal.toReal_add
        (mul_ne_top_real ENNReal.ofReal_ne_top
          (toOuterMeasure_ne_top Ω (M d') (↑S)))
        ENNReal.ofReal_ne_top,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hE0,
      toOuterMeasure_toReal, ENNReal.toReal_ofReal hδ] at hto
    have hfilter : Finset.univ.filter (fun w => w ∈ (↑S : Set Ω)) = S := by
      ext w
      simp
    rw [← hfilter]
    exact hto

/-- H1 mechanism theorem for the event-form predicate: for symmetric
adjacency and nonnegative budgets, event-form approximate DP is equivalent
to the KOV pair condition at every adjacent pair. -/
theorem isApproxDP_iff_forall_kovpair (D Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (M : D → PMF Ω) (adj : D → D → Prop) (eps delta : ℝ)
    (hε : 0 ≤ eps) (hδ : 0 ≤ delta) (hsym : Symmetric adj) :
    DifferentialPrivacy.IsApproxDP M adj eps delta ↔
      ∀ d d2 : D, adj d d2 → KOVpair Ω (M d) (M d2) eps delta := by
  rw [← isApproxDPFin_iff_isApproxDP D Ω M adj eps delta]
  exact isApproxDPFin_iff_forall_kovpair D Ω M adj eps delta hε hδ hsym

/-- The KOV pair condition is symmetric in the two distributions. -/
lemma kovpair_symm (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (P Q : PMF Ω) (eps delta : ℝ) (h : KOVpair Ω P Q eps delta) :
    KOVpair Ω Q P eps delta := by
  rw [kovpair_iff_event_bounds Ω Q P eps delta]
  have hev := (kovpair_iff_event_bounds Ω P Q eps delta).mp h
  intro S
  exact ⟨(hev S).2, (hev S).1⟩

/-! ## H2: randomized tests and the tradeoff function -/

/-- A randomized test takes values in `[0, 1]`. -/
def IsTest (Ω : Type*) (phi : Ω → ℝ) : Prop :=
  ∀ w, 0 ≤ phi w ∧ phi w ≤ 1

/-- Type-I error of a randomized test. -/
noncomputable def alphaOf (Ω : Type*) [Fintype Ω]
    (P : PMF Ω) (phi : Ω → ℝ) : ℝ :=
  ∑ w, (P w).toReal * phi w

/-- Type-II error of a randomized test. -/
noncomputable def betaOf (Ω : Type*) [Fintype Ω]
    (Q : PMF Ω) (phi : Ω → ℝ) : ℝ :=
  ∑ w, (Q w).toReal * (1 - phi w)

/-- The hypothesis-testing tradeoff function: the least type-II error among
tests whose type-I error is at most `alpha`.

Total extension outside `[0, 1]`: for `alpha < 0` no test is feasible, since
type-I error is always nonnegative, so the feasible set is empty and
`sInf ∅ = 0` (see `tradeoff_eq_zero_of_neg`); for `1 ≤ alpha` the
always-reject test is feasible with type-II error `0`, so the value is `0`
(see `tradeoff_eq_zero_of_one_le`). -/
noncomputable def tradeoff (Ω : Type*) [Fintype Ω]
    (P Q : PMF Ω) (alpha : ℝ) : ℝ :=
  sInf { b : ℝ | ∃ phi : Ω → ℝ,
    IsTest Ω phi ∧ alphaOf Ω P phi ≤ alpha ∧ betaOf Ω Q phi = b }

lemma alphaOf_nonneg (Ω : Type*) [Fintype Ω]
    (P : PMF Ω) (phi : Ω → ℝ) (hphi : IsTest Ω phi) :
    0 ≤ alphaOf Ω P phi := by
  simp only [alphaOf]
  apply Finset.sum_nonneg
  intro w _
  exact mul_nonneg_real toReal_nonneg_real (hphi w).1

lemma betaOf_nonneg (Ω : Type*) [Fintype Ω]
    (Q : PMF Ω) (phi : Ω → ℝ) (hphi : IsTest Ω phi) :
    0 ≤ betaOf Ω Q phi := by
  simp only [betaOf]
  apply Finset.sum_nonneg
  intro w _
  have h1w : 0 ≤ 1 - phi w := by linarith [(hphi w).2]
  exact mul_nonneg_real toReal_nonneg_real h1w

lemma test_phi0 (Ω : Type*) [Fintype Ω] : IsTest Ω (fun _ => (0 : ℝ)) :=
  fun _ => ⟨le_refl 0, zero_le_one⟩

lemma test_phi1 (Ω : Type*) [Fintype Ω] : IsTest Ω (fun _ => (1 : ℝ)) :=
  fun _ => ⟨zero_le_one, le_refl 1⟩

lemma alphaOf_phi0 (Ω : Type*) [Fintype Ω] (P : PMF Ω) :
    alphaOf Ω P (fun _ => (0 : ℝ)) = 0 := by
  simp only [alphaOf, mul_zero, sum_zero_eq]

lemma betaOf_phi0 (Ω : Type*) [Fintype Ω] (Q : PMF Ω) :
    betaOf Ω Q (fun _ => (0 : ℝ)) = 1 := by
  simp only [betaOf, sub_zero, mul_one]
  exact pmf_toReal_sum Ω Q

lemma alphaOf_phi1 (Ω : Type*) [Fintype Ω] (P : PMF Ω) :
    alphaOf Ω P (fun _ => (1 : ℝ)) = 1 := by
  simp only [alphaOf, mul_one]
  exact pmf_toReal_sum Ω P

lemma betaOf_phi1 (Ω : Type*) [Fintype Ω] (Q : PMF Ω) :
    betaOf Ω Q (fun _ => (1 : ℝ)) = 0 := by
  simp only [betaOf, sub_self, mul_zero, sum_zero_eq]

lemma tradeoff_set_nonempty (Ω : Type*) [Fintype Ω]
    (P Q : PMF Ω) (alpha : ℝ) (hα0 : 0 ≤ alpha) :
    { b : ℝ | ∃ phi : Ω → ℝ,
      IsTest Ω phi ∧ alphaOf Ω P phi ≤ alpha ∧ betaOf Ω Q phi = b
    }.Nonempty := by
  have htest0 : IsTest Ω (fun _ => (0 : ℝ)) := test_phi0 Ω
  have hα0' : alphaOf Ω P (fun _ => (0 : ℝ)) ≤ alpha := by
    have hz : alphaOf Ω P (fun _ => (0 : ℝ)) = 0 := alphaOf_phi0 Ω P
    rw [hz]
    exact hα0
  exact ⟨betaOf Ω Q (fun _ => (0 : ℝ)), (fun _ => (0 : ℝ)),
    htest0, hα0', rfl⟩

lemma tradeoff_bddBelow (Ω : Type*) [Fintype Ω] (P Q : PMF Ω) (alpha : ℝ) :
    BddBelow { b : ℝ | ∃ phi : Ω → ℝ,
      IsTest Ω phi ∧ alphaOf Ω P phi ≤ alpha ∧ betaOf Ω Q phi = b } := by
  refine ⟨0, ?_⟩
  intro b hb
  simp only [Set.mem_ofPred_eq] at hb
  obtain ⟨phi, hphi, -, rfl⟩ := hb
  exact betaOf_nonneg Ω Q phi hphi

/-- Lower bounds on the tradeoff function: it suffices to bound the type-II
error of every feasible test. Stated only for `0 ≤ alpha`. -/
lemma le_tradeoff (Ω : Type*) [Fintype Ω] (P Q : PMF Ω) (alpha x : ℝ)
    (hα0 : 0 ≤ alpha)
    (h : ∀ phi : Ω → ℝ, IsTest Ω phi → alphaOf Ω P phi ≤ alpha →
      x ≤ betaOf Ω Q phi) :
    x ≤ tradeoff Ω P Q alpha := by
  have hne := tradeoff_set_nonempty Ω P Q alpha hα0
  have hbd := tradeoff_bddBelow Ω P Q alpha
  have hall : ∀ b ∈ { b : ℝ | ∃ phi : Ω → ℝ,
      IsTest Ω phi ∧ alphaOf Ω P phi ≤ alpha ∧ betaOf Ω Q phi = b },
      x ≤ b := by
    intro b hb
    simp only [Set.mem_ofPred_eq] at hb
    obtain ⟨phi, hphi, hα, rfl⟩ := hb
    exact h phi hphi hα
  show x ≤ sInf { b : ℝ | ∃ phi : Ω → ℝ,
    IsTest Ω phi ∧ alphaOf Ω P phi ≤ alpha ∧ betaOf Ω Q phi = b }
  apply le_csInf <;> assumption

/-- Upper bounds on the tradeoff function: every feasible test witnesses one.
Stated only for `0 ≤ alpha`. -/
lemma tradeoff_le_betaOf (Ω : Type*) [Fintype Ω] (P Q : PMF Ω)
    (alpha : ℝ) (phi : Ω → ℝ) (hα0 : 0 ≤ alpha) (hphi : IsTest Ω phi)
    (hα : alphaOf Ω P phi ≤ alpha) :
    tradeoff Ω P Q alpha ≤ betaOf Ω Q phi := by
  have hne := tradeoff_set_nonempty Ω P Q alpha hα0
  have hbd := tradeoff_bddBelow Ω P Q alpha
  have hmem : betaOf Ω Q phi ∈ { b : ℝ | ∃ phi : Ω → ℝ,
      IsTest Ω phi ∧ alphaOf Ω P phi ≤ alpha ∧ betaOf Ω Q phi = b } :=
    ⟨phi, hphi, hα, rfl⟩
  show sInf { b : ℝ | ∃ phi : Ω → ℝ,
    IsTest Ω phi ∧ alphaOf Ω P phi ≤ alpha ∧ betaOf Ω Q phi = b }
    ≤ betaOf Ω Q phi
  apply csInf_le <;> assumption

/-- The tradeoff at `alpha = 1` is `0` in general, via the always-reject
test. -/
theorem tradeoff_at_one (Ω : Type*) [Fintype Ω] (P Q : PMF Ω) :
    tradeoff Ω P Q 1 = 0 := by
  apply le_antisymm
  · have htest1 : IsTest Ω (fun _ => (1 : ℝ)) := test_phi1 Ω
    have hα : alphaOf Ω P (fun _ => (1 : ℝ)) ≤ 1 :=
      le_of_eq (alphaOf_phi1 Ω P)
    have h := tradeoff_le_betaOf Ω P Q 1 (fun _ => (1 : ℝ)) zero_le_one
      htest1 hα
    rw [betaOf_phi1 Ω Q] at h
    exact h
  · refine le_tradeoff Ω P Q 1 0 zero_le_one ?_
    intro phi hphi _
    exact betaOf_nonneg Ω Q phi hphi

/-- Below `[0, 1]`: no test is feasible, so the tradeoff is `sInf ∅ = 0`. -/
theorem tradeoff_eq_zero_of_neg (Ω : Type*) [Fintype Ω]
    (P Q : PMF Ω) (alpha : ℝ) (hα : alpha < 0) :
    tradeoff Ω P Q alpha = 0 := by
  have hempty : { b : ℝ | ∃ phi : Ω → ℝ,
      IsTest Ω phi ∧ alphaOf Ω P phi ≤ alpha ∧ betaOf Ω Q phi = b } = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro b hb
    simp only [Set.mem_ofPred_eq] at hb
    obtain ⟨phi, hphi, hαphi, -⟩ := hb
    have hnn := alphaOf_nonneg Ω P phi hphi
    linarith
  show sInf { b : ℝ | ∃ phi : Ω → ℝ,
    IsTest Ω phi ∧ alphaOf Ω P phi ≤ alpha ∧ betaOf Ω Q phi = b } = 0
  rw [hempty, Real.sInf_empty]

/-- Above `[0, 1]`: the always-reject test is feasible with type-II error `0`,
so the tradeoff is `0`. -/
theorem tradeoff_eq_zero_of_one_le (Ω : Type*) [Fintype Ω]
    (P Q : PMF Ω) (alpha : ℝ) (hα : 1 ≤ alpha) :
    tradeoff Ω P Q alpha = 0 := by
  apply le_antisymm
  · have htest1 : IsTest Ω (fun _ => (1 : ℝ)) := test_phi1 Ω
    have hαphi : alphaOf Ω P (fun _ => (1 : ℝ)) ≤ alpha := by
      rw [alphaOf_phi1 Ω P]
      exact hα
    have h := tradeoff_le_betaOf Ω P Q alpha (fun _ => (1 : ℝ))
      (by linarith) htest1 hαphi
    rw [betaOf_phi1 Ω Q] at h
    exact h
  · refine le_tradeoff Ω P Q alpha 0 (by linarith) ?_
    intro phi hphi _
    exact betaOf_nonneg Ω Q phi hphi

/-! ## H3: the f-DP lower bound -/

/-- The `(eps, delta)`-DP tradeoff lower bound. -/
noncomputable def fEpsDelta (eps delta alpha : ℝ) : ℝ :=
  max 0 (max (1 - delta - Real.exp eps * alpha)
    (Real.exp (-eps) * (1 - delta - alpha)))

/-- Signed-mass trick: a test-weighted signed sum is bounded by the positive
part, hence by any bound on the single superlevel event. -/
lemma test_superlevel_le (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (phi : Ω → ℝ) (hphi : IsTest Ω phi) (v : Ω → ℝ) (delta : ℝ)
    (S : Finset Ω) (hmem : ∀ w, w ∈ S ↔ 0 < v w)
    (hbound : ∑ w ∈ S, v w ≤ delta) :
    ∑ w, phi w * v w ≤ delta := by
  have hsplit : (∑ w ∈ S, phi w * v w) + (∑ w ∈ Sᶜ, phi w * v w)
      = ∑ w, phi w * v w :=
    sum_add_compl_eq Ω (fun w => phi w * v w) S
  have hS : ∑ w ∈ S, phi w * v w ≤ ∑ w ∈ S, v w := by
    apply Finset.sum_le_sum
    intro w hw
    have hv : 0 < v w := (hmem w).mp hw
    have h1 : phi w ≤ 1 := (hphi w).2
    calc phi w * v w ≤ 1 * v w := mul_le_mul_right_real h1 (le_of_lt hv)
      _ = v w := one_mul _
  have hSc : ∑ w ∈ Sᶜ, phi w * v w ≤ 0 := by
    apply Finset.sum_nonpos
    intro w hw
    have hwn : w ∉ S := Finset.mem_compl.mp hw
    have hv : v w ≤ 0 := le_of_not_gt (fun h => hwn ((hmem w).mpr h))
    have h0 : 0 ≤ phi w := (hphi w).1
    exact mul_nonpos_real h0 hv
  calc ∑ w, phi w * v w
      = (∑ w ∈ S, phi w * v w) + (∑ w ∈ Sᶜ, phi w * v w) := hsplit.symm
    _ ≤ (∑ w ∈ S, v w) + 0 := add_le_add hS hSc
    _ ≤ delta := by linarith [hbound]

/-- H3 forward: the KOV pair condition implies the f-DP lower bound on the
tradeoff function, on `0 ≤ alpha ≤ 1`. -/
theorem kovpair_forward_tradeoff_ge (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (P Q : PMF Ω) (eps delta alpha : ℝ)
    (hKov : KOVpair Ω P Q eps delta) (hα0 : 0 ≤ alpha) (hα1 : alpha ≤ 1) :
    fEpsDelta eps delta alpha ≤ tradeoff Ω P Q alpha := by
  have hev := (kovpair_iff_event_bounds Ω P Q eps delta).mp hKov
  have hE0 : 0 ≤ Real.exp eps := (Real.exp_pos eps).le
  have hE'0 : 0 ≤ Real.exp (-eps) := (Real.exp_pos _).le
  refine le_tradeoff Ω P Q alpha (fEpsDelta eps delta alpha) hα0 ?_
  intro phi hphi hαphi
  set vA : Ω → ℝ := fun w => (Q w).toReal - Real.exp eps * (P w).toReal
    with hvA
  set SA : Finset Ω := Finset.univ.filter (fun w => 0 < vA w) with hSA
  have hmemA : ∀ w, w ∈ SA ↔ 0 < vA w := fun w => by
    simp only [hSA, Finset.mem_filter, Finset.mem_univ, true_and]
  have hδA : ∑ w ∈ SA, vA w ≤ delta := by
    have hQ := (hev SA).2
    have hexpand : ∑ w ∈ SA, vA w
        = (∑ w ∈ SA, (Q w).toReal)
          - Real.exp eps * (∑ w ∈ SA, (P w).toReal) := by
      simp only [hvA, Finset.sum_sub_distrib]
      congr 1
      rw [Finset.mul_sum]
    linarith [hexpand, hQ]
  have hAsum : ∑ w, phi w * vA w ≤ delta :=
    test_superlevel_le Ω phi hphi vA delta SA hmemA hδA
  have hβphi : betaOf Ω Q phi = 1 - ∑ w, (Q w).toReal * phi w := by
    have hpt : ∀ w : Ω, (Q w).toReal * (1 - phi w)
        = (Q w).toReal - (Q w).toReal * phi w := fun w => by ring
    have hmass : ∑ w, (Q w).toReal = 1 := pmf_toReal_sum Ω Q
    simp only [betaOf, hpt, Finset.sum_sub_distrib]
    linarith [hmass]
  have hαphi' : ∑ w, phi w * (P w).toReal = alphaOf Ω P phi := by
    have hpt : ∀ w : Ω, phi w * (P w).toReal = (P w).toReal * phi w :=
      fun w => mul_comm _ _
    simp only [alphaOf, hpt]
  have hAform : ∑ w, phi w * vA w
      = (1 - betaOf Ω Q phi) - Real.exp eps * alphaOf Ω P phi := by
    have hpt : ∀ w : Ω, phi w * vA w
        = phi w * (Q w).toReal - Real.exp eps * (phi w * (P w).toReal) := by
      intro w
      simp only [hvA]
      ring
    have hqphi : ∑ w, phi w * (Q w).toReal = 1 - betaOf Ω Q phi := by
      have hpt2 : ∀ w : Ω, phi w * (Q w).toReal = (Q w).toReal * phi w :=
        fun w => mul_comm _ _
      simp only [hpt2]
      linarith [hβphi]
    simp only [hpt, Finset.sum_sub_distrib]
    have hfac : ∑ w, Real.exp eps * (phi w * (P w).toReal)
        = Real.exp eps * (∑ w, phi w * (P w).toReal) := by
      rw [Finset.mul_sum]
    rw [hfac, hqphi, hαphi']
  have hA' : (1 - betaOf Ω Q phi) - Real.exp eps * alphaOf Ω P phi
      ≤ delta := by
    rw [← hAform]
    exact hAsum
  set psi : Ω → ℝ := fun w => 1 - phi w with hpsi_def
  have hpsi : IsTest Ω psi := by
    intro w
    obtain ⟨h0, h1⟩ := hphi w
    simp only [hpsi_def]
    constructor <;> linarith
  set vB : Ω → ℝ := fun w => (P w).toReal - Real.exp eps * (Q w).toReal
    with hvB
  set SB : Finset Ω := Finset.univ.filter (fun w => 0 < vB w) with hSB
  have hmemB : ∀ w, w ∈ SB ↔ 0 < vB w := fun w => by
    simp only [hSB, Finset.mem_filter, Finset.mem_univ, true_and]
  have hδB : ∑ w ∈ SB, vB w ≤ delta := by
    have hP := (hev SB).1
    have hexpand : ∑ w ∈ SB, vB w
        = (∑ w ∈ SB, (P w).toReal)
          - Real.exp eps * (∑ w ∈ SB, (Q w).toReal) := by
      simp only [hvB, Finset.sum_sub_distrib]
      congr 1
      rw [Finset.mul_sum]
    linarith [hexpand, hP]
  have hBsum : ∑ w, psi w * vB w ≤ delta :=
    test_superlevel_le Ω psi hpsi vB delta SB hmemB hδB
  have hBform : ∑ w, psi w * vB w
      = (1 - alphaOf Ω P phi) - Real.exp eps * betaOf Ω Q phi := by
    have hpt : ∀ w : Ω, psi w * vB w
        = psi w * (P w).toReal
          - Real.exp eps * (psi w * (Q w).toReal) := by
      intro w
      simp only [hvB]
      ring
    have hpsiP : ∑ w, psi w * (P w).toReal = 1 - alphaOf Ω P phi := by
      have hpt2 : ∀ w : Ω, psi w * (P w).toReal
          = (P w).toReal - phi w * (P w).toReal := by
        intro w
        simp only [hpsi_def]
        ring
      have hmass : ∑ w, (P w).toReal = 1 := pmf_toReal_sum Ω P
      simp only [hpt2, Finset.sum_sub_distrib]
      rw [hmass, hαphi']
    have hpsiQ : ∑ w, psi w * (Q w).toReal = betaOf Ω Q phi := by
      have hpt2 : ∀ w : Ω, psi w * (Q w).toReal
          = (Q w).toReal * (1 - phi w) := by
        intro w
        simp only [hpsi_def]
        ring
      simp only [hpt2, betaOf]
    simp only [hpt, Finset.sum_sub_distrib]
    have hfac : ∑ w, Real.exp eps * (psi w * (Q w).toReal)
        = Real.exp eps * (∑ w, psi w * (Q w).toReal) := by
      rw [Finset.mul_sum]
    rw [hfac, hpsiP, hpsiQ]
  have hB' : (1 - alphaOf Ω P phi) - Real.exp eps * betaOf Ω Q phi
      ≤ delta := by
    rw [← hBform]
    exact hBsum
  have hβ0 : 0 ≤ betaOf Ω Q phi := betaOf_nonneg Ω Q phi hphi
  have hii : 1 - delta - Real.exp eps * alpha ≤ betaOf Ω Q phi := by
    have hEα : Real.exp eps * alphaOf Ω P phi ≤ Real.exp eps * alpha :=
      mul_le_mul_left_real hαphi hE0
    linarith [hA', hEα]
  have hiii : Real.exp (-eps) * (1 - delta - alpha)
      ≤ betaOf Ω Q phi := by
    have hEE : Real.exp (-eps) * Real.exp eps = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hX : (1 - delta - alpha) ≤ Real.exp eps * betaOf Ω Q phi := by
      linarith [hB', hαphi]
    calc Real.exp (-eps) * (1 - delta - alpha)
        ≤ Real.exp (-eps) * (Real.exp eps * betaOf Ω Q phi) :=
          mul_le_mul_left_real hX hE'0
      _ = betaOf Ω Q phi := by rw [← mul_assoc, hEE, one_mul]
  have hmax : max 0 (max (1 - delta - Real.exp eps * alpha)
      (Real.exp (-eps) * (1 - delta - alpha))) ≤ betaOf Ω Q phi :=
    max_le_real hβ0 (max_le_real hii hiii)
  exact hmax

/-! ## H3 converse: indicator tests -/

lemma sum_ite_mem_eq (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (S : Finset Ω) (c : Ω → ℝ) :
    ∑ w, (if w ∈ S then c w else 0) = ∑ w ∈ S, c w := by
  have hsplit : (∑ w ∈ S, (if w ∈ S then c w else 0))
        + (∑ w ∈ Sᶜ, (if w ∈ S then c w else 0))
      = ∑ w, (if w ∈ S then c w else 0) :=
    sum_add_compl_eq Ω (fun w => if w ∈ S then c w else 0) S
  have hS : ∑ w ∈ S, (if w ∈ S then c w else 0) = ∑ w ∈ S, c w := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    exact ite_eq_left hw
  have hSc : ∑ w ∈ Sᶜ, (if w ∈ S then c w else 0) = 0 := by
    have h0 : (∑ w ∈ Sᶜ, (if w ∈ S then c w else 0))
        = ∑ w ∈ Sᶜ, (0 : ℝ) :=
      Finset.sum_congr rfl (fun w hw => ite_eq_right (Finset.mem_compl.mp hw))
    rw [h0]
    exact sum_zero_eq Ω Sᶜ
  rw [← hsplit, hS, hSc, add_zero]

lemma sum_mul_ite_mem_eq (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (S : Finset Ω) (c : Ω → ℝ) :
    ∑ w, c w * (if w ∈ S then (1 : ℝ) else 0) = ∑ w ∈ S, c w := by
  have hpt : ∀ w : Ω, c w * (if w ∈ S then (1 : ℝ) else 0)
      = (if w ∈ S then c w else 0) := by
    intro w
    by_cases hw : w ∈ S <;> simp [hw]
  simp only [hpt]
  exact sum_ite_mem_eq Ω S c

lemma sum_mul_ite_mem_compl_eq (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (S : Finset Ω) (c : Ω → ℝ) :
    ∑ w, c w * (if w ∈ S then (0 : ℝ) else 1) = ∑ w ∈ Sᶜ, c w := by
  have hpt : ∀ w : Ω, c w * (if w ∈ S then (0 : ℝ) else 1)
      = (if w ∈ Sᶜ then c w else 0) := by
    intro w
    by_cases hw : w ∈ S
    · have hnc : w ∉ Sᶜ := fun h => (Finset.mem_compl.mp h) hw
      rw [ite_eq_left hw, ite_eq_right hnc, mul_zero]
    · have hc : w ∈ Sᶜ := Finset.mem_compl.mpr hw
      rw [ite_eq_right hw, ite_eq_left hc, mul_one]
  simp only [hpt]
  exact sum_ite_mem_eq Ω Sᶜ c

lemma alphaOf_indicator (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (P : PMF Ω) (S : Finset Ω) :
    alphaOf Ω P (fun w => if w ∈ S then (1 : ℝ) else 0)
      = typeI Ω P S := by
  have h : ∑ w, (P w).toReal * (if w ∈ S then (1 : ℝ) else 0)
      = ∑ w ∈ S, (P w).toReal :=
    sum_mul_ite_mem_eq Ω S (fun w => (P w).toReal)
  have hα : alphaOf Ω P (fun w => if w ∈ S then (1 : ℝ) else 0)
      = ∑ w, (P w).toReal * (if w ∈ S then (1 : ℝ) else 0) := rfl
  have hI : typeI Ω P S = ∑ w ∈ S, (P w).toReal := rfl
  rw [hα, hI]
  exact h

lemma betaOf_indicator (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (Q : PMF Ω) (S : Finset Ω) :
    betaOf Ω Q (fun w => if w ∈ S then (1 : ℝ) else 0)
      = typeII Ω Q S := by
  have h1 : ∀ w : Ω, (Q w).toReal * (1 - (if w ∈ S then (1 : ℝ) else 0))
      = (Q w).toReal * (if w ∈ S then (0 : ℝ) else 1) := by
    intro w
    by_cases hw : w ∈ S <;> simp [hw]
  have h2 : betaOf Ω Q (fun w => if w ∈ S then (1 : ℝ) else 0)
      = ∑ w, (Q w).toReal * (if w ∈ S then (0 : ℝ) else 1) := by
    simp only [betaOf, h1]
  have h3 : ∑ w, (Q w).toReal * (if w ∈ S then (0 : ℝ) else 1)
      = ∑ w ∈ Sᶜ, (Q w).toReal :=
    sum_mul_ite_mem_compl_eq Ω S (fun w => (Q w).toReal)
  have hII : typeII Ω Q S = ∑ w ∈ Sᶜ, (Q w).toReal := rfl
  rw [h2, h3, hII]

/-- Indicator upper bound: at level `typeI S`, the tradeoff is at most the
type-II error of `S`. -/
lemma tradeoff_indicator_upper (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (P Q : PMF Ω) (S : Finset Ω) :
    tradeoff Ω P Q (typeI Ω P S) ≤ typeII Ω Q S := by
  have htest : IsTest Ω (fun w => if w ∈ S then (1 : ℝ) else 0) := by
    intro w
    by_cases hw : w ∈ S <;> simp [hw]
  have hα : alphaOf Ω P (fun w => if w ∈ S then (1 : ℝ) else 0)
      ≤ typeI Ω P S :=
    le_of_eq (alphaOf_indicator Ω P S)
  have hI0 : 0 ≤ typeI Ω P S := typeI_nonneg Ω P S
  have hub := tradeoff_le_betaOf Ω P Q (typeI Ω P S)
    (fun w => if w ∈ S then (1 : ℝ) else 0) hI0 htest hα
  rw [betaOf_indicator Ω Q S] at hub
  exact hub

/-- H3 converse: if the f-DP lower bound holds at every level in `[0, 1]`,
then the KOV pair condition holds, via indicator tests at `alpha = P(S)`. -/
theorem kovpair_of_tradeoff_ge (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (P Q : PMF Ω) (eps delta : ℝ)
    (h : ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ 1 →
      fEpsDelta eps delta alpha ≤ tradeoff Ω P Q alpha) :
    KOVpair Ω P Q eps delta := by
  rw [kovpair_iff_event_bounds Ω P Q eps delta]
  intro S
  have hI0 : 0 ≤ typeI Ω P S := typeI_nonneg Ω P S
  have hI1 : typeI Ω P S ≤ 1 := typeI_le_one Ω P S
  have hIc0 : 0 ≤ typeI Ω P Sᶜ := typeI_nonneg Ω P Sᶜ
  have hIc1 : typeI Ω P Sᶜ ≤ 1 := typeI_le_one Ω P Sᶜ
  have hup := tradeoff_indicator_upper Ω P Q S
  have hupc := tradeoff_indicator_upper Ω P Q Sᶜ
  have hlo := h _ hI0 hI1
  have hloc := h _ hIc0 hIc1
  have hp1 : 1 - delta - Real.exp eps * typeI Ω P S
      ≤ fEpsDelta eps delta (typeI Ω P S) :=
    le_trans le_max_left_real le_max_right_real
  have hp2 : Real.exp (-eps) * (1 - delta - typeI Ω P Sᶜ)
      ≤ fEpsDelta eps delta (typeI Ω P Sᶜ) :=
    le_trans le_max_right_real le_max_right_real
  have hsplitP := pmf_sum_add_compl Ω P S
  have hsplitQ := pmf_sum_add_compl Ω Q S
  have hIIc : typeII Ω Q Sᶜ = ∑ w ∈ S, (Q w).toReal := by
    simp only [typeII, compl_compl]
  have hIQ : typeII Ω Q S = 1 - ∑ w ∈ S, (Q w).toReal := by
    simp only [typeII]
    linarith [hsplitQ]
  have hIP : typeI Ω P S = ∑ w ∈ S, (P w).toReal := rfl
  have hIcP : typeI Ω P Sᶜ = ∑ w ∈ Sᶜ, (P w).toReal := rfl
  constructor
  · have hEE : Real.exp (-eps) * Real.exp eps = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hchain : Real.exp (-eps) * (1 - delta - ∑ w ∈ Sᶜ, (P w).toReal)
        ≤ ∑ w ∈ S, (Q w).toReal := by
      rw [← hIcP, ← hIIc]
      exact le_trans hp2 (le_trans hloc hupc)
    have hpos : 0 < Real.exp eps := Real.exp_pos eps
    have hmul := mul_le_mul_left_real hchain (le_of_lt hpos)
    rw [← mul_assoc, mul_comm (Real.exp eps) (Real.exp (-eps)), hEE,
      one_mul] at hmul
    linarith [hmul, hsplitP]
  · have hchain : 1 - delta - Real.exp eps * ∑ w ∈ S, (P w).toReal
        ≤ 1 - ∑ w ∈ S, (Q w).toReal := by
      rw [← hIP, ← hIQ]
      exact le_trans hp1 (le_trans hlo hup)
    linarith [hchain]

/-! ## H4: post-processing increases the tradeoff -/

/-- Pullback of a test on post-processed outputs to a test on inputs. -/
noncomputable def pullbackTest (Ω Ω2 : Type*) [Fintype Ω] [Fintype Ω2]
    (k : Ω → PMF Ω2) (phi : Ω2 → ℝ) : Ω → ℝ :=
  fun w => ∑ y, (k w y).toReal * phi y

lemma pullbackTest_isTest (Ω Ω2 : Type*) [Fintype Ω] [Fintype Ω2]
    (k : Ω → PMF Ω2) (phi : Ω2 → ℝ) (hphi : IsTest Ω2 phi) :
    IsTest Ω (pullbackTest Ω Ω2 k phi) := by
  intro w
  show 0 ≤ (∑ y, (k w y).toReal * phi y) ∧
    (∑ y, (k w y).toReal * phi y) ≤ 1
  constructor
  · apply Finset.sum_nonneg
    intro y _
    exact mul_nonneg_real toReal_nonneg_real (hphi y).1
  · have hle : ∑ y, (k w y).toReal * phi y
        ≤ ∑ y, (k w y).toReal * 1 := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_left_real (hphi y).2 toReal_nonneg_real
    have heq : ∑ y, (k w y).toReal * 1 = 1 := by
      simp only [mul_one]
      exact pmf_toReal_sum Ω2 (k w)
    linarith [hle, heq]

/-- Real-valued form of bind on finite types. -/
lemma pmf_bind_toReal (Ω Ω2 : Type*) [Fintype Ω] [Fintype Ω2]
    (P : PMF Ω) (k : Ω → PMF Ω2) (y : Ω2) :
    ((P.bind k) y).toReal = ∑ w, (P w).toReal * (k w y).toReal := by
  have htsum : ((P.bind k) y : ℝ≥0∞)
      = tsum fun w => (P w : ℝ≥0∞) * (k w y : ℝ≥0∞) :=
    PMF.bind_apply P k y
  have hsum : ((P.bind k) y : ℝ≥0∞)
      = ∑ w, (P w : ℝ≥0∞) * (k w y : ℝ≥0∞) := by
    rw [htsum, tsum_fintype]
  have htr := congrArg ENNReal.toReal hsum
  have hpush : (∑ w, (P w : ℝ≥0∞) * (k w y : ℝ≥0∞)).toReal
      = ∑ w, (P w).toReal * (k w y).toReal := by
    have hstep : (∑ w, (P w : ℝ≥0∞) * (k w y : ℝ≥0∞)).toReal
        = ∑ w, (((P w : ℝ≥0∞) * (k w y : ℝ≥0∞))).toReal := by
      apply ENNReal.toReal_sum
      intro w _
      exact mul_ne_top_real (pmf_ne_top Ω P w) (pmf_ne_top Ω2 (k w) y)
    rw [hstep]
    have hpt : ∀ w : Ω, ((P w : ℝ≥0∞) * (k w y : ℝ≥0∞)).toReal
        = (P w).toReal * (k w y).toReal := fun w => ENNReal.toReal_mul
    simp only [hpt]
  rw [hsum]
  exact hpush

/-- The pullback test preserves type-I error. -/
lemma pullbackTest_alpha (Ω Ω2 : Type*) [Fintype Ω] [Fintype Ω2]
    (P : PMF Ω) (k : Ω → PMF Ω2) (phi : Ω2 → ℝ) :
    alphaOf Ω P (pullbackTest Ω Ω2 k phi)
      = alphaOf Ω2 (P.bind k) phi := by
  have hLHS : alphaOf Ω P (pullbackTest Ω Ω2 k phi)
      = ∑ w, ∑ y, (P w).toReal * ((k w y).toReal * phi y) := by
    have hpt : ∀ w : Ω, (P w).toReal * pullbackTest Ω Ω2 k phi w
        = ∑ y, (P w).toReal * ((k w y).toReal * phi y) := by
      intro w
      show (P w).toReal * (∑ y, (k w y).toReal * phi y) = _
      rw [Finset.mul_sum]
    simp only [alphaOf, hpt]
  have hswap : (∑ w, ∑ y, (P w).toReal * ((k w y).toReal * phi y))
      = ∑ y, ∑ w, (P w).toReal * ((k w y).toReal * phi y) :=
    Finset.sum_comm
  have hRHS : alphaOf Ω2 (P.bind k) phi
      = ∑ y, ∑ w, (P w).toReal * ((k w y).toReal * phi y) := by
    have hbind := pmf_bind_toReal Ω Ω2 P k
    have hpt : ∀ y : Ω2, ((P.bind k) y).toReal * phi y
        = ∑ w, (P w).toReal * ((k w y).toReal * phi y) := by
      intro y
      rw [hbind y]
      have hpt2 : ∀ w : Ω, (P w).toReal * ((k w y).toReal * phi y)
          = phi y * ((P w).toReal * (k w y).toReal) := fun w => by ring
      simp only [hpt2]
      rw [mul_comm]
      rw [Finset.mul_sum]
    simp only [alphaOf, hpt]
  rw [hLHS, hswap]
  exact hRHS.symm

/-- The pullback test preserves type-II error. -/
lemma pullbackTest_beta (Ω Ω2 : Type*) [Fintype Ω] [Fintype Ω2]
    (Q : PMF Ω) (k : Ω → PMF Ω2) (phi : Ω2 → ℝ) :
    betaOf Ω Q (pullbackTest Ω Ω2 k phi)
      = betaOf Ω2 (Q.bind k) phi := by
  have hone : ∀ w : Ω, 1 - pullbackTest Ω Ω2 k phi w
      = ∑ y, (k w y).toReal * (1 - phi y) := by
    intro w
    have hmass : ∑ y, (k w y).toReal = 1 := pmf_toReal_sum Ω2 (k w)
    have hpt : ∀ y : Ω2, (k w y).toReal * (1 - phi y)
        = (k w y).toReal - (k w y).toReal * phi y := fun y => by ring
    have hsum : ∑ y, (k w y).toReal * (1 - phi y)
        = 1 - ∑ y, (k w y).toReal * phi y := by
      simp only [hpt, Finset.sum_sub_distrib]
      rw [hmass]
    exact hsum.symm
  have hLHS : betaOf Ω Q (pullbackTest Ω Ω2 k phi)
      = ∑ w, ∑ y, (Q w).toReal * ((k w y).toReal * (1 - phi y)) := by
    have hpt : ∀ w : Ω, (Q w).toReal * (1 - pullbackTest Ω Ω2 k phi w)
        = ∑ y, (Q w).toReal * ((k w y).toReal * (1 - phi y)) := by
      intro w
      rw [hone w]
      rw [Finset.mul_sum]
    simp only [betaOf, hpt]
  have hswap : (∑ w, ∑ y, (Q w).toReal * ((k w y).toReal * (1 - phi y)))
      = ∑ y, ∑ w, (Q w).toReal * ((k w y).toReal * (1 - phi y)) :=
    Finset.sum_comm
  have hRHS : betaOf Ω2 (Q.bind k) phi
      = ∑ y, ∑ w, (Q w).toReal * ((k w y).toReal * (1 - phi y)) := by
    have hbind := pmf_bind_toReal Ω Ω2 Q k
    have hpt : ∀ y : Ω2, ((Q.bind k) y).toReal * (1 - phi y)
        = ∑ w, (Q w).toReal * ((k w y).toReal * (1 - phi y)) := by
      intro y
      rw [hbind y]
      have hpt2 : ∀ w : Ω, (Q w).toReal * ((k w y).toReal * (1 - phi y))
          = (1 - phi y) * ((Q w).toReal * (k w y).toReal) :=
        fun w => by ring
      simp only [hpt2]
      rw [mul_comm]
      rw [Finset.mul_sum]
    simp only [betaOf, hpt]
  rw [hLHS, hswap]
  exact hRHS.symm

/-- H4 post-processing: pushing both distributions through a channel can only
increase the tradeoff function, on `0 ≤ alpha ≤ 1`. -/
theorem tradeoff_postprocess (Ω Ω2 : Type*) [Fintype Ω] [Fintype Ω2]
    (P Q : PMF Ω) (k : Ω → PMF Ω2) (alpha : ℝ)
    (hα0 : 0 ≤ alpha) (hα1 : alpha ≤ 1) :
    tradeoff Ω P Q alpha ≤ tradeoff Ω2 (P.bind k) (Q.bind k) alpha := by
  have hne := tradeoff_set_nonempty Ω2 (P.bind k) (Q.bind k) alpha hα0
  have hbd := tradeoff_bddBelow Ω2 (P.bind k) (Q.bind k) alpha
  have hall : ∀ b ∈ { b : ℝ | ∃ phi : Ω2 → ℝ,
      IsTest Ω2 phi ∧ alphaOf Ω2 (P.bind k) phi ≤ alpha ∧
        betaOf Ω2 (Q.bind k) phi = b },
      tradeoff Ω P Q alpha ≤ b := by
    intro b hb
    simp only [Set.mem_ofPred_eq] at hb
    obtain ⟨phi, hphi, hαphi, rfl⟩ := hb
    have hpsi := pullbackTest_isTest Ω Ω2 k phi hphi
    have hαpsi : alphaOf Ω P (pullbackTest Ω Ω2 k phi) ≤ alpha := by
      rw [pullbackTest_alpha Ω Ω2 P k phi]
      exact hαphi
    have hub := tradeoff_le_betaOf Ω P Q alpha (pullbackTest Ω Ω2 k phi)
      hα0 hpsi hαpsi
    rw [pullbackTest_beta Ω Ω2 Q k phi] at hub
    exact hub
  show tradeoff Ω P Q alpha ≤ sInf { b : ℝ | ∃ phi : Ω2 → ℝ,
    IsTest Ω2 phi ∧ alphaOf Ω2 (P.bind k) phi ≤ alpha ∧
      betaOf Ω2 (Q.bind k) phi = b }
  apply le_csInf <;> assumption

/-! ## H5: the `3/4` vs `1/4` boundary pair on `Bool` -/

/-- Mass function with `P(true) = 3/4` and `P(false) = 1/4`. -/
noncomputable def fPH5 : Bool → ℝ≥0∞
  | true => ENNReal.ofReal (3/4 : ℝ)
  | false => ENNReal.ofReal (1/4 : ℝ)

/-- Mass function with `Q(true) = 1/4` and `Q(false) = 3/4`. -/
noncomputable def fQH5 : Bool → ℝ≥0∞
  | true => ENNReal.ofReal (1/4 : ℝ)
  | false => ENNReal.ofReal (3/4 : ℝ)

/-- The `P` distribution of the boundary pair. -/
noncomputable def PH5 : PMF Bool :=
  ⟨fPH5, by
    suffices h1 : (∑ x, fPH5 x) = 1 by exact h1 ▸ hasSum_fintype fPH5
    have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
    rw [huniv]
    have hstep : (∑ x ∈ ({false, true} : Finset Bool), fPH5 x)
        = fPH5 false + (∑ x ∈ ({true} : Finset Bool), fPH5 x) :=
      Finset.sum_insert (by decide)
    rw [hstep, Finset.sum_singleton fPH5 true]
    show ENNReal.ofReal (1/4 : ℝ) + ENNReal.ofReal (3/4 : ℝ) = 1
    have h14a : (0 : ℝ) ≤ 1/4 := by norm_num
    have h14b : (0 : ℝ) ≤ 3/4 := by norm_num
    have hadd : ENNReal.ofReal (1/4 : ℝ) + ENNReal.ofReal (3/4 : ℝ)
        = ENNReal.ofReal ((1/4 : ℝ) + 3/4) :=
      (ENNReal.ofReal_add h14a h14b).symm
    rw [hadd]
    have h14 : (1/4 : ℝ) + 3/4 = 1 := by norm_num
    rw [h14]
    exact ENNReal.ofReal_one⟩

/-- The `Q` distribution of the boundary pair. -/
noncomputable def QH5 : PMF Bool :=
  ⟨fQH5, by
    suffices h1 : (∑ x, fQH5 x) = 1 by exact h1 ▸ hasSum_fintype fQH5
    have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
    rw [huniv]
    have hstep : (∑ x ∈ ({false, true} : Finset Bool), fQH5 x)
        = fQH5 false + (∑ x ∈ ({true} : Finset Bool), fQH5 x) :=
      Finset.sum_insert (by decide)
    rw [hstep, Finset.sum_singleton fQH5 true]
    show ENNReal.ofReal (3/4 : ℝ) + ENNReal.ofReal (1/4 : ℝ) = 1
    have h34a : (0 : ℝ) ≤ 3/4 := by norm_num
    have h34b : (0 : ℝ) ≤ 1/4 := by norm_num
    have hadd : ENNReal.ofReal (3/4 : ℝ) + ENNReal.ofReal (1/4 : ℝ)
        = ENNReal.ofReal ((3/4 : ℝ) + 1/4) :=
      (ENNReal.ofReal_add h34a h34b).symm
    rw [hadd]
    have h34 : (3/4 : ℝ) + 1/4 = 1 := by norm_num
    rw [h34]
    exact ENNReal.ofReal_one⟩

lemma PH5_true : (PH5 true).toReal = 3/4 := by
  have hval : ((PH5 true : ℝ≥0∞)) = ENNReal.ofReal (3/4 : ℝ) := rfl
  rw [hval]
  have hnn : (0 : ℝ) ≤ 3/4 := by norm_num
  exact toReal_ofReal_eq hnn

lemma PH5_false : (PH5 false).toReal = 1/4 := by
  have hval : ((PH5 false : ℝ≥0∞)) = ENNReal.ofReal (1/4 : ℝ) := rfl
  rw [hval]
  have hnn : (0 : ℝ) ≤ 1/4 := by norm_num
  exact toReal_ofReal_eq hnn

lemma QH5_true : (QH5 true).toReal = 1/4 := by
  have hval : ((QH5 true : ℝ≥0∞)) = ENNReal.ofReal (1/4 : ℝ) := rfl
  rw [hval]
  have hnn : (0 : ℝ) ≤ 1/4 := by norm_num
  exact toReal_ofReal_eq hnn

lemma QH5_false : (QH5 false).toReal = 3/4 := by
  have hval : ((QH5 false : ℝ≥0∞)) = ENNReal.ofReal (3/4 : ℝ) := rfl
  rw [hval]
  have hnn : (0 : ℝ) ≤ 3/4 := by norm_num
  exact toReal_ofReal_eq hnn

/-- Full support of `PH5`. -/
lemma PH5_pos (w : Bool) : 0 < (PH5 w).toReal := by
  fin_cases w
  · rw [PH5_true]
    norm_num
  · rw [PH5_false]
    norm_num

/-- Type-I error of the boundary test `S = {false}`. -/
lemma typeI_PH5_singleton_false : typeI Bool PH5 {false} = 1/4 := by
  simp only [typeI, sum_singleton_eq, PH5_false]

/-- Type-II error of the boundary test `S = {false}`. -/
lemma typeII_PH5_singleton_false : typeII Bool QH5 {false} = 1/4 := by
  have hc : ({false} : Finset Bool)ᶜ = {true} := by decide
  simp only [typeII, hc, sum_singleton_eq, QH5_true]

/-- The boundary pair satisfies the KOV condition at `eps = log 3`,
`delta = 0`. -/
theorem kovpair_PH5_QH5 : KOVpair Bool PH5 QH5 (Real.log 3) 0 := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hexp : Real.exp (Real.log 3) = 3 := exp_log_three h3
  have hS : ∀ S : Finset Bool,
      S = ∅ ∨ S = {true} ∨ S = {false} ∨ S = Finset.univ := by decide
  intro S
  rcases hS S with rfl | rfl | rfl | rfl
  · have hI : typeI Bool PH5 ∅ = 0 := by
      simp only [typeI, sum_empty_eq]
    have hII : typeII Bool QH5 ∅ = 1 := by
      have hc : (∅ : Finset Bool)ᶜ = Finset.univ := by decide
      simp only [typeII, hc]
      exact pmf_toReal_sum Bool QH5
    rw [hI, hII, hexp]
    constructor <;> norm_num
  · have hI : typeI Bool PH5 {true} = 3/4 := by
      simp only [typeI, sum_singleton_eq, PH5_true]
    have hII : typeII Bool QH5 {true} = 3/4 := by
      have hc : ({true} : Finset Bool)ᶜ = {false} := by decide
      simp only [typeII, hc, sum_singleton_eq, QH5_false]
    rw [hI, hII, hexp]
    constructor <;> norm_num
  · rw [typeI_PH5_singleton_false, typeII_PH5_singleton_false, hexp]
    constructor <;> norm_num
  · have hI : typeI Bool PH5 Finset.univ = 1 := by
      simp only [typeI]
      exact pmf_toReal_sum Bool PH5
    have hII : typeII Bool QH5 Finset.univ = 0 := by
      have hc : (Finset.univ : Finset Bool)ᶜ = ∅ := by decide
      simp only [typeII, hc, sum_empty_eq]
    rw [hI, hII, hexp]
    constructor <;> norm_num

/-- H5 boundary value: the tradeoff of the pair at `alpha = 1/4` is `1/4`,
by the H3 lower bound and the indicator upper bound at `S = {false}`. -/
theorem tradeoff_PH5_QH5_quarter : tradeoff Bool PH5 QH5 (1/4 : ℝ) = 1/4 := by
  apply le_antisymm
  · have hub := tradeoff_indicator_upper Bool PH5 QH5 {false}
    rw [typeI_PH5_singleton_false, typeII_PH5_singleton_false] at hub
    exact hub
  · have hlow := kovpair_forward_tradeoff_ge Bool PH5 QH5 (Real.log 3) 0
      (1/4) kovpair_PH5_QH5 (by norm_num) (by norm_num)
    have hf : fEpsDelta (Real.log 3) 0 (1/4 : ℝ) = 1/4 := by
      have h3 : (0 : ℝ) < 3 := by norm_num
      have hexp : Real.exp (Real.log 3) = 3 := exp_log_three h3
      have hexpneg : Real.exp (-Real.log 3) = 1/3 := by
        have hEE : Real.exp (-Real.log 3) * Real.exp (Real.log 3) = 1 := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
        rw [hexp] at hEE
        linarith [hEE]
      have e1 : (1 - (0 : ℝ) - 3 * (1/4)) = 1/4 := by norm_num
      have e2 : ((1/3 : ℝ) * (1 - 0 - 1/4)) = 1/4 := by norm_num
      have hmax : max (1/4 : ℝ) (1/4 : ℝ) = 1/4 := by
        apply le_antisymm
        · exact max_le_real (le_refl _) (le_refl _)
        · exact le_max_left_real
      show max 0 (max (1 - 0 - Real.exp (Real.log 3) * (1/4))
        (Real.exp (-Real.log 3) * (1 - 0 - 1/4))) = 1/4
      rw [hexp, hexpneg, e1, e2, hmax]
      have h01 : (0 : ℝ) ≤ 1/4 := by norm_num
      exact max_eq_right_real h01
    calc (1/4 : ℝ) = fEpsDelta (Real.log 3) 0 (1/4 : ℝ) := hf.symm
      _ ≤ tradeoff Bool PH5 QH5 (1/4 : ℝ) := hlow

/-! ## Four-outcome randomized response

Finite sharpness by an explicit construction: a pair on `Fin 4` whose
tradeoff (Dong-Roth-Su Definition 2.1) meets `fEpsDelta` on `[0, 1]`,
hence lies below every pair satisfying `KOVpair`
(Kairouz-Oh-Viswanath Theorem 2.1 Eq. 1) by Proposition 2.5.
-/

/-- Shared mass scale for the four-outcome construction. -/
noncomputable def rrC (eps delta : ℝ) : ℝ := (1 - delta) / (1 + Real.exp eps)

/-- Masses under the first hypothesis. -/
noncomputable def rrMass0 (eps delta : ℝ) : Fin 4 → ℝ := ![delta, Real.exp eps * rrC eps delta, rrC eps delta, 0]

/-- Masses under the second hypothesis. -/
noncomputable def rrMass1 (eps delta : ℝ) : Fin 4 → ℝ := ![0, rrC eps delta, Real.exp eps * rrC eps delta, delta]

lemma rrC_nonneg (eps delta : ℝ) (hδ1 : delta ≤ 1) : 0 ≤ rrC eps delta := by
  unfold rrC
  apply div_nonneg
  · linarith
  · have hE : 0 ≤ Real.exp eps := (Real.exp_pos eps).le
    linarith

lemma rrC_pos (eps delta : ℝ) (hδ1 : delta < 1) : 0 < rrC eps delta := by
  unfold rrC
  apply div_pos
  · linarith
  · have hE : 0 ≤ Real.exp eps := (Real.exp_pos eps).le
    linarith

lemma rrC_add_exp_mul (eps delta : ℝ) :
    rrC eps delta + Real.exp eps * rrC eps delta = 1 - delta := by
  unfold rrC
  have hE : 0 < 1 + Real.exp eps := by
    have h := Real.exp_pos eps
    linarith
  have hne : (1 + Real.exp eps) ≠ 0 := ne_of_gt hE
  field_simp

lemma rrMass0_nonneg (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1)
    (i : Fin 4) : 0 ≤ rrMass0 eps delta i := by
  have hC := rrC_nonneg eps delta hδ1
  have hE : 0 ≤ Real.exp eps := (Real.exp_pos eps).le
  fin_cases i
  · show 0 ≤ rrMass0 eps delta 0
    simp only [rrMass0]
    show 0 ≤ delta
    exact hδ0
  · show 0 ≤ rrMass0 eps delta 1
    simp only [rrMass0]
    show 0 ≤ Real.exp eps * rrC eps delta
    exact mul_nonneg hE hC
  · show 0 ≤ rrMass0 eps delta 2
    simp only [rrMass0]
    show 0 ≤ rrC eps delta
    exact hC
  · show 0 ≤ rrMass0 eps delta 3
    simp only [rrMass0]
    show (0 : ℝ) ≤ 0
    exact le_refl 0

lemma rrMass1_nonneg (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1)
    (i : Fin 4) : 0 ≤ rrMass1 eps delta i := by
  have hC := rrC_nonneg eps delta hδ1
  have hE : 0 ≤ Real.exp eps := (Real.exp_pos eps).le
  fin_cases i
  · show 0 ≤ rrMass1 eps delta 0
    simp only [rrMass1]
    show (0 : ℝ) ≤ 0
    exact le_refl 0
  · show 0 ≤ rrMass1 eps delta 1
    simp only [rrMass1]
    show 0 ≤ rrC eps delta
    exact hC
  · show 0 ≤ rrMass1 eps delta 2
    simp only [rrMass1]
    show 0 ≤ Real.exp eps * rrC eps delta
    exact mul_nonneg hE hC
  · show 0 ≤ rrMass1 eps delta 3
    simp only [rrMass1]
    show 0 ≤ delta
    exact hδ0

lemma rrMass0_sum (eps delta : ℝ) : ∑ i, rrMass0 eps delta i = 1 := by
  rw [Fin.sum_univ_four]
  simp only [rrMass0]
  have hadd := rrC_add_exp_mul eps delta
  have e0 : (![delta, Real.exp eps * rrC eps delta, rrC eps delta, 0] : Fin 4 → ℝ) 0 = delta := rfl
  have e1 : (![delta, Real.exp eps * rrC eps delta, rrC eps delta, 0] : Fin 4 → ℝ) 1 = Real.exp eps * rrC eps delta := by simp
  have e2 : (![delta, Real.exp eps * rrC eps delta, rrC eps delta, 0] : Fin 4 → ℝ) 2 = rrC eps delta := by simp
  have e3 : (![delta, Real.exp eps * rrC eps delta, rrC eps delta, 0] : Fin 4 → ℝ) 3 = 0 := by simp
  rw [e0, e1, e2, e3]
  linarith

lemma rrMass1_sum (eps delta : ℝ) : ∑ i, rrMass1 eps delta i = 1 := by
  rw [Fin.sum_univ_four]
  simp only [rrMass1]
  have hadd := rrC_add_exp_mul eps delta
  have e0 : (![0, rrC eps delta, Real.exp eps * rrC eps delta, delta] : Fin 4 → ℝ) 0 = 0 := rfl
  have e1 : (![0, rrC eps delta, Real.exp eps * rrC eps delta, delta] : Fin 4 → ℝ) 1 = rrC eps delta := by simp
  have e2 : (![0, rrC eps delta, Real.exp eps * rrC eps delta, delta] : Fin 4 → ℝ) 2 = Real.exp eps * rrC eps delta := by simp
  have e3 : (![0, rrC eps delta, Real.exp eps * rrC eps delta, delta] : Fin 4 → ℝ) 3 = delta := by simp
  rw [e0, e1, e2, e3]
  linarith

/-- First distribution of the four-outcome construction. -/
noncomputable def rrR0 (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) :
    PMF (Fin 4) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (rrMass0 eps delta i)) (by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ rrMass0 eps delta i :=
      fun i _ => rrMass0_nonneg eps delta hδ0 hδ1 i
    have hsum : ∑ i, rrMass0 eps delta i = 1 := rrMass0_sum eps delta
    have h := ENNReal.ofReal_sum_of_nonneg hnn
    simpa [hsum] using h.symm)

/-- Second distribution of the four-outcome construction. -/
noncomputable def rrR1 (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) :
    PMF (Fin 4) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (rrMass1 eps delta i)) (by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ rrMass1 eps delta i :=
      fun i _ => rrMass1_nonneg eps delta hδ0 hδ1 i
    have hsum : ∑ i, rrMass1 eps delta i = 1 := rrMass1_sum eps delta
    have h := ENNReal.ofReal_sum_of_nonneg hnn
    simpa [hsum] using h.symm)

lemma rrR0_toReal (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1)
    (i : Fin 4) :
    ((rrR0 eps delta hδ0 hδ1) i).toReal = rrMass0 eps delta i := by
  have h : (rrR0 eps delta hδ0 hδ1) i
      = ENNReal.ofReal (rrMass0 eps delta i) := rfl
  rw [h]
  exact ENNReal.toReal_ofReal (rrMass0_nonneg eps delta hδ0 hδ1 i)

lemma rrR1_toReal (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1)
    (i : Fin 4) :
    ((rrR1 eps delta hδ0 hδ1) i).toReal = rrMass1 eps delta i := by
  have h : (rrR1 eps delta hδ0 hδ1) i
      = ENNReal.ofReal (rrMass1 eps delta i) := rfl
  rw [h]
  exact ENNReal.toReal_ofReal (rrMass1_nonneg eps delta hδ0 hδ1 i)

lemma rrR0_toReal_zero (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) :
    ((rrR0 eps delta hδ0 hδ1) 0).toReal = delta := by
  rw [rrR0_toReal]
  rfl

lemma rrR0_toReal_one (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) :
    ((rrR0 eps delta hδ0 hδ1) 1).toReal
      = Real.exp eps * rrC eps delta := by
  rw [rrR0_toReal]
  simp [rrMass0]

lemma rrR0_toReal_two (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) :
    ((rrR0 eps delta hδ0 hδ1) 2).toReal = rrC eps delta := by
  rw [rrR0_toReal]
  simp [rrMass0]

lemma rrR0_toReal_three (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) :
    ((rrR0 eps delta hδ0 hδ1) 3).toReal = 0 := by
  rw [rrR0_toReal]
  simp [rrMass0]

lemma rrR1_toReal_zero (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) :
    ((rrR1 eps delta hδ0 hδ1) 0).toReal = 0 := by
  rw [rrR1_toReal]
  rfl

lemma rrR1_toReal_one (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) :
    ((rrR1 eps delta hδ0 hδ1) 1).toReal = rrC eps delta := by
  rw [rrR1_toReal]
  simp [rrMass1]

lemma rrR1_toReal_two (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) :
    ((rrR1 eps delta hδ0 hδ1) 2).toReal
      = Real.exp eps * rrC eps delta := by
  rw [rrR1_toReal]
  simp [rrMass1]

lemma rrR1_toReal_three (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) :
    ((rrR1 eps delta hδ0 hδ1) 3).toReal = delta := by
  rw [rrR1_toReal]
  simp [rrMass1]

/-- Event bounds from a total positive-part bound. -/
lemma sum_le_mul_sum_add_of_posPart (Ω : Type*) [Fintype Ω]
    (p q : Ω → ℝ) (c delta : ℝ)
    (h : ∑ w, (p w - c * q w)⁺ ≤ delta) (S : Finset Ω) :
    (∑ w ∈ S, p w) ≤ c * (∑ w ∈ S, q w) + delta := by
  have h1 : ∑ w ∈ S, (p w - c * q w) ≤ ∑ w ∈ S, (p w - c * q w)⁺ :=
    Finset.sum_le_sum fun w _ => le_posPart _
  have h2 : ∑ w ∈ S, (p w - c * q w)⁺ ≤ ∑ w, (p w - c * q w)⁺ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      fun w _ _ => posPart_nonneg _
  have h3 : ∑ w ∈ S, (p w - c * q w) ≤ delta := le_trans (le_trans h1 h2) h
  have hexpand : ∑ w ∈ S, (p w - c * q w)
      = (∑ w ∈ S, p w) - c * (∑ w ∈ S, q w) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
  linarith [h3, hexpand]

lemma rr_c_sub_le (eps delta : ℝ) (hε : 0 ≤ eps) (hδ1 : delta ≤ 1) :
    rrC eps delta - Real.exp eps * (Real.exp eps * rrC eps delta) ≤ 0 := by
  have hC0 := rrC_nonneg eps delta hδ1
  have hE1 : (1 : ℝ) ≤ Real.exp eps := Real.one_le_exp hε
  have hEE : (1 : ℝ) ≤ Real.exp eps * Real.exp eps := by
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ Real.exp eps * Real.exp eps :=
        mul_le_mul hE1 hE1 zero_le_one (le_trans zero_le_one hE1)
  have heq : rrC eps delta - Real.exp eps * (Real.exp eps * rrC eps delta)
      = rrC eps delta * (1 - Real.exp eps * Real.exp eps) := by ring
  rw [heq]
  exact mul_nonpos_of_nonneg_of_nonpos hC0 (by linarith [hEE])

lemma rr_posPart_sum_01 (eps delta : ℝ) (hε : 0 ≤ eps)
    (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) :
    ∑ i, (rrMass0 eps delta i - Real.exp eps * rrMass1 eps delta i)⁺
      = delta := by
  rw [Fin.sum_univ_four]
  have hE0 : 0 ≤ Real.exp eps := (Real.exp_pos eps).le
  have e0 : rrMass0 eps delta 0 - Real.exp eps * rrMass1 eps delta 0
      = delta := by simp [rrMass0, rrMass1]
  have h0 : (rrMass0 eps delta 0 - Real.exp eps * rrMass1 eps delta 0)⁺
      = delta := by rw [e0, posPart_of_nonneg hδ0]
  have e1 : rrMass0 eps delta 1 - Real.exp eps * rrMass1 eps delta 1
      = 0 := by simp [rrMass0, rrMass1]
  have h1 : (rrMass0 eps delta 1 - Real.exp eps * rrMass1 eps delta 1)⁺
      = 0 := by rw [e1]; exact posPart_of_nonpos le_rfl
  have e2 : rrMass0 eps delta 2 - Real.exp eps * rrMass1 eps delta 2
      = rrC eps delta - Real.exp eps * (Real.exp eps * rrC eps delta) := by
    simp [rrMass0, rrMass1]
  have h2 : (rrMass0 eps delta 2 - Real.exp eps * rrMass1 eps delta 2)⁺
      = 0 := by
    rw [e2]
    exact posPart_of_nonpos (rr_c_sub_le eps delta hε hδ1)
  have e3 : rrMass0 eps delta 3 - Real.exp eps * rrMass1 eps delta 3
      = 0 - Real.exp eps * delta := by simp [rrMass0, rrMass1]
  have h3 : (rrMass0 eps delta 3 - Real.exp eps * rrMass1 eps delta 3)⁺
      = 0 := by
    rw [e3]
    apply posPart_of_nonpos
    have hED : 0 ≤ Real.exp eps * delta := mul_nonneg hE0 hδ0
    linarith
  rw [h0, h1, h2, h3]
  simp

lemma rr_posPart_sum_10 (eps delta : ℝ) (hε : 0 ≤ eps)
    (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) :
    ∑ i, (rrMass1 eps delta i - Real.exp eps * rrMass0 eps delta i)⁺
      = delta := by
  rw [Fin.sum_univ_four]
  have hE0 : 0 ≤ Real.exp eps := (Real.exp_pos eps).le
  have e0 : rrMass1 eps delta 0 - Real.exp eps * rrMass0 eps delta 0
      = 0 - Real.exp eps * delta := by simp [rrMass0, rrMass1]
  have h0 : (rrMass1 eps delta 0 - Real.exp eps * rrMass0 eps delta 0)⁺
      = 0 := by
    rw [e0]
    apply posPart_of_nonpos
    have hED : 0 ≤ Real.exp eps * delta := mul_nonneg hE0 hδ0
    linarith
  have e1 : rrMass1 eps delta 1 - Real.exp eps * rrMass0 eps delta 1
      = rrC eps delta - Real.exp eps * (Real.exp eps * rrC eps delta) := by
    simp [rrMass0, rrMass1]
  have h1 : (rrMass1 eps delta 1 - Real.exp eps * rrMass0 eps delta 1)⁺
      = 0 := by
    rw [e1]
    exact posPart_of_nonpos (rr_c_sub_le eps delta hε hδ1)
  have e2 : rrMass1 eps delta 2 - Real.exp eps * rrMass0 eps delta 2
      = 0 := by simp [rrMass0, rrMass1]
  have h2 : (rrMass1 eps delta 2 - Real.exp eps * rrMass0 eps delta 2)⁺
      = 0 := by rw [e2]; exact posPart_of_nonpos le_rfl
  have e3 : rrMass1 eps delta 3 - Real.exp eps * rrMass0 eps delta 3
      = delta := by simp [rrMass0, rrMass1]
  have h3 : (rrMass1 eps delta 3 - Real.exp eps * rrMass0 eps delta 3)⁺
      = delta := by rw [e3, posPart_of_nonneg hδ0]
  rw [h0, h1, h2, h3]
  simp

theorem rr_kovpair (eps delta : ℝ) (hε : 0 ≤ eps) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) : KOVpair (Fin 4) (rrR0 eps delta hδ0 hδ1) (rrR1 eps delta hδ0 hδ1) eps delta := by
  rw [kovpair_iff_event_bounds]
  intro S
  have h01 : ∑ i, (rrMass0 eps delta i
      - Real.exp eps * rrMass1 eps delta i)⁺ ≤ delta :=
    le_of_eq (rr_posPart_sum_01 eps delta hε hδ0 hδ1)
  have h10 : ∑ i, (rrMass1 eps delta i
      - Real.exp eps * rrMass0 eps delta i)⁺ ≤ delta :=
    le_of_eq (rr_posPart_sum_10 eps delta hε hδ0 hδ1)
  have b01 := sum_le_mul_sum_add_of_posPart (Fin 4)
    (fun w => rrMass0 eps delta w) (fun w => rrMass1 eps delta w)
    (Real.exp eps) delta h01 S
  have b10 := sum_le_mul_sum_add_of_posPart (Fin 4)
    (fun w => rrMass1 eps delta w) (fun w => rrMass0 eps delta w)
    (Real.exp eps) delta h10 S
  have e0 : (∑ w ∈ S, ((rrR0 eps delta hδ0 hδ1) w).toReal)
      = ∑ w ∈ S, rrMass0 eps delta w :=
    Finset.sum_congr rfl fun w _ => rrR0_toReal eps delta hδ0 hδ1 w
  have e1 : (∑ w ∈ S, ((rrR1 eps delta hδ0 hδ1) w).toReal)
      = ∑ w ∈ S, rrMass1 eps delta w :=
    Finset.sum_congr rfl fun w _ => rrR1_toReal eps delta hδ0 hδ1 w
  rw [e0, e1]
  exact ⟨b01, b10⟩

lemma isTest_fin4 (phi : Fin 4 → ℝ)
    (h0 : 0 ≤ phi 0 ∧ phi 0 ≤ 1)
    (h1 : 0 ≤ phi 1 ∧ phi 1 ≤ 1)
    (h2 : 0 ≤ phi 2 ∧ phi 2 ≤ 1)
    (h3 : 0 ≤ phi 3 ∧ phi 3 ≤ 1) :
    IsTest (Fin 4) phi := by
  intro w
  fin_cases w
  · exact h0
  · exact h1
  · exact h2
  · exact h3

lemma rr_alphaOf_vec (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1)
    (a b c d : ℝ) :
    alphaOf (Fin 4) (rrR0 eps delta hδ0 hδ1) ![a, b, c, d]
      = delta * a + (Real.exp eps * rrC eps delta) * b
        + rrC eps delta * c + 0 * d := by
  simp only [alphaOf, Fin.sum_univ_four,
    rrR0_toReal_zero eps delta hδ0 hδ1,
    rrR0_toReal_one eps delta hδ0 hδ1,
    rrR0_toReal_two eps delta hδ0 hδ1,
    rrR0_toReal_three eps delta hδ0 hδ1]
  have p0 : (![a, b, c, d] : Fin 4 → ℝ) 0 = a := rfl
  have p1 : (![a, b, c, d] : Fin 4 → ℝ) 1 = b := by simp
  have p2 : (![a, b, c, d] : Fin 4 → ℝ) 2 = c := by simp
  have p3 : (![a, b, c, d] : Fin 4 → ℝ) 3 = d := by simp
  rw [p0, p1, p2, p3]

lemma rr_betaOf_vec (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1)
    (a b c d : ℝ) :
    betaOf (Fin 4) (rrR1 eps delta hδ0 hδ1) ![a, b, c, d]
      = 0 * (1 - a) + rrC eps delta * (1 - b)
        + (Real.exp eps * rrC eps delta) * (1 - c) + delta * (1 - d) := by
  simp only [betaOf, Fin.sum_univ_four,
    rrR1_toReal_zero eps delta hδ0 hδ1,
    rrR1_toReal_one eps delta hδ0 hδ1,
    rrR1_toReal_two eps delta hδ0 hδ1,
    rrR1_toReal_three eps delta hδ0 hδ1]
  have p0 : (![a, b, c, d] : Fin 4 → ℝ) 0 = a := rfl
  have p1 : (![a, b, c, d] : Fin 4 → ℝ) 1 = b := by simp
  have p2 : (![a, b, c, d] : Fin 4 → ℝ) 2 = c := by simp
  have p3 : (![a, b, c, d] : Fin 4 → ℝ) 3 = d := by simp
  rw [p0, p1, p2, p3]

lemma rr_regimeIII (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) :
    IsTest (Fin 4) ![0, 1, 1, 1] ∧
      alphaOf (Fin 4) (rrR0 eps delta hδ0 hδ1) ![0, 1, 1, 1] = 1 - delta ∧
      betaOf (Fin 4) (rrR1 eps delta hδ0 hδ1) ![0, 1, 1, 1] = 0 := by
  have htest : IsTest (Fin 4) (![0, 1, 1, 1] : Fin 4 → ℝ) :=
    isTest_fin4 _ (by simp) (by simp) (by simp) (by simp)
  have hadd := rrC_add_exp_mul eps delta
  have hα : alphaOf (Fin 4) (rrR0 eps delta hδ0 hδ1) ![0, 1, 1, 1]
      = 1 - delta := by
    rw [rr_alphaOf_vec]
    simp only [mul_zero, mul_one, zero_add, add_zero]
    linarith
  have hβ : betaOf (Fin 4) (rrR1 eps delta hδ0 hδ1) ![0, 1, 1, 1] = 0 := by
    rw [rr_betaOf_vec]
    simp
  exact ⟨htest, hα, hβ⟩

lemma rr_regimeI (eps delta alpha : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1)
    (hC : 0 < rrC eps delta) (hα0 : 0 ≤ alpha)
    (hαC : alpha ≤ rrC eps delta) :
    IsTest (Fin 4) ![0, 0, alpha / rrC eps delta, 1] ∧
      alphaOf (Fin 4) (rrR0 eps delta hδ0 hδ1)
        ![0, 0, alpha / rrC eps delta, 1] = alpha ∧
      betaOf (Fin 4) (rrR1 eps delta hδ0 hδ1)
        ![0, 0, alpha / rrC eps delta, 1]
        = 1 - delta - Real.exp eps * alpha := by
  have hCne : rrC eps delta ≠ 0 := ne_of_gt hC
  have hdiv0 : 0 ≤ alpha / rrC eps delta :=
    div_nonneg hα0 (le_of_lt hC)
  have hdiv1 : alpha / rrC eps delta ≤ 1 := by
    rw [div_le_one (by linarith [hC])]
    exact hαC
  have p2 : ((![0, 0, alpha / rrC eps delta, 1] : Fin 4 → ℝ)) 2
      = alpha / rrC eps delta := by simp
  have h2 : 0 ≤ ((![0, 0, alpha / rrC eps delta, 1] : Fin 4 → ℝ)) 2 ∧
      ((![0, 0, alpha / rrC eps delta, 1] : Fin 4 → ℝ)) 2 ≤ 1 := by
    rw [p2]
    exact ⟨hdiv0, hdiv1⟩
  have htest : IsTest (Fin 4) (![0, 0, alpha / rrC eps delta, 1] : Fin 4 → ℝ) :=
    isTest_fin4 _ (by simp) (by simp) h2 (by simp)
  have hadd := rrC_add_exp_mul eps delta
  have hα : alphaOf (Fin 4) (rrR0 eps delta hδ0 hδ1)
      ![0, 0, alpha / rrC eps delta, 1] = alpha := by
    rw [rr_alphaOf_vec]
    simp only [mul_zero, zero_mul, zero_add, add_zero]
    field_simp
  have hEC : (Real.exp eps * rrC eps delta) * (alpha / rrC eps delta)
      = Real.exp eps * alpha := by
    field_simp
  have hβ : betaOf (Fin 4) (rrR1 eps delta hδ0 hδ1)
      ![0, 0, alpha / rrC eps delta, 1]
      = 1 - delta - Real.exp eps * alpha := by
    rw [rr_betaOf_vec]
    simp only [sub_zero, sub_self, mul_zero, mul_one,
      zero_add, add_zero]
    have hexpand : (Real.exp eps * rrC eps delta)
        * (1 - alpha / rrC eps delta)
        = (Real.exp eps * rrC eps delta) - Real.exp eps * alpha := by
      rw [mul_sub, mul_one, hEC]
    rw [hexpand]
    linarith
  exact ⟨htest, hα, hβ⟩

lemma rr_regimeII (eps delta alpha : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1)
    (hC : 0 < rrC eps delta) (hCα : rrC eps delta < alpha)
    (hαδ : alpha ≤ 1 - delta) :
    IsTest (Fin 4) ![0, (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta), 1, 1] ∧
      alphaOf (Fin 4) (rrR0 eps delta hδ0 hδ1)
        ![0, (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta), 1, 1]
        = alpha ∧
      betaOf (Fin 4) (rrR1 eps delta hδ0 hδ1)
        ![0, (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta), 1, 1]
        = Real.exp (-eps) * (1 - delta - alpha) := by
  have hEpos : 0 < Real.exp eps := Real.exp_pos eps
  have hdenom : 0 < Real.exp eps * rrC eps delta := mul_pos hEpos hC
  have hdenom_ne : Real.exp eps * rrC eps delta ≠ 0 := ne_of_gt hdenom
  have hEne : Real.exp eps ≠ 0 := ne_of_gt hEpos
  have hnum0 : 0 ≤ alpha - rrC eps delta := le_of_lt (sub_pos.mpr hCα)
  have hdiv0 : 0 ≤ (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta) :=
    div_nonneg hnum0 (le_of_lt hdenom)
  have hadd := rrC_add_exp_mul eps delta
  have hdiv1 : (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta) ≤ 1 := by
    rw [div_le_one hdenom]
    linarith
  have p1 : ((![0, (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta), 1, 1]
      : Fin 4 → ℝ)) 1
      = (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta) := by simp
  have h1 : 0 ≤ ((![0, (alpha - rrC eps delta)
      / (Real.exp eps * rrC eps delta), 1, 1] : Fin 4 → ℝ)) 1 ∧
      ((![0, (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta), 1, 1]
        : Fin 4 → ℝ)) 1 ≤ 1 := by
    rw [p1]
    exact ⟨hdiv0, hdiv1⟩
  have htest : IsTest (Fin 4)
      (![0, (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta), 1, 1]
        : Fin 4 → ℝ) :=
    isTest_fin4 _ (by simp) h1 (by simp) (by simp)
  have hcancel : (Real.exp eps * rrC eps delta)
      * ((alpha - rrC eps delta) / (Real.exp eps * rrC eps delta))
      = alpha - rrC eps delta := by
    field_simp
  have hα : alphaOf (Fin 4) (rrR0 eps delta hδ0 hδ1)
      ![0, (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta), 1, 1]
      = alpha := by
    rw [rr_alphaOf_vec]
    simp only [mul_zero, mul_one, zero_add, add_zero]
    rw [hcancel]
    ring
  have hEE : Real.exp (-eps) * Real.exp eps = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h2 : Real.exp eps * (rrC eps delta
      * (1 - (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta)))
      = 1 - delta - alpha := by
    have heq1 : Real.exp eps * (rrC eps delta
        * (1 - (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta)))
        = (Real.exp eps * rrC eps delta)
          * (1 - (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta)) := by
      ring
    rw [heq1]
    have heq2 : (Real.exp eps * rrC eps delta)
        * (1 - (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta))
        = (Real.exp eps * rrC eps delta)
          - (Real.exp eps * rrC eps delta)
            * ((alpha - rrC eps delta) / (Real.exp eps * rrC eps delta)) := by
      rw [mul_sub, mul_one]
    rw [heq2, hcancel]
    linarith
  have h3 : Real.exp eps * (Real.exp (-eps) * (1 - delta - alpha))
      = 1 - delta - alpha := by
    have hcomm : Real.exp eps * Real.exp (-eps) = 1 := by
      rw [mul_comm]
      exact hEE
    calc Real.exp eps * (Real.exp (-eps) * (1 - delta - alpha))
        = (Real.exp eps * Real.exp (-eps)) * (1 - delta - alpha) := by ring
      _ = 1 * (1 - delta - alpha) := by rw [hcomm]
      _ = 1 - delta - alpha := one_mul _
  have hEq : Real.exp eps * (rrC eps delta
      * (1 - (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta)))
      = Real.exp eps * (Real.exp (-eps) * (1 - delta - alpha)) := by
    rw [h2, h3]
  have hcancelEq : rrC eps delta
      * (1 - (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta))
      = Real.exp (-eps) * (1 - delta - alpha) :=
    mul_left_cancel₀ hEne hEq
  have hβ : betaOf (Fin 4) (rrR1 eps delta hδ0 hδ1)
      ![0, (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta), 1, 1]
      = Real.exp (-eps) * (1 - delta - alpha) := by
    rw [rr_betaOf_vec]
    simp only [sub_zero, sub_self, mul_zero, mul_one,
      zero_add, add_zero]
    exact hcancelEq
  exact ⟨htest, hα, hβ⟩

theorem rr_tradeoff_le_fEpsDelta (eps delta alpha : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) (hα0 : 0 ≤ alpha) : tradeoff (Fin 4) (rrR0 eps delta hδ0 hδ1) (rrR1 eps delta hδ0 hδ1) alpha ≤ fEpsDelta eps delta alpha := by
  unfold fEpsDelta
  by_cases hle : 1 - delta ≤ alpha
  · obtain ⟨htest, hαeq, hβeq⟩ := rr_regimeIII eps delta hδ0 hδ1
    have hαle : alphaOf (Fin 4) (rrR0 eps delta hδ0 hδ1) ![0, 1, 1, 1]
        ≤ alpha := by rw [hαeq]; exact hle
    have hub := tradeoff_le_betaOf (Fin 4)
      (rrR0 eps delta hδ0 hδ1) (rrR1 eps delta hδ0 hδ1) alpha
      ![0, 1, 1, 1] hα0 htest hαle
    rw [hβeq] at hub
    exact le_trans hub (le_max_left _ _)
  · have hlt : alpha < 1 - delta := lt_of_not_ge hle
    have hδlt : delta < 1 := by linarith [hα0, hlt]
    have hC : 0 < rrC eps delta := rrC_pos eps delta hδlt
    by_cases hαC : alpha ≤ rrC eps delta
    · obtain ⟨htest, hαeq, hβeq⟩ :=
        rr_regimeI eps delta alpha hδ0 hδ1 hC hα0 hαC
      have hαle : alphaOf (Fin 4) (rrR0 eps delta hδ0 hδ1)
          ![0, 0, alpha / rrC eps delta, 1] ≤ alpha := le_of_eq hαeq
      have hub := tradeoff_le_betaOf (Fin 4)
        (rrR0 eps delta hδ0 hδ1) (rrR1 eps delta hδ0 hδ1) alpha
        ![0, 0, alpha / rrC eps delta, 1] hα0 htest hαle
      rw [hβeq] at hub
      have hmax : 1 - delta - Real.exp eps * alpha
          ≤ max 0 (max (1 - delta - Real.exp eps * alpha)
            (Real.exp (-eps) * (1 - delta - alpha))) :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      exact le_trans hub hmax
    · have hCα : rrC eps delta < alpha := lt_of_not_ge hαC
      have hαδ : alpha ≤ 1 - delta := le_of_lt hlt
      obtain ⟨htest, hαeq, hβeq⟩ :=
        rr_regimeII eps delta alpha hδ0 hδ1 hC hCα hαδ
      have hαle : alphaOf (Fin 4) (rrR0 eps delta hδ0 hδ1)
          ![0, (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta), 1, 1]
          ≤ alpha := le_of_eq hαeq
      have hub := tradeoff_le_betaOf (Fin 4)
        (rrR0 eps delta hδ0 hδ1) (rrR1 eps delta hδ0 hδ1) alpha
        ![0, (alpha - rrC eps delta) / (Real.exp eps * rrC eps delta), 1, 1]
        hα0 htest hαle
      rw [hβeq] at hub
      have hmax : Real.exp (-eps) * (1 - delta - alpha)
          ≤ max 0 (max (1 - delta - Real.exp eps * alpha)
            (Real.exp (-eps) * (1 - delta - alpha))) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      exact le_trans hub hmax

theorem rr_tradeoff_eq_fEpsDelta (eps delta alpha : ℝ) (hε : 0 ≤ eps) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) (hα0 : 0 ≤ alpha) (hα1 : alpha ≤ 1) : tradeoff (Fin 4) (rrR0 eps delta hδ0 hδ1) (rrR1 eps delta hδ0 hδ1) alpha = fEpsDelta eps delta alpha := by
  apply le_antisymm
  · exact rr_tradeoff_le_fEpsDelta eps delta alpha hδ0 hδ1 hα0
  · exact kovpair_forward_tradeoff_ge (Fin 4)
      (rrR0 eps delta hδ0 hδ1) (rrR1 eps delta hδ0 hδ1)
      eps delta alpha (rr_kovpair eps delta hε hδ0 hδ1) hα0 hα1

theorem rr_tradeoff_le_of_kovpair (Ω : Type*) [Fintype Ω] [DecidableEq Ω] (P Q : PMF Ω) (eps delta alpha : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) (hKov : KOVpair Ω P Q eps delta) (hα0 : 0 ≤ alpha) (hα1 : alpha ≤ 1) : tradeoff (Fin 4) (rrR0 eps delta hδ0 hδ1) (rrR1 eps delta hδ0 hδ1) alpha ≤ tradeoff Ω P Q alpha := by
  exact (rr_tradeoff_le_fEpsDelta eps delta alpha hδ0 hδ1 hα0).trans
    (kovpair_forward_tradeoff_ge Ω P Q eps delta alpha hKov hα0 hα1)

end CSLibExt.Privacy.HypothesisTesting
