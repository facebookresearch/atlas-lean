/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalBayesNet
public import CSLibExt.MachineLearning.GraphicalModels.Identifiability
public import MathlibExt.Probability.FiniteProbability
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The g-formula for time-varying treatments on finite spaces

A finite study population `Ω` with weights `p` (`0 ≤ p`, `∑ ω, p ω = 1`) is followed over the
time points `k = 0, …, K`. At time `k` a covariate `L k` is measured and then a treatment `A k`
is received; the outcome `Y` is measured after the last treatment. For a static deterministic
plan `ā = (a 0, …, a K)` each individual has a counterfactual outcome `Y^ā`. Write `L̄_k` and
`Ā_k` for the covariate and treatment histories through time `k`, both empty before time `0`.

The **g-formula** of the plan `ā` is the functional of the observed variables
`∑_{l̄} E[Y | Ā = ā, L̄ = l̄] ∏_{k=0}^{K} f(l_k | ā_{k-1}, l̄_{k-1})`
(Hernán and Robins, *What If*, §21.1: p. 272 for two time points, p. 274 for `K + 1`). Under
consistency, sequential positivity along the plan and static sequential exchangeability for
`Y^ā` (Technical Point 19.2 and §19.5) it equals the counterfactual mean `E[Y^ā]`, so this mean
is identified from the observed data.

Conditional means are totalized: `E[Z | s] = (∑_{ω ∈ s} p ω Z ω) / P(s)` is `0` on a null event
(Lean's `x / 0 = 0`). Under positivity a term of positive weight in the g-formula never meets a
null conditioning event, so the convention does not affect the identity.

## Main definitions

* `ObsModel Ω 𝓛 𝓐 K`: the observed part `(p, L, A, Y)` of a study with time points `0, …, K`;
  `POModel` adds the counterfactual outcome `Ycf ā` of every static plan `ā`.
* `cmean p Z s`: the totalized conditional mean `E[Z | s]`.
* `ObsModel.Hist`, `ObsModel.Pre`, `ObsModel.HistT`: the history events
  `{L̄_k = l̄_k, Ā_{k-1} = ā_{k-1}}`, `{L̄_{k-1} = l̄_{k-1}, Ā_{k-1} = ā_{k-1}}` and
  `{L̄_k = l̄_k, Ā_k = ā_k}`.
* `ObsModel.gFormula`: the g-formula, with factors `ObsModel.condL`.
* `ObsModel.Positive`: sequential positivity along the plan.
* `POModel.Consistent`: consistency for the plan, almost surely.
* `POModel.SeqExch`: static sequential exchangeability for `Y^ā`, in product form;
  `POModel.MeanSeqExch`: its mean form.
* `BayesNet.toObsModel`: the observed part of a Bayesian network whose nodes are, in
  topological order, `L₀, A₀, L₁, A₁, …, L_K, A_K, Y`.

## Main results

* `sum_filter_mul_eq_sum`: the step shared by both milestones: expand a conditional mean over
  the next covariate, then add the next treatment to the conditioning event.
* `expectation_Ycf_eq_two_period`: the g-formula for two time points.
* `expectation_Ycf_eq_gFormula`, `expectation_Ycf_eq_gFormula_of_mean`: the g-formula for
  `K + 1` time points, by induction on the shared step; `gFormula_one`: for `K = 1` the general
  display is the two-period one.
* `identifiedOn_expectation_Ycf`: `E[Y^ā]` is identified from the observed joint law on the class of
  models satisfying the three conditions (`IdentifiedOn`, Pearl 2009, Definition 3.2.3).
* `not_identifiedOn_without_positivity`: without positivity `E[Y^ā]` is not identified, even
  from the whole observed part, on a class that keeps consistency and exchangeability.
* `gFormula_toObsModel_eq_mutilateSet`: under positivity the g-formula of a Bayesian network on
  the time-ordered layout is the mean of the outcome under `do(Ā = ā)` given by the truncated
  factorization `BayesNet.mutilateSet`. The equality fails without positivity.

Out of scope: dynamic and random strategies, the joint law of `(Y^ā, L̄^ā)` (the g-formula
density of Technical Point 21.1), causal DAGs with latent nodes, estimation (IP weighting,
g-estimation) and continuous variables.

## References

* M. A. Hernán and J. M. Robins, *Causal Inference: What If*, Chapman & Hall/CRC (2020),
  revision of 2 January 2025: §19.4 (sequential exchangeability, pp. 253–254), Technical
  Point 19.2 (sequential positivity and consistency, p. 255), §19.5 (static sequential
  exchangeability, p. 257), §21.1 (the g-formula: p. 272 for two time points, p. 274 for
  `K + 1`) and Technical Point 21.1 (the g-formula density and the ordering of the causal DAG,
  p. 275).
* T. S. Richardson and A. Rotnitzky, *Causal etiology of the research of James M. Robins*,
  Statistical Science 29(4) (2014), §2.2, eqs. (3)–(7); arXiv:1503.02894.
* J. M. Robins, *A new approach to causal inference in mortality studies with a sustained
  exposure period*, Mathematical Modelling 7 (1986), 1393–1512, cited through Richardson and
  Rotnitzky (2014).
* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), eq. (3.10).
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels.GFormula

open Finset MathlibExt.Probability.FiniteProbability

/-- The **observed part** of a finite study with time points `0, …, K`: the weight `p ω` of each
individual `ω : Ω`, the covariate `L k` and the treatment `A k` at each time `k`, and the
outcome `Y`. Theorems assume `0 ≤ p` and `∑ ω, p ω = 1` where they use them. -/
structure ObsModel (Ω 𝓛 𝓐 : Type*) (K : ℕ) where
  /-- The weight of each individual. -/
  p : Ω → ℝ
  /-- The covariate measured at time `k`. -/
  L : Fin (K + 1) → Ω → 𝓛
  /-- The treatment received at time `k`, after the covariate `L k` is measured. -/
  A : Fin (K + 1) → Ω → 𝓐
  /-- The outcome, measured after the last treatment. -/
  Y : Ω → ℝ

/-- A finite **potential-outcome model**: the observed part of a study together with the
counterfactual outcome `Y^ā` (`Ycf ā`) of every static deterministic plan
`ā : Fin (K + 1) → 𝓐`. Counterfactual covariates are not part of the model: the identification
of `E[Y^ā]` does not use them. -/
structure POModel (Ω 𝓛 𝓐 : Type*) (K : ℕ) extends ObsModel Ω 𝓛 𝓐 K where
  /-- The counterfactual outcome `Y^ā` under the static plan `ā`. -/
  Ycf : (Fin (K + 1) → 𝓐) → Ω → ℝ

variable {Ω 𝓛 𝓐 : Type*} {K : ℕ}

/-- The totalized conditional mean `E[Z | s] = (∑_{ω ∈ s} p ω Z ω) / P(s)` of `Z` given an
event `s : Finset Ω`; it is `0` on a null event (Lean's `x / 0 = 0`). Taking the event as a
`Finset` keeps one decidability instance for the numerator and the denominator. -/
noncomputable def cmean (p : Ω → ℝ) (Z : Ω → ℝ) (s : Finset Ω) : ℝ :=
  (∑ ω ∈ s, p ω * Z ω) / prob p s

namespace ObsModel

variable (O : ObsModel Ω 𝓛 𝓐 K)

/-- The history event `{L̄_k = l̄_k, Ā_{k-1} = ā_{k-1}}`: the covariates through time `k` and
the treatments before time `k` agree with `l` and `a`. Indices beyond `K` saturate. -/
def Hist (k : ℕ) (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) : Ω → Prop := fun ω =>
  (∀ j : Fin (K + 1), j.val ≤ k → O.L j ω = l j) ∧ ∀ j : Fin (K + 1), j.val < k → O.A j ω = a j

/-- The history event `{L̄_{k-1} = l̄_{k-1}, Ā_{k-1} = ā_{k-1}}` before time `k`; for `k = 0`
it is the whole space. -/
def Pre (k : ℕ) (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) : Ω → Prop := fun ω =>
  (∀ j : Fin (K + 1), j.val < k → O.L j ω = l j) ∧ ∀ j : Fin (K + 1), j.val < k → O.A j ω = a j

/-- The history event `{L̄_k = l̄_k, Ā_k = ā_k}` after the treatment at time `k`. -/
def HistT (k : ℕ) (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) : Ω → Prop := fun ω =>
  (∀ j : Fin (K + 1), j.val ≤ k → O.L j ω = l j) ∧ ∀ j : Fin (K + 1), j.val ≤ k → O.A j ω = a j

@[simp] theorem hist_iff (k : ℕ) (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) (ω : Ω) :
    O.Hist k l a ω ↔ (∀ j : Fin (K + 1), j.val ≤ k → O.L j ω = l j) ∧
      ∀ j : Fin (K + 1), j.val < k → O.A j ω = a j :=
  Iff.rfl

@[simp] theorem pre_iff (k : ℕ) (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) (ω : Ω) :
    O.Pre k l a ω ↔ (∀ j : Fin (K + 1), j.val < k → O.L j ω = l j) ∧
      ∀ j : Fin (K + 1), j.val < k → O.A j ω = a j :=
  Iff.rfl

@[simp] theorem histT_iff (k : ℕ) (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) (ω : Ω) :
    O.HistT k l a ω ↔ (∀ j : Fin (K + 1), j.val ≤ k → O.L j ω = l j) ∧
      ∀ j : Fin (K + 1), j.val ≤ k → O.A j ω = a j :=
  Iff.rfl

open Classical in
/-- The factor `f(l_k | ā_{k-1}, l̄_{k-1})` of the g-formula, the totalized conditional
probability `P(L̄_k = l̄_k, Ā_{k-1} = ā_{k-1}) / P(L̄_{k-1} = l̄_{k-1}, Ā_{k-1} = ā_{k-1})`. -/
noncomputable def condL [Fintype Ω] (a : Fin (K + 1) → 𝓐) (l : Fin (K + 1) → 𝓛) (k : ℕ) : ℝ :=
  prob O.p (univ.filter (O.Hist k l a)) / prob O.p (univ.filter (O.Pre k l a))

open Classical in
/-- **The g-formula** of the static plan `ā` (Hernán and Robins, *What If*, §21.1, p. 274;
p. 272 for two time points):
`∑_{l̄} E[Y | L̄ = l̄, Ā = ā] ∏_{k=0}^{K} f(l_k | ā_{k-1}, l̄_{k-1})`, summed over all covariate
histories `l̄ : Fin (K + 1) → 𝓛`. The conditionals are totalized (`cmean`, `condL`) instead of
requiring them to be well defined. -/
noncomputable def gFormula [Fintype Ω] [Fintype 𝓛] (a : Fin (K + 1) → 𝓐) : ℝ :=
  ∑ l : Fin (K + 1) → 𝓛,
    cmean O.p O.Y (univ.filter (O.HistT K l a)) * ∏ k : Fin (K + 1), O.condL a l k

open Classical in
/-- **Sequential positivity along the static plan `ā`** (Hernán and Robins, *What If*,
Technical Point 19.2, p. 255, required only for histories compatible with the plan): every
history `{L̄_k = l̄_k, Ā_{k-1} = ā_{k-1}}` of nonzero probability keeps nonzero probability when
`A_k = a_k` is added. -/
def Positive [Fintype Ω] (a : Fin (K + 1) → 𝓐) : Prop :=
  ∀ (k : Fin (K + 1)) (l : Fin (K + 1) → 𝓛),
    prob O.p (univ.filter (O.Hist k l a)) ≠ 0 → prob O.p (univ.filter (O.HistT k l a)) ≠ 0

end ObsModel

namespace POModel

variable (M : POModel Ω 𝓛 𝓐 K)

/-- **Consistency for the static plan `ā`**, almost surely (Hernán and Robins, *What If*,
Technical Point 19.2, p. 255, the weak form sufficient for static strategies): an individual of
nonzero weight whose treatments follow the plan has `Y^ā = Y`. A model whose observed outcome
is defined by `Y ω = Y^{Ā ω} ω` satisfies it for every plan. -/
def Consistent (a : Fin (K + 1) → 𝓐) : Prop :=
  ∀ ω, M.p ω ≠ 0 → (∀ k, M.A k ω = a k) → M.Ycf a ω = M.Y ω

open Classical in
/-- **Static sequential exchangeability for `Y^ā`** (Hernán and Robins, *What If*, §19.5,
p. 257): `Y^ā ⫫ A_k | Ā_{k-1} = ā_{k-1}, L̄_k` for `k = 0, …, K`, in product form on every
history cell, so that cells of probability `0` need no case split. It is weaker than
sequential exchangeability for all strategies (§19.4, p. 254). -/
def SeqExch [Fintype Ω] (a : Fin (K + 1) → 𝓐) : Prop :=
  ∀ (k : Fin (K + 1)) (l : Fin (K + 1) → 𝓛) (y : ℝ) (b : 𝓐),
    prob M.p (univ.filter fun ω => M.Hist k l a ω ∧ M.Ycf a ω = y ∧ M.A k ω = b) *
        prob M.p (univ.filter (M.Hist k l a)) =
      prob M.p (univ.filter fun ω => M.Hist k l a ω ∧ M.Ycf a ω = y) *
        prob M.p (univ.filter fun ω => M.Hist k l a ω ∧ M.A k ω = b)

open Classical in
/-- The mean form of static sequential exchangeability: on every history cell where the planned
treatment `a_k` has nonzero probability, adding `A_k = a_k` to the conditioning event does not
change the conditional mean of `Y^ā`. It follows from `SeqExch` for nonnegative weights
(`SeqExch.meanSeqExch`) and is the form that the proofs use. -/
def MeanSeqExch [Fintype Ω] (a : Fin (K + 1) → 𝓐) : Prop :=
  ∀ (k : Fin (K + 1)) (l : Fin (K + 1) → 𝓛),
    prob M.p (univ.filter (M.HistT k l a)) ≠ 0 →
      cmean M.p (M.Ycf a) (univ.filter (M.HistT k l a)) =
        cmean M.p (M.Ycf a) (univ.filter (M.Hist k l a))

end POModel

/-! ### The shared step and the two milestones -/

open Classical in
/-- **The step shared by both milestones.** Let `p` be nonnegative weights, `E` an event, `X` a
covariate, `T` a treatment with planned value `a`, and `Z` a random variable. If every fiber
`E ∩ {X = l}` of nonzero probability keeps nonzero probability when `T = a` is added, and on
such fibers adding `T = a` does not change the conditional mean of `Z`, then
`∑_{ω ∈ E} p ω Z ω = ∑_l P(E ∩ {X = l}) E[Z | E ∩ {X = l, T = a}]`. -/
theorem sum_filter_mul_eq_sum [Fintype Ω] [Fintype 𝓛] {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω)
    (E : Ω → Prop) (X : Ω → 𝓛) (T : Ω → 𝓐) (a : 𝓐) (Z : Ω → ℝ)
    (hpos : ∀ l, prob p (univ.filter fun ω => E ω ∧ X ω = l) ≠ 0 →
      prob p (univ.filter fun ω => E ω ∧ X ω = l ∧ T ω = a) ≠ 0)
    (hexch : ∀ l, prob p (univ.filter fun ω => E ω ∧ X ω = l ∧ T ω = a) ≠ 0 →
      cmean p Z (univ.filter fun ω => E ω ∧ X ω = l ∧ T ω = a) =
        cmean p Z (univ.filter fun ω => E ω ∧ X ω = l)) :
    ∑ ω ∈ univ.filter E, p ω * Z ω =
      ∑ l, prob p (univ.filter fun ω => E ω ∧ X ω = l) *
        cmean p Z (univ.filter fun ω => E ω ∧ X ω = l ∧ T ω = a) := by
  rw [← Finset.sum_fiberwise (univ.filter E) X (fun ω => p ω * Z ω)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.filter_filter]
  by_cases h0 : prob p (univ.filter fun ω => E ω ∧ X ω = l) = 0
  · have hz : ∀ ω ∈ univ.filter (fun ω => E ω ∧ X ω = l), p ω = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun ω _ => hp ω).1 h0
    rw [h0, zero_mul]
    exact Finset.sum_eq_zero fun ω hω => by rw [hz ω hω, zero_mul]
  · rw [hexch l (hpos l h0)]
    unfold cmean
    rw [mul_div_assoc', mul_div_cancel_left₀ _ h0]

private theorem gf_aux_histT_iff {Ω 𝓛 𝓐 : Type*} {K : ℕ} [Fintype Ω] (M : POModel Ω 𝓛 𝓐 K)
    (a : Fin (K + 1) → 𝓐) (k : Fin (K + 1)) (l : Fin (K + 1) → 𝓛) (ω : Ω) :
    M.HistT k l a ω ↔ M.Hist k l a ω ∧ M.A k ω = a k := by
  constructor
  · intro hT
    exact ⟨⟨hT.1, fun j hj => hT.2 j (le_of_lt hj)⟩, hT.2 k le_rfl⟩
  · rintro ⟨⟨hL, hA⟩, hAk⟩
    refine ⟨hL, fun j hj => ?_⟩
    by_cases hlt : j.val < k.val
    · exact hA j hlt
    · have heq : j.val = k.val := by omega
      have hjk : j = k := Fin.ext heq
      rw [hjk]
      exact hAk

private theorem gf_aux_histT_conj {Ω 𝓛 𝓐 : Type*} {K : ℕ} [Fintype Ω] (M : POModel Ω 𝓛 𝓐 K)
    (a : Fin (K + 1) → 𝓐) (k : Fin (K + 1)) (l : Fin (K + 1) → 𝓛) (y : ℝ) (ω : Ω) :
    (M.HistT k l a ω ∧ M.Ycf a ω = y) ↔
      (M.Hist k l a ω ∧ M.Ycf a ω = y ∧ M.A k ω = a k) := by
  rw [gf_aux_histT_iff M a k l ω]
  constructor
  · rintro ⟨⟨hH, hA⟩, hZ⟩
    exact ⟨hH, hZ, hA⟩
  · rintro ⟨hH, hZ, hA⟩
    exact ⟨⟨hH, hA⟩, hZ⟩

/-- Static sequential exchangeability in product form implies its mean form for nonnegative
weights: on a history cell, the mean of `Y^ā` given `A_k = a_k` is its mean on the cell, by
summing the product identity over the finitely many values of `Y^ā`. -/
theorem POModel.SeqExch.meanSeqExch [Fintype Ω] {M : POModel Ω 𝓛 𝓐 K} {a : Fin (K + 1) → 𝓐}
    (hp : ∀ ω, 0 ≤ M.p ω) (h : M.SeqExch a) : M.MeanSeqExch a := by
  classical
  intro k l hT
  have hsub : univ.filter (M.HistT k l a) ⊆ univ.filter (M.Hist k l a) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact ((gf_aux_histT_iff M a k l ω).1 hω).1
  have hTpos : 0 < prob M.p (univ.filter (M.HistT k l a)) :=
    lt_of_le_of_ne (Finset.sum_nonneg fun ω _ => hp ω) (Ne.symm hT)
  have hHpos : 0 < prob M.p (univ.filter (M.Hist k l a)) :=
    lt_of_lt_of_le hTpos (Finset.sum_le_sum_of_subset_of_nonneg hsub fun ω _ _ => hp ω)
  have hfin : Finite { y : ℝ // ∃ ω, M.Ycf a ω = y } :=
    Finite.of_surjective
      (fun ω => (⟨M.Ycf a ω, ω, rfl⟩ : { y : ℝ // ∃ ω, M.Ycf a ω = y }))
      (fun j => by
        obtain ⟨ω, hω⟩ := j.property
        exact ⟨ω, Subtype.ext hω⟩)
  letI hFT : Fintype { y : ℝ // ∃ ω, M.Ycf a ω = y } := @Fintype.ofFinite _ hfin
  letI hDE : DecidableEq { y : ℝ // ∃ ω, M.Ycf a ω = y } :=
    fun a b => Classical.propDecidable _
  set g : Ω → { y : ℝ // ∃ ω, M.Ycf a ω = y } := fun ω => ⟨M.Ycf a ω, ω, rfl⟩ with hg
  have hfibT := Finset.sum_fiberwise (univ.filter (M.HistT k l a)) g
    (fun ω => M.p ω * M.Ycf a ω)
  have hfibH := Finset.sum_fiberwise (univ.filter (M.Hist k l a)) g
    (fun ω => M.p ω * M.Ycf a ω)
  have hvalT : ∀ j : { y : ℝ // ∃ ω, M.Ycf a ω = y },
      ∑ ω ∈ (univ.filter (M.HistT k l a)).filter (fun i => g i = j), M.p ω * M.Ycf a ω
        = j.val * prob M.p (univ.filter fun ω => M.HistT k l a ω ∧ M.Ycf a ω = j.val) := by
    intro j
    have hfilter : (univ.filter (M.HistT k l a)).filter (fun i => g i = j)
        = univ.filter (fun ω => M.HistT k l a ω ∧ M.Ycf a ω = j.val) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hg]
      exact and_congr_right fun _ => Subtype.ext_iff
    rw [hfilter]
    have hc : ∀ ω ∈ univ.filter (fun ω => M.HistT k l a ω ∧ M.Ycf a ω = j.val),
        M.p ω * M.Ycf a ω = j.val * M.p ω := by
      intro ω hω
      have hy : M.Ycf a ω = j.val := (Finset.mem_filter.1 hω).2.2
      rw [hy, mul_comm]
    rw [Finset.sum_congr rfl hc, ← Finset.mul_sum]
    rfl
  have hvalH : ∀ j : { y : ℝ // ∃ ω, M.Ycf a ω = y },
      ∑ ω ∈ (univ.filter (M.Hist k l a)).filter (fun i => g i = j), M.p ω * M.Ycf a ω
        = j.val * prob M.p (univ.filter fun ω => M.Hist k l a ω ∧ M.Ycf a ω = j.val) := by
    intro j
    have hfilter : (univ.filter (M.Hist k l a)).filter (fun i => g i = j)
        = univ.filter (fun ω => M.Hist k l a ω ∧ M.Ycf a ω = j.val) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hg]
      exact and_congr_right fun _ => Subtype.ext_iff
    rw [hfilter]
    have hc : ∀ ω ∈ univ.filter (fun ω => M.Hist k l a ω ∧ M.Ycf a ω = j.val),
        M.p ω * M.Ycf a ω = j.val * M.p ω := by
      intro ω hω
      have hy : M.Ycf a ω = j.val := (Finset.mem_filter.1 hω).2.2
      rw [hy, mul_comm]
    rw [Finset.sum_congr rfl hc, ← Finset.mul_sum]
    rfl
  unfold cmean
  rw [div_eq_div_iff (ne_of_gt hTpos) (ne_of_gt hHpos), ← hfibT, ← hfibH]
  simp only [hvalT, hvalH, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcell := h k l j.val (a k)
  have eQT : (univ.filter fun ω => M.Hist k l a ω ∧ M.Ycf a ω = j.val ∧ M.A k ω = a k)
      = univ.filter fun ω => M.HistT k l a ω ∧ M.Ycf a ω = j.val := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (gf_aux_histT_conj M a k l j.val ω).symm
  have ePT : (univ.filter fun ω => M.Hist k l a ω ∧ M.A k ω = a k)
      = univ.filter (M.HistT k l a) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (gf_aux_histT_iff M a k l ω).symm
  rw [eQT, ePT] at hcell
  linear_combination j.val * hcell

private theorem gf_aux_hist0_K1 {Ω 𝓛 𝓐 : Type*} [Fintype Ω] (M : POModel Ω 𝓛 𝓐 1)
    (l : Fin (1 + 1) → 𝓛) (a : Fin (1 + 1) → 𝓐) (ω : Ω) :
    M.Hist 0 l a ω ↔ M.L 0 ω = l 0 := by
  simp only [M.hist_iff]
  constructor
  · intro h
    exact h.1 0 (by decide)
  · intro hL0
    constructor
    · intro j hj
      have hj0 : j.val = 0 := by omega
      have h0val : (0 : Fin (1 + 1)).val = 0 := by decide
      have hjk : j = 0 := Fin.ext (hj0.trans h0val.symm)
      rw [hjk]
      exact hL0
    · intro j hj
      exact absurd hj (by omega)

private theorem gf_aux_histT0_K1 {Ω 𝓛 𝓐 : Type*} [Fintype Ω] (M : POModel Ω 𝓛 𝓐 1)
    (l : Fin (1 + 1) → 𝓛) (a : Fin (1 + 1) → 𝓐) (ω : Ω) :
    M.HistT 0 l a ω ↔ M.L 0 ω = l 0 ∧ M.A 0 ω = a 0 := by
  simp only [M.histT_iff]
  constructor
  · intro h
    exact ⟨h.1 0 (by decide), h.2 0 (by decide)⟩
  · rintro ⟨hL0, hA0⟩
    constructor
    · intro j hj
      have hj0 : j.val = 0 := by omega
      have h0val : (0 : Fin (1 + 1)).val = 0 := by decide
      have hjk : j = 0 := Fin.ext (hj0.trans h0val.symm)
      rw [hjk]
      exact hL0
    · intro j hj
      have hj0 : j.val = 0 := by omega
      have h0val : (0 : Fin (1 + 1)).val = 0 := by decide
      have hjk : j = 0 := Fin.ext (hj0.trans h0val.symm)
      rw [hjk]
      exact hA0

private theorem gf_aux_hist1_K1 {Ω 𝓛 𝓐 : Type*} [Fintype Ω] (M : POModel Ω 𝓛 𝓐 1)
    (l : Fin (1 + 1) → 𝓛) (a : Fin (1 + 1) → 𝓐) (ω : Ω) :
    M.Hist 1 l a ω ↔ M.L 0 ω = l 0 ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l 1 := by
  simp only [M.hist_iff]
  constructor
  · intro h
    exact ⟨h.1 0 (by decide), h.2 0 (by decide), h.1 1 (by decide)⟩
  · rintro ⟨hL0, hA0, hL1⟩
    constructor
    · intro j hj
      have hjlt := j.isLt
      have h01 : j.val = 0 ∨ j.val = 1 := by omega
      cases h01 with
      | inl h0 =>
        have h0val : (0 : Fin (1 + 1)).val = 0 := by decide
        have hjk : j = 0 := Fin.ext (h0.trans h0val.symm)
        rw [hjk]
        exact hL0
      | inr h1 =>
        have h1val : (1 : Fin (1 + 1)).val = 1 := by decide
        have hjk : j = 1 := Fin.ext (h1.trans h1val.symm)
        rw [hjk]
        exact hL1
    · intro j hj
      have hj0 : j.val = 0 := by omega
      have h0val : (0 : Fin (1 + 1)).val = 0 := by decide
      have hjk : j = 0 := Fin.ext (hj0.trans h0val.symm)
      rw [hjk]
      exact hA0

private theorem gf_aux_histT1_K1 {Ω 𝓛 𝓐 : Type*} [Fintype Ω] (M : POModel Ω 𝓛 𝓐 1)
    (l : Fin (1 + 1) → 𝓛) (a : Fin (1 + 1) → 𝓐) (ω : Ω) :
    M.HistT 1 l a ω ↔
      M.L 0 ω = l 0 ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l 1 ∧ M.A 1 ω = a 1 := by
  simp only [M.histT_iff]
  constructor
  · intro h
    exact ⟨h.1 0 (by decide), h.2 0 (by decide), h.1 1 (by decide), h.2 1 (by decide)⟩
  · rintro ⟨hL0, hA0, hL1, hA1⟩
    constructor
    · intro j hj
      have hjlt := j.isLt
      have h01 : j.val = 0 ∨ j.val = 1 := by omega
      cases h01 with
      | inl h0 =>
        have h0val : (0 : Fin (1 + 1)).val = 0 := by decide
        have hjk : j = 0 := Fin.ext (h0.trans h0val.symm)
        rw [hjk]
        exact hL0
      | inr h1 =>
        have h1val : (1 : Fin (1 + 1)).val = 1 := by decide
        have hjk : j = 1 := Fin.ext (h1.trans h1val.symm)
        rw [hjk]
        exact hL1
    · intro j hj
      have hjlt := j.isLt
      have h01 : j.val = 0 ∨ j.val = 1 := by omega
      cases h01 with
      | inl h0 =>
        have h0val : (0 : Fin (1 + 1)).val = 0 := by decide
        have hjk : j = 0 := Fin.ext (h0.trans h0val.symm)
        rw [hjk]
        exact hA0
      | inr h1 =>
        have h1val : (1 : Fin (1 + 1)).val = 1 := by decide
        have hjk : j = 1 := Fin.ext (h1.trans h1val.symm)
        rw [hjk]
        exact hA1

/-- **Milestone 1: the g-formula for two time points** (Hernán and Robins, *What If*, §21.1,
p. 272, here with a baseline covariate `L₀`; the book's display is the case of a constant
`L₀`). Under consistency, positivity and static sequential exchangeability for the plan
`(a₀, a₁)`, `E[Y^{a₀,a₁}] = ∑_{l₀, l₁} E[Y | l₀, a₀, l₁, a₁] P(L₁ = l₁ | l₀, a₀) P(L₀ = l₀)`. -/
theorem expectation_Ycf_eq_two_period [Fintype Ω] [Fintype 𝓛] [DecidableEq 𝓛] [DecidableEq 𝓐]
    (M : POModel Ω 𝓛 𝓐 1) (a : Fin 2 → 𝓐) (hp0 : ∀ ω, 0 ≤ M.p ω) (hp1 : ∑ ω, M.p ω = 1)
    (hcons : M.Consistent a) (hpos : M.Positive a) (hexch : M.SeqExch a) :
    expectation M.p (M.Ycf a) =
      ∑ l₀ : 𝓛, ∑ l₁ : 𝓛,
        cmean M.p M.Y
            (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁ ∧ M.A 1 ω = a 1) *
          (prob M.p (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁) /
            prob M.p (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0)) *
          prob M.p (univ.filter fun ω => M.L 0 ω = l₀) := by
  classical
  have hmean : M.MeanSeqExch a := POModel.SeqExch.meanSeqExch hp0 hexch
  have hpos0 : ∀ l₀ : 𝓛, prob M.p (univ.filter fun ω => M.L 0 ω = l₀) ≠ 0 →
      prob M.p (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0) ≠ 0 := by
    intro l₀ hne
    obtain ⟨ω₀, hω₀, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hl0 : M.L 0 ω₀ = l₀ := (Finset.mem_filter.1 hω₀).2
    have eH : (univ.filter fun ω => M.L 0 ω = l₀)
        = univ.filter (M.Hist 0 (fun j => M.L j ω₀) a) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        gf_aux_hist0_K1 M (fun j => M.L j ω₀) a ω, hl0]
    have eT : (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0)
        = univ.filter (M.HistT 0 (fun j => M.L j ω₀) a) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        gf_aux_histT0_K1 M (fun j => M.L j ω₀) a ω, hl0]
    rw [eH] at hne
    rw [eT]
    exact hpos 0 (fun j => M.L j ω₀) hne
  have hexch0 : ∀ l₀ : 𝓛, prob M.p (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0) ≠ 0 →
      cmean M.p (M.Ycf a) (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0) =
      cmean M.p (M.Ycf a) (univ.filter fun ω => M.L 0 ω = l₀) := by
    intro l₀ hne
    obtain ⟨ω₀, hω₀, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hm : M.L 0 ω₀ = l₀ ∧ M.A 0 ω₀ = a 0 := (Finset.mem_filter.1 hω₀).2
    have eH : (univ.filter fun ω => M.L 0 ω = l₀)
        = univ.filter (M.Hist 0 (fun j => M.L j ω₀) a) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        gf_aux_hist0_K1 M (fun j => M.L j ω₀) a ω, hm.1]
    have eT : (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0)
        = univ.filter (M.HistT 0 (fun j => M.L j ω₀) a) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        gf_aux_histT0_K1 M (fun j => M.L j ω₀) a ω, hm.1]
    simp only [eH, eT] at hne ⊢
    exact hmean 0 (fun j => M.L j ω₀) hne
  have step1 : ∑ ω, M.p ω * M.Ycf a ω =
      ∑ l₀, prob M.p (univ.filter fun ω => M.L 0 ω = l₀) *
        cmean M.p (M.Ycf a) (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0) := by
    rw [← Finset.sum_fiberwise univ (M.L 0) (fun ω => M.p ω * M.Ycf a ω)]
    refine Finset.sum_congr rfl fun l₀ _ => ?_
    by_cases h0 : prob M.p (univ.filter fun ω => M.L 0 ω = l₀) = 0
    · have hz : ∀ ω ∈ univ.filter (fun ω => M.L 0 ω = l₀), M.p ω = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun ω _ => hp0 ω).1 h0
      rw [h0, zero_mul]
      exact Finset.sum_eq_zero fun ω hω => by rw [hz ω hω, zero_mul]
    · rw [hexch0 l₀ (hpos0 l₀ h0)]
      unfold cmean
      rw [mul_div_assoc', mul_div_cancel_left₀ _ h0]
  have hpos1 : ∀ l₀ l₁ : 𝓛,
      prob M.p (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁) ≠ 0 →
      prob M.p (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁ ∧ M.A 1 ω = a 1) ≠ 0 := by
    intro l₀ l₁ hne
    obtain ⟨ω₀, hω₀, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hm : M.L 0 ω₀ = l₀ ∧ M.A 0 ω₀ = a 0 ∧ M.L 1 ω₀ = l₁ :=
      (Finset.mem_filter.1 hω₀).2
    have eH : (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁)
        = univ.filter (M.Hist 1 (fun j => M.L j ω₀) a) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        gf_aux_hist1_K1 M (fun j => M.L j ω₀) a ω, hm.1, hm.2.2]
    have eT : (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁ ∧ M.A 1 ω = a 1)
        = univ.filter (M.HistT 1 (fun j => M.L j ω₀) a) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        gf_aux_histT1_K1 M (fun j => M.L j ω₀) a ω, hm.1, hm.2.2]
    rw [eH] at hne
    rw [eT]
    exact hpos 1 (fun j => M.L j ω₀) hne
  have hexch1 : ∀ l₀ l₁ : 𝓛,
      prob M.p (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁ ∧ M.A 1 ω = a 1) ≠ 0 →
      cmean M.p (M.Ycf a) (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁ ∧ M.A 1 ω = a 1) =
      cmean M.p (M.Ycf a) (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁) := by
    intro l₀ l₁ hne
    obtain ⟨ω₀, hω₀, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hm : M.L 0 ω₀ = l₀ ∧ M.A 0 ω₀ = a 0 ∧ M.L 1 ω₀ = l₁ ∧ M.A 1 ω₀ = a 1 :=
      (Finset.mem_filter.1 hω₀).2
    have eH : (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁)
        = univ.filter (M.Hist 1 (fun j => M.L j ω₀) a) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        gf_aux_hist1_K1 M (fun j => M.L j ω₀) a ω, hm.1, hm.2.2.1]
    have eT : (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁ ∧ M.A 1 ω = a 1)
        = univ.filter (M.HistT 1 (fun j => M.L j ω₀) a) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        gf_aux_histT1_K1 M (fun j => M.L j ω₀) a ω, hm.1, hm.2.2.1]
    simp only [eH, eT] at hne ⊢
    exact hmean 1 (fun j => M.L j ω₀) hne
  have step2 : ∀ l₀ : 𝓛, ∑ ω ∈ univ.filter (fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0), M.p ω * M.Ycf a ω
      = ∑ l₁ : 𝓛, prob M.p (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁)
        * cmean M.p (M.Ycf a) (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁ ∧ M.A 1 ω = a 1) := by
    intro l₀
    rw [← Finset.sum_fiberwise (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0) (M.L 1) (fun ω => M.p ω * M.Ycf a ω)]
    refine Finset.sum_congr rfl fun l₁ _ => ?_
    rw [Finset.filter_filter]
    have e1 : (univ.filter fun ω => (M.L 0 ω = l₀ ∧ M.A 0 ω = a 0) ∧ M.L 1 ω = l₁)
        = univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁ := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
    rw [e1]
    by_cases h0 : prob M.p (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁) = 0
    · have hz : ∀ ω ∈ univ.filter (fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁), M.p ω = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun ω _ => hp0 ω).1 h0
      rw [h0, zero_mul]
      exact Finset.sum_eq_zero fun ω hω => by rw [hz ω hω, zero_mul]
    · rw [hexch1 l₀ l₁ (hpos1 l₀ l₁ h0)]
      unfold cmean
      rw [mul_div_assoc', mul_div_cancel_left₀ _ h0]
  have hcons_eq : ∀ l₀ l₁ : 𝓛,
      cmean M.p (M.Ycf a) (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁ ∧ M.A 1 ω = a 1)
      = cmean M.p M.Y (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁ ∧ M.A 1 ω = a 1) := by
    intro l₀ l₁
    have hsum : ∑ ω ∈ univ.filter (fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁ ∧ M.A 1 ω = a 1),
          M.p ω * M.Ycf a ω
        = ∑ ω ∈ univ.filter (fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁ ∧ M.A 1 ω = a 1),
          M.p ω * M.Y ω := by
      refine Finset.sum_congr rfl fun ω hω => ?_
      have hm : M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁ ∧ M.A 1 ω = a 1 :=
        (Finset.mem_filter.1 hω).2
      by_cases hpω : M.p ω = 0
      · rw [hpω, zero_mul, zero_mul]
      · have hA : ∀ k, M.A k ω = a k := by
          show ∀ k : Fin 2, M.A k ω = a k
          simp only [Fin.forall_fin_two]
          exact ⟨hm.2.1, hm.2.2.2⟩
        have hY := hcons ω hpω hA
        rw [hY]
    unfold cmean
    rw [hsum]
  have perL0 : ∀ l₀ : 𝓛, prob M.p (univ.filter fun ω => M.L 0 ω = l₀)
        * cmean M.p (M.Ycf a) (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0)
      = ∑ l₁ : 𝓛, cmean M.p M.Y (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁ ∧ M.A 1 ω = a 1)
        * (prob M.p (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁)
          / prob M.p (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0))
        * prob M.p (univ.filter fun ω => M.L 0 ω = l₀) := by
    intro l₀
    have hcm : cmean M.p (M.Ycf a) (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0)
        = (∑ l₁ : 𝓛, prob M.p (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁)
            * cmean M.p M.Y (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0 ∧ M.L 1 ω = l₁ ∧ M.A 1 ω = a 1))
          / prob M.p (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0) := by
      have h2 := step2 l₀
      simp only [hcons_eq] at h2
      have hunfold : cmean M.p (M.Ycf a) (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0)
          = (∑ ω ∈ univ.filter (fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0), M.p ω * M.Ycf a ω)
            / prob M.p (univ.filter fun ω => M.L 0 ω = l₀ ∧ M.A 0 ω = a 0) := rfl
      rw [hunfold, h2]
    rw [hcm, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l₁ _ => ?_
    ring
  unfold expectation
  rw [step1]
  exact Finset.sum_congr rfl fun l₀ _ => perL0 l₀

private def gf_aux_agree {𝓛 : Type*} {K : ℕ} (m : ℕ) (l l' : Fin (K + 1) → 𝓛) : Prop :=
  ∀ j : Fin (K + 1), j.val < m → l' j = l j

open Classical in
private noncomputable def gf_aux_weight {Ω 𝓛 𝓐 : Type*} {K : ℕ} [Fintype Ω]
    (M : POModel Ω 𝓛 𝓐 K) (a : Fin (K + 1) → 𝓐) (l' : Fin (K + 1) → 𝓛) : ℝ :=
  cmean M.p (M.Ycf a) (univ.filter (M.HistT K l' a)) * ∏ k : Fin (K + 1), M.condL a l' k

private theorem gf_aux_pre_succ {Ω 𝓛 𝓐 : Type*} {K m : ℕ} (O : ObsModel Ω 𝓛 𝓐 K)
    (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) (ω : Ω) :
    O.Pre (m + 1) l a ω ↔ O.HistT m l a ω := by
  simp only [ObsModel.pre_iff, ObsModel.histT_iff]
  have hiff : ∀ j : Fin (K + 1), (j.val < m + 1 ↔ j.val ≤ m) := fun j => by omega
  constructor
  · rintro ⟨hL, hA⟩
    exact ⟨fun j hj => hL j ((hiff j).mpr hj), fun j hj => hA j ((hiff j).mpr hj)⟩
  · rintro ⟨hL, hA⟩
    exact ⟨fun j hj => hL j ((hiff j).mp hj), fun j hj => hA j ((hiff j).mp hj)⟩

private theorem gf_aux_hist_update {Ω 𝓛 𝓐 : Type*} {K m : ℕ} (O : ObsModel Ω 𝓛 𝓐 K)
    (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) (hm : m < K + 1) (v : 𝓛) (ω : Ω) :
    O.Hist m (Function.update l ⟨m, hm⟩ v) a ω ↔
      O.Pre m l a ω ∧ O.L ⟨m, hm⟩ ω = v := by
  simp only [ObsModel.hist_iff, ObsModel.pre_iff]
  constructor
  · rintro ⟨hL, hA⟩
    refine ⟨⟨fun j hj => ?_, hA⟩, ?_⟩
    · have hne : j ≠ ⟨m, hm⟩ := by rintro rfl; exact absurd hj (lt_irrefl m)
      have hLj := hL j (Nat.le_of_lt hj)
      rwa [Function.update_of_ne hne] at hLj
    · have hLm := hL ⟨m, hm⟩ (le_refl m)
      rwa [Function.update_self] at hLm
  · rintro ⟨⟨hL, hA⟩, hmv⟩
    refine ⟨fun j hj => ?_, hA⟩
    by_cases hjlt : j.val < m
    · have hne : j ≠ ⟨m, hm⟩ := by rintro rfl; exact absurd hjlt (lt_irrefl m)
      rw [Function.update_of_ne hne]
      exact hL j hjlt
    · have hjeq : j.val = m := by omega
      have hje : j = ⟨m, hm⟩ := Fin.ext hjeq
      subst hje
      rw [Function.update_self]
      exact hmv

private theorem gf_aux_preh_update {Ω 𝓛 𝓐 : Type*} {K m : ℕ} (O : ObsModel Ω 𝓛 𝓐 K)
    (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) (hm : m < K + 1) (v : 𝓛) (ω : Ω) :
    O.Pre (m + 1) (Function.update l ⟨m, hm⟩ v) a ω ↔
      O.Pre m l a ω ∧ O.L ⟨m, hm⟩ ω = v ∧ O.A ⟨m, hm⟩ ω = a ⟨m, hm⟩ := by
  simp only [ObsModel.pre_iff]
  have hvm : (⟨m, hm⟩ : Fin (K + 1)).val = m := rfl
  constructor
  · rintro ⟨hL, hA⟩
    refine ⟨⟨fun j hj => ?_, fun j hj => hA j (by omega)⟩, ?_, ?_⟩
    · have hne : j ≠ ⟨m, hm⟩ := by rintro rfl; exact absurd hj (lt_irrefl m)
      have hLj := hL j (by omega : j.val < m + 1)
      rwa [Function.update_of_ne hne] at hLj
    · have hLm := hL ⟨m, hm⟩ (by omega : (⟨m, hm⟩ : Fin (K + 1)).val < m + 1)
      rwa [Function.update_self] at hLm
    · exact hA ⟨m, hm⟩ (by omega : (⟨m, hm⟩ : Fin (K + 1)).val < m + 1)
  · rintro ⟨⟨hL, hA⟩, hmv, ham⟩
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · by_cases hjlt : j.val < m
      · have hne : j ≠ ⟨m, hm⟩ := by rintro rfl; exact absurd hjlt (lt_irrefl m)
        rw [Function.update_of_ne hne]
        exact hL j hjlt
      · have hjeq : j.val = m := by omega
        have hje : j = ⟨m, hm⟩ := Fin.ext hjeq
        subst hje
        rw [Function.update_self]
        exact hmv
    · by_cases hjlt : j.val < m
      · exact hA j hjlt
      · have hjeq : j.val = m := by omega
        have hje : j = ⟨m, hm⟩ := Fin.ext hjeq
        subst hje
        exact ham

private theorem gf_aux_pre_update {Ω 𝓛 𝓐 : Type*} {K m : ℕ} (O : ObsModel Ω 𝓛 𝓐 K)
    (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) (hm : m < K + 1) (v : 𝓛) (ω : Ω) :
    O.Pre m (Function.update l ⟨m, hm⟩ v) a ω ↔ O.Pre m l a ω := by
  simp only [ObsModel.pre_iff]
  constructor
  · rintro ⟨hL, hA⟩
    refine ⟨fun j hj => ?_, hA⟩
    have hne : j ≠ ⟨m, hm⟩ := by rintro rfl; exact absurd hj (lt_irrefl m)
    have hLj := hL j hj
    rwa [Function.update_of_ne hne] at hLj
  · rintro ⟨hL, hA⟩
    refine ⟨fun j hj => ?_, hA⟩
    have hne : j ≠ ⟨m, hm⟩ := by rintro rfl; exact absurd hj (lt_irrefl m)
    rw [Function.update_of_ne hne]
    exact hL j hj

private theorem gf_aux_hist_update_of_lt {Ω 𝓛 𝓐 : Type*} {K m : ℕ} (O : ObsModel Ω 𝓛 𝓐 K)
    (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) (hm : m < K + 1) (v : 𝓛)
    (k : Fin (K + 1)) (hkm : k.val < m) (ω : Ω) :
    O.Hist ↑k (Function.update l ⟨m, hm⟩ v) a ω ↔ O.Hist ↑k l a ω := by
  simp only [ObsModel.hist_iff]
  constructor
  · rintro ⟨hL, hA⟩
    refine ⟨fun j hj => ?_, hA⟩
    have hjlt : j.val < m := lt_of_le_of_lt hj hkm
    have hne : j ≠ ⟨m, hm⟩ := by rintro rfl; exact absurd hjlt (lt_irrefl m)
    have hLj := hL j hj
    rwa [Function.update_of_ne hne] at hLj
  · rintro ⟨hL, hA⟩
    refine ⟨fun j hj => ?_, hA⟩
    have hjlt : j.val < m := lt_of_le_of_lt hj hkm
    have hne : j ≠ ⟨m, hm⟩ := by rintro rfl; exact absurd hjlt (lt_irrefl m)
    rw [Function.update_of_ne hne]
    exact hL j hj

private theorem gf_aux_pre_update_of_lt {Ω 𝓛 𝓐 : Type*} {K m : ℕ} (O : ObsModel Ω 𝓛 𝓐 K)
    (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) (hm : m < K + 1) (v : 𝓛)
    (k : Fin (K + 1)) (hkm : k.val < m) (ω : Ω) :
    O.Pre ↑k (Function.update l ⟨m, hm⟩ v) a ω ↔ O.Pre ↑k l a ω := by
  simp only [ObsModel.pre_iff]
  constructor
  · rintro ⟨hL, hA⟩
    refine ⟨fun j hj => ?_, hA⟩
    have hjlt : j.val < m := lt_trans hj hkm
    have hne : j ≠ ⟨m, hm⟩ := by rintro rfl; exact absurd hjlt (lt_irrefl m)
    have hLj := hL j hj
    rwa [Function.update_of_ne hne] at hLj
  · rintro ⟨hL, hA⟩
    refine ⟨fun j hj => ?_, hA⟩
    have hjlt : j.val < m := lt_trans hj hkm
    have hne : j ≠ ⟨m, hm⟩ := by rintro rfl; exact absurd hjlt (lt_irrefl m)
    rw [Function.update_of_ne hne]
    exact hL j hj

private theorem gf_aux_prod_split {K m : ℕ} (hm : m < K + 1) (f : Fin (K + 1) → ℝ) :
    ∏ k ∈ univ.filter (fun k : Fin (K + 1) => k.val < m + 1), f k =
      (∏ k ∈ univ.filter (fun k : Fin (K + 1) => k.val < m), f k) * f ⟨m, hm⟩ := by
  have hvm : (⟨m, hm⟩ : Fin (K + 1)).val = m := rfl
  have hset : univ.filter (fun k : Fin (K + 1) => k.val < m + 1) =
      insert ⟨m, hm⟩ (univ.filter (fun k : Fin (K + 1) => k.val < m)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases hk : k.val < m
      · exact Or.inr hk
      · exact Or.inl (Fin.ext (by omega : k.val = m))
    · rintro (rfl | hk)
      · omega
      · omega
  have hnot : (⟨m, hm⟩ : Fin (K + 1)) ∉
      univ.filter (fun k : Fin (K + 1) => k.val < m) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hset, Finset.prod_insert hnot]
  exact mul_comm _ _

open Classical in
private theorem gf_aux_fiber {𝓛 : Type*} {K m : ℕ} [Fintype 𝓛]
    (l : Fin (K + 1) → 𝓛) (hm : m < K + 1) (W : (Fin (K + 1) → 𝓛) → ℝ) :
    ∑ l' ∈ univ.filter (gf_aux_agree m l), W l' =
      ∑ v, ∑ l' ∈ univ.filter (gf_aux_agree (m + 1) (Function.update l ⟨m, hm⟩ v)),
        W l' := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (gf_aux_agree m l))
    (g := fun l' => l' ⟨m, hm⟩) (t := univ) (fun i _ => Finset.mem_univ _) W]
  refine Finset.sum_congr rfl fun v _ => ?_
  show (∑ l' ∈ (univ.filter (gf_aux_agree m l)).filter (fun l' => l' ⟨m, hm⟩ = v),
      W l') =
    ∑ l' ∈ univ.filter (gf_aux_agree (m + 1) (Function.update l ⟨m, hm⟩ v)), W l'
  have hset : (univ.filter (gf_aux_agree m l)).filter (fun l' => l' ⟨m, hm⟩ = v) =
      univ.filter (gf_aux_agree (m + 1) (Function.update l ⟨m, hm⟩ v)) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun l' _ => ?_
    show (gf_aux_agree m l l' ∧ l' ⟨m, hm⟩ = v) ↔
      gf_aux_agree (m + 1) (Function.update l ⟨m, hm⟩ v) l'
    simp only [gf_aux_agree]
    constructor
    · rintro ⟨hag, hfm⟩ j hj
      by_cases hjlt : j.val < m
      · have hne : j ≠ ⟨m, hm⟩ := by rintro rfl; exact absurd hjlt (lt_irrefl m)
        rw [hag j hjlt, Function.update_of_ne hne]
      · have hjeq : j.val = m := by omega
        have hje : j = ⟨m, hm⟩ := Fin.ext hjeq
        subst hje
        rw [Function.update_self]
        exact hfm
    · intro hag
      refine ⟨fun j hj => ?_, ?_⟩
      · have hlt : j.val < m + 1 := by omega
        have hne : j ≠ ⟨m, hm⟩ := by rintro rfl; exact absurd hj (lt_irrefl m)
        have hagj := hag j hlt
        rwa [Function.update_of_ne hne] at hagj
      · have hvm : (⟨m, hm⟩ : Fin (K + 1)).val = m := rfl
        have hagm := hag ⟨m, hm⟩ (by omega : (⟨m, hm⟩ : Fin (K + 1)).val < m + 1)
        rwa [Function.update_self] at hagm
  rw [hset]

private theorem gf_aux_sum_zero_of_prob_zero {Ω : Type*} (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω)
    (Z : Ω → ℝ) (s : Finset Ω) (h : prob p s = 0) :
    (∑ ω ∈ s, p ω * Z ω) = 0 := by
  have h0 : ∀ ω ∈ s, p ω = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun ω _ => hp0 ω).1 h
  exact Finset.sum_eq_zero fun ω hω => by rw [h0 ω hω, zero_mul]

open Classical in
private theorem gf_aux_cmean_consistent {Ω 𝓛 𝓐 : Type*} {K : ℕ} [Fintype Ω]
    (M : POModel Ω 𝓛 𝓐 K) (a : Fin (K + 1) → 𝓐)
    (hcons : M.Consistent a) (l : Fin (K + 1) → 𝓛) :
    cmean M.p (M.Ycf a) (univ.filter (M.HistT K l a)) =
      cmean M.p M.Y (univ.filter (M.HistT K l a)) := by
  unfold cmean
  congr 1
  refine Finset.sum_congr rfl fun ω hω => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ObsModel.histT_iff] at hω
  by_cases hp : M.p ω = 0
  · rw [hp, zero_mul, zero_mul]
  · have hY : M.Ycf a ω = M.Y ω := by
      apply hcons ω hp
      intro k
      have hkK : k.val ≤ K := by have h := k.isLt; omega
      exact hω.2 k hkK
    rw [hY]

open Classical in
private theorem gf_aux_induct {Ω 𝓛 𝓐 : Type*} {K : ℕ} [Fintype Ω] [Fintype 𝓛]
    (M : POModel Ω 𝓛 𝓐 K) (a : Fin (K + 1) → 𝓐)
    (hp0 : ∀ ω, 0 ≤ M.p ω) (hpos : M.Positive a) (hexch : M.MeanSeqExch a) :
    ∀ (m : ℕ) (_hmle : m ≤ K + 1) (l : Fin (K + 1) → 𝓛),
      prob M.p (univ.filter (M.Pre m l a)) *
          ∑ l' ∈ univ.filter (gf_aux_agree m l), gf_aux_weight M a l' =
        (∑ ω ∈ univ.filter (M.Pre m l a), M.p ω * M.Ycf a ω) *
          ∏ k ∈ univ.filter (fun k : Fin (K + 1) => k.val < m), M.condL a l k := by
  have hbase : ∀ l : Fin (K + 1) → 𝓛,
      prob M.p (univ.filter (M.Pre (K + 1) l a)) *
          ∑ l' ∈ univ.filter (gf_aux_agree (K + 1) l), gf_aux_weight M a l' =
        (∑ ω ∈ univ.filter (M.Pre (K + 1) l a), M.p ω * M.Ycf a ω) *
          ∏ k ∈ univ.filter (fun k : Fin (K + 1) => k.val < K + 1), M.condL a l k := by
    intro l
    have hag : univ.filter (gf_aux_agree (K + 1) l) = {l} := by
      ext l'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        gf_aux_agree]
      constructor
      · intro h
        funext j
        exact h j j.isLt
      · intro h
        subst h
        intro j _
        rfl
    have hpre : univ.filter (M.Pre (K + 1) l a) = univ.filter (M.HistT K l a) := by
      refine Finset.filter_congr fun ω _ => ?_
      simp only [ObsModel.pre_iff, ObsModel.histT_iff]
      constructor
      · rintro ⟨hL, hA⟩
        exact ⟨fun j _ => hL j j.isLt, fun j _ => hA j j.isLt⟩
      · rintro ⟨hL, hA⟩
        have hjK : ∀ j : Fin (K + 1), j.val ≤ K := fun j => by have h := j.isLt; omega
        exact ⟨fun j _ => hL j (hjK j), fun j _ => hA j (hjK j)⟩
    have hprod : univ.filter (fun k : Fin (K + 1) => k.val < K + 1) = univ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun _ => trivial, fun _ => k.isLt⟩
    rw [hag, hpre, hprod, Finset.sum_singleton]
    simp only [gf_aux_weight, cmean]
    by_cases hP : prob M.p (univ.filter (M.HistT K l a)) = 0
    · have hS := gf_aux_sum_zero_of_prob_zero M.p hp0 (M.Ycf a) _ hP
      rw [hP, hS, zero_mul, zero_mul]
    · rw [← mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hP]
  have hstep : ∀ m : ℕ, m ≤ K → (∀ l : Fin (K + 1) → 𝓛,
        prob M.p (univ.filter (M.Pre (m + 1) l a)) *
            ∑ l' ∈ univ.filter (gf_aux_agree (m + 1) l), gf_aux_weight M a l' =
          (∑ ω ∈ univ.filter (M.Pre (m + 1) l a), M.p ω * M.Ycf a ω) *
            ∏ k ∈ univ.filter (fun k : Fin (K + 1) => k.val < m + 1),
              M.condL a l k) →
      ∀ l : Fin (K + 1) → 𝓛,
        prob M.p (univ.filter (M.Pre m l a)) *
            ∑ l' ∈ univ.filter (gf_aux_agree m l), gf_aux_weight M a l' =
          (∑ ω ∈ univ.filter (M.Pre m l a), M.p ω * M.Ycf a ω) *
            ∏ k ∈ univ.filter (fun k : Fin (K + 1) => k.val < m), M.condL a l k := by
    intro m hmK ih l
    have hm : m < K + 1 := by omega
    set E : Finset Ω := univ.filter (M.Pre m l a) with hE
    by_cases hPE : prob M.p E = 0
    · have hSE := gf_aux_sum_zero_of_prob_zero M.p hp0 (M.Ycf a) E hPE
      rw [hPE, hSE, zero_mul, zero_mul]
    · have hfibsum : (∑ l' ∈ univ.filter (gf_aux_agree m l), gf_aux_weight M a l') =
          ∑ v, ∑ l' ∈ univ.filter (gf_aux_agree (m + 1) (Function.update l ⟨m, hm⟩ v)),
            gf_aux_weight M a l' := gf_aux_fiber l hm _
      rw [hfibsum, Finset.mul_sum]
      have hper : ∀ v : 𝓛, prob M.p E *
            (∑ l' ∈ univ.filter (gf_aux_agree (m + 1) (Function.update l ⟨m, hm⟩ v)),
              gf_aux_weight M a l') =
            (∏ k ∈ univ.filter (fun k : Fin (K + 1) => k.val < m), M.condL a l k) *
            (∑ ω ∈ univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v),
              M.p ω * M.Ycf a ω) := by
        intro v
        set l₁ : Fin (K + 1) → 𝓛 := Function.update l ⟨m, hm⟩ v with hl₁
        have hPre1 : univ.filter (M.Pre (m + 1) l₁ a) =
            univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v ∧
              M.A ⟨m, hm⟩ ω = a ⟨m, hm⟩) := by
          refine Finset.filter_congr fun ω _ => ?_
          exact gf_aux_preh_update _ l a hm v ω
        have hHist : univ.filter (M.Hist m l₁ a) =
            univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v) := by
          refine Finset.filter_congr fun ω _ => ?_
          exact gf_aux_hist_update _ l a hm v ω
        have hHist' : univ.filter (M.Hist ↑(⟨m, hm⟩ : Fin (K + 1)) l₁ a) =
            univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v) := by
          refine Finset.filter_congr fun ω _ => ?_
          exact gf_aux_hist_update _ l a hm v ω
        have hPre0' : univ.filter (M.Pre m l₁ a) = E := by
          rw [hE]
          refine Finset.filter_congr fun ω _ => ?_
          exact gf_aux_pre_update _ l a hm v ω
        have hHT' : univ.filter (M.HistT ↑(⟨m, hm⟩ : Fin (K + 1)) l₁ a) =
            univ.filter (M.Pre (m + 1) l₁ a) := by
          refine Finset.filter_congr fun ω _ => ?_
          exact (gf_aux_pre_succ _ l₁ a ω).symm
        have hprod : ∏ k ∈ univ.filter (fun k : Fin (K + 1) => k.val < m + 1),
            M.condL a l₁ k =
            (∏ k ∈ univ.filter (fun k : Fin (K + 1) => k.val < m), M.condL a l k) *
            (prob M.p (univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v)) /
              prob M.p E) := by
          have hsplit : ∏ k ∈ univ.filter (fun k : Fin (K + 1) => k.val < m + 1),
              M.condL a l₁ k =
              (∏ k ∈ univ.filter (fun k : Fin (K + 1) => k.val < m), M.condL a l₁ k) *
              M.condL a l₁ m := gf_aux_prod_split hm _
          rw [hsplit]
          congr 1
          · refine Finset.prod_congr rfl fun k hk => ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            have eH : univ.filter (M.Hist ↑k l₁ a) = univ.filter (M.Hist ↑k l a) := by
              refine Finset.filter_congr fun ω _ => ?_
              exact gf_aux_hist_update_of_lt _ l a hm v k hk ω
            have eP : univ.filter (M.Pre ↑k l₁ a) = univ.filter (M.Pre ↑k l a) := by
              refine Finset.filter_congr fun ω _ => ?_
              exact gf_aux_pre_update_of_lt _ l a hm v k hk ω
            unfold ObsModel.condL
            rw [eH, eP]
          · show M.condL a l₁ m =
              prob M.p (univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v)) /
                prob M.p E
            unfold ObsModel.condL
            rw [hHist, hPre0']
        have hIH := ih l₁
        rw [hPre1, hprod] at hIH
        by_cases hP1 : prob M.p (univ.filter (M.Pre (m + 1) l₁ a)) = 0
        · have hPHT0 : prob M.p (univ.filter (M.HistT m l₁ a)) = 0 := by
            have hHT : univ.filter (M.HistT m l₁ a) =
                univ.filter (M.Pre (m + 1) l₁ a) := by
              refine Finset.filter_congr fun ω _ => ?_
              exact (gf_aux_pre_succ _ l₁ a ω).symm
            rw [hHT]; exact hP1
          have hPH0 : prob M.p (univ.filter (M.Hist m l₁ a)) = 0 := by
            by_contra hne
            exact hpos ⟨m, hm⟩ l₁ hne hPHT0
          have hSH0 : (∑ ω ∈ univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v),
              M.p ω * M.Ycf a ω) = 0 := by
            rw [← hHist]
            exact gf_aux_sum_zero_of_prob_zero M.p hp0 (M.Ycf a) _ hPH0
          have hInner0 : (∑ l' ∈ univ.filter (gf_aux_agree (m + 1) l₁),
              gf_aux_weight M a l') = 0 := by
            refine Finset.sum_eq_zero fun l' hl' => ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              gf_aux_agree] at hl'
            have hfactor : M.condL a l' ↑(⟨m, hm⟩ : Fin (K + 1)) = 0 := by
              have hset : univ.filter (M.Hist ↑(⟨m, hm⟩ : Fin (K + 1)) l' a) =
                  univ.filter (M.Hist m l₁ a) := by
                refine Finset.filter_congr fun ω _ => ?_
                simp only [ObsModel.hist_iff]
                constructor
                · rintro ⟨hL, hA⟩
                  refine ⟨fun j hj => ?_, hA⟩
                  have hjlt : j.val < m + 1 := lt_of_le_of_lt hj (Nat.lt_succ_self m)
                  have hmem := hl' j hjlt
                  rw [← hmem]
                  exact hL j hj
                · rintro ⟨hL, hA⟩
                  refine ⟨fun j hj => ?_, hA⟩
                  have hjlt : j.val < m + 1 := lt_of_le_of_lt hj (Nat.lt_succ_self m)
                  have hmem := hl' j hjlt
                  rw [hmem]
                  exact hL j hj
              have hnum : prob M.p (univ.filter (M.Hist ↑(⟨m, hm⟩ : Fin (K + 1)) l' a)) = 0 := by
                rw [hset]; exact hPH0
              unfold ObsModel.condL
              rw [hnum, zero_div]
            have hprod0 : (∏ k : Fin (K + 1), M.condL a l' k) = 0 :=
              Finset.prod_eq_zero (Finset.mem_univ _) hfactor
            simp only [gf_aux_weight]
            rw [hprod0, mul_zero]
          rw [hInner0, hSH0, mul_zero, mul_zero]
        · have hexch_v : cmean M.p (M.Ycf a)
              (univ.filter (M.HistT ↑(⟨m, hm⟩ : Fin (K + 1)) l₁ a)) =
              cmean M.p (M.Ycf a)
                (univ.filter (M.Hist ↑(⟨m, hm⟩ : Fin (K + 1)) l₁ a)) := by
            apply hexch ⟨m, hm⟩ l₁
            rw [hHT']; exact hP1
          have hcmean : (∑ ω ∈ univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v ∧
              M.A ⟨m, hm⟩ ω = a ⟨m, hm⟩), M.p ω * M.Ycf a ω) /
                prob M.p (univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v ∧
                  M.A ⟨m, hm⟩ ω = a ⟨m, hm⟩)) =
              (∑ ω ∈ univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v),
                M.p ω * M.Ycf a ω) /
              prob M.p (univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v)) := by
            have h := hexch_v
            unfold cmean at h
            rw [hHT', hHist', hPre1] at h
            exact h
          set P1 : ℝ := prob M.p (univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v ∧
            M.A ⟨m, hm⟩ ω = a ⟨m, hm⟩)) with hP₁
          set S1 : ℝ := (∑ ω ∈ univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v ∧
            M.A ⟨m, hm⟩ ω = a ⟨m, hm⟩), M.p ω * M.Ycf a ω) with hS₁
          set PH : ℝ := prob M.p (univ.filter (fun ω => M.Pre m l a ω ∧
            M.L ⟨m, hm⟩ ω = v)) with hPHd
          set SH : ℝ := (∑ ω ∈ univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v),
            M.p ω * M.Ycf a ω) with hSHd
          set PR : ℝ := (∏ k ∈ univ.filter (fun k : Fin (K + 1) => k.val < m),
            M.condL a l k) with hPR
          set INv : ℝ := (∑ l' ∈ univ.filter (gf_aux_agree (m + 1) l₁),
            gf_aux_weight M a l') with hINv
          set PE : ℝ := prob M.p E with hPEd
          have hP1' : P1 ≠ 0 := by rw [hP₁, ← hPre1]; exact hP1
          by_cases hPH : PH = 0
          · have hSH0 : SH = 0 := gf_aux_sum_zero_of_prob_zero M.p hp0 (M.Ycf a) _ hPH
            have hIN0 : INv = 0 := by
              have h0 : PR * (PH / PE) = 0 := by rw [hPH, zero_div, mul_zero]
              rw [h0, mul_zero] at hIH
              exact (mul_eq_zero.mp hIH).resolve_left hP1'
            rw [hIN0, hSH0, mul_zero, mul_zero]
          · have hcross : S1 * PH = SH * P1 := (div_eq_div_iff hP1' hPH).mp hcmean
            suffices hfin : (PE * INv) * P1 = (PR * SH) * P1 from
              mul_right_cancel₀ hP1' hfin
            have hcancel : PE * (PH / PE) = PH := by
              rw [← mul_div_assoc, mul_div_cancel_left₀ _ hPE]
            have hLHS : (PE * INv) * P1 = S1 * PR * PH := by
              have h1 : (PE * INv) * P1 = PE * (P1 * INv) := by ring
              rw [h1, hIH]
              have h2 : PE * (S1 * (PR * (PH / PE))) = S1 * PR * (PE * (PH / PE)) := by
                ring
              rw [h2, hcancel]
            have hRHS : (PR * SH) * P1 = S1 * PR * PH := by
              have h2 : (PR * SH) * P1 = PR * (SH * P1) := by ring
              rw [h2, ← hcross]
              ring
            exact hLHS.trans hRHS.symm
      have hfib : (∑ v, ∑ ω ∈ univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v),
          M.p ω * M.Ycf a ω) = ∑ ω ∈ E, M.p ω * M.Ycf a ω := by
        calc (∑ v, ∑ ω ∈ univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v),
              M.p ω * M.Ycf a ω)
            = ∑ v, ∑ ω ∈ E.filter (fun ω => M.L ⟨m, hm⟩ ω = v),
              M.p ω * M.Ycf a ω := by
              refine Finset.sum_congr rfl fun v _ => ?_
              have hset : E.filter (fun ω => M.L ⟨m, hm⟩ ω = v) =
                  univ.filter (fun ω => M.Pre m l a ω ∧ M.L ⟨m, hm⟩ ω = v) := by
                rw [hE, Finset.filter_filter]
              rw [hset]
          _ = ∑ ω ∈ E, M.p ω * M.Ycf a ω :=
            Finset.sum_fiberwise E (fun ω => M.L ⟨m, hm⟩ ω)
              (fun ω => M.p ω * M.Ycf a ω)
      rw [Finset.sum_congr rfl (fun v _ => hper v), ← Finset.mul_sum, hfib]
      exact mul_comm _ _
  have hdesc : ∀ d : ℕ, d ≤ K + 1 → ∀ l : Fin (K + 1) → 𝓛,
      prob M.p (univ.filter (M.Pre (K + 1 - d) l a)) *
          ∑ l' ∈ univ.filter (gf_aux_agree (K + 1 - d) l), gf_aux_weight M a l' =
        (∑ ω ∈ univ.filter (M.Pre (K + 1 - d) l a), M.p ω * M.Ycf a ω) *
          ∏ k ∈ univ.filter (fun k : Fin (K + 1) => k.val < K + 1 - d),
            M.condL a l k := by
    intro d
    induction d with
    | zero =>
      intro _ l
      simp only [Nat.sub_zero]
      exact hbase l
    | succ d ih =>
      intro hd l
      have hm1 : K + 1 - (d + 1) + 1 = K + 1 - d := by omega
      have hmK : K + 1 - (d + 1) ≤ K := by omega
      have hih := ih (by omega : d ≤ K + 1)
      rw [← hm1] at hih
      exact hstep (K + 1 - (d + 1)) hmK hih l
  intro m hmle l
  have hdesc_m := hdesc (K + 1 - m) (Nat.sub_le _ _) l
  have hmm : K + 1 - (K + 1 - m) = m := by omega
  rw [hmm] at hdesc_m
  exact hdesc_m

open Classical in

private theorem gf_aux_expectation {Ω 𝓛 𝓐 : Type*} {K : ℕ} [Fintype Ω] [Fintype 𝓛]
    (M : POModel Ω 𝓛 𝓐 K) (a : Fin (K + 1) → 𝓐)
    (hp0 : ∀ ω, 0 ≤ M.p ω) (hp1 : ∑ ω, M.p ω = 1)
    (hcons : M.Consistent a) (hpos : M.Positive a) (hexch : M.MeanSeqExch a) :
    expectation M.p (M.Ycf a) = M.gFormula a := by
  rcases isEmpty_or_nonempty 𝓛 with hE | hNE
  · haveI := hE
    have hO : IsEmpty Ω := ⟨fun ω => IsEmpty.false (M.L ⟨0, by omega⟩ ω)⟩
    have hF : IsEmpty (Fin (K + 1) → 𝓛) :=
      ⟨fun l => IsEmpty.false (l ⟨0, by omega⟩)⟩
    haveI := hO
    have hL : expectation M.p (M.Ycf a) = 0 := by
      unfold expectation
      exact Fintype.sum_empty _
    haveI := hF
    have hR : M.gFormula a = 0 := by
      rw [ObsModel.gFormula]
      exact Fintype.sum_empty _
    rw [hL, hR]
  · obtain ⟨lstar⟩ := hNE
    have hP0 := gf_aux_induct M a hp0 hpos hexch 0 (Nat.zero_le _) (fun _ => lstar)
    have hpre0 : univ.filter (M.Pre 0 (fun _ : Fin (K + 1) => lstar) a) = univ := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ObsModel.pre_iff]
      exact ⟨fun _ => trivial, fun _ => ⟨fun j hj => absurd hj (by omega),
        fun j hj => absurd hj (by omega)⟩⟩
    have hagree0 : univ.filter (gf_aux_agree 0 (fun _ : Fin (K + 1) => lstar)) = univ := by
      ext l'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, gf_aux_agree]
      exact ⟨fun _ => trivial, fun _ j hj => absurd hj (by omega)⟩
    have hprod0 : univ.filter (fun k : Fin (K + 1) => k.val < 0) = ∅ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty]
      exact ⟨fun h => absurd h (by omega), fun h => False.elim h⟩
    rw [hpre0, hagree0, hprod0, Finset.prod_empty, mul_one] at hP0
    have hP1 : prob M.p univ = 1 := hp1
    rw [hP1, one_mul] at hP0
    have hW : (∑ l', gf_aux_weight M a l') = M.gFormula a := by
      rw [ObsModel.gFormula]
      refine Finset.sum_congr rfl fun l' _ => ?_
      simp only [gf_aux_weight]
      rw [gf_aux_cmean_consistent M a hcons l']
    rw [← hW]
    exact hP0.symm

/-- **Milestone 2: the g-formula for `K + 1` time points** (Hernán and Robins, *What If*,
§21.1, p. 274). Under consistency, sequential positivity along the plan and static sequential
exchangeability for `Y^ā`, the counterfactual mean `E[Y^ā]` is the g-formula of `ā`. The proof
is an induction whose step is `sum_filter_mul_eq_sum`; iterating the two-period case instead
would merge treatments and drop the intermediate exchangeability conditions. -/
theorem expectation_Ycf_eq_gFormula [Fintype Ω] [Fintype 𝓛] (M : POModel Ω 𝓛 𝓐 K)
    (a : Fin (K + 1) → 𝓐) (hp0 : ∀ ω, 0 ≤ M.p ω) (hp1 : ∑ ω, M.p ω = 1)
    (hcons : M.Consistent a) (hpos : M.Positive a) (hexch : M.SeqExch a) :
    expectation M.p (M.Ycf a) = M.gFormula a := by
  exact gf_aux_expectation M a hp0 hp1 hcons hpos (POModel.SeqExch.meanSeqExch hp0 hexch)

/-- The g-formula for `K + 1` time points under the mean form of static sequential
exchangeability (`POModel.MeanSeqExch`), which `POModel.SeqExch` implies for nonnegative
weights. -/
theorem expectation_Ycf_eq_gFormula_of_mean [Fintype Ω] [Fintype 𝓛] (M : POModel Ω 𝓛 𝓐 K)
    (a : Fin (K + 1) → 𝓐) (hp0 : ∀ ω, 0 ≤ M.p ω) (hp1 : ∑ ω, M.p ω = 1)
    (hcons : M.Consistent a) (hpos : M.Positive a) (hexch : M.MeanSeqExch a) :
    expectation M.p (M.Ycf a) = M.gFormula a := by
  exact gf_aux_expectation M a hp0 hp1 hcons hpos hexch

/-- For `K = 1` the g-formula is the two-period display of `expectation_Ycf_eq_two_period`,
with the factor of time `0` written as `P(L₀ = l₀) / P(Ω)` (no normalization is assumed). -/
theorem gFormula_one [Fintype Ω] [Fintype 𝓛] [DecidableEq 𝓛] [DecidableEq 𝓐]
    (O : ObsModel Ω 𝓛 𝓐 1) (a : Fin 2 → 𝓐) :
    O.gFormula a =
      ∑ l₀ : 𝓛, ∑ l₁ : 𝓛,
        cmean O.p O.Y
            (univ.filter fun ω => O.L 0 ω = l₀ ∧ O.A 0 ω = a 0 ∧ O.L 1 ω = l₁ ∧ O.A 1 ω = a 1) *
          (prob O.p (univ.filter fun ω => O.L 0 ω = l₀ ∧ O.A 0 ω = a 0 ∧ O.L 1 ω = l₁) /
            prob O.p (univ.filter fun ω => O.L 0 ω = l₀ ∧ O.A 0 ω = a 0)) *
          (prob O.p (univ.filter fun ω => O.L 0 ω = l₀) / prob O.p univ) := by
  classical
  rw [ObsModel.gFormula, sum_snoc, sum_snoc, Fintype.sum_unique]
  refine Finset.sum_congr rfl fun l₀ _ => Finset.sum_congr rfl fun l₁ _ => ?_
  set l : Fin (1 + 1) → 𝓛 :=
    Fin.snoc (n := 1) (Fin.snoc (n := 0) (default : Fin 0 → 𝓛) l₀) l₁ with hl
  have e0 : (0 : Fin (1 + 1)) = Fin.castSucc (0 : Fin 1) := Fin.ext (by decide)
  have e0' : (0 : Fin 1) = Fin.last 0 := Fin.ext (by decide)
  have eS : (0 : Fin 1).succ = Fin.last 1 := Fin.ext (by decide)
  have hl0 : l 0 = l₀ := by rw [hl, e0, Fin.snoc_castSucc, e0', Fin.snoc_last]
  have hlS : l ((0 : Fin 1).succ) = l₁ := by rw [hl, eS, Fin.snoc_last]
  have hprod : ∏ k : Fin (1 + 1), O.condL a l k =
      O.condL a l ↑(0 : Fin (1 + 1)) * O.condL a l (0 : Fin 1).succ := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_one]
  rw [hprod]
  unfold ObsModel.condL
  have eT : univ.filter (O.HistT 1 l a) =
      univ.filter (fun ω => O.L 0 ω = l₀ ∧ O.A 0 ω = a 0 ∧ O.L 1 ω = l₁ ∧
        O.A 1 ω = a 1) := by
    refine Finset.filter_congr fun ω _ => ?_
    simp only [ObsModel.histT_iff, Fin.forall_fin_succ]
    rw [hl0, hlS]
    have t0 : (0 : Fin (1 + 1)).val ≤ 1 := by decide
    have tS : ((0 : Fin 1).succ).val ≤ 1 := by decide
    simp only [t0, tS, true_imp_iff, Fin.forall_fin_zero]
    constructor
    · rintro ⟨⟨hL0, hLS, -⟩, ⟨hA0, hAS, -⟩⟩
      exact ⟨hL0, hA0, hLS, hAS⟩
    · rintro ⟨hL0, hA0, hLS, hAS⟩
      exact ⟨⟨hL0, hLS, trivial⟩, ⟨hA0, hAS, trivial⟩⟩
  have eH1 : univ.filter (O.Hist ↑((0 : Fin 1).succ) l a) =
      univ.filter (fun ω => O.L 0 ω = l₀ ∧ O.A 0 ω = a 0 ∧ O.L 1 ω = l₁) := by
    refine Finset.filter_congr fun ω _ => ?_
    simp only [ObsModel.hist_iff, Fin.forall_fin_succ]
    rw [hl0, hlS]
    have u0 : (0 : Fin (1 + 1)).val ≤ ↑((0 : Fin 1).succ) := by decide
    have uS : ((0 : Fin 1).succ).val ≤ ↑((0 : Fin 1).succ) := by decide
    have v0 : (0 : Fin (1 + 1)).val < ↑((0 : Fin 1).succ) := by decide
    have vS : ¬ ((0 : Fin 1).succ).val < ↑((0 : Fin 1).succ) := by decide
    simp only [u0, uS, v0, vS, true_imp_iff, false_imp_iff, Fin.forall_fin_zero]
    constructor
    · rintro ⟨⟨hL0, hLS, -⟩, ⟨hA0, -, -⟩⟩
      exact ⟨hL0, hA0, hLS⟩
    · rintro ⟨hL0, hA0, hLS⟩
      exact ⟨⟨hL0, hLS, trivial⟩, ⟨hA0, trivial, trivial⟩⟩
  have eP1 : univ.filter (O.Pre ↑((0 : Fin 1).succ) l a) =
      univ.filter (fun ω => O.L 0 ω = l₀ ∧ O.A 0 ω = a 0) := by
    refine Finset.filter_congr fun ω _ => ?_
    simp only [ObsModel.pre_iff, Fin.forall_fin_succ]
    rw [hl0, hlS]
    have v0 : (0 : Fin (1 + 1)).val < ↑((0 : Fin 1).succ) := by decide
    have vS : ¬ ((0 : Fin 1).succ).val < ↑((0 : Fin 1).succ) := by decide
    simp only [v0, vS, true_imp_iff, false_imp_iff, Fin.forall_fin_zero]
    constructor
    · rintro ⟨⟨hL0, -, -⟩, ⟨hA0, -, -⟩⟩
      exact ⟨hL0, hA0⟩
    · rintro ⟨hL0, hA0⟩
      exact ⟨⟨hL0, trivial, trivial⟩, ⟨hA0, trivial, trivial⟩⟩
  have eH0 : univ.filter (O.Hist ↑(0 : Fin (1 + 1)) l a) =
      univ.filter (fun ω => O.L 0 ω = l₀) := by
    refine Finset.filter_congr fun ω _ => ?_
    simp only [ObsModel.hist_iff, Fin.forall_fin_succ]
    rw [hl0, hlS]
    have w0 : (0 : Fin (1 + 1)).val ≤ ↑(0 : Fin (1 + 1)) := by decide
    have wS : ¬ ((0 : Fin 1).succ).val ≤ ↑(0 : Fin (1 + 1)) := by decide
    have w0lt : ¬ (0 : Fin (1 + 1)).val < ↑(0 : Fin (1 + 1)) := by decide
    have wSlt : ¬ ((0 : Fin 1).succ).val < ↑(0 : Fin (1 + 1)) := by decide
    simp only [w0, wS, w0lt, wSlt, true_imp_iff, false_imp_iff, Fin.forall_fin_zero]
    constructor
    · rintro ⟨⟨hL0, -, -⟩, ⟨-, -, -⟩⟩
      exact hL0
    · intro hL0
      exact ⟨⟨hL0, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩⟩
  have eP0 : univ.filter (O.Pre ↑(0 : Fin (1 + 1)) l a) = univ := by
    apply Finset.filter_true_of_mem
    intro ω _
    have hz : (↑(0 : Fin (1 + 1)) : ℕ) = 0 := by decide
    simp only [ObsModel.pre_iff]
    rw [hz]
    exact ⟨fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega)⟩
  rw [eT, eH1, eP1, eH0, eP0]
  ring

/-! ### The observed joint law and its cell moments -/

namespace ObsModel

open Classical in
/-- The **observed joint law**: the pushforward of the study weights to covariate
histories, treatment histories and outcomes. `observedLaw l a y` is the probability of
the cell `{L̄ = l, Ā = a, Y = y}`. -/
noncomputable def observedLaw {Ω 𝓛 𝓐 : Type*} {K : ℕ} [Fintype Ω] (O : ObsModel Ω 𝓛 𝓐 K)
    (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) (y : ℝ) : ℝ :=
  prob O.p (univ.filter (fun ω => (∀ j : Fin (K + 1), O.L j ω = l j) ∧
    (∀ j : Fin (K + 1), O.A j ω = a j) ∧ O.Y ω = y))

open Classical in
/-- The **cell moments** of the observed law: for each covariate history `l` and treatment
history `a`, the probability of the cell `{L̄ = l, Ā = a}` and its `Y`-weighted mass
`∑_{ω ∈ cell} p ω * Y ω`. This is a summary of `observedLaw`, not the law itself:
different outcome distributions on one cell can share the same two components. The
g-formula consumes only these moments (`gFormula_eq_gFormulaOfMoments`), and the law
determines them (`cellMoments_eq_of_observedLaw_eq`). -/
noncomputable def cellMoments {Ω 𝓛 𝓐 : Type*} {K : ℕ} [Fintype Ω] (O : ObsModel Ω 𝓛 𝓐 K)
    (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) : ℝ × ℝ :=
  (prob O.p (univ.filter (O.HistT K l a)),
    ∑ ω ∈ univ.filter (O.HistT K l a), O.p ω * O.Y ω)

open Classical in
private theorem gf_aux_observedLaw_eq_zero_of_not_mem {Ω 𝓛 𝓐 : Type*} {K : ℕ} [Fintype Ω]
    (O : ObsModel Ω 𝓛 𝓐 K) (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) (y : ℝ)
    (hy : y ∉ univ.image O.Y) : O.observedLaw l a y = 0 := by
  unfold observedLaw prob
  apply Finset.sum_eq_zero
  intro ω hω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
  exact absurd (Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, hω.2.2⟩) hy

open Classical in
private theorem gf_aux_prob_histT_eq_sum_observedLaw {Ω 𝓛 𝓐 : Type*} {K : ℕ} [Fintype Ω]
    (O : ObsModel Ω 𝓛 𝓐 K) (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) :
    prob O.p (univ.filter (O.HistT K l a)) = ∑ y ∈ univ.image O.Y, O.observedLaw l a y := by
  have hK : ∀ j : Fin (K + 1), j.val ≤ K := by
    intro j
    have hj := j.2
    omega
  have hfiber : ∀ y : ℝ, (univ.filter (O.HistT K l a)).filter (fun ω => O.Y ω = y) =
      univ.filter (fun ω => (∀ j : Fin (K + 1), O.L j ω = l j) ∧
        (∀ j : Fin (K + 1), O.A j ω = a j) ∧ O.Y ω = y) := by
    intro y
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, O.histT_iff]
    constructor
    · rintro ⟨⟨hL, hA⟩, hY⟩
      exact ⟨fun j => hL j (hK j), fun j => hA j (hK j), hY⟩
    · rintro ⟨hL, hA, hY⟩
      exact ⟨⟨fun j _ => hL j, fun j _ => hA j⟩, hY⟩
  have hmaps : ∀ ω ∈ univ.filter (O.HistT K l a), O.Y ω ∈ univ.image O.Y := by
    intro ω _
    exact Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, rfl⟩
  have hfib := Finset.sum_fiberwise_of_maps_to (s := univ.filter (O.HistT K l a))
    (g := O.Y) (t := univ.image O.Y) hmaps (fun ω => O.p ω)
  have hprob : prob O.p (univ.filter (O.HistT K l a)) =
      ∑ ω ∈ univ.filter (O.HistT K l a), O.p ω := rfl
  rw [hprob, ← hfib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hfiber y]
  rfl

open Classical in
private theorem gf_aux_weighted_histT_eq_sum_observedLaw {Ω 𝓛 𝓐 : Type*} {K : ℕ} [Fintype Ω]
    (O : ObsModel Ω 𝓛 𝓐 K) (l : Fin (K + 1) → 𝓛) (a : Fin (K + 1) → 𝓐) :
    (∑ ω ∈ univ.filter (O.HistT K l a), O.p ω * O.Y ω) =
      ∑ y ∈ univ.image O.Y, y * O.observedLaw l a y := by
  have hK : ∀ j : Fin (K + 1), j.val ≤ K := by
    intro j
    have hj := j.2
    omega
  have hfiber : ∀ y : ℝ, (univ.filter (O.HistT K l a)).filter (fun ω => O.Y ω = y) =
      univ.filter (fun ω => (∀ j : Fin (K + 1), O.L j ω = l j) ∧
        (∀ j : Fin (K + 1), O.A j ω = a j) ∧ O.Y ω = y) := by
    intro y
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, O.histT_iff]
    constructor
    · rintro ⟨⟨hL, hA⟩, hY⟩
      exact ⟨fun j => hL j (hK j), fun j => hA j (hK j), hY⟩
    · rintro ⟨hL, hA, hY⟩
      exact ⟨⟨fun j _ => hL j, fun j _ => hA j⟩, hY⟩
  have hmaps : ∀ ω ∈ univ.filter (O.HistT K l a), O.Y ω ∈ univ.image O.Y := by
    intro ω _
    exact Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, rfl⟩
  have hfib := Finset.sum_fiberwise_of_maps_to (s := univ.filter (O.HistT K l a))
    (g := O.Y) (t := univ.image O.Y) hmaps (fun ω => O.p ω * O.Y ω)
  rw [← hfib]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h1 : (∑ ω ∈ (univ.filter (O.HistT K l a)).filter (fun ω => O.Y ω = y), O.p ω * O.Y ω) =
      ∑ ω ∈ (univ.filter (O.HistT K l a)).filter (fun ω => O.Y ω = y), O.p ω * y :=
    Finset.sum_congr rfl fun ω hω => by
      simp only [Finset.mem_filter] at hω
      rw [hω.2]
  have h2 : (∑ ω ∈ (univ.filter (O.HistT K l a)).filter (fun ω => O.Y ω = y), O.p ω * y) =
      y * (∑ ω ∈ (univ.filter (O.HistT K l a)).filter (fun ω => O.Y ω = y), O.p ω) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => by rw [mul_comm]
  have h3 : (∑ ω ∈ (univ.filter (O.HistT K l a)).filter (fun ω => O.Y ω = y), O.p ω) =
      O.observedLaw l a y := by
    rw [hfiber y]
    rfl
  rw [h1, h2, h3]

/-- **The observed law determines the cell moments**: two studies on the same sample space
with the same `observedLaw` have the same `cellMoments`. Each cell mass is the sum of
the law over the outcome values in the cell, and each weighted mass is the
corresponding first-moment sum. -/
theorem cellMoments_eq_of_observedLaw_eq {Ω 𝓛 𝓐 : Type*} {K : ℕ} [Fintype Ω]
    {O₁ O₂ : ObsModel Ω 𝓛 𝓐 K} (h : O₁.observedLaw = O₂.observedLaw) :
    O₁.cellMoments = O₂.cellMoments := by
  classical
  funext l a
  apply Prod.ext
  · show prob O₁.p (univ.filter (O₁.HistT K l a)) =
      prob O₂.p (univ.filter (O₂.HistT K l a))
    rw [gf_aux_prob_histT_eq_sum_observedLaw O₁ l a,
      gf_aux_prob_histT_eq_sum_observedLaw O₂ l a]
    have hsub1 : univ.image O₁.Y ⊆ univ.image O₁.Y ∪ univ.image O₂.Y :=
      Finset.subset_union_left
    have hsub2 : univ.image O₂.Y ⊆ univ.image O₁.Y ∪ univ.image O₂.Y :=
      Finset.subset_union_right
    have hvan1 : ∀ y ∈ univ.image O₁.Y ∪ univ.image O₂.Y,
        y ∉ univ.image O₁.Y → O₁.observedLaw l a y = 0 :=
      fun y _ hy => gf_aux_observedLaw_eq_zero_of_not_mem O₁ l a y hy
    have hvan2 : ∀ y ∈ univ.image O₁.Y ∪ univ.image O₂.Y,
        y ∉ univ.image O₂.Y → O₂.observedLaw l a y = 0 :=
      fun y _ hy => gf_aux_observedLaw_eq_zero_of_not_mem O₂ l a y hy
    have heq1 : (∑ y ∈ univ.image O₁.Y, O₁.observedLaw l a y) =
        ∑ y ∈ univ.image O₁.Y ∪ univ.image O₂.Y, O₁.observedLaw l a y :=
      Finset.sum_subset hsub1 hvan1
    have heq2 : (∑ y ∈ univ.image O₂.Y, O₂.observedLaw l a y) =
        ∑ y ∈ univ.image O₁.Y ∪ univ.image O₂.Y, O₂.observedLaw l a y :=
      Finset.sum_subset hsub2 hvan2
    rw [heq1, heq2, h]
  · show (∑ ω ∈ univ.filter (O₁.HistT K l a), O₁.p ω * O₁.Y ω) =
      (∑ ω ∈ univ.filter (O₂.HistT K l a), O₂.p ω * O₂.Y ω)
    rw [gf_aux_weighted_histT_eq_sum_observedLaw O₁ l a,
      gf_aux_weighted_histT_eq_sum_observedLaw O₂ l a]
    have hsub1 : univ.image O₁.Y ⊆ univ.image O₁.Y ∪ univ.image O₂.Y :=
      Finset.subset_union_left
    have hsub2 : univ.image O₂.Y ⊆ univ.image O₁.Y ∪ univ.image O₂.Y :=
      Finset.subset_union_right
    have hvan1 : ∀ y ∈ univ.image O₁.Y ∪ univ.image O₂.Y,
        y ∉ univ.image O₁.Y → y * O₁.observedLaw l a y = 0 := by
      intro y _ hy
      rw [gf_aux_observedLaw_eq_zero_of_not_mem O₁ l a y hy, mul_zero]
    have hvan2 : ∀ y ∈ univ.image O₁.Y ∪ univ.image O₂.Y,
        y ∉ univ.image O₂.Y → y * O₂.observedLaw l a y = 0 := by
      intro y _ hy
      rw [gf_aux_observedLaw_eq_zero_of_not_mem O₂ l a y hy, mul_zero]
    have heq1 : (∑ y ∈ univ.image O₁.Y, y * O₁.observedLaw l a y) =
        ∑ y ∈ univ.image O₁.Y ∪ univ.image O₂.Y, y * O₁.observedLaw l a y :=
      Finset.sum_subset hsub1 hvan1
    have heq2 : (∑ y ∈ univ.image O₂.Y, y * O₂.observedLaw l a y) =
        ∑ y ∈ univ.image O₁.Y ∪ univ.image O₂.Y, y * O₂.observedLaw l a y :=
      Finset.sum_subset hsub2 hvan2
    rw [heq1, heq2, h]

open Classical in
private theorem gf_aux_prob_cell_eq_sum_cellMoments {Ω 𝓛 𝓐 : Type*} {K : ℕ} [Fintype Ω] [Fintype 𝓛]
    [Fintype 𝓐] (O : ObsModel Ω 𝓛 𝓐 K) (k : ℕ) (l : Fin (K + 1) → 𝓛)
    (a : Fin (K + 1) → 𝓐) (BL : ℕ → Prop) [DecidablePred BL] (cell : Ω → Prop)
    (hcell : ∀ ω, cell ω ↔ (∀ j : Fin (K + 1), BL j.val → O.L j ω = l j) ∧
      ∀ j : Fin (K + 1), j.val < k → O.A j ω = a j) :
    prob O.p (univ.filter cell) =
      ∑ l' ∈ univ.filter (fun l' : Fin (K + 1) → 𝓛 => ∀ j : Fin (K + 1), BL j.val → l' j = l j),
        ∑ a' ∈ univ.filter (fun a' : Fin (K + 1) → 𝓐 => ∀ j : Fin (K + 1), j.val < k → a' j = a j),
          (O.cellMoments l' a').1 := by
  set F : Ω → ((Fin (K + 1) → 𝓛) × (Fin (K + 1) → 𝓐)) :=
    fun ω => ((fun j => O.L j ω), (fun j => O.A j ω)) with hF
  have hK : ∀ j : Fin (K + 1), j.val ≤ K := by
    intro j
    have h := j.2
    omega
  have hchar : ∀ (ω : Ω) (lq : Fin (K + 1) → 𝓛) (aq : Fin (K + 1) → 𝓐),
      (F ω = (lq, aq) ↔ (∀ j, O.L j ω = lq j) ∧ ∀ j, O.A j ω = aq j) := by
    intro ω lq aq
    simp only [hF, Prod.mk.injEq, funext_iff]
  have hmaps : ∀ ω ∈ univ.filter cell,
      F ω ∈ (univ.filter (fun l' : Fin (K + 1) → 𝓛 => ∀ j : Fin (K + 1), BL j.val → l' j = l j)) ×ˢ
        (univ.filter (fun a' : Fin (K + 1) → 𝓐 => ∀ j : Fin (K + 1), j.val < k → a' j = a j)) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    rw [hcell ω] at hω
    rw [Finset.mem_product]
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hω
  have hfiber : ∀ (lq : Fin (K + 1) → 𝓛) (aq : Fin (K + 1) → 𝓐),
      (∀ j : Fin (K + 1), BL j.val → lq j = l j) →
      (∀ j : Fin (K + 1), j.val < k → aq j = a j) →
      (univ.filter cell).filter (fun ω => F ω = (lq, aq)) =
        univ.filter (O.HistT K lq aq) := by
    intro lq aq hlag haag
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hchar ω lq aq, hcell ω, O.histT_iff]
    constructor
    · rintro ⟨⟨hHL, hHA⟩, hFL, hFA⟩
      exact ⟨fun j _ => hFL j, fun j _ => hFA j⟩
    · rintro ⟨hTL, hTA⟩
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · intro j hjk
        rw [hTL j (hK j), hlag j hjk]
      · intro j hjk
        rw [hTA j (hK j), haag j hjk]
      · intro j
        exact hTL j (hK j)
      · intro j
        exact hTA j (hK j)
  show (∑ ω ∈ univ.filter cell, O.p ω) =
      ∑ l' ∈ univ.filter (fun l' : Fin (K + 1) → 𝓛 => ∀ j : Fin (K + 1), BL j.val → l' j = l j),
        ∑ a' ∈ univ.filter (fun a' : Fin (K + 1) → 𝓐 => ∀ j : Fin (K + 1), j.val < k → a' j = a j),
          (O.cellMoments l' a').1
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter cell) (g := F)
    (t := (univ.filter (fun l' : Fin (K + 1) → 𝓛 => ∀ j : Fin (K + 1), BL j.val → l' j = l j)) ×ˢ
      (univ.filter (fun a' : Fin (K + 1) → 𝓐 => ∀ j : Fin (K + 1), j.val < k → a' j = a j)))
    hmaps (fun ω => O.p ω)]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun lq hlq => Finset.sum_congr rfl fun aq haq => ?_
  show (∑ ω ∈ (univ.filter cell).filter (fun ω => F ω = (lq, aq)), O.p ω) =
    (O.cellMoments lq aq).1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlq haq
  have hfin : (O.cellMoments lq aq).1 = ∑ ω ∈ univ.filter (O.HistT K lq aq), O.p ω := rfl
  rw [hfiber lq aq hlq haq, hfin]

open Classical in
/-- The probability of the history event `{L̄_k = l̄_k, Ā_{k-1} = ā_{k-1}}` is the sum of the
cell masses of `cellMoments` over the full histories extending it. -/
theorem prob_hist_eq_sum_cellMoments {Ω 𝓛 𝓐 : Type*} {K : ℕ} [Fintype Ω] [Fintype 𝓛]
    [Fintype 𝓐] (O : ObsModel Ω 𝓛 𝓐 K) (k : ℕ) (l : Fin (K + 1) → 𝓛)
    (a : Fin (K + 1) → 𝓐) :
    prob O.p (univ.filter (O.Hist k l a)) =
      ∑ l' ∈ univ.filter (fun l' : Fin (K + 1) → 𝓛 => ∀ j : Fin (K + 1), j.val ≤ k → l' j = l j),
        ∑ a' ∈ univ.filter (fun a' : Fin (K + 1) → 𝓐 => ∀ j : Fin (K + 1), j.val < k → a' j = a j),
          (O.cellMoments l' a').1 := by
  exact gf_aux_prob_cell_eq_sum_cellMoments O k l a (fun n => n ≤ k) (O.Hist k l a)
    (fun ω => O.hist_iff k l a ω)

open Classical in
/-- The probability of the history event `{L̄_{k-1} = l̄_{k-1}, Ā_{k-1} = ā_{k-1}}` is the sum
of the cell masses of `cellMoments` over the full histories extending it. -/
theorem prob_pre_eq_sum_cellMoments {Ω 𝓛 𝓐 : Type*} {K : ℕ} [Fintype Ω] [Fintype 𝓛]
    [Fintype 𝓐] (O : ObsModel Ω 𝓛 𝓐 K) (k : ℕ) (l : Fin (K + 1) → 𝓛)
    (a : Fin (K + 1) → 𝓐) :
    prob O.p (univ.filter (O.Pre k l a)) =
      ∑ l' ∈ univ.filter (fun l' : Fin (K + 1) → 𝓛 => ∀ j : Fin (K + 1), j.val < k → l' j = l j),
        ∑ a' ∈ univ.filter (fun a' : Fin (K + 1) → 𝓐 => ∀ j : Fin (K + 1), j.val < k → a' j = a j),
          (O.cellMoments l' a').1 := by
  exact gf_aux_prob_cell_eq_sum_cellMoments O k l a (fun n => n < k) (O.Pre k l a)
    (fun ω => O.pre_iff k l a ω)

end ObsModel

open Classical in
/-- The g-formula as a function of the cell moments alone: the display of `ObsModel.gFormula`
with every cell probability and conditional mean read from the moments `q` instead of
from a study. -/
noncomputable def gFormulaOfMoments {𝓛 𝓐 : Type*} {K : ℕ} [Fintype 𝓛] [Fintype 𝓐]
    (q : (Fin (K + 1) → 𝓛) → (Fin (K + 1) → 𝓐) → ℝ × ℝ) (a : Fin (K + 1) → 𝓐) : ℝ :=
  ∑ l : Fin (K + 1) → 𝓛, ((q l a).2 / (q l a).1) * ∏ k : Fin (K + 1),
    (∑ l' ∈ univ.filter (fun l' : Fin (K + 1) → 𝓛 => ∀ j : Fin (K + 1), j.val ≤ k.val → l' j = l j),
        ∑ a' ∈ univ.filter (fun a' : Fin (K + 1) → 𝓐 =>
          ∀ j : Fin (K + 1), j.val < k.val → a' j = a j),
          (q l' a').1) /
    (∑ l' ∈ univ.filter (fun l' : Fin (K + 1) → 𝓛 => ∀ j : Fin (K + 1), j.val < k.val → l' j = l j),
        ∑ a' ∈ univ.filter (fun a' : Fin (K + 1) → 𝓐 =>
          ∀ j : Fin (K + 1), j.val < k.val → a' j = a j),
          (q l' a').1)

/-- **The g-formula factors through the cell moments**: `O.gFormula a` depends on the study
only through `O.cellMoments`, and hence, by `ObsModel.cellMoments_eq_of_observedLaw_eq`,
only through the observed joint law. -/
theorem ObsModel.gFormula_eq_gFormulaOfMoments {Ω 𝓛 𝓐 : Type*} {K : ℕ} [Fintype Ω] [Fintype 𝓛]
    [Fintype 𝓐] (O : ObsModel Ω 𝓛 𝓐 K) (a : Fin (K + 1) → 𝓐) :
    O.gFormula a = gFormulaOfMoments O.cellMoments a := by
  unfold ObsModel.gFormula gFormulaOfMoments
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun k _ => by
    have hk : (↑k : ℕ) = k.val := rfl
    unfold ObsModel.condL
    rw [hk, ObsModel.prob_hist_eq_sum_cellMoments, ObsModel.prob_pre_eq_sum_cellMoments]

/-- **Identification of `E[Y^ā]`**: on the class of models with nonnegative weights summing to
`1` that satisfy consistency, positivity and static sequential exchangeability for the plan
`ā`, the counterfactual mean is a function of the observed joint law (`ObsModel.observedLaw`)
(`IdentifiedOn`, Pearl 2009, Definition 3.2.3), namely the g-formula, which factors through
the cell moments of that law (`gFormulaOfMoments`). -/
theorem identifiedOn_expectation_Ycf [Fintype Ω] [Finite 𝓛] [Finite 𝓐] (a : Fin (K + 1) → 𝓐) :
    IdentifiedOn {M : POModel Ω 𝓛 𝓐 K | (∀ ω, 0 ≤ M.p ω) ∧ ∑ ω, M.p ω = 1 ∧ M.Consistent a ∧
        M.Positive a ∧ M.SeqExch a}
      (fun M => M.toObsModel.observedLaw) (fun M => expectation M.p (M.Ycf a)) := by
  intro M hM M1 hM1 h
  have := Fintype.ofFinite 𝓛
  have := Fintype.ofFinite 𝓐
  have hcell : M.toObsModel.cellMoments = M1.toObsModel.cellMoments :=
    ObsModel.cellMoments_eq_of_observedLaw_eq h
  have e1 := expectation_Ycf_eq_gFormula M a hM.1 hM.2.1 hM.2.2.1 hM.2.2.2.1 hM.2.2.2.2
  have e2 := expectation_Ycf_eq_gFormula M1 a hM1.1 hM1.2.1 hM1.2.2.1 hM1.2.2.2.1 hM1.2.2.2.2
  have g1 := ObsModel.gFormula_eq_gFormulaOfMoments M.toObsModel a
  have g2 := ObsModel.gFormula_eq_gFormulaOfMoments M1.toObsModel a
  show expectation M.p (M.Ycf a) = expectation M1.p (M1.Ycf a)
  rw [e1, e2, g1, g2, hcell]

/-! ### Positivity cannot be dropped -/

/-- The static plan "always treat" for two time points. -/
def tt : Fin 2 → Bool := fun _ => true

/-- The positivity counterexample on `Ω = A₀ × L₁ × A₁` (Booleans), with `L₀` constant:
`A₀ ~ Bern(1/2)`; `L₁ ~ Bern(1/2)` independent of `A₀`; `A₁ = L₁` when `A₀ = 1` and
`A₁ ~ Bern(1/2)` otherwise; `Y = 1`. Under the plan `(1, 1)` the counterfactual outcome is `c`
on `{L₁ = 0}`, the stratum in which nobody follows the plan, and `1` elsewhere; the null points
with `Ā = (1, 1)` and `L₁ = 0` are excluded so that consistency also holds pointwise. Every
other plan has counterfactual outcome `1`. -/
noncomputable def cxModel (c : ℝ) : POModel (Bool × Bool × Bool) Bool Bool 1 where
  p ω := if ω.1 then (if ω.2.2 = ω.2.1 then 1 / 4 else 0) else 1 / 8
  L k ω := if k = 0 then false else ω.2.1
  A k ω := if k = 0 then ω.1 else ω.2.2
  Y _ := 1
  Ycf a ω := if a = tt ∧ ω.2.1 = false ∧ ¬(ω.1 = true ∧ ω.2.2 = true) then c else 1

/-- The observed part of the counterexample does not depend on `c`. -/
theorem cxModel_toObsModel (c c' : ℝ) : (cxModel c).toObsModel = (cxModel c').toObsModel := rfl

theorem cxModel_nonneg (c : ℝ) : ∀ ω, 0 ≤ (cxModel c).p ω := by
  rintro ⟨a0, l1, a1⟩
  cases a0 <;> cases l1 <;> cases a1 <;> norm_num [cxModel]

theorem cxModel_sum (c : ℝ) : ∑ ω, (cxModel c).p ω = 1 := by
  simp [cxModel, Fintype.sum_prod_type]
  norm_num

/-- The counterfactual mean under "always treat" is `1 / 2 + c / 2`. -/
theorem cxModel_expectation (c : ℝ) :
    expectation (cxModel c).p ((cxModel c).Ycf tt) = 1 / 2 + c / 2 := by
  simp [expectation, cxModel, Fintype.sum_prod_type]
  ring

theorem cxModel_consistent (c : ℝ) (a : Fin 2 → Bool) : (cxModel c).Consistent a := by
  rintro ⟨a0, l1, a1⟩ hp hA
  have h0 := hA 0
  have h1 := hA 1
  cases a0 <;> cases l1 <;> cases a1 <;> simp_all [cxModel, tt, funext_iff, Fin.forall_fin_two]

/-- Positivity fails at time `1` on the history `A₀ = 1, L₁ = 0`. -/
theorem cxModel_not_positive (c : ℝ) : ¬ (cxModel c).Positive tt := by
  intro h
  have := h 1 (fun _ => false)
  apply this
  · simp [prob, cxModel, Fintype.sum_prod_type, Finset.sum_filter, Fin.forall_fin_two, tt]
  · simp [prob, cxModel, Fintype.sum_prod_type, Finset.sum_filter, Fin.forall_fin_two, tt]

theorem cxModel_seqExch (c : ℝ) : (cxModel c).SeqExch tt := by
  intro k l y b
  fin_cases k <;> cases h0 : l 0 <;> cases h1 : l 1 <;> cases b <;>
    simp [prob, cxModel, Fintype.sum_prod_type, Finset.sum_filter, Fin.forall_fin_two, tt, h0,
      h1] <;>
    by_cases hy1 : (1 : ℝ) = y <;> by_cases hyc : c = y <;> simp [hy1, hyc] <;> ring_nf

/-- **Positivity cannot be dropped**: on the class with consistency and static sequential
exchangeability but not positivity, `E[Y^{(1,1)}]` is not identified even from the whole
observed part `(p, L, A, Y)`; in particular no functional of the observed data, the g-formula
included, equals it on the whole class. -/
theorem not_identifiedOn_without_positivity :
    ¬ IdentifiedOn {M : POModel (Bool × Bool × Bool) Bool Bool 1 |
        (∀ ω, 0 ≤ M.p ω) ∧ ∑ ω, M.p ω = 1 ∧ M.Consistent tt ∧ M.SeqExch tt}
      POModel.toObsModel (fun M => expectation M.p (M.Ycf tt)) := by
  intro h
  have := h (cxModel 0)
    ⟨cxModel_nonneg 0, cxModel_sum 0, cxModel_consistent 0 tt, cxModel_seqExch 0⟩
    (cxModel 1) ⟨cxModel_nonneg 1, cxModel_sum 1, cxModel_consistent 1 tt, cxModel_seqExch 1⟩
    (cxModel_toObsModel 0 1)
  simp only [cxModel_expectation] at this
  norm_num at this

/-! ### Agreement with the truncated factorization -/

/-- The node of the covariate `L_k` in the time-ordered layout `L₀, A₀, L₁, A₁, …, L_K, A_K, Y`
of a Bayesian network with `2 * K + 3` nodes. -/
def lNode (K : ℕ) (k : Fin (K + 1)) : Fin (2 * K + 3) := ⟨2 * k.val, by have := k.isLt; omega⟩

/-- The node of the treatment `A_k` in the time-ordered layout. -/
def aNode (K : ℕ) (k : Fin (K + 1)) : Fin (2 * K + 3) := ⟨2 * k.val + 1, by have := k.isLt; omega⟩

/-- The node of the outcome `Y`, the last node of the time-ordered layout. -/
def yNode (K : ℕ) : Fin (2 * K + 3) := ⟨2 * K + 2, by omega⟩

/-- The treatment nodes `A₀, …, A_K`, the nodes that the intervention `do(Ā = ā)` sets. -/
def treatNodes (K : ℕ) : Finset (Fin (2 * K + 3)) := univ.image (aNode K)

/-- The intervention values of the plan `ā` on the layout: node `j` gets `ā (min (j / 2) K)`, so
the treatment node `2k + 1` gets `ā k`; the values on the other nodes are never read. -/
def planVec {α : Type*} (K : ℕ) (a : Fin (K + 1) → α) : Fin (2 * K + 3) → α :=
  fun j => a ⟨min (j.val / 2) K, by omega⟩

/-- The observed part of a Bayesian network `b` on the time-ordered layout: the population is
the set of configurations `Fin (2 * K + 3) → α` weighted by the joint law of `b`, the covariate
and the treatment at time `k` are the values of the nodes `2k` and `2k + 1`, and the outcome is
`f` applied to the value of the last node. -/
noncomputable def _root_.Cslib.MachineLearning.GraphicalModels.BayesNet.toObsModel
    {α : Type*} [Nonempty α] (b : BayesNet α (2 * K + 3)) (f : α → ℝ) :
    ObsModel (Fin (2 * K + 3) → α) α α K where
  p := b.joint
  L k x := x (lNode K k)
  A k x := x (aNode K k)
  Y x := f (x (yNode K))

/-- Summing a function of the first `k` variables against the joint of `n ≥ k` variables of a
chain gives the sum against the joint of the first `k` variables. A local copy of the private
marginalization lemma of `CausalBayesNet.lean`, for the proof of
`gFormula_toObsModel_eq_mutilateSet`. -/
private theorem gf_aux_chain_sum_mul_joint_castLE {α : Type*} [Fintype α] (c : Chain α) {k : ℕ}
    (g : (Fin k → α) → ℝ) (n : ℕ) (h : k ≤ n) :
    ∑ x : Fin n → α, g (fun j => x (Fin.castLE h j)) * c.joint n x =
      ∑ y : Fin k → α, g y * c.joint k y := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    rw [sum_snoc]
    have hc : ∀ (y : Fin n → α) (a : α),
        (fun j : Fin k => (Fin.snoc y a : Fin (n + 1) → α) (Fin.castLE (hkn.trans n.le_succ) j)) =
          fun j => y (Fin.castLE hkn j) := by
      intro y a; funext j
      have : Fin.castLE (hkn.trans n.le_succ) j = Fin.castSucc (Fin.castLE hkn j) := Fin.ext rfl
      rw [this, Fin.snoc_castSucc]
    simp_rw [hc, Chain.joint_snoc, ← mul_assoc, ← mul_sum, (c.cond n _).total_of_fintype,
      mul_one]
    exact ih

private noncomputable def gf_aux_val {α : Type*} (K : ℕ) (l a : Fin (K + 1) → α) (y : α) :
    Fin (2 * K + 3) → α :=
  fun j => if _h : j.val < 2 * K + 2 then
    (if j.val % 2 = 0 then l ⟨j.val / 2, by omega⟩ else a ⟨j.val / 2, by omega⟩)
    else y

private noncomputable def gf_aux_pre {α : Type*} [Nonempty α] (K : ℕ) (l a : Fin (K + 1) → α)
    (m : ℕ) : Fin m → α :=
  fun j => if h : j.val / 2 < K + 1 then
    (if j.val % 2 = 0 then l ⟨j.val / 2, h⟩ else a ⟨j.val / 2, h⟩)
    else Classical.arbitrary α

private theorem gf_aux_O_p {α : Type*} [Nonempty α] (K : ℕ) (b : BayesNet α (2 * K + 3))
    (f : α → ℝ) : (b.toObsModel f).p = b.joint := rfl

private theorem gf_aux_O_L {α : Type*} [Nonempty α] (K : ℕ) (b : BayesNet α (2 * K + 3))
    (f : α → ℝ) (k : Fin (K + 1)) (x : Fin (2 * K + 3) → α) :
    (b.toObsModel f).L k x = x (lNode K k) := rfl

private theorem gf_aux_O_A {α : Type*} [Nonempty α] (K : ℕ) (b : BayesNet α (2 * K + 3))
    (f : α → ℝ) (k : Fin (K + 1)) (x : Fin (2 * K + 3) → α) :
    (b.toObsModel f).A k x = x (aNode K k) := rfl

private theorem gf_aux_O_Y {α : Type*} [Nonempty α] (K : ℕ) (b : BayesNet α (2 * K + 3))
    (f : α → ℝ) (x : Fin (2 * K + 3) → α) :
    (b.toObsModel f).Y x = f (x (yNode K)) := rfl

private theorem gf_aux_val_even {α : Type*} (K : ℕ) (l a : Fin (K + 1) → α) (y : α)
    (j : Fin (2 * K + 3)) (hj : j.val < 2 * K + 2) (he : j.val % 2 = 0) :
    gf_aux_val K l a y j = l ⟨j.val / 2, by omega⟩ := by
  simp only [gf_aux_val, dite_eq_left hj, ite_eq_left he]

private theorem gf_aux_val_odd {α : Type*} (K : ℕ) (l a : Fin (K + 1) → α) (y : α)
    (j : Fin (2 * K + 3)) (hj : j.val < 2 * K + 2) (he : ¬ j.val % 2 = 0) :
    gf_aux_val K l a y j = a ⟨j.val / 2, by omega⟩ := by
  simp only [gf_aux_val, dite_eq_left hj, ite_eq_right he]

private theorem gf_aux_pre_even {α : Type*} [Nonempty α] (K : ℕ) (l a : Fin (K + 1) → α)
    (m : ℕ) (j : Fin m) (hlt : j.val / 2 < K + 1) (he : j.val % 2 = 0) :
    gf_aux_pre K l a m j = l ⟨j.val / 2, hlt⟩ := by
  simp only [gf_aux_pre, dite_eq_left hlt, ite_eq_left he]

private theorem gf_aux_pre_odd {α : Type*} [Nonempty α] (K : ℕ) (l a : Fin (K + 1) → α)
    (m : ℕ) (j : Fin m) (hlt : j.val / 2 < K + 1) (he : ¬ j.val % 2 = 0) :
    gf_aux_pre K l a m j = a ⟨j.val / 2, hlt⟩ := by
  simp only [gf_aux_pre, dite_eq_left hlt, ite_eq_right he]

private theorem gf_aux_val_lNode {α : Type*} (K : ℕ) (l a : Fin (K + 1) → α) (y : α)
    (k : Fin (K + 1)) : gf_aux_val K l a y (lNode K k) = l k := by
  have hv : (lNode K k).val = 2 * k.val := rfl
  have hk := k.isLt
  have hlt : (lNode K k).val < 2 * K + 2 := by omega
  have hev : (lNode K k).val % 2 = 0 := by omega
  rw [gf_aux_val_even K l a y _ hlt hev]
  congr 1
  apply Fin.ext
  show (lNode K k).val / 2 = k.val
  omega

private theorem gf_aux_val_aNode {α : Type*} (K : ℕ) (l a : Fin (K + 1) → α) (y : α)
    (k : Fin (K + 1)) : gf_aux_val K l a y (aNode K k) = a k := by
  have hv : (aNode K k).val = 2 * k.val + 1 := rfl
  have hk := k.isLt
  have hlt : (aNode K k).val < 2 * K + 2 := by omega
  have hev : ¬ (aNode K k).val % 2 = 0 := by omega
  rw [gf_aux_val_odd K l a y _ hlt hev]
  congr 1
  apply Fin.ext
  show (aNode K k).val / 2 = k.val
  omega

private theorem gf_aux_val_yNode {α : Type*} (K : ℕ) (l a : Fin (K + 1) → α) (y : α) :
    gf_aux_val K l a y (yNode K) = y := by
  have hv : (yNode K).val = 2 * K + 2 := rfl
  simp only [gf_aux_val, dite_eq_right (by omega : ¬ (yNode K).val < 2 * K + 2)]

private theorem gf_aux_plan_aNode {α : Type*} (K : ℕ) (a : Fin (K + 1) → α)
    (k : Fin (K + 1)) : planVec K a (aNode K k) = a k := by
  have hv : (aNode K k).val = 2 * k.val + 1 := rfl
  have hk := k.isLt
  simp only [planVec]
  congr 1
  apply Fin.ext
  show min ((aNode K k).val / 2) K = k.val
  omega

private theorem gf_aux_mem_treat (K : ℕ) (j : Fin (2 * K + 3)) :
    j ∈ treatNodes K ↔ ∃ k : Fin (K + 1), aNode K k = j := by
  simp [treatNodes]

private theorem gf_aux_aNode_mem (K : ℕ) (k : Fin (K + 1)) : aNode K k ∈ treatNodes K := by
  simp [treatNodes]

private theorem gf_aux_lNode_not_mem (K : ℕ) (k : Fin (K + 1)) :
    lNode K k ∉ treatNodes K := by
  rw [gf_aux_mem_treat]
  rintro ⟨k', hk'⟩
  have hv1 : (aNode K k').val = 2 * k'.val + 1 := rfl
  have hv2 : (lNode K k).val = 2 * k.val := rfl
  have h := congrArg Fin.val hk'
  omega

private theorem gf_aux_yNode_not_mem (K : ℕ) : yNode K ∉ treatNodes K := by
  rw [gf_aux_mem_treat]
  rintro ⟨k', hk'⟩
  have hv1 : (aNode K k').val = 2 * k'.val + 1 := rfl
  have hv2 : (yNode K).val = 2 * K + 2 := rfl
  have h := congrArg Fin.val hk'
  omega

private theorem gf_aux_lNode_ne_yNode (K : ℕ) (k : Fin (K + 1)) : lNode K k ≠ yNode K := by
  intro h
  have hv1 : (lNode K k).val = 2 * k.val := rfl
  have hv2 : (yNode K).val = 2 * K + 2 := rfl
  have hk := k.isLt
  have h2 := congrArg Fin.val h
  omega

private theorem gf_aux_lNode_inj (K : ℕ) {k1 k2 : Fin (K + 1)}
    (h : lNode K k1 = lNode K k2) : k1 = k2 := by
  have hv1 : (lNode K k1).val = 2 * k1.val := rfl
  have hv2 : (lNode K k2).val = 2 * k2.val := rfl
  have h2 := congrArg Fin.val h
  have hv : k1.val = k2.val := by omega
  exact Fin.ext hv

private theorem gf_aux_pre_last_L {α : Type*} [Nonempty α] (K : ℕ) (l a : Fin (K + 1) → α)
    (k : Fin (K + 1)) :
    gf_aux_pre K l a (2 * k.val + 1) (Fin.last (2 * k.val)) = l k := by
  have hk := k.isLt
  have hv : (Fin.last (2 * k.val)).val = 2 * k.val := rfl
  have hlt : (Fin.last (2 * k.val)).val / 2 < K + 1 := by omega
  have hev : (Fin.last (2 * k.val)).val % 2 = 0 := by omega
  have hp := gf_aux_pre_even K l a (2 * k.val + 1) _ hlt hev
  rw [hp]
  congr 1
  apply Fin.ext
  have hmk : (⟨(Fin.last (2 * k.val)).val / 2, hlt⟩ : Fin (K + 1)).val =
    (Fin.last (2 * k.val)).val / 2 := rfl
  omega

private theorem gf_aux_pre_last_A {α : Type*} [Nonempty α] (K : ℕ) (l a : Fin (K + 1) → α)
    (k : Fin (K + 1)) :
    gf_aux_pre K l a (2 * k.val + 2) (Fin.last (2 * k.val + 1)) = a k := by
  have hk := k.isLt
  have hv : (Fin.last (2 * k.val + 1)).val = 2 * k.val + 1 := rfl
  have hlt : (Fin.last (2 * k.val + 1)).val / 2 < K + 1 := by omega
  have hev : ¬ (Fin.last (2 * k.val + 1)).val % 2 = 0 := by omega
  have hp := gf_aux_pre_odd K l a (2 * k.val + 2) _ hlt hev
  rw [hp]
  congr 1
  apply Fin.ext
  have hmk : (⟨(Fin.last (2 * k.val + 1)).val / 2, hlt⟩ : Fin (K + 1)).val =
    (Fin.last (2 * k.val + 1)).val / 2 := rfl
  omega

private theorem gf_aux_pred_iff_pre {α : Type*} [Nonempty α] (K : ℕ) (l a : Fin (K + 1) → α)
    (m : ℕ) (hm : m ≤ 2 * K + 2) (hm3 : m ≤ 2 * K + 3)
    (x : Fin (2 * K + 3) → α) :
    ((∀ j : Fin (K + 1), j.val < (m + 1) / 2 → x (lNode K j) = l j) ∧
      (∀ j : Fin (K + 1), j.val < m / 2 → x (aNode K j) = a j)) ↔
      (fun j : Fin m => x (Fin.castLE hm3 j)) = gf_aux_pre K l a m := by
  constructor
  · intro hH
    funext j
    show x (Fin.castLE hm3 j) = gf_aux_pre K l a m j
    have hj := j.isLt
    by_cases he : j.val % 2 = 0
    · have h2 : 2 * (j.val / 2) = j.val := by omega
      have hlt : j.val / 2 < (m + 1) / 2 := by omega
      have hK : j.val / 2 < K + 1 := by omega
      have h1 := hH.1 ⟨j.val / 2, hK⟩ hlt
      have hcast : Fin.castLE hm3 j = lNode K ⟨j.val / 2, hK⟩ := by
        apply Fin.ext
        have hc : (Fin.castLE hm3 j).val = j.val := rfl
        have hv : (lNode K ⟨j.val / 2, hK⟩).val = 2 * (j.val / 2) := rfl
        omega
      rw [hcast, h1]
      have hp := gf_aux_pre_even K l a m j hK he
      exact hp.symm
    · have h2 : 2 * (j.val / 2) + 1 = j.val := by omega
      have hlt : j.val / 2 < m / 2 := by omega
      have hK : j.val / 2 < K + 1 := by omega
      have h1 := hH.2 ⟨j.val / 2, hK⟩ hlt
      have hcast : Fin.castLE hm3 j = aNode K ⟨j.val / 2, hK⟩ := by
        apply Fin.ext
        have hc : (Fin.castLE hm3 j).val = j.val := rfl
        have hv : (aNode K ⟨j.val / 2, hK⟩).val = 2 * (j.val / 2) + 1 := rfl
        omega
      rw [hcast, h1]
      have hp := gf_aux_pre_odd K l a m j hK he
      exact hp.symm
  · intro hP
    constructor
    · intro j hjL
      have h2m : 2 * j.val < m := by omega
      have hjK := j.isLt
      have hcast : lNode K j = Fin.castLE hm3 ⟨2 * j.val, h2m⟩ := by
        apply Fin.ext
        have hv : (lNode K j).val = 2 * j.val := rfl
        have hv2 : (Fin.castLE hm3 ⟨2 * j.val, h2m⟩).val = 2 * j.val := rfl
        omega
      have h2 : x (Fin.castLE hm3 ⟨2 * j.val, h2m⟩) =
          gf_aux_pre K l a m ⟨2 * j.val, h2m⟩ := congrFun hP _
      rw [hcast, h2]
      have hv : (⟨2 * j.val, h2m⟩ : Fin m).val = 2 * j.val := rfl
      have hp := gf_aux_pre_even K l a m ⟨2 * j.val, h2m⟩ (by omega) (by omega)
      rw [hp]
      congr 1
      apply Fin.ext
      show (⟨2 * j.val, h2m⟩ : Fin m).val / 2 = j.val
      omega
    · intro j hjA
      have h2m : 2 * j.val + 1 < m := by omega
      have hjK := j.isLt
      have hcast : aNode K j = Fin.castLE hm3 ⟨2 * j.val + 1, h2m⟩ := by
        apply Fin.ext
        have hv : (aNode K j).val = 2 * j.val + 1 := rfl
        have hv2 : (Fin.castLE hm3 ⟨2 * j.val + 1, h2m⟩).val = 2 * j.val + 1 := rfl
        omega
      have h2 : x (Fin.castLE hm3 ⟨2 * j.val + 1, h2m⟩) =
          gf_aux_pre K l a m ⟨2 * j.val + 1, h2m⟩ := congrFun hP _
      rw [hcast, h2]
      have hv : (⟨2 * j.val + 1, h2m⟩ : Fin m).val = 2 * j.val + 1 := rfl
      have hp := gf_aux_pre_odd K l a m ⟨2 * j.val + 1, h2m⟩ (by omega) (by omega)
      rw [hp]
      congr 1
      apply Fin.ext
      show (⟨2 * j.val + 1, h2m⟩ : Fin m).val / 2 = j.val
      omega

private theorem gf_aux_prob_eq_joint {α : Type*} [Fintype α] [Nonempty α] (K : ℕ)
    (b : BayesNet α (2 * K + 3))
    (m : ℕ) (hm : m ≤ 2 * K + 3) (q : Fin m → α) (P : (Fin (2 * K + 3) → α) → Prop)
    [DecidablePred P] (hP : ∀ x, P x ↔ (fun j => x (Fin.castLE hm j)) = q) :
    prob b.joint (univ.filter P) = b.toChain.joint m q := by
  classical
  unfold prob
  rw [Finset.sum_filter]
  have hmain := gf_aux_chain_sum_mul_joint_castLE (b.toChain)
    (fun y : Fin m → α => if y = q then (1 : ℝ) else 0) (2 * K + 3) hm
  simp only [BayesNet.joint] at hmain ⊢
  have h2 : (∑ x ∈ (univ : Finset (Fin (2 * K + 3) → α)),
      (if P x then b.toChain.joint (2 * K + 3) x else (0 : ℝ))) =
      (∑ x ∈ (univ : Finset (Fin (2 * K + 3) → α)),
        (if (fun j => x (Fin.castLE hm j)) = q then (1 : ℝ) else 0) *
          b.toChain.joint (2 * K + 3) x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : P x
    · rw [ite_eq_left hx, ite_eq_left ((hP x).mp hx), one_mul]
    · rw [ite_eq_right hx, ite_eq_right (fun h => hx ((hP x).mpr h)), zero_mul]
  rw [h2]
  have h3 : (∑ x ∈ (univ : Finset (Fin (2 * K + 3) → α)),
      (if (fun j => x (Fin.castLE hm j)) = q then (1 : ℝ) else 0) *
        b.toChain.joint (2 * K + 3) x) =
      ∑ x : Fin (2 * K + 3) → α,
        (if (fun j => x (Fin.castLE hm j)) = q then (1 : ℝ) else 0) *
          b.toChain.joint (2 * K + 3) x := rfl
  rw [h3, hmain]
  rw [Fintype.sum_eq_single q (fun y hyq => by rw [ite_eq_right hyq, zero_mul])]
  rw [ite_eq_left rfl, one_mul]

open Classical in
private theorem gf_aux_mass_pre {α : Type*} [Fintype α] [Nonempty α] (K : ℕ)
    (b : BayesNet α (2 * K + 3)) (f : α → ℝ) (l a : Fin (K + 1) → α)
    (k : Fin (K + 1)) :
    prob (b.toObsModel f).p (univ.filter ((b.toObsModel f).Pre k.val l a)) =
      b.toChain.joint (2 * k.val) (gf_aux_pre K l a (2 * k.val)) := by
  classical
  have hk := k.isLt
  have hm : 2 * k.val ≤ 2 * K + 2 := by omega
  have hm3 : 2 * k.val ≤ 2 * K + 3 := by omega
  have e1 : (2 * k.val + 1) / 2 = k.val := by omega
  have e2 : (2 * k.val) / 2 = k.val := by omega
  rw [gf_aux_O_p]
  apply gf_aux_prob_eq_joint K b (2 * k.val) hm3 _ _
  intro x
  rw [ObsModel.pre_iff]
  have h := gf_aux_pred_iff_pre K l a (2 * k.val) hm hm3 x
  simp only [e1, e2] at h
  exact h

open Classical in
private theorem gf_aux_mass_hist {α : Type*} [Fintype α] [Nonempty α] (K : ℕ)
    (b : BayesNet α (2 * K + 3)) (f : α → ℝ) (l a : Fin (K + 1) → α)
    (k : Fin (K + 1)) :
    prob (b.toObsModel f).p (univ.filter ((b.toObsModel f).Hist k.val l a)) =
      b.toChain.joint (2 * k.val + 1) (gf_aux_pre K l a (2 * k.val + 1)) := by
  classical
  have hk := k.isLt
  have hm : 2 * k.val + 1 ≤ 2 * K + 2 := by omega
  have hm3 : 2 * k.val + 1 ≤ 2 * K + 3 := by omega
  have e1 : (2 * k.val + 1 + 1) / 2 = k.val + 1 := by omega
  have e2 : (2 * k.val + 1) / 2 = k.val := by omega
  rw [gf_aux_O_p]
  apply gf_aux_prob_eq_joint K b (2 * k.val + 1) hm3 _ _
  intro x
  rw [ObsModel.hist_iff]
  have h := gf_aux_pred_iff_pre K l a (2 * k.val + 1) hm hm3 x
  simp only [e1, e2, Nat.lt_add_one_iff] at h
  exact h

open Classical in
private theorem gf_aux_mass_histT_fin {α : Type*} [Fintype α] [Nonempty α] (K : ℕ)
    (b : BayesNet α (2 * K + 3)) (f : α → ℝ) (l a : Fin (K + 1) → α)
    (k : Fin (K + 1)) :
    prob (b.toObsModel f).p (univ.filter ((b.toObsModel f).HistT k.val l a)) =
      b.toChain.joint (2 * k.val + 2) (gf_aux_pre K l a (2 * k.val + 2)) := by
  classical
  have hk := k.isLt
  have hm : 2 * k.val + 2 ≤ 2 * K + 2 := by omega
  have hm3 : 2 * k.val + 2 ≤ 2 * K + 3 := by omega
  have e1 : (2 * k.val + 2 + 1) / 2 = k.val + 1 := by omega
  have e2 : (2 * k.val + 2) / 2 = k.val + 1 := by omega
  rw [gf_aux_O_p]
  apply gf_aux_prob_eq_joint K b (2 * k.val + 2) hm3 _ _
  intro x
  rw [ObsModel.histT_iff]
  have h := gf_aux_pred_iff_pre K l a (2 * k.val + 2) hm hm3 x
  simp only [e1, e2, Nat.lt_add_one_iff] at h
  exact h

open Classical in
private theorem gf_aux_mass_histT_K {α : Type*} [Fintype α] [Nonempty α] (K : ℕ)
    (b : BayesNet α (2 * K + 3)) (f : α → ℝ) (l a : Fin (K + 1) → α) :
    prob (b.toObsModel f).p (univ.filter ((b.toObsModel f).HistT K l a)) =
      b.toChain.joint (2 * K + 2) (gf_aux_pre K l a (2 * K + 2)) := by
  classical
  have hm : 2 * K + 2 ≤ 2 * K + 2 := le_rfl
  have hm3 : 2 * K + 2 ≤ 2 * K + 3 := by omega
  have e1 : (2 * K + 2 + 1) / 2 = K + 1 := by omega
  have e2 : (2 * K + 2) / 2 = K + 1 := by omega
  rw [gf_aux_O_p]
  apply gf_aux_prob_eq_joint K b (2 * K + 2) hm3 _ _
  intro x
  rw [ObsModel.histT_iff]
  have h := gf_aux_pred_iff_pre K l a (2 * K + 2) hm hm3 x
  simp only [e1, e2, Nat.lt_add_one_iff] at h
  exact h

private theorem gf_aux_pre_init {α : Type*} [Nonempty α] (K : ℕ) (l a : Fin (K + 1) → α)
    (m : ℕ) : Fin.init (gf_aux_pre K l a (m + 1)) = gf_aux_pre K l a m := by
  funext j
  show gf_aux_pre K l a (m + 1) j.castSucc = gf_aux_pre K l a m j
  simp only [gf_aux_pre]
  have hv : (Fin.castSucc j).val = j.val := rfl
  rw [hv]

private theorem gf_aux_pre_snoc {α : Type*} [Nonempty α] (K : ℕ) (l a : Fin (K + 1) → α)
    (m : ℕ) : gf_aux_pre K l a (m + 1) =
      Fin.snoc (gf_aux_pre K l a m) (gf_aux_pre K l a (m + 1) (Fin.last m)) := by
  have heta := Fin.snoc_init_self (gf_aux_pre K l a (m + 1))
  rw [gf_aux_pre_init] at heta
  exact heta.symm

private theorem gf_aux_val_pre {α : Type*} [Nonempty α] (K : ℕ) (l a : Fin (K + 1) → α)
    (y : α) (m : ℕ) (hm : m ≤ 2 * K + 2) (hm3 : m ≤ 2 * K + 3) (j : Fin m) :
    gf_aux_val K l a y (Fin.castLE hm3 j) =
      gf_aux_pre K l a m j := by
  have hj := j.isLt
  have hc : (Fin.castLE hm3 j).val = j.val := rfl
  have hlt : (Fin.castLE hm3 j).val < 2 * K + 2 := by omega
  have hK : j.val / 2 < K + 1 := by omega
  by_cases he : j.val % 2 = 0
  · have he' : (Fin.castLE hm3 j).val % 2 = 0 := by omega
    have h1 := gf_aux_val_even K l a y _ hlt he'
    have h2 := gf_aux_pre_even K l a m j hK he
    rw [h1, h2]
    congr 1
  · have he' : ¬ (Fin.castLE hm3 j).val % 2 = 0 := by omega
    have h1 := gf_aux_val_odd K l a y _ hlt he'
    have h2 := gf_aux_pre_odd K l a m j hK he
    rw [h1, h2]
    congr 1

private theorem gf_aux_paVal_lNode {α : Type*} [Nonempty α] (K : ℕ) (b : BayesNet α (2 * K + 3))
    (l a : Fin (K + 1) → α) (y : α) (k : Fin (K + 1)) :
    b.paVal (lNode K k) (gf_aux_val K l a y) =
      (fun j => gf_aux_pre K l a (2 * k.val) j.val : b.pa (lNode K k) → α) := by
  funext j
  simp only [BayesNet.paVal]
  have hk := k.isLt
  have hm : 2 * k.val ≤ 2 * K + 2 := by omega
  exact gf_aux_val_pre K l a y (2 * k.val) hm _ _

private theorem gf_aux_paVal_yNode {α : Type*} [Nonempty α] (K : ℕ) (b : BayesNet α (2 * K + 3))
    (l a : Fin (K + 1) → α) (y : α) :
    b.paVal (yNode K) (gf_aux_val K l a y) =
      (fun j => gf_aux_pre K l a (2 * K + 2) j.val : b.pa (yNode K) → α) := by
  funext j
  simp only [BayesNet.paVal]
  have hm : 2 * K + 2 ≤ 2 * K + 2 := le_rfl
  exact gf_aux_val_pre K l a y (2 * K + 2) hm _ _

open Classical in
private theorem gf_aux_condL_eq_cpt {α : Type*} [Fintype α] [Nonempty α] (K : ℕ)
    (b : BayesNet α (2 * K + 3)) (f : α → ℝ) (l a : Fin (K + 1) → α)
    (k : Fin (K + 1))
    (hR : prob (b.toObsModel f).p (univ.filter ((b.toObsModel f).Pre k.val l a)) ≠ 0) :
    (b.toObsModel f).condL a l k.val =
      (b.cpt (lNode K k)
        (fun j => gf_aux_pre K l a (2 * k.val) j.val : b.pa (lNode K k) → α)).weights
        (l k) := by
  classical
  have hk := k.isLt
  have hH := gf_aux_mass_hist K b f l a k
  have hR0 := gf_aux_mass_pre K b f l a k
  have hsnoc := gf_aux_pre_snoc K l a (2 * k.val)
  have hlast := gf_aux_pre_last_L K l a k
  have hsnocL : gf_aux_pre K l a (2 * k.val + 1) =
      Fin.snoc (gf_aux_pre K l a (2 * k.val)) (l k) := by
    rw [hsnoc, hlast]
  have hR' : b.toChain.joint (2 * k.val) (gf_aux_pre K l a (2 * k.val)) ≠ 0 := by
    rw [← hR0]
    exact hR
  have hk3 : 2 * k.val < 2 * K + 3 := by omega
  have hcpt := BayesNet.cond_eq_cpt b hk3 hR' (l k)
  unfold ObsModel.condL
  rw [hH, hR0, hsnocL]
  exact hcpt

open Classical in
private theorem gf_aux_cmean_num {α : Type*} [Fintype α] [Nonempty α] (K : ℕ)
    (b : BayesNet α (2 * K + 3)) (f : α → ℝ) (l a : Fin (K + 1) → α) :
    ∑ ω ∈ univ.filter ((b.toObsModel f).HistT K l a),
        (b.toObsModel f).p ω * (b.toObsModel f).Y ω =
      b.toChain.joint (2 * K + 2) (gf_aux_pre K l a (2 * K + 2)) *
        ∑ yv : α, (b.cpt (yNode K)
          (fun j => gf_aux_pre K l a (2 * K + 2) j.val : b.pa (yNode K) → α)).weights
          yv * f yv := by
  classical
  have hm : 2 * K + 2 ≤ 2 * K + 2 := le_rfl
  have hm3 : 2 * K + 2 ≤ 2 * K + 3 := by omega
  have e1 : (2 * K + 2 + 1) / 2 = K + 1 := by omega
  have e2 : (2 * K + 2) / 2 = K + 1 := by omega
  have hP : ∀ ω : Fin (2 * K + 3) → α,
      (b.toObsModel f).HistT K l a ω ↔
        (fun j => ω (Fin.castLE hm3 j)) = gf_aux_pre K l a (2 * K + 2) := by
    intro ω
    have h := gf_aux_pred_iff_pre K l a (2 * K + 2) hm hm3 ω
    simp only [e1, e2, Nat.lt_add_one_iff] at h
    rw [ObsModel.histT_iff]
    exact h
  show (∑ ω ∈ univ.filter ((b.toObsModel f).HistT K l a),
    b.joint ω * f (ω (yNode K))) = _
  rw [Finset.sum_filter]
  have hss := sum_snoc (n := 2 * K + 2)
    (fun x : Fin (2 * K + 2 + 1) → α =>
      if (b.toObsModel f).HistT K l a (x : Fin (2 * K + 3) → α) then
        b.joint (x : Fin (2 * K + 3) → α) * f ((x : Fin (2 * K + 3) → α) (yNode K))
      else 0)
  have hss2 : (∑ ω ∈ (univ : Finset (Fin (2 * K + 3) → α)),
      (if (b.toObsModel f).HistT K l a ω then
        b.joint ω * f (ω (yNode K)) else (0 : ℝ))) =
      ∑ q' : Fin (2 * K + 2) → α, ∑ yv : α,
        (if (b.toObsModel f).HistT K l a
          ((Fin.snoc q' yv : Fin (2 * K + 2 + 1) → α) : Fin (2 * K + 3) → α) then
          b.joint ((Fin.snoc q' yv : Fin (2 * K + 2 + 1) → α) : Fin (2 * K + 3) → α) *
            f (((Fin.snoc q' yv : Fin (2 * K + 2 + 1) → α) : Fin (2 * K + 3) → α)
              (yNode K)) else (0 : ℝ)) := hss
  rw [hss2]
  have hcast : ∀ j : Fin (2 * K + 2),
      Fin.castLE hm3 j = (⟨j.val, j.isLt⟩ : Fin (2 * K + 2)).castSucc :=
    fun j => Fin.ext rfl
  have hpre_snoc : ∀ q' : Fin (2 * K + 2) → α, ∀ yv : α,
      (fun j : Fin (2 * K + 2) =>
        (((Fin.snoc q' yv : Fin (2 * K + 2 + 1) → α) : Fin (2 * K + 3) → α))
          (Fin.castLE hm3 j)) = q' := by
    intro q' yv
    funext j
    show (((Fin.snoc q' yv : Fin (2 * K + 2 + 1) → α) : Fin (2 * K + 3) → α))
      (Fin.castLE hm3 j) = q' j
    rw [hcast j, Fin.snoc_castSucc]
  have hyN : ∀ q' : Fin (2 * K + 2) → α, ∀ yv : α,
      (((Fin.snoc q' yv : Fin (2 * K + 2 + 1) → α) : Fin (2 * K + 3) → α))
        (yNode K) = yv := by
    intro q' yv
    have hyl : yNode K = Fin.last (2 * K + 2) := Fin.ext rfl
    rw [hyl]
    exact Fin.snoc_last (α := fun _ => α) yv q'
  have hJ : ∀ q' : Fin (2 * K + 2) → α, ∀ yv : α,
      b.joint ((Fin.snoc q' yv : Fin (2 * K + 2 + 1) → α) : Fin (2 * K + 3) → α) =
        b.toChain.joint (2 * K + 2) q' * (b.toChain.cond (2 * K + 2) q').weights yv :=
    fun q' yv => Chain.joint_snoc b.toChain (2 * K + 2) q' yv
  have hcond : ∀ q' : Fin (2 * K + 2) → α, b.toChain.cond (2 * K + 2) q' =
      b.cpt (yNode K) (fun j => q' j.val : b.pa (yNode K) → α) := by
    intro q'
    have hlt : 2 * K + 2 < 2 * K + 3 := by omega
    show dite (2 * K + 2 < 2 * K + 3)
      (fun hk => b.cpt ⟨2 * K + 2, hk⟩ (fun j => q' j.val)) _
      = b.cpt (yNode K) (fun j => q' j.val : b.pa (yNode K) → α)
    rw [dite_eq_left hlt]
    rfl
  have hpt : ∀ q' : Fin (2 * K + 2) → α, ∀ yv : α,
      (if (b.toObsModel f).HistT K l a
        ((Fin.snoc q' yv : Fin (2 * K + 2 + 1) → α) : Fin (2 * K + 3) → α) then
        b.joint ((Fin.snoc q' yv : Fin (2 * K + 2 + 1) → α) : Fin (2 * K + 3) → α) *
          f (((Fin.snoc q' yv : Fin (2 * K + 2 + 1) → α) : Fin (2 * K + 3) → α)
            (yNode K)) else (0 : ℝ)) =
      (if q' = gf_aux_pre K l a (2 * K + 2) then
        b.toChain.joint (2 * K + 2) (gf_aux_pre K l a (2 * K + 2)) *
          ((b.cpt (yNode K)
            (fun j => gf_aux_pre K l a (2 * K + 2) j.val : b.pa (yNode K) → α)).weights
            yv * f yv) else (0 : ℝ)) := by
    intro q' yv
    by_cases hq : q' = gf_aux_pre K l a (2 * K + 2)
    · have hpre := hpre_snoc q' yv
      have hHolds : (b.toObsModel f).HistT K l a
          ((Fin.snoc q' yv : Fin (2 * K + 2 + 1) → α) : Fin (2 * K + 3) → α) :=
        (hP _).mpr (by rw [hpre]; exact hq)
      rw [ite_eq_left hHolds, ite_eq_left hq, hJ q' yv, hyN q' yv, hcond q', hq, mul_assoc]
    · have hpre := hpre_snoc q' yv
      have hFail : ¬ (b.toObsModel f).HistT K l a
          ((Fin.snoc q' yv : Fin (2 * K + 2 + 1) → α) : Fin (2 * K + 3) → α) := by
        intro hH
        apply hq
        have h2 := (hP _).mp hH
        rw [hpre] at h2
        exact h2
      rw [ite_eq_right hFail, ite_eq_right hq]
  simp only [hpt]
  rw [Fintype.sum_eq_single _ (fun q' hq =>
    Finset.sum_eq_zero (fun yv _ => by rw [ite_eq_right hq]))]
  have hif : ∀ yv : α, (if gf_aux_pre K l a (2 * K + 2) = gf_aux_pre K l a (2 * K + 2)
      then b.toChain.joint (2 * K + 2) (gf_aux_pre K l a (2 * K + 2)) *
        ((b.cpt (yNode K)
          (fun j => gf_aux_pre K l a (2 * K + 2) j.val : b.pa (yNode K) → α)).weights
          yv * f yv) else (0 : ℝ)) =
      b.toChain.joint (2 * K + 2) (gf_aux_pre K l a (2 * K + 2)) *
        ((b.cpt (yNode K)
          (fun j => gf_aux_pre K l a (2 * K + 2) j.val : b.pa (yNode K) → α)).weights
          yv * f yv) :=
    fun yv => ite_eq_left rfl
  simp only [hif]
  have hmul := Finset.mul_sum (univ : Finset α)
    (fun yv : α => (b.cpt (yNode K)
      (fun j => gf_aux_pre K l a (2 * K + 2) j.val : b.pa (yNode K) → α)).weights
      yv * f yv)
    (b.toChain.joint (2 * K + 2) (gf_aux_pre K l a (2 * K + 2)))
  exact hmul.symm

open Classical in
private theorem gf_aux_cmean_eq {α : Type*} [Fintype α] [Nonempty α] (K : ℕ)
    (b : BayesNet α (2 * K + 3)) (f : α → ℝ) (l a : Fin (K + 1) → α)
    (hT : prob (b.toObsModel f).p (univ.filter ((b.toObsModel f).HistT K l a)) ≠ 0) :
    cmean (b.toObsModel f).p (b.toObsModel f).Y
        (univ.filter ((b.toObsModel f).HistT K l a)) =
      ∑ yv : α, (b.cpt (yNode K)
        (fun j => gf_aux_pre K l a (2 * K + 2) j.val : b.pa (yNode K) → α)).weights
        yv * f yv := by
  classical
  have hnum := gf_aux_cmean_num K b f l a
  have hTmass := gf_aux_mass_histT_K K b f l a
  have hT' : b.toChain.joint (2 * K + 2) (gf_aux_pre K l a (2 * K + 2)) ≠ 0 := by
    rw [← hTmass]
    exact hT
  unfold cmean
  rw [hnum, hTmass]
  exact mul_div_cancel_left₀ _ hT'

private theorem gf_aux_pre_last_Ln {α : Type*} [Nonempty α] (K : ℕ) (l a : Fin (K + 1) → α)
    (t : ℕ) (ht : t < K + 1) :
    gf_aux_pre K l a (2 * t + 1) (Fin.last (2 * t)) = l ⟨t, ht⟩ := by
  have hv : (Fin.last (2 * t)).val = 2 * t := rfl
  have hlt : (Fin.last (2 * t)).val / 2 < K + 1 := by omega
  have hev : (Fin.last (2 * t)).val % 2 = 0 := by omega
  have hp := gf_aux_pre_even K l a (2 * t + 1) _ hlt hev
  rw [hp]
  congr 1
  apply Fin.ext
  show (Fin.last (2 * t)).val / 2 = t
  omega

private theorem gf_aux_chase {α : Type*} [Fintype α] [Nonempty α] (K : ℕ)
    (b : BayesNet α (2 * K + 3)) (f : α → ℝ) (l a : Fin (K + 1) → α)
    (hpos : (b.toObsModel f).Positive a) (t : ℕ) (ht : t < K + 1)
    (hz : b.toChain.joint (2 * t) (gf_aux_pre K l a (2 * t)) = 0) :
    ∃ k' : Fin (K + 1), (b.cpt (lNode K k')
      (fun j => gf_aux_pre K l a (2 * k'.val) j.val : b.pa (lNode K k') → α)).weights
      (l k') = 0 := by
  classical
  have main : ∀ t : ℕ, ∀ ht : t < K + 1,
      b.toChain.joint (2 * t) (gf_aux_pre K l a (2 * t)) = 0 →
      ∃ k' : Fin (K + 1), (b.cpt (lNode K k')
        (fun j => gf_aux_pre K l a (2 * k'.val) j.val : b.pa (lNode K k') → α)).weights
        (l k') = 0 := by
    intro t
    induction t with
    | zero =>
      intro ht hz
      simp at hz
      have h1 : b.toChain.joint 0 (gf_aux_pre K l a 0) = 1 := rfl
      rw [h1] at hz
      exact absurd hz one_ne_zero
    | succ t ih =>
      intro ht hz
      have ht' : t < K + 1 := by omega
      by_cases hJ1 : b.toChain.joint (2 * t + 1) (gf_aux_pre K l a (2 * t + 1)) = 0
      · have hsnocL := gf_aux_pre_snoc K l a (2 * t)
        have hlastL := gf_aux_pre_last_Ln K l a t ht'
        rw [hlastL] at hsnocL
        have hjsL : b.toChain.joint (2 * t + 1)
            (Fin.snoc (gf_aux_pre K l a (2 * t)) (l ⟨t, ht'⟩)) =
            b.toChain.joint (2 * t) (gf_aux_pre K l a (2 * t)) *
              (b.toChain.cond (2 * t) (gf_aux_pre K l a (2 * t))).weights
                (l ⟨t, ht'⟩) :=
          Chain.joint_snoc b.toChain (2 * t) _ _
        rw [hsnocL] at hJ1
        rw [hjsL] at hJ1
        rcases mul_eq_zero.mp hJ1 with hz0 | hc0
        · exact ih ht' hz0
        · have hcondL : b.toChain.cond (2 * t) (gf_aux_pre K l a (2 * t)) =
              b.cpt (lNode K (⟨t, ht'⟩ : Fin (K + 1)))
                (fun j => gf_aux_pre K l a (2 * (⟨t, ht'⟩ : Fin (K + 1)).val) j.val :
                  b.pa (lNode K (⟨t, ht'⟩ : Fin (K + 1))) → α) := by
            have hlt : 2 * t < 2 * K + 3 := by omega
            show dite (2 * t < 2 * K + 3)
              (fun hk => b.cpt ⟨2 * t, hk⟩ (fun j => gf_aux_pre K l a (2 * t) j.val)) _
              = b.cpt (lNode K (⟨t, ht'⟩ : Fin (K + 1)))
                (fun j => gf_aux_pre K l a (2 * (⟨t, ht'⟩ : Fin (K + 1)).val) j.val :
                  b.pa (lNode K (⟨t, ht'⟩ : Fin (K + 1))) → α)
            rw [dite_eq_left hlt]
            rfl
          rw [hcondL] at hc0
          exact ⟨⟨t, ht'⟩, hc0⟩
      · have eA : 2 * (t + 1) = 2 * t + 2 := by omega
        rw [eA] at hz
        have hHne : prob (b.toObsModel f).p
            (univ.filter ((b.toObsModel f).Hist (⟨t, ht'⟩ : Fin (K + 1)).val l a)) ≠ 0 := by
          have hm := gf_aux_mass_hist K b f l a ⟨t, ht'⟩
          rw [hm]
          exact hJ1
        have hT0 : prob (b.toObsModel f).p
            (univ.filter ((b.toObsModel f).HistT (⟨t, ht'⟩ : Fin (K + 1)).val l a)) = 0 := by
          have hm := gf_aux_mass_histT_fin K b f l a ⟨t, ht'⟩
          rw [hm]
          exact hz
        exact absurd hT0 (hpos ⟨t, ht'⟩ l hHne)
  exact main t ht hz

open Classical in
private theorem gf_aux_term_eq {α : Type*} [Fintype α] [Nonempty α] (K : ℕ)
    (b : BayesNet α (2 * K + 3)) (f : α → ℝ) (l a : Fin (K + 1) → α)
    (hpos : (b.toObsModel f).Positive a) :
    cmean (b.toObsModel f).p (b.toObsModel f).Y
        (univ.filter ((b.toObsModel f).HistT K l a)) *
        ∏ k : Fin (K + 1), (b.toObsModel f).condL a l k.val =
      (∏ k : Fin (K + 1), (b.cpt (lNode K k)
        (fun j => gf_aux_pre K l a (2 * k.val) j.val : b.pa (lNode K k) → α)).weights
        (l k)) *
        (∑ yv : α, (b.cpt (yNode K)
          (fun j => gf_aux_pre K l a (2 * K + 2) j.val : b.pa (yNode K) → α)).weights
          yv * f yv) := by
  classical
  by_cases hall : ∀ k : Fin (K + 1),
      prob (b.toObsModel f).p (univ.filter ((b.toObsModel f).Pre k.val l a)) ≠ 0 ∧
      prob (b.toObsModel f).p (univ.filter ((b.toObsModel f).Hist k.val l a)) ≠ 0
  · have hKlt : K < K + 1 := Nat.lt_succ_self K
    have hHne := (hall ⟨K, hKlt⟩).2
    have hTne := hpos ⟨K, hKlt⟩ l hHne
    have hC := gf_aux_cmean_eq K b f l a hTne
    have hP : (∏ k : Fin (K + 1), (b.toObsModel f).condL a l k.val) =
        (∏ k : Fin (K + 1), (b.cpt (lNode K k)
          (fun j => gf_aux_pre K l a (2 * k.val) j.val : b.pa (lNode K k) → α)).weights
          (l k)) :=
      Finset.prod_congr rfl fun k _ => gf_aux_condL_eq_cpt K b f l a k (hall k).1
    rw [hC, hP]
    exact mul_comm _ _
  · push_neg at hall
    obtain ⟨k, hk⟩ := hall
    have hdisj : prob (b.toObsModel f).p (univ.filter ((b.toObsModel f).Pre k.val l a)) = 0 ∨
        prob (b.toObsModel f).p (univ.filter ((b.toObsModel f).Hist k.val l a)) = 0 := by
      by_cases hR : prob (b.toObsModel f).p (univ.filter ((b.toObsModel f).Pre k.val l a)) = 0
      · exact Or.inl hR
      · exact Or.inr (hk hR)
    obtain hk0 | hk0 := hdisj
    · have hcond0 : (b.toObsModel f).condL a l k.val = 0 := by
        unfold ObsModel.condL
        rw [hk0, div_zero]
      have hP0 : (∏ k : Fin (K + 1), (b.toObsModel f).condL a l k.val) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ k) hcond0
      have hJ0 : b.toChain.joint (2 * k.val) (gf_aux_pre K l a (2 * k.val)) = 0 := by
        have hm := gf_aux_mass_pre K b f l a k
        rw [← hm]
        exact hk0
      obtain ⟨k', hk'z⟩ := gf_aux_chase K b f l a hpos k.val k.isLt hJ0
      have hL0 : (∏ k : Fin (K + 1), (b.cpt (lNode K k)
          (fun j => gf_aux_pre K l a (2 * k.val) j.val : b.pa (lNode K k) → α)).weights
          (l k)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ k') hk'z
      rw [hP0, hL0, mul_zero, zero_mul]
    · have hcond0 : (b.toObsModel f).condL a l k.val = 0 := by
        unfold ObsModel.condL
        rw [hk0, zero_div]
      have hP0 : (∏ k : Fin (K + 1), (b.toObsModel f).condL a l k.val) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ k) hcond0
      have hJ1 : b.toChain.joint (2 * k.val + 1)
          (gf_aux_pre K l a (2 * k.val + 1)) = 0 := by
        have hm := gf_aux_mass_hist K b f l a k
        rw [← hm]
        exact hk0
      have hsnocL := gf_aux_pre_snoc K l a (2 * k.val)
      have hlastL := gf_aux_pre_last_L K l a k
      rw [hlastL] at hsnocL
      have hjsL : b.toChain.joint (2 * k.val + 1)
          (Fin.snoc (gf_aux_pre K l a (2 * k.val)) (l k)) =
          b.toChain.joint (2 * k.val) (gf_aux_pre K l a (2 * k.val)) *
            (b.toChain.cond (2 * k.val) (gf_aux_pre K l a (2 * k.val))).weights
              (l k) :=
        Chain.joint_snoc b.toChain (2 * k.val) _ _
      rw [hsnocL] at hJ1
      rw [hjsL] at hJ1
      have hL0 : (∏ k : Fin (K + 1), (b.cpt (lNode K k)
          (fun j => gf_aux_pre K l a (2 * k.val) j.val : b.pa (lNode K k) → α)).weights
          (l k)) = 0 := by
        rcases mul_eq_zero.mp hJ1 with hz0 | hc0
        · obtain ⟨k', hk'z⟩ := gf_aux_chase K b f l a hpos k.val k.isLt hz0
          exact Finset.prod_eq_zero (Finset.mem_univ k') hk'z
        · have hcondL : b.toChain.cond (2 * k.val) (gf_aux_pre K l a (2 * k.val)) =
              b.cpt (lNode K k)
                (fun j => gf_aux_pre K l a (2 * k.val) j.val :
                  b.pa (lNode K k) → α) := by
            have hk := k.isLt
            have hlt : 2 * k.val < 2 * K + 3 := by omega
            show dite (2 * k.val < 2 * K + 3)
              (fun hk => b.cpt ⟨2 * k.val, hk⟩
                (fun j => gf_aux_pre K l a (2 * k.val) j.val)) _
              = _
            rw [dite_eq_left hlt]
            rfl
          rw [hcondL] at hc0
          exact Finset.prod_eq_zero (Finset.mem_univ k) hc0
      rw [hP0, hL0, mul_zero, zero_mul]

private noncomputable def gf_aux_valEquiv {α : Type*} (K : ℕ) :
    ((Fin (K + 1) → α) × (Fin (K + 1) → α) × α) ≃ (Fin (2 * K + 3) → α) where
  toFun p := gf_aux_val K p.1 p.2.1 p.2.2
  invFun x := ((fun k => x (lNode K k)), ((fun k => x (aNode K k)), x (yNode K)))
  left_inv := by
    rintro ⟨l, a', y⟩
    show ((fun k => gf_aux_val K l a' y (lNode K k)),
      ((fun k => gf_aux_val K l a' y (aNode K k)), gf_aux_val K l a' y (yNode K))) =
      (l, a', y)
    refine Prod.ext (funext fun k => gf_aux_val_lNode K l a' y k)
      (Prod.ext (funext fun k => gf_aux_val_aNode K l a' y k)
        (gf_aux_val_yNode K l a' y))
  right_inv := by
    intro x
    funext j
    show gf_aux_val K (fun k => x (lNode K k)) (fun k => x (aNode K k)) (x (yNode K)) j
      = x j
    by_cases hj : j.val < 2 * K + 2
    · by_cases he : j.val % 2 = 0
      · have h2 : 2 * (j.val / 2) = j.val := by omega
        have hlt : j.val / 2 < K + 1 := by omega
        have hjnode : j = lNode K ⟨j.val / 2, hlt⟩ := by
          apply Fin.ext
          show j.val = (lNode K ⟨j.val / 2, hlt⟩).val
          have hv : (lNode K ⟨j.val / 2, hlt⟩).val = 2 * (j.val / 2) := rfl
          omega
        rw [hjnode]
        exact gf_aux_val_lNode K _ _ _ _
      · have h2 : 2 * (j.val / 2) + 1 = j.val := by omega
        have hlt : j.val / 2 < K + 1 := by omega
        have hjnode : j = aNode K ⟨j.val / 2, hlt⟩ := by
          apply Fin.ext
          show j.val = (aNode K ⟨j.val / 2, hlt⟩).val
          have hv : (aNode K ⟨j.val / 2, hlt⟩).val = 2 * (j.val / 2) + 1 := rfl
          omega
        rw [hjnode]
        exact gf_aux_val_aNode K _ _ _ _
    · have hj2 : j.val = 2 * K + 2 := by
        have hj3 := j.isLt
        omega
      have hjnode : j = yNode K := by
        apply Fin.ext
        show j.val = (yNode K).val
        have hv : (yNode K).val = 2 * K + 2 := rfl
        omega
      rw [hjnode]
      exact gf_aux_val_yNode K _ _ _

private theorem gf_aux_mut_eq_zero {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] (K : ℕ)
    (b : BayesNet α (2 * K + 3)) (f : α → ℝ) (l a' a : Fin (K + 1) → α) (y : α)
    (hne : a' ≠ a) :
    (b.mutilateSet (treatNodes K) (planVec K a)).joint
        (gf_aux_val K l a' y) * f (gf_aux_val K l a' y (yNode K)) = 0 := by
  classical
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
  have hmem := gf_aux_aNode_mem K k
  have hfactor : (if (aNode K k) ∈ treatNodes K then
      (if gf_aux_val K l a' y (aNode K k) = planVec K a (aNode K k) then (1 : ℝ) else 0)
      else (b.cpt (aNode K k) (b.paVal (aNode K k) (gf_aux_val K l a' y))).weights
        (gf_aux_val K l a' y (aNode K k))) = 0 := by
    rw [ite_eq_left hmem, gf_aux_val_aNode, gf_aux_plan_aNode]
    exact ite_eq_right hk
  have hmut0 : (b.mutilateSet (treatNodes K) (planVec K a)).joint
      (gf_aux_val K l a' y) = 0 := by
    rw [BayesNet.joint_mutilateSet]
    exact Finset.prod_eq_zero (Finset.mem_univ _) hfactor
  rw [hmut0, zero_mul]

private theorem gf_aux_filter_compl (K : ℕ) :
    univ.filter (fun j : Fin (2 * K + 3) => j ∉ treatNodes K) =
      univ.image (lNode K) ∪ {yNode K} := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_image, Finset.mem_singleton]
  constructor
  · intro hjW
    by_cases hjy : j = yNode K
    · exact Or.inr hjy
    · left
      by_cases hjb : j.val < 2 * K + 2
      · by_cases he : j.val % 2 = 0
        · refine ⟨⟨j.val / 2, by omega⟩, ?_⟩
          show lNode K ⟨j.val / 2, by omega⟩ = j
          apply Fin.ext
          show (lNode K ⟨j.val / 2, by omega⟩).val = j.val
          have hv : (lNode K ⟨j.val / 2, by omega⟩).val = 2 * (j.val / 2) := rfl
          omega
        · exfalso
          apply hjW
          rw [gf_aux_mem_treat]
          refine ⟨⟨j.val / 2, by omega⟩, ?_⟩
          show aNode K ⟨j.val / 2, by omega⟩ = j
          apply Fin.ext
          show (aNode K ⟨j.val / 2, by omega⟩).val = j.val
          have hv : (aNode K ⟨j.val / 2, by omega⟩).val = 2 * (j.val / 2) + 1 := rfl
          omega
      · exfalso
        apply hjy
        apply Fin.ext
        show j.val = (yNode K).val
        have hv : (yNode K).val = 2 * K + 2 := rfl
        have hj3 := j.isLt
        omega
  · intro h
    rcases h with ⟨k, rfl⟩ | rfl
    · exact gf_aux_lNode_not_mem K k
    · exact gf_aux_yNode_not_mem K

private theorem gf_aux_mut_eq {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] (K : ℕ)
    (b : BayesNet α (2 * K + 3)) (l a : Fin (K + 1) → α) (y : α) :
    (b.mutilateSet (treatNodes K) (planVec K a)).joint (gf_aux_val K l a y) =
      (∏ k : Fin (K + 1), (b.cpt (lNode K k)
        (fun j => gf_aux_pre K l a (2 * k.val) j.val : b.pa (lNode K k) → α)).weights
        (l k)) *
        (b.cpt (yNode K)
          (fun j => gf_aux_pre K l a (2 * K + 2) j.val : b.pa (yNode K) → α)).weights
          y := by
  classical
  rw [BayesNet.joint_mutilateSet]
  have hW1 : ∀ j ∈ univ.filter (fun j : Fin (2 * K + 3) => j ∈ treatNodes K),
      (if j ∈ treatNodes K then
        (if gf_aux_val K l a y j = planVec K a j then (1 : ℝ) else 0)
        else (b.cpt j (b.paVal j (gf_aux_val K l a y))).weights
          (gf_aux_val K l a y j)) = 1 := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [ite_eq_left hj]
    obtain ⟨k', rfl⟩ := (gf_aux_mem_treat K j).mp hj
    rw [gf_aux_val_aNode K l a y k', gf_aux_plan_aNode K a k']
    exact ite_eq_left rfl
  have hsplit := Finset.prod_filter_mul_prod_filter_not
    (univ : Finset (Fin (2 * K + 3))) (fun j => j ∈ treatNodes K)
    (fun j => if j ∈ treatNodes K then
      (if gf_aux_val K l a y j = planVec K a j then (1 : ℝ) else 0)
      else (b.cpt j (b.paVal j (gf_aux_val K l a y))).weights (gf_aux_val K l a y j))
  have hsplit' : (∏ j : Fin (2 * K + 3),
      (if j ∈ treatNodes K then
        (if gf_aux_val K l a y j = planVec K a j then (1 : ℝ) else 0)
        else (b.cpt j (b.paVal j (gf_aux_val K l a y))).weights
          (gf_aux_val K l a y j))) =
      (∏ j ∈ univ.filter (fun j : Fin (2 * K + 3) => j ∈ treatNodes K),
        (if j ∈ treatNodes K then
          (if gf_aux_val K l a y j = planVec K a j then (1 : ℝ) else 0)
          else (b.cpt j (b.paVal j (gf_aux_val K l a y))).weights
            (gf_aux_val K l a y j))) *
      (∏ j ∈ univ.filter (fun j : Fin (2 * K + 3) => j ∉ treatNodes K),
        (if j ∈ treatNodes K then
          (if gf_aux_val K l a y j = planVec K a j then (1 : ℝ) else 0)
          else (b.cpt j (b.paVal j (gf_aux_val K l a y))).weights
            (gf_aux_val K l a y j))) := hsplit.symm
  rw [hsplit']
  have hW1' : (∏ j ∈ univ.filter (fun j : Fin (2 * K + 3) => j ∈ treatNodes K),
      (if j ∈ treatNodes K then
        (if gf_aux_val K l a y j = planVec K a j then (1 : ℝ) else 0)
        else (b.cpt j (b.paVal j (gf_aux_val K l a y))).weights
          (gf_aux_val K l a y j))) = 1 :=
    Finset.prod_eq_one hW1
  rw [hW1', one_mul]
  have hF : ∀ j ∈ univ.filter (fun j : Fin (2 * K + 3) => j ∉ treatNodes K),
      (if j ∈ treatNodes K then
        (if gf_aux_val K l a y j = planVec K a j then (1 : ℝ) else 0)
        else (b.cpt j (b.paVal j (gf_aux_val K l a y))).weights
          (gf_aux_val K l a y j)) =
        (b.cpt j (b.paVal j (gf_aux_val K l a y))).weights
          (gf_aux_val K l a y j) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [ite_eq_right hj]
  rw [Finset.prod_congr rfl hF, gf_aux_filter_compl]
  have hdisj : Disjoint (univ.image (lNode K)) ({yNode K} : Finset (Fin (2 * K + 3))) := by
    rw [Finset.disjoint_left]
    intro j hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
    simp only [Finset.mem_singleton]
    exact gf_aux_lNode_ne_yNode K k
  rw [Finset.prod_union hdisj]
  have hinj : Set.InjOn (lNode K) (↑(univ : Finset (Fin (K + 1)))) :=
    fun k1 _ k2 _ h => gf_aux_lNode_inj K h
  rw [Finset.prod_image hinj, Finset.prod_singleton]
  have hL : ∀ k ∈ (univ : Finset (Fin (K + 1))),
      (b.cpt (lNode K k) (b.paVal (lNode K k) (gf_aux_val K l a y))).weights
        (gf_aux_val K l a y (lNode K k)) =
        (b.cpt (lNode K k)
          (fun j => gf_aux_pre K l a (2 * k.val) j.val : b.pa (lNode K k) → α)).weights
          (l k) := by
    intro k _
    rw [gf_aux_paVal_lNode, gf_aux_val_lNode]
  rw [Finset.prod_congr rfl hL]
  have hY : (b.cpt (yNode K) (b.paVal (yNode K) (gf_aux_val K l a y))).weights
      (gf_aux_val K l a y (yNode K)) =
      (b.cpt (yNode K)
        (fun j => gf_aux_pre K l a (2 * K + 2) j.val : b.pa (yNode K) → α)).weights
        y := by
    rw [gf_aux_paVal_yNode, gf_aux_val_yNode]
  rw [hY]

private theorem gf_aux_valEquiv_apply {α : Type*} (K : ℕ) (l a' : Fin (K + 1) → α) (y : α) :
    (gf_aux_valEquiv K).toFun (l, (a', y)) = gf_aux_val K l a' y := rfl

/-- **The g-formula is the truncated factorization** on the time-ordered causal DAG
(Richardson and Rotnitzky 2014, §2.2, eq. (5), after Robins 1986; Pearl 2009, eq. (3.10); the
point-mass form on p. 275 of Hernán and Robins, *What If*). Let `b` be a Bayesian network whose
nodes are `L₀, A₀, …, L_K, A_K, Y` in this order, with no latent nodes, and `f` an outcome
readout. If the plan `ā` satisfies positivity for the observational joint, then the g-formula
of `ā` is the mean of `f(Y)` under `do(Ā = ā)`, computed by `BayesNet.mutilateSet` on the
treatment nodes. Positivity cannot be dropped: two networks that differ only in a table entry
at a parent value of probability `0` have the same joint, hence the same g-formula, and can
have different interventional means. -/
theorem gFormula_toObsModel_eq_mutilateSet {α : Type*} [Fintype α] [Nonempty α]
    (b : BayesNet α (2 * K + 3)) (f : α → ℝ) (a : Fin (K + 1) → α)
    (hpos : (b.toObsModel f).Positive a) :
    (b.toObsModel f).gFormula a =
      ∑ x, (b.mutilateSet (treatNodes K) (planVec K a)).joint x * f (x (yNode K)) := by
  classical
  have hreidx : (∑ x : Fin (2 * K + 3) → α,
        (b.mutilateSet (treatNodes K) (planVec K a)).joint x * f (x (yNode K))) =
      ∑ l : Fin (K + 1) → α, ∑ a' : Fin (K + 1) → α, ∑ y : α,
        (b.mutilateSet (treatNodes K) (planVec K a)).joint (gf_aux_val K l a' y) *
          f (gf_aux_val K l a' y (yNode K)) := by
    have h1 : (∑ x : Fin (2 * K + 3) → α,
          (b.mutilateSet (treatNodes K) (planVec K a)).joint x * f (x (yNode K))) =
        (∑ p : (Fin (K + 1) → α) × (Fin (K + 1) → α) × α,
          (b.mutilateSet (treatNodes K) (planVec K a)).joint
            ((gf_aux_valEquiv K).toFun p) *
          f (((gf_aux_valEquiv K).toFun p) (yNode K))) :=
      (Equiv.sum_comp (gf_aux_valEquiv K) _).symm
    rw [h1]
    simp only [Fintype.sum_prod_type, gf_aux_valEquiv_apply]
  have hmid : ∀ l : Fin (K + 1) → α,
      (∑ a' : Fin (K + 1) → α, ∑ y : α,
        (b.mutilateSet (treatNodes K) (planVec K a)).joint (gf_aux_val K l a' y) *
          f (gf_aux_val K l a' y (yNode K))) =
      (∏ k : Fin (K + 1), (b.cpt (lNode K k)
        (fun j => gf_aux_pre K l a (2 * k.val) j.val : b.pa (lNode K k) → α)).weights
        (l k)) *
        (∑ yv : α, (b.cpt (yNode K)
          (fun j => gf_aux_pre K l a (2 * K + 2) j.val : b.pa (yNode K) → α)).weights
          yv * f yv) := by
    intro l
    have hpt : ∀ y : α,
        (b.mutilateSet (treatNodes K) (planVec K a)).joint (gf_aux_val K l a y) *
          f (gf_aux_val K l a y (yNode K)) =
        (∏ k : Fin (K + 1), (b.cpt (lNode K k)
          (fun j => gf_aux_pre K l a (2 * k.val) j.val : b.pa (lNode K k) → α)).weights
          (l k)) *
          (((b.cpt (yNode K)
            (fun j => gf_aux_pre K l a (2 * K + 2) j.val : b.pa (yNode K) → α)).weights
            y) * f y) := by
      intro y
      rw [gf_aux_mut_eq, gf_aux_val_yNode]
      exact mul_assoc _ _ _
    rw [Fintype.sum_eq_single _
      (fun a' ha' => Finset.sum_eq_zero
        (fun y _ => gf_aux_mut_eq_zero K b f l a' a y ha'))]
    simp only [hpt]
    exact (Finset.mul_sum univ
      (fun yv : α => (b.cpt (yNode K)
        (fun j => gf_aux_pre K l a (2 * K + 2) j.val : b.pa (yNode K) → α)).weights
        yv * f yv)
      (∏ k : Fin (K + 1), (b.cpt (lNode K k)
        (fun j => gf_aux_pre K l a (2 * k.val) j.val : b.pa (lNode K k) → α)).weights
        (l k))).symm
  have hLHS : (b.toObsModel f).gFormula a =
      ∑ l : Fin (K + 1) → α,
        (∏ k : Fin (K + 1), (b.cpt (lNode K k)
          (fun j => gf_aux_pre K l a (2 * k.val) j.val : b.pa (lNode K k) → α)).weights
          (l k)) *
        (∑ yv : α, (b.cpt (yNode K)
          (fun j => gf_aux_pre K l a (2 * K + 2) j.val : b.pa (yNode K) → α)).weights
          yv * f yv) := by
    have h1 : (b.toObsModel f).gFormula a =
        ∑ l : Fin (K + 1) → α, cmean (b.toObsModel f).p (b.toObsModel f).Y
          (univ.filter ((b.toObsModel f).HistT K l a)) *
          ∏ k : Fin (K + 1), (b.toObsModel f).condL a l k.val := rfl
    rw [h1]
    refine Finset.sum_congr rfl fun l _ => gf_aux_term_eq K b f l a hpos
  have hRHS : (∑ l : Fin (K + 1) → α, ∑ a' : Fin (K + 1) → α, ∑ y : α,
        (b.mutilateSet (treatNodes K) (planVec K a)).joint (gf_aux_val K l a' y) *
          f (gf_aux_val K l a' y (yNode K))) =
      ∑ l : Fin (K + 1) → α,
        (∏ k : Fin (K + 1), (b.cpt (lNode K k)
          (fun j => gf_aux_pre K l a (2 * k.val) j.val : b.pa (lNode K k) → α)).weights
          (l k)) *
        (∑ yv : α, (b.cpt (yNode K)
          (fun j => gf_aux_pre K l a (2 * K + 2) j.val : b.pa (yNode K) → α)).weights
          yv * f yv) := by
    refine Finset.sum_congr rfl fun l _ => hmid l
  rw [hreidx, hLHS, hRHS]

end Cslib.MachineLearning.GraphicalModels.GFormula
