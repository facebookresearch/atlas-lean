/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import MathlibExt.Probability.Distributions.Beta

/-!
# The Dirichlet process: Sethuraman's stick-breaking construction

A **stick-breaking process** breaks a stick of length `1` at independent proportions
`β₀, β₁, … ∈ [0, 1]`: the `k`-th piece has length `πₖ = βₖ ∏_{j<k} (1 - βⱼ)` and the stick left
after `k` breaks has length `∏_{j<k} (1 - βⱼ)`. Placing the pieces at i.i.d. atoms `θₖ ∼ H`,
independent of the proportions, gives the random discrete measure `G = ∑ₖ πₖ δ_{θₖ}`.
Sethuraman (1994) showed that for i.i.d. `βₖ ∼ Beta(1, α)` with `α > 0` the law of `G` is
Ferguson's (1973) Dirichlet process `DP(α, H)`; we take this construction as the definition.
Indices start at `0`, so `πₖ` here is `π_{k+1}` in Sethuraman's notation.

## Main results

Deterministic stick breaking (`stickWeight`, `stickRemainder`, `stickBreakingMeasure`):

* `sum_range_stickWeight_add_stickRemainder`: `∑_{k<n} πₖ + ∏_{k<n} (1 - βₖ) = 1`;
* `hasSum_stickWeight_iff`: the pieces sum to `1` iff the leftover stick tends to `0`.

General stick-breaking processes (`StickBreakingProcess`: independent proportions in `[0, 1]`,
i.i.d. atoms, the two families independent):

* `StickBreakingProcess.integral_weight`, `StickBreakingProcess.integral_weight_sq`:
  `E[πₖ] = E[βₖ] ∏_{j<k} (1 - E[βⱼ])` and `E[πₖ²] = E[βₖ²] ∏_{j<k} E[(1 - βⱼ)²]`;
* `StickBreakingProcess.ae_hasSum_weight`: if `∏_{j<k} (1 - E[βⱼ]) → 0`, the pieces sum to `1`
  almost surely;
* `StickBreakingProcess.lintegral_G_apply`: `E[G(A)] = H(A)`;
* `StickBreakingProcess.lintegral_G_mul_G`: `E[G(A) G(B)] = (1 - s) H(A) H(B) + s H(A ∩ B)`
  with `s = ∑ₖ E[πₖ²]`.

The Dirichlet process (`StickBreakingProcess.IsDirichlet`: proportions i.i.d. `Beta(1, α)`):

* `StickBreakingProcess.IsDirichlet.integral_weight`: `E[πₖ] = αᵏ / (1 + α)^(k+1)`;
* `StickBreakingProcess.IsDirichlet.ae_isProbabilityMeasure_G`: `G` is a.s. a probability
  measure (the pieces sum to `1`);
* `StickBreakingProcess.IsDirichlet.lintegral_G_apply`: `E[G(A)] = H(A)` (Ferguson 1973);
* `StickBreakingProcess.IsDirichlet.variance_G_apply`:
  `Var(G(A)) = H(A) (1 - H(A)) / (α + 1)` (Ferguson 1973);
* `StickBreakingProcess.IsDirichlet.sumSqWeight_eq`,
  `StickBreakingProcess.IsDirichlet.lintegral_G_mul_G`:
  `∑ₖ E[πₖ²] = 1 / (1 + α)` and `E[G(A) G(B)] = (α H(A) H(B) + H(A ∩ B)) / (α + 1)`;
* `StickBreakingProcess.IsDirichlet.lintegral_G_mul_G_eq_predictive`: the **Blackwell–MacQueen
  urn for two draws**: `E[G(A) G(B)] = ∫_A (α H(B) + 1_B(x)) / (α + 1) dH(x)`. When `X₁, X₂`
  are i.i.d. draws from `G` the left side is `P(X₁ ∈ A, X₂ ∈ B)`, so the predictive law of `X₂`
  given `X₁ = x` is `polyaUrnPredictive α H ![x] = (α H + δₓ) / (α + 1)`;
* `sethuraman`, `StickBreakingProcess.isDirichlet_sethuraman`: the canonical model on
  `(ℕ → ℝ) × (ℕ → X)`, so the hypotheses are satisfiable for every `α > 0` and every probability
  measure `H`; `dirichletProcess α hα H`, the law of `G` as a measure on `Measure X`, with its
  mean `lintegral_dirichletProcess_apply`.

Along the way: `integral_sq_betaMeasure_one` and `integral_one_sub_sq_betaMeasure_one`, the
second moments `E[x²]` and `E[(1 - x)²]` of `Beta(1, α)`.

## Not covered

The finite-dimensional Dirichlet marginals, Ferguson's posterior conjugacy, the
Blackwell–MacQueen predictive rule for `n` observations, and the Chinese restaurant law of the
ties are stated in `WantedExt/Probability/DirichletProcessWanted.lean`.

## Applications

Dirichlet-process mixtures (draw a component parameter from `G` for each observation) are a
standard nonparametric prior for clustering with an unknown number of clusters, e.g. of gene
expression profiles (Medvedovic–Sivaganesan 2002). Pritchard, Stephens and Donnelly (2000)
model population structure with a fixed number `K` of ancestral populations; a Dirichlet
process removes the need to fix `K` (Huelsenbeck–Andolfatto 2007), and the finite mixture with
symmetric `Dirichlet(α/K, …, α/K)` weights approaches the Dirichlet-process mixture as
`K → ∞` (Neal 2000). These connections are motivation only; none is formalized here. Replacing
`Beta(1, α)` by `Beta(1 - d, α + (k + 1) d)` gives the two-parameter Pitman–Yor process, to
which the general `StickBreakingProcess` results apply.

## References

* T. S. Ferguson, *A Bayesian analysis of some nonparametric problems*, Ann. Statist. 1 (1973),
  209–230.
* J. Sethuraman, *A constructive definition of Dirichlet priors*, Statist. Sinica 4 (1994),
  639–650.
* D. Blackwell, J. B. MacQueen, *Ferguson distributions via Pólya urn schemes*, Ann. Statist. 1
  (1973), 353–355.
* H. Ishwaran, L. F. James, *Gibbs sampling methods for stick-breaking priors*, J. Amer.
  Statist. Assoc. 96 (2001), 161–173.
* Y. W. Teh, *Dirichlet process*, Encyclopedia of Machine Learning, Springer, 2010.
* J. K. Pritchard, M. Stephens, P. Donnelly, *Inference of population structure using
  multilocus genotype data*, Genetics 155 (2000), 945–959.
* R. M. Neal, *Markov chain sampling methods for Dirichlet process mixture models*, J. Comput.
  Graph. Statist. 9 (2000), 249–265.
* M. Medvedovic, S. Sivaganesan, *Bayesian infinite mixture model based clustering of gene
  expression profiles*, Bioinformatics 18 (2002), 1194–1206.
* J. P. Huelsenbeck, P. Andolfatto, *Inference of population structure under a Dirichlet
  process model*, Genetics 175 (2007), 1787–1802.
-/

@[expose] public section

open MeasureTheory Filter Finset Topology
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-! ### Deterministic stick breaking -/

/-- The stick left after breaking off the first `k` pieces at proportions `b`:
`∏_{j<k} (1 - bⱼ)`. -/
def stickRemainder (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∏ j ∈ range k, (1 - b j)

/-- The `k`-th piece of a stick broken at proportions `b`: `bₖ ∏_{j<k} (1 - bⱼ)`. -/
def stickWeight (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  b k * stickRemainder b k

/-- The discrete measure `∑ₖ πₖ δ_{θₖ}` with the stick-breaking weights `πₖ = stickWeight b k`
(negative weights, which do not occur for proportions in `[0, 1]`, are read as `0`). -/
noncomputable def stickBreakingMeasure (b : ℕ → ℝ) (θ : ℕ → X) : Measure X :=
  Measure.sum fun k ↦ ENNReal.ofReal (stickWeight b k) • Measure.dirac (θ k)

/-- The first `n` pieces and the leftover stick make up the whole stick. Holds for all real
`b`. -/
theorem sum_range_stickWeight_add_stickRemainder (b : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range n, stickWeight b k + stickRemainder b n = 1 := by
  induction n with
  | zero => simp [stickRemainder]
  | succ n ih =>
    rw [sum_range_succ, stickRemainder, prod_range_succ, ← stickRemainder, stickWeight]
    linear_combination ih

/-- The leftover stick is in `[0, 1]` for proportions in `[0, 1]`. -/
theorem stickRemainder_mem_Icc {b : ℕ → ℝ} (hb : ∀ k, b k ∈ Set.Icc 0 1) (k : ℕ) :
    stickRemainder b k ∈ Set.Icc 0 1 :=
  ⟨prod_nonneg fun j _ ↦ sub_nonneg.2 (hb j).2,
    prod_le_one₀ (fun j _ ↦ sub_nonneg.2 (hb j).2) fun j _ ↦ by linarith [(hb j).1]⟩

/-- The pieces are nonnegative for proportions in `[0, 1]`. -/
theorem stickWeight_nonneg {b : ℕ → ℝ} (hb : ∀ k, b k ∈ Set.Icc 0 1) (k : ℕ) :
    0 ≤ stickWeight b k :=
  mul_nonneg (hb k).1 (stickRemainder_mem_Icc hb k).1

/-- The leftover stick shrinks for proportions in `[0, 1]`. -/
theorem antitone_stickRemainder {b : ℕ → ℝ} (hb : ∀ k, b k ∈ Set.Icc 0 1) :
    Antitone (stickRemainder b) := by
  refine antitone_nat_of_succ_le fun k ↦ ?_
  rw [stickRemainder, prod_range_succ, ← stickRemainder]
  have := (stickRemainder_mem_Icc hb k).1
  nlinarith [(hb k).1]

/-- For proportions in `[0, 1]`, the pieces sum to `1` iff the leftover stick tends to `0`. -/
theorem hasSum_stickWeight_iff {b : ℕ → ℝ} (hb : ∀ k, b k ∈ Set.Icc 0 1) :
    HasSum (stickWeight b) 1 ↔ Tendsto (stickRemainder b) atTop (𝓝 0) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (stickWeight_nonneg hb)]
  have h : ∀ n, stickRemainder b n = 1 - ∑ k ∈ range n, stickWeight b k := fun n ↦ by
    linarith [sum_range_stickWeight_add_stickRemainder b n]
  rw [show stickRemainder b = fun n ↦ 1 - ∑ k ∈ range n, stickWeight b k from funext h]
  constructor
  · intro h1
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1
  · intro h1
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1

/-- The mass of a measurable set under the stick-breaking measure. -/
theorem stickBreakingMeasure_apply (b : ℕ → ℝ) (θ : ℕ → X) {A : Set X} (hA : MeasurableSet A) :
    stickBreakingMeasure b θ A = ∑' k, ENNReal.ofReal (stickWeight b k) * A.indicator 1 (θ k) := by
  simp [stickBreakingMeasure, Measure.sum_apply _ hA, Measure.dirac_apply' _ hA]

/-- The stick-breaking measure is a probability measure when the pieces sum to `1`. -/
theorem isProbabilityMeasure_stickBreakingMeasure {b : ℕ → ℝ} (hb : ∀ k, b k ∈ Set.Icc 0 1)
    (h : HasSum (stickWeight b) 1) (θ : ℕ → X) :
    IsProbabilityMeasure (stickBreakingMeasure b θ) := by
  constructor
  rw [stickBreakingMeasure_apply b θ MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (stickWeight_nonneg hb) h.summable, h.tsum_eq,
    ENNReal.ofReal_one]

/-- The stick-breaking measure has total mass at most `1` for proportions in `[0, 1]`. -/
theorem stickBreakingMeasure_apply_le_one {b : ℕ → ℝ} (hb : ∀ k, b k ∈ Set.Icc 0 1)
    (θ : ℕ → X) (A : Set X) : stickBreakingMeasure b θ A ≤ 1 := by
  refine (measure_mono (Set.subset_univ A)).trans ?_
  rw [stickBreakingMeasure_apply b θ MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ stickWeight_nonneg hb k, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [sum_range_stickWeight_add_stickRemainder b n, (stickRemainder_mem_Icc hb n).1]

/-- The stick-breaking measure depends measurably (for the Giry σ-algebra on `Measure X`) on
the proportions and the atoms. -/
theorem measurable_stickBreakingMeasure :
    Measurable fun p : (ℕ → ℝ) × (ℕ → X) ↦ stickBreakingMeasure p.1 p.2 := by
  refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
  simp_rw [stickBreakingMeasure_apply _ _ hA]
  refine Measurable.tsum fun k ↦ ?_
  have hw : Measurable fun p : (ℕ → ℝ) × (ℕ → X) ↦ stickWeight p.1 k := by
    unfold stickWeight stickRemainder
    fun_prop
  exact (ENNReal.measurable_ofReal.comp hw).mul
    ((measurable_one.indicator hA).comp ((measurable_pi_apply k).comp measurable_snd))

/-! ### Stick-breaking processes -/

/-- A **stick-breaking process** on the probability space `(Ω, μ)`: independent proportions
`βₖ ∈ [0, 1]` (almost surely, with arbitrary laws), i.i.d. atoms `atom k` with law `H`, and the
proportion sequence independent of the atom sequence. Ishwaran–James (2001) take
`βₖ ∼ Beta(aₖ, bₖ)`; Sethuraman's Dirichlet process is `IsDirichlet`. -/
structure StickBreakingProcess (μ : Measure Ω) (X : Type*) [MeasurableSpace X] where
  /-- The stick-breaking proportions. -/
  β : ℕ → Ω → ℝ
  /-- The atoms. -/
  atom : ℕ → Ω → X
  /-- The base measure, the common law of the atoms. -/
  H : Measure X
  /-- The proportions are measurable. -/
  measurable_β : ∀ k, Measurable (β k)
  /-- The atoms are measurable. -/
  measurable_atom : ∀ k, Measurable (atom k)
  /-- The proportions lie in `[0, 1]` almost surely. -/
  ae_mem_Icc : ∀ k, ∀ᵐ ω ∂μ, β k ω ∈ Set.Icc 0 1
  /-- Each atom has law `H`. -/
  hasLaw_atom : ∀ k, HasLaw (atom k) H μ
  /-- The proportions are mutually independent. -/
  iIndepFun_β : iIndepFun β μ
  /-- The atoms are mutually independent. -/
  iIndepFun_atom : iIndepFun atom μ
  /-- The proportion sequence is independent of the atom sequence. -/
  indepFun_β_atom : IndepFun (fun ω k ↦ β k ω) (fun ω k ↦ atom k ω) μ

namespace StickBreakingProcess

variable {μ : Measure Ω} (P : StickBreakingProcess μ X)

/-- The random piece `πₖ = βₖ ∏_{j<k} (1 - βⱼ)`. -/
def weight (k : ℕ) (ω : Ω) : ℝ :=
  stickWeight (fun j ↦ P.β j ω) k

/-- The random leftover stick `∏_{j<k} (1 - βⱼ)`. -/
def remainder (k : ℕ) (ω : Ω) : ℝ :=
  stickRemainder (fun j ↦ P.β j ω) k

/-- The random measure `G = ∑ₖ πₖ δ_{θₖ}`. -/
noncomputable def G (ω : Ω) : Measure X :=
  stickBreakingMeasure (fun j ↦ P.β j ω) (fun j ↦ P.atom j ω)

/-- `∑ₖ E[πₖ²]`: given `G`, two independent draws from `G` pick the same piece `k` with
probability `∑ₖ πₖ²`. For an atomless base measure the atoms are almost surely distinct, so this
is also the probability that the two draws coincide (not used here). -/
noncomputable def sumSqWeight : ℝ≥0∞ :=
  ∑' k, ∫⁻ ω, ENNReal.ofReal (P.weight k ω) ^ 2 ∂μ

/-- The pieces are measurable. -/
theorem measurable_weight (k : ℕ) : Measurable (P.weight k) :=
  (P.measurable_β k).mul
    (Finset.measurable_prod _ fun j _ ↦ measurable_const.sub (P.measurable_β j))

/-- Almost surely every proportion is in `[0, 1]`. -/
theorem ae_forall_mem_Icc : ∀ᵐ ω ∂μ, ∀ k, P.β k ω ∈ Set.Icc 0 1 :=
  ae_all_iff.2 P.ae_mem_Icc

/-- Almost surely every piece is in `[0, 1]`. -/
theorem ae_weight_mem_Icc : ∀ᵐ ω ∂μ, ∀ k, P.weight k ω ∈ Set.Icc 0 1 := by
  filter_upwards [P.ae_forall_mem_Icc] with ω h k
  have h1 := h k
  have h2 := stickRemainder_mem_Icc h k
  refine ⟨stickWeight_nonneg h k, ?_⟩
  change P.β k ω * stickRemainder (fun j ↦ P.β j ω) k ≤ 1
  nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- The random measure depends measurably on `ω`. -/
theorem measurable_G : Measurable P.G :=
  measurable_stickBreakingMeasure.comp (Measurable.prodMk (measurable_pi_iff.2 P.measurable_β)
    (measurable_pi_iff.2 P.measurable_atom))

/-- The base measure is a probability measure. -/
theorem isProbabilityMeasure_H [IsProbabilityMeasure μ] : IsProbabilityMeasure P.H :=
  (P.hasLaw_atom 0).isProbabilityMeasure_iff.1 inferInstance

private theorem integral_prod_range [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ}
    (hf : iIndepFun f μ) (hm : ∀ j, Measurable (f j)) (k : ℕ) :
    μ[fun ω ↦ ∏ j ∈ range k, f j ω] = ∏ j ∈ range k, μ[f j] := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hind := hf.indepFun_finsetProd_of_notMem hm (s := range k) (i := k) notMem_range_self
    have h := hind.integral_fun_mul_eq_mul_integral
      (Finset.aestronglyMeasurable_prod _ fun j _ ↦ (hm j).aestronglyMeasurable)
      (hm k).aestronglyMeasurable
    simp only [Finset.prod_apply] at h
    simp_rw [prod_range_succ]
    rw [h, ← ih]

private theorem integrable_β [IsProbabilityMeasure μ] (j : ℕ) : Integrable (P.β j) μ := by
  refine Integrable.of_bound (P.measurable_β j).aestronglyMeasurable 1 ?_
  filter_upwards [P.ae_mem_Icc j] with ω h
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h.1, h.2]

private theorem integral_one_sub_β [IsProbabilityMeasure μ] (j : ℕ) :
    μ[fun ω ↦ 1 - P.β j ω] = 1 - μ[P.β j] := by
  rw [integral_sub (integrable_const 1) (P.integrable_β j), integral_const, probReal_univ,
    smul_eq_mul, one_mul]

/-- The family `ω ↦ g j (βⱼ ω)` is independent for measurable `g j`. -/
private theorem iIndepFun_comp_β (g : ℕ → ℝ → ℝ) (hg : ∀ j, Measurable (g j)) :
    iIndepFun (fun j ω ↦ g j (P.β j ω)) μ :=
  P.iIndepFun_β.comp g hg

/-- `E[∏_{j<k} (1 - βⱼ)] = ∏_{j<k} (1 - E[βⱼ])`. -/
theorem integral_remainder [IsProbabilityMeasure μ] (k : ℕ) :
    μ[P.remainder k] = ∏ j ∈ range k, (1 - μ[P.β j]) := by
  have h := integral_prod_range (P.iIndepFun_comp_β (fun _ x ↦ 1 - x) fun _ ↦ by fun_prop)
    (fun j ↦ measurable_const.sub (P.measurable_β j)) k
  simp_rw [P.integral_one_sub_β] at h
  exact h

/-- **Mean of a stick-breaking weight**: `E[πₖ] = E[βₖ] ∏_{j<k} (1 - E[βⱼ])`. -/
theorem integral_weight [IsProbabilityMeasure μ] (k : ℕ) :
    μ[P.weight k] = μ[P.β k] * ∏ j ∈ range k, (1 - μ[P.β j]) := by
  classical
  let g : ℕ → ℝ → ℝ := fun j x ↦ if j = k then x else 1 - x
  have hg : ∀ j, Measurable (g j) := fun j ↦ by
    by_cases hj : j = k <;> simp only [g, hj, ite_true, ite_false] <;> fun_prop
  have hw : P.weight k = fun ω ↦ ∏ j ∈ range (k + 1), g j (P.β j ω) := by
    ext ω
    rw [prod_range_succ, weight, stickWeight, stickRemainder, mul_comm]
    simp only [g, ite_true]
    congr 1
    exact prod_congr rfl fun j hj ↦ by simp [(mem_range.1 hj).ne]
  rw [hw, integral_prod_range (P.iIndepFun_comp_β g hg) (fun j ↦ (hg j).comp (P.measurable_β j)),
    prod_range_succ, mul_comm]
  simp only [g, ite_true]
  congr 1
  exact prod_congr rfl fun j hj ↦ by
    simp only [(mem_range.1 hj).ne, ite_false]
    exact P.integral_one_sub_β j

/-- **Second moment of a stick-breaking weight**:
`E[πₖ²] = E[βₖ²] ∏_{j<k} E[(1 - βⱼ)²]`. -/
theorem integral_weight_sq [IsProbabilityMeasure μ] (k : ℕ) :
    μ[fun ω ↦ P.weight k ω ^ 2] =
      μ[fun ω ↦ P.β k ω ^ 2] * ∏ j ∈ range k, μ[fun ω ↦ (1 - P.β j ω) ^ 2] := by
  classical
  let g : ℕ → ℝ → ℝ := fun j x ↦ if j = k then x ^ 2 else (1 - x) ^ 2
  have hg : ∀ j, Measurable (g j) := fun j ↦ by
    by_cases hj : j = k <;> simp only [g, hj, ite_true, ite_false] <;> fun_prop
  have hw : (fun ω ↦ P.weight k ω ^ 2) = fun ω ↦ ∏ j ∈ range (k + 1), g j (P.β j ω) := by
    ext ω
    rw [prod_range_succ, weight, stickWeight, stickRemainder, mul_pow, ← prod_pow, mul_comm]
    simp only [g, ite_true]
    congr 1
    exact prod_congr rfl fun j hj ↦ by simp [(mem_range.1 hj).ne]
  rw [hw, integral_prod_range (P.iIndepFun_comp_β g hg) (fun j ↦ (hg j).comp (P.measurable_β j)),
    prod_range_succ, mul_comm]
  simp only [g, ite_true]
  congr 1
  exact prod_congr rfl fun j hj ↦ by simp only [(mem_range.1 hj).ne, ite_false]

/-- If the expected leftover stick `∏_{j<k} (1 - E[βⱼ])` tends to `0`, the pieces sum to `1`
almost surely. -/
theorem ae_hasSum_weight [IsProbabilityMeasure μ]
    (h : Tendsto (fun k ↦ ∏ j ∈ range k, (1 - μ[P.β j])) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, HasSum (fun k ↦ P.weight k ω) 1 := by
  have hRm : ∀ k, Measurable (P.remainder k) := fun k ↦
    Finset.measurable_fun_prod (f := fun j ω ↦ 1 - P.β j ω) (range k) fun j _ ↦
      measurable_const.sub (P.measurable_β j)
  have hbdd : ∀ ω, (∀ k, P.β k ω ∈ Set.Icc 0 1) → BddBelow (Set.range fun k ↦ P.remainder k ω) :=
    fun ω hω ↦ ⟨0, by rintro _ ⟨k, rfl⟩; exact (stickRemainder_mem_Icc hω k).1⟩
  set L : Ω → ℝ := fun ω ↦ ⨅ k, P.remainder k ω
  have hLm : Measurable L := Measurable.iInf hRm
  have hL0 : ∀ᵐ ω ∂μ, 0 ≤ L ω := by
    filter_upwards [P.ae_forall_mem_Icc] with ω hω
    exact le_ciInf fun k ↦ (stickRemainder_mem_Icc hω k).1
  have hLle : ∀ k, ∀ᵐ ω ∂μ, L ω ≤ P.remainder k ω := fun k ↦ by
    filter_upwards [P.ae_forall_mem_Icc] with ω hω
    exact ciInf_le (hbdd ω hω) k
  have hint_R : ∀ k, Integrable (P.remainder k) μ := fun k ↦ by
    refine Integrable.of_bound (hRm k).aestronglyMeasurable 1 ?_
    filter_upwards [P.ae_forall_mem_Icc] with ω hω
    have : P.remainder k ω ∈ Set.Icc 0 1 := stickRemainder_mem_Icc hω k
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]
  have hint_L : Integrable L μ := by
    refine Integrable.of_bound hLm.aestronglyMeasurable 1 ?_
    filter_upwards [P.ae_forall_mem_Icc, hL0, hLle 0] with ω hω h0 h1
    have : P.remainder 0 ω = 1 := by simp [remainder, stickRemainder]
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hEL : ∀ k, μ[L] ≤ ∏ j ∈ range k, (1 - μ[P.β j]) := fun k ↦
    (integral_mono_ae hint_L (hint_R k) (hLle k)).trans_eq (P.integral_remainder k)
  have hLint : μ[L] = 0 := le_antisymm (ge_of_tendsto' h hEL) (integral_nonneg_of_ae hL0)
  have hLz : L =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hL0 hint_L).1 hLint
  filter_upwards [P.ae_forall_mem_Icc, hLz] with ω hω hz
  refine (hasSum_stickWeight_iff hω).2 ?_
  have ht : Tendsto (fun k ↦ P.remainder k ω) atTop (𝓝 (L ω)) :=
    tendsto_atTop_ciInf (antitone_stickRemainder hω) (hbdd ω hω)
  rw [show L ω = 0 from hz] at ht
  exact ht

private theorem measurable_stickWeight_ofReal (k : ℕ) :
    Measurable fun b : ℕ → ℝ ↦ ENNReal.ofReal (stickWeight b k) := by
  unfold stickWeight stickRemainder
  fun_prop

/-- A function of the proportion sequence and a function of the atom sequence are
uncorrelated. -/
private theorem lintegral_mul_seq [IsProbabilityMeasure μ] {φ : (ℕ → ℝ) → ℝ≥0∞}
    {ψ : (ℕ → X) → ℝ≥0∞} (hφ : Measurable φ) (hψ : Measurable ψ) :
    ∫⁻ ω, φ (fun j ↦ P.β j ω) * ψ (fun j ↦ P.atom j ω) ∂μ =
      (∫⁻ ω, φ (fun j ↦ P.β j ω) ∂μ) * ∫⁻ ω, ψ (fun j ↦ P.atom j ω) ∂μ :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (hφ.comp (measurable_pi_iff.2 P.measurable_β))
    (hψ.comp (measurable_pi_iff.2 P.measurable_atom)) (P.indepFun_β_atom.comp hφ hψ)

/-- `∫ ∑ₖ ofReal πₖ = 1` when the pieces sum to `1` almost surely. -/
private theorem tsum_lintegral_weight [IsProbabilityMeasure μ]
    (h : ∀ᵐ ω ∂μ, HasSum (fun k ↦ P.weight k ω) 1) :
    ∑' k, ∫⁻ ω, ENNReal.ofReal (P.weight k ω) ∂μ = 1 := by
  rw [← lintegral_tsum (f := fun k ω ↦ ENNReal.ofReal (P.weight k ω)) fun k ↦
    (ENNReal.measurable_ofReal.comp (P.measurable_weight k)).aemeasurable]
  rw [lintegral_congr_ae (g := fun _ ↦ (1 : ℝ≥0∞)), lintegral_const, measure_univ, one_mul]
  filter_upwards [h, P.ae_weight_mem_Icc] with ω h1 h2
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ (h2 k).1) h1.summable, h1.tsum_eq,
    ENNReal.ofReal_one]

/-- When the pieces sum to `1` almost surely, `G` is almost surely a probability measure. -/
theorem ae_isProbabilityMeasure_G_of_hasSum (h : ∀ᵐ ω ∂μ, HasSum (fun k ↦ P.weight k ω) 1) :
    ∀ᵐ ω ∂μ, IsProbabilityMeasure (P.G ω) := by
  filter_upwards [h, P.ae_forall_mem_Icc] with ω h1 h2
  exact isProbabilityMeasure_stickBreakingMeasure h2 h1 _

/-- **Mean of the random measure**: if the pieces sum to `1` almost surely, then
`E[G(A)] = H(A)` for every measurable `A`. -/
theorem lintegral_G_apply [IsProbabilityMeasure μ] (h : ∀ᵐ ω ∂μ, HasSum (fun k ↦ P.weight k ω) 1)
    {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ ω, P.G ω A ∂μ = P.H A := by
  have hterm : ∀ k, ∫⁻ ω, ENNReal.ofReal (P.weight k ω) * A.indicator 1 (P.atom k ω) ∂μ =
      (∫⁻ ω, ENNReal.ofReal (P.weight k ω) ∂μ) * P.H A := fun k ↦ by
    have h1 := P.lintegral_mul_seq (φ := fun b ↦ ENNReal.ofReal (stickWeight b k))
      (ψ := fun θ ↦ A.indicator (1 : X → ℝ≥0∞) (θ k)) (measurable_stickWeight_ofReal k)
      ((measurable_one.indicator hA).comp (measurable_pi_apply k))
    have h2 := (P.hasLaw_atom k).lintegral_comp (f := A.indicator (1 : X → ℝ≥0∞))
      (measurable_one.indicator hA).aemeasurable
    refine h1.trans ?_
    congr 1
    exact h2.trans (lintegral_indicator_one hA)
  simp_rw [G, stickBreakingMeasure_apply _ _ hA]
  refine (lintegral_tsum
    (f := fun k ω ↦ ENNReal.ofReal (P.weight k ω) * A.indicator 1 (P.atom k ω))
    fun k ↦ ((ENNReal.measurable_ofReal.comp (P.measurable_weight k)).mul
      ((measurable_one.indicator hA).comp (P.measurable_atom k))).aemeasurable).trans ?_
  rw [tsum_congr hterm, ENNReal.tsum_mul_right, P.tsum_lintegral_weight h, one_mul]

/-- **Mixed second moment of the random measure**: if the pieces sum to `1` almost surely, then
`E[G(A) G(B)] = (1 - s) H(A) H(B) + s H(A ∩ B)` with `s = ∑ₖ E[πₖ²]` (`sumSqWeight`, at most
`1` under this hypothesis): two draws from `G` pick the same piece with probability `s`, and
otherwise land on two independent atoms. -/
theorem lintegral_G_mul_G [IsProbabilityMeasure μ]
    (h : ∀ᵐ ω ∂μ, HasSum (fun k ↦ P.weight k ω) 1) {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    ∫⁻ ω, P.G ω A * P.G ω B ∂μ =
      (1 - P.sumSqWeight) * P.H A * P.H B + P.sumSqWeight * P.H (A ∩ B) := by
  classical
  have hmw : ∀ k, Measurable fun ω ↦ ENNReal.ofReal (P.weight k ω) := fun k ↦
    ENNReal.measurable_ofReal.comp (P.measurable_weight k)
  have hI : ∀ (C : Set X), MeasurableSet C → ∀ k,
      Measurable fun ω ↦ C.indicator (1 : X → ℝ≥0∞) (P.atom k ω) := fun C hC k ↦
    (measurable_one.indicator hC).comp (P.measurable_atom k)
  have hlaw : ∀ (C : Set X), MeasurableSet C → ∀ k,
      ∫⁻ ω, C.indicator (1 : X → ℝ≥0∞) (P.atom k ω) ∂μ = P.H C := fun C hC k ↦
    ((P.hasLaw_atom k).lintegral_comp (f := C.indicator 1)
      (measurable_one.indicator hC).aemeasurable).trans (lintegral_indicator_one hC)
  -- the joint law of two atoms
  have hpair : ∀ k l, ∫⁻ ω, A.indicator (1 : X → ℝ≥0∞) (P.atom k ω) *
      B.indicator (1 : X → ℝ≥0∞) (P.atom l ω) ∂μ =
        if l = k then P.H (A ∩ B) else P.H A * P.H B := by
    intro k l
    split_ifs with hlk
    · subst hlk
      have hAB : ∀ x, A.indicator (1 : X → ℝ≥0∞) x * B.indicator 1 x =
          (A ∩ B).indicator 1 x := fun x ↦ by
        by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [hxA, hxB]
      simp_rw [hAB]
      exact hlaw _ (hA.inter hB) l
    · have hind := (P.iIndepFun_atom.indepFun (Ne.symm hlk)).comp
        (measurable_one.indicator hA : Measurable (A.indicator (1 : X → ℝ≥0∞)))
        (measurable_one.indicator hB : Measurable (B.indicator (1 : X → ℝ≥0∞)))
      refine (lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hI A hA k) (hI B hB l)
        hind).trans ?_
      rw [hlaw A hA k, hlaw B hB l]
  -- the second moments of the weights
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℝ≥0∞, ∀ k l,
      c k l = ∫⁻ ω, ENNReal.ofReal (P.weight k ω) * ENNReal.ofReal (P.weight l ω) ∂μ :=
    ⟨_, fun _ _ ↦ rfl⟩
  have hterm : ∀ (C D : Set X) (hC : MeasurableSet C) (hD : MeasurableSet D) (k l : ℕ),
      ∫⁻ ω, ENNReal.ofReal (P.weight k ω) * C.indicator (1 : X → ℝ≥0∞) (P.atom k ω) *
        (ENNReal.ofReal (P.weight l ω) * D.indicator (1 : X → ℝ≥0∞) (P.atom l ω)) ∂μ =
      c k l * ∫⁻ ω, C.indicator (1 : X → ℝ≥0∞) (P.atom k ω) *
        D.indicator (1 : X → ℝ≥0∞) (P.atom l ω) ∂μ := by
    intro C D hC hD k l
    simp_rw [mul_mul_mul_comm]
    rw [hc]
    exact P.lintegral_mul_seq
      (φ := fun b ↦ ENNReal.ofReal (stickWeight b k) * ENNReal.ofReal (stickWeight b l))
      (ψ := fun θ ↦ C.indicator (1 : X → ℝ≥0∞) (θ k) * D.indicator 1 (θ l))
      ((measurable_stickWeight_ofReal k).mul (measurable_stickWeight_ofReal l))
      (((measurable_one.indicator hC).comp (measurable_pi_apply k)).mul
        ((measurable_one.indicator hD).comp (measurable_pi_apply l)))
  -- expanding a product of two random masses as a double series
  have hexp : ∀ (C D : Set X) (hC : MeasurableSet C) (hD : MeasurableSet D),
      ∫⁻ ω, P.G ω C * P.G ω D ∂μ = ∑' k, ∑' l, c k l * ∫⁻ ω,
        C.indicator (1 : X → ℝ≥0∞) (P.atom k ω) * D.indicator (1 : X → ℝ≥0∞) (P.atom l ω) ∂μ := by
    intro C D hC hD
    have hpt : ∀ ω, P.G ω C * P.G ω D = ∑' k, ∑' l,
        ENNReal.ofReal (P.weight k ω) * C.indicator (1 : X → ℝ≥0∞) (P.atom k ω) *
          (ENNReal.ofReal (P.weight l ω) * D.indicator (1 : X → ℝ≥0∞) (P.atom l ω)) := by
      intro ω
      simp only [G, stickBreakingMeasure_apply _ _ hC, stickBreakingMeasure_apply _ _ hD]
      rw [← ENNReal.tsum_mul_right]
      exact tsum_congr fun k ↦ (ENNReal.tsum_mul_left).symm
    simp_rw [hpt]
    have hm : ∀ k l, Measurable fun ω ↦
        ENNReal.ofReal (P.weight k ω) * C.indicator (1 : X → ℝ≥0∞) (P.atom k ω) *
          (ENNReal.ofReal (P.weight l ω) * D.indicator (1 : X → ℝ≥0∞) (P.atom l ω)) :=
      fun k l ↦ ((hmw k).mul (hI C hC k)).mul ((hmw l).mul (hI D hD l))
    rw [lintegral_tsum fun k ↦ (Measurable.tsum fun l ↦ hm k l).aemeasurable]
    refine tsum_congr fun k ↦ ?_
    rw [lintegral_tsum fun l ↦ (hm k l).aemeasurable]
    exact tsum_congr fun l ↦ hterm C D hC hD k l
  -- the double series of the `c k l` sums to `1`
  have hone : ∑' k, ∑' l, c k l = 1 := by
    have h1 := hexp Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
    simp only [Set.indicator_univ, Pi.one_apply, mul_one, lintegral_const, measure_univ] at h1
    rw [← h1, lintegral_congr_ae (g := fun _ ↦ (1 : ℝ≥0∞)), lintegral_const, measure_univ,
      one_mul]
    filter_upwards [P.ae_isProbabilityMeasure_G_of_hasSum h] with ω hω
    simp
  -- split off the diagonal
  have hsplit : ∀ (a : ℕ → ℕ → ℝ≥0∞), ∑' k, ∑' l, a k l =
      ∑' k, a k k + ∑' k, ∑' l, ite (l = k) 0 (a k l) := fun a ↦ by
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun k ↦ by convert ENNReal.tsum_eq_add_tsum_ite (f := a k) k
  have hdiag : ∑' k, c k k = P.sumSqWeight := by
    refine tsum_congr fun k ↦ ?_
    rw [hc]
    simp_rw [← sq]
  set T := ∑' k, ∑' l, ite (l = k) 0 (c k l)
  have hsT : P.sumSqWeight + T = 1 := by rw [← hdiag, ← hsplit, hone]
  have hT : T = 1 - P.sumSqWeight :=
    ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top
      (hsT ▸ le_self_add)) (by rw [add_comm, hsT])
  rw [hexp A B hA hB]
  simp_rw [hpair]
  rw [hsplit]
  simp only [ite_true]
  rw [← hT, ← hdiag, ENNReal.tsum_mul_right]
  have hoff : ∀ k, ∑' l, ite (l = k) 0 (c k l * ite (l = k) (P.H (A ∩ B)) (P.H A * P.H B)) =
      (∑' l, ite (l = k) 0 (c k l)) * (P.H A * P.H B) := fun k ↦ by
    rw [← ENNReal.tsum_mul_right]
    exact tsum_congr fun l ↦ by split_ifs <;> simp
  simp_rw [hoff]
  rw [ENNReal.tsum_mul_right]
  ring

/-! ### The Dirichlet process -/

/-- **Sethuraman's stick-breaking representation of the Dirichlet process** `DP(α, H)`
(Sethuraman 1994): the proportions are `Beta(1, α)` with `α > 0`. We take this construction as
the definition of `DP(α, H)`; Sethuraman's theorem that it has Ferguson's Dirichlet marginals
is recorded in `WantedExt/Probability/DirichletProcessWanted.lean`. -/
structure IsDirichlet (α : ℝ) : Prop where
  /-- The concentration parameter is positive. -/
  pos : 0 < α
  /-- Each proportion has law `Beta(1, α)`. -/
  hasLaw_β : ∀ k, HasLaw (P.β k) (betaMeasure 1 α) μ

end StickBreakingProcess

/-- The predictive law in the **Blackwell–MacQueen urn**: after observations `x₀, …, x_{n-1}`,
the next observation has law `(α H + ∑ᵢ δ_{xᵢ}) / (α + n)`. It is a probability measure for
`α > 0` and a probability measure `H` (`isProbabilityMeasure_polyaUrnPredictive`); outside that
domain the definition is total but meaningless (e.g. `α = n = 0` gives the zero measure). -/
noncomputable def polyaUrnPredictive (α : ℝ) (H : Measure X) {n : ℕ} (xs : Fin n → X) :
    Measure X :=
  (ENNReal.ofReal (α + n))⁻¹ • (ENNReal.ofReal α • H + ∑ i, Measure.dirac (xs i))

open scoped Classical in
/-- The predictive probability of a measurable set: `(α H(A) + #{i | xᵢ ∈ A}) / (α + n)`. -/
theorem polyaUrnPredictive_apply (α : ℝ) (H : Measure X) {n : ℕ} (xs : Fin n → X) {A : Set X}
    (hA : MeasurableSet A) :
    polyaUrnPredictive α H xs A =
      (ENNReal.ofReal α * H A + (univ.filter fun i ↦ xs i ∈ A).card) /
        ENNReal.ofReal (α + n) := by
  rw [polyaUrnPredictive, Measure.smul_apply, Measure.add_apply, Measure.smul_apply,
    Measure.finsetSum_apply, smul_eq_mul, smul_eq_mul, ENNReal.div_eq_inv_mul]
  congr 2
  simp_rw [Measure.dirac_apply' _ hA, Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_boole]

/-- The predictive law is a probability measure for `α > 0` and a probability measure `H`. -/
theorem isProbabilityMeasure_polyaUrnPredictive {α : ℝ} (hα : 0 < α) {H : Measure X}
    [IsProbabilityMeasure H] {n : ℕ} (xs : Fin n → X) :
    IsProbabilityMeasure (polyaUrnPredictive α H xs) := by
  classical
  constructor
  rw [polyaUrnPredictive_apply α H xs MeasurableSet.univ, measure_univ, mul_one]
  simp only [Set.mem_univ, Finset.filter_true, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_add hα.le n.cast_nonneg]
  exact ENNReal.div_self (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)
    ENNReal.ofReal_ne_top

/-! ### Moments of `Beta(1, α)` -/

/-- The Beta law is concentrated on `[0, 1]`. -/
theorem ae_mem_Icc_betaMeasure (a b : ℝ) : ∀ᵐ x ∂betaMeasure a b, x ∈ Set.Icc (0 : ℝ) 1 := by
  have hs : MeasurableSet {x : ℝ | ¬x ∈ Set.Icc (0 : ℝ) 1} := measurableSet_Icc.compl
  rw [ae_iff, betaMeasure, withDensity_apply _ hs]
  refine (setLIntegral_congr_fun hs fun x hx ↦ ?_).trans lintegral_zero
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · exact betaPDF_eq_zero_of_nonpos hx.le
  · exact betaPDF_eq_zero_of_one_le hx.le

private theorem integrable_betaMeasure_of_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ C) :
    Integrable f (betaMeasure a b) := by
  have := isProbabilityMeasureBeta ha hb
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_mem_Icc_betaMeasure a b] with x hx
  exact (Real.norm_eq_abs _).trans_le (hC x hx)

/-- The second moment of `Beta(1, α)`: `E[x²] = 2 / ((1 + α) (2 + α))`. -/
theorem integral_sq_betaMeasure_one {α : ℝ} (hα : 0 < α) :
    ∫ x, x ^ 2 ∂betaMeasure 1 α = 2 / ((1 + α) * (2 + α)) := by
  have h1 := integral_id_betaMeasure zero_lt_one hα
  have h2 := integral_heterozygosity_betaMeasure
    zero_lt_one hα
  have i1 : Integrable (fun x : ℝ ↦ x) (betaMeasure 1 α) :=
    integrable_betaMeasure_of_bound zero_lt_one hα measurable_id (C := 1) fun x hx ↦ by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have i2 : Integrable (fun x : ℝ ↦ 2 * x * (1 - x) / 2) (betaMeasure 1 α) :=
    (integrable_betaMeasure_of_bound zero_lt_one hα (by fun_prop) (C := 2) fun x hx ↦ by
      rw [abs_le]; constructor <;> nlinarith [hx.1, hx.2]).div_const 2
  rw [show (fun x : ℝ ↦ x ^ 2) = fun x ↦ x - 2 * x * (1 - x) / 2 by ext; ring,
    integral_sub i1 i2, integral_div, h1, h2]
  have : (0 : ℝ) < 1 + α := by linarith
  field_simp
  ring

/-- `E[(1 - x)²] = α / (α + 2)` under `Beta(1, α)`. -/
theorem integral_one_sub_sq_betaMeasure_one {α : ℝ} (hα : 0 < α) :
    ∫ x, (1 - x) ^ 2 ∂betaMeasure 1 α = α / (α + 2) := by
  have := isProbabilityMeasureBeta zero_lt_one hα
  have h1 := integral_id_betaMeasure zero_lt_one hα
  have i1 : Integrable (fun x : ℝ ↦ x) (betaMeasure 1 α) :=
    integrable_betaMeasure_of_bound zero_lt_one hα measurable_id (C := 1) fun x hx ↦ by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have i2 : Integrable (fun x : ℝ ↦ x ^ 2) (betaMeasure 1 α) :=
    integrable_betaMeasure_of_bound zero_lt_one hα (by fun_prop) (C := 1) fun x hx ↦ by
      rw [abs_le]; constructor <;> nlinarith [hx.1, hx.2]
  have e : ∫ x, (1 - x) ^ 2 ∂betaMeasure 1 α =
      ∫ _, (1 : ℝ) ∂betaMeasure 1 α - 2 * ∫ x, x ∂betaMeasure 1 α +
        ∫ x, x ^ 2 ∂betaMeasure 1 α := by
    have i3 : Integrable (fun a : ℝ ↦ 1 - 2 * a) (betaMeasure 1 α) :=
      (integrable_const 1).sub (i1.const_mul 2)
    rw [← integral_const_mul, ← integral_sub (integrable_const _) (i1.const_mul 2),
      ← integral_add i3 i2]
    congr 1
    ext x
    ring
  rw [e, h1, integral_sq_betaMeasure_one hα, integral_const, probReal_univ, smul_eq_mul, one_mul]
  have : (0 : ℝ) < 1 + α := by linarith
  field_simp
  ring

namespace StickBreakingProcess

variable {μ : Measure Ω} {P : StickBreakingProcess μ X} {α : ℝ}

namespace IsDirichlet

/-- The proportions of a Dirichlet process have mean `1 / (1 + α)`. -/
theorem integral_β (hP : P.IsDirichlet α) (k : ℕ) : μ[P.β k] = 1 / (1 + α) := by
  rw [(hP.hasLaw_β k).integral_eq,
    integral_id_betaMeasure zero_lt_one hP.pos]

/-- **Mean of a Dirichlet-process weight** (Sethuraman 1994): `E[πₖ] = αᵏ / (1 + α)^(k+1)`
(`α^{k-1} / (1 + α)^k` for Sethuraman's `π_k`, indexed from `1`). -/
theorem integral_weight [IsProbabilityMeasure μ] (hP : P.IsDirichlet α) (k : ℕ) :
    μ[P.weight k] = α ^ k / (1 + α) ^ (k + 1) := by
  have hm := hP.integral_β
  rw [P.integral_weight, hm k]
  simp_rw [hm, prod_const, card_range]
  have h1 : (0 : ℝ) < 1 + α := by linarith [hP.pos]
  rw [show 1 - 1 / (1 + α) = α / (1 + α) by field_simp; ring, div_pow, pow_succ]
  field_simp

/-- **The Dirichlet-process weights sum to `1` almost surely** (Sethuraman 1994): the leftover
stick tends to `0`. -/
theorem ae_hasSum_weight [IsProbabilityMeasure μ] (hP : P.IsDirichlet α) :
    ∀ᵐ ω ∂μ, HasSum (fun k ↦ P.weight k ω) 1 := by
  refine P.ae_hasSum_weight ?_
  simp_rw [hP.integral_β, prod_const, card_range]
  have h1 : (0 : ℝ) < 1 + α := by linarith [hP.pos]
  refine tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_
  · rw [sub_nonneg, div_le_one h1]
    linarith [hP.pos]
  · rw [sub_lt_self_iff]
    positivity

/-- A Dirichlet process is almost surely a probability measure. -/
theorem ae_isProbabilityMeasure_G [IsProbabilityMeasure μ] (hP : P.IsDirichlet α) :
    ∀ᵐ ω ∂μ, IsProbabilityMeasure (P.G ω) := by
  filter_upwards [hP.ae_hasSum_weight, P.ae_forall_mem_Icc] with ω h1 h2
  exact isProbabilityMeasure_stickBreakingMeasure h2 h1 _

/-- **Mean of the Dirichlet process** (Ferguson 1973): `E[G(A)] = H(A)`. -/
theorem lintegral_G_apply [IsProbabilityMeasure μ] (hP : P.IsDirichlet α) {A : Set X}
    (hA : MeasurableSet A) : ∫⁻ ω, P.G ω A ∂μ = P.H A :=
  P.lintegral_G_apply hP.ae_hasSum_weight hA

/-- Two draws from a Dirichlet process pick the same piece with probability `1 / (1 + α)`:
`∑ₖ E[πₖ²] = 1 / (1 + α)`. This is the probability that the second customer of the Chinese
restaurant process with parameter `α` joins the first one's table. -/
theorem sumSqWeight_eq [IsProbabilityMeasure μ] (hP : P.IsDirichlet α) :
    P.sumSqWeight = ENNReal.ofReal (1 / (1 + α)) := by
  have hα := hP.pos
  have h1 : (0 : ℝ) < 1 + α := by linarith
  set c : ℝ := 2 / ((1 + α) * (2 + α))
  set r : ℝ := α / (α + 2)
  have hsq : ∀ k, μ[fun ω ↦ P.β k ω ^ 2] = c := fun k ↦ by
    have := (hP.hasLaw_β k).integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
    exact this.trans (integral_sq_betaMeasure_one hα)
  have hsq' : ∀ k, μ[fun ω ↦ (1 - P.β k ω) ^ 2] = r := fun k ↦ by
    have := (hP.hasLaw_β k).integral_comp (f := fun x : ℝ ↦ (1 - x) ^ 2) (by fun_prop)
    exact this.trans (integral_one_sub_sq_betaMeasure_one hα)
  have hterm : ∀ k, ∫⁻ ω, ENNReal.ofReal (P.weight k ω) ^ 2 ∂μ = ENNReal.ofReal (c * r ^ k) := by
    intro k
    have hint : Integrable (fun ω ↦ P.weight k ω ^ 2) μ := by
      refine Integrable.of_bound ((P.measurable_weight k).pow_const 2).aestronglyMeasurable 1 ?_
      filter_upwards [P.ae_weight_mem_Icc] with ω h
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [(h k).1, (h k).2]
    have hE : μ[fun ω ↦ P.weight k ω ^ 2] = c * r ^ k := by
      rw [P.integral_weight_sq k, hsq, prod_congr rfl fun j _ ↦ hsq' j, prod_const, card_range]
    rw [← hE, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω ↦ sq_nonneg _)]
    refine lintegral_congr_ae ?_
    filter_upwards [P.ae_weight_mem_Icc] with ω h
    rw [ENNReal.ofReal_pow (h k).1]
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [div_lt_one (by linarith)]; linarith
  rw [sumSqWeight, tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg
      (fun k ↦ by positivity) ((summable_geometric_of_lt_one hr0 hr1).mul_left c),
    tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  congr 1
  simp only [c, r]
  have : (0 : ℝ) < α + 2 := by linarith
  field_simp
  ring

/-- **Mixed second moment of the Dirichlet process** (Ferguson 1973):
`E[G(A) G(B)] = (α H(A) H(B) + H(A ∩ B)) / (α + 1)`. -/
theorem lintegral_G_mul_G [IsProbabilityMeasure μ] (hP : P.IsDirichlet α) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ ω, P.G ω A * P.G ω B ∂μ =
      (ENNReal.ofReal α * P.H A * P.H B + P.H (A ∩ B)) / ENNReal.ofReal (α + 1) := by
  have hα := hP.pos
  have h1 : (0 : ℝ) < α + 1 := by linarith
  rw [P.lintegral_G_mul_G hP.ae_hasSum_weight hA hB, hP.sumSqWeight_eq]
  have hsub : 1 - ENNReal.ofReal (1 / (1 + α)) =
      ENNReal.ofReal α / ENNReal.ofReal (α + 1) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by positivity),
      ← ENNReal.ofReal_div_of_pos h1]
    congr 1
    field_simp
    ring
  rw [hsub, ENNReal.ofReal_div_of_pos (by linarith : (0 : ℝ) < 1 + α), ENNReal.ofReal_one,
    add_comm (1 : ℝ) α]
  simp only [div_eq_mul_inv]
  ring

/-- **The Blackwell–MacQueen urn for two draws** (Blackwell–MacQueen 1973): if `X₁, X₂` are
i.i.d. draws from a Dirichlet process `G`, then `P(X₁ ∈ A, X₂ ∈ B) = E[G(A) G(B)]` equals
`∫_A P(X₂ ∈ B | X₁ = x) dH(x)` with the predictive law
`polyaUrnPredictive α H ![x] = (α H + δₓ) / (α + 1)`. -/
theorem lintegral_G_mul_G_eq_predictive [IsProbabilityMeasure μ] (hP : P.IsDirichlet α)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ ω, P.G ω A * P.G ω B ∂μ = ∫⁻ x in A, polyaUrnPredictive α P.H ![x] B ∂P.H := by
  have hpt : ∀ x, polyaUrnPredictive α P.H ![x] B =
      (ENNReal.ofReal α * P.H B + B.indicator 1 x) * (ENNReal.ofReal (α + 1))⁻¹ := by
    intro x
    rw [polyaUrnPredictive_apply _ _ _ hB, div_eq_mul_inv, Nat.cast_one]
    congr 2
    by_cases hx : x ∈ B <;> simp [hx]
  simp_rw [hpt]
  have hm : Measurable fun x ↦ ENNReal.ofReal α * P.H B + B.indicator 1 x :=
    measurable_const.add (measurable_one.indicator hB)
  rw [lintegral_mul_const _ hm,
    lintegral_add_left (f := fun _ ↦ ENNReal.ofReal α * P.H B) measurable_const,
    setLIntegral_const, lintegral_indicator_one hB,
    Measure.restrict_apply hB, Set.inter_comm B A, hP.lintegral_G_mul_G hA hB, div_eq_mul_inv]
  ring

/-- **Variance of the Dirichlet process** (Ferguson 1973):
`Var(G(A)) = H(A) (1 - H(A)) / (α + 1)`. -/
theorem variance_G_apply [IsProbabilityMeasure μ] (hP : P.IsDirichlet α) {A : Set X}
    (hA : MeasurableSet A) :
    Var[fun ω ↦ (P.G ω A).toReal; μ] = P.H.real A * (1 - P.H.real A) / (α + 1) := by
  have hα := hP.pos
  have := P.isProbabilityMeasure_H
  have hYm : Measurable fun ω ↦ P.G ω A := (Measure.measurable_coe hA).comp P.measurable_G
  have hY1 : ∀ᵐ ω ∂μ, P.G ω A ≤ 1 := by
    filter_upwards [P.ae_forall_mem_Icc] with ω h
    exact stickBreakingMeasure_apply_le_one h _ _
  have hYfin : ∀ᵐ ω ∂μ, P.G ω A < ∞ := hY1.mono fun ω h ↦ h.trans_lt ENNReal.one_lt_top
  have hmem : MemLp (fun ω ↦ (P.G ω A).toReal) 2 μ := by
    refine MemLp.of_bound hYm.ennreal_toReal.aestronglyMeasurable 1 ?_
    filter_upwards [hY1] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h)
  rw [variance_eq_sub hmem]
  have e1 : μ[fun ω ↦ (P.G ω A).toReal] = P.H.real A := by
    rw [integral_toReal hYm.aemeasurable hYfin, hP.lintegral_G_apply hA]
    rfl
  have e2 : μ[(fun ω ↦ (P.G ω A).toReal) ^ 2] =
      (α * P.H.real A * P.H.real A + P.H.real A) / (α + 1) := by
    have hsq : (fun ω ↦ (P.G ω A).toReal) ^ 2 = fun ω ↦ (P.G ω A * P.G ω A).toReal := by
      ext ω
      simp [sq, ENNReal.toReal_mul]
    have hfin : ∀ᵐ ω ∂μ, P.G ω A * P.G ω A < ∞ := by
      filter_upwards [hYfin] with ω h
      exact ENNReal.mul_lt_top h h
    have hHA : P.H A = ENNReal.ofReal (P.H.real A) :=
      (ofReal_measureReal (measure_ne_top _ _)).symm
    rw [hsq, integral_toReal (f := fun ω ↦ P.G ω A * P.G ω A) (hYm.mul hYm).aemeasurable
        hfin, hP.lintegral_G_mul_G hA hA,
      Set.inter_self, hHA, ← ENNReal.ofReal_mul hα.le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) measureReal_nonneg,
      ← ENNReal.ofReal_div_of_pos (by linarith), ENNReal.toReal_ofReal (by positivity)]
  rw [e1, e2]
  have : (0 : ℝ) < α + 1 := by linarith
  field_simp
  ring

end IsDirichlet

end StickBreakingProcess

/-! ### The canonical model and the law of the Dirichlet process -/

/-- The product probability space `(ℕ → ℝ) × (ℕ → X)` carrying i.i.d. `Beta(1, α)` proportions
and, independently, i.i.d. `H` atoms. -/
noncomputable def sethuramanMeasure (α : ℝ) (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] : Measure ((ℕ → ℝ) × (ℕ → X)) :=
  haveI := isProbabilityMeasureBeta zero_lt_one hα
  (Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 α).prod (Measure.infinitePi fun _ : ℕ ↦ H)

instance isProbabilityMeasure_sethuramanMeasure (α : ℝ) (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] : IsProbabilityMeasure (sethuramanMeasure α hα H) := by
  have := isProbabilityMeasureBeta zero_lt_one hα
  simp only [sethuramanMeasure]
  infer_instance

/-- The proportion coordinate of the canonical space has law `⊗ₖ Beta(1, α)`. -/
theorem measurePreserving_fst_sethuramanMeasure {α : ℝ} (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] :
    haveI := isProbabilityMeasureBeta zero_lt_one hα
    MeasurePreserving Prod.fst (sethuramanMeasure α hα H)
      (Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 α) := by
  have := isProbabilityMeasureBeta zero_lt_one hα
  exact ⟨measurable_fst, by simp [sethuramanMeasure]⟩

/-- The atom coordinate of the canonical space has law `⊗ₖ H`. -/
theorem measurePreserving_snd_sethuramanMeasure {α : ℝ} (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] :
    MeasurePreserving Prod.snd (sethuramanMeasure α hα H) (Measure.infinitePi fun _ : ℕ ↦ H) := by
  have := isProbabilityMeasureBeta zero_lt_one hα
  exact ⟨measurable_snd, by simp [sethuramanMeasure]⟩

/-- Each proportion of the canonical space has law `Beta(1, α)`. -/
theorem hasLaw_fst_sethuramanMeasure {α : ℝ} (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] (k : ℕ) :
    HasLaw (fun p : (ℕ → ℝ) × (ℕ → X) ↦ p.1 k) (betaMeasure 1 α) (sethuramanMeasure α hα H) := by
  have := isProbabilityMeasureBeta zero_lt_one hα
  exact ((measurePreserving_eval_infinitePi _ k).comp
    (measurePreserving_fst_sethuramanMeasure hα H)).hasLaw

/-- Each atom of the canonical space has law `H`. -/
theorem hasLaw_snd_sethuramanMeasure {α : ℝ} (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] (k : ℕ) :
    HasLaw (fun p : (ℕ → ℝ) × (ℕ → X) ↦ p.2 k) H (sethuramanMeasure α hα H) :=
  ((measurePreserving_eval_infinitePi _ k).comp
    (measurePreserving_snd_sethuramanMeasure hα H)).hasLaw

/-- **Sethuraman's construction** on the canonical space: the coordinates of the two factors are
the proportions and the atoms. -/
noncomputable def sethuraman (α : ℝ) (hα : 0 < α) (H : Measure X) [IsProbabilityMeasure H] :
    StickBreakingProcess (sethuramanMeasure α hα H) X where
  β k p := p.1 k
  atom k p := p.2 k
  H := H
  measurable_β k := by fun_prop
  measurable_atom k := by fun_prop
  ae_mem_Icc k := (hasLaw_fst_sethuramanMeasure hα H k).ae_iff (p := (· ∈ Set.Icc 0 1))
    measurableSet_Icc.mem |>.2 (ae_mem_Icc_betaMeasure 1 α)
  hasLaw_atom k := hasLaw_snd_sethuramanMeasure hα H k
  iIndepFun_β := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map fun k ↦ by fun_prop]
    simp_rw [fun k ↦ (hasLaw_fst_sethuramanMeasure hα H k).map_eq]
    exact (measurePreserving_fst_sethuramanMeasure hα H).map_eq
  iIndepFun_atom := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map fun k ↦ by fun_prop]
    simp_rw [fun k ↦ (hasLaw_snd_sethuramanMeasure hα H k).map_eq]
    exact (measurePreserving_snd_sethuramanMeasure hα H).map_eq
  indepFun_β_atom := by
    rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop),
      (measurePreserving_fst_sethuramanMeasure hα H).map_eq,
      (measurePreserving_snd_sethuramanMeasure hα H).map_eq]
    exact Measure.map_id

/-- The canonical model is a Dirichlet process. -/
theorem StickBreakingProcess.isDirichlet_sethuraman (α : ℝ) (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] : (sethuraman α hα H).IsDirichlet α :=
  ⟨hα, hasLaw_fst_sethuramanMeasure hα H⟩

/-- The **Dirichlet process** `DP(α, H)` as a law on `Measure X`, defined as the law of
Sethuraman's (1994) stick-breaking measure with `Beta(1, α)` proportions and `H` atoms.
Ferguson's (1973) definition by Dirichlet marginals is the wanted statement
`map_dirichletProcess_partition`. -/
noncomputable def dirichletProcess (α : ℝ) (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] : Measure (Measure X) :=
  (sethuramanMeasure α hα H).map fun p ↦ stickBreakingMeasure p.1 p.2

/-- `DP(α, H)` is a probability measure on `Measure X`. -/
instance isProbabilityMeasure_dirichletProcess (α : ℝ) (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] : IsProbabilityMeasure (dirichletProcess α hα H) :=
  (Measure.isProbabilityMeasure_map_iff measurable_stickBreakingMeasure.aemeasurable).2
    inferInstance

/-- **Mean of the Dirichlet process**, law form: `∫ ν(A) dDP(α, H)(ν) = H(A)`. -/
theorem lintegral_dirichletProcess_apply (α : ℝ) (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ ν, ν A ∂dirichletProcess α hα H = H A := by
  rw [dirichletProcess, lintegral_map (Measure.measurable_coe hA) measurable_stickBreakingMeasure]
  exact (StickBreakingProcess.isDirichlet_sethuraman α hα H).lintegral_G_apply hA

end ProbabilityTheory
