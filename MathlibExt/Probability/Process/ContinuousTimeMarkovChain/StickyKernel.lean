/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Stationary
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.LinearCombination

/-!
# The sticky (equal-input) kernel on a finite state space

Fix a finite state space `ι` and a vector `π : ι → ℝ` (a probability vector in the
applications). The **equal-input matrix** `equalInput π = 𝟙 πᵀ` has every row equal to `π`.
For a persistence parameter `c`, the **sticky kernel**

`stickyKernel π c = c • 1 + (1 - c) • 𝟙 πᵀ`

stays put with probability `c` and otherwise redraws the state from `π`. It is the transition
matrix of the continuous-time chain with the equal-input generator `κ (𝟙 πᵀ - 1)`, the
state-space-free form of Felsenstein's F81 model, at time `t` with `c = e^{-κ t}`
(`ctmcTransition_equalInputRate`). In GATK-gCNV (Babadi et al. 2023) the copy-number states
of neighbouring genomic intervals at distance `Δ` follow this kernel with `c = e^{-Δ/d}`
(`d` the coherence length, `κ = 1/d`); in a two-way pulse admixture the local-ancestry chain
along the genome has the same form with `c = (1 - r)^n` (see
`covariance_indicator_stickyKernel_two`).

All algebraic identities below hold for every real `c` and `π`; probabilistic meaning needs
`0 ≤ c ≤ 1`, `0 ≤ π` and `∑ π = 1`, which each statement assumes exactly where it is used.

## Main definitions

* `ProbabilityTheory.equalInput π`: the matrix with every row equal to `π`.
* `ProbabilityTheory.stickyKernel π c`: `c • 1 + (1 - c) • equalInput π`.
* `ProbabilityTheory.equalInputRate π κ`: the generator `κ • (equalInput π - 1)`.

## Main results

* `stickyKernel_mem_rowStochastic`: for `0 ≤ c ≤ 1`, `0 ≤ π`, `∑ π = 1` the kernel is
  row-stochastic.
* `stickyKernel_reversible`, `vecMul_stickyKernel`: `π i K i j = π j K j i`, and `π` is
  stationary.
* `stickyKernel_mul`, `stickyKernel_pow`: `K c * K c' = K (c c')`, so `K c ^ n = K (c ^ n)`.
* `isRateMatrix_equalInputRate`: for `κ ≥ 0`, `π ≥ 0`, `∑ π = 1`, the generator is a rate
  matrix.
* `ctmcTransition_equalInputRate`: `exp (t • κ (𝟙 πᵀ - 1)) = K (e^{-κ t})` for all real
  `t`, `κ`; hence the semigroup law `stickyKernel_exp_add`.
* `tendsto_stickyKernel_atTop`, `tendsto_stickyKernel_nhds_zero`: as `t → ∞` (`κ > 0`) the
  kernel tends to `𝟙 πᵀ`; as `t → 0` it tends to the identity.
* `covariance_stickyKernel`: for a stationary pair `(X, Y)` with joint law `π i K i j`,
  `Cov(f X, g Y) = c Cov_π(f, g)`.
* `covariance_indicator_stickyKernel_two`: on two states with `π = (α, 1 - α)` and
  `c = (1 - r)^n`, the ancestry-indicator covariance is `α (1 - α) (1 - r)^n`.

## References

* J. Felsenstein, *Evolutionary trees from DNA sequences: a maximum likelihood approach*,
  J. Mol. Evol. 17 (1981), 368–376.
* M. Babadi et al., *GATK-gCNV enables the discovery of rare copy number variants from exome
  sequencing data*, Nat. Genet. 55 (2023), 1589–1597.
* R. Chakraborty, K. M. Weiss, *Admixture as a tool for finding linked genes and detecting
  that difference from allelic association between loci*, Proc. Natl. Acad. Sci. USA 85
  (1988), 9119–9123 (the pulse-admixture model).
-/

@[expose] public section

open Finset Matrix Filter Topology NormedSpace

namespace ProbabilityTheory

variable {ι : Type*}

/-- The **equal-input matrix** `𝟙 πᵀ`: every row equals `π`. -/
def equalInput (π : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun _ j => π j

/-- The **sticky kernel** with persistence `c`: `c • 1 + (1 - c) • 𝟙 πᵀ`. Started from `i`,
it stays at `i` with probability `c` and otherwise redraws the state from `π`. -/
noncomputable def stickyKernel [DecidableEq ι] (π : ι → ℝ) (c : ℝ) : Matrix ι ι ℝ :=
  c • (1 : Matrix ι ι ℝ) + (1 - c) • equalInput π

/-- The **equal-input generator** `κ • (𝟙 πᵀ - 1)` with rate `κ` (Felsenstein's F81 model on
an arbitrary finite state space): jumps at rate `κ` to a state drawn from `π`. -/
noncomputable def equalInputRate [DecidableEq ι] (π : ι → ℝ) (κ : ℝ) : Matrix ι ι ℝ :=
  κ • (equalInput π - 1)

variable {π : ι → ℝ}

/-- Entrywise form of the equal-input matrix. -/
@[simp]
theorem equalInput_apply (π : ι → ℝ) (i j : ι) : equalInput π i j = π j := rfl

/-- With `∑ π = 1`, `𝟙 πᵀ` is idempotent. -/
theorem equalInput_mul_self [Fintype ι] (hπ : ∑ i, π i = 1) :
    equalInput π * equalInput π = equalInput π := by
  ext i j
  simp [Matrix.mul_apply, ← Finset.sum_mul, hπ]

section DecidableEq

variable [DecidableEq ι]

/-- Entrywise form of the sticky kernel. -/
theorem stickyKernel_apply (π : ι → ℝ) (c : ℝ) (i j : ι) :
    stickyKernel π c i j = c * (if i = j then 1 else 0) + (1 - c) * π j := by
  simp [stickyKernel, Matrix.one_apply]

/-- The sticky kernel at persistence `1` is the identity. -/
@[simp]
theorem stickyKernel_one (π : ι → ℝ) : stickyKernel π 1 = 1 := by
  simp [stickyKernel]

/-- The sticky kernel at persistence `0` is `𝟙 πᵀ`. -/
@[simp]
theorem stickyKernel_zero (π : ι → ℝ) : stickyKernel π 0 = equalInput π := by
  simp [stickyKernel]

/-- For `0 ≤ c ≤ 1` and `π ≥ 0` the entries of the sticky kernel are nonnegative. -/
theorem stickyKernel_nonneg (hπ : ∀ i, 0 ≤ π i) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (i j : ι) : 0 ≤ stickyKernel π c i j := by
  rw [stickyKernel_apply]
  have : 0 ≤ (1 - c) * π j := mul_nonneg (by linarith) (hπ j)
  split_ifs <;> nlinarith

/-- **Reversibility**: `π i K i j = π j K j i` (detailed balance), for all real `c`, `π`. -/
theorem stickyKernel_reversible (π : ι → ℝ) (c : ℝ) (i j : ι) :
    π i * stickyKernel π c i j = π j * stickyKernel π c j i := by
  simp only [stickyKernel_apply]
  by_cases h : i = j
  · subst h; ring
  · simp [h, Ne.symm h]; ring

/-- The sticky kernel depends continuously on the persistence. -/
theorem continuous_stickyKernel (π : ι → ℝ) : Continuous (stickyKernel π) := by
  unfold stickyKernel
  fun_prop

/-- **Long-distance limit**: for `κ > 0`, `K (e^{-κ t}) → 𝟙 πᵀ` as `t → ∞`. -/
theorem tendsto_stickyKernel_atTop (π : ι → ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun t => stickyKernel π (Real.exp (-(κ * t)))) atTop (𝓝 (equalInput π)) := by
  have h : Tendsto (fun t : ℝ => Real.exp (-(κ * t))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hκ)
  have := ((continuous_stickyKernel π).tendsto 0).comp h
  rw [stickyKernel_zero] at this
  exact this

/-- **Short-distance limit**: `K (e^{-κ t}) → 1` as `t → 0`, for every real `κ`. -/
theorem tendsto_stickyKernel_nhds_zero (π : ι → ℝ) (κ : ℝ) :
    Tendsto (fun t => stickyKernel π (Real.exp (-(κ * t)))) (𝓝 0) (𝓝 1) := by
  have h : Continuous fun t : ℝ => stickyKernel π (Real.exp (-(κ * t))) :=
    (continuous_stickyKernel π).comp (by fun_prop)
  simpa using h.tendsto 0

variable [Fintype ι]

/-- With `∑ π = 1`, the rows of the sticky kernel sum to `1` (for every real `c`). -/
theorem sum_stickyKernel (hπ : ∑ i, π i = 1) (c : ℝ) (i : ι) :
    ∑ j, stickyKernel π c i j = 1 := by
  simp [stickyKernel_apply, Finset.sum_add_distrib, ← Finset.mul_sum, hπ]

/-- For `0 ≤ c ≤ 1`, `π ≥ 0` and `∑ π = 1` the sticky kernel is row-stochastic. -/
theorem stickyKernel_mem_rowStochastic (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : stickyKernel π c ∈ rowStochastic ℝ ι := by
  rw [mem_rowStochastic_iff_sum]
  exact ⟨stickyKernel_nonneg hπ0 hc0 hc1, sum_stickyKernel hπ c⟩

/-- With `∑ π = 1`, `π` is a stationary vector of the sticky kernel: `π K = π`. -/
theorem vecMul_stickyKernel (hπ : ∑ i, π i = 1) (c : ℝ) : π ᵥ* stickyKernel π c = π := by
  ext j
  simp only [vecMul, dotProduct]
  calc ∑ i, π i * stickyKernel π c i j = ∑ i, π j * stickyKernel π c j i :=
        Finset.sum_congr rfl fun i _ => stickyKernel_reversible π c i j
    _ = π j := by rw [← Finset.mul_sum, sum_stickyKernel hπ, mul_one]

/-- **Composition**: with `∑ π = 1`, `K c * K c' = K (c c')` for all real `c`, `c'`. -/
theorem stickyKernel_mul (hπ : ∑ i, π i = 1) (c c' : ℝ) :
    stickyKernel π c * stickyKernel π c' = stickyKernel π (c * c') := by
  have hP := equalInput_mul_self hπ
  simp only [stickyKernel, add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, hP]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- With `∑ π = 1`, `K c ^ n = K (c ^ n)`: `n` steps of the sticky kernel are one step with
persistence `c ^ n`. -/
theorem stickyKernel_pow (hπ : ∑ i, π i = 1) (c : ℝ) (n : ℕ) :
    stickyKernel π c ^ n = stickyKernel π (c ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, stickyKernel_mul hπ, pow_succ]

/-- For `κ ≥ 0`, `π ≥ 0` and `∑ π = 1`, the equal-input generator is a rate matrix. -/
theorem isRateMatrix_equalInputRate (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1) {κ : ℝ}
    (hκ : 0 ≤ κ) : IsRateMatrix (equalInputRate π κ) where
  nonneg_of_ne i j h := by
    simpa [equalInputRate, h] using mul_nonneg hκ (hπ0 j)
  sum_row i := by
    simp [equalInputRate, Matrix.sub_apply, Matrix.one_apply, ← Finset.mul_sum,
      Finset.sum_sub_distrib, hπ]

/-- **The sticky kernel is the equal-input transition function**: with `∑ π = 1`,
`exp (t • κ (𝟙 πᵀ - 1)) = K (e^{-κ t})` for all real `κ` and `t`. -/
theorem ctmcTransition_equalInputRate (hπ : ∑ i, π i = 1) (κ t : ℝ) :
    ctmcTransition (equalInputRate π κ) t = stickyKernel π (Real.exp (-(κ * t))) := by
  let P : Matrix ι ι ℝ := 1 - equalInput π
  let a : ℝ := -(κ * t)
  have hP : IsIdempotentElem P := by
    change (1 - equalInput π) * (1 - equalInput π) = 1 - equalInput π
    simp [sub_mul, mul_sub, equalInput_mul_self hπ]
  have hs : HasSum (fun n : ℕ => ((n + 1).factorial : ℝ)⁻¹ * a ^ (n + 1))
      (Real.exp a - 1) := by
    simpa [← Real.exp_eq_exp_ℝ] using
      (hasSum_nat_add_iff' 1).mpr (exp_series_hasSum_exp' (𝕂 := ℝ) a)
  have ht : HasSum (fun n : ℕ => ((n + 1).factorial : ℝ)⁻¹ • (a • P) ^ (n + 1))
      ((Real.exp a - 1) • P) := by
    convert hs.smul_const P using 1
    funext n
    rw [smul_pow, hP.pow_succ_eq n, smul_smul]
  have he : exp (a • P) = 1 + (Real.exp a - 1) • P := by
    rw [exp_eq_tsum ℝ]
    simpa only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul] using
      (ht.zero_add (f := fun n : ℕ => (n.factorial : ℝ)⁻¹ • (a • P) ^ n)).tsum_eq
  have harg : t • equalInputRate π κ = a • P := by
    simp only [equalInputRate, P, a, smul_smul, smul_sub, neg_smul]
    rw [mul_comm t κ]
    abel
  rw [ctmcTransition, harg, he]
  ext i j
  simp [stickyKernel, P, a, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  ring

/-- **Semigroup law** of the sticky kernel in time:
`K (e^{-κ s}) * K (e^{-κ t}) = K (e^{-κ (s + t)})` (with `∑ π = 1`). -/
theorem stickyKernel_exp_add (hπ : ∑ i, π i = 1) (κ s t : ℝ) :
    stickyKernel π (Real.exp (-(κ * s))) * stickyKernel π (Real.exp (-(κ * t))) =
      stickyKernel π (Real.exp (-(κ * (s + t)))) := by
  rw [stickyKernel_mul hπ, ← Real.exp_add]
  congr 2
  ring

/-- **Covariance under the sticky kernel.** If `(X, Y)` has joint law `P(X = i, Y = j) =
π i K i j` (stationary start, one step of the kernel), then
`Cov(f X, g Y) = c Cov_π(f, g)`. The algebraic identity holds for all real `π`, `f`, `g`, `c`;
it is a covariance of a probability law when `π` is a probability vector and `0 ≤ c ≤ 1`. -/
theorem covariance_stickyKernel (π : ι → ℝ) (c : ℝ) (f g : ι → ℝ) :
    ∑ i, ∑ j, π i * stickyKernel π c i j * (f i * g j) -
        (∑ i, π i * f i) * (∑ j, π j * g j) =
      c * (∑ i, π i * (f i * g i) - (∑ i, π i * f i) * (∑ j, π j * g j)) := by
  have h : ∀ i, ∑ j, π i * stickyKernel π c i j * (f i * g j) =
      c * (π i * (f i * g i)) + (1 - c) * (π i * f i) * ∑ j, π j * g j := by
    intro i
    simp only [stickyKernel_apply, mul_add, add_mul, Finset.sum_add_distrib, mul_ite,
      mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- **Two-state ancestry covariance** (the local-ancestry chain of a two-way pulse
admixture). With ancestry proportions `π = (α, 1 - α)` and persistence `c = (1 - r) ^ n`
(no recombination between the two sites along the `n` meioses since admixture, recombination
fraction `r` per meiosis), the indicators `I_x = [X = 0]`, `I_y = [Y = 0]` of ancestry `0` at
the two sites have covariance `α (1 - α) (1 - r) ^ n`. The kernel form of the ancestry pair is
the modeling assumption here; this statement does not derive it from a genealogy. -/
theorem covariance_indicator_stickyKernel_two (α r : ℝ) (n : ℕ) :
    let π : Fin 2 → ℝ := ![α, 1 - α]
    let I : Fin 2 → ℝ := ![1, 0]
    ∑ i, ∑ j, π i * stickyKernel π ((1 - r) ^ n) i j * (I i * I j) -
        (∑ i, π i * I i) * (∑ j, π j * I j) = α * (1 - α) * (1 - r) ^ n := by
  intro π I
  rw [covariance_stickyKernel]
  simp [π, I, Fin.sum_univ_two]
  ring

end DecidableEq

end ProbabilityTheory
