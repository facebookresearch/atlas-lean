/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.InfiniteMixtureLimit
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.NumberTheory.Harmonic.Defs
public import MathlibExt.Probability.Distributions.PoissonSum

/-!
# The Indian buffet process: limits of the finite-model closed forms and Poisson history counts

Griffiths and Ghahramani (*The Indian buffet process: an introduction and review*, JMLR 12
(2011), Section 4) build a prior on binary feature matrices with `N` rows (objects) and an
unbounded number of columns (features). In the finite model with `K` features, feature `k` has
probability `πₖ ~ Beta(α/K, 1)` and `zᵢₖ | πₖ ~ Bernoulli(πₖ)` independently (their Equation 9).
Collapsing matrices that differ only by the order of their columns (`lof`-equivalence classes,
Section 4.2) and letting `K → ∞` gives the Indian buffet process.

A `lof`-class is described here by its `K₊` non-empty columns, a matrix `Z : Fin N → Fin K₊ → Bool`
in any column order: `mₖ` is the number of ones in column `k` (`featureCount`) and `K_h` the
number of columns equal to the history `h` (`historyCount`). Equation 12, rewritten with
Equation 13, is the paper's closed form for the finite-`K` probability of the class
(`finiteLofProb`)

  `α^{K₊} / ∏_h K_h! · K! / (K₀! K^{K₊}) · (N! / ∏_{j=1}^{N} (j + α/K))^K
    · ∏ₖ (N - mₖ)! ∏_{j=1}^{mₖ-1} (j + α/K) / N!`,  `K₀ = K - K₊`,

and Equation 14 is its limit (`lofProb`)

  `α^{K₊} / ∏_h K_h! · exp(-α H_N) · ∏ₖ (N - mₖ)! (mₖ - 1)! / N!`.

The finite-`K` closed forms (`finiteLofProb`, and the expected number of ones `expectedOnes`)
are recorded from the paper as definitions; this file does not derive them from the
beta–Bernoulli model. What is proved is their limits, and that Equation 14 agrees pointwise with
the joint probability of independent Poisson history counts.

Main results:

* `tendsto_emptyColumnsFactor`: `(N! / ∏_{j=1}^{N} (j + α/K))^K → exp(-α H_N)`, the factor
  contributed by the `K₀ → ∞` empty columns.
* `tendsto_finiteLofProb`: **the closed-form finite-model `lof`-class probability tends to the
  Indian buffet process formula** (Equation 14).
* `expectedOnes_eq`, `expectedOnes_le`, `tendsto_expectedOnes`: the closed-form expected number
  of ones `N K (α/K) / (α/K + 1)` (Equation 11) equals `N α / (1 + α/K) ≤ N α` and tends to `N α`.
* `sum_choose_mul_factorial_div`, `sum_onesCount_factorial_div`:
  `∑_h (m_h - 1)! (N - m_h)! / N! = ∑_{j=1}^{N} C(N, j) (j - 1)! (N - j)! / N! = H_N`
  over the non-zero histories (Equation 16), the identity behind the `exp(-α H_N)` normaliser.
* `prod_poissonMeasure_historyCount`: **Equation 14 as a product of Poisson probabilities**:
  the product over non-zero histories of the `Poisson(α (m_h - 1)! (N - m_h)! / N!)`
  probabilities of the history counts of `Z` equals `lofProb α Z` (Section 4.5).
* `measureReal_historyCount_eq_lofProb`: the same for random counts: if the `K_h` are independent
  with those Poisson laws, the event that they equal the history counts of `Z` has probability
  `lofProb α Z`.
* `hasLaw_sum_historyCount`, `coe_sum_historyRate`: with such counts, `K₊ = ∑_h K_h` is
  `Poisson(α H_N)` (Section 4.6), via `iIndepFun.hasLaw_sum_poissonMeasure_of_nonempty`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.IndianBuffet

open Filter Topology Finset MathlibExt.Probability.InfiniteMixtureLimit
open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {N r : ℕ}

/-- **Number of objects possessing a feature.** For a binary feature matrix
`Z : Fin N → Fin r → Bool`, `featureCount Z k = mₖ = ∑ᵢ zᵢₖ` is the number of rows with a one in
column `k` (Griffiths and Ghahramani 2011, Section 4.1). -/
def featureCount (Z : Fin N → Fin r → Bool) (k : Fin r) : ℕ := #{i | Z i k = true}

/-- **History of a feature.** The history of column `k` of a binary feature matrix is the column
itself, `(z₁ₖ, …, z_Nₖ)` (Griffiths and Ghahramani 2011, Section 4.2). -/
def history (Z : Fin N → Fin r → Bool) (k : Fin r) : Fin N → Bool := fun i => Z i k

/-- **Number of features with a given history.** `historyCount Z h = K_h` is the number of
columns of `Z` whose history is `h` (Griffiths and Ghahramani 2011, Section 4.2). -/
def historyCount (Z : Fin N → Fin r → Bool) (h : Fin N → Bool) : ℕ := #{k | history Z k = h}

/-- **Product of the history multiplicities.** `historyFactorial Z = ∏_h K_h!`, the number of
column orders of `Z` that give the same matrix; it divides `K!` in the cardinality
`K! / ∏_h K_h!` of a `lof`-equivalence class (Griffiths and Ghahramani 2011, Section 4.2). When
`Z` has no zero column, only the histories `h ≠ 0` contribute, as in their Equation 14. -/
def historyFactorial (Z : Fin N → Fin r → Bool) : ℕ :=
  ∏ h : Fin N → Bool, (historyCount Z h).factorial

/-- **Empty-column factor of the finite feature-model closed form.**
`(N! / ∏_{j=1}^{N} (j + α/K))^K`, the first factor of Griffiths and Ghahramani (2011),
Equation 13, where `N! / ∏_{j=1}^{N} (j + α/K)` is their value for the probability of an empty
column with the factor `α/K` moved onto the non-empty columns. Recorded as a definition. -/
noncomputable def emptyColumnsFactor (α : ℝ) (N K : ℕ) : ℝ :=
  ((N.factorial : ℝ) / ∏ j ∈ range N, ((j + 1 : ℝ) + α / K)) ^ K

/-- **The empty-column factor as compound interest.** For every `K`,
`(N! / ∏_{j=1}^{N} (j + α/K))^K = (∏_{j=1}^{N} (1 + (α/j)/K)^K)⁻¹`. -/
theorem emptyColumnsFactor_eq (α : ℝ) (N K : ℕ) :
    emptyColumnsFactor α N K = (∏ j ∈ range N, (1 + α / (j + 1) / K) ^ K)⁻¹ := by
  have hfac : ((N.factorial : ℕ) : ℝ) = ∏ j ∈ range N, ((j : ℝ) + 1) := by
    rw [← Finset.prod_range_add_one_eq_factorial]; push_cast; rfl
  have hsplit : ∏ j ∈ range N, ((j + 1 : ℝ) + α / K) =
      (∏ j ∈ range N, ((j : ℝ) + 1)) * ∏ j ∈ range N, (1 + α / (j + 1) / K) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hj : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hne : ∏ j ∈ range N, ((j : ℝ) + 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => by positivity
  rw [emptyColumnsFactor, hsplit, hfac, div_mul_cancel_left₀ hne, inv_pow, Finset.prod_pow]

/-- **The empty columns contribute `exp(-α H_N)`.** For every real `α` and natural `N`,
`(N! / ∏_{j=1}^{N} (j + α/K))^K → exp(-α H_N)` as `K → ∞`, where `H_N = ∑_{j=1}^{N} 1/j` is the
`N`-th harmonic number (Griffiths and Ghahramani 2011, Equation 14). -/
theorem tendsto_emptyColumnsFactor (α : ℝ) (N : ℕ) :
    Tendsto (fun K : ℕ => emptyColumnsFactor α N K) atTop
      (𝓝 (Real.exp (-α * (harmonic N : ℝ)))) := by
  have hprod : Tendsto (fun K : ℕ => ∏ j ∈ range N, (1 + α / (j + 1) / K) ^ K) atTop
      (𝓝 (∏ j ∈ range N, Real.exp (α / (j + 1)))) :=
    tendsto_finsetProd _ fun j _ => Real.tendsto_one_add_div_pow_exp (α / (j + 1))
  have hinv := hprod.inv₀ (Finset.prod_ne_zero_iff.2 fun j _ => (Real.exp_pos _).ne')
  have hlim : (∏ j ∈ range N, Real.exp (α / (j + 1)))⁻¹ = Real.exp (-α * (harmonic N : ℝ)) := by
    rw [← Real.exp_sum, ← Real.exp_neg, harmonic]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hlim] at hinv
  exact hinv.congr fun K => (emptyColumnsFactor_eq α N K).symm

/-- **Closed-form `lof`-class probability of the finite feature model.** The expression
`α^{K₊} / ∏_h K_h! · K! / (K₀! K^{K₊}) · (N! / ∏_{j=1}^{N} (j + α/K))^K ·
∏ₖ (N - mₖ)! ∏_{j=1}^{mₖ-1} (j + α/K) / N!` with `K₊ = r`, `K₀ = K - K₊`, for a matrix
`Z : Fin N → Fin r → Bool`. Griffiths and Ghahramani (2011, Equation 12 in the form given by
Equation 13) give it as the probability, for `K` features with `πₖ ~ Beta(α/K, 1)` and
`zᵢₖ ~ Bernoulli(πₖ)`, of the `lof`-equivalence class whose non-empty columns are those of `Z`
(so the intended input has `mₖ ≥ 1` for every column). It is the paper's closed form, taken here
as a definition for every `α`, `K` and `Z`; it is not derived from the beta–Bernoulli model. It is
that probability only for `α ≥ 0`, `K ≥ 1` and matrices without empty columns; outside that range
the formula is not a probability (for `α < 0` it can be negative, and an empty column is read
through `(0 - 1)! = 0! = 1`). The limit `tendsto_finiteLofProb` is an identity of formulas that
holds for every input. -/
noncomputable def finiteLofProb (α : ℝ) (K : ℕ) (Z : Fin N → Fin r → Bool) : ℝ :=
  α ^ r / (historyFactorial Z : ℝ) * ((K.descFactorial r : ℝ) / (K : ℝ) ^ r) *
    emptyColumnsFactor α N K *
    ∏ k, ((N - featureCount Z k).factorial *
      ∏ j ∈ range (featureCount Z k - 1), ((j + 1 : ℝ) + α / K)) / N.factorial

/-- **Indian buffet process formula for a `lof`-class.** The expression
`α^{K₊} / ∏_h K_h! · exp(-α H_N) · ∏ₖ (N - mₖ)! (mₖ - 1)! / N!`, `K₊ = r`, for a matrix
`Z : Fin N → Fin r → Bool`: Griffiths and Ghahramani (2011, Equation 14) give it as the
probability of the `lof`-equivalence class whose non-empty columns are those of `Z`. Taken here
as a definition for every `α` and `Z`; it is that probability only for `α ≥ 0` and matrices
without empty columns (for `α < 0` it can be negative, and an empty column is read through
`(0 - 1)! = 0! = 1`). -/
noncomputable def lofProb (α : ℝ) (Z : Fin N → Fin r → Bool) : ℝ :=
  α ^ r / (historyFactorial Z : ℝ) * Real.exp (-α * (harmonic N : ℝ)) *
    ∏ k, ((N - featureCount Z k).factorial * (featureCount Z k - 1).factorial : ℝ) /
      N.factorial

/-- **The closed-form finite-model `lof`-class probability tends to the Indian buffet process
formula** (Griffiths and Ghahramani 2011, Equation 14). For every `α` and every binary matrix
`Z`, the closed form `finiteLofProb α K Z` (Equations 12–13, recorded from the paper, not derived
from the beta–Bernoulli model here) converges, as `K → ∞`, to
`lofProb α Z = α^{K₊} / ∏_h K_h! · exp(-α H_N) · ∏ₖ (N - mₖ)! (mₖ - 1)! / N!`. As an identity
of formulas it needs no hypothesis on `Z`; the probabilistic reading is for matrices whose
columns are all non-empty. -/
theorem tendsto_finiteLofProb (α : ℝ) (Z : Fin N → Fin r → Bool) :
    Tendsto (fun K : ℕ => finiteLofProb α K Z) atTop (𝓝 (lofProb α Z)) := by
  have hcols : Tendsto (fun K : ℕ => ∏ k, ((N - featureCount Z k).factorial *
      ∏ j ∈ range (featureCount Z k - 1), ((j + 1 : ℝ) + α / K)) / N.factorial) atTop
      (𝓝 (∏ k, ((N - featureCount Z k).factorial * (featureCount Z k - 1).factorial : ℝ) /
        N.factorial)) :=
    tendsto_finsetProd _ fun k _ =>
      ((tendsto_prod_range_add_div α (featureCount Z k - 1)).const_mul _).div_const _
  have h := (((tendsto_descFactorial_div_pow r).const_mul
    (α ^ r / (historyFactorial Z : ℝ))).mul (tendsto_emptyColumnsFactor α N)).mul hcols
  rw [mul_one] at h
  exact h

/-- **Closed-form expected number of ones of the finite feature model.** The expression
`N K (α/K) / (α/K + 1)`, Griffiths and Ghahramani's value (2011, Equation 11) of `E[∑ᵢₖ zᵢₖ]`
for `K` features with `πₖ ~ Beta(α/K, 1)`: each entry is one with probability
`E[πₖ] = (α/K) / (α/K + 1)`, the mean `r / (r + s)` of `Beta(r, s)`. It is the paper's closed
form, taken here as a definition for every `α`; the expectation is not computed from a measure
here. It is that expectation only for `α ≥ 0`, the range of every theorem below (for `α < 0` the
formula can be negative or exceed the number `N K` of entries). -/
noncomputable def expectedOnes (α : ℝ) (N K : ℕ) : ℝ := N * K * ((α / K) / (α / K + 1))

/-- **The closed-form expected number of ones equals `N α / (1 + α/K)`** (Griffiths and
Ghahramani 2011, Equation 11), for `α ≥ 0` and `K ≥ 1`. -/
theorem expectedOnes_eq {α : ℝ} (hα : 0 ≤ α) (N : ℕ) {K : ℕ} (hK : K ≠ 0) :
    expectedOnes α N K = N * α / (1 + α / K) := by
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK
  have h1 : α / K + 1 ≠ 0 := by positivity
  rw [expectedOnes, add_comm 1]
  field_simp

/-- **The closed-form expected number of ones is at most `N α`**: for `α ≥ 0` and every number
of features `K`, `expectedOnes α N K ≤ N α`, the bound independent of `K` that Griffiths and
Ghahramani (2011, Section 4.1, with Equation 11) note for the finite model. -/
theorem expectedOnes_le {α : ℝ} (hα : 0 ≤ α) (N K : ℕ) : expectedOnes α N K ≤ N * α := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · rw [expectedOnes]
    simp only [CharP.cast_eq_zero, mul_zero, zero_mul]
    positivity
  rw [expectedOnes_eq hα N hK.ne']
  have h1 : 1 ≤ 1 + α / K := le_add_of_nonneg_right (by positivity)
  exact div_le_self (by positivity) h1

/-- **The closed-form expected number of ones tends to `N α`** as the number of features
`K → ∞` (Griffiths and Ghahramani 2011, Section 4.6, the limit of Equation 11). -/
theorem tendsto_expectedOnes {α : ℝ} (hα : 0 ≤ α) (N : ℕ) :
    Tendsto (fun K : ℕ => expectedOnes α N K) atTop (𝓝 (N * α)) := by
  have h : Tendsto (fun K : ℕ => N * α / (1 + α / K)) atTop (𝓝 (N * α / (1 + 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat α))
      (by norm_num)
  rw [add_zero, div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with K hK
  exact (expectedOnes_eq hα N hK.ne').symm

/-- **Harmonic numbers from binomial coefficients** (Griffiths and Ghahramani 2011,
Equation 16, right-hand side): `∑_{j=1}^{N} C(N, j) (j - 1)! (N - j)! / N! = H_N`.
Grouping the `2^N - 1` non-zero histories by their number of ones `j`, this is the sum over
histories of the rates `(m_h - 1)! (N - m_h)! / N!`, which produces the factor `exp(-α H_N)` of
Equation 14. -/
theorem sum_choose_mul_factorial_div (N : ℕ) :
    ∑ j ∈ range N, (N.choose (j + 1) : ℝ) * (j.factorial * (N - (j + 1)).factorial) /
      N.factorial = harmonic N := by
  rw [harmonic]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjN : j + 1 ≤ N := Finset.mem_range.1 hj
  have hkey : (N.choose (j + 1) : ℝ) * (j + 1).factorial * (N - (j + 1)).factorial =
      N.factorial := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjN
  have hN : (N.factorial : ℝ) ≠ 0 := by positivity
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  rw [Nat.factorial_succ, Nat.cast_mul] at hkey
  push_cast at hkey
  rw [div_eq_iff hN, ← hkey]
  field_simp

/-- **Number of ones in a history.** For a history `h : Fin N → Bool`, `onesCount h = m_h` is the
number of objects possessing a feature with that history (Griffiths and Ghahramani 2011,
Section 4.5). -/
def onesCount (h : Fin N → Bool) : ℕ := #{i | h i = true}

/-- **Counting histories by their number of ones.** There are `C(N, j)` histories with exactly
`j` ones (Griffiths and Ghahramani 2011,
Section 4.5, before Equation 16). -/
theorem card_filter_onesCount_eq (j : ℕ) :
    #{h : Fin N → Bool | onesCount h = j} = N.choose j := by
  have h : #{h : Fin N → Bool | onesCount h = j} = #(powersetCard j (univ : Finset (Fin N))) := by
    refine Finset.card_nbij' (fun h => ({i | h i = true} : Finset (Fin N)))
      (fun s i => decide (i ∈ s)) ?_ ?_ ?_ ?_
    · intro h hh
      rw [Finset.mem_coe, Finset.mem_filter] at hh
      rw [Finset.mem_coe, Finset.mem_powersetCard]
      exact ⟨subset_univ _, hh.2⟩
    · intro s hs
      rw [Finset.mem_coe, Finset.mem_powersetCard] at hs
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨mem_univ _, ?_⟩
      simp [onesCount, hs.2]
    · intro h _
      funext i
      simp
    · intro s _
      ext i
      simp
  rw [h, card_powersetCard, card_univ, Fintype.card_fin]

/-- **The history rates sum to the harmonic number** (Griffiths and Ghahramani 2011,
Equation 16, left-hand side): summed over the `2^N - 1` histories `h` with at least one one,
`∑_h (m_h - 1)! (N - m_h)! / N! = H_N`. -/
theorem sum_onesCount_factorial_div (N : ℕ) :
    ∑ h ∈ ({h | 0 < onesCount h} : Finset (Fin N → Bool)),
      ((onesCount h - 1).factorial * (N - onesCount h).factorial : ℝ) / N.factorial =
        harmonic N := by
  have hmaps : ∀ h ∈ ({h | 0 < onesCount h} : Finset (Fin N → Bool)),
      onesCount h ∈ Ico 1 (N + 1) := by
    intro h hh
    simp only [mem_filter, mem_univ, true_and] at hh
    have : onesCount h ≤ N := by
      simpa [onesCount] using card_filter_le (univ : Finset (Fin N)) fun i => h i = true
    simp only [mem_Ico]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps
    (fun j => ((j - 1).factorial * (N - j).factorial : ℝ) / N.factorial),
    Finset.sum_Ico_eq_sum_range, ← sum_choose_mul_factorial_div N]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul, add_comm 1 j, Nat.add_sub_cancel]
  have hfil : ({h ∈ ({h | 0 < onesCount h} : Finset (Fin N → Bool)) | onesCount h = j + 1}) =
      ({h | onesCount h = j + 1} : Finset (Fin N → Bool)) := by
    ext h
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    omega
  rw [hfil, card_filter_onesCount_eq]
  ring

/-- **Poisson rate of a history.** `historyRate α h = α (m_h - 1)! (N - m_h)! / N!
= α B(m_h, N - m_h + 1)`, the rate of the Poisson number of features with history `h`
(Griffiths and Ghahramani 2011, Section 4.5). -/
noncomputable def historyRate (α : ℝ≥0) (h : Fin N → Bool) : ℝ≥0 :=
  α * ((onesCount h - 1).factorial * (N - onesCount h).factorial / N.factorial)

/-- **History rates as real numbers.** The rate `α (m_h - 1)! (N - m_h)! / N!` of a history,
computed in `ℝ` (Griffiths and Ghahramani 2011, Section 4.5). -/
theorem coe_historyRate (α : ℝ≥0) (h : Fin N → Bool) :
    (historyRate α h : ℝ) =
      α * (((onesCount h - 1).factorial * (N - onesCount h).factorial : ℝ) / N.factorial) := by
  simp [historyRate]

/-- **Equation 14 as a product of Poisson probabilities** (Griffiths and Ghahramani 2011,
Section 4.5). For a matrix `Z` whose columns are all non-zero, the product over the `2^N - 1`
non-zero histories `h` of the `Poisson(α (m_h - 1)! (N - m_h)! / N!)` probabilities of the
history counts `K_h` of `Z` (the joint pmf of independent Poisson counts) equals the Indian
buffet process formula `lofProb α Z`. -/
theorem prod_poissonMeasure_historyCount (α : ℝ≥0) (Z : Fin N → Fin r → Bool)
    (hZ : ∀ k, 0 < featureCount Z k) :
    ∏ h ∈ ({h | 0 < onesCount h} : Finset (Fin N → Bool)),
      (poissonMeasure (historyRate α h)).real {historyCount Z h} = lofProb α Z := by
  set S : Finset (Fin N → Bool) := {h | 0 < onesCount h} with hS
  have hout : ∀ h, h ∉ S → historyCount Z h = 0 := by
    intro h hh
    simp only [hS, mem_filter, mem_univ, true_and, not_lt, Nat.le_zero] at hh
    simp only [historyCount, card_eq_zero, filter_eq_empty_iff, mem_univ, true_implies]
    intro k hk
    have := hZ k
    rw [show featureCount Z k = onesCount (history Z k) from rfl, hk, hh] at this
    exact lt_irrefl 0 this
  -- the three products over `S`
  have hexp : ∏ h ∈ S, Real.exp (-(historyRate α h : ℝ)) = Real.exp (-α * (harmonic N : ℝ)) := by
    rw [← Real.exp_sum, ← sum_onesCount_factorial_div N, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [coe_historyRate]
    ring
  have hfac : ∏ h ∈ S, ((historyCount Z h).factorial : ℝ) = historyFactorial Z := by
    rw [historyFactorial, Nat.cast_prod]
    refine Finset.prod_subset (subset_univ S) fun h _ hh => ?_
    simp [hout h hh]
  have hpow : ∏ h ∈ S, (historyRate α h : ℝ) ^ historyCount Z h =
      (α : ℝ) ^ r * ∏ k, ((N - featureCount Z k).factorial * (featureCount Z k - 1).factorial : ℝ) /
        N.factorial := by
    rw [Finset.prod_subset (subset_univ S) fun h _ hh => by simp [hout h hh]]
    have hfib := Finset.prod_fiberwise_of_maps_to' (s := (univ : Finset (Fin r)))
      (t := (univ : Finset (Fin N → Bool))) (g := history Z) (fun _ _ => mem_univ _)
      (fun h => (historyRate α h : ℝ))
    simp only [Finset.prod_const] at hfib
    rw [show (∏ h : Fin N → Bool, (historyRate α h : ℝ) ^ historyCount Z h) =
        ∏ h : Fin N → Bool, (historyRate α h : ℝ) ^ #{k | history Z k = h} from rfl, hfib]
    simp_rw [coe_historyRate]
    rw [Finset.prod_mul_distrib, Finset.prod_const, card_univ, Fintype.card_fin]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [show onesCount (history Z k) = featureCount Z k from rfl]
    ring
  simp only [poissonMeasure_real_singleton]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, hexp, hfac, hpow, lofProb]
  ring

/-- **The history rates sum to `α H_N`.** The Poisson rates of the non-zero histories of the
Indian buffet process sum to `α H_N` (Griffiths and Ghahramani 2011,
Equation 16 multiplied by `α`). -/
theorem coe_sum_historyRate (α : ℝ≥0) (N : ℕ) :
    ((∑ h ∈ ({h | 0 < onesCount h} : Finset (Fin N → Bool)), historyRate α h : ℝ≥0) : ℝ) =
      α * (harmonic N : ℝ) := by
  rw [NNReal.coe_sum, ← sum_onesCount_factorial_div N, Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ => coe_historyRate α h

/-- **Independent Poisson history counts give `Poisson(α H_N)` features** (Griffiths and
Ghahramani 2011, Section 4.6). If random counts `K_h` are independent with
`K_h ~ Poisson(α (m_h - 1)! (N - m_h)! / N!)` over the non-zero histories (the construction of
Section 4.5), then for `N ≥ 1` their total `K₊ = ∑_h K_h` is Poisson with rate
`∑_h α (m_h - 1)! (N - m_h)! / N!`, which equals `α H_N` by `coe_sum_historyRate`. -/
theorem hasLaw_sum_historyCount {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (α : ℝ≥0) (hN : 0 < N) {K : (Fin N → Bool) → Ω → ℕ} (hind : iIndepFun K P)
    (hmeas : ∀ h, Measurable (K h))
    (hlaw : ∀ h ∈ ({h | 0 < onesCount h} : Finset (Fin N → Bool)),
      HasLaw (K h) Po(historyRate α h) P) :
    HasLaw (∑ h ∈ ({h | 0 < onesCount h} : Finset (Fin N → Bool)), K h)
      Po(∑ h ∈ ({h | 0 < onesCount h} : Finset (Fin N → Bool)), historyRate α h) P := by
  refine hind.hasLaw_sum_poissonMeasure_of_nonempty hmeas hlaw ⟨fun _ => true, ?_⟩
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  simp [onesCount]

/-- **Independent Poisson history counts reproduce Equation 14** (Griffiths and Ghahramani 2011,
Section 4.5). If random counts `K_h` are independent with
`K_h ~ Poisson(α (m_h - 1)! (N - m_h)! / N!)` over the non-zero histories, then for every matrix
`Z` whose columns are all non-zero, the event that every `K_h` equals the number of columns of
`Z` with history `h` has probability `lofProb α Z`. -/
theorem measureReal_historyCount_eq_lofProb {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} (α : ℝ≥0) (Z : Fin N → Fin r → Bool) (hZ : ∀ k, 0 < featureCount Z k)
    {K : (Fin N → Bool) → Ω → ℕ} (hind : iIndepFun K P) (hmeas : ∀ h, Measurable (K h))
    (hlaw : ∀ h ∈ ({h | 0 < onesCount h} : Finset (Fin N → Bool)),
      HasLaw (K h) Po(historyRate α h) P) :
    P.real {ω | ∀ h ∈ ({h | 0 < onesCount h} : Finset (Fin N → Bool)),
      K h ω = historyCount Z h} = lofProb α Z := by
  rw [← prod_poissonMeasure_historyCount α Z hZ]
  have hset : {ω | ∀ h ∈ ({h | 0 < onesCount h} : Finset (Fin N → Bool)),
      K h ω = historyCount Z h} =
      ⋂ h ∈ ({h | 0 < onesCount h} : Finset (Fin N → Bool)), K h ⁻¹' {historyCount Z h} := by
    ext ω
    simp
  rw [hset, measureReal_def, hind.measure_inter_preimage_eq_mul _
    (fun h _ => measurableSet_singleton _), ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun h hh => ?_
  rw [measureReal_def, ← (hlaw h hh).map_eq, Measure.map_apply (hmeas h)
    (measurableSet_singleton _)]

end MathlibExt.Probability.IndianBuffet
