/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.KolmogorovCycleNecessity
public import MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisher
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import MathlibExt.Probability.ErgodicMarkovChain
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The Moran model: fixation probability

The Moran process (Moran 1958) models a haploid population of constant size `N` in which a
mutant type has relative fitness `r > 0` (the wild type has fitness `1`). In each step one
individual is chosen to reproduce with probability proportional to fitness and one individual,
chosen uniformly (possibly the parent), dies and is replaced by the offspring. The number `i` of
mutants is a birth–death chain on `{0, …, N}`: from state `i` it moves

* up to `i + 1` with probability `a_i = r i / (r i + N - i) · (N - i) / N` (`moranUp`),
* down to `i - 1` with probability `b_i = (N - i) / (r i + N - i) · i / N` (`moranDown`),
* and stays at `i` otherwise.

The states `0` (loss) and `N` (fixation) absorb, and `b_i / a_i = 1 / r` for `0 < i < N`.
The fixation probability from `i` mutants is

  `φ_i = (1 - r⁻¹ ^ i) / (1 - r⁻¹ ^ N)` if `r ≠ 1`, and `φ_i = i / N` if `r = 1`

(`moranFixation`). Time and selection scaling for the diffusion limit: with `r = 1 + σ / N` and
`i = ⌊x N⌋`, `φ_i → (1 - e^{-σ x}) / (1 - e^{-σ})`. This is Kimura's fixation probability
`kimuraFixation (σ / 2) x` of `Diffusion/WrightFisher.lean`, whose scaled selection coefficient
is `σ_WF = 2 N s` for `2 N` gene copies. Measured in generations of `N` replacement events, a
Moran population of `N` individuals drifts like a Wright–Fisher population of `N / 2` gene
copies (its effective size is `N / 2`), so the Moran scaled selection `σ = N s` (with
`r = 1 + s`) enters Kimura's formula as `σ_WF = (N / 2) s = σ / 2`.

## Main results

* `moranUp`, `moranDown`, `moranProb`, `moranMatrix`: the one-step transition probabilities and
  the chain as a `StochasticMatrix` on `Fin (N + 1)`.
* `moranFixation_zero`, `moranFixation_self`, `moranFixation_eq_firstStep`: `φ` solves the
  first-step boundary-value problem `φ_0 = 0`, `φ_N = 1`,
  `φ_i = a_i φ_{i+1} + b_i φ_{i-1} + (1 - a_i - b_i) φ_i` for `0 < i < N`.
* `eq_moranFixation`: it is the unique solution of that boundary-value problem.
* `tendsto_matPow_moranMatrix_last`, `tendsto_matPow_moranMatrix_zero`: the `t`-step
  probability of being at `N` (resp. `0`) tends to `φ_i` (resp. `1 - φ_i`); since `N` and `0`
  absorb, these are the probabilities of eventual fixation and loss.
* `tendsto_moranFixation_diffusion`: the diffusion limit, and `kimuraFixation_half` identifying
  it with Kimura's formula.

## References

* P. A. P. Moran, *Random processes in genetics*, Proc. Cambridge Philos. Soc. 54 (1958),
  60–71.
* M. A. Nowak, *Evolutionary Dynamics*, Harvard University Press (2006), ch. 6.
* W. J. Ewens, *Mathematical Population Genetics I*, 2nd ed., Springer (2004), §3.4.
-/

@[expose] public section

open Real Filter Finset
open scoped Topology

namespace MathlibExt.Biology.PopulationGenetics.Moran

open MathlibExt.Biology.PopulationGenetics.Diffusion

/-- Probability that one step of the Moran process with `N` individuals and mutant relative
fitness `r` takes the mutant count from `i` to `i + 1`: a mutant is chosen to reproduce
(probability `r i / (r i + N - i)`) and a wild type is chosen to die (probability
`(N - i) / N`). Meaningful for `0 < r` and `i ≤ N` (the real subtraction `N - i` is negative
for `i > N`). -/
noncomputable def moranUp (r : ℝ) (N i : ℕ) : ℝ :=
  r * i / (r * i + (N - i)) * ((N - i) / N)

/-- Probability that one step of the Moran process takes the mutant count from `i` to `i - 1`:
a wild type is chosen to reproduce (probability `(N - i) / (r i + N - i)`) and a mutant is
chosen to die (probability `i / N`). Meaningful for `0 < r` and `i ≤ N`. -/
noncomputable def moranDown (r : ℝ) (N i : ℕ) : ℝ :=
  (N - i) / (r * i + (N - i)) * (i / N)

/-- The fixation probability of the Moran process started from `i` mutants out of `N`:
`(1 - r⁻¹ ^ i) / (1 - r⁻¹ ^ N)` for `r ≠ 1`, and `i / N` in the neutral case `r = 1`.
The model's domain is `0 < r`, `N ≥ 1`, `i ≤ N`; outside it the value is the closed formula
evaluated with Lean's total division (e.g. `x / 0 = 0`) and carries no meaning. -/
noncomputable def moranFixation (r : ℝ) (N i : ℕ) : ℝ :=
  if r = 1 then i / N else (1 - r⁻¹ ^ i) / (1 - r⁻¹ ^ N)

/-- One-step transition probabilities of the Moran process on the states `Fin (N + 1)`:
`a_i` to `i + 1`, `b_i` to `i - 1`, `1 - a_i - b_i` to `i`, and `0` elsewhere. -/
noncomputable def moranProb (r : ℝ) (N : ℕ) (i j : Fin (N + 1)) : ℝ :=
  if (j : ℕ) = i + 1 then moranUp r N i
  else if (j : ℕ) + 1 = i then moranDown r N i
  else if j = i then 1 - moranUp r N i - moranDown r N i
  else 0

/-- No mutant can be added when the mutant type is fixed. -/
@[simp]
theorem moranUp_last (r : ℝ) (N : ℕ) : moranUp r N N = 0 := by
  simp [moranUp]

/-- No mutant can be removed when the mutant type is absent. -/
@[simp]
theorem moranDown_zero (r : ℝ) (N : ℕ) : moranDown r N 0 = 0 := by
  simp [moranDown]

/-- The ratio of the down- and up-step probabilities is `1 / r`: `r · b_i = a_i`. -/
theorem mul_moranDown (r : ℝ) (N i : ℕ) : r * moranDown r N i = moranUp r N i := by
  unfold moranDown moranUp
  ring

/-- The up-step probability is nonnegative on the states `0 ≤ i ≤ N`. -/
theorem moranUp_nonneg {r : ℝ} (hr : 0 < r) {N i : ℕ} (hi : i ≤ N) : 0 ≤ moranUp r N i := by
  have : (i : ℝ) ≤ N := by exact_mod_cast hi
  unfold moranUp
  have h1 : 0 ≤ (N : ℝ) - i := by linarith
  positivity

/-- The down-step probability is nonnegative on the states `0 ≤ i ≤ N`. -/
theorem moranDown_nonneg {r : ℝ} (hr : 0 < r) {N i : ℕ} (hi : i ≤ N) :
    0 ≤ moranDown r N i := by
  have : (i : ℝ) ≤ N := by exact_mod_cast hi
  unfold moranDown
  have h1 : 0 ≤ (N : ℝ) - i := by linarith
  positivity

/-- On the states `0 ≤ i ≤ N` the up- and down-step probabilities sum to at most `1`, so
the probability `1 - a_i - b_i` of staying is nonnegative. -/
theorem moranUp_add_moranDown_le_one {r : ℝ} (hr : 0 < r) {N i : ℕ} (hi : i ≤ N) :
    moranUp r N i + moranDown r N i ≤ 1 := by
  have hiN : (i : ℝ) ≤ N := by exact_mod_cast hi
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain rfl : i = 0 := by omega
    simp [moranUp, moranDown]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hD : 0 < r * i + (N - i) := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa using hN'
    · have : (0 : ℝ) < i := by exact_mod_cast hi0
      nlinarith
  unfold moranUp moranDown
  rw [div_mul_div_comm, div_mul_div_comm, ← add_div, div_le_one (by positivity)]
  nlinarith [sq_nonneg ((N : ℝ) - i), mul_nonneg hr.le (sq_nonneg (i : ℝ))]

/-- One-step expectation of a function `f` of the mutant count from state `i`:
`∑ j, P i j f j = a_i f (i + 1) + b_i f (i - 1) + (1 - a_i - b_i) f i` (the boundary terms
vanish at `i = 0` and `i = N`). -/
theorem sum_moranProb_mul (r : ℝ) (N : ℕ) (i : Fin (N + 1)) (f : ℕ → ℝ) :
    ∑ j, moranProb r N i j * f j = moranUp r N i * f (i + 1) + moranDown r N i * f (i - 1)
      + (1 - moranUp r N i - moranDown r N i) * f i := by
  have hiN : (i : ℕ) ≤ N := Nat.lt_succ_iff.1 i.2
  have key : ∀ j : Fin (N + 1), moranProb r N i j * f j =
      (if (j : ℕ) = i + 1 then moranUp r N i * f (i + 1) else 0)
      + (if (j : ℕ) = i - 1 then moranDown r N i * f (i - 1) else 0)
      + (if (j : ℕ) = i then (1 - moranUp r N i - moranDown r N i) * f i else 0) := by
    intro j
    unfold moranProb
    simp only [Fin.ext_iff]
    split_ifs <;> first
      | omega
      | (have h0 : (i : ℕ) = 0 := by omega
         have hj : (j : ℕ) = 0 := by omega
         simp [h0, hj, moranDown_zero])
      | simp_all
  have hsum : ∀ (c : ℕ) (x : ℝ), (∑ j : Fin (N + 1), if (j : ℕ) = c then x else 0) =
      if c < N + 1 then x else 0 := fun c x => by
    rw [Fin.sum_univ_eq_sum_range (fun k => if k = c then x else 0), Finset.sum_ite_eq']
    simp only [Finset.mem_range]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [hsum, show (i : ℕ) - 1 < N + 1 by omega, show (i : ℕ) < N + 1 by omega, ite_true]
  split_ifs with h
  · rfl
  · have : (i : ℕ) = N := by omega
    simp [this, moranUp_last]

/-- The Moran process with `N` individuals and mutant relative fitness `r > 0`, as a stochastic
matrix on the mutant counts `Fin (N + 1)`. -/
noncomputable def moranMatrix (N : ℕ) {r : ℝ} (hr : 0 < r) : StochasticMatrix N where
  prob := moranProb r N
  nonneg i j := by
    have hi : (i : ℕ) ≤ N := Nat.lt_succ_iff.1 i.2
    unfold moranProb
    split_ifs
    · exact moranUp_nonneg hr hi
    · exact moranDown_nonneg hr hi
    · linarith [moranUp_add_moranDown_le_one hr hi]
    · exact le_rfl
  row_sum i := by
    simpa using sum_moranProb_mul r N i (fun _ => 1)

/-- A mutant that is absent is never fixed: `φ_0 = 0`. -/
@[simp]
theorem moranFixation_zero (r : ℝ) (N : ℕ) : moranFixation r N 0 = 0 := by
  simp [moranFixation]

/-- A mutant that is already fixed stays fixed: `φ_N = 1` (for `N ≠ 0`). -/
theorem moranFixation_self {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : N ≠ 0) :
    moranFixation r N N = 1 := by
  unfold moranFixation
  split_ifs with h1
  · exact div_self (Nat.cast_ne_zero.2 hN)
  · refine div_self (sub_ne_zero.2 (Ne.symm ?_))
    rw [Ne, pow_eq_one_iff_of_nonneg (inv_nonneg.2 hr.le) hN, inv_eq_one]
    exact h1

/-- **First-step equation (Moran 1958).** The fixation probability satisfies
`φ_i = a_i φ_{i+1} + b_i φ_{i-1} + (1 - a_i - b_i) φ_i`. This is the first-step equation of the
chain for the interior states `0 < i < N`; the identity is algebraic (it follows from
`r · b_i = a_i`), so it is stated for every `i ≥ 1`. -/
theorem moranFixation_eq_firstStep {r : ℝ} (hr : 0 < r) {N i : ℕ} (hi0 : 0 < i) :
    moranFixation r N i = moranUp r N i * moranFixation r N (i + 1)
      + moranDown r N i * moranFixation r N (i - 1)
      + (1 - moranUp r N i - moranDown r N i) * moranFixation r N i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hstep : r * (moranFixation r N (k + 1 + 1) - moranFixation r N (k + 1)) =
      moranFixation r N (k + 1) - moranFixation r N k := by
    unfold moranFixation
    split_ifs with h1
    · subst h1
      push_cast
      ring
    · have hr' : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
      rw [← sub_div, ← sub_div, mul_div_assoc']
      congr 1
      linear_combination (r⁻¹ ^ k - r⁻¹ ^ (k + 1)) * hr'
  rw [Nat.add_sub_cancel, ← mul_moranDown]
  linear_combination (-moranDown r N (k + 1)) * hstep

/-- **Uniqueness of the fixation probability.** Any `ψ` with `ψ 0 = 0`, `ψ N = 1` that satisfies
the first-step equation `ψ i = a_i ψ (i+1) + b_i ψ (i-1) + (1 - a_i - b_i) ψ i` at every
`0 < i < N` equals `moranFixation r N` on `0 ≤ i ≤ N`. -/
theorem eq_moranFixation {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : N ≠ 0) {ψ : ℕ → ℝ}
    (h0 : ψ 0 = 0) (hN1 : ψ N = 1)
    (hψ : ∀ i, 0 < i → i < N → ψ i = moranUp r N i * ψ (i + 1) + moranDown r N i * ψ (i - 1)
      + (1 - moranUp r N i - moranDown r N i) * ψ i) :
    ∀ i ≤ N, ψ i = moranFixation r N i := by
  let δ : ℕ → ℝ := fun i => ψ i - moranFixation r N i
  have hδ0 : δ 0 = 0 := by simp [δ, h0]
  have hδN : δ N = 0 := by simp [δ, hN1, moranFixation_self hr hN]
  have hstep (i : ℕ) (hi0 : 0 < i) (hiN : i < N) :
      r * (δ (i + 1) - δ i) = δ i - δ (i - 1) := by
    have hiR : (0 : ℝ) < i := by exact_mod_cast hi0
    have hiNR : (i : ℝ) < N := by exact_mod_cast hiN
    have hNR : (0 : ℝ) < N := by linarith
    have hb : 0 < moranDown r N i := by
      unfold moranDown
      have hsub : 0 < (N : ℝ) - i := by linarith
      positivity
    have hp := hψ i hi0 hiN
    have hf := moranFixation_eq_firstStep (N := N) hr hi0
    rw [← mul_moranDown] at hp hf
    apply (mul_left_cancel₀ hb.ne' :
      moranDown r N i * _ = moranDown r N i * _ → _)
    dsimp [δ]
    linear_combination hf - hp
  have hd (k : ℕ) (hk : k < N) : δ (k + 1) - δ k = r⁻¹ ^ k * δ 1 := by
    induction k with
    | zero => simp [hδ0]
    | succ k ih =>
      have hs := hstep (k + 1) (by omega) hk
      rw [Nat.add_sub_cancel, ih (by omega)] at hs
      apply (mul_left_cancel₀ hr.ne' : r * _ = r * _ → _)
      rw [pow_succ]
      calc
        r * (δ (k + 1 + 1) - δ (k + 1)) = r⁻¹ ^ k * δ 1 := hs
        _ = r * (r⁻¹ ^ k * r⁻¹ * δ 1) := by
          linear_combination -(r⁻¹ ^ k * δ 1) * (mul_inv_cancel₀ hr.ne')
  have hsum (i : ℕ) (hi : i ≤ N) : δ i = δ 1 * ∑ k ∈ range i, r⁻¹ ^ k := by
    induction i with
    | zero => simp [hδ0]
    | succ i ih =>
      rw [sum_range_succ]
      have hdi := hd i (by omega)
      have hsi := ih (by omega)
      linear_combination hdi + hsi
  have hpos : 0 < ∑ k ∈ range N, r⁻¹ ^ k := by
    apply sum_pos'
    · intro k hk
      exact pow_nonneg (inv_nonneg.mpr hr.le) k
    · exact ⟨0, mem_range.mpr (Nat.pos_of_ne_zero hN), by simp⟩
  have hδ1 : δ 1 = 0 := by
    have hs := hsum N le_rfl
    rw [hδN] at hs
    exact (mul_eq_zero.mp hs.symm).resolve_right hpos.ne'
  intro i hi
  have hs := hsum i hi
  rw [hδ1, zero_mul] at hs
  exact sub_eq_zero.mp hs

private theorem matPow_le_one {M : ℕ} (P : StochasticMatrix M) (t : ℕ)
    (i j : Fin (M + 1)) : P.matPow t i j ≤ 1 := by
  rw [← P.matPow_row_sum t i]
  exact single_le_sum (fun k _ => P.matPow_nonneg t i k) (mem_univ j)

private theorem matPow_absorbing {M : ℕ} (P : StochasticMatrix M)
    (e : Fin (M + 1)) (he : ∀ k, P.prob e k = if e = k then 1 else 0)
    (t : ℕ) (j : Fin (M + 1)) : P.matPow t e j = if e = j then 1 else 0 := by
  classical
  induction t with
  | zero => rfl
  | succ t ih => simpa [StochasticMatrix.matPow, he, ite_mul] using ih

private theorem matPow_endpoint_monotone {M : ℕ} (P : StochasticMatrix M)
    (e : Fin (M + 1)) (he : ∀ k, P.prob e k = if e = k then 1 else 0)
    (i : Fin (M + 1)) : Monotone (fun t => P.matPow t i e) := by
  classical
  apply monotone_nat_of_le_succ
  intro t
  induction t generalizing i with
  | zero =>
    by_cases hie : i = e
    · subst i
      simp [matPow_absorbing P e he]
    · simpa [StochasticMatrix.matPow, hie] using P.matPow_nonneg 1 i e
  | succ t ih =>
    exact sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (ih k) (P.nonneg i k)

private theorem endpoint_limit {M : ℕ} (P : StochasticMatrix M)
    (e : Fin (M + 1)) (he : ∀ k, P.prob e k = if e = k then 1 else 0) :
    ∃ f : Fin (M + 1) → ℝ,
      (∀ i, Tendsto (fun t => P.matPow t i e) atTop (𝓝 (f i))) ∧
      (∀ i, ∑ k, P.prob i k * f k = f i) := by
  classical
  let f : Fin (M + 1) → ℝ := fun i => ⨆ t, P.matPow t i e
  have hf (i : Fin (M + 1)) :
      Tendsto (fun t => P.matPow t i e) atTop (𝓝 (f i)) := by
    apply tendsto_atTop_ciSup (matPow_endpoint_monotone P e he i)
    exact ⟨1, by rintro _ ⟨t, rfl⟩; exact matPow_le_one P t i e⟩
  refine ⟨f, hf, fun i => ?_⟩
  have hs : Tendsto (fun t => ∑ k, P.prob i k * P.matPow t k e) atTop
      (𝓝 (∑ k, P.prob i k * f k)) := by
    exact tendsto_finsetSum _ fun k _ => (hf k).const_mul _
  have ht : Tendsto (fun t => P.matPow (t + 1) i e) atTop (𝓝 (f i)) :=
    (hf i).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hs ht

private theorem moran_zero_absorbing (r : ℝ) (N : ℕ) (k : Fin (N + 1)) :
    moranProb r N 0 k = if (0 : Fin (N + 1)) = k then 1 else 0 := by
  have hu : moranUp r N 0 = 0 := by simp [moranUp]
  unfold moranProb
  rw [Fin.val_zero, hu, moranDown_zero]
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · simp [hk, Ne.symm hk]

private theorem moran_last_absorbing (r : ℝ) (N : ℕ) (k : Fin (N + 1)) :
    moranProb r N (Fin.last N) k = if Fin.last N = k then 1 else 0 := by
  classical
  have hk : (k : ℕ) ≠ N + 1 := by omega
  have hd : moranDown r N N = 0 := by simp [moranDown]
  simp only [moranProb, Fin.val_last, hk, ite_false, moranUp_last, hd]
  by_cases h : k = Fin.last N
  · subst k; simp
  · split_ifs <;> simp_all [eq_comm]

private theorem harmonic_eq_fixation {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : N ≠ 0)
    (f : Fin (N + 1) → ℝ) (h0 : f 0 = 0) (h1 : f (Fin.last N) = 1)
    (hf : ∀ i, ∑ k, moranProb r N i k * f k = f i) :
    ∀ i, f i = moranFixation r N i := by
  let ψ : ℕ → ℝ := fun n => f ⟨min n N, by omega⟩
  have hψ (n : ℕ) (hn : n ≤ N) : ψ n = f ⟨n, by omega⟩ := by
    simp only [ψ, min_eq_left hn]
  have hz : ψ 0 = 0 := by simpa [ψ] using h0
  have ho : ψ N = 1 := by simpa [ψ, Fin.last] using h1
  have hh (n : ℕ) (hn0 : 0 < n) (hnN : n < N) :
      ψ n = moranUp r N n * ψ (n + 1) + moranDown r N n * ψ (n - 1)
        + (1 - moranUp r N n - moranDown r N n) * ψ n := by
    have hs := sum_moranProb_mul r N ⟨n, by omega⟩ ψ
    have he : (∑ k : Fin (N + 1), moranProb r N ⟨n, by omega⟩ k * ψ k) =
        f ⟨n, by omega⟩ := by
      simpa only [hψ _ (Nat.lt_succ_iff.mp (Fin.isLt _))] using hf ⟨n, by omega⟩
    rw [he, ← hψ n (by omega)] at hs
    exact hs
  intro i
  simpa only [hψ _ (Nat.lt_succ_iff.mp i.isLt)] using
    eq_moranFixation hr hN hz ho hh i (Nat.lt_succ_iff.mp i.isLt)

private theorem endpoint_limit_at_absorbing {M : ℕ} (P : StochasticMatrix M)
    (e j : Fin (M + 1)) (hj : ∀ k, P.prob j k = if j = k then 1 else 0)
    (f : Fin (M + 1) → ℝ)
    (hf : Tendsto (fun t => P.matPow t j e) atTop (𝓝 (f j))) :
    f j = if j = e then 1 else 0 := by
  apply tendsto_nhds_unique hf
  simpa only [matPow_absorbing P j hj] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => if j = e then (1 : ℝ) else 0)
      atTop (𝓝 (if j = e then 1 else 0)))

/-- **Fixation probability of the chain.** For `N ≠ 0`, the probability that the Moran chain
started at `i` is in state `N` after `t` steps tends to `φ_i` as `t → ∞`. Since `N` absorbs,
this `t`-step probability is the probability of fixation by time `t`, so its limit is the
probability of eventual fixation. -/
theorem tendsto_matPow_moranMatrix_last {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : N ≠ 0)
    (i : Fin (N + 1)) :
    Tendsto (fun t => (moranMatrix N hr).matPow t i (Fin.last N)) atTop
      (𝓝 (moranFixation r N i)) := by
  obtain ⟨f, hf, hm⟩ := endpoint_limit (moranMatrix N hr) (Fin.last N)
    (moran_last_absorbing r N)
  have hne : (0 : Fin (N + 1)) ≠ Fin.last N := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hv
    exact hN hv.symm
  have hz : f 0 = 0 := by
    simpa only [ite_eq_right hne] using endpoint_limit_at_absorbing (moranMatrix N hr)
      (Fin.last N) 0 (moran_zero_absorbing r N) f (hf 0)
  have ho : f (Fin.last N) = 1 := by
    simpa only [ite_true] using endpoint_limit_at_absorbing (moranMatrix N hr)
      (Fin.last N) (Fin.last N) (moran_last_absorbing r N) f (hf (Fin.last N))
  have heq := harmonic_eq_fixation hr hN f hz ho hm i
  simpa only [heq] using hf i

/-- **Loss probability of the chain.** For `N ≠ 0`, the probability that the Moran chain
started at `i` is in state `0` after `t` steps tends to `1 - φ_i`; together with
`tendsto_matPow_moranMatrix_last`, absorption at `0` or `N` is certain. -/
theorem tendsto_matPow_moranMatrix_zero {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : N ≠ 0)
    (i : Fin (N + 1)) :
    Tendsto (fun t => (moranMatrix N hr).matPow t i 0) atTop
      (𝓝 (1 - moranFixation r N i)) := by
  obtain ⟨f, hf, hm⟩ := endpoint_limit (moranMatrix N hr) 0
    (moran_zero_absorbing r N)
  have hne : Fin.last N ≠ (0 : Fin (N + 1)) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hv
    exact hN hv
  have hz : f 0 = 1 := by
    simpa only [ite_true] using endpoint_limit_at_absorbing (moranMatrix N hr)
      0 0 (moran_zero_absorbing r N) f (hf 0)
  have ho : f (Fin.last N) = 0 := by
    simpa only [ite_eq_right hne] using endpoint_limit_at_absorbing (moranMatrix N hr)
      0 (Fin.last N) (moran_last_absorbing r N) f (hf (Fin.last N))
  have hg (j : Fin (N + 1)) :
      ∑ k, moranProb r N j k * (1 - f k) = 1 - f j := by
    simp_rw [mul_sub, mul_one]
    rw [sum_sub_distrib]
    have hs : ∑ k, moranProb r N j k = 1 := (moranMatrix N hr).row_sum j
    have hh : ∑ k, moranProb r N j k * f k = f j := hm j
    rw [hs, hh]
  have heq := harmonic_eq_fixation hr hN (fun j => 1 - f j)
    (by simp [hz]) (by simp [ho]) hg i
  have hi : f i = 1 - moranFixation r N i := by linarith
  simpa only [hi] using hf i


/-- Kimura's diffusion fixation probability at scaled selection `σ / 2` is
`(1 - e^{-σ x}) / (1 - e^{-σ})` (for `σ ≠ 0`). -/
theorem kimuraFixation_half {σ : ℝ} (hσ : σ ≠ 0) (x : ℝ) :
    kimuraFixation (σ / 2) x = (1 - exp (-σ * x)) / (1 - exp (-σ)) := by
  have h : σ / 2 ≠ 0 := div_ne_zero hσ two_ne_zero
  simp only [kimuraFixation, h, ↓reduceIte]
  ring_nf

/-- **Diffusion limit of the Moran fixation probability.** With relative fitness
`r_N = 1 + σ / N` and initial count `i_N = ⌊x N⌋`, the fixation probability `φ^{(N)}_{i_N}`
tends to Kimura's `kimuraFixation (σ / 2) x`, which is `(1 - e^{-σ x}) / (1 - e^{-σ})` for
`σ ≠ 0` (`kimuraFixation_half`) and `x` for `σ = 0`. The initial frequency `x` is meaningful in
`[0, 1]`; the limit of the closed formula holds for every `x ≥ 0`, so only `0 ≤ x` is assumed
(for negative `x`, `⌊x N⌋₊ = 0` is a junk value of the truncated floor). -/
theorem tendsto_moranFixation_diffusion (σ : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun N : ℕ => moranFixation (1 + σ / N) N ⌊x * N⌋₊) atTop
      (𝓝 (kimuraFixation (σ / 2) x)) := by
  have hfloor : Tendsto (fun N : ℕ => (⌊x * N⌋₊ : ℝ) / N) atTop (𝓝 x) :=
    (tendsto_nat_floor_mul_div_atTop hx).comp tendsto_natCast_atTop_atTop
  by_cases hσ : σ = 0
  · subst σ
    simpa [moranFixation, kimuraFixation] using hfloor
  rw [kimuraFixation_half hσ]
  have hlog : Tendsto (fun N : ℕ => (N : ℝ) * log (1 + σ / N)) atTop (𝓝 σ) :=
    (Real.tendsto_mul_log_one_add_div_atTop σ).comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun N : ℕ => 1 + σ / (N : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat σ)
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < 1 + σ / (N : ℝ) :=
    hbase.eventually_const_lt zero_lt_one
  have hpow : Tendsto (fun N : ℕ => (1 + σ / (N : ℝ)) ^ ⌊x * N⌋₊) atTop
      (𝓝 (exp (x * σ))) := by
    have h := (Real.continuous_exp.tendsto (x * σ)).comp (hfloor.mul hlog)
    apply h.congr'
    filter_upwards [hpos, eventually_ne_atTop 0] with N hp hN
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
    change exp ((⌊x * N⌋₊ : ℝ) / N * ((N : ℝ) * log (1 + σ / N))) =
      (1 + σ / (N : ℝ)) ^ ⌊x * N⌋₊
    have heq : (⌊x * N⌋₊ : ℝ) / N * ((N : ℝ) * log (1 + σ / N)) =
        (⌊x * N⌋₊ : ℝ) * log (1 + σ / N) := by
      field_simp
    rw [heq, Real.exp_nat_mul, Real.exp_log hp]
  have hnum : Tendsto (fun N : ℕ => (1 + σ / (N : ℝ))⁻¹ ^ ⌊x * N⌋₊) atTop
      (𝓝 (exp (-σ * x))) := by
    simpa [inv_pow, ← Real.exp_neg, mul_comm] using hpow.inv₀ (Real.exp_ne_zero _)
  have hden : Tendsto (fun N : ℕ => (1 + σ / (N : ℝ))⁻¹ ^ N) atTop
      (𝓝 (exp (-σ))) := by
    simpa [inv_pow, ← Real.exp_neg] using
      (Real.tendsto_one_add_div_pow_exp σ).inv₀ (Real.exp_ne_zero _)
  have hden_ne : 1 - exp (-σ) ≠ 0 := by
    intro h
    have : exp (-σ) = 1 := by linarith
    exact hσ (neg_eq_zero.mp ((Real.exp_eq_one_iff (-σ)).mp this))
  apply ((tendsto_const_nhds.sub hnum).div (tendsto_const_nhds.sub hden) hden_ne).congr'
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hr : 1 + σ / (N : ℝ) ≠ 1 := by
    intro h
    have : σ / (N : ℝ) = 0 := by linarith
    exact hσ ((div_eq_zero_iff.mp this).resolve_right (Nat.cast_ne_zero.2 hN))
  simp [moranFixation, hr]

end MathlibExt.Biology.PopulationGenetics.Moran
