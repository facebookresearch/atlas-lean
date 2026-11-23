/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.GallagerExponent
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Logic.Equiv.Prod

@[expose] public section

/-!
# Gallager's random coding bound for discrete memoryless channels

Let `W : α → PMF β` be a discrete memoryless channel on finite alphabets, used `N` times: the
block transition probability is `W^N(y | x) = ∏_i W(y_i | x_i)` (`blockTransition`). A code is
a list `C : Fin M → (Fin N → α)` of `M` code words. Under maximum-likelihood decoding, with
every tie counted as an error, message `m` is decoded wrongly on the outputs `y` for which some
other code word `m' ≠ m` has `W^N(y | x_m) ≤ W^N(y | x_{m'})`; `mlErrorProb W C m` is the
probability of that event when `x_m` is sent (Gallager 1965, equations (2)-(5)).

Gallager's ensemble picks all code words independently, and every letter of every code word
independently with law `p` (equation (13)); `randomCodingAvgError p W N M m` is the ensemble
average of `mlErrorProb W C m`.

* `mul_indicator_le`: Gallager's bound (6) on the error indicator, multiplied by `W^N(y | x_m)`.
* `randomCodingAvgError_le`: the **random coding bound**, equation (17): for `0 ≤ ρ ≤ 1`,
  `P̄ₑ,ₘ ≤ (M - 1)^ρ exp(-N E₀(ρ, p))`.
* `exists_code_avgError_le`: Theorem 1: some code has average error probability (messages
  equiprobable) at most `M^ρ exp(-N E₀(ρ, p)) = exp(-N (E₀(ρ, p) - ρ R))`, `R = (ln M) / N`
  (`exists_code_avgError_le_exp_rate`).
* `exists_pos_exponent_avgError_le`: below the mutual information the average error decays
  exponentially in `N`.
* `exists_code_mlErrorProb_le`: Corollary 2, by expurgation (`mlErrorProb_comp_le`,
  `exists_injective_le_two_mul`): some code has every word's error at most
  `4 M^ρ exp(-N E₀(ρ, p))`.

Counting ties as errors makes `mlErrorProb` an upper bound for the error probability of every
maximum-likelihood decoder, whatever its tie-breaking rule, so the bounds hold for all of them.

## References

* R. G. Gallager, A simple derivation of the coding theorem and some applications, IEEE Trans.
  Inform. Theory IT-11 (1965), 3–18: Section II, equations (2)-(17), Theorem 1 and Corollary 2.
-/

namespace MathlibExt.InformationTheory.RandomCodingBound

open Real MathlibExt.InformationTheory.GallagerExponent _root_.InformationTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Block transition probability of a memoryless channel.** For a channel `W : α → PMF β`
used `N` times, `W^N(y | x) = ∏_i W(y_i | x_i)` (Gallager 1965, equation (12)). -/
noncomputable def blockTransition (W : α → PMF β) {N : ℕ} (x : Fin N → α) (y : Fin N → β) : ℝ :=
  ∏ i, ((W (x i)) (y i)).toReal

/-- **Probability of a code word in Gallager's ensemble.** Each letter is drawn independently
with law `p`: `P(x) = ∏_i p(x_i)` (Gallager 1965, equation (13)). -/
noncomputable def blockInputProb (p : PMF α) {N : ℕ} (x : Fin N → α) : ℝ :=
  ∏ i, (p (x i)).toReal

open Classical in
/-- **Error probability of maximum-likelihood decoding, ties counted as errors.** For a code
`C : Fin M → (Fin N → α)` on the channel `W`, the probability, when code word `m` is sent, of
receiving an output `y` for which some other code word `m' ≠ m` is at least as likely:
`W^N(y | x_m) ≤ W^N(y | x_{m'})` (Gallager 1965, equations (2)-(5)). -/
noncomputable def mlErrorProb (W : α → PMF β) {N M : ℕ} (C : Fin M → Fin N → α) (m : Fin M) :
    ℝ :=
  ∑ y, blockTransition W (C m) y *
    if ∃ m', m' ≠ m ∧ blockTransition W (C m) y ≤ blockTransition W (C m') y then 1 else 0

/-- **Ensemble-average error probability of random coding.** The average of
`mlErrorProb W C m` over Gallager's ensemble, in which the `M` code words of length `N` are
independent and each letter is drawn independently with law `p`, so that the code `C` has
probability `∏_{m'} ∏_i p(C m' i)` (Gallager 1965, Section II, equations (8) and (13)). -/
noncomputable def randomCodingAvgError (p : PMF α) (W : α → PMF β) (N M : ℕ) (m : Fin M) : ℝ :=
  ∑ C : Fin M → Fin N → α, (∏ m', blockInputProb p (C m')) * mlErrorProb W C m

omit [Fintype α] [Fintype β] in
theorem blockTransition_nonneg (W : α → PMF β) {N : ℕ} (x : Fin N → α) (y : Fin N → β) :
    0 ≤ blockTransition W x y :=
  Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg

omit [Fintype α] in
theorem blockInputProb_nonneg (p : PMF α) {N : ℕ} (x : Fin N → α) : 0 ≤ blockInputProb p x :=
  Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg

theorem sum_blockInputProb (p : PMF α) (N : ℕ) : ∑ x : Fin N → α, blockInputProb p x = 1 := by
  classical
  unfold blockInputProb
  rw [← Fintype.prod_sum (fun (_ : Fin N) (a : α) => (p a).toReal)]
  simp [sum_toReal_eq_one]

/-- **The inequality behind Gallager's bound (6).** If `a ≥ 0`, all `f j ≥ 0` and `a ≤ f j₀` for
one index, then `a ≤ a^s (∑_j f_j^s)^ρ` with `s = 1/(1+ρ)`, for every `ρ ≥ 0`. -/
theorem le_rpow_mul_sum_rpow {ι : Type*} [Fintype ι] {a : ℝ} {f : ι → ℝ} (ha : 0 ≤ a)
    (hf : ∀ j, 0 ≤ f j) {j₀ : ι} (h : a ≤ f j₀) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    a ≤ a ^ (1 / (1 + ρ)) * (∑ j, f j ^ (1 / (1 + ρ))) ^ ρ := by
  have hs : 0 < 1 / (1 + ρ) := by positivity
  rcases ha.lt_or_eq with ha' | ha'
  · have h1 : a ^ (1 / (1 + ρ)) ≤ ∑ j, f j ^ (1 / (1 + ρ)) :=
      (Real.rpow_le_rpow ha h hs.le).trans
        (Finset.single_le_sum (f := fun j => f j ^ (1 / (1 + ρ)))
          (fun j _ => Real.rpow_nonneg (hf j) _) (Finset.mem_univ j₀))
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg ha _) h1 hρ
    calc a = a ^ (1 / (1 + ρ)) * (a ^ (1 / (1 + ρ))) ^ ρ := by
          rw [← Real.rpow_mul ha, ← Real.rpow_add ha']
          have : 1 / (1 + ρ) + 1 / (1 + ρ) * ρ = 1 := by field_simp
          rw [this, Real.rpow_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg ha _)
  · rw [← ha']
    exact mul_nonneg (Real.rpow_nonneg le_rfl _)
      (Real.rpow_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hf j) _) _)

omit [Fintype α] [Fintype β] in
open Classical in
/-- **Gallager's bound on the error indicator** (Gallager 1965, equation (6), multiplied by
`W^N(y | x_m)`). For `ρ ≥ 0`, writing `s = 1/(1+ρ)`,
`W^N(y|x_m) · 1[some m' ≠ m has W^N(y|x_m) ≤ W^N(y|x_{m'})]
  ≤ W^N(y|x_m)^s (∑_{m' ≠ m} W^N(y|x_{m'})^s)^ρ`. -/
theorem mul_indicator_le (W : α → PMF β) {N M : ℕ} (C : Fin M → Fin N → α) (m : Fin M)
    (y : Fin N → β) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    blockTransition W (C m) y *
        (if ∃ m', m' ≠ m ∧ blockTransition W (C m) y ≤ blockTransition W (C m') y then 1 else 0)
      ≤ blockTransition W (C m) y ^ (1 / (1 + ρ)) *
        (∑ j : {j // j ≠ m}, blockTransition W (C j) y ^ (1 / (1 + ρ))) ^ ρ := by
  have ha := blockTransition_nonneg W (C m) y
  have hf : ∀ j : {j // j ≠ m}, 0 ≤ blockTransition W (C j) y :=
    fun j => blockTransition_nonneg W _ y
  split_ifs with h
  · obtain ⟨m', hm', hle⟩ := h
    rw [mul_one]
    exact le_rpow_mul_sum_rpow (f := fun j : {j // j ≠ m} => blockTransition W (C j) y) ha hf
      (j₀ := ⟨m', hm'⟩) hle hρ
  · rw [mul_zero]
    exact mul_nonneg (Real.rpow_nonneg ha _)
      (Real.rpow_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hf j) _) _)

/-- **Marginal of an independent product.** For a law `P` on `X` (nonnegative, total mass `1`),
averaging a function of the `i₀`-th coordinate over the product law `∏_i P(c i)` on `ι → X`
gives its average under `P`. -/
theorem sum_prod_mul_apply {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]
    (P : X → ℝ) (hP : ∑ x, P x = 1) (i₀ : ι) (f : X → ℝ) :
    ∑ c : ι → X, (∏ i, P (c i)) * f (c i₀) = ∑ x, P x * f x := by
  have key := Fintype.prod_sum (fun (i : ι) (x : X) => P x * if i = i₀ then f x else 1)
  have hl : ∀ c : ι → X, (∏ i, P (c i) * if i = i₀ then f (c i) else 1) =
      (∏ i, P (c i)) * f (c i₀) := by
    intro c
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i₀ (fun i => f (c i))]
    simp
  simp_rw [hl] at key
  rw [← key]
  rw [Finset.prod_eq_single i₀]
  · simp
  · intro i _ hi
    simp [hi, hP]
  · simp

omit [Fintype β] in
/-- **Letter-by-letter factorisation.** Under Gallager's ensemble, the output sum
`∑_x P(x) W^N(y | x)^{1/(1+ρ)}` is the product over the letters of `y` of
`∑_a p(a) W(y_i | a)^{1/(1+ρ)}` (Gallager 1965, equations (14)-(16)). -/
theorem sum_blockInputProb_mul_rpow (p : PMF α) (W : α → PMF β) {N : ℕ} (y : Fin N → β)
    (ρ : ℝ) :
    ∑ x : Fin N → α, blockInputProb p x * blockTransition W x y ^ (1 / (1 + ρ)) =
      ∏ i, gallagerInner p W ρ (y i) := by
  classical
  unfold gallagerInner
  rw [Fintype.prod_sum (fun (i : Fin N) (a : α) =>
    (p a).toReal * ((W a) (y i)).toReal ^ (1 / (1 + ρ)))]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold blockInputProb blockTransition
  rw [← Real.finsetProd_rpow _ _ (fun _ _ => ENNReal.toReal_nonneg), ← Finset.prod_mul_distrib]

/-- **`exp(-N E₀)` as a power.** `exp(-N E₀(ρ, p))` is the `N`-th power of
`∑_b (∑_a p(a) W(b|a)^{1/(1+ρ)})^{1+ρ}`. -/
theorem exp_neg_mul_gallagerE0 (p : PMF α) (W : α → PMF β) (N : ℕ) (ρ : ℝ) :
    Real.exp (-(N * gallagerE0 p W ρ)) = (∑ b, gallagerInner p W ρ b ^ (1 + ρ)) ^ N := by
  rw [gallagerE0, mul_neg, neg_neg, Real.exp_nat_mul,
    Real.exp_log (sum_gallagerInner_rpow_pos p W ρ)]

/-- **Gallager's random coding bound** (R. G. Gallager, A simple derivation of the coding theorem
and some applications, IEEE Trans. Inform. Theory IT-11 (1965), equation (17)). For a discrete
memoryless channel `W` on finite alphabets, every input law `p`, every block length `N`, every
number `M` of code words, every message `m` and every `0 ≤ ρ ≤ 1`, the error probability of
maximum-likelihood decoding (ties counted as errors), averaged over Gallager's ensemble of codes
with independent letters of law `p`, satisfies
`P̄ₑ,ₘ ≤ (M - 1)^ρ exp(-N E₀(ρ, p))`. -/
theorem randomCodingAvgError_le (p : PMF α) (W : α → PMF β) (N M : ℕ) (m : Fin M) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    randomCodingAvgError p W N M m ≤
      ((M : ℝ) - 1) ^ ρ * Real.exp (-(N * gallagerE0 p W ρ)) := by
  classical
  set s : ℝ := 1 / (1 + ρ)
  set Z : (Fin N → β) → (Fin N → α) → ℝ := fun y x => blockTransition W x y ^ s
  set P : (Fin N → α) → ℝ := blockInputProb p
  set EZ : (Fin N → β) → ℝ := fun y => ∑ x, P x * Z y x
  have hP0 : ∀ x, 0 ≤ P x := blockInputProb_nonneg p
  have hP1 : ∑ x, P x = 1 := sum_blockInputProb p N
  have hZ0 : ∀ y x, 0 ≤ Z y x := fun y x => Real.rpow_nonneg (blockTransition_nonneg W x y) _
  have hEZ0 : ∀ y, 0 ≤ EZ y := fun y => Finset.sum_nonneg fun x _ => mul_nonneg (hP0 x) (hZ0 y x)
  have hcard : (Fintype.card {j : Fin M // j ≠ m} : ℝ) = (M : ℝ) - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
    have : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact m.elim0)
    push_cast [this]
    ring
  -- Step 1: Jensen over the other code words, for a fixed output `y`.
  have hJensen : ∀ y, ∑ r : {j : Fin M // j ≠ m} → (Fin N → α),
      (∏ j, P (r j)) * (∑ j, Z y (r j)) ^ ρ ≤ (((M : ℝ) - 1) * EZ y) ^ ρ := by
    intro y
    have hw0 : ∀ r ∈ (Finset.univ : Finset ({j : Fin M // j ≠ m} → (Fin N → α))),
        0 ≤ ∏ j, P (r j) := fun r _ => Finset.prod_nonneg fun j _ => hP0 _
    have hw1 : ∑ r : {j : Fin M // j ≠ m} → (Fin N → α), ∏ j, P (r j) = 1 := by
      rw [← Fintype.prod_sum (fun (_ : {j : Fin M // j ≠ m}) x => P x)]
      simp [hP1]
    have := (concaveOn_rpow hρ0 hρ1).le_map_sum hw0 hw1
      (p := fun r => ∑ j, Z y (r j))
      (fun r _ => Set.mem_Ici.2 (Finset.sum_nonneg fun j _ => hZ0 y _))
    simp only [smul_eq_mul] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [sum_prod_mul_apply P hP1 _ (Z y)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  -- Step 2: bound the error indicator and average.
  have hstep : randomCodingAvgError p W N M m ≤
      ∑ y, ∑ C : Fin M → Fin N → α, (∏ m', P (C m')) *
        (Z y (C m) * (∑ j : {j // j ≠ m}, Z y (C j)) ^ ρ) := by
    unfold randomCodingAvgError mlErrorProb
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun C _ => ?_
    exact mul_le_mul_of_nonneg_left (mul_indicator_le W C m y hρ0)
      (Finset.prod_nonneg fun _ _ => hP0 _)
  refine hstep.trans ?_
  -- Step 3: split off the code word `m` and apply Jensen to the others.
  have hsplit : ∀ y, ∑ C : Fin M → Fin N → α, (∏ m', P (C m')) *
      (Z y (C m) * (∑ j : {j // j ≠ m}, Z y (C j)) ^ ρ) ≤
      ((M : ℝ) - 1) ^ ρ * EZ y ^ (1 + ρ) := by
    intro y
    let e := Equiv.piSplitAt m (fun _ : Fin M => Fin N → α)
    let F : (Fin N → α) × ({j : Fin M // j ≠ m} → (Fin N → α)) → ℝ := fun q =>
      (P q.1 * ∏ j, P (q.2 j)) * (Z y q.1 * (∑ j, Z y (q.2 j)) ^ ρ)
    have hF : ∀ C, (∏ m', P (C m')) * (Z y (C m) * (∑ j : {j // j ≠ m}, Z y (C j)) ^ ρ) =
        F (e C) := by
      intro C
      simp only [F, e, Equiv.piSplitAt_apply]
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ m]
    simp_rw [hF]
    rw [e.sum_comp F, Fintype.sum_prod_type]
    have : ∀ x, ∑ r : {j : Fin M // j ≠ m} → (Fin N → α), F (x, r) =
        P x * Z y x * ∑ r : {j : Fin M // j ≠ m} → (Fin N → α),
          (∏ j, P (r j)) * (∑ j, Z y (r j)) ^ ρ := by
      intro x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [F]
      ring
    simp_rw [this]
    calc ∑ x, P x * Z y x * ∑ r : {j : Fin M // j ≠ m} → (Fin N → α),
          (∏ j, P (r j)) * (∑ j, Z y (r j)) ^ ρ
        ≤ ∑ x, P x * Z y x * (((M : ℝ) - 1) * EZ y) ^ ρ :=
          Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (hJensen y) (mul_nonneg (hP0 x) (hZ0 y x))
      _ = EZ y * (((M : ℝ) - 1) * EZ y) ^ ρ := by rw [← Finset.sum_mul]
      _ = ((M : ℝ) - 1) ^ ρ * EZ y ^ (1 + ρ) := by
          have hM : (0 : ℝ) ≤ (M : ℝ) - 1 := by rw [← hcard]; positivity
          rw [Real.mul_rpow hM (hEZ0 y), Real.rpow_add' (hEZ0 y) (by positivity), Real.rpow_one]
          ring
  refine (Finset.sum_le_sum fun y _ => hsplit y).trans (le_of_eq ?_)
  -- Step 4: the output sum factorises letter by letter.
  rw [← Finset.mul_sum, exp_neg_mul_gallagerE0 p W N ρ]
  congr 1
  have hEZ : ∀ y, EZ y = ∏ i, gallagerInner p W ρ (y i) :=
    fun y => sum_blockInputProb_mul_rpow p W y ρ
  simp_rw [hEZ]
  rw [← Fin.prod_const N (∑ b, gallagerInner p W ρ b ^ (1 + ρ)),
    Fintype.prod_sum (fun (_ : Fin N) b => gallagerInner p W ρ b ^ (1 + ρ))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Real.finsetProd_rpow _ _ (fun i _ => gallagerInner_nonneg p W ρ _)]

theorem sum_prod_blockInputProb (p : PMF α) (N M : ℕ) :
    ∑ C : Fin M → Fin N → α, ∏ m', blockInputProb p (C m') = 1 := by
  classical
  rw [← Fintype.prod_sum (fun (_ : Fin M) (x : Fin N → α) => blockInputProb p x)]
  simp [sum_blockInputProb]

/-- **Gallager's coding theorem for discrete memoryless channels** (R. G. Gallager, A simple
derivation of the coding theorem and some applications, IEEE Trans. Inform. Theory IT-11 (1965),
Theorem 1). For a discrete memoryless channel `W` on finite alphabets, every input law `p`, every
block length `N`, every number `M ≥ 1` of code words and every `0 ≤ ρ ≤ 1`, there is a code whose
error probability under maximum-likelihood decoding (ties counted as errors), averaged over
equiprobable messages, is at most `M^ρ exp(-N E₀(ρ, p))`. With `M = e^{NR}` this is Gallager's
`Pₑ ≤ exp(-N(E₀(ρ, p) - ρ R))` (`exists_code_avgError_le_exp_rate`). -/
theorem exists_code_avgError_le (p : PMF α) (W : α → PMF β) (N M : ℕ) (hM : 0 < M) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : Fin M → Fin N → α,
      (∑ m, mlErrorProb W C m) / M ≤ (M : ℝ) ^ ρ * Real.exp (-(N * gallagerE0 p W ρ)) := by
  classical
  set B := (M : ℝ) ^ ρ * Real.exp (-(N * gallagerE0 p W ρ))
  set PC : (Fin M → Fin N → α) → ℝ := fun C => ∏ m', blockInputProb p (C m')
  have hPC0 : ∀ C, 0 ≤ PC C := fun C => Finset.prod_nonneg fun _ _ => blockInputProb_nonneg p _
  have hPC1 : ∑ C, PC C = 1 := sum_prod_blockInputProb p N M
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have havg : ∑ C, PC C * ((∑ m, mlErrorProb W C m) / M) ≤ B := by
    have : ∑ C, PC C * ((∑ m, mlErrorProb W C m) / M) =
        (∑ m, randomCodingAvgError p W N M m) / M := by
      unfold randomCodingAvgError
      simp only [PC, Finset.sum_div, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [this, div_le_iff₀ hMR]
    calc ∑ m, randomCodingAvgError p W N M m
        ≤ ∑ _m : Fin M, ((M : ℝ) - 1) ^ ρ * Real.exp (-(N * gallagerE0 p W ρ)) :=
          Finset.sum_le_sum fun m _ => randomCodingAvgError_le p W N M m hρ0 hρ1
      _ ≤ ∑ _m : Fin M, B := by
          refine Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact Real.rpow_le_rpow (by have : (1 : ℝ) ≤ M := by exact_mod_cast hM
                                      linarith) (by linarith) hρ0
      _ = B * M := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_comm]
  by_contra h
  push Not at h
  obtain ⟨C₀, hC₀⟩ : ∃ C, 0 < PC C := by
    by_contra h'
    push Not at h'
    have : ∑ C, PC C ≤ 0 := Finset.sum_nonpos fun C _ => h' C
    linarith
  have : ∑ C, PC C * B < ∑ C, PC C * ((∑ m, mlErrorProb W C m) / M) :=
    Finset.sum_lt_sum (fun C _ => mul_le_mul_of_nonneg_left (h C).le (hPC0 C))
      ⟨C₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (h C₀) hC₀⟩
  rw [← Finset.sum_mul, hPC1, one_mul] at this
  linarith

/-- **Gallager's coding theorem, rate form** (Gallager 1965, Theorem 1, equation (19)). For
`N ≥ 1` and `M ≥ 1` code words, at rate `R = (ln M) / N` nats per channel use, some code has
average error probability at most `exp(-N (E₀(ρ, p) - ρ R))`, for every `0 ≤ ρ ≤ 1`. -/
theorem exists_code_avgError_le_exp_rate (p : PMF α) (W : α → PMF β) {N M : ℕ} (hN : 0 < N)
    (hM : 0 < M) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : Fin M → Fin N → α, (∑ m, mlErrorProb W C m) / M ≤
      Real.exp (-(N * (gallagerE0 p W ρ - ρ * (Real.log M / N)))) := by
  obtain ⟨C, hC⟩ := exists_code_avgError_le p W N M hM hρ0 hρ1
  refine ⟨C, hC.trans (le_of_eq ?_)⟩
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Real.rpow_def_of_pos hMR, ← Real.exp_add]
  congr 1
  field_simp
  ring

omit [Fintype α] in
/-- **Coding theorem, exponential achievability for average error.** For a discrete memoryless
channel `W` on finite alphabets, an input law `p` and a rate `R` (nats per channel use) below
the mutual information `I(p; W)` in nats, there is an exponent `E > 0` such that for every block
length `N` and every number of code words `1 ≤ M ≤ e^{NR}` some code has average error
probability (equiprobable messages, maximum-likelihood decoding, ties counted as errors) at most
`e^{-NE}`. This is the achievability half of Shannon's theorem in the form Gallager derives from
Theorem 1 (Gallager 1965, Theorem 1 with Section III: `E(R) > 0` for `R < C`), for the average
error and a fixed input law `p`. Choosing `p` with `I(p; W)` close to the capacity gives every
rate below capacity; the maximal-error form, through `exists_code_mlErrorProb_le`, is
`ChannelCodingAchievability.channelCoding_achievability`. -/
theorem exists_pos_exponent_avgError_le {α : Type*} [Finite α] (p : PMF α) (W : α → PMF β) {R : ℝ}
    (hR : R < finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a)) * Real.log 2) :
    ∃ E > 0, ∀ N M : ℕ, 0 < M → (M : ℝ) ≤ Real.exp (N * R) →
      ∃ C : Fin M → Fin N → α, (∑ m, mlErrorProb W C m) / M ≤ Real.exp (-(N * E)) := by
  have := Fintype.ofFinite α
  obtain ⟨ρ, ⟨hρ0, hρ1⟩, hpos⟩ := exists_gallagerE0_sub_pos p W hR
  refine ⟨gallagerE0 p W ρ - ρ * R, hpos, fun N M hM hMR => ?_⟩
  obtain ⟨C, hC⟩ := exists_code_avgError_le p W N M hM hρ0.le hρ1
  refine ⟨C, hC.trans ?_⟩
  calc (M : ℝ) ^ ρ * Real.exp (-(N * gallagerE0 p W ρ))
      ≤ Real.exp (N * R) ^ ρ * Real.exp (-(N * gallagerE0 p W ρ)) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg M) hMR hρ0.le)
          (Real.exp_pos _).le
    _ = Real.exp (-(N * (gallagerE0 p W ρ - ρ * R))) := by
        rw [← Real.exp_mul, ← Real.exp_add]
        ring_nf

omit [Fintype α] in
/-- **Removing code words does not increase the error.** If the code `C ∘ e` keeps the words of
`C` at the injective positions `e`, then under maximum-likelihood decoding with ties counted as
errors every kept word has at most its error probability in `C`: it has fewer competitors. -/
theorem mlErrorProb_comp_le (W : α → PMF β) {N K M : ℕ} (C : Fin K → Fin N → α)
    {e : Fin M → Fin K} (he : Function.Injective e) (m : Fin M) :
    mlErrorProb W (C ∘ e) m ≤ mlErrorProb W C (e m) := by
  classical
  unfold mlErrorProb
  refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (blockTransition_nonneg W _ y)
  split_ifs with h1 h2 <;> try norm_num
  obtain ⟨m', hm', hle⟩ := h1
  exact h2 ⟨e m', fun h => hm' (he h), hle⟩

/-- **Selecting the better half of a code.** If `2M` nonnegative numbers have sum at most
`2M A`, then at least `M` of them are at most `2A`: there is an injection `e : Fin M → Fin (2M)`
with `x (e m) ≤ 2A` for every `m`. -/
theorem exists_injective_le_two_mul {M : ℕ} (x : Fin (2 * M) → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hsum : ∑ k, x k ≤ (2 * M : ℕ) * A) (hx : ∀ k, 0 ≤ x k) :
    ∃ e : Fin M → Fin (2 * M), Function.Injective e ∧ ∀ m, x (e m) ≤ 2 * A := by
  classical
  set S := Finset.univ.filter fun k => x k ≤ 2 * A
  have hS : M ≤ S.card := by
    by_contra h
    push Not at h
    have hc : M + 1 ≤ Sᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]; omega
    have hlt : ∑ _k ∈ Sᶜ, 2 * A < ∑ k ∈ Sᶜ, x k := by
      refine Finset.sum_lt_sum_of_nonempty (Finset.card_pos.1 (by omega)) fun k hk => ?_
      simpa [S] using hk
    have hle : ∑ k ∈ Sᶜ, x k ≤ ∑ k, x k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => hx k
    rw [Finset.sum_const, nsmul_eq_mul] at hlt
    have : ((M + 1 : ℕ) : ℝ) * (2 * A) ≤ (Sᶜ.card : ℝ) * (2 * A) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    push_cast at this hsum
    nlinarith
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hS
  refine ⟨fun m => T.orderEmbOfFin hT m, (T.orderEmbOfFin hT).injective, fun m => ?_⟩
  have := hTS (T.orderEmbOfFin_mem hT m)
  simpa [S] using this

/-- **Expurgated random coding bound, maximal error** (R. G. Gallager, A simple derivation of the
coding theorem and some applications, IEEE Trans. Inform. Theory IT-11 (1965), Corollary 2). For a
discrete memoryless channel `W` on finite alphabets, every input law `p`, every block length `N`,
every number `M ≥ 1` of code words and every `0 ≤ ρ ≤ 1`, there is a code in which every code
word `m` has error probability under maximum-likelihood decoding (ties counted as errors) at most
`4 M^ρ exp(-N E₀(ρ, p))`. This is the fixed-`(ρ, p)` form of Gallager's proof
(`2 (2M)^ρ ≤ 4 M^ρ` for `ρ ≤ 1`); optimising over `ρ` and `p` at `M = e^{NR}` gives his
`Pₑ,ₘ ≤ 4 exp(-N E(R))`, equation (23). -/
theorem exists_code_mlErrorProb_le (p : PMF α) (W : α → PMF β) (N M : ℕ) (hM : 0 < M) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : Fin M → Fin N → α, ∀ m,
      mlErrorProb W C m ≤ 4 * (M : ℝ) ^ ρ * Real.exp (-(N * gallagerE0 p W ρ)) := by
  obtain ⟨C', hC'⟩ := exists_code_avgError_le p W N (2 * M) (by omega) hρ0 hρ1
  set A := ((2 * M : ℕ) : ℝ) ^ ρ * Real.exp (-(N * gallagerE0 p W ρ))
  have hA : 0 ≤ A := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.exp_pos _).le
  have h2M : (0 : ℝ) < ((2 * M : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * M)
  have hsum : ∑ k, mlErrorProb W C' k ≤ ((2 * M : ℕ) : ℝ) * A := by
    rw [div_le_iff₀ h2M] at hC'
    linarith
  have hnn : ∀ k, 0 ≤ mlErrorProb W C' k := fun k => Finset.sum_nonneg fun y _ =>
    mul_nonneg (blockTransition_nonneg W _ y) (by split_ifs <;> norm_num)
  obtain ⟨e, he, hle⟩ := exists_injective_le_two_mul _ hA hsum hnn
  refine ⟨C' ∘ e, fun m => (mlErrorProb_comp_le W C' he m).trans ((hle m).trans ?_)⟩
  have hM' : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h2 : ((2 * M : ℕ) : ℝ) ^ ρ ≤ 2 * (M : ℝ) ^ ρ := by
    rw [Nat.cast_mul, Nat.cast_two, Real.mul_rpow (by norm_num) hM']
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hM' _)
    calc (2 : ℝ) ^ ρ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hρ1
      _ = 2 := Real.rpow_one 2
  have := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-(N * gallagerE0 p W ρ))).le
  simp only [A]
  linarith

end MathlibExt.InformationTheory.RandomCodingBound
