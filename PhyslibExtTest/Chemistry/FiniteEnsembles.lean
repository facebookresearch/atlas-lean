/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.FiniteEnsembles

/-!

# Tests for finite-state ensembles and partition functions

-/

@[expose] public section

open Chemistry.FiniteEnsembles

namespace PhyslibExtTest.Chemistry.FiniteEnsembles

/-!

## A. Partition function and Boltzmann distribution

-/

/-- A three-state system with energies `0`, `1` and `2` at `β = 1`. -/
example : partitionFunction (![0, 1, 2] : Fin 3 → ℝ) 1 = 1 + Real.exp (-1) + Real.exp (-2) := by
  simp [partitionFunction, Fin.sum_univ_three]

example (E : Fin 3 → ℝ) (β : ℝ) : 0 < partitionFunction E β :=
  partitionFunction_pos E β

example (E : Fin 3 → ℝ) (β : ℝ) (i : Fin 3) :
    0 < boltzmannProb E β i ∧ 0 ≤ boltzmannProb E β i :=
  ⟨boltzmannProb_pos E β i, boltzmannProb_nonneg E β i⟩

example (E : Fin 3 → ℝ) (β : ℝ) : ∑ i, boltzmannProb E β i = 1 :=
  sum_boltzmannProb_eq_one E β

example (E : Fin 3 → ℝ) (β : ℝ) (i : Fin 3) :
    Real.log (boltzmannProb E β i) = -β * E i - Real.log (partitionFunction E β) :=
  log_boltzmannProb E β i

/-- (e) Boundary case: the empty state space, excluded by `Nonempty ι`, has partition function
`0` and Boltzmann probabilities summing to `0`, not `1`. So `partitionFunction_pos` and
`sum_boltzmannProb_eq_one` need their `Nonempty` instance. -/
example (E : Empty → ℝ) (β : ℝ) : partitionFunction E β = 0 ∧ ∑ i, boltzmannProb E β i = 0 := by
  simp [partitionFunction]

/-- (e) Boundary case: `Empty` has no `Nonempty` instance. -/
example : ¬ Nonempty Empty :=
  not_nonempty_empty

/-!

## B. Entropy maximization

-/

/-- The uniform distribution on two states. -/
noncomputable def uniformTwo (_i : Fin 2) : ℝ :=
  1 / 2

/-- The uniform distribution is nonnegative. -/
lemma uniformTwo_nonneg : ∀ i, 0 ≤ uniformTwo i := by
  intro i
  norm_num [uniformTwo]

/-- The uniform distribution sums to `1`. -/
lemma sum_uniformTwo : ∑ i, uniformTwo i = 1 := by
  norm_num [uniformTwo, Fin.sum_univ_two]

example {ι : Type*} [Fintype ι] {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1) : 0 ≤ ∑ i, p i * Real.log (p i / q i) :=
  sum_mul_log_div_nonneg hp hp1 hq hq1

/-- No `Nonempty` instance is needed here: it follows from `∑ i, p i = 1`. -/
example {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) : 0 ≤ ∑ i, p i * Real.log (p i / boltzmannProb E β i) :=
  sum_mul_log_div_boltzmannProb_nonneg E β hp hp1

/-- Gibbs' inequality is strict away from the Boltzmann distribution: at `β * Δ = log 3` the
uniform distribution has positive relative entropy to the two-level Boltzmann distribution. -/
example {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    0 < ∑ i, uniformTwo i * Real.log (uniformTwo i / boltzmannProb (twoLevelEnergy Δ) β i) := by
  refine lt_of_le_of_ne
    (sum_mul_log_div_boltzmannProb_nonneg _ _ uniformTwo_nonneg sum_uniformTwo) (Ne.symm ?_)
  rw [Ne, sum_mul_log_div_boltzmannProb_eq_zero_iff _ _ uniformTwo_nonneg sum_uniformTwo]
  intro h
  have h1 := congrFun h 1
  rw [boltzmannProb_twoLevelEnergy_one hβΔ, uniformTwo] at h1
  norm_num at h1

/-- The relative entropy of the Boltzmann distribution to itself is `0`. -/
example (E : Fin 3 → ℝ) (β : ℝ) :
    ∑ i, boltzmannProb E β i * Real.log (boltzmannProb E β i / boltzmannProb E β i) = 0 :=
  (sum_mul_log_div_boltzmannProb_eq_zero_iff E β (boltzmannProb_nonneg E β)
    (sum_boltzmannProb_eq_one E β)).mpr rfl

example (E : Fin 3 → ℝ) (β : ℝ) {p : Fin 3 → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hU : ∑ i, p i * E i = ∑ i, boltzmannProb E β i * E i) :
    shannonEntropy p ≤ shannonEntropy (boltzmannProb E β) :=
  shannonEntropy_le_shannonEntropy_boltzmannProb E β hp hp1 hU

example (E : Fin 3 → ℝ) (β : ℝ) {p : Fin 3 → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hU : ∑ i, p i * E i = ∑ i, boltzmannProb E β i * E i) :
    shannonEntropy p = shannonEntropy (boltzmannProb E β) ↔ p = boltzmannProb E β :=
  shannonEntropy_eq_shannonEntropy_boltzmannProb_iff E β hp hp1 hU

/-- (e) Boundary case: the mean-energy hypothesis of the maximum-entropy theorem is needed. For the
two-level system with `0 < Δ` at `β * Δ = log 3`, the uniform distribution has the mean energy
`Δ / 2 ≠ Δ / 4` and the larger entropy `log 2 > log 4 - 3 / 4 * log 3`. -/
example {β Δ : ℝ} (hΔ : 0 < Δ) (hβΔ : β * Δ = Real.log 3) :
    ∑ i, uniformTwo i * twoLevelEnergy Δ i ≠
        ∑ i, boltzmannProb (twoLevelEnergy Δ) β i * twoLevelEnergy Δ i ∧
      shannonEntropy (boltzmannProb (twoLevelEnergy Δ) β) < shannonEntropy uniformTwo := by
  simp only [shannonEntropy, Fin.sum_univ_two, boltzmannProb_twoLevelEnergy_zero hβΔ,
    boltzmannProb_twoLevelEnergy_one hβΔ, uniformTwo, twoLevelEnergy_zero, twoLevelEnergy_one]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, Nat.cast_ofNat]
  have h16 : 4 * Real.log 2 < 3 * Real.log 3 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2 ^ 4) (by norm_num : (2 : ℝ) ^ 4 < 3 ^ 3)
    rwa [Real.log_pow, Real.log_pow, Nat.cast_ofNat, Nat.cast_ofNat] at h
  refine ⟨fun h => hΔ.ne' (by linarith), ?_⟩
  rw [Real.log_div (by norm_num) (by norm_num), one_div, one_div, Real.log_inv, Real.log_inv,
    hlog4]
  nlinarith

/-!

## C. Thermodynamic functions and fluctuations

The positive-temperature requirement: `0 < β` and `0 < kB` are explicit hypotheses exactly of the
lemmas that use them, `temperature_pos`, `helmholtzFreeEnergy_eq_meanEnergy_sub_entropy_div`,
`helmholtzFreeEnergy_eq_meanEnergy_sub_temperature_mul_entropy`,
`helmholtzFreeEnergy_eq_neg_mul_temperature_mul_log` and `heatCapacity_eq_energyVariance_div`
(with `0 < kB` alone for `heatCapacity_nonneg`). No example specializes `β` to `0` or to a
negative value; the examples for a general `β` are finite-sum identities, valid for every real `β`.

-/

example {kB β : ℝ} (hkB : 0 < kB) (hβ : 0 < β) : 0 < temperature kB β :=
  temperature_pos hkB hβ

example (E : Fin 3 → ℝ) (β : ℝ) : 0 ≤ energyVariance E β :=
  energyVariance_nonneg E β

example {kB : ℝ} (hkB : 0 < kB) (E : Fin 3 → ℝ) (β : ℝ) : 0 ≤ heatCapacity kB E β :=
  heatCapacity_nonneg hkB E β

example (kB : ℝ) (E : Fin 3 → ℝ) (β : ℝ) :
    entropy kB E β = kB * shannonEntropy (boltzmannProb E β) :=
  entropy_eq_mul_shannonEntropy kB E β

example {kB β : ℝ} (hkB : 0 < kB) (hβ : 0 < β) (E : Fin 3 → ℝ) :
    helmholtzFreeEnergy E β = meanEnergy E β - entropy kB E β / (kB * β) :=
  helmholtzFreeEnergy_eq_meanEnergy_sub_entropy_div hkB hβ E

example {kB β : ℝ} (hkB : 0 < kB) (hβ : 0 < β) (E : Fin 3 → ℝ) :
    helmholtzFreeEnergy E β = meanEnergy E β - temperature kB β * entropy kB E β :=
  helmholtzFreeEnergy_eq_meanEnergy_sub_temperature_mul_entropy hkB hβ E

example {kB β : ℝ} (hkB : 0 < kB) (hβ : 0 < β) (E : Fin 3 → ℝ) :
    helmholtzFreeEnergy E β =
      -(kB * temperature kB β) * Real.log (partitionFunction E β) :=
  helmholtzFreeEnergy_eq_neg_mul_temperature_mul_log hkB hβ E

example (E : Fin 3 → ℝ) (β : ℝ) :
    deriv (fun b => Real.log (partitionFunction E b)) β = -(meanEnergy E β) :=
  deriv_log_partitionFunction E β

example (E : Fin 3 → ℝ) (β : ℝ) :
    deriv (fun b => meanEnergy E b) β = -(energyVariance E β) :=
  deriv_meanEnergy E β

example (kB : ℝ) (E : Fin 3 → ℝ) (β : ℝ) :
    heatCapacity kB E β = -(kB * β ^ 2) * deriv (fun b => meanEnergy E b) β :=
  heatCapacity_eq_neg_mul_deriv_meanEnergy kB E β

example {kB β : ℝ} (hkB : 0 < kB) (hβ : 0 < β) (E : Fin 3 → ℝ) :
    heatCapacity kB E β = energyVariance E β / (kB * temperature kB β ^ 2) :=
  heatCapacity_eq_energyVariance_div hkB hβ E

/-- The two-level system at `β * Δ = log 3`: `d(log Z)/dβ = -Δ / 4`. -/
example {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    deriv (fun b => Real.log (partitionFunction (twoLevelEnergy Δ) b)) β = -(Δ / 4) := by
  rw [deriv_log_partitionFunction, meanEnergy_twoLevelEnergy hβΔ]

/-- The two-level system at `β * Δ = log 3`: `S = kB * (log 4 - 3 / 4 * log 3)`. -/
example (kB : ℝ) {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    entropy kB (twoLevelEnergy Δ) β = kB * (Real.log 4 - 3 / 4 * Real.log 3) := by
  rw [entropy, partitionFunction_twoLevelEnergy_eq hβΔ, meanEnergy_twoLevelEnergy hβΔ,
    Real.log_div (by norm_num) (by norm_num), show β * (Δ / 4) = β * Δ / 4 by ring, hβΔ]
  ring

/-- The two-level worked example is at a positive temperature: for `0 < kB` and `0 < Δ`,
`β * Δ = log 3` gives `0 < T`. -/
example {kB β Δ : ℝ} (hkB : 0 < kB) (hΔ : 0 < Δ) (hβΔ : β * Δ = Real.log 3) :
    0 < temperature kB β :=
  temperature_pos hkB (pos_of_mul_eq_log_three hΔ hβΔ)

/-!

## D. Independent subsystems

-/

example {ι κ : Type*} [Fintype ι] [Fintype κ] (E₁ : ι → ℝ) (E₂ : κ → ℝ) (β : ℝ) (i : ι)
    (j : κ) :
    partitionFunction (combinedEnergy E₁ E₂) β =
        partitionFunction E₁ β * partitionFunction E₂ β ∧
      boltzmannProb (combinedEnergy E₁ E₂) β (i, j) =
        boltzmannProb E₁ β i * boltzmannProb E₂ β j :=
  ⟨partitionFunction_combinedEnergy E₁ E₂ β, boltzmannProb_combinedEnergy E₁ E₂ β i j⟩

/-- Two independent two-level systems at `β * Δ = log 3`: `Z = (4 / 3) ^ 2 = 16 / 9`. -/
example {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    partitionFunction (combinedEnergy (twoLevelEnergy Δ) (twoLevelEnergy Δ)) β = 16 / 9 := by
  rw [partitionFunction_combinedEnergy, partitionFunction_twoLevelEnergy_eq hβΔ]
  norm_num

/-- The doubly excited state of the two two-level systems has probability `1 / 16`. -/
example {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    boltzmannProb (combinedEnergy (twoLevelEnergy Δ) (twoLevelEnergy Δ)) β (1, 1) = 1 / 16 := by
  rw [boltzmannProb_combinedEnergy, boltzmannProb_twoLevelEnergy_one hβΔ]
  norm_num

/-- The two two-level systems have mean energy `Δ / 4 + Δ / 4 = Δ / 2`. -/
example {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    meanEnergy (combinedEnergy (twoLevelEnergy Δ) (twoLevelEnergy Δ)) β = Δ / 2 := by
  rw [meanEnergy_combinedEnergy, meanEnergy_twoLevelEnergy hβΔ]
  ring

/-- (e) Boundary case: `meanEnergy_combinedEnergy` needs its `Nonempty` instances. With an empty
second factor the combined system is empty and has mean energy `0`, while one state of energy `1`
and the empty system have mean energies adding up to `1`. -/
example (β : ℝ) (E₂ : Empty → ℝ) :
    meanEnergy (combinedEnergy (fun _ : Fin 1 => (1 : ℝ)) E₂) β = 0 ∧
      meanEnergy (fun _ : Fin 1 => (1 : ℝ)) β + meanEnergy E₂ β = 1 := by
  constructor
  · simp [meanEnergy]
  · simp [meanEnergy, boltzmannProb, partitionFunction]

/-!

## E. Two-level system

-/

example (Δ β : ℝ) :
    partitionFunction (twoLevelEnergy Δ) β = Real.exp 0 + Real.exp (-β * Δ) :=
  partitionFunction_twoLevelEnergy Δ β

/-- The two-state sum at `β * Δ = log 3`, stated exactly: `exp 0 + exp (-β * Δ) = 4 / 3`. -/
example {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) : Real.exp 0 + Real.exp (-β * Δ) = 4 / 3 := by
  rw [← partitionFunction_twoLevelEnergy, partitionFunction_twoLevelEnergy_eq hβΔ]

example {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    boltzmannProb (twoLevelEnergy Δ) β 1 = 1 / 4 ∧ boltzmannProb (twoLevelEnergy Δ) β 0 = 3 / 4 :=
  ⟨boltzmannProb_twoLevelEnergy_one hβΔ, boltzmannProb_twoLevelEnergy_zero hβΔ⟩

example {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    meanEnergy (twoLevelEnergy Δ) β = Δ / 4 ∧
      energyVariance (twoLevelEnergy Δ) β = 3 * Δ ^ 2 / 16 :=
  ⟨meanEnergy_twoLevelEnergy hβΔ, energyVariance_twoLevelEnergy hβΔ⟩

example (kB : ℝ) {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    heatCapacity kB (twoLevelEnergy Δ) β = kB * (3 * Real.log 3 ^ 2 / 16) :=
  heatCapacity_twoLevelEnergy kB hβΔ

/-- `C / kB = 3 * (log 3) ^ 2 / 16` for `0 < kB`. -/
example {kB β Δ : ℝ} (hkB : 0 < kB) (hβΔ : β * Δ = Real.log 3) :
    heatCapacity kB (twoLevelEnergy Δ) β / kB = 3 * Real.log 3 ^ 2 / 16 := by
  rw [heatCapacity_twoLevelEnergy kB hβΔ, mul_div_cancel_left₀ _ hkB.ne']

/-- The worked example under its hypotheses `0 < Δ` and `β * Δ = log 3`. -/
example (kB : ℝ) {β Δ : ℝ} (hΔ : 0 < Δ) (hβΔ : β * Δ = Real.log 3) :
    0 < β ∧ partitionFunction (twoLevelEnergy Δ) β = 4 / 3 :=
  ⟨(twoLevelEnergy_workedExample kB hΔ hβΔ).1, (twoLevelEnergy_workedExample kB hΔ hβΔ).2.2.1⟩

/-- A numeric instance: `Δ = 1` at `β = log 3`. -/
example : meanEnergy (twoLevelEnergy 1) (Real.log 3) = 1 / 4 :=
  meanEnergy_twoLevelEnergy (mul_one _)

/-- The two-level system with its states swapped: state `0` has energy `Δ` and state `1` has
energy `0`. -/
def swappedTwoLevelEnergy (Δ : ℝ) : Fin 2 → ℝ :=
  ![Δ, 0]

/-- The swapped energies are the two-level energies relabeled by the transposition of the two
states. -/
lemma swappedTwoLevelEnergy_eq (Δ : ℝ) :
    swappedTwoLevelEnergy Δ = fun i => twoLevelEnergy Δ (Equiv.swap 0 1 i) := by
  funext i
  fin_cases i <;> rfl

/-- Relabeling the states by a permutation leaves the partition function unchanged. -/
lemma partitionFunction_perm {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) (σ : Equiv.Perm ι) :
    partitionFunction (fun i => E (σ i)) β = partitionFunction E β :=
  Equiv.sum_comp σ fun i => Real.exp (-β * E i)

/-- Relabeling the states by a permutation relabels the Boltzmann probabilities. -/
lemma boltzmannProb_perm {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) (σ : Equiv.Perm ι)
    (i : ι) : boltzmannProb (fun i => E (σ i)) β i = boltzmannProb E β (σ i) := by
  rw [boltzmannProb, boltzmannProb, partitionFunction_perm]

/-- Relabeling the states by a permutation leaves the mean energy unchanged. -/
lemma meanEnergy_perm {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) (σ : Equiv.Perm ι) :
    meanEnergy (fun i => E (σ i)) β = meanEnergy E β := by
  simp only [meanEnergy, boltzmannProb_perm]
  exact Equiv.sum_comp σ fun i => boltzmannProb E β i * E i

/-- Relabeling the states by a permutation leaves the energy variance unchanged. -/
lemma energyVariance_perm {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) (σ : Equiv.Perm ι) :
    energyVariance (fun i => E (σ i)) β = energyVariance E β := by
  simp only [energyVariance, meanEnergy_perm, boltzmannProb_perm]
  exact Equiv.sum_comp σ fun i => boltzmannProb E β i * (E i - meanEnergy E β) ^ 2

/-- The swapped two-level partition function, computed directly. -/
example (Δ β : ℝ) :
    partitionFunction (swappedTwoLevelEnergy Δ) β = Real.exp (-β * Δ) + Real.exp 0 := by
  simp [partitionFunction, swappedTwoLevelEnergy, Fin.sum_univ_two]

/-- State relabeling: with the two states swapped and the energies relabeled accordingly, the
worked example has the same values, the excited state now being `0`. -/
example (kB : ℝ) {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    partitionFunction (swappedTwoLevelEnergy Δ) β = 4 / 3 ∧
      boltzmannProb (swappedTwoLevelEnergy Δ) β 0 = 1 / 4 ∧
      boltzmannProb (swappedTwoLevelEnergy Δ) β 1 = 3 / 4 ∧
      meanEnergy (swappedTwoLevelEnergy Δ) β = Δ / 4 ∧
      energyVariance (swappedTwoLevelEnergy Δ) β = 3 * Δ ^ 2 / 16 ∧
      heatCapacity kB (swappedTwoLevelEnergy Δ) β = kB * (3 * Real.log 3 ^ 2 / 16) := by
  rw [swappedTwoLevelEnergy_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [partitionFunction_perm, partitionFunction_twoLevelEnergy_eq hβΔ]
  · rw [boltzmannProb_perm, Equiv.swap_apply_left, boltzmannProb_twoLevelEnergy_one hβΔ]
  · rw [boltzmannProb_perm, Equiv.swap_apply_right, boltzmannProb_twoLevelEnergy_zero hβΔ]
  · rw [meanEnergy_perm, meanEnergy_twoLevelEnergy hβΔ]
  · rw [energyVariance_perm, energyVariance_twoLevelEnergy hβΔ]
  · rw [heatCapacity, energyVariance_perm, ← heatCapacity, heatCapacity_twoLevelEnergy kB hβΔ]

/-!

## F. Einstein-solid counting and Stirling's formula

-/

/-- Two oscillators sharing two quanta have `3` microstates. -/
example : Nat.card {f : Fin 2 → ℕ // ∑ i, f i = 2} = 3 :=
  (card_sum_eq_choose 2 2).trans (by decide)

/-- Three oscillators sharing two quanta have `6` microstates. -/
example : Nat.card {f : Fin 3 → ℕ // ∑ i, f i = 2} = 6 :=
  (card_sum_eq_choose 3 2).trans (by decide)

/-- The same counts by explicit enumeration, independently of `card_sum_eq_choose`. -/
example : (Finset.Nat.antidiagonalTuple 2 2).card = 3 ∧
    (Finset.Nat.antidiagonalTuple 3 2).card = 6 := by
  decide

/-- The three microstates of two oscillators sharing two quanta. -/
example : Finset.Nat.antidiagonalTuple 2 2 = {![0, 2], ![1, 1], ![2, 0]} := by
  decide

example (N q : ℕ) : (Finset.Nat.antidiagonalTuple N q).card = (N + q - 1).choose q :=
  card_antidiagonalTuple N q

/-- `5! = 120` is an exact count. -/
example : Nat.factorial 5 = 120 := by
  decide

/-- The Stirling value at `n = 2` is not `2!`. -/
example : (Nat.factorial 2 : ℝ) ≠
    (2 : ℝ) ^ ((2 : ℝ) + 1 / 2) * Real.exp (-2) * Real.sqrt (2 * Real.pi) :=
  factorial_two_ne_stirling

/-!

## G. The canonical postulate

-/

example (E : Fin 3 → ℝ) (β : ℝ) : IsCanonical (boltzmannProb E β) E β :=
  isCanonical_boltzmannProb E β

/-- A canonical distribution maximizes the entropy among distributions with its mean energy. -/
example (E : Fin 3 → ℝ) (β : ℝ) {p q : Fin 3 → ℝ} (hp : IsCanonical p E β)
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) (hU : ∑ i, q i * E i = ∑ i, p i * E i) :
    shannonEntropy q ≤ shannonEntropy p := by
  obtain rfl : p = boltzmannProb E β := hp
  exact shannonEntropy_le_shannonEntropy_boltzmannProb E β hq hq1 hU

/-- The uniform distribution is not canonical for the two-level system at `β * Δ = log 3`. -/
example {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) : ¬ IsCanonical uniformTwo (twoLevelEnergy Δ) β := by
  intro h
  have h1 := congrFun h 1
  rw [boltzmannProb_twoLevelEnergy_one hβΔ, uniformTwo] at h1
  norm_num at h1

/-!

## H. Bridge to Physlib's canonical-ensemble API

-/

/-- The counting-measure ensemble is finite in Physlib's sense. -/
example (E : Fin 3 → ℝ) : (canonicalEnsemble E).IsFinite :=
  inferInstance

example (E : Fin 3 → ℝ) (β : ℝ) :
    partitionFunction E β =
      (canonicalEnsemble E).mathematicalPartitionFunctionBetaReal β :=
  partitionFunction_eq_mathematicalPartitionFunctionBetaReal E β

example (E : Fin 3 → ℝ) (β : ℝ) (i : Fin 3) :
    boltzmannProb E β i = (canonicalEnsemble E).probabilityBetaReal β i :=
  boltzmannProb_eq_probabilityBetaReal E β i

example (E : Fin 3 → ℝ) (β : ℝ) :
    meanEnergy E β = (canonicalEnsemble E).meanEnergyBetaReal β :=
  meanEnergy_eq_meanEnergyBetaReal E β

end PhyslibExtTest.Chemistry.FiniteEnsembles

#print axioms Chemistry.FiniteEnsembles.partitionFunction
#print axioms Chemistry.FiniteEnsembles.partitionFunction_pos
#print axioms Chemistry.FiniteEnsembles.boltzmannProb
#print axioms Chemistry.FiniteEnsembles.boltzmannProb_pos
#print axioms Chemistry.FiniteEnsembles.boltzmannProb_nonneg
#print axioms Chemistry.FiniteEnsembles.sum_boltzmannProb_eq_one
#print axioms Chemistry.FiniteEnsembles.log_boltzmannProb
#print axioms Chemistry.FiniteEnsembles.shannonEntropy
#print axioms Chemistry.FiniteEnsembles.nonempty_of_sum_eq_one
#print axioms Chemistry.FiniteEnsembles.mul_log_div_le_sub
#print axioms Chemistry.FiniteEnsembles.mul_log_div_lt_sub
#print axioms Chemistry.FiniteEnsembles.sum_mul_log_div_eq_sum_sub
#print axioms Chemistry.FiniteEnsembles.sum_mul_log_div_nonneg
#print axioms Chemistry.FiniteEnsembles.sum_mul_log_div_eq_zero_iff
#print axioms Chemistry.FiniteEnsembles.sum_mul_log_div_boltzmannProb_nonneg
#print axioms Chemistry.FiniteEnsembles.sum_mul_log_div_boltzmannProb_eq_zero_iff
#print axioms Chemistry.FiniteEnsembles.sum_mul_log_boltzmannProb
#print axioms Chemistry.FiniteEnsembles.sum_mul_log_div_boltzmannProb_eq
#print axioms Chemistry.FiniteEnsembles.shannonEntropy_le_shannonEntropy_boltzmannProb
#print axioms Chemistry.FiniteEnsembles.shannonEntropy_eq_shannonEntropy_boltzmannProb_iff
#print axioms Chemistry.FiniteEnsembles.meanEnergy
#print axioms Chemistry.FiniteEnsembles.energyVariance
#print axioms Chemistry.FiniteEnsembles.temperature
#print axioms Chemistry.FiniteEnsembles.helmholtzFreeEnergy
#print axioms Chemistry.FiniteEnsembles.entropy
#print axioms Chemistry.FiniteEnsembles.heatCapacity
#print axioms Chemistry.FiniteEnsembles.energyVariance_nonneg
#print axioms Chemistry.FiniteEnsembles.heatCapacity_nonneg
#print axioms Chemistry.FiniteEnsembles.energyVariance_eq_sum_sub_meanEnergy_sq
#print axioms Chemistry.FiniteEnsembles.entropy_eq_mul_shannonEntropy
#print axioms Chemistry.FiniteEnsembles.helmholtzFreeEnergy_eq_meanEnergy_sub_entropy_div
#print axioms Chemistry.FiniteEnsembles.temperature_pos
#print axioms Chemistry.FiniteEnsembles.helmholtzFreeEnergy_eq_meanEnergy_sub_temperature_mul_entropy
#print axioms Chemistry.FiniteEnsembles.helmholtzFreeEnergy_eq_neg_mul_temperature_mul_log
#print axioms Chemistry.FiniteEnsembles.hasDerivAt_exp_neg_mul
#print axioms Chemistry.FiniteEnsembles.hasDerivAt_partitionFunction
#print axioms Chemistry.FiniteEnsembles.meanEnergy_eq_div
#print axioms Chemistry.FiniteEnsembles.hasDerivAt_log_partitionFunction
#print axioms Chemistry.FiniteEnsembles.deriv_log_partitionFunction
#print axioms Chemistry.FiniteEnsembles.hasDerivAt_meanEnergy
#print axioms Chemistry.FiniteEnsembles.deriv_meanEnergy
#print axioms Chemistry.FiniteEnsembles.heatCapacity_eq_neg_mul_deriv_meanEnergy
#print axioms Chemistry.FiniteEnsembles.heatCapacity_eq_energyVariance_div
#print axioms Chemistry.FiniteEnsembles.combinedEnergy
#print axioms Chemistry.FiniteEnsembles.partitionFunction_combinedEnergy
#print axioms Chemistry.FiniteEnsembles.boltzmannProb_combinedEnergy
#print axioms Chemistry.FiniteEnsembles.meanEnergy_combinedEnergy
#print axioms Chemistry.FiniteEnsembles.twoLevelEnergy
#print axioms Chemistry.FiniteEnsembles.twoLevelEnergy_zero
#print axioms Chemistry.FiniteEnsembles.twoLevelEnergy_one
#print axioms Chemistry.FiniteEnsembles.partitionFunction_twoLevelEnergy
#print axioms Chemistry.FiniteEnsembles.exp_neg_mul_eq_one_third
#print axioms Chemistry.FiniteEnsembles.partitionFunction_twoLevelEnergy_eq
#print axioms Chemistry.FiniteEnsembles.boltzmannProb_twoLevelEnergy_zero
#print axioms Chemistry.FiniteEnsembles.boltzmannProb_twoLevelEnergy_one
#print axioms Chemistry.FiniteEnsembles.meanEnergy_twoLevelEnergy
#print axioms Chemistry.FiniteEnsembles.energyVariance_twoLevelEnergy
#print axioms Chemistry.FiniteEnsembles.heatCapacity_twoLevelEnergy
#print axioms Chemistry.FiniteEnsembles.pos_of_mul_eq_log_three
#print axioms Chemistry.FiniteEnsembles.twoLevelEnergy_workedExample
#print axioms Chemistry.FiniteEnsembles.card_sum_eq_choose
#print axioms Chemistry.FiniteEnsembles.card_antidiagonalTuple
#print axioms Chemistry.FiniteEnsembles.stirling_two_lt_factorial
#print axioms Chemistry.FiniteEnsembles.factorial_two_ne_stirling
#print axioms Chemistry.FiniteEnsembles.IsCanonical
#print axioms Chemistry.FiniteEnsembles.isCanonical_boltzmannProb
#print axioms Chemistry.FiniteEnsembles.canonicalEnsemble
#print axioms Chemistry.FiniteEnsembles.partitionFunction_eq_mathematicalPartitionFunctionBetaReal
#print axioms Chemistry.FiniteEnsembles.boltzmannProb_eq_probabilityBetaReal
#print axioms Chemistry.FiniteEnsembles.meanEnergy_eq_meanEnergyBetaReal
#print axioms PhyslibExtTest.Chemistry.FiniteEnsembles.uniformTwo
#print axioms PhyslibExtTest.Chemistry.FiniteEnsembles.uniformTwo_nonneg
#print axioms PhyslibExtTest.Chemistry.FiniteEnsembles.sum_uniformTwo
#print axioms PhyslibExtTest.Chemistry.FiniteEnsembles.swappedTwoLevelEnergy
#print axioms PhyslibExtTest.Chemistry.FiniteEnsembles.swappedTwoLevelEnergy_eq
#print axioms PhyslibExtTest.Chemistry.FiniteEnsembles.partitionFunction_perm
#print axioms PhyslibExtTest.Chemistry.FiniteEnsembles.boltzmannProb_perm
#print axioms PhyslibExtTest.Chemistry.FiniteEnsembles.meanEnergy_perm
#print axioms PhyslibExtTest.Chemistry.FiniteEnsembles.energyVariance_perm
