/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Probability.BorelCantelli
import Mathlib.Data.Set.Card
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs
public import MathlibExt.GameTheory.PotentialGame

@[expose] public section

/-! # Asynchronous Hopfield networks

The state and single-neuron update follow J. J. Hopfield, “Neural networks and physical
systems with emergent collective computational abilities”, PNAS 79 (1982), 2554–2558,
Eq. [1], with ties retaining the current bit. The zero-threshold energy is Eq. [7].
The energy with a threshold term extends that formula. The random model uses discrete
independent attempts with a common law assigning positive mass to every neuron.

Every energy, descent and convergence theorem below assumes that the weight matrix is symmetric
(`Matrix.IsSymm T`, i.e. `T j i = T i j` for all neurons `i`, `j`), as Hopfield's convergence
argument requires. Diagonal entries never enter the dynamics or the energy.

Prior formalization: P. Cipollina, M. Karatarakis and F. Wiedijk, "Formalized Hopfield Networks
and Boltzmann Machines", arXiv:2512.07766 (LPAR-26), prove convergence under fair schedules for
the ±1 encoding with ties resolved to +1. `exists_stable_tail` extends that result to the 0/1
model with ties keeping the current bit. No code from that development is used.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENat

namespace Cslib.MachineLearning.Hopfield

open MathlibExt.GameTheory.PotentialGame

/-- The input to neuron `i` from the other neurons. A Boolean contributes its 0/1 value. -/
noncomputable def localField {N : ℕ} (T : Fin N → Fin N → ℝ)
    (v : Fin N → Bool) (i : Fin N) : ℝ :=
  ∑ j ∈ univ.erase i, T i j * (v j).toNat

/-- Make one update attempt at neuron `i`, retaining the whole state at a tie. -/
noncomputable def step {N : ℕ} (T : Fin N → Fin N → ℝ) (U : Fin N → ℝ)
    (i : Fin N) (v : Fin N → Bool) : Fin N → Bool :=
  if U i < localField T v i then Function.update v i true
  else if localField T v i < U i then Function.update v i false
  else v

/-- Hopfield's Eq. [7], used for zero-threshold dynamics. -/
noncomputable def energy {N : ℕ} (T : Fin N → Fin N → ℝ) (v : Fin N → Bool) : ℝ :=
  -(1 / 2 : ℝ) * ∑ i, ∑ j ∈ univ.erase i, T i j * (v i).toNat * (v j).toNat

/-- The energy extension for arbitrary thresholds. -/
noncomputable def energyWithThreshold {N : ℕ} (T : Fin N → Fin N → ℝ) (U : Fin N → ℝ)
    (v : Fin N → Bool) : ℝ :=
  energy T v + ∑ i, U i * (v i).toNat

/-- For any weights `T` and state `v`, the threshold energy with all thresholds zero is Hopfield's
Eq. [7] energy: `energyWithThreshold T 0 v = energy T v`. No hypothesis on `T` is needed. -/
@[simp] theorem energyWithThreshold_zero {N : ℕ} (T : Fin N → Fin N → ℝ) (v : Fin N → Bool) :
    energyWithThreshold T 0 v = energy T v := by
  simp [energyWithThreshold]

/-- The state at each attempt index, starting at `v₀` before attempt zero. -/
noncomputable def trajectory {N : ℕ} (T : Fin N → Fin N → ℝ) (U : Fin N → ℝ)
    (σ : ℕ → Fin N) (v₀ : Fin N → Bool) : ℕ → Fin N → Bool
  | 0 => v₀
  | k + 1 => step T U (σ k) (trajectory T U σ v₀ k)

/-- For any weights `T`, thresholds `U`, schedule `σ` and initial state `v₀`, the trajectory begins
at its supplied initial state: `trajectory T U σ v₀ 0 = v₀`. -/
@[simp] theorem trajectory_zero {N : ℕ} (T : Fin N → Fin N → ℝ) (U : Fin N → ℝ)
    (σ : ℕ → Fin N) (v₀ : Fin N → Bool) : trajectory T U σ v₀ 0 = v₀ :=
  rfl

/-- For any weights `T`, thresholds `U`, schedule `σ`, initial state `v₀` and index `k`, the
successor state results from the next scheduled attempt:
`trajectory T U σ v₀ (k + 1) = step T U (σ k) (trajectory T U σ v₀ k)`. -/
theorem trajectory_succ {N : ℕ} (T : Fin N → Fin N → ℝ) (U : Fin N → ℝ)
    (σ : ℕ → Fin N) (v₀ : Fin N → Bool) (k : ℕ) :
    trajectory T U σ v₀ (k + 1) = step T U (σ k) (trajectory T U σ v₀ k) :=
  rfl

/-- The indices of attempts that change the state. -/
def changeTimes {N : ℕ} (T : Fin N → Fin N → ℝ) (U : Fin N → ℝ)
    (σ : ℕ → Fin N) (v₀ : Fin N → Bool) : Set ℕ :=
  {k | trajectory T U σ v₀ (k + 1) ≠ trajectory T U σ v₀ k}

/-- Each neuron occurs arbitrarily late in the attempt sequence. -/
def Fair {N : ℕ} (σ : ℕ → Fin N) : Prop :=
  ∀ i K, ∃ k ≥ K, σ k = i

/-- A state fixed by every single-neuron update. -/
def Stable {N : ℕ} (T : Fin N → Fin N → ℝ) (U : Fin N → ℝ) (v : Fin N → Bool) : Prop :=
  ∀ i, step T U i v = v

/-- The cost of one neuron in the unilateral-deviation game. -/
noncomputable def cost {N : ℕ} (T : Fin N → Fin N → ℝ) (U : Fin N → ℝ)
    (i : Fin N) (v : Fin N → Bool) : ℝ :=
  -((v i).toNat : ℝ) * (localField T v i - U i)

private theorem localField_update {N : ℕ} (T : Fin N → Fin N → ℝ)
    (v : Fin N → Bool) (i : Fin N) (a : Bool) :
    localField T (Function.update v i a) i = localField T v i := by
  apply sum_congr rfl
  intro j hj
  simp only [mem_erase, mem_univ, and_true] at hj
  simp [Function.update_of_ne hj]

private theorem cost_update {N : ℕ} (T : Fin N → Fin N → ℝ) (U : Fin N → ℝ)
    (v : Fin N → Bool) (i : Fin N) (a : Bool) :
    cost T U i (Function.update v i a) =
      -(a.toNat : ℝ) * (localField T v i - U i) := by
  simp [cost, localField_update]

/-- **Hopfield's Eq. [8]** for a unilateral change. Let `T` be a symmetric weight matrix
(`Matrix.IsSymm T`). Then for every state `v`, neuron `i` and bit `a`, setting neuron `i` to `a`
changes the zero-threshold energy by
`energy T (update v i a) - energy T v = -(a - vᵢ) · localField T v i`, with bits read as 0/1. -/
theorem energy_update {N : ℕ} {T : Fin N → Fin N → ℝ}
    (hT : Matrix.IsSymm T) (v : Fin N → Bool) (i : Fin N) (a : Bool) :
    energy T (Function.update v i a) - energy T v =
      -((a.toNat : ℝ) - (v i).toNat) * localField T v i := by
  classical
  let f (w : Fin N → Bool) (j : Fin N) :=
    ∑ k ∈ univ.erase j, T j k * (w j).toNat * (w k).toNat
  let d : ℝ := (a.toNat : ℝ) - (v i).toNat
  have hi : f (Function.update v i a) i - f v i = d * localField T v i := by
    simp only [f, localField, ← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro j hj
    have hji : j ≠ i := (mem_erase.mp hj).1
    simp only [Function.update_self, Function.update_of_ne hji]
    dsimp [d]
    ring
  have hj (j : Fin N) (hji : j ≠ i) :
      f (Function.update v i a) j - f v j = d * (T i j * (v j).toNat) := by
    simp only [f, ← sum_sub_distrib, Function.update_of_ne hji]
    rw [sum_eq_single i]
    · simp only [Function.update_self]
      rw [hT.apply i j]
      dsimp [d]
      ring
    · intro k hk hki
      simp [Function.update_of_ne hki]
    · intro hnot
      exact False.elim (hnot (mem_erase.mpr ⟨Ne.symm hji, mem_univ i⟩))
  have hs : (∑ j, f (Function.update v i a) j) - ∑ j, f v j =
      2 * d * localField T v i := by
    rw [← sum_sub_distrib,
      ← sum_erase_add univ (fun j => f (Function.update v i a) j - f v j) (mem_univ i), hi]
    have he : (∑ j ∈ univ.erase i, (f (Function.update v i a) j - f v j)) =
        d * localField T v i := by
      simp only [localField, mul_sum]
      exact sum_congr rfl fun j hj' => hj j (mem_erase.mp hj').1
    rw [he]
    ring
  change -(1 / 2 : ℝ) * (∑ j, f (Function.update v i a) j) -
    -(1 / 2 : ℝ) * (∑ j, f v j) = -d * localField T v i
  linarith

/-- **The one-coordinate energy identity with thresholds.** Let `T` be a symmetric weight matrix
(`Matrix.IsSymm T`) and `U` any thresholds. Then for every state `v`, neuron `i` and bit `a`, the
difference `energyWithThreshold T U (update v i a) - energyWithThreshold T U v` equals
`-(a - vᵢ) · (localField T v i - Uᵢ)`, with bits read as 0/1. -/
theorem energyWithThreshold_update {N : ℕ} {T : Fin N → Fin N → ℝ} {U : Fin N → ℝ}
    (hT : Matrix.IsSymm T)
    (v : Fin N → Bool) (i : Fin N) (a : Bool) :
    energyWithThreshold T U (Function.update v i a) - energyWithThreshold T U v =
      -((a.toNat : ℝ) - (v i).toNat) * (localField T v i - U i) := by
  classical
  have hs : (∑ j, U j * ((Function.update v i a) j).toNat) -
      ∑ j, U j * (v j).toNat = U i * ((a.toNat : ℝ) - (v i).toNat) := by
    rw [← sum_sub_distrib, sum_eq_single i]
    · simp only [Function.update_self]
      ring
    · intro j hj hji
      simp [Function.update_of_ne hji]
    · simp
  have he := energy_update hT v i a
  unfold energyWithThreshold
  linarith

/-- **The threshold energy is an exact potential.** Let `T` be a symmetric weight matrix
(`Matrix.IsSymm T`) and `U` any thresholds. Then `energyWithThreshold T U` is an exact potential for
the neuron costs `cost T U`: every unilateral deviation changes the deviating neuron's cost and the
energy by the same amount. -/
theorem isExactPotential_energyWithThreshold {N : ℕ} {T : Fin N → Fin N → ℝ} {U : Fin N → ℝ}
    (hT : Matrix.IsSymm T) :
    IsExactPotential (S := fun _ : Fin N => Bool) (cost T U) (energyWithThreshold T U) := by
  intro v i a
  rw [energyWithThreshold_update hT, cost_update]
  unfold cost
  ring

/-- For any weights `T` (no symmetry is needed), thresholds `U`, neuron `i` and state `v`: if the
update of neuron `i` changes the state (`step T U i v ≠ v`), then it is an improving move that
strictly lowers neuron `i`'s cost `cost T U i`. -/
theorem improvingMove_of_step_ne {N : ℕ} {T : Fin N → Fin N → ℝ} {U : Fin N → ℝ}
    {i : Fin N} {v : Fin N → Bool} (h : step T U i v ≠ v) :
    ImprovingMove (S := fun _ : Fin N => Bool) (cost T U) (step T U i v) v := by
  classical
  unfold step at h ⊢
  split_ifs at h ⊢ with hlt hgt
  · refine ⟨i, true, rfl, ?_⟩
    have hv : v i = false := by
      cases hv : v i
      · rfl
      · exact False.elim (h (by simp [hv]))
    rw [cost_update]
    simp [cost, hv]
    linarith
  · refine ⟨i, false, rfl, ?_⟩
    have hv : v i = true := by
      cases hv : v i
      · exact False.elim (h (by simp [hv]))
      · rfl
    rw [cost_update]
    simp [cost, hv]
    linarith
  · exact False.elim (h rfl)

/-- For any weights `T` (no symmetry is needed), thresholds `U` and state `v`: `v` is stable under
every single-neuron update if and only if it is a pure Nash equilibrium of the unilateral-deviation
game with costs `cost T U`. -/
theorem stable_iff_isPureNash {N : ℕ} {T : Fin N → Fin N → ℝ} {U : Fin N → ℝ}
    (v : Fin N → Bool) :
    Stable T U v ↔ IsPureNash (S := fun _ : Fin N => Bool) (cost T U) v := by
  classical
  constructor
  · intro hs i a
    have hi := hs i
    unfold step at hi
    rw [cost_update]
    unfold cost
    split_ifs at hi with hlt hgt
    · have hv : v i = true := by simpa using (congrFun hi i).symm
      cases a <;> simp [hv]
      linarith
    · have hv : v i = false := by simpa using (congrFun hi i).symm
      cases a <;> simp [hv]
      linarith
    · have he : localField T v i = U i := le_antisymm (le_of_not_gt hlt) (le_of_not_gt hgt)
      simp [he]
  · intro hn i
    by_contra h
    obtain ⟨j, a, hj, hlt⟩ := improvingMove_of_step_ne h
    have := hn j a
    rw [← hj] at this
    exact (not_lt_of_ge this) hlt

/-- **Energy descent with thresholds.** Let `T` be a symmetric weight matrix (`Matrix.IsSymm T`) and
`U` any thresholds. Then for every neuron `i` and state `v`, if the update of neuron `i` changes the
state (`step T U i v ≠ v`), it strictly decreases the threshold energy:
`energyWithThreshold T U (step T U i v) < energyWithThreshold T U v`. -/
theorem energyWithThreshold_step_lt {N : ℕ} {T : Fin N → Fin N → ℝ} {U : Fin N → ℝ}
    (hT : Matrix.IsSymm T) {i : Fin N}
    {v : Fin N → Bool} (h : step T U i v ≠ v) :
    energyWithThreshold T U (step T U i v) < energyWithThreshold T U v := by
  exact (isExactPotential_energyWithThreshold hT).lt_of_improvingMove
    (improvingMove_of_step_ne h)

/-- **Energy descent at zero threshold** (Hopfield 1982, Eq. [7]–[8]). Let `T` be a symmetric weight
matrix (`Matrix.IsSymm T`). Then for every neuron `i` and state `v`, if the zero-threshold update of
neuron `i` changes the state (`step T 0 i v ≠ v`), it strictly decreases the energy:
`energy T (step T 0 i v) < energy T v`. -/
theorem energy_step_lt {N : ℕ} {T : Fin N → Fin N → ℝ}
    (hT : Matrix.IsSymm T) {i : Fin N} {v : Fin N → Bool}
    (h : step T 0 i v ≠ v) : energy T (step T 0 i v) < energy T v := by
  simpa using energyWithThreshold_step_lt hT h

private theorem trajectory_energy_antitone {N : ℕ} {T : Fin N → Fin N → ℝ}
    {U : Fin N → ℝ} (hT : Matrix.IsSymm T) (σ : ℕ → Fin N)
    (v₀ : Fin N → Bool) :
    Antitone (fun k => energyWithThreshold T U (trajectory T U σ v₀ k)) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [trajectory_succ]
  by_cases h : step T U (σ k) (trajectory T U σ v₀ k) = trajectory T U σ v₀ k
  · rw [h]
  · exact (energyWithThreshold_step_lt hT h).le

private theorem trajectory_energy_lt_of_change {N : ℕ} {T : Fin N → Fin N → ℝ}
    {U : Fin N → ℝ} (hT : Matrix.IsSymm T) (σ : ℕ → Fin N)
    (v₀ : Fin N → Bool) {k n : ℕ} (hk : k ∈ changeTimes T U σ v₀) (hn : n ≤ k) :
    energyWithThreshold T U (trajectory T U σ v₀ (k + 1)) <
      energyWithThreshold T U (trajectory T U σ v₀ n) := by
  have hlt : energyWithThreshold T U (trajectory T U σ v₀ (k + 1)) <
      energyWithThreshold T U (trajectory T U σ v₀ k) :=
    energyWithThreshold_step_lt hT hk
  exact hlt.trans_le (trajectory_energy_antitone hT σ v₀ hn)

/-- **At most `2 ^ N - 1` changes.** Let `T` be a symmetric weight matrix (`Matrix.IsSymm T`) and
`U` any thresholds. Then for every schedule `σ` and initial state `v₀`, the set of attempt indices
at which the state changes has at most `2 ^ N - 1` elements:
`(changeTimes T U σ v₀).encard ≤ 2 ^ N - 1`. -/
theorem encard_changeTimes_le {N : ℕ} {T : Fin N → Fin N → ℝ} {U : Fin N → ℝ}
    (hT : Matrix.IsSymm T) (σ : ℕ → Fin N) (v₀ : Fin N → Bool) :
    (changeTimes T U σ v₀).encard ≤ ((2 ^ N - 1 : ℕ) : ℕ∞) := by
  classical
  let f : ℕ → (Fin N → Bool) := fun k => trajectory T U σ v₀ (k + 1)
  have hf : Set.InjOn f (changeTimes T U σ v₀) := by
    intro k hk l hl he
    rcases lt_trichotomy k l with hkl | hkl | hlk
    · have hlt := trajectory_energy_lt_of_change hT σ v₀ hl (Nat.succ_le_of_lt hkl)
      change energyWithThreshold T U (f l) < energyWithThreshold T U (f k) at hlt
      rw [he] at hlt
      exact False.elim (lt_irrefl _ hlt)
    · exact hkl
    · have hlt := trajectory_energy_lt_of_change hT σ v₀ hk (Nat.succ_le_of_lt hlk)
      change energyWithThreshold T U (f k) < energyWithThreshold T U (f l) at hlt
      rw [he] at hlt
      exact False.elim (lt_irrefl _ hlt)
  have hs : f '' changeTimes T U σ v₀ ⊆
      (↑(univ.erase v₀) : Set (Fin N → Bool)) := by
    rintro w ⟨k, hk, rfl⟩
    have hlt := trajectory_energy_lt_of_change hT σ v₀ hk (Nat.zero_le k)
    have hne : f k ≠ v₀ := by
      intro he
      change energyWithThreshold T U (f k) < energyWithThreshold T U v₀ at hlt
      rw [he] at hlt
      exact lt_irrefl _ hlt
    simpa using hne
  calc
    (changeTimes T U σ v₀).encard = (f '' changeTimes T U σ v₀).encard := hf.encard_image.symm
    _ ≤ (↑(univ.erase v₀) : Set (Fin N → Bool)).encard := Set.encard_mono hs
    _ = ((2 ^ N - 1 : ℕ) : ℕ∞) := by
      rw [Set.encard_coe_eq_coe_finsetCard, card_erase_of_mem (mem_univ v₀), card_univ]
      simp

/-- **Eventually constant trajectories.** Let `T` be a symmetric weight matrix (`Matrix.IsSymm T`)
and `U` any thresholds. Then for every schedule `σ` and initial state `v₀` there is `K` such that
`trajectory T U σ v₀ k = trajectory T U σ v₀ K` for every `k ≥ K`. -/
theorem exists_constant_tail {N : ℕ} {T : Fin N → Fin N → ℝ} {U : Fin N → ℝ}
    (hT : Matrix.IsSymm T) (σ : ℕ → Fin N) (v₀ : Fin N → Bool) :
    ∃ K, ∀ k ≥ K, trajectory T U σ v₀ k = trajectory T U σ v₀ K := by
  have hf := Set.finite_of_encard_le_coe (encard_changeTimes_le (U := U) hT σ v₀)
  obtain ⟨B, hB⟩ := hf.bddAbove
  refine ⟨B + 1, ?_⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    have hnot : k ∉ changeTimes T U σ v₀ := by
      intro hmem
      have := hB hmem
      omega
    have he : trajectory T U σ v₀ (k + 1) = trajectory T U σ v₀ k :=
      not_not.mp hnot
    exact he.trans ih

/-- **Convergence under a fair schedule.** Let `T` be a symmetric weight matrix (`Matrix.IsSymm T`)
and `U` any thresholds, and let `σ` be a fair schedule (every neuron is attempted arbitrarily late,
`Fair σ`). Then for every initial state `v₀` there is `K` such that `trajectory T U σ v₀ K` is
stable and `trajectory T U σ v₀ k = trajectory T U σ v₀ K` for every `k ≥ K`. -/
theorem exists_stable_tail {N : ℕ} {T : Fin N → Fin N → ℝ} {U : Fin N → ℝ}
    (hT : Matrix.IsSymm T) {σ : ℕ → Fin N}
    (hσ : Fair σ) (v₀ : Fin N → Bool) :
    ∃ K, Stable T U (trajectory T U σ v₀ K) ∧
      ∀ k ≥ K, trajectory T U σ v₀ k = trajectory T U σ v₀ K := by
  obtain ⟨K, hK⟩ := exists_constant_tail hT σ v₀
  refine ⟨K, ?_, hK⟩
  intro i
  obtain ⟨k, hk, hi⟩ := hσ i K
  have hs := trajectory_succ T U σ v₀ k
  rw [hK k hk, hK (k + 1) (by omega), hi] at hs
  exact hs.symm

/-- **Convergence under a fair schedule at zero threshold** (Hopfield 1982). Let `T` be a symmetric
weight matrix (`Matrix.IsSymm T`), and let `σ` be a fair schedule (`Fair σ`). Then for every initial
state `v₀` there is `K` such that `trajectory T 0 σ v₀ K` is stable for the zero-threshold dynamics
and `trajectory T 0 σ v₀ k = trajectory T 0 σ v₀ K` for every `k ≥ K`. -/
theorem exists_stable_tail_zero {N : ℕ} {T : Fin N → Fin N → ℝ}
    (hT : Matrix.IsSymm T) {σ : ℕ → Fin N}
    (hσ : Fair σ) (v₀ : Fin N → Bool) :
    ∃ K, Stable T 0 (trajectory T 0 σ v₀ K) ∧
      ∀ k ≥ K, trajectory T 0 σ v₀ k = trajectory T 0 σ v₀ K := by
  exact exists_stable_tail hT hσ v₀

/-- **Stable states are single-flip local minima.** Let `T` be a symmetric weight matrix
(`Matrix.IsSymm T`) and `U` any thresholds. Then a state `v` is stable if and only if, for every
neuron `i`, flipping bit `i` does not decrease the threshold energy:
`energyWithThreshold T U v ≤ energyWithThreshold T U (update v i (!vᵢ))`. -/
theorem stable_iff_energyWithThreshold_le_flip {N : ℕ} {T : Fin N → Fin N → ℝ} {U : Fin N → ℝ}
    (hT : Matrix.IsSymm T) (v : Fin N → Bool) :
    Stable T U v ↔
      ∀ i, energyWithThreshold T U v ≤ energyWithThreshold T U (Function.update v i (!v i)) := by
  classical
  rw [stable_iff_isPureNash]
  have hp := isExactPotential_energyWithThreshold (U := U) hT
  constructor
  · intro hn i
    have hc := hn i (!v i)
    have he := hp v i (!v i)
    linarith
  · intro he i a
    by_cases ha : a = v i
    · simp [ha, Function.update_eq_self]
    · have ha' : a = !v i := by cases a <;> cases hv : v i <;> simp_all
      rw [ha']
      have hi := he i
      have hc := hp v i a
      rw [ha'] at hc
      linarith

/-- **Stable states are single-flip local minima at zero threshold** (Eq. [7]). Let `T` be a
symmetric weight matrix (`Matrix.IsSymm T`). Then a state `v` is stable for the zero-threshold
dynamics if and only if, for every neuron `i`, flipping bit `i` does not decrease the energy:
`energy T v ≤ energy T (update v i (!vᵢ))`. -/
theorem stable_iff_energy_le_flip {N : ℕ} {T : Fin N → Fin N → ℝ}
    (hT : Matrix.IsSymm T) (v : Fin N → Bool) :
    Stable T 0 v ↔ ∀ i, energy T v ≤ energy T (Function.update v i (!v i)) := by
  simpa using stable_iff_energyWithThreshold_le_flip (U := 0) hT v

section Random

/-- Independent measurable attempts with a common full-support law on `Fin N`. -/
structure IIDFullSupport {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (σ : ℕ → Ω → Fin N) : Prop where
  /-- Each attempt is a measurable random variable. -/
  measurable : ∀ k, Measurable (σ k)
  /-- The entire sequence of attempt variables is independent. -/
  indep : iIndepFun σ μ
  /-- Every attempt has the same law as attempt zero. -/
  identDistrib : ∀ k, IdentDistrib (σ k) (σ 0) μ μ
  /-- The common law gives positive probability to each neuron. -/
  pos : ∀ i, 0 < μ {ω | σ 0 ω = i}

/-- **Random schedules are almost surely fair.** Let `μ` be a probability measure and let the
attempts `σ k` be measurable, independent and identically distributed, with a common law that gives
positive probability to every neuron (`IIDFullSupport μ σ`). Then `μ`-almost every realized schedule
`k ↦ σ k ω` is fair (`Fair`). No weights are involved. -/
theorem ae_fair {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {σ : ℕ → Ω → Fin N} [IsProbabilityMeasure μ] (hσ : IIDFullSupport μ σ) :
    ∀ᵐ ω ∂μ, Fair (fun k => σ k ω) := by
  classical
  have hi (i : Fin N) : ∀ᵐ ω ∂μ, ∀ K, ∃ k ≥ K, σ k ω = i := by
    let s : ℕ → Set Ω := fun k => {ω | σ k ω = i}
    have hm (k : ℕ) : MeasurableSet (s k) :=
      (hσ.measurable k) (measurableSet_singleton i)
    have hind : iIndepSet s μ := by
      apply (iIndepSet_iff_meas_biInter hm).2
      intro S
      exact hσ.indep.measure_inter_preimage_eq_mul S
        (sets := fun _ => {i}) (fun _ _ => measurableSet_singleton i)
    have hd (k : ℕ) : μ (s k) = μ (s 0) :=
      (hσ.identDistrib k).measure_mem_eq (measurableSet_singleton i)
    have ht : (∑' k, μ (s k)) = ⊤ := by
      simp_rw [hd]
      exact ENNReal.tsum_const_eq_top_of_ne_zero (ne_of_gt (hσ.pos i))
    have hml : MeasurableSet (Filter.limsup s Filter.atTop) := by
      rw [Filter.limsup_eq_iInf_iSup_of_nat]
      exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun k =>
        MeasurableSet.iUnion fun _ => hm k
    have hl : ∀ᵐ ω ∂μ, ω ∈ Filter.limsup s Filter.atTop :=
      (mem_ae_iff_prob_eq_one hml).2
        (measure_limsup_eq_one hm hind ht)
    filter_upwards [hl] with ω hω
    simpa only [Filter.mem_limsup_iff_frequently_mem, Filter.frequently_atTop,
      s, Set.mem_ofPred_eq] using hω
  exact ae_all_iff.2 hi

/-- **Almost-sure convergence under random schedules.** Let `T` be a symmetric weight matrix
(`Matrix.IsSymm T`) and `U` any thresholds, let `μ` be a probability measure, and let the attempts
`σ k` be measurable, independent and identically distributed with a common full-support law
(`IIDFullSupport μ σ`). Then for every initial state `v₀`, for `μ`-almost every `ω` there is `K`
such that the trajectory under the schedule `k ↦ σ k ω` is stable at `K` and constant from `K` on.
-/
theorem ae_exists_stable_tail {N : ℕ} {T : Fin N → Fin N → ℝ} {U : Fin N → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {σ : ℕ → Ω → Fin N}
    [IsProbabilityMeasure μ] (hT : Matrix.IsSymm T)
    (hσ : IIDFullSupport μ σ) (v₀ : Fin N → Bool) :
    ∀ᵐ ω ∂μ, ∃ K, Stable T U (trajectory T U (fun k => σ k ω) v₀ K) ∧
      ∀ k ≥ K, trajectory T U (fun n => σ n ω) v₀ k =
        trajectory T U (fun n => σ n ω) v₀ K := by
  filter_upwards [ae_fair hσ] with ω hω
  exact exists_stable_tail hT hω v₀

/-- **Almost-sure convergence under random schedules at zero threshold.** Let `T` be a symmetric
weight matrix (`Matrix.IsSymm T`), let `μ` be a probability measure, and let the attempts `σ k` be
measurable, independent and identically distributed with a common full-support law
(`IIDFullSupport μ σ`). Then for every initial state `v₀`, for `μ`-almost every `ω` there is `K`
such that the zero-threshold trajectory under the schedule `k ↦ σ k ω` is stable at `K` and constant
from `K` on. -/
theorem ae_exists_stable_tail_zero {N : ℕ} {T : Fin N → Fin N → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {σ : ℕ → Ω → Fin N}
    [IsProbabilityMeasure μ] (hT : Matrix.IsSymm T)
    (hσ : IIDFullSupport μ σ) (v₀ : Fin N → Bool) :
    ∀ᵐ ω ∂μ, ∃ K, Stable T 0 (trajectory T 0 (fun k => σ k ω) v₀ K) ∧
      ∀ k ≥ K, trajectory T 0 (fun n => σ n ω) v₀ k =
        trajectory T 0 (fun n => σ n ω) v₀ K := by
  exact ae_exists_stable_tail hT hσ v₀

end Random

end Cslib.MachineLearning.Hopfield
