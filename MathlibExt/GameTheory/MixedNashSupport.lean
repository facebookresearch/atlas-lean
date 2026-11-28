/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.MixedNashExistence

/-! # Best-response (support) condition for mixed Nash equilibria

In a finite game with payoffs `u`, `pureExpectedPayoff u σ i a` is the expected payoff
`U_i(a, σ_{-i})` of player `i` when `i` plays the pure action `a`, as the point mass
`StdSimplex.single a`, and every other player `j` mixes according to `σ j`. It does not depend
on `σ i`.

The expected payoff `expectedPayoff u σ i` is affine in each player's mixed strategy; for the
own strategy of player `i` this reads `U_i(τ, σ_{-i}) = ∑ₐ τ(a) U_i(a, σ_{-i})`. Hence a mixed
strategy of player `i` is a best response to `σ_{-i}` exactly when every pure action in its
support is a pure best response, and `σ` is a mixed Nash equilibrium exactly when no player
gains by a unilateral deviation to a pure action, or equivalently when, for every player `i`,
every pure action in the support of `σ i` is a pure best response to `σ_{-i}`.

## Main definitions and results

* `pureExpectedPayoff`: the payoff `U_i(a, σ_{-i})` of a pure action against a mixed profile.
* `expectedPayoff_update_eq_sum_update_single`: `U_i` is affine in each player's mixed strategy.
* `expectedPayoff_update_eq_sum`: `U_i(τ, σ_{-i}) = ∑ₐ τ(a) U_i(a, σ_{-i})`.
* `forall_expectedPayoff_update_le_iff`: the support characterization of mixed best responses.
* `isMixedNash_iff_forall_pureExpectedPayoff_le`: pure deviations suffice.
* `isMixedNash_iff_support`: the best-response (support) condition.
* `IsMixedNash.pureExpectedPayoff_eq`: in a mixed Nash equilibrium, every pure action in the
  support of `σ i` earns exactly the equilibrium payoff of `i`.

## References

* R. Savani and B. von Stengel, *Hard-to-Solve Bimatrix Games*, Econometrica 74 (2006),
  397–429, Section 2, Lemma 1, attributed there to Nash (1951) and stated for one player of a
  bimatrix game; the `n`-player form follows by the same argument, since the expected payoff
  of player `i` is linear in the mixed strategy of `i`.
* J. Nash, *Non-cooperative games*, Ann. of Math. 54 (1951), 286–295.
-/

@[expose] public section

namespace MathlibExt.GameTheory.MixedNashExistence

open Convexity

/-- **Payoff of a pure action against a mixed profile.** `U_i(a, σ_{-i})`: the expected payoff
of player `i` when it plays the pure action `a` (the point mass `StdSimplex.single a`) and every
other player `j` mixes according to `σ j`. The value does not depend on `σ i`
(`pureExpectedPayoff_update`). -/
noncomputable def pureExpectedPayoff {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] (u : ι → (∀ i, A i) → ℝ) (σ : ∀ i, StdSimplex ℝ (A i)) (i : ι)
    (a : A i) : ℝ :=
  expectedPayoff u (Function.update σ i (StdSimplex.single a)) i

/-- Helper: expected payoff of `i` from the other players' mix, given `j` plays `b`. -/
private noncomputable def restPayoff {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] (u : ι → (∀ i, A i) → ℝ) (ρ : ∀ i, StdSimplex ℝ (A i))
    (i j : ι) [DecidableEq (A j)] (b : A j) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s => s j = b),
    (∏ k ∈ Finset.univ.erase j, (ρ k).weights (s k)) * u i s

/-- Helper: group the expected payoff by the action of one player. -/
private theorem expectedPayoff_eq_sum_restPayoff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (u : ι → (∀ i, A i) → ℝ)
    (ρ : ∀ i, StdSimplex ℝ (A i)) (i j : ι) [DecidableEq (A j)] :
    expectedPayoff u ρ i = ∑ b, (ρ j).weights b * restPayoff u ρ i j b := by
  have hfib : expectedPayoff u ρ i = ∑ b, ∑ s ∈ Finset.univ.filter (fun s => s j = b),
      (∏ k, (ρ k).weights (s k)) * u i s :=
    (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := fun s : (∀ k, A k) => s j) (fun x _ => Finset.mem_univ _) _).symm
  rw [hfib]
  unfold restPayoff
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
  rw [← hs, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  ring

/-- Helper: `restPayoff` ignores the mixed strategy of player `j`. -/
private theorem restPayoff_update {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] (u : ι → (∀ i, A i) → ℝ) (ρ : ∀ i, StdSimplex ℝ (A i))
    (i j : ι) [DecidableEq (A j)] (τ : StdSimplex ℝ (A j)) (b : A j) :
    restPayoff u (Function.update ρ j τ) i j b = restPayoff u ρ i j b := by
  unfold restPayoff
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

/-- Helper: a point-mass average collapses to the value at that point. -/
private theorem single_sum_mul {X : Type*} [Fintype X] (b : X) (F : X → ℝ) :
    ∑ b', (StdSimplex.single b).weights b' * F b' = F b := by
  classical
  have h₀ : ∀ b' ∈ (Finset.univ : Finset X), b' ≠ b →
      (StdSimplex.single b).weights b' * F b' = 0 := by
    intro b' _ hb'
    have hw : (StdSimplex.single b).weights b' = (0 : ℝ) := by
      simp [StdSimplex.weights_single, Ne.symm hb']
    rw [hw, zero_mul]
  rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ b) h₀]
  have hw : (StdSimplex.single b).weights b = (1 : ℝ) := by simp [StdSimplex.weights_single]
  rw [hw, one_mul]

/-- Helper: the expected payoff against a point mass is `restPayoff`. -/
private theorem expectedPayoff_update_single_eq_restPayoff {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)] (u : ι → (∀ i, A i) → ℝ)
    (ρ : ∀ i, StdSimplex ℝ (A i)) (i j : ι) [DecidableEq (A j)] (b : A j) :
    expectedPayoff u (Function.update ρ j (StdSimplex.single b)) i =
      restPayoff u ρ i j b := by
  have hsum := expectedPayoff_eq_sum_restPayoff u (Function.update ρ j (StdSimplex.single b)) i j
  rw [Function.update_self] at hsum
  simp only [restPayoff_update] at hsum
  rw [single_sum_mul] at hsum
  exact hsum

/-- Helper: a simplex-weighted average is bounded by a uniform upper bound. -/
private theorem weighted_avg_le {X : Type*} [Fintype X] (τ : StdSimplex ℝ X)
    (U : X → ℝ) (m : ℝ) (h : ∀ b, U b ≤ m) :
    ∑ a, τ.weights a * U a ≤ m := by
  calc ∑ a, τ.weights a * U a ≤ ∑ a, τ.weights a * m :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (StdSimplex.weights_nonneg a)
    _ = m := by rw [← Finset.sum_mul, StdSimplex.total_of_fintype, one_mul]

/-- Helper: the average reaches the upper bound iff every supported value does. -/
private theorem le_weighted_avg_iff {X : Type*} [Fintype X] (τ : StdSimplex ℝ X)
    (U : X → ℝ) (m : ℝ) (h : ∀ b, U b ≤ m) :
    m ≤ ∑ a, τ.weights a * U a ↔ ∀ a, τ.weights a ≠ 0 → U a = m := by
  have hnn : ∀ a ∈ (Finset.univ : Finset X),
      0 ≤ τ.weights a * m - τ.weights a * U a := by
    intro a _
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left (h a) (StdSimplex.weights_nonneg a))
  constructor
  · intro hle a ha
    have havg : ∑ a, τ.weights a * U a = m :=
      le_antisymm (weighted_avg_le τ U m h) hle
    have hS0 : ∑ a, (τ.weights a * m - τ.weights a * U a) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, StdSimplex.total_of_fintype, one_mul, havg,
        sub_self]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hS0 a (Finset.mem_univ a)
    have hfac : τ.weights a * (m - U a) = 0 := by linear_combination hterm
    rcases mul_eq_zero.mp hfac with h0 | h0
    · exact absurd h0 ha
    · exact (sub_eq_zero.mp h0).symm
  · intro hall
    have hterm : ∀ a ∈ (Finset.univ : Finset X), τ.weights a * U a = τ.weights a * m := by
      intro a _
      by_cases ha : τ.weights a = 0
      · simp [ha]
      · rw [hall a ha]
    have hsum : ∑ a, τ.weights a * U a = m := by
      calc ∑ a, τ.weights a * U a = ∑ a, τ.weights a * m := Finset.sum_congr rfl hterm
        _ = m := by rw [← Finset.sum_mul, StdSimplex.total_of_fintype, one_mul]
    exact hsum.ge

/-- Helper: best responses are exactly the strategies supported on maximizers. -/
private theorem best_response_iff_support_max {X : Type*} [Fintype X] (τ : StdSimplex ℝ X)
    (U : X → ℝ) :
    (∀ τ' : StdSimplex ℝ X, ∑ a, τ'.weights a * U a ≤ ∑ a, τ.weights a * U a) ↔
      ∀ a, τ.weights a ≠ 0 → ∀ b, U b ≤ U a := by
  have : Nonempty X := StdSimplex.nonempty τ
  obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ U Finset.univ_nonempty
  have hub : ∀ b, U b ≤ U c := fun b => hc b (Finset.mem_univ b)
  constructor
  · intro h a ha b
    have hbest := h (StdSimplex.single c)
    rw [single_sum_mul] at hbest
    have heq := (le_weighted_avg_iff τ U (U c) hub).mp hbest a ha
    rw [heq]
    exact hub b
  · intro h τ'
    have hle_c : U c ≤ ∑ a, τ.weights a * U a :=
      (le_weighted_avg_iff τ U (U c) hub).mpr (fun a ha => le_antisymm (hub a) (h a ha c))
    calc ∑ a, τ'.weights a * U a ≤ U c := weighted_avg_le τ' U (U c) hub
      _ ≤ ∑ a, τ.weights a * U a := hle_c

/-- **The expected payoff is affine in each player's mixed strategy.** Replacing the mixed
strategy of any player `j` by `τ` turns the expected payoff of player `i` into the
`τ`-weighted average of its values when `j` plays each pure action `b`. -/
theorem expectedPayoff_update_eq_sum_update_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (u : ι → (∀ i, A i) → ℝ)
    (σ : ∀ i, StdSimplex ℝ (A i)) (i j : ι) (τ : StdSimplex ℝ (A j)) :
    expectedPayoff u (Function.update σ j τ) i =
      ∑ b, τ.weights b * expectedPayoff u (Function.update σ j (StdSimplex.single b)) i := by
  classical
  have hsum := expectedPayoff_eq_sum_restPayoff u (Function.update σ j τ) i j
  rw [Function.update_self] at hsum
  simp only [restPayoff_update] at hsum
  simp only [← expectedPayoff_update_single_eq_restPayoff u σ i j] at hsum
  exact hsum

/-- **Expected payoff of a mixed deviation.** For every mixed strategy `τ` of player `i`,
`U_i(τ, σ_{-i}) = ∑ₐ τ(a) U_i(a, σ_{-i})`. -/
theorem expectedPayoff_update_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] (u : ι → (∀ i, A i) → ℝ) (σ : ∀ i, StdSimplex ℝ (A i)) (i : ι)
    (τ : StdSimplex ℝ (A i)) :
    expectedPayoff u (Function.update σ i τ) i =
      ∑ a, τ.weights a * pureExpectedPayoff u σ i a := by
  exact expectedPayoff_update_eq_sum_update_single u σ i i τ

/-- **Expected payoff as an average of pure payoffs.**
`U_i(σ) = ∑ₐ σ_i(a) U_i(a, σ_{-i})`. -/
theorem expectedPayoff_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] (u : ι → (∀ i, A i) → ℝ) (σ : ∀ i, StdSimplex ℝ (A i)) (i : ι) :
    expectedPayoff u σ i = ∑ a, (σ i).weights a * pureExpectedPayoff u σ i a := by
  have h := expectedPayoff_update_eq_sum u σ i (σ i)
  rwa [Function.update_eq_self] at h

/-- The payoffs of the pure actions of player `i` do not depend on the mixed strategy of `i`. -/
theorem pureExpectedPayoff_update {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] (u : ι → (∀ i, A i) → ℝ) (σ : ∀ i, StdSimplex ℝ (A i)) (i : ι)
    (τ : StdSimplex ℝ (A i)) (a : A i) :
    pureExpectedPayoff u (Function.update σ i τ) i a = pureExpectedPayoff u σ i a := by
  unfold pureExpectedPayoff
  rw [Function.update_idem]

/-- **Support characterization of mixed best responses** (Savani and von Stengel 2006, Lemma 1,
for `n` players). Against the mixed strategies `σ_{-i}` of the other players, the mixed strategy
`τ` of player `i` is a best response if and only if every pure action in the support of `τ`
earns at least as much as every pure action of `i`. -/
theorem forall_expectedPayoff_update_le_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (u : ι → (∀ i, A i) → ℝ)
    (σ : ∀ i, StdSimplex ℝ (A i)) (i : ι) (τ : StdSimplex ℝ (A i)) :
    (∀ τ' : StdSimplex ℝ (A i), expectedPayoff u (Function.update σ i τ') i ≤
        expectedPayoff u (Function.update σ i τ) i) ↔
      ∀ a, τ.weights a ≠ 0 → ∀ b, pureExpectedPayoff u σ i b ≤ pureExpectedPayoff u σ i a := by
  simp only [expectedPayoff_update_eq_sum]
  exact best_response_iff_support_max τ (pureExpectedPayoff u σ i)

/-- **Pure deviations suffice.** `σ` is a mixed Nash equilibrium if and only if no player gains
by a unilateral deviation to a pure action: `U_i(a, σ_{-i}) ≤ U_i(σ)` for every player `i` and
every pure action `a` of `i`. -/
theorem isMixedNash_iff_forall_pureExpectedPayoff_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (u : ι → (∀ i, A i) → ℝ)
    (σ : ∀ i, StdSimplex ℝ (A i)) :
    IsMixedNash u σ ↔ ∀ i (a : A i), pureExpectedPayoff u σ i a ≤ expectedPayoff u σ i := by
  constructor
  · intro h i a
    exact h i (StdSimplex.single a)
  · intro h i τ
    rw [expectedPayoff_update_eq_sum]
    exact weighted_avg_le τ _ _ (h i)

/-- **Best-response (support) condition** (Nash 1951; Savani and von Stengel 2006, Lemma 1,
applied to each player). `σ` is a mixed Nash equilibrium if and only if, for every player `i`,
every pure action in the support of `σ i` earns at least as much against `σ_{-i}` as every pure
action of `i`. -/
theorem isMixedNash_iff_support {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] (u : ι → (∀ i, A i) → ℝ) (σ : ∀ i, StdSimplex ℝ (A i)) :
    IsMixedNash u σ ↔ ∀ i (a : A i), (σ i).weights a ≠ 0 → ∀ b : A i,
      pureExpectedPayoff u σ i b ≤ pureExpectedPayoff u σ i a := by
  constructor
  · intro h i a ha b
    have hbest : ∀ τ' : StdSimplex ℝ (A i), expectedPayoff u (Function.update σ i τ') i ≤
        expectedPayoff u (Function.update σ i (σ i)) i := by
      intro τ'
      rw [Function.update_eq_self]
      exact h i τ'
    exact (forall_expectedPayoff_update_le_iff u σ i (σ i)).mp hbest a ha b
  · intro h i τ
    have hsupp := (forall_expectedPayoff_update_le_iff u σ i (σ i)).mpr (h i)
    have hle := hsupp τ
    rwa [Function.update_eq_self] at hle

/-- **Indifference on the support.** In a mixed Nash equilibrium, every pure action that
player `i` plays with positive probability earns exactly the equilibrium payoff of `i`. -/
theorem IsMixedNash.pureExpectedPayoff_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] {u : ι → (∀ i, A i) → ℝ}
    {σ : ∀ i, StdSimplex ℝ (A i)} (h : IsMixedNash u σ) {i : ι} {a : A i}
    (ha : (σ i).weights a ≠ 0) : pureExpectedPayoff u σ i a = expectedPayoff u σ i := by
  have hle : pureExpectedPayoff u σ i a ≤ expectedPayoff u σ i :=
    (isMixedNash_iff_forall_pureExpectedPayoff_le u σ).mp h i a
  have hmax : ∀ b, pureExpectedPayoff u σ i b ≤ pureExpectedPayoff u σ i a :=
    (isMixedNash_iff_support u σ).mp h i a ha
  have hge : expectedPayoff u σ i ≤ pureExpectedPayoff u σ i a := by
    rw [expectedPayoff_eq_sum]
    exact weighted_avg_le (σ i) _ _ hmax
  exact le_antisymm hle hge

end MathlibExt.GameTheory.MixedNashExistence
