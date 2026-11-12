/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Function.Basic

@[expose] public section

/-!
# Strictly dominant strategies and Nash equilibrium

A strategic game has players `ι`, strategy types `S i` and payoffs `u i σ` at profiles
`σ : ∀ i, S i`; player `i`'s unilateral deviation to `t` is `Function.update σ i t`. A strategy is
strictly dominant if it beats every other strategy against every profile of the others. A profile
of strictly dominant strategies is a Nash equilibrium, and the only one. No finiteness is assumed.

The game interface is local (payoff functions, as in `MathlibExt.GameTheory.PotentialGames`);
it should be unified with the `StrategicGame` interface of the pending Atlas EC12.T01 pull request
once that lands.

## Main results

* `isNash_of_isStrictlyDominant`: a strictly dominant-strategy profile is Nash.
* `eq_of_isNash_of_isStrictlyDominant`: it is the unique Nash equilibrium.

## References

* M. J. Osborne and A. Rubinstein, *A Course in Game Theory*, MIT Press (1994), Chapter 2
  (Nash equilibrium) and Section 4.1 (dominated actions).
* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University
  Press (1995), Section 8.B (dominant strategies).
-/

namespace MathlibExt.GameTheory.DominantStrategy

/-- A strategy profile `σ` of the game with payoffs `u i σ` is a (pure) Nash equilibrium: no
player `i` gains by a unilateral deviation to `t`, which yields the profile
`Function.update σ i t`. -/
def IsNash {ι : Type*} [DecidableEq ι] {S : ι → Type*} (u : ι → (∀ i, S i) → ℝ)
    (σ : ∀ i, S i) : Prop :=
  ∀ (i : ι) (t : S i), u i (Function.update σ i t) ≤ u i σ

/-- `s` is a strictly dominant strategy of player `i`: against every profile `τ` of the others'
strategies, `s` gives `i` a strictly higher payoff than any other strategy `t ≠ s`. -/
def IsStrictlyDominant {ι : Type*} [DecidableEq ι] {S : ι → Type*} (u : ι → (∀ i, S i) → ℝ)
    (i : ι) (s : S i) : Prop :=
  ∀ (τ : ∀ j, S j) (t : S i), t ≠ s → u i (Function.update τ i t) < u i (Function.update τ i s)

/-- **A strictly dominant-strategy profile is Nash.** -/
theorem isNash_of_isStrictlyDominant {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    {u : ι → (∀ i, S i) → ℝ} {σ : ∀ i, S i} (h : ∀ i, IsStrictlyDominant u i (σ i)) :
    IsNash u σ := by
  intro i t
  by_cases ht : t = σ i
  · subst ht
    simp [Function.update_eq_self]
  · have hlt := h i σ t ht
    rw [Function.update_eq_self] at hlt
    exact le_of_lt hlt

/-- A strictly dominant-strategy profile is the only Nash equilibrium. -/
theorem eq_of_isNash_of_isStrictlyDominant {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    {u : ι → (∀ i, S i) → ℝ} {σ τ : ∀ i, S i} (h : ∀ i, IsStrictlyDominant u i (σ i))
    (hτ : IsNash u τ) : τ = σ := by
  apply funext
  intro i
  by_contra hne
  have hlt := h i τ (τ i) hne
  rw [Function.update_eq_self] at hlt
  have hle := hτ i (σ i)
  exact (not_le_of_gt hlt) hle

end MathlibExt.GameTheory.DominantStrategy
