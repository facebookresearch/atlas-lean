/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.StrategicGame
public import MathlibExt.GameTheory.DominantStrategy
public import MathlibExt.GameTheory.PotentialGames
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Function.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Normal-form game adapters

Cost view, potential results and dominance for `StrategicGame`.

Clause map:
- C1 cost view: `cost`, `cost_eq`, `ofCost`, `cost_ofCost`, `ofCost_cost`.
- C2 payoff Nash: `isNash_iff_dominantStrategy_isNash`.
- C3 cost Nash: `isNash_iff_isPureNash_cost`.
- C4a potential minimizer: `isNash_of_isExactPotential_of_min`.
- C4b no improvement path: `no_infinite_payoff_improvement_path`.
- C5 strict dominance: `isNash_of_forall_isStrictlyDominant`,
  `eq_of_isNash_of_forall_isStrictlyDominant`.
- C6 weak dominance: `IsWeaklyDominant`.
- C7 Nash via weak dominance: `isNash_of_forall_isWeaklyDominant`.

Reverse map is the same list read by declaration.
Matching pennies and the constant game are covered by the
`StrategicGame` test module.
-/

namespace MathlibExt.GameTheory

namespace StrategicGame

/-- C1: cost view, `cost G i σ = -payoff`. -/
def cost {ι : Type*} {S : ι → Type*} (G : StrategicGame ι S)
    (i : ι) (σ : ∀ i, S i) : ℝ :=
  -G.payoff i σ

/-- C1: unfolding lemma for `cost`. -/
theorem cost_eq {ι : Type*} {S : ι → Type*} (G : StrategicGame ι S)
    (i : ι) (σ : ∀ i, S i) : G.cost i σ = -G.payoff i σ :=
  rfl

/-- C1: build a game from costs, with payoff `-c`. -/
def ofCost {ι : Type*} {S : ι → Type*} (c : ι → (∀ i, S i) → ℝ)
    (h : ∀ i, Nonempty (S i)) : StrategicGame ι S where
  payoff := fun i σ => -c i σ
  strategy_nonempty := h

/-- C1: the cost of `ofCost c` is `c`. -/
theorem cost_ofCost {ι : Type*} {S : ι → Type*} (c : ι → (∀ i, S i) → ℝ)
    (h : ∀ i, Nonempty (S i)) : (ofCost c h).cost = c :=
  funext fun _i => funext fun _σ => neg_neg _

/-- C1: `ofCost` of the cost view is the game. -/
theorem ofCost_cost {ι : Type*} {S : ι → Type*} (G : StrategicGame ι S) :
    ofCost G.cost G.strategy_nonempty = G := by
  cases G with
  | mk payoff h =>
    have hpay : (fun i σ => -(-payoff i σ)) = payoff :=
      funext fun i => funext fun σ => neg_neg _
    change (⟨fun i σ => -(-payoff i σ), h⟩ : StrategicGame ι S) = ⟨payoff, h⟩
    rw [hpay]

/-- C2: Nash via payoff functions. -/
theorem isNash_iff_dominantStrategy_isNash {ι : Type*} [DecidableEq ι]
    {S : ι → Type*} (G : StrategicGame ι S) (σ : ∀ i, S i) :
    G.IsNash σ ↔ DominantStrategy.IsNash G.payoff σ :=
  isNash_iff_update_le G σ

/-- C3: Nash via the cost view. -/
theorem isNash_iff_isPureNash_cost {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] (G : StrategicGame ι S)
    (σ : ∀ i, S i) :
    G.IsNash σ ↔ @_root_.IsPureNash ι _ _ S _ G.strategy_nonempty G.cost σ := by
  have := G.strategy_nonempty
  rw [isNash_iff_update_le G σ]
  change (∀ i t, G.payoff i (Function.update σ i t) ≤ G.payoff i σ) ↔
    (∀ i a, G.cost i σ ≤ G.cost i (Function.update σ i a))
  simp [cost_eq, neg_le_neg_iff]

/-- C4a: minimizer of an exact potential is Nash. -/
theorem isNash_of_isExactPotential_of_min {ι : Type*} [Fintype ι]
    [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    (G : StrategicGame ι S) (Φ : (∀ i, S i) → ℝ) (σ : ∀ i, S i)
    (hΦ : @_root_.IsExactPotential ι _ _ S _ G.strategy_nonempty G.cost Φ)
    (hmin : ∀ t, Φ σ ≤ Φ t) : G.IsNash σ := by
  have := G.strategy_nonempty
  rw [isNash_iff_isPureNash_cost G σ]
  exact _root_.pureNash_of_min_potential hΦ σ hmin

/-- C4b: no infinite payoff improvement path with a potential. -/
theorem no_infinite_payoff_improvement_path {ι : Type*} [Fintype ι]
    [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    (G : StrategicGame ι S) (Φ : (∀ i, S i) → ℝ)
    (hΦ : @_root_.IsExactPotential ι _ _ S _ G.strategy_nonempty G.cost Φ)
    (s : ℕ → ∀ i, S i)
    (hstep : ∀ k, ∃ i a, s (k + 1) = Function.update (s k) i a ∧
      G.payoff i (s k) < G.payoff i (s (k + 1))) : False := by
  have := G.strategy_nonempty
  apply _root_.no_infinite_improvement_path hΦ s
  intro k
  obtain ⟨i, a, heq, hlt⟩ := hstep k
  exact ⟨i, a, heq, by simp only [cost_eq]; exact neg_lt_neg_iff.mpr hlt⟩

/-- C5: strictly dominant profile is Nash. -/
theorem isNash_of_forall_isStrictlyDominant {ι : Type*} [DecidableEq ι]
    {S : ι → Type*} (G : StrategicGame ι S) (σ : ∀ i, S i)
    (h : ∀ i, @DominantStrategy.IsStrictlyDominant ι _ S
      G.strategy_nonempty G.payoff i (σ i)) : G.IsNash σ := by
  have := G.strategy_nonempty
  rw [isNash_iff_dominantStrategy_isNash G σ]
  exact DominantStrategy.isNash_of_isStrictlyDominant h

/-- C5: strictly dominant profile is the unique Nash. -/
theorem eq_of_isNash_of_forall_isStrictlyDominant {ι : Type*} [DecidableEq ι]
    {S : ι → Type*} (G : StrategicGame ι S) (σ τ : ∀ i, S i)
    (h : ∀ i, @DominantStrategy.IsStrictlyDominant ι _ S
      G.strategy_nonempty G.payoff i (σ i)) (hτ : G.IsNash τ) : τ = σ := by
  have := G.strategy_nonempty
  rw [isNash_iff_dominantStrategy_isNash G τ] at hτ
  exact DominantStrategy.eq_of_isNash_of_isStrictlyDominant h hτ

/-- C6: weak dominance on the anchor. -/
def IsWeaklyDominant {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (G : StrategicGame ι S) (i : ι) (a : S i) : Prop :=
  ∀ (τ : ∀ j, S j) (t : S i),
    G.payoff i (Function.update τ i t) ≤ G.payoff i (Function.update τ i a)

/-- C7: weakly dominant profile is Nash. -/
theorem isNash_of_forall_isWeaklyDominant {ι : Type*} [DecidableEq ι]
    {S : ι → Type*} (G : StrategicGame ι S) (σ : ∀ i, S i)
    (h : ∀ i, G.IsWeaklyDominant i (σ i)) : G.IsNash σ := by
  rw [isNash_iff_update_le G σ]
  intro i t
  have hle := h i σ t
  have heq : Function.update σ i (σ i) = σ := Function.update_eq_self i σ
  rw [heq] at hle
  exact hle

end StrategicGame

end MathlibExt.GameTheory
