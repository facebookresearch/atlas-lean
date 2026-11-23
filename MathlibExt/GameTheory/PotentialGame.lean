/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Order.WellFounded
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Potential games, Rosenthal's theorem and the price of stability

A finite strategic game in cost form has players `ι`, a strategy type `S i` for every
player and a cost `cost i s` of player `i` at the strategy profile `s : ∀ i, S i`;
players minimise cost. A profile is a *pure Nash equilibrium* when no player can lower
its cost by a unilateral deviation `Function.update s i a`.

A function `Φ` on profiles is an *exact potential* (Monderer–Shapley) when every
unilateral deviation changes the deviator's cost by exactly the change in `Φ`. Then every
strictly improving move strictly decreases `Φ`, so in a finite game improvement paths
are finite and a minimiser of `Φ` is a pure Nash equilibrium.

Rosenthal (1973) showed that *congestion games* — each player chooses a set of resources
and pays, on each resource it uses, a delay depending on the number of players using
it — have the exact potential `Φ(s) = ∑ₑ ∑_{k=1}^{nₑ(s)} dₑ(k)`.

In the *fair cost-sharing* network design game of Anshelevich, Dasgupta, Kleinberg,
Tardos, Wexler and Roughgarden, the players using an edge of cost `cₑ ≥ 0` split it
equally. It is a congestion game with `dₑ(k) = cₑ / k`, its Rosenthal potential lies
between the network cost and `H(k)` times it, and hence some pure Nash equilibrium costs
at most `H(k)` times the optimum, where `k` is the number of players and `H(k)` the
`k`-th harmonic number: the price of stability is at most `H(k)`.

## Main results

* `IsExactPotential.isPureNash_of_forall_le`, `IsExactPotential.exists_isPureNash`:
  a minimiser of an exact potential is a pure Nash equilibrium, so finite potential games
  have pure Nash equilibria (Monderer–Shapley, Lemma 2.1 and Corollary 2.2).
* `IsExactPotential.wellFounded_improvingMove`: the finite improvement property — there
  is no infinite sequence of strictly improving unilateral moves (Monderer–Shapley,
  Lemma 2.3).
* `CongestionGame.isExactPotential_potential`: Rosenthal's theorem.
* `FairCostSharing.exists_isPureNash_networkCost_le`: price of stability at most `H(k)`
  (Anshelevich et al., Theorem 2.1).

## Relation to `MathlibExt.GameTheory.PotentialGames`

That module declares `IsExactPotential` and `IsPureNash` in the root namespace (same conditions,
plus `Fintype` and `Nonempty` assumptions) and proves `pureNash_of_min_potential` and
`no_infinite_improvement_path`, the counterparts of `IsExactPotential.isPureNash_of_forall_le`
and `IsExactPotential.wellFounded_improvingMove`; it has no congestion or cost-sharing games.

## References

* R. W. Rosenthal, "A class of games possessing pure-strategy Nash equilibria",
  Int. J. Game Theory 2 (1973), 65–67, Theorem 1.
* D. Monderer and L. S. Shapley, "Potential games", Games Econom. Behav. 14 (1996),
  124–143, Lemmas 2.1 and 2.3, Corollary 2.2.
* E. Anshelevich, A. Dasgupta, J. Kleinberg, É. Tardos, T. Wexler and T. Roughgarden,
  "The price of stability for network design with fair cost allocation",
  SIAM J. Comput. 38(4) (2008), 1602–1623, Theorem 2.1.
* J. Kleinberg and É. Tardos, *Algorithm Design*, Addison-Wesley, 2005, §12.7.
-/

namespace MathlibExt.GameTheory.PotentialGame

open Finset

variable {ι : Type*} [DecidableEq ι] {S : ι → Type*}

section General

/-- A pure Nash equilibrium of the game with costs `cost`: no player lowers its cost by
changing only its own strategy. -/
def IsPureNash (cost : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : Prop :=
  ∀ i (a : S i), cost i s ≤ cost i (Function.update s i a)

/-- `Φ` is an exact potential for `cost`: a unilateral deviation of player `i` changes
`cost i` by exactly the change in `Φ` (Monderer–Shapley 1996, §2). -/
def IsExactPotential (cost : ι → (∀ i, S i) → ℝ) (Φ : (∀ i, S i) → ℝ) : Prop :=
  ∀ s i (a : S i),
    cost i (Function.update s i a) - cost i s = Φ (Function.update s i a) - Φ s

/-- `t` is reached from `s` by a strictly improving unilateral move of some player. -/
def ImprovingMove (cost : ι → (∀ i, S i) → ℝ) (t s : ∀ i, S i) : Prop :=
  ∃ i, ∃ a : S i, t = Function.update s i a ∧ cost i t < cost i s

variable {cost : ι → (∀ i, S i) → ℝ} {Φ : (∀ i, S i) → ℝ}

/-- A global minimiser of an exact potential is a pure Nash equilibrium. -/
theorem IsExactPotential.isPureNash_of_forall_le (hΦ : IsExactPotential cost Φ)
    {s : ∀ i, S i} (hs : ∀ t, Φ s ≤ Φ t) : IsPureNash cost s := by
  intro i a
  have := hΦ s i a
  have := hs (Function.update s i a)
  linarith

/-- Every game with finitely many strategy profiles and an exact potential has a pure Nash
equilibrium (Monderer–Shapley 1996, Corollary 2.2; Rosenthal 1973). -/
theorem IsExactPotential.exists_isPureNash [Finite (∀ i, S i)] [Nonempty (∀ i, S i)]
    (hΦ : IsExactPotential cost Φ) : ∃ s, IsPureNash cost s := by
  obtain ⟨s, hs⟩ := Finite.exists_min Φ
  exact ⟨s, hΦ.isPureNash_of_forall_le hs⟩

/-- A strictly improving move strictly decreases an exact potential. -/
theorem IsExactPotential.lt_of_improvingMove (hΦ : IsExactPotential cost Φ)
    {s t : ∀ i, S i} (h : ImprovingMove cost t s) : Φ t < Φ s := by
  obtain ⟨i, a, rfl, hlt⟩ := h
  have := hΦ s i a
  linarith

/-- **Finite improvement property** (Monderer–Shapley 1996, Lemma 2.3): in a game with
finitely many profiles and an exact potential, the improving-move relation is
well-founded, i.e. every sequence of strictly improving unilateral moves is finite; in
particular best-response dynamics terminate at a pure Nash equilibrium. -/
theorem IsExactPotential.wellFounded_improvingMove [Finite (∀ i, S i)]
    (hΦ : IsExactPotential cost Φ) : WellFounded (ImprovingMove cost) := by
  have : IsTrans (∀ i, S i) (fun t s => Φ t < Φ s) := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
  have : Std.Irrefl (fun t s : ∀ i, S i => Φ t < Φ s) := ⟨fun _ => lt_irrefl _⟩
  exact Subrelation.wf (fun h => hΦ.lt_of_improvingMove h)
    (Finite.wellFounded_of_trans_of_irrefl _)

end General

/-- A congestion game (Rosenthal 1973): player `i` choosing strategy `a` uses the resource
set `uses i a`, and a resource `e` used by `n` players costs each of them `delay e n`. -/
structure CongestionGame (ι R : Type*) (S : ι → Type*) where
  /-- The resources used by a strategy. -/
  uses : ∀ i, S i → Finset R
  /-- The delay of a resource as a function of the number of its users. -/
  delay : R → ℕ → ℝ

namespace CongestionGame

variable {R : Type*} [Fintype ι] [Fintype R] [DecidableEq R] (G : CongestionGame ι R S)

/-- The number of players using resource `e` at the profile `s`. -/
def load (s : ∀ i, S i) (e : R) : ℕ :=
  #{i | e ∈ G.uses i (s i)}

/-- The cost of player `i`: the sum of the delays of the resources it uses. -/
def cost (i : ι) (s : ∀ i, S i) : ℝ :=
  ∑ e ∈ G.uses i (s i), G.delay e (G.load s e)

/-- Rosenthal's potential `∑ₑ ∑_{k=1}^{nₑ(s)} dₑ(k)`. -/
def potential (s : ∀ i, S i) : ℝ :=
  ∑ e, ∑ k ∈ range (G.load s e), G.delay e (k + 1)

/-- The number of players other than `i` using resource `e`. -/
def loadOthers (s : ∀ i, S i) (i : ι) (e : R) : ℕ :=
  #{j | j ≠ i ∧ e ∈ G.uses j (s j)}

omit [Fintype R] in
/-- The load of a resource is the number of other players using it, plus one if player
`i` uses it. -/
theorem load_eq (s : ∀ i, S i) (i : ι) (e : R) :
    G.load s e = G.loadOthers s i e + if e ∈ G.uses i (s i) then 1 else 0 := by
  unfold load loadOthers
  rw [← card_filter_add_card_filter_not (s := univ.filter fun j => e ∈ G.uses j (s j))
    (fun j => j ≠ i)]
  congr 1
  · rw [filter_filter]
    congr 1
    ext j
    simp [and_comm]
  · split_ifs with h
    · rw [card_eq_one]
      refine ⟨i, ?_⟩
      ext j
      simp only [mem_filter, mem_univ, true_and, not_not, mem_singleton]
      constructor
      · exact fun h' => h'.2
      · rintro rfl
        exact ⟨h, rfl⟩
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro j hj hji
      simp only [mem_filter, mem_univ, true_and, not_not] at hj hji
      exact h (hji ▸ hj)

omit [Fintype R] in
/-- The number of players other than `i` using a resource does not depend on `i`'s
strategy. -/
theorem loadOthers_update (s : ∀ i, S i) (i : ι) (a : S i) (e : R) :
    G.loadOthers (Function.update s i a) i e = G.loadOthers s i e := by
  unfold loadOthers
  congr 1
  ext j
  simp only [mem_filter, mem_univ, true_and]
  constructor <;> rintro ⟨hj, h⟩ <;> exact ⟨hj, by simpa [Function.update_of_ne hj] using h⟩

/-- Rosenthal's potential splits into a part that does not depend on player `i`'s
strategy and player `i`'s cost. -/
theorem potential_eq (s : ∀ i, S i) (i : ι) :
    G.potential s = (∑ e, ∑ k ∈ range (G.loadOthers s i e), G.delay e (k + 1)) +
      G.cost i s := by
  have hcost : G.cost i s = ∑ e, if e ∈ G.uses i (s i) then
      G.delay e (G.loadOthers s i e + 1) else 0 := by
    rw [← sum_filter, cost]
    have : univ.filter (fun e => e ∈ G.uses i (s i)) = G.uses i (s i) := by ext; simp
    rw [this]
    refine sum_congr rfl fun e he => ?_
    rw [G.load_eq s i e]
    simp [he]
  rw [hcost, potential, ← sum_add_distrib]
  refine sum_congr rfl fun e _ => ?_
  rw [G.load_eq s i e]
  split_ifs
  · rw [sum_range_succ]
  · simp

/-- **Rosenthal's theorem** (Rosenthal 1973, Theorem 1): congestion games are exact
potential games, with potential `∑ₑ ∑_{k=1}^{nₑ(s)} dₑ(k)`. -/
theorem isExactPotential_potential : IsExactPotential G.cost G.potential := by
  intro s i a
  rw [G.potential_eq (Function.update s i a) i, G.potential_eq s i]
  simp only [loadOthers_update]
  ring

omit [Fintype R] in
/-- Every finite congestion game has a pure Nash equilibrium (Rosenthal 1973). -/
theorem exists_isPureNash [Finite R] [∀ i, Finite (S i)] [∀ i, Nonempty (S i)] :
    ∃ s, IsPureNash G.cost s := by
  cases nonempty_fintype R
  exact G.isExactPotential_potential.exists_isPureNash

end CongestionGame

/-- The fair cost-sharing network design game (Anshelevich et al. 2008, §2): player `i`
choosing `a` buys the edge set `uses i a`, and the cost `c e ≥ 0` of each edge is split
equally among the players using it. -/
structure FairCostSharing (ι R : Type*) (S : ι → Type*) where
  /-- The edges used by a strategy. -/
  uses : ∀ i, S i → Finset R
  /-- The cost of building an edge. -/
  edgeCost : R → ℝ
  edgeCost_nonneg : ∀ e, 0 ≤ edgeCost e

namespace FairCostSharing

variable {R : Type*} [Fintype ι] [Fintype R] [DecidableEq R] (G : FairCostSharing ι R S)

/-- Fair cost sharing as a congestion game with delay `cₑ / n`. -/
noncomputable def toCongestionGame : CongestionGame ι R S where
  uses := G.uses
  delay e n := G.edgeCost e / n

/-- The cost of the network built at `s`: the total cost of the edges used by some player. -/
noncomputable def networkCost (s : ∀ i, S i) : ℝ :=
  ∑ e with 0 < G.toCongestionGame.load s e, G.edgeCost e

omit [DecidableEq ι] in
/-- The Rosenthal potential of fair cost sharing is `∑ₑ cₑ H(nₑ)`. -/
theorem potential_eq (s : ∀ i, S i) :
    G.toCongestionGame.potential s =
      ∑ e, G.edgeCost e * (harmonic (G.toCongestionGame.load s e) : ℝ) := by
  unfold CongestionGame.potential
  refine sum_congr rfl fun e _ => ?_
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  simp [toCongestionGame, div_eq_mul_inv]

private theorem harmonic_mono {m n : ℕ} (h : m ≤ n) : (harmonic m : ℝ) ≤ harmonic n := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 h)
    fun _ _ _ => by positivity

private theorem one_le_harmonic {n : ℕ} (h : 0 < n) : (1 : ℝ) ≤ harmonic n := by
  have := harmonic_mono (Nat.one_le_iff_ne_zero.2 h.ne')
  simpa using this

omit [DecidableEq ι] in
/-- The network cost is at most the Rosenthal potential (Anshelevich et al. 2008,
proof of Theorem 2.1). -/
theorem networkCost_le_potential (s : ∀ i, S i) :
    G.networkCost s ≤ G.toCongestionGame.potential s := by
  rw [potential_eq, networkCost, sum_filter]
  refine sum_le_sum fun e _ => ?_
  split_ifs with h
  · exact le_mul_of_one_le_right (G.edgeCost_nonneg e) (one_le_harmonic h)
  · exact mul_nonneg (G.edgeCost_nonneg e) (by simp only [harmonic, Rat.cast_sum]; positivity)

omit [DecidableEq ι] in
/-- The Rosenthal potential is at most `H(k)` times the network cost, where `k` is the
number of players (Anshelevich et al. 2008, proof of Theorem 2.1). -/
theorem potential_le_harmonic_mul_networkCost (s : ∀ i, S i) :
    G.toCongestionGame.potential s ≤ harmonic (Fintype.card ι) * G.networkCost s := by
  rw [potential_eq, networkCost, sum_filter, mul_sum]
  refine sum_le_sum fun e _ => ?_
  split_ifs with h
  · rw [mul_comm]
    refine mul_le_mul_of_nonneg_right (harmonic_mono ?_) (G.edgeCost_nonneg e)
    exact card_le_univ _
  · simp [Nat.pos_iff_ne_zero.not.1 h |> not_not.1]

/-- **Price of stability at most `H(k)`** (Anshelevich, Dasgupta, Kleinberg, Tardos,
Wexler and Roughgarden 2008, Theorem 2.1; Kleinberg–Tardos, *Algorithm Design*, §12.7):
in the fair cost-sharing game with `k` players and finitely many strategies, some pure Nash
equilibrium builds a network of cost at most `H(k)` times the cost of every profile, in
particular of an optimal one. -/
theorem exists_isPureNash_networkCost_le [∀ i, Finite (S i)] [∀ i, Nonempty (S i)] :
    ∃ s, IsPureNash G.toCongestionGame.cost s ∧
      ∀ t, G.networkCost s ≤ harmonic (Fintype.card ι) * G.networkCost t := by
  obtain ⟨s, hs⟩ := Finite.exists_min G.toCongestionGame.potential
  refine ⟨s, G.toCongestionGame.isExactPotential_potential.isPureNash_of_forall_le hs,
    fun t => ?_⟩
  calc G.networkCost s ≤ G.toCongestionGame.potential s := G.networkCost_le_potential s
    _ ≤ G.toCongestionGame.potential t := hs t
    _ ≤ _ := G.potential_le_harmonic_mul_networkCost t

end FairCostSharing

end MathlibExt.GameTheory.PotentialGame
