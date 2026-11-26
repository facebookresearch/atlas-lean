/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.NoRegretDynamics
public import MathlibExt.GameTheory.PotentialGame
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! # Price of anarchy `5/2` for atomic congestion games with affine delays

An atomic congestion game has *affine delays* when every resource `e` used by `n` players
costs each of them `aₑ n + bₑ` with `aₑ, bₑ ≥ 0`. Christodoulou and Koutsoupias, and
independently Awerbuch, Azar and Epstein, proved that its pure Nash equilibria cost at most
`5/2` times the optimum. Roughgarden observed that their argument shows that such games are
`(5/3, 1/3)`-smooth, so the bound `5/2` also holds for coarse correlated equilibria and for
the time-averaged social cost of no-regret dynamics.

The key inequality is Christodoulou–Koutsoupias, Lemma 1: `y (z + 1) ≤ 5/3 y² + 1/3 z²` for
all natural numbers `y, z`.

## Main results

* `nat_mul_succ_le`: the Christodoulou–Koutsoupias inequality.
* `isSmooth_of_affine`: affine congestion games are `(5/3, 1/3)`-smooth
  (Roughgarden 2015, Example 2.5).
* `socialCost_le_of_isPureNash_of_affine`: price of anarchy `5/2` for pure
  Nash equilibria (Christodoulou–Koutsoupias 2005; Awerbuch–Azar–Epstein 2005).
* `average_socialCost_le_of_affine`: the same bound, up to the regret term, for
  no-regret dynamics.

## Relation to `MathlibExt.GameTheory.CongestionPoA`

That module proves the price-of-anarchy bound `5/2` for singleton congestion games only (each
player uses one resource), as `MathlibExt.GameTheory.CongestionGame.congestion_poa`, assuming
only that no player gains by switching to its resource in the profile it is compared with; its
private `key_ineq` is `nat_mul_succ_le`. It has no smoothness or no-regret results.

## References

* G. Christodoulou and E. Koutsoupias, "The price of anarchy of finite congestion games",
  STOC 2005, 67–73, Lemma 1 and Theorem 1.
* B. Awerbuch, Y. Azar and A. Epstein, "The price of routing unsplittable flow", STOC 2005,
  57–66.
* T. Roughgarden, "Intrinsic robustness of the price of anarchy", J. ACM 62(5) (2015),
  Article 32, Example 2.5 and Theorems 3.2–3.3.
-/

namespace MathlibExt.GameTheory.AffineCongestionGame

open Finset MathlibExt.GameTheory.PotentialGame MathlibExt.GameTheory.NoRegretDynamics

/-- **Christodoulou–Koutsoupias inequality** (Christodoulou–Koutsoupias 2005, Lemma 1):
`y (z + 1) ≤ 5/3 y² + 1/3 z²` for all natural numbers `y` and `z`. -/
theorem nat_mul_succ_le (y z : ℕ) :
    (y : ℝ) * (z + 1) ≤ 5 / 3 * (y : ℝ) ^ 2 + 1 / 3 * (z : ℝ) ^ 2 := by
  rcases Nat.lt_or_ge y 2 with hy | hy
  · interval_cases y
    · simp
    · rcases Nat.lt_or_ge z 2 with hz | hz
      · interval_cases z <;> norm_num
      · have hz' : (2 : ℝ) ≤ z := by exact_mod_cast hz
        push_cast; nlinarith
  · have hy' : (2 : ℝ) ≤ y := by exact_mod_cast hy
    nlinarith [sq_nonneg (2 * (z : ℝ) - 3 * y)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} {R : Type*} [DecidableEq R]

omit [DecidableEq ι] in
/-- Summing a function of the resources over every player's resource set counts each resource
with the number of players using it. -/
theorem sum_sum_uses (U : ι → Finset R) (h : R → ℝ) [Fintype R] :
    ∑ i, ∑ e ∈ U i, h e = ∑ e, (#{i | e ∈ U i} : ℝ) * h e := by
  rw [sum_comm' (t' := univ) (s' := fun e => univ.filter fun i => e ∈ U i) (fun i e => by simp)]
  simp [sum_const, nsmul_eq_mul]

variable (G : CongestionGame ι R S)

/-- The load of a resource in a deviation `(tᵢ, s₋ᵢ)` used by the deviator is at most one
more than its load at `s`. -/
theorem load_update_le (s : ∀ i, S i) (i : ι) (a : S i) (e : R) :
    G.load (Function.update s i a) e ≤ G.load s e + 1 := by
  rw [G.load_eq (Function.update s i a) i e, G.loadOthers_update, G.load_eq s i e]
  split_ifs <;> omega

/-- **Affine congestion games are `(5/3, 1/3)`-smooth** (Roughgarden 2015, Example 2.5): if
every delay is `dₑ(n) = aₑ n + bₑ` with `aₑ, bₑ ≥ 0`, then
`∑ᵢ costᵢ(tᵢ, s₋ᵢ) ≤ 5/3 C(t) + 1/3 C(s)` for all profiles `s` and `t`. -/
theorem isSmooth_of_affine [Finite R] {a b : R → ℝ} (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hdelay : ∀ e n, G.delay e n = a e * n + b e) :
    IsSmooth G.cost (5 / 3) (1 / 3) := by
  cases nonempty_fintype R
  intro s t
  have hdev : ∑ i, G.cost i (Function.update s i (t i)) ≤
      ∑ e, (G.load t e : ℝ) * (a e * (G.load s e + 1) + b e) := by
    calc ∑ i, G.cost i (Function.update s i (t i))
        ≤ ∑ i, ∑ e ∈ G.uses i (t i), (a e * (G.load s e + 1) + b e) := by
          refine sum_le_sum fun i _ => ?_
          simp only [PotentialGame.CongestionGame.cost, Function.update_self]
          refine sum_le_sum fun e _ => ?_
          rw [hdelay]
          have := load_update_le G s i (t i) e
          have : (G.load (Function.update s i (t i)) e : ℝ) ≤ G.load s e + 1 := by
            exact_mod_cast this
          nlinarith [ha e]
      _ = _ := sum_sum_uses (fun i => G.uses i (t i)) _
  have hC : ∀ u : ∀ i, S i, socialCost G.cost u =
      ∑ e, (G.load u e : ℝ) * (a e * G.load u e + b e) := by
    intro u
    simp only [socialCost, PotentialGame.CongestionGame.cost, hdelay]
    exact sum_sum_uses (fun i => G.uses i (u i)) _
  rw [hC s, hC t, mul_sum, mul_sum, ← sum_add_distrib]
  refine hdev.trans (sum_le_sum fun e _ => ?_)
  have key := nat_mul_succ_le (G.load t e) (G.load s e)
  have hx : (0 : ℝ) ≤ G.load s e := Nat.cast_nonneg _
  have hy : (0 : ℝ) ≤ G.load t e := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left key (ha e), mul_nonneg (hb e) hx, mul_nonneg (hb e) hy]

/-- **Price of anarchy `5/2` for affine congestion games** (Christodoulou–Koutsoupias 2005,
Theorem 1; Awerbuch–Azar–Epstein 2005): with delays `aₑ n + bₑ`, `aₑ, bₑ ≥ 0`, every pure
Nash equilibrium `s` has social cost at most `5/2` times that of every profile `t`. -/
theorem socialCost_le_of_isPureNash_of_affine [Finite R] {a b : R → ℝ} (ha : ∀ e, 0 ≤ a e)
    (hb : ∀ e, 0 ≤ b e) (hdelay : ∀ e n, G.delay e n = a e * n + b e) {s : ∀ i, S i}
    (hs : IsPureNash G.cost s) (t : ∀ i, S i) :
    socialCost G.cost s ≤ 5 / 2 * socialCost G.cost t := by
  have hsm := isSmooth_of_affine G ha hb hdelay s t
  have hne : socialCost G.cost s ≤ ∑ i, G.cost i (Function.update s i (t i)) :=
    sum_le_sum fun i _ => hs i (t i)
  linarith

/-- **Robust price of anarchy `5/2` for no-regret play in affine congestion games**
(Roughgarden 2015, Example 2.5 with Theorem 3.3): if after `T ≥ 1` rounds every player's
regret against every fixed strategy is at most `T ε`, the time-averaged social cost is at most
`5/2 C(t) + 3/2 |ι| ε` for every profile `t`. -/
theorem average_socialCost_le_of_affine [Finite R] [∀ i, Finite (S i)] {a b : R → ℝ}
    (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e) (hdelay : ∀ e n, G.delay e n = a e * n + b e)
    {T : ℕ} (hT : 0 < T) {play : Fin T → ∀ i, S i} {ε : ℝ}
    (hreg : ∀ i a, regret G.cost play i a ≤ T * ε) (t : ∀ i, S i) :
    (∑ k, socialCost G.cost (play k)) / T ≤
      5 / 2 * socialCost G.cost t + 3 / 2 * (Fintype.card ι * ε) := by
  have := (isSmooth_of_affine G ha hb hdelay).average_socialCost_le hT hreg t
  linarith

end MathlibExt.GameTheory.AffineCongestionGame
