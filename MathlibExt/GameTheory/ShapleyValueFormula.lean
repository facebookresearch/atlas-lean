/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ShapleyValue
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Logic.Equiv.Finset

@[expose] public section

/-! # The Shapley value as an average of marginal contributions

Shapley's formula: the unique efficient, symmetric, linear value with the null-player property
(`ShapleyValue.shapley_characterization`) pays player `i`
`φᵢ(v) = ∑_{S ∋ i} (|S| − 1)! (n − |S|)! / n! · (v(S) − v(S \ {i}))`, the average of `i`'s
marginal contributions when all orders of the `n` players are equally likely.

## Main results

* `shapleyFormula`: the formula, as a linear map from games to payoff vectors.
* `shapleyFormula_isEfficient`, `shapleyFormula_isSymmetric`,
  `shapleyFormula_satisfiesNullPlayerAxiom`: it satisfies the three axioms.
* `eq_shapleyFormula`: every value satisfying the axioms is the formula.

## References

* L. S. Shapley, "A value for n-person games", Contributions to the Theory of Games II, Ann. of
  Math. Stud. 28, Princeton Univ. Press (1953), 307–317 (not consulted directly).
* R. Serrano, "Cooperative games: core and Shapley value", CEMFI Working Paper 0709 (2007), §4.1,
  Theorem (Shapley, 1953), with the formula used here (secondary source).
-/

namespace MathlibExt.GameTheory.ShapleyValue

open Finset

variable {Player : Type*} [DecidableEq Player] [Fintype Player]

/-- **Shapley weight.** The probability `(s − 1)! (n − s)! / n!` that, in a uniformly random
order of `n` players, a given player arrives exactly when the coalition of the players before
it, together with itself, is a given coalition of size `s` (Serrano 2007, §4.1). -/
noncomputable def shapleyWeight (n s : ℕ) : ℝ :=
  ((s - 1).factorial * (n - s).factorial : ℝ) / n.factorial

/-- **Shapley's formula.** The value paying player `i` the weighted sum of its marginal
contributions `v(S) − v(S \ {i})` over the coalitions `S` containing `i`, with weights
`shapleyWeight n |S|`, `n` the number of players (Serrano 2007, §4.1, formula for `Shᵢ(N, v)`).
It is linear in the game. -/
noncomputable def shapleyFormula : CoopGame Player →ₗ[ℝ] (Player → ℝ) where
  toFun v i := ∑ S ∈ univ.filter (fun S : Finset Player => i ∈ S),
    shapleyWeight (Fintype.card Player) S.card * (v.charFun ↑S - v.charFun ↑(S.erase i))
  map_add' v w := by
    funext i
    simp only [Pi.add_apply, ← sum_add_distrib]
    refine sum_congr rfl fun S _ => ?_
    change _ * ((v.charFun _ + w.charFun _) - (v.charFun _ + w.charFun _)) = _
    ring
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    refine sum_congr rfl fun S _ => ?_
    change _ * (c * v.charFun _ - c * v.charFun _) = _
    ring

theorem shapleyFormula_apply (v : CoopGame Player) (i : Player) :
    shapleyFormula v i = ∑ S ∈ univ.filter (fun S : Finset Player => i ∈ S),
      shapleyWeight (Fintype.card Player) S.card * (v.charFun ↑S - v.charFun ↑(S.erase i)) :=
  rfl

/-- **Telescoping of the Shapley weights.** For `1 ≤ k ≤ n`,
`k · w(n, k) − (n − k) · w(n, k + 1)` is `1` if `k = n` and `0` otherwise; this is the identity
behind efficiency. -/
theorem shapleyWeight_telescope {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (k : ℝ) * shapleyWeight n k - ((n - k : ℕ) : ℝ) * shapleyWeight n (k + 1) =
      if k = n then 1 else 0 := by
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hk' : (k : ℝ) * ((k - 1).factorial : ℝ) = (k.factorial : ℝ) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp [Nat.factorial_succ]
  unfold shapleyWeight
  simp only [Nat.add_sub_cancel]
  split_ifs with h
  · subst h
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, sub_zero, Nat.factorial_zero,
      Nat.cast_one, mul_one]
    rw [← mul_div_assoc, hk', div_self hn]
  · have hlt : k < n := lt_of_le_of_ne hkn h
    have hnk : ((n - k : ℕ) : ℝ) * ((n - (k + 1)).factorial : ℝ) = ((n - k).factorial : ℝ) := by
      obtain ⟨j, hj⟩ : ∃ j, n - k = j + 1 := ⟨n - k - 1, by omega⟩
      rw [hj, show n - (k + 1) = j by omega]
      simp [Nat.factorial_succ]
    rw [← mul_div_assoc, ← mul_div_assoc, ← mul_assoc, hk', mul_left_comm, hnk, mul_comm, sub_self]

/-- **Shapley's formula is efficient**: it distributes exactly `v(N)`. -/
theorem shapleyFormula_isEfficient : IsEfficient (shapleyFormula (Player := Player)) := by
  intro v
  set n := Fintype.card Player
  set w := shapleyWeight n
  -- Split each marginal contribution and regroup both parts by coalition.
  have h1 : ∑ i : Player, ∑ S ∈ univ.filter (fun S : Finset Player => i ∈ S),
      w S.card * v.charFun ↑S = ∑ S : Finset Player, (S.card : ℝ) * w S.card * v.charFun ↑S := by
    simp_rw [sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun S _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul, filter_mem_eq_inter, univ_inter, mul_assoc]
  have h2 : ∑ i : Player, ∑ S ∈ univ.filter (fun S : Finset Player => i ∈ S),
      w S.card * v.charFun ↑(S.erase i) =
      ∑ T : Finset Player, ((n - T.card : ℕ) : ℝ) * w (T.card + 1) * v.charFun ↑T := by
    have hre : ∀ i : Player, ∑ S ∈ univ.filter (fun S : Finset Player => i ∈ S),
        w S.card * v.charFun ↑(S.erase i) =
        ∑ T ∈ univ.filter (fun T : Finset Player => i ∉ T), w (T.card + 1) * v.charFun ↑T := by
      intro i
      refine sum_nbij' (fun S => S.erase i) (fun T => insert i T) ?_ ?_ ?_ ?_ ?_
      · intro S _; simp
      · intro T _; simp
      · intro S hS
        have hS' : i ∈ S := by simpa using hS
        exact insert_erase hS'
      · intro T hT
        have hT' : i ∉ T := by simpa using hT
        exact erase_insert hT'
      · intro S hS
        simp only [mem_filter, mem_univ, true_and] at hS
        rw [card_erase_of_mem hS, Nat.sub_add_cancel (card_pos.mpr ⟨i, hS⟩)]
    simp_rw [hre, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun T _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_assoc]
    congr 2
    rw [filter_not, filter_mem_eq_inter, univ_inter, card_sdiff_of_subset (subset_univ T),
      card_univ]
  calc ∑ i, shapleyFormula v i
      = ∑ i : Player, ∑ S ∈ univ.filter (fun S : Finset Player => i ∈ S),
          (w S.card * v.charFun ↑S - w S.card * v.charFun ↑(S.erase i)) := by
        refine sum_congr rfl fun i _ => sum_congr rfl fun S _ => ?_
        ring
    _ = ∑ T : Finset Player, ((T.card : ℝ) * w T.card - ((n - T.card : ℕ) : ℝ) * w (T.card + 1)) *
          v.charFun ↑T := by
        simp_rw [sum_sub_distrib]
        rw [h1, h2, ← sum_sub_distrib]
        refine sum_congr rfl fun T _ => ?_
        ring
    _ = ∑ T : Finset Player, if T = univ then v.charFun ↑T else 0 := by
        refine sum_congr rfl fun T _ => ?_
        by_cases hT : T = ∅
        · subst hT
          simp [v.empty]
        · have h1 : 1 ≤ T.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hT)
          rw [shapleyWeight_telescope h1 (card_le_univ T)]
          by_cases hu : T = univ
          · simp [hu]
          · have : T.card ≠ Fintype.card Player := fun h => hu (eq_univ_of_card T h)
            simp [this, hu]
    _ = v.charFun Set.univ := by
        simp

/-- **Shapley's formula gives nothing to null players.** -/
theorem shapleyFormula_satisfiesNullPlayerAxiom :
    SatisfiesNullPlayerAxiom (shapleyFormula (Player := Player)) := by
  intro v i hi
  rw [shapleyFormula_apply]
  refine sum_eq_zero fun S hS => ?_
  simp only [mem_filter, mem_univ, true_and] at hS
  have := hi ↑(S.erase i) (by simp)
  rw [← coe_insert, insert_erase hS] at this
  rw [this, sub_self, mul_zero]

/-- **Shapley's formula is symmetric**: a permutation of the players that leaves the game
invariant leaves the payoffs invariant. -/
theorem shapleyFormula_isSymmetric : IsSymmetric (shapleyFormula (Player := Player)) := by
  intro σ v hv i
  rw [shapleyFormula_apply, shapleyFormula_apply, sum_filter, sum_filter,
    ← (Equiv.finsetCongr σ).sum_comp]
  refine sum_congr rfl fun T _ => ?_
  simp only [Equiv.finsetCongr_apply]
  have hmem : σ i ∈ T.map σ.toEmbedding ↔ i ∈ T := by simp
  have hcard : (T.map σ.toEmbedding).card = T.card := card_map _
  have h1 : v.charFun ↑(T.map σ.toEmbedding) = v.charFun ↑T := by
    rw [coe_map]; exact hv ↑T
  have h2 : v.charFun ↑((T.map σ.toEmbedding).erase (σ i)) = v.charFun ↑(T.erase i) := by
    rw [show σ i = σ.toEmbedding i from rfl, ← map_erase, coe_map]; exact hv _
  simp only [hmem, hcard, h1, h2]

/-- **The Shapley value is given by Shapley's formula** (Shapley 1953, as stated in Serrano 2007,
§4.1). Every linear value on a fixed finite set of players that is efficient, symmetric and
gives nothing to null players pays player `i`
`∑_{S ∋ i} (|S| − 1)! (n − |S|)! / n! · (v(S) − v(S \ {i}))`. -/
theorem eq_shapleyFormula {φ : CoopGame Player →ₗ[ℝ] (Player → ℝ)} (he : IsEfficient φ)
    (hs : IsSymmetric φ) (hn : SatisfiesNullPlayerAxiom φ) : φ = shapleyFormula := by
  classical
  exact (shapley_characterization (Player := Player)).unique ⟨he, hs, hn⟩
    ⟨shapleyFormula_isEfficient, shapleyFormula_isSymmetric,
      shapleyFormula_satisfiesNullPlayerAxiom⟩

end MathlibExt.GameTheory.ShapleyValue
