/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Digraph.TournamentScoreSequence
import Mathlib.Tactic.NormNum.Basic

/-!
# Tests for tournament score sequences

* The cyclic tournament `cyc` on `Fin 3` (a directed `3`-cycle) and the
  transitive tournament `tr` on `Fin 4` (larger players beat smaller
  ones), with their scores, reducibility and circular triads computed by
  `decide` and compared with Theorems 5 and 6.
* Landau's theorem in both directions: `(1, 1, 2, 2)` is a score
  sequence, while `(0, 0, 3)` (total `C(3, 2)`, but the first two players
  have no wins between them) and `(1, 1, 2)` (wrong total) are not. The
  unsorted form recognises `(2, 0, 1)`.
* Theorem 1 at `a = 2`, `b = 0` and `a = 1`, `b = 1`, with a coefficient
  of the series computed directly.
* The helper lemmas on small inputs.
-/

@[expose] public section

namespace MetaMathlibExtTest.TournamentScoreSequence

open Finset MetaMathlibExt
  MathlibExt.GraphTheory.TournamentScoreSequenceWanted

/-! ### A directed `3`-cycle -/

/-- The cyclic tournament on `Fin 3`: `i` beats `i + 1`. -/
def cyc : Fin 3 → Fin 3 → Bool := fun i j => decide (j = i + 1)

theorem isTournament_cyc : IsTournament cyc := by
  unfold IsTournament cyc
  decide

example : ∀ i, score cyc i = 1 := by decide

/-- The whole of `Fin 3` is a circular triad of `cyc`. -/
example : IsCircularTriad cyc Finset.univ := by decide

/-- `cyc` has exactly one circular triad, as Theorem 6 predicts:
`C(3, 3) - 3 * C(1, 2) = 1`. -/
example : ((Finset.univ.powersetCard 3).filter
    (IsCircularTriad cyc)).card = 1 := by
  decide

example : ((Finset.univ.powersetCard 3).filter
    (IsCircularTriad cyc)).card = 1 := by
  rw [card_circularTriads 3 cyc isTournament_cyc]
  decide

/-- The score sequence `(1, 1, 1)` has no proper initial segment summing
to `C(k, 2)`, so by Theorem 5 the directed `3`-cycle is irreducible. -/
example : ¬ IsReducible cyc := by
  rw [isReducible_iff 3 cyc (fun _ => 1) isTournament_cyc
    (fun _ _ _ => le_rfl) (by decide)]
  rintro ⟨k, hk, hk1, hk3, hsum⟩
  obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
  · exact absurd hsum (by decide)
  · exact absurd hsum (by decide)

/-! ### The transitive tournament on `Fin 4` -/

/-- The transitive tournament on `Fin 4`: `i` beats `j` when `j < i`. -/
def tr : Fin 4 → Fin 4 → Bool := fun i j => decide (j < i)

theorem isTournament_tr : IsTournament tr := by
  unfold IsTournament tr
  decide

example : ∀ i, score tr i = i := by decide

/-- Player `0` loses every game, so `tr` is reducible. -/
example : IsReducible tr :=
  ⟨{0}, Finset.singleton_nonempty 0, by decide, by decide⟩

/-- Theorem 5 detects the reducibility of `tr` at `k = 1`. -/
example : IsReducible tr :=
  (isReducible_iff 4 tr (fun i => i) isTournament_tr
    (fun _ _ h => h) (by decide)).2 ⟨1, by norm_num, le_rfl, by norm_num,
      by decide⟩

/-- `tr` has no circular triad: `C(4, 3) - (0 + 0 + 1 + 3) = 0`. -/
example : ((Finset.univ.powersetCard 3).filter
    (IsCircularTriad tr)).card = 0 := by
  decide

example : ((Finset.univ.powersetCard 3).filter
    (IsCircularTriad tr)).card = 0 := by
  rw [card_circularTriads 4 tr isTournament_tr]
  decide

/-! ### Landau's theorem -/

/-- `(1, 1, 2, 2)` satisfies Landau's conditions, so it is a score
sequence. -/
example : ∃ T : Fin 4 → Fin 4 → Bool, IsTournament T ∧
    ∀ i, score T i = ![1, 1, 2, 2] i :=
  (landau_score_sequence 4 ![1, 1, 2, 2] (by decide)).2 ⟨by decide, by decide⟩

/-- `(0, 0, 3)` has total `C(3, 2) = 3` but is not a score sequence: the
first two players must win their game against each other. -/
example : ¬ ∃ T : Fin 3 → Fin 3 → Bool, IsTournament T ∧
    ∀ i, score T i = ![0, 0, 3] i := by
  rw [landau_score_sequence 3 ![0, 0, 3] (by decide)]
  rintro ⟨h, -⟩
  exact absurd (h 2 (by norm_num) (by norm_num)) (by decide)

/-- `(1, 1, 2)` has the wrong total. -/
example : ¬ ∃ T : Fin 3 → Fin 3 → Bool, IsTournament T ∧
    ∀ i, score T i = ![1, 1, 2] i := by
  rw [landau_score_sequence 3 ![1, 1, 2] (by decide)]
  rintro ⟨-, h⟩
  exact absurd h (by decide)

/-- The unsorted form applies directly to `(2, 0, 1)`. -/
example : ∃ T : Fin 3 → Fin 3 → Bool, IsTournament T ∧
    ∀ i, score T i = ![2, 0, 1] i :=
  (exists_isTournament_score_eq_iff ![2, 0, 1]).2 ⟨by decide, by decide⟩

/-! ### Theorem 1 -/

/-- At `a = 2`, `b = 0`: `(1 - x) * (x^2 + x^3 + ⋯) = x^2`. -/
example : (1 - PowerSeries.X) *
    PowerSeries.mk (fun n => if 2 ≤ n then (1 : ℚ) else 0) =
      PowerSeries.X ^ 2 := by
  simpa using egf_factorial_choose 2 0

/-- At `a = 1`, `b = 1` the coefficients are `n - 1 + 1 = n` for
`n ≥ 1`; for instance the coefficient of `x^4` is `4`. -/
example : PowerSeries.coeff 4 (PowerSeries.mk (fun n =>
    if 1 ≤ n then (Nat.choose (n - 1 + 1) 1 : ℚ) else 0)) = 4 := by
  norm_num

example : (1 - PowerSeries.X) ^ 2 * PowerSeries.mk (fun n =>
    if 1 ≤ n then (Nat.choose (n - 1 + 1) 1 : ℚ) else 0) =
      PowerSeries.X :=
  (egf_factorial_choose 1 1).trans (pow_one _)

/-! ### Helper lemmas -/

/-- The players `0` and `1` of `cyc` win `C(2, 2) = 1` game between
them. -/
example : ∑ i ∈ ({0, 1} : Finset (Fin 3)), #{j ∈ {0, 1} | cyc i j} = 1 :=
  sum_card_filter_eq_choose isTournament_cyc _

/-- Player `3` of `tr` wins all three games against `{0, 1, 2}`. -/
example : ∑ i ∈ ({3} : Finset (Fin 4)),
    #{j ∈ ({3} : Finset (Fin 4))ᶜ | tr i j} = 3 := by
  decide

/-- In `tr`, player `2` beats both others in `C(2, 2) = 1` of the
`3`-sets: `{0, 1, 2}`. -/
example : #{S ∈ Finset.univ.powersetCard 3 |
    (2 : Fin 4) ∈ S ∧ #{j ∈ S | tr 2 j} = 2} = 1 := by
  rw [card_filter_powersetCard_eq_choose isTournament_tr]
  decide

/-- The two smallest values of a monotone sequence sum to at most the
sum over any pair. -/
example : ∑ i : Fin 2, (fun i : Fin 4 => (i : ℕ) ^ 2) (Fin.castLE
    (by decide) i) ≤ ∑ i ∈ ({1, 3} : Finset (Fin 4)), (i : ℕ) ^ 2 :=
  sum_castLE_le_sum_of_monotone (s := fun i : Fin 4 => (i : ℕ) ^ 2)
    (fun _ _ h => Nat.pow_le_pow_left h 2) {1, 3} (by decide)

example : ((2 : Fin 3) : ℕ) ≤ (Fin.succ (2 : Fin 3) : ℕ) :=
  val_le_val_of_strictMono Fin.strictMono_succ 2

/-! ### Axioms -/

#print axioms egf_factorial_choose
#print axioms landau_score_sequence
#print axioms isReducible_iff
#print axioms card_circularTriads
#print axioms exists_isTournament_score_eq_iff
#print axioms exists_isTournament_of_forall_choose_two_le
#print axioms sum_card_filter_eq_choose
#print axioms sum_score_eq_choose_add
#print axioms choose_two_le_sum_score
#print axioms sum_score_eq_choose
#print axioms card_filter_card_filter_eq_two
#print axioms card_filter_powersetCard_eq_choose
#print axioms sum_castLE_le_sum_of_monotone
#print axioms val_le_val_of_strictMono

end MetaMathlibExtTest.TournamentScoreSequence
