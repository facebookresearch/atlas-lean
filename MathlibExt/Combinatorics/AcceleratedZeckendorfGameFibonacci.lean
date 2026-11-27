/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.AcceleratedZeckendorfGameAccelZeckGameLowerBound
import all MathlibExt.Combinatorics.AcceleratedZeckendorfGame

/-!
# Shortest Accelerated Zeckendorf Games on Fibonacci inputs

Combining consecutive Fibonacci denominations in batches attains the lower bound on the
number of moves when the input is itself a Fibonacci number.

## References

* Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
  Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024),
  no. 1, pp. 3–14, Lemma 2.3 (using Lemmas 2.1 and 2.2).
* Paul Baird-Smith, Alyssa Epstein, Kristen Flint, and Steven J. Miller,
  *The Zeckendorf Game*, in *Combinatorial and Additive Number Theory III*, Springer
  Proceedings in Mathematics & Statistics 297 (2020), pp. 25–38, §1, for the original game.
* Paul Baird-Smith, Alyssa Epstein, Kristen Flint, and Steven J. Miller,
  *The Generalized Zeckendorf Game*, The Fibonacci Quarterly 57 (2019), no. 5, pp. 1–14, §1.
* Édouard Zeckendorf, *Représentation des nombres naturels par une somme de nombres de
  Fibonacci ou de nombres de Lucas*, Bulletin de la Société Royale des Sciences de Liège 41
  (1972), pp. 179–182, for the original decomposition theorem.
-/

namespace MetaMathlibExt

private theorem no_move_from_single_token (k : ℕ) (t : ℕ →₀ ℕ) :
    ¬ AccelZeckMove (Finsupp.single k 1) t := by
  have hcount (i : ℕ) : Finsupp.single k (1 : ℕ) i ≤ 1 := by
    simp only [Finsupp.single_apply]
    split_ifs <;> omega
  have hpos (i : ℕ) (hi : 0 < Finsupp.single k (1 : ℕ) i) : k = i := by
    by_contra h
    simp [h] at hi
  rintro ⟨m, hm, ⟨i, hi, h₁, h₂, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨i, -, h, -⟩⟩
  · have := hpos (i - 1) (hm.trans_le h₁)
    have := hpos i (hm.trans_le h₂)
    omega
  · have := hcount 1
    omega
  · have := hcount 2
    omega
  · have := hcount i
    omega

-- After j positive steps the only possible nonzero counts are at indices j and j + 1.
private noncomputable def fibBatchState (k : ℕ) : ℕ → ℕ →₀ ℕ
  | 0 => Finsupp.single 1 (Nat.fib (k + 1))
  | j + 1 => Finsupp.single (j + 1) (Nat.fib (k - (j + 1) - 1)) +
      Finsupp.single (j + 2) (Nat.fib (k - (j + 1)))

private theorem fibBatchState_move (k j : ℕ) (hj : j < k - 1) :
    AccelZeckMove (fibBatchState k j) (fibBatchState k (j + 1)) := by
  cases j with
  | zero =>
    have h₁ := Nat.fib_add_two (n := k - 2)
    have h₂ := Nat.fib_add_two (n := k - 1)
    rw [show k - 2 + 2 = k by omega, show k - 2 + 1 = k - 1 by omega] at h₁
    rw [show k - 1 + 2 = k + 1 by omega, show k - 1 + 1 = k by omega] at h₂
    have hrest : Nat.fib (k + 1) - 2 * Nat.fib (k - 1) = Nat.fib (k - 1 - 1) := by
      rw [show k - 1 - 1 = k - 2 by omega]
      omega
    simpa [fibBatchState, hrest] using
      (accelZeckMove_between_openings (n := Nat.fib (k + 1)) (a := 0)
        (Nat.fib_pos.mpr (by omega : 0 < k - 1)) (by omega))
  | succ j =>
    let p := j + 2
    let i := k - (j + 1) - 1
    let s := fibBatchState k (j + 1)
    have hsub : p - 1 = j + 1 := by omega
    have hi : i + 1 = k - (j + 1) := by omega
    have hs : s = Finsupp.single (p - 1) (Nat.fib i) +
        Finsupp.single p (Nat.fib (i + 1)) := by
      simp [s, fibBatchState, hsub, p, i, hi]
    have ht : fibBatchState k (j + 1 + 1) =
        Finsupp.single p (Nat.fib (i - 1)) + Finsupp.single (p + 1) (Nat.fib i) := by
      simp [fibBatchState, p, i, show k - (j + 1 + 1) = i by omega]
    have h₁ : s (p - 1) = Nat.fib i := by rw [hs]; simp [hsub, p]
    have h₂ : s p = Nat.fib (i + 1) := by rw [hs]; simp [hsub, p]
    have h₃ : s (p + 1) = 0 := by rw [hs]; simp [hsub, p]
    obtain ⟨hm, ha, hb, hc⟩ :=
      accelZeckMove_fib_combine p i (by omega) (by omega) s h₁ h₂ h₃
    change AccelZeckMove s _
    rw [ht]
    convert hm using 1
    ext a
    rcases eq_or_ne a (p - 1) with rfl | hna
    · rw [ha]
      simp [Finsupp.single_eq_of_ne, show p - 1 ≠ p by omega,
        show p - 1 ≠ p + 1 by omega]
    rcases eq_or_ne a p with rfl | hnb
    · rw [hb]
      simp
    rcases eq_or_ne a (p + 1) with rfl | hnc
    · rw [hc]
      simp
    simp [hs, Finsupp.single_eq_of_ne, hnb, hnc]

@[expose] public section

/-- **Sharp lower bound for the Accelerated Zeckendorf Game on a Fibonacci number.** Index the
Fibonacci numbers as $F_1 = 1$, $F_2 = 2$, $F_{i+1} = F_i + F_{i-1}$, and let $k \ge 1$. Every
complete Accelerated Zeckendorf Game on $F_k$ (a sequence of moves from $F_k$ copies of $F_1$ to
a state from which no move is possible) has at least $k - 1$ moves, and some complete game on
$F_k$ has exactly $k - 1$ moves.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Lemma 2.3. -/
public theorem accelZeckGame_sharp_lower_bound_fib (k : ℕ) (hk : 1 ≤ k) :
    (∀ L g, IsAccelZeckGame (Nat.fib (k + 1)) L g → k - 1 ≤ L) ∧
      ∃ g, IsAccelZeckGame (Nat.fib (k + 1)) (k - 1) g := by
  constructor
  · intro L g hg
    have hf : Nat.greatestFib (Nat.fib (k + 1)) = k + 1 := Nat.greatestFib_fib (by omega)
    have h := accelZeckGame_lower_bound _ (Nat.fib_pos.mpr (by omega)) L g hg
    omega
  · refine ⟨fibBatchState k, rfl, fibBatchState_move k, ?_⟩
    have hlast : fibBatchState k (k - 1) = Finsupp.single k 1 := by
      rcases eq_or_lt_of_le hk with rfl | hk'
      · simp [fibBatchState]
      · have hk₀ : k - 1 - 1 + 1 = k - 1 := by omega
        conv_lhs => rw [← hk₀]
        rw [fibBatchState]
        rw [hk₀, show k - 1 - 1 + 2 = k by omega]
        simp [show k - (k - 1) = 1 by omega]
    rw [hlast]
    exact no_move_from_single_token k

end

end MetaMathlibExt
