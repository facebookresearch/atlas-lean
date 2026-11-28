/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.ComplementarySequences
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import MathlibExt.NumberTheory.PolygonalNumber

/-!
# Rounding formula for non-polygonal numbers

For $3 \le k \le 10$ and $n \ge 1$, rounding $\sqrt{2n/(k-2)}$ to the nearest integer
(with ties rounded up) gives the offset from $n$ to the $n$-th positive integer not of the form
$(k - 2)j(j - 1)/2 + j$ for $j \ge 1$.

## References

* Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025), Article A95,
  Section 2.2.1, Theorem 4 (last sentence, p. 8). The proof uses Wu's parity argument for the
  rounding bound and applies the interleaving formula of Theorem 3 (p. 7), available as
  `nthNonValue_eq_interleave` in `MathlibExt.NumberTheory.ComplementarySequences`.
-/

namespace MetaMathlibExt

private theorem polygonal_round_bounds (a : ℕ) (ha : 0 < a) (ha' : a ≤ 8) (n : ℕ) (hn : 1 ≤ n) :
    let s := ⌊Real.sqrt (2 * n / (a : ℝ)) + 1 / 2⌋₊
    1 ≤ s ∧ a * s.choose 2 < n ∧ n ≤ a * (s + 1).choose 2 := by
  let x : ℝ := 2 * n / a
  let s := ⌊Real.sqrt x + 1 / 2⌋₊
  change 1 ≤ s ∧ a * s.choose 2 < n ∧ n ≤ a * (s + 1).choose 2
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have haR' : (a : ℝ) ≤ 8 := by exact_mod_cast ha'
  have hfloorHi : Real.sqrt x + 1 / 2 < (s : ℝ) + 1 := Nat.lt_floor_add_one _
  have hhi : x < ((s : ℝ) + 1 / 2) ^ 2 :=
    (Real.sqrt_lt' (by positivity)).mp (by linarith only [hfloorHi])
  have hmulHi : (2 * n : ℝ) < ((s : ℝ) + 1 / 2) ^ 2 * a := (div_lt_iff₀ haR).mp hhi
  -- Both doubled quantities are even, so the strict error bound of two gives an exact cutoff.
  have hu : 2 * n < 2 * (a * (s + 1).choose 2) + 2 := by
    exact_mod_cast (show (2 * n : ℝ) < 2 * (a * (s + 1).choose 2 : ℕ) + 2 by
      push_cast only [Nat.cast_mul]
      rw [Nat.cast_choose_two ℝ, Nat.cast_add, Nat.cast_one]
      nlinarith only [hmulHi, haR'])
  have hupper : n ≤ a * (s + 1).choose 2 := by omega
  have hs : 1 ≤ s := by
    by_contra! h
    have he : s = 0 := by omega
    have hc : (s + 1).choose 2 = 0 := by rw [he]; decide
    rw [hc, mul_zero] at hupper
    omega
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hx : 0 ≤ x := by positivity
  have hfloorLo : (s : ℝ) ≤ Real.sqrt x + 1 / 2 := Nat.floor_le (by positivity)
  have hlo : ((s : ℝ) - 1 / 2) ^ 2 ≤ x :=
    (Real.le_sqrt (by linarith only [hsR]) hx).mp (by linarith only [hfloorLo])
  have hmulLo : ((s : ℝ) - 1 / 2) ^ 2 * a ≤ 2 * n := (le_div_iff₀ haR).mp hlo
  have hl : 2 * (a * s.choose 2) < 2 * n := by
    exact_mod_cast (show (2 : ℝ) * (a * s.choose 2 : ℕ) < 2 * n by
      push_cast only [Nat.cast_mul]
      rw [Nat.cast_choose_two ℝ]
      nlinarith only [hmulLo, haR])
  exact ⟨hs, by omega, hupper⟩

/-- **Rounding formula for the non-$k$-gonal numbers, $3 \le k \le 10$.** Let $3 \le k \le 10$;
the $k$-gonal numbers are $(k - 2) j (j - 1)/2 + j$ for $j \ge 1$. For every $n \ge 1$, the $n$-th
positive integer that is not a $k$-gonal number equals
$n + \lfloor \sqrt{2n/(k - 2)} + 1/2 \rfloor$.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 4 (last sentence). -/
public theorem nthNonValue_polygonal_eq_round (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 10)
    (n : ℕ) (hn : 1 ≤ n) :
    nthNonValue (fun j => (k - 2) * j * (j - 1) / 2 + j) n =
      n + ⌊Real.sqrt (2 * n / ((k : ℝ) - 2)) + 1 / 2⌋₊ := by
  let a := k - 2
  let f := Nat.polygonalNumber k
  have hf (j : ℕ) : f j = a * j.choose 2 + j := Nat.polygonalNumber_eq k j
  have heq : (fun j : ℕ => (k - 2) * j * (j - 1) / 2 + j) = f := by
    funext j
    have hdiv : 2 ∣ j * (j - 1) := even_iff_two_dvd.mp (Nat.even_mul_pred_self j)
    change a * j * (j - 1) / 2 + j = f j
    rw [hf, Nat.choose_two_right, mul_assoc a, Nat.mul_div_assoc _ hdiv]
  let h (m : ℕ) := ⌊Real.sqrt (2 * m / (a : ℝ)) + 1 / 2⌋₊
  have ha : 0 < a := by omega
  have ha' : a ≤ 8 := by omega
  have haCast : (a : ℝ) = (k : ℝ) - 2 := by
    dsimp only [a]
    rw [Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_ofNat]
  rw [heq, ← haCast]
  change nthNonValue f n = n + h n
  have hchoose (j : ℕ) : (j + 1).choose 2 = j.choose 2 + j := by
    simpa [Nat.choose_one_right, add_comm] using Nat.choose_succ_succ j 1
  have hmul (j : ℕ) : j ≤ a * j := by
    simpa using Nat.mul_le_mul_right j (show 1 ≤ a by omega)
  have hgap (j : ℕ) (_ : 1 ≤ j) : f j + j ≤ f (j + 1) := by
    rw [hf j, hf (j + 1), hchoose, Nat.mul_add]
    have := hmul j
    omega
  -- One more than the number of non-values up to f(j) interleaves the polygonal values.
  let α (j : ℕ) : ℝ := (a * j.choose 2 + 1 : ℕ)
  have hα (j : ℕ) (hj : 2 ≤ j) : (f (j - 1) : ℝ) ≤ α j ∧ α j ≤ f j := by
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = m + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel, α, Nat.cast_le]
    rw [hf m, hf (m + 1), hchoose, Nat.mul_add]
    have := hmul m
    omega
  have hh (m : ℕ) (hm : 1 ≤ m) : 1 ≤ h m ∧ α (h m) ≤ m ∧ (m : ℝ) < α (h m + 1) := by
    obtain ⟨hs, hleft, hright⟩ := polygonal_round_bounds a ha ha' m hm
    refine ⟨hs, ?_, ?_⟩
    · exact Nat.cast_le.mpr (Nat.succ_le_of_lt hleft)
    · exact Nat.cast_lt.mpr (Nat.lt_succ_of_le hright)
  obtain ⟨_, hlo, hhi⟩ := polygonal_round_bounds a ha ha' n hn
  change a * (h n).choose 2 < n at hlo
  change n ≤ a * (h n + 1).choose 2 at hhi
  have hleft : f (h n) < n + h n := by rw [hf]; omega
  have hright : n + h n < f (h n + 1) := by rw [hf]; omega
  rw [nthNonValue_eq_interleave f (by simp [f]) hgap α hα h hh n hn]
  simp only [hright.not_ge, hleft.not_ge, ↓reduceIte]

end MetaMathlibExt
