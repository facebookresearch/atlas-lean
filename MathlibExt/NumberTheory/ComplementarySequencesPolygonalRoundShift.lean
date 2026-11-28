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
# Shifted rounding formula for non-polygonal numbers

For $k \ge 3$ and $n \ge 1$, the $n$-th positive integer outside the $k$-gonal numbers
$(k - 2)j(j - 1)/2 + j$ for $j \ge 1$ is $n$ plus the nearest integer to
$\sqrt{(2n - 2 + \lfloor (k+1)/4 \rfloor)/(k-2)}$, with ties rounded up.
The shift makes the rounded index identify the consecutive binomial thresholds that bracket $n$,
so neither correction in the interleaving formula is needed.

## References

* Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025), Article A95,
  pp. 1–26, Section 2.2.1, Theorem 5 (last sentence, p. 9). The proof uses the evenness of the
  doubled thresholds and applies Theorem 3 (p. 7) via `nthNonValue_eq_interleave` in
  `MathlibExt.NumberTheory.ComplementarySequences`.
-/

namespace MetaMathlibExt

/-- **Rounding formula for the non-$k$-gonal numbers, every $k \ge 3$.** Let $k \ge 3$; the
$k$-gonal numbers are $(k - 2) j (j - 1)/2 + j$ for $j \ge 1$. For every $n \ge 1$, the $n$-th
positive integer that is not a $k$-gonal number equals
$n + \lfloor \sqrt{(2n - 2 + \lfloor (k + 1)/4 \rfloor)/(k - 2)} + 1/2 \rfloor$.

This corresponds to the shift $r = \lfloor (k + 1)/4 \rfloor - 2$ in the source.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 5 (last sentence). -/
public theorem nthNonValue_polygonal_eq_round_shift (k : ℕ) (hk : 3 ≤ k) (n : ℕ)
    (hn : 1 ≤ n) :
    nthNonValue (fun j => (k - 2) * j * (j - 1) / 2 + j) n =
      n + ⌊Real.sqrt ((2 * n - 2 + ((k + 1) / 4 : ℕ)) / ((k : ℝ) - 2)) + 1 / 2⌋₊ := by
  let d := k - 2
  let q := (k + 1) / 4
  let x (m : ℕ) : ℝ := (2 * m - 2 + q) / d
  let h (m : ℕ) := ⌊Real.sqrt (x m) + 1 / 2⌋₊
  let α (j : ℕ) : ℝ := (d * j.choose 2 + 1 : ℕ)
  have hd : 1 ≤ d := by omega
  have hdPos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdCast : (d : ℝ) = (k : ℝ) - 2 := by
    simp only [d, Nat.cast_sub (show 2 ≤ k by omega), Nat.cast_ofNat]
  have hseq : (fun j : ℕ => (k - 2) * j * (j - 1) / 2 + j) = Nat.polygonalNumber k := by
    funext j
    rw [Nat.polygonalNumber_eq, Nat.choose_two_right, mul_assoc,
      Nat.mul_div_assoc _ (even_iff_two_dvd.mp (Nat.even_mul_pred_self j))]
  rw [hseq, ← hdCast]
  change nthNonValue (Nat.polygonalNumber k) n = n + h n
  -- The shift uses the ceiling of d / 4, computed by natural division.
  have hq : (d : ℝ) / 4 ≤ q ∧ (q : ℝ) < d / 4 + 1 := by
    have hlo : d ≤ 4 * q := by dsimp only [d, q]; omega
    have hhi : 4 * q < d + 4 := by dsimp only [d, q]; omega
    have hlo' : (d : ℝ) ≤ 4 * q := by exact_mod_cast hlo
    have hhi' : 4 * (q : ℝ) < d + 4 := by exact_mod_cast hhi
    exact ⟨by linarith only [hlo'], by linarith only [hhi']⟩
  have hcut (m : ℕ) (hm : 1 ≤ m) :
      1 ≤ h m ∧ d * (h m).choose 2 < m ∧ m ≤ d * (h m + 1).choose 2 := by
    let t := h m
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hx : (1 / 2 : ℝ) ^ 2 ≤ x m := by
      apply (le_div_iff₀ hdPos).2
      linarith only [hq.1, hm']
    have ht : 1 ≤ t := by
      change 1 ≤ ⌊Real.sqrt (x m) + 1 / 2⌋₊
      apply (Nat.le_floor_iff' (by decide)).2
      have hs := Real.le_sqrt_of_sq_le hx
      norm_num only [Nat.cast_one]
      linarith only [hs]
    have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hlo : (t : ℝ) ≤ Real.sqrt (x m) + 1 / 2 := Nat.floor_le (by positivity)
    have hhi : Real.sqrt (x m) + 1 / 2 < (t : ℝ) + 1 := Nat.lt_floor_add_one _
    have hsqLo := (Real.le_sqrt' (show (0 : ℝ) < t - 1 / 2 by linarith only [ht'])).1
      (show (t : ℝ) - 1 / 2 ≤ Real.sqrt (x m) by linarith only [hlo])
    have hsqHi := Real.lt_sq_of_sqrt_lt
      (show Real.sqrt (x m) < (t : ℝ) + 1 / 2 by linarith only [hhi])
    have hmulLo := (le_div_iff₀ hdPos).mp hsqLo
    have hmulHi := (div_lt_iff₀ hdPos).mp hsqHi
    change ((t : ℝ) - 1 / 2) ^ 2 * d ≤ 2 * m - 2 + q at hmulLo
    change 2 * (m : ℝ) - 2 + q < ((t : ℝ) + 1 / 2) ^ 2 * d at hmulHi
    have hleft : ((d * t.choose 2 : ℕ) : ℝ) < m := by
      rw [Nat.cast_mul, Nat.cast_choose_two ℝ]
      nlinarith only [hmulLo, hq.2]
    -- Both doubled thresholds are even; being below the next even integer suffices.
    have hright : 2 * m < 2 * (d * (t + 1).choose 2) + 2 := by
      exact_mod_cast (show (2 * m : ℝ) < 2 * (d * (t + 1).choose 2 : ℕ) + 2 by
        rw [Nat.cast_mul, Nat.cast_choose_two ℝ, Nat.cast_add, Nat.cast_one]
        nlinarith only [hmulHi, hq.1])
    change 1 ≤ t ∧ d * t.choose 2 < m ∧ m ≤ d * (t + 1).choose 2
    exact ⟨ht, by exact_mod_cast hleft, by omega⟩
  have hprev (j : ℕ) : Nat.polygonalNumber k j ≤ d * (j + 1).choose 2 := by
    rw [Nat.polygonalNumber_eq, Nat.choose_succ_succ' j 1, Nat.choose_one_right, Nat.mul_add]
    have hj : j ≤ d * j := by simpa using Nat.mul_le_mul_right j hd
    change d * j.choose 2 + j ≤ d * j + d * j.choose 2
    omega
  have hgap (j : ℕ) (_ : 1 ≤ j) :
      Nat.polygonalNumber k j + j ≤ Nat.polygonalNumber k (j + 1) := by
    have hj := hprev j
    rw [Nat.polygonalNumber_eq k (j + 1)]
    change Nat.polygonalNumber k j + j ≤ d * (j + 1).choose 2 + (j + 1)
    omega
  have hinterleave (j : ℕ) (hj : 2 ≤ j) :
      (Nat.polygonalNumber k (j - 1) : ℝ) ≤ α j ∧ α j ≤ Nat.polygonalNumber k j := by
    have hstep := hprev (j - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ j)] at hstep
    constructor
    · exact Nat.cast_le.mpr (hstep.trans (Nat.le_succ _))
    · apply Nat.cast_le.mpr
      rw [Nat.polygonalNumber_eq]
      change d * j.choose 2 + 1 ≤ d * j.choose 2 + j
      omega
  have hh (m : ℕ) (hm : 1 ≤ m) : 1 ≤ h m ∧ α (h m) ≤ m ∧ (m : ℝ) < α (h m + 1) := by
    obtain ⟨hp, hlo, hhi⟩ := hcut m hm
    exact ⟨hp, Nat.cast_le.mpr (Nat.succ_le_of_lt hlo), Nat.cast_lt.mpr (Nat.lt_succ_of_le hhi)⟩
  obtain ⟨_, hlo, hhi⟩ := hcut n hn
  have hleft : Nat.polygonalNumber k (h n) < n + h n := by
    rw [Nat.polygonalNumber_eq]
    exact Nat.add_lt_add_right hlo _
  have hright : n + h n < Nat.polygonalNumber k (h n + 1) := by
    rw [Nat.polygonalNumber_eq]
    exact Nat.lt_succ_of_le (Nat.add_le_add_right hhi _)
  rw [nthNonValue_eq_interleave (Nat.polygonalNumber k) (by simp) hgap α hinterleave h hh n hn,
    ite_eq_right hright.not_ge, ite_eq_right hleft.not_ge]

end MetaMathlibExt
