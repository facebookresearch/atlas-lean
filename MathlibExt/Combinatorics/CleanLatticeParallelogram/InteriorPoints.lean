/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.CleanLatticeParallelogram
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Ring
import all MathlibExt.Combinatorics.CleanLatticeParallelogram

/-!
# Interior lattice points of standard clean parallelograms

## References

* Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao,
  *A Geometric Relationship between Continued Fractions and Clean Lattice Parallelograms*,
  INTEGERS 26 (2026), Article A10, pp. 1–23, Lemma 3.
* Bruce Reznick, *Clean Lattice Tetrahedra*, arXiv:math/0606227 (2006), pp. 1–21,
  Section 1, credited by Khan et al. for the term “clean”.
-/

namespace MetaMathlibExt

/-- **Interior lattice points of a standard clean parallelogram.** Let $1 \le a < n$ with
$\gcd(a, n) = 1$, let $P_{a,n} = \{s (1, 0) + t (a, n) : 0 \le s \le 1,\ 0 \le t \le 1\}$, and
write $\langle x \rangle = x - \lfloor x \rfloor$ for the fractional part of a real number $x$.
The lattice points in the interior of $P_{a,n}$ are exactly the points
$\langle k(n - a)/n \rangle \, (1, 0) + (k/n) \, (a, n)$ for $k = 1, \dots, n - 1$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 3 (`integers-2026-A10-lem-3`). -/
public theorem interior_stdCleanParallelogram_latticePoints {a n : ℕ} (ha : 1 ≤ a)
    (han : a < n) (hcop : Nat.Coprime a n) :
    interior (stdCleanParallelogram a n) ∩ latticePoints =
      (fun k : ℕ => (Int.fract ((k : ℝ) * (n - a) / n) + (k : ℝ) * a / n, (k : ℝ))) ''
        Set.Icc 1 (n - 1) := by
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let q (k : ℕ) : ℝ := (k : ℝ) * a / n
  have abscissa (k : ℕ) :
      Int.fract ((k : ℝ) * (n - a) / n) + q k = (⌈q k⌉ : ℤ) := by
    have hshift : (k : ℝ) * (n - a) / n = (k : ℝ) + -(q k) := by
      dsimp only [q]
      rw [mul_sub, sub_div, mul_div_cancel_right₀ _ hnR.ne', sub_eq_add_neg]
    rw [hshift, Int.fract_natCast_add, Int.fract, Int.floor_neg, Int.cast_neg]
    ring
  have row (k : ℕ) (hk : 0 < k) (hkn : k < n) (x : ℤ) :
      ((x : ℝ), (k : ℝ)) ∈ interior (stdCleanParallelogram a n) ↔ x = ⌈q k⌉ := by
    -- The coprime rounding lemma for vertical columns applies with the sides interchanged.
    have hq : (↑(stdColumn_least_greatest.edge n a k) : ℝ) = q k := by
      simp [q, stdColumn_least_greatest.edge]
    have hceil : ⌈q k⌉ = ⌊q k⌋ + 1 := by
      rw [← hq, Rat.ceil_cast, Rat.floor_cast]
      exact stdColumn_least_greatest.ceil_eq_floor_add_one hcop.symm hk hkn
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hknR : (k : ℝ) < n := by exact_mod_cast hkn
    rw [stdColumn_least_greatest.mem_interior_iff hn, ← lt_div_iff₀ hnR, ← div_lt_iff₀ hnR]
    change ((x : ℝ) - 1 < q k ∧ q k < (x : ℝ) ∧ 0 < (k : ℝ) ∧ (k : ℝ) < n) ↔ _
    have hxsub : (x : ℝ) - 1 = ((x - 1 : ℤ) : ℝ) := by simp
    simp only [hkR, hknR, and_true, hxsub, ← Int.lt_ceil, ← Int.floor_lt]
    omega
  ext p
  constructor
  · rintro ⟨hp, ⟨⟨x, y⟩, rfl⟩⟩
    have hy := (stdColumn_least_greatest.mem_interior_iff hn (x : ℝ) (y : ℝ)).mp hp
    have hy₀ : 0 < y := by exact_mod_cast hy.2.2.1
    have hy₁ : y < (n : ℤ) := by exact_mod_cast hy.2.2.2
    let k := y.toNat
    have hk : 0 < k := by omega
    have hkn : k < n := by omega
    have hyR : (k : ℝ) = (y : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hy₀.le)
    have hx := (row k hk hkn x).mp (by simpa only [hyR] using hp)
    refine ⟨k, ⟨by omega, by omega⟩, Prod.ext ?_ hyR⟩
    exact (abscissa k).trans (congrArg (fun z : ℤ => (z : ℝ)) hx.symm)
  · rintro ⟨k, ⟨hk, hkn⟩, rfl⟩
    change (Int.fract ((k : ℝ) * (n - a) / n) + q k, (k : ℝ)) ∈
      interior (stdCleanParallelogram a n) ∩ latticePoints
    rw [abscissa]
    refine ⟨(row k (by omega) (by omega) _).mpr rfl, ⟨(⌈q k⌉, (k : ℤ)), ?_⟩⟩
    exact Prod.ext rfl (Int.cast_natCast k)

end MetaMathlibExt
