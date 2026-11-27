/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import MathlibExt.Combinatorics.DisjunctiveRado
import Mathlib.Data.ZMod.Basic

/-!
# The parity obstruction for singleton Rado numbers

Color each natural number by its parity. In a monochromatic solution, the left-hand side
reduces modulo two to the common residue times the sum of the coefficients.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.DisjunctiveRadoWanted

-- Retain the source's hypothesis `m ≤ a`, although the parity obstruction does not need it.
set_option linter.unusedVariables false in
/-- **Theorem 1** (quoted from the authors' earlier paper): for `4 ≤ m ≤ a` with
`a + m` and `c` odd, the Rado number of
`∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c` does not exist: no `R` has the
monochromatic-solution property.

Source: Srashti Dwivedi and Amitabha Tripathi, "On the Two-Color Disjunctive
Rado Number for the Equations `∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j`,
`j = 1, 2`", INTEGERS 25 (2025), Article A108, Theorem 1 (from [5, Theorem 1]). -/
theorem not_radoGood_of_odd (a m : ℕ) (c : ℤ) (hm : 4 ≤ m) (hma : m ≤ a)
    (ham : Odd (a + m)) (hc : Odd c) (R : ℕ) : ¬ radoGood m a {c} R := by
  intro H
  obtain ⟨d, hd, x, y, z, _, _, _, hx, hz, he⟩ := H (fun n => decide (n % 2 = 0))
  have hdc : d = c := Finset.mem_singleton.mp hd
  rw [hdc] at he
  have same_residue (n : ℕ) (h : decide (n % 2 = 0) = decide (y % 2 = 0)) :
      (n : ZMod 2) = (y : ZMod 2) := by
    have hmod : n % 2 = y % 2 := by
      by_cases hn : n % 2 = 0
      · have hy : y % 2 = 0 := by simpa [hn] using h
        omega
      · have hy : y % 2 ≠ 0 := by simpa [hn] using h
        omega
    rw [← ZMod.natCast_mod n 2, ← ZMod.natCast_mod y 2, hmod]
  have he' : ∑ i, (x i : ZMod 2) + (a : ZMod 2) * y - z = (c : ZMod 2) := by
    simpa only [map_add, map_sub, map_mul, map_sum, Int.coe_castRingHom, Int.cast_natCast]
      using congrArg (Int.castRingHom (ZMod 2)) he
  have hsum : ∑ i, (x i : ZMod 2) = ((m - 2 : ℕ) : ZMod 2) * y := by
    calc
      ∑ i, (x i : ZMod 2) = ∑ _ : Fin (m - 2), (y : ZMod 2) :=
        Finset.sum_congr rfl (fun i _ => same_residue (x i) (hx i))
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  obtain ⟨k, hk⟩ := ham
  have hcount : (m - 2 : ℕ) + a = 2 * (k - 1) + 1 := by omega
  have hcoeff : ((m - 2 : ℕ) : ZMod 2) + a - 1 = 0 := by
    have h := congrArg (fun n : ℕ => (n : ZMod 2)) hcount
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, htwo, zero_mul,
      zero_add] at h
    rw [h, sub_self]
  obtain ⟨k, hk⟩ := hc
  have hc' : (c : ZMod 2) = 1 := by
    rw [hk, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one, htwo, zero_mul, zero_add]
  have hzero : (c : ZMod 2) = 0 := by
    calc
      (c : ZMod 2) = ((m - 2 : ℕ) : ZMod 2) * y + a * y - y := by
        rw [← he', hsum, same_residue z hz]
      _ = (((m - 2 : ℕ) : ZMod 2) + a - 1) * y := by rw [sub_mul, add_mul, one_mul]
      _ = 0 := by rw [hcoeff, zero_mul]
  exact one_ne_zero (hc'.symm.trans hzero)

end MathlibExt.Combinatorics.DisjunctiveRadoWanted
