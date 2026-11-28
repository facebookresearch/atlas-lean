/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PolygonalNumber
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs
import MathlibExt.NumberTheory.PracticalPolygonalSumsExistsSqAddSqModEqPrimePow
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Sums of two polygonal numbers modulo prime powers

For a natural number $s > 3$, there is a prime $p \equiv 1 \pmod{4}$ with
$p \nmid s - 2$ such that every positive integer is congruent modulo every
positive prime power $p^k$ to a sum of two positive $s$-gonal numbers. The main
result is `MetaMathlibExt.exists_prime_polygonal_add_polygonal_modEq_prime_pow`,
proved by completing the square and representing residues modulo prime powers as
sums of two squares (`MetaMathlibExt.exists_sq_add_sq_modEq_prime_pow`). -/

namespace MetaMathlibExt

/-- **Sums of two polygonal numbers modulo prime powers.** For a natural number $s > 3$ and a
natural number $x$, let $P_s(x) = (s-2)\binom{x}{2} + x$ be the $x$-th $s$-gonal number. There
is a prime $p$ with $p \equiv 1 \pmod{4}$ and $p \nmid s - 2$ such that for all natural numbers
$k > 0$ and $n > 0$ there are natural numbers $x, y > 0$ with
$P_s(x) + P_s(y) \equiv n \pmod{p^k}$.

The paper's statement asks only for an odd prime; the condition $p \equiv 1 \pmod{4}$ is the
choice made in its proof via Lemma 8 (arXiv Lemma 4.3).

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 9
(arXiv Lemma 4.4; `jis-2024-24.5.1-lem-9`). -/
public theorem exists_prime_polygonal_add_polygonal_modEq_prime_pow (s : ℕ)
    (hs : 3 < s) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ ¬ p ∣ s - 2 ∧ ∀ k n : ℕ, 0 < k → 0 < n →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧
        Nat.polygonalNumber s x + Nat.polygonalNumber s y ≡ n [MOD p ^ k] := by
  obtain ⟨p, hp, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one (s - 2) (by norm_num : (4 : ℕ) ≠ 0)
  have hp4 : p % 4 = 1 := hmod
  have hpdvd : ¬ p ∣ s - 2 := by
    intro h
    have hle := Nat.le_of_dvd (by omega : 0 < s - 2) h
    omega
  have hnot2 : ¬ p ∣ 2 := by
    intro h
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h
    have h2le := hp.two_le
    omega
  refine ⟨p, hp, hp4, hpdvd, ?_⟩
  intro k n hk hn
  set m := p ^ k with hm_def
  have hmpos : 0 < m := pow_pos hp.pos k
  have : NeZero m := ⟨hmpos.ne'⟩
  have hs2 : 0 < s - 2 := by omega
  obtain ⟨x0, y0, _, _, hxy0, _⟩ :=
    exists_sq_add_sq_modEq_prime_pow p (8 * (s - 2) * n + 2 * (s - 4) ^ 2) k hp hp4
      (by positivity) hk
  have hcop2 : Nat.Coprime 2 p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnot2).symm
  have hcopd : Nat.Coprime (s - 2) p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpdvd).symm
  have hcop : Nat.Coprime (2 * (s - 2)) m :=
    (Nat.Coprime.mul_left hcop2 hcopd).pow_right k
  have hA : IsUnit (((2 * (s - 2) : ℕ) : ZMod m)) := (ZMod.isUnit_iff_coprime _ _).mpr hcop
  have solve : ∀ z0 : ℕ, ∃ z : ℕ, 0 < z ∧
      (((2 * (s - 2) : ℕ) : ZMod m)) * (z : ZMod m) =
        (z0 : ZMod m) + ((s - 4 : ℕ) : ZMod m) := by
    intro z0
    let u : ZMod m := (((2 * (s - 2) : ℕ) : ZMod m))⁻¹ *
      ((z0 : ZMod m) + ((s - 4 : ℕ) : ZMod m))
    have hu : (((2 * (s - 2) : ℕ) : ZMod m)) * u =
        (z0 : ZMod m) + ((s - 4 : ℕ) : ZMod m) := by
      change (((2 * (s - 2) : ℕ) : ZMod m)) * ((((2 * (s - 2) : ℕ) : ZMod m))⁻¹ *
        ((z0 : ZMod m) + ((s - 4 : ℕ) : ZMod m))) = _
      rw [← mul_assoc, (((2 * (s - 2) : ℕ) : ZMod m)).mul_inv_of_unit hA, one_mul]
    let z : ℕ := if u.val = 0 then m else u.val
    have hzcast : (z : ZMod m) = u := by
      by_cases hv : u.val = 0
      · have hu0 : u = 0 := by rw [← ZMod.val_eq_zero]; exact hv
        simp [z, hu0]
      · simp [z, hv]
    have hzpos : 0 < z := by
      by_cases hv : u.val = 0
      · simp [z, hv, hmpos]
      · have hpos : 0 < u.val := Nat.pos_of_ne_zero hv
        simp [z, hv, hpos]
    exact ⟨z, hzpos, by rw [hzcast]; exact hu⟩
  obtain ⟨x, hxpos, hxeq⟩ := solve x0
  obtain ⟨y, hypos, hyeq⟩ := solve y0
  have hid : ∀ z : ℕ, (8 : ZMod m) * ((s - 2 : ℕ) : ZMod m) *
        (Nat.polygonalNumber s z : ZMod m) =
        (2 * ((s - 2 : ℕ) : ZMod m) * (z : ZMod m) - ((s - 4 : ℕ) : ZMod m)) ^ 2 -
          ((s - 4 : ℕ) : ZMod m) ^ 2 := by
    intro z
    have h2c : (2 : ZMod m) * ((Nat.choose z 2 : ℕ) : ZMod m) =
        (z : ZMod m) ^ 2 - (z : ZMod m) := by
      have h' : ((2 * Nat.choose z 2 + z : ℕ) : ZMod m) = ((z ^ 2 : ℕ) : ZMod m) :=
        congrArg (Nat.cast : ℕ → ZMod m) (Nat.polygonalNumber_four z)
      push_cast at h'
      linear_combination h'
    have hP : (Nat.polygonalNumber s z : ZMod m) =
        ((s - 2 : ℕ) : ZMod m) * ((Nat.choose z 2 : ℕ) : ZMod m) + (z : ZMod m) := by
      have hdef : Nat.polygonalNumber s z = (s - 2) * Nat.choose z 2 + z := rfl
      rw [hdef]
      push_cast
      rfl
    have hE : ((s - 4 : ℕ) : ZMod m) = ((s - 2 : ℕ) : ZMod m) - 2 := by
      have h : s - 4 = (s - 2) - 2 := by omega
      rw [h, Nat.cast_sub (by omega : 2 ≤ s - 2)]
      push_cast
      ring
    rw [hP, hE]
    linear_combination (4 * (((s - 2 : ℕ) : ZMod m)) ^ 2) * h2c
  have hx0 : 2 * ((s - 2 : ℕ) : ZMod m) * (x : ZMod m) - ((s - 4 : ℕ) : ZMod m) =
      (x0 : ZMod m) := by
    have h := hxeq
    push_cast at h
    linear_combination h
  have hy0 : 2 * ((s - 2 : ℕ) : ZMod m) * (y : ZMod m) - ((s - 4 : ℕ) : ZMod m) =
      (y0 : ZMod m) := by
    have h := hyeq
    push_cast at h
    linear_combination h
  have hN : (x0 : ZMod m) ^ 2 + (y0 : ZMod m) ^ 2 =
      8 * ((s - 2 : ℕ) : ZMod m) * (n : ZMod m) + 2 * ((s - 4 : ℕ) : ZMod m) ^ 2 := by
    rw [← ZMod.natCast_eq_natCast_iff] at hxy0
    push_cast at hxy0
    exact hxy0
  have hnot8 : ¬ p ∣ 8 := by
    intro h
    have hle := Nat.le_of_dvd (by norm_num : 0 < 8) h
    have h2le := hp.two_le
    have h5 : p = 5 := by omega
    subst h5
    norm_num at h
  have hcop8 : Nat.Coprime 8 p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnot8).symm
  have hD : IsUnit (((s - 2 : ℕ) : ZMod m)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (hcopd.pow_right k)
  have h8 : IsUnit (8 : ZMod m) := by
    rw [← Nat.cast_ofNat (R := ZMod m)]
    exact (ZMod.isUnit_iff_coprime _ _).mpr (hcop8.pow_right k)
  have hC : IsUnit ((8 : ZMod m) * ((s - 2 : ℕ) : ZMod m)) := h8.mul hD
  have hsum : (8 : ZMod m) * ((s - 2 : ℕ) : ZMod m) *
        ((Nat.polygonalNumber s x : ZMod m) + (Nat.polygonalNumber s y : ZMod m)) =
      (8 : ZMod m) * ((s - 2 : ℕ) : ZMod m) * (n : ZMod m) := by
    rw [mul_add, hid x, hid y, hx0, hy0]
    linear_combination hN
  have hcast : (Nat.polygonalNumber s x : ZMod m) + (Nat.polygonalNumber s y : ZMod m) =
      (n : ZMod m) := hC.mul_left_cancel hsum
  refine ⟨x, y, hxpos, hypos, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact hcast

end MetaMathlibExt
