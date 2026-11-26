/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ReducedResidueLongestAP

/-!
# Longest progressions of absolute least residues for primes congruent to one modulo four

The theorem `MetaMathlibExt.absLeastAPLength_prime_of_mod_four_eq_one` gives the length
`(p - 1) / 2` for a prime `p` congruent to one modulo four.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem centered_length {p k : ℕ} (hp : p.Prime) (hpk : p = 4 * k + 1)
    (hk : 0 < k) : longestAPLength (-(2 * (k : ℤ) + 1)) p = 2 * k := by
  unfold longestAPLength
  apply le_antisymm
  · apply csSup_le'
    rintro s ⟨b, d, hd, h⟩
    by_contra! hs
    have hfirst := (Finset.mem_Icc.mp (Finset.mem_filter.mp (h 0 (by omega))).1).1
    have hlast := (Finset.mem_Icc.mp (Finset.mem_filter.mp (h (2 * k) hs)).1).2
    push_cast at hfirst hlast
    have hd2 : d ≤ 2 := by
      by_contra! hd3
      have hmul := mul_le_mul_of_nonneg_left (show (3 : ℤ) ≤ d by omega)
        (show (0 : ℤ) ≤ 2 * k by positivity)
      omega
    have hd_cases : d = 1 ∨ d = 2 := by omega
    rcases hd_cases with rfl | rfl
    · have hb : b ≤ 0 := by omega
      have hi : (-b).toNat < s := by omega
      have hzero := (Finset.mem_filter.mp (h (-b).toNat hi)).2
      apply hp.ne_one
      simpa [Int.toNat_of_nonneg (neg_nonneg.mpr hb)] using hzero
    · have hz : b + (k : ℤ) * 2 = 0 := by omega
      have hzero := (Finset.mem_filter.mp (h k (by omega))).2
      apply hp.ne_one
      simpa [hz] using hzero
  · refine le_csSup ⟨p, fun _ ⟨_, _, hd, h⟩ => apLength_le hd h⟩
      ⟨-(2 * (k : ℤ)), 1, one_pos, ?_⟩
    intro i hi
    simp only [Nat.cast_one, mul_one]
    let a := -(2 * (k : ℤ)) + i
    change a ∈ reducedResidueWindow (-(2 * (k : ℤ) + 1)) p
    have ha : -(p : ℤ) < a ∧ a < 0 := by dsimp [a]; omega
    have hlt : (a.natAbs : ℤ) < p := by
      rw [Int.natCast_natAbs, abs_lt]
      constructor <;> omega
    have hne : a.natAbs ≠ 0 := by
      intro hz
      have : a = 0 := Int.natAbs_eq_zero.mp hz
      omega
    have hcop := Nat.coprime_of_lt_prime hne (by exact_mod_cast hlt) hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ?_, ?_⟩
    · dsimp [a]
      omega
    · change a.natAbs.Coprime p
      exact hcop.symm

/-- **Longest progressions of absolute least residues: primes congruent to 1 mod 4.** For a
prime $p \equiv 1 \pmod 4$, the length $g(p)$ of the longest arithmetic progression in the
absolute least reduced residue system modulo $p$ is $(p - 1)/2$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem absLeastAPLength_prime_of_mod_four_eq_one {p : ℕ} (hp : p.Prime)
    (h4 : p % 4 = 1) : absLeastAPLength p = (p - 1) / 2 := by
  let k := p / 4
  have hpk : p = 4 * k + 1 := by dsimp [k]; omega
  have hk : 0 < k := by have := hp.two_le; omega
  have hc : ⌈(p : ℚ) / 2⌉ = 2 * (k : ℤ) + 1 := by
    rw [Int.ceil_eq_iff]
    have hpk' : (p : ℚ) = 4 * (k : ℚ) + 1 := by exact_mod_cast hpk
    push_cast
    constructor <;> linarith
  unfold absLeastAPLength
  rw [hc, centered_length hp hpk hk]
  omega

end

end MetaMathlibExt
