/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Order.Nat

/-!
# The Brauer–Shockley formula

The Frobenius number of a numerical semigroup is the maximum of its least representatives
of the nonzero residues modulo a generator of size at least two, minus that generator.
-/

namespace MetaMathlibExt

private theorem exists_least_modEq_of_setGcd_one {G : Set ℕ} (hg : Nat.setGcd G = 1)
    {a : ℕ} (ha : 0 < a) (r : ℕ) :
    ∃ m, IsLeast {s | s ∈ AddSubmonoid.closure G ∧ s ≡ r [MOD a]} m := by
  classical
  obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge G
  have hex : ∃ s, s ∈ AddSubmonoid.closure G ∧ s ≡ r [MOD a] := by
    refine ⟨r + N * a, hN _ ?_ (hg ▸ one_dvd _), by simp⟩
    exact (Nat.le_mul_of_pos_right N ha).trans (Nat.le_add_left ..)
  exact ⟨Nat.find hex, Nat.isLeast_find hex⟩

/-- **Brauer–Shockley formula for the Frobenius number.** Let $A_1, \dots, A_k$ be positive
integers with $\gcd(A_1, \dots, A_k) = 1$, let $S$ be the additive submonoid of $\mathbb{N}$ they
generate, and let $a = A_i$ be one of them with $a \ge 2$. For $1 \le x \le a - 1$ let $m_x$ be
the least element of $S$ congruent to $x$ modulo $a$. If $M$ is the largest of the numbers $m_x$,
then $M - a$ is the largest integer not in $S$, that is, the Frobenius number of $S$.

The case $a = 1$, where the maximum would be over an empty set, is excluded.

Source: Edgar Federico Elizeche and Amitabha Tripathi, *A Note on Deletions from Compound
Sequences That Leave the Frobenius Number Invariant*, INTEGERS 25 (2025), Article A6,
Lemma 1 (`integers-2025-A6-lem-1`), quoting Brauer and Shockley. -/
public theorem frobenius_eq_max_apery_sub {k : ℕ} (A : Fin k → ℕ) (hA : ∀ i, 0 < A i)
    (hgcd : Finset.univ.gcd A = 1) (i : Fin k) (ha : 2 ≤ A i) (M : ℕ)
    (hM : IsGreatest {m | ∃ x ∈ Finset.Icc 1 (A i - 1),
      IsLeast {s | s ∈ AddSubmonoid.closure (Set.range A) ∧ s ≡ x [MOD A i]} m} M) :
    IsGreatest {m : ℤ | ∀ s ∈ AddSubmonoid.closure (Set.range A), (s : ℤ) ≠ m}
      ((M : ℤ) - A i) := by
  let S := AddSubmonoid.closure (Set.range A)
  have haS : A i ∈ S := AddSubmonoid.subset_closure (Set.mem_range_self i)
  constructor
  · obtain ⟨x, _, hmin⟩ := hM.1
    intro s hs heq
    have hsum : s + A i = M := by omega
    have hmod : s ≡ x [MOD A i] := Nat.add_modulus_modEq_iff.mp (hsum ▸ hmin.1.2)
    have := hmin.2 ⟨hs, hmod⟩
    omega
  · intro z hz
    by_contra! hgt
    -- Compare the natural number z + a with the least representative of its residue.
    let n := (z + A i).toNat
    have hn : (n : ℤ) = z + A i := Int.toNat_of_nonneg (by omega)
    have hMn : M < n := by omega
    have hg : Nat.setGcd (Set.range A) = 1 := by
      apply Nat.dvd_one.mp
      rw [← hgcd]
      exact Finset.dvd_gcd fun j _ ↦ Nat.setGcd_dvd_of_mem (Set.mem_range_self j)
    let r := n % A i
    obtain ⟨b, hb⟩ := exists_least_modEq_of_setGcd_one hg (hA i) r
    have hbM : b ≤ M := by
      by_cases hr : r = 0
      · have hzero := hb.2 (show 0 ∈ {s | s ∈ S ∧ s ≡ r [MOD A i]} from
          ⟨S.zero_mem, hr ▸ Nat.ModEq.rfl⟩)
        omega
      · have hlt : r < A i := Nat.mod_lt _ (hA i)
        exact hM.2 ⟨r, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hb⟩
    have hmod := hb.1.2.trans (Nat.mod_modEq n (A i))
    -- The representatives b and n differ by at least one whole copy of a.
    have hstep := hmod.add_le_of_lt (hbM.trans_lt hMn)
    have hprev : b ≡ n - A i [MOD A i] := by
      rwa [Nat.modEq_sub_modulus_iff (by omega)]
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_exists_eq_add (by omega : b ≤ n - A i)).mp hprev
    have hmem : b + A i * t ∈ S := by
      simpa [nsmul_eq_mul, Nat.mul_comm] using S.add_mem hb.1.1 (S.nsmul_mem haS t)
    exact hz _ hmem (by omega)

end MetaMathlibExt
