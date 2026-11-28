/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.ModEq

/-!
# Available integers for two distinct primes

The definitions and the statement come from Florian Pausinger, *Counting Appearances of Integers
in Sets of Arithmetic Progressions*, INTEGERS 26 (2026), Article A50 (preprint arXiv:2512.16358).

For moduli `p : Fin k → ℕ` and residues `r : Fin k → ℕ`, the residue hit count
`residueHitCount p r n` is the number of indices `i` with `n ≡ r i [MOD p i]`, and
`availableCount p r` is the number of integers `n` with `1 ≤ n ≤ ∏ i, p i` that are hit at most
once. `onesDiagDet p` is the determinant of the `k × k` integer matrix with `p` on the diagonal
and `1` in every other entry.

For two distinct primes `p` and `q`, the Chinese remainder theorem gives exactly one integer in
`[1, p q]` that lies in both chosen residue classes, so `p q - 1` integers are available. This is
the determinant `p q - 1` of the `2 × 2` matrix with diagonal `p, q` and both other entries `1`.
The proof follows the argument the preprint (version 1) gives for its Lemma 4, the two-prime
case. The primes must be distinct: when `p = q` the two classes are disjoint or equal, and the
count is `p ^ 2` or `p ^ 2 - p` instead of `p ^ 2 - 1`.

## Main statements

* `availableCount_two_primes`: for distinct primes `p` and `q` and any residues, the number of
  available integers in `[1, p q]` is `onesDiagDet ![p, q]`.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

/-- **Ones-diagonal determinant.** For natural numbers $p_1, \dots, p_k$, the determinant
$A_k(p_1, \dots, p_k)$ is the determinant of the $k \times k$ integer matrix with
$p_1, \dots, p_k$ on the diagonal and $1$ in every other entry. -/
def onesDiagDet {k : ℕ} (p : Fin k → ℕ) : ℤ :=
  Matrix.det (fun i j => if i = j then (p i : ℤ) else 1)

/-- **Residue hit count.** For natural numbers $p_1, \dots, p_k$, $r_1, \dots, r_k$ and $n$, the
residue hit count $\gamma(n)$ is the number of indices $i$ with $n \equiv r_i \pmod{p_i}$, that
is, the number of the residue classes $r_i \bmod p_i$ that contain $n$. -/
def residueHitCount {k : ℕ} (p r : Fin k → ℕ) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => n % p i = r i % p i)).card

/-- **Number of available integers.** For natural numbers $p_1, \dots, p_k$ and $r_1, \dots, r_k$,
let $\gamma(n)$ be the number of indices $i$ with $n \equiv r_i \pmod{p_i}$, and call $n$ available
if $\gamma(n) \le 1$. This is the number of available integers $n$ with
$1 \le n \le p_1 p_2 \cdots p_k$. For the first $k$ primes it is the count written
$\mathrm{av}(k)$. -/
def availableCount {k : ℕ} (p r : Fin k → ℕ) : ℕ :=
  ((Finset.Icc 1 (∏ i, p i)).filter
    (fun n => residueHitCount p r n ≤ 1)).card

-- Chinese remainder theorem, counted on `[1, m n]`: for coprime positive moduli, exactly one
-- integer in this interval lies in both residue classes.
private theorem card_filter_Icc_mod_eq_and_mod_eq {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) (a b : ℕ) :
    ((Finset.Icc 1 (m * n)).filter
      (fun x => x % m = a % m ∧ x % n = b % n)).card = 1 := by
  set c : ℕ := (Nat.chineseRemainder hmn a b : ℕ)
  have hc : c ≡ a [MOD m] ∧ c ≡ b [MOD n] := (Nat.chineseRemainder hmn a b).2
  have hcN : c < m * n := Nat.chineseRemainder_lt_mul hmn a b hm hn
  have hN : 0 < m * n := Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)
  have key : ∀ x, (x % m = a % m ∧ x % n = b % n) ↔ x ≡ c [MOD m * n] := fun x =>
    ⟨fun h => Nat.chineseRemainder_modEq_unique hmn h.1 h.2,
      fun h => ⟨(h.of_mul_right n).trans hc.1, (h.of_mul_left m).trans hc.2⟩⟩
  -- The representative of `c` in `[1, m n]`.
  have hw : (if c = 0 then m * n else c) ≡ c [MOD m * n] := by
    split_ifs with h0
    · rw [h0]
      exact Nat.modEq_zero_iff_dvd.mpr dvd_rfl
    · rfl
  rw [Finset.card_eq_one]
  refine ⟨if c = 0 then m * n else c, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, key]
  constructor
  · rintro ⟨⟨hx1, hxN⟩, hx⟩
    refine (hx.trans hw.symm).eq_of_abs_lt ?_
    split_ifs with h0 <;> rw [abs_lt] <;> constructor <;> push_cast <;> omega
  · rintro rfl
    refine ⟨?_, hw⟩
    split_ifs with h0
    · exact ⟨hN, le_rfl⟩
    · exact ⟨Nat.pos_of_ne_zero h0, hcN.le⟩

/-- **Available integers for two distinct primes.** Let $p \ne q$ be primes and let $r_1, r_2$ be
any natural numbers. Call an integer $n$ available if it satisfies at most one of the congruences
$n \equiv r_1 \pmod p$ and $n \equiv r_2 \pmod q$. Then the number of available integers $n$ with
$1 \le n \le pq$ equals $A_2(p, q)$, the determinant of the $2 \times 2$ matrix with diagonal
entries $p, q$ and both other entries $1$.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 5. -/
theorem availableCount_two_primes (p q : ℕ) (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (r : Fin 2 → ℕ) :
    (availableCount ![p, q] r : ℤ) = onesDiagDet ![p, q] := by
  -- An integer is not available exactly when it lies in both residue classes.
  have hhit : ∀ n, residueHitCount ![p, q] r n ≤ 1 ↔
      ¬ (n % p = r 0 % p ∧ n % q = r 1 % q) := by
    intro n
    simp only [residueHitCount, Finset.card_filter, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    by_cases h0 : n % p = r 0 % p <;> by_cases h1 : n % q = r 1 % q <;> simp [h0, h1]
  have hcount : availableCount ![p, q] r + 1 = p * q := by
    have hprod : ∏ i, ![p, q] i = p * q := by simp [Fin.prod_univ_two]
    have hone := card_filter_Icc_mod_eq_and_mod_eq hp.ne_zero hq.ne_zero
      ((Nat.coprime_primes hp hq).2 hpq) (r 0) (r 1)
    have hfilt : (Finset.Icc 1 (p * q)).filter (fun n => residueHitCount ![p, q] r n ≤ 1) =
        (Finset.Icc 1 (p * q)).filter (fun n => ¬ (n % p = r 0 % p ∧ n % q = r 1 % q)) :=
      Finset.filter_congr (fun n _ => hhit n)
    have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 (p * q))
      (fun n => n % p = r 0 % p ∧ n % q = r 1 % q)
    rw [hone, Nat.card_Icc, Nat.add_sub_cancel] at hsplit
    rw [availableCount, hprod, hfilt]
    omega
  have hdet : onesDiagDet ![p, q] = (p : ℤ) * q - 1 := by
    refine (Matrix.det_fin_two (R := ℤ)
      (fun i j => if i = j then ((![p, q] i : ℕ) : ℤ) else 1)).trans ?_
    simp
  rw [hdet]
  have h := congrArg (fun n : ℕ => (n : ℤ)) hcount
  push_cast at h
  exact eq_sub_of_add_eq h

end MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted
