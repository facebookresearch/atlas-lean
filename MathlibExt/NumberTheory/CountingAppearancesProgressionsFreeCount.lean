/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CountingAppearancesProgressions
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.ModEq
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.Ring

/-!
# Bordered determinants and free integers for two distinct primes

Rotating the first row to the bottom turns the signed bordered determinant for any natural
moduli into the determinant of a symmetric ones-diagonal matrix with a final diagonal entry
of one. For two distinct primes and any two residues, `freeCount_two_primes` identifies this
signed determinant with the number of integers between one and the product of the primes
that avoid both chosen classes. The Chinese remainder theorem gives one representative per
pair of remainders in that interval.

## References

* Florian Pausinger, *Counting Appearances of Integers in Sets of Arithmetic Progressions*,
  INTEGERS **26** (2026), Article A50, pp. 1–10, Lemmas 1 and 5 and Section 5.
  <https://math.colgate.edu/~integers/aa50/aa50.pdf>
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

/-- **Bordered ones-diagonal matrix.** For natural numbers $p_1, \dots, p_k$, the
$(k+1) \times (k+1)$ integer matrix whose first row consists of ones and whose row $i + 1$, for
$1 \le i \le k$, has $p_i$ in column $i$ and $1$ in every other column. Equivalently, it is the
$k \times k$ matrix with diagonal entries $p_1, \dots, p_k$ and all other entries $1$, with a
column of ones appended on the right and then a row of ones placed on top. -/
def borderedOnesDiag {k : ℕ} (p : Fin k → ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
  fun i j => if i = 0 then 1
    else if h : j.val + 1 = i.val then
      (p ⟨j.val, by have hi := i.isLt; omega⟩ : ℤ)
    else 1

/-- **Bordered ones-diagonal determinant.** For natural numbers $p_1, \dots, p_k$, the integer
$F_k(p_1, \dots, p_k)$ is $(-1)^k$ times the determinant of the bordered ones-diagonal matrix of
$p_1, \dots, p_k$: the $(k+1) \times (k+1)$ integer matrix whose first row consists of ones and
whose row $i + 1$, for $1 \le i \le k$, has $p_i$ in column $i$ and $1$ in every other column. -/
def borderedOnesDiagDet {k : ℕ} (p : Fin k → ℕ) : ℤ :=
  (-1 : ℤ) ^ k * (borderedOnesDiag p).det

/-- **Bordered determinant with a symmetric border.** For natural numbers $p_1, \dots, p_k$,
the signed bordered determinant is the determinant of the $(k+1) \times (k+1)$ matrix with
$p_1, \dots, p_k, 1$ on the diagonal and $1$ in every off-diagonal entry. -/
theorem borderedOnesDiagDet_eq_det_snoc_one {k : ℕ} (p : Fin k → ℕ) :
    borderedOnesDiagDet p =
      (Matrix.of (fun i j : Fin (k + 1) =>
        if i = j then ((Fin.snoc p 1 : Fin (k + 1) → ℕ) i : ℤ) else 1)).det := by
  have hrot : (borderedOnesDiag p).submatrix (finRotate (k + 1)) id =
      Matrix.of (fun i j : Fin (k + 1) =>
        if i = j then ((Fin.snoc p 1 : Fin (k + 1) → ℕ) i : ℤ) else 1) := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq, Matrix.of_apply]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [borderedOnesDiag]
    · rw [show finRotate (k + 1) i.castSucc = i.succ from finRotate_of_lt i.isLt]
      by_cases hij : i.castSucc = j
      · subst j
        simp [borderedOnesDiag]
      · have hval : j.val ≠ i.val := fun h => hij (Fin.ext h.symm)
        simp [borderedOnesDiag, hij, hval]
  rw [← hrot, borderedOnesDiagDet, Matrix.det_permute]
  simp

/-- **Free count.** For natural numbers $p_1, \dots, p_k$ and $r_1, \dots, r_k$, let $\gamma(n)$
be the number of indices $i$ with $n \equiv r_i \pmod{p_i}$. The free count is the number of
integers $n$ with $1 \le n \le p_1 \cdots p_k$ and $\gamma(n) = 0$.

When $p_1, \dots, p_k$ are the first $k$ primes, this is the count $\mathrm{free}(k)$ of
Pausinger's paper. -/
def freeCount {k : ℕ} (p r : Fin k → ℕ) : ℕ :=
  ((Finset.Icc 1 (∏ i, p i)).filter
    (fun n => residueHitCount p r n = 0)).card

/-- **Lemma 5, free count.** Let $p$ and $q$ be distinct primes and let $r_1, r_2$ be natural
numbers. Then the number of integers $n$ with $1 \le n \le pq$ such that
$n \not\equiv r_1 \pmod p$ and $n \not\equiv r_2 \pmod q$ equals $F_2(p, q)$, where
$$F_2(p, q) = \det \begin{pmatrix} 1 & 1 & 1 \\ p & 1 & 1 \\ 1 & q & 1 \end{pmatrix}.$$

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 5. -/
theorem freeCount_two_primes (p q : ℕ) (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (r : Fin 2 → ℕ) :
    (freeCount ![p, q] r : ℤ) = borderedOnesDiagDet ![p, q] := by
  have hcount : freeCount ![p, q] r = (p - 1) * (q - 1) := by
    have hprod : ∏ i, ![p, q] i = p * q := by simp [Fin.prod_univ_two]
    have hhit (n : ℕ) : residueHitCount ![p, q] r n = 0 ↔
        n % p ≠ r 0 % p ∧ n % q ≠ r 1 % q := by
      simp [residueHitCount, Fin.forall_fin_two]
    rw [freeCount, hprod]
    let allowedP := (Finset.range p).erase (r 0 % p)
    let allowedQ := (Finset.range q).erase (r 1 % q)
    have hcop := (Nat.coprime_primes hp hq).2 hpq
    have hcard : ((Finset.Icc 1 (p * q)).filter (fun n => residueHitCount ![p, q] r n = 0)).card =
        (allowedP ×ˢ allowedQ).card := by
      refine Finset.card_nbij (fun n => (n % p, n % q)) ?_ ?_ ?_
      · intro n hn
        obtain ⟨hnp, hnq⟩ := (hhit n).mp (Finset.mem_filter.mp hn).2
        exact Finset.mk_mem_product
          (Finset.mem_erase.mpr ⟨hnp, Finset.mem_range.mpr (Nat.mod_lt n hp.pos)⟩)
          (Finset.mem_erase.mpr ⟨hnq, Finset.mem_range.mpr (Nat.mod_lt n hq.pos)⟩)
      · intro x hx y hy hxy
        obtain ⟨hx₁, hx₂⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1
        obtain ⟨hy₁, hy₂⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hy).1
        have hmod := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
          ⟨congrArg Prod.fst hxy, congrArg Prod.snd hxy⟩
        apply hmod.eq_of_abs_lt
        rw [abs_lt]
        constructor <;> push_cast <;> omega
      · rintro ⟨a, b⟩ hab
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
        obtain ⟨ha_ne, ha_lt⟩ := Finset.mem_erase.mp ha
        obtain ⟨hb_ne, hb_lt⟩ := Finset.mem_erase.mp hb
        let c := Nat.chineseRemainder hcop a b
        have hc := Nat.chineseRemainder_lt_mul hcop a b hp.ne_zero hq.ne_zero
        -- The representative of the zero class modulo `p * q` is the right endpoint.
        let n := if (c : ℕ) = 0 then p * q else (c : ℕ)
        have hn : n ∈ Finset.Icc 1 (p * q) := by
          apply Finset.mem_Icc.mpr
          dsimp only [n]
          split_ifs with hzero
          · exact ⟨Nat.mul_pos hp.pos hq.pos, le_rfl⟩
          · exact ⟨Nat.pos_of_ne_zero hzero, hc.le⟩
        have hmod : n ≡ (c : ℕ) [MOD p * q] := by
          dsimp only [n]
          split_ifs with hzero
          · rw [hzero, Nat.modEq_zero_iff_dvd]
          · rfl
        have hnp : n % p = a := calc
          n % p = a % p := (hmod.of_mul_right q).trans c.prop.1
          _ = a := Nat.mod_eq_of_lt (Finset.mem_range.mp ha_lt)
        have hnq : n % q = b := calc
          n % q = b % q := (hmod.of_mul_left p).trans c.prop.2
          _ = b := Nat.mod_eq_of_lt (Finset.mem_range.mp hb_lt)
        exact ⟨n, Finset.mem_filter.mpr ⟨hn, (hhit n).mpr ⟨hnp ▸ ha_ne, hnq ▸ hb_ne⟩⟩,
          Prod.ext hnp hnq⟩
    rw [hcard]
    simp [allowedP, allowedQ, Finset.card_product, Finset.card_erase_of_mem,
      Nat.mod_lt, hp.pos, hq.pos]
  have hdet : borderedOnesDiagDet ![p, q] = ((p : ℤ) - 1) * ((q : ℤ) - 1) := by
    rw [borderedOnesDiagDet, Matrix.det_fin_three]
    norm_num [borderedOnesDiag, Fin.val_one, Fin.val_two]
    ring
  rw [hcount, hdet, Nat.cast_mul, Nat.cast_sub hp.one_lt.le, Nat.cast_sub hq.one_lt.le,
    Nat.cast_one]

end MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted
