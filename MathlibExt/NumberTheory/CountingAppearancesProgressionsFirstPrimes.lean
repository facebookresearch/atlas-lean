/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CountingAppearancesProgressionsAvailableRecurrence
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.PrimeFin

/-!
# Free integers modulo the first primes

The theorem `freeCount_firstPrimes` counts integers avoiding one residue class for each of the
first primes. The Chinese remainder theorem gives a product of the numbers of allowed
remainders, and subtracting the first row from each later row gives the same product for the
signed bordered determinant.
-/

set_option autoImplicit false

public section

namespace MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

namespace freeCount_firstPrimes

private theorem freeCount_eq_prod {k : ℕ} (p r : Fin k → ℕ)
    (hp : ∀ i, 0 < p i) (hcop : Pairwise (fun i j => (p i).Coprime (p j))) :
    freeCount p r = ∏ i, (p i - 1) := by
  let P := ∏ i, p i
  let allowed (i : Fin k) := (Finset.range (p i)).erase (r i % p i)
  have hfree (n : ℕ) : residueHitCount p r n = 0 ↔ ∀ i, n % p i ≠ r i % p i := by
    simp [residueHitCount]
  have hcard : freeCount p r = (Fintype.piFinset allowed).card := by
    unfold freeCount
    refine Finset.card_nbij (fun n i => n % p i) ?_ ?_ ?_
    · intro n hn
      exact Fintype.mem_piFinset.mpr fun i => Finset.mem_erase.mpr
        ⟨(hfree n).mp (Finset.mem_filter.mp hn).2 i, Finset.mem_range.mpr (Nat.mod_lt _ (hp i))⟩
    · intro a ha b hb hab
      obtain ⟨ha₁, ha₂⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
      obtain ⟨hb₁, hb₂⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1
      have hlist : Finset.univ.toList.Pairwise (fun i j => (p i).Coprime (p j)) :=
        Finset.nodup_toList _ |>.pairwise_of_forall_ne (fun _ _ _ _ hij => hcop hij)
      have hmod : a ≡ b [MOD P] := by
        rw [show P = (Finset.univ.toList.map p).prod from (Finset.prod_map_toList _ _).symm]
        exact (Nat.modEq_list_map_prod_iff hlist).mpr (fun i _ => congrFun hab i)
      apply hmod.eq_of_abs_lt
      dsimp only [P]
      rw [abs_lt]
      constructor <;> omega
    · intro a ha
      let c := Nat.chineseRemainderOfFinset a p Finset.univ (fun i _ => (hp i).ne')
        (fun _ _ _ _ hij => hcop hij)
      have hc : (c : ℕ) < P := Nat.chineseRemainderOfFinset_lt_prod ..
      -- The zero class modulo the product is represented by the right endpoint.
      let n := if (c : ℕ) = 0 then P else (c : ℕ)
      have hn : n ∈ Finset.Icc 1 P := by
        apply Finset.mem_Icc.mpr
        dsimp only [n]
        split_ifs with hz
        · exact ⟨Finset.prod_pos (fun i _ => hp i), le_rfl⟩
        · exact ⟨Nat.pos_of_ne_zero hz, hc.le⟩
      have hmod : n ≡ (c : ℕ) [MOD P] := by
        dsimp only [n]
        split_ifs with hz
        · rw [hz, Nat.modEq_zero_iff_dvd]
        · rfl
      have hrem (i : Fin k) : n % p i = a i := by
        have hi : a i < p i :=
          Finset.mem_range.mp (Finset.mem_erase.mp (Fintype.mem_piFinset.mp ha i)).2
        calc
          n % p i = a i % p i :=
            (hmod.of_dvd (Finset.dvd_prod_of_mem p (Finset.mem_univ i))).trans
              (c.prop i (Finset.mem_univ i))
          _ = a i := Nat.mod_eq_of_lt hi
      refine ⟨n, Finset.mem_filter.mpr ⟨hn, (hfree n).mpr (fun i => ?_)⟩, funext hrem⟩
      rw [hrem]
      exact (Finset.mem_erase.mp (Fintype.mem_piFinset.mp ha i)).1
  rw [hcard, Fintype.card_piFinset]
  exact Finset.prod_congr rfl fun i _ => by
    simp [allowed, Finset.card_erase_of_mem (Finset.mem_range.mpr (Nat.mod_lt _ (hp i)))]

private theorem borderedDet_eq_prod {k : ℕ} (p : Fin k → ℕ) :
    borderedOnesDiagDet p = ∏ i, ((p i : ℤ) - 1) := by
  let B := borderedOnesDiag p
  let A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    Matrix.of fun i j => if i = 0 then 1 else B i j - 1
  have hdet : A.det = B.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const
      (fun i => if i = 0 then 0 else -1) 0 (by simp)
    intro i j
    by_cases hi : i = 0 <;> simp [A, B, borderedOnesDiag, hi, sub_eq_add_neg]
  have hlast (i : Fin k) : A i.succ (Fin.last k) = 0 := by
    simp [A, B, borderedOnesDiag, i.isLt.ne']
  have hminor : A.submatrix Fin.succ Fin.castSucc =
      Matrix.diagonal (fun i => (p i : ℤ) - 1) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [A, B, borderedOnesDiag]
    · have hval : j.val ≠ i.val := fun h => hij (Fin.ext h.symm)
      simp [A, B, borderedOnesDiag, hval, hij]
  have hexpand : A.det = (-1 : ℤ) ^ k * ∏ i, ((p i : ℤ) - 1) := by
    rw [Matrix.det_succ_column A (Fin.last k), Fin.sum_univ_succ]
    simp [A, hlast, hminor, Matrix.det_diagonal]
  change (-1 : ℤ) ^ k * B.det = _
  rw [← hdet, hexpand, ← mul_assoc, ← mul_pow]
  simp

end freeCount_firstPrimes

/-- **Theorem 1, free count.** Let $k$ be a natural number, let $p_1 < \cdots < p_k$ be the
first $k$ primes and let $r_1, \dots, r_k$ be natural numbers. Then the number of integers $n$
with $1 \le n \le p_1 \cdots p_k$ such that $n \not\equiv r_i \pmod{p_i}$ for every $i$ equals
$f_k = (-1)^k \det B$, where $B$ is the $(k+1) \times (k+1)$ integer matrix whose first row
consists of ones and whose row $i + 1$, for $1 \le i \le k$, has $p_i$ in column $i$ and $1$ in
every other column.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Theorem 1. -/
theorem freeCount_firstPrimes (k : ℕ) (r : Fin k → ℕ) :
    (freeCount (firstPrimes k) r : ℤ) =
      borderedOnesDiagDet (firstPrimes k) := by
  have hprime (j : ℕ) : (Nat.nth Nat.Prime j).Prime :=
    Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j
  have hp (i : Fin k) : (firstPrimes k i).Prime := hprime i.val
  have hcop : Pairwise (fun i j => (firstPrimes k i).Coprime (firstPrimes k j)) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr
      ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective.ne (fun h => hij (Fin.ext h)))
  rw [freeCount_firstPrimes.freeCount_eq_prod _ _ (fun i => (hp i).pos) hcop,
    freeCount_firstPrimes.borderedDet_eq_prod, Nat.cast_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [Nat.cast_sub (hp i).one_le, Nat.cast_one]

/-- **Recurrence for the bordered determinants of the first primes.** Let $k \ge 2$ and let
$p_1, \dots, p_k$ be the first $k$ primes. For $m \le k$ let $f_m = F_m(p_1, \dots, p_m)$, where
$F_m(p_1, \dots, p_m)$ is $(-1)^m$ times the determinant of the $(m+1) \times (m+1)$ matrix whose
first row consists of ones and whose row $i + 1$, for $1 \le i \le m$, has $p_i$ in column $i$ and
$1$ in every other column. Then $f_k = (p_k - 1) f_{k-1}$.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 1. -/
theorem borderedOnesDiagDet_firstPrimes_recurrence (k : ℕ)
    (hk : 2 ≤ k) :
    borderedOnesDiagDet (firstPrimes k) =
      ((Nat.nth Nat.Prime (k - 1) : ℤ) - 1) *
        borderedOnesDiagDet (firstPrimes (k - 1)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  simp only [Nat.succ_sub_one, freeCount_firstPrimes.borderedDet_eq_prod, firstPrimes]
  rw [Fin.prod_univ_castSucc]
  exact mul_comm _ _

end MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted
