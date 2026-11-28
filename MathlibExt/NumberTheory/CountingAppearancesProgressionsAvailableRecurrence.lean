/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CountingAppearancesProgressionsFreeCount
public import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.PrimeFin

/-!
# Recurrence for available integers modulo the first primes

The Chinese remainder theorem identifies each lift of a representative modulo the old product
with one remainder modulo the new prime. Among the lifts of each available representative,
all lifts that miss the new class remain available; the unique lift that hits it remains
available precisely when the representative is free.

## References

* Florian Pausinger, *Counting Appearances of Integers in Sets of Arithmetic Progressions*,
  INTEGERS **26** (2026), Article A50, pp. 1–10, Lemma 4.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

/-- **The first primes.** For a natural number $k$, the $k$-tuple whose entry with index $i$, for
$0 \le i < k$, is the $(i+1)$-st prime; that is, the first $k$ primes $2, 3, 5, \dots$ in
increasing order. -/
noncomputable def firstPrimes (k : ℕ) : Fin k → ℕ :=
  fun i => Nat.nth Nat.Prime i.val

/-- **Characterization of the first primes by rank.** For natural numbers $k$ and $p$ and a
zero-based index $0 \le i < k$, the entry at index $i$ of the first $k$ primes is $p$ if and
only if $p$ is prime and there are exactly $i$ primes strictly smaller than $p$. -/
theorem firstPrimes_eq_iff {k : ℕ} {i : Fin k} {p : ℕ} :
    firstPrimes k i = p ↔ p.Prime ∧ Nat.count Nat.Prime p = i.val := by
  constructor
  · rintro rfl
    exact ⟨Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _,
      Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime _⟩
  · rintro ⟨hp, hcount⟩
    rw [firstPrimes, ← hcount, Nat.nth_count hp]

-- Use the right endpoint as the representative of the zero class.
private def intervalRep (m n : ℕ) : ℕ :=
  if n % m = 0 then m else n % m

private theorem intervalRep_mem (m n : ℕ) (hm : 0 < m) :
    intervalRep m n ∈ Finset.Icc 1 m := by
  rw [intervalRep, Finset.mem_Icc]
  split_ifs with h
  · exact ⟨hm, le_rfl⟩
  · exact ⟨Nat.pos_of_ne_zero h, (Nat.mod_lt n hm).le⟩

private theorem intervalRep_modEq (m n : ℕ) : intervalRep m n ≡ n [MOD m] := by
  rw [intervalRep]
  split_ifs with h
  · exact (Nat.modEq_zero_iff_dvd.mpr dvd_rfl).trans (h ▸ Nat.mod_modEq n m)
  · exact Nat.mod_modEq n m

private theorem eq_of_modEq_of_mem_Icc {m a b : ℕ} (ha : a ∈ Finset.Icc 1 m)
    (hb : b ∈ Finset.Icc 1 m) (h : a ≡ b [MOD m]) : a = b := by
  obtain ⟨ha₁, ha₂⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hb₁, hb₂⟩ := Finset.mem_Icc.mp hb
  apply h.eq_of_abs_lt
  rw [abs_lt]
  constructor <;> omega

-- CRT identifies a lift with its old interval representative and its new remainder.
private theorem card_filter_crt {m q : ℕ} (hm : 0 < m) (hq : 0 < q) (hcop : m.Coprime q)
    (ok : ℕ → ℕ → Prop) [DecidableRel ok] :
    ((Finset.Icc 1 (m * q)).filter (fun n => ok (intervalRep m n) (n % q))).card =
      ((Finset.Icc 1 m ×ˢ Finset.range q).filter (fun ab => ok ab.1 ab.2)).card := by
  refine Finset.card_nbij (fun n => (intervalRep m n, n % q)) ?_ ?_ ?_
  · intro n hn
    exact Finset.mem_filter.mpr ⟨Finset.mk_mem_product (intervalRep_mem m n hm)
      (Finset.mem_range.mpr (Nat.mod_lt n hq)), (Finset.mem_filter.mp hn).2⟩
  · intro a ha b hb hab
    have hrep : intervalRep m a = intervalRep m b := congrArg Prod.fst hab
    have h₁ : a ≡ b [MOD m] := by
      apply (intervalRep_modEq m a).symm.trans
      rw [hrep]
      exact intervalRep_modEq m b
    have h₂ : a ≡ b [MOD q] := congrArg Prod.snd hab
    exact eq_of_modEq_of_mem_Icc (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
      ((Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h₁, h₂⟩)
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hab).1
    let c := Nat.chineseRemainder hcop a b
    let n := intervalRep (m * q) c
    have hn := intervalRep_modEq (m * q) c
    have hna : intervalRep m n = a := eq_of_modEq_of_mem_Icc (intervalRep_mem m n hm) ha
      ((intervalRep_modEq m n).trans ((hn.of_mul_right q).trans c.prop.1))
    have hnb : n % q = b := calc
      n % q = b % q := (hn.of_mul_left m).trans c.prop.2
      _ = b := Nat.mod_eq_of_lt (Finset.mem_range.mp hb)
    refine ⟨n, Finset.mem_filter.mpr ⟨intervalRep_mem (m * q) c (Nat.mul_pos hm hq), ?_⟩,
      Prod.ext hna hnb⟩
    simpa only [hna, hnb] using (Finset.mem_filter.mp hab).2

private theorem residueHitCount_modEq {k : ℕ} (p r : Fin k → ℕ) {a b : ℕ}
    (hab : a ≡ b [MOD ∏ i, p i]) : residueHitCount p r a = residueHitCount p r b := by
  unfold residueHitCount
  congr 1
  exact Finset.filter_congr (fun i _ => by
    have hi : a % p i = b % p i := hab.of_dvd (Finset.dvd_prod_of_mem p (Finset.mem_univ i))
    rw [hi])

-- Non-hits can extend any available representative; the single hit needs a free one.
private theorem card_available_pairs (m q b : ℕ) (hb : b < q) (hits : ℕ → ℕ) :
    ((Finset.Icc 1 m ×ˢ Finset.range q).filter
      (fun ab => hits ab.1 + (if ab.2 = b then 1 else 0) ≤ 1)).card =
    (q - 1) * ((Finset.Icc 1 m).filter (fun a => hits a ≤ 1)).card +
      ((Finset.Icc 1 m).filter (fun a => hits a = 0)).card := by
  let available := (Finset.Icc 1 m).filter (fun a => hits a ≤ 1)
  let free := (Finset.Icc 1 m).filter (fun a => hits a = 0)
  let other := (Finset.range q).erase b
  have hsplit : ((Finset.Icc 1 m ×ˢ Finset.range q).filter
      (fun ab => hits ab.1 + (if ab.2 = b then 1 else 0) ≤ 1)) =
      (available ×ˢ other) ∪ (free ×ˢ {b}) := by
    ext ⟨x, y⟩
    by_cases hy : y = b
    · subst y
      simp [available, free, other, Finset.mem_range.mpr hb]
    · simp [available, free, other, hy, Ne.symm hy, and_left_comm, and_comm]
  have hd : Disjoint (available ×ˢ other) (free ×ˢ {b}) := by
    rw [Finset.disjoint_left]
    intro ab ha hb'
    have hne := (Finset.mem_erase.mp (Finset.mem_product.mp ha).2).1
    exact hne (Finset.mem_singleton.mp (Finset.mem_product.mp hb').2)
  rw [hsplit, Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product,
    Finset.card_singleton, mul_one, mul_comm available.card]
  simp [available, free, other, Finset.card_erase_of_mem (Finset.mem_range.mpr hb)]

-- Keep the published lower-bound binder, even though the argument also allows an empty prefix.
set_option linter.unusedVariables false in
/-- **Recurrence for the number of available integers.** Let $k \ge 1$, let $p_1, \dots, p_{k+1}$
be the first $k + 1$ primes, and let $r_1, \dots, r_{k+1}$ be any natural numbers. For $m = k$ and
$m = k + 1$, call an integer $n$ free if $n \not\equiv r_i \pmod{p_i}$ for every $i \le m$, and
available if $n \equiv r_i \pmod{p_i}$ for at most one $i \le m$; let $\mathrm{av}(m)$ and
$\mathrm{free}(m)$ be the numbers of available and of free integers $n$ with
$1 \le n \le p_1 \cdots p_m$. Then
$\mathrm{av}(k+1) = (p_{k+1} - 1) \cdot \mathrm{av}(k) + \mathrm{free}(k)$.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 4. -/
theorem availableCount_firstPrimes_succ (k : ℕ) (hk : 1 ≤ k)
    (r : Fin (k + 1) → ℕ) :
    availableCount (firstPrimes (k + 1)) r =
      (Nat.nth Nat.Prime k - 1) *
          availableCount (firstPrimes k) (r ∘ Fin.castSucc) +
        freeCount (firstPrimes k) (r ∘ Fin.castSucc) := by
  -- The counting argument also works for the empty prefix.
  clear hk
  let P := ∏ i, firstPrimes k i
  let q := Nat.nth Nat.Prime k
  let hits := residueHitCount (firstPrimes k) (r ∘ Fin.castSucc)
  have hprime (j : ℕ) : (Nat.nth Nat.Prime j).Prime :=
    Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j
  have hP : 0 < P := Finset.prod_pos (fun i _ => (hprime i.val).pos)
  have hq : 0 < q := (hprime k).pos
  have hcop : P.Coprime q := by
    refine Nat.Coprime.prod_left (fun i _ => ?_)
    exact (Nat.coprime_primes (hprime i.val) (hprime k)).2
      ((Nat.nth_strictMono Nat.infinite_setOfPred_prime i.isLt).ne)
  have hprod : ∏ i, firstPrimes (k + 1) i = P * q := Fin.prod_univ_castSucc _
  have hsplit (n : ℕ) : residueHitCount (firstPrimes (k + 1)) r n =
      hits (intervalRep P n) + (if n % q = r (Fin.last k) % q then 1 else 0) := by
    have hrep : hits (intervalRep P n) = hits n :=
      residueHitCount_modEq _ _ (intervalRep_modEq P n)
    rw [hrep]
    dsimp only [hits, residueHitCount]
    rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
    rfl
  simpa only [availableCount, freeCount, hprod, hsplit, q, P, hits] using
    (card_filter_crt hP hq hcop
      (fun a b => hits a + (if b = r (Fin.last k) % q then 1 else 0) ≤ 1)).trans
    (card_available_pairs P q (r (Fin.last k) % q) (Nat.mod_lt _ hq) hits)

end MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted
