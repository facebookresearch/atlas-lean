/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# ℓ-regular overpartitions modulo 4

`A_ℓ(n)` is `regularOverpartitionCount ℓ n`, the number of overpartitions of `n` with no part
divisible by `ℓ`, counted with the existing `Nat.Overpartition` structure. The main result,
`regularOverpartition_mod_four_progression`, says that for `ℓ ≡ 3 (mod 4)` the count
`A_ℓ(4ℓn + 4j + 3)` is divisible by `4` whenever `j ≢ (ℓ - 3)/4 (mod ℓ)`; its docstring cites the
source of the statement. The module also gives the values `A_ℓ(0) = 1` and, for `ℓ ≥ 2`,
`A_ℓ(1) = 2`.

The proof is elementary and follows A. M. Alanazi and M. P. Saikia, *Some Comments on Regular
Overpartitions modulo 2^k* (arXiv:2607.07259), Lemma 1, Theorem 1 (the case `k = 2`) and the
proof of Corollary 1. An ℓ-regular partition with `r` distinct part sizes underlies exactly
`2 ^ r` overpartitions, so modulo `4` only the partitions with a single part size count, and
those correspond to the divisors of `n` not divisible by `ℓ`. For `n = 4ℓn' + 4j + 3` the
condition on `j` says that `ℓ` does not divide `n`, so every divisor counts, and `n` has an even
number of divisors because `n ≡ 3 (mod 4)` is not a perfect square.
-/

namespace MetaMathlibExt

@[expose] public section

/--
**Number of $\ell$-regular overpartitions.** For natural numbers $\ell$ and $n$, $A_\ell(n)$ is
the number of overpartitions of $n$ in which no part is divisible by $\ell$.

No positivity restriction is placed on $\ell$; for $\ell = 0$ every overpartition of $n$ is
counted, since parts are positive.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Identity (1).
-/
public noncomputable def regularOverpartitionCount (ℓ n : ℕ) : ℕ :=
  Nat.card {O : Nat.Overpartition n // ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a}

/--
**One $\ell$-regular overpartition of zero.** For every natural number $\ell$, the number
$A_\ell(0)$ of overpartitions of $0$ with no part divisible by $\ell$ equals $1$: the only one is
the empty overpartition.

The statement also covers $\ell = 0$, a harmless extension of the paper's positive regularity
parameter.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Identity (1).
-/
public theorem regularOverpartitionCount_zero (ℓ : ℕ) :
    regularOverpartitionCount ℓ 0 = 1 := by
  let O : {O : Nat.Overpartition 0 //
      ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a} :=
    ⟨Nat.Overpartition.ofPartition default, by
      intro a ha
      simp [_root_.Nat.Partition.partition_zero_parts] at ha⟩
  let _ : Nonempty {O : Nat.Overpartition 0 //
      ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a} := ⟨O⟩
  let _ : Subsingleton {O : Nat.Overpartition 0 //
      ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a} :=
    ⟨fun O₁ O₂ => Subtype.ext (Nat.Overpartition.eq_of_zero O₁.1 O₂.1)⟩
  exact Nat.card_unique

/--
**Two $\ell$-regular overpartitions of one.** For every natural number $\ell \ge 2$, the number
$A_\ell(1)$ of overpartitions of $1$ with no part divisible by $\ell$ equals $2$: they are the
single part $1$, without and with an overline.

Among positive $\ell$, the hypothesis $\ell \ge 2$ says exactly that $\ell$ does not divide the
sole part $1$.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Identity (1).
-/
public theorem regularOverpartitionCount_one (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    regularOverpartitionCount ℓ 1 = 2 := by
  let e :
      {O : Nat.Overpartition 1 //
        ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a} ≃ Bool := {
    toFun O := decide (1 ∈ O.1.overlines)
    invFun b :=
      ⟨{
        toPartition := default
        overlines := if b = true then {1} else ∅
        overlines_subset := by
          intro a ha
          rw [_root_.Nat.Partition.partition_one_parts]
          cases b <;> simp_all
      }, by
        intro a ha hdiv
        rw [_root_.Nat.Partition.partition_one_parts] at ha
        have haone : a = 1 := by simpa using ha
        subst a
        have hle : ℓ ≤ 1 := Nat.le_of_dvd (by decide) hdiv
        omega⟩
    left_inv O := by
      apply Subtype.ext
      apply Nat.Overpartition.ext
      · exact Subsingleton.elim _ _
      · have hsub : O.1.overlines ⊆ {1} := by
          intro a ha
          have h := O.1.overlines_subset ha
          rw [_root_.Nat.Partition.partition_one_parts] at h
          simpa using h
        by_cases hmem : 1 ∈ O.1.overlines
        · have hover : O.1.overlines = {1} := by
            apply Finset.Subset.antisymm hsub
            simpa using hmem
          simp [hover]
        · have hover : O.1.overlines = ∅ := by
            apply Finset.Subset.antisymm
            · intro a ha
              have haone : a = 1 := by simpa using hsub ha
              subst a
              exact (hmem ha).elim
            · exact Finset.empty_subset _
          simp [hover]
    right_inv b := by
      cases b <;> simp
  }
  unfold regularOverpartitionCount
  calc
    Nat.card {O : Nat.Overpartition 1 //
        ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a} =
        Nat.card Bool := Nat.card_congr e
    _ = 2 := by simp

namespace regularOverpartition_mod_four_progression

open Finset

/-- An ℓ-regular overpartition is an ℓ-regular partition together with a set of its distinct
part sizes, the overlined ones. -/
private def regularEquiv (ℓ n : ℕ) :
    {O : Nat.Overpartition n // ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a} ≃
      Σ p : {p : Nat.Partition n // ∀ a ∈ p.parts, ¬ ℓ ∣ a}, p.1.parts.toFinset.powerset where
  toFun O := ⟨⟨O.1.toPartition, O.2⟩, ⟨O.1.overlines, mem_powerset.mpr O.1.overlines_subset⟩⟩
  invFun x := ⟨⟨x.1.1, x.2.1, mem_powerset.mp x.2.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Each ℓ-regular partition with `r` distinct part sizes underlies `2 ^ r` ℓ-regular
overpartitions (Alanazi and Saikia, Lemma 1). -/
private theorem count_eq_sum (ℓ n : ℕ) :
    regularOverpartitionCount ℓ n =
      ∑ p : Nat.Partition n with ∀ a ∈ p.parts, ¬ ℓ ∣ a, 2 ^ #p.parts.toFinset := by
  rw [regularOverpartitionCount, Nat.card_congr (regularEquiv ℓ n), Nat.card_sigma]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, card_powerset]
  exact (sum_subtype _ (by simp) (fun p : Nat.Partition n => 2 ^ #p.parts.toFinset)).symm

/-- The partition of `n` into `n / a` parts equal to `a`, for a positive divisor `a` of `n`. -/
private def single (n a : ℕ) (ha : a ∣ n) (ha0 : 0 < a) : Nat.Partition n where
  parts := Multiset.replicate (n / a) a
  parts_pos hi := by rw [Multiset.eq_of_mem_replicate hi]; exact ha0
  parts_sum := by rw [Multiset.sum_replicate, smul_eq_mul, Nat.div_mul_cancel ha]

/-- For `n ≠ 0`, the ℓ-regular partitions of `n` with a single part size correspond to the
divisors of `n` that are not divisible by `ℓ`. -/
private theorem card_single (ℓ n : ℕ) (hn : n ≠ 0) :
    #{p : Nat.Partition n | (∀ a ∈ p.parts, ¬ ℓ ∣ a) ∧ #p.parts.toFinset = 1} =
      #{a ∈ n.divisors | ¬ ℓ ∣ a} := by
  symm
  refine card_bij (fun a ha => single n a (Nat.dvd_of_mem_divisors (mem_filter.1 ha).1)
    (Nat.pos_of_mem_divisors (mem_filter.1 ha).1)) ?_ ?_ ?_
  · intro a ha
    obtain ⟨had, hla⟩ := mem_filter.1 ha
    have hpos : 0 < n / a := Nat.div_pos (Nat.divisor_le had) (Nat.pos_of_mem_divisors had)
    simp only [mem_filter, mem_univ, true_and, single]
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [Multiset.eq_of_mem_replicate hx]
      exact hla
    · rw [card_eq_one]
      refine ⟨a, ?_⟩
      ext x
      simp [hpos.ne']
  · intro a ha b hb hab
    have had := (mem_filter.1 ha).1
    have hpos : 0 < n / a := Nat.div_pos (Nat.divisor_le had) (Nat.pos_of_mem_divisors had)
    have h := congrArg Nat.Partition.parts hab
    simp only [single] at h
    have hmem : a ∈ Multiset.replicate (n / a) a := Multiset.mem_replicate.2 ⟨hpos.ne', rfl⟩
    rw [h] at hmem
    exact Multiset.eq_of_mem_replicate hmem
  · intro p hp
    obtain ⟨hreg, hone⟩ := (mem_filter.1 hp).2
    obtain ⟨a, ha⟩ := card_eq_one.1 hone
    have hall : ∀ x ∈ p.parts, x = a := by
      intro x hx
      have hx' : x ∈ p.parts.toFinset := Multiset.mem_toFinset.2 hx
      rw [ha] at hx'
      exact mem_singleton.1 hx'
    have hamem : a ∈ p.parts := by
      have ha' : a ∈ p.parts.toFinset := by
        rw [ha]
        exact mem_singleton_self a
      exact Multiset.mem_toFinset.1 ha'
    have hrep : p.parts = Multiset.replicate (Multiset.card p.parts) a :=
      Multiset.eq_replicate_card.2 hall
    have hsum : Multiset.card p.parts * a = n := by
      have hs := p.parts_sum
      rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hs
      simpa using hs
    have hapos : 0 < a := p.parts_pos hamem
    have hdvd : a ∣ n := Dvd.intro_left _ hsum
    refine ⟨a, mem_filter.2 ⟨Nat.mem_divisors.2 ⟨hdvd, hn⟩, hreg a hamem⟩, ?_⟩
    apply Nat.Partition.ext
    simp only [single]
    rw [Nat.div_eq_of_eq_mul_left hapos hsum.symm, ← hrep]

/-- For `n ≠ 0`, the number of ℓ-regular overpartitions of `n` is congruent modulo `4` to twice
the number of divisors of `n` that are not divisible by `ℓ` (Alanazi and Saikia, Theorem 1 with
`k = 2`). -/
private theorem count_modEq (ℓ n : ℕ) (hn : n ≠ 0) :
    regularOverpartitionCount ℓ n ≡ 2 * #{a ∈ n.divisors | ¬ ℓ ∣ a} [MOD 4] := by
  rw [count_eq_sum, ← card_single ℓ n hn, ← filter_filter,
    ← sum_filter_add_sum_filter_not _ (fun p : Nat.Partition n => #p.parts.toFinset = 1)]
  set S := ({p : Nat.Partition n | ∀ a ∈ p.parts, ¬ ℓ ∣ a} : Finset (Nat.Partition n))
  have h1 : ∑ p ∈ S with #p.parts.toFinset = 1, 2 ^ #p.parts.toFinset =
      2 * #{p ∈ S | #p.parts.toFinset = 1} := by
    rw [sum_congr rfl (fun p hp => by rw [(mem_filter.1 hp).2, pow_one]), sum_const,
      smul_eq_mul, mul_comm]
  have h2 : 4 ∣ ∑ p ∈ S with ¬ #p.parts.toFinset = 1, 2 ^ #p.parts.toFinset := by
    apply dvd_sum
    intro p hp
    have hne : #p.parts.toFinset ≠ 1 := (mem_filter.1 hp).2
    have hne0 : #p.parts.toFinset ≠ 0 := by
      intro h0
      rw [card_eq_zero, Multiset.toFinset_eq_empty] at h0
      apply hn
      rw [← p.parts_sum, h0, Multiset.sum_zero]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ∣ 2 ^ #p.parts.toFinset := pow_dvd_pow 2 (by omega)
  rw [h1]
  calc _ ≡ 2 * #{p ∈ S | #p.parts.toFinset = 1} + 0 [MOD 4] :=
        (Nat.modEq_zero_iff_dvd.mpr h2).add_left _
    _ = _ := add_zero _

/-- A positive natural number that is not a perfect square has an even number of divisors: some
prime occurs to an odd power, which makes a factor of the divisor-count product even. -/
private theorem even_card_divisors {m : ℕ} (hm : m ≠ 0) (hsq : ¬ IsSquare m) :
    Even #m.divisors := by
  rw [Nat.isSquare_iff_even_factorization] at hsq
  push Not at hsq
  obtain ⟨p, hp, hodd⟩ := hsq
  have hmem : p ∈ m.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    intro h
    rw [h] at hodd
    exact Nat.not_odd_zero hodd
  rw [Nat.card_divisors hm, even_iff_two_dvd]
  exact (even_iff_two_dvd.mp hodd.add_one).trans (dvd_prod_of_mem _ hmem)

end regularOverpartition_mod_four_progression

open regularOverpartition_mod_four_progression in
/--
**$\ell$-regular overpartitions vanish modulo $4$ on progressions modulo $4\ell$.** For a
natural number $\ell$, let $A_\ell(m)$ be the number of overpartitions of $m$ with no part
divisible by $\ell$. Let $\ell \equiv 3 \pmod 4$, and let $n$ and $j$ be natural numbers with
$j \not\equiv (\ell - 3)/4 \pmod{\ell}$. Then $A_\ell(4\ell n + 4j + 3) \equiv 0 \pmod 4$.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 6.
-/
public theorem regularOverpartition_mod_four_progression
    (ℓ n j : ℕ) (hℓ : Nat.ModEq 4 ℓ 3)
    (hj : ¬ Nat.ModEq ℓ j ((ℓ - 3) / 4)) :
    Nat.ModEq 4
      (regularOverpartitionCount ℓ (4 * ℓ * n + 4 * j + 3))
      0 := by
  have hℓ4 : ℓ % 4 = 3 := hℓ
  obtain ⟨r, hr⟩ : ∃ r, ℓ = 4 * r + 3 := ⟨ℓ / 4, by omega⟩
  have hm0 : 4 * ℓ * n + 4 * j + 3 ≠ 0 := by omega
  -- The condition on `j` says exactly that `ℓ` does not divide `4ℓn + 4j + 3`.
  have hℓm : ¬ ℓ ∣ 4 * ℓ * n + 4 * j + 3 := by
    intro h
    apply hj
    have h1 : ℓ ∣ 4 * j + 3 := by
      rw [add_assoc] at h
      exact (Nat.dvd_add_right (dvd_mul_of_dvd_left (dvd_mul_left ℓ 4) n)).mp h
    have h2 : 4 * j + 3 ≡ 4 * r + 3 [MOD ℓ] :=
      (Nat.modEq_zero_iff_dvd.mpr h1).trans (Nat.modEq_zero_iff_dvd.mpr (hr ▸ dvd_refl ℓ)).symm
    have hcop : Nat.gcd ℓ 4 = 1 := by
      rw [Nat.gcd_comm, Nat.gcd_rec, hℓ4]
      rfl
    rw [show (ℓ - 3) / 4 = r by omega]
    exact Nat.ModEq.cancel_left_of_coprime hcop (Nat.ModEq.add_right_cancel' 3 h2)
  -- A number congruent to `3` modulo `4` is not a perfect square.
  have hsq : ¬ IsSquare (4 * ℓ * n + 4 * j + 3) := by
    rintro ⟨k, hk⟩
    have hmod : (4 * ℓ * n + 4 * j + 3) % 4 = 3 := by
      rw [show 4 * ℓ * n + 4 * j + 3 = 4 * (ℓ * n + j) + 3 by ring]
      omega
    rw [hk, Nat.mul_mod] at hmod
    have hlt := Nat.mod_lt k (show 4 > 0 by norm_num)
    generalize k % 4 = t at hmod hlt
    interval_cases t <;> simp at hmod
  have h := count_modEq ℓ _ hm0
  have hfilter : {a ∈ (4 * ℓ * n + 4 * j + 3).divisors | ¬ ℓ ∣ a} =
      (4 * ℓ * n + 4 * j + 3).divisors :=
    Finset.filter_true_of_mem fun a ha hdvd => hℓm (hdvd.trans (Nat.dvd_of_mem_divisors ha))
  rw [hfilter] at h
  obtain ⟨c, hc⟩ := even_card_divisors hm0 hsq
  refine h.trans ?_
  rw [hc]
  exact Nat.modEq_zero_iff_dvd.mpr ⟨c, by ring⟩

end

end MetaMathlibExt
