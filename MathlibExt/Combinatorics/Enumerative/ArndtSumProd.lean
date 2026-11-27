/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ArndtCompositions

/-!
# Arndt compositions with a given number of parts as a sum of products

We prove that the number of Arndt compositions of `n` with `2ℓ` parts is the sum of
`∏ᵢ ⌊(aᵢ - 1)/2⌋` over the `ℓ`-tuples `(a₁, …, a_ℓ)` of natural numbers with sum `n` and every
`aᵢ ≥ 3`, and that the number with `2ℓ + 1` parts is the same sum of products over the
`(ℓ + 1)`-tuples with sum `n`, `a₁, …, a_ℓ ≥ 3` and `a_{ℓ+1} ≥ 1`
(`MetaMathlibExt.arndtCompositionCount_eq_sum_prod`).

An Arndt composition is a concatenation of descending pairs `σ_{2i-1} > σ_{2i}`, followed by one
last part when the number of parts is odd (D. F. Checa and J. L. Ramírez, arXiv:2311.15388v1,
proof of Theorem 2.1). A pair of weight `s` is determined by its second part, which ranges over
`1, …, ⌊(s - 1)/2⌋`, so removing the leading pair gives
`a(n, k + 2) = ∑_{s + t = n} ⌊(s - 1)/2⌋ a(t, k)`. Splitting a tuple into its first entry and its
tail gives the same recursion for the sums of products, and both formulas follow by induction on
`ℓ`. The terms with some `aᵢ ≤ 2` vanish, since then `⌊(aᵢ - 1)/2⌋ = 0`.
-/

namespace MetaMathlibExt

namespace arndtCompositionCount_eq_sum_prod

open Finset

-- A tuple of weight `n` splits into its first entry `s` and a tail of weight `t`, `s + t = n`.
private lemma sum_antidiagonalTuple_succ {M : Type*} [AddCommMonoid M] (k n : ℕ)
    (f : (Fin (k + 1) → ℕ) → M) :
    ∑ a ∈ Nat.antidiagonalTuple (k + 1) n, f a =
      ∑ p ∈ antidiagonal n, ∑ a ∈ Nat.antidiagonalTuple k p.2, f (Fin.cons p.1 a) := by
  rw [sum_sigma']
  refine sum_nbij' (fun a ↦ ⟨(a 0, ∑ i, Fin.tail a i), Fin.tail a⟩)
    (fun z ↦ Fin.cons z.1.1 z.2) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Nat.mem_antidiagonalTuple, Fin.sum_univ_succ] at ha
    simp [Nat.mem_antidiagonalTuple, Fin.tail, ha]
  · rintro ⟨⟨s, t⟩, a⟩ hz
    simp only [mem_sigma, mem_antidiagonal, Nat.mem_antidiagonalTuple] at hz
    simp [Nat.mem_antidiagonalTuple, Fin.sum_cons, hz.1, hz.2]
  · intro a _
    exact Fin.cons_self_tail a
  · rintro ⟨⟨s, t⟩, a⟩ hz
    simp only [mem_sigma, mem_antidiagonal, Nat.mem_antidiagonalTuple] at hz
    simp [hz.2]
  · intro a _
    simp

-- `2ℓ` parts: `ℓ` descending pairs.
private lemma count_two_mul (ℓ n : ℕ) :
    arndtCompositionCount (fun _ => True) n (2 * ℓ) =
      ∑ a ∈ (Nat.antidiagonalTuple ℓ n).filter (fun a => ∀ i, 3 ≤ a i),
        ∏ i, (a i - 1) / 2 := by
  induction ℓ generalizing n with
  | zero => cases n <;> simp [arndtCompositionCount]
  | succ ℓ ih =>
    rw [show 2 * (ℓ + 1) = 2 * ℓ + 2 by ring, arndtCompositionCount.add_two,
      sum_filter, sum_antidiagonalTuple_succ]
    refine sum_congr rfl fun p _ ↦ ?_
    rw [ih, sum_filter, mul_sum]
    refine sum_congr rfl fun a _ ↦ ?_
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ]
    by_cases h3 : 3 ≤ p.1
    · simp [h3]
    · have : (p.1 - 1) / 2 = 0 := by omega
      simp [h3, this]

-- `2ℓ + 1` parts: `ℓ` descending pairs and a last part.
private lemma count_two_mul_add_one (ℓ n : ℕ) :
    arndtCompositionCount (fun _ => True) n (2 * ℓ + 1) =
      ∑ a ∈ (Nat.antidiagonalTuple (ℓ + 1) n).filter
          (fun a => (∀ i : Fin ℓ, 3 ≤ a i.castSucc) ∧ 1 ≤ a (Fin.last ℓ)),
        ∏ i : Fin ℓ, (a i.castSucc - 1) / 2 := by
  induction ℓ generalizing n with
  | zero =>
    rcases n with _ | n <;>
      simp [arndtCompositionCount, Nat.antidiagonalTuple_one, Fin.forall_fin_one,
        filter_singleton]
  | succ ℓ ih =>
    rw [show 2 * (ℓ + 1) + 1 = 2 * ℓ + 1 + 2 by ring, arndtCompositionCount.add_two,
      sum_filter, sum_antidiagonalTuple_succ]
    refine sum_congr rfl fun p _ ↦ ?_
    rw [ih, sum_filter, mul_sum]
    refine sum_congr rfl fun a _ ↦ ?_
    simp only [Fin.forall_fin_succ, Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc,
      Fin.cons_succ, Fin.prod_univ_succ, ← Fin.succ_last]
    by_cases h3 : 3 ≤ p.1
    · simp [h3]
    · have : (p.1 - 1) / 2 = 0 := by omega
      simp [h3, this]

end arndtCompositionCount_eq_sum_prod

open arndtCompositionCount_eq_sum_prod in
/-- **Arndt compositions with a given number of parts as a sum of products.** For all natural
numbers $n$ and $\ell$, the number of Arndt compositions of $n$ with $2\ell$ parts is
$$\sum_{(a_1, \dots, a_\ell)} \prod_{i=1}^{\ell} \left\lfloor \frac{a_i - 1}{2} \right\rfloor,$$
the sum running over the $\ell$-tuples of natural numbers with $a_1 + \dots + a_\ell = n$ and
every $a_i \ge 3$; and the number of Arndt compositions of $n$ with $2\ell + 1$ parts is the same
sum of products $\prod_{i=1}^{\ell} \lfloor (a_i - 1)/2 \rfloor$, now running over the
$(\ell + 1)$-tuples $(a_1, \dots, a_{\ell+1})$ of natural numbers with
$a_1 + \dots + a_{\ell+1} = n$, $a_1, \dots, a_\ell \ge 3$ and $a_{\ell+1} \ge 1$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 10 (`jis-2025-25.3.6-thm-10`). -/
public theorem arndtCompositionCount_eq_sum_prod (n ℓ : ℕ) :
    arndtCompositionCount (fun _ => True) n (2 * ℓ) =
        (∑ a ∈ (Finset.Nat.antidiagonalTuple ℓ n).filter (fun a => ∀ i, 3 ≤ a i),
          ∏ i, (a i - 1) / 2) ∧
      arndtCompositionCount (fun _ => True) n (2 * ℓ + 1) =
        (∑ a ∈ (Finset.Nat.antidiagonalTuple (ℓ + 1) n).filter
            (fun a => (∀ i : Fin ℓ, 3 ≤ a i.castSucc) ∧ 1 ≤ a (Fin.last ℓ)),
          ∏ i : Fin ℓ, (a i.castSucc - 1) / 2) :=
  ⟨count_two_mul ℓ n, count_two_mul_add_one ℓ n⟩

end MetaMathlibExt
