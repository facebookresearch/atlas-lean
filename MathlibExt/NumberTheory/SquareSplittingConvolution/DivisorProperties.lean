/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SquareSplittingConvolution
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import all MathlibExt.NumberTheory.SquareSplittingConvolution
import all MathlibExt.NumberTheory.SquareSplittingConvolution.MoebiusInversion
import Mathlib.Data.Nat.Squarefree

/-!
# Square-splitting divisor sets

The square-splitting divisors include both endpoints and multiply across coprime inputs.
Their number is the product of the divisor counts of the squarefree and square-root parts.
-/

namespace MetaMathlibExt
namespace squareSplitDivisors_properties

open squareSplit_moebius_inversion

private theorem card_image {u v : ℕ} (hu : Squarefree u) :
    ((u.divisors ×ˢ v.divisors).image fun x => x.1 * x.2 ^ 2).card =
      u.divisors.card * v.divisors.card := by
  rw [Finset.card_image_of_injOn, Finset.card_product]
  apply Set.LeftInvOn.injOn (f₁' := fun d => (squareSplitU d, squareSplitV d))
  rintro ⟨a, b⟩ hab
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  obtain ⟨hU, hV⟩ := split_coords (hu.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha))
    (Nat.pos_of_mem_divisors hb).ne'
  exact Prod.ext hU hV

private theorem card_divisors {u : ℕ} (hu : Squarefree u) :
    u.divisors.card = 2 ^ ArithmeticFunction.cardDistinctFactors u := by
  rw [Nat.card_divisors hu.ne_zero, ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors,
    ← Finset.prod_const]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.factorization_eq_one_of_squarefree hu (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp)]

end squareSplitDivisors_properties

open squareSplitConv_isMultiplicative squareSplit_moebius_inversion squareSplitDivisors_properties

/-- **Basic properties of the square-splitting divisor sets.** Let
$A(n) = \{u_1 v_1^2 : u_1 \mid u(n),\ v_1 \mid v(n)\}$ be the square-splitting divisor set of
$n$, where $u(n)$ is the squarefree part of $n$ and $n = u(n) v(n)^2$ for $n \ge 1$. Then
(i) for every $n \ge 1$, both $1$ and $n$ belong to $A(n)$, and every element of $A(n)$ divides
$n$; (ii) for all coprime natural numbers $m$ and $n$, $A(mn) = \{ab : a \in A(m),\ b \in A(n)\}$;
and (iii) for every $n \ge 1$, $|A(n)| = d(u(n))\, d(v(n))$ and $|A(n)| = 2^{\omega(u(n))} d(v(n))$,
where $d(k)$ is the number of divisors of $k$ and $\omega(k)$ is the number of distinct prime
factors of $k$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 1
(`integers-2026-A56-thm-1`). -/
public theorem squareSplitDivisors_properties :
    (∀ n ≠ 0, 1 ∈ squareSplitDivisors n ∧ n ∈ squareSplitDivisors n ∧
      ∀ d ∈ squareSplitDivisors n, d ∣ n) ∧
    (∀ m n, Nat.Coprime m n → squareSplitDivisors (m * n) =
      (squareSplitDivisors m ×ˢ squareSplitDivisors n).image fun x => x.1 * x.2) ∧
    (∀ n ≠ 0, (squareSplitDivisors n).card =
        (squareSplitU n).divisors.card * (squareSplitV n).divisors.card ∧
      (squareSplitDivisors n).card =
        2 ^ ArithmeticFunction.cardDistinctFactors (squareSplitU n) *
          (squareSplitV n).divisors.card) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have h := squareSplitU_mul_squareSplitV_sq hn
    have huv : squareSplitU n ≠ 0 ∧ squareSplitV n ≠ 0 := by
      simpa using (h.trans_ne hn)
    refine ⟨Finset.mem_image.mpr ⟨(1, 1), ?_, by simp⟩,
      Finset.mem_image.mpr ⟨(squareSplitU n, squareSplitV n), ?_, h⟩,
      fun d hd => Nat.dvd_of_mem_divisors (squareSplitDivisors_subset hn hd)⟩ <;>
      simp [huv.1, huv.2]
  · intro m n h
    simpa only [Finset.mul_def] using squareSplitDivisors_mul h
  · intro n hn
    obtain ⟨u, v, _, hv, h, hu⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hn)
    rw [mul_comm] at h
    obtain ⟨hU, hV⟩ := split_coords hu hv.ne'
    rw [← h, squareSplitDivisors, hU, hV, card_image hu, card_divisors hu]
    exact ⟨rfl, rfl⟩

end MetaMathlibExt
