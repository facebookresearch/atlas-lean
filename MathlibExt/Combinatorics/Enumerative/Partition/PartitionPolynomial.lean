/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Combinatorics.Enumerative.Partition.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Partition polynomial.** For a partition $\lambda$ of a natural number $n$ with parts
$\lambda_1, \dots, \lambda_\ell$, listed with multiplicity, the (unnormalized) partition
polynomial of $\lambda$ is $f_\lambda(x) = x^{\lambda_1} + \dots + x^{\lambda_\ell}$, a polynomial
with natural number coefficients.

Source: concept `jis_term_a06e44e4f62cf3639dfdaa73`, source
`jis_source_4a49f53a6c92c67501cd5ea5`. -/
public noncomputable def partitionPolynomial {n : ℕ} (lam : Nat.Partition n) :
    Polynomial ℕ :=
  (lam.parts.map fun a => (Polynomial.X : Polynomial ℕ) ^ a).sum

/-- **Coefficients of the partition polynomial.** For every partition $\lambda$ of a natural
number $n$ and every $j \in \mathbb{N}$, the coefficient of $x^j$ in the partition polynomial
$f_\lambda$ equals the number of parts of $\lambda$ equal to $j$.

Source: concept `jis_term_a06e44e4f62cf3639dfdaa73`, source
`jis_source_4a49f53a6c92c67501cd5ea5`. -/
public theorem coeff_partitionPolynomial {n : ℕ} (lam : Nat.Partition n) (j : ℕ) :
    (partitionPolynomial lam).coeff j = Multiset.count j lam.parts := by
  have key : ∀ t : Multiset ℕ,
      ((Multiset.map (fun b => (Polynomial.X : Polynomial ℕ) ^ b) t).sum).coeff j =
        Multiset.count j t := by
    intro t
    induction t using Multiset.induction with
    | empty => simp
    | cons b t ih =>
      simp [Multiset.map_cons, Multiset.sum_cons, Polynomial.coeff_add,
        Polynomial.coeff_X_pow, Multiset.count_cons, ih, add_comm]
  simpa [partitionPolynomial] using key lam.parts

/-- **The partition polynomial at one.** For every partition $\lambda$ of a natural number $n$,
the value $f_\lambda(1)$ of the partition polynomial $f_\lambda$ at $1$ equals the number of
parts of $\lambda$, counted with multiplicity.

Source: concept `jis_term_a06e44e4f62cf3639dfdaa73`, source
`jis_source_4a49f53a6c92c67501cd5ea5`. -/
public theorem eval_partitionPolynomial_at_one {n : ℕ} (lam : Nat.Partition n) :
    (partitionPolynomial lam).eval 1 = lam.parts.card := by
  have key : ∀ t : Multiset ℕ,
      ((Multiset.map (fun b => (Polynomial.X : Polynomial ℕ) ^ b) t).sum).eval 1 =
        Multiset.card t := by
    intro t
    induction t using Multiset.induction with
    | empty => simp
    | cons b t ih =>
      simp [Multiset.map_cons, Multiset.sum_cons, Polynomial.eval_add,
        Polynomial.eval_pow, Polynomial.eval_X, Multiset.card_cons, ih, add_comm]
  simpa [partitionPolynomial] using key lam.parts

end

end MetaMathlibExt
