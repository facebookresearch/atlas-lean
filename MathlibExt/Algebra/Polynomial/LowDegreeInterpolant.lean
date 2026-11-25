/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.LinearAlgebra.Lagrange

/-!
# Integrality of low-degree interpolants

The main result, `MetaMathlibExt.mem_lifts_of_degree_lt_of_eval_eq`, says that a rational
polynomial of degree less than `|X|` that agrees with an integer polynomial `p` on a finite set
`X` of integers has integer coefficients (Borisov, Lemma 2). The remainder of `p` modulo the
monic polynomial `∏ a ∈ X, (x - a)` is an integer polynomial of degree less than `|X|` with the
same values on `X`, and two polynomials of degree less than `|X|` that agree on `X` are equal.
-/

open Polynomial

namespace MetaMathlibExt

/-- **Integrality of low-degree interpolants.** Let $X \subseteq \mathbb{Z}$ be finite, let
$q \in \mathbb{Q}[x]$ have degree less than $|X|$, and let $p \in \mathbb{Z}[x]$ satisfy
$q(x) = p(x)$ for all $x \in X$. Then $q$ has integer coefficients, that is, $q$ is the image in
$\mathbb{Q}[x]$ of a polynomial in $\mathbb{Z}[x]$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 2 (`integers-2025-A41-lem-2`). -/
public theorem mem_lifts_of_degree_lt_of_eval_eq (X : Finset ℤ) (q : ℚ[X])
    (hq : q.degree < X.card) (p : ℤ[X]) (h : ∀ x ∈ X, q.eval (x : ℚ) = ((p.eval x : ℤ) : ℚ)) :
    q ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
  -- `Lagrange.nodal X id = ∏ a ∈ X, (x - a)` is monic of degree `|X|` and vanishes on `X`.
  have hm : (Lagrange.nodal X id : ℤ[X]).Monic := Lagrange.nodal_monic
  refine (mem_lifts q).2 ⟨p %ₘ Lagrange.nodal X id, ?_⟩
  refine eq_of_degrees_lt_of_eval_index_eq X (v := fun x : ℤ => (x : ℚ))
    Int.cast_injective.injOn ?_ hq fun x hx => ?_
  · calc ((p %ₘ Lagrange.nodal X id).map (Int.castRingHom ℚ)).degree
        ≤ (p %ₘ Lagrange.nodal X id).degree := degree_map_le
      _ < (Lagrange.nodal X id).degree := degree_modByMonic_lt p hm
      _ = X.card := Lagrange.degree_nodal
  · have hmod : (p %ₘ Lagrange.nodal X id).eval x = p.eval x := by
      conv_rhs => rw [← modByMonic_add_div p (Lagrange.nodal X id)]
      rw [eval_add, eval_mul, show (Lagrange.nodal X id).eval x = 0 from
        Lagrange.eval_nodal_at_node (v := id) hx, zero_mul, add_zero]
    rw [h x hx, eval_intCast_map, Int.cast_id, hmod, eq_intCast]

end MetaMathlibExt
