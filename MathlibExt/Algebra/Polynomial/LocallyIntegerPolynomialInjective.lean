/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.LocallyIntegerPolynomial
import Mathlib.Algebra.Polynomial.Roots

/-!
# Injectivity of polynomial evaluation into LIP

## References

* Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
  Article A41, pp. 1–16, Lemma 1.
-/

namespace MetaMathlibExt

/-- **Integer polynomials embed in LIP(U).** For every infinite set $U \subseteq \mathbb{Z}$, the
evaluation map $\mathbb{Z}[x] \to \mathrm{LIP}(U)$, sending $p$ to the function $u \mapsto p(u)$,
is injective: distinct integer polynomials give distinct functions on $U$.

The other part of Lemma 1, that $\mathrm{LIP}(U)$ is a subring of the ring of all functions
$U \to \mathbb{Z}$, holds by construction.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 1 (`integers-2025-A41-lem-1`). -/
public theorem polynomialToLIP_injective {U : Set ℤ} (hU : U.Infinite) :
    Function.Injective (polynomialToLIP U) := by
  intro p q hpq
  apply Polynomial.eq_of_infinite_eval_eq p q
  refine hU.mono ?_
  intro x hx
  change p.eval x = q.eval x
  simpa only [polynomialToLIP_apply] using
    congrArg (fun f : lipSubring U => (f : U → ℤ) ⟨x, hx⟩) hpq

end MetaMathlibExt
