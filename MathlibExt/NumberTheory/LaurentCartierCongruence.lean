/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
public import MathlibExt.NumberTheory.ConstantTermLinearRepresentation

/-!
# The Rowland–Zeilberger constant-term congruence modulo a prime

Modulo a prime, taking the `p`-th power dilates Laurent exponents by `p` and leaves
coefficients unchanged. This supplies the hypothesis of the prime-power Cartier congruence.
-/

namespace MetaMathlibExt

open AddMonoidAlgebra

/-- **Rowland–Zeilberger congruence.** Let $p$ be a prime and let $P$ and $Q$ be Laurent
polynomials in $r$ variables with integer coefficients. Write $\operatorname{ct}[F]$ for the
constant term of a Laurent polynomial $F$ and $\Lambda_p$ for Kohen's operator, which keeps the
terms whose exponents are all divisible by $p$ and replaces $x^{pj}$ by $x^j$. Then for all
natural numbers $n$ and $k$,
$\operatorname{ct}[P^{pn+k} Q] \equiv \operatorname{ct}[P^n \Lambda_p(P^k Q)] \pmod{p}$.

The exponents $n$ and $k$ are natural numbers; the paper writes "integers", but negative powers
of a general Laurent polynomial are undefined.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 3 (`jis-2026-26.4.2-lem-3`). -/
public theorem constantTerm_pow_mul_modEq_laurentCartier {r p : ℕ} (hp : p.Prime)
    (P Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) (n k : ℕ) :
    (P ^ (p * n + k) * Q).coeff 0 ≡ (P ^ n * laurentCartier p (P ^ k * Q)).coeff 0 [ZMOD p] := by
  let : Fact p.Prime := ⟨hp⟩
  let : CharP (AddMonoidAlgebra (ZMod p) (Fin r → ℤ)) p :=
    charP_of_injective_ringHom (f := singleZeroRingHom) single_right_injective p
  let reduce := mapRingHom (Fin r → ℤ) (Int.castRingHom (ZMod p))
  have hdilate : reduce (P ^ p) = reduce (mapDomain (fun j => p • j) P) := by
    induction P using AddMonoidAlgebra.induction_linear with
    | zero => simp [hp.ne_zero]
    | add F G hF hG =>
      rw [map_pow, map_add, add_pow_char, ← map_pow, ← map_pow, hF, hG, mapDomain_add, map_add]
    | single j c =>
      have hc : (Int.castRingHom (ZMod p) c) ^ p = Int.castRingHom (ZMod p) c :=
        map_intCast (frobenius (ZMod p) p) c
      rw [map_pow, mapDomain_single]
      simp only [reduce, mapRingHom_single, single_pow, hc]
  have hcoeff (j : Fin r → ℤ) : (P ^ p).coeff j ≡
      (mapDomain (fun j => p • j) P).coeff j [ZMOD p] :=
    (ZMod.intCast_eq_intCast_iff _ _ p).1 (congrArg (fun F => F.coeff j) hdilate)
  simpa only [pow_one] using
    constantTerm_tilde_pow_mul_modEq_laurentCartier (a := 1) hp P
      (by simpa only [pow_one] using hcoeff) Q n k

end MetaMathlibExt
