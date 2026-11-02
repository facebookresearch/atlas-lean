/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.LucasSequence

namespace MetaMathlibExt

@[expose] public section

/-- **Subsequences of a second-order linear recurrence.** Let $(P, Q)$ be Lucas sequence
parameters (integers with $Q \ne 0$), let $U_n$ and $V_n$ be the terms of the Lucas sequence
$U(P, Q)$ and of the companion Lucas sequence $V(P, Q)$, and let $(w_n)_{n \ge 0}$ be an integer
sequence with $w_{n+2} = P w_{n+1} - Q w_n$ for every natural number $n$. Then for all natural
numbers $t > 0$ and $r$, the subsequence $w'_n = w_{tn + r}$ satisfies
$w'_{n+2} = V_t w'_{n+1} - Q^t w'_n$ for every natural number $n$, and
$V_t^2 - 4 Q^t = U_t^2 (P^2 - 4Q)$.

The source writes the recurrence as $w_{n+2} = a w_{n+1} + b w_n$,
with subsequence coefficients $a' = V_t$ and $b' = (-1)^{t+1} b^t$ and discriminant
$D(a, b) = a^2 + 4b$; this is the statement above with $P = a$ and $Q = -b$. The source's
identification of the characteristic roots of the new recurrence as $\alpha^t$ and $\beta^t$ is
not part of this statement.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Theorem 2.4 (`integers-2025-A1-thm-2-4`). -/
public theorem_wanted subsequence_secondOrderRecurrence
    (params : LucasSequenceParams) (w : ℕ → ℤ)
    (hw : ∀ n : ℕ, w (n + 2) = params.p * w (n + 1) - params.q * w n)
    (t r : ℕ) (ht : 0 < t) :
    (∀ n : ℕ, w (t * (n + 2) + r)
      = lucasV params t * w (t * (n + 1) + r)
        - params.q ^ t * w (t * n + r)) ∧
    (lucasV params t) ^ 2 - 4 * params.q ^ t
      = (lucasU params t) ^ 2 * (params.p ^ 2 - 4 * params.q)

end

end MetaMathlibExt
