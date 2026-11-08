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

/-- Subsequences of a second-order linear recurrence are again
second-order: if `w (n + 2) = P * w (n + 1) - Q * w n` for all `n`,
then for positive `t` and any shift `r` the subsequence
`n ↦ w (t * n + r)` satisfies the recurrence with coefficients
`V_t` and `Q ^ t`, and the discriminants are related by
`V_t ^ 2 - 4 * Q ^ t = U_t ^ 2 * (P ^ 2 - 4 * Q)`, where `U` and `V`
are the Lucas sequences `lucasU` and `lucasV` for the parameters.

The paper writes the recurrence as `w_{n+2} = a w_{n+1} + b w_n`
with subsequence coefficients `a' = v_t(a, b)` and
`b' = (-1) ^ (t + 1) * b ^ t` and discriminant
`D(a, b) = a ^ 2 + 4 * b`; this is the same statement in the
repository convention `P = a`, `Q = -b` (so `b' = -Q ^ t` in the
`signed` position). The paper's sentence identifying the new
characteristic roots as `α ^ t` and `β ^ t` is not formalized.

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
