/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Identities and Hadamard products of generalized sequences

Statement from Vladimir V. Kruchinin and Maria Y. Perminova,
"Identities and Hadamard Product of the Generalized Fibonacci,
Lucas, Catalan, and Harmonic Numbers", *Journal of Integer
Sequences* 28 (2025), Article 25.8.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Perminova/perm3.html>).

The paper's generalized Fibonacci and Lucas numbers have
generating functions `x / (1 - a x - b x ^ 2)` and
`(2 - a x) / (1 - a x - b x ^ 2)`, so they are the Lucas
sequences `U(P, Q)` and `V(P, Q)` with `P = a` and `Q = -b`,
here `MetaMathlibExt.lucasU` and `MetaMathlibExt.lucasV`.
Note this is only an integer specialization of the paper's
Proposition 1: the paper allows real parameters `a, b`
(cf. `MetaMathlibExt.AbGeneralizedFibonacciSequence`),
whereas `LucasSequenceParams` requires integer `P, Q`
with `Q ≠ 0`, i.e. integer `a` and nonzero integer `b`.
The identity below was verified
numerically for `(P, Q)` among seven sample pairs and
`m, n ≤ 12`.

Not stated (see the source audit table): Theorem 2 (the
sequences `p_n` and `T_{n-i, i}` are not defined in the
extracted statements), Theorem 3 (a Hadamard product of
generating functions involving `log`), and Corollaries 4
and 5 (whose nested-radical generating functions are not
reliably parenthesized in the extraction).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.LucasSequence

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted

/-- **Proposition 1** (integer specialization): for the
generalized Fibonacci numbers `F_n` and Lucas numbers
`L_n` with integer parameters `a` and nonzero integer
`b` (the paper allows real `a, b`),
`2 F_{m + n} = F_m L_n + L_m F_n`.

Source: Vladimir V. Kruchinin and Maria Y. Perminova,
"Identities and Hadamard Product of the Generalized
Fibonacci, Lucas, Catalan, and Harmonic Numbers",
Proposition 1. -/
theorem_wanted two_mul_lucasU_add
    (params : MetaMathlibExt.LucasSequenceParams) (m n : ℕ) :
    2 * MetaMathlibExt.lucasU params (m + n) =
      MetaMathlibExt.lucasU params m * MetaMathlibExt.lucasV params n +
        MetaMathlibExt.lucasV params m * MetaMathlibExt.lucasU params n

end MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted
