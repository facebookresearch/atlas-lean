/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Decidability.Degrees

@[expose] public section

set_option autoImplicit false

namespace Cslib.OracleEvalnPrimrecWanted

/-- **The finite oracle evaluator is primitive recursive**: for every
primitive recursive oracle `o`, the fuel-bounded evaluation
`oracleEvaln o` is primitive recursive in `(fuel, code, input)`. The
numbering side is now proved in `Degrees.lean` (`Primcodable OracleCode`,
`primrec_encodeOracleCode`, `primrec_decodeOracleCode`,
`primrec_oracleCodeOfNat`, `computable_oracleCodeOfNat`), so this statement
is well-formed in Mathlib's `Primrec` sense; what is not yet proved is the
evaluator itself, whose proof needs the two-dimensional course-of-values
table argument (fuel × code, as in Mathlib's `Nat.Partrec.Code.primrec_evaln`,
which has no OracleCode analogue yet). The proved companion
`oracleEvaln_bound` (fuel bounds the accepted inputs) is in `Degrees.lean`.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, §2 (oracle
computations); Rogers, *Theory of Recursive Functions and Effective
Computability*, §1.6 (Gödel numberings; decoding). -/
theorem_wanted oracleEvaln_primrec :
  ∀ {o : ℕ → Option ℕ} (ho : Primrec o),
    Primrec fun a : (ℕ × Cslib.Decidability.OracleCode) × ℕ =>
      Cslib.Decidability.oracleEvaln o a.1.1 a.1.2 a.2

end Cslib.OracleEvalnPrimrecWanted
