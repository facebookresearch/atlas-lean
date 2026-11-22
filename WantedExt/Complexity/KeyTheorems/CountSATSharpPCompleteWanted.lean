/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Counting SAT is #P-complete

Source:
L. G. Valiant, "The complexity of enumeration and reliability problems", SIAM Journal on
Computing 8 (1979), 410-421.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.CountSATSharpPComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Counting SAT is #P-complete

Counting the satisfying assignments of a CNF formula, as a function from bitstrings (decoding
to a unary variable count `n` - a bitstring of length `n` - and a CNF formula whose variables
are below `n`, malformed inputs giving `0`), is `#P`-complete. Assignments are functions `Fin n
→ Bool` counted with `Set.ncard`; the matrix is the canonical `Cslib.Logic.PL.CNF`.
-/


/-- The number of satisfying assignments of a CNF formula in `n` variables. -/
noncomputable def countSatFun (x : List Bool) : ℕ :=
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := List Bool × Cslib.Logic.PL.CNF) x with
  | some i =>
    if ∀ clause ∈ i.2, ∀ l ∈ clause, l.1 < i.1.length then
      Set.ncard {a : Fin i.1.length → Bool |
        Cslib.Logic.PL.CNF.Satisfies
          (fun v => if h : v < i.1.length then a ⟨v, h⟩ else false) i.2}
    else 0
  | none => 0

/-- **Counting SAT is #P-complete.** Source: L. G. Valiant, "The complexity of enumeration and
reliability problems", SIAM Journal on Computing 8 (1979), 410-421. -/
public theorem_wanted count_sat_sharpP_complete :
    SharpPComplete countSatFun

end MetaMathlibExt.Complexity.KeyTheorems.CountSATSharpPComplete
