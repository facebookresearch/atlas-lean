/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Decidability of WS1S (weak monadic second-order logic of one successor)
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.WS1S.Basic
public import Mathlib.Computability.RE

/-!
# Decidability of WS1S

The syntax, semantics and Gödel numbering of WS1S are in `CSLibExt.Logics.WS1S.Basic`.
-/

@[expose] public section

namespace Cslib.Logic.WS1SWanted

open Cslib.Logic.WS1S

/-- Decidability of WS1S: the set of Gödel codes of WS1S formulas valid under every
assignment is computable. The statement is a `ComputablePred` over `Nat` via the
explicit Gödel numbering `codeWS1S`: a bare `∃ dec : WS1SFormula → Bool` would not
express algorithmic decidability, since classical choice supplies a characteristic
function for every predicate. The standard proof compiles formulas to Büchi automata
over finite words and checks emptiness.
Source: J. R. Büchi, "Weak second-order arithmetic and finite automata", Zeitschrift für
mathematische Logik und Grundlagen der Mathematik 6 (1960), 66-92; see also
W. Thomas, "Languages, Automata, and Logic", in Handbook of Formal Languages, Vol. 3,
Springer, 1997, §7. -/
public theorem_wanted ws1s_decidable :
    ComputablePred (fun n : Nat => ∃ φ : WS1SFormula,
      codeWS1S φ = n ∧ ∀ (v : Nat → Nat) (V : Nat → Finset Nat), φ.Holds v V)

end Cslib.Logic.WS1SWanted
