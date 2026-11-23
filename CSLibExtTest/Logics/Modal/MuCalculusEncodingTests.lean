/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.MuCalculusEncoding

/-!
# Modal μ-calculus encoding tests

Closed checks: decoding inverts encoding on a concrete formula, for both the
Nat code and the token-list encoding (whose `box^3` example uses 4 tokens,
not an exponentially long code), the encoding is injective, `EF` is closed,
and a closed formula's denotation does not depend on the environment. Axiom
audit follows.
-/

namespace CSLibExtTest.Logics.Modal.MuCalculusEncoding

open Cslib.Modal.MuCalculus

/-- The two-world model `0 → 1`, `1 → 1`, with the atom true only at `1`. -/
def chain2 : Cslib.Modal.KripkeModel (Fin 2) Unit :=
  ⟨⟨0⟩, fun w v => (w = 0 ∧ v = 1) ∨ (w = 1 ∧ v = 1), fun w _ => w = 1⟩

example : muDecode (muCode (.mu (.or (.atom 0) (.dia (.var 0))) : MuFormula ℕ)) =
    some (.mu (.or (.atom 0) (.dia (.var 0)))) :=
  muDecode_muCode _

example : Function.Injective muCode := muCode_injective

example : muDecodeList
      (muTokens (.box (.box (.box (.atom 0))) : MuFormula ℕ)) =
    some (.box (.box (.box (.atom 0)))) :=
  muDecodeList_muTokens _

/-- `box^3 (atom 0)` uses 4 tokens: token length is linear, not exponential. -/
example : (muTokens (.box (.box (.box (.atom 0))) : MuFormula ℕ)).length = 4 :=
  rfl

example : MuFormula.ClosedAt 0 (EF ()) := ⟨True.intro, Nat.zero_lt_one⟩

example (env env' : ℕ → Fin 2 → Prop) (h : ∀ n, n < 0 → env n = env' n) :
    sat chain2 env (EF ()) = sat chain2 env' (EF ()) :=
  sat_closed_env chain2 (EF ()) 0 ⟨True.intro, Nat.zero_lt_one⟩ h

#print axioms muDecode_muCode
#print axioms muDecodeList_muTokens
#print axioms sat_closed_env

end CSLibExtTest.Logics.Modal.MuCalculusEncoding
