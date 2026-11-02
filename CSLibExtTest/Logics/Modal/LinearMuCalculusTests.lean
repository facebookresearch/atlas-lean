/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.LinearMuCalculus

/-!
# Linear μ-calculus tests

Closed checks: `F p` holds at `0` when `p` holds at position `2`;
`G p` holds at `0` when `p` holds everywhere; decoding inverts encoding on a
concrete formula; and a closed formula's denotation does not depend on the
environment. Axiom audit follows.
-/

namespace CSLibExtTest.Logics.Modal.LinearMuCalculus

open Cslib.Modal.LinearMuCalculus

example (val : ℕ → Unit → Prop) (hval : val 2 ()) :
    sat val (fun _ _ => False) (F ()) 0 :=
  (F_iff val (fun _ _ => False) () 0).mpr ⟨2, Nat.zero_le 2, hval⟩

example (val : ℕ → Unit → Prop) (hall : ∀ m : ℕ, val m ()) :
    sat val (fun _ _ => False) (G ()) 0 :=
  (G_iff val (fun _ _ => False) () 0).mpr (fun m _ => hall m)

example : linearMuDecode
      (linearMuCode (.mu (.or (.atom 0) (.next (.var 0))) : LinearMuFormula ℕ)) =
    some (.mu (.or (.atom 0) (.next (.var 0)))) :=
  linearMuDecode_linearMuCode _

example : Function.Injective linearMuCode := linearMuCode_injective

example (val : ℕ → Unit → Prop) (env env' : ℕ → ℕ → Prop)
    (h : ∀ n, n < 0 → env n = env' n) :
    sat val env (F ()) = sat val env' (F ()) :=
  sat_closed_env val (F ()) 0 ⟨True.intro, Nat.zero_lt_one⟩ h

#print axioms F_iff
#print axioms G_iff
#print axioms linearMuDecode_linearMuCode

end CSLibExtTest.Logics.Modal.LinearMuCalculus
