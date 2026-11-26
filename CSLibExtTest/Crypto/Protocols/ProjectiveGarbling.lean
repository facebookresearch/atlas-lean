/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Crypto.Protocols.ProjectiveGarbling
import Mathlib.Data.Fin.VecNotation
/-! Tests for projective garbling: physical row layout, fan-out and designation of outputs. -/

namespace Cslib.Crypto.ProjectiveGarbling.Tests

open Cslib.Circuits

variable {K C : Type*} (E : RowCipher K C)

-- The left pointer is complemented, the right is not. Check the actual four ciphertexts,
-- including the key order, for a noncommutative gate; do not assume anything about the cipher.
example (k₀ k₁ l₀ l₁ : K) (out : WireCoins K) :
    garbleGate E (fun a b => a && !b)
      ⟨(fun b => if b then k₁ else k₀), true⟩ ⟨(fun b => if b then l₁ else l₀), false⟩ out =
    ⟨E.enc k₁ l₀ (out.label true), E.enc k₁ l₁ (out.label false),
     E.enc k₀ l₀ (out.label false), E.enc k₀ l₁ (out.label false)⟩ := rfl

private abbrev basis := binaryBasis (Bool → Bool → Bool)

private def line {g : ℕ} (f : Bool → Bool → Bool) (left right : Wire 2 g) : Line basis 2 g :=
  ⟨f, fun i => if i.val = 0 then left else right⟩

-- Gate 0 computes a ∧ ¬b; gate 1 reads gate 0 and a; gate 2 reads both preceding gates.
-- Output 3 is an input wire; outputs 1 and 4 are the same internal wire.
private def fanout : Circuit basis 2 5 :=
  let p₀ := Program.gate .empty (line (fun a b => a && !b) (.input 0) (.input 1))
  let p₁ := p₀.gate (line (fun u a => !u && a) (.gate 0) (.input 0))
  let p₂ := p₁.gate (line (· || ·) (.gate 0) (.gate 1))
  ⟨p₂, ![.gate 2, .gate 0, .gate 1, .input 1, .gate 0]⟩

-- Every sampled garbling has these five outputs for all four assignments. The expected
-- answers are Boolean expressions in the original inputs, not a call to circuit evaluation.
example [Fintype K] [Nonempty K] (d) (hd : d ∈ ((yao E 2 5).garble fanout).support) :
    ∀ a b : Bool, List.ofFn ((yao E 2 5).decode d.decoder
      ((yao E 2 5).eval d.circuit (select d.labels ![a, b]))) =
        [a, a && !b, a && b, b, a && !b] := by
  intro a b
  rw [yao_correct E fanout d hd]
  revert a b
  decide

-- No gates: a designated input wire can still carry a complemented pointer, which must be
-- decoded rather than mistaken for the bit. This tests the concrete construction on fixed coins.
example (keys : Bool → K) (b : Bool) :
    let c := Circuit.id basis 1
    let d := fromCoins E c (fun _ => ⟨keys, true⟩, Fin.elim0)
    ((d.circuit.eval (evalGate E.dec) (select d.labels (fun _ => b)) 0).2 ^^ d.decoder 0) = b := by
  cases b <;> rfl

end Cslib.Crypto.ProjectiveGarbling.Tests
