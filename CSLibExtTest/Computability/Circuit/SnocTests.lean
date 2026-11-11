/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Circuit.Snoc
public import Cslib.Computability.Circuit.Boolean.Basic

/-! Tests for `Circuit.snocLine`: its characteristic lemmas over a signature and a carrier in
arbitrary universes, and a concrete De Morgan circuit (CSLib's `Boolean.signature`) extended by
an AND gate, evaluated and measured on every input. -/

namespace Cslib.Circuits

universe u w

/-- Over a signature in any universe, `snocLine` adds one gate and one output, and the new output
is the new gate. -/
example {σ : Signature.{u}} {n k : ℕ} (c : Circuit σ n k) (line : Line σ n c.size) :
    (c.snocLine line).size = c.size + 1 ∧
      (c.snocLine line).outputs (Fin.last k) = .gate (Fin.last c.size) := by
  simp

/-- Over any signature and carrier, the old outputs keep their values and the new output is the
value of the line. -/
example {σ : Signature.{u}} {U : Type w} {n k : ℕ} (c : Circuit σ n k) (line : Line σ n c.size)
    (I : Interpretation σ U) (x : Fin n → U) (t : Fin k) :
    (c.snocLine line).eval I x t.castSucc = c.eval I x t ∧
      (c.snocLine line).eval I x (Fin.last k) = line.eval I x (c.program.eval I x) := by
  simp

/-- The identity circuit on two inputs, extended by an AND gate reading both inputs. -/
private def andOfInputs : Circuit Boolean.signature 2 3 :=
  (Circuit.id Boolean.signature 2).snocLine ⟨.and, fun j => .input j⟩

/-- Its outputs are `a`, `b` and `a && b` on every input `(a, b)`. -/
example : ∀ a b : Bool,
    List.ofFn (andOfInputs.eval Boolean.interpretation fun i => if i.val = 0 then a else b) =
      [a, b, a && b] := by
  decide

/-- One gate; the inputs have depth `0` and the AND gate depth `1`. -/
example : andOfInputs.size = 1 ∧ List.ofFn andOfInputs.outputDepths = [0, 0, 1] := by
  decide

end Cslib.Circuits
