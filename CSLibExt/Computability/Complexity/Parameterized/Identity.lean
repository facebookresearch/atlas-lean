/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.MapFirst
import CSLibExt.Computability.Complexity.PolynomialEncoding.UnaryNat
import CSLibExt.Computability.Complexity.BoolClosure

/-!
# The identity parameterized reduction

In the definition of FPT time a parameter is presented by unary padding. To preserve
its value in an output instance, the machine must emit a binary natural. The existing
unary-count emitter computes the binary word in linear time before the surrounding
input and output framing is restored.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized

open MetaMathlibExt BitstringEncoding ComplexityTheory TM2Program
open Cslib.Complexity Cslib.Complexity.Karp Turing Function

/-- Computing the binary representation of the length of a bitstring is polynomial time. -/
theorem isPolyTime_encodeLength :
    IsPolyTime (fun w : List Bool => bitEncode w.length) := by
  let c := PolynomialEncoding.UnaryNat.component false
  apply Host.isPolyTime_reduction (c := c) (cX := EmitSS.K.A) (cO := EmitSS.K.O)
    (gX := fun _ => EmitSS.U) (start := .emit .hv) (done := .done) (Equiv.refl Bool)
    _ (Polynomial.C 710 * Polynomial.X + Polynomial.C 306) rfl
  intro x
  let S := update (fun k : EmitSS.K => ([] : List (EmitSS.Γ k))) .A (x.map fun _ => EmitSS.U)
  obtain ⟨w, U, hr, ho, _⟩ := PolynomialEncoding.UnaryNat.run_raw x.length [] false S
    (by simp [S, cnt]) (by simp [S]) (by simp [S]) (by simp [S]) (by simp [S])
  exact ⟨w, U, by simpa [c, S, PolynomialEncoding.UnaryNat.component] using hr,
    by change U .O = List.map id _; simpa using ho⟩

/-- The padded parameter can be reconstructed in binary while retaining the instance bits. -/
theorem FPTTime.id : FPTTime (id : List Bool × ℕ → List Bool × ℕ) := by
  let read (p : List Bool × List Bool) := (p.1, p.2.length)
  have hr : IsPolyTime read := by
    apply isPolyTime_of_encodedSnd
    exact isPolyTime_swap.comp ((isPolyTime_mapFirst (β := List Bool) isPolyTime_encodeLength).comp
      isPolyTime_swap)
  exact ⟨_root_.id, Computable.id, read, hr, by simp [read]⟩

/-- Reflexivity of encoded FPT many-one reduction, including writing the output parameter. -/
theorem FPTReduces.refl (P : ParamProblem) : FPTReduces P P :=
  ⟨id, FPTTime.id, id, Computable.id, fun _ _ => ⟨le_rfl, Iff.rfl⟩⟩

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized
