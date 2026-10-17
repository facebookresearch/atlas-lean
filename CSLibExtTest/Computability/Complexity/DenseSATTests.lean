/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.DenseSATVerifier

namespace Cslib.Complexity.DenseSAT

/-! ### Sanity checks: the language is neither trivial nor empty -/

/-- `00` is the single empty clause. -/
example : decodeCNF [false, false] = [[]] := rfl

/-- `10 00 11 00` is `x₀ ∧ ¬x₀`. -/
example : decodeCNF [true, false, false, false, true, true, false, false] =
    [[some true], [some false]] := rfl

/-- The empty clause is unsatisfiable. -/
example : ¬ SAT [false, false] := by
  rintro ⟨a, h⟩
  obtain ⟨j, b, hj, -⟩ := h [] (by simp [decodeCNF, decodeAux])
  simp at hj

/-- `x₀ ∧ ¬x₀` is unsatisfiable. -/
example : ¬ SAT [true, false, false, false, true, true, false, false] := by
  rintro ⟨a, h⟩
  obtain ⟨j₁, b₁, hj₁, ha₁⟩ := h [some true] (by simp [decodeCNF, decodeAux])
  obtain ⟨j₂, b₂, hj₂, ha₂⟩ := h [some false] (by simp [decodeCNF, decodeAux])
  rcases j₁ with _ | j₁ <;> rcases j₂ with _ | j₂ <;> simp at hj₁ hj₂
  subst hj₁ hj₂
  rw [ha₁] at ha₂
  simp at ha₂

/-- `x₀ ∧ (¬x₀ ∨ x₁)` (`10 00 11 10 00`) is satisfiable, by `[true, true]`. -/
example : SAT [true, false, false, false, true, true, true, false, false, false] := by
  refine ⟨[true, true], ?_⟩
  intro c hc
  simp only [decodeCNF, decodeAux, Bool.not_false, Bool.not_true, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨0, true, rfl, rfl⟩
  · exact ⟨1, true, rfl, rfl⟩

/-! ### The certificate check agrees with the semantics on concrete inputs -/

/-- `x₀ ∧ (¬x₀ ∨ x₁)` is accepted with certificate `[true, true]` ... -/
example : check [true, false, false, false, true, true, true, false, false, false]
    [true, true] = true := by decide

/-- ... and rejected with `[true, false]`, which falsifies the second clause. -/
example : check [true, false, false, false, true, true, true, false, false, false]
    [true, false] = false := by decide

/-- A variable beyond the certificate's length satisfies no literal. -/
example : check [true, false, false, false] [] = false := by decide

/-- Round trip of the dense encoding. -/
example : decodeCNF (encodeCNF [[some true, none], [none, some false]]) =
    [[some true, none], [none, some false]] := decodeCNF_encodeCNF _

/-! ### The verifier machine's interface -/

example : Verifier.pairEncode ([true], [false]) = [.inl true, .inr none, .inr (some false)] := rfl

noncomputable example : Turing.TM2ComputableInPolyTime Verifier.pairEncode (fun b : Bool => [b])
    (fun p => check p.1 p.2) := Verifier.verifier

end Cslib.Complexity.DenseSAT
