/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.TokThen
public import CSLibExt.Computability.Complexity.Karp.ThreeSatEmit
public import CSLibExt.Computability.Complexity.Karp.ThreeSatCorrect
public import CSLibExt.Computability.Complexity.SatVerifierTM

/-!
# 3SAT is NP-complete

The SAT-to-3SAT reduction `reduce3` (spec `Karp.ThreeSat`) is polynomial-time: the SAT tokenizer
followed by the emitter `Emit3` (`TokThen.isPolyTime_out`). With `satDec_eq_sat3Dec_reduce3` it
is a polynomial-time many-one reduction from `satDec`, so `sat3Dec` is NP-hard; with
`SatVerifier.Machine.sat3Dec_mem_NP` it is NP-complete (`sat3Dec_npComplete`).

`polyManyOneRed_trans` and `npHard_of_polyManyOneRed` are the general facts used to chain
reductions.
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL MetaMathlibExt.ComplexityTheory

/-- Polynomial-time many-one reductions compose. -/
theorem polyManyOneRed_trans {L₁ L₂ L₃ : DecisionProblem} (h₁ : PolyManyOneRed L₁ L₂)
    (h₂ : PolyManyOneRed L₂ L₃) : PolyManyOneRed L₁ L₃ := by
  obtain ⟨f, hf, e₁⟩ := h₁
  obtain ⟨g, hg, e₂⟩ := h₂
  exact ⟨g ∘ f, IsPolyTime.comp hf hg, fun x => (e₁ x).trans (e₂ (f x))⟩

/-- NP-hardness transfers along a polynomial-time many-one reduction. -/
theorem npHard_of_polyManyOneRed {L L' : DecisionProblem}
    (hL : ∀ A : DecisionProblem, A ∈ NP → PolyManyOneRed A L) (h : PolyManyOneRed L L') :
    ∀ A : DecisionProblem, A ∈ NP → PolyManyOneRed A L' :=
  fun A hA => polyManyOneRed_trans (hL A hA) h

instance (k : Emit3.K) : Fintype (Emit3.Γ k) := by cases k <;> infer_instance

/-- The 3SAT emitter as an `Emitter`. -/
abbrev emit3 : Emitter where
  K := Emit3.K
  Γ := Emit3.Γ
  L := Emit3.Lab
  prog := Emit3.prog
  start := Emit3.start
  done := .done
  start_ne_done := by decide
  prog_done := rfl
  cT := .T
  cO := .O
  cT_ne_cO := by decide
  iT := Equiv.refl _
  eO := Equiv.refl _
  g φ := encodeCNF (to3 φ)
  noOut := []
  B n := 8 * (n + 1) ^ 2
  B_mono a b h := by dsimp only; gcongr
  run φ v St hT hO h0 := by
    obtain ⟨v', S', r, h⟩ := Emit3.run φ [] v St (by simpa using hT) hO h0
    exact ⟨v', S', r, by simpa using h⟩

theorem out_emit3 (x : List Bool) : TokThen.out emit3 x = reduce3 x := by
  unfold TokThen.out reduce3
  cases decodeCNF x <;> rfl

/-- The emitter's stacks, listed. -/
def emit3Ks : List Emit3.K := [.T, .O, .U, .Z, .W, .C]

/-- **`reduce3` is polynomial-time**. -/
theorem isPolyTime_reduce3 : IsPolyTime reduce3 := by
  have h := TokThen.isPolyTime_out emit3 emit3Ks (by decide) (fun k => by cases k <;> decide)
    (Polynomial.C 8 * (Polynomial.X + 1) ^ 2 + Polynomial.C 2 * Polynomial.X + Polynomial.C 3)
    (fun n => by simp [emit3]; omega)
  rwa [show TokThen.out emit3 = reduce3 from funext out_emit3] at h

/-- SAT reduces to 3SAT in polynomial time. -/
theorem satDec_polyManyOneRed_sat3Dec : PolyManyOneRed satDec sat3Dec :=
  ⟨reduce3, isPolyTime_reduce3, satDec_eq_sat3Dec_reduce3⟩

/-- **3SAT is NP-hard**. -/
theorem sat3Dec_npHard : ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L sat3Dec :=
  npHard_of_polyManyOneRed Cslib.Complexity.CookLevin.Hardness.satDec_npHard
    satDec_polyManyOneRed_sat3Dec

/-- **3SAT is NP-complete** for formal-math's canonical `NP`. -/
theorem sat3Dec_npComplete :
    sat3Dec ∈ NP ∧ ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L sat3Dec :=
  ⟨SatVerifier.Machine.sat3Dec_mem_NP, sat3Dec_npHard⟩

end Cslib.Complexity.Karp
