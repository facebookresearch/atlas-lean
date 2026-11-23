/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.Canonical
public import CSLibExt.Computability.Machines.Turing.SingleTape.PolyTime
public import CSLibExt.Computability.Machines.Turing.Universal.CodeTimeSingleTape

/-!
# Unconditional CodeTime inclusion in canonical single-tape decision time

The step-for-step machine `Code.singleTapeTM` can leave dirty cells left of its answer head.
`Code.canonicalSingleTapeTM` follows its marked simulation with the counted cleanup of
`SingleTapeTM.canonicalComputer`. On every binary input it has the same answer, now on a clean
one-cell tape, within `canonicalTime t n = 4 * t n + 2 * n + 10` steps.

`exists_canonicalDecider_of_mem_codeTime` is the unconditional class result: every language in
`CodeTime t` has a finite-alphabet single-tape decider with an injective bit embedding and this
explicit bound, using the repository's actual `OutputsWithinTime` decision shape.
`codeTime_subset_singleTapeP_of_le_polynomial` transfers polynomially bounded `t` into the
existing `SingleTapeP`, with the displayed polynomial `4 * p + 2 * X + 10`.

This is deliberately not `TimeComputable`: that structure specifies the output on *every*
word of the full tape alphabet, whereas `CodeTime` and `SingleTapeP` specify all binary words
embedded in a finite working alphabet. No hypothesis about nonbinary runs is added or inferred.
-/

@[expose] public section

set_option autoImplicit false

open Relation MetaMathlibExt.ComplexityTheory

namespace Cslib.Turing.Universal

open Cslib.Turing.SingleTapeTM

/-- The proved overhead of canonical simulation and cleanup for the time bound `t`. -/
def canonicalTime (t : ℕ → ℕ) (n : ℕ) : ℕ := 4 * t n + 2 * n + 10

namespace Code

/-- A code's existing single-tape machine with visited markers and canonical tape cleanup. -/
abbrev canonicalSingleTapeTM (c : Code) :
    SingleTapeTM (Canonical.Symbol (NonBlank (Fin c.symBound))) :=
  c.singleTapeTM.canonicalComputer

/-- The same bit embedding as `inputSym`, carried into the marked alphabet. -/
def canonicalInputSym (c : Code) (b : Bool) : Canonical.Symbol (NonBlank (Fin c.symBound)) :=
  Canonical.embed (c.inputSym b)

/-- Distinct input and answer bits remain distinct in the canonical machine. -/
theorem canonicalInputSym_injective (c : Code) : Function.Injective c.canonicalInputSym :=
  Canonical.embed_injective.comp c.inputSym_injective

/-- Every deciding code has canonical outputs on every binary input, without any clean-left
assumption. The `+1` source halting transition is included in the explicit overhead. -/
theorem DecidesWithin.outputsWithinTime_canonicalSingleTapeTM {c : Code} {L : DecisionProblem}
    {t : ℕ → ℕ} (h : c.DecidesWithin L t) (x : List Bool) :
    c.canonicalSingleTapeTM.OutputsWithinTime (x.map c.canonicalInputSym)
      [c.canonicalInputSym (L x)] (canonicalTime t x.length) := by
  obtain ⟨left, -, hrun⟩ := h.exists_relatesWithinSteps_singleTapeTM x
  have hr := canonicalComputer_outputsHeadWithinTime c.singleTapeTM hrun rfl rfl
  have hinput : (x.map c.inputSym).map Canonical.embed = x.map c.canonicalInputSym := by
    rw [List.map_map]
    rfl
  rw [hinput] at hr
  simp only [List.length_map] at hr
  convert hr using 1
  · rfl
  · simp only [canonicalTime]
    omega

end Code

/-- **Unconditional canonical decision-time inclusion.** Every problem in `CodeTime t` is
computed on every binary word by an existing CSLib single-tape machine over a finite alphabet,
with an injective bit embedding, a blank left and right half-tape, and the answer under the
halting head, within `4 * t n + 2 * n + 10` steps. No new complexity class is introduced. -/
theorem exists_canonicalDecider_of_mem_codeTime {L : DecisionProblem} {t : ℕ → ℕ}
    (h : L ∈ CodeTime t) :
    ∃ (Γ : Type) (_ : Inhabited Γ) (_ : Fintype Γ) (ι : Bool → Γ),
      Function.Injective ι ∧ ∃ tm : SingleTapeTM Γ,
        ∀ w : List Bool, tm.OutputsWithinTime (w.map ι) [ι (L w)]
          (4 * t w.length + 2 * w.length + 10) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨_, inferInstance, inferInstance, c.canonicalInputSym, c.canonicalInputSym_injective,
    c.canonicalSingleTapeTM, hc.outputsWithinTime_canonicalSingleTapeTM⟩

/-- **Polynomially bounded CodeTime is contained in the existing SingleTapeP.** The source time
need not be monotone or computable; only its stated domination by `p.eval` is used. The witness's
polynomial is exactly `4 * p + 2 * X + 10`. -/
theorem codeTime_subset_singleTapeP_of_le_polynomial {t : ℕ → ℕ} (p : Polynomial ℕ)
    (ht : ∀ n, t n ≤ p.eval n) : CodeTime t ⊆ Cslib.Complexity.SingleTapeP := by
  intro L hL
  obtain ⟨c, hc⟩ := hL
  refine ⟨_, inferInstance, inferInstance, c.canonicalInputSym, c.canonicalInputSym_injective,
    c.canonicalSingleTapeTM, 4 * p + 2 * Polynomial.X + 10, fun w ↦ ?_⟩
  refine RelatesWithinSteps.mono ?_ (hc.outputsWithinTime_canonicalSingleTapeTM w)
  simp only [canonicalTime, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  gcongr
  exact ht w.length

/-- In particular, CodeTime at any natural-coefficient polynomial is contained in SingleTapeP. -/
theorem codeTime_polynomial_subset_singleTapeP (p : Polynomial ℕ) :
    CodeTime (fun n ↦ p.eval n) ⊆ Cslib.Complexity.SingleTapeP :=
  codeTime_subset_singleTapeP_of_le_polynomial p fun _ ↦ le_rfl

end Cslib.Turing.Universal
