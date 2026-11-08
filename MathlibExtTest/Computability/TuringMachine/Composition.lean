/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.TuringMachine.Composition

namespace MetaMathlibExt

open Turing TM2Composition ComplexityTheory

/-! A concrete run: the composite of two identity machines on the input `[true, false]`
halts with output `[true, false]` after `1 + 5 + 5 + 1 = 12` steps (run `M₁`, two copy
loops of `2 · 2 + 1` steps each, run `M₂`); after 11 steps it is still at `M₂`'s entry label. -/

/-- The composite of two identity machines on `Bool`. -/
noncomputable abbrev idId : FinTM2 := compTM (idComputer Bool) (idComputer Bool) id

example : ((flip bind idId.step)^[12] (some (initList idId [true, false]))).map
    (fun c => (c.l, (c.stk idId.k₁ : List Bool))) = some (none, [true, false]) :=
  rfl

example : ((flip bind idId.step)^[11] (some (initList idId [true, false]))).map (·.l) =
    some (some (.inr (.inl ()))) :=
  rfl

/-! The identity machine pushes nothing, so the composite time bound is `4n + 4`:
both machines' unit time plus `2n + 1` steps for each copy loop. -/

example : pushBound (idComputer Bool) = 0 := by
  simp [pushBound, idComputer, pushes]

example (n : ℕ) :
    (compTime (idComputableInPolyTime Computability.encodeBool)
      (idComputableInPolyTime Computability.encodeBool)).eval n = 4 * n + 4 := by
  have h : pushBound (idComputer Bool) = 0 := by simp [pushBound, idComputer, pushes]
  simp [compTime, midPoly, idComputableInPolyTime, h]
  omega

/-! Public API. -/

example {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ} {eγ : γ → List γΓ}
    {f : α → β} {g : β → γ} (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) :
    Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) :=
  tm2ComputableInPolyTime_comp h₁ h₂

example {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
    {f : α → β} {g : β → γ} (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (g ∘ f) :=
  hf.comp hg

example {α : Type} [BitstringEncoding α] : IsPolyTime (id ∘ id : α → α) :=
  IsPolyTime.comp ⟨idComputableInPolyTime _⟩ ⟨idComputableInPolyTime _⟩

example {L : DecisionProblem} {f : List Bool → List Bool} (hL : L ∈ P) (hf : IsPolyTime f) :
    L ∘ f ∈ P :=
  comp_mem_P hL hf

end MetaMathlibExt
