/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Preference.UtilityRepresentation

@[expose] public section

/-!
# Ordinal invariance of utility representations and choice (Atlas EC01.T03)

Source: J. Levin and P. Milgrom, *Introduction to Choice Theory*, Stanford Econ 202 notes (2004),
§4 (Utility): after Definition 5 (if `u` represents `≿` then
`C(B; ≿) = {x | x solves max_{y ∈ B} u(y)}`) and after Proposition 4 (if `u` represents `≿`, then
`U(·) = v(u(·))` also represents `≿` so long as `v : ℝ → ℝ` is increasing; here strictly
increasing).
-/

namespace MathlibExt.Economics

/-- Utility-maximizing choice from the menu `B`: the maximizers of `u` on `B`. -/
def utilityChoice {α : Type*} (u : α → ℝ) (B : Set α) : Set α :=
  {x | x ∈ B ∧ ∀ y ∈ B, u y ≤ u x}

/-- A strictly increasing transformation of a representation is again a representation. -/
theorem Preference.Represents.comp_strictMono {α : Type*} {P : Preference α} {u : α → ℝ}
    (hu : P.Represents u) {f : ℝ → ℝ} (hf : StrictMono f) : P.Represents (f ∘ u) := by
  intro x y
  simp only [Function.comp_apply]
  exact (hu x y).trans (hf.le_iff_le.symm)

/-- A strictly increasing transformation does not change utility-maximizing choice sets. -/
theorem utilityChoice_comp_strictMono {α : Type*} (u : α → ℝ) {f : ℝ → ℝ} (hf : StrictMono f)
    (B : Set α) : utilityChoice (f ∘ u) B = utilityChoice u B := by
  ext x
  simp only [utilityChoice, Set.mem_ofPred_eq, Function.comp_apply, hf.le_iff_le]

/-- If `u` represents `P`, the choice rule of `P` is utility maximization (Levin–Milgrom, §4). -/
theorem Preference.Represents.choice_eq_utilityChoice {α : Type*} {P : Preference α}
    {u : α → ℝ} (hu : P.Represents u) (B : Set α) : P.choice B = utilityChoice u B := by
  ext x
  simp only [Preference.choice, utilityChoice, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hB, h⟩
    exact ⟨hB, fun y hy => (hu x y).mp (h y hy)⟩
  · rintro ⟨hB, h⟩
    exact ⟨hB, fun y hy => (hu x y).mpr (h y hy)⟩

end MathlibExt.Economics
