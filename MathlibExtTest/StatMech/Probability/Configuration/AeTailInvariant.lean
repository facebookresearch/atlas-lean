/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Configuration.AeTailInvariant
public import MathlibExt.Probability.Percolation.TranslationInvariance

/-!
# Tests for `MathlibExt.Probability.Configuration.AeTailInvariant`

* `ati_invariant_aeTail` in a nontrivial model: `E = ℤ` with the translation action of
  `Multiplicative ℤ`, windows `[-k, k]`, and the fair Bernoulli product measure (translation
  invariant by `StatMech.Percolation.bernoulli_translationInvariant`). The escape hypothesis
  (every finite set can be translated outside every window) is proved, so every invariant event
  is a.e. a tail event.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal
open StatMech StatMech.ConfigSpace

namespace MathlibExtTest.StatMech.Probability.Configuration.AeTailInvariant

/-- The windows `[-k, k]`. -/
def window (k : ℕ) : Set ℤ := Set.Icc (-(k : ℤ)) k

theorem window_mono : Monotone window := fun j k h => by
  have : (j : ℤ) ≤ k := by exact_mod_cast h
  exact Set.Icc_subset_Icc (by omega) (by omega)

theorem escape (F : Finset ℤ) (k : ℕ) : ∃ g : Multiplicative ℤ,
    (↑(F.image (fun e => g⁻¹ • e)) : Set ℤ) ⊆ (window k)ᶜ := by
  refine ⟨Multiplicative.ofAdd ((k : ℤ) + 1 + ∑ e ∈ F, |e|), ?_⟩
  intro x hx
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
  obtain ⟨e, he, rfl⟩ := hx
  have h1 : |e| ≤ ∑ e ∈ F, |e| :=
    Finset.single_le_sum (f := fun e : ℤ => |e|) (fun _ _ => abs_nonneg _) he
  have h2 := le_abs_self e
  simp only [window, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le]
  left
  change -((k : ℤ) + 1 + ∑ e ∈ F, |e|) + e < -(k : ℤ)
  linarith

example : ∀ s : Set (ConfigSpace ℤ), MeasurableSet s →
    (∀ g : Multiplicative ℤ, shift g ⁻¹' s = s) →
    ∃ s' : Set (ConfigSpace ℤ), AtiTailEvent window s' ∧
      s =ᵐ[bernoulliProductMeasure (E := ℤ) (2⁻¹ : ℝ≥0) (by norm_num)] s' :=
  ati_invariant_aeTail window window_mono escape
    (StatMech.Percolation.bernoulli_translationInvariant (G := Multiplicative ℤ) _ _)

end MathlibExtTest.StatMech.Probability.Configuration.AeTailInvariant
