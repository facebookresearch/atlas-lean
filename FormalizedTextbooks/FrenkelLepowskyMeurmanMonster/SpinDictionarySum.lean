/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Summation over the two actual spin coordinates of each source label. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityPairTensor

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Reindex the entire spin space by the source label and its all-one bit. -/
theorem sum_spinDictionary (F : SpinIndex → ℝ) :
    (∑ t, F t) = ∑ d : Fin 2048,
      (F (golayLabelCoefficients ⟨d.val, by omega⟩) +
        F (golayLabelCoefficients ⟨d.val + 2048, by omega⟩)) := by
  let E : Fin 4096 ≃ SpinIndex :=
    Equiv.ofBijective golayLabelCoefficients golayLabelCoefficients_bijective
  calc
    _ = ∑ u : Fin 4096, F (golayLabelCoefficients u) := (E.sum_comp F).symm
    _ = (∑ d : Fin 2048, F (golayLabelCoefficients ⟨d.val, by omega⟩)) +
        ∑ d : Fin 2048, F (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) := by
      have hl : (∑ d : Fin 2048, F (golayLabelCoefficients (Fin.castAdd 2048 d))) =
          ∑ d : Fin 2048, F (golayLabelCoefficients ⟨d.val, by omega⟩) := by
        apply Finset.sum_congr rfl
        intro d _
        apply congrArg (fun u : Fin 4096 => F (golayLabelCoefficients u))
        rfl
      have hh : (∑ d : Fin 2048, F (golayLabelCoefficients (Fin.natAdd 2048 d))) =
          ∑ d : Fin 2048, F (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) := by
        apply Finset.sum_congr rfl
        intro d _
        apply congrArg (fun u : Fin 4096 => F (golayLabelCoefficients u))
        apply Fin.ext
        simp only [Fin.val_natAdd]
        omega
      exact (Fin.sum_univ_add (a := 2048) (b := 2048)
        (fun u => F (golayLabelCoefficients u))).trans
          (congrArg₂ (fun x y : ℝ => x + y) hl hh)
    _ = _ := (Finset.sum_add_distrib).symm

/-- Restricting a spin sum to one source code leaves exactly its two spin coordinates. -/
theorem sum_spinDictionaryCode (d : Fin 2048) (F : SpinIndex → ℝ) :
    (∑ t, if spinDictionaryCode t = d then F t else 0) =
      F (golayLabelCoefficients ⟨d.val, by omega⟩) +
        F (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) := by
  rw [sum_spinDictionary]
  simp only [spinDictionaryCode_low, spinDictionaryCode_high]
  rw [Finset.sum_add_distrib]
  simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
