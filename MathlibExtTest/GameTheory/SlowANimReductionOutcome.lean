/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.GameTheory.SlowANimReductionOutcome

namespace MetaMathlibExt

private theorem reduction_eq_sub_of_terminal {n : ℕ} {A : Finset ℕ} {p t : Fin n → ℕ}
    (hterminal : {q | Relation.ReflTransGen (fun x y => y ∈ slowANimMoves A x) p q ∧
      slowANimMoves A q = ∅} = {t}) :
    slowANimReduction A p = fun i => p i - t i := by
  funext i
  simp [slowANimReduction, hterminal, Set.image_singleton]

private theorem reduction_of_one_move {n : ℕ} {A : Finset ℕ} {p t : Fin n → ℕ}
    (hp : slowANimMoves A p = {t}) (ht : slowANimMoves A t = ∅) :
    slowANimReduction A p = fun i => p i - t i := by
  apply reduction_eq_sub_of_terminal
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  refine ⟨fun ⟨hreach, hq⟩ => ?_, fun h => ?_⟩
  · rcases hreach.cases_head with rfl | ⟨r, hr, hrq⟩
    · rw [hp] at hq
      simp at hq
    · have : r = t := by simpa [hp] using hr
      subst r
      exact (Relation.reflTransGen_iff_eq (by simp [ht])).mp hrq
  · subst q
    exact ⟨.single (by simp [hp]), ht⟩

-- The height-five stack has four unplayable tokens. Both positions have one move and are N.
example : ¬ SpragueGrundy.IsP (slowANimGame 2 {2}) ![5, 1] := by
  have heq : slowANimReduction {2} ![5, 1] = slowANimReduction {2} ![1, 1] := by
    rw [reduction_of_one_move (t := ![4, 0]) (by decide) (by decide),
      reduction_of_one_move (t := ![0, 0]) (by decide) (by decide)]
    decide
  rw [slowANim_isP_iff_of_reduction_eq 2 {2} (by decide) _ _ heq]
  intro h
  exact (SpragueGrundy.isP_iff (slowANimGame 2 {2}) ![1, 1]).mp h (fun _ => 0)
    (show (fun _ : Fin 2 => 0) ∈ slowANimMoves {2} ![1, 1] by decide) (slowANim_isP_zero 2 {2})

-- With no allowed move size, a nonzero position reduces to the all-zero P-position.
example : SpragueGrundy.IsP (slowANimGame 2 ∅) ![3, 5] := by
  have hred (p : Fin 2 → ℕ) : slowANimReduction ∅ p = fun _ => 0 := by
    have hempty (q : Fin 2 → ℕ) : slowANimMoves ∅ q = ∅ := by simp [slowANimMoves]
    have heq : slowANimReduction ∅ p = fun i => p i - p i := by
      apply reduction_eq_sub_of_terminal
      ext t
      simp [hempty, Relation.reflTransGen_iff_eq]
    simpa only [Nat.sub_self] using heq
  apply (slowANim_isP_iff_of_reduction_eq 2 ∅ (by simp) _ (fun _ => 0) (by rw [hred, hred])).2
  exact slowANim_isP_zero 2 ∅

-- No stack labels are available, so equality of reductions is vacuous.
example (p q : Fin 0 → ℕ) :
    SpragueGrundy.IsP (slowANimGame 0 ∅) p ↔ SpragueGrundy.IsP (slowANimGame 0 ∅) q :=
  slowANim_isP_iff_of_reduction_eq 0 ∅ (by simp) p q (Subsingleton.elim _ _)

end MetaMathlibExt
