/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Four distinct absolute coordinates chosen from the actual norm-eight shapes. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightShapes
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Signed four-coordinate rows used by the concrete three-bases reduction. -/
def leechNormEightTargetRows : Fin 8 → Fin 4 → ℤ :=
  ![![8, 0, 0, 0], ![6, 2, 2, 2], ![4, -4, -4, -4], ![4, 4, 2, -2],
    ![4, 2, 2, 2], ![2, -2, -2, -2], ![5, 3, 1, 1], ![3, 3, 3, -1]]

theorem leechNormEightTargetRows_natAbs_le (s : Fin 8) (j : Fin 4) :
    (leechNormEightTargetRows s j).natAbs ≤ 8 := by
  revert s j
  decide +kernel

/-- Each requested row uses no more coordinates of any magnitude than its shape supplies. -/
theorem leechNormEightTargetRows_demand (s : Fin 8) (k : Fin 9) :
    (Finset.univ.filter fun j => (leechNormEightTargetRows s j).natAbs = k.val).card ≤
      leechNormEightShapeCounts s k := by
  revert s k
  decide +kernel

/-- Fiber cardinal bounds yield an injective coordinate selection with prescribed labels. -/
theorem leechNormEight_select_of_fiber_counts (a : Fin 4 → ℕ) (b : Fin 24 → ℕ)
    (hc : ∀ k : ℕ, (Finset.univ.filter fun j => a j = k).card ≤
      (Finset.univ.filter fun i => b i = k).card) :
    ∃ f : Fin 4 → Fin 24, Function.Injective f ∧ ∀ j, b (f j) = a j := by
  classical
  have he (k : ℕ) : Nonempty ({j : Fin 4 // a j = k} ↪ {i : Fin 24 // b i = k}) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_subtype] using hc k)
  let e (k : ℕ) : {j : Fin 4 // a j = k} ↪ {i : Fin 24 // b i = k} :=
    Classical.choice (he k)
  let E : Fin 4 ↪ Fin 24 := (Equiv.sigmaFiberEquiv a).symm.toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl ℕ) e).trans
      (Equiv.sigmaFiberEquiv b).toEmbedding)
  exact ⟨E, E.injective, fun j => (e (a j) ⟨j, rfl⟩).property⟩

/-- The shape hypothesis itself supplies the required four distinct absolute coordinates. -/
theorem leechNormEight_select_target_coordinates (u : Fin 24 → ℤ) (s : Fin 8)
    (hshape : leechNormEightMultiplicity u = leechNormEightShapeCounts s) :
    ∃ f : Fin 4 → Fin 24, Function.Injective f ∧
      ∀ j, (u (f j)).natAbs = (leechNormEightTargetRows s j).natAbs := by
  apply leechNormEight_select_of_fiber_counts
    (fun j => (leechNormEightTargetRows s j).natAbs) (fun i => (u i).natAbs)
  intro k
  by_cases hk : k < 9
  · have hc := leechNormEightTargetRows_demand s ⟨k, hk⟩
    have hs := congrFun hshape ⟨k, hk⟩
    change (Finset.univ.filter fun i => (u i).natAbs = k).card = _ at hs
    exact hc.trans_eq hs.symm
  · have hz : (Finset.univ.filter fun j => (leechNormEightTargetRows s j).natAbs = k) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have he := (Finset.mem_filter.mp hj).2
      have hb := leechNormEightTargetRows_natAbs_le s j
      omega
    rw [hz, Finset.card_empty]
    exact Nat.zero_le _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
