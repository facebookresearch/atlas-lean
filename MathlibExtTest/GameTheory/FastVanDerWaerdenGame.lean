/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.FastVanDerWaerdenGame
import Mathlib.Tactic.NormNum

open MetaMathlibExt.FastVanDerWaerdenGame

-- Check both the exact type and the named arguments on the direct import.
example (S : Finset ℚ) (hS : 4 ≤ S.card) (i j i' j' : Fin S.card)
    (h : IsSymmetricOfType S i j) (h' : IsSymmetricOfType S i' j') : i = i' ∧ j = j' :=
  isSymmetricOfType_unique (S := S) (hS := hS) (i := i) (j := j) (i' := i') (j' := j')
    (h := h) (h' := h')

private def four : Finset ℚ := ([0, 1, 2, 4] : List ℚ).toFinset

private theorem four_sort : four.sort = [0, 1, 2, 4] :=
  (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)

-- At the cardinality bound, the type (1, 3) occurs and is unique.
example (i j : Fin four.card) (h : IsSymmetricOfType four i j) :
    i = ⟨1, by decide⟩ ∧ j = ⟨3, by decide⟩ := by
  have hs : IsSymmetricOfType four ⟨1, by decide⟩ ⟨3, by decide⟩ := by
    refine ⟨by decide, 2, 0, by decide, ?_⟩
    simp only [Finset.orderEmbOfFin_apply, four_sort, Fin.getElem_fin]
    decide +kernel
  exact isSymmetricOfType_unique four (by decide) i j _ _ h hs

private def reflected : Finset ℚ := ([0, 2, 3, 4] : List ℚ).toFinset

private theorem reflected_sort : reflected.sort = [0, 2, 3, 4] :=
  (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)

-- Its reflection is instead of type (0, 2), with zero-based indices.
example (i j : Fin reflected.card) (h : IsSymmetricOfType reflected i j) :
    i = ⟨0, by decide⟩ ∧ j = ⟨2, by decide⟩ := by
  have hs : IsSymmetricOfType reflected ⟨0, by decide⟩ ⟨2, by decide⟩ := by
    refine ⟨by decide, 1 / 2, 2, by norm_num, ?_⟩
    simp only [Finset.orderEmbOfFin_apply, reflected_sort, Fin.getElem_fin]
    decide +kernel
  exact isSymmetricOfType_unique reflected (by decide) i j _ _ h hs

private def progression : Finset ℚ := ([0, 1, 2, 3, 4] : List ℚ).toFinset

private theorem progression_sort : progression.sort = [0, 1, 2, 3, 4] :=
  (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)

example (i j : Fin progression.card) (h : IsSymmetricOfType progression i j) :
    i = ⟨0, by decide⟩ ∧ j = ⟨4, by decide⟩ := by
  have hs : IsSymmetricOfType progression ⟨0, by decide⟩ ⟨4, by decide⟩ := by
    refine ⟨by decide, 1, 1, by decide, ?_⟩
    simp only [Finset.orderEmbOfFin_apply, progression_sort, Fin.getElem_fin]
    decide +kernel
  exact isSymmetricOfType_unique progression (by decide) i j _ _ h hs

private def three : Finset ℚ := ([0, 1, 2] : List ℚ).toFinset

private theorem three_sort : three.sort = [0, 1, 2] :=
  (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)

-- Below the bound, deleting the same last element can give two different types.
example : IsSymmetricOfType three ⟨0, by decide⟩ ⟨2, by decide⟩ ∧
    IsSymmetricOfType three ⟨1, by decide⟩ ⟨2, by decide⟩ := by
  refine ⟨⟨by decide, 1, 1, by decide, ?_⟩, ⟨by decide, 2, 0, by decide, ?_⟩⟩ <;>
    simp only [Finset.orderEmbOfFin_apply, three_sort, Fin.getElem_fin] <;> decide +kernel
