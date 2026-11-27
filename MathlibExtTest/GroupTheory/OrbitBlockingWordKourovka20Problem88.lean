/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.OrbitBlockingWordKourovka20Problem88

open FreeGroup MathlibExt.GroupTheory.OrbitBlockingWordKourovka20Problem88Wanted

-- Even for the empty input word in rank one, a blocker must be nonempty.
example : ∃ v : FreeGroup (Fin 1), v.toWord ≠ [] := by
  obtain ⟨v, hv⟩ := existsOrbitBlockingWord_holds 1 le_rfl 1
  have h := hv (MulEquiv.refl _) (by simp [toWord_one])
  exact ⟨v, fun he => h (by simp [he])⟩

-- The same blocker works for all images of a generator under basis permutations.
example : ∃ v : FreeGroup (Fin 2), ∀ i : Fin 2, ¬ v.toWord <:+: [(i, true)] := by
  obtain ⟨v, hv⟩ := existsOrbitBlockingWord_holds 2 (by decide) (of 0)
  refine ⟨v, fun i => ?_⟩
  let e := freeGroupCongr (Equiv.swap 0 i)
  have he : (e (of 0)).toWord = [(i, true)] := by simp [e]
  simpa only [he] using hv e (he ▸ IsCyclicallyReduced.singleton)

-- In rank zero, every candidate occurs in the reduced word of the identity.
example (v : FreeGroup (Fin 0)) : v.toWord <:+: (1 : FreeGroup (Fin 0)).toWord := by
  rw [Subsingleton.elim v 1]
  exact ⟨[], [], by simp⟩
