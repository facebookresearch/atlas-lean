/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ScottishBook9

open MathlibExt.Combinatorics.ScottishBook9Wanted

-- At bound zero the empty family still has a common element in any nonempty ambient type.
example {α : Type} [Nonempty α] (E : Empty → Finset α) :
    (⋂ i, (E i : Set α)).Nonempty :=
  finiteSetsCommonElement 0 Empty E (fun i ↦ i.elim) (fun s ↦ (s 0).elim)

-- With just two distinct indices, the triple-intersection condition detects disjoint singletons.
example : ¬ ∀ s : Fin (2 + 1) → Bool, (⋂ j, (({s j} : Finset Bool) : Set Bool)).Nonempty := by
  intro h
  obtain ⟨x, hx⟩ := finiteSetsCommonElement 2 Bool (fun i ↦ {i}) (by simp) h
  have hf : x = false := by simpa using Set.mem_iInter.mp hx false
  have ht : x = true := by simpa using Set.mem_iInter.mp hx true
  simp_all
