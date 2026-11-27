/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.PartitionMeetingInfiniteCosetsKourovka16Problem43

open MathlibExt.GroupTheory.PartitionMeetingInfiniteCosetsKourovka16Problem43Wanted

-- On an index set of cardinality ℵ₁, the coset with one fixed nonzero coordinate
-- of the kernel of evaluation is proper and meets every color of the same coloring.
example {ι : Type} (hι : Cardinal.mk ι = Cardinal.aleph 1) (a : ι) :
    ∃ c : (ι →₀ ZMod 3) → Fin 3, ∀ i, ∃ f : ι →₀ ZMod 3, f a = 1 ∧ c f = i := by
  classical
  have : Infinite ι := Cardinal.aleph0_le_mk_iff.1 (by
    rw [hι]
    exact Cardinal.aleph0_le_aleph 1)
  let H := (Finsupp.applyAddHom (M := ZMod 3) a).ker
  let J : Set ι := {a}ᶜ
  have hJ : J.Infinite := (Set.finite_singleton a).infinite_compl
  have : Infinite J := Set.infinite_coe_iff.2 hJ
  have hH : (H : Set (ι →₀ ZMod 3)).Infinite := by
    apply Set.infinite_of_injective_forall_mem (f := fun j : J ↦ Finsupp.single (j : ι) 1)
    · intro j k he
      have h := congrArg Finsupp.support he
      apply Subtype.ext
      simpa using h
    · intro j
      have hj : (j : ι) ≠ a := j.2
      change Finsupp.single (j : ι) (1 : ZMod 3) a = 0
      exact Finsupp.single_eq_of_ne hj.symm
  obtain ⟨c, hc⟩ := threePartitionMeetsInfiniteCosets_holds ι hι
  refine ⟨c, fun i ↦ ?_⟩
  obtain ⟨h, hh, hi⟩ := hc H hH (Finsupp.single a 1) i
  have ha : h a = 0 := hh
  exact ⟨Finsupp.single a 1 + h, by simp [Finsupp.add_apply, ha], hi⟩
