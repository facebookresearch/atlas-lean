/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.PartitionRefinement

@[expose] public section

/-- Boundary check: state `1` can move (to itself) while state `0`
cannot move at all, so `0` and `1` are not bisimilar, and
partition refinement agrees at the stabilization round. -/
example : ¬ Bisim (S := Fin 2) (fun a b => a = 1 ∧ b = 1) 0 1 := by
  rintro ⟨R, hR, h01⟩
  obtain ⟨_, hmatch⟩ := hR 0 1 h01
  obtain ⟨a', ha', _⟩ := hmatch 1 ⟨rfl, rfl⟩
  exact absurd ha'.1 (by decide)

/-- Boundary check: on the same system, `1` is bisimilar to itself
witnessed by the equality relation, so refinement keeps `1`
related to itself at the stabilization round. -/
example :
    refineIter (S := Fin 2) (fun a b => a = 1 ∧ b = 1)
      (Fintype.card (Fin 2)) 1 1 := by
  apply bisim_refineIter
  refine ⟨fun a b => a = b, ?_, rfl⟩
  intro a b h
  subst h
  constructor
  · intro a' h'
    exact ⟨a', h', rfl⟩
  · intro b' h'
    exact ⟨b', h', rfl⟩
