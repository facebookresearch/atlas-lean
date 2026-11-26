/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FiniteStateFreeProduct
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Set.Finite.Basic

/-! # Tests for finite-state actions of free products -/

namespace MathlibExtTest.GroupTheory.FiniteStateFreeProduct

open MathlibExt.GroupTheory.FiniteStateFreeProductKourovka16Problem85Wanted

private def letterwise (d : ℕ) : Equiv.Perm (Fin d) →* Equiv.Perm (List (Fin d)) where
  toFun := Equiv.listEquivOfEquiv
  map_one' := by
    apply Equiv.ext
    intro w
    exact List.map_id w
  map_mul' g h := by
    apply Equiv.ext
    intro w
    change w.map (g ∘ h) = (w.map h).map g
    rw [List.map_map]

-- The same permutation acts at every vertex, including the root.
private theorem letterwise_action {d : ℕ} (hd : 2 ≤ d) :
    ActsFaithfullyByFiniteStateAuts (Equiv.Perm (Fin d)) := by
  refine ⟨d, letterwise d, hd, ?_, fun g => ⟨?_, ?_⟩⟩
  · intro g h eqn
    apply Equiv.ext
    intro x
    exact List.singleton_inj.mp (congrArg (fun p : Equiv.Perm (List (Fin d)) => p [x]) eqn)
  · intro u v
    simp [letterwise, Equiv.listEquivOfEquiv]
  · apply (Set.finite_singleton (List.map g)).subset
    rintro _ ⟨u, rfl⟩
    apply Set.mem_singleton_iff.mpr
    funext w
    simp [treeSection, letterwise, Equiv.listEquivOfEquiv, List.map_append]

-- Both factors act nontrivially, on alphabets of different cardinalities.
example : ActsFaithfullyByFiniteStateAuts
    (Monoid.Coprod (Equiv.Perm (Fin 2)) (Equiv.Perm (Fin 3))) :=
  finiteStateFreeProduct_holds _ _ (letterwise_action (by decide)) (letterwise_action (by decide))

-- This permutation preserves lengths but moves a child without moving its parent.
example : ¬ IsTreeAut (Equiv.swap ([0, 0] : List (Fin 2)) [1, 0]) := by
  intro h
  have hp := (h [0] [0]).2
  simp [Equiv.swap_apply_def] at hp

end MathlibExtTest.GroupTheory.FiniteStateFreeProduct
