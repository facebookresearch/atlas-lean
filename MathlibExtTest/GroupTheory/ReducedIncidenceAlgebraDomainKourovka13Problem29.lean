/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ReducedIncidenceAlgebraDomainKourovka13Problem29
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Set.Finite.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.NormNum

/-! # Tests for Cameron's invariant incidence algebra theorem -/

namespace MathlibExtTest.GroupTheory.ReducedIncidenceAlgebraDomainKourovka13Problem29

open MathlibExt.GroupTheory.ReducedIncidenceAlgebraDomainKourovka13Problem29Wanted

private def layers (c : ℚ) (X : Finset ℕ) : ℚ :=
  if X.card = 1 then 1 else if X.card = 2 then c else 0

private theorem bounded (c : ℚ) : IsInA (layers c) :=
  ⟨2, fun X h => by simp [layers, show X.card ≠ 1 by omega, show X.card ≠ 2 by omega]⟩

private theorem invariant (G : Subgroup (Equiv.Perm ℕ)) (c : ℚ) : IsInvariant G (layers c) :=
  fun _ _ X => by simp [layers]

private theorem nonzero (c : ℚ) : layers c ≠ 0 := by
  intro h
  have he := congrFun h {0}
  simp [layers] at he

-- The full symmetric group on the naturals has one infinite orbit.
example : incMul (layers 1) (layers (-1)) ≠ 0 := by
  let G : Subgroup (Equiv.Perm ℕ) := ⊤
  have horbit (x : ℕ) : MulAction.orbit G x = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact ⟨⟨Equiv.swap x y, by simp [G]⟩, Equiv.swap_apply_left x y⟩
  apply invariantIncidenceAlgebraIsDomain_holds ℕ G (fun x => horbit x ▸ Set.infinite_univ)
  exacts [bounded _, invariant _ _, bounded _, invariant _ _, nonzero _, nonzero _]

private theorem sum_singleton_subsets (x : ℕ) (w : Finset ℕ → ℚ) :
    ∑ Y ∈ ({x} : Finset ℕ).powerset, w Y = w ∅ + w {x} := by
  simpa using Finset.sum_powerset_insert (Finset.notMem_empty x) w

-- The contributions of degrees one and two cancel on triples and add on pairs.
example : incMul (layers 1) (layers (-1)) {0, 1, 2} = 0 := by
  norm_num [incMul, Finset.sum_powerset_insert, layers, sum_singleton_subsets,
    Finset.sdiff_insert, Finset.sdiff_singleton_eq_erase, Finset.erase_insert,
    Finset.erase_insert_of_ne]
example : incMul (layers 1) (layers (-1)) {0, 1} = 2 := by
  norm_num [incMul, Finset.sum_powerset_insert, layers, sum_singleton_subsets,
    Finset.sdiff_insert, Finset.sdiff_singleton_eq_erase, Finset.erase_insert,
    Finset.erase_insert_of_ne]

-- A function supported on a single fixed singleton has square zero.
example (a : ℕ) :
    let δ := fun X : Finset ℕ => if X = {a} then (1 : ℚ) else 0
    incMul δ δ = 0 := by
  funext X
  apply Finset.sum_eq_zero
  intro Y hY
  by_cases h : Y = {a}
  · subst Y
    have hn : X \ {a} ≠ {a} := by
      intro he
      have : a ∈ X \ {a} := by rw [he]; simp
      simp at this
    simp [hn]
  · simp [h]

end MathlibExtTest.GroupTheory.ReducedIncidenceAlgebraDomainKourovka13Problem29
