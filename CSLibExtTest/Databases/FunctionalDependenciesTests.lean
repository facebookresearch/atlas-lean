/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.FunctionalDependencies
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.List.FinRange

/-!
# Tests for functional dependencies

The schema `R(A, B, C, D)` (attributes `0, 1, 2, 3`) with `F = {AB → C, C → D, D → A}`.
* The closure algorithm: `AB⁺ = ABCD`, `C⁺ = ACD`, `B⁺ = B`.
* Derivability is decided through the closure: `C → A` and `BD → C` are derivable, `A → B` is
  not; the closure witness for `A` satisfies `F` and violates `A → B`.
* The candidate keys are `AB`, `BC` and `BD`; `ABC` is a superkey but not a candidate key;
  `findKey` returns `BD`.
-/

@[expose] public section

namespace Cslib.Databases.FunctionalDependenciesTests

open Cslib.Databases

/-- `F = {AB → C, C → D, D → A}` over `A, B, C, D = 0, 1, 2, 3`. -/
def F : Finset (FD (Fin 4)) := {⟨{0, 1}, {2}⟩, ⟨{2}, {3}⟩, ⟨{3}, {0}⟩}

example : attrClosure F {0, 1} = Finset.univ := by decide
example : attrClosure F {2} = {0, 2, 3} := by decide
example : attrClosure F {1} = {1} := by decide

example : Derives F ⟨{2}, {0}⟩ := by decide
example : Derives F ⟨{1, 3}, {2}⟩ := by decide
example : ¬ Derives F ⟨{0}, {1}⟩ := by decide

/-- A derivation by hand: `C → D` and `D → A` give `C → A` by transitivity. -/
example : Derives F ⟨{2}, {0}⟩ :=
  Derives.trans (Y := {3}) (Derives.mem (by decide)) (Derives.mem (by decide))

/-- The closure witness for `A` satisfies `F` but not `A → B`, so `A → B` is not entailed. -/
example : ¬ (FD.HoldsIn ⟨{0}, {1}⟩ (↑(closureWitnessRelation F {0}) : Set (Fin 4 → Bool))) := by
  intro h
  have := h (fun _ => true) (by simp [closureWitnessRelation])
    (fun a => decide (a ∈ attrClosure F {0})) (by simp [closureWitnessRelation])
    (fun b hb => by simp at hb; subst hb; decide) 1 (by decide)
  revert this
  decide

example : ¬ Entails F ⟨{0}, {1}⟩ := fun h => absurd (derives_iff_entails.mpr h) (by decide)

example : IsCandidateKey F {0, 1} := by decide
example : IsCandidateKey F {1, 2} := by decide
example : IsCandidateKey F {1, 3} := by decide
example : IsSuperkey F {0, 1, 2} ∧ ¬ IsCandidateKey F {0, 1, 2} := by decide
example : ¬ IsSuperkey F {0, 2, 3} := by decide

example : findKey F (List.finRange 4) = {1, 3} := by decide

example : IsCandidateKey F (findKey F (List.finRange 4)) :=
  findKey_isCandidateKey F (List.mem_finRange)

end Cslib.Databases.FunctionalDependenciesTests
