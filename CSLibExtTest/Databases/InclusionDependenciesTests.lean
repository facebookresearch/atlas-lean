/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Databases.InclusionDependencies
import Mathlib.Data.Fin.Rev

/-!
# Tests for inclusion dependencies

The two relations have two and three attributes respectively; all values are natural numbers.
In one instance only a reordered projection succeeds. In another, the target's rows are
constant: either one of the two source values can be matched, but not both by the same row.
-/

namespace Cslib.Databases.InclusionDependenciesTests

private def schema : RelationalSchema where
  Name := Bool
  Attr r := Fin (if r then 3 else 2)
  finite_attr _ := inferInstance

private def xy : Fin 2 ↪ schema.Attr false := Function.Embedding.refl _

private def ab : Fin 2 ↪ schema.Attr true :=
  ⟨Fin.castSucc, fun _ _ h => Fin.ext (congrArg (Fin.val : Fin 3 → ℕ) h)⟩

private def ba : Fin 2 ↪ schema.Attr true := Fin.revPerm.toEmbedding.trans ab

private def forward : IND schema := ⟨false, true, 2, xy, ab⟩
private def backwardCols : IND schema := ⟨false, true, 2, xy, ba⟩

private def ordered : schema.Instance ℕ
  | false => {fun i : Fin 2 => i.val}
  | true => {fun j : Fin 3 => 1 - j.val}

-- The source row is (0,1); the target is (1,0,0).
example : backwardCols.HoldsIn ordered ∧ ¬ forward.HoldsIn ordered := by
  constructor
  · apply (backwardCols.holdsIn_iff_exists_row ordered).2
    rintro _ (rfl : _ = _)
    refine ⟨_, rfl, ?_⟩
    decide
  · intro h
    obtain ⟨_, (rfl : _ = _), he⟩ := (forward.holdsIn_iff_exists_row ordered).1 h _ rfl
    have bad : (0 : ℕ) = 1 := he (0 : Fin 2)
    contradiction

-- A self-inclusion uses the same relation on both sides; an empty source is vacuous.
example : (IND.mk false false 2 xy xy).HoldsIn ordered := IND.holdsIn_refl _ _ _

example (d : IND schema) : d.HoldsIn (V := ℕ) (fun _ => ∅) := by
  apply (d.holdsIn_iff_exists_row _).2
  rintro _ ⟨⟩

private def noColumns {A : Type*} : Fin 0 ↪ A := ⟨Fin.elim0, fun i => i.elim0⟩

private def noTargets : schema.Instance ℕ
  | false => {fun _ => 0}
  | true => ∅

-- Even a zero-column projection requires a target row if the source is inhabited.
example : ¬ (IND.mk false true 0 noColumns noColumns).HoldsIn noTargets := by
  intro h
  obtain ⟨_, hs, _⟩ := (IND.holdsIn_iff_exists_row _ _).1 h _ rfl
  exact hs

private def separated : schema.Instance ℕ
  | false => {fun i : Fin 2 => i.val}
  | true => Set.range fun i : Fin 2 => fun _ : Fin 3 => i.val

-- Each extent is finite even though the type of values is infinite.
private theorem separated_finite : separated.IsFinite := by
  intro R
  cases R
  · exact Set.finite_singleton _
  · exact Set.finite_range _

-- Matching coordinate i to the constant-i row works for every i individually.
example : ∀ t ∈ separated forward.source, ∀ i, ∃ s ∈ separated forward.target,
    t (forward.lhs i) = s (forward.rhs i) := by
  rintro _ (rfl : _ = _) i
  exact ⟨_, ⟨i, rfl⟩, rfl⟩

-- No constant target row has first coordinate 0 and second coordinate 1.
private theorem no_joint_match : ¬ forward.HoldsIn separated := by
  intro h
  obtain ⟨_, ⟨i, rfl⟩, he⟩ := (forward.holdsIn_iff_exists_row separated).1 h _ rfl
  have h₀ : (0 : ℕ) = i.val := he (0 : Fin 2)
  have h₁ : (1 : ℕ) = i.val := he (1 : Fin 2)
  omega

-- A named FD holds on the singleton source, but the IND fails in the same finite instance.
example : ¬ Dependency.FinitelyImplies ℕ {Dependency.functional false (⟨∅, {0}⟩ : FD (Fin 2))}
    (.inclusion forward) := by
  intro h
  apply no_joint_match (h separated separated_finite ?_)
  rintro _ (rfl : _ = _) _ (rfl : _ = _) _ (rfl : _ = _) _ _ _
  rfl

-- The two hypotheses are checked in one instance; unrestricted transitivity restricts to finite ones.
example {S : RelationalSchema} (V : Type*) {R P T : S.Name} {k : ℕ}
    (X : Fin k ↪ S.Attr R) (Y : Fin k ↪ S.Attr P) (Z : Fin k ↪ S.Attr T) :
    Dependency.FinitelyImplies V {.inclusion ⟨R, P, k, X, Y⟩, .inclusion ⟨P, T, k, Y, Z⟩}
      (.inclusion ⟨R, T, k, X, Z⟩) := by
  apply Dependency.finitelyImplies_of_implies
  intro I h
  exact IND.holdsIn_trans (h _ (Set.mem_insert _ _)) (h _ (Set.mem_insert_of_mem _ rfl))

end Cslib.Databases.InclusionDependenciesTests
