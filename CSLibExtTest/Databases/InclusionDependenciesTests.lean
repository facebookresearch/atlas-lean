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

/-! ### The separating example of finite implication -/

open FiniteImplication in
-- The counter-models must be infinite: on a finite instance the first theorem would apply.
example : ¬ descending.IsFinite := by
  intro h
  exact not_holdsIn_indBA_descending (finitelyImplies_indBA ℕ descending h descending_holdsIn_deps)

open FiniteImplication in
example : ¬ descendingWithLoop.IsFinite := by
  intro h
  exact not_holdsIn_fdBA_descendingWithLoop
    (finitelyImplies_fdBA ℕ descendingWithLoop h descendingWithLoop_holdsIn_deps)

private def onlyRow : FiniteImplication.schema.Instance ℕ := fun _ => {![0, 1]}

private def fork : FiniteImplication.schema.Instance ℕ := fun _ => {![0, 0], ![0, 1]}

open FiniteImplication in
-- Both hypotheses are needed: the functional dependency alone fails on one row (0, 1).
example : ¬ Dependency.FinitelyImplies ℕ {fdAB} (.inclusion indBA) := by
  intro h
  have hfin : onlyRow.IsFinite := fun R => Set.finite_singleton _
  have hFD : fdAB.HoldsIn onlyRow := by
    change (⟨{0}, {1}⟩ : FD (Fin 2)).HoldsIn (onlyRow ())
    intro t ht u hu _ a _
    have ht' : t = ![0, 1] := Set.mem_singleton_iff.mp ht
    have hu' : u = ![0, 1] := Set.mem_singleton_iff.mp hu
    rw [ht', hu']
  have hcon : indBA.HoldsIn onlyRow := h onlyRow hfin (by rintro _ (rfl : _ = _); exact hFD)
  have hmem : ![0, 1] ∈ onlyRow () := Set.mem_singleton_iff.mpr rfl
  rw [indBA.holdsIn_iff_exists_row onlyRow] at hcon
  obtain ⟨s, hs, he⟩ := hcon _ hmem
  obtain rfl : s = ![0, 1] := Set.mem_singleton_iff.mp hs
  have h10 : (1 : ℕ) = 0 := he (0 : Fin 1)
  exact one_ne_zero h10

open FiniteImplication in
-- The inclusion dependency alone fails on the rows (0, 0) and (0, 1).
example : ¬ Dependency.FinitelyImplies ℕ {.inclusion indAB} (.inclusion indBA) := by
  intro h
  have hfin : fork.IsFinite := fun R => (Set.finite_singleton _).insert _
  have hIND : indAB.HoldsIn fork := by
    have hmem0 : ![0, 0] ∈ fork () := Set.mem_insert_iff.mpr (Or.inl rfl)
    rw [indAB.holdsIn_iff_exists_row fork]
    intro t ht
    rcases Set.mem_insert_iff.mp ht with rfl | hmem_t
    · refine ⟨_, hmem0, ?_⟩
      simp only [indAB, Fin.forall_fin_one]
      decide
    · obtain rfl : t = ![0, 1] := Set.mem_singleton_iff.mp hmem_t
      refine ⟨_, hmem0, ?_⟩
      simp only [indAB, Fin.forall_fin_one]
      decide
  have hcon : indBA.HoldsIn fork :=
    h fork hfin (by rintro _ (rfl : _ = _); exact hIND)
  have hmem1 : ![0, 1] ∈ fork () :=
    Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
  rw [indBA.holdsIn_iff_exists_row fork] at hcon
  obtain ⟨s, hs, he⟩ := hcon _ hmem1
  rcases Set.mem_insert_iff.mp hs with rfl | hmem_s
  · have h10 : (1 : ℕ) = 0 := he (0 : Fin 1)
    exact one_ne_zero h10
  · obtain rfl : s = ![0, 1] := Set.mem_singleton_iff.mp hmem_s
    have h10 : (1 : ℕ) = 0 := he (0 : Fin 1)
    exact one_ne_zero h10

end Cslib.Databases.InclusionDependenciesTests
