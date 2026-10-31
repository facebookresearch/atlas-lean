/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.RNA.Zuker

/-!
# Zuker minimum free energy tests

* A concrete two-pair structure on `GGGAAAUCC` (minimum hairpin `3`): its exterior branch, the
  branches of each pair, the unique closing pair of the inner pair, the unique loop of an
  unpaired position, and its loop-model free energy (one interior loop plus one hairpin).
* A three-pair multiloop: the multiloop energy `a + 2 b + c · 1`.
* Non-vacuity: `LoopEnergy` has a witness, the structure hypotheses hold for a concrete
  structure, and Zuker's minimum free energy can be negative.
* Boundary: on a sequence too short to fold the minimum free energy is `0` (the open chain);
  outside secondary structures (crossing pairs) the unpaired-base count of `loopEnergy`
  truncates to `0`, a junk value.
-/

namespace Cslib.Bioinformatics.RNA.Zuker

open Cslib.Bioinformatics.RNA.Nussinov Cslib.Bioinformatics.RNA.PartitionFunction

/-- RNA bases. -/
inductive Base
  | A | C | G | U
  deriving DecidableEq, Repr

open Base

/-- Watson–Crick and `G–U` wobble complementarity. -/
def wc : Base → Base → Bool
  | A, U | U, A | G, C | C, G | G, U | U, G => true
  | _, _ => false

/-- Complementarity as a relation. -/
abbrev wcP (a b : Base) : Prop := wc a b = true

/-- The sequence `GGGAAAUCC`. -/
def s₀ : List Base := [G, G, G, A, A, A, U, C, C]

/-- A two-pair structure on `s₀`: the stem `(0, 8)` enclosing `(1, 7)`. -/
def P₀ : Finset (ℕ × ℕ) := {(0, 8), (1, 7)}

/-- `P₀` is a secondary structure on `s₀` with minimum hairpin `3`. -/
theorem isStructure_P₀ : IsStructure wcP 3 s₀ P₀ where
  loop := by decide
  compl := by
    change ∀ p ∈ P₀, CanPair wcP s₀ p.1 p.2
    decide
  disjoint := by decide
  noncrossing := by decide

-- The loop decomposition of `P₀`: the exterior branch is `(0, 8)`, its only branch is
-- `(1, 7)`, which closes a hairpin.
example : exteriorBranches P₀ = {(0, 8)} := by decide
example : branches P₀ (0, 8) = {(1, 7)} := by decide
example : branches P₀ (1, 7) = ∅ := by decide

-- The closing pair of `(1, 7)` is `(0, 8)`, as `existsUnique_closing_pair` predicts.
example : (1, 7) ∉ exteriorBranches P₀ ∧ ∃! p, p ∈ P₀ ∧ (1, 7) ∈ branches P₀ p := by
  rcases existsUnique_closing_pair wcP 3 s₀ P₀ isStructure_P₀ (1, 7) (by decide) with h | h
  · exact absurd h.1 (by decide)
  · exact h

-- Position `4` (unpaired) lies in the hairpin closed by `(1, 7)` and in no other loop.
example : ∃! p, p ∈ P₀ ∧ (p.1 < 4 ∧ 4 < p.2) ∧ ∀ q ∈ branches P₀ p, ¬ (q.1 < 4 ∧ 4 < q.2) := by
  rcases existsUnique_loop_of_pos wcP 3 s₀ P₀ isStructure_P₀ 4 with h | h
  · exact absurd (h (1, 7) (by decide)) (by decide)
  · exact h

/-- A loop energy model (non-vacuity witness), with round Turner-like values in kcal/mol. -/
noncomputable def E₀ : LoopEnergy where
  hairpin _ _ := 5.4
  interior _ _ _ _ := -3.3
  multiA := 3.4
  multiB := 0
  multiC := 0.4

-- The free energy of `P₀`: an interior loop (here a stack) closed by `(0, 8)` plus the hairpin
-- closed by `(1, 7)`.
example : freeEnergy E₀ P₀ = -3.3 + 5.4 := by
  have h₁ : branches P₀ (0, 8) = {(1, 7)} := by decide
  have h₂ : branches P₀ (1, 7) = ∅ := by decide
  rw [freeEnergy, P₀, Finset.sum_pair (by decide), ← P₀, loopEnergy_eq_interior E₀ h₁,
    loopEnergy_eq_hairpin E₀ h₂]
  rfl

/-- A multiloop closed by `(0, 10)` with branches `(1, 4)` and `(6, 9)`. -/
def P₁ : Finset (ℕ × ℕ) := {(0, 10), (1, 4), (6, 9)}

-- Multiloop energy: `a + b · 2 + c · u` with `u = 9 - 4 - 4 = 1` unpaired base (position 5).
example (E : LoopEnergy) : loopEnergy E P₁ (0, 10) = E.multiA + E.multiB * 2 + E.multiC * 1 := by
  have h : branches P₁ (0, 10) = {(1, 4), (6, 9)} := by decide
  rw [loopEnergy_eq_multiloop E (by rw [h]; decide), h]
  norm_num

-- Non-vacuity of the minimum: with a negative hairpin energy the minimum free energy is
-- negative, attained by the single pair `(0, 8)`.
example : zukerMFE wcP 3 s₀ { E₀ with hairpin := fun _ _ => -1 } ≤ ((-1 : ℝ) : WithTop ℝ) := by
  have hS : IsStructure wcP 3 s₀ {(0, 8)} :=
    ⟨by decide, by change ∀ p ∈ ({(0, 8)} : Finset (ℕ × ℕ)), CanPair wcP s₀ p.1 p.2; decide,
      by decide, by decide⟩
  rw [zukerMFE_eq_inf]
  refine (Finset.inf_le ((mem_structures wcP 3 s₀ _).mpr hS)).trans (le_of_eq ?_)
  have h : branches {(0, 8)} (0, 8) = ∅ := by decide
  rw [freeEnergy, Finset.sum_singleton, loopEnergy_eq_hairpin _ h]

-- Boundary: `GC` is too short to close a hairpin of size `3`, so the minimum free energy is
-- that of the open chain, `0`.
example (E : LoopEnergy) : zukerMFE wcP 3 [G, C] E = 0 := by
  refine le_antisymm (zukerMFE_le_zero wcP 3 [G, C] E) ?_
  rw [zukerMFE_eq_inf]
  refine Finset.le_inf fun P hP => ?_
  have hP := (mem_structures wcP 3 [G, C] P).mp hP
  have : P = ∅ := Finset.eq_empty_of_forall_notMem fun p hp => by
    have h₁ := hP.loop p hp
    obtain ⟨a, b, -, hb, -⟩ := hP.compl p hp
    have := (List.getElem?_eq_some_iff.mp hb).choose
    simp only [List.length_cons, List.length_nil] at this
    omega
  simp [this, freeEnergy]

-- Junk value outside secondary structures: for the crossing pairs `(1, 3)` and `(2, 4)` inside
-- `(0, 5)` the branch spans `3 + 3` exceed the `4` inner positions, and the unpaired count
-- truncates to `0`.
example (E : LoopEnergy) :
    loopEnergy E {(0, 5), (1, 3), (2, 4)} (0, 5) = E.multiA + E.multiB * 2 + E.multiC * 0 := by
  have h : branches {(0, 5), (1, 3), (2, 4)} (0, 5) = {(1, 3), (2, 4)} := by decide
  rw [loopEnergy_eq_multiloop E (by rw [h]; decide), h]
  norm_num

end Cslib.Bioinformatics.RNA.Zuker
