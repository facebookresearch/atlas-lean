/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual coordinate stabilizers of the independent finite diagonal isometry group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3DiagonalCandidates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationGramIsometryGroup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationFiniteActionUpperBound
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The independent full group of the exact diagonal finite form. -/
def y322Orthogonal3DiagonalGroup : Subgroup (Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) :=
  y322GramIsometryGroup y322Orthogonal3DiagonalGram

/-- A coordinate unit column for the actual matrix action. -/
def y322Orthogonal3DiagonalUnit (i : Fin 7) : Matrix (Fin 7) Unit (ZMod 3) :=
  fun r _ => if r = i then 1 else 0

/-- The actual diagonal isometries fixing every coordinate column at or after dimension d. -/
def y322Orthogonal3DiagonalChain (d : ℕ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) :=
  y322Orthogonal3DiagonalGroup ⊓ fixingSubgroup _
    {v | ∃ i : Fin 7, d ≤ i.val ∧ v = y322Orthogonal3DiagonalUnit i}

/-- Coordinate stabilizer membership means form preservation and fixed later columns. -/
theorem y322Orthogonal3DiagonalChain_mem (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) :
    g ∈ y322Orthogonal3DiagonalChain d ↔
      g ∈ y322Orthogonal3DiagonalGroup ∧
        ∀ i : Fin 7, d ≤ i.val → g • y322Orthogonal3DiagonalUnit i =
          y322Orthogonal3DiagonalUnit i := by
  simp only [y322Orthogonal3DiagonalChain, Subgroup.mem_inf,
    mem_fixingSubgroup_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hg, hf⟩
    exact ⟨hg, fun i hi => hf _ ⟨i, hi, rfl⟩⟩
  · rintro ⟨hg, hf⟩
    exact ⟨hg, fun v ⟨i, hi, hv⟩ => hv ▸ hf i hi⟩

/-- Each coordinate step includes the preceding smaller stabilizer. -/
theorem y322Orthogonal3DiagonalChain_mono : Monotone y322Orthogonal3DiagonalChain := by
  intro d e h g hg
  obtain ⟨hform, hfix⟩ := (y322Orthogonal3DiagonalChain_mem d g).mp hg
  exact (y322Orthogonal3DiagonalChain_mem e g).mpr
    ⟨hform, fun i hi => hfix i (h.trans hi)⟩

/-- With all seven coordinates free the chain is the independent full diagonal isometry group. -/
theorem y322Orthogonal3DiagonalChain_seven :
    y322Orthogonal3DiagonalChain 7 = y322Orthogonal3DiagonalGroup := by
  ext g
  rw [y322Orthogonal3DiagonalChain_mem]
  constructor
  · exact And.left
  · intro hg
    exact ⟨hg, fun i hi => (by omega)⟩

/-- The actual matrix action on a coordinate unit reads the corresponding matrix column. -/
theorem y322Orthogonal3DiagonalUnit_action
    (g : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) (i r : Fin 7) :
    (g • y322Orthogonal3DiagonalUnit i) r () = g.val r i := by
  change (∑ k : Fin 7, g.val r k * (if k = i then 1 else 0)) = g.val r i
  simp

/-- Fixing all coordinate units forces the literal matrix to be the identity. -/
theorem y322Orthogonal3DiagonalChain_zero : y322Orthogonal3DiagonalChain 0 = ⊥ := by
  apply le_antisymm
  · intro g hg
    obtain ⟨_, hfix⟩ := (y322Orthogonal3DiagonalChain_mem 0 g).mp hg
    have heq : g = 1 := by
      apply Units.ext
      ext r i
      have h := congrArg (fun v : Matrix (Fin 7) Unit (ZMod 3) => v r ())
        (hfix i (Nat.zero_le _))
      rw [y322Orthogonal3DiagonalUnit_action] at h
      simpa [y322Orthogonal3DiagonalUnit,
        Matrix.one_apply] using h
    simpa [Subgroup.mem_bot] using heq
  · exact bot_le

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
