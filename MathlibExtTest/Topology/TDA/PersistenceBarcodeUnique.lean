/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.TDA.PersistenceBarcodeUnique
import Mathlib.Analysis.Real.Cardinality

open CategoryTheory Limits MathlibExt.Topology.PersistenceModuleWanted MathlibExt.Topology.TDA

/-- The multiplicity of a bar is an isomorphism invariant: two copies of `[0, 1]` are not one. -/
example :
    let I (_ : Bool) : Set ℝ := Set.Icc 0 1
    let J (_ : Unit) : Set ℝ := Set.Icc 0 1
    let hI : ∀ i, (I i).Nonempty ∧ (I i).OrdConnected :=
      fun _ => ⟨⟨0, le_rfl, zero_le_one⟩, Set.ordConnected_Icc⟩
    let hJ : ∀ j, (J j).Nonempty ∧ (J j).OrdConnected :=
      fun _ => ⟨⟨0, le_rfl, zero_le_one⟩, Set.ordConnected_Icc⟩
    IsEmpty ((∐ fun i => intervalModule ℚ (I i) (hI i).2) ≅
      ∐ fun j => intervalModule ℚ (J j) (hJ j).2) := by
  intro I J hI hJ
  refine ⟨fun e => ?_⟩
  obtain ⟨σ, -⟩ := intervalModule_decomposition_unique ℚ I J hI hJ e
  simpa using Fintype.card_congr σ

/-- The barcode sees whether a bar is closed or open at its end: `[0, 1]` is not `[0, 1)`. -/
example :
    let I (_ : Unit) : Set ℝ := Set.Icc 0 1
    let J (_ : Unit) : Set ℝ := Set.Ico 0 1
    let hI : ∀ i, (I i).Nonempty ∧ (I i).OrdConnected :=
      fun _ => ⟨⟨0, le_rfl, zero_le_one⟩, Set.ordConnected_Icc⟩
    let hJ : ∀ j, (J j).Nonempty ∧ (J j).OrdConnected :=
      fun _ => ⟨⟨0, le_rfl, zero_lt_one⟩, Set.ordConnected_Ico⟩
    IsEmpty ((∐ fun i => intervalModule ℚ (I i) (hI i).2) ≅
      ∐ fun j => intervalModule ℚ (J j) (hJ j).2) := by
  intro I J hI hJ
  refine ⟨fun e => ?_⟩
  obtain ⟨σ, hσ⟩ := intervalModule_decomposition_unique ℚ I J hI hJ e
  have h : (1 : ℝ) ∈ J (σ ()) := by
    rw [hσ ()]
    exact ⟨zero_le_one, le_rfl⟩
  exact lt_irrefl _ h.2

/-- Interval modules of distinct intervals are not isomorphic: apply the uniqueness of the
barcode to one-term sums. -/
example (e : intervalModule ℚ (Set.Icc (0 : ℝ) 1) Set.ordConnected_Icc ≅
    intervalModule ℚ (Set.Icc (0 : ℝ) 2) Set.ordConnected_Icc) : False := by
  have hI : ∀ _ : Unit, (Set.Icc (0 : ℝ) 1).Nonempty ∧ (Set.Icc (0 : ℝ) 1).OrdConnected :=
    fun _ => ⟨⟨0, le_rfl, zero_le_one⟩, Set.ordConnected_Icc⟩
  have hJ : ∀ _ : Unit, (Set.Icc (0 : ℝ) 2).Nonempty ∧ (Set.Icc (0 : ℝ) 2).OrdConnected :=
    fun _ => ⟨⟨0, le_rfl, zero_le_two⟩, Set.ordConnected_Icc⟩
  obtain ⟨σ, hσ⟩ := intervalModule_decomposition_unique ℚ (fun _ => Set.Icc (0 : ℝ) 1)
    (fun _ => Set.Icc (0 : ℝ) 2) hI hJ
    (coproductUniqueIso (fun _ : Unit => intervalModule ℚ (Set.Icc (0 : ℝ) 1) (hI ()).2) ≪≫ e ≪≫
      (coproductUniqueIso fun _ : Unit => intervalModule ℚ (Set.Icc (0 : ℝ) 2) (hJ ()).2).symm)
  have h : (2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    rw [← hσ ()]
    exact ⟨zero_le_two, le_rfl⟩
  norm_num at h

/-- Infinite multiplicities are invariants too: countably many copies of the ray `[0, ∞)` are not
uncountably many. -/
example :
    let I (_ : ℕ) : Set ℝ := Set.Ici 0
    let J (_ : ℝ) : Set ℝ := Set.Ici 0
    let hI : ∀ i, (I i).Nonempty ∧ (I i).OrdConnected :=
      fun _ => ⟨⟨0, le_rfl⟩, Set.ordConnected_Ici⟩
    let hJ : ∀ j, (J j).Nonempty ∧ (J j).OrdConnected :=
      fun _ => ⟨⟨0, le_rfl⟩, Set.ordConnected_Ici⟩
    IsEmpty ((∐ fun i => intervalModule ℚ (I i) (hI i).2) ≅
      ∐ fun j => intervalModule ℚ (J j) (hJ j).2) := by
  intro I J hI hJ
  refine ⟨fun e => ?_⟩
  obtain ⟨σ, -⟩ := intervalModule_decomposition_unique ℚ I J hI hJ e
  have : Countable ℝ := σ.symm.injective.countable
  exact Cardinal.not_countable_real (Set.countable_univ_iff.2 this)
