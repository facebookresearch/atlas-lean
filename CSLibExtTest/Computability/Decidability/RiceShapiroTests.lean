/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.RiceShapiro

@[expose] public section

/-!
# Tests for the Rice–Shapiro theorem

Both halves re-derive earlier non-recognizability results: upward closure for emptiness, and
finite approximation for totality.
-/

set_option autoImplicit false

open Cslib.Decidability
open Nat.Partrec (Code)

namespace CSLibExtTest.Computability.Decidability.RiceShapiro

/-- Upward closure: the class `{⊥}` is not closed under extensions (the identity extends `⊥`),
so emptiness is not recognizable. -/
example : ¬TM2Recognizable fun c : Code ↦ c.eval ∈ ({fun _ ↦ Part.none} : Set (ℕ →. ℕ)) := by
  intro h
  have hid := rice_shapiro_mono _ h Nat.Partrec.none (Code.exists_code.2 ⟨Code.id, rfl⟩) rfl
    (fun _ y hy ↦ absurd hy (Part.notMem_none y))
  have := congrFun (Set.mem_singleton_iff.mp hid) 0
  simp [Code.eval_id] at this

/-- Finite approximation: no total function has a finite-domain subfunction that is total, so
totality is not recognizable. -/
example : ¬TM2Recognizable fun c : Code ↦ c.eval ∈ {f : ℕ →. ℕ | ∀ n, (f n).Dom} := by
  intro h
  obtain ⟨θ, -, -, hfin, htot⟩ :=
    rice_shapiro_finite _ h (Code.exists_code.2 ⟨Code.id, rfl⟩) (fun n ↦ by simp [Code.eval_id])
  exact Set.infinite_univ (hfin.subset fun n _ ↦ htot n)

/-- A finite graph takes the first value listed at each input. -/
example : 5 ∈ finFun [(0, 5), (0, 6), (2, 7)] 0 ∧ ¬(finFun [(0, 5), (0, 6), (2, 7)] 1).Dom := by
  simp [finFun]

/-- A list with two values at one input is not a graph; one with distinct inputs is. -/
example : ¬IsGraph [(0, 5), (0, 6)] ∧ IsGraph [(0, 5), (2, 7)] := by
  simp [IsGraph, finFun]

/-- Effective sufficiency: the partial recursive members of "outputs `3` on input `0`" are the
extensions of the one graph `[(0, 3)]`, so its index set is recognizable. -/
example : TM2Recognizable fun c : Code ↦ c.eval ∈ {f : ℕ →. ℕ | 3 ∈ f 0} := by
  have hB : TM2Recognizable fun θ : List (ℕ × ℕ) ↦ θ = [(0, 3)] := by
    refine TM2Decidable.tm2Recognizable (tm2Decidable_iff_computablePred.mpr ?_)
    obtain ⟨d, h⟩ : PrimrecPred fun θ : List (ℕ × ℕ) ↦ θ = [(0, 3)] :=
      Primrec.eq.comp Primrec.id (Primrec.const _)
    exact ⟨d, h.to_comp⟩
  refine tm2Recognizable_of_basis _ hB fun f _ ↦ ⟨fun h ↦ ⟨_, rfl, by simpa using h⟩, ?_⟩
  rintro ⟨θ, rfl, hθ⟩
  exact hθ (0, 3) (List.mem_singleton_self _)

/-- Effective necessity, applied to a recognizable class: the graphs of its finite functions form a
recognizable set whose extensions are exactly its partial recursive members. -/
example : ∃ B : List (ℕ × ℕ) → Prop, TM2Recognizable B ∧ (∀ θ, B θ → IsGraph θ) ∧
    ∀ f : ℕ →. ℕ, Nat.Partrec f →
      (f ∈ {f : ℕ →. ℕ | (f 0).Dom} ↔ ∃ θ, B θ ∧ ∀ p ∈ θ, p.2 ∈ f p.1) := by
  refine exists_basis_of_tm2Recognizable _ (tm2Recognizable_iff_rePred.mpr ?_)
  exact (Code.eval_part.comp Computable.id (Computable.const 0)).dom_re

end CSLibExtTest.Computability.Decidability.RiceShapiro
