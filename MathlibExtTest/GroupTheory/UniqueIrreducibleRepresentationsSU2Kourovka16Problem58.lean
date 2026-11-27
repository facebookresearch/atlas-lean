/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.UniqueIrreducibleRepresentationsSU2Kourovka16Problem58
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open MathlibExt.GroupTheory.UniqueIrreducibleRepresentationsSU2Kourovka16Problem58Wanted
open Matrix

-- Dimension zero is excluded even though the representation space has just one subspace.
example {G : Type*} [Group G] (ρ : G →* GL (Fin 0) ℂ) : ¬ IsIrreducibleRep ρ :=
  fun h => (Nat.lt_irrefl 0) h.1

-- Every one-dimensional representation satisfies the invariant-subspace condition.
example {G : Type*} [Group G] (ρ : G →* GL (Fin 1) ℂ) : IsIrreducibleRep ρ := by
  have h : IsSimpleOrder (Submodule ℂ (Fin 1 → ℂ)) :=
    is_simple_module_of_finrank_eq_one (Module.finrank_fin_fun ℂ)
  exact ⟨by decide, fun W _ => h.eq_bot_or_eq_top W⟩

-- The refutation applies to the characterization with both directions spelled out.
example
    (necessary : ∀ (G : Type) [Group G], HasUniqueIrreducibleRepOfEachDim G →
      Nonempty (G ≃* specialUnitaryGroup (Fin 2) ℂ))
    (sufficient : ∀ (G : Type) [Group G], Nonempty (G ≃* specialUnitaryGroup (Fin 2) ℂ) →
      HasUniqueIrreducibleRepOfEachDim G) : False :=
  su2OnlyGroupWithUniqueIrreducibleReps_refuted fun G _ => ⟨necessary G, sufficient G⟩
