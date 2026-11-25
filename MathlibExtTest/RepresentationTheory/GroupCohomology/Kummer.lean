/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.GroupCohomology.Kummer

@[expose] public section

open groupCohomology

-- Source consumer with the original binders (`Type`, not `Type*`).
example (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {n : ℕ}
    (hμ : (primitiveRoots n K).Nonempty)
    (hcomm : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ)
    (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ n = 1) :
    Nat.card (L ≃ₐ[K] L)
      = Nat.card (Kummer.powerSubgroup K L n ⧸
          ((powMonoidHom n : Kˣ →* Kˣ).range).subgroupOf
            (Kummer.powerSubgroup K L n)) :=
  Kummer.natCard_algEquiv_eq_natCard_powerSubgroup_quotient hμ hcomm hexp

-- Characterization consumer: `1` lies in the power subgroup, and a unit
-- of `K` lies in it exactly when it becomes an `n`-th power in `L`.
example : (1 : ℚˣ) ∈ Kummer.powerSubgroup ℚ ℚ 2 :=
  Kummer.mem_powerSubgroup_iff.2 ⟨1, by simp⟩

example (a : ℚˣ) :
    a ∈ Kummer.powerSubgroup ℚ ℚ 2 ↔
      ∃ α : ℚˣ, algebraMap ℚ ℚ (a : ℚ) = (α : ℚ) ^ 2 :=
  Kummer.mem_powerSubgroup_iff

-- Nontrivial instance: the trivial extension `ℚ/ℚ` at `n = 1`, where
-- the Galois group is trivial and `1` is a primitive first root of unity.
example : Nat.card (ℚ ≃ₐ[ℚ] ℚ)
    = Nat.card (Kummer.powerSubgroup ℚ ℚ 1 ⧸
        ((powMonoidHom 1 : ℚˣ →* ℚˣ).range).subgroupOf
          (Kummer.powerSubgroup ℚ ℚ 1)) := by
  apply Kummer.natCard_algEquiv_eq_natCard_powerSubgroup_quotient
    (K := ℚ) (L := ℚ) (n := 1)
  · exact ⟨1, by simp [IsPrimitiveRoot.primitiveRoots_one]⟩
  · intro σ τ
    exact Subsingleton.elim _ _
  · intro σ
    exact Subsingleton.elim _ _
