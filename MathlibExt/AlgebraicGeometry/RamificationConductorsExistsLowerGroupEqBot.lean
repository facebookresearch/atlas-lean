/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FiniteRamificationConductors
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Localization.FractionRing

@[expose] public noncomputable section

/-!
# Termination of the lower ramification filtration

The lower ramification filtration of a finite Galois extension of
nonarchimedean local fields is trivial at some natural-number index.

Authors: Jean-Pierre Serre.
Source: Corps Locaux, Chapter IV, §1;
https://doi.org/10.1007/978-1-4757-5673-9.
-/

open ValuativeRel

universe u v

namespace WantedExt.AlgebraicGeometry.RamificationConductors

open MathlibExt.NumberTheory.FiniteRamificationConductors

/-- The lower ramification filtration of a finite Galois extension of
nonarchimedean local fields terminates: some `G_N` is trivial. -/
public theorem exists_lowerGroup_eq_bot
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (L : Type v) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    [Module.Finite K L] [IsGalois K L] :
    ∃ N : ℕ, lowerGroup K L N = ⊥ := by
  classical
  let : IsNoetherianRing (integerRing L) := inferInstanceAs (IsNoetherianRing 𝒪[L])
  have hsep (σ : DecompositionGroup K L)
      (hσ : ∀ n : ℕ, σ ∈ lowerGroup K L n) : σ = 1 := by
    apply Subtype.ext
    apply AlgEquiv.ext
    have hring : σ.val.toRingHom = RingHom.id L := by
      apply IsFractionRing.ringHom_ext (A := integerRing L)
      intro a
      have hdiff : σ • a - a = 0 := by
        have hmem : σ • a - a ∈
            ⨅ n : ℕ, IsLocalRing.maximalIdeal (integerRing L) ^ n := by
          rw [Ideal.mem_iInf]
          intro n
          exact Ideal.pow_le_pow_right (Nat.le_succ n)
            (by simpa using (mem_lowerGroup_iff K L).mp (hσ n) a)
        simpa only [Ideal.iInf_pow_eq_bot_of_isLocalRing _
          (IsLocalRing.maximalIdeal.isMaximal (integerRing L)).ne_top, Ideal.mem_bot] using hmem
      exact congrArg Subtype.val (sub_eq_zero.mp hdiff)
    intro x
    exact RingHom.congr_fun hring x
  have hex : ∀ σ : DecompositionGroup K L,
      ∃ n : ℕ, σ ∈ lowerGroup K L n → σ = 1 := by
    intro σ
    by_contra! h
    exact (h 0).2 (hsep σ (fun n => (h n).1))
  choose n hn using hex
  obtain ⟨N, hN⟩ := Finite.exists_le n
  refine ⟨N, eq_bot_iff.mpr ?_⟩
  intro σ hσ
  rw [Subgroup.mem_bot]
  exact hn σ (lowerGroup_antitone K L (by exact_mod_cast hN σ) hσ)

end WantedExt.AlgebraicGeometry.RamificationConductors
