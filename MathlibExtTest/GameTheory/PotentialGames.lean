/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Max
public import MathlibExt.GameTheory.PotentialGames

open Finset

/-- Non-vacuity: every finite exact-potential game has a pure Nash
equilibrium (a minimizer of the potential). -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    {c : ι → (∀ i, S i) → ℝ} {Φ : (∀ i, S i) → ℝ}
    (hΦ : IsExactPotential c Φ) : ∃ s, IsPureNash c s := by
  obtain ⟨s, -, hs⟩ := Finset.exists_min_image Finset.univ Φ Finset.univ_nonempty
  exact ⟨s, pureNash_of_min_potential hΦ s (fun t => hs t (Finset.mem_univ t))⟩

/-- The zero game has the constant profile as an equilibrium, by
definition unfolding. -/
example : IsPureNash (fun _ : Fin 2 => fun _ : (∀ _ : Fin 2, Bool) => (0 : ℝ))
    (fun _ => true) := by
  intro i a
  exact le_refl 0
