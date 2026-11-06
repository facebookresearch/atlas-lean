/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQStates00
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCacheData

/-! The entire genuine first-root Q action from individually checked
literal source-factor states. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem initial_state (i : Fin 24) :
    generatedAxisGlobalFifthQState00 0 i = qCoordinateGenerator i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24, toAdd (generatedAxisGlobalFifthQState00 0 i).base j =
        toAdd (qCoordinateGenerator i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24, toAdd (generatedAxisGlobalFifthQState00 0 i).coeff =
        toAdd (qCoordinateGenerator i).coeff := by decide +kernel
    exact h i

private theorem final_state (i : Fin 24) :
    generatedAxisGlobalFifthQState00 22 i = generatedAxisGlobalFifthQCache 0 i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24, toAdd (generatedAxisGlobalFifthQState00 22 i).base j =
        toAdd (generatedAxisGlobalFifthQCache 0 i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24, toAdd (generatedAxisGlobalFifthQState00 22 i).coeff =
        toAdd (generatedAxisGlobalFifthQCache 0 i).coeff := by decide +kernel
    exact h i

/-- All twenty-four entire coordinate lifts follow the genuine chronological
source-factor states. -/
theorem generatedAxisGlobalFifthQCache00_actual (i : Fin 24) :
    generatedAxisGlobalFifthChainQImage 0 7 (qCoordinateGenerator i) =
      generatedAxisGlobalFifthQCache 0 i := by
  rw [generatedAxisGlobalFifthQFactors_run]
  let w := generatedAxisGlobalFifthChainQFactors 0 (generatedAxisGlobalFifthActiveStages 0)
  let u := fun j => generatedAxisGlobalFifthQState00 ⟨j % 23, Nat.mod_lt _ (by decide)⟩ i
  have hs : ∀ j (hj : j < w.length),
      generatedAxisGlobalQFactorImage w[j] (u j) = u (j + 1) := by
    intro j hj
    have hj22 : j < 22 := by
      simpa only [w, generatedAxisGlobalFifthQFactor00_length] using hj
    let n : Fin 22 := ⟨j, hj22⟩
    have hl : (⟨j % 23, Nat.mod_lt _ (by decide)⟩ : Fin 23) = Fin.castAdd 1 n := by
      apply Fin.ext
      change j % 23 = j
      exact Nat.mod_eq_of_lt (by omega)
    have hr : (⟨(j + 1) % 23, Nat.mod_lt _ (by decide)⟩ : Fin 23) = Fin.natAdd 1 n := by
      apply Fin.ext
      change (j + 1) % 23 = 1 + j
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    change generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor00 n)
      (generatedAxisGlobalFifthQState00 ⟨j % 23, Nat.mod_lt _ (by decide)⟩ i) =
        generatedAxisGlobalFifthQState00 ⟨(j + 1) % 23, Nat.mod_lt _ (by decide)⟩ i
    rw [hl, hr]
    exact generatedAxisGlobalFifthQStates00_actual n i
  have h := generatedAxisGlobalQFactorRun_states w u hs
  rw [show w.length = 22 from generatedAxisGlobalFifthQFactor00_length] at h
  change generatedAxisGlobalQFactorRun w (generatedAxisGlobalFifthQState00 0 i) =
    generatedAxisGlobalFifthQState00 22 i at h
  rw [initial_state, final_state] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
