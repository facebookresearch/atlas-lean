/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQStates04
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCacheData

/-! The entire genuine root 4 4 Q action from individually checked
literal source-factor states. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem initial_state (i : Fin 24) :
    generatedAxisGlobalFifthQState04 0 i = qCoordinateGenerator i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24, toAdd (generatedAxisGlobalFifthQState04 0 i).base j =
        toAdd (qCoordinateGenerator i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24, toAdd (generatedAxisGlobalFifthQState04 0 i).coeff =
        toAdd (qCoordinateGenerator i).coeff := by decide +kernel
    exact h i

private theorem final_state (i : Fin 24) :
    generatedAxisGlobalFifthQState04 62 i = generatedAxisGlobalFifthQCache 4 i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24, toAdd (generatedAxisGlobalFifthQState04 62 i).base j =
        toAdd (generatedAxisGlobalFifthQCache 4 i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24, toAdd (generatedAxisGlobalFifthQState04 62 i).coeff =
        toAdd (generatedAxisGlobalFifthQCache 4 i).coeff := by decide +kernel
    exact h i

/-- All twenty-four entire coordinate lifts follow the genuine chronological
source-factor states. -/
theorem generatedAxisGlobalFifthQCache04_actual (i : Fin 24) :
    generatedAxisGlobalFifthChainQImage 4 7 (qCoordinateGenerator i) =
      generatedAxisGlobalFifthQCache 4 i := by
  rw [generatedAxisGlobalFifthQFactors_run]
  let w := generatedAxisGlobalFifthChainQFactors 4 (generatedAxisGlobalFifthActiveStages 4)
  let u := fun j => generatedAxisGlobalFifthQState04 ⟨j % 63, Nat.mod_lt _ (by decide)⟩ i
  have hs : ∀ j (hj : j < w.length),
      generatedAxisGlobalQFactorImage w[j] (u j) = u (j + 1) := by
    intro j hj
    have hjBound : j < 62 := by
      simpa only [w, generatedAxisGlobalFifthQFactor04_length] using hj
    let n : Fin 62 := ⟨j, hjBound⟩
    have hl : (⟨j % 63, Nat.mod_lt _ (by decide)⟩ : Fin 63) = Fin.castAdd 1 n := by
      apply Fin.ext
      change j % 63 = j
      exact Nat.mod_eq_of_lt (by omega)
    have hr : (⟨(j + 1) % 63, Nat.mod_lt _ (by decide)⟩ : Fin 63) = Fin.natAdd 1 n := by
      apply Fin.ext
      change (j + 1) % 63 = 1 + j
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    change generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor04 n)
      (generatedAxisGlobalFifthQState04 ⟨j % 63, Nat.mod_lt _ (by decide)⟩ i) =
        generatedAxisGlobalFifthQState04 ⟨(j + 1) % 63, Nat.mod_lt _ (by decide)⟩ i
    rw [hl, hr]
    exact generatedAxisGlobalFifthQStates04_actual n i
  have h := generatedAxisGlobalQFactorRun_states w u hs
  rw [show w.length = 62 from generatedAxisGlobalFifthQFactor04_length] at h
  change generatedAxisGlobalQFactorRun w (generatedAxisGlobalFifthQState04 0 i) =
    generatedAxisGlobalFifthQState04 62 i at h
  rw [initial_state, final_state] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
