/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQStates01
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCacheData

/-! The entire genuine root 1 1 Q action from individually checked
literal source-factor states. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem initial_state (i : Fin 24) :
    generatedAxisGlobalFifthQState01 0 i = qCoordinateGenerator i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24, toAdd (generatedAxisGlobalFifthQState01 0 i).base j =
        toAdd (qCoordinateGenerator i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24, toAdd (generatedAxisGlobalFifthQState01 0 i).coeff =
        toAdd (qCoordinateGenerator i).coeff := by decide +kernel
    exact h i

private theorem final_state (i : Fin 24) :
    generatedAxisGlobalFifthQState01 26 i = generatedAxisGlobalFifthQCache 1 i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24, toAdd (generatedAxisGlobalFifthQState01 26 i).base j =
        toAdd (generatedAxisGlobalFifthQCache 1 i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24, toAdd (generatedAxisGlobalFifthQState01 26 i).coeff =
        toAdd (generatedAxisGlobalFifthQCache 1 i).coeff := by decide +kernel
    exact h i

/-- All twenty-four entire coordinate lifts follow the genuine chronological
source-factor states. -/
theorem generatedAxisGlobalFifthQCache01_actual (i : Fin 24) :
    generatedAxisGlobalFifthChainQImage 1 7 (qCoordinateGenerator i) =
      generatedAxisGlobalFifthQCache 1 i := by
  rw [generatedAxisGlobalFifthQFactors_run]
  let w := generatedAxisGlobalFifthChainQFactors 1 (generatedAxisGlobalFifthActiveStages 1)
  let u := fun j => generatedAxisGlobalFifthQState01 ⟨j % 27, Nat.mod_lt _ (by decide)⟩ i
  have hs : ∀ j (hj : j < w.length),
      generatedAxisGlobalQFactorImage w[j] (u j) = u (j + 1) := by
    intro j hj
    have hjBound : j < 26 := by
      simpa only [w, generatedAxisGlobalFifthQFactor01_length] using hj
    let n : Fin 26 := ⟨j, hjBound⟩
    have hl : (⟨j % 27, Nat.mod_lt _ (by decide)⟩ : Fin 27) = Fin.castAdd 1 n := by
      apply Fin.ext
      change j % 27 = j
      exact Nat.mod_eq_of_lt (by omega)
    have hr : (⟨(j + 1) % 27, Nat.mod_lt _ (by decide)⟩ : Fin 27) = Fin.natAdd 1 n := by
      apply Fin.ext
      change (j + 1) % 27 = 1 + j
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    change generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor01 n)
      (generatedAxisGlobalFifthQState01 ⟨j % 27, Nat.mod_lt _ (by decide)⟩ i) =
        generatedAxisGlobalFifthQState01 ⟨(j + 1) % 27, Nat.mod_lt _ (by decide)⟩ i
    rw [hl, hr]
    exact generatedAxisGlobalFifthQStates01_actual n i
  have h := generatedAxisGlobalQFactorRun_states w u hs
  rw [show w.length = 26 from generatedAxisGlobalFifthQFactor01_length] at h
  change generatedAxisGlobalQFactorRun w (generatedAxisGlobalFifthQState01 0 i) =
    generatedAxisGlobalFifthQState01 26 i at h
  rw [initial_state, final_state] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
