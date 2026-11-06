/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQStates12
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCacheData

/-! The entire genuine root 12 12 Q action from individually checked
literal source-factor states. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem initial_state (i : Fin 24) :
    generatedAxisGlobalFifthQState12 0 i = qCoordinateGenerator i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24, toAdd (generatedAxisGlobalFifthQState12 0 i).base j =
        toAdd (qCoordinateGenerator i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24, toAdd (generatedAxisGlobalFifthQState12 0 i).coeff =
        toAdd (qCoordinateGenerator i).coeff := by decide +kernel
    exact h i

private theorem final_state (i : Fin 24) :
    generatedAxisGlobalFifthQState12 40 i = generatedAxisGlobalFifthQCache 12 i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24, toAdd (generatedAxisGlobalFifthQState12 40 i).base j =
        toAdd (generatedAxisGlobalFifthQCache 12 i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24, toAdd (generatedAxisGlobalFifthQState12 40 i).coeff =
        toAdd (generatedAxisGlobalFifthQCache 12 i).coeff := by decide +kernel
    exact h i

/-- All twenty-four entire coordinate lifts follow the genuine chronological
source-factor states. -/
theorem generatedAxisGlobalFifthQCache12_actual (i : Fin 24) :
    generatedAxisGlobalFifthChainQImage 12 7 (qCoordinateGenerator i) =
      generatedAxisGlobalFifthQCache 12 i := by
  rw [generatedAxisGlobalFifthQFactors_run]
  let w := generatedAxisGlobalFifthChainQFactors 12 (generatedAxisGlobalFifthActiveStages 12)
  let u := fun j => generatedAxisGlobalFifthQState12 ⟨j % 41, Nat.mod_lt _ (by decide)⟩ i
  have hs : ∀ j (hj : j < w.length),
      generatedAxisGlobalQFactorImage w[j] (u j) = u (j + 1) := by
    intro j hj
    have hjBound : j < 40 := by
      simpa only [w, generatedAxisGlobalFifthQFactor12_length] using hj
    let n : Fin 40 := ⟨j, hjBound⟩
    have hl : (⟨j % 41, Nat.mod_lt _ (by decide)⟩ : Fin 41) = Fin.castAdd 1 n := by
      apply Fin.ext
      change j % 41 = j
      exact Nat.mod_eq_of_lt (by omega)
    have hr : (⟨(j + 1) % 41, Nat.mod_lt _ (by decide)⟩ : Fin 41) = Fin.natAdd 1 n := by
      apply Fin.ext
      change (j + 1) % 41 = 1 + j
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    change generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor12 n)
      (generatedAxisGlobalFifthQState12 ⟨j % 41, Nat.mod_lt _ (by decide)⟩ i) =
        generatedAxisGlobalFifthQState12 ⟨(j + 1) % 41, Nat.mod_lt _ (by decide)⟩ i
    rw [hl, hr]
    exact generatedAxisGlobalFifthQStates12_actual n i
  have h := generatedAxisGlobalQFactorRun_states w u hs
  rw [show w.length = 40 from generatedAxisGlobalFifthQFactor12_length] at h
  change generatedAxisGlobalQFactorRun w (generatedAxisGlobalFifthQState12 0 i) =
    generatedAxisGlobalFifthQState12 40 i at h
  rw [initial_state, final_state] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
