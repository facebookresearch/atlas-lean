/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQStates08
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCacheData

/-! The entire genuine root 8 8 Q action from individually checked
literal source-factor states. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem initial_state (i : Fin 24) :
    generatedAxisGlobalFifthQState08 0 i = qCoordinateGenerator i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24, toAdd (generatedAxisGlobalFifthQState08 0 i).base j =
        toAdd (qCoordinateGenerator i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24, toAdd (generatedAxisGlobalFifthQState08 0 i).coeff =
        toAdd (qCoordinateGenerator i).coeff := by decide +kernel
    exact h i

private theorem final_state (i : Fin 24) :
    generatedAxisGlobalFifthQState08 60 i = generatedAxisGlobalFifthQCache 8 i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24, toAdd (generatedAxisGlobalFifthQState08 60 i).base j =
        toAdd (generatedAxisGlobalFifthQCache 8 i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24, toAdd (generatedAxisGlobalFifthQState08 60 i).coeff =
        toAdd (generatedAxisGlobalFifthQCache 8 i).coeff := by decide +kernel
    exact h i

/-- All twenty-four entire coordinate lifts follow the genuine chronological
source-factor states. -/
theorem generatedAxisGlobalFifthQCache08_actual (i : Fin 24) :
    generatedAxisGlobalFifthChainQImage 8 7 (qCoordinateGenerator i) =
      generatedAxisGlobalFifthQCache 8 i := by
  rw [generatedAxisGlobalFifthQFactors_run]
  let w := generatedAxisGlobalFifthChainQFactors 8 (generatedAxisGlobalFifthActiveStages 8)
  let u := fun j => generatedAxisGlobalFifthQState08 ⟨j % 61, Nat.mod_lt _ (by decide)⟩ i
  have hs : ∀ j (hj : j < w.length),
      generatedAxisGlobalQFactorImage w[j] (u j) = u (j + 1) := by
    intro j hj
    have hjBound : j < 60 := by
      simpa only [w, generatedAxisGlobalFifthQFactor08_length] using hj
    let n : Fin 60 := ⟨j, hjBound⟩
    have hl : (⟨j % 61, Nat.mod_lt _ (by decide)⟩ : Fin 61) = Fin.castAdd 1 n := by
      apply Fin.ext
      change j % 61 = j
      exact Nat.mod_eq_of_lt (by omega)
    have hr : (⟨(j + 1) % 61, Nat.mod_lt _ (by decide)⟩ : Fin 61) = Fin.natAdd 1 n := by
      apply Fin.ext
      change (j + 1) % 61 = 1 + j
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    change generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor08 n)
      (generatedAxisGlobalFifthQState08 ⟨j % 61, Nat.mod_lt _ (by decide)⟩ i) =
        generatedAxisGlobalFifthQState08 ⟨(j + 1) % 61, Nat.mod_lt _ (by decide)⟩ i
    rw [hl, hr]
    exact generatedAxisGlobalFifthQStates08_actual n i
  have h := generatedAxisGlobalQFactorRun_states w u hs
  rw [show w.length = 60 from generatedAxisGlobalFifthQFactor08_length] at h
  change generatedAxisGlobalQFactorRun w (generatedAxisGlobalFifthQState08 0 i) =
    generatedAxisGlobalFifthQState08 60 i at h
  rw [initial_state, final_state] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
