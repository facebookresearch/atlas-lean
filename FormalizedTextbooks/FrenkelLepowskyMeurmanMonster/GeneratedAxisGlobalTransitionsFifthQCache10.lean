/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQStates10
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCacheData

/-! The entire genuine root 10 10 Q action from individually checked
literal source-factor states. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem initial_state (i : Fin 24) :
    generatedAxisGlobalFifthQState10 0 i = qCoordinateGenerator i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24, toAdd (generatedAxisGlobalFifthQState10 0 i).base j =
        toAdd (qCoordinateGenerator i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24, toAdd (generatedAxisGlobalFifthQState10 0 i).coeff =
        toAdd (qCoordinateGenerator i).coeff := by decide +kernel
    exact h i

private theorem final_state (i : Fin 24) :
    generatedAxisGlobalFifthQState10 99 i = generatedAxisGlobalFifthQCache 10 i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24, toAdd (generatedAxisGlobalFifthQState10 99 i).base j =
        toAdd (generatedAxisGlobalFifthQCache 10 i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24, toAdd (generatedAxisGlobalFifthQState10 99 i).coeff =
        toAdd (generatedAxisGlobalFifthQCache 10 i).coeff := by decide +kernel
    exact h i

/-- All twenty-four entire coordinate lifts follow the genuine chronological
source-factor states. -/
theorem generatedAxisGlobalFifthQCache10_actual (i : Fin 24) :
    generatedAxisGlobalFifthChainQImage 10 7 (qCoordinateGenerator i) =
      generatedAxisGlobalFifthQCache 10 i := by
  rw [generatedAxisGlobalFifthQFactors_run]
  let w := generatedAxisGlobalFifthChainQFactors 10 (generatedAxisGlobalFifthActiveStages 10)
  let u := fun j => generatedAxisGlobalFifthQState10 ⟨j % 100, Nat.mod_lt _ (by decide)⟩ i
  have hs : ∀ j (hj : j < w.length),
      generatedAxisGlobalQFactorImage w[j] (u j) = u (j + 1) := by
    intro j hj
    have hjBound : j < 99 := by
      simpa only [w, generatedAxisGlobalFifthQFactor10_length] using hj
    let n : Fin 99 := ⟨j, hjBound⟩
    have hl : (⟨j % 100, Nat.mod_lt _ (by decide)⟩ : Fin 100) = Fin.castAdd 1 n := by
      apply Fin.ext
      change j % 100 = j
      exact Nat.mod_eq_of_lt (by omega)
    have hr : (⟨(j + 1) % 100, Nat.mod_lt _ (by decide)⟩ : Fin 100) = Fin.natAdd 1 n := by
      apply Fin.ext
      change (j + 1) % 100 = 1 + j
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    change generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor10 n)
      (generatedAxisGlobalFifthQState10 ⟨j % 100, Nat.mod_lt _ (by decide)⟩ i) =
        generatedAxisGlobalFifthQState10 ⟨(j + 1) % 100, Nat.mod_lt _ (by decide)⟩ i
    rw [hl, hr]
    exact generatedAxisGlobalFifthQStates10_actual n i
  have h := generatedAxisGlobalQFactorRun_states w u hs
  rw [show w.length = 99 from generatedAxisGlobalFifthQFactor10_length] at h
  change generatedAxisGlobalQFactorRun w (generatedAxisGlobalFifthQState10 0 i) =
    generatedAxisGlobalFifthQState10 99 i at h
  rw [initial_state, final_state] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
