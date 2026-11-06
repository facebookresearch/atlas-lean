/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQStates06
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCacheData

/-! The entire genuine root 6 6 Q action from individually checked
literal source-factor states. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem initial_state (i : Fin 24) :
    generatedAxisGlobalFifthQState06 0 i = qCoordinateGenerator i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24, toAdd (generatedAxisGlobalFifthQState06 0 i).base j =
        toAdd (qCoordinateGenerator i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24, toAdd (generatedAxisGlobalFifthQState06 0 i).coeff =
        toAdd (qCoordinateGenerator i).coeff := by decide +kernel
    exact h i

private theorem final_state (i : Fin 24) :
    generatedAxisGlobalFifthQState06 66 i = generatedAxisGlobalFifthQCache 6 i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24, toAdd (generatedAxisGlobalFifthQState06 66 i).base j =
        toAdd (generatedAxisGlobalFifthQCache 6 i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24, toAdd (generatedAxisGlobalFifthQState06 66 i).coeff =
        toAdd (generatedAxisGlobalFifthQCache 6 i).coeff := by decide +kernel
    exact h i

/-- All twenty-four entire coordinate lifts follow the genuine chronological
source-factor states. -/
theorem generatedAxisGlobalFifthQCache06_actual (i : Fin 24) :
    generatedAxisGlobalFifthChainQImage 6 7 (qCoordinateGenerator i) =
      generatedAxisGlobalFifthQCache 6 i := by
  rw [generatedAxisGlobalFifthQFactors_run]
  let w := generatedAxisGlobalFifthChainQFactors 6 (generatedAxisGlobalFifthActiveStages 6)
  let u := fun j => generatedAxisGlobalFifthQState06 ⟨j % 67, Nat.mod_lt _ (by decide)⟩ i
  have hs : ∀ j (hj : j < w.length),
      generatedAxisGlobalQFactorImage w[j] (u j) = u (j + 1) := by
    intro j hj
    have hjBound : j < 66 := by
      simpa only [w, generatedAxisGlobalFifthQFactor06_length] using hj
    let n : Fin 66 := ⟨j, hjBound⟩
    have hl : (⟨j % 67, Nat.mod_lt _ (by decide)⟩ : Fin 67) = Fin.castAdd 1 n := by
      apply Fin.ext
      change j % 67 = j
      exact Nat.mod_eq_of_lt (by omega)
    have hr : (⟨(j + 1) % 67, Nat.mod_lt _ (by decide)⟩ : Fin 67) = Fin.natAdd 1 n := by
      apply Fin.ext
      change (j + 1) % 67 = 1 + j
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    change generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor06 n)
      (generatedAxisGlobalFifthQState06 ⟨j % 67, Nat.mod_lt _ (by decide)⟩ i) =
        generatedAxisGlobalFifthQState06 ⟨(j + 1) % 67, Nat.mod_lt _ (by decide)⟩ i
    rw [hl, hr]
    exact generatedAxisGlobalFifthQStates06_actual n i
  have h := generatedAxisGlobalQFactorRun_states w u hs
  rw [show w.length = 66 from generatedAxisGlobalFifthQFactor06_length] at h
  change generatedAxisGlobalQFactorRun w (generatedAxisGlobalFifthQState06 0 i) =
    generatedAxisGlobalFifthQState06 66 i at h
  rw [initial_state, final_state] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
