/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQFinitePhase

/-! Selected scalar phases retain both pairings and nonzero central coefficients. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Full selected-factor phase, including each factor's central coefficient. -/
def generatedSixthQSelectedPhase (c : Fin 24 → ZMod 2)
    (p : Fin 24 → Fin 24 → ZMod 2) (v : Fin 24 → ZMod 2) :
    List (Fin 24) → ZMod 2
  | [] => 0
  | i :: l => generatedSixthQSelectedPhase c p v l +
      if v i = 0 then 0 else c i + (l.map (fun j => if v j = 0 then 0 else p i j)).sum

/-- The selected scalar formula equals the complete phase of the genuine Q-factor product. -/
theorem generatedSixth_Q_selected_phase_actual (images : Fin 24 → Q)
    (c : Fin 24 → ZMod 2) (p : Fin 24 → Fin 24 → ZMod 2)
    (hc : ∀ i, toAdd (images i).coeff = c i)
    (hp : ∀ i j, qBeta (toAdd (images i).base) (toAdd (images j).base) = p i j)
    (v : Fin 24 → ZMod 2) (l : List (Fin 24)) :
    monsterNortonQFinitePhase (l.map (fun i => if v i = 0 then 1 else images i)) =
      generatedSixthQSelectedPhase c p v l := by
  have hb : toAdd (1 : Q).base = 0 := rfl
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hi : v i = 0
    · simp [monsterNortonQFinitePhase, generatedSixthQSelectedPhase, hi,
        qBeta_zero_left, ih, Function.comp_def]
    · simp only [List.map_cons, monsterNortonQFinitePhase, hi, ite_false, hc,
        ih, generatedSixthQSelectedPhase]
      have hs : ((l.map (fun j => if v j = 0 then 1 else images j)).map (fun r =>
          qBeta (toAdd (images i).base) (toAdd r.base))).sum =
          (l.map (fun j => if v j = 0 then 0 else p i j)).sum := by
        rw [List.map_map]
        apply congrArg List.sum
        apply List.map_congr_left
        intro j _
        by_cases hj : v j = 0
        · simp only [hj, ite_true, Function.comp_apply, hb, qBeta_zero_right]
        · simp only [hj, ite_false, Function.comp_apply, hp]
      rw [hs]
      ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
