/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite scalar evaluation of full Q-product phases without repeated extension products. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQCoordinateEvaluation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- A product's central coefficient, evaluated only with scalar pairings of its factors. -/
def monsterNortonQFinitePhase : List Q → ZMod 2
  | [] => 0
  | q :: l => toAdd q.coeff + monsterNortonQFinitePhase l +
      (l.map (fun r => qBeta (toAdd q.base) (toAdd r.base))).sum

private theorem list_binary (l : List Q) :
    toAdd l.prod.base = (l.map (fun q => toAdd q.base)).sum := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    change toAdd q.base + toAdd l.prod.base =
      toAdd q.base + (l.map (fun r => toAdd r.base)).sum
    rw [ih]

private theorem beta_list_sum (v : Fin 24 → ZMod 2) (l : List Q) :
    qBeta v (l.map (fun q => toAdd q.base)).sum =
      (l.map (fun q => qBeta v (toAdd q.base))).sum := by
  induction l with
  | nil => exact qBeta_zero_right v
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons, qBeta_add_right, ih]

/-- The finite scalar formula is exactly the complete coefficient of the actual Q product. -/
theorem monsterNortonQFinitePhase_actual (l : List Q) :
    toAdd l.prod.coeff = monsterNortonQFinitePhase l := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    change toAdd q.coeff + toAdd l.prod.coeff +
      qBeta (toAdd q.base) (toAdd l.prod.base) = _
    rw [ih, list_binary, beta_list_sum]
    rfl

/-- Full generator-image evaluation has this exact scalar phase, including the input correction. -/
theorem monsterNortonCoordinateEvaluation_finite_phase (images : Fin 24 → Q) (q : Q) :
    toAdd (monsterNortonCoordinateEvaluation images q).coeff =
      toAdd q.coeff + monsterNortonQFinitePhase
        (List.ofFn (fun i : Fin 24 => if toAdd q.base i = 0 then 1
          else qCoordinateGenerator i)) +
        monsterNortonQFinitePhase
          (List.ofFn (fun i : Fin 24 => if toAdd q.base i = 0 then 1 else images i)) := by
  rw [monsterNortonCoordinateEvaluation, qCentral_mul_coeff]
  rw [monsterNortonCoordinateSection, monsterNortonQFinitePhase_actual,
    monsterNortonQFinitePhase_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
