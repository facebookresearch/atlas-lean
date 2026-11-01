/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Fast full-phase evaluation from the twenty-four actual coordinate lifts. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.QCoordinateGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

/-- The fixed ordered product of coordinate lifts of a binary vector. -/
def monsterNortonCoordinateSection (v : Fin 24 → ZMod 2) : Q :=
  (List.ofFn (fun i : Fin 24 => if v i = 0 then 1 else qCoordinateGenerator i)).prod

private theorem coordinate_lift_binary (v : Fin 24 → ZMod 2) (i : Fin 24) :
    toAdd (qQuotHom (if v i = 0 then 1 else qCoordinateGenerator i)) = Pi.single i (v i) := by
  rcases two_cases (v i) with h | h
  · simp only [h, ite_true, map_one, Pi.single_zero]
    rfl
  · simp only [h, one_ne_zero, ite_false, qCoordinateGenerator_binary]
    rfl

private theorem coordinate_list_binary (v : Fin 24 → ZMod 2) (l : List (Fin 24)) :
    toAdd (qQuotHom ((l.map (fun i => if v i = 0 then 1 else qCoordinateGenerator i)).prod)) =
      (l.map (fun i => Pi.single i (v i))).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul]
    change toAdd (qQuotHom (if v i = 0 then 1 else qCoordinateGenerator i)) +
      toAdd (qQuotHom ((l.map (fun i => if v i = 0 then 1 else qCoordinateGenerator i)).prod)) = _
    rw [coordinate_lift_binary, ih]

/-- The ordered product has the actual binary coordinates, including every lift correction. -/
theorem monsterNortonCoordinateSection_binary (v : Fin 24 → ZMod 2) :
    toAdd (qQuotHom (monsterNortonCoordinateSection v)) = v := by
  rw [monsterNortonCoordinateSection, List.ofFn_eq_map, coordinate_list_binary,
    ← List.ofFn_eq_map, List.sum_ofFn, Finset.univ_sum_single]

/-- Every actual Q element has an ordered coordinate normal form with its central correction. -/
theorem monsterNortonCoordinateSection_normal_form (q : Q) :
    q = qCentral (toAdd q.coeff +
      toAdd (monsterNortonCoordinateSection (toAdd q.base)).coeff) *
        monsterNortonCoordinateSection (toAdd q.base) := by
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    apply toAdd.injective
    exact (monsterNortonCoordinateSection_binary (toAdd q.base)).symm
  · apply toAdd.injective
    rw [qCentral_mul_coeff]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- A finite generator-image evaluator retaining the full central phase. -/
def monsterNortonCoordinateEvaluation (images : Fin 24 → Q) (q : Q) : Q :=
  qCentral (toAdd q.coeff + toAdd (monsterNortonCoordinateSection (toAdd q.base)).coeff) *
    (List.ofFn (fun i : Fin 24 => if toAdd q.base i = 0 then 1 else images i)).prod

private theorem map_coordinate_section (s : SpinHolomorph) (images : Fin 24 → Q)
    (hi : ∀ i, spinConjugation s (qCoordinateGenerator i) = images i)
    (v : Fin 24 → ZMod 2) :
    spinConjugation s (monsterNortonCoordinateSection v) =
      (List.ofFn (fun i : Fin 24 => if v i = 0 then 1 else images i)).prod := by
  have hm := (spinConjugation s).toMonoidHom.map_list_prod
    (List.ofFn (fun i : Fin 24 => if v i = 0 then 1 else qCoordinateGenerator i))
  change spinConjugation s (monsterNortonCoordinateSection v) = _ at hm
  rw [hm, List.map_ofFn]
  congr 1
  congr 1
  funext i
  dsimp only [Function.comp_apply]
  change spinConjugation s (if v i = 0 then 1 else qCoordinateGenerator i) = _
  split_ifs <;> simp only [map_one, hi]

/-- Twenty-four checked generator images determine genuine spin conjugation on every actual Q. -/
theorem monsterNortonCoordinateEvaluation_eq (s : SpinHolomorph) (images : Fin 24 → Q)
    (hi : ∀ i, spinConjugation s (qCoordinateGenerator i) = images i) (q : Q) :
    spinConjugation s q = monsterNortonCoordinateEvaluation images q := by
  conv_lhs => rw [monsterNortonCoordinateSection_normal_form q]
  rw [map_mul, spinConjugation_central, map_coordinate_section s images hi]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
