/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceFiber

/-! Expand genuine inverse three-bases letters into two original positive factors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual inverse source fiber equals the two positive fibers by its proved cube relation. -/
theorem generatedAxisGlobalOddSourceFiberLetter_one :
    generatedAxisGlobalOddSourceFiberLetter 1 =
      generatedAxisGlobalOddSourceFiberLetter 0 * generatedAxisGlobalOddSourceFiberLetter 0 := by
  change xiSpinLocalFiber⁻¹ = xiSpinLocalFiber * xiSpinLocalFiber
  apply inv_eq_of_mul_eq_one_right
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using xiSpinLocalFiber_cube

/-- Expand only original inverse three-bases letters, preserving all other signed source letters. -/
def generatedAxisGlobalOddExpandXi (ls : List (Fin 10)) : List (Fin 10) :=
  ls.flatMap (fun l => if l = 1 then [0, 0] else [l])

/-- The expanded product is the identical actual phase-preserving local fiber word. -/
theorem generatedAxisGlobalOddExpandXi_product (ls : List (Fin 10)) :
    (((generatedAxisGlobalOddExpandXi ls).map generatedAxisGlobalOddSourceFiberLetter).prod) =
      ((ls.map generatedAxisGlobalOddSourceFiberLetter).prod) := by
  induction ls with
  | nil => simp only [generatedAxisGlobalOddExpandXi, List.flatMap_nil, List.map_nil,
      List.prod_nil]
  | cons l ls ih =>
    rw [generatedAxisGlobalOddExpandXi, List.flatMap_cons, List.map_append, List.prod_append]
    change _ * ((generatedAxisGlobalOddExpandXi ls).map
      generatedAxisGlobalOddSourceFiberLetter).prod = _
    rw [ih]
    by_cases hl : l = 1
    · subst l
      simp only [ite_true, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, generatedAxisGlobalOddSourceFiberLetter_one]
    · simp only [hl, ite_false, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
