/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1AutomorphismNonsplitSoundness

/-! The literal Conway action has no homomorphic lift to automorphisms of Q. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- A homomorphism evaluates each original word as the same word in its generator lifts. -/
theorem co1NonsplitLiftWord_map (s : Co1 →* MulAut Q) (w : List (Fin 5)) :
    s (co1NonsplitActualWord w) =
      co1NonsplitLiftWord (fun k => s (monsterCo1FiveGenerator k)) w := by
  induction w with
  | nil => exact s.map_one
  | cons k w ih => simp only [co1NonsplitActualWord, co1NonsplitLiftWord, map_mul, ih]

/-- Every section of the actual action would satisfy all selected central correction equations. -/
theorem co1NonsplitSection_equations (s : Co1 →* MulAut Q)
    (h : ∀ g, qBinaryAction (s g) = co1BinaryAction g) (j : Fin 28) :
    (if (co1NonsplitEquationMasks j).2.testBit 0 then (1 : ZMod 2) else 0) +
      monsterCo1GeometryBinaryMaskDecode (co1NonsplitEquationMasks j).1 ⬝ᵥ
        co1NonsplitLiftParameters (fun k => s (monsterCo1FiveGenerator k))
          (fun k => h (monsterCo1FiveGenerator k)) = 0 := by
  let a : Fin 5 → MulAut Q := fun k => s (monsterCo1FiveGenerator k)
  have ha : ∀ k, qBinaryAction (a k) = co1BinaryAction (monsterCo1FiveGenerator k) :=
    fun k => h (monsterCo1FiveGenerator k)
  let i : Fin 24 := (co1NonsplitEquationInput j).2
  let r : Fin 14 := (co1NonsplitEquationInput j).1
  have hc := (co1NonsplitLiftWord_state a ha (co1NonsplitRelationWords r)
    (2 ^ i.val, (0, 0)) (qSection (monsterCo1GeometryBinaryMaskDecode (2 ^ i.val)))
      rfl (by
        change (0 : ZMod 2) = (if (0 : ℕ).testBit 0 then 1 else 0) +
          monsterCo1GeometryBinaryMaskDecode 0 ⬝ᵥ co1NonsplitLiftParameters a ha
        simp [monsterCo1GeometryBinaryMaskDecode_zero])).2
  have hw : co1NonsplitLiftWord a (co1NonsplitRelationWords r) = 1 := by
    rw [← co1NonsplitLiftWord_map, co1NonsplitActual_relation, map_one]
  rw [hw] at hc
  have hstate := co1NonsplitEquation_mask_state j
  change (co1NonsplitMaskRun (co1NonsplitRelationWords r)
    (2 ^ i.val, (0, 0))).2 = _ at hstate
  rw [hstate] at hc
  exact hc.symm

/-- The actual faithful Co₁ binary action has no group-homomorphic section in Aut(Q). -/
theorem co1BinaryAction_no_automorphism_lift :
    ¬ ∃ s : Co1 →* MulAut Q, ∀ g, qBinaryAction (s g) = co1BinaryAction g := by
  rintro ⟨s, hs⟩
  let p := co1NonsplitLiftParameters (fun k => s (monsterCo1FiveGenerator k))
    (fun k => hs (monsterCo1FiveGenerator k))
  have hconst := congrFun (monsterCo1GeometryBinaryMaskDecode_sum (n := 1)
    (List.ofFn (fun j : Fin 28 => (co1NonsplitEquationMasks j).2))) 0
  rw [co1NonsplitEquation_constants_xor] at hconst
  simp only [List.map_ofFn, List.sum_ofFn, Finset.sum_apply] at hconst
  change (1 : ZMod 2) =
    ∑ j : Fin 28, if (co1NonsplitEquationMasks j).2.testBit 0 then 1 else 0 at hconst
  have hrows := congrArg (fun v : Fin 120 → ZMod 2 => v ⬝ᵥ p)
    (monsterCo1GeometryBinaryMaskDecode_sum (n := 120)
      (List.ofFn (fun j : Fin 28 => (co1NonsplitEquationMasks j).1)))
  rw [co1NonsplitEquation_rows_xor, monsterCo1GeometryBinaryMaskDecode_zero,
    zero_dotProduct, List.map_ofFn, List.sum_ofFn, sum_dotProduct] at hrows
  simp only [Function.comp_apply] at hrows
  have he : (∑ j : Fin 28,
      ((if (co1NonsplitEquationMasks j).2.testBit 0 then (1 : ZMod 2) else 0) +
        monsterCo1GeometryBinaryMaskDecode (co1NonsplitEquationMasks j).1 ⬝ᵥ p)) = 0 :=
    Finset.sum_eq_zero fun j _ => co1NonsplitSection_equations s hs j
  rw [Finset.sum_add_distrib, ← hconst, ← hrows, add_zero] at he
  exact one_ne_zero he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
