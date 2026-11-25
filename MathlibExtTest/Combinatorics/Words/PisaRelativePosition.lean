/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.PisaRelativePosition
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for the relative position of the extended Pisa fixed point -/

namespace MetaMathlibExt.pisa_relativePosition_of_letterPosition_b

-- For `k = 1`, `l = 0`, `m = 1` the substitution is the Fibonacci substitution `a ↦ ab`, `b ↦ a`,
-- and the formula reduces to `r(n) = n`.
example {w : ℕ → Bool}
    (hfix : IsSubstitutionImage (fun x : Bool => if x then List.replicate 1 true ++ [false] ++
      List.replicate 0 true else List.replicate 1 true) w w)
    (h₀ : w 0 = true) (n : ℕ) (hn : 1 ≤ n) : relativePosition w n = n := by
  have h := pisa_relativePosition_of_letterPosition_b 1 0 1 le_rfl le_rfl hfix h₀ n hn
  norm_num at h
  exact_mod_cast h

/-- The period-doubling word `abaaabab⋯`: `ℓ_{2j} = a` and `ℓ_{2j+1}` is the other letter than
`ℓ_j`. -/
private def periodDoubling (i : ℕ) : Bool := if i % 2 = 0 then true else !periodDoubling (i / 2)
decreasing_by omega

private theorem periodDoubling_even (j : ℕ) : periodDoubling (2 * j) = true := by
  rw [periodDoubling]
  simp

private theorem periodDoubling_odd (j : ℕ) : periodDoubling (2 * j + 1) = !periodDoubling j := by
  rw [periodDoubling, show (2 * j + 1) / 2 = j by omega]
  simp

/-- The period-doubling substitution `a ↦ ab`, `b ↦ aa`, written as in the main theorem with
`k = 1`, `l = 0` and `m = 2`. -/
private abbrev doubling : Bool → List Bool := fun x : Bool =>
  if x then List.replicate 1 true ++ [false] ++ List.replicate 0 true else List.replicate 2 true

private theorem flatMap_prefix (j : ℕ) :
    (List.ofFn fun i : Fin j => periodDoubling i).flatMap doubling =
      List.ofFn fun i : Fin (2 * j) => periodDoubling i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.flatMap_append]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    rw [show List.ofFn (fun i : Fin (2 * (j + 1)) => periodDoubling i) =
        List.ofFn (fun i : Fin (2 * j + 2) => periodDoubling i) from rfl, List.ofFn_add]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Fin.val_natAdd]
    congr 1
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
    cases h : periodDoubling j <;> simp [doubling, periodDoubling_even, periodDoubling_odd, h]

/-- The period-doubling word is a fixed point of `a ↦ ab`, `b ↦ aa`. -/
private theorem periodDoubling_fixed :
    IsSubstitutionImage doubling periodDoubling periodDoubling := by
  refine ⟨fun N => ⟨N, by rw [flatMap_prefix, List.length_ofFn]; omega⟩, fun j i hi => ?_⟩
  rw [flatMap_prefix] at hi ⊢
  rw [List.getD_eq_getElem _ _ hi, List.getElem_ofFn]

-- The hypotheses are satisfiable: for the period-doubling word (`k = 1`, `l = 0`, `m = 2`) the
-- formula reads `2 r(n) = p_b(n) + 1`.
example (n : ℕ) (hn : 1 ≤ n) :
    2 * (relativePosition periodDoubling n : ℚ) = letterPosition periodDoubling false n + 1 := by
  have h := pisa_relativePosition_of_letterPosition_b 1 0 2 le_rfl (by norm_num)
    periodDoubling_fixed (periodDoubling_even 0) n hn
  rw [h]
  ring

-- At `n = 1`: the word starts with `ab`, so `r(1) = 1`, and the formula gives `p_b(1) = 1`.
example : letterPosition periodDoubling false 1 = 1 := by
  have h := pisa_relativePosition_of_letterPosition_b 1 0 2 le_rfl (by norm_num)
    periodDoubling_fixed (periodDoubling_even 0) 1 le_rfl
  have hr : relativePosition periodDoubling 1 = 1 :=
    relativePosition_one_of_head_ab (periodDoubling_even 0)
      (by rw [periodDoubling_odd 0, periodDoubling_even 0]; rfl)
  rw [hr] at h
  norm_num at h
  exact_mod_cast (by linarith : (letterPosition periodDoubling false 1 : ℚ) = 1)

end MetaMathlibExt.pisa_relativePosition_of_letterPosition_b
