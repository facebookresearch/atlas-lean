/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal final equation and actual word interpretation of the independent C322 derivation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCContextCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationE7Centrality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The second corrected seven-letter E7 word as a literal positive word. -/
def y322TCPositive13 : List (Fin 8) :=
  (List.replicate 9 ([0, 1, 4, 6, 2, 7, 3] : List (Fin 8))).flatten

/-- Its interpretation is precisely the source's corrected F13. -/
theorem y322TCPositive13_value :
    y322PositiveWord y322TCPositive13 = PresentedGroup.mk y322Relations y322E7Word13 := by
  rw [y322TCPositive13, y322PositiveWord_replicate]
  simp [y322E7Word13, y322PositiveWord, map_pow, map_mul, PresentedGroup.of, mul_assoc]

/-- Positive original-generator letters retain their exact values under finite numbering. -/
theorem y322TC_numbered_positive_value (word : List (Fin 8)) :
    y322EquationWordValue (y322FiniteAuxiliaryValue y322TransportProgram)
        (word.map (fun v => (v.castAdd 48640, true))) = y322PositiveWord word := by
  have hv (v : Fin 8) : y322FiniteAuxiliaryValue y322TransportProgram (v.castAdd 48640) =
      (PresentedGroup.of v : Y322Presentation) := by
    exact y322FiniteAuxiliaryValue_number y322TransportProgram (.inl v)
  unfold y322EquationWordValue
  rw [FreeGroup.lift_mk]
  simp only [List.map_map, Function.comp_def, Bool.cond_true, hv]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel compares the decoded literal final claim with the exact source word spellings.
/-- The final claim is F12 followed by the reverse of F13, equated to its actual transporter. -/
theorem y322TCContext_target_shape :
    (y322TCContextProgram 28529).1 =
      ⟨(y322E7Positive12 ++ y322TCPositive13.reverse).map
          (fun v => (v.castAdd 48640, true)), [(38547, true)]⟩ := by
  have hl : (y322TCContextProgram 28529).1.left =
      (y322E7Positive12 ++ y322TCPositive13.reverse).map
        (fun v => (v.castAdd 48640, true)) := by decide +kernel
  have hr : (y322TCContextProgram 28529).1.right = [(38547, true)] := by decide +kernel
  cases h : (y322TCContextProgram 28529).1
  simp only [h] at hl hr
  cases hl
  cases hr
  rfl

/-- The actual left side of the final claim is the corrected F12 times F13 inverse. -/
theorem y322TCContext_target_left_value :
    y322EquationWordValue (y322FiniteAuxiliaryValue y322TransportProgram)
        (y322TCContextProgram 28529).1.left =
      PresentedGroup.mk y322Relations y322E7Word12 *
        (PresentedGroup.mk y322Relations y322E7Word13)⁻¹ := by
  rw [y322TCContext_target_shape]
  dsimp only
  rw [y322TC_numbered_positive_value, y322PositiveWord_append, y322PositiveWord_reverse,
    y322E7Positive12_value, y322TCPositive13_value]

/-- The actual right side is the named acyclic transporter H38539, not an assumed identity. -/
theorem y322TCContext_target_right_value :
    y322EquationWordValue (y322FiniteAuxiliaryValue y322TransportProgram)
        (y322TCContextProgram 28529).1.right =
      y322LocalProgramValue y322TransportProgram 38539 := by
  rw [y322TCContext_target_shape]
  dsimp only
  unfold y322EquationWordValue
  rw [FreeGroup.lift_mk]
  simp only [List.map_cons, List.map_nil, Bool.cond_true, List.prod_cons, List.prod_nil, mul_one]
  exact y322FiniteAuxiliaryValue_number y322TransportProgram (.inr 38539)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
