/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputCheck00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputCheck01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputCheck02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputCheck03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputCheck04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputCheck05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputCheck06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputCheck07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputCheck08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputCheck09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputCheck10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputCheck11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputCheck12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputCheck13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputCheck14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputCheck15

/-! Every candidate input integer equals the complete true original tensor numerator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All spin labels and physical coordinates retain their complete original signed integer. -/
theorem generatedSixth_xi_tensor_input (n : Fin 4096) (i : Fin 24) :
    generatedSixthXiTensorInput n i = generatedSixthTensorFastExecutable n i := by
  have h : ∀ b : Fin 16, ∀ a : Fin 256,
      let t : Fin 4096 := ⟨b.val * 256 + a.val, by omega⟩
      generatedSixthXiTensorInput t i = generatedSixthTensorFastExecutable t i := by
    intro b a
    fin_cases b
    · exact generatedSixth_xi_tensor_input_check00 a i
    · exact generatedSixth_xi_tensor_input_check01 a i
    · exact generatedSixth_xi_tensor_input_check02 a i
    · exact generatedSixth_xi_tensor_input_check03 a i
    · exact generatedSixth_xi_tensor_input_check04 a i
    · exact generatedSixth_xi_tensor_input_check05 a i
    · exact generatedSixth_xi_tensor_input_check06 a i
    · exact generatedSixth_xi_tensor_input_check07 a i
    · exact generatedSixth_xi_tensor_input_check08 a i
    · exact generatedSixth_xi_tensor_input_check09 a i
    · exact generatedSixth_xi_tensor_input_check10 a i
    · exact generatedSixth_xi_tensor_input_check11 a i
    · exact generatedSixth_xi_tensor_input_check12 a i
    · exact generatedSixth_xi_tensor_input_check13 a i
    · exact generatedSixth_xi_tensor_input_check14 a i
    · exact generatedSixth_xi_tensor_input_check15 a i
  let b : Fin 16 := ⟨n.val / 256, by omega⟩
  let a : Fin 256 := ⟨n.val % 256, by omega⟩
  have he : (⟨b.val * 256 + a.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    dsimp [b, a]
    omega
  have hh := h b a
  simpa only [he] using hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
