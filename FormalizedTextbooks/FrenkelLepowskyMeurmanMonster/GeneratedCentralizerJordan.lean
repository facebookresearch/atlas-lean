/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Orthogonal spatial reconstruction from the actual centralizer's intrinsic matrix constituent. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerConstituents
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerMatrixProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SymmetricJordanRecognition

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual centralizer matrix action in the original symmetric-matrix coordinates. -/
noncomputable def generatedCentralizerMatrixAction (g : generatedCentralizer) :
    Sym24 ≃ₗ[ℝ] Sym24 :=
  generatedCentralMatrixCoordinates.symm.trans
    ((generatedCentralizerMatrixEquiv g).trans generatedCentralMatrixCoordinates)

/-- The actual centralizer short action in the original short-label coordinates. -/
noncomputable def generatedCentralizerShortAction (g : generatedCentralizer) :
    (GriessShortIndex → ℝ) ≃ₗ[ℝ] (GriessShortIndex → ℝ) :=
  generatedCentralShortCoordinates.symm.trans
    ((generatedCentralizerShortEquiv g).trans generatedCentralShortCoordinates)

/-- The spatial coordinate action is exactly the actual action on pure matrix vectors. -/
theorem generatedCentralizerMatrixAction_embed (g : generatedCentralizer) (A : Sym24) :
    g.val.val (generatedCentralPlusEmbed A 0).val =
      (generatedCentralPlusEmbed (generatedCentralizerMatrixAction g A) 0).val := by
  have h := generatedCentralMatrixCoordinates.symm_apply_apply
    (generatedCentralizerMatrixEquiv g (generatedCentralMatrixCoordinates.symm A))
  exact (congrArg (fun x : generatedCentralMatrix => x.val.val) h).symm

/-- The short coordinate action is exactly the actual action on pure short vectors. -/
theorem generatedCentralizerShortAction_embed (g : generatedCentralizer)
    (X : GriessShortIndex → ℝ) :
    g.val.val (generatedCentralPlusEmbed 0 X).val =
      (generatedCentralPlusEmbed 0 (generatedCentralizerShortAction g X)).val := by
  have h := generatedCentralShortCoordinates.symm_apply_apply
    (generatedCentralizerShortEquiv g (generatedCentralShortCoordinates.symm X))
  exact (congrArg (fun x : generatedCentralShort => x.val.val) h).symm

/-- The actual centralizer acts separately on the two original fixed-space coordinates. -/
theorem generatedCentralizerPlusCoordinates_action (g : generatedCentralizer)
    (x : generatedCentralPlus) :
    generatedCentralPlusCoordinates (generatedCentralizerPlusEquiv g x) =
      (generatedCentralizerMatrixAction g (generatedCentralPlusCoordinates x).1,
        generatedCentralizerShortAction g (generatedCentralPlusCoordinates x).2) := by
  have hm (A : Sym24) : generatedCentralizerPlusEquiv g (generatedCentralPlusEmbed A 0) =
      generatedCentralPlusEmbed (generatedCentralizerMatrixAction g A) 0 :=
    Subtype.ext (generatedCentralizerMatrixAction_embed g A)
  have hs (X : GriessShortIndex → ℝ) :
      generatedCentralizerPlusEquiv g (generatedCentralPlusEmbed 0 X) =
        generatedCentralPlusEmbed 0 (generatedCentralizerShortAction g X) :=
    Subtype.ext (generatedCentralizerShortAction_embed g X)
  calc
    _ = generatedCentralPlusCoordinates (generatedCentralizerPlusEquiv g
        (generatedCentralPlusEmbed (generatedCentralPlusCoordinates x).1 0 +
          generatedCentralPlusEmbed 0 (generatedCentralPlusCoordinates x).2)) := by
      exact congrArg (fun v => generatedCentralPlusCoordinates (generatedCentralizerPlusEquiv g v))
        (generatedCentralPlus_matrix_short_decomposition x)
    _ = _ := by
      rw [map_add, hm, hs, map_add, ← generatedCentralPlusCoordinates_symm_apply,
        ← generatedCentralPlusCoordinates_symm_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
      exact Prod.ext (add_zero _) (zero_add _)

/-- The short coordinate action preserves its actual ordinary Euclidean pairing. -/
theorem generatedCentralizerShortAction_pairing (g : generatedCentralizer)
    (X Y : GriessShortIndex → ℝ) :
    (∑ r, generatedCentralizerShortAction g X r * generatedCentralizerShortAction g Y r) =
      ∑ r, X r * Y r := by
  have h := generated_group_preserves_griessForm g.val
    (generatedCentralPlusEmbed 0 X).val (generatedCentralPlusEmbed 0 Y).val
  rw [generatedCentralizerShortAction_embed, generatedCentralizerShortAction_embed,
    generatedCentralPlusEmbed_griessForm, generatedCentralPlusEmbed_griessForm] at h
  simpa only [Submodule.coe_zero, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    zero_add] using h

/-- The actual centralizer's matrix action preserves the original symmetric Jordan product. -/
theorem generatedCentralizerMatrixAction_jordan (g : generatedCentralizer) (A B : Sym24) :
    generatedCentralizerMatrixAction g (sym24Jordan A B) =
      sym24Jordan (generatedCentralizerMatrixAction g A)
        (generatedCentralizerMatrixAction g B) := by
  have h := generated_group_preserves_griessProduct sExtra_preserves_griessProd g.val
    (generatedCentralPlusEmbed A 0).val (generatedCentralPlusEmbed B 0).val
  rw [generatedCentral_matrix_product, generatedCentralizerMatrixAction_embed,
    generatedCentralizerMatrixAction_embed, generatedCentralizerMatrixAction_embed,
    generatedCentral_matrix_product] at h
  have hc := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) h
  rw [generatedCentralPlusEmbed_encode, generatedCentralPlusEmbed_encode] at hc
  have hv : (2 : ℝ) • (generatedCentralizerMatrixAction g (sym24Jordan A B)).val =
      (2 : ℝ) • (sym24Jordan (generatedCentralizerMatrixAction g A)
        (generatedCentralizerMatrixAction g B)).val := by
    simpa only [map_smul, Submodule.coe_smul] using hc
  apply Subtype.ext
  exact (smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0)) hv

/-- The actual centralizer's matrix action preserves ordinary matrix trace pairing. -/
theorem generatedCentralizerMatrixAction_trace (g : generatedCentralizer) (A B : Sym24) :
    ((generatedCentralizerMatrixAction g A).val *
      (generatedCentralizerMatrixAction g B).val).trace = (A.val * B.val).trace := by
  have h := generated_group_preserves_griessForm g.val
    (generatedCentralPlusEmbed A 0).val (generatedCentralPlusEmbed B 0).val
  rw [generatedCentralizerMatrixAction_embed, generatedCentralizerMatrixAction_embed,
    generatedCentral_matrix_form, generatedCentral_matrix_form] at h
  exact h

/-- Every actual centralizer element acts on symmetric matrices by an orthogonal conjugation. -/
theorem generatedCentralizer_orthogonal_matrix_action (g : generatedCentralizer) :
    ∃ R : Matrix (Fin 24) (Fin 24) ℝ, R.transpose * R = 1 ∧ R * R.transpose = 1 ∧
      ∀ A : Sym24, (generatedCentralizerMatrixAction g A).val = R * A.val * R.transpose :=
  sym24Jordan_orthogonal_conjugation (generatedCentralizerMatrixAction g)
    (generatedCentralizerMatrixAction_jordan g) (generatedCentralizerMatrixAction_trace g)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
