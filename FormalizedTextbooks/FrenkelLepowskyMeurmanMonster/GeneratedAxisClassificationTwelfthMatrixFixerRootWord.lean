/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthMatrixFixerRootData

/-! Complete original words in genuine full matrix stabilizers realize each root-orbit witness. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine subgroup of the original section group fixing the whole actual Twelfth matrix. -/
def generatedTwelfthMatrixSectionStabilizer : Subgroup leechSeventhE8SectionGroup where
  carrier := {g | conwayMatrixAction g.val (griessConwayEncode generatedTwelfthAxis).1 =
    (griessConwayEncode generatedTwelfthAxis).1}
  one_mem' := by change conwayMatrixAction 1 _ = _; rw [map_one]; rfl
  mul_mem' := by
    intro g h hg hh
    change conwayMatrixAction (g.val * h.val) _ = _
    rw [map_mul]
    change conwayMatrixAction g.val (conwayMatrixAction h.val _) = _
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    change conwayMatrixAction g.val⁻¹ _ = _
    rw [← hg, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    exact hg.symm

/-- Restriction retains the actual original whole root-line action. -/
def generatedTwelfthMatrixRootAction :
    generatedTwelfthMatrixSectionStabilizer →* Equiv.Perm (Fin 120) :=
  generatedTwelfthRootAction.comp generatedTwelfthMatrixSectionStabilizer.subtype

/-- Each checked entire original word is an actual whole matrix stabilizer element. -/
def generatedTwelfthMatrixRootGenerator (g : Fin 3) : generatedTwelfthMatrixSectionStabilizer :=
  ⟨generatedTwelfthMatrixFixer g, generatedTwelfth_matrix_fixer_actual_matrix g⟩

/-- All 120 actual root coordinates agree with the complete original source-word calculation. -/
theorem generatedTwelfth_matrix_root_generator_actual (g : Fin 3) (r : Fin 120) :
    generatedTwelfthMatrixRootAction (generatedTwelfthMatrixRootGenerator g) r =
      generatedTwelfthMatrixFixerRootForward g r := by
  rw [← generatedTwelfth_matrix_fixer_root_source]
  exact generatedTwelfth_root_orbit_word_actual (generatedTwelfthMatrixFixerWord g) r

/-- Positive and inverse actual letters in the entire genuine matrix stabilizer. -/
def generatedTwelfthMatrixRootLetter (l : Fin 3 × Bool) : generatedTwelfthMatrixSectionStabilizer :=
  if l.2 then (generatedTwelfthMatrixRootGenerator l.1)⁻¹
  else generatedTwelfthMatrixRootGenerator l.1

/-- Every complete original positive and inverse letter has its true entire root action. -/
theorem generatedTwelfth_matrix_root_letter_actual (l : Fin 3 × Bool) (r : Fin 120) :
    generatedTwelfthMatrixRootAction (generatedTwelfthMatrixRootLetter l) r =
      generatedTwelfthMatrixFixerRootFiniteLetter l r := by
  rcases l with ⟨g, b⟩
  cases b
  · exact generatedTwelfth_matrix_root_generator_actual g r
  · change generatedTwelfthMatrixRootAction (generatedTwelfthMatrixRootGenerator g)⁻¹ r = _
    rw [map_inv]
    apply (generatedTwelfthMatrixRootAction (generatedTwelfthMatrixRootGenerator g)).injective
    change generatedTwelfthMatrixRootAction (generatedTwelfthMatrixRootGenerator g)
        ((generatedTwelfthMatrixRootAction (generatedTwelfthMatrixRootGenerator g)).symm r) =
      generatedTwelfthMatrixRootAction (generatedTwelfthMatrixRootGenerator g)
        (generatedTwelfthMatrixFixerRootBackward g r)
    rw [Equiv.apply_symm_apply, generatedTwelfth_matrix_root_generator_actual,
      generatedTwelfth_matrix_fixer_root_inverse]

/-- Every full matrix fixing word uses the genuine original finite root dictionary. -/
theorem generatedTwelfth_matrix_root_word_actual (w : List (Fin 3 × Bool)) (r : Fin 120) :
    generatedTwelfthMatrixRootAction ((w.map generatedTwelfthMatrixRootLetter).prod) r =
      w.foldr generatedTwelfthMatrixFixerRootFiniteLetter r := by
  induction w generalizing r with
  | nil => rw [List.map_nil, List.prod_nil, map_one]; rfl
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, map_mul]
    change generatedTwelfthMatrixRootAction (generatedTwelfthMatrixRootLetter l)
      (generatedTwelfthMatrixRootAction ((w.map generatedTwelfthMatrixRootLetter).prod) r) = _
    rw [ih, generatedTwelfth_matrix_root_letter_actual]
    rfl

/-- Each entire original matrix fixing witness is a genuine element of the full matrix subgroup. -/
def generatedTwelfthMatrixRootWitness (n : Fin 86) : generatedTwelfthMatrixSectionStabilizer :=
  ((generatedTwelfthMatrixFixerRootWitnessWord n).map generatedTwelfthMatrixRootLetter).prod

/-- Every witness uses precisely the entire true original root word. -/
theorem generatedTwelfth_matrix_root_witness_actual (n : Fin 86) (r : Fin 120) :
    generatedTwelfthMatrixRootAction (generatedTwelfthMatrixRootWitness n) r =
      generatedTwelfthMatrixFixerRootFiniteWord n r :=
  generatedTwelfth_matrix_root_word_actual (generatedTwelfthMatrixFixerRootWitnessWord n) r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
