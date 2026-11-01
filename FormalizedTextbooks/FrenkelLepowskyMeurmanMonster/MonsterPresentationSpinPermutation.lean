/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Explicit linear relabelings of the actual binary spin labels. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationSpinMonomial

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Pull back an actual cocode character along a binary linear equivalence. -/
def monsterMonomialPullback (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (b : SpinIndex) :
    SpinIndex := fun j => spinDot b (P (Pi.single j 1))

/-- The displayed coordinates are the actual pullback character on every label. -/
theorem monsterMonomialPullback_dot (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex)
    (b t : SpinIndex) : spinDot (monsterMonomialPullback P b) t = spinDot b (P t) := by
  have ht : t = ∑ j : Fin 12, t j • (Pi.single j 1 : SpinIndex) := by
    ext i
    simp [Pi.single_apply]
  conv_rhs => rw [ht, map_sum]
  simp only [map_smul, xiSpinDot_sum_right, xiSpinDot_smul_right]
  unfold spinDot monsterMonomialPullback
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- A binary linear change of labels as an explicit real linear equivalence. -/
def monsterMonomialPermutation (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) :
    SpinSpace ≃ₗ[ℝ] SpinSpace where
  toFun f t := f (P.symm t)
  invFun f t := f (P t)
  left_inv f := by ext t; exact congrArg f (P.symm_apply_apply t)
  right_inv f := by ext t; exact congrArg f (P.apply_symm_apply t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Inverting the label equivalence inverts the actual real operator. -/
theorem monsterMonomialPermutation_symm (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) :
    monsterMonomialPermutation P.symm = (monsterMonomialPermutation P)⁻¹ := by
  apply LinearEquiv.ext
  intro f
  rfl

/-- The exact Q image of the coordinate relabeling, including its central coordinate. -/
def monsterMonomialPermutationImage (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (q : Q) : Q :=
  ⟨ofAdd (Fin.append (P (spinTranslation q))
      (monsterMonomialPullback P.symm (spinModulation q))), q.coeff⟩

/-- Evaluation of the actual linear label relabeling. -/
theorem monsterMonomialPermutation_apply (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex)
    (f : SpinSpace) (t : SpinIndex) : monsterMonomialPermutation P f t = f (P.symm t) := rfl

/-- Evaluation of its actual inverse. -/
theorem monsterMonomialPermutation_inv_apply (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex)
    (f : SpinSpace) (t : SpinIndex) : (monsterMonomialPermutation P)⁻¹ f t = f (P t) := rfl

/-- The faithful representation evaluates by its already proved coordinate formula. -/
theorem monsterMonomialSpinRepresentation_apply (q : Q) (f : SpinSpace) (t : SpinIndex) :
    spinRepresentation q f t = qSign (spinPhase q t) * f (t + spinTranslation q) := rfl

/-- A relabeling sends translation coordinates through the actual binary linear map. -/
theorem monsterMonomialPermutationImage_translation
    (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (q : Q) :
    spinTranslation (monsterMonomialPermutationImage P q) = P (spinTranslation q) := by
  ext i
  exact Fin.append_left _ _ i

/-- Its phase pulls back the actual cocode character without changing the central sign. -/
theorem monsterMonomialPermutationImage_phase
    (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (q : Q) (t : SpinIndex) :
    spinPhase (monsterMonomialPermutationImage P q) t = toAdd q.coeff +
      spinDot (monsterMonomialPullback P.symm (spinModulation q)) t := by
  have hm : spinModulation (monsterMonomialPermutationImage P q) =
      monsterMonomialPullback P.symm (spinModulation q) := by
    ext i
    exact Fin.append_right _ _ i
  have hc : (monsterMonomialPermutationImage P q).coeff = q.coeff := rfl
  simp only [spinPhase, hm, hc]

/-- The explicit coordinate relabeling conjugates the actual Q representation. -/
theorem monsterMonomialPermutation_conjugation
    (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (q : Q) :
    monsterMonomialPermutation P * spinRepresentation q *
      (monsterMonomialPermutation P)⁻¹ =
        spinRepresentation (monsterMonomialPermutationImage P q) := by
  apply LinearEquiv.ext
  intro f
  ext t
  simp only [LinearEquiv.mul_apply, monsterMonomialPermutation_apply,
    monsterMonomialPermutation_inv_apply, monsterMonomialSpinRepresentation_apply,
    monsterMonomialPermutationImage_translation, monsterMonomialPermutationImage_phase]
  rw [spinPhase, monsterMonomialPullback_dot, map_add, P.apply_symm_apply]

/-- Linear relabeling preserves the actual Euclidean pairing by finite reindexing. -/
theorem monsterMonomialPermutation_pairing (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex)
    (f h : SpinSpace) :
    spinPairing (monsterMonomialPermutation P f) (monsterMonomialPermutation P h) =
      spinPairing f h := Equiv.sum_comp P.symm.toEquiv (fun t => f t * h t)

/-- The proved linear relabeling belongs to the actual spin holomorph. -/
noncomputable def monsterMonomialPermutationHolomorph
    (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) : SpinHolomorph :=
  ⟨monsterMonomialPermutation P, by
    constructor
    · apply Subgroup.mem_normalizer_iff.mpr
      intro h
      constructor
      · rintro ⟨q, rfl⟩
        exact ⟨monsterMonomialPermutationImage P q,
          (monsterMonomialPermutation_conjugation P q).symm⟩
      · rintro ⟨q, hq⟩
        refine ⟨monsterMonomialPermutationImage P.symm q, ?_⟩
        rw [← monsterMonomialPermutation_conjugation P.symm q,
          monsterMonomialPermutation_symm, hq]
        group
    · exact monsterMonomialPermutation_pairing P⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
