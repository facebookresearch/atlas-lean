/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Binding the rank-four Gaussian candidate to actual Norton spin conjugation, up to a scalar
  sign. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoCompactSpinData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoQImageCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Finiteness

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxRecDepth 10000 in
set_option maxHeartbeats 80000000 in
-- Check every binary coordinate and central sign of the twenty-four actual generator images.
/-- The compact actual spin factors have all twenty-four full Norton Q generator images. -/
theorem monsterNortonUTwoCompactSpin_generator_certificate (i : Fin 24) :
    monsterNortonUTwoCompactQImage (qCoordinateGenerator i) =
      monsterNortonUTwoQGeneratorImage i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change (fun j : Fin 24 => toAdd (monsterNortonUTwoCompactQImage (qCoordinateGenerator
      i)).base j) =
      (fun j : Fin 24 => toAdd (monsterNortonUTwoQGeneratorImage i).base j)
    fin_cases i <;> decide +kernel
  · apply toAdd.injective
    change toAdd (monsterNortonUTwoCompactQImage (qCoordinateGenerator i)).coeff =
      monsterNortonUTwoQGeneratorPhase i
    fin_cases i <;> decide +kernel

/-- The compact actual spin operator agrees with Norton conjugation on every full Q element. -/
theorem monsterNortonUTwoCompactSpin_Q_eq (q : Q) :
    spinConjugation monsterNortonUTwoCompactSpin q = spinConjugation
      (monsterNortonUFiber.val.1 ^ 2) q := by
  have hs : spinConjugation monsterNortonUTwoCompactSpin q =
      monsterNortonCoordinateEvaluation monsterNortonUTwoQGeneratorImage q := by
    apply monsterNortonCoordinateEvaluation_eq
    intro i
    rw [monsterNortonUTwoCompactSpin_conjugation]
    exact monsterNortonUTwoCompactSpin_generator_certificate i
  have hu : spinConjugation (monsterNortonUFiber.val.1 ^ 2) q =
      monsterNortonCoordinateEvaluation monsterNortonUTwoQGeneratorImage q :=
    monsterNortonCoordinateEvaluation_eq _ _ monsterNortonUTwoQGeneratorImage_actual q
  exact hs.trans hu.symm

private theorem spin_scalar_of_conjugation_eq (a b : SpinHolomorph)
    (he : spinConjugation a = spinConjugation b) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ ∀ x : SpinSpace, a.val x = c • b.val x := by
  let s : SpinHolomorph := a * b⁻¹
  have hk : s ∈ spinConjugation.ker := by
    change spinConjugation s = 1
    dsimp only [s]
    rw [map_mul, map_inv, he, mul_inv_cancel]
  obtain ⟨c, hc, hs⟩ := spinHolomorph_conjugation_kernel_scalar ⟨s, hk⟩
  refine ⟨c, hc, ?_⟩
  intro x
  have h := hs (b.val x)
  change a.val (b.val.symm (b.val x)) = c • b.val x at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

/-- The genuine Norton spin operator is the compact candidate times one scalar sign. -/
theorem monsterNortonUTwoCompactSpin_scalar :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ ∀ x : SpinSpace,
      (monsterNortonUFiber.val.1 ^ 2).val x = c • monsterNortonUTwoCompactSpin.val x := by
  apply spin_scalar_of_conjugation_eq
  exact (MulEquiv.ext monsterNortonUTwoCompactSpin_Q_eq).symm

/-- One actual fixed-vector coordinate fixes the remaining scalar sign of the compact operator. -/
theorem monsterNortonUTwoCompactSpin_eq_of_fixed_coordinate (v : SpinSpace) (t : SpinIndex)
    (hv : (monsterNortonUFiber.val.1 ^ 2).val v = v)
    (ht : monsterNortonUTwoCompactSpin.val v t = v t) (hn : v t ≠ 0) :
    (monsterNortonUFiber.val.1 ^ 2) = monsterNortonUTwoCompactSpin := by
  obtain ⟨c, hc, hs⟩ := monsterNortonUTwoCompactSpin_scalar
  have hc1 : c = 1 := by
    rcases hc with hc | hc
    · exact hc
    · exfalso
      have h := congrFun (hs v) t
      rw [hv] at h
      simp only [Pi.smul_apply, smul_eq_mul, hc, neg_one_mul] at h
      rw [ht] at h
      apply hn
      linarith
  subst c
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  simpa only [one_smul] using hs x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
