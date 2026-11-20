/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingTrotterCylinder
import Mathlib.Analysis.Normed.Algebra.MatrixExponential











open scoped BigOperators
open Matrix

namespace StatMech.FrontierA


def quantumIsingDisagreementSet {L : Nat}
    (sigma tau : QuantumIsingChainConfig L) : Finset (Fin L) :=
  Finset.univ.filter fun i => sigma i ≠ tau i


def quantumIsingDisagreementCount {L : Nat}
    (sigma tau : QuantumIsingChainConfig L) : Nat :=
  (quantumIsingDisagreementSet sigma tau).card

theorem quantumIsingDisagreementSet_comm {L : Nat}
    (sigma tau : QuantumIsingChainConfig L) :
    quantumIsingDisagreementSet sigma tau =
      quantumIsingDisagreementSet tau sigma := by
  classical
  ext i
  simp [quantumIsingDisagreementSet, ne_comm]

theorem quantumIsingDisagreementCount_comm {L : Nat}
    (sigma tau : QuantumIsingChainConfig L) :
    quantumIsingDisagreementCount sigma tau =
      quantumIsingDisagreementCount tau sigma := by
  rw [quantumIsingDisagreementCount, quantumIsingDisagreementCount,
    quantumIsingDisagreementSet_comm]

@[simp] theorem quantumIsingDisagreementCount_self {L : Nat}
    (sigma : QuantumIsingChainConfig L) :
    quantumIsingDisagreementCount sigma sigma = 0 := by
  simp [quantumIsingDisagreementCount, quantumIsingDisagreementSet]

theorem quantumIsingDisagreementCount_eq_zero_iff {L : Nat}
    (sigma tau : QuantumIsingChainConfig L) :
    quantumIsingDisagreementCount sigma tau = 0 ↔ sigma = tau := by
  classical
  unfold quantumIsingDisagreementCount quantumIsingDisagreementSet
  rw [Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  constructor
  · intro h
    funext i
    by_contra hne
    exact h (Finset.mem_univ i) hne
  · intro h i hi
    subst tau
    simp




noncomputable def quantumIsingHamiltonian
    (h : Real) (L : Nat) :
    Matrix (QuantumIsingChainConfig L) (QuantumIsingChainConfig L) Complex :=
  fun sigma tau =>
    if sigma = tau then
      -(quantumIsingChainInteraction L sigma : Complex) / 4
    else if quantumIsingDisagreementCount sigma tau = 1 then
      -(h : Complex) / 2
    else 0

theorem quantumIsingHamiltonian_apply_diag
    (h : Real) (L : Nat) (sigma : QuantumIsingChainConfig L) :
    quantumIsingHamiltonian h L sigma sigma =
      -(quantumIsingChainInteraction L sigma : Complex) / 4 := by
  simp [quantumIsingHamiltonian]

theorem quantumIsingHamiltonian_apply_oneFlip
    (h : Real) (L : Nat) (sigma tau : QuantumIsingChainConfig L)
    (hne : sigma ≠ tau) (hflip : quantumIsingDisagreementCount sigma tau = 1) :
    quantumIsingHamiltonian h L sigma tau = -(h : Complex) / 2 := by
  simp [quantumIsingHamiltonian, hne, hflip]

theorem quantumIsingHamiltonian_apply_other
    (h : Real) (L : Nat) (sigma tau : QuantumIsingChainConfig L)
    (hne : sigma ≠ tau) (hflip : quantumIsingDisagreementCount sigma tau ≠ 1) :
    quantumIsingHamiltonian h L sigma tau = 0 := by
  simp [quantumIsingHamiltonian, hne, hflip]


theorem quantumIsingHamiltonian_isHermitian (h : Real) (L : Nat) :
    (quantumIsingHamiltonian h L).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro sigma tau
  by_cases heq : sigma = tau
  · subst tau
    simp [quantumIsingHamiltonian]
  · have heq' : tau ≠ sigma := Ne.symm heq
    by_cases hflip : quantumIsingDisagreementCount sigma tau = 1
    · have hflip' : quantumIsingDisagreementCount tau sigma = 1 := by
        rw [quantumIsingDisagreementCount_comm]
        exact hflip
      simp [quantumIsingHamiltonian, heq, heq', hflip, hflip']
    · have hflip' : quantumIsingDisagreementCount tau sigma ≠ 1 := by
        rw [quantumIsingDisagreementCount_comm]
        exact hflip
      simp [quantumIsingHamiltonian, heq, heq', hflip, hflip']


noncomputable def quantumIsingBoltzmannGenerator
    (beta h : Real) (L : Nat) :
    Matrix (QuantumIsingChainConfig L) (QuantumIsingChainConfig L) Complex :=
  (-beta : Complex) • quantumIsingHamiltonian h L

theorem quantumIsingBoltzmannGenerator_apply
    (beta h : Real) (L : Nat)
    (sigma tau : QuantumIsingChainConfig L) :
    quantumIsingBoltzmannGenerator beta h L sigma tau =
      if sigma = tau then
        (beta / 4 * quantumIsingChainInteraction L sigma : Real)
      else if quantumIsingDisagreementCount sigma tau = 1 then
        (beta * h / 2 : Real)
      else 0 := by
  by_cases heq : sigma = tau
  · subst tau
    simp [quantumIsingBoltzmannGenerator,
      quantumIsingHamiltonian, div_eq_mul_inv]
    ring
  · by_cases hflip : quantumIsingDisagreementCount sigma tau = 1
    · simp [quantumIsingBoltzmannGenerator,
        quantumIsingHamiltonian, heq, hflip, div_eq_mul_inv]
      ring
    · simp [quantumIsingBoltzmannGenerator,
        quantumIsingHamiltonian, heq, hflip]


noncomputable def quantumIsingQuantumPartition
    (beta h : Real) (L : Nat) : Complex :=
  (NormedSpace.exp (quantumIsingBoltzmannGenerator beta h L)).trace



noncomputable def quantumIsingTrotterStep
    (beta h : Real) (L : Nat) (t : Real) :
    Matrix (QuantumIsingChainConfig L) (QuantumIsingChainConfig L) Complex :=
  fun sigma tau =>
    (Real.exp (t * (beta / 4 * quantumIsingChainInteraction L sigma)) : Complex) *
      ((t * (beta * h / 2) : Real) : Complex) ^
        quantumIsingDisagreementCount sigma tau

private theorem prod_if_ne_eq_pow_card {L : Nat}
    (sigma tau : QuantumIsingChainConfig L) (a : Real) :
    (∏ i : Fin L, if sigma i = tau i then (1 : Real) else a) =
      a ^ quantumIsingDisagreementCount sigma tau := by
  classical
  let S : Finset (Fin L) := Finset.univ
  have hgeneral : forall T : Finset (Fin L),
      (∏ i ∈ T, if sigma i = tau i then (1 : Real) else a) =
        a ^ ((T.filter fun i => sigma i ≠ tau i).card) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert i T hi ih =>
        by_cases heq : sigma i = tau i
        · simp [Finset.prod_insert hi, Finset.filter_insert, heq, ih]
        · simp [Finset.prod_insert hi, Finset.filter_insert, hi, heq, ih, pow_succ']
  simpa [S, quantumIsingDisagreementCount, quantumIsingDisagreementSet]
    using hgeneral S

theorem quantumIsingTrotterTransferKernel_eq_step
    (beta h : Real) (n L : Nat) (hn : n ≠ 0)
    (sigma tau : QuantumIsingChainConfig L) :
    (quantumIsingTrotterTransferKernel beta h n L sigma tau : Complex) =
      quantumIsingTrotterStep beta h L (1 / n) sigma tau := by
  unfold quantumIsingTrotterTransferKernel quantumIsingSpatialTrotterWeight
  rw [show (∏ i : Fin L,
      quantumIsingTrotterKernel beta h n (sigma i) (tau i)) =
      (beta * h / (2 * n)) ^ quantumIsingDisagreementCount sigma tau by
    unfold quantumIsingTrotterKernel
    rw [prod_if_ne_eq_pow_card]
  ]
  unfold quantumIsingTrotterStep
  have hspace :
      beta / (4 * (n : Real)) * quantumIsingChainInteraction L sigma =
        (1 / (n : Real)) *
          (beta / 4 * quantumIsingChainInteraction L sigma) := by
    field_simp [hn]
  have hfield : beta * h / (2 * (n : Real)) =
      (1 / (n : Real)) * (beta * h / 2) := by
    field_simp [hn]
  rw [hspace, hfield]
  push_cast
  rfl

theorem quantumIsingTrotterTransferMatrix_eq_step
    (beta h : Real) (n L : Nat) (hn : n ≠ 0) :
    quantumIsingTrotterTransferMatrix beta h n L =
      quantumIsingTrotterStep beta h L (1 / n) := by
  ext sigma tau
  exact quantumIsingTrotterTransferKernel_eq_step beta h n L hn sigma tau


@[simp] theorem quantumIsingTrotterStep_zero
    (beta h : Real) (L : Nat) :
    quantumIsingTrotterStep beta h L 0 = 1 := by
  ext sigma tau
  by_cases heq : sigma = tau
  · subst tau
    simp [quantumIsingTrotterStep]
  · have hcount : quantumIsingDisagreementCount sigma tau ≠ 0 :=
      (quantumIsingDisagreementCount_eq_zero_iff sigma tau).not.mpr heq
    simp [quantumIsingTrotterStep, heq, hcount,
      zero_pow]



theorem quantumIsingTrotterStep_entry_hasDerivAt_zero
    (beta h : Real) (L : Nat)
    (sigma tau : QuantumIsingChainConfig L) :
    HasDerivAt (fun t => quantumIsingTrotterStep beta h L t sigma tau)
      (quantumIsingBoltzmannGenerator beta h L sigma tau) 0 := by
  let a : Real := beta / 4 * quantumIsingChainInteraction L sigma
  let b : Real := beta * h / 2
  have hexp : HasDerivAt (fun t : Real => (Real.exp (t * a) : Complex)) a 0 := by
    convert ((Real.hasDerivAt_exp (0 * a)).comp 0
      ((hasDerivAt_id 0).mul_const a)).ofReal_comp using 1
    all_goals simp
  have hlinear : HasDerivAt
      (fun t : Real => ((t * b : Real) : Complex)) b 0 := by
    convert ((hasDerivAt_id 0).mul_const b).ofReal_comp using 1
    all_goals simp
  by_cases heq : sigma = tau
  · subst tau
    simpa only [quantumIsingTrotterStep,
      quantumIsingDisagreementCount_self, pow_zero, mul_one,
      quantumIsingBoltzmannGenerator_apply, ↓reduceIte, a] using hexp
  · by_cases hflip : quantumIsingDisagreementCount sigma tau = 1
    · simpa [quantumIsingTrotterStep, hflip,
        quantumIsingBoltzmannGenerator_apply, heq, a, b]
        using hexp.mul hlinear
    · have hcount : 2 ≤ quantumIsingDisagreementCount sigma tau := by
        have hnezero : quantumIsingDisagreementCount sigma tau ≠ 0 :=
          (quantumIsingDisagreementCount_eq_zero_iff sigma tau).not.mpr heq
        omega
      have hcount0 : quantumIsingDisagreementCount sigma tau ≠ 0 := by omega
      have hcountPred : quantumIsingDisagreementCount sigma tau - 1 ≠ 0 := by omega
      simpa [quantumIsingTrotterStep,
        quantumIsingBoltzmannGenerator_apply, heq, hflip, a, b,
        zero_pow hcount0, zero_pow hcountPred]
        using hexp.mul (hlinear.pow
          (quantumIsingDisagreementCount sigma tau))

end StatMech.FrontierA
