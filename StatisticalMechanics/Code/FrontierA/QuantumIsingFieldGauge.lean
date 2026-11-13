/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingFiniteHamiltonian









open Matrix
open scoped Norms.Operator

namespace StatMech.FrontierA


def quantumIsingFieldGaugeSign {L : Nat}
    (sigma : QuantumIsingChainConfig L) : Real :=
  ∏ i : Fin L, quantumIsingSpinSign (sigma i)

@[simp] theorem quantumIsingFieldGaugeSign_sq {L : Nat}
    (sigma : QuantumIsingChainConfig L) :
    quantumIsingFieldGaugeSign sigma * quantumIsingFieldGaugeSign sigma = 1 := by
  unfold quantumIsingFieldGaugeSign
  rw [← Finset.prod_mul_distrib]
  simp [quantumIsingSpinSign_mul_self]

private theorem quantumIsingSpinSign_eq_neg_of_ne {s t : Bool} (hst : s ≠ t) :
    quantumIsingSpinSign s = -quantumIsingSpinSign t := by
  cases s <;> cases t <;> simp_all [quantumIsingSpinSign]


theorem quantumIsingFieldGaugeSign_eq_neg_of_disagreementCount_eq_one
    {L : Nat} (sigma tau : QuantumIsingChainConfig L)
    (hcount : quantumIsingDisagreementCount sigma tau = 1) :
    quantumIsingFieldGaugeSign sigma = -quantumIsingFieldGaugeSign tau := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcount
  have hdiff : sigma i ≠ tau i := by
    have : i ∈ quantumIsingDisagreementSet sigma tau := by simp [hi]
    simpa [quantumIsingDisagreementSet] using this
  have hout (j : Fin L) (hji : j ≠ i) : sigma j = tau j := by
    by_contra hne
    have hj : j ∈ quantumIsingDisagreementSet sigma tau := by
      simp [quantumIsingDisagreementSet, hne]
    rw [hi] at hj
    exact hji (Finset.mem_singleton.mp hj)
  unfold quantumIsingFieldGaugeSign
  rw [← Finset.univ.mul_prod_erase
      (fun j => quantumIsingSpinSign (sigma j)) (Finset.mem_univ i),
    ← Finset.univ.mul_prod_erase
      (fun j => quantumIsingSpinSign (tau j)) (Finset.mem_univ i)]
  have herase :
      ∏ j ∈ Finset.univ.erase i, quantumIsingSpinSign (sigma j) =
        ∏ j ∈ Finset.univ.erase i, quantumIsingSpinSign (tau j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [hout j (Finset.ne_of_mem_erase hj)]
  rw [herase, quantumIsingSpinSign_eq_neg_of_ne hdiff]
  ring


noncomputable def quantumIsingFieldGaugeMatrix (L : Nat) :
    Matrix (QuantumIsingChainConfig L) (QuantumIsingChainConfig L) Complex :=
  diagonal fun sigma => (quantumIsingFieldGaugeSign sigma : Complex)

@[simp] theorem quantumIsingFieldGaugeMatrix_sq (L : Nat) :
    quantumIsingFieldGaugeMatrix L * quantumIsingFieldGaugeMatrix L = 1 := by
  ext sigma tau
  by_cases heq : sigma = tau
  · subst tau
    have hg : (quantumIsingFieldGaugeSign sigma : Complex) *
        quantumIsingFieldGaugeSign sigma = 1 := by
      exact_mod_cast quantumIsingFieldGaugeSign_sq sigma
    simp [quantumIsingFieldGaugeMatrix, hg]
  · simp [quantumIsingFieldGaugeMatrix, heq]


theorem quantumIsingFieldGaugeMatrix_mul_hamiltonian_mul
    (h : Real) (L : Nat) :
    quantumIsingFieldGaugeMatrix L * quantumIsingHamiltonian h L *
        quantumIsingFieldGaugeMatrix L =
      quantumIsingHamiltonian (-h) L := by
  ext sigma tau
  simp only [quantumIsingFieldGaugeMatrix, diagonal_mul, mul_diagonal]
  by_cases heq : sigma = tau
  · subst tau
    rw [quantumIsingHamiltonian_apply_diag,
      quantumIsingHamiltonian_apply_diag]
    have hg : (quantumIsingFieldGaugeSign sigma : Complex) *
        quantumIsingFieldGaugeSign sigma = 1 := by
      exact_mod_cast quantumIsingFieldGaugeSign_sq sigma
    calc
      (quantumIsingFieldGaugeSign sigma : Complex) *
          (-(quantumIsingChainInteraction L sigma : Complex) / 4) *
          quantumIsingFieldGaugeSign sigma =
        ((quantumIsingFieldGaugeSign sigma : Complex) *
          quantumIsingFieldGaugeSign sigma) *
          (-(quantumIsingChainInteraction L sigma : Complex) / 4) := by ring
      _ = _ := by rw [hg, one_mul]
  · by_cases hflip : quantumIsingDisagreementCount sigma tau = 1
    · rw [quantumIsingHamiltonian_apply_oneFlip _ _ _ _ heq hflip,
        quantumIsingHamiltonian_apply_oneFlip _ _ _ _ heq hflip]
      rw [quantumIsingFieldGaugeSign_eq_neg_of_disagreementCount_eq_one
        sigma tau hflip]
      push_cast
      have hgt : (quantumIsingFieldGaugeSign tau : Complex) ^ 2 = 1 := by
        rw [pow_two]
        exact_mod_cast quantumIsingFieldGaugeSign_sq tau
      calc
        -(quantumIsingFieldGaugeSign tau : Complex) * (-(h : Complex) / 2) *
            quantumIsingFieldGaugeSign tau =
          (quantumIsingFieldGaugeSign tau : Complex) ^ 2 * (h / 2) := by ring
        _ = -(-(h : Complex)) / 2 := by rw [hgt]; ring
    · rw [quantumIsingHamiltonian_apply_other _ _ _ _ heq hflip,
        quantumIsingHamiltonian_apply_other _ _ _ _ heq hflip]
      simp


theorem quantumIsingFieldGaugeMatrix_mul_generator_mul
    (beta h : Real) (L : Nat) :
    quantumIsingFieldGaugeMatrix L *
        quantumIsingBoltzmannGenerator beta h L *
        quantumIsingFieldGaugeMatrix L =
      quantumIsingBoltzmannGenerator beta (-h) L := by
  rw [quantumIsingBoltzmannGenerator, quantumIsingBoltzmannGenerator]
  rw [mul_smul_comm, smul_mul_assoc]
  rw [quantumIsingFieldGaugeMatrix_mul_hamiltonian_mul]


theorem quantumIsingQuantumPartition_neg_field
    (beta h : Real) (L : Nat) :
    quantumIsingQuantumPartition beta (-h) L =
      quantumIsingQuantumPartition beta h L := by
  let G := quantumIsingFieldGaugeMatrix L
  let C := quantumIsingBoltzmannGenerator beta h L
  let Cneg := quantumIsingBoltzmannGenerator beta (-h) L
  have hGG : G * G = 1 := quantumIsingFieldGaugeMatrix_sq L
  have hconj : G * C * G = Cneg :=
    quantumIsingFieldGaugeMatrix_mul_generator_mul beta h L
  have hsemi : SemiconjBy G C Cneg := by
    rw [SemiconjBy]
    calc
      G * C = G * C * 1 := by rw [mul_one]
      _ = G * C * (G * G) := by rw [hGG]
      _ = (G * C * G) * G := by noncomm_ring
      _ = Cneg * G := by rw [hconj]
  have hexpSemi := hsemi.exp_right
  change G * NormedSpace.exp C = NormedSpace.exp Cneg * G at hexpSemi
  have hexpConj : NormedSpace.exp Cneg =
      G * NormedSpace.exp C * G := by
    calc
      NormedSpace.exp Cneg = NormedSpace.exp Cneg * 1 := by rw [mul_one]
      _ = NormedSpace.exp Cneg * (G * G) := by rw [hGG]
      _ = (NormedSpace.exp Cneg * G) * G := by noncomm_ring
      _ = (G * NormedSpace.exp C) * G :=
        congrArg (fun A => A * G) hexpSemi.symm
  unfold quantumIsingQuantumPartition
  change (NormedSpace.exp Cneg).trace = (NormedSpace.exp C).trace
  rw [hexpConj, Matrix.trace_mul_cycle G (NormedSpace.exp C) G,
    hGG, one_mul]

end StatMech.FrontierA
