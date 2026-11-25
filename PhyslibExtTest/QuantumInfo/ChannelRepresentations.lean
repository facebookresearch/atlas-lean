/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.ChannelRepresentations

/-!
# Tests: channel representations (Kraus, Choi, Stinespring)
-/

@[expose] public section

namespace PhyslibExtTest.QuantumInfo.ChannelRepresentations

set_option autoImplicit false

open PhyslibExt.QuantumInfo.Channels

#print axioms exists_cptpMap_iff_kraus
#print axioms exists_cptpMap_iff_choi
#print axioms transposeMap_not_isCompletelyPositive

/-- The transpose example separates positivity from complete positivity on
`Fin 2`: the same map passes one test and fails the other. -/
theorem transposeMap_fin2_positive_not_cp :
    (transposeMap (Fin 2)).IsPositive ∧
      ¬ (transposeMap (Fin 2)).IsCompletelyPositive := by
  constructor
  · first
      | exact transposeMap_isPositive (Fin 2)
      | exact transposeMap_isPositive
  · first
      | exact transposeMap_not_isCompletelyPositive (Fin 2)
      | exact transposeMap_not_isCompletelyPositive

/-- The identity channel has Kraus operators (the general existence
statement at a concrete channel), and they satisfy completeness. -/
theorem id_exists_kraus :
    ∃ K : (Fin 2 × Fin 2) → Matrix (Fin 2) (Fin 2) ℂ,
      (CPTPMap.id (dIn := Fin 2)).map = MatrixMap.of_kraus K K ∧
        ∑ k, (K k).conjTranspose * (K k) = 1 := by
  first
    | exact exists_kraus_of_cptpMap (CPTPMap.id (dIn := Fin 2))

/-- The singleton identity Kraus family is complete, gives the identity channel
through `ofKraus`, and through the backward direction of
`exists_cptpMap_iff_kraus`. -/
theorem ofKraus_singleton_id :
    let K : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ := fun _ => 1;
    (∑ k, (K k).conjTranspose * (K k) = 1) ∧
      ∀ hK : (∑ k, (K k).conjTranspose * (K k) = 1),
        (ofKraus K hK).map = MatrixMap.of_kraus K K ∧
          (∀ X, (ofKraus K hK).map X = X) ∧
          ∃ c : CPTPMap (dIn := Fin 2) (dOut := Fin 2),
            c.map = MatrixMap.of_kraus K K := by
  have hK1 : ∑ _ : Fin 1, ((1 : Matrix (Fin 2) (Fin 2) ℂ)).conjTranspose * 1 = 1 := by
    rw [Fin.sum_univ_one]
    simp
  refine ⟨?_, ?_⟩
  · simpa using hK1
  · intro hK
    refine ⟨?_, ?_, ?_⟩
    · exact ofKraus_map _ _
    · intro X
      rw [ofKraus_map]
      simp only [MatrixMap.of_kraus, LinearMap.sum_apply]
      rw [Fin.sum_univ_one]
      simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      rfl
    · set K2 : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
        fun p => if p = (0, 0) then 1 else 0 with hK2_def
      have hK2 : ∑ p, (K2 p).conjTranspose * (K2 p) = 1 := by
        simp only [hK2_def]
        rw [Finset.sum_eq_single (0, 0)]
        · simp
        · intro b _ hb
          simp [hb]
        · intro h
          simp at h
      have hId1 : ∀ X, MatrixMap.of_kraus (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℂ))
          (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℂ)) X = X := by
        intro X
        simp only [MatrixMap.of_kraus, LinearMap.sum_apply]
        rw [Fin.sum_univ_one]
        simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
        rfl
      have hId2 : ∀ X, MatrixMap.of_kraus K2 K2 X = X := by
        intro X
        simp only [MatrixMap.of_kraus, LinearMap.sum_apply, Finset.sum_apply, hK2_def]
        rw [Finset.sum_eq_single (0, 0)]
        · simp
        · intro b _ hb
          simp [hb]
        · intro h
          simp at h
      have heq : MatrixMap.of_kraus K2 K2 = MatrixMap.of_kraus
          (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℂ))
          (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
        apply LinearMap.ext
        intro X
        rw [hId2, hId1]
      exact (exists_cptpMap_iff_kraus _).2 ⟨K2, heq.symm, hK2⟩

end PhyslibExtTest.QuantumInfo.ChannelRepresentations
