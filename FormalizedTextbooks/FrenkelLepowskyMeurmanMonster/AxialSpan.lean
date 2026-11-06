/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneralAxialVector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

/-! Spanning prerequisites for Conway short axes and their triality images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

-- Matrix aliases must reduce when comparing explicit rank-one coordinates.
set_option backward.isDefEq.respectTransparency false

def dictionaryInitialBlocks (d : Fin 24 → ℝ) (a : Fin 3 → Fin 276 → ℝ)
    (t : Fin 759 → Fin 64 → ℝ) (x : Fin 49152 → ℝ) : TrialityBlocks :=
  (d, (a, (t, Pi.single 0 x)))

def dictionaryXYZBlocks (s : Fin 3) (x : Fin 49152 → ℝ) : TrialityBlocks :=
  (0, (0, (0, Pi.single s x)))

noncomputable def dictionaryXYZVector (s : Fin 3) (x : Fin 49152 → ℝ) : GriessSpace :=
  trialityBlocksEquiv.symm (dictionaryXYZBlocks s x)

lemma dictionaryXYZVector_triality (s : Fin 3) (x : Fin 49152 → ℝ) :
    sExtra (dictionaryXYZVector s x) = dictionaryXYZVector (trialityCycle s) x := by
  apply trialityBlocksEquiv.injective
  change trialityBlocksEquiv (griessTriality (trialityBlocksEquiv.symm (dictionaryXYZBlocks s x))) =
    trialityBlocksEquiv (trialityBlocksEquiv.symm (dictionaryXYZBlocks (trialityCycle s) x))
  simp only [griessTriality, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change trialityBlockAction (dictionaryXYZBlocks s x) = dictionaryXYZBlocks (trialityCycle s) x
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact map_zero (trialityCycleAction 276)
    · apply Prod.ext
      · exact map_zero (LinearEquiv.piCongrRight fun _ : Fin 759 => trialityOctadAction)
      · change trialityCycleAction 49152 (Pi.single s x) = Pi.single (trialityCycle s) x
        funext i k
        change (Pi.single s x : Fin 3 → Fin 49152 → ℝ) (trialityCycle.symm i) k =
          (Pi.single (trialityCycle s) x : Fin 3 → Fin 49152 → ℝ) i k
        simp only [Pi.single_apply]
        have he : trialityCycle.symm i = s ↔ i = trialityCycle s := by
          constructor
          · intro h; rw [← h, Equiv.apply_symm_apply]
          · intro h; rw [h, Equiv.symm_apply_apply]
        simp only [he]

lemma dictionaryXYZVector_first_image (x : Fin 49152 → ℝ) :
    sExtra (dictionaryXYZVector 0 x) = dictionaryXYZVector 1 x := by
  rw [dictionaryXYZVector_triality]
  rfl
lemma dictionaryXYZVector_second_image (x : Fin 49152 → ℝ) :
    sExtra (sExtra (dictionaryXYZVector 0 x)) = dictionaryXYZVector 2 x := by
  rw [dictionaryXYZVector_first_image, dictionaryXYZVector_triality]
  rfl

lemma dictionaryBlocks_decompose (b : TrialityBlocks) :
    b = dictionaryInitialBlocks b.1 b.2.1 b.2.2.1 (b.2.2.2 0) +
      dictionaryXYZBlocks 1 (b.2.2.2 1) + dictionaryXYZBlocks 2 (b.2.2.2 2) := by
  apply Prod.ext
  · simp [dictionaryInitialBlocks, dictionaryXYZBlocks]
  · apply Prod.ext
    · simp [dictionaryInitialBlocks, dictionaryXYZBlocks]
    · apply Prod.ext
      · simp [dictionaryInitialBlocks, dictionaryXYZBlocks]
      · funext s k
        obtain hs : s = 0 ∨ s = 1 ∨ s = 2 := by omega
        rcases hs with rfl | rfl | rfl <;>
          simp [dictionaryInitialBlocks, dictionaryXYZBlocks]

/-- Containing the initial dictionary blocks and the first two triality
images of X suffices to contain the entire Griess space. -/
theorem submodule_eq_top_of_initial_and_triality (P : Submodule ℝ GriessSpace)
    (hinitial : ∀ d a t x, trialityBlocksEquiv.symm (dictionaryInitialBlocks d a t x) ∈ P)
    (hfirst : ∀ x, sExtra (dictionaryXYZVector 0 x) ∈ P)
    (hsecond : ∀ x, sExtra (sExtra (dictionaryXYZVector 0 x)) ∈ P) : P = ⊤ := by
  apply P.eq_top_iff'.mpr
  intro g
  let b := trialityBlocksEquiv g
  have h1 : dictionaryXYZVector 1 (b.2.2.2 1) ∈ P := by
    rw [← dictionaryXYZVector_first_image]
    exact hfirst _
  have h2 : dictionaryXYZVector 2 (b.2.2.2 2) ∈ P := by
    rw [← dictionaryXYZVector_second_image]
    exact hsecond _
  have h := P.add_mem (P.add_mem (hinitial b.1 b.2.1 b.2.2.1 (b.2.2.2 0)) h1) h2
  have hg : g = trialityBlocksEquiv.symm (dictionaryInitialBlocks b.1 b.2.1 b.2.2.1 (b.2.2.2 0)) +
      dictionaryXYZVector 1 (b.2.2.2 1) + dictionaryXYZVector 2 (b.2.2.2 2) := by
    have hb := congrArg trialityBlocksEquiv.symm (dictionaryBlocks_decompose b)
    simpa only [b, map_add, dictionaryXYZVector, LinearEquiv.symm_apply_apply] using hb
  rw [hg]
  exact h

noncomputable def axialRawMatrixLinear : Matrix (Fin 24) (Fin 24) ℝ →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp (LinearMap.inl ℝ _ _)

noncomputable def axialRawShortLinear : (GriessShortIndex → ℝ) →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp
    ((LinearMap.inr ℝ _ _).comp (LinearMap.inl ℝ _ _))

lemma axialShort_basis_of_axes (P : Submodule ℝ GriessSpace)
    (haxes : ∀ r c, conwayShortAxis r c ∈ P) (r : GriessShortIndex) :
    axialRawShortLinear (Pi.single r 1) ∈ P := by
  have hraw : conwayShortAxisRaw r 1 - conwayShortAxisRaw r 0 =
      (16 : ℝ) • ((0, (Pi.single r 1, 0)) : ConwayRawSpace) := by
    have hs : qSign (1 : ZMod 2) = -1 := by norm_num [qSign]
    apply Prod.ext
    · simp [conwayShortAxisRaw]
    · apply Prod.ext
      · funext s
        simp only [conwayShortAxisRaw, hs, qSign_zero, Prod.fst_sub, Prod.snd_sub,
          Prod.smul_fst, Prod.smul_snd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · simp [conwayShortAxisRaw]
  have h : (16 : ℝ) • axialRawShortLinear (Pi.single r 1) ∈ P := by
    have hm := P.sub_mem (haxes r 1) (haxes r 0)
    change griessConwayDecodeLinear (conwayShortAxisRaw r 1) -
      griessConwayDecodeLinear (conwayShortAxisRaw r 0) ∈ P at hm
    rw [← map_sub, hraw, map_smul] at hm
    exact hm
  have hscaled := P.smul_mem (1/16 : ℝ) h
  simpa only [smul_smul, show (1/16:ℝ)*16=1 by norm_num, one_smul] using hscaled

lemma axialMatrix_rankone_of_axes (P : Submodule ℝ GriessSpace)
    (haxes : ∀ r c, conwayShortAxis r c ∈ P) (r : GriessShortIndex) :
    axialRawMatrixLinear (Matrix.vecMulVec (griessShortVector r) (griessShortVector r)) ∈ P := by
  have hraw : conwayShortAxisRaw r 0 + conwayShortAxisRaw r 1 =
      (4 : ℝ) • (Matrix.vecMulVec (griessShortVector r) (griessShortVector r), (0, 0)) := by
    have hs : qSign (1 : ZMod 2) = -1 := by norm_num [qSign]
    apply Prod.ext
    · ext i j
      simp only [conwayShortAxisRaw, Prod.fst_add, Prod.smul_fst, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul]
      ring
    · apply Prod.ext
      · funext s
        simp only [conwayShortAxisRaw, hs, qSign_zero, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
          smul_eq_mul, mul_zero]
        ring
      · simp [conwayShortAxisRaw]
  have h : (4 : ℝ) • axialRawMatrixLinear
      (Matrix.vecMulVec (griessShortVector r) (griessShortVector r)) ∈ P := by
    have hm := P.add_mem (haxes r 0) (haxes r 1)
    change griessConwayDecodeLinear (conwayShortAxisRaw r 0) +
      griessConwayDecodeLinear (conwayShortAxisRaw r 1) ∈ P at hm
    rw [← map_add, hraw, map_smul] at hm
    exact hm
  have hscaled := P.smul_mem (1/4 : ℝ) h
  simpa only [smul_smul, show (1/4:ℝ)*4=1 by norm_num, one_smul] using hscaled

lemma axialShort_all_of_axes (P : Submodule ℝ GriessSpace)
    (haxes : ∀ r c, conwayShortAxis r c ∈ P) (x : GriessShortIndex → ℝ) :
    axialRawShortLinear x ∈ P := by
  rw [pi_eq_sum_univ' x, map_sum]
  apply P.sum_mem
  intro r _
  rw [map_smul]
  exact P.smul_mem _ (axialShort_basis_of_axes P haxes r)


noncomputable def axialDiagMatrix (i : Fin 24) : Matrix (Fin 24) (Fin 24) ℝ :=
  Matrix.vecMulVec (leechUnit i) (leechUnit i)
noncomputable def axialOffMatrix (i j : Fin 24) : Matrix (Fin 24) (Fin 24) ℝ :=
  Matrix.vecMulVec (leechUnit i) (leechUnit j) + Matrix.vecMulVec (leechUnit j) (leechUnit i)

lemma axialPairScale_sq : (4 / Real.sqrt 8 : ℝ) * (4 / Real.sqrt 8) = 2 := by
  rw [div_mul_div_comm]
  norm_num [Real.mul_self_sqrt (show (0:ℝ) ≤ 8 by norm_num)]

lemma axialPairOuter_plus (i j : Fin 24) (hij : i ≠ j) :
    Matrix.vecMulVec (griessShortVector (Sum.inl (1, griessPairIndex i j hij)))
      (griessShortVector (Sum.inl (1, griessPairIndex i j hij))) =
      (2:ℝ) • (axialDiagMatrix i + axialDiagMatrix j + axialOffMatrix i j) := by
  rw [leech_pair_vector_short]
  ext k l
  simp only [Matrix.vecMulVec, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    axialDiagMatrix, axialOffMatrix, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply]
  calc
    _ = ((4 / Real.sqrt 8) * (4 / Real.sqrt 8)) *
        ((leechUnit i k + leechUnit j k) * (leechUnit i l + leechUnit j l)) := by ring
    _ = _ := by rw [axialPairScale_sq]; ring

lemma axialPairOuter_minus (i j : Fin 24) (hij : i ≠ j) :
    Matrix.vecMulVec (griessShortVector (Sum.inl (0, griessPairIndex i j hij)))
      (griessShortVector (Sum.inl (0, griessPairIndex i j hij))) =
      (2:ℝ) • (axialDiagMatrix i + axialDiagMatrix j - axialOffMatrix i j) := by
  ext k l
  simp only [Matrix.vecMulVec, griessShortVector, griessShortIntegral,
    griessPairIndex_coordinates, ite_true]
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  by_cases hlt : i < j
  · simp only [ite_eq_left hlt, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      axialDiagMatrix, axialOffMatrix, Matrix.vecMulVec, leechUnit, Pi.single_apply,
      Matrix.of_apply, smul_eq_mul]
    push_cast
    rw [div_mul_div_comm, hs]
    simp only [eq_comm]
    ring
  · simp only [ite_eq_right hlt, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      axialDiagMatrix, axialOffMatrix, Matrix.vecMulVec, leechUnit, Pi.single_apply,
      Matrix.of_apply, smul_eq_mul]
    push_cast
    rw [div_mul_div_comm, hs]
    simp only [eq_comm]
    ring

lemma axialMatrix_diagSum_of_axes (P : Submodule ℝ GriessSpace)
    (haxes : ∀ r c, conwayShortAxis r c ∈ P) (i j : Fin 24) (hij : i ≠ j) :
    axialRawMatrixLinear (axialDiagMatrix i + axialDiagMatrix j) ∈ P := by
  have hp := axialMatrix_rankone_of_axes P haxes (Sum.inl (1, griessPairIndex i j hij))
  have hm := axialMatrix_rankone_of_axes P haxes (Sum.inl (0, griessPairIndex i j hij))
  rw [axialPairOuter_plus, map_smul] at hp
  rw [axialPairOuter_minus, map_smul] at hm
  have h : (4:ℝ) • axialRawMatrixLinear (axialDiagMatrix i + axialDiagMatrix j) ∈ P := by
    have h := P.add_mem hp hm
    rw [map_add, map_sub, map_add] at h
    rw [map_add]
    convert h using 1
    module
  have h := P.smul_mem (1/4:ℝ) h
  simpa only [smul_smul, show (1/4:ℝ)*4=1 by norm_num, one_smul] using h

lemma axialMatrix_off_of_axes (P : Submodule ℝ GriessSpace)
    (haxes : ∀ r c, conwayShortAxis r c ∈ P) (i j : Fin 24) (hij : i ≠ j) :
    axialRawMatrixLinear (axialOffMatrix i j) ∈ P := by
  have hp := axialMatrix_rankone_of_axes P haxes (Sum.inl (1, griessPairIndex i j hij))
  have hm := axialMatrix_rankone_of_axes P haxes (Sum.inl (0, griessPairIndex i j hij))
  rw [axialPairOuter_plus, map_smul] at hp
  rw [axialPairOuter_minus, map_smul] at hm
  have h : (4:ℝ) • axialRawMatrixLinear (axialOffMatrix i j) ∈ P := by
    have h := P.sub_mem hp hm
    rw [map_add, map_sub, map_add] at h
    convert h using 1
    module
  have h := P.smul_mem (1/4:ℝ) h
  simpa only [smul_smul, show (1/4:ℝ)*4=1 by norm_num, one_smul] using h

lemma axialMatrix_diag_of_axes (P : Submodule ℝ GriessSpace)
    (haxes : ∀ r c, conwayShortAxis r c ∈ P) (i : Fin 24) :
    axialRawMatrixLinear (axialDiagMatrix i) ∈ P := by
  have h0 : axialRawMatrixLinear (axialDiagMatrix 0) ∈ P := by
    have h01 := axialMatrix_diagSum_of_axes P haxes 0 1 (by decide)
    have h02 := axialMatrix_diagSum_of_axes P haxes 0 2 (by decide)
    have h12 := axialMatrix_diagSum_of_axes P haxes 1 2 (by decide)
    have h := P.smul_mem (1/2:ℝ) (P.sub_mem (P.add_mem h01 h02) h12)
    simp only [map_add] at h
    convert h using 1
    module
  by_cases hi : i=0
  · subst i; exact h0
  · have h := P.sub_mem (axialMatrix_diagSum_of_axes P haxes 0 i (Ne.symm hi)) h0
    simpa only [map_add, add_sub_cancel_left] using h

lemma axialSymmetric_decompose (A : Matrix (Fin 24) (Fin 24) ℝ)
    (hA : ∀ i j, A i j = A j i) :
    A = ∑ i, ∑ j, (A i j / 2) • axialOffMatrix i j := by
  ext k l
  simp only [Matrix.sum_apply, Matrix.smul_apply, axialOffMatrix, Matrix.add_apply,
    Matrix.vecMulVec, Matrix.of_apply, leechUnit, Pi.single_apply, smul_eq_mul]
  simp [mul_add, mul_ite, Finset.sum_add_distrib, hA k l]

lemma axialMatrix_symmetric_of_axes (P : Submodule ℝ GriessSpace)
    (haxes : ∀ r c, conwayShortAxis r c ∈ P) (A : Matrix (Fin 24) (Fin 24) ℝ)
    (hA : ∀ i j, A i j = A j i) : axialRawMatrixLinear A ∈ P := by
  rw [axialSymmetric_decompose A hA, map_sum]
  apply P.sum_mem
  intro i _
  rw [map_sum]
  apply P.sum_mem
  intro j _
  rw [map_smul]
  apply P.smul_mem
  by_cases hij : i=j
  · subst j
    have h := P.smul_mem (2:ℝ) (axialMatrix_diag_of_axes P haxes i)
    have hmat : axialOffMatrix i i = (2:ℝ) • axialDiagMatrix i := by
      ext k l
      simp [axialOffMatrix, axialDiagMatrix, two_mul]
    rwa [hmat, map_smul]
  · exact axialMatrix_off_of_axes P haxes i j hij


lemma dictionaryInitial_no_tensor (d : Fin 24 → ℝ) (a : Fin 3 → Fin 276 → ℝ)
    (t : Fin 759 → Fin 64 → ℝ) (x : Fin 49152 → ℝ) :
    (griessConwayEncode (trialityBlocksEquiv.symm (dictionaryInitialBlocks d a t x))).2.2 = 0 := by
  unfold griessConwayEncode
  rw [trialityBlocksEquiv.apply_symm_apply]
  funext s i
  simp [dictionaryInitialBlocks]

lemma dictionaryInitial_mem_of_axes (P : Submodule ℝ GriessSpace)
    (haxes : ∀ r c, conwayShortAxis r c ∈ P)
    (d : Fin 24 → ℝ) (a : Fin 3 → Fin 276 → ℝ)
    (t : Fin 759 → Fin 64 → ℝ) (x : Fin 49152 → ℝ) :
    trialityBlocksEquiv.symm (dictionaryInitialBlocks d a t x) ∈ P := by
  let g := trialityBlocksEquiv.symm (dictionaryInitialBlocks d a t x)
  let y := griessConwayEncode g
  have ht : y.2.2 = 0 := dictionaryInitial_no_tensor d a t x
  have hmat := axialMatrix_symmetric_of_axes P haxes y.1 (griessConwayEncode_symmetric g)
  have hshort := axialShort_all_of_axes P haxes y.2.1
  have h := P.add_mem hmat hshort
  change griessConwayDecodeLinear (y.1, (0, 0)) + griessConwayDecodeLinear (0, (y.2.1, 0)) ∈ P at h
  rw [← map_add] at h
  have hy : (y.1, (0, 0)) + (0, (y.2.1, 0)) = y := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · simpa using ht.symm
  rw [hy] at h
  change griessConwayDecode (griessConwayEncode g) ∈ P at h
  rwa [griessConwayDecode_encode] at h

lemma dictionaryInitial_map_mem_of_axes (P : Submodule ℝ GriessSpace)
    (L : GriessSpace →ₗ[ℝ] GriessSpace)
    (haxes : ∀ r c, L (conwayShortAxis r c) ∈ P)
    (d : Fin 24 → ℝ) (a : Fin 3 → Fin 276 → ℝ)
    (t : Fin 759 → Fin 64 → ℝ) (x : Fin 49152 → ℝ) :
    L (trialityBlocksEquiv.symm (dictionaryInitialBlocks d a t x)) ∈ P :=
  dictionaryInitial_mem_of_axes (P.comap L) haxes d a t x

theorem submodule_eq_top_of_axes_and_images (P : Submodule ℝ GriessSpace)
    (h0 : ∀ r c, conwayShortAxis r c ∈ P)
    (h1 : ∀ r c, sExtra (conwayShortAxis r c) ∈ P)
    (h2 : ∀ r c, sExtra (sExtra (conwayShortAxis r c)) ∈ P) : P = ⊤ := by
  apply submodule_eq_top_of_initial_and_triality P
  · exact dictionaryInitial_mem_of_axes P h0
  · intro x
    exact dictionaryInitial_map_mem_of_axes P sExtra.toLinearMap h1 0 0 0 x
  · intro x
    exact dictionaryInitial_map_mem_of_axes P
      (sExtra.toLinearMap.comp sExtra.toLinearMap) h2 0 0 0 x

-- The finite coordinate encodings require additional kernel recursion depth.
set_option maxRecDepth 10000 in
/-- The explicitly finite family of both signs of every short axis, and
its first two triality images, spans all 196884 dictionary coordinates. -/
theorem span_short_axes_triality :
    Submodule.span ℝ
      (Set.range (fun rc : GriessShortIndex × ZMod 2 => conwayShortAxis rc.1 rc.2) ∪
        Set.range (fun rc : GriessShortIndex × ZMod 2 => sExtra (conwayShortAxis rc.1 rc.2)) ∪
        Set.range (fun rc : GriessShortIndex × ZMod 2 =>
          sExtra (sExtra (conwayShortAxis rc.1 rc.2)))) = ⊤ := by
  let P := Submodule.span ℝ
      (Set.range (fun rc : GriessShortIndex × ZMod 2 => conwayShortAxis rc.1 rc.2) ∪
        Set.range (fun rc : GriessShortIndex × ZMod 2 => sExtra (conwayShortAxis rc.1 rc.2)) ∪
        Set.range (fun rc : GriessShortIndex × ZMod 2 =>
          sExtra (sExtra (conwayShortAxis rc.1 rc.2))))
  have h0 (r : GriessShortIndex) (c : ZMod 2) : conwayShortAxis r c ∈ P := by
    apply Submodule.subset_span
    exact Or.inl (Or.inl ⟨(r, c), rfl⟩)
  have h1 (r : GriessShortIndex) (c : ZMod 2) : sExtra (conwayShortAxis r c) ∈ P := by
    apply Submodule.subset_span
    exact Or.inl (Or.inr ⟨(r, c), rfl⟩)
  have h2 (r : GriessShortIndex) (c : ZMod 2) : sExtra (sExtra (conwayShortAxis r c)) ∈ P := by
    apply Submodule.subset_span
    exact Or.inr ⟨(r, c), rfl⟩
  exact submodule_eq_top_of_axes_and_images P h0 h1 h2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
