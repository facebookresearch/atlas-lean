/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientZeroTools
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthTensorSquares
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthTensorState
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQSpinOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPairWitness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneCanonicalShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorOddShortTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityProduct

/-! The Eighth local family: no actual signed-short axis is orthogonal to the actual Eighth
prototype.

The prototype is positive triality applied to the actual local image of the odd axis. Its
matrix is diagonal with entries `1/4 + n_i^2/32` for the actual norm-eight numerator `n`, so
the matrix contraction against every actual short vector is at least one.

* Pair rows are `±n_a n_b/32`, and the pairing is `2 + (n_a ∓ n_b)^2/8`.
* Odd rows are `∓(ψ + ψ')F_i/2` for two genuine spin coefficients of square at most `1/1024`
  and an actual frame coordinate `|F_i| ≤ 4`, so their squares are below `1/16`.
* Octad rows are the actual octad triality of the middle octad block. The middle short
  coefficients are signed images of the original pair coefficients, and the supports of the
  264 forward pair images of octad shape are pairwise distinct (a checked decoding table), so
  each middle octad block has at most one nonzero entry, of square at most `9/16`. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The binary support mask of a Boolean coordinate predicate. -/
def generatedFeasibleAmbientSupportMask (P : Fin 24 → Bool) : ℕ :=
  ∑ i : Fin 24, if P i then 2 ^ i.val else 0

/-- The nonvanishing coordinates of the forward Eighth image of a signed coordinate pair, from
the actual frame numerators. -/
def generatedFeasibleAmbientEighthPairSupport (s : Fin 2) (a b i : Fin 24) : Bool :=
  decide (generatedEighthFrameVectorData 7 a i +
    (if s = 0 then -1 else 1) * generatedEighthFrameVectorData 7 b i ≠ 0)

/-- Support masks of the 264 forward pair images of octad shape, with their pair addresses. -/
def generatedFeasibleAmbientEighthOctadTable : List (ℕ × Fin 2 × Fin 24 × Fin 24) :=
    [(15728655, 0, 0, 1), (6030857, 0, 0, 2), (9830505, 0, 0, 3), (1122861, 0, 0, 6),
      (1131595, 0, 0, 7), (1315879, 0, 0, 8), (13730849, 0, 0, 9), (9438917, 0, 0, 16),
      (9438778, 0, 0, 19), (5245539, 0, 0, 20), (5244268, 0, 0, 22), (11273734, 0, 1, 2),
      (6684774, 0, 1, 3), (14754338, 0, 1, 6), (14763076, 0, 1, 7), (14947368, 0, 1, 8),
      (2196526, 0, 1, 9), (6293194, 0, 1, 16), (6293045, 0, 1, 19), (10488428, 0, 1, 20),
      (10487139, 0, 1, 22), (13239904, 0, 2, 3), (5055524, 0, 2, 6), (5063234, 0, 2, 7),
      (4723246, 0, 2, 8), (9273896, 0, 2, 9), (13369548, 0, 2, 16), (13369395, 0, 2, 19),
      (789610, 0, 2, 20), (787301, 0, 2, 22), (8856132, 0, 3, 6), (8864802, 0, 3, 7),
      (8524878, 0, 3, 8), (4686920, 0, 3, 9), (394924, 0, 3, 16), (394835, 0, 3, 19),
      (12978698, 0, 3, 20), (12977413, 0, 3, 22), (3825673, 0, 4, 5), (696467, 0, 4, 10),
      (706821, 0, 4, 11), (1171729, 0, 4, 12), (1970449, 0, 4, 13), (4354433, 0, 4, 14),
      (8943633, 0, 4, 15), (1627265, 0, 4, 17), (2282001, 0, 4, 18), (1226785, 0, 4, 21),
      (2666817, 0, 4, 23), (3195034, 0, 5, 10), (3189004, 0, 5, 11), (2851096, 0, 5, 12),
      (2388248, 0, 5, 13), (7868808, 0, 5, 14), (11671576, 0, 5, 15), (2274440, 0, 5, 17),
      (1618456, 0, 5, 18), (2676776, 0, 5, 21), (1233224, 0, 5, 23), (26214, 0, 6, 7),
      (341514, 0, 6, 8), (12625420, 0, 6, 9), (8463592, 0, 6, 16), (8463383, 0, 6, 19),
      (4270158, 0, 6, 20), (4269889, 0, 6, 22), (348268, 0, 7, 8), (12632170, 0, 7, 9),
      (8471182, 0, 7, 16), (8471153, 0, 7, 19), (4279848, 0, 7, 20), (4276519, 0, 7, 22),
      (12947462, 0, 8, 9), (8655586, 0, 8, 16), (8655389, 0, 8, 19), (4464196, 0, 8, 20),
      (4460875, 0, 8, 22), (4293348, 0, 9, 16), (4293147, 0, 9, 19), (8490562, 0, 9, 20),
      (8487245, 0, 9, 22), (27030, 0, 10, 11), (1786242, 0, 10, 12), (1356162, 0, 10, 13),
      (4772114, 0, 10, 14), (8575106, 0, 10, 15), (1209362, 0, 10, 17), (2650754, 0, 10, 18),
      (1579186, 0, 10, 21), (2232786, 0, 10, 23), (1779732, 0, 11, 12), (1366036, 0, 11, 13),
      (4765828, 0, 11, 14), (8565012, 0, 11, 15), (1187204, 0, 11, 17), (2628372, 0, 11, 18),
      (1601828, 0, 11, 21), (2259012, 0, 11, 23), (1044480, 0, 12, 13), (5476496, 0, 12, 14),
      (10066176, 0, 12, 15), (603536, 0, 12, 17), (3355392, 0, 12, 18), (219440, 0, 12, 21),
      (3756112, 0, 12, 23), (6054032, 0, 13, 14), (9857280, 0, 13, 15), (443792, 0, 13, 17),
      (3982080, 0, 13, 18), (829744, 0, 13, 21), (3579984, 0, 13, 23), (13240720, 0, 14, 15),
      (5940480, 0, 14, 17), (6333328, 0, 14, 18), (5294496, 0, 14, 21), (6996160, 0, 14, 23),
      (9481360, 0, 15, 17), (11184640, 0, 15, 18), (10141744, 0, 15, 21), (10537296, 0, 15, 23),
      (255, 0, 16, 19), (12586150, 0, 16, 20), (12583849, 0, 16, 22), (3802768, 0, 17, 18),
      (683168, 0, 17, 21), (3171776, 0, 17, 23), (3172912, 0, 18, 21), (680784, 0, 18, 23),
      (12586073, 0, 19, 20), (12583766, 0, 19, 22), (3855, 0, 20, 22), (3803488, 0, 21, 23),
      (3475040, 1, 0, 1), (10027110, 1, 0, 2), (5441030, 1, 0, 3), (13902914, 1, 0, 6),
      (13910564, 1, 0, 7), (13701704, 1, 0, 8), (1344078, 1, 0, 9), (5570730, 1, 0, 16),
      (5570645, 1, 0, 19), (9767948, 1, 0, 20), (9765635, 1, 0, 22), (6881385, 1, 1, 2),
      (10683913, 1, 1, 3), (2368589, 1, 1, 6), (2376235, 1, 1, 7), (2167367, 1, 1, 8),
      (14975553, 1, 1, 9), (10813605, 1, 1, 16), (10813530, 1, 1, 19), (6622211, 1, 1, 20),
      (6619916, 1, 1, 22), (983055, 1, 2, 3), (8921675, 1, 2, 6), (8930349, 1, 2, 7),
      (9245761, 1, 2, 8), (4752455, 1, 2, 9), (591523, 1, 2, 16), (591452, 1, 2, 19),
      (13175301, 1, 2, 20), (13174026, 1, 2, 22), (4334635, 1, 3, 6), (4342349, 1, 3, 7),
      (4657697, 1, 3, 8), (8552999, 1, 3, 9), (12779715, 1, 3, 16), (12779580, 1, 3, 19),
      (199781, 1, 3, 20), (197482, 1, 3, 22), (39321, 1, 4, 5), (3168515, 1, 4, 10),
      (3158165, 1, 4, 11), (2824321, 1, 4, 12), (2418817, 1, 4, 13), (7899153, 1, 4, 14),
      (11698561, 1, 4, 15), (2239761, 1, 4, 17), (1584001, 1, 4, 18), (2638257, 1, 4, 21),
      (1198289, 1, 4, 23), (669962, 1, 5, 10), (675996, 1, 5, 11), (1144968, 1, 5, 12),
      (2001032, 1, 5, 13), (4384792, 1, 5, 14), (8970632, 1, 5, 15), (1592600, 1, 5, 17),
      (2247560, 1, 5, 18), (1188280, 1, 5, 21), (2631896, 1, 5, 23), (12935177, 1, 6, 7),
      (12595301, 1, 6, 8), (368739, 1, 6, 9), (4465287, 1, 6, 16), (4465272, 1, 6, 19),
      (8662561, 1, 6, 20), (8659246, 1, 6, 22), (12604931, 1, 7, 8), (378373, 1, 7, 9),
      (4474081, 1, 7, 16), (4473886, 1, 7, 19), (8669255, 1, 7, 20), (8669000, 1, 7, 22),
      (38505, 1, 8, 9), (4265101, 1, 8, 16), (4265074, 1, 8, 19), (8460331, 1, 8, 20),
      (8460068, 1, 8, 22), (8684683, 1, 9, 16), (8684660, 1, 9, 19), (4491309, 1, 9, 20),
      (4491042, 1, 9, 22), (3837958, 1, 10, 11), (2209810, 1, 10, 12), (3033106, 1, 10, 13),
      (7481474, 1, 10, 14), (12067090, 1, 10, 15), (2657666, 1, 10, 17), (1215250, 1, 10, 18),
      (2285858, 1, 10, 21), (1632322, 1, 10, 23), (2216324, 1, 11, 12), (3023236, 1, 11, 13),
      (7487764, 1, 11, 14), (12077188, 1, 11, 15), (2679828, 1, 11, 17), (1237636, 1, 11, 18),
      (2263220, 1, 11, 21), (1606100, 1, 11, 23), (3475856, 1, 12, 13), (6908160, 1, 12, 14),
      (10707088, 1, 12, 15), (3394560, 1, 12, 17), (641680, 1, 12, 18), (3776672, 1, 12, 21),
      (240064, 1, 12, 23), (6723840, 1, 13, 14), (11309200, 1, 13, 15), (3947520, 1, 13, 17),
      (408208, 1, 13, 18), (3559584, 1, 13, 21), (809408, 1, 13, 23), (15790080, 1, 14, 15),
      (6315152, 1, 14, 17), (5921280, 1, 14, 18), (6959152, 1, 14, 21), (5257552, 1, 14, 23),
      (11162880, 1, 15, 17), (9458576, 1, 15, 18), (10500512, 1, 15, 21), (10105024, 1, 15, 23),
      (12912272, 1, 16, 19), (330441, 1, 16, 20), (329158, 1, 16, 22), (65280, 1, 17, 18),
      (3183920, 1, 17, 21), (695376, 1, 17, 23), (693152, 1, 18, 21), (3185344, 1, 18, 23),
      (330294, 1, 19, 20), (329017, 1, 19, 22), (12912992, 1, 20, 22), (61680, 1, 21, 23)]

/-- Decoding of an octad-shaped support mask to its unique forward pair address. -/
def generatedFeasibleAmbientEighthDecode (m : ℕ) : Option (Fin 2 × Fin 24 × Fin 24) :=
  (generatedFeasibleAmbientEighthOctadTable.find? fun t => t.1 == m).map Prod.snd

set_option maxRecDepth 100000 in
-- All 552 forward pair images are checked: full support, or decoded back to their address.
private theorem pair_support_certificate : ∀ s : Fin 2, ∀ a b : Fin 24, a < b →
    (∀ i, generatedFeasibleAmbientEighthPairSupport s a b i = true) ∨
      generatedFeasibleAmbientEighthDecode
        (generatedFeasibleAmbientSupportMask (generatedFeasibleAmbientEighthPairSupport s a b)) =
        some (s, a, b) := by
  unfold generatedFeasibleAmbientEighthDecode generatedFeasibleAmbientEighthOctadTable
    generatedFeasibleAmbientSupportMask generatedFeasibleAmbientEighthPairSupport
  decide +kernel

private theorem frame_sq : ∀ i : Fin 24, generatedEighthFrameVectorData 7 0 i ^ 2 ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
-- All 4096 actual octad Fourier entries are checked.
private theorem triality_entry_abs : ∀ e f : Fin 64, |trialityIntegerMatrix e f| = 1 := by
  unfold trialityIntegerMatrix trialityIntegerDiagonal trialityHadamard
  decide +kernel

private theorem qSign_cases (c : ZMod 2) : qSign c = 1 ∨ qSign c = -1 := by
  unfold qSign
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Diagonal entries of the actual Eighth prototype matrix. -/
noncomputable def generatedFeasibleAmbientEighthDiag (i : Fin 24) : ℝ :=
  1 / 4 + (generatedEighthNormEightVectorData 7 i : ℝ) ^ 2 / 32

/-- The actual Eighth prototype matrix is diagonal. -/
theorem generatedFeasibleAmbient_eighth_matrix :
    (griessConwayEncode generatedEighthAxis).1 =
      Matrix.diagonal generatedFeasibleAmbientEighthDiag := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, generatedEighth_matrix_diagonal_data]
    rfl
  · rw [Matrix.diagonal_apply_ne _ hij, generatedEighth_matrix_off_diagonal i j hij]

private theorem contraction_ge (r : GriessShortIndex) :
    1 ≤ axisMatrixContraction (griessShortVector r) (griessConwayEncode generatedEighthAxis).1 := by
  rw [generatedFeasibleAmbient_eighth_matrix, generatedFeasibleAmbient_diagonal_contraction]
  have hs := griessShortIntegral_squareSum r
  unfold leechSquareSum at hs
  have hs' : (∑ i, (griessShortIntegral r i : ℝ) ^ 2) = 32 := by exact_mod_cast hs
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin 24)), (griessShortIntegral r i : ℝ) ^ 2 / 32 ≤
      generatedFeasibleAmbientEighthDiag i * griessShortVector r i ^ 2 := by
    intro i _
    rw [generatedFeasibleAmbient_shortVector_sq]
    unfold generatedFeasibleAmbientEighthDiag
    have h1 := sq_nonneg (generatedEighthNormEightVectorData 7 i : ℝ)
    have h2 := sq_nonneg (griessShortIntegral r i : ℝ)
    nlinarith [mul_nonneg h1 h2]
  calc (1 : ℝ) = ∑ i, (griessShortIntegral r i : ℝ) ^ 2 / 32 := by
        rw [← Finset.sum_div, hs']
        norm_num
    _ ≤ _ := Finset.sum_le_sum hle

private theorem real_ne (q S σ : ℝ) (hq : 1 ≤ q) (hσ : σ = 1 ∨ σ = -1) (hS : S ^ 2 < 1 / 16) :
    2 * q - 8 * σ * S ≠ 0 := by
  intro h
  rcases hσ with rfl | rfl
  · have he : S = q / 4 := by linarith
    subst he
    nlinarith
  · have he : S = -(q / 4) := by linarith
    subst he
    nlinarith

/-- A short coordinate of square below `1/16` excludes orthogonality. -/
private theorem ne_of_sq_lt (r : GriessShortIndex) (c : ZMod 2)
    (h : ((griessConwayEncode generatedEighthAxis).2.1 r) ^ 2 < 1 / 16) :
    griessForm (conwayShortAxis r c) generatedEighthAxis ≠ 0 := by
  rw [generatedFeasibleAmbient_axis_form]
  exact real_ne _ _ _ (contraction_ge r) (qSign_cases c) h

/-! ### Pair rows -/

private theorem middle_matrix (i j : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedEighthLocalFiber)
      generatedOddAxis)).1 i j =
      ((if i = j then (8 : ℝ) else 0) +
        (generatedEighthNormEightVectorData 7 i : ℝ) *
          (generatedEighthNormEightVectorData 7 j : ℝ)) / 32 := by
  rw [generatedEighth_middle_matrix]
  have hv (k : Fin 24) : generatedNormEightVector generatedEighthNormEightVector k =
      (generatedEighthNormEightVectorData 7 k : ℝ) / Real.sqrt 8 := by
    simp only [generatedNormEightVector, generatedEighthNormEightVector_val,
      leechCoordinateEmbedding]
    rfl
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    generatedNormEightLineMatrix, Matrix.vecMulVec_apply, Matrix.one_apply]
  rw [hv, hv]
  have hs : Real.sqrt 8 ≠ 0 := by positivity
  have hr : (Real.sqrt 8) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  split_ifs <;> field_simp [hs] <;> rw [hr] <;> ring

/-- Every actual pair row of the Eighth prototype. -/
theorem generatedFeasibleAmbient_eighth_pair_short (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedEighthAxis).2.1 (Sum.inl (s, p)) =
      (if s = 0 then 1 else -1) *
        ((generatedEighthNormEightVectorData 7 (griessCoordinatePair p).1 : ℝ) *
          (generatedEighthNormEightVectorData 7 (griessCoordinatePair p).2 : ℝ)) / 32 := by
  rw [generatedEighthAxis_local_expression, generatedSeventhXi_pair_triality_coordinate,
    generatedEighth_middle_pair_zero, generatedEighth_middle_pair_zero, middle_matrix]
  have hn := griessCoordinatePair_ne p
  simp only [hn, ite_false, zero_add, sub_self, zero_div]
  split_ifs <;> ring

private theorem contraction_eq_pairing (M : Matrix (Fin 24) (Fin 24) ℝ) (r : GriessShortIndex) :
    axisMatrixContraction (griessShortVector r) M = conwayShortPairing M r := by
  unfold axisMatrixContraction conwayShortPairing
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem pair_ne (s : Fin 2) (p : Fin 276) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inl (s, p)) c) generatedEighthAxis ≠ 0 := by
  rw [generatedFeasibleAmbient_axis_form, generatedFeasibleAmbient_eighth_matrix,
    contraction_eq_pairing, conwayShortPairing_diagonal_pair,
    generatedFeasibleAmbient_eighth_pair_short]
  unfold generatedFeasibleAmbientEighthDiag
  have hA := sq_nonneg ((generatedEighthNormEightVectorData 7 (griessCoordinatePair p).1 : ℝ) -
    (generatedEighthNormEightVectorData 7 (griessCoordinatePair p).2 : ℝ))
  have hB := sq_nonneg ((generatedEighthNormEightVectorData 7 (griessCoordinatePair p).1 : ℝ) +
    (generatedEighthNormEightVectorData 7 (griessCoordinatePair p).2 : ℝ))
  rcases qSign_cases c with hc | hc <;> rw [hc] <;> split_ifs <;> intro h <;> nlinarith

/-! ### Odd rows -/

private theorem odd_real (σ ψ₁ ψ₂ F : ℝ) (hσ : σ ^ 2 = 1) (h₁ : ψ₁ ^ 2 ≤ 1 / 1024)
    (h₂ : ψ₂ ^ 2 ≤ 1 / 1024) (hF : F ^ 2 ≤ 16) :
    (σ * (generatedOddTensorScale * ψ₁ * (F / 8) + generatedOddTensorScale * ψ₂ * (F / 8)) /
      Real.sqrt 2) ^ 2 < 1 / 16 := by
  have hs : generatedOddTensorScale ^ 2 = 32 := by
    unfold generatedOddTensorScale
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hr : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have he : (σ * (generatedOddTensorScale * ψ₁ * (F / 8) +
      generatedOddTensorScale * ψ₂ * (F / 8)) / Real.sqrt 2) ^ 2 =
      σ ^ 2 * generatedOddTensorScale ^ 2 * ((ψ₁ + ψ₂) ^ 2 * F ^ 2) /
        (64 * Real.sqrt 2 ^ 2) := by
    ring
  rw [he, hσ, hs, hr]
  have hA : (ψ₁ + ψ₂) ^ 2 ≤ 1 / 256 := by nlinarith [sq_nonneg (ψ₁ - ψ₂)]
  have hP : (ψ₁ + ψ₂) ^ 2 * F ^ 2 ≤ 1 / 256 * 16 :=
    mul_le_mul hA hF (sq_nonneg _) (by norm_num)
  rw [div_lt_iff₀ (by norm_num)]
  linarith

/-- The genuine odd-row triality formula for the Eighth prototype. -/
private theorem odd_formula (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode generatedEighthAxis).2.1 (Sum.inr (Sum.inr (d, i))) =
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        ((griessConwayEncode (rhoLocal (localFiberIntoH generatedEighthLocalFiber)
            generatedOddAxis)).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i +
          (griessConwayEncode (rhoLocal (localFiberIntoH generatedEighthLocalFiber)
            generatedOddAxis)).2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) /
            Real.sqrt 2 := by
  rw [generatedEighthAxis_local_expression, monsterNortonTensor_extra_odd_short_coordinates]

private theorem frame_coordinate (i : Fin 24) :
    generatedEighthLocalFiber.val.2.val (Pi.single (0 : Fin 24) 1) i =
      (generatedEighthFrameVectorData 7 0 i : ℝ) / 8 := by
  change leechIsomMatrix generatedEighthLocalFiber.val.2 i 0 = _
  exact generatedEighth_forward_matrix_coordinate i 0

/-- Each middle tensor coordinate is the genuine spin state times an actual frame coordinate. -/
private theorem middle_tensor (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedEighthLocalFiber)
      generatedOddAxis)).2.2 t i =
      generatedOddTensorScale * generatedEighthSpinState t *
        ((generatedEighthFrameVectorData 7 0 i : ℝ) / 8) := by
  rw [generatedEighth_middle_tensor_rank_one, frame_coordinate]
  rfl

/-- Every actual odd row of the Eighth prototype has square below `1/16`. -/
private theorem odd_sq (d : Fin 2048) (i : Fin 24) :
    ((griessConwayEncode generatedEighthAxis).2.1 (Sum.inr (Sum.inr (d, i)))) ^ 2 < 1 / 16 := by
  rw [odd_formula, middle_tensor, middle_tensor]
  have hF : ((generatedEighthFrameVectorData 7 0 i : ℤ) : ℝ) ^ 2 ≤ 16 := by
    exact_mod_cast frame_sq i
  exact odd_real _ _ _ _ (by rw [pow_two, qSign_sq])
    (generatedEighth_spin_state_square_bound _) (generatedEighth_spin_state_square_bound _) hF

/-! ### Octad rows -/

private theorem middle_short (r : GriessShortIndex) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedEighthLocalFiber)
      generatedOddAxis)).2.1 r =
      qSign (localShortPhase generatedEighthLocalFiber
        ((griessShortPermutation generatedEighthLocalFiber.val.2).symm r)) *
        (griessConwayEncode generatedOddAxis).2.1
          ((griessShortPermutation generatedEighthLocalFiber.val.2).symm r) := by
  rw [generatedFourth_local_short]
  rfl

private theorem middle_preimage_pair (r : GriessShortIndex)
    (h : (griessConwayEncode (rhoLocal (localFiberIntoH generatedEighthLocalFiber)
      generatedOddAxis)).2.1 r ≠ 0) :
    ∃ s p, (griessShortPermutation generatedEighthLocalFiber.val.2).symm r = Sum.inl (s, p) := by
  by_contra hn
  push Not at hn
  exact h (by rw [middle_short, generatedSixth_original_nonpair_zero _ hn, mul_zero])

private theorem pair_lt (p : Fin 276) :
    (griessCoordinatePair p).1 < (griessCoordinatePair p).2 :=
  (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2

private theorem pair_injective {p q : Fin 276}
    (h : griessCoordinatePair p = griessCoordinatePair q) : p = q :=
  griessCoordinatePairEquiv.injective (Subtype.ext h)

/-- A forward pair image with an octad label has exactly the octad support. -/
private theorem pair_support_octad (s : Fin 2) (p : Fin 276) (o : Fin 759) (f : Fin 64)
    (h : griessShortPermutation generatedEighthLocalFiber.val.2 (Sum.inl (s, p)) =
      Sum.inr (Sum.inl (o, f))) (i : Fin 24) :
    generatedFeasibleAmbientEighthPairSupport s (griessCoordinatePair p).1
      (griessCoordinatePair p).2 i =
      (golayEncodedMask (golayOctadLabel o).val).testBit i.val := by
  have hv := generatedSixth_short_integral_sign generatedEighthLocalFiber.val.2 (Sum.inl (s, p))
  rw [h] at hv
  have hf := generatedEighth_forward_pair_coordinate s p i
  have hn := griessOctad_coordinate_nonzero o f i
  have key : (leechIntegralAction generatedEighthLocalFiber.val.2
      (griessShortLatticeVector (Sum.inl (s, p)))).val i ≠ 0 ↔
      griessShortIntegral (Sum.inr (Sum.inl (o, f))) i ≠ 0 := by
    rcases hv with hv | hv
    · rw [hv]
    · rw [hv, Pi.neg_apply, ne_eq, neg_eq_zero]
  rw [Bool.eq_iff_iff, ← hn, ← key]
  unfold generatedFeasibleAmbientEighthPairSupport
  rw [decide_eq_true_iff, ← hf]
  constructor <;> intro h₁ h₂ <;> apply h₁ <;> omega

/-- No octad support is the full coordinate set. -/
private theorem octad_not_full (o : Fin 759) (f : Fin 64) :
    ¬ ∀ i : Fin 24, (golayEncodedMask (golayOctadLabel o).val).testBit i.val = true := by
  intro h
  have hs := griessShortIntegral_squareSum (Sum.inr (Sum.inl (o, f)))
  unfold leechSquareSum at hs
  simp only [griessOctad_coordinate_square, h, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin] at hs
  norm_num at hs

/-- Each middle octad block has at most one nonzero entry. -/
private theorem octad_block_unique (o : Fin 759) (f₁ f₂ : Fin 64)
    (h₁ : (griessConwayEncode (rhoLocal (localFiberIntoH generatedEighthLocalFiber)
      generatedOddAxis)).2.1 (Sum.inr (Sum.inl (o, f₁))) ≠ 0)
    (h₂ : (griessConwayEncode (rhoLocal (localFiberIntoH generatedEighthLocalFiber)
      generatedOddAxis)).2.1 (Sum.inr (Sum.inl (o, f₂))) ≠ 0) : f₁ = f₂ := by
  obtain ⟨s₁, p₁, hp₁⟩ := middle_preimage_pair _ h₁
  obtain ⟨s₂, p₂, hp₂⟩ := middle_preimage_pair _ h₂
  have hi₁ : griessShortPermutation generatedEighthLocalFiber.val.2 (Sum.inl (s₁, p₁)) =
      Sum.inr (Sum.inl (o, f₁)) := by
    rw [← hp₁, Equiv.apply_symm_apply]
  have hi₂ : griessShortPermutation generatedEighthLocalFiber.val.2 (Sum.inl (s₂, p₂)) =
      Sum.inr (Sum.inl (o, f₂)) := by
    rw [← hp₂, Equiv.apply_symm_apply]
  have hd (s : Fin 2) (p : Fin 276) (f : Fin 64)
      (hi : griessShortPermutation generatedEighthLocalFiber.val.2 (Sum.inl (s, p)) =
        Sum.inr (Sum.inl (o, f))) :
      generatedFeasibleAmbientEighthDecode (generatedFeasibleAmbientSupportMask
        fun i => (golayEncodedMask (golayOctadLabel o).val).testBit i.val) =
        some (s, (griessCoordinatePair p).1, (griessCoordinatePair p).2) := by
    have hfun : generatedFeasibleAmbientEighthPairSupport s (griessCoordinatePair p).1
        (griessCoordinatePair p).2 =
        fun i => (golayEncodedMask (golayOctadLabel o).val).testBit i.val :=
      funext (pair_support_octad s p o f hi)
    rcases pair_support_certificate s _ _ (pair_lt p) with hc | hc
    · rw [hfun] at hc
      exact absurd hc (octad_not_full o f)
    · rw [hfun] at hc
      exact hc
  have he := (hd s₁ p₁ f₁ hi₁).symm.trans (hd s₂ p₂ f₂ hi₂)
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨hs, ha, hb⟩ := he
  have hp : p₁ = p₂ := pair_injective (Prod.ext ha hb)
  subst hs hp
  have h := hi₁.symm.trans hi₂
  simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and] at h
  exact h

private theorem octad_formula (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode generatedEighthAxis).2.1 (Sum.inr (Sum.inl (o, e))) =
      ∑ f : Fin 64, ((1 / 8 : ℝ) * (trialityIntegerMatrix e f : ℝ)) *
        (griessConwayEncode (rhoLocal (localFiberIntoH generatedEighthLocalFiber)
          generatedOddAxis)).2.1 (Sum.inr (Sum.inl (o, f))) := by
  rw [generatedEighthAxis_local_expression, generatedSeventhXi_octad_triality_coordinate,
    trialityOctadAction_matrix]
  rfl

/-- Every actual octad row of the Eighth prototype has square below `1/16`. -/
private theorem octad_sq (o : Fin 759) (e : Fin 64) :
    ((griessConwayEncode generatedEighthAxis).2.1 (Sum.inr (Sum.inl (o, e)))) ^ 2 < 1 / 16 := by
  rw [octad_formula]
  by_cases h : ∃ f, (griessConwayEncode (rhoLocal (localFiberIntoH generatedEighthLocalFiber)
      generatedOddAxis)).2.1 (Sum.inr (Sum.inl (o, f))) ≠ 0
  · obtain ⟨f, hf⟩ := h
    rw [Finset.sum_eq_single f]
    · have hT : ((trialityIntegerMatrix e f : ℤ) : ℝ) ^ 2 = 1 := by
        have h₁ := triality_entry_abs e f
        have h₂ : (trialityIntegerMatrix e f) ^ 2 = 1 := by
          rw [← sq_abs, h₁]
          norm_num
        exact_mod_cast h₂
      have hS : ((griessConwayEncode (rhoLocal (localFiberIntoH generatedEighthLocalFiber)
          generatedOddAxis)).2.1 (Sum.inr (Sum.inl (o, f)))) ^ 2 ≤ 9 / 16 := by
        rcases generatedEighth_middle_short_squares (Sum.inr (Sum.inl (o, f))) with h | h | h <;>
          rw [h] <;> norm_num
      rw [mul_pow, mul_pow, hT]
      linarith
    · intro g _ hg
      have hz : (griessConwayEncode (rhoLocal (localFiberIntoH generatedEighthLocalFiber)
          generatedOddAxis)).2.1 (Sum.inr (Sum.inl (o, g))) = 0 := by
        by_contra hne
        exact hg (octad_block_unique o g f hne hf)
      rw [hz, mul_zero]
    · intro hf'
      exact absurd (Finset.mem_univ f) hf'
  · push Not at h
    simp only [h, mul_zero, Finset.sum_const_zero]
    norm_num

/-! ### Assembly -/

/-- No actual signed-short axis is orthogonal to the actual Eighth prototype. -/
theorem generatedFeasibleAmbient_eighth_form_ne (r : GriessShortIndex) (c : ZMod 2) :
    griessForm (conwayShortAxis r c) generatedEighthAxis ≠ 0 := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · exact pair_ne s p c
  · exact ne_of_sq_lt _ c (octad_sq o e)
  · exact ne_of_sq_lt _ c (odd_sq d i)

/-- No actual signed-short axis is orthogonal to the actual Eighth prototype. -/
theorem generatedFeasibleAmbientAxisZeroCount_eighth :
    generatedFeasibleAmbientAxisZeroCount generatedEighthAxis = 0 := by
  unfold generatedFeasibleAmbientAxisZeroCount
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨⟨r, c⟩, h⟩
  exact generatedFeasibleAmbient_eighth_form_ne r c h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
