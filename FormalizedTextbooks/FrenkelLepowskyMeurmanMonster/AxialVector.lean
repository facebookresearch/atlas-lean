/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Conway's distinguished axial vector from Invent. Math. 79 (1985), §13,
printed page 527. The spectrum and orbit-spanning claims are not proved here.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechQuadratic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Conway's vector `4[(ii)+(jj)−(ij)₁−(ij)₂−(ij)₃]` in dictionary blocks. -/
def conwayAxisBlocks (p : Fin 276) : TrialityBlocks :=
  ((fun i => if i = (griessCoordinatePair p).1 ∨ i = (griessCoordinatePair p).2 then 4 else 0),
    ((fun _ q => if q = p then -4 else 0), (0, 0)))

/-- Conway's distinguished vector in the fixed Griess coordinate space. -/
noncomputable def conwayAxis (p : Fin 276) : GriessSpace :=
  trialityBlocksEquiv.symm (conwayAxisBlocks p)

/-- Triality fixes Conway's distinguished vector, since its three pair
coordinates are equal and its octad and X/Y/Z coordinates vanish. -/
theorem conwayAxis_triality (p : Fin 276) : sExtra (conwayAxis p) = conwayAxis p := by
  apply trialityBlocksEquiv.injective
  change trialityBlocksEquiv (griessTriality (trialityBlocksEquiv.symm (conwayAxisBlocks p))) =
    trialityBlocksEquiv (trialityBlocksEquiv.symm (conwayAxisBlocks p))
  simp only [griessTriality, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change trialityBlockAction (conwayAxisBlocks p) = conwayAxisBlocks p
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext s q
      rfl
    · apply Prod.ext
      · change (LinearEquiv.piCongrRight fun _ : Fin 759 => trialityOctadAction) 0 = 0
        exact map_zero _
      · change trialityCycleAction 49152 0 = 0
        exact map_zero _

/-- The fixed dictionary blocks of the axis. -/
theorem conwayAxis_blocks (p : Fin 276) :
    trialityBlocksEquiv (conwayAxis p) = conwayAxisBlocks p :=
  trialityBlocksEquiv.apply_symm_apply _

/-- The symmetric-matrix component of Conway's axis. -/
noncomputable def conwayAxisMatrix (p : Fin 276) : Matrix (Fin 24) (Fin 24) ℝ :=
  fun i j => if h : i = j then
    if i = (griessCoordinatePair p).1 ∨ i = (griessCoordinatePair p).2 then 4 else 0
    else if griessPairIndex i j h = p then -4 else 0

/-- Under the Conway dictionary, the axis has a single short-vector
coordinate, namely `−8 X_(e_i−e_j)`, and no spin-tensor component. -/
theorem conwayAxis_encode (p : Fin 276) :
    griessConwayEncode (conwayAxis p) =
      (conwayAxisMatrix p, ((-8 : ℝ) • Pi.single (Sum.inl (0, p)) 1, 0)) := by
  have hb := conwayAxis_blocks p
  unfold griessConwayEncode
  rw [hb]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext r
      rcases r with ⟨s, q⟩ | (⟨d, e⟩ | ⟨d, i⟩)
      · have hs : s = 0 ∨ s = 1 := by
          fin_cases s
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases hs with rfl | rfl
        · by_cases hq : q = p <;> norm_num [conwayAxisBlocks, hq]
        · simp [conwayAxisBlocks]
      · simp [conwayAxisBlocks]
      · simp [conwayAxisBlocks]
    · funext t i
      simp [conwayAxisBlocks]

/-- No shortest lattice vector represents zero modulo twice the lattice. -/
theorem griessShortClass_ne_zero (r : GriessShortIndex) : griessShortClass r ≠ 0 := by
  intro h
  let u := griessShortLatticeVector r
  have hu : leechReduction u = 0 := h
  have hm : u ∈ twiceLeechIntegral := (QuotientAddGroup.eq_zero_iff u).mp hu
  obtain ⟨w, hw⟩ := hm
  have hsq : leechSquareSum u.val = 4 * leechSquareSum w.val := by
    rw [← hw]
    simp only [leechDouble, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      leechSquareSum, two_nsmul, Submodule.coe_add, Pi.add_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hn : leechSquareSum u.val = 32 := griessShortIntegral_squareSum r
  by_cases hw0 : w.val = 0
  · have hz : leechSquareSum u.val = 0 := hsq.trans (by simp [hw0, leechSquareSum])
    omega
  · have hmin := leechIntegral_minimum w w.property hw0
    omega

/-- A preferred short lift has nontrivial binary base. -/
theorem griessShortQ_base_ne_one (r : GriessShortIndex) : (griessShortQ r).base ≠ 1 := by
  intro h
  apply griessShortClass_ne_zero r
  apply leechHyperbolicCoordinates.injective
  have hc := congrArg Multiplicative.toAdd h
  change leechHyperbolicCoordinates (griessShortClass r) = 0 at hc
  simpa only [map_zero] using hc

/-- The distinguished axial vector has squared Griess length 128. -/
theorem conwayAxis_square_length (p : Fin 276) :
    griessForm (conwayAxis p) (conwayAxis p) = 128 := by
  rw [griessForm_eq_trialityBlockForm, conwayAxis_blocks]
  have hne := griessCoordinatePair_ne p
  unfold trialityBlockForm conwayAxisBlocks
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  have hd : (∑ i : Fin 24, (if i = (griessCoordinatePair p).1 ∨
        i = (griessCoordinatePair p).2 then (4 : ℝ) else 0) *
      (if i = (griessCoordinatePair p).1 ∨ i = (griessCoordinatePair p).2 then 4 else 0)) = 32 := by
    have he (i : Fin 24) :
        (if i = (griessCoordinatePair p).1 ∨ i = (griessCoordinatePair p).2 then (4 : ℝ) else 0) *
        (if i = (griessCoordinatePair p).1 ∨ i = (griessCoordinatePair p).2 then 4 else 0) =
      (if i = (griessCoordinatePair p).1 then 16 else 0) +
      (if i = (griessCoordinatePair p).2 then 16 else 0) := by
      by_cases hi : i = (griessCoordinatePair p).1
      · subst i; norm_num [hne]
      · by_cases hj : i = (griessCoordinatePair p).2 <;> norm_num [hi, hj, hne.symm]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    norm_num
  rw [hd]
  norm_num [Fin.sum_univ_three]

private theorem griessPairIndex_eq_iff (p : Fin 276) (i j : Fin 24) (h : i ≠ j) :
    griessPairIndex i j h = p ↔
      (i = (griessCoordinatePair p).1 ∧ j = (griessCoordinatePair p).2) ∨
      (i = (griessCoordinatePair p).2 ∧ j = (griessCoordinatePair p).1) := by
  constructor
  · intro hp
    have hc := congrArg griessCoordinatePair hp
    rw [griessPairIndex_coordinates] at hc
    split_ifs at hc with hij
    · exact Or.inl ⟨congrArg Prod.fst hc, congrArg Prod.snd hc⟩
    · exact Or.inr ⟨congrArg Prod.snd hc, congrArg Prod.fst hc⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact griessPairIndex_pair p
    · rw [griessPairIndex_swap]
      exact griessPairIndex_pair p

/-- The unnormalized vector `e_i−e_j` underlying the distinguished axis. -/
def conwayAxisDifference (p : Fin 276) : Fin 24 → ℝ :=
  fun i => (if i = (griessCoordinatePair p).1 then 1 else 0) -
    (if i = (griessCoordinatePair p).2 then 1 else 0)

/-- The symmetric-matrix component is the rank-one matrix `4(e_i−e_j)(e_i−e_j)ᵀ`. -/
theorem conwayAxisMatrix_rank_one (p : Fin 276) (i j : Fin 24) :
    conwayAxisMatrix p i j = 4 * conwayAxisDifference p i * conwayAxisDifference p j := by
  have hn := griessCoordinatePair_ne p
  unfold conwayAxisMatrix conwayAxisDifference
  by_cases hij : i = j
  · subst j
    rw [dite_eq_left rfl]
    by_cases hi : i = (griessCoordinatePair p).1
    · subst i; norm_num [hn]
    · by_cases hj : i = (griessCoordinatePair p).2 <;> norm_num [hi, hj, hn.symm]
  · rw [dite_eq_right hij]
    simp only [griessPairIndex_eq_iff]
    by_cases hi1 : i = (griessCoordinatePair p).1 <;>
      by_cases hi2 : i = (griessCoordinatePair p).2 <;>
      by_cases hj1 : j = (griessCoordinatePair p).1 <;>
      by_cases hj2 : j = (griessCoordinatePair p).2 <;>
      norm_num [hi1, hi2, hj1, hj2] <;> simp_all

/-- The coordinate difference underlying the axis has squared norm two. -/
theorem conwayAxisDifference_square_sum (p : Fin 276) :
    (∑ i, conwayAxisDifference p i * conwayAxisDifference p i) = 2 := by
  have hn := griessCoordinatePair_ne p
  have he (i : Fin 24) : conwayAxisDifference p i * conwayAxisDifference p i =
      (if i = (griessCoordinatePair p).1 then (1 : ℝ) else 0) +
      (if i = (griessCoordinatePair p).2 then 1 else 0) := by
    unfold conwayAxisDifference
    by_cases hi : i = (griessCoordinatePair p).1
    · subst i; norm_num [hn]
    · by_cases hj : i = (griessCoordinatePair p).2 <;> norm_num [hi, hj, hn.symm]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  norm_num

/-- The pair short vector is the normalized coordinate difference of the axis. -/
theorem conwayAxis_short_vector (p : Fin 276) (i : Fin 24) :
    griessShortVector (Sum.inl (0, p)) i = (4 / Real.sqrt 8 : ℝ) * conwayAxisDifference p i := by
  unfold griessShortVector griessShortIntegral conwayAxisDifference
  norm_num only [ite_true, mul_ite, Int.cast_add, Int.cast_mul, Int.cast_ite,
    Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one]
  split_ifs <;> ring

/-- Products of pair-short coordinates are twice products of the unnormalized difference. -/
theorem conwayAxis_short_outer (p : Fin 276) (i j : Fin 24) :
    griessShortVector (Sum.inl (0, p)) i * griessShortVector (Sum.inl (0, p)) j =
      2 * conwayAxisDifference p i * conwayAxisDifference p j := by
  rw [conwayAxis_short_vector, conwayAxis_short_vector]
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have hn : Real.sqrt 8 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp
  have hs2 : Real.sqrt 8 ^ 2 = 8 := by nlinarith [hs]
  rw [hs2]
  ring

/-- The axis matrix squared, in its rank-one coordinates. -/
theorem conwayAxisMatrix_square (p : Fin 276) (i j : Fin 24) :
    (∑ k, conwayAxisMatrix p i k * conwayAxisMatrix p k j) =
      32 * conwayAxisDifference p i * conwayAxisDifference p j := by
  simp_rw [conwayAxisMatrix_rank_one]
  have he (k : Fin 24) :
      (4 * conwayAxisDifference p i * conwayAxisDifference p k) *
      (4 * conwayAxisDifference p k * conwayAxisDifference p j) =
    (16 * conwayAxisDifference p i * conwayAxisDifference p j) *
      (conwayAxisDifference p k * conwayAxisDifference p k) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum, conwayAxisDifference_square_sum]
  ring

/-- The pair short vector evaluates to 32 on the axis matrix. -/
theorem conwayAxisMatrix_short_pairing (p : Fin 276) :
    conwayShortPairing (conwayAxisMatrix p) (Sum.inl (0, p)) = 32 := by
  unfold conwayShortPairing
  simp_rw [conwayAxisMatrix_rank_one]
  have he (i j : Fin 24) :
      4 * conwayAxisDifference p i * conwayAxisDifference p j *
        griessShortVector (Sum.inl (0, p)) i * griessShortVector (Sum.inl (0, p)) j =
      8 * (conwayAxisDifference p i * conwayAxisDifference p i) *
        (conwayAxisDifference p j * conwayAxisDifference p j) := by
    calc
      _ = (4 * conwayAxisDifference p i * conwayAxisDifference p j) *
        (griessShortVector (Sum.inl (0, p)) i * griessShortVector (Sum.inl (0, p)) j) := by ring
      _ = _ := by rw [conwayAxis_short_outer]; ring
  simp_rw [he]
  simp_rw [← Finset.mul_sum, conwayAxisDifference_square_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum, conwayAxisDifference_square_sum]
  norm_num

/-- Conway's distinguished vector has square `64t` in the raw product. -/
theorem conwayAxis_raw_square (p : Fin 276) :
    conwayRawProduct (griessConwayEncode (conwayAxis p))
      (griessConwayEncode (conwayAxis p)) =
      (64 : ℝ) • griessConwayEncode (conwayAxis p) := by
  rw [conwayAxis_encode]
  let r0 : GriessShortIndex := Sum.inl (0, p)
  let S : GriessShortIndex → ℝ := (-8 : ℝ) • Pi.single r0 1
  have hs0 : S r0 = -8 := by simp [S]
  have hs (r : GriessShortIndex) (hr : r ≠ r0) : S r = 0 := by simp [S, hr]
  have hxx (i j : Fin 24) :
      (∑ r, ∑ s, if (griessShortQ r * griessShortQ s).base = 1 then
        qSign (Multiplicative.toAdd (griessShortQ r * griessShortQ s).coeff) * S r * S s *
          griessShortVector r i * griessShortVector r j else 0) =
      64 * griessShortVector r0 i * griessShortVector r0 j := by
    rw [Finset.sum_eq_single r0]
    · rw [Finset.sum_eq_single r0]
      · rw [griessShortQ_square, hs0]
        change (if True then qSign 0 * -8 * -8 * _ * _ else 0) = _
        simp only [ite_true, qSign_zero]
        ring
      · intro s _ hsr
        simp [hs s hsr]
      · simp
    · intro r _ hrr
      simp [hs r hrr]
    · simp
  have hshort (u : GriessShortIndex) :
      (∑ r, ∑ s,
        if (griessShortQ r * griessShortQ s).base = (griessShortQ u).base then
        qSign (Multiplicative.toAdd (griessShortQ r * griessShortQ s).coeff) *
          S r * S s else 0) = 0 := by
    rw [Finset.sum_eq_single r0]
    · rw [Finset.sum_eq_single r0]
      · rw [griessShortQ_square]
        change (if (1 : Multiplicative (Fin 24 → ZMod 2)) = (griessShortQ u).base then
          qSign 0 * S r0 * S r0 else 0) = 0
        rw [ite_eq_right (Ne.symm (griessShortQ_base_ne_one u))]
      · intro s _ hsr
        simp [hs s hsr]
      · simp
    · intro r _ hrr
      simp [hs r hrr]
    · simp
  change conwayRawProduct (conwayAxisMatrix p, (S, 0)) (conwayAxisMatrix p, (S, 0)) =
    (64 : ℝ) • (conwayAxisMatrix p, (S, 0))
  apply Prod.ext
  · funext i j
    change 2 * (∑ k, (conwayAxisMatrix p i k * conwayAxisMatrix p k j +
      conwayAxisMatrix p i k * conwayAxisMatrix p k j)) + _ + _ = _
    rw [Finset.sum_add_distrib, conwayAxisMatrix_square, hxx]
    simp only [Pi.zero_apply, mul_zero, zero_mul, add_zero, Finset.sum_const_zero,
      zero_div, Prod.smul_fst, Matrix.smul_apply, smul_eq_mul]
    rw [conwayAxisMatrix_rank_one]
    change _ + 64 * griessShortVector (Sum.inl (0, p)) i *
      griessShortVector (Sum.inl (0, p)) j = _
    have ho := conwayAxis_short_outer p i j
    nlinarith [ho]
  · apply Prod.ext
    · funext u
      change conwayShortPairing (conwayAxisMatrix p) u * S u +
        conwayShortPairing (conwayAxisMatrix p) u * S u + _ + _ = 64 * S u
      rw [hshort]
      simp only [Pi.zero_apply, spinOperator, LinearMap.coe_mk, AddHom.coe_mk,
        mul_zero, zero_mul, add_zero, Finset.sum_const_zero, zero_div]
      by_cases hu : u = r0
      · subst u
        rw [hs0]
        change conwayShortPairing (conwayAxisMatrix p) (Sum.inl (0, p)) * -8 +
          conwayShortPairing (conwayAxisMatrix p) (Sum.inl (0, p)) * -8 = 64 * -8
        rw [conwayAxisMatrix_short_pairing]
        norm_num
      · rw [hs u hu]
        ring
    · funext t i
      simp [conwayRawProduct, spinOperator]

/-- Conway's distinguished vector is a scaled idempotent in the concrete Griess product. -/
theorem conwayAxis_square (p : Fin 276) :
    griessProd (conwayAxis p) (conwayAxis p) = (64 : ℝ) • conwayAxis p := by
  rw [griessProd_eq_conwayRawProduct, conwayAxis_raw_square]
  have he := congrArg (fun e : ConwayRawSpace => e)
    (griessConwayEncodeLinear.map_smul 64 (conwayAxis p))
  change griessConwayEncode ((64 : ℝ) • conwayAxis p) =
    (64 : ℝ) • griessConwayEncode (conwayAxis p) at he
  rw [← he, griessConwayDecode_encode]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
