/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardRationalPhaseReduction









namespace StatMech.FrontierA

open scoped BigOperators


def kwRatCommonDenominator {n : ℕ} (q : Fin n → ℚ × ℚ) : ℕ :=
  ∏ i : Fin n, (q i).1.den * (q i).2.den

theorem kwRatCommonDenominator_pos {n : ℕ} (q : Fin n → ℚ × ℚ) :
    0 < kwRatCommonDenominator q := by
  unfold kwRatCommonDenominator
  exact Finset.prod_pos fun i _ ↦ Nat.mul_pos (q i).1.den_pos (q i).2.den_pos

theorem kwRatCommonDenominator_first_den_dvd
    {n : ℕ} (q : Fin n → ℚ × ℚ) (i : Fin n) :
    (q i).1.den ∣ kwRatCommonDenominator q := by
  apply dvd_trans (dvd_mul_right _ _)
  exact Finset.dvd_prod_of_mem
    (fun j : Fin n ↦ (q j).1.den * (q j).2.den) (Finset.mem_univ i)

theorem kwRatCommonDenominator_second_den_dvd
    {n : ℕ} (q : Fin n → ℚ × ℚ) (i : Fin n) :
    (q i).2.den ∣ kwRatCommonDenominator q := by
  apply dvd_trans (dvd_mul_left _ _)
  exact Finset.dvd_prod_of_mem
    (fun j : Fin n ↦ (q j).1.den * (q j).2.den) (Finset.mem_univ i)



theorem exists_int_eq_nat_mul_ratCast (q : ℚ) (D : ℕ) (hD : q.den ∣ D) :
    ∃ z : ℤ, (D : ℝ) * (q : ℝ) = (z : ℝ) := by
  obtain ⟨k, rfl⟩ := hD
  refine ⟨(k : ℤ) * q.num, ?_⟩
  rw [Rat.cast_def]
  push_cast
  field_simp


def kwIntComplex (p : ℤ × ℤ) : ℂ :=
  (p.1 : ℝ) + (p.2 : ℝ) * Complex.I



theorem kwRatVertex_clear_denominators
    {n : ℕ} (q : Fin n → ℚ × ℚ) :
    ∃ p : Fin n → ℤ × ℤ, ∀ i : Fin n,
      (kwRatCommonDenominator q : ℝ) * kwRatVertex q i =
        kwIntComplex (p i) := by
  choose x hx using fun i ↦ exists_int_eq_nat_mul_ratCast
    (q i).1 (kwRatCommonDenominator q)
      (kwRatCommonDenominator_first_den_dvd q i)
  choose y hy using fun i ↦ exists_int_eq_nat_mul_ratCast
    (q i).2 (kwRatCommonDenominator q)
      (kwRatCommonDenominator_second_den_dvd q i)
  refine ⟨fun i ↦ (x i, y i), ?_⟩
  intro i
  apply Complex.ext
  · simpa [kwRatVertex, kwRatComplex, kwIntComplex] using hx i
  · simpa [kwRatVertex, kwRatComplex, kwIntComplex] using hy i



noncomputable def kwPositiveScaleLinearEquiv
    (s : ℝ) (hs : 0 < s) : ℂ ≃ₗ[ℝ] ℂ where
  toFun z := (s : ℂ) * z
  invFun z := ((s⁻¹ : ℝ) : ℂ) * z
  left_inv z := by
    dsimp only
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hs.ne',
      Complex.ofReal_one, one_mul]
  right_inv z := by
    dsimp only
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hs.ne',
      Complex.ofReal_one, one_mul]
  map_add' z w := mul_add _ _ _
  map_smul' r z := by
    simp only [RingHom.id_apply, Complex.real_smul]
    ring

@[simp] theorem kwPositiveScaleLinearEquiv_apply
    (s : ℝ) (hs : 0 < s) (z : ℂ) :
    kwPositiveScaleLinearEquiv s hs z = (s : ℂ) * z := rfl

theorem Complex.arg_posReal_mul (s : ℝ) (hs : 0 < s) (z : ℂ)
    (hz : z ≠ 0) : Complex.arg ((s : ℂ) * z) = Complex.arg z := by
  have harg : Complex.arg (s : ℂ) = 0 :=
    Complex.arg_ofReal_of_nonneg hs.le
  have hmem : Complex.arg (s : ℂ) + Complex.arg z ∈
      Set.Ioc (-Real.pi) Real.pi := by
    rw [harg, zero_add]
    exact ⟨Complex.neg_pi_lt_arg z, Complex.arg_le_pi z⟩
  rw [Complex.arg_mul (Complex.ofReal_ne_zero.mpr hs.ne') hz hmem,
    harg, zero_add]


theorem kwVectorTurnPhase_pos_scale
    (s : ℝ) (hs : 0 < s) (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    kwVectorTurnPhase ((s : ℂ) * z) ((s : ℂ) * w) =
      kwVectorTurnPhase z w := by
  unfold kwVectorTurnPhase kwAngleTurnPhase
  rw [Complex.arg_posReal_mul s hs z hz,
    Complex.arg_posReal_mul s hs w hw]


theorem KWFiniteSimplePolygon.phaseCycle_mapPositiveScale
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (s : ℝ) (hs : 0 < s) :
    kwVectorPhaseCycle polygon.edgeList =
      kwVectorPhaseCycle
        (polygon.mapLinearEquiv
          (kwPositiveScaleLinearEquiv s hs)).edgeList := by
  rw [KWFiniteSimplePolygon.edgeList, kwVectorPhaseCycle_ofFn,
    KWFiniteSimplePolygon.edgeList, kwVectorPhaseCycle_ofFn]
  unfold kwLoopPhaseProduct
  apply Finset.prod_congr rfl
  intro k _
  simp only [KWFiniteSimplePolygon.mapLinearEquiv_edgeVector,
    kwPositiveScaleLinearEquiv_apply]
  symm
  apply kwVectorTurnPhase_pos_scale s hs
  · unfold KWFiniteSimplePolygon.edgeVector
    exact sub_ne_zero.mpr (polygon.vertex_injective.ne
      (polygon.add_one_ne_self k))
  · unfold KWFiniteSimplePolygon.edgeVector
    exact sub_ne_zero.mpr (polygon.vertex_injective.ne
      (polygon.add_one_ne_self (k + 1)))


theorem KWFiniteSimplePolygon.exists_integral_positive_scale
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (q : Fin n → ℚ × ℚ) (hvertex : polygon.vertex = kwRatVertex q) :
    ∃ (D : ℕ) (hD : 0 < D) (p : Fin n → ℤ × ℤ),
      let scaled := polygon.mapLinearEquiv
        (kwPositiveScaleLinearEquiv (D : ℝ) (by exact_mod_cast hD))
      ∀ i : Fin n, scaled.vertex i = kwIntComplex (p i) := by
  let D := kwRatCommonDenominator q
  have hD : 0 < D := kwRatCommonDenominator_pos q
  obtain ⟨p, hp⟩ := kwRatVertex_clear_denominators q
  refine ⟨D, hD, p, ?_⟩
  dsimp only
  intro i
  simp only [KWFiniteSimplePolygon.mapLinearEquiv_vertex,
    kwPositiveScaleLinearEquiv_apply, hvertex]
  simpa only [D] using hp i



theorem KWFiniteSimplePolygon.exists_integral_phaseModel
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i)
      (polygon.edgeVector (i + 1)) ≠ 0) :
    ∃ (p : Fin n → ℤ × ℤ) (integral : KWFiniteSimplePolygon n),
      integral.vertex = (fun i ↦ kwIntComplex (p i)) ∧
      kwVectorPhaseCycle polygon.edgeList =
        kwVectorPhaseCycle integral.edgeList := by
  obtain ⟨q, rational, hrational, hphase⟩ :=
    polygon.exists_rational_phaseModel hcross
  obtain ⟨D, hD, p, hp⟩ :=
    rational.exists_integral_positive_scale q hrational
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
  let integral := rational.mapLinearEquiv
    (kwPositiveScaleLinearEquiv (D : ℝ) hDreal)
  refine ⟨p, integral, ?_, ?_⟩
  · funext i
    exact hp i
  · exact hphase.trans
      (rational.phaseCycle_mapPositiveScale (D : ℝ) hDreal)

end StatMech.FrontierA
