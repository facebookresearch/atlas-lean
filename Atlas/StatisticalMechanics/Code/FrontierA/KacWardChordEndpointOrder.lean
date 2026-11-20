/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardChordPhaseGlue










namespace StatMech.FrontierA



theorem kw_halfAngle_two_eq_neg_four_of_odd_full_turn
    (x₁ x₂ y₁ y₂ y₃ y₄ : ℝ)
    (hturn : x₁ + x₂ - (y₁ + y₂ + y₃ + y₄) = 2 * Real.pi ∨
      x₁ + x₂ - (y₁ + y₂ + y₃ + y₄) = -(2 * Real.pi)) :
    Complex.exp (((x₁ : ℂ) * Complex.I) / 2) *
        Complex.exp (((x₂ : ℂ) * Complex.I) / 2) =
      -(Complex.exp (((y₁ : ℂ) * Complex.I) / 2) *
          Complex.exp (((y₂ : ℂ) * Complex.I) / 2) *
        (Complex.exp (((y₃ : ℂ) * Complex.I) / 2) *
          Complex.exp (((y₄ : ℂ) * Complex.I) / 2))) := by
  let X : ℂ := ((x₁ : ℂ) * Complex.I) / 2 +
    ((x₂ : ℂ) * Complex.I) / 2
  let Y : ℂ := ((y₁ : ℂ) * Complex.I) / 2 +
    ((y₂ : ℂ) * Complex.I) / 2 +
    ((y₃ : ℂ) * Complex.I) / 2 +
    ((y₄ : ℂ) * Complex.I) / 2
  have hleft : Complex.exp (((x₁ : ℂ) * Complex.I) / 2) *
      Complex.exp (((x₂ : ℂ) * Complex.I) / 2) = Complex.exp X := by
    rw [← Complex.exp_add]
  have hright : Complex.exp (((y₁ : ℂ) * Complex.I) / 2) *
          Complex.exp (((y₂ : ℂ) * Complex.I) / 2) *
        (Complex.exp (((y₃ : ℂ) * Complex.I) / 2) *
          Complex.exp (((y₄ : ℂ) * Complex.I) / 2)) = Complex.exp Y := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [hleft, hright]
  rcases hturn with hturn | hturn
  · have hXY : X = Y + (Real.pi : ℂ) * Complex.I := by
      dsimp only [X, Y]
      have hturn' : (x₁ : ℂ) + x₂ - (y₁ + y₂ + y₃ + y₄) =
          (2 * Real.pi : ℝ) := by exact_mod_cast hturn
      push_cast at hturn'
      linear_combination (Complex.I / 2) * hturn'
    rw [hXY, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  · have hXY : X = Y - (Real.pi : ℂ) * Complex.I := by
      dsimp only [X, Y]
      have hturn' : (x₁ : ℂ) + x₂ - (y₁ + y₂ + y₃ + y₄) =
          (-(2 * Real.pi) : ℝ) := by exact_mod_cast hturn
      push_cast at hturn'
      linear_combination (Complex.I / 2) * hturn'
    have hnegPi : Complex.exp (-((Real.pi : ℂ) * Complex.I)) = -1 := by
      rw [Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    rw [hXY, sub_eq_add_neg, Complex.exp_add, hnegPi]
    ring




noncomputable def kwChordBoundaryTurnDiscrepancy
    (a b c d chord : ℂ) : ℝ :=
  (((Complex.arg b : Real.Angle) -
          (Complex.arg a : Real.Angle)).toReal +
      ((Complex.arg d : Real.Angle) -
          (Complex.arg c : Real.Angle)).toReal) -
    ((((Complex.arg (-chord) : Real.Angle) -
            (Complex.arg a : Real.Angle)).toReal +
        ((Complex.arg d : Real.Angle) -
            (Complex.arg (-chord) : Real.Angle)).toReal) +
      (((Complex.arg chord : Real.Angle) -
            (Complex.arg c : Real.Angle)).toReal +
        ((Complex.arg b : Real.Angle) -
            (Complex.arg chord : Real.Angle)).toReal))



noncomputable def kwAntipodalEndpointTurnDefect
    (a b chord : ℂ) : ℝ :=
  ((Complex.arg b : Real.Angle) -
      (Complex.arg a : Real.Angle)).toReal -
    ((Complex.arg (-chord) : Real.Angle) -
      (Complex.arg a : Real.Angle)).toReal -
    ((Complex.arg b : Real.Angle) -
      (Complex.arg chord : Real.Angle)).toReal



theorem kwChordBoundaryTurnDiscrepancy_eq_endpointDefects
    (a b c d chord : ℂ) :
    kwChordBoundaryTurnDiscrepancy a b c d chord =
      kwAntipodalEndpointTurnDefect a b chord +
        kwAntipodalEndpointTurnDefect c d (-chord) := by
  unfold kwChordBoundaryTurnDiscrepancy
    kwAntipodalEndpointTurnDefect
  simp only [neg_neg]
  ring



theorem kw_antipodal_endpoint_turn_defect_eq_pi_or_neg_pi
    (a b chord : ℂ) (hchord : chord ≠ 0) :
    let defect :=
      ((Complex.arg b : Real.Angle) -
          (Complex.arg a : Real.Angle)).toReal -
        ((Complex.arg (-chord) : Real.Angle) -
          (Complex.arg a : Real.Angle)).toReal -
        ((Complex.arg b : Real.Angle) -
          (Complex.arg chord : Real.Angle)).toReal
    defect = Real.pi ∨ defect = -Real.pi := by
  dsimp only
  let A : Real.Angle := Complex.arg a
  let B : Real.Angle := Complex.arg b
  let H : Real.Angle := Complex.arg chord
  let Hneg : Real.Angle := Complex.arg (-chord)
  let defect : ℝ := (B - A).toReal - (Hneg - A).toReal -
    (B - H).toReal
  have hHneg : Hneg = H + (Real.pi : Real.Angle) := by
    dsimp only [Hneg, H]
    exact Complex.arg_neg_coe_angle hchord
  have hcoe : ((defect - Real.pi : ℝ) : Real.Angle) = 0 := by
    have hdefect : (defect : Real.Angle) =
        (Real.pi : Real.Angle) := by
      change Real.Angle.coeHom defect = (Real.pi : Real.Angle)
      dsimp only [defect]
      rw [map_sub, map_sub]
      change ((B - A).toReal : Real.Angle) -
          ((Hneg - A).toReal : Real.Angle) -
          ((B - H).toReal : Real.Angle) = (Real.pi : Real.Angle)
      rw [Real.Angle.coe_toReal,
        Real.Angle.coe_toReal, Real.Angle.coe_toReal]
      calc
        (B - A) - (Hneg - A) - (B - H) = H - Hneg := by abel
        _ = -(Real.pi : Real.Angle) := by rw [hHneg]; abel
        _ = (Real.pi : Real.Angle) := Real.Angle.neg_coe_pi
    rw [Real.Angle.coe_sub, hdefect]
    simp
  obtain ⟨k, hk⟩ := Real.Angle.coe_eq_zero_iff.mp hcoe
  have hk' : (k : ℝ) * (2 * Real.pi) = defect - Real.pi := by
    simpa only [zsmul_eq_mul] using hk
  have hlower : -3 * Real.pi < defect := by
    dsimp only [defect]
    nlinarith [Real.Angle.neg_pi_lt_toReal (B - A),
      Real.Angle.toReal_le_pi (Hneg - A),
      Real.Angle.toReal_le_pi (B - H)]
  have hupper : defect < 3 * Real.pi := by
    dsimp only [defect]
    nlinarith [Real.Angle.toReal_le_pi (B - A),
      Real.Angle.neg_pi_lt_toReal (Hneg - A),
      Real.Angle.neg_pi_lt_toReal (B - H)]
  have hkLower : (-1 : ℤ) ≤ k := by
    by_contra h
    have hkTwo : k ≤ -2 := by omega
    have hkTwo' : (k : ℝ) ≤ -2 := by exact_mod_cast hkTwo
    nlinarith [Real.pi_pos]
  have hkUpper : k ≤ 0 := by
    by_contra h
    have hkOne : 1 ≤ k := by omega
    have hkOne' : (1 : ℝ) ≤ k := by exact_mod_cast hkOne
    nlinarith [Real.pi_pos]
  have hkCases : k = -1 ∨ k = 0 := by omega
  rcases hkCases with rfl | rfl
  · right
    norm_num at hk'
    dsimp only [defect] at hk' ⊢
    linarith
  · left
    norm_num at hk'
    dsimp only [defect] at hk' ⊢
    linarith


theorem kwAntipodalEndpointTurnDefect_eq_pi_or_neg_pi
    (a b chord : ℂ) (hchord : chord ≠ 0) :
    kwAntipodalEndpointTurnDefect a b chord = Real.pi ∨
      kwAntipodalEndpointTurnDefect a b chord = -Real.pi := by
  simpa only [kwAntipodalEndpointTurnDefect] using
    kw_antipodal_endpoint_turn_defect_eq_pi_or_neg_pi a b chord hchord



theorem kwChordBoundaryTurnDiscrepancy_ne_zero_iff_endpointDefects_eq
    (a b c d chord : ℂ) (hchord : chord ≠ 0) :
    kwChordBoundaryTurnDiscrepancy a b c d chord ≠ 0 ↔
      kwAntipodalEndpointTurnDefect a b chord =
        kwAntipodalEndpointTurnDefect c d (-chord) := by
  have hfirst := kwAntipodalEndpointTurnDefect_eq_pi_or_neg_pi
    a b chord hchord
  have hsecond := kwAntipodalEndpointTurnDefect_eq_pi_or_neg_pi
    c d (-chord) (neg_ne_zero.mpr hchord)
  rw [kwChordBoundaryTurnDiscrepancy_eq_endpointDefects]
  rcases hfirst with hfirst | hfirst
  · rcases hsecond with hsecond | hsecond
    · rw [hfirst, hsecond]
      exact iff_of_true (by nlinarith [Real.pi_pos]) rfl
    · rw [hfirst, hsecond]
      constructor
      · intro h
        exact (h (by ring)).elim
      · intro h
        exfalso
        nlinarith [Real.pi_pos]
  · rcases hsecond with hsecond | hsecond
    · rw [hfirst, hsecond]
      constructor
      · intro h
        exact (h (by ring)).elim
      · intro h
        exfalso
        nlinarith [Real.pi_pos]
    · rw [hfirst, hsecond]
      exact iff_of_true (by nlinarith [Real.pi_pos]) rfl



theorem kwChordBoundaryTurnDiscrepancy_trichotomy
    (a b c d chord : ℂ) (hchord : chord ≠ 0) :
    kwChordBoundaryTurnDiscrepancy a b c d chord = 2 * Real.pi ∨
      kwChordBoundaryTurnDiscrepancy a b c d chord = 0 ∨
      kwChordBoundaryTurnDiscrepancy a b c d chord = -(2 * Real.pi) := by
  have hfirst := kw_antipodal_endpoint_turn_defect_eq_pi_or_neg_pi
    a b chord hchord
  have hnegChord : -chord ≠ 0 := neg_ne_zero.mpr hchord
  have hsecond := kw_antipodal_endpoint_turn_defect_eq_pi_or_neg_pi
    c d (-chord) hnegChord
  rcases hfirst with hfirst | hfirst <;>
    rcases hsecond with hsecond | hsecond
  · left
    unfold kwChordBoundaryTurnDiscrepancy
    simp only [neg_neg] at hsecond
    linear_combination hfirst + hsecond
  · right; left
    unfold kwChordBoundaryTurnDiscrepancy
    simp only [neg_neg] at hsecond
    linear_combination hfirst + hsecond
  · right; left
    unfold kwChordBoundaryTurnDiscrepancy
    simp only [neg_neg] at hsecond
    linear_combination hfirst + hsecond
  · right; right
    unfold kwChordBoundaryTurnDiscrepancy
    simp only [neg_neg] at hsecond
    linear_combination hfirst + hsecond



theorem kwChordBoundaryTurnDiscrepancy_odd_iff_ne_zero
    (a b c d chord : ℂ) (hchord : chord ≠ 0) :
    (kwChordBoundaryTurnDiscrepancy a b c d chord = 2 * Real.pi ∨
      kwChordBoundaryTurnDiscrepancy a b c d chord = -(2 * Real.pi)) ↔
    kwChordBoundaryTurnDiscrepancy a b c d chord ≠ 0 := by
  constructor
  · rintro (h | h) <;> rw [h]
    · exact mul_ne_zero (by norm_num) Real.pi_ne_zero
    · exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  · intro hne
    rcases kwChordBoundaryTurnDiscrepancy_trichotomy
        a b c d chord hchord with h | h | h
    · exact Or.inl h
    · exact (hne h).elim
    · exact Or.inr h



theorem kwVectorTurnPhase_chord_boundary_of_odd_full_turn
    (a b c d chord : ℂ)
    (hturn : kwChordBoundaryTurnDiscrepancy a b c d chord =
          2 * Real.pi ∨
        kwChordBoundaryTurnDiscrepancy a b c d chord =
          -(2 * Real.pi)) :
    kwVectorTurnPhase a b * kwVectorTurnPhase c d =
      -(kwVectorTurnPhase a (-chord) *
          kwVectorTurnPhase (-chord) d *
        (kwVectorTurnPhase c chord * kwVectorTurnPhase chord b)) := by
  apply kw_halfAngle_two_eq_neg_four_of_odd_full_turn
  simpa only [kwChordBoundaryTurnDiscrepancy, sub_eq_add_neg,
    add_assoc] using hturn




def KWFiniteSimplePolygon.CleanChordEndpointOddFullTurn
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 1 ≤ j.val) : Prop :=
  let p := polygon.edgeList.take j.val
  let q := polygon.edgeList.drop j.val
  let hpne : p ≠ [] := by
    intro h
    rw [List.take_eq_nil_iff] at h
    rcases h with hzero | hempty
    · omega
    · have hlen := congrArg List.length hempty
      simp [KWFiniteSimplePolygon.edgeList] at hlen
      omega
  let hqne : q ≠ [] := by
    intro h
    rw [List.drop_eq_nil_iff] at h
    simp [KWFiniteSimplePolygon.edgeList] at h
    exact (Nat.not_le_of_lt j.isLt) h
  let chord := polygon.vertex j - polygon.vertex 0
  kwChordBoundaryTurnDiscrepancy
      (p.getLast hpne) (q.head hqne)
      (q.getLast hqne) (p.head hpne) chord = 2 * Real.pi ∨
    kwChordBoundaryTurnDiscrepancy
      (p.getLast hpne) (q.head hqne)
      (q.getLast hqne) (p.head hpne) chord = -(2 * Real.pi)




def KWFiniteSimplePolygon.CleanChordEndpointOrder
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 1 ≤ j.val) : Prop :=
  let p := polygon.edgeList.take j.val
  let q := polygon.edgeList.drop j.val
  let hpne : p ≠ [] := by
    intro h
    rw [List.take_eq_nil_iff] at h
    rcases h with hzero | hempty
    · omega
    · have hlen := congrArg List.length hempty
      simp [KWFiniteSimplePolygon.edgeList] at hlen
      omega
  let hqne : q ≠ [] := by
    intro h
    rw [List.drop_eq_nil_iff] at h
    simp [KWFiniteSimplePolygon.edgeList] at h
    exact (Nat.not_le_of_lt j.isLt) h
  let chord := polygon.vertex j - polygon.vertex 0
  kwChordBoundaryTurnDiscrepancy
      (p.getLast hpne) (q.head hqne)
      (q.getLast hqne) (p.head hpne) chord ≠ 0



theorem KWFiniteSimplePolygon.cleanChordEndpointOddFullTurn_of_endpointOrder
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 1 ≤ j.val)
    (horder : polygon.CleanChordEndpointOrder j hj) :
    polygon.CleanChordEndpointOddFullTurn j hj := by
  let p := polygon.edgeList.take j.val
  let q := polygon.edgeList.drop j.val
  let chord := polygon.vertex j - polygon.vertex 0
  have hpne : p ≠ [] := by
    intro h
    rw [List.take_eq_nil_iff] at h
    rcases h with hzero | hempty
    · omega
    · have hlen := congrArg List.length hempty
      simp [KWFiniteSimplePolygon.edgeList] at hlen
      omega
  have hqne : q ≠ [] := by
    intro h
    rw [List.drop_eq_nil_iff] at h
    simp [KWFiniteSimplePolygon.edgeList] at h
    exact (Nat.not_le_of_lt j.isLt) h
  have hj0 : j ≠ 0 := by
    apply Fin.ne_of_val_ne
    simpa using (show j.val ≠ 0 by omega)
  have hchord : chord ≠ 0 := by
    exact sub_ne_zero.mpr (polygon.vertex_injective.ne hj0)
  have hne : kwChordBoundaryTurnDiscrepancy
      (p.getLast hpne) (q.head hqne)
      (q.getLast hqne) (p.head hpne) chord ≠ 0 := by
    simpa only [KWFiniteSimplePolygon.CleanChordEndpointOrder,
      p, q, chord] using horder
  have hodd := (kwChordBoundaryTurnDiscrepancy_odd_iff_ne_zero
    (p.getLast hpne) (q.head hqne) (q.getLast hqne)
    (p.head hpne) chord hchord).mpr hne
  simpa only [KWFiniteSimplePolygon.CleanChordEndpointOddFullTurn,
    p, q, chord] using hodd



theorem KWFiniteSimplePolygon.cleanChordBoundaryPhaseCompatible_of_oddFullTurn
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 1 ≤ j.val)
    (hturn : polygon.CleanChordEndpointOddFullTurn j hj) :
    polygon.CleanChordBoundaryPhaseCompatible j hj := by
  let p := polygon.edgeList.take j.val
  let q := polygon.edgeList.drop j.val
  let chord := polygon.vertex j - polygon.vertex 0
  have hpne : p ≠ [] := by
    intro h
    rw [List.take_eq_nil_iff] at h
    rcases h with hzero | hempty
    · omega
    · have hlen := congrArg List.length hempty
      simp [KWFiniteSimplePolygon.edgeList] at hlen
      omega
  have hqne : q ≠ [] := by
    intro h
    rw [List.drop_eq_nil_iff] at h
    simp [KWFiniteSimplePolygon.edgeList] at h
    exact (Nat.not_le_of_lt j.isLt) h
  have hturn' : kwChordBoundaryTurnDiscrepancy
          (p.getLast hpne) (q.head hqne)
          (q.getLast hqne) (p.head hpne) chord = 2 * Real.pi ∨
      kwChordBoundaryTurnDiscrepancy
          (p.getLast hpne) (q.head hqne)
          (q.getLast hqne) (p.head hpne) chord = -(2 * Real.pi) := by
    simpa only [KWFiniteSimplePolygon.CleanChordEndpointOddFullTurn,
      p, q, chord] using hturn
  have hboundary := kwVectorTurnPhase_chord_boundary_of_odd_full_turn
    (p.getLast hpne) (q.head hqne) (q.getLast hqne)
    (p.head hpne) chord hturn'
  simpa only [KWFiniteSimplePolygon.CleanChordBoundaryPhaseCompatible,
    p, q, chord] using hboundary

end StatMech.FrontierA
