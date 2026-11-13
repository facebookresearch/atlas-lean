/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalFixedOffset
import Code.FrontierD.SixVertexBetheOddOffsetBoundaryEstimate





namespace StatMech.FrontierD

open Finset

noncomputable section

def sixVertexCanonicalEvenLeftBoundaryIndex (s k : Nat) (i : Fin s) :
    Fin ((2 * s + k + 1) + (2 * s + k + 1)) :=
  ⟨i, by omega⟩

def sixVertexCanonicalEvenRightBoundaryIndex (s k : Nat) (i : Fin s) :
    Fin ((2 * s + k + 1) + (2 * s + k + 1)) :=
  ⟨s + ((s + k + 1) + (s + k + 1)) + i, by omega⟩

theorem sixVertexCanonicalEvenOffsetBoundarySource_eq_boundarySums
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin ((s + k + 1) + (s + k + 1))) :
    sixVertexCanonicalEvenOffsetBoundarySource hc s k j =
      (∑ i : Fin s, sixVertexTheta c
        (sixVertexCanonicalEvenAlignedHalfRoots hc s k j)
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k)
          (sixVertexCanonicalEvenLeftBoundaryIndex s k i))) +
      ∑ i : Fin s, sixVertexTheta c
        (sixVertexCanonicalEvenAlignedHalfRoots hc s k j)
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k)
          (sixVertexCanonicalEvenRightBoundaryIndex s k i)) := by
  let n := (s + k + 1) + (s + k + 1)
  let H := (2 * s + k + 1) + (2 * s + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k)
  let x := sixVertexCanonicalEvenAlignedHalfRoots hc s k j
  let f : Fin H -> Real := fun l => sixVertexTheta c x (p l)
  have hH : H = s + n + s := by omega
  have hH' : H = s + (n + s) := by omega
  have htotal : (∑ l : Fin H, f l) =
      (∑ i : Fin s, f ⟨i, by omega⟩) +
      ((∑ l : Fin n, f ⟨s + l, by omega⟩) +
        ∑ i : Fin s, f ⟨s + n + i, by omega⟩) := by
    let g : Fin (s + (n + s)) -> Real := fun i =>
      f (Fin.cast hH'.symm i)
    have hfirst := Fin.sum_univ_add (a := s) (b := n + s) g
    have hsecond := Fin.sum_univ_add (a := n) (b := s)
      (fun i : Fin (n + s) => g (Fin.natAdd s i))
    rw [hsecond] at hfirst
    let e : Fin (s + (n + s)) ≃ Fin H :=
      (Fin.castOrderIso hH'.symm).toEquiv
    have hleft : (∑ i : Fin s, g (Fin.castAdd (n + s) i)) =
        ∑ i : Fin s, f ⟨i, by omega⟩ := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [g, e]
      congr 1
    have hmiddle :
        (∑ l : Fin n, g (Fin.natAdd s (Fin.castAdd s l))) =
          ∑ l : Fin n, f ⟨s + l, by omega⟩ := by
      apply Finset.sum_congr rfl
      intro l _
      dsimp only [g, e]
      congr 1
    have hright :
        (∑ i : Fin s, g (Fin.natAdd s (Fin.natAdd n i))) =
          ∑ i : Fin s, f ⟨s + n + i, by omega⟩ := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [g, e]
      congr 1
      apply Fin.ext
      simp only [Fin.cast, Fin.natAdd, Fin.val_mk]
      omega
    calc
      (∑ l : Fin H, f l) = ∑ i : Fin (s + (n + s)), g i := by
        exact (Equiv.sum_comp e f).symm
      _ = (∑ i : Fin s, g (Fin.castAdd (n + s) i)) +
          ((∑ l : Fin n, g (Fin.natAdd s (Fin.castAdd s l))) +
            ∑ i : Fin s, g (Fin.natAdd s (Fin.natAdd n i))) := hfirst
      _ = _ := by rw [hleft, hmiddle, hright]
  unfold sixVertexCanonicalEvenOffsetBoundarySource
  have haligned :
      (∑ l, sixVertexTheta c x
        (sixVertexCanonicalEvenAlignedHalfRoots hc s k l)) =
      ∑ l : Fin n, f ⟨s + l, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro l _
    dsimp [f, x, p, n, sixVertexCanonicalEvenAlignedHalfRoots,
      sixVertexCanonicalEvenHalfIndex]
  rw [haligned]
  change (∑ l : Fin H, f l) -
      ∑ l : Fin n, f ⟨s + l, by omega⟩ = _
  rw [htotal]
  dsimp [f, x, p, n, H, sixVertexCanonicalEvenLeftBoundaryIndex,
    sixVertexCanonicalEvenRightBoundaryIndex]
  ring

theorem abs_sixVertexCanonicalEvenOffsetBoundarySource_sub_continuous_le
    {c : Real} (hc : 2 < c) (s k : Nat)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall y, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + k))
        ((2 * s + k + 1) + (2 * s + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k)) y)
    (j : Fin ((s + k + 1) + (s + k + 1))) :
    |sixVertexCanonicalEvenOffsetBoundarySource hc s k j -
        (2 * s : Real) * sixVertexContinuousOffsetSource c
          (sixVertexCanonicalEvenAlignedHalfRoots hc s k j)| <=
      2 * (s : Real) ^ 2 *
          (sixVertexThetaRightLipschitzNNReal c : Real) /
        ((sixVertexFourWidth 0 (2 * s + k) : Real) * lower) := by
  let t := 2 * s + k
  let N := sixVertexFourWidth 0 t
  let H := (t + 1) + (t + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc t
  let x := sixVertexCanonicalEvenAlignedHalfRoots hc s k j
  let A := (sixVertexThetaRightLipschitzNNReal c : Real)
  let D := (N : Real) * lower
  have hN : 0 < N := sixVertexFourWidth_pos 0 t
  have hhalf : N = 2 * H := by
    dsimp [N, H, t]
    unfold sixVertexFourWidth
    omega
  have hopen : SixVertexOpenRootSimplex p := by
    exact sixVertexCanonicalDensityPerronBetheRoots_mem_open hc t
  have hsol : SixVertexSatisfiesBetheEquations c N H p := by
    exact sixVertexCanonicalDensityPerronBetheRoots_is_solution hc t
  have hD : 0 < D := mul_pos (by exact_mod_cast hN) hlower
  have hA : 0 <= A := NNReal.coe_nonneg _
  have hlip := lipschitzWith_sixVertexTheta_right hc x
  have hleftRoot (i : Fin s) :
      p (sixVertexCanonicalEvenLeftBoundaryIndex s k i) - (-Real.pi) <=
        (s : Real) / D := by
    have h := sixVertexBetheSolution_first_endpoint_le_of_finiteDensityLower
      hc hN hhalf hopen hsol hlower hdensity
        (sixVertexCanonicalEvenLeftBoundaryIndex s k i)
    have hindex :
        (((sixVertexCanonicalEvenLeftBoundaryIndex s k i).val : Real) + 1) <=
          s := by
      dsimp [sixVertexCanonicalEvenLeftBoundaryIndex]
      exact_mod_cast i.isLt
    exact h.trans (div_le_div_of_nonneg_right hindex hD.le)
  have hrightRoot (i : Fin s) :
      Real.pi - p (sixVertexCanonicalEvenRightBoundaryIndex s k i) <=
        (s : Real) / D := by
    have h := sixVertexBetheSolution_last_endpoint_le_of_finiteDensityLower
      hc hN hhalf hopen hsol hlower hdensity
        (sixVertexCanonicalEvenRightBoundaryIndex s k i)
    have hindex :
        ((((sixVertexCanonicalEvenRightBoundaryIndex s k i).rev.val : Nat) :
          Real) + 1) <= s := by
      have hindexNat :
          (sixVertexCanonicalEvenRightBoundaryIndex s k i).rev.val + 1 <= s := by
        simp only [Fin.rev, sixVertexCanonicalEvenRightBoundaryIndex, Fin.val_mk]
        omega
      exact_mod_cast hindexNat
    exact h.trans (div_le_div_of_nonneg_right hindex hD.le)
  have hleftPoint (i : Fin s) :
      |sixVertexTheta c x
          (p (sixVertexCanonicalEvenLeftBoundaryIndex s k i)) -
        sixVertexTheta c x (-Real.pi)| <= A * ((s : Real) / D) := by
    have hdist := hlip.dist_le_mul
      (p (sixVertexCanonicalEvenLeftBoundaryIndex s k i)) (-Real.pi)
    rw [Real.dist_eq, Real.dist_eq] at hdist
    have hroot :
        |p (sixVertexCanonicalEvenLeftBoundaryIndex s k i) - (-Real.pi)| <=
          (s : Real) / D := by
      rw [abs_of_nonneg]
      · exact hleftRoot i
      · exact sub_nonneg.mpr
          (hopen.2.2 (sixVertexCanonicalEvenLeftBoundaryIndex s k i)).1.le
    exact hdist.trans (mul_le_mul_of_nonneg_left hroot hA)
  have hrightPoint (i : Fin s) :
      |sixVertexTheta c x
          (p (sixVertexCanonicalEvenRightBoundaryIndex s k i)) -
        sixVertexTheta c x Real.pi| <= A * ((s : Real) / D) := by
    have hdist := hlip.dist_le_mul
      (p (sixVertexCanonicalEvenRightBoundaryIndex s k i)) Real.pi
    rw [Real.dist_eq, Real.dist_eq] at hdist
    have hroot :
        |p (sixVertexCanonicalEvenRightBoundaryIndex s k i) - Real.pi| <=
          (s : Real) / D := by
      rw [abs_of_nonpos]
      · simpa only [neg_sub] using hrightRoot i
      · exact sub_nonpos.mpr
          (hopen.2.2 (sixVertexCanonicalEvenRightBoundaryIndex s k i)).2.le
    exact hdist.trans (mul_le_mul_of_nonneg_left hroot hA)
  have hleftSum :
      |(∑ i : Fin s, sixVertexTheta c x
          (p (sixVertexCanonicalEvenLeftBoundaryIndex s k i))) -
        (s : Real) * sixVertexTheta c x (-Real.pi)| <=
          (s : Real) * (A * ((s : Real) / D)) := by
    have hconst : (s : Real) * sixVertexTheta c x (-Real.pi) =
        ∑ _i : Fin s, sixVertexTheta c x (-Real.pi) := by simp
    rw [hconst, <- sum_sub_distrib]
    calc
      |∑ i : Fin s, (sixVertexTheta c x
          (p (sixVertexCanonicalEvenLeftBoundaryIndex s k i)) -
            sixVertexTheta c x (-Real.pi))| <=
        ∑ i : Fin s, |sixVertexTheta c x
          (p (sixVertexCanonicalEvenLeftBoundaryIndex s k i)) -
            sixVertexTheta c x (-Real.pi)| := abs_sum_le_sum_abs _ _
      _ <= ∑ _i : Fin s, A * ((s : Real) / D) :=
        sum_le_sum fun i _ => hleftPoint i
      _ = _ := by simp
  have hrightSum :
      |(∑ i : Fin s, sixVertexTheta c x
          (p (sixVertexCanonicalEvenRightBoundaryIndex s k i))) -
        (s : Real) * sixVertexTheta c x Real.pi| <=
          (s : Real) * (A * ((s : Real) / D)) := by
    have hconst : (s : Real) * sixVertexTheta c x Real.pi =
        ∑ _i : Fin s, sixVertexTheta c x Real.pi := by simp
    rw [hconst, <- sum_sub_distrib]
    calc
      |∑ i : Fin s, (sixVertexTheta c x
          (p (sixVertexCanonicalEvenRightBoundaryIndex s k i)) -
            sixVertexTheta c x Real.pi)| <=
        ∑ i : Fin s, |sixVertexTheta c x
          (p (sixVertexCanonicalEvenRightBoundaryIndex s k i)) -
            sixVertexTheta c x Real.pi| := abs_sum_le_sum_abs _ _
      _ <= ∑ _i : Fin s, A * ((s : Real) / D) :=
        sum_le_sum fun i _ => hrightPoint i
      _ = _ := by simp
  rw [sixVertexCanonicalEvenOffsetBoundarySource_eq_boundarySums hc s k j]
  change |((∑ i : Fin s, sixVertexTheta c x
      (p (sixVertexCanonicalEvenLeftBoundaryIndex s k i))) +
      (∑ i : Fin s, sixVertexTheta c x
        (p (sixVertexCanonicalEvenRightBoundaryIndex s k i)))) -
      (2 * s : Real) * sixVertexContinuousOffsetSource c x| <= _
  unfold sixVertexContinuousOffsetSource
  rw [show ((∑ i : Fin s, sixVertexTheta c x
        (p (sixVertexCanonicalEvenLeftBoundaryIndex s k i))) +
      (∑ i : Fin s, sixVertexTheta c x
        (p (sixVertexCanonicalEvenRightBoundaryIndex s k i)))) -
      (2 * s : Real) *
        ((sixVertexTheta c x (-Real.pi) + sixVertexTheta c x Real.pi) / 2) =
      ((∑ i : Fin s, sixVertexTheta c x
        (p (sixVertexCanonicalEvenLeftBoundaryIndex s k i))) -
        (s : Real) * sixVertexTheta c x (-Real.pi)) +
      ((∑ i : Fin s, sixVertexTheta c x
        (p (sixVertexCanonicalEvenRightBoundaryIndex s k i))) -
        (s : Real) * sixVertexTheta c x Real.pi) by ring]
  calc
    |_ + _| <=
      |(∑ i : Fin s, sixVertexTheta c x
        (p (sixVertexCanonicalEvenLeftBoundaryIndex s k i))) -
          (s : Real) * sixVertexTheta c x (-Real.pi)| +
      |(∑ i : Fin s, sixVertexTheta c x
        (p (sixVertexCanonicalEvenRightBoundaryIndex s k i))) -
          (s : Real) * sixVertexTheta c x Real.pi| := abs_add_le _ _
    _ <= (s : Real) * (A * ((s : Real) / D)) +
        (s : Real) * (A * ((s : Real) / D)) :=
      add_le_add hleftSum hrightSum
    _ = 2 * (s : Real) ^ 2 * A / D := by ring

private theorem canonical_sum_fin_three_blocks_pre
    {a n b H : Nat} (hH : H = a + n + b) (f : Fin H -> Real) :
    (∑ i, f i) =
      (∑ i : Fin a, f ⟨i, by omega⟩) +
      (∑ j : Fin n, f ⟨a + j, by omega⟩) +
      (∑ i : Fin b, f ⟨a + n + i, by omega⟩) := by
  have hH' : H = a + (n + b) := by omega
  let g : Fin (a + (n + b)) -> Real := fun i =>
    f (Fin.cast hH'.symm i)
  have hfirst := Fin.sum_univ_add (a := a) (b := n + b) g
  have hsecond := Fin.sum_univ_add (a := n) (b := b)
    (fun i : Fin (n + b) => g (Fin.natAdd a i))
  rw [hsecond] at hfirst
  let e : Fin (a + (n + b)) ≃ Fin H :=
    (Fin.castOrderIso hH'.symm).toEquiv
  have hleft : (∑ i : Fin a, g (Fin.castAdd (n + b) i)) =
      ∑ i : Fin a, f ⟨i, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [g, e]
    congr 1
  have hmiddle :
      (∑ j : Fin n, g (Fin.natAdd a (Fin.castAdd b j))) =
        ∑ j : Fin n, f ⟨a + j, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [g, e]
    congr 1
  have hright :
      (∑ i : Fin b, g (Fin.natAdd a (Fin.natAdd n i))) =
        ∑ i : Fin b, f ⟨a + n + i, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [g, e]
    congr 1
    apply Fin.ext
    simp only [Fin.cast, Fin.natAdd, Fin.val_mk]
    omega
  calc
    (∑ i : Fin H, f i) = ∑ i : Fin (a + (n + b)), g i := by
      exact (Equiv.sum_comp e f).symm
    _ = (∑ i : Fin a, g (Fin.castAdd (n + b) i)) +
        ((∑ j : Fin n, g (Fin.natAdd a (Fin.castAdd b j))) +
          ∑ i : Fin b, g (Fin.natAdd a (Fin.natAdd n i))) := hfirst
    _ = _ := by rw [hleft, hmiddle, hright]; ring

private theorem sixVertexCanonicalOddOffsetBoundarySource_eq_boundary_add_midpoint_pre
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
    let xL := p (sixVertexCanonicalOddLowerHalfIndex s k j)
    let xU := p (sixVertexCanonicalOddUpperHalfIndex s k j)
    let x := (xL + xU) / 2
    let n := ((s + k + 1) + 1) + (s + k + 1)
    sixVertexCanonicalOddOffsetBoundarySource hc s k j =
      ((∑ i : Fin s, sixVertexTheta c xL (p ⟨i, by omega⟩)) +
        (∑ i : Fin (s + 1), sixVertexTheta c xL
          (p ⟨s + n + i, by omega⟩)) +
        (∑ i : Fin (s + 1), sixVertexTheta c xU (p ⟨i, by omega⟩)) +
        (∑ i : Fin s, sixVertexTheta c xU
          (p ⟨s + 1 + n + i, by omega⟩))) / 2 +
      ((∑ l : Fin n, sixVertexTheta c xL (p ⟨s + l, by omega⟩)) +
        (∑ l : Fin n, sixVertexTheta c xU
          (p ⟨s + 1 + l, by omega⟩))) / 2 -
        ∑ l : Fin n, sixVertexTheta c x
          (sixVertexCanonicalOddAlignedHalfRoots hc s k l) := by
  dsimp only
  let n := ((s + k + 1) + 1) + (s + k + 1)
  let H := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  let xL := p (sixVertexCanonicalOddLowerHalfIndex s k j)
  let xU := p (sixVertexCanonicalOddUpperHalfIndex s k j)
  let x := (xL + xU) / 2
  have hLower : H = s + n + (s + 1) := by omega
  have hUpper : H = (s + 1) + n + s := by omega
  have hsumLower := canonical_sum_fin_three_blocks_pre hLower
    (fun l : Fin H => sixVertexTheta c xL (p l))
  have hsumUpper := canonical_sum_fin_three_blocks_pre hUpper
    (fun l : Fin H => sixVertexTheta c xU (p l))
  unfold sixVertexCanonicalOddOffsetBoundarySource
  dsimp only
  change ((∑ l : Fin H, sixVertexTheta c xL (p l)) +
      (∑ l : Fin H, sixVertexTheta c xU (p l))) / 2 -
      (∑ l : Fin n, sixVertexTheta c x
        (sixVertexCanonicalOddAlignedHalfRoots hc s k l)) = _
  rw [hsumLower, hsumUpper]
  ring

private theorem sixVertexCanonicalOddAlignedHalfGap_le_of_finiteDensityLower_pre
    {c : Real} (hc : 2 < c) (s k : Nat)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall y, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + 1 + k))
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) y)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
        (sixVertexCanonicalOddUpperHalfIndex s k j) -
      sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
        (sixVertexCanonicalOddLowerHalfIndex s k j) <=
      1 / ((sixVertexFourWidth 0 (2 * s + 1 + k) : Real) * lower) := by
  let t := 2 * s + 1 + k
  let N := sixVertexFourWidth 0 t
  let H := (t + 1) + (t + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc t
  let iL := sixVertexCanonicalOddLowerHalfIndex s k j
  let iU := sixVertexCanonicalOddUpperHalfIndex s k j
  have hN : 0 < N := sixVertexFourWidth_pos 0 t
  have hopen : SixVertexOpenRootSimplex p :=
    sixVertexCanonicalDensityPerronBetheRoots_mem_open hc t
  have hsol : SixVertexSatisfiesBetheEquations c N H p :=
    sixVertexCanonicalDensityPerronBetheRoots_is_solution hc t
  have horder : p iL <= p iU := by
    exact (hopen.1 (by
      dsimp [iL, iU, sixVertexCanonicalOddLowerHalfIndex,
        sixVertexCanonicalOddUpperHalfIndex]
      simp)).le
  have hmono := intervalIntegral.integral_mono_on horder
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _)
    ((continuous_sixVertexFiniteRootDensity hc N H p).intervalIntegrable _ _)
    (fun x _ => hdensity x)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  rw [intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p (p iL) (p iU),
    sixVertexBetheCountingFunction_at_root hN hsol iU,
    sixVertexBetheCountingFunction_at_root hN hsol iL] at hmono
  have hquantum :
      sixVertexCentralQuantumNumber iU -
        sixVertexCentralQuantumNumber iL = 1 := by
    dsimp [iL, iU]
    rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
    simp [sixVertexCanonicalOddLowerHalfIndex,
      sixVertexCanonicalOddUpperHalfIndex]
  rw [<- sub_div, hquantum] at hmono
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  change p iU - p iL <= 1 / ((N : Real) * lower)
  rw [le_div_iff₀ (mul_pos hNreal hlower)]
  calc
    (p iU - p iL) * ((N : Real) * lower) =
        (N : Real) * ((p iU - p iL) * lower) := by ring
    _ <= (N : Real) * (1 / (N : Real)) :=
      mul_le_mul_of_nonneg_left hmono hNreal.le
    _ = 1 := by field_simp [hNreal.ne']

private theorem canonical_abs_sum_sub_card_mul_le_pre
    {m : Nat} {f : Fin m -> Real} {z E : Real}
    (h : forall i, |f i - z| <= E) :
    |(∑ i, f i) - (m : Real) * z| <= (m : Real) * E := by
  have hconst : (m : Real) * z = ∑ _i : Fin m, z := by simp
  rw [hconst, <- Finset.sum_sub_distrib]
  calc
    |∑ i, (f i - z)| <= ∑ i, |f i - z| := abs_sum_le_sum_abs _ _
    _ <= ∑ _i : Fin m, E := Finset.sum_le_sum fun i _ => h i
    _ = (m : Real) * E := by simp

private theorem canonical_sum_fin_three_blocks
    {a n b H : Nat} (hH : H = a + n + b) (f : Fin H -> Real) :
    (∑ i, f i) =
      (∑ i : Fin a, f ⟨i, by omega⟩) +
      (∑ j : Fin n, f ⟨a + j, by omega⟩) +
      (∑ i : Fin b, f ⟨a + n + i, by omega⟩) := by
  have hH' : H = a + (n + b) := by omega
  let g : Fin (a + (n + b)) -> Real := fun i =>
    f (Fin.cast hH'.symm i)
  have hfirst := Fin.sum_univ_add (a := a) (b := n + b) g
  have hsecond := Fin.sum_univ_add (a := n) (b := b)
    (fun i : Fin (n + b) => g (Fin.natAdd a i))
  rw [hsecond] at hfirst
  let e : Fin (a + (n + b)) ≃ Fin H :=
    (Fin.castOrderIso hH'.symm).toEquiv
  have hleft : (∑ i : Fin a, g (Fin.castAdd (n + b) i)) =
      ∑ i : Fin a, f ⟨i, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [g, e]
    congr 1
  have hmiddle :
      (∑ j : Fin n, g (Fin.natAdd a (Fin.castAdd b j))) =
        ∑ j : Fin n, f ⟨a + j, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [g, e]
    congr 1
  have hright :
      (∑ i : Fin b, g (Fin.natAdd a (Fin.natAdd n i))) =
        ∑ i : Fin b, f ⟨a + n + i, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [g, e]
    congr 1
    apply Fin.ext
    simp only [Fin.cast, Fin.natAdd, Fin.val_mk]
    omega
  calc
    (∑ i : Fin H, f i) = ∑ i : Fin (a + (n + b)), g i := by
      exact (Equiv.sum_comp e f).symm
    _ = (∑ i : Fin a, g (Fin.castAdd (n + b) i)) +
        ((∑ j : Fin n, g (Fin.natAdd a (Fin.castAdd b j))) +
        ∑ i : Fin b, g (Fin.natAdd a (Fin.natAdd n i))) := hfirst
    _ = _ := by rw [hleft, hmiddle, hright]; ring



theorem sixVertexCanonicalOddOffsetBoundarySource_eq_boundary_add_midpoint
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin ((((s + k + 1) + 1) + (s + k + 1)))) :
    let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
    let xL := p (sixVertexCanonicalOddLowerHalfIndex s k j)
    let xU := p (sixVertexCanonicalOddUpperHalfIndex s k j)
    let x := (xL + xU) / 2
    sixVertexCanonicalOddOffsetBoundarySource hc s k j =
      ((∑ i : Fin s, sixVertexTheta c xL (p ⟨i, by omega⟩)) +
        (∑ i : Fin (s + 1),
          sixVertexTheta c xL (p ⟨s +
              (((s + k + 1) + 1) + (s + k + 1)) + i, by
            omega⟩)) +
        (∑ i : Fin (s + 1),
          sixVertexTheta c xU (p ⟨i, by omega⟩)) +
        (∑ i : Fin s,
          sixVertexTheta c xU (p ⟨s + 1 +
              (((s + k + 1) + 1) + (s + k + 1)) + i, by
            omega⟩))) / 2 +
      ((∑ l : Fin ((((s + k + 1) + 1) + (s + k + 1))),
          sixVertexTheta c xL (p ⟨s + l, by
            have hl := l.isLt
            omega⟩)) +
        (∑ l : Fin ((((s + k + 1) + 1) + (s + k + 1))),
          sixVertexTheta c xU (p ⟨s + 1 + l, by
            have hl := l.isLt
            omega⟩))) / 2 -
        ∑ l : Fin ((((s + k + 1) + 1) + (s + k + 1))),
          sixVertexTheta c x
            (sixVertexCanonicalOddAlignedHalfRoots hc s k l) := by
  dsimp only
  let n := (((s + k + 1) + 1) + (s + k + 1))
  let H := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  let iL := sixVertexCanonicalOddLowerHalfIndex s k j
  let iU := sixVertexCanonicalOddUpperHalfIndex s k j
  let xL := p iL
  let xU := p iU
  let x := (xL + xU) / 2
  have hLower : H = s + n + (s + 1) := by
    dsimp [H, n]
    omega
  have hUpper : H = (s + 1) + n + s := by
    dsimp [H, n]
    omega
  have hsumLower := canonical_sum_fin_three_blocks hLower
    (fun l : Fin H => sixVertexTheta c xL (p l))
  have hsumUpper := canonical_sum_fin_three_blocks hUpper
    (fun l : Fin H => sixVertexTheta c xU (p l))
  unfold sixVertexCanonicalOddOffsetBoundarySource
  dsimp only
  change ((∑ l : Fin H, sixVertexTheta c xL (p l)) +
      (∑ l : Fin H, sixVertexTheta c xU (p l))) / 2 -
      (∑ l : Fin n, sixVertexTheta c x
        (sixVertexCanonicalOddAlignedHalfRoots hc s k l)) = _
  rw [hsumLower, hsumUpper]
  apply congrArg (fun z : Real => z)
  ring



theorem sixVertexCanonicalOddAlignedHalfGap_le_of_finiteDensityLower
    {c : Real} (hc : 2 < c) (s k : Nat)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall y, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + 1 + k))
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) y)
    (j : Fin ((((s + k + 1) + 1) + (s + k + 1)))) :
    sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
        (sixVertexCanonicalOddUpperHalfIndex s k j) -
      sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
        (sixVertexCanonicalOddLowerHalfIndex s k j) <=
      1 / ((sixVertexFourWidth 0 (2 * s + 1 + k) : Real) * lower) := by
  let t := 2 * s + 1 + k
  let N := sixVertexFourWidth 0 t
  let H := (t + 1) + (t + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc t
  let iL := sixVertexCanonicalOddLowerHalfIndex s k j
  let iU := sixVertexCanonicalOddUpperHalfIndex s k j
  have hN : 0 < N := sixVertexFourWidth_pos 0 t
  have hopen : SixVertexOpenRootSimplex p :=
    sixVertexCanonicalDensityPerronBetheRoots_mem_open hc t
  have hsol : SixVertexSatisfiesBetheEquations c N H p := by
    exact sixVertexCanonicalDensityPerronBetheRoots_is_solution hc t
  have horder : p iL <= p iU := by
    exact (hopen.1 (by
      dsimp [iL, iU, sixVertexCanonicalOddLowerHalfIndex,
        sixVertexCanonicalOddUpperHalfIndex]
      simp)).le
  have hmono := intervalIntegral.integral_mono_on horder
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _)
    ((continuous_sixVertexFiniteRootDensity hc N H p).intervalIntegrable _ _)
    (fun x _ => hdensity x)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  rw [intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p (p iL) (p iU),
    sixVertexBetheCountingFunction_at_root hN hsol iU,
    sixVertexBetheCountingFunction_at_root hN hsol iL] at hmono
  have hquantum :
      sixVertexCentralQuantumNumber iU -
        sixVertexCentralQuantumNumber iL = 1 := by
    dsimp [iL, iU]
    rw [sixVertexCentralQuantumNumber_eq,
      sixVertexCentralQuantumNumber_eq]
    simp [sixVertexCanonicalOddLowerHalfIndex,
      sixVertexCanonicalOddUpperHalfIndex]
  rw [<- sub_div, hquantum] at hmono
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  change p iU - p iL <= 1 / ((N : Real) * lower)
  rw [le_div_iff₀ (mul_pos hNreal hlower)]
  calc
    (p iU - p iL) * ((N : Real) * lower) =
        (N : Real) * ((p iU - p iL) * lower) := by ring
    _ <= (N : Real) * (1 / (N : Real)) :=
      mul_le_mul_of_nonneg_left hmono hNreal.le
    _ = 1 := by field_simp [hNreal.ne']



private theorem canonical_abs_sum_sub_card_mul_le
    {m : Nat} {f : Fin m -> Real} {z E : Real}
    (h : forall i, |f i - z| <= E) :
    |(∑ i, f i) - (m : Real) * z| <= (m : Real) * E := by
  have hconst : (m : Real) * z = ∑ _i : Fin m, z := by simp
  rw [hconst, <- Finset.sum_sub_distrib]
  calc
    |∑ i, (f i - z)| <= ∑ i, |f i - z| := abs_sum_le_sum_abs _ _
    _ <= ∑ _i : Fin m, E := Finset.sum_le_sum fun i _ => h i
    _ = (m : Real) * E := by simp




theorem abs_sixVertexCanonicalOddOffsetBoundarySource_sub_continuous_le
    {c : Real} (hc : 2 < c) (s k : Nat)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall y, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + 1 + k))
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) y)
    (j : Fin ((((s + k + 1) + 1) + (s + k + 1)))) :
    |sixVertexCanonicalOddOffsetBoundarySource hc s k j -
        (2 * s + 1 : Real) * sixVertexContinuousOffsetSource c
          (sixVertexCanonicalOddAlignedHalfRoots hc s k j)| <=
      (2 * s + 1 : Real) *
          (sixVertexThetaRightLipschitzNNReal c : Real) * (s + 2 : Real) /
        ((sixVertexFourWidth 0 (2 * s + 1 + k) : Real) * lower) +
      ((((s + k + 1) + 1) + (s + k + 1)) : Real) *
          sixVertexThetaTaylorBound c /
        (((sixVertexFourWidth 0 (2 * s + 1 + k) : Real) * lower) ^ 2) := by
  let t := 2 * s + 1 + k
  let N := sixVertexFourWidth 0 t
  let n := (((s + k + 1) + 1) + (s + k + 1))
  let H := (t + 1) + (t + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc t
  let iL := sixVertexCanonicalOddLowerHalfIndex s k j
  let iU := sixVertexCanonicalOddUpperHalfIndex s k j
  let xL := p iL
  let xU := p iU
  let x := (xL + xU) / 2
  let A := (sixVertexThetaRightLipschitzNNReal c : Real)
  let T := sixVertexThetaTaylorBound c
  let D := (N : Real) * lower
  let E := A * ((s + 2 : Nat) : Real) / D
  have hN : 0 < N := sixVertexFourWidth_pos 0 t
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hD : 0 < D := mul_pos hNreal hlower
  have hA : 0 <= A := NNReal.coe_nonneg _
  have hT : 0 <= T := by
    dsimp [T, sixVertexThetaTaylorBound, sixVertexThetaCrossLipschitzBound]
    exact add_nonneg (sixVertexThetaLeftKernelLipschitzBound_pos hc).le
      (div_nonneg (sixVertexRootDensityKernelLipschitzBound_pos hc).le
        (div_nonneg
          (sub_nonneg.mpr (one_lt_sixVertexAnisotropyMagnitude hc).le)
          (sixVertexRootDensityScale_pos hc).le))
  have hE : 0 <= E := by dsimp [E]; positivity
  have hopen : SixVertexOpenRootSimplex p :=
    sixVertexCanonicalDensityPerronBetheRoots_mem_open hc t
  have hsol : SixVertexSatisfiesBetheEquations c N H p :=
    sixVertexCanonicalDensityPerronBetheRoots_is_solution hc t
  have hhalf : N = 2 * H := by
    dsimp [N, H, t]
    unfold sixVertexFourWidth
    omega
  have hgap (l : Fin n) :
      0 <= p (sixVertexCanonicalOddUpperHalfIndex s k l) -
          p (sixVertexCanonicalOddLowerHalfIndex s k l) /\
      p (sixVertexCanonicalOddUpperHalfIndex s k l) -
          p (sixVertexCanonicalOddLowerHalfIndex s k l) <= 1 / D := by
    constructor
    · exact sub_nonneg.mpr ((hopen.1 (by
        simp [sixVertexCanonicalOddLowerHalfIndex,
          sixVertexCanonicalOddUpperHalfIndex])).le)
    · simpa [t, N, p, D, n] using
        sixVertexCanonicalOddAlignedHalfGap_le_of_finiteDensityLower
          hc s k hlower hdensity l
  have hxgap := hgap j
  have hxL : |xL - x| <= 1 / D := by
    have hx : xL - x =
        -(p iU - p iL) / 2 := by dsimp [x, xL, xU]; ring
    rw [hx, abs_div, abs_neg, abs_of_nonneg hxgap.1,
      abs_of_pos (by norm_num : (0 : Real) < 2)]
    nlinarith [one_div_pos.mpr hD]
  have hxU : |xU - x| <= 1 / D := by
    have hx : xU - x = (p iU - p iL) / 2 := by
      dsimp [x, xL, xU]
      ring
    rw [hx, abs_div, abs_of_nonneg hxgap.1,
      abs_of_pos (by norm_num : (0 : Real) < 2)]
    nlinarith [one_div_pos.mpr hD]
  have hpoint (row y endpoint : Real)
      (hrow : |row - x| <= 1 / D)
      (hy : |y - endpoint| <= (s + 1 : Real) / D) :
      |sixVertexTheta c row y - sixVertexTheta c x endpoint| <= E := by
    have hleft := (lipschitzWith_sixVertexTheta_left hc y).dist_le_mul row x
    have hright := (lipschitzWith_sixVertexTheta_right hc x).dist_le_mul y endpoint
    rw [Real.dist_eq, Real.dist_eq] at hleft hright
    calc
      |sixVertexTheta c row y - sixVertexTheta c x endpoint| <=
          |sixVertexTheta c row y - sixVertexTheta c x y| +
            |sixVertexTheta c x y - sixVertexTheta c x endpoint| :=
        abs_sub_le _ _ _
      _ <= A * |row - x| + A * |y - endpoint| :=
        add_le_add hleft hright
      _ <= A * (1 / D) + A * ((s + 1 : Real) / D) :=
        add_le_add (mul_le_mul_of_nonneg_left hrow hA)
          (mul_le_mul_of_nonneg_left hy hA)
      _ = E := by dsimp [E]; push_cast; ring
  have hleftEndpoint (q : Fin H)
      (hq : ((q.val : Nat) : Real) + 1 <= (s : Real) + 1) :
      |p q - (-Real.pi)| <= ((s : Real) + 1) / D := by
    have h := sixVertexBetheSolution_first_endpoint_le_of_finiteDensityLower
      hc hN hhalf hopen hsol hlower hdensity q
    rw [abs_of_nonneg]
    · exact h.trans (div_le_div_of_nonneg_right hq hD.le)
    · exact sub_nonneg.mpr (hopen.2.2 q).1.le
  have hrightEndpoint (q : Fin H)
      (hq : (((q.rev.val : Nat) : Real) + 1) <= (s : Real) + 1) :
      |p q - Real.pi| <= ((s : Real) + 1) / D := by
    have h := sixVertexBetheSolution_last_endpoint_le_of_finiteDensityLower
      hc hN hhalf hopen hsol hlower hdensity q
    rw [abs_of_nonpos]
    · simpa only [neg_sub] using
        h.trans (div_le_div_of_nonneg_right hq hD.le)
    · exact sub_nonpos.mpr (hopen.2.2 q).2.le
  let LL : Real := ∑ i : Fin s, sixVertexTheta c xL (p ⟨i, by omega⟩)
  let LR : Real := ∑ i : Fin (s + 1), sixVertexTheta c xL
    (p ⟨s + n + i, by
      dsimp [n, H, t]
      omega⟩)
  let UL : Real := ∑ i : Fin (s + 1), sixVertexTheta c xU (p ⟨i, by omega⟩)
  let UR : Real := ∑ i : Fin s, sixVertexTheta c xU
    (p ⟨s + 1 + n + i, by
      dsimp [n, H, t]
      omega⟩)
  let thetaL := sixVertexTheta c x (-Real.pi)
  let thetaR := sixVertexTheta c x Real.pi
  have hLL : |LL - (s : Real) * thetaL| <= (s : Real) * E := by
    apply canonical_abs_sum_sub_card_mul_le
    intro i
    exact hpoint xL (p ⟨i, by omega⟩) (-Real.pi) hxL
      (hleftEndpoint ⟨i, by omega⟩ (by
        have hiNat : i.val + 1 <= s + 1 := by omega
        exact_mod_cast hiNat))
  have hUL : |UL - (s + 1 : Real) * thetaL| <= (s + 1 : Real) * E := by
    simpa [UL, thetaL] using
      (canonical_abs_sum_sub_card_mul_le (m := s + 1) (E := E)
        (f := fun i : Fin (s + 1) =>
          sixVertexTheta c xU (p ⟨i, by omega⟩))
        (z := thetaL) (fun i =>
          hpoint xU (p ⟨i, by omega⟩) (-Real.pi) hxU
            (hleftEndpoint ⟨i, by omega⟩ (by
              have hiNat : i.val + 1 <= s + 1 := by omega
              exact_mod_cast hiNat))))
  have hLR : |LR - (s + 1 : Real) * thetaR| <= (s + 1 : Real) * E := by
    simpa [LR, thetaR] using
      (canonical_abs_sum_sub_card_mul_le (m := s + 1) (E := E)
        (f := fun i : Fin (s + 1) => sixVertexTheta c xL
          (p ⟨s + n + i, by
            dsimp [n, H, t]
            omega⟩))
        (z := thetaR) (fun i =>
          hpoint xL _ Real.pi hxL (hrightEndpoint _ (by
            have hi := i.isLt
            have hnat :
                ((⟨s + n + i, by
                    dsimp [n, H, t]
                    omega⟩ : Fin H).rev.val + 1) <= s + 1 := by
              simp only [Fin.rev, Fin.val_mk]
              dsimp [n, H, t]
              omega
            exact_mod_cast hnat))))
  have hUR : |UR - (s : Real) * thetaR| <= (s : Real) * E := by
    apply canonical_abs_sum_sub_card_mul_le
    intro i
    let q : Fin H := ⟨s + 1 + n + i, by
      dsimp [n, H, t]
      omega⟩
    have hq : (((q.rev.val : Nat) : Real) + 1) <= (s : Real) + 1 := by
      have hnat : q.rev.val + 1 <= s + 1 := by
        have hi := i.isLt
        dsimp [q, Fin.rev, n, H, t]
        omega
      exact_mod_cast hnat
    have hi := hrightEndpoint q hq
    exact hpoint xU (p q) Real.pi hxU hi
  have hboundary :
      |(LL + LR + UL + UR) / 2 -
          (2 * s + 1 : Real) * (thetaL + thetaR) / 2| <=
        (2 * s + 1 : Real) * E := by
    have hrewrite :
        (LL + LR + UL + UR) / 2 -
            (2 * s + 1 : Real) * (thetaL + thetaR) / 2 =
          ((LL - (s : Real) * thetaL) +
            (UL - (s + 1 : Real) * thetaL) +
            (LR - (s + 1 : Real) * thetaR) +
            (UR - (s : Real) * thetaR)) / 2 := by
      ring
    rw [hrewrite, abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
    calc
      |_ + _ + _ + _| / 2 <=
          (|LL - (s : Real) * thetaL| +
            |UL - (s + 1 : Real) * thetaL| +
            |LR - (s + 1 : Real) * thetaR| +
            |UR - (s : Real) * thetaR|) / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact (abs_add_le _ _).trans
          (add_le_add ((abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ <= (((s : Real) * E + (s + 1 : Real) * E) +
          ((s + 1 : Real) * E + (s : Real) * E)) / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        linarith
      _ = (2 * s + 1 : Real) * E := by ring
  let CL : Real := ∑ l : Fin n, sixVertexTheta c xL
    (p ⟨s + l, by
      have hl := l.isLt
      dsimp [n, H, t]
      omega⟩)
  let CU : Real := ∑ l : Fin n, sixVertexTheta c xU
    (p ⟨s + 1 + l, by
      have hl := l.isLt
      dsimp [n, H, t]
      omega⟩)
  let CM : Real := ∑ l : Fin n, sixVertexTheta c x
    (sixVertexCanonicalOddAlignedHalfRoots hc s k l)
  have hmidPoint (l : Fin n) :
      |(sixVertexTheta c xL
            (p ⟨s + l, by
              have hl := l.isLt
              dsimp [n, H, t]
              omega⟩) +
          sixVertexTheta c xU
            (p ⟨s + 1 + l, by
              have hl := l.isLt
              dsimp [n, H, t]
              omega⟩)) / 2 -
        sixVertexTheta c x
          (sixVertexCanonicalOddAlignedHalfRoots hc s k l)| <= T / D ^ 2 := by
    have hIL : (⟨s + l, by
          have hl := l.isLt
          dsimp [n, H, t]
          omega⟩ : Fin H) = sixVertexCanonicalOddLowerHalfIndex s k l := by
      apply Fin.ext
      simp [sixVertexCanonicalOddLowerHalfIndex]
    have hIU : (⟨s + 1 + l, by
          have hl := l.isLt
          dsimp [n, H, t]
          omega⟩ : Fin H) = sixVertexCanonicalOddUpperHalfIndex s k l := by
      apply Fin.ext
      simp [sixVertexCanonicalOddUpperHalfIndex]
    have h := abs_sixVertexTheta_average_sub_midpoint_le hc xL xU
      (p ⟨s + l, by
        have hl := l.isLt
        dsimp [n, H, t]
        omega⟩)
      (p ⟨s + 1 + l, by
        have hl := l.isLt
        dsimp [n, H, t]
        omega⟩)
    have hgl := hgap l
    have hsum : |xU - xL| +
        |p (sixVertexCanonicalOddUpperHalfIndex s k l) -
          p (sixVertexCanonicalOddLowerHalfIndex s k l)| <= 2 / D := by
      rw [abs_of_nonneg hxgap.1, abs_of_nonneg hgl.1]
      calc
        _ <= 1 / D + 1 / D := add_le_add hxgap.2 hgl.2
        _ = 2 / D := by ring
    have hsq : (|xU - xL| +
        |p (sixVertexCanonicalOddUpperHalfIndex s k l) -
          p (sixVertexCanonicalOddLowerHalfIndex s k l)|) ^ 2 <=
          (2 / D) ^ 2 := by
      exact (sq_le_sq₀ (by positivity)
        (div_nonneg (by norm_num) hD.le)).2 hsum
    rw [hIL, hIU] at h
    have hscaled := mul_le_mul_of_nonneg_left hsq hT
    calc
      _ <= T * (|xU - xL| +
          |p (sixVertexCanonicalOddUpperHalfIndex s k l) -
            p (sixVertexCanonicalOddLowerHalfIndex s k l)|) ^ 2 / 4 := by
        simpa only [x, xL, xU, T, p,
          sixVertexCanonicalOddAlignedHalfRoots] using h
      _ <= T * (2 / D) ^ 2 / 4 :=
        div_le_div_of_nonneg_right hscaled (by norm_num)
      _ = T / D ^ 2 := by field_simp [hD.ne']; ring
  have hmid : |(CL + CU) / 2 - CM| <= (n : Real) * T / D ^ 2 := by
    have hrearrange : (CL + CU) / 2 - CM =
        ∑ l : Fin n,
          ((sixVertexTheta c xL
                (p ⟨s + l, by
                  have hl := l.isLt
                  dsimp [n, H, t]
                  omega⟩) +
              sixVertexTheta c xU
                (p ⟨s + 1 + l, by
                  have hl := l.isLt
                  dsimp [n, H, t]
                  omega⟩)) / 2 -
            sixVertexTheta c x
              (sixVertexCanonicalOddAlignedHalfRoots hc s k l)) := by
      dsimp [CL, CU, CM]
      simp only [div_eq_mul_inv]
      rw [Finset.sum_sub_distrib]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
    rw [hrearrange]
    calc
      |∑ l : Fin n, _| <= ∑ l : Fin n, |_| := abs_sum_le_sum_abs _ _
      _ <= ∑ _l : Fin n, T / D ^ 2 :=
        Finset.sum_le_sum fun l _ => hmidPoint l
      _ = (n : Real) * T / D ^ 2 := by simp; ring
  have hexact :=
    sixVertexCanonicalOddOffsetBoundarySource_eq_boundary_add_midpoint hc s k j
  have hxdef : sixVertexCanonicalOddAlignedHalfRoots hc s k j = x := by
    rfl
  have hsource : sixVertexContinuousOffsetSource c x =
      (thetaL + thetaR) / 2 := by rfl
  rw [hxdef, hexact]
  change |(LL + LR + UL + UR) / 2 + (CL + CU) / 2 - CM -
      (2 * s + 1 : Real) * sixVertexContinuousOffsetSource c x| <= _
  rw [hsource]
  have hrearrange :
      (LL + LR + UL + UR) / 2 + (CL + CU) / 2 - CM -
          (2 * s + 1 : Real) * ((thetaL + thetaR) / 2) =
        ((LL + LR + UL + UR) / 2 -
          (2 * s + 1 : Real) * (thetaL + thetaR) / 2) +
        ((CL + CU) / 2 - CM) := by ring
  rw [hrearrange]
  calc
    |_ + _| <=
        |(LL + LR + UL + UR) / 2 -
          (2 * s + 1 : Real) * (thetaL + thetaR) / 2| +
        |(CL + CU) / 2 - CM| := abs_add_le _ _
    _ <= (2 * s + 1 : Real) * E + (n : Real) * T / D ^ 2 :=
      add_le_add hboundary hmid
    _ = _ := by
      dsimp [E, D, A, T, N, n, t]
      push_cast
      ring


end

end StatMech.FrontierD
