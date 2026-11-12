/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopRectangularSpectralBridge
import Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint










open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology

namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Ising StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def ons_setGraphEdgeWeight (weight : Sym2 V → Complex)
    (edge : Sym2 V) (z : Complex) : Sym2 V → Complex :=
  fun other ↦ if other = edge then z else weight other

@[simp] theorem ons_setGraphEdgeWeight_self
    (weight : Sym2 V → Complex) (edge : Sym2 V) (z : Complex) :
    ons_setGraphEdgeWeight weight edge z edge = z := by
  simp [ons_setGraphEdgeWeight]

@[simp] theorem ons_setGraphEdgeWeight_of_ne
    (weight : Sym2 V → Complex) (edge other : Sym2 V) (z : Complex)
    (hne : other ≠ edge) :
    ons_setGraphEdgeWeight weight edge z other = weight other := by
  simp [ons_setGraphEdgeWeight, hne]

private theorem prod_ons_setGraphEdgeWeight_of_mem
    (weight : Sym2 V → Complex) (edge : Sym2 V) (z : Complex)
    (F : Finset (Sym2 V)) (hedge : edge ∈ F) :
    ∏ f ∈ F, ons_setGraphEdgeWeight weight edge z f =
      z * ∏ f ∈ F.erase edge, weight f := by
  calc
    ∏ f ∈ F, ons_setGraphEdgeWeight weight edge z f =
        (∏ f ∈ F.erase edge,
          ons_setGraphEdgeWeight weight edge z f) *
            ons_setGraphEdgeWeight weight edge z edge := by
      exact (Finset.prod_erase_mul _ _ hedge).symm
    _ = z * ∏ f ∈ F.erase edge, weight f := by
      rw [ons_setGraphEdgeWeight_self]
      rw [mul_comm]
      congr 1
      apply Finset.prod_congr rfl
      intro f hf
      exact ons_setGraphEdgeWeight_of_ne weight edge f z
        (Finset.ne_of_mem_erase hf)

private theorem prod_ons_setGraphEdgeWeight_of_not_mem
    (weight : Sym2 V → Complex) (edge : Sym2 V) (z : Complex)
    (F : Finset (Sym2 V)) (hedge : edge ∉ F) :
    ∏ f ∈ F, ons_setGraphEdgeWeight weight edge z f =
      ∏ f ∈ F, weight f := by
  apply Finset.prod_congr rfl
  intro f hf
  exact ons_setGraphEdgeWeight_of_ne weight edge f z
    (fun h ↦ hedge (h ▸ hf))



def ons_kwEvenEdgeCoefficient (weight : Sym2 V → Complex)
    (edge : Sym2 V) : Complex :=
  ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
    if edge ∈ F then ∏ f ∈ F.erase edge, weight f else 0



theorem kwEvenPolynomial_setEdge_affine
    (weight : Sym2 V → Complex) (edge : Sym2 V) (z : Complex) :
    kwEvenPolynomial G (ons_setGraphEdgeWeight weight edge z) =
      kwEvenPolynomial G (ons_setGraphEdgeWeight weight edge 0) +
        z * ons_kwEvenEdgeCoefficient G weight edge := by
  classical
  unfold kwEvenPolynomial ons_kwEvenEdgeCoefficient
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro F hF
  by_cases hedge : edge ∈ F
  · rw [prod_ons_setGraphEdgeWeight_of_mem weight edge z F hedge,
      prod_ons_setGraphEdgeWeight_of_mem weight edge 0 F hedge]
    simp [hedge]
  · rw [prod_ons_setGraphEdgeWeight_of_not_mem weight edge z F hedge,
      prod_ons_setGraphEdgeWeight_of_not_mem weight edge 0 F hedge]
    simp [hedge]




def ons_reciprocalInterpolationCoeff (q : Complex) (s : Fin 3) : Complex :=
  if s = 0 then q ^ 2 - (q ^ 2)⁻¹
  else if s = 1 then ((q ^ 2)⁻¹ + 1) / 2
  else ((q ^ 2)⁻¹ - 1) / 2


def ons_reciprocalInterpolationValue (q : Complex) (s : Fin 3) : Complex :=
  if s = 0 then 0 else if s = 1 then q else -q

@[simp] theorem ons_reciprocalInterpolationCoeff_zero (q : Complex) :
    ons_reciprocalInterpolationCoeff q (0 : Fin 3) =
      q ^ 2 - (q ^ 2)⁻¹ := by
  simp [ons_reciprocalInterpolationCoeff]

@[simp] theorem ons_reciprocalInterpolationCoeff_one (q : Complex) :
    ons_reciprocalInterpolationCoeff q (1 : Fin 3) =
      ((q ^ 2)⁻¹ + 1) / 2 := by
  simp [ons_reciprocalInterpolationCoeff]

@[simp] theorem ons_reciprocalInterpolationCoeff_two (q : Complex) :
    ons_reciprocalInterpolationCoeff q (2 : Fin 3) =
      ((q ^ 2)⁻¹ - 1) / 2 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp [ons_reciprocalInterpolationCoeff, h20, h21]

@[simp] theorem ons_reciprocalInterpolationValue_zero (q : Complex) :
    ons_reciprocalInterpolationValue q (0 : Fin 3) = 0 := by
  simp [ons_reciprocalInterpolationValue]

@[simp] theorem ons_reciprocalInterpolationValue_one (q : Complex) :
    ons_reciprocalInterpolationValue q (1 : Fin 3) = q := by
  simp [ons_reciprocalInterpolationValue]

@[simp] theorem ons_reciprocalInterpolationValue_two (q : Complex) :
    ons_reciprocalInterpolationValue q (2 : Fin 3) = -q := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp [ons_reciprocalInterpolationValue, h20, h21]

theorem sum_reciprocalInterpolationCoeff (q : Complex) (hq : q ≠ 0) :
    ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s = q ^ 2 := by
  rw [Fin.sum_univ_three]
  simp only [ons_reciprocalInterpolationCoeff_zero,
    ons_reciprocalInterpolationCoeff_one,
    ons_reciprocalInterpolationCoeff_two]
  field_simp
  ring

theorem sum_reciprocalInterpolationCoeff_mul_value
    (q : Complex) (hq : q ≠ 0) :
    ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s *
      ons_reciprocalInterpolationValue q s = q := by
  rw [Fin.sum_univ_three]
  simp only [ons_reciprocalInterpolationCoeff_zero,
    ons_reciprocalInterpolationCoeff_one,
    ons_reciprocalInterpolationCoeff_two,
    ons_reciprocalInterpolationValue_zero,
    ons_reciprocalInterpolationValue_one,
    ons_reciprocalInterpolationValue_two]
  field_simp
  ring

theorem sum_reciprocalInterpolationCoeff_mul_value_sq
    (q : Complex) (hq : q ≠ 0) :
    ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s *
      ons_reciprocalInterpolationValue q s ^ 2 = 1 := by
  rw [Fin.sum_univ_three]
  simp only [ons_reciprocalInterpolationCoeff_zero,
    ons_reciprocalInterpolationCoeff_one,
    ons_reciprocalInterpolationCoeff_two,
    ons_reciprocalInterpolationValue_zero,
    ons_reciprocalInterpolationValue_one,
    ons_reciprocalInterpolationValue_two]
  field_simp
  ring



theorem reciprocalInterpolation_affine_sq
    (A B q : Complex) (hq : q ≠ 0) :
    q ^ 2 * (A + q⁻¹ * B) ^ 2 =
      ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s *
        (A + ons_reciprocalInterpolationValue q s * B) ^ 2 := by
  rw [Fin.sum_univ_three]
  simp only [ons_reciprocalInterpolationCoeff_zero,
    ons_reciprocalInterpolationCoeff_one,
    ons_reciprocalInterpolationCoeff_two,
    ons_reciprocalInterpolationValue_zero,
    ons_reciprocalInterpolationValue_one,
    ons_reciprocalInterpolationValue_two]
  field_simp
  ring





theorem reciprocalKWDet_eq_bounded_three_point
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → Complex) (edge : Sym2 V)
    (q : Complex) (hq : q ≠ 0) :
    q ^ 2 *
        (1 - kwGraphTransition G
          (ons_setGraphEdgeWeight weight edge q⁻¹)
          embedding.turnPhase).det =
      ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s *
        (1 - kwGraphTransition G
          (ons_setGraphEdgeWeight weight edge
            (ons_reciprocalInterpolationValue q s))
          embedding.turnPhase).det := by
  simp_rw [kacWard_straightLine_arbitrary_adaptive G embedding]
  let A := kwEvenPolynomial G (ons_setGraphEdgeWeight weight edge 0)
  let B := ons_kwEvenEdgeCoefficient G weight edge
  have haff (z : Complex) :
      kwEvenPolynomial G (ons_setGraphEdgeWeight weight edge z) = A + z * B :=
    kwEvenPolynomial_setEdge_affine G weight edge z
  simp_rw [haff]
  exact reciprocalInterpolation_affine_sq A B q hq





def ons_setGraphEdgeWeightList (weight : Sym2 V → Complex)
    (z : Complex) : List (Sym2 V) → Sym2 V → Complex
  | [] => weight
  | edge :: edges =>
      ons_setGraphEdgeWeight
        (ons_setGraphEdgeWeightList weight z edges) edge z

theorem ons_setGraphEdgeWeightList_apply
    (weight : Sym2 V → Complex) (z : Complex)
    (edges : List (Sym2 V)) (edge : Sym2 V) :
    ons_setGraphEdgeWeightList weight z edges edge =
      if edge ∈ edges then z else weight edge := by
  induction edges with
  | nil => simp [ons_setGraphEdgeWeightList]
  | cons first rest ih =>
      by_cases hfirst : edge = first
      · subst first
        simp [ons_setGraphEdgeWeightList]
      · simp [ons_setGraphEdgeWeightList, hfirst, ih]

theorem ons_setGraphEdgeWeight_comm
    (weight : Sym2 V → Complex) (e f : Sym2 V) (z w : Complex)
    (hef : e ≠ f) :
    ons_setGraphEdgeWeight (ons_setGraphEdgeWeight weight e z) f w =
      ons_setGraphEdgeWeight (ons_setGraphEdgeWeight weight f w) e z := by
  funext edge
  by_cases he : edge = e
  · subst edge
    simp [ons_setGraphEdgeWeight, hef]
  · by_cases hf : edge = f
    · subst edge
      simp [ons_setGraphEdgeWeight, he]
    · simp [ons_setGraphEdgeWeight, he, hf]

theorem ons_setGraphEdgeWeightList_set_comm
    (weight : Sym2 V → Complex) (edge : Sym2 V)
    (z w : Complex) (edges : List (Sym2 V))
    (hedge : edge ∉ edges) :
    ons_setGraphEdgeWeightList
        (ons_setGraphEdgeWeight weight edge z) w edges =
      ons_setGraphEdgeWeight
        (ons_setGraphEdgeWeightList weight w edges) edge z := by
  induction edges with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.mem_cons, not_or] at hedge
      simp only [ons_setGraphEdgeWeightList]
      rw [ih hedge.2,
        ons_setGraphEdgeWeight_comm _ edge first z w hedge.1]


def ons_boundedReciprocalKWDetResum
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → Complex) (q : Complex) :
    List (Sym2 V) → Complex
  | [] => (1 - kwGraphTransition G weight embedding.turnPhase).det
  | edge :: edges =>
      ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s *
        ons_boundedReciprocalKWDetResum embedding
          (ons_setGraphEdgeWeight weight edge
            (ons_reciprocalInterpolationValue q s)) q edges



theorem reciprocalKWDet_list_eq_bounded_resum
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → Complex) (q : Complex) (hq : q ≠ 0)
    (edges : List (Sym2 V)) (hedges : edges.Nodup) :
    q ^ (2 * edges.length) *
        (1 - kwGraphTransition G
          (ons_setGraphEdgeWeightList weight q⁻¹ edges)
          embedding.turnPhase).det =
      ons_boundedReciprocalKWDetResum G embedding weight q edges := by
  induction edges generalizing weight with
  | nil => simp [ons_setGraphEdgeWeightList,
      ons_boundedReciprocalKWDetResum]
  | cons edge edges ih =>
      rw [List.nodup_cons] at hedges
      have hcomm :
          ons_setGraphEdgeWeightList weight q⁻¹ (edge :: edges) =
            ons_setGraphEdgeWeight
              (ons_setGraphEdgeWeightList weight q⁻¹ edges)
              edge q⁻¹ := rfl
      rw [hcomm, List.length_cons, Nat.mul_succ]
      rw [pow_add, pow_two]
      have hlocal := reciprocalKWDet_eq_bounded_three_point G embedding
        (ons_setGraphEdgeWeightList weight q⁻¹ edges) edge q hq
      rw [show q ^ (2 * edges.length) * (q * q) *
          (1 - kwGraphTransition G
            (ons_setGraphEdgeWeight
              (ons_setGraphEdgeWeightList weight q⁻¹ edges)
              edge q⁻¹) embedding.turnPhase).det =
          q ^ (2 * edges.length) *
            (q ^ 2 *
              (1 - kwGraphTransition G
                (ons_setGraphEdgeWeight
                  (ons_setGraphEdgeWeightList weight q⁻¹ edges)
                  edge q⁻¹) embedding.turnPhase).det) by ring]
      rw [hlocal, Finset.mul_sum]
      unfold ons_boundedReciprocalKWDetResum
      apply Finset.sum_congr rfl
      intro s hs
      have hind := ih
        (ons_setGraphEdgeWeight weight edge
          (ons_reciprocalInterpolationValue q s)) hedges.2
      rw [ons_setGraphEdgeWeightList_set_comm
        weight edge (ons_reciprocalInterpolationValue q s) q⁻¹
        edges hedges.1] at hind
      calc
        q ^ (2 * edges.length) *
            (ons_reciprocalInterpolationCoeff q s *
              (1 - kwGraphTransition G
                (ons_setGraphEdgeWeight
                  (ons_setGraphEdgeWeightList weight q⁻¹ edges) edge
                  (ons_reciprocalInterpolationValue q s))
                embedding.turnPhase).det) =
          ons_reciprocalInterpolationCoeff q s *
            (q ^ (2 * edges.length) *
              (1 - kwGraphTransition G
                (ons_setGraphEdgeWeight
                  (ons_setGraphEdgeWeightList weight q⁻¹ edges) edge
                  (ons_reciprocalInterpolationValue q s))
                embedding.turnPhase).det) := by ring
        _ = _ := by rw [hind]





def ons_boundedReciprocalRectWalkResum (M N : Nat)
    (weight : Sym2 (ons_RectDualVertex M N) → Complex) (q : Complex) :
    List (Sym2 (ons_RectDualVertex M N)) → Complex
  | [] => Complex.exp (-(ons_rectDualWalkExponent M N weight))
  | edge :: edges =>
      ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s *
        ons_boundedReciprocalRectWalkResum M N
          (ons_setGraphEdgeWeight weight edge
            (ons_reciprocalInterpolationValue q s)) q edges

theorem norm_reciprocalInterpolationValue_le
    (q : Real) (hq : 0 ≤ q) (s : Fin 3) :
    ‖ons_reciprocalInterpolationValue (q : Complex) s‖ ≤ q := by
  fin_cases s
  · simp [ons_reciprocalInterpolationValue, hq]
  · simp [ons_reciprocalInterpolationValue, Real.norm_eq_abs,
      abs_of_nonneg hq]
  · simpa [ons_reciprocalInterpolationValue, Real.norm_eq_abs,
      abs_of_nonneg hq] using le_rfl

theorem norm_ons_setGraphEdgeWeight_le
    (weight : Sym2 V → Complex) (edge : Sym2 V) (z : Complex)
    (q : Real) (hweight : ∀ f, ‖weight f‖ ≤ q) (hz : ‖z‖ ≤ q) :
    ∀ f, ‖ons_setGraphEdgeWeight weight edge z f‖ ≤ q := by
  intro f
  by_cases hfe : f = edge
  · subst f
    simpa using hz
  · simpa [ons_setGraphEdgeWeight, hfe] using hweight f




theorem boundedReciprocalRectKWDetResum_eq_walkResum
    (M N : Nat)
    (weight : Sym2 (ons_RectDualVertex M N) → Complex)
    (q : Real) (hq0 : 0 ≤ q) (hq : q < ons_signedLoopCriticalWeight)
    (hweight : ∀ edge, ‖weight edge‖ ≤ q)
    (edges : List (Sym2 (ons_RectDualVertex M N))) :
    ons_boundedReciprocalKWDetResum (ons_rectDualGraph M N)
        (ons_rectDualStraightLineEmbedding M N) weight (q : Complex) edges =
      ons_boundedReciprocalRectWalkResum M N weight (q : Complex) edges := by
  induction edges generalizing weight with
  | nil =>
      simp only [ons_boundedReciprocalKWDetResum,
        ons_boundedReciprocalRectWalkResum]
      exact kwGraphTransition_canonical_det_eq_walk_exp
        M N weight q hq0 hq hweight
  | cons edge edges ih =>
      simp only [ons_boundedReciprocalKWDetResum,
        ons_boundedReciprocalRectWalkResum]
      apply Finset.sum_congr rfl
      intro s hs
      congr 1
      exact ih
        (ons_setGraphEdgeWeight weight edge
          (ons_reciprocalInterpolationValue (q : Complex) s))
        (norm_ons_setGraphEdgeWeight_le _ edge _ q hweight
          (norm_reciprocalInterpolationValue_le q hq0 s))

theorem setGraphEdgeWeightList_uniform_eq_pathDefectWeight
    {M N : Nat} (path : ons_RectDualPath M N) (q : Real) :
    ons_setGraphEdgeWeightList (fun _ ↦ (q : Complex)) (q : Complex)⁻¹
        (ons_rectDualPathDefect path).toList =
      ons_rectDualPathDefectWeight path q := by
  funext edge
  rw [ons_setGraphEdgeWeightList_apply]
  simp [ons_rectDualPathDefectWeight]





theorem rectDualPath_sourceDet_eq_bounded_walkResum
    {M N : Nat} (path : ons_RectDualPath M N)
    (q : Real) (hq0 : 0 < q) (hq : q < ons_signedLoopCriticalWeight) :
    (q : Complex) ^ (2 * (ons_rectDualPathDefect path).card) *
        ons_rectDualPathCanonicalDefectKWDet path q =
      ons_boundedReciprocalRectWalkResum M N
        (fun _ ↦ (q : Complex)) (q : Complex)
        (ons_rectDualPathDefect path).toList := by
  have hqne : (q : Complex) ≠ 0 := by exact_mod_cast hq0.ne'
  have hinterp := reciprocalKWDet_list_eq_bounded_resum
    (ons_rectDualGraph M N) (ons_rectDualStraightLineEmbedding M N)
    (fun _ ↦ (q : Complex)) (q : Complex) hqne
    (ons_rectDualPathDefect path).toList
    (Finset.nodup_toList (ons_rectDualPathDefect path))
  rw [Finset.length_toList,
    setGraphEdgeWeightList_uniform_eq_pathDefectWeight path q] at hinterp
  have hwalk := boundedReciprocalRectKWDetResum_eq_walkResum
    M N (fun _ ↦ (q : Complex)) q hq0.le hq
    (fun _ ↦ by
      simp [Real.norm_eq_abs, abs_of_pos hq0])
    (ons_rectDualPathDefect path).toList
  rw [← hwalk]
  simpa [ons_rectDualPathCanonicalDefectKWDet,
    ons_rectDualPathDefectKWDet] using hinterp





theorem coe_rectDualPath_finiteTwoPoint_sq_eq_bounded_walkResum
    {M N : Nat} (path : ons_RectDualPath M N)
    (beta : Real) (hbeta0 : 0 < beta) (hbetaC : beta < ons_betaC) :
    (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) beta 0
        (fun spin ↦ StatMech.Ising.spin spin path.source *
          StatMech.Ising.spin spin path.target) : Complex) ^ 2 =
      ons_boundedReciprocalRectWalkResum M N
          (fun _ ↦ (Real.tanh beta : Complex))
          (Real.tanh beta : Complex)
          (ons_rectDualPathDefect path).toList /
        Complex.exp (-(ons_rectDualWalkExponent M N
          (fun _ ↦ (Real.tanh beta : Complex)))) := by
  let q := Real.tanh beta
  have hq0 : 0 < q := by
    dsimp only [q]
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hbeta0) (Real.cosh_pos beta)
  have hqcrit : q < ons_signedLoopCriticalWeight :=
    tanh_lt_signedLoopCriticalWeight hbetaC
  have hsource := rectDualPath_sourceDet_eq_bounded_walkResum
    path q hq0 hqcrit
  have hplain := kwGraphTransition_canonical_det_eq_walk_exp
    M N (fun _ ↦ (q : Complex)) q hq0.le hqcrit
    (fun _ ↦ by simp [Real.norm_eq_abs, abs_of_pos hq0])
  rw [coe_ons_rectDualPath_finiteTwoPoint_sq_eq_canonicalKWDet_ratio
    path hbeta0]
  change ((q : Complex) ^ (2 * (ons_rectDualPathDefect path).card) *
      ons_rectDualPathCanonicalDefectKWDet path q) /
        ons_rectDualCanonicalKWDet M N q = _
  rw [hsource]
  change _ / (1 - kwGraphTransition (ons_rectDualGraph M N)
    (fun _ ↦ (q : Complex))
    (ons_rectDualStraightLineEmbedding M N).turnPhase).det = _
  rw [hplain]
  rfl


def ons_rectDualPathHighTempWalkRatio {M N : Nat}
    (path : ons_RectDualPath M N) (beta : Real) : Complex :=
  ons_boundedReciprocalRectWalkResum M N
      (fun _ ↦ (Real.tanh beta : Complex))
      (Real.tanh beta : Complex) (ons_rectDualPathDefect path).toList /
    Complex.exp (-(ons_rectDualWalkExponent M N
      (fun _ ↦ (Real.tanh beta : Complex))))

theorem rectDualPathHighTempWalkRatio_eq_finiteTwoPoint_sq
    {M N : Nat} (path : ons_RectDualPath M N)
    (beta : Real) (hbeta0 : 0 < beta) (hbetaC : beta < ons_betaC) :
    ons_rectDualPathHighTempWalkRatio path beta =
      (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) beta 0
        (fun spin ↦ StatMech.Ising.spin spin path.source *
          StatMech.Ising.spin spin path.target) : Complex) ^ 2 := by
  rw [ons_rectDualPathHighTempWalkRatio]
  have hfinite := coe_rectDualPath_finiteTwoPoint_sq_eq_bounded_walkResum
    path beta hbeta0 hbetaC
  exact hfinite.symm




theorem canonicalHighTempWalkRatio_shifted_tendsto_freeState
    (beta : Real) (hbeta0 : 0 < beta) (hbetaC : beta < ons_betaC)
    (path : ∀ n, ons_RectDualPath (2 * (n + 1)) (2 * (n + 1)))
    (a b : Site 2)
    (hsource : ∀ᶠ n in Filter.atTop,
      ((ons_box2EquivRect (n + 1)).symm (path n).source).1 = a)
    (htarget : ∀ᶠ n in Filter.atTop,
      ((ons_box2EquivRect (n + 1)).symm (path n).target).1 = b) :
    Filter.Tendsto
      (fun n ↦ ons_rectDualPathHighTempWalkRatio (path n) beta)
      Filter.atTop
      (nhds ((((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 beta 0 : MeasureTheory.Measure
          (ConfigSpace (Site 2)))) : Real) : Complex) ^ 2)) := by
  apply (ons_canonicalRectDualPathRatio_shifted_tendsto_freeState
    beta hbeta0 path a b hsource htarget).congr'
  filter_upwards with n
  calc
    ons_rectDualPathRatio
        (ons_rectDualStraightLineEmbedding
          (2 * (n + 1)) (2 * (n + 1))) (path n) beta =
        (StatMech.Ising.isingExpectation
          (ons_rectDualGraph (2 * (n + 1)) (2 * (n + 1))) beta 0
          (fun spin ↦ StatMech.Ising.spin spin (path n).source *
            StatMech.Ising.spin spin (path n).target) : Complex) ^ 2 := by
      symm
      exact coe_ons_rectDualPath_finiteTwoPoint_sq_eq_canonicalKWDet_ratio
        (path n) hbeta0
    _ = ons_rectDualPathHighTempWalkRatio (path n) beta := by
      symm
      exact rectDualPathHighTempWalkRatio_eq_finiteTwoPoint_sq
        (path n) beta hbeta0 hbetaC



theorem fixedPairHighTempWalkRatio_tendsto_freeState
    (beta : Real) (hbeta0 : 0 < beta) (hbetaC : beta < ons_betaC)
    (N : Nat) (a b : Site 2)
    (ha : a ∈ StatMech.Lattice.box 2 N)
    (hb : b ∈ StatMech.Lattice.box 2 N) (hab : a ≠ b) :
    Tendsto
      (fun n ↦ ons_rectDualPathHighTempWalkRatio
        (ons_fixedPairRectDualPath N a b ha hb hab n) beta)
      atTop
      (nhds ((((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) ^ 2)) := by
  exact canonicalHighTempWalkRatio_shifted_tendsto_freeState
    beta hbeta0 hbetaC
    (ons_fixedPairRectDualPath N a b ha hb hab) a b
    (ons_fixedPairRectDualPath_source_eventually N a b ha hb hab)
    (ons_fixedPairRectDualPath_target_eventually N a b ha hb hab)

end

end StatMech.Onsager
