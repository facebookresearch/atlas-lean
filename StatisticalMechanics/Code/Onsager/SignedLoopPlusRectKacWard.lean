/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopPlusRectCutCycle
import Code.Onsager.SignedLoopPlusWiredCutLimit
import Code.Onsager.SignedLoopRectangularSpectralBridge





open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology

namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section



def ons_plusRectContourSum (n : Nat) (q : Real) : Real :=
  ∑ F : ons_PlusRectEvenSubgraph n, q ^ F.1.card



def ons_plusRectPathSum (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) (q : Real) : Real :=
  ∑ F : ons_PlusRectEvenSubgraph n,
    ons_plusRectPathDefectSign n path F * q ^ F.1.card

theorem card_ons_plusRectCutEven (n : Nat)
    (config : AnchoredConfig (ons_PlusWiredVertex 2 n) none) :
    (ons_plusRectCutEven n config).1.card =
      (multibondCut (ons_plusWiredBondEnds 2 n) config.1).card := by
  unfold ons_plusRectCutEven ons_plusRectDualCut
  rw [Finset.card_map]



theorem ons_plusWiredContourDenominator_eq_plusRectContourSum
    (n : Nat) (beta : Real) :
    ons_plusWiredContourDenominator 2 n beta =
      ons_plusRectContourSum n (Real.exp (-2 * beta)) := by
  unfold ons_plusWiredContourDenominator ons_plusRectContourSum
  rw [← (ons_plusRectCutEvenEquiv n).sum_comp]
  apply Finset.sum_congr rfl
  intro config _
  change Real.exp (-2 * beta) ^
      (multibondCut (ons_plusWiredBondEnds 2 n) config.1).card =
    Real.exp (-2 * beta) ^ (ons_plusRectCutEven n config).1.card
  rw [card_ons_plusRectCutEven]



theorem ons_plusWiredPathNumerator_eq_plusRectPathSum
    (n : Nat) (beta : Real) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) :
    ons_plusWiredPathNumerator 2 n beta u v =
      ons_plusRectPathSum n path (Real.exp (-2 * beta)) := by
  unfold ons_plusWiredPathNumerator ons_plusRectPathSum
  rw [← (ons_plusRectCutEvenEquiv n).sum_comp]
  apply Finset.sum_congr rfl
  intro config _
  change ons_plusWiredEndpointSign 2 n config.1 u v *
      Real.exp (-2 * beta) ^
        (multibondCut (ons_plusWiredBondEnds 2 n) config.1).card =
    ons_plusRectPathDefectSign n path (ons_plusRectCutEven n config) *
      Real.exp (-2 * beta) ^ (ons_plusRectCutEven n config).1.card
  rw [card_ons_plusRectCutEven]
  have hsign := ons_plusRectPathDefectSign_eq_endpointSign n
    (ons_plusRectCutEvenEquiv n config) path
  simpa using congrArg
    (fun sign : Real ↦ sign * Real.exp (-2 * beta) ^
      (multibondCut (ons_plusWiredBondEnds 2 n) config.1).card) hsign.symm





def ons_plusRectPathWeight (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) (q : Real)
    (edge : Sym2 (ons_RectDualVertex (2 * n + 1) (2 * n + 1))) : Complex :=
  (ons_plusRectPathEdgeSign n path edge : Complex) * (q : Complex)



theorem ofReal_ons_plusRectContourSum_eq_kwEvenPolynomial
    (n : Nat) (q : Real) :
    (ons_plusRectContourSum n q : Complex) =
      kwEvenPolynomial (ons_rectDualGraph (2 * n + 1) (2 * n + 1))
        (fun _ => (q : Complex)) := by
  rw [kwEvenPolynomial_eq_sum_actual]
  unfold ons_plusRectContourSum
  push_cast
  apply Finset.sum_congr rfl
  intro F _
  simp [Finset.prod_const]



theorem ofReal_ons_plusRectPathSum_eq_kwEvenPolynomial
    (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) (q : Real) :
    (ons_plusRectPathSum n path q : Complex) =
      kwEvenPolynomial (ons_rectDualGraph (2 * n + 1) (2 * n + 1))
        (ons_plusRectPathWeight n path q) := by
  rw [kwEvenPolynomial_eq_sum_actual]
  unfold ons_plusRectPathSum
  push_cast
  apply Finset.sum_congr rfl
  intro F _
  unfold ons_plusRectPathDefectSign ons_plusRectPathWeight
  rw [Finset.prod_mul_distrib]
  push_cast
  simp [Finset.prod_const]





def ons_plusRectKWDet (n : Nat) (q : Real) : Complex :=
  (1 - kwGraphTransition
    (ons_rectDualGraph (2 * n + 1) (2 * n + 1))
    (fun _ => (q : Complex))
    (ons_rectDualStraightLineEmbedding
      (2 * n + 1) (2 * n + 1)).turnPhase).det



def ons_plusRectPathKWDet (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) (q : Real) : Complex :=
  (1 - kwGraphTransition
    (ons_rectDualGraph (2 * n + 1) (2 * n + 1))
    (ons_plusRectPathWeight n path q)
    (ons_rectDualStraightLineEmbedding
      (2 * n + 1) (2 * n + 1)).turnPhase).det



theorem coe_ons_plusRectContourSum_sq_eq_kwDet
    (n : Nat) (q : Real) :
    (ons_plusRectContourSum n q : Complex) ^ 2 =
      ons_plusRectKWDet n q := by
  rw [ofReal_ons_plusRectContourSum_eq_kwEvenPolynomial]
  exact (kacWard_straightLine_arbitrary_adaptive
    (ons_rectDualGraph (2 * n + 1) (2 * n + 1))
    (ons_rectDualStraightLineEmbedding (2 * n + 1) (2 * n + 1))
    (fun _ => (q : Complex))).symm



theorem coe_ons_plusRectPathSum_sq_eq_kwDet
    (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) (q : Real) :
    (ons_plusRectPathSum n path q : Complex) ^ 2 =
      ons_plusRectPathKWDet n path q := by
  rw [ofReal_ons_plusRectPathSum_eq_kwEvenPolynomial]
  exact (kacWard_straightLine_arbitrary_adaptive
    (ons_rectDualGraph (2 * n + 1) (2 * n + 1))
    (ons_rectDualStraightLineEmbedding (2 * n + 1) (2 * n + 1))
    (ons_plusRectPathWeight n path q)).symm

theorem ons_plusRectContourSum_pos (n : Nat) (q : Real) (hq : 0 < q) :
    0 < ons_plusRectContourSum n q := by
  unfold ons_plusRectContourSum
  apply Finset.sum_pos'
  · intro F _
    positivity
  · refine ⟨⟨∅, ?_⟩, Finset.mem_univ _, by simp⟩
    simp [evenSubgraphs, IsEvenSubgraph, incCount]




theorem coe_integral_plusMeasure_twoPoint_sq_eq_plusRectKWDet_ratio
    (n : Nat) (beta : Real) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) :
    ((∫ config, spin config u * spin config v
        ∂(plusMeasure 2 n beta 0 : Measure (ConfigSpace (Site 2)))) :
        Complex) ^ 2 =
      ons_plusRectPathKWDet n path (Real.exp (-2 * beta)) /
        ons_plusRectKWDet n (Real.exp (-2 * beta)) := by
  have hratio := integral_plusMeasure_twoPoint_eq_wiredCutRatio
    2 n beta path
  rw [ons_plusWiredPathNumerator_eq_plusRectPathSum n beta path,
    ons_plusWiredContourDenominator_eq_plusRectContourSum n beta] at hratio
  have hratioComplex :
      ((∫ config, spin config u * spin config v
          ∂(plusMeasure 2 n beta 0 : Measure (ConfigSpace (Site 2)))) :
          Complex) =
        (ons_plusRectPathSum n path (Real.exp (-2 * beta)) : Complex) /
          (ons_plusRectContourSum n (Real.exp (-2 * beta)) : Complex) := by
    exact_mod_cast hratio
  rw [hratioComplex, div_pow,
    coe_ons_plusRectPathSum_sq_eq_kwDet,
    coe_ons_plusRectContourSum_sq_eq_kwDet]

theorem norm_ons_plusRectPathWeight (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v)
    {q : Real} (hq : 0 ≤ q)
    (edge : Sym2 (ons_RectDualVertex (2 * n + 1) (2 * n + 1))) :
    ‖ons_plusRectPathWeight n path q edge‖ = q := by
  unfold ons_plusRectPathWeight ons_plusRectPathEdgeSign
  split_ifs
  · rw [norm_mul]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
  · simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]




theorem ons_plusRectPathKWDet_ratio_eq_walk_exp
    (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v)
    (q : Real) (hq0 : 0 ≤ q) (hq : q < ons_signedLoopCriticalWeight) :
    ons_plusRectPathKWDet n path q / ons_plusRectKWDet n q =
      Complex.exp (-(ons_rectDualWalkExponent (2 * n + 1) (2 * n + 1)
          (ons_plusRectPathWeight n path q) -
        ons_rectDualWalkExponent (2 * n + 1) (2 * n + 1)
          (fun _ ↦ (q : Complex)))) := by
  have hpath := kwGraphTransition_canonical_det_eq_walk_exp
    (2 * n + 1) (2 * n + 1) (ons_plusRectPathWeight n path q)
    q hq0 hq (fun edge ↦ (norm_ons_plusRectPathWeight n path hq0 edge).le)
  have hplain := kwGraphTransition_canonical_det_eq_walk_exp
    (2 * n + 1) (2 * n + 1) (fun _ ↦ (q : Complex))
    q hq0 hq (fun _ ↦ by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0])
  unfold ons_plusRectPathKWDet ons_plusRectKWDet
  rw [hpath, hplain, ← Complex.exp_sub]
  congr 1
  unfold ons_rectDualWalkExponent
  ring



theorem coe_integral_plusMeasure_twoPoint_sq_eq_walk_exp
    (n : Nat) {beta : Real} (hbeta : ons_betaC < beta)
    {u v : Site 2} (path : (hypercubicLattice 2).Walk u v) :
    ((∫ config, spin config u * spin config v
        ∂(plusMeasure 2 n beta 0 : Measure (ConfigSpace (Site 2)))) :
        Complex) ^ 2 =
      Complex.exp (-(ons_rectDualWalkExponent (2 * n + 1) (2 * n + 1)
          (ons_plusRectPathWeight n path (Real.exp (-2 * beta))) -
        ons_rectDualWalkExponent (2 * n + 1) (2 * n + 1)
          (fun _ ↦ (Real.exp (-2 * beta) : Complex)))) := by
  rw [coe_integral_plusMeasure_twoPoint_sq_eq_plusRectKWDet_ratio n beta path]
  exact ons_plusRectPathKWDet_ratio_eq_walk_exp n path
    (Real.exp (-2 * beta)) (Real.exp_pos _).le
    (exp_neg_two_lt_signedLoopCriticalWeight hbeta)



theorem ons_plusRectWalkExp_tendsto_plusState_sq
    {beta : Real} (hbeta : ons_betaC < beta)
    {u v : Site 2} (huv : u ≠ v)
    (path : (hypercubicLattice 2).Walk u v) :
    Tendsto
      (fun n ↦ Complex.exp
        (-(ons_rectDualWalkExponent (2 * n + 1) (2 * n + 1)
            (ons_plusRectPathWeight n path (Real.exp (-2 * beta))) -
          ons_rectDualWalkExponent (2 * n + 1) (2 * n + 1)
            (fun _ ↦ (Real.exp (-2 * beta) : Complex)))))
      atTop
      (nhds ((((∫ config, spin config u * spin config v
        ∂(plusState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) ^ 2)) := by
  have hratio := plusWiredCutRatio_tendsto_plusState
    2 beta (ons_betaC_pos.le.trans hbeta.le) huv path
  have hcomplex : Tendsto
      (fun n ↦ ((ons_plusWiredPathNumerator 2 n beta u v /
        ons_plusWiredContourDenominator 2 n beta : Real) : Complex))
      atTop
      (nhds (((∫ config, spin config u * spin config v
        ∂(plusState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex)) := by
    simpa only [Function.comp_apply] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hratio
  apply (hcomplex.pow 2).congr'
  filter_upwards [] with n
  rw [← coe_integral_plusMeasure_twoPoint_sq_eq_walk_exp n hbeta path]
  have hintegral :
      (∫ config, ((spin config u : Real) : Complex) *
          ((spin config v : Real) : Complex)
        ∂(plusMeasure 2 n beta 0 : Measure (ConfigSpace (Site 2)))) =
        (((∫ config, spin config u * spin config v
          ∂(plusMeasure 2 n beta 0 : Measure (ConfigSpace (Site 2)))) :
            Real) : Complex) := by
    calc
      _ = ∫ config, ((spin config u * spin config v : Real) : Complex)
          ∂(plusMeasure 2 n beta 0 : Measure (ConfigSpace (Site 2))) := by
        congr 1
        funext config
        push_cast
        rfl
      _ = _ := integral_ofReal
  rw [hintegral,
    integral_plusMeasure_twoPoint_eq_wiredCutRatio 2 n beta path]

end

end StatMech.Onsager
