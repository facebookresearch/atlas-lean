/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheLocalAnalytic
import Code.FrontierD.SixVertexBetheJacobianSign
import Mathlib.LinearAlgebra.Matrix.Gershgorin











open Finset Filter Topology Matrix

namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheJacobianMatrix (N n : Nat) (c : Real)
    (p : Fin n → Real) : Matrix (Fin n) (Fin n) Real := fun j k =>
  if j = k then
    (N : Real) + ∑ l ∈ Finset.univ.erase j,
      4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p l) /
        sixVertexThetaDerivativeDenominator c (p j) (p l)
  else
    -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p j) /
      sixVertexThetaDerivativeDenominator c (p j) (p k)

theorem sixVertexBetheRootJacobian_toMatrix'_apply
    {N n : Nat} {c : Real} (hc : 2 < c)
    (p : Fin n → Real) (j k : Fin n) :
    LinearMap.toMatrix' (sixVertexBetheRootJacobian N n c p).toLinearMap j k =
      sixVertexBetheJacobianMatrix N n c p j k := by
  let R : (Fin n → Real) → (Fin n → Real) := fun q j =>
    sixVertexBetheResidual c N n q j
  have hR : HasFDerivAt R (sixVertexBetheRootJacobian N n c p) p := by
    exact (analyticAt_sixVertexBetheResidual_family N n (c, p) hc).comp
      (x := p) (f := fun q : Fin n → Real => (c, q))
      (analyticAt_const.prod analyticAt_id) |>.hasStrictFDerivAt.hasFDerivAt
  have hj : HasFDerivAt (fun q : Fin n → Real =>
      sixVertexBetheResidual c N n q j)
      ((ContinuousLinearMap.proj j).comp
        (sixVertexBetheRootJacobian N n c p)) p := by
    simpa [R] using (ContinuousLinearMap.proj j).hasFDerivAt.comp p hR
  have hdirect : HasFDerivAt (fun q : Fin n → Real =>
      sixVertexBetheResidual c N n q j)
      ((N : Real) • ContinuousLinearMap.proj j +
        ∑ l, (sixVertexThetaFDeriv c (p j) (p l)).comp
          ((ContinuousLinearMap.proj j).prod
            (ContinuousLinearMap.proj l))) p := by
    unfold sixVertexBetheResidual
    apply HasFDerivAt.sub_const
    apply HasFDerivAt.add
    · simpa using (hasFDerivAt_apply (𝕜 := Real) j p).const_mul (N : Real)
    · apply HasFDerivAt.fun_sum
      intro l _
      exact (hasFDerivAt_sixVertexTheta hc (p j) (p l)).comp p
        ((hasFDerivAt_apply (𝕜 := Real) j p).prodMk
          (hasFDerivAt_apply (𝕜 := Real) l p))
  have heq := hj.unique hdirect
  rw [LinearMap.toMatrix'_apply]
  change sixVertexBetheRootJacobian N n c p (Pi.single k 1) j = _
  have happly := congrArg
    (fun L : (Fin n → Real) →L[Real] Real => L (Pi.single k 1)) heq
  change sixVertexBetheRootJacobian N n c p (Pi.single k 1) j = _ at happly
  rw [happly]
  let P : Fin n → ((Fin n → Real) →L[Real] Real) :=
    fun i => ContinuousLinearMap.proj i
  change (((N : Real) • P j +
      ∑ l, (sixVertexThetaFDeriv c (p j) (p l)).comp
        ((P j).prod (P l))) (Pi.single k 1)) = _
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  rw [show (∑ l, (sixVertexThetaFDeriv c (p j) (p l)).comp
        ((P j).prod (P l))) (Pi.single k 1) =
      ∑ l, ((sixVertexThetaFDeriv c (p j) (p l)).comp
        ((P j).prod (P l))) (Pi.single k 1) by
    change (ContinuousLinearMap.apply Real Real (Pi.single k 1))
      (∑ l, (sixVertexThetaFDeriv c (p j) (p l)).comp
        ((P j).prod (P l))) = _
    rw [map_sum]
    rfl]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Finset.sum_apply,
    sixVertexThetaFDeriv, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  classical
  by_cases hjk : j = k
  · subst k
    rw [sixVertexBetheJacobianMatrix, if_pos rfl]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    simp_rw [P, ContinuousLinearMap.proj_apply, Pi.single_apply]
    rw [Finset.sum_add_distrib]
    have hzero : (∑ x ∈ Finset.univ.erase j,
        (if x = j then 1 else 0) *
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p j) /
            sixVertexThetaDerivativeDenominator c (p j) (p x))) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hxne := (Finset.mem_erase.mp hx).1
      simp [hxne]
    rw [hzero]
    simp
    ring
  · rw [sixVertexBetheJacobianMatrix, if_neg hjk]
    rw [Finset.sum_eq_single k]
    · simp [P, Pi.single_apply, hjk]
    · intro l _ hlk
      simp [P, Pi.single_apply, hlk, hjk]
    · exact fun hk => (hk (Finset.mem_univ k)).elim

def sixVertexAnisotropyMagnitude (c : Real) : Real :=
  -sixVertexDelta c

theorem one_lt_sixVertexAnisotropyMagnitude {c : Real} (hc : 2 < c) :
    1 < sixVertexAnisotropyMagnitude c := by
  simpa [sixVertexAnisotropyMagnitude] using
    neg_lt_neg (sixVertexDelta_lt_neg_one hc)

theorem sixVertexThetaDerivativeDenominator_eq (c x y : Real) :
    sixVertexThetaDerivativeDenominator c x y =
      4 * sixVertexBetheIntegratingFactor c x *
          sixVertexBetheIntegratingFactor c y +
        2 * (1 - Real.cos (x - y)) := by
  unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
    sixVertexBetheIntegratingFactor
  rw [Real.cos_sub]
  have hx := Real.sin_sq_add_cos_sq x
  have hy := Real.sin_sq_add_cos_sq y
  ring_nf at hx hy ⊢
  nlinarith

theorem norm_sixVertexTheta_rightDerivative_le
    {c : Real} (hc : 2 < c) (x y : Real) :
    ‖-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
        sixVertexThetaDerivativeDenominator c x y‖ ≤
      sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1) := by
  let d := sixVertexAnisotropyMagnitude c
  let Fx := sixVertexBetheIntegratingFactor c x
  let Fy := sixVertexBetheIntegratingFactor c y
  let D := sixVertexThetaDerivativeDenominator c x y
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hFx : 0 < Fx := sixVertexBetheIntegratingFactor_pos hc x
  have hFy : 0 < Fy := sixVertexBetheIntegratingFactor_pos hc y
  have hD : 0 < D := sixVertexThetaDerivativeDenominator_pos hc x y
  have hFyLower : d - 1 ≤ Fy := by
    dsimp [d, Fy, sixVertexAnisotropyMagnitude,
      sixVertexBetheIntegratingFactor]
    linarith [Real.neg_one_le_cos y]
  have hDLower : 4 * Fx * Fy ≤ D := by
    dsimp [D, Fx, Fy]
    rw [sixVertexThetaDerivativeDenominator_eq]
    have hcos := Real.cos_le_one (x - y)
    nlinarith
  have hnum : 0 ≤ -4 * sixVertexDelta c * Fx := by
    have hcoef : 0 ≤ -4 * sixVertexDelta c := by
      have := sixVertexDelta_lt_neg_one hc
      nlinarith
    exact mul_nonneg hcoef hFx.le
  change ‖(-4 * sixVertexDelta c * Fx / D : Real)‖ ≤ d / (d - 1)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum hD.le)]
  change (-4 * sixVertexDelta c * Fx) / D ≤ d / (d - 1)
  rw [div_le_div_iff₀ hD (sub_pos.mpr hd)]
  change (-4 * sixVertexDelta c * Fx) * (d - 1) ≤ d * D
  have hprod : Fx * (d - 1) ≤ Fx * Fy :=
    mul_le_mul_of_nonneg_left hFyLower hFx.le
  have hd0 : 0 ≤ d := le_trans (by norm_num) hd.le
  have hscaled := mul_le_mul_of_nonneg_left hDLower hd0
  dsimp [d, sixVertexAnisotropyMagnitude] at hprod hscaled ⊢
  nlinarith

theorem norm_sixVertexTheta_leftDerivative_le
    {c : Real} (hc : 2 < c) (x y : Real) :
    ‖4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
        sixVertexThetaDerivativeDenominator c x y‖ ≤
      sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1) := by
  have h := norm_sixVertexTheta_rightDerivative_le hc y x
  rw [sixVertexThetaDerivativeDenominator_swap] at h
  calc
    ‖4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
        sixVertexThetaDerivativeDenominator c x y‖ =
      ‖-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
        sixVertexThetaDerivativeDenominator c x y‖ := by
        rw [← norm_neg]
        congr 1
        ring
    _ ≤ _ := h

theorem sixVertexBetheRootJacobian_injective_of_diagonalDominance
    {N n : Nat} {c : Real} (hc : 2 < c) (p : Fin n → Real)
    (hdom : 2 * ((n : Real) - 1) *
        (sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1)) < (N : Real)) :
    Function.Injective (sixVertexBetheRootJacobian N n c p) := by
  by_cases hn0 : n = 0
  · subst n
    exact fun x y _ => Subsingleton.elim x y
  let A := sixVertexBetheJacobianMatrix N n c p
  let R := sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)
  have hR : 0 < R := div_pos
    (by linarith [one_lt_sixVertexAnisotropyMagnitude hc])
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hcard (j : Fin n) :
      ((Finset.univ.erase j).card : Real) = (n : Real) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
    simp [Nat.cast_sub hn]
  have hoff (j k : Fin n) (hjk : j ≠ k) : ‖A j k‖ ≤ R := by
    simpa [A, sixVertexBetheJacobianMatrix, hjk] using
      norm_sixVertexTheta_rightDerivative_le hc (p j) (p k)
  have hleft (j k : Fin n) :
      ‖4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p k) /
          sixVertexThetaDerivativeDenominator c (p j) (p k)‖ ≤ R :=
    norm_sixVertexTheta_leftDerivative_le hc (p j) (p k)
  have hdiag (j : Fin n) :
      ∑ k ∈ Finset.univ.erase j, ‖A j k‖ < ‖A j j‖ := by
    have hoffsum :
        ∑ k ∈ Finset.univ.erase j, ‖A j k‖ ≤
          ((n : Real) - 1) * R := by
      calc
        _ ≤ ∑ _k ∈ Finset.univ.erase j, R := by
          apply Finset.sum_le_sum
          intro k hk
          exact hoff j k (Ne.symm (Finset.mem_erase.mp hk).1)
        _ = ((n : Real) - 1) * R := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
    have hAsumAbs :
        ∑ k ∈ Finset.univ.erase j,
            ‖4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p k) /
              sixVertexThetaDerivativeDenominator c (p j) (p k)‖ ≤
          ((n : Real) - 1) * R := by
      calc
        _ ≤ ∑ _k ∈ Finset.univ.erase j, R := by
          apply Finset.sum_le_sum
          intro k _
          exact hleft j k
        _ = ((n : Real) - 1) * R := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
    have hsumLower :
        -((n : Real) - 1) * R ≤
          ∑ k ∈ Finset.univ.erase j,
            4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p k) /
              sixVertexThetaDerivativeDenominator c (p j) (p k) := by
      calc
        -((n : Real) - 1) * R ≤
            -(∑ k ∈ Finset.univ.erase j,
              ‖4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p k) /
                sixVertexThetaDerivativeDenominator c (p j) (p k)‖) := by
          linarith
        _ ≤ _ := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_le_sum
          intro k _
          exact neg_abs_le _
    have hdiagPos : 0 < A j j := by
      have hAjj : A j j = (N : Real) +
          ∑ l ∈ Finset.univ.erase j,
            4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p l) /
              sixVertexThetaDerivativeDenominator c (p j) (p l) := by
        simp [A, sixVertexBetheJacobianMatrix]
      rw [hAjj]
      have := hdom
      nlinarith
    rw [Real.norm_eq_abs, abs_of_pos hdiagPos]
    have hdiagLower : ((n : Real) - 1) * R < A j j := by
      have hAjj : A j j = (N : Real) +
          ∑ l ∈ Finset.univ.erase j,
            4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p l) /
              sixVertexThetaDerivativeDenominator c (p j) (p l) := by
        simp [A, sixVertexBetheJacobianMatrix]
      rw [hAjj]
      nlinarith [hdom]
    exact hoffsum.trans_lt hdiagLower
  have hdetA : Matrix.det A ≠ 0 :=
    det_ne_zero_of_sum_row_lt_diag hdiag
  have hmatrix : LinearMap.toMatrix'
      (sixVertexBetheRootJacobian N n c p).toLinearMap = A := by
    ext j k
    exact sixVertexBetheRootJacobian_toMatrix'_apply hc p j k
  have hdetJ : LinearMap.det
      (sixVertexBetheRootJacobian N n c p).toLinearMap ≠ 0 := by
    rw [← LinearMap.det_toMatrix', hmatrix]
    exact hdetA
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  exact hdetJ ((LinearMap.det_eq_zero_iff_ker_ne_bot).2 hker)

theorem sixVertexBetheRootJacobian_injective_of_anisotropyMagnitude
    {N n : Nat} {c : Real} (hc : 2 < c) (hhalf : 2 * n ≤ N)
    (htail : (n : Real) < sixVertexAnisotropyMagnitude c)
    (p : Fin n → Real) :
    Function.Injective (sixVertexBetheRootJacobian N n c p) := by
  apply sixVertexBetheRootJacobian_injective_of_diagonalDominance hc p
  let d := sixVertexAnisotropyMagnitude c
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hN : (2 * n : Real) ≤ (N : Real) := by exact_mod_cast hhalf
  have hstrict :
      2 * ((n : Real) - 1) * (d / (d - 1)) < 2 * (n : Real) := by
    rw [show 2 * ((n : Real) - 1) * (d / (d - 1)) =
      (2 * ((n : Real) - 1) * d) / (d - 1) by ring]
    rw [div_lt_iff₀ (sub_pos.mpr hd)]
    dsimp [d] at htail ⊢
    nlinarith
  exact hstrict.trans_le (by norm_num at hN ⊢; exact hN)

theorem sixVertexAnisotropyMagnitude_mono
    {a c : Real} (ha : 0 ≤ a) (hac : a ≤ c) :
    sixVertexAnisotropyMagnitude a ≤ sixVertexAnisotropyMagnitude c := by
  have hc : 0 ≤ c := ha.trans hac
  have hsquare : a ^ 2 ≤ c ^ 2 := by nlinarith
  unfold sixVertexAnisotropyMagnitude sixVertexDelta
  nlinarith




theorem exists_sixVertexContinuousBetheBranch_of_anisotropyMagnitude
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N)
    (htail : (n : Real) < sixVertexAnisotropyMagnitude a)
    (z₀ : SixVertexBetheContinuationSpace a b N n)
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin n → Real),
      roots c₀ = z₀.1.2 ∧
      ∀ t ∈ Set.Icc a b,
        SixVertexSatisfiesBetheEquations t N n (roots t) := by
  apply exists_sixVertexContinuousBetheBranch_of_rootJacobian
    ha hab hc₀ hN hhalf _ z₀ hz₀
  intro q hq
  apply sixVertexBetheRootJacobian_injective_of_anisotropyMagnitude
    (ha.trans_le hq.1.1) hhalf
  exact htail.trans_le
    (sixVertexAnisotropyMagnitude_mono (by linarith) hq.1.1)



theorem exists_sixVertexAnalyticBetheBranch_of_anisotropyMagnitude
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N)
    (htail : (n : Real) < sixVertexAnisotropyMagnitude a)
    (z₀ : SixVertexBetheContinuationSpace a b N n)
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin n → Real),
      roots c₀ = z₀.1.2 ∧
      (∀ t ∈ Set.Icc a b,
        SixVertexSatisfiesBetheEquations t N n (roots t)) ∧
      ∀ t ∈ Set.Ioo a b, AnalyticAt Real roots t := by
  obtain ⟨roots, hroots₀, hrootsSol⟩ :=
    exists_sixVertexContinuousBetheBranch_of_anisotropyMagnitude
      ha hab hc₀ hN hhalf htail z₀ hz₀
  refine ⟨roots, hroots₀, hrootsSol, ?_⟩
  intro t ht
  have htIcc : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
  have htc : 2 < t := ha.trans ht.1
  have hjac : Function.Injective
      (sixVertexBetheRootJacobian N n t (roots t)) :=
    sixVertexBetheRootJacobian_injective_of_anisotropyMagnitude
      htc hhalf (htail.trans_le
        (sixVertexAnisotropyMagnitude_mono (by linarith) ht.1.le)) _
  obtain ⟨B⟩ := exists_sixVertexLocalAnalyticBetheBranch_of_rootJacobian
    htc (hrootsSol t htIcc) hjac
  have hgraph : Tendsto (fun s => (s, roots s))
      (nhds t) (nhds (t, roots t)) :=
    continuousAt_id.prodMk roots.continuous.continuousAt
  have hunique : ∀ᶠ s in nhds t,
      SixVertexSatisfiesBetheEquations s N n (roots s) →
        B.roots s = roots s :=
    hgraph.eventually B.eventually_unique
  have hIoo : ∀ᶠ s in nhds t, s ∈ Set.Ioo a b :=
    isOpen_Ioo.mem_nhds ht
  have hwithin : ∀ᶠ s in nhds t, s ∈ Set.Icc a b := by
    filter_upwards [hIoo] with s hs
    exact ⟨hs.1.le, hs.2.le⟩
  have heq : B.roots =ᶠ[nhds t] roots := by
    filter_upwards [hunique, hwithin] with s hsu hs
    exact hsu (hrootsSol s hs)
  exact B.analyticAt_roots.congr heq



theorem exists_sixVertexAnalyticBetheBranch_throughChosen
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N)
    (htail : (n : Real) < sixVertexAnisotropyMagnitude a) :
    ∃ roots : C(Real, Fin n → Real),
      roots c₀ = sixVertexChosenBetheSolution
        (ha.trans_le hc₀.1) hhalf ∧
      (∀ t ∈ Set.Icc a b,
        SixVertexSatisfiesBetheEquations t N n (roots t)) ∧
      ∀ t ∈ Set.Ioo a b, AnalyticAt Real roots t := by
  let hc : 2 < c₀ := ha.trans_le hc₀.1
  let p : Fin n → Real := sixVertexChosenBetheSolution hc hhalf
  have hpopen : SixVertexOpenRootSimplex p :=
    sixVertexChosenBetheSolution_mem_open hc hhalf
  have hpsol : SixVertexSatisfiesBetheEquations c₀ N n p :=
    sixVertexChosenBetheSolution_is_solution hc hhalf
  have hpfix : sixVertexBetheUpdate c₀ N n p = p :=
    (sixVertexBetheUpdate_eq_self_iff hN p).mpr hpsol
  let z₀ : SixVertexBetheContinuationSpace a b N n :=
    ⟨(c₀, p), hc₀, hpopen.toClosed, hpfix⟩
  have hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩ := by
    rfl
  simpa [p, hc] using
    exists_sixVertexAnalyticBetheBranch_of_anisotropyMagnitude
      ha hab hc₀ hN hhalf htail z₀ hz₀



def sixVertexFirstHalfIndex (m : Nat) (j : Fin m) : Fin (m + m) :=
  Fin.castAdd m j

def sixVertexReflectedHalfIndex (m : Nat) (j : Fin m) : Fin (m + m) :=
  (sixVertexFirstHalfIndex m j).rev

theorem sixVertexFirstHalfIndex_lt_reflected (m : Nat) (j : Fin m) :
    sixVertexFirstHalfIndex m j < sixVertexReflectedHalfIndex m j := by
  rw [Fin.lt_def]
  simp [sixVertexFirstHalfIndex, sixVertexReflectedHalfIndex, Fin.rev]
  omega

theorem sixVertexFirstHalfRoot_mem_Icc
    {m : Nat} {p : Fin (m + m) → Real}
    (hp : SixVertexOpenRootSimplex p) (j : Fin m) :
    p (sixVertexFirstHalfIndex m j) ∈ Set.Icc (-Real.pi) 0 := by
  let i := sixVertexFirstHalfIndex m j
  have hlt := hp.1 (sixVertexFirstHalfIndex_lt_reflected m j)
  have hsymm := hp.2.1 i
  have hneg : p i < 0 := by
    change p i < p i.rev at hlt
    rw [hsymm] at hlt
    linarith
  exact ⟨(hp.2.2 i).1.le, hneg.le⟩

theorem sixVertexThetaDerivativeDenominator_neg_right
    (c x y : Real) :
    sixVertexThetaDerivativeDenominator c x (-y) =
      sixVertexThetaDerivativeDenominator c (-x) y := by
  unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
  rw [Real.cos_neg, Real.cos_neg, Real.sin_neg, Real.sin_neg]
  ring



def sixVertexBetheSymmetricHalfJacobianMatrix
    (N m : Nat) (c : Real) (p : Fin (m + m) → Real) :
    Matrix (Fin m) (Fin m) Real := fun j k =>
  sixVertexBetheJacobianMatrix N (m + m) c p
      (sixVertexFirstHalfIndex m j) (sixVertexFirstHalfIndex m k) -
    sixVertexBetheJacobianMatrix N (m + m) c p
      (sixVertexFirstHalfIndex m j) (sixVertexReflectedHalfIndex m k)



theorem sixVertexBetheSymmetricHalfJacobianMatrix_offdiag_nonneg
    {N m : Nat} {c : Real} (hc : 2 < c)
    {p : Fin (m + m) → Real} (hp : SixVertexOpenRootSimplex p)
    {j k : Fin m} (hjk : j ≠ k) :
    0 ≤ sixVertexBetheSymmetricHalfJacobianMatrix N m c p j k := by
  let i := sixVertexFirstHalfIndex m j
  let l := sixVertexFirstHalfIndex m k
  let lr := sixVertexReflectedHalfIndex m k
  have hil : i ≠ l := by
    intro h
    apply hjk
    have hval := congrArg Fin.val h
    dsimp [i, l, sixVertexFirstHalfIndex] at hval
    exact Fin.ext hval
  have hilr : i ≠ lr := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [i, lr, sixVertexFirstHalfIndex,
      sixVertexReflectedHalfIndex, Fin.rev] at hval
    omega
  have hsymm : p lr = -p l := by
    exact hp.2.1 l
  have hiIcc : p i ∈ Set.Icc (-Real.pi) 0 :=
    sixVertexFirstHalfRoot_mem_Icc hp j
  have hlIcc : p l ∈ Set.Icc (-Real.pi) 0 :=
    sixVertexFirstHalfRoot_mem_Icc hp k
  have hsign := sixVertexTheta_right_difference_nonneg hc hiIcc hlIcc
  unfold sixVertexBetheSymmetricHalfJacobianMatrix
  rw [sixVertexBetheJacobianMatrix, if_neg hil,
    sixVertexBetheJacobianMatrix, if_neg hilr, hsymm,
    sixVertexBetheIntegratingFactor]
  rw [sixVertexThetaDerivativeDenominator_neg_right]
  simpa [i, l, lr, sixVertexBetheIntegratingFactor, Real.cos_neg] using hsign

end
end StatMech.FrontierD
