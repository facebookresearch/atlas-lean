/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.LebowitzPfisterSingleBridgeVariance

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


def twoBridgeSites (x y : V) : Bool -> V
  | false => x
  | true => y

@[simp] theorem replicaBridgeInteraction_twoBridgeSites
    (x y : V) (a b : ConfigSpace V) :
    replicaBridgeInteraction (twoBridgeSites x y) a b =
      spin a x * spin b x + spin a y * spin b y := by
  unfold replicaBridgeInteraction twoBridgeSites
  rw [Fintype.sum_bool]
  simp only
  ring

theorem replicaBridgeMoment_twoBridgeSites_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y : V) (r : Real) :
    replicaBridgeMoment G J hf (twoBridgeSites x y) r =
      twoReplicaTwoBridgeMoment G J hf x y r := by
  unfold replicaBridgeMoment twoReplicaTwoBridgeMoment
  congr 1
  funext a b
  rw [replicaBridgeInteraction_twoBridgeSites]


def twoBridgeTiltMean (t A E : Real) : Real :=
  2 * t + (1 - t ^ 2) * (A + 2 * E * t) /
    (1 + A * t + E * t ^ 2)



theorem replicaBridgeMean_twoBridgeSites_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y : V) (r : Real) :
    replicaBridgeMean G J hf (twoBridgeSites x y) r =
      twoBridgeTiltMean (Real.tanh r)
        ((expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 +
          (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2)
        ((expJ G.edgeFinset J hf
          (fun s => spin s x * spin s y)) ^ 2) := by
  let mx := expJ G.edgeFinset J hf (fun s => spin s x)
  let my := expJ G.edgeFinset J hf (fun s => spin s y)
  let cxy := expJ G.edgeFinset J hf (fun s => spin s x * spin s y)
  let A := mx ^ 2 + my ^ 2
  let E := cxy ^ 2
  let M : Real -> Real := fun u =>
    Real.cosh u ^ 2 + Real.cosh u * Real.sinh u * A +
      Real.sinh u ^ 2 * E
  have hmoment (u : Real) :
      replicaBridgeMoment G J hf (twoBridgeSites x y) u = M u := by
    rw [replicaBridgeMoment_twoBridgeSites_eq,
      twoReplicaTwoBridgeMoment_eq]
  have hMderiv : HasDerivAt M
      (2 * Real.cosh r * Real.sinh r +
        (Real.cosh r ^ 2 + Real.sinh r ^ 2) * A +
        2 * Real.sinh r * Real.cosh r * E) r := by
    dsimp [M]
    convert ((Real.hasDerivAt_cosh r).pow 2).add
      (((Real.hasDerivAt_cosh r).mul (Real.hasDerivAt_sinh r)).mul_const A) |>.add
      (((Real.hasDerivAt_sinh r).pow 2).mul_const E) using 1 <;> ring
  have hMpos : 0 < M r := by
    rw [← hmoment]
    exact replicaBridgeMoment_pos G J hf (twoBridgeSites x y) r
  have hlogM := hMderiv.log hMpos.ne'
  have hlogBridge :=
    hasDerivAt_log_replicaBridgeMoment G J hf (twoBridgeSites x y) r
  have hfun :
      (fun u => Real.log
        (replicaBridgeMoment G J hf (twoBridgeSites x y) u)) =
      (fun u => Real.log (M u)) := by
    funext u
    rw [hmoment]
  rw [hfun] at hlogBridge
  have hmean : replicaBridgeMean G J hf (twoBridgeSites x y) r =
      (2 * Real.cosh r * Real.sinh r +
        (Real.cosh r ^ 2 + Real.sinh r ^ 2) * A +
        2 * Real.sinh r * Real.cosh r * E) / M r :=
    hlogBridge.unique hlogM
  rw [hmean]
  change _ = twoBridgeTiltMean (Real.tanh r) A E
  have hD : Real.cosh r ^ 2 + Real.cosh r * Real.sinh r * A +
      Real.sinh r ^ 2 * E ≠ 0 := by
    simpa [M] using hMpos.ne'
  have hD' : Real.cosh r * Real.sinh r * A + Real.cosh r ^ 2 +
      Real.sinh r ^ 2 * E ≠ 0 := by
    simpa [add_comm, add_left_comm, add_assoc] using hD
  unfold twoBridgeTiltMean M
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh r ≠ 0 := (Real.cosh_pos r).ne'
  have hcs : Real.cosh r ^ 2 = Real.sinh r ^ 2 + 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq r]
  have hPidentity :
      1 + A * (Real.sinh r / Real.cosh r) +
          E * (Real.sinh r / Real.cosh r) ^ 2 =
        (Real.cosh r ^ 2 + Real.cosh r * Real.sinh r * A +
          Real.sinh r ^ 2 * E) / Real.cosh r ^ 2 := by
    field_simp [hc]
  rw [hPidentity]
  have hDc :
      (Real.cosh r ^ 2 + Real.cosh r * Real.sinh r * A +
          Real.sinh r ^ 2 * E) / Real.cosh r ^ 2 ≠ 0 :=
    div_ne_zero hD (pow_ne_zero 2 hc)
  rw [show
    (1 - (Real.sinh r / Real.cosh r) ^ 2) *
          (A + 2 * E * (Real.sinh r / Real.cosh r)) /
        ((Real.cosh r ^ 2 + Real.cosh r * Real.sinh r * A +
          Real.sinh r ^ 2 * E) / Real.cosh r ^ 2) =
      (1 - (Real.sinh r / Real.cosh r) ^ 2) *
          (A + 2 * E * (Real.sinh r / Real.cosh r)) *
        Real.cosh r ^ 2 /
          (Real.cosh r ^ 2 + Real.cosh r * Real.sinh r * A +
            Real.sinh r ^ 2 * E) by
      field_simp [hc, hD, hDc]]
  apply (div_eq_iff hD).2
  rw [add_mul
    (2 * (Real.sinh r / Real.cosh r))
    ((1 - (Real.sinh r / Real.cosh r) ^ 2) *
      (A + 2 * E * (Real.sinh r / Real.cosh r)) * Real.cosh r ^ 2 /
        (Real.cosh r ^ 2 + Real.cosh r * Real.sinh r * A +
          Real.sinh r ^ 2 * E))
    (Real.cosh r ^ 2 + Real.cosh r * Real.sinh r * A +
      Real.sinh r ^ 2 * E)]
  rw [div_mul_cancel₀ _ hD]
  field_simp [hc]
  have hcsE := congrArg
    (fun z : Real => z * Real.sinh r * E * 2) hcs
  ring_nf at hcsE ⊢


def twoBridgeTiltMeanDeriv (t A E : Real) : Real :=
  (A ^ 2 * t ^ 2 - A ^ 2 - 2 * A * E * t + 2 * A * t -
      2 * E ^ 2 * t ^ 2 - 2 * E * t ^ 2 + 2 * E + 2) /
    (1 + A * t + E * t ^ 2) ^ 2



theorem hasDerivAt_twoBridgeTiltMean
    (t A E : Real) (hP : 1 + A * t + E * t ^ 2 ≠ 0) :
    HasDerivAt (fun u => twoBridgeTiltMean u A E)
      (twoBridgeTiltMeanDeriv t A E) t := by
  let U : Real -> Real := fun u => 1 - u ^ 2
  let L : Real -> Real := fun u => A + 2 * E * u
  let P : Real -> Real := fun u => 1 + A * u + E * u ^ 2
  have hU : HasDerivAt U (-2 * t) t := by
    dsimp [U]
    convert (hasDerivAt_const t 1).sub
      ((hasDerivAt_id t).pow 2) using 1 <;> simp [id_eq] <;> ring
  have hL : HasDerivAt L (2 * E) t := by
    dsimp [L]
    convert (hasDerivAt_const t A).add
      ((hasDerivAt_id t).const_mul (2 * E)) using 1 <;> simp [id_eq] <;> ring
  have hPderiv : HasDerivAt P (A + 2 * E * t) t := by
    dsimp [P]
    convert ((hasDerivAt_const t 1).add ((hasDerivAt_id t).const_mul A)).add
      (((hasDerivAt_id t).pow 2).const_mul E) using 1 <;> simp [id_eq] <;> ring
  have hquot := (hU.mul hL).div hPderiv (by simpa [P] using hP)
  have htotal := ((hasDerivAt_id t).const_mul 2).add hquot
  change HasDerivAt (fun u => 2 * u + U u * L u / P u)
    (twoBridgeTiltMeanDeriv t A E) t
  convert htotal using 1
  unfold twoBridgeTiltMeanDeriv
  dsimp [U, L, P]
  have hPpow : (1 + A * t + E * t ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hP
  rw [div_eq_iff hPpow]
  rw [add_mul, div_mul_cancel₀ _ hPpow]
  ring



theorem replicaBridgeVariance_twoBridgeSites_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y : V) (r : Real) :
    replicaBridgeVariance G J hf (twoBridgeSites x y) r =
      twoBridgeTiltVariance (Real.tanh r)
        ((expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 +
          (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2)
        ((expJ G.edgeFinset J hf
          (fun s => spin s x * spin s y)) ^ 2) := by
  let A := (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2
  let E := (expJ G.edgeFinset J hf
    (fun s => spin s x * spin s y)) ^ 2
  let t := Real.tanh r
  have hmeanfun :
      replicaBridgeMean G J hf (twoBridgeSites x y) =
        fun u => twoBridgeTiltMean (Real.tanh u) A E := by
    funext u
    exact replicaBridgeMean_twoBridgeSites_eq G J hf x y u
  have hmomentPos := replicaBridgeMoment_pos G J hf (twoBridgeSites x y) r
  have hmomentEq := replicaBridgeMoment_twoBridgeSites_eq G J hf x y r
  have hc2 : 0 < Real.cosh r ^ 2 := sq_pos_of_pos (Real.cosh_pos r)
  have hfactor :
      twoReplicaTwoBridgeMoment G J hf x y r =
        Real.cosh r ^ 2 * (1 + A * t + E * t ^ 2) := by
    rw [twoReplicaTwoBridgeMoment_eq]
    dsimp [A, E, t]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos r).ne']
  have hMfactor :
      replicaBridgeMoment G J hf (twoBridgeSites x y) r =
        Real.cosh r ^ 2 * (1 + A * t + E * t ^ 2) :=
    hmomentEq.trans hfactor
  have hPpos : 0 < 1 + A * t + E * t ^ 2 := by
    rw [hMfactor] at hmomentPos
    exact pos_of_mul_pos_right hmomentPos hc2.le
  have htderiv : HasDerivAt Real.tanh (1 - t ^ 2) r := by
    have h := hasDerivAt_tanh r
    convert h using 1
    dsimp [t]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos r).ne']
    nlinarith [Real.cosh_sq_sub_sinh_sq r]
  have hcomp :=
    (hasDerivAt_twoBridgeTiltMean t A E hPpos.ne').comp r htderiv
  have hvar := hasDerivAt_replicaBridgeMean G J hf (twoBridgeSites x y) r
  rw [hmeanfun] at hvar
  have heq := hvar.unique hcomp
  dsimp [t] at heq ⊢
  rw [heq]
  unfold twoBridgeTiltMeanDeriv twoBridgeTiltVariance
  ring


theorem replicaBridgeVariance_twoBridgeSites_le_neg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    (x y : V) (hxy : x ≠ y) (r : Real) (hr : 0 <= r) :
    replicaBridgeVariance G J hf (twoBridgeSites x y) r <=
      replicaBridgeVariance G J hf (twoBridgeSites x y) (-r) := by
  let mx := expJ G.edgeFinset J hf (fun s => spin s x)
  let my := expJ G.edgeFinset J hf (fun s => spin s y)
  let cxy := expJ G.edgeFinset J hf (fun s => spin s x * spin s y)
  let A := mx ^ 2 + my ^ 2
  let E := cxy ^ 2
  have hmx0 : 0 <= mx := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf (fun e he => hJ e) hhf {x}
    rw [spinProd_singleton] at h
    exact h
  have hmy0 : 0 <= my := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf (fun e he => hJ e) hhf {y}
    rw [spinProd_singleton] at h
    exact h
  have hc0 : 0 <= cxy := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf
      (fun e he => hJ e) hhf {x, y}
    rw [spinProd_pair x y hxy] at h
    exact h
  have hmx1 : mx <= 1 := expJ_monomial_le_one _ _ _ _ (fun s => by
    rcases spin_eq_pm s x with h | h <;> rw [h] <;> norm_num)
  have hmy1 : my <= 1 := expJ_monomial_le_one _ _ _ _ (fun s => by
    rcases spin_eq_pm s y with h | h <;> rw [h] <;> norm_num)
  have hc1 : cxy <= 1 := expJ_monomial_le_one _ _ _ _ (fun s => by
    rcases spin_eq_pm s x with hx | hx <;>
      rcases spin_eq_pm s y with hy | hy <;> rw [hx, hy] <;> norm_num)
  have hgks : mx * my <= cxy := by
    have h := gks_second_J G.edgeFinset J hf
      (fun e he => hJ e) hhf {x} {y}
    rw [spinProd_singleton, spinProd_singleton,
      symmDiff_singleton_pair x y hxy, spinProd_pair x y hxy] at h
    exact h
  have hE0 : 0 <= E := sq_nonneg cxy
  have hE1 : E <= 1 := by dsimp [E]; nlinarith
  have hA0 : 0 <= A := by dsimp [A]; positivity
  have hab : mx ^ 2 * my ^ 2 <= E := by
    dsimp [E]
    nlinarith [mul_self_le_mul_self (mul_nonneg hmx0 hmy0) hgks]
  have hAE : A <= 1 + E := by
    dsimp [A]
    have hmxsq : mx ^ 2 <= 1 := by nlinarith
    have hmysq : my ^ 2 <= 1 := by nlinarith
    have hprod : 0 <= (1 - mx ^ 2) * (1 - my ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hmxsq) (sub_nonneg.mpr hmysq)
    have hone : mx ^ 2 + my ^ 2 <= 1 + mx ^ 2 * my ^ 2 := by
      nlinarith
    exact hone.trans (by simpa [add_comm] using add_le_add_left hab 1)
  have ht0 : 0 <= Real.tanh r := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hr) (Real.cosh_pos r).le
  have ht1 : Real.tanh r < 1 := Real.tanh_lt_one r
  rw [replicaBridgeVariance_twoBridgeSites_eq,
    replicaBridgeVariance_twoBridgeSites_eq, Real.tanh_neg]
  exact twoBridgeTiltVariance_le_neg ht0 ht1 hA0 hE0 hE1 hAE

theorem replicaCrossBridgeVariance_twoBridgeSites_same_le_negField
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    (x y : V) (hxy : x ≠ y) (r : Real) (hr : 0 <= r) :
    replicaCrossBridgeVariance G J hf hf (twoBridgeSites x y) r <=
      replicaCrossBridgeVariance G J hf (fun v => -hf v)
        (twoBridgeSites x y) r := by
  rw [← replicaBridgeVariance_order_iff_crossField]
  exact replicaBridgeVariance_twoBridgeSites_le_neg
    G J hf hJ hhf x y hxy r hr

theorem replicaBridgeFreeEnergy_twoBridgeSites_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    (x y : V) (hxy : x ≠ y) (r : Real) (hr : 0 <= r) :
    replicaBridgeFreeEnergy G J hf (twoBridgeSites x y) r <=
      2 * r *
        ((expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 +
          (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2) := by
  have h := replicaBridgeFreeEnergy_le_of_variance_order G J hf
    (twoBridgeSites x y) r hr (fun t ht =>
      replicaBridgeVariance_twoBridgeSites_le_neg
        G J hf hJ hhf x y hxy t ht)
  simpa [twoBridgeSites, Fintype.sum_bool, add_comm] using h

end

end StatMech.Ising
