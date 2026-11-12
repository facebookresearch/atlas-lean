/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterThreeBridgeGraham









open Finset SimpleGraph

namespace StatMech.Ising

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

variable {V : Type*}


def threeBridgeSites (x y z : V) : Fin 3 -> V :=
  Fin.cases x (Fin.cases y (fun _ => z))

@[simp] theorem threeBridgeSites_zero (x y z : V) :
    threeBridgeSites x y z 0 = x := rfl

@[simp] theorem threeBridgeSites_one (x y z : V) :
    threeBridgeSites x y z 1 = y := rfl

@[simp] theorem threeBridgeSites_two (x y z : V) :
    threeBridgeSites x y z 2 = z := rfl



@[simp] theorem replicaBridgeInteraction_threeBridgeSites
    (x y z : V) (a b : ConfigSpace V) :
    replicaBridgeInteraction (threeBridgeSites x y z) a b =
      spin a x * spin b x + spin a y * spin b y + spin a z * spin b z := by
  simp [replicaBridgeInteraction, threeBridgeSites, Fin.sum_univ_succ]
  ring

variable [Fintype V] [DecidableEq V]


def threeBridgeOneCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y z : V) : Real :=
  (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s z)) ^ 2


def threeBridgeTwoCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y z : V) : Real :=
  (expJ G.edgeFinset J hf (fun s => spin s x * spin s y)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s x * spin s z)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s y * spin s z)) ^ 2


def threeBridgeThreeCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y z : V) : Real :=
  (expJ G.edgeFinset J hf
    (fun s => spin s x * (spin s y * spin s z))) ^ 2



def threeBridgeTiltMean (t a b c : Real) : Real :=
  3 * t + (1 - t ^ 2) * (a + 2 * b * t + 3 * c * t ^ 2) /
    (1 + a * t + b * t ^ 2 + c * t ^ 3)



theorem hasDerivAt_threeBridgeTiltMean_tanh
    (r a b c : Real)
    (hP : 1 + a * Real.tanh r + b * Real.tanh r ^ 2 +
      c * Real.tanh r ^ 3 ≠ 0) :
    HasDerivAt (fun u => threeBridgeTiltMean (Real.tanh u) a b c)
      (threeBridgeTiltVariance (Real.tanh r) a b c) r := by
  let t := Real.tanh r
  let U : Real -> Real := fun u => 1 - u ^ 2
  let Q : Real -> Real := fun u => a + 2 * b * u + 3 * c * u ^ 2
  let P : Real -> Real := fun u => 1 + a * u + b * u ^ 2 + c * u ^ 3
  have hU : HasDerivAt U (-2 * t) t := by
    dsimp [U]
    convert (hasDerivAt_const t 1).sub ((hasDerivAt_id t).pow 2) using 1 <;>
      simp [id_eq] <;> ring
  have hQ : HasDerivAt Q (2 * b + 6 * c * t) t := by
    dsimp [Q]
    convert ((hasDerivAt_const t a).add
      ((hasDerivAt_id t).const_mul (2 * b))).add
      (((hasDerivAt_id t).pow 2).const_mul (3 * c)) using 1 <;>
      simp [id_eq] <;> ring
  have hPderiv : HasDerivAt P (a + 2 * b * t + 3 * c * t ^ 2) t := by
    dsimp [P]
    convert (((hasDerivAt_const t 1).add
      ((hasDerivAt_id t).const_mul a)).add
      (((hasDerivAt_id t).pow 2).const_mul b)).add
      (((hasDerivAt_id t).pow 3).const_mul c) using 1 <;>
      simp [id_eq] <;> ring
  have hP' : P t ≠ 0 := by simpa [P, t] using hP
  have houter := ((hasDerivAt_id t).const_mul 3).add
    ((hU.mul hQ).div hPderiv hP')
  have htderiv : HasDerivAt Real.tanh (1 - t ^ 2) r := by
    have h := hasDerivAt_tanh r
    convert h using 1
    dsimp [t]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos r).ne']
    nlinarith [Real.cosh_sq_sub_sinh_sq r]
  have hcomp := houter.comp r htderiv
  change HasDerivAt
    (fun u => 3 * Real.tanh u +
      U (Real.tanh u) * Q (Real.tanh u) / P (Real.tanh u)) _ r at hcomp
  convert hcomp using 1
  change threeBridgeTiltVariance t a b c = _
  let d := 1 + a * t + b * t ^ 2 + c * t ^ 3
  let q := a + 2 * b * t + 3 * c * t ^ 2
  let qp := 2 * b + 6 * c * t
  have hd : d ≠ 0 := by simpa [d, t] using hP
  dsimp [U, Q, P, threeBridgeTiltVariance]
  simp only [mul_one]
  change
    (t - 1) * (t + 1) *
        (-2 * a ^ 2 * t ^ 2 + a ^ 2 - 2 * a * b * t ^ 3 +
          2 * a * b * t + 2 * a * c * t ^ 4 - 4 * a * t -
          b ^ 2 * t ^ 4 + 2 * b ^ 2 * t ^ 2 + 4 * b * c * t ^ 3 -
          2 * b + 3 * c ^ 2 * t ^ 4 + 6 * c * t ^ 3 -
          6 * c * t - 3) / d ^ 2 =
      (3 + (((-2 * t) * q + (1 - t ^ 2) * qp) * d -
        (1 - t ^ 2) * q * q) / d ^ 2) * (1 - t ^ 2)
  field_simp [hd]
  ring


theorem replicaBridgeMoment_threeBridgeSites_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y z : V) (r : Real) :
    replicaBridgeMoment G J hf (threeBridgeSites x y z) r =
      Real.cosh r ^ 3 +
        Real.cosh r ^ 2 * Real.sinh r *
          threeBridgeOneCoeff G J hf x y z +
        Real.cosh r * Real.sinh r ^ 2 *
          threeBridgeTwoCoeff G J hf x y z +
        Real.sinh r ^ 3 * threeBridgeThreeCoeff G J hf x y z := by
  let c := Real.cosh r
  let s := Real.sinh r
  have hexpand :
      (fun a b : ConfigSpace V => Real.exp (r *
        (spin a x * spin b x + spin a y * spin b y +
          spin a z * spin b z))) =
      (fun a b =>
        c ^ 3 +
          c ^ 2 * s *
            (spin a x * spin b x + spin a y * spin b y +
              spin a z * spin b z) +
          c * s ^ 2 *
            ((spin a x * spin a y) * (spin b x * spin b y) +
              (spin a x * spin a z) * (spin b x * spin b z) +
              (spin a y * spin a z) * (spin b y * spin b z)) +
          s ^ 3 *
            ((spin a x * (spin a y * spin a z)) *
              (spin b x * (spin b y * spin b z)))) := by
    funext a b
    have hx : spin a x * spin b x = 1 ∨ spin a x * spin b x = -1 := by
      rcases spin_eq_pm a x with ha | ha <;>
        rcases spin_eq_pm b x with hb | hb <;> simp [ha, hb]
    have hy : spin a y * spin b y = 1 ∨ spin a y * spin b y = -1 := by
      rcases spin_eq_pm a y with ha | ha <;>
        rcases spin_eq_pm b y with hb | hb <;> simp [ha, hb]
    have hz : spin a z * spin b z = 1 ∨ spin a z * spin b z = -1 := by
      rcases spin_eq_pm a z with ha | ha <;>
        rcases spin_eq_pm b z with hb | hb <;> simp [ha, hb]
    rw [mul_add, mul_add, Real.exp_add, Real.exp_add,
      exp_mul_pm _ _ hx, exp_mul_pm _ _ hy, exp_mul_pm _ _ hz]
    dsimp [c, s]
    ring
  have hone : ghsiExp2 G J hf (fun _ _ => (1 : Real)) = 1 := by
    have h := ghsiExp2_factor G J hf
      (fun _ => (1 : Real)) (fun _ => (1 : Real))
    simpa [expJ_one G J hf] using h
  have hconst (u : Real) :
      ghsiExp2 G J hf (fun _ _ => u) = u := by
    have hfun : (fun _ _ : ConfigSpace V => u) =
        (fun _ _ => u * (1 : Real)) := by funext a b; ring
    rw [hfun, ghsiExp2_const_mul, hone, mul_one]
  unfold replicaBridgeMoment
  simp only [replicaBridgeInteraction_threeBridgeSites]
  rw [hexpand]
  simp only [ghsiExp2_add, ghsiExp2_const_mul, ghsiExp2_factor]
  rw [hconst]
  dsimp [c, s, threeBridgeOneCoeff, threeBridgeTwoCoeff,
    threeBridgeThreeCoeff]
  ring




theorem replicaBridgeMoment_threeBridgeSites_eq_factor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y z : V) (r : Real) :
    replicaBridgeMoment G J hf (threeBridgeSites x y z) r =
      Real.cosh r ^ 3 *
        (1 + threeBridgeOneCoeff G J hf x y z * Real.tanh r +
          threeBridgeTwoCoeff G J hf x y z * Real.tanh r ^ 2 +
          threeBridgeThreeCoeff G J hf x y z * Real.tanh r ^ 3) := by
  rw [replicaBridgeMoment_threeBridgeSites_eq]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos r).ne']



theorem replicaBridgeMean_threeBridgeSites_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y z : V) (r : Real) :
    replicaBridgeMean G J hf (threeBridgeSites x y z) r =
      threeBridgeTiltMean (Real.tanh r)
        (threeBridgeOneCoeff G J hf x y z)
        (threeBridgeTwoCoeff G J hf x y z)
        (threeBridgeThreeCoeff G J hf x y z) := by
  let a := threeBridgeOneCoeff G J hf x y z
  let b := threeBridgeTwoCoeff G J hf x y z
  let c := threeBridgeThreeCoeff G J hf x y z
  let t := Real.tanh r
  let P : Real -> Real := fun u => 1 + a * u + b * u ^ 2 + c * u ^ 3
  have hfactor (u : Real) :
      replicaBridgeMoment G J hf (threeBridgeSites x y z) u =
        Real.cosh u ^ 3 * P (Real.tanh u) := by
    simpa [a, b, c, P] using
      replicaBridgeMoment_threeBridgeSites_eq_factor G J hf x y z u
  have hc3 : 0 < Real.cosh r ^ 3 := pow_pos (Real.cosh_pos r) 3
  have hPpos : 0 < P t := by
    have hm := replicaBridgeMoment_pos G J hf (threeBridgeSites x y z) r
    rw [hfactor] at hm
    exact pos_of_mul_pos_right hm hc3.le
  have htderiv : HasDerivAt Real.tanh (1 - t ^ 2) r := by
    have h := hasDerivAt_tanh r
    convert h using 1
    dsimp [t]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos r).ne']
    nlinarith [Real.cosh_sq_sub_sinh_sq r]
  have hPouter : HasDerivAt P (a + 2 * b * t + 3 * c * t ^ 2) t := by
    dsimp [P]
    convert (((hasDerivAt_const t 1).add
      ((hasDerivAt_id t).const_mul a)).add
      (((hasDerivAt_id t).pow 2).const_mul b)).add
      (((hasDerivAt_id t).pow 3).const_mul c) using 1 <;>
      simp [id_eq] <;> ring
  have hPcomp := hPouter.comp r htderiv
  have hcosh3 : HasDerivAt (fun u => Real.cosh u ^ 3)
      (3 * Real.cosh r ^ 2 * Real.sinh r) r := by
    convert (Real.hasDerivAt_cosh r).pow 3 using 1 <;> ring
  have hprod := hcosh3.mul hPcomp
  have hclosed : HasDerivAt
      (fun u => Real.log (Real.cosh u ^ 3 * P (Real.tanh u)))
      (threeBridgeTiltMean t a b c) r := by
    have hlog := hprod.log (mul_ne_zero hc3.ne' hPpos.ne')
    convert hlog using 1
    change threeBridgeTiltMean t a b c =
      (3 * Real.cosh r ^ 2 * Real.sinh r * P t +
          Real.cosh r ^ 3 *
            ((a + 2 * b * t + 3 * c * t ^ 2) * (1 - t ^ 2))) /
        (Real.cosh r ^ 3 * P t)
    let C := Real.cosh r
    let S := Real.sinh r
    let d := P t
    let q := a + 2 * b * t + 3 * c * t ^ 2
    have hC : C ≠ 0 := by exact (Real.cosh_pos r).ne'
    have hd : d ≠ 0 := by exact hPpos.ne'
    change 3 * t + (1 - t ^ 2) * q / d =
      (3 * C ^ 2 * S * d + C ^ 3 * (q * (1 - t ^ 2))) /
        (C ^ 3 * d)
    rw [show t = S / C by
      dsimp [t, S, C]
      exact Real.tanh_eq_sinh_div_cosh r]
    field_simp [hC, hd]
  have hnative :=
    hasDerivAt_log_replicaBridgeMoment G J hf (threeBridgeSites x y z) r
  have hfun :
      (fun u => Real.log
        (replicaBridgeMoment G J hf (threeBridgeSites x y z) u)) =
      (fun u => Real.log (Real.cosh u ^ 3 * P (Real.tanh u))) := by
    funext u
    rw [hfactor]
  rw [hfun] at hnative
  simpa [a, b, c, t] using hnative.unique hclosed



theorem replicaBridgeVariance_threeBridgeSites_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y z : V) (r : Real) :
    replicaBridgeVariance G J hf (threeBridgeSites x y z) r =
      threeBridgeTiltVariance (Real.tanh r)
        (threeBridgeOneCoeff G J hf x y z)
        (threeBridgeTwoCoeff G J hf x y z)
        (threeBridgeThreeCoeff G J hf x y z) := by
  let a := threeBridgeOneCoeff G J hf x y z
  let b := threeBridgeTwoCoeff G J hf x y z
  let c := threeBridgeThreeCoeff G J hf x y z
  let t := Real.tanh r
  have hmeanfun :
      replicaBridgeMean G J hf (threeBridgeSites x y z) =
        fun u => threeBridgeTiltMean (Real.tanh u) a b c := by
    funext u
    simpa [a, b, c] using
      replicaBridgeMean_threeBridgeSites_eq G J hf x y z u
  have hmoment := replicaBridgeMoment_pos G J hf (threeBridgeSites x y z) r
  have hfactor := replicaBridgeMoment_threeBridgeSites_eq_factor
    G J hf x y z r
  have hc3 : 0 < Real.cosh r ^ 3 := pow_pos (Real.cosh_pos r) 3
  have hP : 1 + a * t + b * t ^ 2 + c * t ^ 3 ≠ 0 := by
    rw [hfactor] at hmoment
    have hmoment' :
        0 < Real.cosh r ^ 3 *
          (1 + a * t + b * t ^ 2 + c * t ^ 3) := by
      simpa [a, b, c, t] using hmoment
    have hp : 0 < 1 + a * t + b * t ^ 2 + c * t ^ 3 := by
      exact pos_of_mul_pos_right hmoment' hc3.le
    exact hp.ne'
  have hclosed := hasDerivAt_threeBridgeTiltMean_tanh r a b c hP
  have hnative :=
    hasDerivAt_replicaBridgeMean G J hf (threeBridgeSites x y z) r
  rw [hmeanfun] at hnative
  simpa [a, b, c, t] using hnative.unique hclosed




theorem replicaBridgeVariance_threeBridgeSites_le_neg_iff_skew
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y z : V)
    {r : Real} (hr : 0 < r) :
    replicaBridgeVariance G J hf (threeBridgeSites x y z) r <=
        replicaBridgeVariance G J hf (threeBridgeSites x y z) (-r) <->
      threeBridgeVarianceSkewPolynomial (Real.tanh r)
        (threeBridgeOneCoeff G J hf x y z)
        (threeBridgeTwoCoeff G J hf x y z)
        (threeBridgeThreeCoeff G J hf x y z) <= 0 := by
  let a := threeBridgeOneCoeff G J hf x y z
  let b := threeBridgeTwoCoeff G J hf x y z
  let c := threeBridgeThreeCoeff G J hf x y z
  let t := Real.tanh r
  have ht0 : 0 < t := by
    dsimp [t]
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hr) (Real.cosh_pos r)
  have ht1 : t < 1 := Real.tanh_lt_one r
  have hcosh3 : 0 < Real.cosh r ^ 3 := pow_pos (Real.cosh_pos r) 3
  have hPp : 1 + a * t + b * t ^ 2 + c * t ^ 3 ≠ 0 := by
    have hm := replicaBridgeMoment_pos G J hf (threeBridgeSites x y z) r
    rw [replicaBridgeMoment_threeBridgeSites_eq_factor] at hm
    have hm' :
        0 < Real.cosh r ^ 3 *
          (1 + a * t + b * t ^ 2 + c * t ^ 3) := by
      simpa [a, b, c, t] using hm
    exact (pos_of_mul_pos_right hm' hcosh3.le).ne'
  have hPm : 1 - a * t + b * t ^ 2 - c * t ^ 3 ≠ 0 := by
    have hm := replicaBridgeMoment_pos G J hf (threeBridgeSites x y z) (-r)
    rw [replicaBridgeMoment_threeBridgeSites_eq_factor] at hm
    simp only [Real.cosh_neg, Real.tanh_neg] at hm
    have hm' :
        0 < Real.cosh r ^ 3 *
          (1 - a * t + b * t ^ 2 - c * t ^ 3) := by
      ring_nf at hm ⊢
      simpa [a, b, c, t] using hm
    exact (pos_of_mul_pos_right hm' hcosh3.le).ne'
  rw [replicaBridgeVariance_threeBridgeSites_eq,
    replicaBridgeVariance_threeBridgeSites_eq]
  simp only [Real.tanh_neg]
  simpa [a, b, c, t] using
    (threeBridgeTiltVariance_le_neg_iff ht0 ht1 hPp hPm)



theorem threeBridgeThreeCoeff_le_grahamBoundSq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall v, 0 <= hf v)
    {i j k : V} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    threeBridgeThreeCoeff G K hf i j k <=
      (grahamInhomOne G K hf i *
          expJ G.edgeFinset K hf (fun s => spin s j * spin s k) +
        expJ G.edgeFinset K hf (fun s => spin s i * spin s j) *
          grahamInhomOne G K hf k +
        expJ G.edgeFinset K hf (fun s => spin s i * spin s k) *
          grahamInhomOne G K hf j -
        2 * grahamInhomOne G K hf i * grahamInhomOne G K hf j *
          grahamInhomOne G K hf k -
        2 * ghsiCovariance G K hf i k * ghsiCovariance G K hf j k *
          grahamInhomOne G K hf k) ^ 2 := by
  simpa [threeBridgeThreeCoeff] using
    (sq_grahamInhomThreePoint_le G K hf hK hhf hij hik hjk)




theorem threeBridge_allDisagreementCoefficient_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y z : V) :
    0 <= 1 - threeBridgeOneCoeff G J hf x y z +
      threeBridgeTwoCoeff G J hf x y z -
      threeBridgeThreeCoeff G J hf x y z := by
  let F : ConfigSpace V -> ConfigSpace V -> Real := fun a b =>
    (1 - spin a x * spin b x) * (1 - spin a y * spin b y) *
      (1 - spin a z * spin b z)
  have hF : forall a b, 0 <= F a b := by
    intro a b
    have hx : 0 <= 1 - spin a x * spin b x := by
      rcases spin_eq_pm a x with ha | ha <;>
        rcases spin_eq_pm b x with hb | hb <;> simp [ha, hb]
    have hy : 0 <= 1 - spin a y * spin b y := by
      rcases spin_eq_pm a y with ha | ha <;>
        rcases spin_eq_pm b y with hb | hb <;> simp [ha, hb]
    have hz : 0 <= 1 - spin a z * spin b z := by
      rcases spin_eq_pm a z with ha | ha <;>
        rcases spin_eq_pm b z with hb | hb <;> simp [ha, hb]
    exact mul_nonneg (mul_nonneg hx hy) hz
  have hnonneg : 0 <= ghsiExp2 G J hf F := by
    unfold ghsiExp2
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro a _
      apply Finset.sum_nonneg
      intro b _
      exact mul_nonneg
        (mul_nonneg (wJ_nonneg G.edgeFinset J hf a)
          (wJ_nonneg G.edgeFinset J hf b)) (hF a b)
    · exact sq_nonneg _
  have hfun : F = fun a b =>
      (1 : Real) +
        (-1) * (spin a x * spin b x) +
        (-1) * (spin a y * spin b y) +
        (-1) * (spin a z * spin b z) +
        (spin a x * spin a y) * (spin b x * spin b y) +
        (spin a x * spin a z) * (spin b x * spin b z) +
        (spin a y * spin a z) * (spin b y * spin b z) +
        (-1) * ((spin a x * (spin a y * spin a z)) *
          (spin b x * (spin b y * spin b z))) := by
    funext a b
    dsimp [F]
    ring
  rw [hfun] at hnonneg
  simp only [ghsiExp2_add, ghsiExp2_const_mul, ghsiExp2_factor] at hnonneg
  have hone : ghsiExp2 G J hf (fun _ _ => (1 : Real)) = 1 := by
    have h := ghsiExp2_factor G J hf
      (fun _ => (1 : Real)) (fun _ => (1 : Real))
    simpa [expJ_one G J hf] using h
  rw [hone] at hnonneg
  dsimp [threeBridgeOneCoeff, threeBridgeTwoCoeff,
    threeBridgeThreeCoeff]
  linarith

end

end StatMech.Ising
