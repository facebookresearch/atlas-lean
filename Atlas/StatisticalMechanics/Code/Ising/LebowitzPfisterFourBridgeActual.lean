/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeObstruction








open Finset SimpleGraph

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*}


def fourBridgeSites (w x y z : V) : Fin 4 -> V :=
  Fin.cases w (Fin.cases x (Fin.cases y (fun _ => z)))

@[simp] theorem fourBridgeSites_zero (w x y z : V) :
    fourBridgeSites w x y z 0 = w := rfl

@[simp] theorem fourBridgeSites_one (w x y z : V) :
    fourBridgeSites w x y z 1 = x := rfl

@[simp] theorem fourBridgeSites_two (w x y z : V) :
    fourBridgeSites w x y z 2 = y := rfl

@[simp] theorem fourBridgeSites_three (w x y z : V) :
    fourBridgeSites w x y z 3 = z := rfl

variable [Fintype V] [DecidableEq V]

def fourBridgeOneCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) : Real :=
  (expJ G.edgeFinset J hf (fun s => spin s w)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s z)) ^ 2

def fourBridgeTwoCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) : Real :=
  (expJ G.edgeFinset J hf (fun s => spin s w * spin s x)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s w * spin s y)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s w * spin s z)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s x * spin s y)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s x * spin s z)) ^ 2 +
    (expJ G.edgeFinset J hf (fun s => spin s y * spin s z)) ^ 2

def fourBridgeThreeCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) : Real :=
  (expJ G.edgeFinset J hf
      (fun s => spin s w * (spin s x * spin s y))) ^ 2 +
    (expJ G.edgeFinset J hf
      (fun s => spin s w * (spin s x * spin s z))) ^ 2 +
    (expJ G.edgeFinset J hf
      (fun s => spin s w * (spin s y * spin s z))) ^ 2 +
    (expJ G.edgeFinset J hf
      (fun s => spin s x * (spin s y * spin s z))) ^ 2

def fourBridgeFourCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) : Real :=
  (expJ G.edgeFinset J hf
    (fun s => spin s w * (spin s x * (spin s y * spin s z)))) ^ 2


theorem replicaBridgeMoment_fourBridgeSites_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) (r : Real) :
    replicaBridgeMoment G J hf (fourBridgeSites w x y z) r =
      Real.cosh r ^ 4 + Real.cosh r ^ 3 * Real.sinh r *
        fourBridgeOneCoeff G J hf w x y z +
      Real.cosh r ^ 2 * Real.sinh r ^ 2 *
        fourBridgeTwoCoeff G J hf w x y z +
      Real.cosh r * Real.sinh r ^ 3 *
        fourBridgeThreeCoeff G J hf w x y z +
      Real.sinh r ^ 4 * fourBridgeFourCoeff G J hf w x y z := by
  rw [replicaBridgeMoment_highTemp]
  have hpowerset : (Finset.univ : Finset (Fin 4)).powerset =
      {∅, {0}, {1}, {2}, {3}, {0, 1}, {0, 2}, {0, 3},
        {1, 2}, {1, 3}, {2, 3}, {0, 1, 2}, {0, 1, 3},
        {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}} := by
    decide
  rw [hpowerset]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  have hm (S : Finset (Fin 4)) (f : ConfigSpace V -> Real)
      (h : forall s, replicaBridgeMonomial (fourBridgeSites w x y z) S s = f s) :
      replicaBridgeMonomial (fourBridgeSites w x y z) S = f := funext h
  rw [hm ∅ (fun _ => 1) (by intro s; simp [replicaBridgeMonomial]),
    hm {0} (fun s => spin s w) (by
      intro s; simp [replicaBridgeMonomial]),
    hm {1} (fun s => spin s x) (by
      intro s; simp [replicaBridgeMonomial]),
    hm {2} (fun s => spin s y) (by
      intro s; simp [replicaBridgeMonomial]),
    hm {3} (fun s => spin s z) (by
      intro s; simp [replicaBridgeMonomial]),
    hm {0, 1} (fun s => spin s w * spin s x) (by
      intro s; simp [replicaBridgeMonomial]),
    hm {0, 2} (fun s => spin s w * spin s y) (by
      intro s; simp [replicaBridgeMonomial]),
    hm {0, 3} (fun s => spin s w * spin s z) (by
      intro s; simp [replicaBridgeMonomial]),
    hm {1, 2} (fun s => spin s x * spin s y) (by
      intro s; simp [replicaBridgeMonomial]),
    hm {1, 3} (fun s => spin s x * spin s z) (by
      intro s; simp [replicaBridgeMonomial]),
    hm {2, 3} (fun s => spin s y * spin s z) (by
      intro s; simp [replicaBridgeMonomial]),
    hm {0, 1, 2} (fun s => spin s w * (spin s x * spin s y)) (by
      intro s; simp [replicaBridgeMonomial]),
    hm {0, 1, 3} (fun s => spin s w * (spin s x * spin s z)) (by
      intro s; simp [replicaBridgeMonomial]),
    hm {0, 2, 3} (fun s => spin s w * (spin s y * spin s z)) (by
      intro s; simp [replicaBridgeMonomial]),
    hm {1, 2, 3} (fun s => spin s x * (spin s y * spin s z)) (by
      intro s; simp [replicaBridgeMonomial]),
    hm {0, 1, 2, 3}
      (fun s => spin s w * (spin s x * (spin s y * spin s z))) (by
        intro s; simp [replicaBridgeMonomial])]
  have hc02 : #({0, 2} : Finset (Fin 4)) = 2 := by decide
  have hc03 : #({0, 3} : Finset (Fin 4)) = 2 := by decide
  have hc12 : #({1, 2} : Finset (Fin 4)) = 2 := by decide
  have hc13 : #({1, 3} : Finset (Fin 4)) = 2 := by decide
  have hc23 : #({2, 3} : Finset (Fin 4)) = 2 := by decide
  have hc012 : #({0, 1, 2} : Finset (Fin 4)) = 3 := by decide
  have hc013 : #({0, 1, 3} : Finset (Fin 4)) = 3 := by decide
  have hc023 : #({0, 2, 3} : Finset (Fin 4)) = 3 := by decide
  have hc123 : #({1, 2, 3} : Finset (Fin 4)) = 3 := by decide
  have hc0123 : #({0, 1, 2, 3} : Finset (Fin 4)) = 4 := by decide
  rw [hc02, hc03, hc12, hc13, hc23, hc012, hc013, hc023, hc123, hc0123]
  norm_num [expJ_one,
    fourBridgeOneCoeff,
    fourBridgeTwoCoeff, fourBridgeThreeCoeff, fourBridgeFourCoeff]
  ring


theorem replicaBridgeMoment_fourBridgeSites_eq_factor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) (r : Real) :
    replicaBridgeMoment G J hf (fourBridgeSites w x y z) r =
      Real.cosh r ^ 4 *
        (1 + fourBridgeOneCoeff G J hf w x y z * Real.tanh r +
          fourBridgeTwoCoeff G J hf w x y z * Real.tanh r ^ 2 +
          fourBridgeThreeCoeff G J hf w x y z * Real.tanh r ^ 3 +
          fourBridgeFourCoeff G J hf w x y z * Real.tanh r ^ 4) := by
  rw [replicaBridgeMoment_fourBridgeSites_eq]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos r).ne']



theorem replicaBridgeMean_fourBridgeSites_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) (r : Real) :
    replicaBridgeMean G J hf (fourBridgeSites w x y z) r =
      fourBridgeTiltMean (Real.tanh r)
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) := by
  let a := fourBridgeOneCoeff G J hf w x y z
  let b := fourBridgeTwoCoeff G J hf w x y z
  let c := fourBridgeThreeCoeff G J hf w x y z
  let d := fourBridgeFourCoeff G J hf w x y z
  let t := Real.tanh r
  let P : Real -> Real := fun u =>
    1 + a * u + b * u ^ 2 + c * u ^ 3 + d * u ^ 4
  have hfactor (u : Real) :
      replicaBridgeMoment G J hf (fourBridgeSites w x y z) u =
        Real.cosh u ^ 4 * P (Real.tanh u) := by
    simpa [a, b, c, d, P] using
      replicaBridgeMoment_fourBridgeSites_eq_factor G J hf w x y z u
  have hc4 : 0 < Real.cosh r ^ 4 := pow_pos (Real.cosh_pos r) 4
  have hPpos : 0 < P t := by
    have hm := replicaBridgeMoment_pos G J hf (fourBridgeSites w x y z) r
    rw [hfactor] at hm
    exact pos_of_mul_pos_right hm hc4.le
  have htderiv : HasDerivAt Real.tanh (1 - t ^ 2) r := by
    have h := hasDerivAt_tanh r
    convert h using 1
    dsimp [t]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos r).ne']
    nlinarith [Real.cosh_sq_sub_sinh_sq r]
  have hPouter : HasDerivAt P
      (a + 2 * b * t + 3 * c * t ^ 2 + 4 * d * t ^ 3) t := by
    dsimp [P]
    convert ((((hasDerivAt_const t 1).add
      ((hasDerivAt_id t).const_mul a)).add
      (((hasDerivAt_id t).pow 2).const_mul b)).add
      (((hasDerivAt_id t).pow 3).const_mul c)).add
      (((hasDerivAt_id t).pow 4).const_mul d) using 1 <;>
      simp [id_eq] <;> ring
  have hPcomp := hPouter.comp r htderiv
  have hcosh4 : HasDerivAt (fun u => Real.cosh u ^ 4)
      (4 * Real.cosh r ^ 3 * Real.sinh r) r := by
    convert (Real.hasDerivAt_cosh r).pow 4 using 1 <;> ring
  have hprod := hcosh4.mul hPcomp
  have hclosed : HasDerivAt
      (fun u => Real.log (Real.cosh u ^ 4 * P (Real.tanh u)))
      (fourBridgeTiltMean t a b c d) r := by
    have hlog := hprod.log (mul_ne_zero hc4.ne' hPpos.ne')
    convert hlog using 1
    change fourBridgeTiltMean t a b c d =
      (4 * Real.cosh r ^ 3 * Real.sinh r * P t +
          Real.cosh r ^ 4 *
            ((a + 2 * b * t + 3 * c * t ^ 2 + 4 * d * t ^ 3) *
              (1 - t ^ 2))) /
        (Real.cosh r ^ 4 * P t)
    let C := Real.cosh r
    let S := Real.sinh r
    let den := P t
    let q := a + 2 * b * t + 3 * c * t ^ 2 + 4 * d * t ^ 3
    have hC : C ≠ 0 := (Real.cosh_pos r).ne'
    have hden : den ≠ 0 := hPpos.ne'
    change 4 * t + (1 - t ^ 2) * q / den =
      (4 * C ^ 3 * S * den + C ^ 4 * (q * (1 - t ^ 2))) /
        (C ^ 4 * den)
    rw [show t = S / C by
      dsimp [t, S, C]
      exact Real.tanh_eq_sinh_div_cosh r]
    field_simp [hC, hden]
  have hnative :=
    hasDerivAt_log_replicaBridgeMoment G J hf (fourBridgeSites w x y z) r
  have hfun :
      (fun u => Real.log
        (replicaBridgeMoment G J hf (fourBridgeSites w x y z) u)) =
      (fun u => Real.log (Real.cosh u ^ 4 * P (Real.tanh u))) := by
    funext u
    rw [hfactor]
  rw [hfun] at hnative
  simpa [a, b, c, d, t] using hnative.unique hclosed



theorem replicaBridgeVariance_fourBridgeSites_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) (r : Real) :
    replicaBridgeVariance G J hf (fourBridgeSites w x y z) r =
      fourBridgeTiltVariance (Real.tanh r)
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) := by
  let a := fourBridgeOneCoeff G J hf w x y z
  let b := fourBridgeTwoCoeff G J hf w x y z
  let c := fourBridgeThreeCoeff G J hf w x y z
  let d := fourBridgeFourCoeff G J hf w x y z
  let t := Real.tanh r
  have hmeanfun :
      replicaBridgeMean G J hf (fourBridgeSites w x y z) =
        fun u => fourBridgeTiltMean (Real.tanh u) a b c d := by
    funext u
    simpa [a, b, c, d] using
      replicaBridgeMean_fourBridgeSites_eq G J hf w x y z u
  have hmoment := replicaBridgeMoment_pos G J hf (fourBridgeSites w x y z) r
  have hfactor := replicaBridgeMoment_fourBridgeSites_eq_factor
    G J hf w x y z r
  have hc4 : 0 < Real.cosh r ^ 4 := pow_pos (Real.cosh_pos r) 4
  have hP : 1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4 ≠ 0 := by
    rw [hfactor] at hmoment
    have hmoment' :
        0 < Real.cosh r ^ 4 *
          (1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4) := by
      simpa [a, b, c, d, t] using hmoment
    exact (pos_of_mul_pos_right hmoment' hc4.le).ne'
  have hclosed := hasDerivAt_fourBridgeTiltMean_tanh r a b c d hP
  have hnative :=
    hasDerivAt_replicaBridgeMean G J hf (fourBridgeSites w x y z) r
  rw [hmeanfun] at hnative
  simpa [a, b, c, d, t] using hnative.unique hclosed



theorem replicaBridgeVariance_fourBridgeSites_le_neg_iff_skew
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V)
    {r : Real} (hr : 0 < r) :
    replicaBridgeVariance G J hf (fourBridgeSites w x y z) r <=
        replicaBridgeVariance G J hf (fourBridgeSites w x y z) (-r) <->
      fourBridgeVarianceSkewPolynomial (Real.tanh r)
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) <= 0 := by
  let a := fourBridgeOneCoeff G J hf w x y z
  let b := fourBridgeTwoCoeff G J hf w x y z
  let c := fourBridgeThreeCoeff G J hf w x y z
  let d := fourBridgeFourCoeff G J hf w x y z
  let t := Real.tanh r
  have ht0 : 0 < t := by
    dsimp [t]
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hr) (Real.cosh_pos r)
  have ht1 : t < 1 := Real.tanh_lt_one r
  have hcosh4 : 0 < Real.cosh r ^ 4 := pow_pos (Real.cosh_pos r) 4
  have hPp : 1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4 ≠ 0 := by
    have hm := replicaBridgeMoment_pos G J hf (fourBridgeSites w x y z) r
    rw [replicaBridgeMoment_fourBridgeSites_eq_factor] at hm
    have hm' :
        0 < Real.cosh r ^ 4 *
          (1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4) := by
      simpa [a, b, c, d, t] using hm
    exact (pos_of_mul_pos_right hm' hcosh4.le).ne'
  have hPm : 1 - a * t + b * t ^ 2 - c * t ^ 3 + d * t ^ 4 ≠ 0 := by
    have hm := replicaBridgeMoment_pos G J hf (fourBridgeSites w x y z) (-r)
    rw [replicaBridgeMoment_fourBridgeSites_eq_factor] at hm
    simp only [Real.cosh_neg, Real.tanh_neg] at hm
    have hm' :
        0 < Real.cosh r ^ 4 *
          (1 - a * t + b * t ^ 2 - c * t ^ 3 + d * t ^ 4) := by
      ring_nf at hm ⊢
      simpa [a, b, c, d, t] using hm
    exact (pos_of_mul_pos_right hm' hcosh4.le).ne'
  rw [replicaBridgeVariance_fourBridgeSites_eq,
    replicaBridgeVariance_fourBridgeSites_eq]
  simp only [Real.tanh_neg]
  simpa [a, b, c, d, t] using
    (fourBridgeTiltVariance_le_neg_iff ht0 ht1 hPp hPm)


theorem fourBridge_allDisagreementCoefficient_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) :
    0 <= 1 - fourBridgeOneCoeff G J hf w x y z +
      fourBridgeTwoCoeff G J hf w x y z -
      fourBridgeThreeCoeff G J hf w x y z +
      fourBridgeFourCoeff G J hf w x y z := by
  let F : ConfigSpace V -> ConfigSpace V -> Real := fun a b =>
    (1 - spin a w * spin b w) * (1 - spin a x * spin b x) *
      (1 - spin a y * spin b y) * (1 - spin a z * spin b z)
  have hfactor (a b : ConfigSpace V) (v : V) :
      0 <= 1 - spin a v * spin b v := by
    rcases spin_eq_pm a v with ha | ha <;>
      rcases spin_eq_pm b v with hb | hb <;> simp [ha, hb]
  have hF : forall a b, 0 <= F a b := by
    intro a b
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (hfactor a b w) (hfactor a b x))
        (hfactor a b y)) (hfactor a b z)
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
      (1 : Real) -
        (spin a w * spin b w + spin a x * spin b x +
          spin a y * spin b y + spin a z * spin b z) +
        ((spin a w * spin a x) * (spin b w * spin b x) +
          (spin a w * spin a y) * (spin b w * spin b y) +
          (spin a w * spin a z) * (spin b w * spin b z) +
          (spin a x * spin a y) * (spin b x * spin b y) +
          (spin a x * spin a z) * (spin b x * spin b z) +
          (spin a y * spin a z) * (spin b y * spin b z)) -
        ((spin a w * (spin a x * spin a y)) *
            (spin b w * (spin b x * spin b y)) +
          (spin a w * (spin a x * spin a z)) *
            (spin b w * (spin b x * spin b z)) +
          (spin a w * (spin a y * spin a z)) *
            (spin b w * (spin b y * spin b z)) +
          (spin a x * (spin a y * spin a z)) *
            (spin b x * (spin b y * spin b z))) +
        (spin a w * (spin a x * (spin a y * spin a z))) *
          (spin b w * (spin b x * (spin b y * spin b z))) := by
    funext a b
    dsimp [F]
    ring
  rw [hfun] at hnonneg
  have ghsiExp2_sub_local
      (A B : ConfigSpace V -> ConfigSpace V -> Real) :
      ghsiExp2 G J hf (fun a b => A a b - B a b) =
        ghsiExp2 G J hf A - ghsiExp2 G J hf B := by
    rw [show (fun a b => A a b - B a b) =
        (fun a b => A a b + (-1 : Real) * B a b) by
      funext a b
      ring,
      ghsiExp2_add, ghsiExp2_const_mul]
    ring
  simp only [ghsiExp2_add, ghsiExp2_sub_local,
    ghsiExp2_factor] at hnonneg
  have hone : ghsiExp2 G J hf (fun _ _ => (1 : Real)) = 1 := by
    have h := ghsiExp2_factor G J hf
      (fun _ => (1 : Real)) (fun _ => (1 : Real))
    simpa [expJ_one G J hf] using h
  rw [hone] at hnonneg
  dsimp [fourBridgeOneCoeff, fourBridgeTwoCoeff,
    fourBridgeThreeCoeff, fourBridgeFourCoeff]
  linarith




theorem fourBridgeRankMass_zero_le_four
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) :
    fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 0 <=
      fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 4 := by
  have ha : 0 <= fourBridgeOneCoeff G J hf w x y z := by
    unfold fourBridgeOneCoeff
    positivity
  have hc : 0 <= fourBridgeThreeCoeff G J hf w x y z := by
    unfold fourBridgeThreeCoeff
    positivity
  simp only [fourBridgeRankMass]
  linarith



theorem fourBridgeRankMass_two_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) :
    0 <= fourBridgeRankMass
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 2 := by
  let Xw : ConfigSpace V -> ConfigSpace V -> Real := fun a b =>
    spin a w * spin b w
  let Xx : ConfigSpace V -> ConfigSpace V -> Real := fun a b =>
    spin a x * spin b x
  let Xy : ConfigSpace V -> ConfigSpace V -> Real := fun a b =>
    spin a y * spin b y
  let Xz : ConfigSpace V -> ConfigSpace V -> Real := fun a b =>
    spin a z * spin b z
  let F : ConfigSpace V -> ConfigSpace V -> Real := fun a b =>
    (1 + Xw a b) * (1 + Xx a b) * (1 - Xy a b) * (1 - Xz a b) +
    (1 + Xw a b) * (1 + Xy a b) * (1 - Xx a b) * (1 - Xz a b) +
    (1 + Xw a b) * (1 + Xz a b) * (1 - Xx a b) * (1 - Xy a b) +
    (1 + Xx a b) * (1 + Xy a b) * (1 - Xw a b) * (1 - Xz a b) +
    (1 + Xx a b) * (1 + Xz a b) * (1 - Xw a b) * (1 - Xy a b) +
    (1 + Xy a b) * (1 + Xz a b) * (1 - Xw a b) * (1 - Xx a b)
  have hpm (a b : ConfigSpace V) (v : V) :
      0 <= 1 + spin a v * spin b v ∧
        0 <= 1 - spin a v * spin b v := by
    rcases spin_eq_pm a v with ha | ha <;>
      rcases spin_eq_pm b v with hb | hb <;> simp [ha, hb]
  have hF : forall a b, 0 <= F a b := by
    intro a b
    obtain ⟨hwp, hwm⟩ := hpm a b w
    obtain ⟨hxp, hxm⟩ := hpm a b x
    obtain ⟨hyp, hym⟩ := hpm a b y
    obtain ⟨hzp, hzm⟩ := hpm a b z
    dsimp [F, Xw, Xx, Xy, Xz]
    positivity
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
      (6 : Real) +
        (-2) * ((spin a w * spin a x) * (spin b w * spin b x)) +
        (-2) * ((spin a w * spin a y) * (spin b w * spin b y)) +
        (-2) * ((spin a w * spin a z) * (spin b w * spin b z)) +
        (-2) * ((spin a x * spin a y) * (spin b x * spin b y)) +
        (-2) * ((spin a x * spin a z) * (spin b x * spin b z)) +
        (-2) * ((spin a y * spin a z) * (spin b y * spin b z)) +
        6 * ((spin a w * (spin a x * (spin a y * spin a z))) *
          (spin b w * (spin b x * (spin b y * spin b z)))) := by
    funext a b
    dsimp [F, Xw, Xx, Xy, Xz]
    ring
  rw [hfun] at hnonneg
  simp only [ghsiExp2_add, ghsiExp2_const_mul, ghsiExp2_factor] at hnonneg
  have hconst : ghsiExp2 G J hf (fun _ _ => (6 : Real)) = 6 := by
    have hone := ghsiExp2_factor G J hf
      (fun _ => (1 : Real)) (fun _ => (1 : Real))
    have hone' : ghsiExp2 G J hf (fun _ _ => (1 : Real)) = 1 := by
      simpa [expJ_one G J hf] using hone
    calc
      ghsiExp2 G J hf (fun _ _ => (6 : Real)) =
          6 * ghsiExp2 G J hf (fun _ _ => (1 : Real)) := by
        rw [show (fun _ _ : ConfigSpace V => (6 : Real)) =
            (fun _ _ => (6 : Real) * 1) by funext a b; ring,
          ghsiExp2_const_mul]
      _ = 6 := by rw [hone']; ring
  rw [hconst] at hnonneg
  simp only [fourBridgeRankMass]
  dsimp [fourBridgeTwoCoeff, fourBridgeFourCoeff]
  nlinarith


theorem fourBridgeVarianceSkewBernsteinCoeff_five_factor
    (a b c d : Real) :
    fourBridgeVarianceSkewBernsteinCoeff a b c d 5 =
      (1 - a + b - c + d) * (1 + a + b + c + d) *
        (2 * a * b + 3 * a * d - 3 * a - b * c - 6 * c) / 3 := by
  unfold fourBridgeVarianceSkewBernsteinCoeff
  ring


theorem fourBridgeVarianceSkewBernsteinCoeff_six_factor
    (a b c d : Real) :
    fourBridgeVarianceSkewBernsteinCoeff a b c d 6 =
      (1 - a + b - c + d) * (1 + a + b + c + d) *
        (a * b + 3 * a * d - a - b * c + c * d - 3 * c) := by
  unfold fourBridgeVarianceSkewBernsteinCoeff
  ring



theorem fourBridgeVarianceSkewBernsteinCoeff_five_six_nonpos_of_rankCross
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V)
    (hcross :
      fourBridgeRankMass
          (fourBridgeOneCoeff G J hf w x y z)
          (fourBridgeTwoCoeff G J hf w x y z)
          (fourBridgeThreeCoeff G J hf w x y z)
          (fourBridgeFourCoeff G J hf w x y z) 0 *
        fourBridgeRankMass
          (fourBridgeOneCoeff G J hf w x y z)
          (fourBridgeTwoCoeff G J hf w x y z)
          (fourBridgeThreeCoeff G J hf w x y z)
          (fourBridgeFourCoeff G J hf w x y z) 3 <=
      fourBridgeRankMass
          (fourBridgeOneCoeff G J hf w x y z)
          (fourBridgeTwoCoeff G J hf w x y z)
          (fourBridgeThreeCoeff G J hf w x y z)
          (fourBridgeFourCoeff G J hf w x y z) 1 *
        fourBridgeRankMass
          (fourBridgeOneCoeff G J hf w x y z)
          (fourBridgeTwoCoeff G J hf w x y z)
          (fourBridgeThreeCoeff G J hf w x y z)
          (fourBridgeFourCoeff G J hf w x y z) 4) :
    fourBridgeVarianceSkewBernsteinCoeff
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 5 <= 0 ∧
      fourBridgeVarianceSkewBernsteinCoeff
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 6 <= 0 := by
  let a := fourBridgeOneCoeff G J hf w x y z
  let b := fourBridgeTwoCoeff G J hf w x y z
  let c := fourBridgeThreeCoeff G J hf w x y z
  let d := fourBridgeFourCoeff G J hf w x y z
  have h2 : 0 <= fourBridgeRankMass a b c d 2 := by
    simpa [a, b, c, d] using fourBridgeRankMass_two_nonneg G J hf w x y z
  have h04 : fourBridgeRankMass a b c d 0 <=
      fourBridgeRankMass a b c d 4 := by
    simpa [a, b, c, d] using fourBridgeRankMass_zero_le_four G J hf w x y z
  have hcross' : fourBridgeRankMass a b c d 0 *
        fourBridgeRankMass a b c d 3 <=
      fourBridgeRankMass a b c d 1 *
        fourBridgeRankMass a b c d 4 := by
    simpa [a, b, c, d] using hcross
  obtain ⟨hq5, hq6⟩ :=
    fourBridge_endpointFactors_nonpos_of_rank h2 h04 hcross'
  have hminus : 0 <= 1 - a + b - c + d := by
    simpa [a, b, c, d] using
      fourBridge_allDisagreementCoefficient_nonneg G J hf w x y z
  have hplus : 0 <= 1 + a + b + c + d := by
    dsimp [a, b, c, d, fourBridgeOneCoeff, fourBridgeTwoCoeff,
      fourBridgeThreeCoeff, fourBridgeFourCoeff]
    positivity
  rw [fourBridgeVarianceSkewBernsteinCoeff_five_factor,
    fourBridgeVarianceSkewBernsteinCoeff_six_factor]
  constructor
  · exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hminus hplus) hq5)
      (by norm_num)
  · exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hminus hplus) hq6

end

end StatMech.Ising
