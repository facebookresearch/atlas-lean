/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.LebowitzPfisterZeroFieldSheet
import Code.Ising.LebowitzPfisterTwoBondUpper

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


@[simp] theorem replicaBridgeInteraction_unit
    (x : V) (a b : ConfigSpace V) :
    replicaBridgeInteraction (fun _ : Unit => x) a b =
      spin a x * spin b x := by
  simp [replicaBridgeInteraction]



theorem replicaBridgeMoment_unit_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x : V) (r : Real) :
    replicaBridgeMoment G J hf (fun _ : Unit => x) r =
      Real.cosh r +
        (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 * Real.sinh r := by
  let m := expJ G.edgeFinset J hf (fun s => spin s x)
  have hexpand :
      (fun a b : ConfigSpace V =>
        Real.exp (r * replicaBridgeInteraction (fun _ : Unit => x) a b)) =
      (fun a b => Real.cosh r +
        Real.sinh r * (spin a x * spin b x)) := by
    funext a b
    rw [replicaBridgeInteraction_unit]
    have hq : spin a x * spin b x = 1 ∨
        spin a x * spin b x = -1 := by
      rcases spin_eq_pm a x with ha | ha
      · rcases spin_eq_pm b x with hb | hb
        · left; rw [ha, hb]; norm_num
        · right; rw [ha, hb]; norm_num
      · rcases spin_eq_pm b x with hb | hb
        · right; rw [ha, hb]; norm_num
        · left; rw [ha, hb]; norm_num
    rw [exp_mul_pm r _ hq]
    ring
  have hone : ghsiExp2 G J hf (fun _ _ => (1 : Real)) = 1 := by
    have hfun : (fun _ _ : ConfigSpace V => (1 : Real)) =
        (fun _ _ => (1 : Real) * 1) := by funext a b; ring
    rw [hfun, ghsiExp2_factor, expJ_one]
    norm_num
  have hconst (c : Real) :
      ghsiExp2 G J hf (fun _ _ => c) = c := by
    have hfun : (fun _ _ : ConfigSpace V => c) =
        (fun _ _ => c * (1 : Real)) := by funext a b; ring
    rw [hfun, ghsiExp2_const_mul, hone, mul_one]
  unfold replicaBridgeMoment
  rw [hexpand, ghsiExp2_add, hconst,
    ghsiExp2_const_mul, ghsiExp2_factor]
  ring


theorem replicaBridgeMean_unit_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x : V) (r : Real) :
    replicaBridgeMean G J hf (fun _ : Unit => x) r =
      (Real.sinh r +
          (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 * Real.cosh r) /
        (Real.cosh r +
          (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 * Real.sinh r) := by
  let m := expJ G.edgeFinset J hf (fun s => spin s x)
  have hexpand :
      (fun a b : ConfigSpace V =>
        replicaBridgeInteraction (fun _ : Unit => x) a b *
          Real.exp (r * replicaBridgeInteraction (fun _ : Unit => x) a b)) =
      (fun a b => Real.sinh r +
        Real.cosh r * (spin a x * spin b x)) := by
    funext a b
    rw [replicaBridgeInteraction_unit]
    let q := spin a x * spin b x
    have hq : q = 1 ∨ q = -1 := by
      rcases spin_eq_pm a x with ha | ha <;>
        rcases spin_eq_pm b x with hb | hb <;> simp [q, ha, hb]
    have hsq : q ^ 2 = 1 := by rcases hq with hq | hq <;> simp [hq]
    change q * Real.exp (r * q) =
      Real.sinh r + Real.cosh r * q
    rw [exp_mul_pm r q hq]
    calc
      q * (Real.cosh r + q * Real.sinh r) =
          q * Real.cosh r + q ^ 2 * Real.sinh r := by ring
      _ = Real.sinh r + Real.cosh r * q := by rw [hsq]; ring
  have hone : ghsiExp2 G J hf (fun _ _ => (1 : Real)) = 1 := by
    have hfun : (fun _ _ : ConfigSpace V => (1 : Real)) =
        (fun _ _ => (1 : Real) * 1) := by funext a b; ring
    rw [hfun, ghsiExp2_factor, expJ_one]
    norm_num
  have hconst (c : Real) :
      ghsiExp2 G J hf (fun _ _ => c) = c := by
    have hfun : (fun _ _ : ConfigSpace V => c) =
        (fun _ _ => c * (1 : Real)) := by funext a b; ring
    rw [hfun, ghsiExp2_const_mul, hone, mul_one]
  unfold replicaBridgeMean
  rw [hexpand, replicaBridgeMoment_unit_eq,
    ghsiExp2_add, hconst, ghsiExp2_const_mul, ghsiExp2_factor]
  ring



theorem replicaBridgeVariance_unit_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x : V) (r : Real) :
    replicaBridgeVariance G J hf (fun _ : Unit => x) r =
      (1 - (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 4) /
        (Real.cosh r +
          (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 * Real.sinh r) ^ 2 := by
  let m := expJ G.edgeFinset J hf (fun s => spin s x)
  have hsecond :
      ghsiExp2 G J hf (fun a b =>
          replicaBridgeInteraction (fun _ : Unit => x) a b ^ 2 *
            Real.exp (r * replicaBridgeInteraction (fun _ : Unit => x) a b)) =
        replicaBridgeMoment G J hf (fun _ : Unit => x) r := by
    unfold replicaBridgeMoment
    congr 1
    funext a b
    rw [replicaBridgeInteraction_unit]
    have hs : (spin a x * spin b x) ^ 2 = 1 := by
      rcases spin_eq_pm a x with ha | ha <;>
        rcases spin_eq_pm b x with hb | hb <;> simp [ha, hb]
    rw [hs, one_mul]
  unfold replicaBridgeVariance
  rw [hsecond, div_self (replicaBridgeMoment_pos G J hf
    (fun _ : Unit => x) r).ne', replicaBridgeMean_unit_eq]
  change 1 - ((Real.sinh r + m ^ 2 * Real.cosh r) /
      (Real.cosh r + m ^ 2 * Real.sinh r)) ^ 2 =
    (1 - m ^ 4) / (Real.cosh r + m ^ 2 * Real.sinh r) ^ 2
  have hden : Real.cosh r + m ^ 2 * Real.sinh r ≠ 0 := by
    rw [← replicaBridgeMoment_unit_eq]
    exact (replicaBridgeMoment_pos G J hf (fun _ : Unit => x) r).ne'
  have hden' : Real.cosh r + Real.sinh r * m ^ 2 ≠ 0 := by
    simpa [mul_comm] using hden
  have hnumid :
      (Real.cosh r + m ^ 2 * Real.sinh r) ^ 2 -
          (Real.sinh r + m ^ 2 * Real.cosh r) ^ 2 = 1 - m ^ 4 := by
    calc
      (Real.cosh r + m ^ 2 * Real.sinh r) ^ 2 -
          (Real.sinh r + m ^ 2 * Real.cosh r) ^ 2 =
        (1 - m ^ 4) * (Real.cosh r ^ 2 - Real.sinh r ^ 2) := by ring
      _ = 1 - m ^ 4 := by
        rw [Real.cosh_sq_sub_sinh_sq]
        ring
  field_simp [hden, hden']
  nlinarith [hnumid]




theorem replicaBridgeVariance_unit_le_neg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    (x : V) (r : Real) (hr : 0 <= r) :
    replicaBridgeVariance G J hf (fun _ : Unit => x) r <=
      replicaBridgeVariance G J hf (fun _ : Unit => x) (-r) := by
  let m := expJ G.edgeFinset J hf (fun s => spin s x)
  have hm0 : 0 <= m := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf
      (fun e he => hJ e) hhf {x}
    rw [spinProd_singleton] at h
    exact h
  have hm1 : m <= 1 := by
    apply expJ_monomial_le_one
    intro s
    rcases spin_eq_pm s x with hx | hx <;> rw [hx] <;> norm_num
  have ha0 : 0 <= m ^ 2 := sq_nonneg m
  have ha1 : m ^ 2 <= 1 := by nlinarith
  have hs0 : 0 <= Real.sinh r := Real.sinh_nonneg_iff.mpr hr
  have hcp : 0 < Real.cosh r + m ^ 2 * Real.sinh r := by
    positivity
  have hcm : 0 < Real.cosh r - m ^ 2 * Real.sinh r := by
    have hbase : 0 < Real.cosh r - Real.sinh r := by
      rw [Real.cosh_sub_sinh]
      positivity
    nlinarith
  have hnum : 0 <= 1 - m ^ 4 := by nlinarith [sq_nonneg (m ^ 2)]
  rw [replicaBridgeVariance_unit_eq, replicaBridgeVariance_unit_eq,
    Real.cosh_neg, Real.sinh_neg]
  simp only [mul_neg]
  change (1 - m ^ 4) / (Real.cosh r + m ^ 2 * Real.sinh r) ^ 2 <=
    (1 - m ^ 4) / (Real.cosh r - m ^ 2 * Real.sinh r) ^ 2
  have hcross : 0 <= Real.cosh r * (m ^ 2 * Real.sinh r) :=
    mul_nonneg (Real.cosh_pos r).le (mul_nonneg ha0 hs0)
  apply div_le_div_of_nonneg_left hnum (sq_pos_of_pos hcm)
  nlinarith [hcross]



theorem replicaCrossBridgeVariance_unit_same_le_negField
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    (x : V) (r : Real) (hr : 0 <= r) :
    replicaCrossBridgeVariance G J hf hf (fun _ : Unit => x) r <=
      replicaCrossBridgeVariance G J hf (fun v => -hf v)
        (fun _ : Unit => x) r := by
  rw [← replicaBridgeVariance_order_iff_crossField]
  exact replicaBridgeVariance_unit_le_neg G J hf hJ hhf x r hr



theorem replicaBridgeFreeEnergy_unit_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    (x : V) (r : Real) (hr : 0 <= r) :
    replicaBridgeFreeEnergy G J hf (fun _ : Unit => x) r <=
      2 * r *
        (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 := by
  have h := replicaBridgeFreeEnergy_le_of_variance_order G J hf
    (fun _ : Unit => x) r hr (fun t ht =>
      replicaBridgeVariance_unit_le_neg G J hf hJ hhf x t ht)
  simpa using h






theorem twoBridgeVarianceSkewPolynomial_nonneg
    {t A E : Real} (ht0 : 0 <= t) (ht1 : t <= 1)
    (hA0 : 0 <= A) (hE0 : 0 <= E) (hE1 : E <= 1)
    (hAE : A <= 1 + E) :
    0 <= A ^ 2 * E * t ^ 4 - A ^ 2 - E ^ 3 * t ^ 4 -
      3 * E ^ 2 * t ^ 4 + 2 * E ^ 2 * t ^ 2 -
      2 * E * t ^ 2 + 3 * E + 1 := by
  let z := t ^ 2
  let B1 := (1 - E) * (1 + E - A) * (A + E + 1)
  let Q := E * ((E ^ 2 + 3 * E) * z + E ^ 2 + E + 2 -
    A ^ 2 * (z + 1))
  have hz0 : 0 <= z := sq_nonneg t
  have hz1 : z <= 1 := by nlinarith
  have hleft0 : 0 <= 1 - E := sub_nonneg.mpr hE1
  have hmiddle0 : 0 <= 1 + E - A := sub_nonneg.mpr hAE
  have hright0 : 0 <= A + E + 1 := by positivity
  have hB10 : 0 <= B1 := by
    exact mul_nonneg (mul_nonneg hleft0 hmiddle0) hright0
  have hAsq : A ^ 2 <= (1 + E) ^ 2 := by
    exact (sq_le_sq₀ hA0 (by positivity)).2 hAE
  have hzadd : 0 <= z + 1 := by positivity
  have hmul : A ^ 2 * (z + 1) <= (1 + E) ^ 2 * (z + 1) :=
    mul_le_mul_of_nonneg_right hAsq hzadd
  have hbase : 0 <= (E - 1) * (z - 1) :=
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hE1)
      (sub_nonpos.mpr hz1)
  have hbracket :
      0 <= (E ^ 2 + 3 * E) * z + E ^ 2 + E + 2 -
        A ^ 2 * (z + 1) := by
    have hid :
        (E ^ 2 + 3 * E) * z + E ^ 2 + E + 2 -
            (1 + E) ^ 2 * (z + 1) =
          (E - 1) * (z - 1) := by ring
    linarith
  have hQ0 : 0 <= Q := mul_nonneg hE0 hbracket
  have honez : 0 <= 1 - z := sub_nonneg.mpr hz1
  have hsum : 0 <= B1 + (1 - z) * Q :=
    add_nonneg hB10 (mul_nonneg honez hQ0)
  have hid :
      A ^ 2 * E * t ^ 4 - A ^ 2 - E ^ 3 * t ^ 4 -
          3 * E ^ 2 * t ^ 4 + 2 * E ^ 2 * t ^ 2 -
          2 * E * t ^ 2 + 3 * E + 1 =
        B1 + (1 - z) * Q := by
    dsimp [B1, Q, z]
    ring
  rw [hid]
  exact hsum



def twoBridgeTiltVariance (t A E : Real) : Real :=
  (1 - t ^ 2) *
      (A ^ 2 * t ^ 2 - A ^ 2 - 2 * A * E * t + 2 * A * t -
        2 * E ^ 2 * t ^ 2 - 2 * E * t ^ 2 + 2 * E + 2) /
    (1 + A * t + E * t ^ 2) ^ 2



theorem twoBridgeTiltVariance_le_neg
    {t A E : Real} (ht0 : 0 <= t) (ht1 : t < 1)
    (hA0 : 0 <= A) (hE0 : 0 <= E) (hE1 : E <= 1)
    (hAE : A <= 1 + E) :
    twoBridgeTiltVariance t A E <= twoBridgeTiltVariance (-t) A E := by
  let Pp := 1 + A * t + E * t ^ 2
  let Pm := 1 - A * t + E * t ^ 2
  let B := A ^ 2 * E * t ^ 4 - A ^ 2 - E ^ 3 * t ^ 4 -
    3 * E ^ 2 * t ^ 4 + 2 * E ^ 2 * t ^ 2 -
    2 * E * t ^ 2 + 3 * E + 1
  have ht1' : t <= 1 := ht1.le
  have hB : 0 <= B := by
    exact twoBridgeVarianceSkewPolynomial_nonneg ht0 ht1' hA0 hE0 hE1 hAE
  have hPp : 0 < Pp := by
    dsimp [Pp]
    positivity
  have hEtlt : E * t < 1 := by
    exact (mul_le_of_le_one_left ht0 hE1).trans_lt ht1
  have hlower : (1 - t) * (1 - E * t) <= Pm := by
    dsimp [Pm]
    have hm := mul_le_mul_of_nonneg_right hAE ht0
    nlinarith [mul_nonneg hE0 (sq_nonneg t)]
  have hPmlower : 0 < (1 - t) * (1 - E * t) :=
    mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hEtlt)
  have hPm : 0 < Pm := hPmlower.trans_le hlower
  have htquad : 0 <= 1 - t ^ 2 := by nlinarith [sq_nonneg t]
  have htop : 0 <= 4 * A * t * (1 - t ^ 2) * B := by positivity
  have hdiff :
      twoBridgeTiltVariance (-t) A E -
          twoBridgeTiltVariance t A E =
        (4 * A * t * (1 - t ^ 2) * B) / (Pm ^ 2 * Pp ^ 2) := by
    unfold twoBridgeTiltVariance
    simp only [neg_sq, mul_neg, neg_mul]
    rw [show 1 + -(A * t) + E * t ^ 2 = Pm by
      dsimp [Pm]; ring]
    rw [show 1 + A * t + E * t ^ 2 = Pp by rfl]
    field_simp [hPp.ne', hPm.ne']
    dsimp [B]
    ring
  apply sub_nonneg.mp
  rw [hdiff]
  exact div_nonneg htop (mul_nonneg (sq_nonneg Pm) (sq_nonneg Pp))

end

end StatMech.Ising
