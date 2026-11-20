/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Ising.LebowitzPfisterSingleBondUpper
import Code.Ising.GHSInhomogeneous
import Code.Sharpness.Simon

open Set
open scoped BigOperators

namespace StatMech.Ising

noncomputable section

open StatMech.Sharpness




def twoBondInterfaceFreeEnergy (K m1 m2 c : Real) : Real :=
  let t := Real.tanh K
  Real.log ((1 + t * (m1 ^ 2 + m2 ^ 2) + t ^ 2 * c ^ 2) /
    (1 - t * (m1 ^ 2 + m2 ^ 2) + t ^ 2 * c ^ 2))



theorem twoBond_skew_ratio_le_product
    {t a b e : Real}
    (ht0 : 0 <= t) (ht1 : t < 1)
    (ha0 : 0 <= a) (ha1 : a <= 1)
    (hb0 : 0 <= b) (hb1 : b <= 1)
    (he : a * b <= e) :
    (1 + t * (a + b) + t ^ 2 * e) /
        (1 - t * (a + b) + t ^ 2 * e) <=
      ((1 + t * a) / (1 - t * a)) *
        ((1 + t * b) / (1 - t * b)) := by
  have hta : 0 <= t * a := mul_nonneg ht0 ha0
  have htb : 0 <= t * b := mul_nonneg ht0 hb0
  have hta1 : t * a < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right ht0 ha1) ht1
  have htb1 : t * b < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right ht0 hb1) ht1
  have hda : 0 < 1 - t * a := sub_pos.mpr hta1
  have hdb : 0 < 1 - t * b := sub_pos.mpr htb1
  have hdprod : 0 < (1 - t * a) * (1 - t * b) := mul_pos hda hdb
  have ht2 : 0 <= t ^ 2 := sq_nonneg t
  have hdenLower :
      (1 - t * a) * (1 - t * b) <=
        1 - t * (a + b) + t ^ 2 * e := by
    have heTerm : t ^ 2 * (a * b) <= t ^ 2 * e :=
      mul_le_mul_of_nonneg_left he ht2
    nlinarith
  have hden : 0 < 1 - t * (a + b) + t ^ 2 * e :=
    hdprod.trans_le hdenLower
  have hbaseDen : 0 < 1 - t * (a + b) + t ^ 2 * (a * b) := by
    convert hdprod using 1 <;> ring
  have heTerm : t ^ 2 * (a * b) <= t ^ 2 * e :=
    mul_le_mul_of_nonneg_left he ht2
  have hmono :
      (1 + t * (a + b) + t ^ 2 * e) /
          (1 - t * (a + b) + t ^ 2 * e) <=
        (1 + t * (a + b) + t ^ 2 * (a * b)) /
          (1 - t * (a + b) + t ^ 2 * (a * b)) := by
    rw [div_le_div_iff₀ hden hbaseDen]
    nlinarith [mul_nonneg ht0 (add_nonneg ha0 hb0)]
  calc
    (1 + t * (a + b) + t ^ 2 * e) /
        (1 - t * (a + b) + t ^ 2 * e) <=
      (1 + t * (a + b) + t ^ 2 * (a * b)) /
        (1 - t * (a + b) + t ^ 2 * (a * b)) := hmono
    _ = ((1 + t * a) / (1 - t * a)) *
        ((1 + t * b) / (1 - t * b)) := by
      rw [show 1 + t * (a + b) + t ^ 2 * (a * b) =
          (1 + t * a) * (1 + t * b) by ring,
        show 1 - t * (a + b) + t ^ 2 * (a * b) =
          (1 - t * a) * (1 - t * b) by ring,
        mul_div_mul_comm]


theorem twoBondInterfaceFreeEnergy_le
    {K m1 m2 c : Real} (hK : 0 <= K)
    (hm10 : 0 <= m1) (hm11 : m1 <= 1)
    (hm20 : 0 <= m2) (hm21 : m2 <= 1)
    (hc0 : 0 <= c) (hc1 : c <= 1)
    (hgks : m1 * m2 <= c) :
    twoBondInterfaceFreeEnergy K m1 m2 c <=
      2 * K * (m1 ^ 2 + m2 ^ 2) := by
  let t := Real.tanh K
  let a := m1 ^ 2
  let b := m2 ^ 2
  let e := c ^ 2
  have ht0 : 0 <= t := by
    dsimp [t]
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hK) (Real.cosh_pos K).le
  have ht1 : t < 1 := Real.tanh_lt_one K
  have ha0 : 0 <= a := sq_nonneg m1
  have ha1 : a <= 1 := by nlinarith
  have hb0 : 0 <= b := sq_nonneg m2
  have hb1 : b <= 1 := by nlinarith
  have he0 : 0 <= e := sq_nonneg c
  have he1 : e <= 1 := by nlinarith
  have hab : a * b <= e := by
    dsimp [a, b, e]
    have hs := mul_self_le_mul_self (mul_nonneg hm10 hm20) hgks
    nlinarith
  have hratio := twoBond_skew_ratio_le_product
    ht0 ht1 ha0 ha1 hb0 hb1 hab
  have hda : 0 < 1 - t * a := by
    apply sub_pos.mpr
    exact lt_of_le_of_lt (mul_le_of_le_one_right ht0 ha1) ht1
  have hdb : 0 < 1 - t * b := by
    apply sub_pos.mpr
    exact lt_of_le_of_lt (mul_le_of_le_one_right ht0 hb1) ht1
  have hfa :
      Real.log ((1 + t * a) / (1 - t * a)) <= 2 * K * a := by
    simpa [singleBondInterfaceFreeEnergy, t, mul_comm] using
      (singleBondInterfaceFreeEnergy_le hK ha0 ha1 zero_le_one le_rfl)
  have hfb :
      Real.log ((1 + t * b) / (1 - t * b)) <= 2 * K * b := by
    simpa [singleBondInterfaceFreeEnergy, t, mul_comm] using
      (singleBondInterfaceFreeEnergy_le hK hb0 hb1 zero_le_one le_rfl)
  have hrightPosA : 0 < (1 + t * a) / (1 - t * a) :=
    div_pos (by nlinarith [mul_nonneg ht0 ha0]) hda
  have hrightPosB : 0 < (1 + t * b) / (1 - t * b) :=
    div_pos (by nlinarith [mul_nonneg ht0 hb0]) hdb
  have hleftDen : 0 < 1 - t * (a + b) + t ^ 2 * e := by
    have hp : 0 < (1 - t * a) * (1 - t * b) := mul_pos hda hdb
    have heTerm : t ^ 2 * (a * b) <= t ^ 2 * e :=
      mul_le_mul_of_nonneg_left hab (sq_nonneg t)
    nlinarith
  have hleftPos : 0 <
      (1 + t * (a + b) + t ^ 2 * e) /
        (1 - t * (a + b) + t ^ 2 * e) := by
    apply div_pos
    · nlinarith [mul_nonneg ht0 (add_nonneg ha0 hb0),
        mul_nonneg (sq_nonneg t) he0]
    · exact hleftDen
  have hlog := Real.log_le_log hleftPos hratio
  rw [Real.log_mul hrightPosA.ne' hrightPosB.ne'] at hlog
  unfold twoBondInterfaceFreeEnergy
  dsimp only
  change Real.log ((1 + t * (a + b) + t ^ 2 * e) /
      (1 - t * (a + b) + t ^ 2 * e)) <= 2 * K * (a + b)
  linarith



variable {V : Type*} [Fintype V] [DecidableEq V]



def twoReplicaTwoBridgeMoment
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y : V) (r : Real) : Real :=
  ghsiExp2 G J hf (fun a b => Real.exp (r *
    (spin a x * spin b x + spin a y * spin b y)))


def twoReplicaTwoBridgeFreeEnergy
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y : V) (K : Real) : Real :=
  Real.log (twoReplicaTwoBridgeMoment G J hf x y K) -
    Real.log (twoReplicaTwoBridgeMoment G J hf x y (-K))


theorem twoReplicaTwoBridgeMoment_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y : V) (r : Real) :
    twoReplicaTwoBridgeMoment G J hf x y r =
      Real.cosh r ^ 2 +
        (Real.cosh r * Real.sinh r) *
          ((expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 +
            (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2) +
        Real.sinh r ^ 2 *
          (expJ G.edgeFinset J hf
            (fun s => spin s x * spin s y)) ^ 2 := by
  let cx := Real.cosh r
  let sx := Real.sinh r
  have hexpand :
      (fun a b : ConfigSpace V => Real.exp (r *
        (spin a x * spin b x + spin a y * spin b y))) =
      (fun a b =>
        cx ^ 2 * ((1 : Real) * 1) +
          (cx * sx) * (spin a x * spin b x) +
          (cx * sx) * (spin a y * spin b y) +
          sx ^ 2 *
            ((spin a x * spin a y) * (spin b x * spin b y))) := by
    funext a b
    have hx : spin a x * spin b x = 1 ∨
        spin a x * spin b x = -1 := by
      rcases spin_eq_pm a x with ha | ha <;>
        rcases spin_eq_pm b x with hb | hb <;> simp [ha, hb]
    have hy : spin a y * spin b y = 1 ∨
        spin a y * spin b y = -1 := by
      rcases spin_eq_pm a y with ha | ha <;>
        rcases spin_eq_pm b y with hb | hb <;> simp [ha, hb]
    rw [mul_add, Real.exp_add, exp_mul_pm _ _ hx, exp_mul_pm _ _ hy]
    dsimp [cx, sx]
    ring
  have hone : ghsiExp2 G J hf (fun _ _ => (1 : Real)) = 1 := by
    have h := ghsiExp2_factor G J hf
      (fun _ => (1 : Real)) (fun _ => (1 : Real))
    simpa [expJ_one G J hf] using h
  unfold twoReplicaTwoBridgeMoment
  rw [hexpand]
  simp only [ghsiExp2_add, ghsiExp2_const_mul, ghsiExp2_factor]
  rw [hone]
  dsimp [cx, sx]
  ring



theorem expJ_monomial_le_one
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hf : V -> Real)
    (f : ConfigSpace V -> Real) (hfpm : forall s, f s <= 1) :
    expJ E J hf f <= 1 := by
  unfold expJ
  have hZ : 0 < ZJ E J hf := ZJ_pos E J hf
  rw [div_le_one hZ]
  unfold ZJ
  apply Finset.sum_le_sum
  intro s _
  exact mul_le_of_le_one_left (wJ_nonneg E J hf s) (hfpm s)



theorem twoReplicaTwoBridgeFreeEnergy_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y : V) (K : Real) :
    twoReplicaTwoBridgeFreeEnergy G J hf x y K =
      twoBondInterfaceFreeEnergy K
        (expJ G.edgeFinset J hf (fun s => spin s x))
        (expJ G.edgeFinset J hf (fun s => spin s y))
        (expJ G.edgeFinset J hf (fun s => spin s x * spin s y)) := by
  let mx := expJ G.edgeFinset J hf (fun s => spin s x)
  let my := expJ G.edgeFinset J hf (fun s => spin s y)
  let cxy := expJ G.edgeFinset J hf (fun s => spin s x * spin s y)
  let t := Real.tanh K
  let Pplus := 1 + t * (mx ^ 2 + my ^ 2) + t ^ 2 * cxy ^ 2
  let Pminus := 1 - t * (mx ^ 2 + my ^ 2) + t ^ 2 * cxy ^ 2
  have hcosh : 0 < Real.cosh K ^ 2 := sq_pos_of_pos (Real.cosh_pos K)
  have hplus : twoReplicaTwoBridgeMoment G J hf x y K =
      Real.cosh K ^ 2 * Pplus := by
    rw [twoReplicaTwoBridgeMoment_eq]
    dsimp [Pplus, t, mx, my, cxy]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos K).ne']
  have hminus : twoReplicaTwoBridgeMoment G J hf x y (-K) =
      Real.cosh K ^ 2 * Pminus := by
    rw [twoReplicaTwoBridgeMoment_eq]
    dsimp [Pminus, t, mx, my, cxy]
    rw [Real.cosh_neg, Real.sinh_neg, Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos K).ne']
    ring
  have hmoment_pos (r : Real) :
      0 < twoReplicaTwoBridgeMoment G J hf x y r := by
    unfold twoReplicaTwoBridgeMoment ghsiExp2
    apply div_pos
    · apply Finset.sum_pos
      · intro a _
        apply Finset.sum_pos
        · intro b _
          exact mul_pos (mul_pos (wJ_pos _ _ _ _) (wJ_pos _ _ _ _))
            (Real.exp_pos _)
        · exact Finset.univ_nonempty
      · exact Finset.univ_nonempty
    · exact sq_pos_of_pos (ZJ_pos _ _ _)
  have hPplus : 0 < Pplus := by
    have hp := hmoment_pos K
    rw [hplus] at hp
    exact pos_of_mul_pos_right hp hcosh.le
  have hPminus : 0 < Pminus := by
    have hp := hmoment_pos (-K)
    rw [hminus] at hp
    exact pos_of_mul_pos_right hp hcosh.le
  unfold twoReplicaTwoBridgeFreeEnergy twoBondInterfaceFreeEnergy
  rw [hplus, hminus, Real.log_mul hcosh.ne' hPplus.ne',
    Real.log_mul hcosh.ne' hPminus.ne']
  dsimp [Pplus, Pminus, t, mx, my, cxy]
  rw [Real.log_div hPplus.ne' hPminus.ne']
  ring




theorem twoReplicaTwoBridgeFreeEnergy_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    (x y : V) (hxy : x ≠ y) (K : Real) (hK : 0 <= K) :
    twoReplicaTwoBridgeFreeEnergy G J hf x y K <=
      2 * K *
        ((expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 +
          (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2) := by
  let mx := expJ G.edgeFinset J hf (fun s => spin s x)
  let my := expJ G.edgeFinset J hf (fun s => spin s y)
  let cxy := expJ G.edgeFinset J hf (fun s => spin s x * spin s y)
  have hmx0 : 0 <= mx := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf
      (fun e he => hJ e) hhf {x}
    rw [spinProd_singleton] at h
    exact h
  have hmy0 : 0 <= my := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf
      (fun e he => hJ e) hhf {y}
    rw [spinProd_singleton] at h
    exact h
  have hc0 : 0 <= cxy := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf
      (fun e he => hJ e) hhf {x, y}
    rw [spinProd_pair x y hxy] at h
    exact h
  have hmx1 : mx <= 1 := by
    apply expJ_monomial_le_one
    intro s
    rcases spin_eq_pm s x with h | h <;> rw [h] <;> norm_num
  have hmy1 : my <= 1 := by
    apply expJ_monomial_le_one
    intro s
    rcases spin_eq_pm s y with h | h <;> rw [h] <;> norm_num
  have hc1 : cxy <= 1 := by
    apply expJ_monomial_le_one
    intro s
    rcases spin_eq_pm s x with hx | hx <;>
      rcases spin_eq_pm s y with hy | hy <;> rw [hx, hy] <;> norm_num
  have hgks : mx * my <= cxy := by
    have h := gks_second_J G.edgeFinset J hf
      (fun e he => hJ e) hhf {x} {y}
    rw [spinProd_singleton, spinProd_singleton,
      symmDiff_singleton_pair x y hxy, spinProd_pair x y hxy] at h
    exact h
  rw [twoReplicaTwoBridgeFreeEnergy_eq]
  exact twoBondInterfaceFreeEnergy_le hK hmx0 hmx1 hmy0 hmy1 hc0 hc1 hgks

end

end StatMech.Ising
