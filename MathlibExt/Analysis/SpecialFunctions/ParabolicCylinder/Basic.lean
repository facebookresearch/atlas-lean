/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# The normalized parabolic-cylinder function U

For complex a,z, use U(a,z)=D_(-a-1/2)(z). Writing M(α,β,w) for the ordinary confluent
hypergeometric function at β=1/2 or 3/2, the definition is

U(a,z)=2^(-a/2-1/4) exp(-z²/4) [ sqrt(π)/Γ(a/2+3/4) M(a/2+1/4,1/2,z²/2) - z sqrt(2π)/Γ(a/2+1/4)
M(a/2+3/4,3/2,z²/2)].

Each M is Γ(β) times its regularized confluent series. Powers of 2 use the principal logarithm;
reciprocal Gamma factors vanish at Gamma poles. For every a, U is entire in z and satisfies
U''=(z²/4+a)U, with the specified initial values at z=0.

## References

The confluent-hypergeometric expression is DLMF §12.4 together with §12.7(iv), and the initial
values at `z=0` are in §12.2. Helfgott, *Major arcs for Goldbach's problem*, arXiv:1305.2897v4,
§3.2, equation (3.8), uses this normalization in the Gaussian Mellin formulation; its integral
representation is proved in the companion module.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Complex

namespace Complex

/-- **Coefficient of a regularized confluent hypergeometric series.** For `a,b∈ℂ` and `n∈ℕ`,
the coefficient with singleton numerator and denominator multisets is `(a)_n / [n!
Γ(b+n)]`, where `(a)_n` is the ascending Pochhammer polynomial evaluated at `a`. Division
and Gamma are totalized; no exclusion of Gamma poles is assumed. -/
theorem regularizedHGFunCoeff_singleton_eq (a b : ℂ) (n : ℕ) :
    regularizedHGFunCoeff ({a} : Multiset ℂ) ({b} : Multiset ℂ) n =
      (ascPochhammer ℂ n).eval a / ((n.factorial : ℂ) * Gamma (b + n)) := by
  simp [regularizedHGFunCoeff]

/-- **Global sum of a regularized confluent hypergeometric series.** For all `a,b,z∈ℂ`, the
series `∑_{n≥0} regularizedHGFunCoeff({a},{b},n) z^n` has sum
`regularizedHGFun({a},{b},z)`. One numerator and one denominator parameter give infinite
convergence radius. The regularized coefficients retain the reciprocal-Gamma convention at
poles. -/
theorem hasSum_regularizedHGFun_singleton (a b z : ℂ) :
    HasSum (fun n : ℕ =>
      regularizedHGFunCoeff ({a} : Multiset ℂ) ({b} : Multiset ℂ) n * z ^ n)
      (regularizedHGFun ({a} : Multiset ℂ) ({b} : Multiset ℂ) z) := by
  have hr : (regularizedHGFunSeries ({a} : Multiset ℂ) ({b} : Multiset ℂ)).radius = ⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  have h := (regularizedHGFunSeries ({a} : Multiset ℂ) ({b} : Multiset ℂ)).hasSum
    (x := z) (by simp [hr])
  simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, regularizedHGFunSeries_coeff,
    smul_eq_mul, mul_comm, regularizedHGFun] using h

end Complex

private def cf (a b : ℂ) (n : ℕ) : ℂ :=
  regularizedHGFunCoeff ({a} : Multiset ℂ) ({b} : Multiset ℂ) n

private lemma cf_succ (a b : ℂ) (n : ℕ) :
    (n + 1 : ℂ) * cf a b (n + 1) = a * cf (a + 1) (b + 1) n := by
  unfold cf
  rw [regularizedHGFunCoeff_singleton_eq, regularizedHGFunCoeff_singleton_eq,
    ascPochhammer_succ_left, Nat.factorial_succ]
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [show b + 1 + (n : ℂ) = b + ((n : ℂ) + 1) by ring]
  simp only [div_eq_mul_inv, mul_inv]
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  calc
    _ = ((n + 1 : ℂ) * (n + 1 : ℂ)⁻¹) *
        (a * (ascPochhammer ℂ n).eval (a + 1) *
          (n.factorial : ℂ)⁻¹ * (Gamma (b + (n + 1)))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hn]; ring

private lemma hasDerivAt_regularizedConfluent (a b z : ℂ) :
    HasDerivAt (regularizedHGFun ({a} : Multiset ℂ) ({b} : Multiset ℂ))
      (a * regularizedHGFun ({a + 1} : Multiset ℂ) ({b + 1} : Multiset ℂ) z) z := by
  let p := regularizedHGFunSeries ({a} : Multiset ℂ) ({b} : Multiset ℂ)
  have hr : p.radius = ⊤ := radius_regularizedHGFunSeries_eq_top (by simp)
  have hdr : p.derivSeries.radius = ⊤ := by
    apply top_le_iff.mp
    simpa only [hr] using p.radius_le_radius_derivSeries
  have hd := (p.hasFDerivAt_sum (x := z) (by simp [hr])).hasDerivAt
  have hs := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).hasSum
    (p.derivSeries.hasSum (x := z) (by simp [hdr]))
  have hcf : ∀ n : ℕ, (p.derivSeries n (fun _ => z)) 1 =
      a * (cf (a + 1) (b + 1) n * z ^ n) := by
    intro n
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
    simp only [smul_apply, smul_eq_mul, p.derivSeries_coeff_one,
      nsmul_eq_mul, p, regularizedHGFunSeries_coeff, Nat.cast_add, Nat.cast_one]
    change z ^ n * ((n + 1 : ℂ) * cf a b (n + 1)) = _
    rw [cf_succ]
    ring
  have heq : (fun n : ℕ => (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ))
      (p.derivSeries n (fun _ => z))) = fun n : ℕ => a * (cf (a + 1) (b + 1) n * z ^ n) := by
    funext n
    exact hcf n
  rw [heq] at hs
  have he := hs.unique ((hasSum_regularizedHGFun_singleton (a + 1) (b + 1) z).mul_left a)
  change (p.derivSeries.sum z) 1 = _ at he
  rw [he] at hd
  exact hd

private lemma cf_kummer (a b : ℂ) (n : ℕ) :
    (n + 1 : ℂ) * (n + b) * cf a b (n + 1) = (n + a) * cf a b n := by
  unfold cf
  rw [regularizedHGFunCoeff_singleton_eq, regularizedHGFunCoeff_singleton_eq,
    ascPochhammer_succ_eval, Nat.factorial_succ]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv]
  rw [show b + ((n : ℂ) + 1) = b + (n : ℂ) + 1 by ring]
  rw [one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (b + n)]
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  calc
    _ = ((n + 1 : ℂ) * (n + 1 : ℂ)⁻¹) *
      ((n + b) * (n + a) * (ascPochhammer ℂ n).eval a *
        (n.factorial : ℂ)⁻¹ * (Gamma (b + n + 1))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hn]; ring

private lemma cf_succ_succ (a b : ℂ) (n : ℕ) :
    (n + 2 : ℂ) * (n + 1) * cf a b (n + 2) =
      a * (a + 1) * cf (a + 2) (b + 2) n := by
  calc
    _ = (n + 1 : ℂ) * ((n + 2) * cf a b (n + 2)) := by ring
    _ = (n + 1 : ℂ) * (a * cf (a + 1) (b + 1) (n + 1)) := by
      rw [show n + 2 = (n + 1) + 1 by omega]
      have h := congrArg (fun x : ℂ => (n + 1) * x) (cf_succ a b (n + 1))
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h
    _ = a * ((n + 1 : ℂ) * cf (a + 1) (b + 1) (n + 1)) := by ring
    _ = a * ((a + 1) * cf ((a + 1) + 1) ((b + 1) + 1) n) := by rw [cf_succ]
    _ = _ := by
      rw [show (a + 1) + 1 = a + 2 by ring, show (b + 1) + 1 = b + 2 by ring]
      ring

private lemma cf_deriv_hasSum (a b z : ℂ) :
    HasSum (fun n : ℕ => (n + 1 : ℂ) * cf a b (n + 1) * z ^ n)
      (a * regularizedHGFun ({a + 1} : Multiset ℂ) ({b + 1} : Multiset ℂ) z) := by
  have h := (hasSum_regularizedHGFun_singleton (a + 1) (b + 1) z).mul_left a
  convert h using 1
  funext n
  rw [cf_succ]
  dsimp only [cf]
  ring

private lemma cf_deriv_deriv_hasSum (a b z : ℂ) :
    HasSum (fun n : ℕ => (n + 2 : ℂ) * (n + 1) * cf a b (n + 2) * z ^ n)
      (a * (a + 1) * regularizedHGFun ({a + 2} : Multiset ℂ) ({b + 2} : Multiset ℂ) z) := by
  have h := (hasSum_regularizedHGFun_singleton (a + 2) (b + 2) z).mul_left (a * (a + 1))
  convert h using 1
  funext n
  rw [cf_succ_succ]
  dsimp only [cf]
  ring

private lemma regularizedConfluent_ode (a b z : ℂ) :
    z * (a * (a + 1) * regularizedHGFun ({a + 2} : Multiset ℂ) ({b + 2} : Multiset ℂ) z) +
      (b - z) * (a * regularizedHGFun ({a + 1} : Multiset ℂ) ({b + 1} : Multiset ℂ) z) -
      a * regularizedHGFun ({a} : Multiset ℂ) ({b} : Multiset ℂ) z = 0 := by
  let vA := fun n : ℕ => (n : ℂ) * (n + 1) * cf a b (n + 1) * z ^ n
  let vC := fun n : ℕ => (n : ℂ) * cf a b n * z ^ n
  have hAtail : HasSum (fun n : ℕ => vA (n + 1))
      (z * (a * (a + 1) * regularizedHGFun ({a + 2} : Multiset ℂ) ({b + 2} : Multiset ℂ) z)) := by
    convert (cf_deriv_deriv_hasSum a b z).mul_left z using 1
    funext n
    dsimp only [vA]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, pow_succ]
    ring
  have hA := hAtail.zero_add
  have hvA : vA 0 = 0 := by simp [vA]
  rw [hvA, zero_add] at hA
  have hCtail : HasSum (fun n : ℕ => vC (n + 1))
      (z * (a * regularizedHGFun ({a + 1} : Multiset ℂ) ({b + 1} : Multiset ℂ) z)) := by
    convert (cf_deriv_hasSum a b z).mul_left z using 1
    funext n
    dsimp only [vC]
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  have hC := hCtail.zero_add
  have hvC : vC 0 = 0 := by simp [vC]
  rw [hvC, zero_add] at hC
  have hB := (cf_deriv_hasSum a b z).mul_left b
  have hD := (hasSum_regularizedHGFun_singleton a b z).mul_left a
  have h := ((hA.add hB).sub hC).sub hD
  have heq : (fun n : ℕ =>
      (vA n + b * ((n + 1 : ℂ) * cf a b (n + 1) * z ^ n) - vC n) -
        a * (cf a b n * z ^ n)) = fun _ : ℕ => (0 : ℂ) := by
    funext n
    dsimp only [vA, vC]
    calc
      _ = ((n + 1 : ℂ) * (n + b) * cf a b (n + 1) - (n + a) * cf a b n) * z ^ n := by
        ring
      _ = 0 := by rw [cf_kummer]; ring
  simp only [cf] at heq h
  rw [heq] at h
  have hzero := h.unique hasSum_zero
  convert hzero using 1; ring



/-- For complex a,b,z, m(a,b,z) = Γ(b) times the regularized confluent
hypergeometric function with numerator a and denominator b. At b=1/2
or b=3/2 this is the ordinary confluent hypergeometric function M(a,b,z). -/
private abbrev m (a b z : ℂ) : ℂ :=
  Gamma b * regularizedHGFun ({a} : Multiset ℂ) ({b} : Multiset ℂ) z

private abbrev m1 (a b z : ℂ) : ℂ :=
  Gamma b * a * regularizedHGFun ({a + 1} : Multiset ℂ) ({b + 1} : Multiset ℂ) z

private abbrev m2 (a b z : ℂ) : ℂ :=
  Gamma b * a * (a + 1) * regularizedHGFun ({a + 2} : Multiset ℂ) ({b + 2} : Multiset ℂ) z

private lemma deriv_m (a b z : ℂ) : deriv (m a b) z = m1 a b z := by
  rw [show m a b = fun w : ℂ => Gamma b * regularizedHGFun ({a} : Multiset ℂ) ({b} : Multiset ℂ) w
    by rfl]
  have h := (hasDerivAt_regularizedConfluent a b z).const_mul (Gamma b)
  simpa only [m1, mul_assoc] using h.deriv

private lemma deriv_m1 (a b z : ℂ) : deriv (m1 a b) z = m2 a b z := by
  rw [show m1 a b = fun w : ℂ =>
    (Gamma b * a) * regularizedHGFun ({a + 1} : Multiset ℂ) ({b + 1} : Multiset ℂ) w by rfl]
  have h := (hasDerivAt_regularizedConfluent (a + 1) (b + 1) z).const_mul (Gamma b * a)
  rw [show (a + 1) + 1 = a + 2 by ring, show (b + 1) + 1 = b + 2 by ring] at h
  simpa only [m2, mul_assoc] using h.deriv

private lemma m_ode (a b z : ℂ) : z * m2 a b z + (b - z) * m1 a b z - a * m a b z = 0 := by
  have h := congrArg (fun w : ℂ => Gamma b * w) (regularizedConfluent_ode a b z)
  dsimp only [m, m1, m2]
  convert h using 1 <;> ring

private lemma analyticAt_m (a b z : ℂ) : AnalyticAt ℂ (m a b) z := by
  exact analyticAt_const.mul (analyticAt_regularizedHGFun_of_card_le (by simp) z)

private lemma analyticAt_m1 (a b z : ℂ) : AnalyticAt ℂ (m1 a b) z := by
  exact analyticAt_const.mul (analyticAt_regularizedHGFun_of_card_le (by simp) z)

private abbrev gaussianFactor (z : ℂ) : ℂ := exp (-(z ^ 2) / 4)

private lemma analyticAt_gaussianFactor (z : ℂ) : AnalyticAt ℂ gaussianFactor z := by
  unfold gaussianFactor
  fun_prop

private lemma deriv_gaussianFactor (z : ℂ) :
    deriv gaussianFactor z = -(z / 2) * gaussianFactor z := by
  have h := (Complex.hasDerivAt_exp (-(z ^ 2) / 4)).comp z
    (((hasDerivAt_id z).pow 2).neg.div_const 4)
  have hd := h.deriv
  simp only [Function.comp_def, Pi.pow_apply, Pi.neg_apply, id_eq,
    Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one] at hd
  change deriv (fun w : ℂ => exp (-(w ^ 2) / 4)) z = _
  calc
    _ = _ := hd
    _ = _ := by unfold gaussianFactor; ring

private def evenWeber (a z : ℂ) : ℂ := gaussianFactor z * m a (1 / 2) (z ^ 2 / 2)

private def oddWeber (a z : ℂ) : ℂ := gaussianFactor z * z * m a (3 / 2) (z ^ 2 / 2)

private abbrev evenFirst (a z : ℂ) : ℂ :=
  gaussianFactor z * (z * m1 a (1 / 2) (z ^ 2 / 2) - z / 2 * m a (1 / 2) (z ^ 2 / 2))

private abbrev evenSecond (a z : ℂ) : ℂ :=
  gaussianFactor z * ((z ^ 2 / 4 - 1 / 2) * m a (1 / 2) (z ^ 2 / 2) +
    (1 - z ^ 2) * m1 a (1 / 2) (z ^ 2 / 2) + z ^ 2 * m2 a (1 / 2) (z ^ 2 / 2))

private abbrev oddFirst (a z : ℂ) : ℂ :=
  gaussianFactor z * ((1 - z ^ 2 / 2) * m a (3 / 2) (z ^ 2 / 2) +
    z ^ 2 * m1 a (3 / 2) (z ^ 2 / 2))

private abbrev oddSecond (a z : ℂ) : ℂ :=
  gaussianFactor z * z * ((z ^ 2 / 4 - 3 / 2) * m a (3 / 2) (z ^ 2 / 2) +
    (3 - z ^ 2) * m1 a (3 / 2) (z ^ 2 / 2) + z ^ 2 * m2 a (3 / 2) (z ^ 2 / 2))

private lemma analyticAt_evenWeber (a z : ℂ) : AnalyticAt ℂ (evenWeber a) z := by
  have hg : AnalyticAt ℂ (fun w : ℂ => w ^ 2 / 2) z := by fun_prop
  exact (analyticAt_gaussianFactor z).mul
    ((analyticAt_m a (1 / 2) (z ^ 2 / 2)).comp (f := fun w : ℂ => w ^ 2 / 2) (x := z) hg)

private lemma analyticAt_oddWeber (a z : ℂ) : AnalyticAt ℂ (oddWeber a) z := by
  have hg : AnalyticAt ℂ (fun w : ℂ => w ^ 2 / 2) z := by fun_prop
  exact ((analyticAt_gaussianFactor z).mul analyticAt_id).mul
    ((analyticAt_m a (3 / 2) (z ^ 2 / 2)).comp (f := fun w : ℂ => w ^ 2 / 2) (x := z) hg)

private lemma deriv_evenWeber (a z : ℂ) : deriv (evenWeber a) z = evenFirst a z := by
  have hp := (analyticAt_gaussianFactor z).differentiableAt.hasDerivAt
  rw [deriv_gaussianFactor] at hp
  have hm := (analyticAt_m a (1 / 2) (z ^ 2 / 2)).differentiableAt.hasDerivAt
  rw [deriv_m] at hm
  have hc := hm.comp z (((hasDerivAt_id z).pow 2).div_const 2)
  have h := hp.mul hc
  have hd := h.deriv
  simp only [Function.comp_def, Pi.pow_apply, id_eq,
    Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one] at hd
  change deriv (fun w : ℂ => gaussianFactor w * m a (1 / 2) (w ^ 2 / 2)) z = _
  calc
    _ = _ := hd
    _ = _ := by unfold evenFirst; ring

private lemma deriv_evenFirst (a z : ℂ) : deriv (evenFirst a) z = evenSecond a z := by
  have hp := (analyticAt_gaussianFactor z).differentiableAt.hasDerivAt
  rw [deriv_gaussianFactor] at hp
  have hm := (analyticAt_m a (1 / 2) (z ^ 2 / 2)).differentiableAt.hasDerivAt
  rw [deriv_m] at hm
  have hm1 := (analyticAt_m1 a (1 / 2) (z ^ 2 / 2)).differentiableAt.hasDerivAt
  rw [deriv_m1] at hm1
  have hw := ((hasDerivAt_id z).pow 2).div_const 2
  have hc := hm.comp z hw
  have hc1 := hm1.comp z hw
  have h := hp.mul (((hasDerivAt_id z).mul hc1).sub (((hasDerivAt_id z).div_const 2).mul hc))
  have hd := h.deriv
  simp only [Function.comp_def, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq,
    Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one] at hd
  change deriv (fun w : ℂ => gaussianFactor w *
    (w * m1 a (1 / 2) (w ^ 2 / 2) - w / 2 * m a (1 / 2) (w ^ 2 / 2))) z = _
  calc
    _ = _ := hd
    _ = _ := by unfold evenSecond; ring

private lemma deriv_oddWeber (a z : ℂ) : deriv (oddWeber a) z = oddFirst a z := by
  have hp := (analyticAt_gaussianFactor z).differentiableAt.hasDerivAt
  rw [deriv_gaussianFactor] at hp
  have hm := (analyticAt_m a (3 / 2) (z ^ 2 / 2)).differentiableAt.hasDerivAt
  rw [deriv_m] at hm
  have hc := hm.comp z (((hasDerivAt_id z).pow 2).div_const 2)
  have h := (hp.mul (hasDerivAt_id z)).mul hc
  have hd := h.deriv
  simp only [Function.comp_def, Pi.mul_apply, Pi.pow_apply, id_eq,
    Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one] at hd
  change deriv (fun w : ℂ => gaussianFactor w * w * m a (3 / 2) (w ^ 2 / 2)) z = _
  calc
    _ = _ := hd
    _ = _ := by unfold oddFirst; ring

private lemma deriv_oddFirst (a z : ℂ) : deriv (oddFirst a) z = oddSecond a z := by
  have hp := (analyticAt_gaussianFactor z).differentiableAt.hasDerivAt
  rw [deriv_gaussianFactor] at hp
  have hm := (analyticAt_m a (3 / 2) (z ^ 2 / 2)).differentiableAt.hasDerivAt
  rw [deriv_m] at hm
  have hm1 := (analyticAt_m1 a (3 / 2) (z ^ 2 / 2)).differentiableAt.hasDerivAt
  rw [deriv_m1] at hm1
  have hw := ((hasDerivAt_id z).pow 2).div_const 2
  have hc := hm.comp z hw
  have hc1 := hm1.comp z hw
  have h := hp.mul ((((hasDerivAt_const z (1 : ℂ)).sub hw).mul hc).add
    (((hasDerivAt_id z).pow 2).mul hc1))
  have hd := h.deriv
  simp only [Function.comp_def, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Pi.add_apply, id_eq,
    Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one] at hd
  change deriv (fun w : ℂ => gaussianFactor w *
    ((1 - w ^ 2 / 2) * m a (3 / 2) (w ^ 2 / 2) + w ^ 2 * m1 a (3 / 2) (w ^ 2 / 2))) z = _
  calc
    _ = _ := hd
    _ = _ := by unfold oddSecond; ring

private lemma evenSecond_eq (a z : ℂ) :
    evenSecond a z = (z ^ 2 / 4 + 2 * a - 1 / 2) * evenWeber a z := by
  have hc : z ^ 2 * m2 a (1 / 2) (z ^ 2 / 2) +
      (1 - z ^ 2) * m1 a (1 / 2) (z ^ 2 / 2) = 2 * a * m a (1 / 2) (z ^ 2 / 2) := by
    calc
      _ = 2 * (z ^ 2 / 2 * m2 a (1 / 2) (z ^ 2 / 2) +
          (1 / 2 - z ^ 2 / 2) * m1 a (1 / 2) (z ^ 2 / 2) - a * m a (1 / 2) (z ^ 2 / 2)) +
          2 * a * m a (1 / 2) (z ^ 2 / 2) := by ring
      _ = _ := by rw [m_ode]; ring
  change gaussianFactor z * _ = _ * (gaussianFactor z * m a (1 / 2) (z ^ 2 / 2))
  calc
    _ = gaussianFactor z * ((z ^ 2 / 4 - 1 / 2) * m a (1 / 2) (z ^ 2 / 2) +
        (z ^ 2 * m2 a (1 / 2) (z ^ 2 / 2) + (1 - z ^ 2) * m1 a (1 / 2) (z ^ 2 / 2))) := by ring
    _ = _ := by rw [hc]; ring

private lemma oddSecond_eq (a z : ℂ) :
    oddSecond a z = (z ^ 2 / 4 + 2 * a - 3 / 2) * oddWeber a z := by
  have hc : z ^ 2 * m2 a (3 / 2) (z ^ 2 / 2) +
      (3 - z ^ 2) * m1 a (3 / 2) (z ^ 2 / 2) = 2 * a * m a (3 / 2) (z ^ 2 / 2) := by
    calc
      _ = 2 * (z ^ 2 / 2 * m2 a (3 / 2) (z ^ 2 / 2) +
          (3 / 2 - z ^ 2 / 2) * m1 a (3 / 2) (z ^ 2 / 2) - a * m a (3 / 2) (z ^ 2 / 2)) +
          2 * a * m a (3 / 2) (z ^ 2 / 2) := by ring
      _ = _ := by rw [m_ode]; ring
  change gaussianFactor z * z * _ = _ * (gaussianFactor z * z * m a (3 / 2) (z ^ 2 / 2))
  calc
    _ = gaussianFactor z * z * ((z ^ 2 / 4 - 3 / 2) * m a (3 / 2) (z ^ 2 / 2) +
        (z ^ 2 * m2 a (3 / 2) (z ^ 2 / 2) + (3 - z ^ 2) * m1 a (3 / 2) (z ^ 2 / 2))) := by ring
    _ = _ := by rw [hc]; ring

private lemma deriv_deriv_evenWeber (a z : ℂ) :
    deriv (deriv (evenWeber a)) z = (z ^ 2 / 4 + 2 * a - 1 / 2) * evenWeber a z := by
  have h : deriv (evenWeber a) = evenFirst a := funext (deriv_evenWeber a)
  rw [h, deriv_evenFirst, evenSecond_eq]

private lemma deriv_deriv_oddWeber (a z : ℂ) :
    deriv (deriv (oddWeber a)) z = (z ^ 2 / 4 + 2 * a - 3 / 2) * oddWeber a z := by
  have h : deriv (oddWeber a) = oddFirst a := funext (deriv_oddWeber a)
  rw [h, deriv_oddFirst, oddSecond_eq]

namespace Complex

/-- For arbitrary complex a,z, U(a,z)=D_(-a-1/2)(z) is defined by
2^(-a/2-1/4) exp(-z²/4) times
[sqrt(π) M(a/2+1/4,1/2,z²/2)/Γ(a/2+3/4)
 - z sqrt(2π) M(a/2+3/4,3/2,z²/2)/Γ(a/2+1/4)].
Here M is Γ(b) times the regularized confluent series at b=1/2 or 3/2.
Positive-base powers use the principal logarithm, and reciprocal Gamma
factors have value zero at Gamma poles. -/
def parabolicCylinderU (a z : ℂ) : ℂ :=
  (2 : ℂ) ^ (-a / 2 - 1 / 4) * exp (-(z ^ 2) / 4) *
    (((Real.sqrt Real.pi : ℂ) / Gamma (a / 2 + 3 / 4)) * Gamma (1 / 2) *
        regularizedHGFun ({a / 2 + 1 / 4} : Multiset ℂ) ({1 / 2} : Multiset ℂ) (z ^ 2 / 2) -
      ((Real.sqrt (2 * Real.pi) : ℂ) / Gamma (a / 2 + 1 / 4)) * z * Gamma (3 / 2) *
        regularizedHGFun ({a / 2 + 3 / 4} : Multiset ℂ) ({3 / 2} : Multiset ℂ) (z ^ 2 / 2))

private lemma parabolicCylinderU_eq_fun (a : ℂ) :
    parabolicCylinderU a = fun z : ℂ => (2 : ℂ) ^ (-a / 2 - 1 / 4) *
      (((Real.sqrt Real.pi : ℂ) / Gamma (a / 2 + 3 / 4)) * evenWeber (a / 2 + 1 / 4) z -
        ((Real.sqrt (2 * Real.pi) : ℂ) / Gamma (a / 2 + 1 / 4)) * oddWeber (a / 2 + 3 / 4) z) := by
  funext z
  unfold parabolicCylinderU evenWeber oddWeber gaussianFactor m
  ring

/-- For every complex a,z, the function w ↦ U(a,w) is complex analytic at z. -/
theorem analyticAt_parabolicCylinderU (a z : ℂ) : AnalyticAt ℂ (parabolicCylinderU a) z := by
  rw [parabolicCylinderU_eq_fun]
  exact analyticAt_const.mul
    ((analyticAt_const.mul (analyticAt_evenWeber (a / 2 + 1 / 4) z)).sub
      (analyticAt_const.mul (analyticAt_oddWeber (a / 2 + 3 / 4) z)))

/-- For every complex order a, the function z ↦ U(a,z) is complex differentiable
throughout ℂ. -/
@[fun_prop]
theorem differentiable_parabolicCylinderU (a : ℂ) : Differentiable ℂ (parabolicCylinderU a) :=
  fun z => (analyticAt_parabolicCylinderU a z).differentiableAt

private lemma deriv_parabolicCylinderU_eq (a z : ℂ) :
    deriv (parabolicCylinderU a) z = (2 : ℂ) ^ (-a / 2 - 1 / 4) *
      (((Real.sqrt Real.pi : ℂ) / Gamma (a / 2 + 3 / 4)) *
          deriv (evenWeber (a / 2 + 1 / 4)) z -
        ((Real.sqrt (2 * Real.pi) : ℂ) / Gamma (a / 2 + 1 / 4)) *
          deriv (oddWeber (a / 2 + 3 / 4)) z) := by
  have he := (analyticAt_evenWeber (a / 2 + 1 / 4) z).differentiableAt.hasDerivAt
  have ho := (analyticAt_oddWeber (a / 2 + 3 / 4) z).differentiableAt.hasDerivAt
  have h := ((he.const_mul ((Real.sqrt Real.pi : ℂ) / Gamma (a / 2 + 3 / 4))).sub
    (ho.const_mul ((Real.sqrt (2 * Real.pi) : ℂ) / Gamma (a / 2 + 1 / 4)))).const_mul
      ((2 : ℂ) ^ (-a / 2 - 1 / 4))
  have hd := h.deriv
  simp only [Pi.sub_apply] at hd
  rw [parabolicCylinderU_eq_fun]
  exact hd

/-- For every complex a,z, the normalized parabolic-cylinder function satisfies
(d²/dz²) U(a,z) = (z²/4+a) U(a,z). -/
theorem deriv_deriv_parabolicCylinderU (a z : ℂ) :
    deriv (deriv (parabolicCylinderU a)) z = (z ^ 2 / 4 + a) * parabolicCylinderU a z := by
  have haE : AnalyticOnNhd ℂ (evenWeber (a / 2 + 1 / 4)) Set.univ :=
    fun w _ => analyticAt_evenWeber (a / 2 + 1 / 4) w
  have haO : AnalyticOnNhd ℂ (oddWeber (a / 2 + 3 / 4)) Set.univ :=
    fun w _ => analyticAt_oddWeber (a / 2 + 3 / 4) w
  have he := (haE.deriv z (by simp)).differentiableAt.hasDerivAt
  have ho := (haO.deriv z (by simp)).differentiableAt.hasDerivAt
  rw [deriv_deriv_evenWeber] at he
  rw [deriv_deriv_oddWeber] at ho
  have h := ((he.const_mul ((Real.sqrt Real.pi : ℂ) / Gamma (a / 2 + 3 / 4))).sub
    (ho.const_mul ((Real.sqrt (2 * Real.pi) : ℂ) / Gamma (a / 2 + 1 / 4)))).const_mul
      ((2 : ℂ) ^ (-a / 2 - 1 / 4))
  have hd := h.deriv
  simp only [Pi.sub_apply] at hd
  have hfun : deriv (parabolicCylinderU a) = fun w : ℂ => (2 : ℂ) ^ (-a / 2 - 1 / 4) *
      (((Real.sqrt Real.pi : ℂ) / Gamma (a / 2 + 3 / 4)) *
          deriv (evenWeber (a / 2 + 1 / 4)) w -
        ((Real.sqrt (2 * Real.pi) : ℂ) / Gamma (a / 2 + 1 / 4)) *
          deriv (oddWeber (a / 2 + 3 / 4)) w) := funext (deriv_parabolicCylinderU_eq a)
  rw [hfun]
  calc
    _ = _ := hd
    _ = _ := by rw [parabolicCylinderU_eq_fun]; ring

private lemma m_zero (a b : ℂ) (hb : Gamma b ≠ 0) : m a b 0 = 1 := by
  simp [m, regularizedHGFun_zero, regularizedHGFunCoeff, hb]

private lemma gamma_half_ne_zero : Gamma (1 / 2 : ℂ) ≠ 0 :=
  Gamma_ne_zero_of_re_pos (by norm_num)

private lemma gamma_three_halves_ne_zero : Gamma (3 / 2 : ℂ) ≠ 0 :=
  Gamma_ne_zero_of_re_pos (by norm_num)

private lemma evenWeber_zero (a : ℂ) : evenWeber a 0 = 1 := by
  simp only [evenWeber, gaussianFactor, zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div,
    exp_zero, one_mul, m_zero a (1 / 2) gamma_half_ne_zero]

private lemma oddWeber_zero (a : ℂ) : oddWeber a 0 = 0 := by
  simp [oddWeber]

private lemma deriv_evenWeber_zero (a : ℂ) : deriv (evenWeber a) 0 = 0 := by
  rw [deriv_evenWeber]
  simp [evenFirst]

private lemma deriv_oddWeber_zero (a : ℂ) : deriv (oddWeber a) 0 = 1 := by
  rw [deriv_oddWeber]
  simp only [oddFirst, gaussianFactor, zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div,
    exp_zero, sub_zero, zero_mul, add_zero, one_mul,
    m_zero a (3 / 2) gamma_three_halves_ne_zero]

private lemma cpow_half_ofReal (x : ℝ) (hx : 0 ≤ x) :
    (x : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt x : ℂ) := by
  rw [Real.sqrt_eq_rpow]
  simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using (ofReal_cpow hx (1 / 2)).symm

private lemma sqrt_two_pi :
    (Real.sqrt (2 * Real.pi) : ℂ) = (Real.sqrt 2 : ℂ) * (Real.sqrt Real.pi : ℂ) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ofReal_mul]

private lemma prefactor_sqrt_two_pi (a : ℂ) :
    (2 : ℂ) ^ (-a / 2 - 1 / 4) * (Real.sqrt (2 * Real.pi) : ℂ) =
      (2 : ℂ) ^ (-a / 2 + 1 / 4) * (Real.sqrt Real.pi : ℂ) := by
  have htwo : (2 : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
    simpa only [ofReal_ofNat] using cpow_half_ofReal 2 (by norm_num)
  calc
    _ = ((2 : ℂ) ^ (-a / 2 - 1 / 4) * (2 : ℂ) ^ (1 / 2 : ℂ)) *
        (Real.sqrt Real.pi : ℂ) := by
      rw [sqrt_two_pi, htwo]
      ring
    _ = (2 : ℂ) ^ ((-a / 2 - 1 / 4) + 1 / 2) * (Real.sqrt Real.pi : ℂ) := by
      rw [cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    _ = _ := by rw [show (-a / 2 - 1 / 4) + 1 / 2 = -a / 2 + 1 / 4 by ring]

/-- For every complex a,
U(a,0)=2^(-a/2-1/4) sqrt(π)/Γ(a/2+3/4).
The formula includes parameters where the reciprocal Gamma factor is zero. -/
theorem parabolicCylinderU_zero (a : ℂ) :
    parabolicCylinderU a 0 =
      (2 : ℂ) ^ (-a / 2 - 1 / 4) * (Real.sqrt Real.pi : ℂ) / Gamma (a / 2 + 3 / 4) := by
  rw [parabolicCylinderU_eq_fun]
  simp only [evenWeber_zero, oddWeber_zero, mul_one, mul_zero, sub_zero]
  ring

/-- For every complex a,
(d/dz) U(a,0)=-2^(-a/2+1/4) sqrt(π)/Γ(a/2+1/4).
The formula includes parameters where the reciprocal Gamma factor is zero. -/
theorem deriv_parabolicCylinderU_zero (a : ℂ) :
    deriv (parabolicCylinderU a) 0 =
      -(2 : ℂ) ^ (-a / 2 + 1 / 4) * (Real.sqrt Real.pi : ℂ) / Gamma (a / 2 + 1 / 4) := by
  rw [deriv_parabolicCylinderU_eq, deriv_evenWeber_zero, deriv_oddWeber_zero]
  simp only [mul_zero, mul_one, zero_sub]
  calc
    _ = -((2 : ℂ) ^ (-a / 2 - 1 / 4) * (Real.sqrt (2 * Real.pi) : ℂ)) /
        Gamma (a / 2 + 1 / 4) := by ring
    _ = _ := by rw [prefactor_sqrt_two_pi]; ring

private lemma regularizedConfluent_zero_parameter (b z : ℂ) :
    regularizedHGFun ({0} : Multiset ℂ) ({b} : Multiset ℂ) z = (Gamma b)⁻¹ := by
  calc
    _ = ∑' n : ℕ, cf 0 b n * z ^ n := (hasSum_regularizedHGFun_singleton 0 b z).tsum_eq.symm
    _ = cf 0 b 0 * z ^ 0 := by
      apply tsum_eq_single 0
      intro n hn
      simp only [cf, regularizedHGFunCoeff_singleton_eq,
        ascPochhammer_ne_zero_eval_zero ℂ hn, zero_div, zero_mul]
    _ = _ := by simp [cf, regularizedHGFunCoeff_singleton_eq]

private lemma m_zero_parameter (b z : ℂ) (hb : Gamma b ≠ 0) : m 0 b z = 1 := by
  rw [m, regularizedConfluent_zero_parameter, mul_inv_cancel₀ hb]

private lemma evenWeber_zero_parameter (z : ℂ) : evenWeber 0 z = gaussianFactor z := by
  rw [evenWeber, m_zero_parameter (1 / 2) _ gamma_half_ne_zero, mul_one]

private lemma oddWeber_zero_parameter (z : ℂ) : oddWeber 0 z = gaussianFactor z * z := by
  rw [oddWeber, m_zero_parameter (3 / 2) _ gamma_three_halves_ne_zero, mul_one]

private lemma sqrt_pi_ne_zero : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'

private lemma gamma_neg_half : Gamma (-1 / 2 : ℂ) = -2 * (Real.sqrt Real.pi : ℂ) := by
  have h := Gamma_add_one (-1 / 2 : ℂ) (by norm_num)
  rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by ring] at h
  calc
    _ = -2 * ((-1 / 2 : ℂ) * Gamma (-1 / 2)) := by ring
    _ = -2 * Gamma (1 / 2) := by rw [← h]
    _ = _ := by
      rw [Gamma_one_half_eq, cpow_half_ofReal Real.pi Real.pi_pos.le]

/-- For every complex z, U(-1/2,z)=exp(-z²/4), the Hermite case D_0(z). -/
theorem parabolicCylinderU_neg_one_half (z : ℂ) :
    parabolicCylinderU (-1 / 2) z = exp (-(z ^ 2) / 4) := by
  rw [parabolicCylinderU_eq_fun]
  norm_num
  rw [evenWeber_zero_parameter, Gamma_one_half_eq,
    cpow_half_ofReal Real.pi Real.pi_pos.le, div_self sqrt_pi_ne_zero, one_mul]

/-- For every complex z, U(-3/2,z)=z exp(-z²/4), the Hermite case D_1(z). -/
theorem parabolicCylinderU_neg_three_halves (z : ℂ) :
    parabolicCylinderU (-3 / 2) z = z * exp (-(z ^ 2) / 4) := by
  have htwo : (2 : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
    simpa only [ofReal_ofNat] using cpow_half_ofReal 2 (by norm_num)
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt (2 * Real.pi) : ℂ) / Gamma (-1 / 2) = -(Real.sqrt 2 : ℂ) / 2 := by
    rw [gamma_neg_half, sqrt_two_pi]
    field_simp [sqrt_pi_ne_zero]
  rw [parabolicCylinderU_eq_fun]
  rw [show -(-3 / 2 : ℂ) / 2 - 1 / 4 = 1 / 2 by ring,
    show (-3 / 2 : ℂ) / 2 + 1 / 4 = -1 / 2 by ring,
    show (-3 / 2 : ℂ) / 2 + 3 / 4 = 0 by ring, Gamma_zero]
  simp only [div_zero, zero_mul, zero_sub]
  rw [oddWeber_zero_parameter, htwo, hc]
  calc
    _ = ((Real.sqrt 2 : ℂ) ^ 2 / 2) * z * gaussianFactor z := by ring
    _ = _ := by rw [hsq]; norm_num

end Complex
