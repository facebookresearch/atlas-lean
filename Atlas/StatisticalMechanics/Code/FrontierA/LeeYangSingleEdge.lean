/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierA.LeeYangDisjointUnion

open scoped BigOperators
open Finset Polynomial

namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB


def twoVertexEdge : SimpleGraph (Fin 2) := ⊤

instance : DecidableRel twoVertexEdge.Adj := by
  unfold twoVertexEdge
  infer_instance


theorem twoVertexEdge_edgeFinset :
    twoVertexEdge.edgeFinset = {s(0, 1)} := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
      fin_cases x <;> fin_cases y <;>
        simp [twoVertexEdge, SimpleGraph.mem_edgeFinset]



theorem minusSpinCount_finTwo (s : ConfigSpace (Fin 2)) :
    minusSpinCount s =
      (if s 0 = false then 1 else 0) + (if s 1 = false then 1 else 0) := by
  calc
    minusSpinCount s = ∑ x : Fin 2, if s x = false then 1 else 0 := by
      simp [minusSpinCount]
    _ = _ := by rw [Fin.sum_univ_two]




theorem leeYangPolynomial_twoVertexEdge (beta : ℝ) :
    leeYangPolynomial twoVertexEdge beta =
      C (Real.exp beta) * (1 + X ^ 2) +
        C (2 * Real.exp (-beta)) * X := by
  unfold leeYangPolynomial zeroFieldInteractionWeight
  rw [← Equiv.sum_comp (piFinTwoEquiv fun _ : Fin 2 => Bool).symm]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
  rw [twoVertexEdge_edgeFinset]
  simp_rw [minusSpinCount_finTwo]
  simp only [Fin.isValue, bond, spin, piFinTwoEquiv, Equiv.symm_mk,
    Equiv.coe_fn_mk, mul_ite, mul_one, mul_neg, sum_singleton, Sym2.lift_mk,
    Fin.cons_one, Fin.cons_zero, ↓reduceIte, Bool.true_eq_false, add_zero,
    pow_zero, Bool.false_eq_true, zero_add, pow_one, Fintype.univ_bool,
    neg_neg, mem_singleton, not_false_eq_true, sum_insert, Nat.reduceAdd,
    map_mul]
  rw [Polynomial.C_ofNat]
  ring


theorem leeYangPolynomial_twoVertexEdge_normalized (beta : ℝ) :
    leeYangPolynomial twoVertexEdge beta =
      C (Real.exp beta) *
        (X ^ 2 + C (2 * Real.exp (-2 * beta)) * X + 1) := by
  rw [leeYangPolynomial_twoVertexEdge]
  have hexp : Real.exp beta * (2 * Real.exp (-2 * beta)) =
      2 * Real.exp (-beta) := by
    calc
      Real.exp beta * (2 * Real.exp (-2 * beta)) =
          2 * (Real.exp beta * Real.exp (-2 * beta)) := by ring
      _ = 2 * Real.exp (beta + -2 * beta) := by rw [Real.exp_add]
      _ = 2 * Real.exp (-beta) := by ring_nf
  have hC : C (2 * Real.exp (-beta)) =
      C (Real.exp beta) * C (2 * Real.exp (-2 * beta)) := by
    rw [← map_mul, hexp]
  rw [hC]
  ring


theorem leeYangComplexPolynomial_twoVertexEdge_normalized (beta : ℝ) :
    leeYangComplexPolynomial twoVertexEdge beta =
      C (Real.exp beta : ℂ) *
        (X ^ 2 + C (2 * Real.exp (-2 * beta) : ℂ) * X + 1) := by
  unfold leeYangComplexPolynomial
  rw [leeYangPolynomial_twoVertexEdge_normalized]
  simp


theorem leeYang_twoVertexEdge_root_equation (beta : ℝ) {z : ℂ}
    (hz : (leeYangComplexPolynomial twoVertexEdge beta).eval z = 0) :
    z ^ 2 + (2 * Real.exp (-2 * beta) : ℂ) * z + 1 = 0 := by
  rw [leeYangComplexPolynomial_twoVertexEdge_normalized] at hz
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at hz
  apply (mul_eq_zero.mp hz).resolve_left
  exact_mod_cast Real.exp_ne_zero beta



theorem leeYang_twoVertexEdge_root_norm {beta : ℝ} (hbeta : 0 ≤ beta) {z : ℂ}
    (hz : (leeYangComplexPolynomial twoVertexEdge beta).eval z = 0) :
    ‖z‖ = 1 := by
  let c : ℝ := 2 * Real.exp (-2 * beta)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hc2 : c ≤ 2 := by
    dsimp [c]
    have hneg : -2 * beta ≤ 0 := by linarith
    have hexp : Real.exp (-2 * beta) ≤ 1 := by
      simpa using Real.exp_le_one_iff.mpr hneg
    nlinarith
  have hquad : z ^ 2 + (c : ℂ) * z + 1 = 0 := by
    simpa only [c, Complex.ofReal_mul, Complex.ofReal_ofNat] using
      leeYang_twoVertexEdge_root_equation beta hz
  have hre : z.re ^ 2 - z.im ^ 2 + c * z.re + 1 = 0 := by
    have := congrArg Complex.re hquad
    simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re] at this
    norm_num at this
    nlinarith
  have him : z.im * (2 * z.re + c) = 0 := by
    have := congrArg Complex.im hquad
    simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_im] at this
    norm_num at this
    nlinarith
  have hnormSq : Complex.normSq z = 1 := by
    rw [Complex.normSq_apply]
    rcases mul_eq_zero.mp him with him0 | hlinear
    · have hdisc : (2 * z.re + c) ^ 2 = c ^ 2 - 4 := by
        nlinarith [hre]
      have hdisc_nonneg : 0 ≤ c ^ 2 - 4 := by
        nlinarith [sq_nonneg (2 * z.re + c)]
      have hc_sq : c ^ 2 ≤ 4 := by nlinarith
      have hlin : 2 * z.re + c = 0 := by
        nlinarith [sq_nonneg (2 * z.re + c)]
      nlinarith
    · nlinarith
  rw [Complex.normSq_eq_norm_sq] at hnormSq
  nlinarith [norm_nonneg z]


def HasLeeYangCircle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (beta : ℝ) : Prop :=
  ∀ z : ℂ, (leeYangComplexPolynomial G beta).eval z = 0 → ‖z‖ = 1


theorem HasLeeYangCircle.sum {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] {beta : ℝ}
    (hG : HasLeeYangCircle G beta) (hH : HasLeeYangCircle H beta) :
    HasLeeYangCircle (G ⊕g H) beta := by
  intro z hz
  rw [leeYangComplexPolynomial_sum G H, Polynomial.eval_mul] at hz
  rcases mul_eq_zero.mp hz with hzG | hzH
  · exact hG z hzG
  · exact hH z hzH


theorem hasLeeYangCircle_twoVertexEdge {beta : ℝ} (hbeta : 0 ≤ beta) :
    HasLeeYangCircle twoVertexEdge beta := by
  intro z hz
  exact leeYang_twoVertexEdge_root_norm hbeta hz




def MatchingVertex : ℕ → Type
  | 0 => Empty
  | n + 1 => Fin 2 ⊕ MatchingVertex n

instance matchingVertexFintype (n : ℕ) : Fintype (MatchingVertex n) := by
  induction n with
  | zero =>
      simp only [MatchingVertex]
      infer_instance
  | succ n ih =>
      simp only [MatchingVertex]
      letI : Fintype (MatchingVertex n) := ih
      infer_instance

instance matchingVertexDecidableEq (n : ℕ) : DecidableEq (MatchingVertex n) := by
  induction n with
  | zero =>
      simp only [MatchingVertex]
      infer_instance
  | succ n ih =>
      simp only [MatchingVertex]
      letI : DecidableEq (MatchingVertex n) := ih
      infer_instance


def finiteMatching : (n : ℕ) → SimpleGraph (MatchingVertex n)
  | 0 => ⊥
  | n + 1 => twoVertexEdge ⊕g finiteMatching n

instance finiteMatchingDecidableAdj : (n : ℕ) →
    DecidableRel (finiteMatching n).Adj
  | 0 => by
      simp only [finiteMatching]
      infer_instance
  | n + 1 => by
      simp only [finiteMatching]
      letI : DecidableRel (finiteMatching n).Adj := finiteMatchingDecidableAdj n
      infer_instance



theorem leeYangComplexPolynomial_finiteMatching (n : ℕ) (beta : ℝ) :
    leeYangComplexPolynomial (finiteMatching n) beta =
      (leeYangComplexPolynomial twoVertexEdge beta) ^ n := by
  induction n with
  | zero =>
      change leeYangComplexPolynomial (⊥ : SimpleGraph Empty) beta = _
      rw [leeYangComplexPolynomial_bot]
      simp
  | succ n ih =>
      change leeYangComplexPolynomial (twoVertexEdge ⊕g finiteMatching n) beta = _
      rw [leeYangComplexPolynomial_sum, ih, pow_succ]
      ring



theorem finiteMatching_hasLeeYangCircle (n : ℕ) {beta : ℝ} (hbeta : 0 ≤ beta) :
    HasLeeYangCircle (finiteMatching n) beta := by
  induction n with
  | zero =>
      intro z hz
      exact leeYangComplexPolynomial_bot_root_norm beta hz
  | succ n ih =>
      simpa only [finiteMatching] using
        HasLeeYangCircle.sum twoVertexEdge (finiteMatching n)
          (hasLeeYangCircle_twoVertexEdge hbeta) ih

end StatMech.FrontierA
