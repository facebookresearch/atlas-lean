/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.PBiasedTensorize
public import MathlibExt.InformationTheory.LogSum

/-!
# Sub-additivity of entropy for Bernoulli product measures

For a nonnegative function `g` on `{0, 1}^n` and the Bernoulli(`p`) product measure with
`0 < p < 1`, the entropy `Ent(g) = 𝔼[g log g] - 𝔼[g] log 𝔼[g]` is at most the sum over the
coordinates of the expected one-coordinate conditional entropies (`esd_subadditivity`). The proof
is by induction on `n`, using the joint convexity of `(a, b) ↦ a log (a / b)` in the form of a
data-processing inequality for the two-point mixture (`esd_dpi`).

## Main definitions

* `StatMech.Probability.esd_Phi`: `x ↦ x log x`.
* `StatMech.Probability.esd_ent`: the entropy `Ent_ν(g)` under a product weight.
* `StatMech.Probability.esd_entCoord`: the conditional entropy of `g` in coordinate `e`, given
  the other coordinates.

## Main results

* `StatMech.Probability.esd_dpi`: entropy of a two-point mixture of expectations is at most the
  expected entropy of the pointwise mixture.
* `StatMech.Probability.esd_subadditivity`: `Ent(g) ≤ ∑ₑ 𝔼[Entₑ(g)]`.

## References

* S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*, Oxford University Press,
  2013, Theorem 4.10.
-/

@[expose] public section

open scoped BigOperators
open Finset
open Real

namespace StatMech.Probability

open StatMech StatMech.OSSS

/-- The function `x ↦ x log x` (with `0 log 0 = 0`). It equals `-Real.negMulLog x`
  (`esd_Phi_eq_neg_negMulLog`). -/
noncomputable def esd_Phi (x : ℝ) : ℝ := x * Real.log x

@[simp] theorem esd_Phi_zero : esd_Phi 0 = 0 := by simp [esd_Phi]

theorem esd_Phi_eq (x : ℝ) : esd_Phi x = x * Real.log x := rfl

/-- `esd_Phi` is the negative of Mathlib's `Real.negMulLog`. -/
theorem esd_Phi_eq_neg_negMulLog (x : ℝ) : esd_Phi x = -Real.negMulLog x := by
  simp [esd_Phi, Real.negMulLog]

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The entropy `Ent_ν(g) = 𝔼_ν[g log g] - 𝔼_ν[g] log 𝔼_ν[g]` of `g` under the product weight `ν`.
-/
noncomputable def esd_ent (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) : ℝ :=
  OSSS.expect ν (fun ω => esd_Phi (g ω)) - esd_Phi (OSSS.expect ν g)

/-- The conditional entropy of `g` in coordinate `e` given the other coordinates, under the
  Bernoulli(`p`) weight: `p Φ(g(ω^{e↦1})) + (1-p) Φ(g(ω^{e↦0})) - Φ(𝔼[g | ω_{≠e}])`, with `Φ(x) =
  x log x`. -/
noncomputable def esd_entCoord (p : ℝ) (g : ConfigSpace E → ℝ) (e : E) (ω : ConfigSpace E) : ℝ :=
  p * esd_Phi (g (StatMech.setOpen e ω)) + (1 - p) * esd_Phi (g (StatMech.setClosed e ω))
    - esd_Phi (OSSS.condMean (OSSS.bernoulliWeight p) e g ω)

/-- Every coordinate weight of `ν` is strictly positive. -/
def esd_PosWeight (ν : E → Bool → ℝ) : Prop := ∀ e b, 0 < ν e b

omit [Fintype E] [DecidableEq E] in
theorem esd_bernoulli_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    esd_PosWeight (E := E) (OSSS.bernoulliWeight p) := by
  intro e b; unfold OSSS.bernoulliWeight; cases b <;> simp <;> linarith

theorem esd_eq_zero_of_expect_zero {ν : E → Bool → ℝ} (hpos : esd_PosWeight ν)
    {g : ConfigSpace E → ℝ} (hg : ∀ ω, 0 ≤ g ω) (h0 : OSSS.expect ν g = 0) :
    ∀ ω, g ω = 0 := by
  intro ω
  unfold OSSS.expect at h0
  have hwpos : ∀ ω', 0 < OSSS.weight ν ω' := fun ω' =>
    Finset.prod_pos (fun e _ => hpos e (ω' e))
  have hterm : ∀ ω' ∈ (Finset.univ : Finset (ConfigSpace E)), 0 ≤ OSSS.weight ν ω' * g ω' :=
    fun ω' _ => mul_nonneg (hwpos ω').le (hg ω')
  have := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp h0 ω (Finset.mem_univ ω)
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (hwpos ω).ne'
  · exact h

theorem esd_dpi_fiber (c0 c1 a0 a1 M0 M1 : ℝ) (hc0 : 0 < c0) (hc1 : 0 < c1)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hM0 : 0 < M0) (hM1 : 0 < M1) :
    (c0*a0+c1*a1) * (Real.log (c0*a0+c1*a1) - Real.log (c0*M0+c1*M1))
      ≤ c0 * a0 * (Real.log a0 - Real.log M0) + c1 * a1 * (Real.log a1 - Real.log M1) := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ c0*a0+c1*a1 by positivity) with hm0 | hm
  · have ha0z : a0 = 0 := by nlinarith [mul_nonneg hc0.le ha0, mul_nonneg hc1.le ha1]
    have ha1z : a1 = 0 := by nlinarith [mul_nonneg hc0.le ha0, mul_nonneg hc1.le ha1]
    rw [ha0z, ha1z]; simp
  · have hLS := Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div (Finset.univ : Finset Bool)
      (fun ε => if ε then c1*a1 else c0*a0) (fun ε => if ε then c1*M1 else c0*M0)
      (by intro ε _; cases ε <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> positivity)
      (by intro ε _; cases ε <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> positivity)
    simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true] at hLS
    have e2 : c0 * a0 * Real.log (c0*a0/(c0*M0)) = c0 * a0 * (Real.log a0 - Real.log M0) := by
      rcases eq_or_lt_of_le ha0 with h | h
      · rw [← h]; ring
      · rw [show c0*a0/(c0*M0) = a0/M0 by field_simp, Real.log_div h.ne' hM0.ne']
    have e3 : c1 * a1 * Real.log (c1*a1/(c1*M1)) = c1 * a1 * (Real.log a1 - Real.log M1) := by
      rcases eq_or_lt_of_le ha1 with h | h
      · rw [← h]; ring
      · rw [show c1*a1/(c1*M1) = a1/M1 by field_simp, Real.log_div h.ne' hM1.ne']
    rw [e2, e3] at hLS
    have e1' : (c1*a1+c0*a0) * Real.log ((c1*a1+c0*a0)/(c1*M1+c0*M0))
        = (c0*a0+c1*a1) * (Real.log (c0*a0+c1*a1) - Real.log (c0*M0+c1*M1)) := by
      rw [show c1*a1+c0*a0 = c0*a0+c1*a1 by ring, show c1*M1+c0*M0 = c0*M0+c1*M1 by ring,
          Real.log_div hm.ne' (by positivity)]
    rw [e1'] at hLS
    linarith [hLS]

theorem esd_dpi_fiber_Phi (c0 c1 a0 a1 M0 M1 : ℝ) (hc0 : 0 < c0) (hc1 : 0 < c1)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hM0 : 0 < M0) (hM1 : 0 < M1) :
    esd_Phi (c0*a0+c1*a1) - (c0*a0+c1*a1) * Real.log (c0*M0+c1*M1)
      ≤ (c0 * esd_Phi a0 + c1 * esd_Phi a1)
        - (c0 * a0 * Real.log M0 + c1 * a1 * Real.log M1) := by
  have h := esd_dpi_fiber c0 c1 a0 a1 M0 M1 hc0 hc1 ha0 ha1 hM0 hM1
  unfold esd_Phi
  nlinarith [h]

theorem esd_Phi_scale (p x : ℝ) (hp : 0 < p) (hx : 0 ≤ x) :
    p * esd_Phi x - esd_Phi (p * x) = - (p * x) * Real.log p := by
  unfold esd_Phi
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]; simp
  · rw [Real.log_mul hp.ne' h.ne']; ring

/-- Data-processing inequality for entropy under a two-point mixture: for nonnegative `g₀, g₁`, `p
  Φ(𝔼 g₁) + (1-p) Φ(𝔼 g₀) - Φ(p 𝔼 g₁ + (1-p) 𝔼 g₀) ≤ 𝔼[p Φ(g₁) + (1-p) Φ(g₀) - Φ(p g₁ + (1-p)
  g₀)]`. -/
theorem esd_dpi {μ : E → Bool → ℝ} (hpos : esd_PosWeight μ)
    (hprob : OSSS.IsProbWeight μ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {g0 g1 : ConfigSpace E → ℝ} (hg0 : ∀ ω, 0 ≤ g0 ω) (hg1 : ∀ ω, 0 ≤ g1 ω) :
    p * esd_Phi (OSSS.expect μ g1) + (1-p) * esd_Phi (OSSS.expect μ g0)
        - esd_Phi (p * OSSS.expect μ g1 + (1-p) * OSSS.expect μ g0)
      ≤ OSSS.expect μ (fun ω => p * esd_Phi (g1 ω) + (1-p) * esd_Phi (g0 ω)
          - esd_Phi (p * g1 ω + (1-p) * g0 ω)) := by
  have hM0nn : 0 ≤ OSSS.expect μ g0 := OSSS.expect_nonneg hprob hg0
  have hM1nn : 0 ≤ OSSS.expect μ g1 := OSSS.expect_nonneg hprob hg1
  rcases eq_or_lt_of_le hM0nn with hM0z | hM0pos
  · have hg0z : ∀ ω, g0 ω = 0 :=
      esd_eq_zero_of_expect_zero hpos hg0 hM0z.symm
    rw [← hM0z]
    simp only [esd_Phi_zero, mul_zero, add_zero]
    rw [esd_Phi_scale p (OSSS.expect μ g1) hp0 hM1nn]
    rw [show (fun ω => p * esd_Phi (g1 ω) + (1-p) * esd_Phi (g0 ω)
        - esd_Phi (p * g1 ω + (1-p) * g0 ω))
        = (fun ω => (-(p * Real.log p)) * g1 ω) from by
          funext ω; rw [hg0z ω]; simp only [esd_Phi_zero, mul_zero, add_zero]
          rw [esd_Phi_scale p (g1 ω) hp0 (hg1 ω)]; ring]
    rw [OSSS.expect_const_mul]
    apply le_of_eq; ring
  rcases eq_or_lt_of_le hM1nn with hM1z | hM1pos
  · have hg1z : ∀ ω, g1 ω = 0 :=
      esd_eq_zero_of_expect_zero hpos hg1 hM1z.symm
    rw [← hM1z]
    simp only [esd_Phi_zero, mul_zero, zero_add]
    rw [esd_Phi_scale (1-p) (OSSS.expect μ g0) (by linarith) hM0nn]
    rw [show (fun ω => p * esd_Phi (g1 ω) + (1-p) * esd_Phi (g0 ω)
        - esd_Phi (p * g1 ω + (1-p) * g0 ω))
        = (fun ω => (-((1-p) * Real.log (1-p))) * g0 ω) from by
          funext ω; rw [hg1z ω]; simp only [esd_Phi_zero, mul_zero, zero_add]
          rw [esd_Phi_scale (1-p) (g0 ω) (by linarith) (hg0 ω)]; ring]
    rw [OSSS.expect_const_mul]
    apply le_of_eq; ring
  set M0 := OSSS.expect μ g0 with hM0d
  set M1 := OSSS.expect μ g1 with hM1d
  set c0 := 1 - p with hc0d
  set c1 := p with hc1d
  set L := Real.log (c0*M0+c1*M1) with hLd
  set S := OSSS.expect μ (fun ω => esd_Phi (c0*g0 ω+c1*g1 ω)) with hSd
  set P0 := OSSS.expect μ (fun ω => esd_Phi (g0 ω)) with hP0d
  set P1 := OSSS.expect μ (fun ω => esd_Phi (g1 ω)) with hP1d
  have hRHS : OSSS.expect μ (fun ω => p * esd_Phi (g1 ω) + (1-p) * esd_Phi (g0 ω)
          - esd_Phi (p * g1 ω + (1-p) * g0 ω))
      = c1 * P1 + c0 * P0 - S := by
    rw [show (fun ω => p * esd_Phi (g1 ω) + (1-p) * esd_Phi (g0 ω)
        - esd_Phi (p * g1 ω + (1-p) * g0 ω))
        = (fun ω => (c1 * esd_Phi (g1 ω) + c0 * esd_Phi (g0 ω)) - esd_Phi (c0*g0 ω+c1*g1 ω)) from by
          funext ω; rw [hc0d, hc1d]; ring_nf]
    rw [OSSS.expect_sub, OSSS.expect_add, OSSS.expect_const_mul, OSSS.expect_const_mul,
        ← hP0d, ← hP1d, ← hSd]
  rw [hRHS]
  have hpt : ∀ ω, esd_Phi (c0*g0 ω+c1*g1 ω) - (c0*g0 ω+c1*g1 ω) * L
      ≤ (c0 * esd_Phi (g0 ω) + c1 * esd_Phi (g1 ω))
        - (c0 * g0 ω * Real.log M0 + c1 * g1 ω * Real.log M1) :=
    fun ω => esd_dpi_fiber_Phi c0 c1 (g0 ω) (g1 ω) M0 M1 (by linarith) hp0 (hg0 ω)
        (hg1 ω) hM0pos hM1pos
  have hmono := OSSS.expect_mono hprob hpt
  rw [OSSS.expect_sub, OSSS.expect_sub, OSSS.expect_add, OSSS.expect_const_mul,
      OSSS.expect_const_mul] at hmono
  rw [← hSd, ← hP0d, ← hP1d] at hmono
  have hEmL : OSSS.expect μ (fun ω => (c0*g0 ω+c1*g1 ω) * L) = (c0*M0+c1*M1) * L := by
    rw [show (fun ω => (c0*g0 ω+c1*g1 ω)*L) = (fun ω => c0*(L*g0 ω) + c1*(L*g1 ω)) from by
          funext ω; ring]
    rw [OSSS.expect_add, OSSS.expect_const_mul, OSSS.expect_const_mul,
        OSSS.expect_const_mul, OSSS.expect_const_mul, ← hM0d, ← hM1d]; ring
  rw [hEmL] at hmono
  have hElog : OSSS.expect μ (fun ω => c0 * g0 ω * Real.log M0 + c1 * g1 ω * Real.log M1)
      = c0 * M0 * Real.log M0 + c1 * M1 * Real.log M1 := by
    rw [show (fun ω => c0 * g0 ω * Real.log M0 + c1 * g1 ω * Real.log M1)
        = (fun ω => (c0 * Real.log M0) * g0 ω + (c1 * Real.log M1) * g1 ω) from by funext ω; ring]
    rw [OSSS.expect_add, OSSS.expect_const_mul, OSSS.expect_const_mul, ← hM0d, ← hM1d]; ring
  rw [hElog] at hmono
  unfold esd_Phi
  have hcomm : p * M1 + (1-p) * M0 = c0*M0+c1*M1 := by rw [hc0d, hc1d]; ring
  rw [hcomm]
  have hLM : (c0*M0+c1*M1) * Real.log (c0*M0+c1*M1) = (c0*M0+c1*M1) * L := by rw [hLd]
  rw [hLM]
  nlinarith [hmono]

theorem esd_setOpen_succ_cons {n : ℕ} (e' : Fin n) (b : Bool) (ω' : Fin n → Bool) :
    StatMech.setOpen (Fin.succ e') (Fin.cons b ω') = Fin.cons b (StatMech.setOpen e' ω') := by
  unfold StatMech.setOpen; funext j; refine Fin.cases ?_ ?_ j
  · simp [Function.update_of_ne (Fin.succ_ne_zero e').symm]
  · intro i; by_cases hi : i = e'
    · subst hi; simp [Function.update_self]
    · rw [Function.update_of_ne (by exact fun h => hi (Fin.succ_injective n h)),
          Fin.cons_succ, Fin.cons_succ, Function.update_of_ne hi]

theorem esd_setClosed_succ_cons {n : ℕ} (e' : Fin n) (b : Bool) (ω' : Fin n → Bool) :
    StatMech.setClosed (Fin.succ e') (Fin.cons b ω') = Fin.cons b (StatMech.setClosed e' ω') := by
  unfold StatMech.setClosed; funext j; refine Fin.cases ?_ ?_ j
  · simp [Function.update_of_ne (Fin.succ_ne_zero e').symm]
  · intro i; by_cases hi : i = e'
    · subst hi; simp [Function.update_self]
    · rw [Function.update_of_ne (by exact fun h => hi (Fin.succ_injective n h)),
          Fin.cons_succ, Fin.cons_succ, Function.update_of_ne hi]

theorem esd_setOpen_zero_cons {n : ℕ} (b : Bool) (ω' : Fin n → Bool) :
    StatMech.setOpen 0 (Fin.cons b ω') = Fin.cons true ω' := by
  unfold StatMech.setOpen; funext j; refine Fin.cases ?_ ?_ j
  · simp
  · intro i; rw [Function.update_of_ne (Fin.succ_ne_zero i), Fin.cons_succ, Fin.cons_succ]

theorem esd_setClosed_zero_cons {n : ℕ} (b : Bool) (ω' : Fin n → Bool) :
    StatMech.setClosed 0 (Fin.cons b ω') = Fin.cons false ω' := by
  unfold StatMech.setClosed; funext j; refine Fin.cases ?_ ?_ j
  · simp
  · intro i; rw [Function.update_of_ne (Fin.succ_ne_zero i), Fin.cons_succ, Fin.cons_succ]

theorem esd_entCoord_succ_cons {n : ℕ} (p : ℝ) (g : (Fin (n + 1) → Bool) → ℝ)
    (e' : Fin n) (b : Bool) (ω' : Fin n → Bool) :
    esd_entCoord p g (Fin.succ e') (Fin.cons b ω')
      = esd_entCoord p (fun ω' => g (Fin.cons b ω')) e' ω' := by
  unfold esd_entCoord OSSS.condMean
  rw [esd_setOpen_succ_cons, esd_setClosed_succ_cons]
  simp only [OSSS.bernoulliWeight, ite_true, Bool.false_eq_true, ite_false]

theorem esd_entCoord_zero_cons {n : ℕ} (p : ℝ) (g : (Fin (n + 1) → Bool) → ℝ)
    (b : Bool) (ω' : Fin n → Bool) :
    esd_entCoord p g 0 (Fin.cons b ω')
      = p * esd_Phi (g (Fin.cons true ω')) + (1-p) * esd_Phi (g (Fin.cons false ω'))
        - esd_Phi (p * g (Fin.cons true ω') + (1-p) * g (Fin.cons false ω')) := by
  unfold esd_entCoord OSSS.condMean
  rw [esd_setOpen_zero_cons, esd_setClosed_zero_cons]
  simp only [OSSS.bernoulliWeight, ite_true, Bool.false_eq_true, ite_false]

theorem esd_entCoord0_expect {n : ℕ} (p : ℝ) (g : (Fin (n + 1) → Bool) → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (esd_entCoord p g 0)
      = OSSS.expect (OSSS.bernoulliWeight p) (fun ω' : Fin n → Bool =>
          p * esd_Phi (g (Fin.cons true ω')) + (1-p) * esd_Phi (g (Fin.cons false ω'))
            - esd_Phi (p * g (Fin.cons true ω') + (1-p) * g (Fin.cons false ω'))) := by
  rw [ptn_expect_cons_split p (esd_entCoord p g 0)]
  rw [show (fun ω' : Fin n → Bool => esd_entCoord p g 0 (Fin.cons false ω'))
      = (fun ω' : Fin n → Bool => p * esd_Phi (g (Fin.cons true ω')) + (1-p)
          * esd_Phi (g (Fin.cons false ω'))
            - esd_Phi (p * g (Fin.cons true ω') + (1-p) * g (Fin.cons false ω'))) from by
        funext ω'; exact esd_entCoord_zero_cons p g false ω']
  rw [show (fun ω' : Fin n → Bool => esd_entCoord p g 0 (Fin.cons true ω'))
      = (fun ω' : Fin n → Bool => p * esd_Phi (g (Fin.cons true ω')) + (1-p)
          * esd_Phi (g (Fin.cons false ω'))
            - esd_Phi (p * g (Fin.cons true ω') + (1-p) * g (Fin.cons false ω'))) from by
        funext ω'; exact esd_entCoord_zero_cons p g true ω']
  ring

theorem esd_entCoordSucc_expect {n : ℕ} (p : ℝ) (g : (Fin (n + 1) → Bool) → ℝ) (e' : Fin n) :
    OSSS.expect (OSSS.bernoulliWeight p) (esd_entCoord p g (Fin.succ e'))
      = (1-p) * OSSS.expect (OSSS.bernoulliWeight p)
          (esd_entCoord p (fun ω' => g (Fin.cons false ω')) e')
        + p * OSSS.expect (OSSS.bernoulliWeight p)
            (esd_entCoord p (fun ω' => g (Fin.cons true ω')) e') := by
  rw [ptn_expect_cons_split p (esd_entCoord p g (Fin.succ e'))]
  rw [show (fun ω' : Fin n → Bool => esd_entCoord p g (Fin.succ e') (Fin.cons false ω'))
      = esd_entCoord p (fun ω' => g (Fin.cons false ω')) e' from by
        funext ω'; exact esd_entCoord_succ_cons p g e' false ω']
  rw [show (fun ω' : Fin n → Bool => esd_entCoord p g (Fin.succ e') (Fin.cons true ω'))
      = esd_entCoord p (fun ω' => g (Fin.cons true ω')) e' from by
        funext ω'; exact esd_entCoord_succ_cons p g e' true ω']

theorem esd_ent_cons_split {n : ℕ} (p : ℝ) (g : (Fin (n + 1) → Bool) → ℝ) :
    esd_ent (OSSS.bernoulliWeight p) g
      = ((1-p) * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω' : Fin n → Bool => esd_Phi (g
          (Fin.cons false ω')))
            - esd_Phi (OSSS.expect (OSSS.bernoulliWeight p) (fun ω' => g (Fin.cons false ω'))))
        + p * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω' : Fin n → Bool => esd_Phi (g
            (Fin.cons true ω')))
            - esd_Phi (OSSS.expect (OSSS.bernoulliWeight p) (fun ω' => g (Fin.cons true ω')))))
      + (p * esd_Phi (OSSS.expect (OSSS.bernoulliWeight p) (fun ω' => g (Fin.cons true ω')))
          + (1-p) * esd_Phi (OSSS.expect (OSSS.bernoulliWeight p) (fun ω' => g (Fin.cons false ω')))
          - esd_Phi ((1-p) * OSSS.expect (OSSS.bernoulliWeight p) (fun ω' => g (Fin.cons false ω'))
              + p * OSSS.expect (OSSS.bernoulliWeight p) (fun ω' => g (Fin.cons true ω')))) := by
  unfold esd_ent
  rw [ptn_expect_cons_split p (fun ω => esd_Phi (g ω)), ptn_expect_cons_split p g]
  ring

theorem esd_ent_fin_zero (p : ℝ) (g : (Fin 0 → Bool) → ℝ) :
    esd_ent (OSSS.bernoulliWeight p) g = 0 := by
  unfold esd_ent OSSS.expect OSSS.weight
  have : (Finset.univ : Finset (Fin 0 → Bool)) = {fun _ => true} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro x _; funext i; exact absurd i.2 (by omega)
  rw [this]
  simp [esd_Phi]

/-- **Sub-additivity (tensorization) of entropy** for the Bernoulli(`p`) product measure on `{0,
  1}^n` (see S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*, 2013, Theorem
  4.10): for nonnegative `g`, `Ent(g) ≤ ∑ₑ 𝔼[Entₑ(g)]`. -/
theorem esd_subadditivity {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (g : (Fin n → Bool) → ℝ) (hg : ∀ ω, 0 ≤ g ω) :
    esd_ent (OSSS.bernoulliWeight p) g
      ≤ ∑ e : Fin n, OSSS.expect (OSSS.bernoulliWeight p) (esd_entCoord p g e) := by
  induction n with
  | zero =>
    rw [esd_ent_fin_zero]
    simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    rw [esd_ent_cons_split p g]
    set g0 := fun ω' : Fin m → Bool => g (Fin.cons false ω') with hg0d
    set g1 := fun ω' : Fin m → Bool => g (Fin.cons true ω') with hg1d
    have hg0nn : ∀ ω', 0 ≤ g0 ω' := fun ω' => hg (Fin.cons false ω')
    have hg1nn : ∀ ω', 0 ≤ g1 ω' := fun ω' => hg (Fin.cons true ω')
    set M0 := OSSS.expect (OSSS.bernoulliWeight p) g0 with hM0d
    set M1 := OSSS.expect (OSSS.bernoulliWeight p) g1 with hM1d
    have hdpi := esd_dpi (μ := OSSS.bernoulliWeight p)
      (esd_bernoulli_pos hp0 hp1) (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le)
      hp0 hp1 hg0nn hg1nn
    have he0 : OSSS.expect (OSSS.bernoulliWeight p) (esd_entCoord p g 0)
        = OSSS.expect (OSSS.bernoulliWeight p) (fun ω' : Fin m → Bool =>
            p * esd_Phi (g1 ω') + (1-p) * esd_Phi (g0 ω')
              - esd_Phi (p * g1 ω' + (1-p) * g0 ω')) := by
      rw [esd_entCoord0_expect]
    have hbound0 : p * esd_Phi M1 + (1-p) * esd_Phi M0
          - esd_Phi ((1-p) * M0 + p * M1)
        ≤ OSSS.expect (OSSS.bernoulliWeight p) (esd_entCoord p g 0) := by
      rw [he0]
      rw [show (1-p) * M0 + p * M1 = p * M1 + (1-p) * M0 by ring]
      exact hdpi
    have hIH0 := ih g0 hg0nn
    have hIH1 := ih g1 hg1nn
    have hfirst : (1-p) *
        (OSSS.expect (OSSS.bernoulliWeight p) (fun ω' : Fin m → Bool => esd_Phi (g0 ω'))
            - esd_Phi M0)
        + p * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω' : Fin m → Bool => esd_Phi (g1 ω'))
            - esd_Phi M1)
        = (1-p) * esd_ent (OSSS.bernoulliWeight p) g0 + p * esd_ent
            (OSSS.bernoulliWeight p) g1 := by
      unfold esd_ent; rw [← hM0d, ← hM1d]
    have hsucc :
        (∑ e' : Fin m, OSSS.expect (OSSS.bernoulliWeight p) (esd_entCoord p g (Fin.succ e')))
        = (1-p) * (∑ e' : Fin m, OSSS.expect (OSSS.bernoulliWeight p) (esd_entCoord p g0 e'))
          + p * (∑ e' : Fin m, OSSS.expect (OSSS.bernoulliWeight p) (esd_entCoord p g1 e')) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e' _
      rw [esd_entCoordSucc_expect p g e', ← hg0d, ← hg1d]
    have hbound1 : (1-p) * esd_ent (OSSS.bernoulliWeight p) g0 + p * esd_ent
        (OSSS.bernoulliWeight p) g1
        ≤ ∑ e' : Fin m, OSSS.expect (OSSS.bernoulliWeight p) (esd_entCoord p g (Fin.succ e')) := by
      rw [hsucc]
      have h0 := mul_le_mul_of_nonneg_left hIH0 (show (0 : ℝ) ≤ 1-p by linarith)
      have h1 := mul_le_mul_of_nonneg_left hIH1 hp0.le
      linarith [h0, h1]
    rw [hfirst]
    linarith [hbound0, hbound1]

end StatMech.Probability
