/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# I-projections on convex sets of distributions: the Pythagorean inequality

Let `Q` be a strictly positive distribution on a finite alphabet and `Γ` a convex set of
distributions. If `P*` minimises the I-divergence `D(P ‖ Q) = ∑ₐ P(a) log (P(a) / Q(a))` over `Γ`
(the *I-projection* of `Q` on `Γ`), then every `P ∈ Γ` is supported inside the support of `P*`, and

`D(P ‖ Q) ≥ D(P ‖ P*) + D(P* ‖ Q)`.

This is Csiszár–Shields, *Information Theory and Statistics: A Tutorial*, 2004, Theorem 3.1
(finite alphabet, `Q > 0`), the finite case of Csiszár, "I-divergence geometry of probability
distributions and minimization problems", Ann. Probab. 3 (1975), Theorem 2.2. The proof is the
tutorial's: the one-sided derivative of `t ↦ D((1 - t) P* + t P ‖ Q)` at `0` is
`∑ₐ (P(a) - P*(a)) log (P*(a) / Q(a))`, which must be nonnegative, and equals `-∞` if `P` charges
a letter that `P*` does not.

Distributions are nonnegative functions `α → ℝ` summing to `1`; divergences are written as
explicit sums with the natural logarithm. For probability mass functions such a sum is Mathlib's
`klDiv` of the associated measures, by `InformationTheory.toReal_klDiv_toMeasure`.
-/

@[expose] public section

namespace MathlibExt.InformationTheory.IProjection

open Finset Real Filter Topology Set

variable {α : Type*} [Fintype α]

/-- **Tangent line of `x log x`.** For `x ≥ 0` and `y > 0`,
`y log y - x log x ≤ (y - x)(log y + 1)`: the convex function `x ↦ x log x` lies above its tangent
at `y` (the convexity of `t log t` used in Csiszár, Ann. Probab. 3 (1975), proof of Lemma 2.1). -/
theorem mul_log_sub_mul_log_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    y * log y - x * log x ≤ (y - x) * (log y + 1) := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp only [sub_zero, zero_mul, mul_add, mul_one]; linarith
  have h := log_le_sub_one_of_pos (div_pos hy hx')
  rw [log_div hy.ne' hx'.ne'] at h
  have h2 := mul_le_mul_of_nonneg_left h hx
  rw [mul_sub, mul_sub, mul_one, mul_div_cancel₀ _ hx'.ne'] at h2
  nlinarith

/-- **Splitting a divergence term.** With `Q(a) > 0` and `R(a) ≥ 0`,
`R(a) log (R(a) / Q(a)) = R(a) log R(a) - R(a) log Q(a)`; both sides vanish at `R(a) = 0`, the
convention `0 log 0 = 0` of Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998),
Section II. -/
theorem mul_log_div_eq {r q : ℝ} (hr : 0 ≤ r) (hq : 0 < q) :
    r * log (r / q) = r * log r - r * log q := by
  rcases hr.eq_or_lt with rfl | hr'
  · simp
  rw [log_div hr'.ne' hq.ne']; ring

/-- **First-order estimate along a segment, one letter** (Csiszár–Shields, *Information Theory and
Statistics: A Tutorial*, 2004, proof of Theorem 3.1). Along `P_t = P* + t (P - P*)` with `0 < t <
1`, the increase of `R(a) log (R(a) / Q(a))` from `P*` to `P_t` is at most `t ((P(a) - P*(a)) (log
P_t(a) - log Q(a)) + (P(a) - P*(a)))`. -/
theorem term_sub_le {p ps q t : ℝ} (hp : 0 ≤ p) (hps : 0 ≤ ps) (hq : 0 < q) (ht0 : 0 < t)
    (ht1 : t < 1) :
    (ps + t * (p - ps)) * log ((ps + t * (p - ps)) / q) - ps * log (ps / q) ≤
      t * ((p - ps) * (log (ps + t * (p - ps)) - log q) + (p - ps)) := by
  set pt := ps + t * (p - ps) with hpt
  have hpt0 : 0 ≤ pt := by nlinarith
  rcases hpt0.eq_or_lt with h0 | hpos
  · -- `P_t(a) = 0` forces `P(a) = P*(a) = 0`
    have hps0 : ps = 0 := by nlinarith
    have hp0 : p = 0 := by nlinarith
    simp [← h0, hps0, hp0]
  rw [mul_log_div_eq hpt0 hq, mul_log_div_eq hps hq]
  have htan := mul_log_sub_mul_log_le hps hpos
  have hdiff : pt - ps = t * (p - ps) := by rw [hpt]; ring
  calc pt * log pt - pt * log q - (ps * log ps - ps * log q)
      = (pt * log pt - ps * log ps) - (pt - ps) * log q := by ring
    _ ≤ (pt - ps) * (log pt + 1) - (pt - ps) * log q := by linarith
    _ = t * ((p - ps) * (log pt - log q) + (p - ps)) := by rw [hdiff]; ring

/-- **First-order condition for an I-projection** (Csiszár–Shields, *Information Theory and
Statistics: A Tutorial*, 2004, proof of Theorem 3.1, quantity (3.1)). Under the hypotheses of
`support_and_pythagorean`, every `P ∈ Γ` vanishes wherever `P*` does, and the one-sided derivative
`∑ₐ (P(a) - P*(a)) (log P*(a) - log Q(a))` of `t ↦ D(P* + t (P - P*) ‖ Q)` at `0` is nonnegative.
-/
theorem support_and_first_order {Q : α → ℝ} (hQ : ∀ a, 0 < Q a) {Γ : Set (α → ℝ)}
    (hΓ : Convex ℝ Γ) (hsub : ∀ R ∈ Γ, (∀ a, 0 ≤ R a) ∧ ∑ a, R a = 1) {Ps : α → ℝ} (hPs : Ps ∈ Γ)
    (hmin : ∀ P ∈ Γ, ∑ a, Ps a * log (Ps a / Q a) ≤ ∑ a, P a * log (P a / Q a))
    {P : α → ℝ} (hP : P ∈ Γ) :
    (∀ a, Ps a = 0 → P a = 0) ∧ 0 ≤ ∑ a, (P a - Ps a) * (log (Ps a) - log (Q a)) := by
  have hP0 : ∀ a, 0 ≤ P a := (hsub P hP).1
  have hPs0 : ∀ a, 0 ≤ Ps a := (hsub Ps hPs).1
  have hsum : ∑ a, (P a - Ps a) = 0 := by
    rw [Finset.sum_sub_distrib, (hsub P hP).2, (hsub Ps hPs).2, sub_self]
  set Pt : ℝ → α → ℝ := fun t a => Ps a + t * (P a - Ps a) with hPt
  have hPtmem : ∀ t ∈ Ioo (0 : ℝ) 1, Pt t ∈ Γ := by
    intro t ht
    have := hΓ hPs hP (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
    convert this using 1
    funext a; simp [hPt]; ring
  -- `g t = ∑ (P - P*) (log P_t - log Q)` is nonnegative on `(0, 1)`
  set g : ℝ → ℝ := fun t => ∑ a, (P a - Ps a) * (log (Pt t a) - log (Q a)) with hg
  have hgnn : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ g t := by
    intro t ht
    have hle : ∑ a, Pt t a * log (Pt t a / Q a) - ∑ a, Ps a * log (Ps a / Q a) ≤ t * g t := by
      rw [← Finset.sum_sub_distrib]
      calc ∑ a, (Pt t a * log (Pt t a / Q a) - Ps a * log (Ps a / Q a))
          ≤ ∑ a, t * ((P a - Ps a) * (log (Pt t a) - log (Q a)) + (P a - Ps a)) :=
            Finset.sum_le_sum fun a _ =>
              term_sub_le (hP0 a) (hPs0 a) (hQ a) ht.1 ht.2
        _ = t * g t := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, hsum, add_zero]
    have := hmin _ (hPtmem t ht)
    exact (mul_nonneg_iff_of_pos_left ht.1).mp (by linarith)
  -- decomposition `g t = B t + c log t` for `t > 0`
  set c : ℝ := ∑ a, if Ps a = 0 then P a else 0 with hc
  set B : ℝ → ℝ := fun t => ∑ a, if Ps a = 0 then P a * (log (P a) - log (Q a))
    else (P a - Ps a) * (log (Pt t a) - log (Q a)) with hB
  have hdecomp : ∀ t, 0 < t → g t = B t + c * log t := by
    intro t ht
    simp only [hg, hB, hc, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : Ps a = 0
    · simp only [h, ite_true, hPt, sub_zero, zero_add]
      rcases (hP0 a).eq_or_lt with h0 | hpos
      · simp [← h0]
      · rw [log_mul ht.ne' hpos.ne']; ring
    · simp [h]
  have hBlim : Tendsto B (𝓝[>] 0) (𝓝 (B 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    refine tendsto_finsetSum _ fun a _ => ?_
    by_cases h : Ps a = 0
    · simp only [h, ite_true]; exact tendsto_const_nhds
    · simp only [h, ite_false]
      have hpos : 0 < Ps a := lt_of_le_of_ne (hPs0 a) (Ne.symm h)
      have hcont : ContinuousAt (fun t : ℝ => Pt t a) 0 := by
        simp only [hPt]; fun_prop
      have hlog : ContinuousAt (fun t : ℝ => log (Pt t a)) 0 :=
        (continuousAt_log (by simpa [hPt] using hpos.ne')).comp hcont
      exact (tendsto_const_nhds.mul (hlog.sub continuousAt_const).tendsto)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  -- the support inclusion: otherwise `c > 0` and `g t → -∞`
  have hc0 : c = 0 := by
    have hcnn : 0 ≤ c := Finset.sum_nonneg fun a _ => by split_ifs <;> simp [hP0 a]
    by_contra hne
    have hcpos : 0 < c := lt_of_le_of_ne hcnn (Ne.symm hne)
    have hbot : Tendsto (fun t => B t + c * log t) (𝓝[>] 0) atBot :=
      hBlim.add_atBot (Tendsto.const_mul_atBot hcpos tendsto_log_nhdsGT_zero)
    obtain ⟨t, ht, hneg⟩ := (hev.and (hbot.eventually (eventually_lt_atBot 0))).exists
    have := hgnn t ht
    rw [hdecomp t ht.1] at this
    linarith
  have hsupp : ∀ a, Ps a = 0 → P a = 0 := by
    intro a ha
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by
      split_ifs <;> simp [hP0 b])).mp hc0.symm.symm a (Finset.mem_univ a)
    simpa [ha] using hterm
  refine ⟨hsupp, ?_⟩
  -- passing to the limit `t → 0⁺` in `0 ≤ g t = B t`
  have hB0 : 0 ≤ B 0 := by
    refine ge_of_tendsto hBlim ?_
    filter_upwards [hev] with t ht
    have := hgnn t ht
    rwa [hdecomp t ht.1, hc0, zero_mul, add_zero] at this
  convert hB0 using 1
  simp only [hB, hPt, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : Ps a = 0
  · simp [h, hsupp a h]
  · simp [h]

/-- **Divergence defect as a first-order term.** If `Q > 0`, `P, P* ≥ 0` and `P` vanishes wherever
`P*` does, then `D(P ‖ Q) - D(P ‖ P*) - D(P* ‖ Q) = ∑ₐ (P(a) - P*(a)) (log P*(a) - log Q(a))`
(Csiszár–Shields, *Information Theory and Statistics: A Tutorial*, 2004, proofs of Theorems 3.1 and
3.2; Csiszár, Ann. Probab. 3 (1975), identity (2.6)). -/
theorem divergence_defect_eq {Q P Ps : α → ℝ} (hQ : ∀ a, 0 < Q a) (hP0 : ∀ a, 0 ≤ P a)
    (hPs0 : ∀ a, 0 ≤ Ps a) (hsupp : ∀ a, Ps a = 0 → P a = 0) :
    ∑ a, P a * log (P a / Q a) - ∑ a, P a * log (P a / Ps a) - ∑ a, Ps a * log (Ps a / Q a) =
      ∑ a, (P a - Ps a) * (log (Ps a) - log (Q a)) := by
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : Ps a = 0
  · simp [h, hsupp a h]
  · have hpos : 0 < Ps a := lt_of_le_of_ne (hPs0 a) (Ne.symm h)
    rcases (hP0 a).eq_or_lt with h0 | hp
    · rw [← h0, log_div hpos.ne' (hQ a).ne']; ring
    · rw [log_div hp.ne' (hQ a).ne', log_div hp.ne' hpos.ne', log_div hpos.ne' (hQ a).ne']
      ring

/-- **I-projection: support and Pythagorean inequality** (Csiszár–Shields, *Information Theory and
Statistics: A Tutorial*, 2004, Theorem 3.1; finite case of Csiszár, "I-divergence geometry of
probability distributions and minimization problems", Ann. Probab. 3 (1975), Theorem 2.2). Let `Q`
be a strictly positive function on a finite alphabet, `Γ` a convex set of probability vectors
(nonnegative, summing to `1`), and `P* ∈ Γ` a minimiser of `D(· ‖ Q) = ∑ₐ · log (· / Q)` over
`Γ`. Then every `P ∈ Γ` vanishes wherever `P*` does, and `D(P ‖ P*) + D(P* ‖ Q) ≤ D(P ‖ Q)`
(natural logarithm). -/
theorem support_and_pythagorean {Q : α → ℝ} (hQ : ∀ a, 0 < Q a) {Γ : Set (α → ℝ)}
    (hΓ : Convex ℝ Γ) (hsub : ∀ R ∈ Γ, (∀ a, 0 ≤ R a) ∧ ∑ a, R a = 1) {Ps : α → ℝ} (hPs : Ps ∈ Γ)
    (hmin : ∀ P ∈ Γ, ∑ a, Ps a * log (Ps a / Q a) ≤ ∑ a, P a * log (P a / Q a))
    {P : α → ℝ} (hP : P ∈ Γ) :
    (∀ a, Ps a = 0 → P a = 0) ∧
      ∑ a, P a * log (P a / Ps a) + ∑ a, Ps a * log (Ps a / Q a) ≤
        ∑ a, P a * log (P a / Q a) := by
  obtain ⟨hsupp, hfo⟩ := support_and_first_order hQ hΓ hsub hPs hmin hP
  refine ⟨hsupp, ?_⟩
  have := divergence_defect_eq hQ (hsub P hP).1 (hsub Ps hPs).1 hsupp
  linarith

/-- **Pythagorean identity at an algebraic inner point** (Csiszár, "I-divergence geometry of
probability distributions and minimization problems", Ann. Probab. 3 (1975), Theorem 2.2, last
assertion, finite alphabet). Under the hypotheses of `support_and_pythagorean`, suppose `P*` is an
algebraic inner point of `Γ`: for every `P ∈ Γ` the segment from `P` through `P*` extends a little
beyond `P*` inside `Γ`. Then `D(P ‖ Q) = D(P ‖ P*) + D(P* ‖ Q)` for every `P ∈ Γ`. -/
theorem pythagorean_eq_of_inner {Q : α → ℝ} (hQ : ∀ a, 0 < Q a) {Γ : Set (α → ℝ)}
    (hΓ : Convex ℝ Γ) (hsub : ∀ R ∈ Γ, (∀ a, 0 ≤ R a) ∧ ∑ a, R a = 1) {Ps : α → ℝ} (hPs : Ps ∈ Γ)
    (hmin : ∀ P ∈ Γ, ∑ a, Ps a * log (Ps a / Q a) ≤ ∑ a, P a * log (P a / Q a))
    (hinner : ∀ P ∈ Γ, ∃ ε > 0, (fun a => Ps a + ε * (Ps a - P a)) ∈ Γ)
    {P : α → ℝ} (hP : P ∈ Γ) :
    ∑ a, P a * log (P a / Q a) =
      ∑ a, P a * log (P a / Ps a) + ∑ a, Ps a * log (Ps a / Q a) := by
  obtain ⟨hsupp, hfo⟩ := support_and_first_order hQ hΓ hsub hPs hmin hP
  obtain ⟨ε, hε, hP'⟩ := hinner P hP
  obtain ⟨-, hfo'⟩ := support_and_first_order hQ hΓ hsub hPs hmin hP'
  have hneg : ∑ a, ((Ps a + ε * (Ps a - P a)) - Ps a) * (log (Ps a) - log (Q a)) =
      -ε * ∑ a, (P a - Ps a) * (log (Ps a) - log (Q a)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
  rw [hneg] at hfo'
  have hzero : ∑ a, (P a - Ps a) * (log (Ps a) - log (Q a)) = 0 := by nlinarith
  have := divergence_defect_eq hQ (hsub P hP).1 (hsub Ps hPs).1 hsupp
  linarith

/-- **Pythagorean identity for linear families** (Csiszár–Shields, *Information Theory and
Statistics: A Tutorial*, 2004, Theorem 3.2, first assertion). Let `Q > 0` on a finite alphabet,
`f₁, …, f_k : α → ℝ`, `c ∈ ℝᵏ`, and `L = {P ≥ 0 : ∑ₐ P(a) = 1, ∑ₐ P(a) fᵢ(a) = cᵢ for all i}`
(a linear family). If `P* ∈ L` minimises `D(· ‖ Q)` over `L` (the I-projection of `Q` on `L`), then
`D(P ‖ Q) = D(P ‖ P*) + D(P* ‖ Q)` for every `P ∈ L`. -/
theorem pythagorean_eq_linearFamily {Q : α → ℝ} (hQ : ∀ a, 0 < Q a) {ι : Type*}
    (f : ι → α → ℝ) (c : ι → ℝ) {Ps : α → ℝ}
    (hPs : Ps ∈ {R : α → ℝ | ((∀ a, 0 ≤ R a) ∧ ∑ a, R a = 1) ∧ ∀ i, ∑ a, R a * f i a = c i})
    (hmin : ∀ P ∈ {R : α → ℝ | ((∀ a, 0 ≤ R a) ∧ ∑ a, R a = 1) ∧ ∀ i, ∑ a, R a * f i a = c i},
      ∑ a, Ps a * log (Ps a / Q a) ≤ ∑ a, P a * log (P a / Q a))
    {P : α → ℝ}
    (hP : P ∈ {R : α → ℝ | ((∀ a, 0 ≤ R a) ∧ ∑ a, R a = 1) ∧ ∀ i, ∑ a, R a * f i a = c i}) :
    ∑ a, P a * log (P a / Q a) =
      ∑ a, P a * log (P a / Ps a) + ∑ a, Ps a * log (Ps a / Q a) := by
  set L := {R : α → ℝ | ((∀ a, 0 ≤ R a) ∧ ∑ a, R a = 1) ∧ ∀ i, ∑ a, R a * f i a = c i}
  have hconv : Convex ℝ L := by
    intro x hx y hy s t hs ht hst
    refine ⟨⟨fun a => ?_, ?_⟩, fun i => ?_⟩
    · have := hx.1.1 a; have := hy.1.1 a
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; positivity
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hx.1.2, hy.1.2, mul_one, hst]
    · have h : ∑ a, (s * x a + t * y a) * f i a =
          s * ∑ a, x a * f i a + t * ∑ a, y a * f i a := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [h, hx.2 i, hy.2 i, ← add_mul, hst, one_mul]
  have hsub : ∀ R ∈ L, (∀ a, 0 ≤ R a) ∧ ∑ a, R a = 1 := fun R hR => hR.1
  refine pythagorean_eq_of_inner hQ hconv hsub hPs hmin (fun R hR => ?_) hP
  -- `P*` is an algebraic inner point: the constraints are affine and `supp R ⊆ supp P*`
  have hsupp := (support_and_first_order hQ hconv hsub hPs hmin hR).1
  have hev : ∀ a, ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ Ps a + ε * (Ps a - R a) := by
    intro a
    by_cases h : Ps a = 0
    · exact Eventually.of_forall fun ε => by simp [h, hsupp a h]
    · have hpos : 0 < Ps a := lt_of_le_of_ne (hPs.1.1 a) (Ne.symm h)
      have hcont : Tendsto (fun ε : ℝ => Ps a + ε * (Ps a - R a)) (𝓝 0) (𝓝 (Ps a)) := by
        have hc : Continuous fun ε : ℝ => Ps a + ε * (Ps a - R a) := by fun_prop
        simpa using hc.tendsto 0
      exact (tendsto_nhdsWithin_of_tendsto_nhds hcont).eventually (eventually_ge_nhds hpos)
  obtain ⟨ε, hε, hnn⟩ := ((eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)).and
    (Filter.eventually_all.mpr hev)).exists
  refine ⟨ε, hε, ⟨⟨hnn, ?_⟩, fun i => ?_⟩⟩
  · have h : ∑ a, (Ps a + ε * (Ps a - R a)) = ∑ a, Ps a + ε * (∑ a, Ps a - ∑ a, R a) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [h, hPs.1.2, hR.1.2, sub_self, mul_zero, add_zero]
  · have h : ∑ a, (Ps a + ε * (Ps a - R a)) * f i a =
        ∑ a, Ps a * f i a + ε * (∑ a, Ps a * f i a - ∑ a, R a * f i a) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [h, hPs.2 i, hR.2 i, sub_self, mul_zero, add_zero]

/-- **Existence of the I-projection on a closed set** (finite-alphabet case of Csiszár,
"I-divergence geometry of probability distributions and minimization problems", Ann. Probab. 3
(1975), Theorem 2.1; Csiszár–Shields, *Information Theory and Statistics: A Tutorial*, 2004,
Section 3). If `Q > 0` on a finite alphabet and `Γ` is a nonempty closed set of probability vectors,
then `D(· ‖ Q)` attains its minimum on `Γ`. Convexity, needed in the source for uniqueness and for
non-finite alphabets, is not used. -/
theorem exists_isMinOn {Q : α → ℝ} (hQ : ∀ a, 0 < Q a) {Γ : Set (α → ℝ)} (hne : Γ.Nonempty)
    (hclosed : IsClosed Γ) (hsub : ∀ R ∈ Γ, (∀ a, 0 ≤ R a) ∧ ∑ a, R a = 1) :
    ∃ Ps ∈ Γ, ∀ P ∈ Γ, ∑ a, Ps a * log (Ps a / Q a) ≤ ∑ a, P a * log (P a / Q a) := by
  have hbox : Γ ⊆ Set.pi univ fun _ => Icc (0 : ℝ) 1 := by
    intro R hR a _
    refine ⟨(hsub R hR).1 a, ?_⟩
    rw [← (hsub R hR).2]
    exact Finset.single_le_sum (fun b _ => (hsub R hR).1 b) (Finset.mem_univ a)
  have hcpt : IsCompact Γ :=
    (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hclosed hbox
  have hcont : Continuous fun P : α → ℝ => ∑ a, P a * log (P a / Q a) := by
    have : (fun P : α → ℝ => ∑ a, P a * log (P a / Q a)) =
        fun P => ∑ a, (P a * log (P a) - P a * log (Q a)) := by
      funext P
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases h : P a = 0
      · simp [h]
      · rw [log_div h (hQ a).ne']; ring
    rw [this]
    refine continuous_finsetSum _ fun a _ => ?_
    exact (continuous_mul_log.comp (continuous_apply a)).sub
      ((continuous_apply a).mul continuous_const)
  obtain ⟨Ps, hPs, hmin⟩ := hcpt.exists_isMinOn hne hcont.continuousOn
  exact ⟨Ps, hPs, fun P hP => hmin hP⟩

end MathlibExt.InformationTheory.IProjection
