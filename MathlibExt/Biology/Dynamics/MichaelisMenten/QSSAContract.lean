/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.MichaelisMenten

/-!
# The Michaelis–Menten QSSA contract: small parameter, slow-time window, initial layer

This file freezes the statement of the quasi-steady-state approximation (QSSA) for the
Michaelis–Menten mechanism `E + S ⇌ C → E + P` (rate constants `k₁, k₋₁, k₂`, written `k₁`,
`kb`, `k₂`; Michaelis constant `K_M = (k₋₁ + k₂)/k₁`; initial data `s(0) = s₀ > 0`,
`c(0) = 0`, `e(0) = e₀ > 0`). It proves the algebraic facts behind that statement and leaves the
analytic claim as a hypothesis: `QSSAContract` is a `Prop`, and nothing here proves it.

## Two different statements

* **Algebraic QSSA relation (proved, not the theorem).** Setting `c' = 0` and solving for `c`
  gives the slow manifold `c = e₀ s / (K_M + s)` (`complexRate_eq_zero_iff`), and substituting
  it into `s'` gives the reduced vector field (`slowTimeScale_mul_substrateRate_qss`). This is
  elimination of a variable. It holds at points of the manifold and says nothing about
  solutions. The true solution starts off the manifold: `c'(0) = k₁ e₀ s₀ > 0`
  (`complexRate_initial_pos`).
* **Singular-perturbation limit statement (`QSSAContract`, not proved here).** Solutions of the
  full system stay within `O(ε)` of the reduced solution on a fixed compact slow-time interval.
  This is Tikhonov's theorem with Vasil'eva's first-order estimate, applied to
  Michaelis–Menten kinetics by Heineken, Tsuchiya and Aris. A consumer must take
  `QSSAContract k₁ kb k₂ s₀ T` as a hypothesis. The wanted theorem `abs_sub_reduced_le` in
  `WantedExt.Biology.Dynamics.MichaelisMentenQSSAWanted` (not imported here) states only the
  substrate half, in time `τ = e₀ t`, for global solutions and a reduced solution defined for
  all `τ ≥ 0`, with cutoff `e₀ ≤ 1`. `QSSAContract` adds the complex bound on `[δ, T]`, drops
  the cutoff (see below) and requires solutions only on the window. Neither statement is
  proved here, and no implication between them is proved.

## The frozen contract

* **Small parameter.** `ε = e₀ / (s₀ + K_M)` (`qssaEpsilon`), the dimensionless parameter of
  Segel and Slemrod. The limit is `e₀ → 0` with `k₁, kb, k₂, s₀` fixed, so `κ = K_M / s₀`
  (`qssaKappa`) is fixed. It always satisfies `ε ≤ e₀ / s₀` (the Heineken–Tsuchiya–Aris
  parameter), and it is small even when `e₀ ≈ s₀`, provided `K_M ≫ e₀`. The ratio of the
  fast time scale `t_C = 1 / (k₁ (s₀ + K_M))` to the slow time scale
  `t_S = (s₀ + K_M) / (k₂ e₀)` is below `ε` (`fastTimeScale_div_slowTimeScale_lt`).
* **Variables and slow-time window.** Use `u = s / s₀`, `v = c / e₀` and slow time `θ = t / t_S`.
  The claim covers the compact window `θ ∈ [0, T]`, that is, `t ∈ [0, t_S T]`. Solutions are
  only required on that window (`IsSolutionOn`). Every global solution (the `IsSolution` of
  `MathlibExt.Biology.Dynamics.MichaelisMenten`) restricts to one
  (`IsSolution.isSolutionOn`).
* **Reduced dynamics.** `du/dθ = -(1 + κ) u / (κ + u)`, `u(0) = 1` (`reducedField`,
  `IsReducedSolutionOn`), with slow manifold `v = u / (κ + u)` (`slowManifold`). In slow time
  neither depends on `e₀`.
* **Error claim and initial layer.** There is a constant `C`, independent of `e₀` (it may
  depend on `k₁, kb, k₂, s₀, T, δ` and `u`), with
  `|s(t_S θ)/s₀ - u(θ)| ≤ C ε` on all of `[0, T]`: the substrate is slow and needs no
  initial-layer correction. The complex has an initial layer of slow-time width `O(ε)`, which
  the contract **excludes**. For each `δ ∈ (0, T]` it claims `|c(t_S θ)/e₀ - u(θ)/(κ+u(θ))| ≤ C ε`
  only on `[δ, T]`, with `C` depending on `δ`. Excluding the layer is necessary: at `θ = 0`
  the complex error is `1/(1 + κ)` for every `e₀` (`initialLayer_gap`), so no `O(ε)` bound
  can hold there (`not_complex_le_at_zero`). A matched (composite) layer expansion is not
  part of this contract.

No cutoff `ε ≤ ε₀` appears. Along solutions `s/s₀`, `c/e₀` and `u` stay in `[0, 1]`
(standard invariance, not proved here), so both errors are at most `2`, and Tikhonov's form
"for `ε ≤ ε₀`" and the uncut form are equivalent after enlarging `C`. The bound has content
only when `C ε` is small.

## API-00 source receipt

* Reuse search (2026-11-11, base `53666a3c1`): the pinned Mathlib (`v4.35.0`) has no singular
  perturbation, Tikhonov, slow-manifold or boundary-layer development. `Mathlib/Analysis/ODE`
  provides only local Picard–Lindelöf existence, Gronwall and uniqueness. The repository has
  `MathlibExt.Biology.Dynamics.MichaelisMenten`, reused here (`michaelisConstant`,
  `substrateRate`, `complexRate`, `qssComplex`, `mmRate`, `IsSolution`,
  `IsSolution.enzyme_conservation`, `substrateRate_qss`), and the wanted theorem
  `abs_sub_reduced_le`, which is cited above and not used as a proof.

## References

* A. N. Tikhonov, *Systems of differential equations containing small parameters in the
  derivatives*, Mat. Sb. (N.S.) 31(73) (1952) 575–586.
* A. B. Vasil'eva, *Asymptotic behaviour of solutions to certain problems involving non-linear
  differential equations containing a small parameter multiplying the highest derivatives*,
  Russian Math. Surveys 18 (1963) 13–84.
* F. G. Heineken, H. M. Tsuchiya and R. Aris, *On the mathematical status of the pseudo-steady
  state hypothesis of biochemical kinetics*, Math. Biosci. 1 (1967) 95–113.
* L. A. Segel and M. Slemrod, *The quasi-steady-state assumption: a case study in
  perturbation*, SIAM Rev. 31 (1989) 446–477.
-/

@[expose] public section

open Set

namespace MathlibExt.Biology.Dynamics.MichaelisMenten

/-! ### Nondimensional parameters and time scales -/

/-- The Segel–Slemrod small parameter `ε = e₀ / (s₀ + K_M)` (dimensionless). -/
noncomputable def qssaEpsilon (k₁ kb k₂ s₀ e₀ : ℝ) : ℝ :=
  e₀ / (s₀ + michaelisConstant k₁ kb k₂)

/-- The dimensionless Michaelis constant `κ = K_M / s₀`, fixed in the limit `e₀ → 0`. -/
noncomputable def qssaKappa (k₁ kb k₂ s₀ : ℝ) : ℝ :=
  michaelisConstant k₁ kb k₂ / s₀

/-- The slow (substrate depletion) time scale `t_S = (s₀ + K_M) / (k₂ e₀)`. -/
noncomputable def slowTimeScale (k₁ kb k₂ s₀ e₀ : ℝ) : ℝ :=
  (s₀ + michaelisConstant k₁ kb k₂) / (k₂ * e₀)

/-- The fast (complex formation) time scale `t_C = 1 / (k₁ (s₀ + K_M))`. -/
noncomputable def fastTimeScale (k₁ kb k₂ s₀ : ℝ) : ℝ :=
  1 / (k₁ * (s₀ + michaelisConstant k₁ kb k₂))

/-- The reduced vector field in slow time for `u = s / s₀`: `du/dθ = -(1 + κ) u / (κ + u)`. -/
noncomputable def reducedField (k₁ kb k₂ s₀ u : ℝ) : ℝ :=
  -mmRate (1 + qssaKappa k₁ kb k₂ s₀) (qssaKappa k₁ kb k₂ s₀) u

/-- The slow manifold for `v = c / e₀`: `v = u / (κ + u)`. -/
noncomputable def slowManifold (k₁ kb k₂ s₀ u : ℝ) : ℝ :=
  u / (qssaKappa k₁ kb k₂ s₀ + u)

lemma michaelisConstant_pos {k₁ kb k₂ : ℝ} (hk₁ : 0 < k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂) :
    0 < michaelisConstant k₁ kb k₂ := by
  unfold michaelisConstant; positivity

lemma qssaEpsilon_pos {k₁ kb k₂ s₀ e₀ : ℝ} (hk₁ : 0 < k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂)
    (hs₀ : 0 < s₀) (he₀ : 0 < e₀) : 0 < qssaEpsilon k₁ kb k₂ s₀ e₀ := by
  have := michaelisConstant_pos hk₁ hkb hk₂
  unfold qssaEpsilon; positivity

lemma qssaKappa_pos {k₁ kb k₂ s₀ : ℝ} (hk₁ : 0 < k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂)
    (hs₀ : 0 < s₀) : 0 < qssaKappa k₁ kb k₂ s₀ :=
  div_pos (michaelisConstant_pos hk₁ hkb hk₂) hs₀

/-- The Segel–Slemrod parameter is below the Heineken–Tsuchiya–Aris parameter `e₀ / s₀`. -/
theorem qssaEpsilon_lt_div {k₁ kb k₂ s₀ e₀ : ℝ} (hk₁ : 0 < k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂)
    (hs₀ : 0 < s₀) (he₀ : 0 < e₀) : qssaEpsilon k₁ kb k₂ s₀ e₀ < e₀ / s₀ := by
  have := michaelisConstant_pos hk₁ hkb hk₂
  unfold qssaEpsilon
  exact div_lt_div_of_pos_left he₀ hs₀ (by linarith)

/-- **Time-scale separation.** `t_C / t_S = ε · k₂ / (k₁ s₀ + kb + k₂)`. -/
theorem fastTimeScale_div_slowTimeScale {k₁ kb k₂ s₀ e₀ : ℝ} (hk₁ : 0 < k₁) (hkb : 0 ≤ kb)
    (hk₂ : 0 < k₂) (hs₀ : 0 < s₀) (he₀ : 0 < e₀) :
    fastTimeScale k₁ kb k₂ s₀ / slowTimeScale k₁ kb k₂ s₀ e₀ =
      qssaEpsilon k₁ kb k₂ s₀ e₀ * (k₂ / (k₁ * s₀ + kb + k₂)) := by
  have hK := michaelisConstant_pos hk₁ hkb hk₂
  have hsum : k₁ * (s₀ + michaelisConstant k₁ kb k₂) = k₁ * s₀ + kb + k₂ := by
    unfold michaelisConstant; field_simp; ring
  unfold fastTimeScale slowTimeScale qssaEpsilon
  rw [← hsum]
  field_simp

/-- The fast-to-slow time-scale ratio is below `ε`, so a small `ε` separates the scales. -/
theorem fastTimeScale_div_slowTimeScale_lt {k₁ kb k₂ s₀ e₀ : ℝ} (hk₁ : 0 < k₁) (hkb : 0 ≤ kb)
    (hk₂ : 0 < k₂) (hs₀ : 0 < s₀) (he₀ : 0 < e₀) :
    fastTimeScale k₁ kb k₂ s₀ / slowTimeScale k₁ kb k₂ s₀ e₀ < qssaEpsilon k₁ kb k₂ s₀ e₀ := by
  rw [fastTimeScale_div_slowTimeScale hk₁ hkb hk₂ hs₀ he₀]
  have hε := qssaEpsilon_pos hk₁ hkb hk₂ hs₀ he₀
  have hlt : k₂ / (k₁ * s₀ + kb + k₂) < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith [mul_pos hk₁ hs₀]
  nlinarith

/-! ### The algebraic QSSA relation (elimination, not a limit theorem) -/

/-- **Algebraic QSSA, slow manifold.** In the scaled variables the quasi-steady-state complex
`c = e₀ s / (K_M + s)` at `s = s₀ u` is `v = c / e₀ = u / (κ + u)`. Pure algebra. -/
theorem qssComplex_div_eq_slowManifold {k₁ kb k₂ s₀ e₀ : ℝ} (hs₀ : s₀ ≠ 0) (he₀ : e₀ ≠ 0)
    (u : ℝ) : qssComplex k₁ kb k₂ e₀ (s₀ * u) / e₀ = slowManifold k₁ kb k₂ s₀ u := by
  unfold qssComplex slowManifold qssaKappa
  by_cases h : michaelisConstant k₁ kb k₂ + s₀ * u = 0
  · have h' : michaelisConstant k₁ kb k₂ / s₀ + u = 0 := by
      field_simp; linarith
    simp [h, h']
  · have h' : michaelisConstant k₁ kb k₂ / s₀ + u ≠ 0 := by
      intro h'; apply h; field_simp at h'; linarith
    field_simp

/-- **Algebraic QSSA, reduced field.** Substituting the slow manifold into `s'` and rescaling to
`u = s / s₀`, `θ = t / t_S` gives `reducedField`: `(t_S / s₀) s' = -(1 + κ) u / (κ + u)`. This
eliminates `c` by setting `c' = 0`. It is not a statement about solutions; that statement is
`QSSAContract`. -/
theorem slowTimeScale_mul_substrateRate_qss {k₁ kb k₂ s₀ e₀ u : ℝ} (hk₁ : 0 < k₁)
    (hk₂ : k₂ ≠ 0) (hs₀ : s₀ ≠ 0) (he₀ : e₀ ≠ 0)
    (hu : michaelisConstant k₁ kb k₂ + s₀ * u ≠ 0) :
    slowTimeScale k₁ kb k₂ s₀ e₀ / s₀ *
        substrateRate k₁ kb (s₀ * u) (qssComplex k₁ kb k₂ e₀ (s₀ * u))
          (e₀ - qssComplex k₁ kb k₂ e₀ (s₀ * u)) =
      reducedField k₁ kb k₂ s₀ u := by
  rw [substrateRate_qss hk₁ hu]
  have hu' : michaelisConstant k₁ kb k₂ / s₀ + u ≠ 0 := by
    intro h'; apply hu; field_simp at h'; linarith
  unfold reducedField slowTimeScale mmRate qssaKappa
  field_simp

/-- The full solution starts off the slow manifold: with `c(0) = 0`, `e(0) = e₀`, `s(0) = s₀`,
the complex rate is `k₁ e₀ s₀ > 0`. So `c' = 0` is not an identity along solutions. -/
theorem complexRate_initial_pos {k₁ kb k₂ s₀ e₀ : ℝ} (hk₁ : 0 < k₁) (hs₀ : 0 < s₀)
    (he₀ : 0 < e₀) : 0 < complexRate k₁ kb k₂ s₀ 0 (e₀ - 0) := by
  simp only [complexRate, sub_zero, mul_zero]; positivity

/-! ### Solutions on the slow-time window -/

/-- A solution of the Michaelis–Menten system with total enzyme `e₀` (so `e = e₀ - c`) on the
time window `[0, t₁]`: `s' = -k₁ (e₀ - c) s + kb c`, `c' = k₁ (e₀ - c) s - (kb + k₂) c`. -/
structure IsSolutionOn (k₁ kb k₂ e₀ t₁ : ℝ) (s c : ℝ → ℝ) : Prop where
  hasDerivAt_substrate : ∀ t ∈ Icc 0 t₁,
    HasDerivAt s (substrateRate k₁ kb (s t) (c t) (e₀ - c t)) t
  hasDerivAt_complex : ∀ t ∈ Icc 0 t₁,
    HasDerivAt c (complexRate k₁ kb k₂ (s t) (c t) (e₀ - c t)) t

/-- A global solution with `e(0) + c(0) = e₀` is a solution on every window `[0, t₁]`. -/
theorem IsSolution.isSolutionOn {k₁ kb k₂ e₀ : ℝ} {s c e p : ℝ → ℝ}
    (h : IsSolution k₁ kb k₂ s c e p) (he₀ : e 0 + c 0 = e₀) (t₁ : ℝ) :
    IsSolutionOn k₁ kb k₂ e₀ t₁ s c := by
  have he (t : ℝ) (ht : 0 ≤ t) : e t = e₀ - c t := by
    rw [← he₀, ← h.enzyme_conservation ht]; ring
  exact ⟨fun t ht ↦ he t ht.1 ▸ h.hasDerivAt_substrate t ht.1,
    fun t ht ↦ he t ht.1 ▸ h.hasDerivAt_complex t ht.1⟩

/-- A solution of the reduced (outer) problem `du/dθ = -(1 + κ) u / (κ + u)`, `u(0) = 1`, on the
slow-time window `[0, T]`. -/
structure IsReducedSolutionOn (k₁ kb k₂ s₀ T : ℝ) (u : ℝ → ℝ) : Prop where
  initial : u 0 = 1
  hasDerivAt : ∀ θ ∈ Icc 0 T, HasDerivAt u (reducedField k₁ kb k₂ s₀ (u θ)) θ

/-! ### The contract -/

/-- **The QSSA contract** (Tikhonov 1952, Vasil'eva 1963, Heineken–Tsuchiya–Aris 1967,
Segel–Slemrod 1989). This is a statement, not a theorem proved here. The parameter
conditions `0 < k₁`, `0 ≤ kb`, `0 < k₂`, `0 < s₀` are premises of the definition (at `k₂ = 0`,
for instance, `t_S = 0` and the substrate clause would be false whenever a reduced solution
exists on `[0, T]`, `T > 0`); for `T ≤ 0` the `δ`-quantifier is empty, so the contract holds
trivially and yields no bound.

Let `u` solve the reduced problem on the slow-time window `[0, T]`. For each `δ ∈ (0, T]` there
is `C`, independent of `e₀` (it may depend on `k₁, kb, k₂, s₀, T, δ` and `u`), such that for
every `e₀ > 0` and every solution `(s, c)` of the full system on `[0, t_S T]` with `s(0) = s₀`,
`c(0) = 0`, `e(0) = e₀`, with `ε = e₀ / (s₀ + K_M)`:

* the substrate satisfies `|s(t_S θ) / s₀ - u(θ)| ≤ C ε` for all `θ ∈ [0, T]`;
* the complex satisfies `|c(t_S θ) / e₀ - u(θ) / (κ + u(θ))| ≤ C ε` for `θ ∈ [δ, T]` only. The
  initial layer `θ < δ` is excluded (see `not_complex_le_at_zero`). -/
def QSSAContract (k₁ kb k₂ s₀ T : ℝ) : Prop :=
  0 < k₁ → 0 ≤ kb → 0 < k₂ → 0 < s₀ →
  ∀ u : ℝ → ℝ, IsReducedSolutionOn k₁ kb k₂ s₀ T u →
    ∀ δ ∈ Ioc 0 T, ∃ C : ℝ, ∀ e₀ : ℝ, 0 < e₀ → ∀ s c : ℝ → ℝ,
      IsSolutionOn k₁ kb k₂ e₀ (slowTimeScale k₁ kb k₂ s₀ e₀ * T) s c → s 0 = s₀ → c 0 = 0 →
        (∀ θ ∈ Icc 0 T, |s (slowTimeScale k₁ kb k₂ s₀ e₀ * θ) / s₀ - u θ| ≤
            C * qssaEpsilon k₁ kb k₂ s₀ e₀) ∧
        (∀ θ ∈ Icc δ T, |c (slowTimeScale k₁ kb k₂ s₀ e₀ * θ) / e₀ -
            slowManifold k₁ kb k₂ s₀ (u θ)| ≤ C * qssaEpsilon k₁ kb k₂ s₀ e₀)

/-! ### Why the initial layer is excluded -/

/-- **Initial-layer gap.** At `θ = 0` the complex starts at `v = 0` while the slow manifold
gives `v = 1 / (1 + κ)`. The outer complex error at `θ = 0` is `1 / (1 + κ)` for every `e₀`. -/
theorem initialLayer_gap {k₁ kb k₂ s₀ e₀ : ℝ} {c u : ℝ → ℝ} (hc : c 0 = 0) (hu : u 0 = 1)
    (hκ : 0 < qssaKappa k₁ kb k₂ s₀) :
    |c (slowTimeScale k₁ kb k₂ s₀ e₀ * 0) / e₀ - slowManifold k₁ kb k₂ s₀ (u 0)| =
      1 / (1 + qssaKappa k₁ kb k₂ s₀) := by
  rw [mul_zero, hc, hu, zero_div, zero_sub, abs_neg, slowManifold, add_comm,
    abs_of_pos (by positivity)]

/-- No `O(ε)` bound on the complex can include `θ = 0`: whenever `C ε < 1 / (1 + κ)`, the
outer complex estimate fails at `θ = 0`. This is why `QSSAContract` claims the complex estimate
only on `[δ, T]` with `δ > 0`. -/
theorem not_complex_le_at_zero {k₁ kb k₂ s₀ e₀ C : ℝ} {c u : ℝ → ℝ} (hc : c 0 = 0)
    (hu : u 0 = 1) (hκ : 0 < qssaKappa k₁ kb k₂ s₀)
    (hsmall : C * qssaEpsilon k₁ kb k₂ s₀ e₀ < 1 / (1 + qssaKappa k₁ kb k₂ s₀)) :
    ¬ |c (slowTimeScale k₁ kb k₂ s₀ e₀ * 0) / e₀ - slowManifold k₁ kb k₂ s₀ (u 0)| ≤
      C * qssaEpsilon k₁ kb k₂ s₀ e₀ := by
  rw [initialLayer_gap hc hu hκ]
  exact not_le.2 hsmall

end MathlibExt.Biology.Dynamics.MichaelisMenten
