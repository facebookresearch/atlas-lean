/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Dynamics.FisherKPP
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import MathlibExt.Analysis.ODE.PlanarShooting.Lemma
public import MathlibExt.Analysis.ODE.PlanarShooting.InvariantRegion

/-!
# Existence of logistic Fisher–KPP traveling fronts at every speed `c ≥ 2 √(r D)`

This file proves the existence half of the Kolmogorov–Petrovsky–Piskunov theorem for the
logistic reaction `f(u) = r u (1 - u)`, including the minimal speed `c = 2 √(r D)`.

## Front convention (frozen)

This is the convention of `FisherKPP.IsFront` (and of the former Wanted contract
`exists_isFront_of_le`), and every statement here uses it unchanged:

* PDE: `∂u/∂t = D ∂²u/∂x² + r u (1 - u)` with `D > 0`, `r > 0`.
* Traveling coordinate: `u(x, t) = U(z)` with `z = x - c t`, so a positive speed `c` moves the
  front towards `x = +∞`.
* Profile equation: `D U'' + c U' + r U (1 - U) = 0`, encoded as
  `MathlibExt.Biology.Dynamics.FisherKPP.IsWaveProfile D r c U U'`, where the second function
  `U'` is the derivative of `U` and `U'' = (-(c U') - r U (1 - U)) / D`.
* Front: `MathlibExt.Biology.Dynamics.FisherKPP.IsFront D r c U U'`, that is a wave profile with
  `0 < U < 1` everywhere, `U → 1` (the invading stable state) as `z → -∞` and `U → 0` (the
  invaded unstable state) as `z → +∞`.
* Monotone front: `StrictAnti U`, a front that decreases strictly from `1` to `0`.
* Admissible speeds: `2 * √(r * D) ≤ c`. The minimal (critical) speed is `c = 2 √(r D)`, where
  the node `(0, 0)` of the phase plane is degenerate.

## Main results

* `exists_isFront_of_le`: **KPP existence.** For every `c ≥ 2 √(r D)` there is a strictly
  decreasing front of speed `c`. It discharges the former Wanted contract of the same name with
  the same hypotheses and conclusion.
* `exists_isFront_two_mul_sqrt`: the minimal-speed boundary `c = 2 √(r D)` itself.
* `exists_isFront_of_sq_le`: the same existence for nonnegative speeds with `4 r D ≤ c²`.

## Proof

Shooting in the phase plane `(U, U')`. `PlanarShooting.exists_unstableBranch` builds the
unstable branch of the saddle `(1, 0)` on `z < 0` from a convergent power series.
`PlanarShooting.exists_isFront_of_unstableBranch` continues it to a global solution that stays
in the trapping triangle `{0 < U < 1, -c U / (2 D) < U' < 0}`, which is forward invariant for
every `c ≥ 2 √(r D)`, the critical speed included, and shows that the solution converges to the
node `(0, 0)`. This file composes the two. The critical speed needs no limit of supercritical
fronts.

## Scope

Only the logistic reaction is treated. Minimal speeds for general monostable reactions are not
stated. Uniqueness of the front up to translation and the converse (no front for
`0 ≤ c < 2 √(r D)`, see `FisherKPP.not_isFront_of_sq_lt`) are not combined here.

## References

* A. Kolmogorov, I. Petrovsky and N. Piskunov, *Étude de l'équation de la diffusion avec
  croissance de la quantité de matière et son application à un problème biologique*, Bull.
  Univ. État Moscou Sér. Int. A 1 (1937), 1–26.
* R. A. Fisher, *The wave of advance of advantageous genes*, Ann. Eugenics 7 (1937), 355–369.
* J. D. Murray, *Mathematical Biology I: An Introduction*, 3rd ed., Springer, 2002, §13.2.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Biology.Dynamics.FisherKPP

open Real Filter Topology

/-- **Kolmogorov–Petrovsky–Piskunov: fronts exist at every speed `c ≥ 2 √(r D)`**, and they are
strictly decreasing. For `D, r > 0` and `2 √(r D) ≤ c` there is a profile `U` with derivative
`U'` solving `D U'' + c U' + r U (1 - U) = 0`, with `0 < U < 1`, `U → 1` at `-∞`, `U → 0` at
`+∞`, and `U` strictly decreasing. -/
theorem exists_isFront_of_le {D r c : ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : 2 * √(r * D) ≤ c) : ∃ U U' : ℝ → ℝ, IsFront D r c U U' ∧ StrictAnti U := by
  obtain ⟨U, V, hode, hq, hU, hV, -⟩ :=
    MathlibExt.Analysis.ODE.PlanarShooting.exists_unstableBranch hD hr c
  exact MathlibExt.Analysis.ODE.PlanarShooting.exists_isFront_of_unstableBranch hD hr hc
    ⟨U, V, hode, hq, hU, hV⟩

/-- **The minimal-speed front.** For `D, r > 0`, at the critical speed `c = 2 √(r D)` a strictly
decreasing front exists. -/
theorem exists_isFront_two_mul_sqrt {D r : ℝ} (hD : 0 < D) (hr : 0 < r) :
    ∃ U U' : ℝ → ℝ, IsFront D r (2 * √(r * D)) U U' ∧ StrictAnti U :=
  exists_isFront_of_le hD hr le_rfl

/-- **KPP existence, squared form.** For `D, r > 0` and a nonnegative speed with `4 r D ≤ c²` a
strictly decreasing front exists. -/
theorem exists_isFront_of_sq_le {D r c : ℝ} (hD : 0 < D) (hr : 0 < r) (hc0 : 0 ≤ c)
    (hc : 4 * r * D ≤ c ^ 2) : ∃ U U' : ℝ → ℝ, IsFront D r c U U' ∧ StrictAnti U := by
  refine exists_isFront_of_le hD hr ?_
  have h : √(4 * (r * D)) ≤ c := by
    rw [Real.sqrt_le_left hc0]
    linarith
  rwa [Real.sqrt_mul (by norm_num), show √(4 : ℝ) = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h

open MathlibExt.Analysis.ODE.PlanarShooting

/-- A function with values in `[0, 1]` cannot have derivative at least `ε > 0` near `+∞`. -/
private lemma not_eventually_le_deriv_atTop {U V : ℝ → ℝ} (hU : ∀ z, HasDerivAt U (V z) z)
    (hb : ∀ z, 0 ≤ U z ∧ U z ≤ 1) {ε : ℝ} (hε : 0 < ε) : ¬ ∀ᶠ z in atTop, ε ≤ V z := by
  intro h
  obtain ⟨a, ha⟩ := eventually_atTop.1 h
  have hmono : MonotoneOn (fun z => U z - ε * z) (Set.Ici a) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun z => V z - ε * 1) (convex_Ici a)
      (fun z _ => (((hU z).sub ((hasDerivAt_id' z).const_mul ε))).continuousAt.continuousWithinAt)
      (fun z _ => ((hU z).sub ((hasDerivAt_id' z).const_mul ε)).hasDerivWithinAt) ?_
    intro z hz
    rw [interior_Ici] at hz
    have := ha z (le_of_lt hz)
    linarith
  have hε2 : 0 < 2 / ε := by positivity
  have key := hmono (Set.mem_Ici.2 le_rfl) (show a + 2 / ε ∈ Set.Ici a from by
    simp only [Set.mem_Ici]; linarith) (by linarith)
  simp only at key
  have h2 : ε * (a + 2 / ε) = ε * a + 2 := by field_simp
  linarith [hb a, hb (a + 2 / ε)]

/-- A function with values in `[0, 1]` cannot have derivative at most `-ε < 0` near `+∞`. -/
private lemma not_eventually_deriv_le_atTop {U V : ℝ → ℝ} (hU : ∀ z, HasDerivAt U (V z) z)
    (hb : ∀ z, 0 ≤ U z ∧ U z ≤ 1) {ε : ℝ} (hε : 0 < ε) : ¬ ∀ᶠ z in atTop, V z ≤ -ε := by
  intro h
  refine not_eventually_le_deriv_atTop (U := fun z => 1 - U z) (V := fun z => -V z)
    (fun z => (hU z).const_sub 1) (fun z => ⟨by linarith [hb z], by linarith [hb z]⟩) hε ?_
  filter_upwards [h] with z hz
  linarith

private lemma hasDerivAt_comp_neg {U V : ℝ → ℝ} (hU : ∀ z, HasDerivAt U (V z) z) (t : ℝ) :
    HasDerivAt (fun t => U (-t)) (-V (-t)) t := by
  have := (hU (-t)).comp t (hasDerivAt_neg' t)
  simpa [Function.comp_def] using this

private lemma eventually_atTop_of_atBot {p : ℝ → Prop} (h : ∀ᶠ z in atBot, p z) :
    ∀ᶠ t in atTop, p (-t) := by
  obtain ⟨a, ha⟩ := eventually_atBot.1 h
  exact eventually_atTop.2 ⟨-a, fun t ht => ha (-t) (by linarith)⟩

/-- A function with values in `[0, 1]` cannot have derivative at least `ε > 0` near `-∞`. -/
private lemma not_eventually_le_deriv_atBot {U V : ℝ → ℝ} (hU : ∀ z, HasDerivAt U (V z) z)
    (hb : ∀ z, 0 ≤ U z ∧ U z ≤ 1) {ε : ℝ} (hε : 0 < ε) : ¬ ∀ᶠ z in atBot, ε ≤ V z := by
  intro h
  refine not_eventually_le_deriv_atTop (U := fun t => 1 - U (-t)) (V := fun t => V (-t))
    (fun t => by simpa using (hasDerivAt_comp_neg hU t).const_sub 1)
    (fun t => ⟨by linarith [hb (-t)], by linarith [hb (-t)]⟩) hε (eventually_atTop_of_atBot h)

/-- A function with values in `[0, 1]` cannot have derivative at most `-ε < 0` near `-∞`. -/
private lemma not_eventually_deriv_le_atBot {U V : ℝ → ℝ} (hU : ∀ z, HasDerivAt U (V z) z)
    (hb : ∀ z, 0 ≤ U z ∧ U z ≤ 1) {ε : ℝ} (hε : 0 < ε) : ¬ ∀ᶠ z in atBot, V z ≤ -ε := by
  intro h
  refine not_eventually_le_deriv_atTop (U := fun t => U (-t)) (V := fun t => -V (-t))
    (hasDerivAt_comp_neg hU) (fun t => hb (-t)) hε ?_
  filter_upwards [eventually_atTop_of_atBot h] with t ht
  linarith

/-- `D U' + c U` is antitone along a front. -/
private lemma antitone_energy {D r c : ℝ} {U V : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r)
    (h : IsFront D r c U V) : Antitone fun z => D * V z + c * U z := by
  obtain ⟨hW, hb, -, -⟩ := h
  refine antitone_of_hasDerivAt_nonpos (f' := fun z => -(r * U z * (1 - U z))) (fun z => ?_)
    (fun z => ?_)
  · have := ((hW z).2.const_mul D).add ((hW z).1.const_mul c)
    convert this using 1
    field_simp
    ring
  · have := mul_nonneg (mul_nonneg hr.le (hb z).1.le) (sub_nonneg.2 (hb z).2.le)
    show -(r * U z * (1 - U z)) ≤ 0
    linarith

/-- For `D, r > 0`, along a front `U' → 0` at `-∞`: the orbit leaves the saddle `(1, 0)`. -/
theorem tendsto_deriv_atBot_of_isFront {D r c : ℝ} {U V : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r)
    (h : IsFront D r c U V) : Tendsto V atBot (𝓝 0) := by
  have hφ := antitone_energy hD hr h
  obtain ⟨hW, hb, hU1, -⟩ := h
  have hb' : ∀ z, 0 ≤ U z ∧ U z ≤ 1 := fun z => ⟨(hb z).1.le, (hb z).2.le⟩
  have hU : ∀ z, HasDerivAt U (V z) z := fun z => (hW z).1
  have hcU : ∀ z, -|c| ≤ c * U z ∧ c * U z ≤ |c| := fun z => by
    have h1 := (hb' z).1; have h2 := (hb' z).2
    constructor <;> nlinarith [abs_nonneg c, le_abs_self c, neg_abs_le c]
  rcases tendsto_atBot_of_antitone hφ with htop | ⟨l, hl⟩
  · exfalso
    refine not_eventually_le_deriv_atBot hU hb' one_pos ?_
    filter_upwards [tendsto_atTop.1 htop (D + |c|)] with z hz
    have := hcU z
    rw [← sub_nonneg]
    have hD' : D * (V z - 1) ≥ 0 := by nlinarith
    nlinarith
  · have hV : Tendsto V atBot (𝓝 ((l - c * 1) / D)) := by
      refine ((hl.sub (hU1.const_mul c)).div_const D).congr fun z => ?_
      field_simp
      ring
    have hl0 : (l - c * 1) / D = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · refine not_eventually_deriv_le_atBot hU hb' (ε := -((l - c * 1) / D) / 2) (by linarith) ?_
        filter_upwards [hV.eventually (eventually_le_nhds (show (l - c * 1) / D <
          (l - c * 1) / D / 2 by linarith))] with z hz
        linarith
      · refine not_eventually_le_deriv_atBot hU hb' (ε := (l - c * 1) / D / 2) (by linarith) ?_
        filter_upwards [hV.eventually (eventually_ge_nhds (show (l - c * 1) / D / 2 <
          (l - c * 1) / D by linarith))] with z hz
        exact hz
    rwa [hl0] at hV

/-- For `D, r > 0`, along a front `U' → 0` at `+∞`: the orbit enters the node `(0, 0)`. -/
theorem tendsto_deriv_atTop_of_isFront {D r c : ℝ} {U V : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r)
    (h : IsFront D r c U V) : Tendsto V atTop (𝓝 0) := by
  have hφ := antitone_energy hD hr h
  obtain ⟨hW, hb, -, hU0⟩ := h
  have hb' : ∀ z, 0 ≤ U z ∧ U z ≤ 1 := fun z => ⟨(hb z).1.le, (hb z).2.le⟩
  have hU : ∀ z, HasDerivAt U (V z) z := fun z => (hW z).1
  have hcU : ∀ z, -|c| ≤ c * U z ∧ c * U z ≤ |c| := fun z => by
    have h1 := (hb' z).1; have h2 := (hb' z).2
    constructor <;> nlinarith [abs_nonneg c, le_abs_self c, neg_abs_le c]
  rcases tendsto_atTop_of_antitone hφ with hbot | ⟨l, hl⟩
  · exfalso
    refine not_eventually_deriv_le_atTop hU hb' one_pos ?_
    filter_upwards [tendsto_atBot.1 hbot (-(D + |c|))] with z hz
    have := hcU z
    have hD' : D * (V z + 1) ≤ 0 := by nlinarith
    nlinarith
  · have hV : Tendsto V atTop (𝓝 ((l - c * 0) / D)) := by
      refine ((hl.sub (hU0.const_mul c)).div_const D).congr fun z => ?_
      field_simp
      ring
    have hl0 : (l - c * 0) / D = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · refine not_eventually_deriv_le_atTop hU hb' (ε := -((l - c * 0) / D) / 2) (by linarith) ?_
        filter_upwards [hV.eventually (eventually_le_nhds (show (l - c * 0) / D <
          (l - c * 0) / D / 2 by linarith))] with z hz
        linarith
      · refine not_eventually_le_deriv_atTop hU hb' (ε := (l - c * 0) / D / 2) (by linarith) ?_
        filter_upwards [hV.eventually (eventually_ge_nhds (show (l - c * 0) / D / 2 <
          (l - c * 0) / D by linarith))] with z hz
        exact hz
    rwa [hl0] at hV

/-- **A front is a heteroclinic orbit** (for `D, r > 0`) of `U' = V`,
`V' = -(c V + r U (1 - U)) / D`: the phase-plane curve `(U, V)` runs from the saddle `(1, 0)` at
`-∞` to the node `(0, 0)` at `+∞`. -/
theorem tendsto_heteroclinic_of_isFront {D r c : ℝ} {U V : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r)
    (h : IsFront D r c U V) :
    Tendsto (fun z => (U z, V z)) atBot (𝓝 (1, 0)) ∧
      Tendsto (fun z => (U z, V z)) atTop (𝓝 (0, 0)) :=
  ⟨h.2.2.1.prodMk_nhds (tendsto_deriv_atBot_of_isFront hD hr h),
    h.2.2.2.prodMk_nhds (tendsto_deriv_atTop_of_isFront hD hr h)⟩

/-- **A front of positive speed has `U' < 0` everywhere** (for `D, r > 0`), so it is strictly
decreasing. -/
theorem deriv_neg_of_isFront {D r c : ℝ} {U V : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r) (hc : 0 < c)
    (h : IsFront D r c U V) (z : ℝ) : V z < 0 := by
  have hV0 := tendsto_deriv_atBot_of_isFront hD hr h
  obtain ⟨hW, hb, -, -⟩ := h
  have hψ : StrictAnti fun z => exp (c / D * z) * V z := by
    refine strictAnti_of_hasDerivAt_neg
      (f' := fun z => -(exp (c / D * z) * (r * U z * (1 - U z)) / D)) (fun z => ?_) (fun z => ?_)
    · have := ((hasDerivAt_id' z).const_mul (c / D)).exp.mul (hW z).2
      convert this using 1
      field_simp
      ring
    · have hX : 0 < r * U z * (1 - U z) := mul_pos (mul_pos hr (hb z).1) (sub_pos.2 (hb z).2)
      have := div_pos (mul_pos (exp_pos (c / D * z)) hX) hD
      linarith
  have hψ0 : Tendsto (fun z => exp (c / D * z) * V z) atBot (𝓝 0) := by
    have he : Tendsto (fun z => exp (c / D * z)) atBot (𝓝 0) :=
      tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (div_pos hc hD))
    simpa using he.mul hV0
  have h1 : exp (c / D * (z - 1)) * V (z - 1) ≤ 0 := by
    refine ge_of_tendsto hψ0 ?_
    filter_upwards [eventually_le_atBot (z - 1)] with w hw
    exact hψ.antitone hw
  have h2 := hψ (show z - 1 < z by linarith)
  exact neg_of_mul_neg_right (h2.trans_le h1) (exp_pos _).le

/-- **A front at a speed `c ≥ 2 √(r D)` lies in the open trapping triangle** (for `D, r > 0`) with
vertices `(0, 0)`, `(1, 0)`, `(1, -c / (2 D))` at every point `z`. -/
theorem mem_trappingTriangle_of_isFront {D r c : ℝ} {U V : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : 2 * √(r * D) ≤ c) (h : IsFront D r c U V) (z : ℝ) :
    (U z, V z) ∈ trappingTriangle D c := by
  obtain ⟨hc0, hc2⟩ := pos_and_sq_of_two_sqrt_le hD hr hc
  have hV0 := tendsto_deriv_atBot_of_isFront hD hr h
  have hVneg := deriv_neg_of_isFront hD hr hc0 h z
  obtain ⟨hW, hb, hU1, -⟩ := h
  have hμpos : 0 < c / (2 * D) := div_pos hc0 (by positivity)
  have hΦ : StrictMono fun z => exp (c / (2 * D) * z) * (V z + c / (2 * D) * U z) := by
    refine strictMono_of_hasDerivAt_pos
      (f' := fun z => exp (c / (2 * D) * z) * (U z * (c ^ 2 / (4 * D) - r + r * U z) / D))
      (fun z => ?_) (fun z => ?_)
    · have := ((hasDerivAt_id' z).const_mul (c / (2 * D))).exp.mul
        ((hW z).2.fun_add ((hW z).1.const_mul (c / (2 * D))))
      convert this using 1
      field_simp
      ring
    · have hk : 0 ≤ c ^ 2 / (4 * D) - r := by
        rw [sub_nonneg, le_div_iff₀ (by positivity)]; linarith
      have hpos : 0 < c ^ 2 / (4 * D) - r + r * U z := by nlinarith [mul_pos hr (hb z).1]
      exact mul_pos (exp_pos _) (div_pos (mul_pos (hb z).1 hpos) hD)
  have hΦ0 : Tendsto (fun z => exp (c / (2 * D) * z) * (V z + c / (2 * D) * U z)) atBot
      (𝓝 0) := by
    have he : Tendsto (fun z => exp (c / (2 * D) * z)) atBot (𝓝 0) :=
      tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hμpos)
    simpa using he.mul (hV0.add (hU1.const_mul (c / (2 * D))))
  have h1 : 0 ≤ exp (c / (2 * D) * (z - 1)) * (V (z - 1) + c / (2 * D) * U (z - 1)) := by
    refine le_of_tendsto hΦ0 ?_
    filter_upwards [eventually_le_atBot (z - 1)] with w hw
    exact hΦ.monotone hw
  have h2 := hΦ (show z - 1 < z by linarith)
  exact ⟨(hb z).2, hVneg, pos_of_mul_pos_right (h1.trans_lt h2) (exp_pos _).le⟩

/-- **Supercritical (and critical) heteroclinic existence.** For `D, r > 0` and `c ≥ 2 √(r D)`
the planar system `U' = V`, `V' = -(c V + r U (1 - U)) / D` has an orbit from `(1, 0)` at `-∞`
to `(0, 0)` at `+∞` lying in the open trapping triangle (in particular `V < 0`), giving a
strictly decreasing wave `0 < U < 1`. The classical hypothesis `c > 2 √(D s)` is the case
`r = s` with strict inequality. -/
theorem exists_heteroclinic_of_le {D r c : ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : 2 * √(r * D) ≤ c) :
    ∃ U V : ℝ → ℝ, IsWaveProfile D r c U V ∧
      Tendsto (fun z => (U z, V z)) atBot (𝓝 (1, 0)) ∧
      Tendsto (fun z => (U z, V z)) atTop (𝓝 (0, 0)) ∧
      (∀ z, (U z, V z) ∈ trappingTriangle D c) ∧
      (∀ z, 0 < U z ∧ U z < 1) ∧ StrictAnti U := by
  obtain ⟨U, V, hF, hanti⟩ := exists_isFront_of_le hD hr hc
  obtain ⟨h1, h2⟩ := tendsto_heteroclinic_of_isFront hD hr hF
  exact ⟨U, V, hF.1, h1, h2, mem_trappingTriangle_of_isFront hD hr hc hF, hF.2.1, hanti⟩

end MathlibExt.Biology.Dynamics.FisherKPP
