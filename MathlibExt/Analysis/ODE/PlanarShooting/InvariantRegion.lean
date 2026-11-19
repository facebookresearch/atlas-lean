/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.FisherKPP
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import MathlibExt.Analysis.ODE.MaximalSolution
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The trapping triangle of the logistic traveling-wave ODE

A traveling wave `u(x, t) = U(x - c t)` of the Fisher–KPP equation has profile equation
`D U'' + c U' + r U (1 - U) = 0` (`MathlibExt.Biology.Dynamics.FisherKPP.IsWaveProfile`). In the
phase plane `(U, U')` the classical existence proof for fronts at speeds `c ≥ 2 √(r D)`
(Kolmogorov–Petrovsky–Piskunov; Murray, §13.2) shoots along the unstable branch of the saddle
`(1, 0)` and traps it in the triangle with vertices `(0, 0)`, `(1, 0)`, `(1, -μ)`, `μ = c / (2 D)`.
This file proves the invariant-region and compactness half of that argument. It takes the
unstable branch (constructed in `PlanarShooting.Lemma`, DYN-02.1) only through its properties,
as hypotheses, and never assumes the heteroclinic connection to `(0, 0)`: that connection is
proved.

## Main results

* `mapsTo_trappingTriangle_Icc`, `mapsTo_trappingTriangle_Ici`: for `c ≥ 2 √(r D)`, including
  the critical speed, the open triangle `trappingTriangle D c` is forward invariant, on compact
  intervals and on the noncompact interval `[a, ∞)`.
* `tendsto_zero_of_mapsTo_trappingTriangle`: a solution trapped on `[a, ∞)` tends to `(0, 0)`.
* `eventually_mem_trappingTriangle_atBot`: a curve with the unstable branch's orientation and
  limit at `-∞` eventually lies in the triangle.
* `isFront_of_unstableBranch`, `exists_isFront_of_global_unstableBranch`: a global solution
  extending the unstable branch is a strictly decreasing front.
* `exists_isFront_of_unstableBranch`: global continuation of the branch through the maximal
  solution (`ode_maximal_solution_exit_compact`) that the triangle keeps in a compact box. Its
  hypothesis is the first four conclusions of `PlanarShooting.exists_unstableBranch`, so the two
  files together give the Wanted contract `FisherKPP.exists_isFront_of_le` as stated.
* `bounds_of_mem_trappingTriangle`, `abs_sub_le_of_mapsTo_trappingTriangle`: a-priori bounds
  and equi-Lipschitz estimates, uniform for speeds in `(0, c₁]`.
* `closedTriangle_of_tendsto`, `hasDerivAt_of_tendsto_of_mapsTo_trappingTriangle`: route to the
  critical-speed limit: pointwise limits of trapped solutions as `cₙ → c` lie in the closed
  triangle at speed `c` and solve the profile equation at speed `c`.

## Boundary cases

* Critical eigenvalue collision: `node_charPoly_neg_slope_eq_zero_iff`: the slope `-μ` of the
  slanted edge is an eigenvalue of the node exactly when `c² = 4 r D`. The invariance theorems
  hold at that speed.
* Subcritical speeds: `exists_outward_of_sq_lt`: for `0 < c`, `c² < 4 r D` the field crosses
  the slanted edge outward, so the speed hypothesis cannot be dropped (compare
  `FisherKPP.not_isFront_of_sq_lt`).
* Branch orientation: invariance needs only the start point in the open triangle; the branch's
  quadrant orientation `U < 1, U' < 0` is what puts it there.
* Noncompact time interval: `mapsTo_trappingTriangle_Ici` and
  `tendsto_zero_of_mapsTo_trappingTriangle`.

## Not proved here

A critical-speed front obtained as a limit of supercritical fronts. The lemmas above only
supply the ingredients; no sequence of solutions is produced. The missing steps are
extraction of a locally uniformly convergent subsequence on each `[-n, n]` (Arzelà–Ascoli), a
diagonal argument over `n`, and a translation normalization (e.g. `Uₙ(0) = 1/2`) so that the
limit is not a constant equilibrium. The critical speed itself is covered directly by the
invariance theorems, so the KPP existence statement does not need that limit.

## References

* J. D. Murray, *Mathematical Biology I: An Introduction*, 3rd ed., Springer, 2002, §13.2.
* A. Kolmogorov, I. Petrovsky and N. Piskunov, *Étude de l'équation de la diffusion avec
  croissance de la quantité de matière et son application à un problème biologique*, Bull.
  Univ. État Moscou Sér. Int. A 1 (1937), 1–26.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Analysis.ODE.PlanarShooting

open Real Filter Topology Set
open MathlibExt.Biology.Dynamics.FisherKPP

/-- The open trapping triangle `{(U, V) : U < 1, V < 0, V + μ U > 0}` with `μ = c / (2 D)` in
the phase plane `(U, U')` of `D U'' + c U' + r U (1 - U) = 0`. Its closure is the triangle with
vertices `(0, 0)`, `(1, 0)`, `(1, -μ)` of Murray, §13.2. -/
def trappingTriangle (D c : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 < 1 ∧ p.2 < 0 ∧ 0 < p.2 + c / (2 * D) * p.1}

/-- The trapping triangle is open. -/
lemma isOpen_trappingTriangle (D c : ℝ) : IsOpen (trappingTriangle D c) := by
  apply IsOpen.inter (isOpen_lt continuous_fst continuous_const)
  exact (isOpen_lt continuous_snd continuous_const).inter
    (isOpen_lt continuous_const (continuous_snd.add (continuous_const.mul continuous_fst)))

/-- Points of the trapping triangle have `0 < U`. -/
lemma pos_of_mem_trappingTriangle {D c : ℝ} (hD : 0 < D) (hc : 0 < c) {p : ℝ × ℝ}
    (hp : p ∈ trappingTriangle D c) : 0 < p.1 := by
  obtain ⟨-, h2, h3⟩ := hp
  have hμ : 0 < c / (2 * D) := by positivity
  by_contra h
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hμ.le (not_lt.1 h)]

/-- First-exit principle: a curve, continuous on `[a, b]`, that starts in an open set `S` and
re-enters `S` at every time `t` up to which it has stayed in `S` stays in `S` on `[a, b]`. -/
private lemma mapsTo_of_firstExit {γ : ℝ → ℝ × ℝ} {S : Set (ℝ × ℝ)} {a b : ℝ} (hS : IsOpen S)
    (hγ : ContinuousOn γ (Icc a b)) (ha : γ a ∈ S)
    (h : ∀ t ∈ Ioc a b, (∀ s ∈ Ico a t, γ s ∈ S) → γ t ∈ S) :
    ∀ t ∈ Icc a b, γ t ∈ S := by
  by_contra hne
  push Not at hne
  set A := Icc a b ∩ γ ⁻¹' Sᶜ with hA
  have hAc : IsClosed A := hγ.preimage_isClosed_of_isClosed isClosed_Icc hS.isClosed_compl
  obtain ⟨t₀, ht₀, ht₀S⟩ := hne
  have hAne : A.Nonempty := ⟨t₀, ht₀, ht₀S⟩
  have hAb : BddBelow A := ⟨a, fun x hx => hx.1.1⟩
  have hmem := hAc.csInf_mem hAne hAb
  set t := sInf A
  have hat : a < t := by
    rcases hmem.1.1.lt_or_eq with h' | h'
    · exact h'
    · exact absurd (h' ▸ ha) hmem.2
  refine hmem.2 (h t ⟨hat, hmem.1.2⟩ fun s hs => ?_)
  by_contra hsS
  exact absurd (csInf_le hAb ⟨⟨hs.1, hs.2.le.trans hmem.1.2⟩, hsS⟩) (not_le.2 hs.2)

/-- The KPP speed condition `2 √(r D) ≤ c` gives `0 < c` and `4 r D ≤ c²`. -/
lemma pos_and_sq_of_two_sqrt_le {D r c : ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : 2 * √(r * D) ≤ c) : 0 < c ∧ 4 * r * D ≤ c ^ 2 := by
  have hs : 0 < √(r * D) := Real.sqrt_pos.2 (mul_pos hr hD)
  have hsq : √(r * D) ^ 2 = r * D := Real.sq_sqrt (mul_pos hr hD).le
  refine ⟨by linarith, ?_⟩
  nlinarith [mul_nonneg (sub_nonneg.2 hc) (by linarith : 0 ≤ c + 2 * √(r * D))]

/-- **Forward invariance of the trapping triangle on a compact interval.** If `c ≥ 2 √(r D)`
(including the critical speed `c = 2 √(r D)`), a solution `(U, U')` of
`D U'' + c U' + r U (1 - U) = 0` on `[a, b]` that starts in the open triangle stays in it.

Proof: first exit plus three barriers. On the edge `U = 1` the field gives `U' = V < 0`; on the
edge `V = 0` it gives `V' = -r U (1 - U) / D < 0`; on the edge `V = -μ U`,
`(V + μ U)' = U (c² / (4 D) - r + r U) / D > 0` exactly because `c² ≥ 4 r D`. The barriers are
proved as monotonicity of `U`, of `e^{c z / D} V` and of `e^{μ z} (V + μ U)`, which also rules
out reaching the equilibria `(0, 0)`, `(1, 0)` in finite time without an ODE uniqueness theorem. -/
theorem mapsTo_trappingTriangle_Icc {D r c a b : ℝ} {U V : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : 2 * √(r * D) ≤ c)
    (hode : ∀ z ∈ Icc a b, HasDerivAt U (V z) z ∧
      HasDerivAt V ((-(c * V z) - r * U z * (1 - U z)) / D) z)
    (ha : (U a, V a) ∈ trappingTriangle D c) :
    ∀ t ∈ Icc a b, (U t, V t) ∈ trappingTriangle D c := by
  obtain ⟨hc0, hc2⟩ := pos_and_sq_of_two_sqrt_le hD hr hc
  have hcont : ContinuousOn (fun z => (U z, V z)) (Icc a b) := fun z hz =>
    ((hode z hz).1.continuousAt.prodMk (hode z hz).2.continuousAt).continuousWithinAt
  refine mapsTo_of_firstExit (isOpen_trappingTriangle D c) hcont ha fun t ht hprev => ?_
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hint : ∀ s ∈ interior (Icc a t), (U s, V s) ∈ trappingTriangle D c := by
    rw [interior_Icc]; exact fun s hs => hprev s ⟨hs.1.le, hs.2⟩
  have hat : a ∈ Icc a t := ⟨le_rfl, ht.1.le⟩
  have htt : t ∈ Icc a t := ⟨ht.1.le, le_rfl⟩
  have hdU : ∀ z ∈ Icc a t, HasDerivAt U (V z) z := fun z hz => (hode z (hsub hz)).1
  have hdV : ∀ z ∈ Icc a t, HasDerivAt V ((-(c * V z) - r * U z * (1 - U z)) / D) z :=
    fun z hz => (hode z (hsub hz)).2
  have hiU : ∀ z ∈ interior (Icc a t), 0 < U z := fun z hz =>
    pos_of_mem_trappingTriangle hD hc0 (hint z hz)
  -- Barrier 1: `U` is antitone.
  have hU : AntitoneOn U (Icc a t) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a t)
      (fun z hz => (hdU z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hdU z (interior_subset hz)).hasDerivWithinAt)
      (fun z hz => (hint z hz).2.1.le)
  -- Barrier 2: `e^{c z / D} V z` is antitone.
  have hV : AntitoneOn (fun z => exp (c / D * z) * V z) (Icc a t) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun z => -(exp (c / D * z) * (r * U z * (1 - U z)) / D)) (convex_Icc a t)
      (fun z hz => (((hasDerivAt_id' z).const_mul (c / D)).exp.mul
        (hdV z hz)).continuousAt.continuousWithinAt) (fun z hz => ?_) (fun z hz => ?_)
    · have h := ((hasDerivAt_id' z).const_mul (c / D)).exp.mul (hdV z (interior_subset hz))
      convert h.hasDerivWithinAt using 1
      field_simp
      ring
    · have hX : 0 ≤ r * U z * (1 - U z) :=
        mul_nonneg (mul_nonneg hr.le (hiU z hz).le) (sub_nonneg.2 (hint z hz).1.le)
      exact neg_nonpos.2 (div_nonneg (mul_nonneg (exp_pos _).le hX) hD.le)
  -- Barrier 3: `e^{μ z} (V z + μ U z)` is monotone, `μ = c / (2 D)`.
  have hW : MonotoneOn (fun z => exp (c / (2 * D) * z) * (V z + c / (2 * D) * U z))
      (Icc a t) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun z => exp (c / (2 * D) * z) *
        (U z * (c ^ 2 / (4 * D) - r + r * U z) / D)) (convex_Icc a t)
      (fun z hz => (((hasDerivAt_id' z).const_mul (c / (2 * D))).exp.mul ((hdV z hz).add
        ((hdU z hz).const_mul (c / (2 * D))))).continuousAt.continuousWithinAt)
      (fun z hz => ?_) (fun z hz => ?_)
    · have h := ((hasDerivAt_id' z).const_mul (c / (2 * D))).exp.mul
        ((hdV z (interior_subset hz)).add ((hdU z (interior_subset hz)).const_mul (c / (2 * D))))
      convert h.hasDerivWithinAt using 1
      simp only [Pi.add_apply]
      field_simp
      ring
    · have hk : 0 ≤ c ^ 2 / (4 * D) - r := by
        rw [sub_nonneg, le_div_iff₀ (by positivity)]; linarith
      have := hiU z hz
      positivity
  refine ⟨(hU hat htt ht.1.le).trans_lt ha.1, ?_, ?_⟩
  · exact neg_of_mul_neg_right ((hV hat htt ht.1.le).trans_lt
      (mul_neg_of_pos_of_neg (exp_pos _) ha.2.1)) (exp_pos _).le
  · exact pos_of_mul_pos_right ((mul_pos (exp_pos _) ha.2.2).trans_le (hW hat htt ht.1.le))
      (exp_pos _).le

/-- **Forward invariance on the noncompact interval `[a, ∞)`.** -/
theorem mapsTo_trappingTriangle_Ici {D r c a : ℝ} {U V : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : 2 * √(r * D) ≤ c)
    (hode : ∀ z ∈ Ici a, HasDerivAt U (V z) z ∧
      HasDerivAt V ((-(c * V z) - r * U z * (1 - U z)) / D) z)
    (ha : (U a, V a) ∈ trappingTriangle D c) :
    ∀ t ∈ Ici a, (U t, V t) ∈ trappingTriangle D c := fun t ht =>
  mapsTo_trappingTriangle_Icc (b := t) hD hr hc (fun z hz => hode z hz.1) ha t ⟨ht, le_rfl⟩

/-- **A solution trapped on `[a, ∞)` converges to the node `(0, 0)`.** The convergence uses
only `c > 0`, not the speed threshold: `U` decreases to some `L ≥ 0`, and `L > 0` is impossible
because `D U' + c U + r ε (1 - U a) z` would decrease while staying bounded below by
`r ε (1 - U a) z`, which grows without bound. Then `-μ U < U' < 0` squeezes `U' → 0`. -/
theorem tendsto_zero_of_mapsTo_trappingTriangle {D r c a : ℝ} {U V : ℝ → ℝ} (hD : 0 < D)
    (hr : 0 < r) (hc : 0 < c)
    (hode : ∀ z ∈ Ici a, HasDerivAt U (V z) z ∧
      HasDerivAt V ((-(c * V z) - r * U z * (1 - U z)) / D) z)
    (hT : ∀ z ∈ Ici a, (U z, V z) ∈ trappingTriangle D c) :
    Tendsto U atTop (𝓝 0) ∧ Tendsto V atTop (𝓝 0) := by
  have hpos : ∀ z ∈ Ici a, 0 < U z := fun z hz => pos_of_mem_trappingTriangle hD hc (hT z hz)
  have hcont : ∀ z ∈ Ici a, ContinuousWithinAt U (Ici a) z := fun z hz =>
    (hode z hz).1.continuousAt.continuousWithinAt
  have hanti : AntitoneOn U (Ici a) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a) hcont
      (fun z hz => (hode z (interior_subset hz)).1.hasDerivWithinAt)
      (fun z hz => (hT z (interior_subset hz)).2.1.le)
  have hDV : ∀ z ∈ Ici a, 0 < D * V z + c / 2 * U z := fun z hz => by
    have h := mul_pos hD (hT z hz).2.2
    have he : D * (V z + c / (2 * D) * U z) = D * V z + c / 2 * U z := by
      field_simp
    linarith
  have hsmall : ∀ ε > 0, ∃ t₀ ∈ Ici a, U t₀ < ε := by
    intro ε hε
    by_contra hne
    push Not at hne
    have ha : a ∈ Ici a := le_rfl
    set m := ε * (1 - U a) with hm
    have hm0 : 0 < m := mul_pos hε (sub_pos.2 (hT a ha).1)
    have hφ : AntitoneOn (fun z => D * V z + c * U z + r * m * z) (Ici a) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos
        (f' := fun z => r * m - r * (U z * (1 - U z))) (convex_Ici a)
        (fun z hz => ((((hode z hz).2.const_mul D).add ((hode z hz).1.const_mul c)).add
          ((hasDerivAt_id' z).const_mul (r * m))).continuousAt.continuousWithinAt)
        (fun z hz => ?_) (fun z hz => ?_)
      · have hz' := interior_subset hz
        have h := (((hode z hz').2.const_mul D).add ((hode z hz').1.const_mul c)).add
          ((hasDerivAt_id' z).const_mul (r * m))
        convert h.hasDerivWithinAt using 1
        field_simp
        ring
      · have hz' : z ∈ Ici a := interior_subset hz
        have h1 : ε ≤ U z := hne z hz'
        have h2 : 1 - U a ≤ 1 - U z := by linarith [hanti ha hz' hz']
        have h3 : m ≤ U z * (1 - U z) :=
          mul_le_mul h1 h2 (sub_pos.2 (hT a ha).1).le (hpos z hz').le
        nlinarith
    set t := max a ((D * V a + c * U a + r * m * a) / (r * m))
    have ht : t ∈ Ici a := le_max_left _ _
    have h1 := hφ ha ht ht
    have h2 := hDV t ht
    have h3 : (D * V a + c * U a + r * m * a) ≤ r * m * t := by
      rw [← div_le_iff₀' (mul_pos hr hm0)]; exact le_max_right _ _
    nlinarith [hpos t ht]
  have hU : Tendsto U atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · filter_upwards [eventually_ge_atTop a] with z hz using hb.trans (hpos z hz)
    · obtain ⟨t₀, ht₀, hlt⟩ := hsmall b hb
      filter_upwards [eventually_ge_atTop t₀] with z hz using
        (hanti ht₀ (ht₀.trans hz) hz).trans_lt hlt
  refine ⟨hU, ?_⟩
  have hlow : Tendsto (fun z => -(c / (2 * D)) * U z) atTop (𝓝 0) := by
    simpa using hU.const_mul (-(c / (2 * D)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop a] with z hz
    linarith [(hT z hz).2.2]
  · filter_upwards [eventually_ge_atTop a] with z hz using (hT z hz).2.1.le

/-- **The unstable branch enters the trapping triangle.** A curve in the quadrant
`{U < 1, U' < 0}` for `z < 0` that tends to the saddle `(1, 0)` as `z → -∞` (the properties of
the unstable branch, `PlanarShooting.exists_unstableBranch`) eventually lies in the open
triangle as `z → -∞`, because `U' + μ U → μ > 0`. -/
theorem eventually_mem_trappingTriangle_atBot {D c : ℝ} {U V : ℝ → ℝ} (hD : 0 < D)
    (hc : 0 < c) (hq : ∀ z < 0, U z < 1 ∧ V z < 0) (hU : Tendsto U atBot (𝓝 1))
    (hV : Tendsto V atBot (𝓝 0)) :
    ∀ᶠ z in atBot, (U z, V z) ∈ trappingTriangle D c := by
  have hμ : 0 < c / (2 * D) := by positivity
  have hlim : Tendsto (fun z => V z + c / (2 * D) * U z) atBot (𝓝 (c / (2 * D))) := by
    simpa using hV.add (hU.const_mul (c / (2 * D)))
  filter_upwards [hlim.eventually (lt_mem_nhds hμ), eventually_lt_atBot 0] with z h1 h2
  exact ⟨(hq z h2).1, (hq z h2).2, h1⟩

/-- **Shooting conclusion, conditional on global continuation.** For `c ≥ 2 √(r D)`, a global
solution of the profile equation whose restriction to `z < 0` has the properties of the
unstable branch (quadrant orientation, `(U, U') → (1, 0)` at `-∞`) is a strictly decreasing
front. The heteroclinic connection to `(0, 0)` is proved, not assumed: the branch enters the
trapping triangle, cannot leave it, and converges to the node. -/
theorem isFront_of_unstableBranch {D r c : ℝ} {U V : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : 2 * √(r * D) ≤ c) (hW : IsWaveProfile D r c U V)
    (hq : ∀ z < 0, 0 < U z ∧ U z < 1 ∧ V z < 0) (hU : Tendsto U atBot (𝓝 1))
    (hV : Tendsto V atBot (𝓝 0)) :
    IsFront D r c U V ∧ StrictAnti U := by
  have hc0 := (pos_and_sq_of_two_sqrt_le hD hr hc).1
  obtain ⟨z₀, hz₀T, hz₀⟩ := ((eventually_mem_trappingTriangle_atBot hD hc0
    (fun z hz => ⟨(hq z hz).2.1, (hq z hz).2.2⟩) hU hV).and (eventually_lt_atBot 0)).exists
  have hT := mapsTo_trappingTriangle_Ici hD hr hc (fun z _ => hW z) hz₀T
  have hall : ∀ z, 0 < U z ∧ U z < 1 ∧ V z < 0 := by
    intro z
    rcases lt_or_ge z 0 with h | h
    · exact hq z h
    · have hz : z ∈ Ici z₀ := (hz₀.trans_le h).le
      exact ⟨pos_of_mem_trappingTriangle hD hc0 (hT z hz), (hT z hz).1, (hT z hz).2.1⟩
  refine ⟨⟨hW, fun z => ⟨(hall z).1, (hall z).2.1⟩, hU,
    (tendsto_zero_of_mapsTo_trappingTriangle hD hr hc0 (fun z _ => hW z) hT).1⟩, ?_⟩
  exact strictAnti_of_hasDerivAt_neg (fun z => (hW z).1) (fun z => (hall z).2.2)

/-- Packaged form, in the shape of the Wanted KPP existence contract
`MathlibExt.Biology.Dynamics.FisherKPP.exists_isFront_of_le`: a front exists at every speed
`c ≥ 2 √(r D)` as soon as the unstable branch continues to a global solution. -/
theorem exists_isFront_of_global_unstableBranch {D r c : ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : 2 * √(r * D) ≤ c)
    (hext : ∃ U V : ℝ → ℝ, IsWaveProfile D r c U V ∧
      (∀ z < 0, 0 < U z ∧ U z < 1 ∧ V z < 0) ∧ Tendsto U atBot (𝓝 1) ∧
      Tendsto V atBot (𝓝 0)) :
    ∃ U V : ℝ → ℝ, IsFront D r c U V ∧ StrictAnti U := by
  obtain ⟨U, V, hW, hq, hU, hV⟩ := hext
  exact ⟨U, V, isFront_of_unstableBranch hD hr hc hW hq hU hV⟩

section Compactness

/-- **A-priori bounds in the trapping triangle**: `0 < U < 1`, `-μ < U' < 0`, and the
second derivative `U'' = (-c U' - r U (1 - U)) / D` is at most `(c² / (2 D) + r / 4) / D` in
absolute value. -/
theorem bounds_of_mem_trappingTriangle {D r c : ℝ} (hD : 0 < D) (hr : 0 < r) (hc : 0 < c)
    {p : ℝ × ℝ} (hp : p ∈ trappingTriangle D c) :
    0 < p.1 ∧ p.1 < 1 ∧ -(c / (2 * D)) < p.2 ∧ p.2 < 0 ∧
      |(-(c * p.2) - r * p.1 * (1 - p.1)) / D| ≤ (c ^ 2 / (2 * D) + r / 4) / D := by
  have hu0 := pos_of_mem_trappingTriangle hD hc hp
  obtain ⟨hu1, hv0, hv⟩ := hp
  set μ := c / (2 * D) with hμdef
  have hμ : 0 < μ := by positivity
  have hvμ : -μ < p.2 := by nlinarith
  refine ⟨hu0, hu1, hvμ, hv0, ?_⟩
  have hcμ : c * μ = c ^ 2 / (2 * D) := by rw [hμdef]; ring
  have hcv : -(c * μ) < c * p.2 := by nlinarith
  have hq : p.1 * (1 - p.1) ≤ 1 / 4 := by nlinarith [sq_nonneg (p.1 - 1 / 2)]
  have hq0 : 0 ≤ p.1 * (1 - p.1) := mul_nonneg hu0.le (sub_pos.2 hu1).le
  rw [abs_div, abs_of_pos hD, div_le_div_iff_of_pos_right hD, abs_le]
  constructor <;> nlinarith [mul_nonneg hr.le hq0, mul_le_mul_of_nonneg_left hq hr.le]

/-- **Equi-Lipschitz bounds, uniform in the speed.** A solution trapped in the triangle on
`[a, b]` at any speed `0 < c ≤ c₁` is Lipschitz with constants depending only on `D, r, c₁`:
`|U t - U s| ≤ (c₁ / (2 D)) |t - s|` and `|U' t - U' s| ≤ ((c₁² / (2 D) + r / 4) / D) |t - s|`.
Together with the bounds `0 < U < 1`, `-c₁ / (2 D) < U' < 0`, this is the Arzelà–Ascoli input
for passing to the critical-speed limit along a sequence `cₙ → 2 √(r D)`. -/
theorem abs_sub_le_of_mapsTo_trappingTriangle {D r c c₁ a b : ℝ} {U V : ℝ → ℝ} (hD : 0 < D)
    (hr : 0 < r) (hc : 0 < c) (hc₁ : c ≤ c₁)
    (hode : ∀ z ∈ Icc a b, HasDerivAt U (V z) z ∧
      HasDerivAt V ((-(c * V z) - r * U z * (1 - U z)) / D) z)
    (hT : ∀ z ∈ Icc a b, (U z, V z) ∈ trappingTriangle D c) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) :
    |U t - U s| ≤ c₁ / (2 * D) * |t - s| ∧
      |V t - V s| ≤ (c₁ ^ 2 / (2 * D) + r / 4) / D * |t - s| := by
  have hB := fun z hz => bounds_of_mem_trappingTriangle hD hr hc (hT z hz)
  constructor
  · have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := U) (f' := V)
      (C := c₁ / (2 * D)) (fun z hz => (hode z hz).1.hasDerivWithinAt) (fun z hz => ?_)
      (convex_Icc a b) hs ht
    · simpa only [Real.norm_eq_abs] using h
    · obtain ⟨-, -, h1, h2, -⟩ := hB z hz
      rw [Real.norm_eq_abs, abs_of_neg h2]
      have : c / (2 * D) ≤ c₁ / (2 * D) := by gcongr
      linarith
  · have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := V)
      (f' := fun z => (-(c * V z) - r * U z * (1 - U z)) / D)
      (C := (c₁ ^ 2 / (2 * D) + r / 4) / D) (fun z hz => (hode z hz).2.hasDerivWithinAt)
      (fun z hz => ?_) (convex_Icc a b) hs ht
    · simpa only [Real.norm_eq_abs] using h
    · obtain ⟨-, -, -, -, h5⟩ := hB z hz
      rw [Real.norm_eq_abs]
      refine h5.trans ?_
      gcongr

/-- **Closedness under speed limits.** If points `pₙ` of the triangles at speeds `cₙ` converge
to `p` while `cₙ → c`, then `p` lies in the closed triangle
`{U ≤ 1, U' ≤ 0, U' + (c / (2 D)) U ≥ 0}` at the limit speed (e.g. the critical speed). -/
theorem closedTriangle_of_tendsto {D c : ℝ} {cs : ℕ → ℝ} {ps : ℕ → ℝ × ℝ} {p : ℝ × ℝ}
    (hcs : Tendsto cs atTop (𝓝 c)) (hps : Tendsto ps atTop (𝓝 p))
    (hmem : ∀ n, ps n ∈ trappingTriangle D (cs n)) :
    p.1 ≤ 1 ∧ p.2 ≤ 0 ∧ 0 ≤ p.2 + c / (2 * D) * p.1 := by
  refine ⟨le_of_tendsto' hps.fst_nhds fun n => (hmem n).1.le,
    le_of_tendsto' hps.snd_nhds fun n => (hmem n).2.1.le,
    ge_of_tendsto' (hps.snd_nhds.add ((hcs.div_const (2 * D)).mul hps.fst_nhds))
      fun n => (hmem n).2.2.le⟩

end Compactness

section BoundaryCases

/-- **Critical eigenvalue collision.** At the node `(0, 0)` the linearization
`D w'' + c w' + r w = 0` has characteristic polynomial `D λ² + c λ + r`. The slope `-μ` of the
slanted edge of the triangle is a root exactly at the critical speed `c² = 4 r D`, where the
two node eigenvalues collide at `-μ` and the slanted edge is the eigendirection. -/
theorem node_charPoly_neg_slope_eq_zero_iff {D r c : ℝ} (hD : 0 < D) :
    D * (-(c / (2 * D))) ^ 2 + c * (-(c / (2 * D))) + r = 0 ↔ c ^ 2 = 4 * r * D := by
  have h : D * (-(c / (2 * D))) ^ 2 + c * (-(c / (2 * D))) + r = (4 * r * D - c ^ 2) / (4 * D) := by
    field_simp
    ring
  rw [h, div_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact h.symm
    · exact absurd h (by positivity)
  · exact fun h => Or.inl h.symm

/-- **Below the critical speed the triangle is not invariant.** If `0 < c` and `c² < 4 r D`,
there is a point `(u, -μ u)`, `0 < u < 1`, on the frontier of the triangle (its slanted edge)
where the field points out of the triangle: `U'' + μ U' < 0` there. -/
theorem exists_outward_of_sq_lt {D r c : ℝ} (hD : 0 < D) (hr : 0 < r) (hc0 : 0 < c)
    (hc : c ^ 2 < 4 * r * D) :
    ∃ u ∈ Ioo (0 : ℝ) 1, (u, -(c / (2 * D)) * u) ∈ frontier (trappingTriangle D c) ∧
      (-(c * (-(c / (2 * D)) * u)) - r * u * (1 - u)) / D + c / (2 * D) * (-(c / (2 * D)) * u)
        < 0 := by
  set δ := r - c ^ 2 / (4 * D) with hδ
  have hδ0 : 0 < δ := by
    rw [hδ, sub_pos, div_lt_iff₀ (by positivity)]; linarith
  have hu1 : min (1 / 2) (δ / (2 * r)) < 1 := (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨min (1 / 2) (δ / (2 * r)), ⟨lt_min (by norm_num) (by positivity), hu1⟩, ?_, ?_⟩
  · set u := min (1 / 2) (δ / (2 * r))
    have hu0 : 0 < u := lt_min (by norm_num) (by positivity)
    have hμu : 0 < c / (2 * D) * u := by positivity
    rw [(isOpen_trappingTriangle D c).frontier_eq]
    refine ⟨mem_closure_of_tendsto (f := fun ε : ℝ => (u, -(c / (2 * D)) * u + ε))
      (b := 𝓝[>] 0) ?_ ?_, fun h => ?_⟩
    · refine (((continuous_const.prodMk (continuous_const.add continuous_id)).tendsto' 0 _
        (by simp)).mono_left nhdsWithin_le_nhds)
    · filter_upwards [Ioo_mem_nhdsGT hμu] with ε hε
      exact ⟨hu1, by linarith [hε.2], by linarith [hε.1]⟩
    · have := h.2.2
      simp only at this
      linarith
  set u := min (1 / 2) (δ / (2 * r))
  have hu0 : 0 < u := lt_min (by norm_num) (by positivity)
  have hru : r * u ≤ δ / 2 := by
    have := min_le_right (1 / 2 : ℝ) (δ / (2 * r))
    calc r * u ≤ r * (δ / (2 * r)) := by gcongr
      _ = δ / 2 := by field_simp
  have he : (-(c * (-(c / (2 * D)) * u)) - r * u * (1 - u)) / D +
      c / (2 * D) * (-(c / (2 * D)) * u) = u * (r * u - δ) / D := by
    rw [hδ]; field_simp; ring
  rw [he]
  apply div_neg_of_neg_of_pos _ hD
  nlinarith

end BoundaryCases

section CriticalLimit

/-- Taylor-type remainder from a Lipschitz derivative: if `|f' z - f' s| ≤ L |z - s|` on
`[a, b]`, then `|f t - f s - f' s (t - s)| ≤ L (t - s)²`. -/
private lemma abs_sub_sub_le_of_lipschitz_deriv {f f' : ℝ → ℝ} {a b s t L : ℝ} (hL0 : 0 ≤ L)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hf : ∀ z ∈ Icc a b, HasDerivAt f (f' z) z)
    (hL : ∀ z ∈ Icc a b, |f' z - f' s| ≤ L * |z - s|) :
    |f t - f s - f' s * (t - s)| ≤ L * (t - s) ^ 2 := by
  have hS := uIcc_subset_Icc hs ht
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => f x - f' s * x) (f' := fun x => f' x - f' s) (C := L * |t - s|)
    (fun z hz => ?_) (fun z hz => ?_) (convex_uIcc s t) (left_mem_uIcc (a := s) (b := t))
    (right_mem_uIcc (a := s) (b := t))
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc, abs_mul_abs_self] at h
    convert h using 2
    · ring
    · ring
  · have hd := (hf z (hS hz)).sub ((hasDerivAt_id' z).const_mul (f' s))
    convert hd.hasDerivWithinAt using 1
    ring
  · rw [Real.norm_eq_abs]
    exact (hL z (hS hz)).trans (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hz) hL0)

/-- A quadratic remainder bound on a neighbourhood gives a derivative. -/
private lemma hasDerivAt_of_sq_remainder {g : ℝ → ℝ} {g' K s δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t, |t - s| < δ → |g t - g s - g' * (t - s)| ≤ K * (t - s) ^ 2) :
    HasDerivAt g g' s := by
  rw [hasDerivAt_iff_isLittleO]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_pow_sub_sub s one_lt_two)
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [Metric.ball_mem_nhds s hδ] with t ht
  rw [Metric.mem_ball, Real.dist_eq] at ht
  simp only [Real.norm_eq_abs, smul_eq_mul, abs_pow, sq_abs]
  rw [mul_comm (t - s) g']
  exact h t ht

/-- **Passage to the limit in the speed.** Let `(Uₙ, Uₙ')` solve the profile equation at speed
`cₙ ∈ (0, c₁]` on `[a, b]` and stay in the trapping triangle there. If `cₙ → c` and
`(Uₙ, Uₙ') → (U, V)` pointwise on `[a, b]`, then `(U, V)` solves the profile equation at the
limit speed `c` on `(a, b)`. With `cₙ ↓ 2 √(r D)` this is the route to the critical-speed
front: the equi-Lipschitz bounds `abs_sub_le_of_mapsTo_trappingTriangle` supply the convergent
subsequence (Arzelà–Ascoli, not formalized here), `closedTriangle_of_tendsto` keeps the limit in
the closed critical triangle, and this theorem identifies the limit as a solution.

Proof: no integrals. Uniform Lipschitz bounds on `Uₙ'` and on `Uₙ''` give quadratic Taylor
remainders with constants independent of `n`; these survive the pointwise limit and force the
derivatives of the limit. -/
theorem hasDerivAt_of_tendsto_of_mapsTo_trappingTriangle {D r c c₁ a b : ℝ} {cs : ℕ → ℝ}
    {Us Vs : ℕ → ℝ → ℝ} {U V : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r) (hcs0 : ∀ n, 0 < cs n)
    (hcs1 : ∀ n, cs n ≤ c₁) (hcs : Tendsto cs atTop (𝓝 c))
    (hode : ∀ n, ∀ z ∈ Icc a b, HasDerivAt (Us n) (Vs n z) z ∧
      HasDerivAt (Vs n) ((-(cs n * Vs n z) - r * Us n z * (1 - Us n z)) / D) z)
    (hT : ∀ n, ∀ z ∈ Icc a b, (Us n z, Vs n z) ∈ trappingTriangle D (cs n))
    (hU : ∀ z ∈ Icc a b, Tendsto (fun n => Us n z) atTop (𝓝 (U z)))
    (hV : ∀ z ∈ Icc a b, Tendsto (fun n => Vs n z) atTop (𝓝 (V z))) :
    ∀ s ∈ Ioo a b, HasDerivAt U (V s) s ∧
      HasDerivAt V ((-(c * V s) - r * U s * (1 - U s)) / D) s := by
  intro s hs
  have hsI : s ∈ Icc a b := Ioo_subset_Icc_self hs
  have hc₁ : 0 < c₁ := (hcs0 0).trans_le (hcs1 0)
  set LU := c₁ / (2 * D) with hLU
  set LV := (c₁ ^ 2 / (2 * D) + r / 4) / D with hLV
  set K := (c₁ * LV + r * LU) / D with hK
  have hLU0 : 0 ≤ LU := by positivity
  have hLV0 : 0 ≤ LV := by positivity
  have hK0 : 0 ≤ K := by positivity
  have hlip := fun n {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) =>
    abs_sub_le_of_mapsTo_trappingTriangle hD hr (hcs0 n) (hcs1 n) (hode n) (hT n) hy hx
  -- the second-derivative field is `K`-Lipschitz along each trajectory
  set F : ℕ → ℝ → ℝ := fun n z => (-(cs n * Vs n z) - r * Us n z * (1 - Us n z)) / D with hF
  have hFlip : ∀ n, ∀ z ∈ Icc a b, |F n z - F n s| ≤ K * |z - s| := by
    intro n z hz
    obtain ⟨h1, h2⟩ := hlip n hz hsI
    obtain ⟨hz0, hz1, -⟩ := bounds_of_mem_trappingTriangle hD hr (hcs0 n) (hT n z hz)
    obtain ⟨hs0, hs1, -⟩ := bounds_of_mem_trappingTriangle hD hr (hcs0 n) (hT n s hsI)
    have he : F n z - F n s = (-(cs n * (Vs n z - Vs n s)) -
        r * ((Us n z - Us n s) * (1 - Us n z - Us n s))) / D := by
      simp only [hF]; field_simp; ring
    have hm : |1 - Us n z - Us n s| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    rw [he, abs_div, abs_of_pos hD, div_le_iff₀ hD, hK]
    calc |-(cs n * (Vs n z - Vs n s)) - r * ((Us n z - Us n s) * (1 - Us n z - Us n s))|
        ≤ cs n * |Vs n z - Vs n s| + r * |Us n z - Us n s| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_of_pos (hcs0 n), abs_of_pos hr]
          gcongr
          exact mul_le_of_le_one_right (abs_nonneg _) hm
      _ ≤ c₁ * (LV * |z - s|) + r * (LU * |z - s|) := by
          gcongr
          · exact hcs1 n
      _ = (c₁ * LV + r * LU) / D * |z - s| * D := by field_simp
  set δ := min (s - a) (b - s)
  have hδ : 0 < δ := lt_min (sub_pos.2 hs.1) (sub_pos.2 hs.2)
  have hmem : ∀ t, |t - s| < δ → t ∈ Icc a b := by
    intro t ht
    rw [abs_lt] at ht
    exact ⟨by linarith [min_le_left (s - a) (b - s)], by linarith [min_le_right (s - a) (b - s)]⟩
  constructor
  · refine hasDerivAt_of_sq_remainder (K := LV) hδ fun t ht => ?_
    have htI := hmem t ht
    have hn : ∀ n, |Us n t - Us n s - Vs n s * (t - s)| ≤ LV * (t - s) ^ 2 := fun n =>
      abs_sub_sub_le_of_lipschitz_deriv hLV0 hsI htI (fun z hz => (hode n z hz).1)
        (fun z hz => (hlip n hz hsI).2)
    exact le_of_tendsto' ((((hU t htI).sub (hU s hsI)).sub ((hV s hsI).mul_const (t - s))).abs)
      hn
  · refine hasDerivAt_of_sq_remainder (K := K) hδ fun t ht => ?_
    have htI := hmem t ht
    have hn : ∀ n, |Vs n t - Vs n s - F n s * (t - s)| ≤ K * (t - s) ^ 2 := fun n =>
      abs_sub_sub_le_of_lipschitz_deriv hK0 hsI htI (fun z hz => (hode n z hz).2)
        (fun z hz => hFlip n z hz)
    have hFs : Tendsto (fun n => F n s) atTop (𝓝 ((-(c * V s) - r * U s * (1 - U s)) / D)) :=
      ((((hcs.mul (hV s hsI)).neg).sub ((tendsto_const_nhds.mul (hU s hsI)).mul
        (tendsto_const_nhds.sub (hU s hsI)))).div_const D)
    exact le_of_tendsto' ((((hV t htI).sub (hV s hsI)).sub (hFs.mul_const (t - s))).abs) hn

end CriticalLimit

section Continuation

private lemma hasDerivAt_fst_comp {x : ℝ → ℝ × ℝ} {x' : ℝ × ℝ} {z : ℝ} (h : HasDerivAt x x' z) :
    HasDerivAt (fun t => (x t).1) x'.1 z :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt z h

private lemma hasDerivAt_snd_comp {x : ℝ → ℝ × ℝ} {x' : ℝ × ℝ} {z : ℝ} (h : HasDerivAt x x' z) :
    HasDerivAt (fun t => (x t).2) x'.2 z :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt z h

/-- Gluing two solutions that meet at `z₀` with equal values and derivatives. -/
private lemma hasDerivAt_ite {f g f' g' : ℝ → ℝ} {z₀ : ℝ}
    (hf : ∀ z ≤ z₀, HasDerivAt f (f' z) z) (hg : ∀ z ≥ z₀, HasDerivAt g (g' z) z)
    (h0 : f z₀ = g z₀) (h0' : f' z₀ = g' z₀) (z : ℝ) :
    HasDerivAt (fun t => if t < z₀ then f t else g t) (if z < z₀ then f' z else g' z) z := by
  have hmid : HasDerivAt (fun t => if t < z₀ then f t else g t) (g' z₀) z₀ := by
    have hl : HasDerivWithinAt (fun t => if t < z₀ then f t else g t) (g' z₀) (Iic z₀) z₀ := by
      rw [← h0']
      refine (hf z₀ le_rfl).hasDerivWithinAt.congr (fun t ht => ?_) ?_
      · rcases (mem_Iic.1 ht).lt_or_eq with h | h
        · exact ite_eq_left h
        · rw [h, ite_eq_right (lt_irrefl _)]; exact h0.symm
      · rw [ite_eq_right (lt_irrefl _)]; exact h0.symm
    have hr : HasDerivWithinAt (fun t => if t < z₀ then f t else g t) (g' z₀) (Ici z₀) z₀ :=
      (hg z₀ le_rfl).hasDerivWithinAt.congr (fun t ht => ite_eq_right (not_lt.2 ht))
        (ite_eq_right (lt_irrefl _))
    simpa [Iic_union_Ici] using hl.union hr
  rcases lt_trichotomy z z₀ with hz | hz | hz
  · rw [ite_eq_left hz]
    refine (hf z hz.le).congr_of_eventuallyEq ?_
    filter_upwards [eventually_lt_nhds hz] with t ht using ite_eq_left ht
  · rw [hz, ite_eq_right (lt_irrefl _)]; exact hmid
  · rw [ite_eq_right (not_lt.2 hz.le)]
    refine (hg z hz.le).congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds hz] with t ht using ite_eq_right (not_lt.2 ht.le)

/-- **Kolmogorov–Petrovsky–Piskunov existence from the unstable branch.** For `c ≥ 2 √(r D)`,
any solution of the profile equation on `z < 0` with the properties of the unstable branch
(quadrant orientation, `(U, U') → (1, 0)` at `-∞`; exactly the first four conclusions of
`PlanarShooting.exists_unstableBranch`) yields a strictly decreasing front of speed `c`.

Proof: the branch enters the trapping triangle at some `z₀ < 0`. The maximal solution through
that point (`ode_maximal_solution_exit_compact`) stays in the triangle, hence in a compact box,
so it cannot end at a finite time and lives on `[z₀, ∞)`. Gluing it to the branch at `z₀` gives
a global solution, which `isFront_of_unstableBranch` turns into a front. No uniqueness theorem
is needed: the two pieces meet at one point with equal data. -/
theorem exists_isFront_of_unstableBranch {D r c : ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : 2 * √(r * D) ≤ c)
    (hbranch : ∃ U V : ℝ → ℝ,
      (∀ z < 0, HasDerivAt U (V z) z ∧
        HasDerivAt V ((-(c * V z) - r * U z * (1 - U z)) / D) z) ∧
      (∀ z < 0, 0 < U z ∧ U z < 1 ∧ V z < 0) ∧ Tendsto U atBot (𝓝 1) ∧
      Tendsto V atBot (𝓝 0)) :
    ∃ U V : ℝ → ℝ, IsFront D r c U V ∧ StrictAnti U := by
  obtain ⟨U₀, V₀, hode₀, hq₀, hU₀, hV₀⟩ := hbranch
  have hc0 := (pos_and_sq_of_two_sqrt_le hD hr hc).1
  obtain ⟨z₀, hz₀T, hz₀⟩ := ((eventually_mem_trappingTriangle_atBot hD hc0
    (fun z hz => ⟨(hq₀ z hz).2.1, (hq₀ z hz).2.2⟩) hU₀ hV₀).and (eventually_lt_atBot 0)).exists
  set g : ℝ × ℝ → ℝ × ℝ := fun p => (p.2, (-(c * p.2) - r * p.1 * (1 - p.1)) / D) with hg
  have hgC : ContDiff ℝ 1 g := by rw [hg]; fun_prop
  obtain ⟨I, x, hx0, -, hz₀I, hIcc, hxd, hexit⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_maximal_solution_exit_compact univ
      (fun p => g p.2) z₀ (U₀ z₀, V₀ z₀) isOpen_univ trivial
      (hgC.continuous.comp continuous_snd).continuousOn fun p _ => by
        obtain ⟨K, s, hs, hK⟩ := hgC.locallyLipschitz p.2
        exact ⟨K, univ ×ˢ s, prod_mem_nhds univ_mem hs,
          fun t x y hx hy => hK.dist_le_mul x hx.1.2 y hy.1.2⟩
  have hodex : ∀ z ∈ I, HasDerivAt (fun t => (x t).1) (x z).2 z ∧
      HasDerivAt (fun t => (x t).2) ((-(c * (x z).2) - r * (x z).1 * (1 - (x z).1)) / D) z :=
    fun z hz => ⟨hasDerivAt_fst_comp (hxd z hz).2, hasDerivAt_snd_comp (hxd z hz).2⟩
  have ha : ((x z₀).1, (x z₀).2) ∈ trappingTriangle D c := by rw [hx0]; exact hz₀T
  have hTx : ∀ t ∈ I, z₀ ≤ t → ((x t).1, (x t).2) ∈ trappingTriangle D c := fun t ht hzt =>
    mapsTo_trappingTriangle_Icc (U := fun t => (x t).1) (V := fun t => (x t).2) hD hr hc
      (fun z hz => hodex z (hIcc z₀ hz₀I t ht hz)) ha t ⟨hzt, le_rfl⟩
  -- the maximal solution lives on `[z₀, ∞)`
  have hIci : ∀ t ≥ z₀, t ∈ I := by
    intro b hb
    by_contra hbI
    obtain ⟨⟨c', hc'I, hc'⟩, -⟩ := hexit (Icc z₀ b ×ˢ (Icc 0 1 ×ˢ Icc (-(c / (2 * D))) 0))
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)) (subset_univ _)
    have htI : max c' z₀ ∈ I := by
      rcases max_cases c' z₀ with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
      · exact hc'I
      · exact hz₀I
    have htb : max c' z₀ ≤ b := by
      by_contra h
      exact hbI (hIcc z₀ hz₀I _ htI ⟨hb, (not_le.1 h).le⟩)
    obtain ⟨h1, h2, h3, h4, -⟩ :=
      bounds_of_mem_trappingTriangle hD hr hc0 (hTx _ htI (le_max_right _ _))
    exact hc' _ htI (le_max_left _ _)
      ⟨⟨le_max_right _ _, htb⟩, ⟨h1.le, h2.le⟩, ⟨h3.le, h4.le⟩⟩
  -- glue the branch and the maximal solution at `z₀`
  have hUd := hasDerivAt_ite (f := U₀) (g := fun t => (x t).1) (f' := V₀)
    (g' := fun t => (x t).2) (fun z hz => (hode₀ z (hz.trans_lt hz₀)).1)
    (fun z hz => (hodex z (hIci z hz)).1) (by rw [hx0]) (by rw [hx0])
  have hVd := hasDerivAt_ite (f := V₀) (g := fun t => (x t).2)
    (f' := fun z => (-(c * V₀ z) - r * U₀ z * (1 - U₀ z)) / D)
    (g' := fun z => (-(c * (x z).2) - r * (x z).1 * (1 - (x z).1)) / D)
    (fun z hz => (hode₀ z (hz.trans_lt hz₀)).2) (fun z hz => (hodex z (hIci z hz)).2)
    (by rw [hx0]) (by rw [hx0])
  set Ug : ℝ → ℝ := fun t => if t < z₀ then U₀ t else (x t).1 with hUg
  set Vg : ℝ → ℝ := fun t => if t < z₀ then V₀ t else (x t).2 with hVg
  have hW : IsWaveProfile D r c Ug Vg := fun z => by
    refine ⟨hUd z, (hVd z).congr_deriv ?_⟩
    simp only [hUg, hVg]
    split_ifs <;> rfl
  have hq : ∀ z < 0, 0 < Ug z ∧ Ug z < 1 ∧ Vg z < 0 := by
    intro z hz
    simp only [hUg, hVg]
    split_ifs with h
    · exact hq₀ z hz
    · obtain ⟨h1, h2, -, h4, -⟩ :=
        bounds_of_mem_trappingTriangle hD hr hc0 (hTx z (hIci z (not_lt.1 h)) (not_lt.1 h))
      exact ⟨h1, h2, h4⟩
  have hev : ∀ᶠ t in atBot, t < z₀ := eventually_lt_atBot z₀
  exact exists_isFront_of_global_unstableBranch hD hr hc ⟨Ug, Vg, hW, hq,
    hU₀.congr' (hev.mono fun t ht => (ite_eq_left ht).symm),
    hV₀.congr' (hev.mono fun t ht => (ite_eq_left ht).symm)⟩

end Continuation

end MathlibExt.Analysis.ODE.PlanarShooting
