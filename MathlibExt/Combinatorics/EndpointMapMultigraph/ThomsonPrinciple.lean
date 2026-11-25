/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.EffectiveResistance

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Thomson's principle

For a finite loopless multigraph with positive conductances `w`, a unit flow from `s` to `t` is an
edge function `θ` (with `θ e` the amount sent from `end₁ e` to `end₂ e`) whose net outflow
`(B θ)(x) = ∑_{end₁ e = x} θ e - ∑_{end₂ e = x} θ e` is `1` at `s`, `-1` at `t` and `0`
elsewhere; its energy is `∑_e θ_e² / w_e`. Thomson's principle says that the unit current flow has
strictly the least energy among unit flows, and that this least energy is the effective resistance
(R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016,
corrected online version of 19 August 2026, Section 2.4: Thomson's principle, equations (2.7) and
(2.10), and Exercise 2.13).

The effective resistance is `EndpointMapMultigraph.effectiveResistance`, the reciprocal of the
Dirichlet-principle minimum; this module therefore also proves the duality between Thomson's and
Dirichlet's principles (Lyons and Peres, Exercise 2.13).

* `flowEnergy_eq_add_flowEnergy_sub`: the Pythagorean identity (2.10),
  `E(θ) = R_eff(s, t) + E(θ - i)` with `i` the unit current;
* `effectiveResistance_le_flowEnergy`: every unit flow has energy at least `R_eff(s, t)`;
* `flowEnergy_eq_effectiveResistance_iff`: equality holds only for the unit current;
* `isLeast_flowEnergy`: when `s` and `t` are connected, `R_eff(s, t)` is the minimum energy of a
  unit flow;
* `isLeast_dirichletEnergy`: Dirichlet's principle, the infimum defining `C_eff(s, t)` is attained.
-/

@[expose] public section

namespace EndpointMapMultigraph

open Matrix

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E] [Fintype V]
  (end₁ end₂ : E → V)

/-- **Energy of an edge function.** For edge conductances `w` (resistances `1 / w e`), the energy
of `θ : E → ℝ` is `∑_e θ_e² / w_e`, the sum of resistance times squared flow (R. Lyons and
Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online
version of 19 August 2026, Section 2.4, Definition of energy `E(θ) := ‖θ‖²_r`). -/
noncomputable def flowEnergy (w θ : E → ℝ) : ℝ :=
  ∑ e, θ e ^ 2 / w e

/-- **Unit flow.** The edge function `θ` is a unit flow from `s` to `t`: its net outflow
`(B θ)(x) = ∑_{end₁ e = x} θ e - ∑_{end₂ e = x} θ e`, where `B` is the oriented incidence matrix,
is `1` at `s`, `-1` at `t` and `0` at every other vertex (R. Lyons and Y. Peres, *Probability on
Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026,
Section 2.4: a flow from `A` to `Z` of strength `1`, with `A = {s}` and `Z = {t}`). -/
def IsUnitFlow (s t : V) (θ : E → ℝ) : Prop :=
  orientedIncidence end₁ end₂ *ᵥ θ = Pi.single s 1 - Pi.single t 1

/-- **Current of a potential.** The edge function `e ↦ w_e (v(end₁ e) - v(end₂ e))`, the current
that Ohm's law assigns to the potential `v` (R. Lyons and Y. Peres, *Probability on Trees and
Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026,
Section 2.1, `i(x, y) := c(x, y)(v(x) - v(y))`). -/
def currentOf (w : E → ℝ) (v : V → ℝ) : E → ℝ :=
  fun e => w e * (v (end₁ e) - v (end₂ e))

/-- The net outflow of the current of `v` is `L v`. -/
private theorem orientedIncidence_mulVec_currentOf (w : E → ℝ) (v : V → ℝ) :
    orientedIncidence end₁ end₂ *ᵥ currentOf end₁ end₂ w v = laplacian end₁ end₂ w *ᵥ v := by
  rw [laplacian, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose]
  congr 1
  funext e
  rw [mulVec_diagonal, vecMul_orientedIncidence_apply]
  rfl

/-- **The current of a solution of `L v = δ_s - δ_t` is a unit flow** (Kirchhoff's node law for
the unit current; R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge
University Press 2016, corrected online version of 19 August 2026, Section 2.1). -/
theorem isUnitFlow_currentOf {w : E → ℝ} {s t : V} {v : V → ℝ}
    (hv : laplacian end₁ end₂ w *ᵥ v = Pi.single s 1 - Pi.single t 1) :
    IsUnitFlow end₁ end₂ s t (currentOf end₁ end₂ w v) := by
  rw [IsUnitFlow, orientedIncidence_mulVec_currentOf, hv]

/-- **Thomson's principle, Pythagorean form.** For positive conductances, if `L v = δ_s - δ_t`
and `θ` is a unit flow from `s` to `t`, then
`E(θ) = (v(s) - v(t)) + E(θ - i)`, where `i` is the current of `v`. This is the orthogonal
decomposition `‖θ‖²_r = ‖i‖²_r + ‖θ - i‖²_r` of R. Lyons and Y. Peres, *Probability on Trees and
Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026,
equation (2.10), together with `E(i) = v(s) - v(t)` from equation (2.7). -/
theorem flowEnergy_eq_add_flowEnergy_sub {w : E → ℝ} (hw : ∀ e, 0 < w e) {s t : V} {v : V → ℝ}
    (hv : laplacian end₁ end₂ w *ᵥ v = Pi.single s 1 - Pi.single t 1) {θ : E → ℝ}
    (hθ : IsUnitFlow end₁ end₂ s t θ) :
    flowEnergy w θ = (v s - v t) + flowEnergy w (θ - currentOf end₁ end₂ w v) := by
  classical
  set a : E → ℝ := fun e => v (end₁ e) - v (end₂ e) with ha
  -- `∑ θ_e a_e = v(s) - v(t)`
  have hcross : ∑ e, θ e * a e = v s - v t := by
    have h1 : v ⬝ᵥ (orientedIncidence end₁ end₂ *ᵥ θ) = v s - v t := by
      rw [hθ, dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one]
    rw [Matrix.dotProduct_mulVec] at h1
    rw [← h1, dotProduct]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [vecMul_orientedIncidence_apply, mul_comm]
  -- `∑ w_e a_e² = v(s) - v(t)`
  have hquad : ∑ e, w e * a e ^ 2 = v s - v t := by
    have h2 : v ⬝ᵥ (laplacian end₁ end₂ w *ᵥ v) = v s - v t := by
      rw [hv, dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one]
    rw [dotProduct_mulVec_laplacian] at h2
    exact h2
  have hterm : ∀ e, (θ - currentOf end₁ end₂ w v) e ^ 2 / w e =
      θ e ^ 2 / w e - 2 * (θ e * a e) + w e * a e ^ 2 := by
    intro e
    have hwe : w e ≠ 0 := (hw e).ne'
    simp only [Pi.sub_apply, currentOf, ha]
    field_simp
    ring
  rw [flowEnergy, flowEnergy, Finset.sum_congr rfl fun e _ => hterm e, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hcross, hquad]
  ring

omit [DecidableEq E] in
/-- **Energy is nonnegative.** For positive conductances, `∑_e θ_e² / w_e ≥ 0` for every edge
function `θ` (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University
Press 2016, corrected online version of 19 August 2026, Section 2.4, `E(θ) = ‖θ‖²_r`). -/
theorem flowEnergy_nonneg {w : E → ℝ} (hw : ∀ e, 0 < w e) (θ : E → ℝ) : 0 ≤ flowEnergy w θ :=
  Finset.sum_nonneg fun e _ => div_nonneg (sq_nonneg _) (hw e).le

/-- A unit flow yields a potential solving `L v = δ_s - δ_t`. -/
private theorem exists_laplacian_mulVec_of_isUnitFlow {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (hloop : ∀ e, end₁ e ≠ end₂ e) {s t : V} {θ : E → ℝ} (hθ : IsUnitFlow end₁ end₂ s t θ) :
    ∃ v : V → ℝ, laplacian end₁ end₂ w *ᵥ v = Pi.single s 1 - Pi.single t 1 := by
  have hmem : Pi.single s 1 - Pi.single t 1 ∈
      LinearMap.range (laplacian end₁ end₂ w).mulVecLin := by
    rw [range_laplacian_eq_range_orientedIncidence end₁ end₂ hw hloop]
    exact ⟨θ, hθ⟩
  obtain ⟨v, hv⟩ := hmem
  exact ⟨v, hv⟩

/-- **Thomson's principle.** In a finite loopless multigraph with positive conductances, every
unit flow `θ` from `s` to `t ≠ s` has energy at least the effective resistance:
`R_eff(s, t) ≤ ∑_e θ_e² / w_e` (R. Lyons and Y. Peres, *Probability on Trees and Networks*,
Cambridge University Press 2016, corrected online version of 19 August 2026, Section 2.4,
Thomson's principle with `A = {s}`, `Z = {t}`, combined with equation (2.7)). -/
theorem effectiveResistance_le_flowEnergy {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (hloop : ∀ e, end₁ e ≠ end₂ e) {s t : V} (hst : s ≠ t) {θ : E → ℝ}
    (hθ : IsUnitFlow end₁ end₂ s t θ) :
    effectiveResistance end₁ end₂ w s t ≤ flowEnergy w θ := by
  obtain ⟨v, hv⟩ := exists_laplacian_mulVec_of_isUnitFlow end₁ end₂ hw hloop hθ
  rw [(effectiveResistance_eq_sub_of_laplacian_mulVec end₁ end₂ (fun e => (hw e).le) hst hv).1,
    flowEnergy_eq_add_flowEnergy_sub end₁ end₂ hw hv hθ]
  linarith [flowEnergy_nonneg hw (θ - currentOf end₁ end₂ w v)]

/-- **Thomson's principle, equality case.** For positive conductances, `s ≠ t` and a potential `v`
with `L v = δ_s - δ_t`, a unit flow `θ` from `s` to `t` has energy exactly `R_eff(s, t)` if and
only if it is the unit current `e ↦ w_e (v(end₁ e) - v(end₂ e))`; every other unit flow has
strictly larger energy (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge
University Press 2016, corrected online version of 19 August 2026, Section 2.4, Thomson's
principle: `E(θ) > E(i)` unless `θ = i`). -/
theorem flowEnergy_eq_effectiveResistance_iff {w : E → ℝ} (hw : ∀ e, 0 < w e) {s t : V}
    (hst : s ≠ t) {v : V → ℝ} (hv : laplacian end₁ end₂ w *ᵥ v = Pi.single s 1 - Pi.single t 1)
    {θ : E → ℝ} (hθ : IsUnitFlow end₁ end₂ s t θ) :
    flowEnergy w θ = effectiveResistance end₁ end₂ w s t ↔ θ = currentOf end₁ end₂ w v := by
  rw [(effectiveResistance_eq_sub_of_laplacian_mulVec end₁ end₂ (fun e => (hw e).le) hst hv).1,
    flowEnergy_eq_add_flowEnergy_sub end₁ end₂ hw hv hθ]
  constructor
  · intro h
    have h0 : flowEnergy w (θ - currentOf end₁ end₂ w v) = 0 := by linarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun e _ => div_nonneg (sq_nonneg _) (hw e).le)).1 h0
    funext e
    have he := hall e (Finset.mem_univ e)
    rw [div_eq_zero_iff] at he
    rcases he with he | he
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 he
      simpa [sub_eq_zero] using this
    · exact absurd he (hw e).ne'
  · rintro rfl
    simp [flowEnergy]

/-- Two vertices in one component have a potential solving `L v = δ_s - δ_t`. -/
private theorem exists_laplacian_mulVec_of_reachable {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (hloop : ∀ e, end₁ e ≠ end₂ e) {s t : V}
    (hreach : (underlyingGraph end₁ end₂).Reachable s t) :
    ∃ v : V → ℝ, laplacian end₁ end₂ w *ᵥ v = Pi.single s 1 - Pi.single t 1 := by
  classical
  set G := underlyingGraph end₁ end₂
  -- `δ_s - δ_t` lies in the range of the incidence matrix
  have hmemB : Pi.single s 1 - Pi.single t 1 ∈
      LinearMap.range (orientedIncidence end₁ end₂).mulVecLin := by
    rw [mem_range_orientedIncidence_iff end₁ end₂ hloop]
    intro c
    have hc : G.connectedComponentMk s = G.connectedComponentMk t :=
      SimpleGraph.ConnectedComponent.eq.2 hreach
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, Pi.single_apply, Finset.sum_ite_eq',
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hc]
    exact sub_self _
  obtain ⟨θ₀, hθ₀⟩ := hmemB
  obtain ⟨v, hv⟩ := exists_laplacian_mulVec_of_isUnitFlow end₁ end₂ hw hloop
    (θ := θ₀) hθ₀
  exact ⟨v, hv⟩

/-- **Effective resistance as minimum energy (Thomson's principle).** In a finite loopless
multigraph with positive conductances, if `s ≠ t` lie in the same connected component then
`R_eff(s, t) = min { ∑_e θ_e² / w_e : θ a unit flow from s to t }`, the minimum being attained by
the unit current (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University
Press 2016, corrected online version of 19 August 2026, Exercise 2.13, first display). -/
theorem isLeast_flowEnergy {w : E → ℝ} (hw : ∀ e, 0 < w e) (hloop : ∀ e, end₁ e ≠ end₂ e)
    {s t : V} (hst : s ≠ t) (hreach : (underlyingGraph end₁ end₂).Reachable s t) :
    IsLeast {q | ∃ θ, IsUnitFlow end₁ end₂ s t θ ∧ q = flowEnergy w θ}
      (effectiveResistance end₁ end₂ w s t) := by
  obtain ⟨v, hv⟩ := exists_laplacian_mulVec_of_reachable end₁ end₂ hw hloop hreach
  refine ⟨⟨currentOf end₁ end₂ w v, isUnitFlow_currentOf end₁ end₂ hv, ?_⟩, ?_⟩
  · exact ((flowEnergy_eq_effectiveResistance_iff end₁ end₂ hw hst hv
      (isUnitFlow_currentOf end₁ end₂ hv)).2 rfl).symm
  · rintro q ⟨θ, hθ, rfl⟩
    exact effectiveResistance_le_flowEnergy end₁ end₂ hw hloop hst hθ

/-- **Dirichlet's principle.** In a finite loopless multigraph with positive conductances, if
`s ≠ t` lie in the same connected component then the effective conductance is attained:
`C_eff(s, t) = min { xᵀ L x : x(s) = 0, x(t) = 1 }`, the minimum being attained by the normalised
voltage `x = (v(s) - v) / (v(s) - v(t))` for any `v` with `L v = δ_s - δ_t` (R. Lyons and
Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online
version of 19 August 2026, Exercise 2.13, second display, with `F = 1 - x`, `A = {s}`,
`Z = {t}`). -/
theorem isLeast_dirichletEnergy {w : E → ℝ} (hw : ∀ e, 0 < w e) (hloop : ∀ e, end₁ e ≠ end₂ e)
    {s t : V} (hst : s ≠ t) (hreach : (underlyingGraph end₁ end₂).Reachable s t) :
    IsLeast {q | ∃ x : V → ℝ, x s = 0 ∧ x t = 1 ∧ q = x ⬝ᵥ (laplacian end₁ end₂ w *ᵥ x)}
      (effectiveConductance end₁ end₂ w s t) := by
  classical
  have hw0 : 0 ≤ w := fun e => (hw e).le
  obtain ⟨v, hv⟩ := exists_laplacian_mulVec_of_reachable end₁ end₂ hw hloop hreach
  obtain ⟨hR, hr⟩ := effectiveResistance_eq_sub_of_laplacian_mulVec end₁ end₂ hw0 hst hv
  set r := v s - v t with hrdef
  have hC : effectiveConductance end₁ end₂ w s t = r⁻¹ := by
    rw [← hR, effectiveResistance, inv_inv]
  set x : V → ℝ := r⁻¹ • (v s • (1 : V → ℝ) - v) with hx
  have hxs : x s = 0 := by simp [hx]
  have hxt : x t = 1 := by
    simp only [hx, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hr.ne'
  have hLx : laplacian end₁ end₂ w *ᵥ x = -(r⁻¹ • (Pi.single s 1 - Pi.single t 1)) := by
    rw [hx, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, laplacian_mulVec_one,
      smul_zero, zero_sub, hv, smul_neg]
  have hE : x ⬝ᵥ (laplacian end₁ end₂ w *ᵥ x) = r⁻¹ := by
    rw [hLx, dotProduct_neg, dotProduct_smul, dotProduct_sub, dotProduct_single,
      dotProduct_single, hxs, hxt, smul_eq_mul]
    ring
  refine ⟨⟨x, hxs, hxt, by rw [hE, hC]⟩, ?_⟩
  rintro q ⟨y, hy0, hy1, rfl⟩
  exact effectiveConductance_le_energy end₁ end₂ hw0 hy0 hy1

end EndpointMapMultigraph
