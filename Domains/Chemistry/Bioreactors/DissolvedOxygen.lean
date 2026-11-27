/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Real.Basic

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!

# Dissolved-oxygen balance with interfacial transfer

The dissolved-oxygen concentration `C` of a well-mixed liquid gains oxygen across the gas–liquid
interface at the volumetric rate `K_L a (C* - C)`: the overall liquid-phase flux
`N_A = K_L (c_A* - c_A)` times the interfacial area `a` per unit liquid volume. It loses oxygen
to uptake at the rate `u(t)` and is diluted at the rate `D(t)` by a feed that carries no oxygen:

  `C' = K_L a (C* - C) - u(t) - D(t) C`.

Below, `kLa` is `K_L a`, `Cstar` the saturation concentration `C*` and `Ccrit` a critical
concentration. A solution on the horizon `[0, T]` is a function `C : ℝ → ℝ` with
`HasDerivWithinAt C (kLa * (Cstar - C t) - u t - D t * C t) (Icc 0 T) t` at every `t ∈ [0, T]`,
that is, differentiable on `[0, T]` with one-sided derivatives at the endpoints, the form of the
solutions that Mathlib's Picard–Lindelöf theorem provides. The results bound every such solution
and do not address its existence; the inputs `u` and `D` need only be nonnegative on `[0, T]`,
not continuous. The equation must hold at every time of `[0, T]`, so an input with a jump, such
as a piecewise-constant feed, in general has no solution in this sense across the jump, since a
derivative has no jump discontinuities; the results then apply piece by piece, on each interval
between jumps, starting from the value the previous interval ends at.

## Main results

All in the namespace `Chemistry.Bioreactors.DissolvedOxygen`:

* `le_of_uptake_add_dilution_le_transfer`: if `C(0) ≥ C_crit` and
  `K_L a (C* - C_crit) ≥ u(t) + D(t) C_crit` on `[0, T]`, then `C ≥ C_crit` on `[0, T]`.
* `mem_Icc_of_uptake_le_transfer`: if `u ≤ K_L a C*` on `[0, T]` and `C(0) ∈ [0, C*]`, then `C`
  stays in `[0, C*]` on `[0, T]`.
* `uptake_add_dilution_le_transfer_iff`: for `K_L a > 0` and constant inputs `u₀` and `D₀ ≥ 0`,
  `K_L a (C* - C_crit) ≥ u₀ + D₀ C_crit` holds if and only if
  `C_eq = (K_L a C* - u₀) / (K_L a + D₀) ≥ C_crit`.
* `balance`: the three statements together.

## Proof

Each bound is a barrier argument. The function `w = C - C_crit` (for the upper bound,
`w = C* - C`) starts nonnegative and has `w' ≥ 0` wherever `w < 0`, so it stays nonnegative: for
every `ε > 0`, Mathlib's `image_le_of_deriv_right_lt_deriv_boundary` keeps `-w` below the barrier
`ε (1 + t)`.

## References

* L. Lamm and L. Jarboe, *Chemical Engineering Separations: A Handbook for Students*, LibreTexts,
  Section 1.2, Equation 3.4 (overall liquid-phase transfer `N_A = K_L (c_A* - c_Ab)`).

-/

@[expose] public section

open Set

namespace Chemistry.Bioreactors.DissolvedOxygen

/-- A function differentiable on `[0, T]` (one-sided at the endpoints) that is nonnegative at `0`
and has nonnegative derivative wherever it is negative stays nonnegative on `[0, T]`. -/
private theorem nonneg_of_deriv_nonneg_of_neg {w w' : ℝ → ℝ} {T : ℝ}
    (hw : ∀ t ∈ Icc 0 T, HasDerivWithinAt w (w' t) (Icc 0 T) t) (h0 : 0 ≤ w 0)
    (hneg : ∀ t ∈ Ico 0 T, w t < 0 → 0 ≤ w' t) :
    ∀ t ∈ Icc 0 T, 0 ≤ w t := by
  intro t ht
  by_contra hlt
  replace hlt := not_le.mp hlt
  have h1 : 0 < 1 + t := by linarith [ht.1]
  set ε := -w t / (2 * (1 + t)) with hε
  have hεpos : 0 < ε := div_pos (by linarith) (by linarith)
  have key := image_le_of_deriv_right_lt_deriv_boundary (a := 0) (b := T)
    (f := fun x ↦ -w x) (f' := fun x ↦ -w' x)
    (B := fun x ↦ ε * (1 + x)) (B' := fun _ ↦ ε * 1)
    (fun x hx ↦ (hw x hx).continuousWithinAt.neg)
    (fun x hx ↦ ((hw x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (Icc_subset_Icc_left hx.1))).neg)
    (by simp only [add_zero, mul_one]; linarith)
    (fun x ↦ ((hasDerivAt_id x).const_add 1).const_mul ε)
    (fun x hx heq ↦ by
      have hx0 : 0 < ε * (1 + x) := mul_pos hεpos (by linarith [hx.1])
      have := hneg x hx (by linarith)
      simp only [mul_one]
      linarith) ht
  have hεt : ε * (1 + t) = -w t / 2 := by
    rw [hε]
    field_simp
  linarith

/-- **Lower bound on dissolved oxygen.** Let $K_L a \ge 0$, let $D(t) \ge 0$ for every
$t \in [0, T]$, and let $C$ solve $C' = K_L a\,(C^* - C) - u(t) - D(t)\,C$ on $[0, T]$:
differentiable on $[0, T]$, with one-sided derivatives at the endpoints. If
$C(0) \ge C_{\mathrm{crit}}$ and
$K_L a\,(C^* - C_{\mathrm{crit}}) \ge u(t) + D(t)\,C_{\mathrm{crit}}$ for every $t \in [0, T]$, then
$C(t) \ge C_{\mathrm{crit}}$ for every $t \in [0, T]$. -/
theorem le_of_uptake_add_dilution_le_transfer {kLa Cstar Ccrit T : ℝ} {u D C : ℝ → ℝ}
    (hkLa : 0 ≤ kLa) (hD : ∀ t ∈ Icc 0 T, 0 ≤ D t)
    (hC : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt C (kLa * (Cstar - C t) - u t - D t * C t) (Icc 0 T) t)
    (hC0 : Ccrit ≤ C 0) (hcrit : ∀ t ∈ Icc 0 T, u t + D t * Ccrit ≤ kLa * (Cstar - Ccrit)) :
    ∀ t ∈ Icc 0 T, Ccrit ≤ C t := by
  have key := nonneg_of_deriv_nonneg_of_neg (w := fun t ↦ C t - Ccrit)
    (w' := fun t ↦ kLa * (Cstar - C t) - u t - D t * C t)
    (fun t ht ↦ (hC t ht).sub_const Ccrit) (by simpa using hC0) (fun t ht hlt ↦ by
      have ht' := Ico_subset_Icc_self ht
      have := mul_nonneg (add_nonneg hkLa (hD t ht')) (by linarith : 0 ≤ Ccrit - C t)
      nlinarith [hcrit t ht'])
  exact fun t ht ↦ sub_nonneg.mp (key t ht)

/-- **Dissolved oxygen stays between zero and saturation.** Let $K_L a \ge 0$, let $u(t) \ge 0$
and $D(t) \ge 0$ for every $t \in [0, T]$, and let $C$ solve
$C' = K_L a\,(C^* - C) - u(t) - D(t)\,C$ on $[0, T]$: differentiable on $[0, T]$, with one-sided
derivatives at the endpoints. If $u(t) \le K_L a\,C^*$ for every $t \in [0, T]$ and
$C(0) \in [0, C^*]$, then $C(t) \in [0, C^*]$ for every $t \in [0, T]$. -/
theorem mem_Icc_of_uptake_le_transfer {kLa Cstar T : ℝ} {u D C : ℝ → ℝ} (hkLa : 0 ≤ kLa)
    (hu : ∀ t ∈ Icc 0 T, 0 ≤ u t) (hD : ∀ t ∈ Icc 0 T, 0 ≤ D t)
    (hC : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt C (kLa * (Cstar - C t) - u t - D t * C t) (Icc 0 T) t)
    (huC : ∀ t ∈ Icc 0 T, u t ≤ kLa * Cstar) (hC0 : C 0 ∈ Icc 0 Cstar) :
    ∀ t ∈ Icc 0 T, C t ∈ Icc 0 Cstar := by
  have hCstar : 0 ≤ Cstar := hC0.1.trans hC0.2
  have lower := le_of_uptake_add_dilution_le_transfer hkLa hD hC hC0.1 (fun t ht ↦ by
    simpa using huC t ht)
  have upper := nonneg_of_deriv_nonneg_of_neg (w := fun t ↦ Cstar - C t)
    (w' := fun t ↦ -(kLa * (Cstar - C t) - u t - D t * C t))
    (fun t ht ↦ (hC t ht).const_sub Cstar) (by simpa using hC0.2) (fun t ht hlt ↦ by
      have ht' := Ico_subset_Icc_self ht
      have h1 := mul_nonneg hkLa (by linarith : 0 ≤ C t - Cstar)
      have h2 := mul_nonneg (hD t ht') (by linarith : 0 ≤ C t)
      nlinarith [hu t ht'])
  exact fun t ht ↦ ⟨lower t ht, sub_nonneg.mp (upper t ht)⟩

/-- **Critical-oxygen condition for constant inputs.** Let $K_L a > 0$. For a constant uptake
rate $u_0$ and a constant dilution rate $D_0 \ge 0$,
$K_L a\,(C^* - C_{\mathrm{crit}}) \ge u_0 + D_0\,C_{\mathrm{crit}}$ holds if and only if
$C_{\mathrm{eq}} = (K_L a\,C^* - u_0)/(K_L a + D_0) \ge C_{\mathrm{crit}}$, where $C_{\mathrm{eq}}$
is the concentration at which $K_L a\,(C^* - C) - u_0 - D_0\,C$ vanishes. -/
theorem uptake_add_dilution_le_transfer_iff {kLa Cstar u₀ D₀ Ccrit : ℝ} (hkLa : 0 < kLa)
    (hD₀ : 0 ≤ D₀) :
    u₀ + D₀ * Ccrit ≤ kLa * (Cstar - Ccrit) ↔ Ccrit ≤ (kLa * Cstar - u₀) / (kLa + D₀) := by
  rw [le_div_iff₀ (by linarith)]
  constructor <;> intro h <;> linarith

/-- **Dissolved-oxygen balance with interfacial transfer.** Let $K_L a > 0$ and $C^*$ be
constants, let the uptake rate $u(t)$ and the dilution rate $D(t)$ be nonnegative for every $t$ in
the horizon $[0, T]$, and let $C$ solve $C' = K_L a\,(C^* - C) - u(t) - D(t)\,C$ on $[0, T]$:
differentiable on $[0, T]$, with one-sided derivatives at the endpoints. Then:

1. If $u(t) \le K_L a\,C^*$ for every $t \in [0, T]$ and $C(0) \in [0, C^*]$, then
   $C(t) \in [0, C^*]$ for every $t \in [0, T]$.
2. For every $C_{\mathrm{crit}}$, if $C(0) \ge C_{\mathrm{crit}}$ and
   $K_L a\,(C^* - C_{\mathrm{crit}}) \ge u(t) + D(t)\,C_{\mathrm{crit}}$ for every $t \in [0, T]$,
   then $C(t) \ge C_{\mathrm{crit}}$ for every $t \in [0, T]$.
3. If $T \ge 0$ and $u = u_0$ and $D = D_0$ are constant on $[0, T]$, the pointwise condition of
   2, $K_L a\,(C^* - C_{\mathrm{crit}}) \ge u(t) + D(t)\,C_{\mathrm{crit}}$ for every
   $t \in [0, T]$, holds if and only if
   $C_{\mathrm{eq}} = (K_L a\,C^* - u_0)/(K_L a + D_0) \ge C_{\mathrm{crit}}$.

No continuity of $u$ or $D$ is needed. -/
theorem balance {kLa Cstar T : ℝ} {u D C : ℝ → ℝ} (hkLa : 0 < kLa)
    (hu : ∀ t ∈ Icc 0 T, 0 ≤ u t) (hD : ∀ t ∈ Icc 0 T, 0 ≤ D t)
    (hC : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt C (kLa * (Cstar - C t) - u t - D t * C t) (Icc 0 T) t) :
    ((∀ t ∈ Icc 0 T, u t ≤ kLa * Cstar) → C 0 ∈ Icc 0 Cstar →
        ∀ t ∈ Icc 0 T, C t ∈ Icc 0 Cstar) ∧
      (∀ Ccrit, Ccrit ≤ C 0 → (∀ t ∈ Icc 0 T, u t + D t * Ccrit ≤ kLa * (Cstar - Ccrit)) →
        ∀ t ∈ Icc 0 T, Ccrit ≤ C t) ∧
      (∀ u₀ D₀ Ccrit, 0 ≤ T → (∀ t ∈ Icc 0 T, u t = u₀) → (∀ t ∈ Icc 0 T, D t = D₀) →
        ((∀ t ∈ Icc 0 T, u t + D t * Ccrit ≤ kLa * (Cstar - Ccrit)) ↔
          Ccrit ≤ (kLa * Cstar - u₀) / (kLa + D₀))) := by
  refine ⟨fun huC hC0 ↦ mem_Icc_of_uptake_le_transfer hkLa.le hu hD hC huC hC0,
    fun Ccrit hC0 hcrit ↦ le_of_uptake_add_dilution_le_transfer hkLa.le hD hC hC0 hcrit,
    fun u₀ D₀ Ccrit hT hu₀ hD₀ ↦ ?_⟩
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  rw [← uptake_add_dilution_le_transfer_iff hkLa (hD₀ 0 h0 ▸ hD 0 h0)]
  constructor
  · intro h
    simpa [hu₀ 0 h0, hD₀ 0 h0] using h 0 h0
  · intro h t ht
    rw [hu₀ t ht, hD₀ t ht]
    exact h

end Chemistry.Bioreactors.DissolvedOxygen
