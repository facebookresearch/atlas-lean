/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# External film resistance of a catalyst pellet

The lumped steady balance follows from the surface-normalized pellet rate and the
external flux condition in Rawlings and Ekerdt, *Chemical Reactor Analysis and
Design Fundamentals*, 2nd ed., seventh printing, §7.4, Eqs. (7.24)–(7.28), and
§7.4.5, Eqs. (7.53)–(7.55). The closed form follows by solving the balance.
-/

namespace MathlibExt.Chemistry.CatalystPellets.ExternalFilmResistance

open Filter Topology

/-- In the first-order isothermal pellet model, `η` is the internal effectiveness factor
normalized at the surface. For `k ≥ 0`, `cb ≥ 0` and positive `η`, `km`, `Sp` and `Vp`,
the film coefficient per pellet volume is `Kf = (Sp / Vp) * km`. The steady surface balance
has a unique solution, at which the consumption rate per pellet volume is `kObs Kf * cb`,
where `kObs F = η * k * F / (η * k + F)`. This rate is zero when `k = 0`. When `k > 0`,
the reciprocal of `kObs Kf` is the sum of the internal and film reciprocals.
As `F` tends to infinity through the positive reals, `kObs F` tends to `η * k`; for `k > 0`,
the bulk-normalized effectiveness `kObs F / k` tends to `η`. -/
public theorem external_film_resistance (k cb η km Sp Vp : ℝ)
    (hk : 0 ≤ k) (_hcb : 0 ≤ cb) (hη : 0 < η) (hkm : 0 < km) (hSp : 0 < Sp) (hVp : 0 < Vp) :
    let Kf := (Sp / Vp) * km
    let kObs := fun F : ℝ ↦ η * k * F / (η * k + F)
    (∀ cs : ℝ, η * k * cs = Kf * (cb - cs) ↔ cs = Kf * cb / (η * k + Kf)) ∧
    (∀ cs : ℝ, η * k * cs = Kf * (cb - cs) → η * k * cs = kObs Kf * cb) ∧
    (k = 0 → kObs Kf * cb = 0) ∧
    (0 < k → 1 / kObs Kf = 1 / (η * k) + 1 / Kf) ∧
    Tendsto kObs atTop (𝓝 (η * k)) ∧
    (0 < k → Tendsto (fun F ↦ kObs F / k) atTop (𝓝 η)) := by
  intro Kf kObs
  have hKf : 0 < Kf := mul_pos (div_pos hSp hVp) hkm
  have hηk : 0 ≤ η * k := mul_nonneg hη.le hk
  have hden : 0 < η * k + Kf := add_pos_of_nonneg_of_pos hηk hKf
  have hsurface (cs : ℝ) :
      η * k * cs = Kf * (cb - cs) ↔ cs = Kf * cb / (η * k + Kf) := by
    rw [eq_div_iff hden.ne']
    constructor <;> intro h <;> linear_combination h
  have hlimit : Tendsto kObs atTop (𝓝 (η * k)) := by
    have hsmall : Tendsto (fun F : ℝ ↦ η * k * F⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_inv_atTop_zero.const_mul (η * k)
    have hnorm : Tendsto (fun F : ℝ ↦ 1 + η * k * F⁻¹) atTop (𝓝 1) := by
      simpa only [add_zero] using hsmall.const_add (1 : ℝ)
    have hnormalized :
        Tendsto (fun F : ℝ ↦ η * k / (1 + η * k * F⁻¹)) atTop (𝓝 (η * k)) := by
      have hdiv : Tendsto (fun F : ℝ ↦ η * k / (1 + η * k * F⁻¹)) atTop (𝓝 (η * k / 1)) :=
        (tendsto_const_nhds (x := η * k)).div hnorm one_ne_zero
      simpa only [div_one] using hdiv
    apply hnormalized.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with F hF
    have hsum : 0 < η * k + F := add_pos_of_nonneg_of_pos hηk hF
    have hnormPos : 0 < 1 + η * k * F⁻¹ :=
      add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hηk (inv_nonneg.mpr hF.le))
    dsimp only [kObs]
    field_simp [hF.ne', hsum.ne', hnormPos.ne']
    ring
  refine ⟨hsurface, ?_, ?_, ?_, hlimit, ?_⟩
  · intro cs hcs
    rw [(hsurface cs).mp hcs]
    dsimp only [kObs]
    ring
  · intro hzero
    simp [kObs, hzero]
  · intro hkpos
    have hηkPos : 0 < η * k := mul_pos hη hkpos
    dsimp only [kObs]
    field_simp [hηkPos.ne', hKf.ne', hden.ne']
    ring
  · intro hkpos
    simpa only [mul_div_assoc, div_self hkpos.ne', mul_one] using hlimit.div_const k

end MathlibExt.Chemistry.CatalystPellets.ExternalFilmResistance
