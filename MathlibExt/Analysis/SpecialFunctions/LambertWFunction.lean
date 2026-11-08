/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Lambert W function, principal real branch (Ouellet JIS VOL20, rank 320)

Source contract, rank 320, lexical id `jis_term_6c376920fa7bc177f6acc4c7`,
semantic id `jis_sem_4b8befd1d7e70075080d07cc`.

Ouellet, JIS VOL20, `ou2.tex`, lines 426-432,
SHA256 `251582ff49dbfc57f6d80b409c0ecedd8c6c27dc64a7cdcf3ce987ac03cfd78f`:
for `x > -1/e`, the Lambert W function is the inverse of the real-valued
function `h y = y * exp y` defined for `y > -1`, so that
`W x * exp (W x) = x`.

Correction ledger: Gessel, JIS VOL10, `gessel20.tex`, lines 271-295,
SHA256 `fd3e913cfabab90d18603e10bf02bce9651ae7e2c5129bdc4f72fdd4807ee5cd`,
prints `W z * exp (-W z) = z`. This is a sign typo. We follow Ouellet's
explicit principal real-branch definition `W z * exp (W z) = z`, corroborated
by Gessel's standard expansion at `-exp (-1)`.

This file formalizes the unique-preimage characterization of the principal real
branch on the open domain `x > -exp (-1)`, with preimages restricted to `y > -1`.
It does not yet define a `lambertW` function; the proved theorem is intended to
justify such a subtype-valued inverse.

`existsUnique_lambertMap_lower_preimage` gives the matching characterization of the lower
real branch `W₋₁`: every `x` with `-exp (-1) ≤ x < 0` has exactly one preimage `y ≤ -1`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The map `h y = y * exp y` whose restricted inverse is Lambert W.
Ouellet JIS VOL20 `ou2.tex` lines 426-432. -/
public noncomputable def lambertMap (y : ℝ) : ℝ :=
  y * Real.exp y

/-- Every `x > -exp (-1)` has exactly one preimage `y > -1` under `h`. -/
public theorem existsUnique_lambertMap_preimage (x : ℝ)
    (hx : -Real.exp (-1) < x) :
    ∃! y : { y : ℝ // -1 < y }, lambertMap y.val = x := by
  have hlam : ∀ y : ℝ, HasDerivAt lambertMap (1 * Real.exp y + y * Real.exp y) y := by
    intro y
    have h := (hasDerivAt_id y).mul (Real.hasDerivAt_exp y)
    -- `lambertMap` unfolds to `fun y => y * Real.exp y`.
    change HasDerivAt lambertMap (1 * Real.exp y + y * Real.exp y) y
    exact h
  have hderiv_eq : ∀ y : ℝ, deriv lambertMap y = Real.exp y * (1 + y) := by
    intro y
    have e := (hlam y).deriv
    have : 1 * Real.exp y + y * Real.exp y = Real.exp y * (1 + y) := by ring
    rw [this] at e
    exact e
  have hcont : Continuous lambertMap :=
    continuous_iff_continuousAt.mpr fun y => (hlam y).continuousAt
  have hcontOn : ContinuousOn lambertMap (Set.Ioi (-1 : ℝ)) :=
    hcont.continuousOn
  have hderiv_pos : ∀ y ∈ Set.Ioi (-1 : ℝ), 0 < deriv lambertMap y := by
    intro y hy
    have hy_lt : (-1 : ℝ) < y := hy
    rw [hderiv_eq y]
    exact mul_pos (Real.exp_pos y) (by linarith)
  have hmono : StrictMonoOn lambertMap (Set.Ioi (-1 : ℝ)) :=
    strictMonoOn_of_deriv_pos (convex_Ioi _) hcontOn (by
      intro y hy
      rw [IsOpen.interior_eq isOpen_Ioi] at hy
      exact hderiv_pos y hy)
  have hinj : Set.InjOn lambertMap (Set.Ioi (-1 : ℝ)) := hmono.injOn
  have huniq_gen : ∀ y₁ y₂ : { y : ℝ // -1 < y },
      lambertMap y₁.val = x → lambertMap y₂.val = x → y₁ = y₂ := by
    intro y₁ y₂ h1 h2
    have heq : lambertMap y₁.val = lambertMap y₂.val := by rw [h1, h2]
    have hval_eq : y₁.val = y₂.val :=
      hinj y₁.property y₂.property heq
    exact Subtype.ext hval_eq
  -- Upper bound: `lambertMap (max x 0) ≥ x` since `exp ≥ 1` there.
  have hb_nonneg : (0 : ℝ) ≤ max x 0 := le_max_right x 0
  have hbx : x ≤ max x 0 := le_max_left x 0
  have hb_mem : max x 0 ∈ Set.Ioi (-1 : ℝ) := by
    change (-1 : ℝ) < max x 0
    linarith [hb_nonneg]
  have h1exp : (1 : ℝ) ≤ Real.exp (max x 0) := by
    have hexp0 := Real.add_one_le_exp (max x 0)
    linarith [hexp0, hb_nonneg]
  have hb_ge : x ≤ lambertMap (max x 0) := by
    change x ≤ max x 0 * Real.exp (max x 0)
    calc x ≤ max x 0 := hbx
      _ = max x 0 * 1 := by ring
      _ ≤ max x 0 * Real.exp (max x 0) :=
          mul_le_mul_of_nonneg_left h1exp hb_nonneg
  -- Lower bound: continuity at `-1` gives a point `a = -1 + δ / 2`
  -- in the domain with `lambertMap a < x`.
  have h_neg1 : lambertMap (-1) = -Real.exp (-1) := by
    change (-1 : ℝ) * Real.exp (-1) = -Real.exp (-1)
    ring
  have h_lt_neg1 : lambertMap (-1) < x := by
    rw [h_neg1]
    exact hx
  have h_eps_pos : 0 < x - lambertMap (-1) := by linarith
  have hcont_neg1 : ContinuousAt lambertMap (-1) := hcont.continuousAt
  obtain ⟨δ, hδ_pos, hδ_ball⟩ :=
    Metric.continuousAt_iff.mp hcont_neg1 _ h_eps_pos
  have hδ2_pos : 0 < δ / 2 := by linarith
  have ha_pos : (-1 : ℝ) < -1 + δ / 2 := by linarith
  have ha_mem : -1 + δ / 2 ∈ Set.Ioi (-1 : ℝ) := ha_pos
  have hdist_a : dist (-1 + δ / 2) (-1) < δ := by
    rw [Real.dist_eq]
    have hsub : -1 + δ / 2 - (-1 : ℝ) = δ / 2 := by ring
    rw [hsub, abs_of_pos hδ2_pos]
    linarith
  have hdist_h :=
    hδ_ball hdist_a
  rw [Real.dist_eq, abs_lt] at hdist_h
  obtain ⟨_, habs_right⟩ := hdist_h
  have ha_lt : lambertMap (-1 + δ / 2) < x := by linarith
  have hab_lt : lambertMap (-1 + δ / 2) < lambertMap (max x 0) :=
    lt_of_lt_of_le ha_lt hb_ge
  have hab_le : -1 + δ / 2 ≤ max x 0 := by
    by_contra hcon
    rw [not_le] at hcon
    have hmono_lt : lambertMap (max x 0) < lambertMap (-1 + δ / 2) :=
      hmono hb_mem ha_mem hcon
    linarith
  have hcont_Icc : ContinuousOn lambertMap (Set.Icc (-1 + δ / 2) (max x 0)) :=
    hcontOn.mono (by
      intro y hy
      change (-1 : ℝ) < y
      exact lt_of_lt_of_le ha_pos hy.1)
  rcases lt_or_eq_of_le hb_ge with hx_lt | hx_eq
  · have hIoo_mem :
        x ∈ Set.Ioo (lambertMap (-1 + δ / 2)) (lambertMap (max x 0)) :=
      ⟨ha_lt, hx_lt⟩
    obtain ⟨c, hc_mem, hc_eq⟩ :=
      intermediate_value_Ioo hab_le hcont_Icc hIoo_mem
    have hc_pos : (-1 : ℝ) < c := lt_trans ha_pos hc_mem.1
    refine ⟨⟨c, hc_pos⟩, hc_eq, fun y hy => ?_⟩
    exact huniq_gen y ⟨c, hc_pos⟩ hy hc_eq
  · have hb_symm : lambertMap (max x 0) = x := hx_eq.symm
    have hb_pos : (-1 : ℝ) < max x 0 := hb_mem
    refine ⟨⟨max x 0, hb_pos⟩, hb_symm, fun y hy => ?_⟩
    exact huniq_gen y ⟨max x 0, hb_pos⟩ hy hb_symm

/-- Lower real branch `W₋₁`: every `x` with `-exp (-1) ≤ x < 0` has exactly one preimage
`y ≤ -1` under `h y = y * exp y`. Existence uses `h (-1) = -exp (-1)`, `h y → 0` as
`y → -∞` and the intermediate value theorem; uniqueness uses `h' y = exp y * (1 + y) < 0`
on `y < -1`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 3.1 (the lower branch `W₋₁`). -/
public theorem existsUnique_lambertMap_lower_preimage {x : ℝ}
    (hx1 : -Real.exp (-1) ≤ x) (hx0 : x < 0) :
    ∃! y : { y : ℝ // y ≤ -1 }, lambertMap y.val = x := by
  have hlam : ∀ y : ℝ, HasDerivAt lambertMap (Real.exp y * (1 + y)) y := by
    intro y
    have h := (hasDerivAt_id y).mul (Real.hasDerivAt_exp y)
    have e : 1 * Real.exp y + y * Real.exp y = Real.exp y * (1 + y) := by ring
    change HasDerivAt lambertMap (1 * Real.exp y + y * Real.exp y) y at h
    rw [e] at h
    exact h
  have hcont : Continuous lambertMap :=
    continuous_iff_continuousAt.mpr fun y => (hlam y).continuousAt
  have hanti : StrictAntiOn lambertMap (Set.Iic (-1 : ℝ)) := by
    refine strictAntiOn_of_deriv_neg (convex_Iic _) hcont.continuousOn ?_
    intro y hy
    rw [interior_Iic] at hy
    rw [(hlam y).deriv]
    exact mul_neg_of_pos_of_neg (Real.exp_pos y) (by linarith [show y < -1 from hy])
  have ht : Filter.Tendsto lambertMap Filter.atBot (nhds 0) := by
    have h2 : Filter.Tendsto (fun y : ℝ => -((-y) ^ 1 * Real.exp (-(-y)))) Filter.atBot
        (nhds (-0)) :=
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp Filter.tendsto_neg_atBot_atTop).neg
    change Filter.Tendsto (fun y : ℝ => y * Real.exp y) Filter.atBot (nhds 0)
    simpa [Function.comp_def] using h2
  obtain ⟨y₀, hy₀⟩ := Filter.eventually_atBot.1
    ((ht.eventually (lt_mem_nhds hx0)).and (Filter.eventually_le_atBot (-1 : ℝ)))
  have h1 := hy₀ (y₀ ⊓ -1) inf_le_left
  have hl : lambertMap (-1) = -Real.exp (-1) := by
    change (-1 : ℝ) * Real.exp (-1) = -Real.exp (-1)
    ring
  obtain ⟨y, hy, hyx⟩ := intermediate_value_Icc' (show y₀ ⊓ -1 ≤ -1 from inf_le_right)
    hcont.continuousOn ⟨by rw [hl]; exact hx1, h1.1.le⟩
  refine ⟨⟨y, hy.2⟩, hyx, fun z hz => Subtype.ext ?_⟩
  exact hanti.injOn z.property hy.2 (hz.trans hyx.symm)

end

end MetaMathlibExt
