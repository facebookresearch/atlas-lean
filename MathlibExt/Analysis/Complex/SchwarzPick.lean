/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Complex.Schwarz

@[expose] public section

/-!
# Schwarz–Pick theorem for the disc
-/

namespace MathlibExt.Analysis.Complex.SchwarzPick

/-- Key norm-square identity for the disc automorphism:
`‖1 - conj q * p‖² - ‖p - q‖² = (1 - ‖p‖²) * (1 - ‖q‖²)`. -/
private lemma schwarzPick_normSq_key (p q : ℂ) :
    Complex.normSq (1 - star q * p) - Complex.normSq (p - q)
      = (1 - Complex.normSq p) * (1 - Complex.normSq q) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- For points of the open unit disc, the M\"obius denominator is nonzero. -/
private lemma schwarzPick_denom_ne_zero {p q : ℂ} (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    1 - star q * p ≠ 0 := by
  intro h
  have h1 : star q * p = 1 := (sub_eq_zero.mp h).symm
  have h2 : ‖star q * p‖ = 1 := by rw [h1, norm_one]
  rw [norm_mul, norm_star] at h2
  have hq1 : ‖q‖ ≤ 1 := le_of_lt hq
  have hlt : ‖q‖ * ‖p‖ < 1 := by
    calc ‖q‖ * ‖p‖ ≤ 1 * ‖p‖ := mul_le_mul_of_nonneg_right hq1 (norm_nonneg _)
      _ = ‖p‖ := one_mul _
      _ < 1 := hp
  linarith

/-- The M\"obius expression maps the disc into itself. -/
private lemma schwarzPick_mobius_lt_one {p q : ℂ} (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    ‖(p - q) / (1 - star q * p)‖ < 1 := by
  have hden : 1 - star q * p ≠ 0 := schwarzPick_denom_ne_zero hp hq
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hden)]
  have hkey := schwarzPick_normSq_key p q
  have hp2 : Complex.normSq p < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    calc ‖p‖ ^ 2 < 1 ^ 2 := pow_lt_pow_left₀ hp (norm_nonneg _) two_ne_zero
      _ = 1 := one_pow 2
  have hq2 : Complex.normSq q < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    calc ‖q‖ ^ 2 < 1 ^ 2 := pow_lt_pow_left₀ hq (norm_nonneg _) two_ne_zero
      _ = 1 := one_pow 2
  have hpos : 0 < (1 - Complex.normSq p) * (1 - Complex.normSq q) := by
    apply mul_pos <;> linarith [Complex.normSq_nonneg p, Complex.normSq_nonneg q]
  have hsq : Complex.normSq (p - q) < Complex.normSq (1 - star q * p) := by linarith
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq

/-- The map `u ↦ (u + w) / (1 + conj w * u)` inverts `z ↦ (z - w) / (1 - conj w * z)`. -/
private lemma schwarzPick_psi_phi {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    ((z - w) / (1 - star w * z) + w) / (1 + star w * ((z - w) / (1 - star w * z))) = z := by
  have hd : 1 - star w * z ≠ 0 := schwarzPick_denom_ne_zero hz hw
  have hD : (1 - star w * z) + star w * (z - w) ≠ 0 := by
    have h := schwarzPick_denom_ne_zero hw hw
    have heq : (1 - star w * z) + star w * (z - w) = 1 - star w * w := by ring
    rwa [heq]
  have e2 : 1 + star w * ((z - w) / (1 - star w * z))
      = ((1 - star w * z) + star w * (z - w)) / (1 - star w * z) := by
    have h1 : star w * ((z - w) / (1 - star w * z))
        = (star w * (z - w)) / (1 - star w * z) := by rw [mul_div_assoc]
    rw [h1]
    have h2 : (1 : ℂ) + (star w * (z - w)) / (1 - star w * z)
        = (1 * (1 - star w * z) + star w * (z - w)) / (1 - star w * z) :=
      add_div' _ _ _ hd
    rwa [one_mul] at h2
  have hd2 : 1 + star w * ((z - w) / (1 - star w * z)) ≠ 0 :=
    e2.symm ▸ div_ne_zero hD hd
  have e3 : (z - w) + w * (1 - star w * z)
      = z * ((1 - star w * z) + star w * (z - w)) := by ring
  rw [div_eq_iff hd2, div_add' _ _ _ hd, e2, ← mul_div_assoc, div_eq_div_iff hd hd, e3]

/--
**Schwarz–Pick lemma.** Let $f : \mathbb{C} \to \mathbb{C}$ be holomorphic on the open unit disc
$\mathbb{D} = \{z : |z| < 1\}$ and map $\mathbb{D}$ into itself. Then for all $z, w \in \mathbb{D}$,
$|f(z) - f(w)| / |1 - \overline{f(w)}\, f(z)| \le |z - w| / |1 - \bar w z|$.

Source: Schwarz–Pick lemma, G. Pick (1916), building on Schwarz's lemma; see Ahlfors; Lean is
holomorphic self-map of disc pseudo-hyperbolic distance nonincreasing inequality with star conj.

Proves `Wanted` entry `schwarzPick`.
-/
theorem schwarzPick
    {f : ℂ → ℂ}
    (hf_diff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hf_maps : Set.MapsTo f (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1)) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1,
      ‖(f z - f w) / (1 - star (f w) * f z)‖ ≤ ‖(z - w) / (1 - star w * z)‖ := by
  intro z hz w hw
  have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hwn : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have han : ‖f w‖ < 1 := mem_ball_zero_iff.mp (hf_maps hw)
  set ψ : ℂ → ℂ := fun u => (u + w) / (1 + star w * u) with hψdef
  have hψden : ∀ u ∈ Metric.ball (0 : ℂ) 1, 1 + star w * u ≠ 0 := by
    intro u hu
    have hun : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
    have hneg : ‖-w‖ < 1 := by simpa using hwn
    have h := schwarzPick_denom_ne_zero (p := u) (q := -w) hun hneg
    simpa [star_neg, sub_neg_eq_add] using h
  have hψdiff : DifferentiableOn ℂ ψ (Metric.ball (0 : ℂ) 1) := by
    have hnum : DifferentiableOn ℂ (fun u : ℂ => u + w) (Metric.ball (0 : ℂ) 1) := by
      fun_prop
    have hden : DifferentiableOn ℂ (fun u : ℂ => 1 + star w * u) (Metric.ball (0 : ℂ) 1) := by
      fun_prop
    have h := hnum.div hden hψden
    rw [hψdef]
    exact h
  have hψmaps : Set.MapsTo ψ (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    intro u hu
    have hun : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
    have hneg : ‖-w‖ < 1 := by simpa using hwn
    have h := schwarzPick_mobius_lt_one (p := u) (q := -w) hun hneg
    have heq : ψ u = (u - -w) / (1 - star (-w) * u) := by
      simp [hψdef, star_neg, sub_neg_eq_add]
    rw [heq, mem_ball_zero_iff]
    exact h
  set g : ℂ → ℂ := fun u => (f (ψ u) - f w) / (1 - star (f w) * f (ψ u)) with hgdef
  have hcomp : DifferentiableOn ℂ (fun u => f (ψ u)) (Metric.ball (0 : ℂ) 1) := by
    have h := hf_diff.comp hψdiff hψmaps
    simpa [Function.comp_def] using h
  have hgnum : DifferentiableOn ℂ (fun u => f (ψ u) - f w) (Metric.ball (0 : ℂ) 1) :=
    hcomp.sub_const _
  have hgden : DifferentiableOn ℂ (fun u => 1 - star (f w) * f (ψ u)) (Metric.ball (0 : ℂ) 1) := by
    have h1 : DifferentiableOn ℂ (fun u => star (f w) * f (ψ u)) (Metric.ball (0 : ℂ) 1) :=
      (differentiableOn_const _).mul hcomp
    exact (differentiableOn_const _).sub h1
  have hgden_ne : ∀ u ∈ Metric.ball (0 : ℂ) 1, 1 - star (f w) * f (ψ u) ≠ 0 := by
    intro u hu
    have h1 : ψ u ∈ Metric.ball (0 : ℂ) 1 := hψmaps hu
    have h2 : f (ψ u) ∈ Metric.ball (0 : ℂ) 1 := hf_maps h1
    have hfn : ‖f (ψ u)‖ < 1 := mem_ball_zero_iff.mp h2
    exact schwarzPick_denom_ne_zero hfn han
  have hgdiff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1) := by
    have h := hgnum.div hgden hgden_ne
    rw [hgdef]
    exact h
  have hgmaps : Set.MapsTo g (Metric.ball (0 : ℂ) 1) (Metric.closedBall (0 : ℂ) 1) := by
    intro u hu
    have h1 : ψ u ∈ Metric.ball (0 : ℂ) 1 := hψmaps hu
    have h2 : f (ψ u) ∈ Metric.ball (0 : ℂ) 1 := hf_maps h1
    have hfn : ‖f (ψ u)‖ < 1 := mem_ball_zero_iff.mp h2
    have h := schwarzPick_mobius_lt_one (p := f (ψ u)) (q := f w) hfn han
    have heq : g u = (f (ψ u) - f w) / (1 - star (f w) * f (ψ u)) := by
      simp [hgdef]
    rw [heq, mem_closedBall_zero_iff]
    exact le_of_lt h
  have hgzero : g 0 = 0 := by
    have hψ0 : ψ 0 = w := by simp [hψdef]
    simp [hgdef, hψ0, sub_self]
  have hUmem : (z - w) / (1 - star w * z) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    exact schwarzPick_mobius_lt_one hzn hwn
  have hUn : ‖(z - w) / (1 - star w * z)‖ < 1 := mem_ball_zero_iff.mp hUmem
  have hSch := Complex.norm_le_norm_of_mapsTo_ball hgdiff hgmaps hgzero hUn
  have hψU : ψ ((z - w) / (1 - star w * z)) = z := by
    simp only [hψdef]
    exact schwarzPick_psi_phi hzn hwn
  have hgU : g ((z - w) / (1 - star w * z)) = (f z - f w) / (1 - star (f w) * f z) := by
    have hgg : g ((z - w) / (1 - star w * z))
        = (f (ψ ((z - w) / (1 - star w * z))) - f w) /
          (1 - star (f w) * f (ψ ((z - w) / (1 - star w * z)))) := by
      simp [hgdef]
    rw [hgg, hψU]
  rw [hgU] at hSch
  exact hSch

end MathlibExt.Analysis.Complex.SchwarzPick
