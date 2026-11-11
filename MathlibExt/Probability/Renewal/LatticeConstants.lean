/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Renewal limits: nonlattice constants versus lattice oscillation

For a negative-drift score random walk with Cramér (Lundberg) root `θ > 0`, the
key renewal theorem gives the tail of the all-time maximum `M` (equivalently of
the ladder-height renewal function) in the form `P(M ≥ t) ~ C e^{-θ t}`. This
file proves what happens around that limit, taking the renewal convergence
itself as an explicit hypothesis.

## Lattice case: oscillation

If the scores live on the lattice `h ℤ` (span `h > 0`), the tail `F t = P(M ≥ t)`
is a step function, `F t = F (h ⌈t / h⌉)`
(`measure_Ici_eq_measure_Ici_ceil` derives this from a lattice-supported law).
The renewal theorem then only gives convergence along the lattice,
`e^{θ k h} F (k h) → C`. From this we prove:

* `tendsto_scaled_tail_offset`: for each offset `0 ≤ s < h`,
  `e^{θ (k h - s)} F (k h - s) → e^{-θ s} C`;
* `limsup_scaled_tail_eq`: `limsup_{t → ∞} e^{θ t} F t = C`;
* `liminf_scaled_tail_eq`: `liminf_{t → ∞} e^{θ t} F t = e^{-θ h} C`;
* `not_tendsto_scaled_tail`: when `C > 0`, `e^{θ t} F t` has no limit over the reals,
  so the nonlattice conclusion `P(M ≥ t) ~ C e^{-θ t}` fails for every constant.

## Nonlattice case: constant identification

The Cramér–Lundberg constant comes from exponential tilting of a defective
renewal equation `Z t = z t + ∫ Z (t - y) dG(y)`. With
`G^θ = e^{θ y} G(dy)` (a probability measure when `∫ e^{θ y} dG = 1`):

* `tilted_renewal_eq`: `e^{θ t} Z t` solves the proper renewal equation driven
  by `G^θ` with input `e^{θ t} z t`;
* `integral_id_tilt`: the mean of `G^θ` is `∫ y e^{θ y} dG(y)`;
* `isProbabilityMeasure_tilted_of_integral_eq_one`: the Cramér root makes `G^θ`
  a probability measure;
* `tendsto_scaled_of_keyRenewal`: given the key renewal theorem for `G^θ`
  (explicit hypothesis), `e^{θ t} Z t → (∫_{(0,∞)} e^{θ s} z s ds) / ∫ y e^{θ y} dG(y)`;
* `integral_exp_mul_measureReal_Ioi`: the layer-cake identity
  `∫_{(0,∞)} e^{θ s} G(s, ∞) ds = (∫ e^{θ y} dG - G(ℝ)) / θ`;
* `tendsto_scaled_cramerLundberg`: for the ladder tail
  (`z t = 1_{t ≥ 0} G(t, ∞)`) the constant is
  `C = (1 - G(ℝ)) / (θ ∫ y e^{θ y} dG(y))`.

The key renewal theorem is not proved here; it is the hypothesis `hKRT`,
quantified over an admissibility relation `Adm` (in the classical statement:
the input is directly Riemann integrable and the solution is the locally bounded
one vanishing on `(-∞, 0)`), so that the hypothesis is the theorem itself rather
than its conclusion for the one tilted pair.

## Source

Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II,
2nd ed., §XI.1 (renewal theorem, lattice and nonlattice forms) and §XI.6
(defective renewal equations, exponential tilting, eq. (6.4)); Karlin and
Dembo, *Limit distributions of maximal segmental score among Markov-dependent
partial sums*, Adv. Appl. Probab. 24 (1992), Theorem A (lattice liminf/limsup
bounds `e^{-θ h} C ≤ ... ≤ C`). Roadmap target PROB-01.2.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Real
open scoped ENNReal NNReal

namespace MathlibExt.Probability.Renewal.LatticeConstants

/-! ### Lattice tails are step functions -/

/-- **Lattice tails are step functions.** If `μ` is concentrated on the lattice
`h ℤ` (`h > 0`), then `μ [t, ∞) = μ [h ⌈t / h⌉, ∞)`: the tail only changes at
lattice points. -/
theorem measure_Ici_eq_measure_Ici_ceil {μ : Measure ℝ} {h : ℝ} (hh : 0 < h)
    (hμ : ∀ᵐ x ∂μ, ∃ k : ℤ, x = k * h) (t : ℝ) :
    μ (Ici t) = μ (Ici (h * ⌈t / h⌉)) := by
  refine measure_congr (hμ.mono fun x hx => ?_)
  obtain ⟨k, rfl⟩ := hx
  change (t ≤ k * h) = (h * ⌈t / h⌉ ≤ k * h)
  refine propext ⟨fun htk => ?_, fun htk => ?_⟩
  · have : ⌈t / h⌉ ≤ k := Int.ceil_le.2 ((div_le_iff₀ hh).2 htk)
    have : (⌈t / h⌉ : ℝ) ≤ k := by exact_mod_cast this
    nlinarith
  · have h1 : t / h ≤ ⌈t / h⌉ := Int.le_ceil _
    have h2 : t ≤ h * ⌈t / h⌉ := by
      rw [div_le_iff₀ hh] at h1
      linarith
    linarith

/-! ### Lattice oscillation of the scaled tail -/

section Lattice

variable {F : ℝ → ℝ} {h θ C : ℝ}

/-- Factor the scaled tail at `t` through the lattice point `h ⌈t / h⌉`. -/
private lemma scaled_eq_lattice (hstep : ∀ t, F t = F (h * ⌈t / h⌉)) (t : ℝ) :
    exp (θ * t) * F t =
      exp (-(θ * (h * ⌈t / h⌉ - t))) * (exp (θ * (h * ⌈t / h⌉)) * F (h * ⌈t / h⌉)) := by
  rw [hstep t, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- For `0 ≤ s < h`, the point `k h - s` rounds up to the lattice point `k h`. -/
private lemma ceil_sub_offset (hh : 0 < h) (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hsh : s < h) :
    ⌈((k : ℝ) * h - s) / h⌉ = k := by
  rw [Int.ceil_eq_iff]
  have hsh' : s / h < 1 := (div_lt_one hh).2 hsh
  have hs0' : 0 ≤ s / h := div_nonneg hs0 hh.le
  have : ((k : ℝ) * h - s) / h = k - s / h := by field_simp
  rw [this]
  push_cast
  constructor <;> linarith

/-- **Lattice offsets.** If the tail is a lattice step function and the scaled
tail converges along the lattice, `e^{θ k h} F (k h) → C`, then at each offset
`0 ≤ s < h` below the lattice it converges to the shifted constant `e^{-θ s} C`. -/
theorem tendsto_scaled_tail_offset (hh : 0 < h) (hstep : ∀ t, F t = F (h * ⌈t / h⌉))
    (hlat : Tendsto (fun k : ℕ => exp (θ * (k * h)) * F (k * h)) atTop (𝓝 C))
    {s : ℝ} (hs0 : 0 ≤ s) (hsh : s < h) :
    Tendsto (fun k : ℕ => exp (θ * (k * h - s)) * F (k * h - s)) atTop
      (𝓝 (exp (-(θ * s)) * C)) := by
  refine (hlat.const_mul _).congr fun k => ?_
  have e : h * ((k : ℤ) : ℝ) = k * h := by push_cast; ring
  rw [scaled_eq_lattice hstep ((k : ℝ) * h - s), ceil_sub_offset hh k hs0 hsh, e]
  congr 2
  ring

/-- For `t > 0`, the scaled tail lies between `e^{-θ h}` times and `1` times its
value at the lattice point `h ⌈t / h⌉₊` above `t`. -/
private lemma scaled_mem_Icc (hh : 0 < h) (hθ : 0 ≤ θ) (hF : ∀ t, 0 ≤ F t)
    (hstep : ∀ t, F t = F (h * ⌈t / h⌉)) {t : ℝ} (ht : 0 < t) :
    exp (-(θ * h)) * (exp (θ * (⌈t / h⌉₊ * h)) * F (⌈t / h⌉₊ * h)) ≤ exp (θ * t) * F t ∧
      exp (θ * t) * F t ≤ exp (θ * (⌈t / h⌉₊ * h)) * F (⌈t / h⌉₊ * h) := by
  have hth : 0 ≤ t / h := div_nonneg ht.le hh.le
  have hcast : ((⌈t / h⌉ : ℤ) : ℝ) = (⌈t / h⌉₊ : ℝ) := (natCast_ceil_eq_intCast_ceil hth).symm
  have hlo : t / h ≤ ⌈t / h⌉₊ := Nat.le_ceil _
  have hhi : (⌈t / h⌉₊ : ℝ) < t / h + 1 := Nat.ceil_lt_add_one hth
  rw [div_le_iff₀ hh] at hlo
  have hhi' : (⌈t / h⌉₊ : ℝ) * h < t + h := by
    have := (mul_lt_mul_iff_left₀ hh).2 hhi
    rwa [add_mul, div_mul_cancel₀ _ hh.ne', one_mul] at this
  set a := exp (θ * (⌈t / h⌉₊ * h)) * F (⌈t / h⌉₊ * h) with ha_def
  have ha : 0 ≤ a := mul_nonneg (exp_pos _).le (hF _)
  have key : exp (θ * t) * F t = exp (-(θ * ((⌈t / h⌉₊ : ℝ) * h - t))) * a := by
    rw [scaled_eq_lattice hstep t, hcast, mul_comm h]
  rw [key]
  constructor
  · refine mul_le_mul_of_nonneg_right (exp_le_exp.2 ?_) ha
    have : (⌈t / h⌉₊ : ℝ) * h - t ≤ h := by linarith
    nlinarith
  · refine mul_le_of_le_one_left ha (exp_le_one_iff.2 ?_)
    have : 0 ≤ (⌈t / h⌉₊ : ℝ) * h - t := by linarith
    nlinarith

/-- The lattice sequence read off at `⌈t / h⌉₊` tends to `C` as `t → ∞`. -/
private lemma tendsto_lattice_ceil (hh : 0 < h)
    (hlat : Tendsto (fun k : ℕ => exp (θ * (k * h)) * F (k * h)) atTop (𝓝 C)) :
    Tendsto (fun t : ℝ => exp (θ * (⌈t / h⌉₊ * h)) * F (⌈t / h⌉₊ * h)) atTop (𝓝 C) :=
  hlat.comp (tendsto_nat_ceil_atTop.comp (tendsto_id.atTop_div_const hh))

/-- If `g ∘ φ → L` along a sequence `φ → ∞`, then `L ≤ limsup g`. -/
private lemma le_limsup_of_tendsto_comp {g : ℝ → ℝ} {φ : ℕ → ℝ} {L : ℝ}
    (hφ : Tendsto φ atTop atTop) (hg : Tendsto (g ∘ φ) atTop (𝓝 L))
    (hb : IsBoundedUnder (· ≤ ·) atTop g) : L ≤ limsup g atTop := by
  refine le_of_forall_sub_le fun ε hε => le_limsup_of_frequently_le ?_ hb
  exact hφ.frequently (hg.eventually (le_mem_nhds (sub_lt_self L hε))).frequently

/-- If `g ∘ φ → L` along a sequence `φ → ∞`, then `liminf g ≤ L`. -/
private lemma liminf_le_of_tendsto_comp {g : ℝ → ℝ} {φ : ℕ → ℝ} {L : ℝ}
    (hφ : Tendsto φ atTop atTop) (hg : Tendsto (g ∘ φ) atTop (𝓝 L))
    (hb : IsBoundedUnder (· ≥ ·) atTop g) : liminf g atTop ≤ L := by
  refine le_of_forall_pos_le_add fun ε hε => liminf_le_of_frequently_le ?_ hb
  exact hφ.frequently (hg.eventually (ge_mem_nhds (lt_add_of_pos_right L hε))).frequently

/-- The lattice points `k h` tend to infinity. -/
private lemma tendsto_mul_h (hh : 0 < h) : Tendsto (fun k : ℕ => (k : ℝ) * h) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_mul_const hh

/-- **Lattice limsup.** For a nonnegative lattice step tail with
`e^{θ k h} F (k h) → C` and `θ ≥ 0`, `limsup_{t → ∞} e^{θ t} F t = C`: the
lattice constant is the upper envelope of the scaled tail. -/
theorem limsup_scaled_tail_eq (hh : 0 < h) (hθ : 0 ≤ θ) (hF : ∀ t, 0 ≤ F t)
    (hstep : ∀ t, F t = F (h * ⌈t / h⌉))
    (hlat : Tendsto (fun k : ℕ => exp (θ * (k * h)) * F (k * h)) atTop (𝓝 C)) :
    limsup (fun t => exp (θ * t) * F t) atTop = C := by
  have hup := tendsto_lattice_ceil hh hlat
  have hev : ∀ᶠ t in atTop, exp (θ * t) * F t ≤
      exp (θ * (⌈t / h⌉₊ * h)) * F (⌈t / h⌉₊ * h) :=
    (eventually_gt_atTop 0).mono fun t ht => (scaled_mem_Icc hh hθ hF hstep ht).2
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun t => exp (θ * t) * F t) :=
    hup.isBoundedUnder_le.mono_le hev
  have hbot : IsBoundedUnder (· ≥ ·) atTop (fun t => exp (θ * t) * F t) :=
    isBoundedUnder_of ⟨0, fun t => mul_nonneg (exp_pos _).le (hF t)⟩
  refine le_antisymm ?_ ?_
  · calc limsup (fun t => exp (θ * t) * F t) atTop
        ≤ limsup (fun t : ℝ => exp (θ * (⌈t / h⌉₊ * h)) * F (⌈t / h⌉₊ * h)) atTop :=
          limsup_le_limsup hev hbot.isCoboundedUnder_le hup.isBoundedUnder_le
      _ = C := hup.limsup_eq
  · exact le_limsup_of_tendsto_comp (tendsto_mul_h hh) hlat hbdd

/-- **Lattice liminf.** Under the hypotheses of `limsup_scaled_tail_eq`,
`liminf_{t → ∞} e^{θ t} F t = e^{-θ h} C`: just below each lattice point the
scaled tail drops by the factor `e^{-θ h}`. -/
theorem liminf_scaled_tail_eq (hh : 0 < h) (hθ : 0 ≤ θ) (hF : ∀ t, 0 ≤ F t)
    (hstep : ∀ t, F t = F (h * ⌈t / h⌉))
    (hlat : Tendsto (fun k : ℕ => exp (θ * (k * h)) * F (k * h)) atTop (𝓝 C)) :
    liminf (fun t => exp (θ * t) * F t) atTop = exp (-(θ * h)) * C := by
  have hup := tendsto_lattice_ceil hh hlat
  have hlow := hup.const_mul (exp (-(θ * h)))
  have hev : ∀ᶠ t in atTop, exp (-(θ * h)) * (exp (θ * (⌈t / h⌉₊ * h)) * F (⌈t / h⌉₊ * h)) ≤
      exp (θ * t) * F t :=
    (eventually_gt_atTop 0).mono fun t ht => (scaled_mem_Icc hh hθ hF hstep ht).1
  have hev' : ∀ᶠ t in atTop, exp (θ * t) * F t ≤
      exp (θ * (⌈t / h⌉₊ * h)) * F (⌈t / h⌉₊ * h) :=
    (eventually_gt_atTop 0).mono fun t ht => (scaled_mem_Icc hh hθ hF hstep ht).2
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun t => exp (θ * t) * F t) :=
    hup.isBoundedUnder_le.mono_le hev'
  have hbot : IsBoundedUnder (· ≥ ·) atTop (fun t => exp (θ * t) * F t) :=
    isBoundedUnder_of ⟨0, fun t => mul_nonneg (exp_pos _).le (hF t)⟩
  refine le_antisymm ?_ ?_
  · -- Approach the lattice points from below with offsets `s_k = h - h / (k + 1) ↑ h`.
    set s : ℕ → ℝ := fun k => h - h * (1 / ((k : ℝ) + 1)) with hs_def
    have hs0 : ∀ k, 0 ≤ s k := fun k => by
      have : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      simp only [hs_def]
      nlinarith
    have hsh : ∀ k, s k < h := fun k => by
      have : 0 < h * (1 / ((k : ℝ) + 1)) := by positivity
      simp only [hs_def]
      linarith
    have hslim : Tendsto s atTop (𝓝 h) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul h
      simpa [hs_def] using (tendsto_const_nhds (x := h)).sub this
    have hφ : Tendsto (fun k : ℕ => (k : ℝ) * h - s k) atTop atTop := by
      refine tendsto_atTop_mono (fun k => ?_) ((tendsto_mul_h hh).atTop_add
        (tendsto_const_nhds (x := -h)))
      linarith [hsh k]
    have hcomp : Tendsto (fun k : ℕ => exp (θ * ((k : ℝ) * h - s k)) * F ((k : ℝ) * h - s k))
        atTop (𝓝 (exp (-(θ * h)) * C)) := by
      have hlim : Tendsto (fun k => exp (-(θ * s k)) * (exp (θ * (k * h)) * F (k * h))) atTop
          (𝓝 (exp (-(θ * h)) * C)) :=
        ((continuous_exp.comp (continuous_const.mul continuous_id).neg).tendsto h |>.comp
          hslim).mul hlat
      refine hlim.congr fun k => ?_
      have e : h * ((k : ℤ) : ℝ) = k * h := by push_cast; ring
      rw [scaled_eq_lattice hstep ((k : ℝ) * h - s k), ceil_sub_offset hh k (hs0 k) (hsh k), e]
      congr 2
      ring
    exact liminf_le_of_tendsto_comp hφ hcomp hbot
  · calc exp (-(θ * h)) * C
        = liminf (fun t : ℝ =>
            exp (-(θ * h)) * (exp (θ * (⌈t / h⌉₊ * h)) * F (⌈t / h⌉₊ * h))) atTop :=
          hlow.liminf_eq.symm
      _ ≤ liminf (fun t => exp (θ * t) * F t) atTop :=
          liminf_le_liminf hev hlow.isBoundedUnder_ge hbdd.isCoboundedUnder_ge

/-- **Lattice dichotomy.** If the tail is a lattice step function with
`e^{θ k h} F (k h) → C`, `θ > 0` and `C ≠ 0`, then `e^{θ t} F t` has no limit as
`t → ∞` through the reals: the nonlattice conclusion `F t ~ L e^{-θ t}` fails for
every `L`. The obstruction is the offset `s = h / 2`, where the scaled tail
tends to `e^{-θ h / 2} C ≠ C`. -/
theorem not_tendsto_scaled_tail (hh : 0 < h) (hθ : 0 < θ) (hC : C ≠ 0)
    (hstep : ∀ t, F t = F (h * ⌈t / h⌉))
    (hlat : Tendsto (fun k : ℕ => exp (θ * (k * h)) * F (k * h)) atTop (𝓝 C)) (L : ℝ) :
    ¬ Tendsto (fun t => exp (θ * t) * F t) atTop (𝓝 L) := by
  intro hL
  have h1 : Tendsto (fun k : ℕ => exp (θ * (k * h)) * F (k * h)) atTop (𝓝 L) :=
    hL.comp (tendsto_mul_h hh)
  have hCL : C = L := tendsto_nhds_unique hlat h1
  have hφ : Tendsto (fun k : ℕ => (k : ℝ) * h - h / 2) atTop atTop :=
    (tendsto_mul_h hh).atTop_add (tendsto_const_nhds (x := -(h / 2))) |>.congr fun k => by ring
  have h2 : Tendsto (fun k : ℕ => exp (θ * (k * h - h / 2)) * F (k * h - h / 2)) atTop (𝓝 L) :=
    hL.comp hφ
  have h3 := tendsto_scaled_tail_offset hh hstep hlat (s := h / 2) (by positivity) (by linarith)
  have hEq : exp (-(θ * (h / 2))) * C = C := by
    rw [tendsto_nhds_unique h3 h2, hCL]
  have hlt : exp (-(θ * (h / 2))) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
  have : exp (-(θ * (h / 2))) = 1 := by
    have := mul_right_cancel₀ hC (hEq.trans (one_mul C).symm)
    exact this
  exact hlt.ne this

end Lattice

/-! ### Nonlattice constant identification by exponential tilting -/

section Tilting

variable {G : Measure ℝ} {θ : ℝ}

/-- A Cramér root `∫ e^{θ y} dG = 1` makes the tilted measure `G.tilted (θ * ·)`
a probability measure. -/
theorem isProbabilityMeasure_tilted_of_integral_eq_one (hθ : ∫ y, exp (θ * y) ∂G = 1) :
    IsProbabilityMeasure (G.tilted (fun y => θ * y)) := by
  have hint : Integrable (fun y => exp (θ * y)) G :=
    Integrable.of_integral_ne_zero (by rw [hθ]; exact one_ne_zero)
  have hG : NeZero G := ⟨fun h0 => by simp [h0] at hθ⟩
  exact isProbabilityMeasure_tilted hint

/-- Under a Cramér root, integrating against the tilted measure is integrating
against `e^{θ y} G(dy)`. -/
private lemma integral_tilted_of_root (hθ : ∫ y, exp (θ * y) ∂G = 1) (g : ℝ → ℝ) :
    ∫ y, g y ∂(G.tilted (fun y => θ * y)) = ∫ y, exp (θ * y) * g y ∂G := by
  rw [integral_tilted, hθ]
  simp only [div_one, smul_eq_mul]

/-- **Mean of the tilted ladder law.** Under a Cramér root, the tilted measure
has mean `∫ y e^{θ y} dG(y)`. -/
theorem integral_id_tilt (hθ : ∫ y, exp (θ * y) ∂G = 1) :
    ∫ y, y ∂(G.tilted (fun y => θ * y)) = ∫ y, y * exp (θ * y) ∂G := by
  rw [integral_tilted_of_root hθ]
  simp only [mul_comm]

/-- **Exponential tilting of a renewal equation.** If
`Z t = z t + ∫ Z (t - y) dG(y)` for every `t` and `∫ e^{θ y} dG = 1`, then
`e^{θ t} Z t` solves the proper renewal equation driven by the tilted
probability measure `G.tilted (θ * ·)` with input `e^{θ t} z t`. -/
theorem tilted_renewal_eq (hθ : ∫ y, exp (θ * y) ∂G = 1) {Z z : ℝ → ℝ}
    (hren : ∀ t, Z t = z t + ∫ y, Z (t - y) ∂G) (t : ℝ) :
    exp (θ * t) * Z t = exp (θ * t) * z t +
      ∫ y, exp (θ * (t - y)) * Z (t - y) ∂(G.tilted (fun y => θ * y)) := by
  rw [integral_tilted_of_root hθ]
  have : ∀ y, exp (θ * y) * (exp (θ * (t - y)) * Z (t - y)) = exp (θ * t) * Z (t - y) := by
    intro y
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [this]
  rw [integral_const_mul, hren t, mul_add]

/-- **Nonlattice constant identification.** Let `Z t = z t + ∫ Z (t - y) dG(y)`
with Cramér root `∫ e^{θ y} dG = 1`. Assume the key renewal theorem for the
tilted law `G^θ = G.tilted (θ * ·)` (hypothesis `hKRT`): every admissible
solution `Y` of `Y t = y t + ∫ Y (t - x) dG^θ(x)` tends to
`(∫_{(0,∞)} y) / mean(G^θ)`. If the tilted pair `(e^{θ t} Z t, e^{θ t} z t)` is
admissible, then
`e^{θ t} Z t → (∫_{(0,∞)} e^{θ s} z s ds) / ∫ y e^{θ y} dG(y)`,
i.e. `Z t ~ C e^{-θ t}` with this explicit `C`. -/
theorem tendsto_scaled_of_keyRenewal (hθ : ∫ y, exp (θ * y) ∂G = 1) {Z z : ℝ → ℝ}
    (hren : ∀ t, Z t = z t + ∫ y, Z (t - y) ∂G)
    (Adm : (ℝ → ℝ) → (ℝ → ℝ) → Prop)
    (hKRT : ∀ Y y : ℝ → ℝ, Adm Y y →
      (∀ t, Y t = y t + ∫ x, Y (t - x) ∂(G.tilted (fun x => θ * x))) →
      Tendsto Y atTop (𝓝 ((∫ s in Ioi 0, y s) / ∫ x, x ∂(G.tilted (fun x => θ * x)))))
    (hAdm : Adm (fun t => exp (θ * t) * Z t) (fun t => exp (θ * t) * z t)) :
    Tendsto (fun t => exp (θ * t) * Z t) atTop
      (𝓝 ((∫ s in Ioi 0, exp (θ * s) * z s) / ∫ y, y * exp (θ * y) ∂G)) := by
  rw [← integral_id_tilt hθ]
  exact hKRT _ _ hAdm (tilted_renewal_eq hθ hren)

/-- `∫_0^y e^{θ t} dt = (e^{θ y} - 1) / θ` for `θ ≠ 0`. -/
private lemma intervalIntegral_exp_mul (hθ : θ ≠ 0) (y : ℝ) :
    ∫ t in (0 : ℝ)..y, exp (θ * t) = (exp (θ * y) - 1) / θ := by
  rw [intervalIntegral.integral_comp_mul_left (fun t => exp t) hθ, integral_exp, mul_zero,
    exp_zero, smul_eq_mul, inv_mul_eq_div]

/-- **Layer-cake form of the Cramér–Lundberg numerator.** For a finite measure `G`
on `[0, ∞)` with `e^{θ y}` integrable and `θ > 0`,
`∫_{(0,∞)} e^{θ s} G(s, ∞) ds = (∫ e^{θ y} dG(y) - G(ℝ)) / θ`. -/
theorem integral_exp_mul_measureReal_Ioi [IsFiniteMeasure G] (hθ : 0 < θ)
    (hG : ∀ᵐ y ∂G, 0 ≤ y) (hint : Integrable (fun y => exp (θ * y)) G) :
    ∫ s in Ioi 0, exp (θ * s) * G.real (Ioi s) = (∫ y, exp (θ * y) ∂G - G.real univ) / θ := by
  have hnn : ∀ s, 0 ≤ exp (θ * s) * G.real (Ioi s) := fun s =>
    mul_nonneg (exp_pos _).le measureReal_nonneg
  have hcake := lintegral_comp_eq_lintegral_meas_lt_mul G (f := id) hG aemeasurable_id
    (g := fun t => exp (θ * t)) (fun _ _ => (by fun_prop : Continuous fun t => exp (θ * t))
      |>.intervalIntegrable _ _) (ae_of_all _ fun t => (exp_pos _).le)
  have hfun_nn : ∀ᵐ y ∂G, 0 ≤ (exp (θ * y) - 1) / θ := hG.mono fun y hy => by
    have : 1 ≤ exp (θ * y) := one_le_exp (by positivity)
    exact div_nonneg (by linarith) hθ.le
  have hint' : Integrable (fun y => (exp (θ * y) - 1) / θ) G :=
    (hint.sub (integrable_const 1)).div_const θ
  calc ∫ s in Ioi 0, exp (θ * s) * G.real (Ioi s)
      = (∫⁻ s in Ioi 0, G {a | s < id a} * ENNReal.ofReal (exp (θ * s))).toReal := by
        have hanti : Antitone (fun s => G.real (Ioi s)) := fun a b hab =>
          measureReal_mono (Ioi_subset_Ioi hab)
        rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn)
          ((by fun_prop : Measurable fun s => exp (θ * s)).mul
            hanti.measurable).aestronglyMeasurable]
        congr 1
        refine lintegral_congr fun s => ?_
        rw [ENNReal.ofReal_mul (exp_pos _).le, mul_comm, ofReal_measureReal]
        rfl
    _ = (∫⁻ y, ENNReal.ofReal ((exp (θ * y) - 1) / θ) ∂G).toReal := by
        rw [← hcake]
        simp only [id, intervalIntegral_exp_mul hθ.ne']
    _ = ∫ y, (exp (θ * y) - 1) / θ ∂G :=
        (integral_eq_lintegral_of_nonneg_ae hfun_nn hint'.aestronglyMeasurable).symm
    _ = (∫ y, exp (θ * y) ∂G - G.real univ) / θ := by
        rw [integral_div, integral_sub hint (integrable_const 1), integral_const, smul_eq_mul,
          mul_one]

/-- **Cramér–Lundberg constant.** Let `G` be a finite (typically defective)
ladder-height measure on `[0, ∞)` with Cramér root `θ > 0`,
`∫ e^{θ y} dG = 1`, and let `Z` solve
`Z t = 1_{t ≥ 0} G(t, ∞) + ∫ Z (t - y) dG(y)` for all real `t` (Feller's
convention: for the maximum `M` of the ladder process, `Z t = P(M > t)` for
`t ≥ 0` and `Z t = 0` for `t < 0`). Given the key renewal theorem for the tilted
law (hypothesis `hKRT`, as in `tendsto_scaled_of_keyRenewal`),
`e^{θ t} Z t → (1 - G(ℝ)) / (θ ∫ y e^{θ y} dG(y))`. -/
theorem tendsto_scaled_cramerLundberg [IsFiniteMeasure G] (hθpos : 0 < θ)
    (hθ : ∫ y, exp (θ * y) ∂G = 1) (hG : ∀ᵐ y ∂G, 0 ≤ y) {Z : ℝ → ℝ}
    (hren : ∀ t, Z t = (Ici 0).indicator (fun s => G.real (Ioi s)) t + ∫ y, Z (t - y) ∂G)
    (Adm : (ℝ → ℝ) → (ℝ → ℝ) → Prop)
    (hKRT : ∀ Y y : ℝ → ℝ, Adm Y y →
      (∀ t, Y t = y t + ∫ x, Y (t - x) ∂(G.tilted (fun x => θ * x))) →
      Tendsto Y atTop (𝓝 ((∫ s in Ioi 0, y s) / ∫ x, x ∂(G.tilted (fun x => θ * x)))))
    (hAdm : Adm (fun t => exp (θ * t) * Z t)
      (fun t => exp (θ * t) * (Ici 0).indicator (fun s => G.real (Ioi s)) t)) :
    Tendsto (fun t => exp (θ * t) * Z t) atTop
      (𝓝 ((1 - G.real univ) / (θ * ∫ y, y * exp (θ * y) ∂G))) := by
  have hint : Integrable (fun y => exp (θ * y)) G :=
    Integrable.of_integral_ne_zero (by rw [hθ]; exact one_ne_zero)
  have h := tendsto_scaled_of_keyRenewal hθ hren Adm hKRT hAdm
  have hset : ∫ s in Ioi 0, exp (θ * s) * (Ici 0).indicator (fun s => G.real (Ioi s)) s =
      ∫ s in Ioi 0, exp (θ * s) * G.real (Ioi s) :=
    setIntegral_congr_fun measurableSet_Ioi fun s hs => by
      rw [indicator_of_mem (mem_Ici.2 (le_of_lt hs))]
  rwa [hset, integral_exp_mul_measureReal_Ioi hθpos hG hint, hθ, div_div] at h

end Tilting

end MathlibExt.Probability.Renewal.LatticeConstants
