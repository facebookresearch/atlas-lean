/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ColoredPartitionsJensen.Reduction
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The smooth class `S_β`

`InS β d Λ` says: on some half-line `(x₀, ∞)` with `x₀ > 0`, `Λ` is `C^d` and
`|Λ^{(k)}(x)| ≤ C x^{β−k}` for every `k ≤ d`. Everything is eventual (smoothness too), because
`1/g` and `log (1 + h)` are only smooth where `g ≠ 0`, `1 + h > 0`.

* gluing: `exists_contDiff_eqOn` (a function `C^n` on `(x₀, ∞)` agrees on `[x₁, ∞)`, `x₁ > x₀`,
  with a
  globally `C^n` one, by a smooth cutoff), and from it the half-line forms of the reduction:
  `exists_fwdDiff_iter_eq_iteratedDeriv_of_contDiffOn`, `hasLogRatioExpansion_of_smooth_model'`,
  `eventually_card_roots_of_smooth_model'`, `eventually_card_roots_of_InS`;
* closure: `InS.congr` (equality on a half-line), `InS.mono` (`β ≤ β'`), `InS.of_le` (`d' ≤ d`),
  `InS.add`, `InS.const_mul`, `InS.sub`, `InS.mul` (`S_β · S_γ ⊆ S_{β+γ}`, Leibniz),
  `InS.deriv_mem`,
  `InS.of_deriv`, `InS.comp_add` (`x ↦ x + a`), `InS.inv` (`1/g`, `g ∈ S_0`, `g ≥ c > 0`),
  `InS.log_one_add` (`log (1 + h) ∈ S_{−η}` for `h ∈ S_{−η}`, `η > 0`);
* members: `inS_rpow` (`x^γ ∈ S_β`, `γ ≤ β`), `inS_sqrt`, `inS_log` (`log ∈ S_ε`, `ε > 0`);
-/

open Filter Topology Asymptotics Set
open scoped fwdDiff Nat

namespace MetaMathlibExt.ColoredPartitionsJensen

@[expose] public section

/-! ### Gluing a half-line `C^n` function to a global one -/

/-- A function `C^n` on `(x₀, ∞)` agrees on `[x₁, ∞)` (`x₀ < x₁`) with a function `C^n` on `ℝ`. -/
theorem exists_contDiff_eqOn {f : ℝ → ℝ} {x₀ x₁ : ℝ} {n : ℕ} (hf : ContDiffOn ℝ n f (Ioi x₀))
    (h01 : x₀ < x₁) : ∃ g : ℝ → ℝ, ContDiff ℝ n g ∧ EqOn g f (Ici x₁) := by
  set m := (x₀ + x₁) / 2 with hm
  have hm0 : x₀ < m := by rw [hm]; linarith
  have hm1 : m < x₁ := by rw [hm]; linarith
  set cut : ℝ → ℝ := fun x => Real.smoothTransition ((x - m) / (x₁ - m)) with hcut
  have hst : ContDiff ℝ n Real.smoothTransition := by
    exact_mod_cast (Real.smoothTransition.contDiff (n := (n : ℕ∞)))
  have hcuts : ContDiff ℝ n cut :=
    hst.comp ((contDiff_id.sub contDiff_const).div_const _)
  refine ⟨fun x => cut x * f x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_or_ge x₀ x with hx | hx
    · exact hcuts.contDiffAt.mul (hf.contDiffAt (Ioi_mem_nhds hx))
    · have hloc : (fun y => cut y * f y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds (show x < m by linarith)] with y hy
        have hy' : (y - m) / (x₁ - m) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith [hy.out]) (by linarith)
        simp only [hcut, Real.smoothTransition.zero_of_nonpos hy', zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hloc
  · intro x hx
    have hx' : 1 ≤ (x - m) / (x₁ - m) := by
      rw [le_div_iff₀ (by linarith)]; linarith [hx.out]
    simp only [hcut, Real.smoothTransition.one_of_one_le hx', one_mul]

/-- Iterated derivatives of two functions equal on `[x₁, ∞)` agree on `(x₁, ∞)`. -/
theorem iteratedDeriv_eq_of_eqOn_Ici {f g : ℝ → ℝ} {x₁ : ℝ} (h : EqOn g f (Ici x₁)) (k : ℕ)
    {x : ℝ} (hx : x₁ < x) : iteratedDeriv k g x = iteratedDeriv k f x :=
  (h.mono Ioi_subset_Ici_self).iteratedDeriv_of_isOpen isOpen_Ioi k hx

/-- Mean value form of the `k`-th difference for `f` of class `C^k` on a half-line `(x₀, ∞)`:
`Δ^k f(x) = f^{(k)}(ξ)` with `ξ ∈ [x, x + k]`, for every `x > x₀`. -/
theorem exists_fwdDiff_iter_eq_iteratedDeriv_of_contDiffOn {k : ℕ} {f : ℝ → ℝ} {x₀ : ℝ}
    (hf : ContDiffOn ℝ k f (Ioi x₀)) {x : ℝ} (hx : x₀ < x) :
    ∃ ξ ∈ Icc x (x + k), (fwdDiff (1 : ℝ))^[k] f x = iteratedDeriv k f ξ := by
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_eqOn hf (show x₀ < (x₀ + x) / 2 by linarith)
  obtain ⟨ξ, hξ, heq⟩ := exists_fwdDiff_iter_eq_iteratedDeriv k hg x
  refine ⟨ξ, hξ, ?_⟩
  have hdiff : (fwdDiff (1 : ℝ))^[k] f x = (fwdDiff (1 : ℝ))^[k] g x := by
    simp only [fwdDiff_iter_eq_sum_shift]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hgf (show x + i • (1 : ℝ) ∈ Ici ((x₀ + x) / 2) by
      simp only [nsmul_eq_mul, mul_one, Set.mem_Ici]; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])]
  rw [hdiff, heq, iteratedDeriv_eq_of_eqOn_Ici hgf k (by linarith [hξ.1])]

/-- **Half-line model.** As `hasLogRatioExpansion_of_smooth_model`, but `Λ` only needs to be
`C^d` on some `(x₀, ∞)`. -/
theorem hasLogRatioExpansion_of_smooth_model' {α : ℕ → ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hα : ∀ᶠ n in atTop, 0 < α n) {Λ : ℝ → ℝ} {x₀ : ℝ} (hΛ : ContDiffOn ℝ d Λ (Ioi x₀))
    {β c C : ℝ} (hβ0 : 0 < β) (hβ2 : β < 2) (hc : 0 < c)
    (hupper : ∀ k ∈ Finset.Icc 2 d, ∀ᶠ x in atTop, |iteratedDeriv k Λ x| ≤ C * x ^ (β - k))
    (hlower : ∀ᶠ x in atTop, iteratedDeriv 2 Λ x ≤ -c * x ^ (β - 2))
    (hε : (fun n : ℕ => Real.log (α n) - Λ n) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((β - 2) * d / 2))) :
    HasLogRatioExpansion α d := by
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_eqOn hΛ (lt_add_one x₀)
  have hev : ∀ k, ∀ᶠ x in atTop, iteratedDeriv k g x = iteratedDeriv k Λ x := fun k =>
    (eventually_gt_atTop (x₀ + 1)).mono fun x hx => iteratedDeriv_eq_of_eqOn_Ici hgf k hx
  refine hasLogRatioExpansion_of_smooth_model (C := C) hd hα hg hβ0 hβ2 hc (fun k hk => ?_) ?_ ?_
  · filter_upwards [hupper k hk, hev k] with x h1 h2
    rw [h2]; exact h1
  · filter_upwards [hlower, hev 2] with x h1 h2
    rw [h2]; exact h1
  · refine hε.congr' ?_ EventuallyEq.rfl
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (x₀ + 1)] with n hn
    rw [hgf (show (n : ℝ) ∈ Ici (x₀ + 1) from hn)]

/-- The half-line model gives eventual real-rootedness, any degree `d ≥ 1`. -/
theorem eventually_card_roots_of_smooth_model' {α : ℕ → ℝ} {d : ℕ} (hd : 1 ≤ d)
    (hα : ∀ᶠ n in atTop, 0 < α n)
    (hlow : ∃ c, ∀ᶠ n in atTop, -c ≤ Real.log (α (n + 1) / α n))
    {Λ : ℝ → ℝ} {x₀ : ℝ} (hΛ : ContDiffOn ℝ d Λ (Ioi x₀))
    {β c K : ℝ} (hβ0 : 0 < β) (hβ2 : β < 2) (hc : 0 < c)
    (hupper : ∀ k ∈ Finset.Icc 2 d, ∀ᶠ x in atTop, |iteratedDeriv k Λ x| ≤ K * x ^ (β - k))
    (hlower : ∀ᶠ x in atTop, iteratedDeriv 2 Λ x ≤ -c * x ^ (β - 2))
    (hε : (fun n : ℕ => Real.log (α n) - Λ n) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((β - 2) * d / 2))) :
    ∀ᶠ n in atTop,
      (∑ j ∈ Finset.range (d + 1), Polynomial.C ((d.choose j : ℝ) * α (n + j)) *
          Polynomial.X ^ j).roots.card =
        (∑ j ∈ Finset.range (d + 1), Polynomial.C ((d.choose j : ℝ) * α (n + j)) *
          Polynomial.X ^ j).natDegree := by
  rcases le_or_gt d 1 with h | h
  · exact (hasLogRatioExpansion_of_le_one α h).eventually_card_roots hd hα hlow
  · exact (hasLogRatioExpansion_of_smooth_model' (by omega) hα hΛ hβ0 hβ2 hc hupper hlower
      hε).eventually_card_roots hd hα hlow

/-! ### The class `S_β` -/

/-- `Λ ∈ S_β` to order `d`: on some half-line `(x₀, ∞)`, `x₀ > 0`, `Λ` is `C^d` and
`|Λ^{(k)}(x)| ≤ C x^{β−k}` for all `k ≤ d`. -/
def InS (β : ℝ) (d : ℕ) (Λ : ℝ → ℝ) : Prop :=
  ∃ x₀ C : ℝ, 0 < x₀ ∧ ContDiffOn ℝ d Λ (Ioi x₀) ∧
    ∀ k ≤ d, ∀ x, x₀ < x → |iteratedDeriv k Λ x| ≤ C * x ^ (β - k)

/-- The threshold can be pushed past any `x₁`, and the constant made nonnegative. -/
theorem InS.exists_ge {β : ℝ} {d : ℕ} {Λ : ℝ → ℝ} (h : InS β d Λ) (x₁ : ℝ) :
    ∃ x₀ C : ℝ, x₁ ≤ x₀ ∧ 0 < x₀ ∧ 0 ≤ C ∧ ContDiffOn ℝ d Λ (Ioi x₀) ∧
      ∀ k ≤ d, ∀ x, x₀ < x → |iteratedDeriv k Λ x| ≤ C * x ^ (β - k) := by
  obtain ⟨a, C, ha, hs, hb⟩ := h
  refine ⟨max a x₁, max C 0, le_max_right _ _, lt_of_lt_of_le ha (le_max_left _ _),
    le_max_right _ _, hs.mono (Ioi_subset_Ioi (le_max_left _ _)), fun k hk x hx => ?_⟩
  have hax : a < x := lt_of_le_of_lt (le_max_left _ _) hx
  exact (hb k hk x hax).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg (by linarith) _))

/-- Build `InS` from data on `(x₀, ∞)`. -/
theorem InS.intro {β : ℝ} {d : ℕ} {Λ : ℝ → ℝ} {x₀ C : ℝ} (h0 : 0 < x₀)
    (hs : ContDiffOn ℝ d Λ (Ioi x₀))
    (hb : ∀ k ≤ d, ∀ x, x₀ < x → |iteratedDeriv k Λ x| ≤ C * x ^ (β - k)) : InS β d Λ :=
  ⟨x₀, C, h0, hs, hb⟩

theorem InS.congr {β : ℝ} {d : ℕ} {f g : ℝ → ℝ} (h : InS β d f) {a : ℝ} (hfg : EqOn f g (Ioi a)) :
    InS β d g := by
  obtain ⟨x₀, C, hx₁, h0, -, hs, hb⟩ := h.exists_ge a
  refine InS.intro (C := C) h0 (hs.congr fun x hx => (hfg (lt_of_le_of_lt hx₁ hx)).symm)
    fun k hk x hx => ?_
  have hsub : EqOn f g (Ioi x₀) := hfg.mono (Ioi_subset_Ioi hx₁)
  rw [← hsub.iteratedDeriv_of_isOpen isOpen_Ioi k hx]
  exact hb k hk x hx

theorem InS.of_eq {β β' : ℝ} {d : ℕ} {f : ℝ → ℝ} (h : InS β d f) (hb : β = β') : InS β' d f :=
  hb ▸ h

theorem InS.of_le {β : ℝ} {d d' : ℕ} {f : ℝ → ℝ} (h : InS β d f) (hd : d' ≤ d) : InS β d' f := by
  obtain ⟨x₀, C, h0, hs, hb⟩ := h
  exact InS.intro h0 (hs.of_le (by exact_mod_cast hd)) fun k hk => hb k (hk.trans hd)

theorem InS.mono {β β' : ℝ} {d : ℕ} {f : ℝ → ℝ} (h : InS β d f) (hb : β ≤ β') : InS β' d f := by
  obtain ⟨x₀, C, hx₁, h0, hC, hs, hbd⟩ := h.exists_ge 1
  refine InS.intro (C := C) h0 hs fun k hk x hx => (hbd k hk x hx).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) hC

/-- Two members can be put on one half-line with nonnegative constants. -/
theorem InS.exists_common {β γ : ℝ} {d : ℕ} {f g : ℝ → ℝ} (hf : InS β d f) (hg : InS γ d g)
    (x₁ : ℝ) :
    ∃ x₀ C₁ C₂ : ℝ, x₁ ≤ x₀ ∧ 0 < x₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ContDiffOn ℝ d f (Ioi x₀) ∧ ContDiffOn ℝ d g (Ioi x₀) ∧
      (∀ k ≤ d, ∀ x, x₀ < x → |iteratedDeriv k f x| ≤ C₁ * x ^ (β - k)) ∧
      (∀ k ≤ d, ∀ x, x₀ < x → |iteratedDeriv k g x| ≤ C₂ * x ^ (γ - k)) := by
  obtain ⟨a, C₁, ha1, ha0, hC₁, hfs, hfb⟩ := hf.exists_ge x₁
  obtain ⟨b, C₂, hab, hb0, hC₂, hgs, hgb⟩ := hg.exists_ge a
  exact ⟨b, C₁, C₂, ha1.trans hab, hb0, hC₁, hC₂, hfs.mono (Ioi_subset_Ioi hab), hgs,
    fun k hk x hx => hfb k hk x (lt_of_le_of_lt hab hx), hgb⟩

theorem InS.add {β : ℝ} {d : ℕ} {f g : ℝ → ℝ} (hf : InS β d f) (hg : InS β d g) :
    InS β d (fun x => f x + g x) := by
  obtain ⟨x₀, C₁, C₂, -, h0, -, -, hfs, hgs, hfb, hgb⟩ := hf.exists_common hg 0
  refine InS.intro (C := C₁ + C₂) h0 (hfs.add hgs) fun k hk x hx => ?_
  have hk' : (k : WithTop ℕ∞) ≤ d := by exact_mod_cast hk
  rw [iteratedDeriv_fun_add ((hfs.contDiffAt (Ioi_mem_nhds hx)).of_le hk')
    ((hgs.contDiffAt (Ioi_mem_nhds hx)).of_le hk')]
  have := hfb k hk x hx
  have := hgb k hk x hx
  calc _ ≤ |iteratedDeriv k f x| + |iteratedDeriv k g x| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem InS.const_mul {β : ℝ} {d : ℕ} {f : ℝ → ℝ} (hf : InS β d f) (a : ℝ) :
    InS β d (fun x => a * f x) := by
  obtain ⟨x₀, C, -, h0, -, hs, hb⟩ := hf.exists_ge 0
  refine InS.intro (C := |a| * C) h0 (contDiffOn_const.mul hs) fun k hk x hx => ?_
  have hk' : (k : WithTop ℕ∞) ≤ d := by exact_mod_cast hk
  rw [iteratedDeriv_const_mul a ((hs.contDiffAt (Ioi_mem_nhds hx)).of_le hk'), abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb k hk x hx) (abs_nonneg a)

theorem InS.sub {β : ℝ} {d : ℕ} {f g : ℝ → ℝ} (hf : InS β d f) (hg : InS β d g) :
    InS β d (fun x => f x - g x) :=
  (hf.add (hg.const_mul (-1))).congr (a := 0) fun x _ => by simp only; ring

/-- Leibniz: `S_β · S_γ ⊆ S_{β+γ}`. -/
theorem InS.mul {β γ : ℝ} {d : ℕ} {f g : ℝ → ℝ} (hf : InS β d f) (hg : InS γ d g) :
    InS (β + γ) d (fun x => f x * g x) := by
  obtain ⟨x₀, C₁, C₂, -, h0, hC₁, hC₂, hfs, hgs, hfb, hgb⟩ := hf.exists_common hg 0
  refine InS.intro (C := 2 ^ d * (C₁ * C₂)) h0 (hfs.mul hgs) fun k hk x hx => ?_
  have hxpos : 0 < x := h0.trans hx
  have hW : ∀ (h : ℝ → ℝ) (j : ℕ),
      ‖iteratedFDerivWithin ℝ j h (Ioi x₀) x‖ = |iteratedDeriv j h x| := fun h j => by
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedDerivWithin_of_isOpen isOpen_Ioi hx, Real.norm_eq_abs]
  have hL := norm_iteratedFDerivWithin_mul_le hfs hgs (uniqueDiffOn_Ioi x₀) hx
    (n := k) (by exact_mod_cast hk)
  rw [hW] at hL
  simp only [hW] at hL
  refine hL.trans ?_
  have hterm : ∀ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |iteratedDeriv i f x| *
      |iteratedDeriv (k - i) g x| ≤ (k.choose i : ℝ) * (C₁ * C₂ * x ^ (β + γ - k)) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h1 := hfb i (hik.trans hk) x hx
    have h2 := hgb (k - i) ((Nat.sub_le k i).trans hk) x hx
    have hpow : x ^ (β - i) * x ^ (γ - ((k - i : ℕ) : ℝ)) = x ^ (β + γ - k) := by
      rw [← Real.rpow_add hxpos, Nat.cast_sub hik]; ring_nf
    have hch : (0 : ℝ) ≤ k.choose i := Nat.cast_nonneg _
    calc (k.choose i : ℝ) * |iteratedDeriv i f x| * |iteratedDeriv (k - i) g x|
        ≤ (k.choose i : ℝ) * (C₁ * x ^ (β - i)) * (C₂ * x ^ (γ - ((k - i : ℕ) : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hch) h2 (abs_nonneg _)
            (mul_nonneg hch (mul_nonneg hC₁ (Real.rpow_nonneg hxpos.le _)))
      _ = (k.choose i : ℝ) * (C₁ * C₂ * x ^ (β + γ - k)) := by rw [← hpow]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  rw [hsum, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) hk) (mul_nonneg hC₁ hC₂)) (Real.rpow_nonneg hxpos.le _)

/-- Derivative: `S_β` to order `d + 1` maps into `S_{β−1}` to order `d`. -/
theorem InS.deriv_mem {β : ℝ} {d : ℕ} {f : ℝ → ℝ} (hf : InS β (d + 1) f) :
    InS (β - 1) d (deriv f) := by
  obtain ⟨x₀, C, h0, hs, hb⟩ := hf
  have hs' : ContDiffOn ℝ ((d : WithTop ℕ∞) + 1) f (Ioi x₀) := by exact_mod_cast hs
  refine InS.intro (C := C) h0 ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).1 hs').2.2
    fun k hk x hx => ?_
  rw [← iteratedDeriv_succ']
  refine (hb (k + 1) (by omega) x hx).trans_eq ?_
  congr 2; push_cast; ring

/-- Antiderivative direction: a bound on `f` itself plus `f' ∈ S_{β−1}` (order `d`) gives
`f ∈ S_β` to order `d + 1`. -/
theorem InS.of_deriv {β : ℝ} {d : ℕ} {f : ℝ → ℝ} {a C₀ : ℝ}
    (hdf : DifferentiableOn ℝ f (Ioi a)) (h0 : ∀ x, a < x → |f x| ≤ C₀ * x ^ β)
    (hf' : InS (β - 1) d (deriv f)) : InS β (d + 1) f := by
  obtain ⟨x₀, C, hx₁, hx0, -, hs, hb⟩ := hf'.exists_ge a
  have hs' : ContDiffOn ℝ ((d : WithTop ℕ∞) + 1) f (Ioi x₀) :=
    (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).2
      ⟨hdf.mono (Ioi_subset_Ioi hx₁), fun h => absurd h (by simp), hs⟩
  refine InS.intro (C := max C₀ C) hx0 (by exact_mod_cast hs') fun k hk x hx => ?_
  have hxpos : 0 < x := hx0.trans hx
  rcases k with _ | k
  · simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero]
    exact (h0 x (lt_of_le_of_lt hx₁ hx)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hxpos.le _))
  · rw [iteratedDeriv_succ']
    refine (hb k (by omega) x hx).trans ?_
    have he : β - 1 - (k : ℝ) = β - ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hxpos.le _)

/-! ### Members -/

/-- `x^γ ∈ S_γ`, to every order. -/
theorem inS_rpow_self (γ : ℝ) (d : ℕ) : InS γ d (fun x => x ^ γ) := by
  refine InS.intro (x₀ := 1)
    (C := ∑ k ∈ Finset.range (d + 1), |(descPochhammer ℝ k).eval γ|) one_pos
    (fun x hx => (Real.contDiffAt_rpow_const_of_ne (ne_of_gt
      (lt_trans one_pos hx))).contDiffWithinAt) fun k hk x hx => ?_
  have hxpos : 0 < x := lt_trans one_pos hx
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hxpos.le _)
  exact Finset.single_le_sum (f := fun k => |(descPochhammer ℝ k).eval γ|)
    (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

/-- `x^γ ∈ S_β` for `γ ≤ β`, to every order. -/
theorem inS_rpow {γ β : ℝ} (hγ : γ ≤ β) (d : ℕ) : InS β d (fun x => x ^ γ) :=
  (inS_rpow_self γ d).mono hγ

/-- `√x ∈ S_{1/2}`, to every order. -/
theorem inS_sqrt (d : ℕ) : InS (1 / 2) d Real.sqrt :=
  (inS_rpow_self (1 / 2) d).congr (a := 0) fun x _ => (Real.sqrt_eq_rpow x).symm

/-- `log x ∈ S_ε` for every `ε > 0`, to every order. -/
theorem inS_log {ε : ℝ} (hε : 0 < ε) (d : ℕ) : InS ε d Real.log := by
  have h1 : InS ε (d + 1) Real.log := by
    refine InS.of_deriv (a := 1) (C₀ := 1 / ε)
      (fun x hx =>
        (Real.differentiableAt_log (ne_of_gt (lt_trans one_pos hx))).differentiableWithinAt)
      (fun x hx => ?_) ?_
    · rw [abs_of_nonneg (Real.log_nonneg (le_of_lt hx))]
      have := Real.log_le_rpow_div (le_of_lt (lt_trans one_pos hx)) hε
      rw [div_eq_mul_inv, mul_comm] at this
      rwa [one_div]
    · rw [Real.deriv_log']
      exact (inS_rpow (by linarith : (-1 : ℝ) ≤ ε - 1) d).congr (a := 0)
        fun x _ => Real.rpow_neg_one x
  exact h1.of_le (Nat.le_succ d)

/-! ### Shift, inverse, `log (1 + h)` -/

/-- `x^e` at `x + a` against `x`: within the factor `2^{|β| + d}` once `x ≥ 2|a|`. -/
theorem rpow_add_le {x a e B : ℝ} (hx : 0 < x) (ha : 2 * |a| ≤ x) (he : |e| ≤ B) :
    (x + a) ^ e ≤ 2 ^ B * x ^ e := by
  have hlo : x / 2 ≤ x + a := by linarith [neg_abs_le a]
  have hhi : x + a ≤ 2 * x := by linarith [le_abs_self a]
  have hxa : 0 < x / 2 := by linarith
  rcases le_or_gt 0 e with he0 | he0
  · calc (x + a) ^ e ≤ (2 * x) ^ e := Real.rpow_le_rpow (by linarith) hhi he0
      _ = 2 ^ e * x ^ e := Real.mul_rpow (by norm_num) hx.le
      _ ≤ 2 ^ B * x ^ e := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by rw [abs_of_nonneg he0] at he; exact he))
          (Real.rpow_nonneg hx.le _)
  · calc (x + a) ^ e ≤ (x / 2) ^ e := Real.rpow_le_rpow_of_nonpos hxa hlo he0.le
      _ = 2 ^ (-e) * x ^ e := by
          rw [Real.div_rpow hx.le (by norm_num), Real.rpow_neg (by norm_num)]; ring
      _ ≤ 2 ^ B * x ^ e := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [abs_of_neg he0] at he; exact he))
          (Real.rpow_nonneg hx.le _)

/-- Composition with a shift `x ↦ x + a`. -/
theorem InS.comp_add {β : ℝ} {d : ℕ} {f : ℝ → ℝ} (hf : InS β d f) (a : ℝ) :
    InS β d (fun x => f (x + a)) := by
  obtain ⟨x₀, C, -, h0, hC, hs, hb⟩ := hf.exists_ge 0
  set y₀ := x₀ + 2 * |a| + 1 with hy₀
  have hy0 : 0 < y₀ := by rw [hy₀]; linarith [abs_nonneg a]
  refine InS.intro (C := C * 2 ^ (|β| + d)) hy0 ?_ fun k hk x hx => ?_
  · refine hs.comp (contDiffOn_id.add contDiffOn_const) fun x hx => ?_
    simp only [mem_Ioi] at hx ⊢
    rw [hy₀] at hx; linarith [neg_abs_le a, abs_nonneg a]
  · have hxpos : 0 < x := hy0.trans hx
    rw [hy₀] at hx
    rw [iteratedDeriv_comp_add_const]
    refine (hb k hk (x + a) (by linarith [neg_abs_le a, abs_nonneg a])).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left (rpow_add_le hxpos (by linarith [abs_nonneg a]) ?_) hC
    have hk' : (k : ℝ) ≤ d := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [abs_le]; constructor <;> linarith [abs_nonneg β, le_abs_self β, neg_abs_le β]

/-- Inverse: `g ∈ S_0` with `g ≥ c > 0` eventually gives `1/g ∈ S_0`. -/
theorem InS.inv {d : ℕ} : ∀ {g : ℝ → ℝ}, InS 0 d g → ∀ {c : ℝ}, 0 < c →
    (∀ᶠ x in atTop, c ≤ g x) → InS 0 d (fun x => (g x)⁻¹) := by
  induction d with
  | zero =>
    intro g hg c hc hev
    obtain ⟨b, hb⟩ := eventually_atTop.1 hev
    obtain ⟨x₀, C, hx₁, h0, -, hs, -⟩ := hg.exists_ge b
    refine InS.intro (C := c⁻¹) h0 (hs.inv fun x hx => ?_) fun k hk x hx => ?_
    · exact (lt_of_lt_of_le hc (hb x (hx₁.trans (le_of_lt hx)))).ne'
    · obtain rfl : k = 0 := by omega
      have hgx := hb x (hx₁.trans (le_of_lt hx))
      simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, Real.rpow_zero, mul_one]
      rw [abs_of_pos (inv_pos.2 (lt_of_lt_of_le hc hgx))]
      exact inv_anti₀ hc hgx
  | succ d ih =>
    intro g hg c hc hev
    obtain ⟨b, hb⟩ := eventually_atTop.1 hev
    obtain ⟨x₀, C, hx₁, h0, -, hs, -⟩ := hg.exists_ge b
    have hgpos : ∀ x, x₀ < x → 0 < g x := fun x hx =>
      lt_of_lt_of_le hc (hb x (hx₁.trans (le_of_lt hx)))
    have hu : InS 0 d (fun x => (g x)⁻¹) := ih (hg.of_le (Nat.le_succ d)) hc hev
    have hdg : InS (0 - 1) d (deriv g) := hg.deriv_mem
    have hprod : InS (0 - 1 + 0 + 0) d
        (fun x => (-1 * deriv g x) * (g x)⁻¹ * (g x)⁻¹) :=
      ((hdg.const_mul (-1)).mul hu).mul hu
    have hdiff : ∀ x, x₀ < x → HasDerivAt g (deriv g x) x := fun x hx =>
      ((hs.contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
    refine InS.of_deriv (a := x₀) (C₀ := c⁻¹) (fun x hx => ?_) (fun x hx => ?_) ?_
    · exact ((hdiff x hx).inv (hgpos x hx).ne').differentiableAt.differentiableWithinAt
    · rw [Real.rpow_zero, mul_one, abs_of_pos (inv_pos.2 (hgpos x hx))]
      exact inv_anti₀ hc (hb x (hx₁.trans (le_of_lt hx)))
    · refine (hprod.of_eq (by ring)).congr (a := x₀) fun x hx => ?_
      have hd : deriv (fun y => (g y)⁻¹) x = -deriv g x / g x ^ 2 :=
        ((hdiff x hx).inv (hgpos x hx).ne').deriv
      rw [hd]
      have := (hgpos x hx).ne'
      field_simp

/-- `|log (1 + t)| ≤ 2|t|` for `|t| ≤ 1/2`. -/
theorem abs_log_one_add_le {t : ℝ} (ht : |t| ≤ 1 / 2) : |Real.log (1 + t)| ≤ 2 * |t| := by
  have hy : 1 / 2 ≤ 1 + t := by linarith [neg_abs_le t]
  have hypos : 0 < 1 + t := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos hypos
  have h2 := Real.log_le_sub_one_of_pos hypos
  have hinv : (1 + t)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hypos (by norm_num)]; linarith
  have hinv0 : 0 < (1 + t)⁻¹ := inv_pos.2 hypos
  have hid : 1 - (1 + t)⁻¹ = t * (1 + t)⁻¹ := by field_simp; ring
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg (by linarith [neg_abs_le t] : 0 ≤ t + |t|) hinv0.le,
      mul_nonneg (abs_nonneg t) (by linarith : 0 ≤ 2 - (1 + t)⁻¹)]
  · linarith [le_abs_self t, abs_nonneg t]

/-- `log (1 + h) ∈ S_{−η}` for `h ∈ S_{−η}`, `η > 0`. -/
theorem InS.log_one_add {η : ℝ} (hη : 0 < η) {d : ℕ} {h : ℝ → ℝ} (hh : InS (-η) d h) :
    InS (-η) d (fun x => Real.log (1 + h x)) := by
  -- `|h| ≤ 1/2` far out
  obtain ⟨x₀, C, -, h0, hC, hs, hb⟩ := hh.exists_ge 0
  have hsmall : ∀ᶠ x in atTop, C * x ^ (-η) < 1 / 2 := by
    have ht := (tendsto_rpow_neg_atTop hη).const_mul C
    rw [mul_zero] at ht
    exact ht.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨b, hbsmall⟩ := eventually_atTop.1 hsmall
  set y₀ := max x₀ b with hy₀
  have hhx : ∀ x, y₀ < x → |h x| ≤ 1 / 2 ∧ |h x| ≤ C * x ^ (-η) := fun x hx => by
    have h1 := hb 0 (Nat.zero_le _) x (lt_of_le_of_lt (le_max_left _ _) hx)
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h1
    exact ⟨h1.trans (hbsmall x (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx))).le, h1⟩
  have hpos : ∀ x, y₀ < x → 0 < 1 + h x := fun x hx => by
    linarith [neg_abs_le (h x), (hhx x hx).1]
  have hy0 : 0 < y₀ := lt_of_lt_of_le h0 (le_max_left _ _)
  have hbound : ∀ x, y₀ < x → |Real.log (1 + h x)| ≤ 2 * C * x ^ (-η) := fun x hx => by
    rw [mul_assoc]
    exact (abs_log_one_add_le (hhx x hx).1).trans
      (mul_le_mul_of_nonneg_left (hhx x hx).2 (by norm_num))
  rcases d with _ | d
  · refine InS.intro (C := 2 * C) hy0 ?_ fun k hk x hx => ?_
    · exact ((contDiffOn_const.add hs).mono (Ioi_subset_Ioi (le_max_left _ _))).log
        fun x hx => (hpos x hx).ne'
    · obtain rfl : k = 0 := by omega
      simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero]
      exact hbound x hx
  · have hone : InS 0 (d + 1) (fun _ => (1 : ℝ)) :=
      (inS_rpow_self 0 (d + 1)).congr (a := 0) fun x _ => Real.rpow_zero x
    have h1 : InS 0 (d + 1) (fun x => 1 + h x) := hone.add (hh.mono (by linarith))
    have hinv : InS 0 (d + 1) (fun x => (1 + h x)⁻¹) :=
      h1.inv (c := 1 / 2) (by norm_num) ((eventually_gt_atTop y₀).mono fun x hx => by
        linarith [neg_abs_le (h x), (hhx x hx).1])
    have hprod : InS (-η - 1 + 0) d (fun x => deriv h x * (1 + h x)⁻¹) :=
      hh.deriv_mem.mul (hinv.of_le (Nat.le_succ d))
    have hdiff : ∀ x, y₀ < x → HasDerivAt (fun y => 1 + h y) (deriv h x) x := fun x hx =>
      (((hs.contDiffAt (Ioi_mem_nhds (lt_of_le_of_lt (le_max_left _ _) hx))).differentiableAt
        (by simp)).hasDerivAt).const_add 1
    refine InS.of_deriv (a := y₀) (C₀ := 2 * C) (fun x hx => ?_) hbound ?_
    · exact ((hdiff x hx).log (hpos x hx).ne').differentiableAt.differentiableWithinAt
    · refine (hprod.of_eq (by ring)).congr (a := y₀) fun x hx => ?_
      rw [((hdiff x hx).log (hpos x hx).ne').deriv, div_eq_mul_inv]

/-! ### Real-rootedness from a model in `S_β` -/

/-- A model in `S_β`, `β ≤ 1`, with `log α(n) − Λ(n) → 0` bounds `log (α (n + 1) / α n)` below:
`Λ(n + 1) − Λ(n) = Λ'(ξ)` and `|Λ'(ξ)| ≤ C ξ^{β−1} ≤ C`. -/
theorem exists_lower_log_ratio_of_InS {α : ℕ → ℝ} {d : ℕ} (hd : 1 ≤ d)
    (hα : ∀ᶠ n in atTop, 0 < α n) {Λ : ℝ → ℝ} {β : ℝ} (hΛ : InS β d Λ) (hβ1 : β ≤ 1)
    (hε : Tendsto (fun n : ℕ => Real.log (α n) - Λ n) atTop (𝓝 0)) :
    ∃ c, ∀ᶠ n in atTop, -c ≤ Real.log (α (n + 1) / α n) := by
  obtain ⟨x₀, C, hx₁, hx₀, hC, hs, hb⟩ := hΛ.exists_ge 1
  refine ⟨C + 2, ?_⟩
  have hsmall : ∀ᶠ n : ℕ in atTop, |Real.log (α n) - Λ n| < 1 :=
    hε.eventually ((isOpen_lt continuous_abs continuous_const).mem_nhds (by norm_num))
  filter_upwards [hα, (tendsto_add_atTop_nat 1).eventually hα, hsmall,
    (tendsto_add_atTop_nat 1).eventually hsmall,
    tendsto_natCast_atTop_atTop.eventually_gt_atTop x₀] with n h0 h1 e0 e1 hn
  have hdiff : ∀ x ∈ Ioi x₀, DifferentiableAt ℝ Λ x := fun x hx =>
    ((hs.contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by simp; omega))
  obtain ⟨ξ, hξ, hmv⟩ := exists_deriv_eq_slope Λ (lt_add_one (n : ℝ))
    (fun x hx => (hdiff x (lt_of_lt_of_le hn hx.1)).continuousAt.continuousWithinAt)
    (fun x hx => (hdiff x (lt_trans hn hx.1)).differentiableWithinAt)
  have hξ0 : x₀ < ξ := lt_trans hn hξ.1
  have hbd : |deriv Λ ξ| ≤ C := by
    have := hb 1 hd ξ hξ0
    rw [iteratedDeriv_one] at this
    refine this.trans (mul_le_of_le_one_right hC ?_)
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by push_cast; linarith)
  rw [hmv, add_sub_cancel_left, div_one] at hbd
  rw [Real.log_div h1.ne' h0.ne']
  push_cast at e1 hbd
  linarith [abs_lt.1 e0, abs_lt.1 e1, abs_le.1 hbd]

/-- **Real-rootedness from a model in `S_β`.** A model `Λ ∈ S_β` (order `d ≥ 1`), `0 < β ≤ 1`,
with `Λ'' ≤ −c x^{β−2}` far out and `log α(n) − Λ(n) = o(n^{(β−2)d/2})` gives: eventually the
degree-`d` Jensen polynomials of `α` have as many real roots, with multiplicity, as their degree. -/
theorem eventually_card_roots_of_InS {α : ℕ → ℝ} {d : ℕ} (hd : 1 ≤ d)
    (hα : ∀ᶠ n in atTop, 0 < α n)
    {Λ : ℝ → ℝ} {β c : ℝ} (hΛ : InS β d Λ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hc : 0 < c)
    (hlower : ∀ᶠ x in atTop, iteratedDeriv 2 Λ x ≤ -c * x ^ (β - 2))
    (hε : (fun n : ℕ => Real.log (α n) - Λ n) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((β - 2) * d / 2))) :
    ∀ᶠ n in atTop,
      (∑ j ∈ Finset.range (d + 1), Polynomial.C ((d.choose j : ℝ) * α (n + j)) *
          Polynomial.X ^ j).roots.card =
        (∑ j ∈ Finset.range (d + 1), Polynomial.C ((d.choose j : ℝ) * α (n + j)) *
          Polynomial.X ^ j).natDegree := by
  have hneg : (β - 2) * d / 2 < 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ ((β - 2) * d / 2)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := -((β - 2) * d / 2)) (by linarith)).comp
      tendsto_natCast_atTop_atTop
    simpa only [neg_neg, Function.comp_def] using this
  have hlow := exists_lower_log_ratio_of_InS hd hα hΛ hβ1 (hε.trans_tendsto hlim)
  obtain ⟨x₀, C, -, hs, hb⟩ := hΛ
  exact eventually_card_roots_of_smooth_model' (K := C) hd hα hlow hs hβ0 (by linarith) hc
    (fun k hk => (eventually_gt_atTop x₀).mono fun x hx => hb k (Finset.mem_Icc.1 hk).2 x hx)
    hlower hε

end

end MetaMathlibExt.ColoredPartitionsJensen
