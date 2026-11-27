/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 8

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry12Qgammaintegers

open scoped Interval
open MeasureTheory

noncomputable section

def chapter8UnitPow (x : ℂ) (u : ℝ) : ℂ :=
  if u = 0 then 0 else Complex.exp (x * Real.log u)

def chapter8Entry12Kernel (x : ℂ) (u : ℝ) : ℂ :=
  if u = 0 then 0
  else if u = 1 then 0
  else
    chapter8UnitPow (x - 2) u * ((1 - u : ℝ) : ℂ) ^ 2 /
      (1 - chapter8UnitPow x u)

def chapter8PhiTerm (x : ℂ) (j : ℕ) : ℂ :=
  let k := j + 1
  2 / ((((k : ℂ) * x) ^ 3) - (k : ℂ) * x)

def chapter8Phi (x : ℂ) : ℂ :=
  1 + ∑' j : ℕ, chapter8PhiTerm x j

/-- Summand as a function of u: cpow form, defined everywhere. -/
private def chapter8Fterm (x : ℂ) (j : ℕ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ ((((j + 1 : ℕ)) : ℂ) * x - 2) * (((1 - u : ℝ)) : ℂ) ^ 2

/-- Real majorant for dominated convergence. -/
private def chapter8Bound (x : ℂ) (j : ℕ) (u : ℝ) : ℝ :=
  u ^ (x.re - 2) * u ^ ((j : ℝ)) * (1 - u) ^ 2

private lemma aux_denom (x : ℂ) (hx : 1 < x.re) (j : ℕ) :
    let k : ℂ := j + 1
    (k * x) ^ 3 - k * x ≠ 0 := by
  intro k
  have h1 : (1:ℝ) ≤ k.re := by
    have hj : (0:ℝ) ≤ ((j : ℂ)).re := by simp [Complex.natCast_re, Nat.cast_nonneg]
    have hkk : k.re = ((j : ℂ)).re + 1 := by simp [k, Complex.add_re]
    linarith
  have hzx : (1:ℝ) < (k * x).re := by
    have hkim : k.im = 0 := by
      simp [k, Complex.natCast_im]
    have hre : (k * x).re = k.re * x.re := by
      rw [Complex.mul_re, hkim]; simp
    rw [hre]
    nlinarith [hx, h1]
  have hfac : (k * x) ^ 3 - k * x = (k * x) * ((k * x) - 1) * ((k * x) + 1) := by ring
  rw [hfac]
  apply mul_ne_zero
  · apply mul_ne_zero
    · intro h
      have h2 : (k * x).re = 0 := by rw [h]; rfl
      linarith
    · intro h
      have h2 : ((k * x) - 1).re = 0 := by rw [h]; rfl
      rw [Complex.sub_re, Complex.one_re] at h2
      linarith
  · intro h
    have h2 : ((k * x) + 1).re = 0 := by rw [h]; rfl
    rw [Complex.add_re, Complex.one_re] at h2
    linarith

/-- **Exponential and principal powers agree for positive bases (Chapter 8, Entry 12).** For a
complex number $x$ and a real number $u$, let $P_x(u) = 0$ if $u = 0$ and
$P_x(u) = e^{x \log |u|}$ otherwise. Then for every complex $x$ and every real $u > 0$,
$P_x(u) = u^x$, where $u^x$ is the principal complex power. -/
theorem chapter8UnitPow_eq_cpow (x : ℂ) (u : ℝ) (hu : 0 < u) :
    chapter8UnitPow x u = (u : ℂ) ^ x := by
  have hune : u ≠ 0 := ne_of_gt hu
  have hcu : (u : ℂ) ≠ 0 := by exact_mod_cast hune
  unfold chapter8UnitPow
  simp only [hune, ↓reduceIte]
  rw [Complex.cpow_def_of_ne_zero hcu, Complex.ofReal_log hu.le]
  congr 1
  ring

private lemma aux_norm (x : ℂ) (hx : 1 < x.re) (u : ℝ) (hu : u ∈ Set.Ioo 0 1) :
    ‖(u : ℂ) ^ x‖ < 1 := by
  obtain ⟨hu0, hu1⟩ := hu
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  have hxpos : (0:ℝ) < x.re := by linarith
  exact Real.rpow_lt_one hu0.le hu1 hxpos

private lemma aux_kernel0 (x : ℂ) : chapter8Entry12Kernel x 0 = 0 := by
  unfold chapter8Entry12Kernel
  simp

private lemma aux_kernel1 (x : ℂ) : chapter8Entry12Kernel x 1 = 0 := by
  unfold chapter8Entry12Kernel
  simp

private lemma aux_kernel_ne (x : ℂ) (hx : 1 < x.re) (u : ℝ) (hu : u ∈ Set.Ioo 0 1) :
    1 - (u : ℂ) ^ x ≠ 0 := by
  have hnorm := aux_norm x hx u hu
  intro h
  have hq : (u : ℂ) ^ x = 1 := (sub_eq_zero.mp h).symm
  rw [hq, norm_one] at hnorm
  exact lt_irrefl 1 hnorm

private lemma aux_kernel_form (x : ℂ) (u : ℝ) (hu : 0 < u) (hu1 : u ≠ 1) :
    chapter8Entry12Kernel x u =
      (u : ℂ) ^ (x - 2) * ((1 - u : ℝ) : ℂ) ^ 2 /
        (1 - (u : ℂ) ^ x) := by
  have hu0 : u ≠ 0 := ne_of_gt hu
  unfold chapter8Entry12Kernel
  rw [ite_eq_right hu0, ite_eq_right hu1, chapter8UnitPow_eq_cpow (x - 2) u hu,
    chapter8UnitPow_eq_cpow x u hu]

private lemma aux_term (x : ℂ) (u : ℝ) (hu : 0 < u) (j : ℕ) :
    (u : ℂ) ^ (x - 2) * ((u : ℂ) ^ x) ^ j =
      (u : ℂ) ^ ((((j + 1 : ℕ)) : ℂ) * x - 2) := by
  have hcu : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hcu]
  congr 1
  push_cast
  ring

private lemma aux_Fterm_eq (x : ℂ) (u : ℝ) (hu : 0 < u) (j : ℕ) :
    chapter8Fterm x j u =
      (u : ℂ) ^ (x - 2) * ((u : ℂ) ^ x) ^ j * (((1 - u : ℝ)) : ℂ) ^ 2 := by
  have ht := aux_term x u hu j
  unfold chapter8Fterm
  rw [← ht]

private lemma aux_hasSum (x : ℂ) (hx : 1 < x.re) (u : ℝ) (hu : u ∈ Set.Ioo 0 1) :
    HasSum (fun j => chapter8Fterm x j u) (chapter8Entry12Kernel x u) := by
  have hu0 : 0 < u := hu.1
  have hu1 : u < 1 := hu.2
  have hun1 : u ≠ 1 := ne_of_lt hu1
  have hnorm : ‖(u : ℂ) ^ x‖ < 1 := aux_norm x hx u hu
  have hgeom := hasSum_geometric_of_norm_lt_one hnorm
  have hker : chapter8Entry12Kernel x u =
      (u : ℂ) ^ (x - 2) * (((1 - u : ℝ)) : ℂ) ^ 2 * (1 - (u : ℂ) ^ x)⁻¹ := by
    rw [aux_kernel_form x u hu0 hun1, div_eq_mul_inv]
  have hmul := hgeom.mul_left ((u : ℂ) ^ (x - 2) * (((1 - u : ℝ)) : ℂ) ^ 2)
  rw [← hker] at hmul
  refine hmul.congr_fun (fun j => ?_)
  rw [aux_Fterm_eq x u hu0 j]
  ring

private lemma aux_zre (x : ℂ) (j : ℕ) :
    ((((j + 1 : ℕ)) : ℂ) * x - 2).re = (x.re - 2) + (j : ℝ) * x.re := by
  have h2 : (2:ℂ).re = (2:ℝ) := by simp
  rw [Complex.sub_re, Complex.mul_re, h2]
  simp only [Complex.natCast_re, Complex.natCast_im]
  push_cast
  ring

private lemma aux_normF (x : ℂ) (hx : 1 < x.re) (u : ℝ) (hu : u ∈ Set.Ioo 0 1) (j : ℕ) :
    ‖chapter8Fterm x j u‖ ≤ chapter8Bound x j u := by
  have hu0 : 0 < u := hu.1
  have hu1 : u < 1 := hu.2
  have h1u : (0:ℝ) ≤ 1 - u := by linarith
  have hx1 : (1:ℝ) ≤ x.re := le_of_lt hx
  have hjnn : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
  have hnorm : ‖chapter8Fterm x j u‖ =
      u ^ ((((j + 1 : ℕ)) : ℂ) * x - 2).re * (1 - u) ^ 2 := by
    unfold chapter8Fterm
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    congr 1
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1u]
  rw [hnorm]
  unfold chapter8Bound
  have hle : u ^ ((((j + 1 : ℕ)) : ℂ) * x - 2).re ≤ u ^ (x.re - 2) * u ^ ((j : ℝ)) := by
    rw [aux_zre, Real.rpow_add hu0]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (le_of_lt hu0) _)
    apply Real.rpow_le_rpow_of_exponent_ge hu0 (le_of_lt hu1)
    calc (j:ℝ) = (j:ℝ) * 1 := by ring
      _ ≤ (j:ℝ) * x.re := mul_le_mul_of_nonneg_left hx1 hjnn
  calc u ^ ((((j + 1 : ℕ)) : ℂ) * x - 2).re * (1 - u) ^ 2
      ≤ (u ^ (x.re - 2) * u ^ ((j : ℝ))) * (1 - u) ^ 2 :=
        mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    _ = u ^ (x.re - 2) * u ^ ((j : ℝ)) * (1 - u) ^ 2 := by ring

private lemma aux_bound_summable (x : ℂ) (u : ℝ) (hu : u ∈ Set.Ioo 0 1) :
    Summable (fun j => chapter8Bound x j u) := by
  have hu0 : 0 < u := hu.1
  have hu1 : u < 1 := hu.2
  have hnorm : ‖(u : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hu0]; exact hu1
  have hgeom := summable_geometric_of_norm_lt_one hnorm
  have hfun : (fun j => chapter8Bound x j u) =
      (fun j => (u ^ (x.re - 2) * (1 - u) ^ 2) * u ^ (j:ℕ)) := by
    funext j
    unfold chapter8Bound
    simp only [Real.rpow_natCast]
    ring
  rw [hfun]
  exact hgeom.mul_left _

private lemma aux_bound_tsum (x : ℂ) (u : ℝ) (hu : u ∈ Set.Ioo 0 1) :
    ∑' j, chapter8Bound x j u = u ^ (x.re - 2) * (1 - u) := by
  have hu0 : 0 < u := hu.1
  have hu1 : u < 1 := hu.2
  have hnorm : ‖(u : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hu0]; exact hu1
  have hgeom := tsum_geometric_of_norm_lt_one hnorm
  have hEq : ∀ j, chapter8Bound x j u = (u ^ (x.re - 2) * (1 - u) ^ 2) * u ^ (j:ℕ) := by
    intro j
    unfold chapter8Bound
    simp only [Real.rpow_natCast]
    ring
  rw [tsum_congr hEq, tsum_mul_left, hgeom]
  have hu1' : (1 : ℝ) - u ≠ 0 := by
    intro h; linarith
  field_simp

private lemma aux_expand (z : ℂ) (u : ℝ) (hu : u ≠ 0) :
    ((u : ℂ) ^ (z - 2)) * (((1 - u : ℝ)) : ℂ) ^ 2 =
      (u : ℂ) ^ (z - 2) - 2 * (u : ℂ) ^ (z - 1) + (u : ℂ) ^ z := by
  have hcu : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  have h1 : (((1 - u : ℝ)) : ℂ) = 1 - (u : ℂ) := by push_cast; ring
  rw [h1]
  have hsq : (1 - (u:ℂ)) ^ 2 = 1 - 2 * (u:ℂ) + (u:ℂ)^(2:ℕ) := by ring
  rw [hsq]
  have e1 : (u:ℂ)^(z-2) * (u:ℂ) = (u:ℂ)^(z-1) := by
    have h := (Complex.cpow_add (z-2) 1 hcu).symm
    rw [Complex.cpow_one] at h
    have heq : z - 2 + 1 = z - 1 := by ring
    rw [heq] at h
    exact h
  have e1' : (u:ℂ)^(z-2) * (2 * (u:ℂ)) = 2 * (u:ℂ)^(z-1) := by
    calc (u:ℂ)^(z-2) * (2 * (u:ℂ)) = 2 * ((u:ℂ)^(z-2) * (u:ℂ)) := by ring
      _ = 2 * (u:ℂ)^(z-1) := by rw [e1]
  have e2 : (u:ℂ)^(z-2) * (u:ℂ)^(2:ℕ) = (u:ℂ)^z := by
    have h := (Complex.cpow_add (z-2) 2 hcu).symm
    have heq : z - 2 + 2 = z := by ring
    rw [heq, Complex.cpow_two] at h
    exact h
  calc (u:ℂ)^(z-2) * (1 - 2 * (u:ℂ) + (u:ℂ)^(2:ℕ))
      = (u:ℂ)^(z-2) - (u:ℂ)^(z-2) * (2 * (u:ℂ)) + (u:ℂ)^(z-2) * (u:ℂ)^(2:ℕ) := by ring
    _ = (u:ℂ)^(z-2) - 2 * (u:ℂ)^(z-1) + (u:ℂ)^z := by rw [e1', e2]

private lemma aux_intcpow (w : ℂ) (hw : -1 < w.re) :
    (∫ u in (0:ℝ)..1, ((u : ℂ) ^ w)) = 1 / (w + 1) := by
  rw [integral_cpow (Or.inl hw)]
  have h1 : ((1 : ℝ) : ℂ) ^ (w + 1) = 1 := by exact_mod_cast Complex.one_cpow (w+1)
  have h0 : ((0 : ℝ) : ℂ) ^ (w + 1) = 0 := by
    apply Complex.zero_cpow
    intro h
    have hre : (w + 1).re = 0 := by rw [h]; rfl
    rw [Complex.add_re, Complex.one_re] at hre
    linarith [hw]
  rw [h1, h0, sub_zero]

private lemma aux_termintegral (x : ℂ) (hx : 1 < x.re) (j : ℕ) :
    (∫ u in (0:ℝ)..1, chapter8Fterm x j u) = chapter8PhiTerm x j := by
  set z : ℂ := (((j + 1 : ℕ)) : ℂ) * x with hz
  have hj1 : (1:ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
    have h : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    push_cast
    linarith
  have hzre : (1:ℝ) < z.re := by
    rw [hz, Complex.mul_re]
    simp only [Complex.natCast_im, Complex.natCast_re]
    nlinarith [hx, hj1]
  have h1 : -1 < (z - 2).re := by
    have hsub : (z - 2).re = z.re - 2 := by
      simp [Complex.sub_re]
    linarith
  have h2 : -1 < (z - 1).re := by
    have hsub : (z - 1).re = z.re - 1 := by
      rw [Complex.sub_re, Complex.one_re]
    linarith
  have h3 : -1 < z.re := by linarith
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 0 := by
    rw [ae_iff]; simp
  have hae : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Ι (0:ℝ) 1 →
      chapter8Fterm x j u =
        ((u:ℂ)^(z-2) - 2*(u:ℂ)^(z-1) + (u:ℂ)^z) := by
    filter_upwards [hne] with u hu _hmem
    unfold chapter8Fterm
    rw [hz]
    exact aux_expand _ _ hu
  rw [intervalIntegral.integral_congr_ae hae]
  have i1 : IntervalIntegrable (fun u : ℝ => (u:ℂ)^(z-2)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_cpow' h1
  have i2 : IntervalIntegrable (fun u : ℝ => (u:ℂ)^(z-1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_cpow' h2
  have i3 : IntervalIntegrable (fun u : ℝ => (u:ℂ)^z) volume 0 1 :=
    intervalIntegral.intervalIntegrable_cpow' h3
  have hint : IntervalIntegrable
      (fun u : ℝ => ((u:ℂ)^(z-2) - 2*(u:ℂ)^(z-1) + (u:ℂ)^z)) volume 0 1 := by
    apply IntervalIntegrable.add
    · apply IntervalIntegrable.sub
      · exact i1
      · exact i2.const_mul 2
    · exact i3
  rw [intervalIntegral.integral_add (IntervalIntegrable.sub i1 (i2.const_mul 2)) i3,
    intervalIntegral.integral_sub i1 (i2.const_mul 2)]
  rw [intervalIntegral.integral_const_mul, aux_intcpow _ h1, aux_intcpow _ h2,
    aux_intcpow _ h3]
  have e1 : z - 2 + 1 = z - 1 := by ring
  have e2 : z - 1 + 1 = z := by ring
  rw [e1, e2]
  have hz0 : z ≠ 0 := by
    intro h
    have hzz : z.re = 0 := by rw [h]; rfl
    linarith
  have hz1 : z - 1 ≠ 0 := by
    intro h
    have hzz : (z-1).re = 0 := by rw [h]; rfl
    rw [Complex.sub_re, Complex.one_re] at hzz; linarith
  have hz2 : z + 1 ≠ 0 := by
    intro h
    have hzz : (z+1).re = 0 := by rw [h]; rfl
    rw [Complex.add_re, Complex.one_re] at hzz; linarith
  have hid : 1 / (z - 1) - 2 * (1 / z) + 1 / (z + 1) = 2 / (z ^ 3 - z) := by
    have hfac : z ^ 3 - z = z * (z - 1) * (z + 1) := by ring
    rw [hfac]; field_simp; ring
  rw [hid]
  unfold chapter8PhiTerm
  simp only [hz]

private lemma aux_memIoo (u : ℝ) (huI : u ∈ Ι (0 : ℝ) 1) (hu1 : u ≠ 1) :
    u ∈ Set.Ioo 0 1 := by
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at huI
  exact ⟨huI.1, lt_of_le_of_ne huI.2 hu1⟩

private lemma aux_h01 : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 0 ∧ u ≠ 1 := by
  have h0 : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 0 := by
    rw [ae_iff]; simp
  have h1 : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 1 := by
    rw [ae_iff]; simp
  filter_upwards [h0, h1] with u hu0 hu1 using ⟨hu0, hu1⟩

private lemma aux_expansion_integrable (x : ℂ) (hx : 1 < x.re) (j : ℕ) :
    IntervalIntegrable
      (fun u : ℝ => ((u:ℂ)^((((j+1:ℕ)):ℂ) * x - 2) - 2*(u:ℂ)^((((j+1:ℕ)):ℂ) * x - 1)
        + (u:ℂ)^((((j+1:ℕ)):ℂ) * x)))
      volume 0 1 := by
  have hj1 : (1:ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
    have h : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    push_cast
    linarith
  have hzre : (1:ℝ) < (((((j + 1 : ℕ)) : ℂ) * x)).re := by
    rw [Complex.mul_re]
    simp only [Complex.natCast_im, Complex.natCast_re]
    nlinarith [hx, hj1]
  have hsub2 : ∀ w : ℂ, (w - 2).re = w.re - 2 := by
    intro w
    have h2 : (2:ℂ).re = (2:ℝ) := by simp
    rw [Complex.sub_re, h2]
  have hsub1 : ∀ w : ℂ, (w - 1).re = w.re - 1 := by
    intro w
    rw [Complex.sub_re, Complex.one_re]
  have h1 : -1 < (((((j + 1 : ℕ)) : ℂ) * x - 2)).re := by
    rw [hsub2]; linarith
  have h2 : -1 < (((((j + 1 : ℕ)) : ℂ) * x - 1)).re := by
    rw [hsub1]; linarith
  have h3 : -1 < (((((j + 1 : ℕ)) : ℂ) * x)).re := by linarith
  exact ((intervalIntegral.intervalIntegrable_cpow' h1).sub
    ((intervalIntegral.intervalIntegrable_cpow' h2).const_mul 2)).add
    (intervalIntegral.intervalIntegrable_cpow' h3)

private lemma aux_Fintegrable (x : ℂ) (hx : 1 < x.re) (j : ℕ) :
    IntervalIntegrable (chapter8Fterm x j) volume 0 1 := by
  apply IntervalIntegrable.congr_ae (aux_expansion_integrable x hx j)
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards [aux_h01] with u ⟨hu0, _⟩
  intro _
  unfold chapter8Fterm
  exact (aux_expand _ _ hu0).symm

private lemma aux_hmeas (x : ℂ) (hx : 1 < x.re) (j : ℕ) :
    AEStronglyMeasurable (chapter8Fterm x j) (volume.restrict (Ι (0:ℝ) 1)) :=
  Integrable.aestronglyMeasurable (intervalIntegrable_iff.mp (aux_Fintegrable x hx j))

private lemma aux_closedIntegrable (x : ℂ) (hx : 1 < x.re) :
    IntervalIntegrable (fun u : ℝ => u ^ (x.re - 2) * (1 - u)) volume 0 1 := by
  have hbase : IntervalIntegrable (fun u : ℝ => u ^ (x.re - 2)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1:ℝ) < x.re - 2)
  have hcont : ContinuousOn (fun u : ℝ => 1 - u) ([[0, 1]] : Set ℝ) :=
    (continuous_const.sub continuous_id).continuousOn
  exact hbase.mul_continuousOn hcont

private lemma aux_boundtsum_integrable (x : ℂ) (hx : 1 < x.re) :
    IntervalIntegrable (fun u => ∑' j, chapter8Bound x j u) volume 0 1 := by
  apply IntervalIntegrable.congr_ae (aux_closedIntegrable x hx)
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards [aux_h01] with u ⟨hu0, hu1⟩
  intro huI
  exact (aux_bound_tsum x u (aux_memIoo u huI hu1)).symm

private lemma aux_tsumF_integrable (x : ℂ) (hx : 1 < x.re) :
    Integrable (fun u => ∑' j, chapter8Fterm x j u) (volume.restrict (Ι (0:ℝ) 1)) := by
  apply Integrable.mono' (intervalIntegrable_iff.mp (aux_boundtsum_integrable x hx))
  · exact AEStronglyMeasurable.tsum (fun j => aux_hmeas x hx j)
  · refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [aux_h01] with u ⟨hu0, hu1⟩
    intro huI
    have hu := aux_memIoo u huI hu1
    have hnorms : Summable (fun j => ‖chapter8Fterm x j u‖) :=
      Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => aux_normF x hx u hu j)
        (aux_bound_summable x u hu)
    calc ‖∑' j, chapter8Fterm x j u‖ ≤ ∑' j, ‖chapter8Fterm x j u‖ :=
          norm_tsum_le_tsum_norm hnorms
      _ ≤ ∑' j, chapter8Bound x j u :=
          Summable.tsum_le_tsum (fun j => aux_normF x hx u hu j) hnorms
            (aux_bound_summable x u hu)

private lemma aux_kernel_intervalIntegrable (x : ℂ) (hx : 1 < x.re) :
    IntervalIntegrable (chapter8Entry12Kernel x) volume 0 1 := by
  have hInt : IntervalIntegrable (fun u => ∑' j, chapter8Fterm x j u) volume 0 1 := by
    rw [intervalIntegrable_iff]
    exact aux_tsumF_integrable x hx
  apply IntervalIntegrable.congr_ae hInt
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  refine Filter.Eventually.of_forall (fun u huI => ?_)
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at huI
  by_cases hu1 : u = 1
  · subst hu1
    have h0 : ∀ j, chapter8Fterm x j (1:ℝ) = 0 := by
      intro j
      unfold chapter8Fterm
      push_cast
      simp
    change ∑' j, chapter8Fterm x j (1:ℝ) = chapter8Entry12Kernel x 1
    rw [tsum_congr h0, tsum_zero, aux_kernel1 x]
  · have hu : u ∈ Set.Ioo 0 1 := ⟨huI.1, lt_of_le_of_ne huI.2 hu1⟩
    exact HasSum.tsum_eq (aux_hasSum x hx u hu)

/-- **Ramanujan's integral for $\varphi(x) - 1$ with principal powers (Chapter 8, Entry 12).**
Let $x$ be a complex number with $\operatorname{Re} x > 1$. For real $u$ and complex $s$ put
$P_s(u) = 0$ if $u = 0$ and $P_s(u) = e^{s \log |u|}$ otherwise, and define $K_x(0) = 0$,
$K_x(1) = 0$ and $K_x(u) = \frac{P_{x-2}(u)\,(1 - u)^2}{1 - P_x(u)}$ for every other real $u$, the
quotient being taken to be $0$ at $u = -1$, where its denominator vanishes. Let
$\varphi(x) = 1 + \sum_{k \ge 1} \frac{2}{(kx)^3 - kx}$. Then $(kx)^3 - kx \ne 0$ for every
positive integer $k$; the series $\sum_{k \ge 1} \frac{2}{(kx)^3 - kx}$ converges
unconditionally; $K_x(0) = 0$ and $K_x(1) = 0$; for every $u \in (0, 1)$, with $u^x$ and
$u^{x-2}$ the principal complex powers, $1 - u^x \ne 0$ and
$K_x(u) = \frac{u^{x-2}\,(1 - u)^2}{1 - u^x}$; $K_x$ is integrable on $[0, 1]$; and
$$\int_0^1 K_x(u)\,du = \varphi(x) - 1.$$

For $u > 0$ the powers $P_s(u)$ and $u^s$ agree, so this is the same statement as the version
written with $P_s$.
-/
theorem ramanujan_part1_ch8_entry12_qgammaintegers_cpow (x : ℂ) (hx : 1 < x.re) :
    (∀ j : ℕ,
      let k : ℂ := j + 1
      (k * x) ^ 3 - k * x ≠ 0) ∧
      Summable (chapter8PhiTerm x) ∧
      chapter8Entry12Kernel x 0 = 0 ∧
      chapter8Entry12Kernel x 1 = 0 ∧
      (∀ u : ℝ, u ∈ Set.Ioo 0 1 →
        1 - (u : ℂ) ^ x ≠ 0 ∧
          chapter8Entry12Kernel x u =
            (u : ℂ) ^ (x - 2) * ((1 - u : ℝ) : ℂ) ^ 2 /
              (1 - (u : ℂ) ^ x)) ∧
      IntervalIntegrable (chapter8Entry12Kernel x) volume 0 1 ∧
      (∫ u in (0 : ℝ)..1, chapter8Entry12Kernel x u) =
        chapter8Phi x - 1 := by
  have hmain : HasSum (fun j => ∫ u in (0:ℝ)..1, chapter8Fterm x j u)
      (∫ u in (0:ℝ)..1, chapter8Entry12Kernel x u) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun j u => chapter8Bound x j u) ?_ ?_ ?_ ?_ ?_
    · intro j
      exact aux_hmeas x hx j
    · intro j
      filter_upwards [aux_h01] with u ⟨hu0, hu1⟩
      intro huI
      exact aux_normF x hx u (aux_memIoo u huI hu1) j
    · filter_upwards [aux_h01] with u ⟨hu0, hu1⟩
      intro huI
      exact aux_bound_summable x u (aux_memIoo u huI hu1)
    · exact aux_boundtsum_integrable x hx
    · filter_upwards [aux_h01] with u ⟨hu0, hu1⟩
      intro huI
      exact aux_hasSum x hx u (aux_memIoo u huI hu1)
  have hmain2 : HasSum (chapter8PhiTerm x)
      (∫ u in (0:ℝ)..1, chapter8Entry12Kernel x u) := by
    have heq : (fun j => ∫ u in (0:ℝ)..1, chapter8Fterm x j u) = chapter8PhiTerm x := by
      funext j
      exact aux_termintegral x hx j
    rwa [heq] at hmain
  refine ⟨fun j => aux_denom x hx j, hmain2.summable, aux_kernel0 x, aux_kernel1 x, ?_,
    aux_kernel_intervalIntegrable x hx, ?_⟩
  · intro u hu
    exact ⟨aux_kernel_ne x hx u hu,
      aux_kernel_form x u hu.1 (ne_of_lt hu.2)⟩
  · have htsum := HasSum.tsum_eq hmain2
    unfold chapter8Phi
    rw [htsum]
    ring

/-- **Ramanujan's integral for $\varphi(x) - 1$ (Chapter 8, Entry 12).** Let $x$ be a complex
number with $\operatorname{Re} x > 1$. For real $u$ and complex $s$ put $P_s(u) = 0$ if $u = 0$
and $P_s(u) = e^{s \log |u|}$ otherwise, and define $K_x(0) = 0$, $K_x(1) = 0$ and
$K_x(u) = \frac{P_{x-2}(u)\,(1 - u)^2}{1 - P_x(u)}$ for every other real $u$, the quotient being
taken to be $0$ at $u = -1$, where its denominator vanishes. Let
$\varphi(x) = 1 + \sum_{k \ge 1} \frac{2}{(kx)^3 - kx}$. Then $(kx)^3 - kx \ne 0$ for every
positive integer $k$; the series $\sum_{k \ge 1} \frac{2}{(kx)^3 - kx}$ converges
unconditionally; $K_x(0) = 0$ and $K_x(1) = 0$; for every $u \in (0, 1)$,
$1 - P_x(u) \ne 0$ and $K_x(u) = \frac{P_{x-2}(u)\,(1 - u)^2}{1 - P_x(u)}$; $K_x$ is integrable
on $[0, 1]$; and
$$\int_0^1 K_x(u)\,du = \varphi(x) - 1.$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8.
-/
theorem ramanujan_part1_ch8_entry12_qgammaintegers (x : ℂ) (hx : 1 < x.re) :
    (∀ j : ℕ,
      let k : ℂ := j + 1
      (k * x) ^ 3 - k * x ≠ 0) ∧
      Summable (chapter8PhiTerm x) ∧
      chapter8Entry12Kernel x 0 = 0 ∧
      chapter8Entry12Kernel x 1 = 0 ∧
      (∀ u : ℝ, u ∈ Set.Ioo 0 1 →
        1 - chapter8UnitPow x u ≠ 0 ∧
          chapter8Entry12Kernel x u =
            chapter8UnitPow (x - 2) u * ((1 - u : ℝ) : ℂ) ^ 2 /
              (1 - chapter8UnitPow x u)) ∧
      IntervalIntegrable (chapter8Entry12Kernel x) volume 0 1 ∧
      (∫ u in (0 : ℝ)..1, chapter8Entry12Kernel x u) =
        chapter8Phi x - 1 := by
  obtain ⟨hdenom, hsum, hk0, hk1, hker, hint, hval⟩ :=
    ramanujan_part1_ch8_entry12_qgammaintegers_cpow x hx
  refine ⟨hdenom, hsum, hk0, hk1, ?_, hint, hval⟩
  intro u hu
  obtain ⟨hne, hform⟩ := hker u hu
  rw [← chapter8UnitPow_eq_cpow x u hu.1] at hne
  rw [← chapter8UnitPow_eq_cpow x u hu.1, ← chapter8UnitPow_eq_cpow (x - 2) u hu.1] at hform
  exact ⟨hne, hform⟩

end
end Entry12Qgammaintegers
end MathlibExt.Analysis.Ramanujan.Part1Ch8
end
