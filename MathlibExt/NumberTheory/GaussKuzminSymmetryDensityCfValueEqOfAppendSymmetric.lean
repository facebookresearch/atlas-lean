/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.NumberTheory.GaussKuzminSymmetry
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.Topology.Order.ProjIcc
import MathlibExt.NumberTheory.GaussKuzminFundamentalIntervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Density at a convergent from symmetric one-digit extensions

This module proves that symmetry of the integrals over one-digit extensions fixes the density
at the corresponding convergent.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 3.1.
-/

namespace MetaMathlibExt

open MeasureTheory Filter Topology Real

private theorem matrix_bounds (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    0 ≤ convergentMatrix a 0 0 ∧ 0 ≤ convergentMatrix a 0 1 ∧
      0 ≤ convergentMatrix a 1 0 ∧ 0 < convergentMatrix a 1 1 ∧
      convergentMatrix a 0 1 ≤ convergentMatrix a 1 1 := by
  induction a with
  | nil => simp [convergentMatrix_nil]
  | cons t a ih =>
    obtain ⟨h00, h01, h10, h11, -⟩ := ih (fun x hx => ha x (by simp [hx]))
    have ht : (1 : ℤ) ≤ t := by exact_mod_cast ha t (by simp)
    have hmul : convergentMatrix a 1 1 ≤ (t : ℤ) * convergentMatrix a 1 1 :=
      le_mul_of_one_le_left h11.le ht
    simp only [convergentMatrix_cons, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      zero_mul, one_mul, zero_add]
    refine ⟨h10, h11.le, ?_, ?_, ?_⟩
    · positivity
    · linarith
    · linarith

private theorem average_tendsto (g : ℝ → ℝ) (hg : Continuous g)
    (u v : ℕ → ℝ) (x : ℝ) (hu : Tendsto u atTop (𝓝 x))
    (hv : Tendsto v atTop (𝓝 x)) (hne : ∀ n, u n ≠ v n) :
    Tendsto (fun n => (∫ y in fundInterval (u n) (v n), g y) / |v n - u n|)
      atTop (𝓝 (g x)) := by
  choose c hc heq using fun n => exists_eq_interval_average (hne n) hg.continuousOn
  have hc_lim : Tendsto c atTop (𝓝 x) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using hu.min hv) (by simpa using hu.max hv)
      (fun n => (hc n).1.le) (fun n => (hc n).2.le)
  have h_integral (n : ℕ) :
      (∫ y in fundInterval (u n) (v n), g y) = ∫ y in Set.uIoc (u n) (v n), g y := by
    by_cases h : u n < v n
    · simpa [fundInterval, h, Set.uIoc_of_le h.le] using
        (integral_Ico_eq_integral_Ioc (f := g) (x := u n) (y := v n))
    · simp [fundInterval, h, Set.uIoc_of_ge (le_of_not_gt h)]
  have h_average (n : ℕ) :
      (∫ y in fundInterval (u n) (v n), g y) / |v n - u n| = g (c n) := by
    rw [h_integral]
    simpa [setAverage_eq, measureReal_def, div_eq_inv_mul] using (heq n).symm
  exact (hg.tendsto x |>.comp hc_lim).congr (fun n => (h_average n).symm)

private theorem affine_ratio_tendsto (r s p q : ℝ) (hq : q ≠ 0) :
    Tendsto (fun n : ℕ => (r + (n + 1) * p) / (s + (n + 1) * q))
      atTop (𝓝 (p / q)) := by
  simpa only [add_mul, one_mul, mul_comm p, mul_comm q, add_assoc, add_left_comm,
    add_comm] using tendsto_add_mul_div_add_mul_atTop_nhds (r + p) (s + q) p hq

private theorem cylinder_integral_eq (f g : ℝ → ℝ)
    (hfg : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = g x) (b : List ℕ) (α β : ℝ)
    (h : cfCylinder b =ᵐ[volume] fundInterval α β) :
    (∫ x in cfCylinder b, f x) = ∫ x in fundInterval α β, g x := by
  have hm : MeasurableSet (fundInterval α β) := by
    unfold fundInterval
    split_ifs
    · exact measurableSet_Ico
    · exact measurableSet_Ioc
  rw [← setIntegral_congr_set h (f := g)]
  exact setIntegral_congr_ae₀ (hm.nullMeasurableSet.congr h.symm)
    (ae_of_all _ fun x hx => hfg x ⟨hx.1.1, hx.1.2.le⟩)

/-- **Symmetric one-digit extensions fix the density at a rational point.** Let $f$ be a real
function that is continuous and nonnegative on $[0, 1]$ with $\int_0^1 f(x)\,dx = 1$. Let
$a = (a_1, \dots, a_n)$ be a string of positive integers, let $p$ and $q$ be the upper-right and
lower-right entries of its convergent matrix $C(a)$, so that $p/q = [0; a_1, \dots, a_n]$, and let
$\overleftarrow{a}$ be the reverse of $a$. Write $I(b)$ for the fundamental interval of a string
$b$, $(a, t)$ for $a$ followed by $t$, and $(t, \overleftarrow{a})$ for $t$ followed by
$\overleftarrow{a}$. If $\int_{I(a, t)} f(x)\,dx = \int_{I(t, \overleftarrow{a})} f(x)\,dx$ for
every integer $t \ge 1$, then $f(p/q) = f(0)/(1 + p/q)$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 3.1 (`integers-2025-A89-lem-3-1`). -/
public theorem density_cfValue_eq_of_append_symmetric (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) (hf0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x)
    (hf1 : ∫ x in (0 : ℝ)..1, f x = 1) (a : List ℕ) (ha : (∀ x ∈ a, 0 < x))
    (hsym : ∀ t : ℕ, 1 ≤ t →
      ∫ x in cfCylinder (a ++ [t]), f x = ∫ x in cfCylinder (t :: a.reverse), f x) :
    f ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ)) = f 0 / (1 +
        (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ)) := by
  have _ := hf0
  have _ := hf1
  let g := Set.IccExtend (show (0 : ℝ) ≤ 1 by norm_num) (Set.Icc (0 : ℝ) 1 |>.domRestrict f)
  have hg : Continuous g := hf.domRestrict.Icc_extend'
  have hg_eq (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : g x = f x :=
    Set.IccExtend_of_mem _ _ hx
  obtain ⟨hr, hp, hs, hq, hpq⟩ := matrix_bounds a ha
  let r : ℝ := convergentMatrix a 0 0
  let p : ℝ := convergentMatrix a 0 1
  let s : ℝ := convergentMatrix a 1 0
  let q : ℝ := convergentMatrix a 1 1
  have hr' : 0 ≤ r := by
    dsimp [r]
    exact_mod_cast hr
  have hp' : 0 ≤ p := by
    dsimp [p]
    exact_mod_cast hp
  have hs' : 0 ≤ s := by
    dsimp [s]
    exact_mod_cast hs
  have hq' : 0 < q := by
    dsimp [q]
    exact_mod_cast hq
  have hpq' : p ≤ q := by
    dsimp [p, q]
    exact_mod_cast hpq
  have hpq_mem : p / q ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hp' hq'.le, (div_le_one hq').mpr hpq'⟩
  let D := fun n : ℕ => s + (n + 1) * q
  let E := fun n : ℕ => s + (n + 2) * q
  let H := fun n : ℕ => r + s + (n + 1) * (p + q)
  let u := fun n : ℕ => (r + (n + 1) * p) / D n
  let w := fun n : ℕ => q / D n
  let ε : ℝ := (-1) ^ (a.length + 1)
  let δ := fun n => ε / (D n * E n)
  let η := fun n => ε / (D n * H n)
  have hD (n : ℕ) : 0 < D n := by
    dsimp [D]
    positivity
  have hE (n : ℕ) : 0 < E n := by
    dsimp [E]
    positivity
  have hH (n : ℕ) : 0 < H n := by
    dsimp [H]
    positivity
  have hε : ε ≠ 0 := by simp [ε]
  have hu : Tendsto u atTop (𝓝 (p / q)) := affine_ratio_tendsto r s p q hq'.ne'
  have hw : Tendsto w atTop (𝓝 0) := by
    simpa [w, D] using affine_ratio_tendsto q s 0 q hq'.ne'
  have hDi : Tendsto (fun n => 1 / D n) atTop (𝓝 0) := by
    simpa [D] using affine_ratio_tendsto 1 s 0 q hq'.ne'
  have hEi : Tendsto (fun n => 1 / E n) atTop (𝓝 0) := by
    have hE_eq : E = fun n : ℕ => s + q + (n + 1) * q := by
      funext n
      dsimp [E]
      ring
    rw [hE_eq]
    simpa using affine_ratio_tendsto 1 (s + q) 0 q hq'.ne'
  have hHi : Tendsto (fun n => 1 / H n) atTop (𝓝 0) := by
    simpa [H] using affine_ratio_tendsto 1 (r + s) 0 (p + q) (by positivity)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa [δ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using (hDi.const_mul ε).mul hEi
  have hη : Tendsto η atTop (𝓝 0) := by
    simpa [η, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using (hDi.const_mul ε).mul hHi
  have hδ_ne (n : ℕ) : δ n ≠ 0 :=
    div_ne_zero hε (mul_ne_zero (hD n).ne' (hE n).ne')
  have hη_ne (n : ℕ) : η n ≠ 0 :=
    div_ne_zero hε (mul_ne_zero (hD n).ne' (hH n).ne')
  have hu_ne (n : ℕ) : u n ≠ u n + δ n := by
    intro h
    apply hδ_ne n
    linarith
  have hw_ne (n : ℕ) : w n ≠ w n + η n := by
    intro h
    apply hη_ne n
    linarith
  have hA : Tendsto (fun n => (∫ x in fundInterval (u n) (u n + δ n), g x) / |δ n|)
      atTop (𝓝 (g (p / q))) := by
    simpa only [add_sub_cancel_left] using
      average_tendsto g hg u (fun n => u n + δ n) (p / q) hu
        (by simpa using hu.add hδ) hu_ne
  have hB : Tendsto (fun n => (∫ x in fundInterval (w n) (w n + η n), g x) / |η n|)
      atTop (𝓝 (g 0)) := by
    simpa only [add_sub_cancel_left] using
      average_tendsto g hg w (fun n => w n + η n) 0 hw
        (by simpa using hw.add hη) hw_ne
  have hsym' (n : ℕ) :
      (∫ x in fundInterval (u n) (u n + δ n), g x) =
        ∫ x in fundInterval (w n) (w n + η n), g x := by
    obtain ⟨-, hleft, -, hright⟩ := cfCylinder_reverse_append_cons_ae_eq a ha (n + 1) (by omega)
    have hl : cfCylinder (a ++ [n + 1]) =ᵐ[volume] fundInterval (u n) (u n + δ n) := by
      simpa [u, δ, D, E, ε, r, p, s, q, Nat.cast_add, Nat.cast_one,
        add_assoc, one_add_one_eq_two] using hleft
    have hr : cfCylinder ((n + 1) :: a.reverse) =ᵐ[volume]
        fundInterval (w n) (w n + η n) := by
      simpa [w, η, D, H, ε, r, p, s, q, Nat.cast_add, Nat.cast_one] using hright
    rw [← cylinder_integral_eq f g (fun x hx => (hg_eq x hx).symm) _ _ _ hl,
      ← cylinder_integral_eq f g (fun x hx => (hg_eq x hx).symm) _ _ _ hr]
    exact hsym (n + 1) (by omega)
  have hwidth (n : ℕ) : |η n| / |δ n| = E n / H n := by
    simp only [δ, η, abs_div, abs_mul, abs_of_pos (hD n), abs_of_pos (hE n),
      abs_of_pos (hH n)]
    field_simp [(hD n).ne', (hE n).ne', (hH n).ne', abs_ne_zero.mpr hε]
  have hmean_eq (n : ℕ) :
      (∫ x in fundInterval (u n) (u n + δ n), g x) / |δ n| =
        ((∫ x in fundInterval (w n) (w n + η n), g x) / |η n|) * (E n / H n) := by
    rw [← hwidth n, ← hsym' n]
    field_simp [abs_ne_zero.mpr (hδ_ne n), abs_ne_zero.mpr (hη_ne n)]
  have hratio : Tendsto (fun n => E n / H n) atTop (𝓝 (q / (p + q))) := by
    have hE_eq : E = fun n : ℕ => s + q + (n + 1) * q := by
      funext n
      dsimp [E]
      ring
    rw [hE_eq]
    exact affine_ratio_tendsto (s + q) (r + s) q (p + q) (by positivity)
  have hlim := tendsto_nhds_unique hA ((hB.mul hratio).congr (fun n => (hmean_eq n).symm))
  rw [hg_eq (p / q) hpq_mem, hg_eq 0 (by norm_num)] at hlim
  change f (p / q) = f 0 / (1 + p / q)
  rw [hlim]
  field_simp
  ring

end MetaMathlibExt
