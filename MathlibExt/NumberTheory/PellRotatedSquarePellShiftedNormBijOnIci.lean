/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PellInverseClosedForm
public import MathlibExt.NumberTheory.PellShiftedIntercepts
public import MathlibExt.NumberTheory.PellShiftedQuadrants
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.IntermediateValue

/-!
# The shifted Pell norm beyond its last crossing

The shifted Pell norm is strictly increasing beyond its last crossing of the bound and maps
that closed ray bijectively onto the closed ray starting at the bound.

Statements from Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in
a Closed Rotated Square Region*, INTEGERS 25 (2025), Article A112.
-/

namespace MetaMathlibExt

private theorem pell_coordinates {D : ℤ} {w : Pell.Solution₁ D}
    (hw : Pell.IsFundamental w) :
    Continuous (pellU D w.x w.y) ∧ Continuous (pellV D w.x w.y) ∧
    MonotoneOn (pellU D w.x w.y) (Set.Ici 0) ∧
    StrictMonoOn (pellV D w.x w.y) (Set.Ici 0) ∧
    (∀ x : ℝ, (pellU D w.x w.y x) ^ 2 - D * (pellV D w.x w.y x) ^ 2 = 1) := by
  have hD : 0 < (D : ℝ) := by exact_mod_cast hw.d_pos
  let ε : ℝ := w.x + w.y * Real.sqrt D
  have hε : 1 < ε := by
    have hx : 1 < (w.x : ℝ) := by exact_mod_cast hw.1
    have hy : 0 ≤ (w.y : ℝ) := by exact_mod_cast hw.2.1.le
    exact lt_add_of_lt_of_nonneg hx (mul_nonneg hy (Real.sqrt_nonneg _))
  have hε₀ := zero_lt_one.trans hε
  have hconj : (w.x : ℝ) - w.y * Real.sqrt D = ε⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ hε₀.ne').mp
    change (_ - _) * (_ + _) = 1
    rw [mul_comm, ← sq_sub_sq, mul_pow, Real.sq_sqrt hD.le, mul_comm _ (D : ℝ)]
    exact_mod_cast w.prop
  have hU (x : ℝ) : pellU D w.x w.y x = (ε ^ x + (ε ^ x)⁻¹) / 2 := by
    simp only [pellU, hconj, Real.inv_rpow hε₀.le]
    rfl
  have hV (x : ℝ) : pellV D w.x w.y x =
      (ε ^ x - (ε ^ x)⁻¹) / (2 * Real.sqrt D) := by
    simp only [pellV, hconj, Real.inv_rpow hε₀.le]
    rfl
  have hc := Real.continuous_const_rpow hε₀.ne'
  have hci := Real.continuous_const_rpow (inv_ne_zero hε₀.ne')
  have hu : Continuous (pellU D w.x w.y) := by
    unfold pellU
    rw [hconj]
    exact (hc.add hci).div_const 2
  have hv : Continuous (pellV D w.x w.y) := by
    unfold pellV
    rw [hconj]
    exact (hc.sub hci).div_const _
  have hmu : MonotoneOn (pellU D w.x w.y) (Set.Ici 0) := by
    intro x hx y hy hxy
    let p := ε ^ x
    let q := ε ^ y
    have hp : 1 ≤ p := Real.one_le_rpow hε.le hx
    have hpq : p ≤ q := Real.rpow_le_rpow_of_exponent_le hε.le hxy
    have hq : 1 ≤ q := hp.trans hpq
    have hinv : p⁻¹ - q⁻¹ ≤ q - p := by
      calc
        p⁻¹ - q⁻¹ = (q - p) / (p * q) := by
          field_simp [(zero_lt_one.trans_le hp).ne', (zero_lt_one.trans_le hq).ne']
        _ ≤ q - p := div_le_self (sub_nonneg.mpr hpq)
          (one_le_mul_of_one_le_of_one_le hp hq)
    rw [hU, hU]
    change (p + p⁻¹) / 2 ≤ (q + q⁻¹) / 2
    linarith
  have hmv : StrictMonoOn (pellV D w.x w.y) (Set.Ici 0) := by
    intro x _ y _ hxy
    have hp := Real.rpow_pos_of_pos hε₀ x
    have hpq := Real.rpow_lt_rpow_of_exponent_lt hε hxy
    have hinv := inv_anti₀ hp hpq.le
    rw [hV, hV]
    apply (div_lt_div_iff_of_pos_right (by positivity : 0 < 2 * Real.sqrt D)).2
    linarith
  refine ⟨hu, hv, hmu, hmv, ?_⟩
  intro x
  rw [hU, hV]
  have hp := Real.rpow_pos_of_pos hε₀ x
  have hs := Real.sq_sqrt hD.le
  field_simp [(Real.sqrt_pos.mpr hD).ne', hp.ne']
  nlinarith

private theorem good_start (u v : ℝ → ℝ) (d A B K : ℝ)
    (hd : 1 ≤ d) (hu : Continuous u) (hv : Continuous v)
    (hmu : MonotoneOn u (Set.Ici 0)) (hmv : MonotoneOn v (Set.Ici 0))
    (hu₀ : u 0 = 1) (hv₀ : v 0 = 0)
    (hnorm : ∀ x, u x ^ 2 - d * v x ^ 2 = 1)
    (hevent : ∃ c, ∀ x, c ≤ x → 0 ≤ u x + A ∧ 0 ≤ v x + B)
    (hK₁ : |A| + |B| + 1 ≤ K) (hK₂ : |A| + Real.sqrt (1 + d * B ^ 2) ≤ K) :
    ∃ t, 0 ≤ t ∧ 0 ≤ u t + A ∧ 0 ≤ v t + B ∧ u t + v t + A + B ≤ K := by
  by_cases hzero : 0 ≤ u 0 + A ∧ 0 ≤ v 0 + B
  · refine ⟨0, le_rfl, hzero.1, hzero.2, ?_⟩
    rw [hu₀, hv₀]
    linarith [le_abs_self A, le_abs_self B]
  obtain ⟨c, hc⟩ := hevent
  let m (x : ℝ) := min (u x + A) (v x + B)
  have hm : Continuous m := (hu.add_const A).min (hv.add_const B)
  have hm₀ : m 0 ≤ 0 := by
    dsimp only [m]
    by_contra h
    exact hzero ⟨(lt_min_iff.mp (lt_of_not_ge h)).1.le,
      (lt_min_iff.mp (lt_of_not_ge h)).2.le⟩
  have hc₀ : 0 ≤ max 0 c := le_max_left _ _
  have hmc : 0 ≤ m (max 0 c) := le_min (hc _ (le_max_right _ _)).1
    (hc _ (le_max_right _ _)).2
  obtain ⟨t, ht, hmt⟩ := intermediate_value_Icc hc₀ hm.continuousOn ⟨hm₀, hmc⟩
  have htU : 0 ≤ u t + A := by rw [← hmt]; exact min_le_left _ _
  have htV : 0 ≤ v t + B := by rw [← hmt]; exact min_le_right _ _
  have hut : 1 ≤ u t := by simpa only [hu₀] using hmu (by simp) ht.1 ht.1
  have hvt : 0 ≤ v t := by simpa only [hv₀] using hmv (by simp) ht.1 ht.1
  refine ⟨t, ht.1, htU, htV, ?_⟩
  rcases le_total (u t + A) (v t + B) with h | h
  · have haxis : u t + A = 0 := by simpa only [m, min_eq_left h] using hmt
    have hvu : v t ≤ u t := by
      have hdsq := le_mul_of_one_le_left (sq_nonneg (v t)) hd
      nlinarith [hnorm t]
    linarith [neg_le_abs A, le_abs_self B]
  · have haxis : v t + B = 0 := by simpa only [m, min_eq_right h] using hmt
    have hueq : u t = Real.sqrt (1 + d * B ^ 2) := by
      rw [← Real.sqrt_sq (zero_le_one.trans hut)]
      congr 1
      have hvB : v t = -B := by linarith
      have hn := hnorm t
      rw [hvB, neg_sq] at hn
      linarith
    rw [hueq]
    linarith [le_abs_self A]

private theorem norm_tail (u v : ℝ → ℝ) (A B K : ℝ)
    (hmu : MonotoneOn u (Set.Ici 0)) (hmv : StrictMonoOn v (Set.Ici 0))
    (hbase : ∀ x, 0 ≤ x → 1 ≤ u x + v x)
    (hsurj : ∀ y, 1 ≤ y → ∃ x, 0 ≤ x ∧ u x + v x = y)
    (hstart : ∃ t, 0 ≤ t ∧ 0 ≤ u t + A ∧ 0 ≤ v t + B ∧ u t + v t + A + B ≤ K) :
    let f := fun x => |u x + A| + |v x + B|
    let r := sSup {x : ℝ | 0 ≤ x ∧ f x = K}
    (∀ x, r ≤ x → f x = u x + v x + A + B) ∧
    StrictMonoOn f (Set.Ici r) ∧ Set.BijOn f (Set.Ici r) (Set.Ici K) := by
  intro f r
  have hmono : StrictMonoOn (fun x => u x + v x) (Set.Ici 0) := hmu.add_strictMono hmv
  obtain ⟨t, ht, htU, htV, htK⟩ := hstart
  have htarget : 1 ≤ K - A - B := by linarith [hbase t ht]
  obtain ⟨z, hz, hsz⟩ := hsurj _ htarget
  have htz : t ≤ z := (hmono.le_iff_le ht hz).mp (by linarith)
  have hformula (x : ℝ) (htx : t ≤ x) : f x = u x + v x + A + B := by
    have hx := ht.trans htx
    have hux := hmu ht hx htx
    have hvx := hmv.monotoneOn ht hx htx
    dsimp only [f]
    rw [abs_of_nonneg (by linarith : 0 ≤ u x + A),
      abs_of_nonneg (by linarith : 0 ≤ v x + B)]
    ring
  have hfz : f z = K := by rw [hformula z htz]; linarith
  have hupper : ∀ x ∈ {x : ℝ | 0 ≤ x ∧ f x = K}, x ≤ z := by
    intro x hx
    by_contra h
    have hzx : z < x := lt_of_not_ge h
    have hlt := hmono hz hx.1 hzx
    have hfx := hformula x (htz.trans hzx.le)
    linarith [hx.2]
  have hrz : r = z := le_antisymm (csSup_le ⟨z, hz, hfz⟩ hupper)
    (le_csSup ⟨z, hupper⟩ ⟨hz, hfz⟩)
  have htail : StrictMonoOn f (Set.Ici z) := by
    intro x hx y hy hxy
    rw [hformula x (htz.trans hx), hformula y (htz.trans hy)]
    have hlt := hmono (hz.trans hx) (hz.trans hy) hxy
    dsimp only at hlt
    linarith
  rw [hrz]
  refine ⟨fun x hx => hformula x (htz.trans hx), htail, ?_⟩
  refine ⟨?_, htail.injOn, ?_⟩
  · intro x hx
    change K ≤ f x
    rw [← hfz]
    exact htail.monotoneOn le_rfl hx hx
  · intro y hy
    change K ≤ y at hy
    have hybase : 1 ≤ y - A - B := by linarith [hbase z hz]
    obtain ⟨x, hx, hsx⟩ := hsurj _ hybase
    have hzx : z ≤ x := (hmono.le_iff_le hz hx).mp (by linarith)
    refine ⟨x, hzx, ?_⟩
    rw [hformula x (htz.trans hzx)]
    linarith

private theorem signed_abs (k : ℤ) (hk : k = 1 ∨ k = -1) (x y : ℝ) :
    |k * x + y| = |x + k * y| := by
  rcases hk with rfl | rfl
  · simp
  · simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul]
    rw [← abs_neg (-x + y)]
    congr 1
    ring

@[expose] public section

/-- **The shifted Pell norm function is increasing past its last crossing of the bound.** Let $D$
be an integer, let $(\alpha, \beta)$ be the fundamental solution of the Pell equation
$X^2 - D Y^2 = 1$, put $\varepsilon = \alpha + \beta \sqrt{D}$ and
$\bar\varepsilon = \alpha - \beta \sqrt{D}$, and let
$u(x) = (\varepsilon^x + \bar\varepsilon^x) / 2$ and
$v(x) = (\varepsilon^x - \bar\varepsilon^x) / (2 \sqrt{D})$ for real $x$. Let $a$ and $b$ be
integers, let $i, j \in \{1, -1\}$, let $f_{i,j}(x) = |i u(x) + a| + |j v(x) + b|$, let
$K = |a| + \max(|b| + 1, \sqrt{1 + D b^2})$ and let $x_1 = \sup \{y \ge 0 : f_{i,j}(y) = K\}$.
Then $f_{i,j}(x) = u(x) + v(x) + i a + j b$ for every real $x \ge x_1$, the function $f_{i,j}$ is
strictly increasing on $[x_1, \infty)$, and $f_{i,j}$ maps $[x_1, \infty)$ bijectively onto
$[K, \infty)$.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Lemma 3.7
(`integers-2025-A112-lem-3-7`). -/
public theorem pellShiftedNorm_bijOn_Ici {D : ℤ} {w : Pell.Solution₁ D}
    (hw : Pell.IsFundamental w) (a b : ℤ) {i j : ℤ} (hi : i = 1 ∨ i = -1) (hj : j = 1 ∨ j = -1) :
    let x₁ : ℝ := sSup {y : ℝ | 0 ≤ y ∧
      pellShiftedNorm D w.x w.y a b i j y = pellShiftBound D a b}
    (∀ x, x₁ ≤ x →
      pellShiftedNorm D w.x w.y a b i j x = pellU D w.x w.y x + pellV D w.x w.y x + i * a + j * b) ∧
    StrictMonoOn (pellShiftedNorm D w.x w.y a b i j) (Set.Ici x₁) ∧
    Set.BijOn (pellShiftedNorm D w.x w.y a b i j) (Set.Ici x₁) (Set.Ici (pellShiftBound D a b))
    := by
  let u := pellU D w.x w.y
  let v := pellV D w.x w.y
  let A : ℝ := i * a
  let B : ℝ := j * b
  let K := pellShiftBound D a b
  obtain ⟨hu, hv, hmu, hmv, hnorm⟩ := pell_coordinates hw
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast (Int.add_one_le_iff.mpr hw.d_pos)
  have hA : |A| = |(a : ℝ)| := by rcases hi with h | h <;> simp [A, h]
  have hB : |B| = |(b : ℝ)| := by rcases hj with h | h <;> simp [B, h]
  have hBs : B ^ 2 = (b : ℝ) ^ 2 := by rw [← sq_abs B, hB, sq_abs]
  have hK₁ : |A| + |B| + 1 ≤ K := by
    dsimp only [K, pellShiftBound]
    rw [hA, hB]
    linarith [le_max_left (|(b : ℝ)| + 1) (Real.sqrt (1 + D * (b : ℝ) ^ 2))]
  have hK₂ : |A| + Real.sqrt (1 + D * B ^ 2) ≤ K := by
    dsimp only [K, pellShiftBound]
    rw [hA, hBs]
    linarith [le_max_right (|(b : ℝ)| + 1) (Real.sqrt (1 + D * (b : ℝ) ^ 2))]
  have hevent : ∃ c : ℝ, ∀ x : ℝ, c ≤ x → 0 ≤ u x + A ∧ 0 ≤ v x + B := by
    exact (Filter.eventually_atTop (p := fun x : ℝ => 0 ≤ u x + A ∧ 0 ≤ v x + B)).mp
      ((pell_shifted_real_solutions_eventually_in_quadrants hw (i * a) (j * b)).mono
        (fun x hx => by simpa only [Int.cast_mul] using hx.1))
  have hstart := good_start u v D A B K hD hu hv hmu hmv.monotoneOn
    (pellU_zero D w.x w.y) (pellV_zero D w.x w.y) hnorm hevent hK₁ hK₂
  have hbase (x : ℝ) (hx : 0 ≤ x) : 1 ≤ u x + v x := by
    simpa only [pellU_zero, pellV_zero, add_zero] using
      add_le_add (hmu (by simp) hx hx) (hmv.monotoneOn (by simp) hx hx)
  have hsurj (y : ℝ) (hy : 1 ≤ y) : ∃ x, 0 ≤ x ∧ u x + v x = y := by
    obtain ⟨hx, hxy⟩ := pell_inverse_closed_form hw hy
    exact ⟨_, hx, hxy⟩
  have hf (x : ℝ) : pellShiftedNorm D w.x w.y a b i j x = |u x + A| + |v x + B| := by
    exact congrArg₂ (· + ·) (signed_abs i hi (u x) a) (signed_abs j hj (v x) b)
  have hf' : pellShiftedNorm D w.x w.y a b i j =
      (fun x => |u x + A| + |v x + B|) := funext hf
  simpa only [hf'] using norm_tail u v A B K hmu hmv hbase hsurj hstart

end

end MetaMathlibExt
