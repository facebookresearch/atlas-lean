/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LurothConvergent
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lower bound for large Lüroth digit values

The integral over a superlevel set is bounded by the measure of the corresponding Lüroth
digit event under positivity and the floor comparison condition.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 7.
-/

open MeasureTheory Set
open scoped ENNReal Function

namespace MetaMathlibExt

private theorem measurable_digit : Measurable lurothDigit := by
  unfold lurothDigit
  fun_prop

private theorem measurable_map : Measurable lurothMap := by
  unfold lurothMap
  have hd : Measurable fun x => (lurothDigit x : ℝ) :=
    (measurable_of_countable ((↑) : ℕ → ℝ)).comp measurable_digit
  fun_prop

private theorem measurable_seq (n : ℕ) : Measurable fun x => lurothDigitSeq x n :=
  measurable_digit.comp (measurable_map.iterate n)

private def slope (n : ℕ) : ℝ := (n + 2) * (n + 1)

private def affine (n : ℕ) (x : ℝ) : ℝ := slope n * x - (n + 1)

private theorem branch_iff (n : ℕ) (x : ℝ) :
    affine n x ∈ Set.Ioc (0 : ℝ) 1 ↔ x ∈ Set.Ioc (0 : ℝ) 1 ∧ lurothDigit x = n + 2 := by
  let q : ℝ := n + 1
  have hq : 1 ≤ q := by simp [q]
  have hpos : 0 < q := by linarith
  have hsucc : 0 < q + 1 := by positivity
  have hlo : 0 < affine n x ↔ 1 < (q + 1) * x := by
    have : affine n x = q * ((q + 1) * x - 1) := by unfold affine slope q; ring
    rw [this, mul_pos_iff_of_pos_left hpos, sub_pos]
  have hhi : affine n x ≤ 1 ↔ q * x ≤ 1 := by
    have : affine n x - 1 = (q + 1) * (q * x - 1) := by unfold affine slope q; ring
    rw [← sub_nonpos, this, ← mul_zero (q + 1), mul_le_mul_iff_right₀ hsucc, sub_nonpos]
  rw [Set.mem_Ioc, hlo, hhi]
  have hd (hx : 0 < x) : lurothDigit x = n + 2 ↔ q * x ≤ 1 ∧ 1 < (q + 1) * x := by
    simp only [lurothDigit, Nat.succ.injEq, Nat.floor_eq_iff (by positivity : 0 ≤ 1 / x),
      Nat.cast_add, Nat.cast_one, le_div_iff₀ hx, div_lt_iff₀ hx, q]
  constructor
  · rintro ⟨hl, hu⟩
    have hx : 0 < x := pos_of_mul_pos_right (by linarith : 0 < (q + 1) * x) hsucc.le
    exact ⟨⟨hx, le_trans (le_mul_of_one_le_left hx.le hq) hu⟩, (hd hx).2 ⟨hu, hl⟩⟩
  · rintro ⟨hx, h⟩
    exact ((hd hx.1).1 h).symm

private theorem affine_eq_map {n : ℕ} {x : ℝ} (h : lurothDigit x = n + 2) :
    affine n x = lurothMap x := by
  simp [affine, slope, lurothMap, h]
  ring

private theorem volume_affine (n : ℕ) (t : Set ℝ) :
    volume (affine n ⁻¹' t) = ENNReal.ofReal (slope n)⁻¹ * volume t := by
  have hp : 0 < slope n := by unfold slope; positivity
  change volume ((slope n * ·) ⁻¹' ((· + -((n : ℝ) + 1)) ⁻¹' t)) = _
  rw [Real.volume_preimage_mul_left hp.ne', abs_of_pos (inv_pos.mpr hp),
    measure_preimage_add_right]

private noncomputable def cylinder {m : ℕ} (d : Fin m → ℕ) : Set ℝ :=
  {x ∈ Set.Ioc (0 : ℝ) 1 | ∀ i : Fin m, lurothDigitSeq x i = d i}

private theorem measurable_cylinder {m : ℕ} (d : Fin m → ℕ) :
    MeasurableSet (cylinder d) := by
  have heq : cylinder d = Ioc (0 : ℝ) 1 ∩
      ⋂ i : Fin m, (fun x => lurothDigitSeq x i) ⁻¹' {d i} := by
    ext x
    simp [cylinder]
  rw [heq]
  exact measurableSet_Ioc.inter
    (.iInter fun i => (measurable_seq i) (measurableSet_singleton (d i)))

private theorem volume_cylinder {m : ℕ} (d : Fin m → ℕ) (hd : ∀ i, 2 ≤ d i) :
    volume (cylinder d) = ∏ i, ENNReal.ofReal (1 / ((d i : ℝ) * ((d i : ℝ) - 1))) := by
  induction m with
  | zero =>
    have heq : cylinder d = Ioc (0 : ℝ) 1 := by ext x; simp [cylinder]
    rw [heq]
    simp
  | succ m ih =>
    let n := d 0 - 2
    have hn : d 0 = n + 2 := (Nat.sub_add_cancel (hd 0)).symm
    let t := cylinder (fun i : Fin m => d i.succ)
    have heq : cylinder d = affine n ⁻¹' t := by
      ext x
      simp only [cylinder, t, mem_ofPred_eq, mem_preimage]
      rw [branch_iff]
      constructor
      · rintro ⟨hx, h⟩
        have he : lurothDigit x = n + 2 := by simpa [lurothDigitSeq, hn] using h 0
        refine ⟨⟨hx, he⟩, fun i => ?_⟩
        rw [affine_eq_map he]
        simpa [lurothDigitSeq, Function.iterate_succ_apply] using h i.succ
      · rintro ⟨⟨hx, he⟩, ht⟩
        refine ⟨hx, Fin.forall_fin_succ.2 ⟨?_, ?_⟩⟩
        · simpa [lurothDigitSeq, hn] using he
        · intro i
          simpa [lurothDigitSeq, Function.iterate_succ_apply, ← affine_eq_map he] using ht i
    rw [heq, volume_affine, ih _ (fun i => hd i.succ), Fin.prod_univ_succ]
    congr 1
    have hs : slope n = (d 0 : ℝ) * ((d 0 : ℝ) - 1) := by
      simp only [slope, hn, Nat.cast_add, Nat.cast_ofNat]
      ring
    rw [hs, one_div, ENNReal.ofReal_inv_of_pos (by
      rw [← hs]
      unfold slope
      positivity)]

private def floorBox {m : ℕ} (d : Fin m → ℕ) : Set (Fin m → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ico (d i : ℝ) ((d i : ℝ) + 1))

private theorem integral_floorBox {m : ℕ} (d : Fin m → ℕ) (hd : ∀ i, 2 ≤ d i) :
    (∫⁻ x in floorBox d, ENNReal.ofReal (∏ i, 1 / x i ^ 2)) ≤
      ∏ i, ENNReal.ofReal (1 / ((d i : ℝ) * ((d i : ℝ) - 1))) := by
  have hp (i : Fin m) : 0 < (d i : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (hd i))
  have hw (i : Fin m) : 0 ≤ 1 / ((d i : ℝ) * ((d i : ℝ) - 1)) := by
    have : (2 : ℝ) ≤ d i := by exact_mod_cast hd i
    exact one_div_nonneg.2 (mul_nonneg (hp i).le (by linarith))
  calc
    _ ≤ ∫⁻ _ in floorBox d, ENNReal.ofReal
        (∏ i, 1 / ((d i : ℝ) * ((d i : ℝ) - 1))) := by
      apply setLIntegral_mono measurable_const
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      apply Finset.prod_le_prod₀
      · intro i _
        positivity
      · intro i _
        have hxi : (d i : ℝ) ≤ x i := (hx i (mem_univ i)).1
        have hxpos : 0 < x i := (hp i).trans_le hxi
        apply one_div_le_one_div_of_le
        · have : (2 : ℝ) ≤ d i := by exact_mod_cast hd i
          exact mul_pos (hp i) (by linarith)
        · nlinarith [sq_nonneg (x i - (d i : ℝ))]
    _ = _ := by
      rw [setLIntegral_const]
      simp only [floorBox, Real.volume_pi_Ico, add_sub_cancel_left, ENNReal.ofReal_one,
        Finset.prod_const_one, mul_one]
      exact ENNReal.ofReal_prod_of_nonneg (fun i _ => hw i)

/-- **Lower bound for the measure of large Lüroth digit values.** Let $m$ be a natural number,
let $D = [2, \infty)^m$, let $F : \mathbb{R}^m \to \mathbb{R}$ satisfy $F(x) > 0$ for every
$x \in D$, and let $M$ be a real number with
$F(x) \le M\,F(\lfloor x_1 \rfloor, \ldots, \lfloor x_m \rfloor)$ for every $x \in D$ (the
paper's condition (6)). Put
$G(y) = \int_{\{x \in D \,:\, F(x) \ge y\}} \prod_{i=1}^m x_i^{-2}\,dx$ for real $y$, let
$\lambda$ be Lebesgue measure on $\mathbb{R}$ and let $d_1(x), d_2(x), \ldots$ be the Lüroth
digits of $x$. Then for every real $y$,
$$G(My) \le \lambda\{x \in (0, 1] : F(d_1(x), \ldots, d_m(x)) \ge y\}.$$

The paper states it only at the values of the sequence in its Theorem 4, under that theorem's
hypotheses, which also require $F$ to be measurable and non-decreasing; only positivity and
condition (6) are assumed here.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 7
(`integers-2024-A67-thm-7`). -/
public theorem le_volume_lurothDigits_ge {m : ℕ} (F : (Fin m → ℝ) → ℝ)
    (hpos : ∀ x : Fin m → ℝ, (∀ i, 2 ≤ x i) → 0 < F x) (M : ℝ)
    (hM : ∀ x : Fin m → ℝ, (∀ i, 2 ≤ x i) → F x ≤ M * F (fun i => (⌊x i⌋₊ : ℝ))) (y : ℝ) :
    (∫⁻ x in {x : Fin m → ℝ | (∀ i, 2 ≤ x i) ∧ M * y ≤ F x},
        ENNReal.ofReal (∏ i, 1 / x i ^ 2)) ≤
      volume {x ∈ Set.Ioc (0 : ℝ) 1 | y ≤ F (fun i => (lurothDigitSeq x i : ℝ))} := by
  classical
  have hMpos : 0 < M := by
    have hp := hpos (fun _ => 2) (fun _ => le_rfl)
    have h := hM (fun _ => 2) (fun _ => le_rfl)
    simp only [Nat.floor_ofNat, Nat.cast_ofNat] at h
    nlinarith
  let A : Set (Fin m → ℕ) := {d | (∀ i, 2 ≤ d i) ∧ y ≤ F (fun i => (d i : ℝ))}
  have hcover : {x : Fin m → ℝ | (∀ i, 2 ≤ x i) ∧ M * y ≤ F x} ⊆
      ⋃ d : A, floorBox d.val := by
    rintro x ⟨hx, hy⟩
    let d : Fin m → ℕ := fun i => ⌊x i⌋₊
    have hd : ∀ i, 2 ≤ d i := fun i => (Nat.le_floor_iff (by linarith [hx i])).2 (hx i)
    have hdy : y ≤ F (fun i => (d i : ℝ)) :=
      (mul_le_mul_iff_right₀ hMpos).1 (hy.trans (hM x hx))
    apply mem_iUnion.2
    refine ⟨⟨d, hd, hdy⟩, ?_⟩
    intro i _
    exact ⟨Nat.floor_le (by linarith [hx i]), Nat.lt_floor_add_one (x i)⟩
  have hdisj : Pairwise (Disjoint on fun d : A => cylinder d.val) := by
    intro d e hne
    apply disjoint_left.2
    rintro x ⟨_, hd⟩ ⟨_, he⟩
    exact hne (Subtype.ext (funext fun i => (hd i).symm.trans (he i)))
  calc
    _ ≤ ∫⁻ x in ⋃ d : A, floorBox d.val, ENNReal.ofReal (∏ i, 1 / x i ^ 2) :=
      lintegral_mono_set hcover
    _ ≤ ∑' d : A, ∫⁻ x in floorBox d.val, ENNReal.ofReal (∏ i, 1 / x i ^ 2) :=
      lintegral_iUnion_le _ _
    _ ≤ ∑' d : A, ∏ i, ENNReal.ofReal (1 / ((d.val i : ℝ) * ((d.val i : ℝ) - 1))) :=
      tsum_le_tsum fun d => integral_floorBox d.val d.property.1
    _ = volume (⋃ d : A, cylinder d.val) := by
      rw [measure_iUnion hdisj (fun d => measurable_cylinder d.val)]
      exact tsum_congr fun d => (volume_cylinder d.val d.property.1).symm
    _ ≤ _ := by
      apply measure_mono
      rintro x hx
      obtain ⟨d, hdx⟩ := mem_iUnion.1 hx
      refine ⟨hdx.1, ?_⟩
      simpa only [hdx.2] using d.property.2

end MetaMathlibExt
