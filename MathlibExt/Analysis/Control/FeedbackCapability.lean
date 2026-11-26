/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The sharp uncertainty bound for feedback stabilisation

We prove the impossibility half of Guo's Theorem 4.1 (*Exploring the capability and limits of
the feedback mechanism*, arXiv:math/0305011v1). The proof below constructs a zero-noise
trajectory by assigning the plant at each new output. The interval of outputs grows by a
factor of at least `1 + √2 / 2` each time, and the assignments extend to a globally
`(3/2 + √2)`-Lipschitz plant.
-/

open Set MeasureTheory

namespace MathlibExt.Analysis.Control.FeedbackCapabilityWanted

/-- A prefix with outputs through time `n + 1` and plant values assigned through time `n`.
The endpoint indices describe the interval before the last output was added. -/
private structure Prefix (K ρ : ℝ) (h : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ) (n : ℕ) where
  y : ℕ → ℝ
  plant : ℕ → ℝ
  lo : ℕ
  hi : ℕ
  lo_le : lo ≤ n
  hi_le : hi ≤ n
  between : ∀ i ≤ n, y lo ≤ y i ∧ y i ≤ y hi
  fresh : y (n + 1) < y lo ∨ y hi < y (n + 1)
  ratio : ρ * (y hi - y lo) ≤ max (y hi) (y (n + 1)) - min (y lo) (y (n + 1))
  growth : ρ ^ n ≤ max (y hi) (y (n + 1)) - min (y lo) (y (n + 1))
  lip : ∀ i ≤ n, ∀ j ≤ n, |plant i - plant j| ≤ K * |y i - y j|
  recurrence : ∀ i ≤ n, y (i + 1) = plant i + h i (fun j => y j)

private def start (K ρ : ℝ) (h : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ) (y₀ : ℝ) :
    Prefix K ρ h 0 where
  y i := if i = 0 then y₀ else y₀ + 1
  plant _ := y₀ + 1 - h 0 (fun _ => y₀)
  lo := 0
  hi := 0
  lo_le := le_rfl
  hi_le := le_rfl
  between := by simp
  fresh := by simp
  ratio := by simp
  growth := by simp
  lip := by simp
  recurrence := by
    intro i hi
    have : i = 0 := Nat.eq_zero_of_le_zero hi
    subst i
    have hist : (fun j : Fin (0 + 1) => if (j : ℕ) = 0 then y₀ else y₀ + 1) =
        fun _ => y₀ := by
      funext j
      simp
    change _ = y₀ + 1 - h 0 (fun _ => y₀) +
      h 0 (fun j => if (j : ℕ) = 0 then y₀ else y₀ + 1)
    rw [hist]
    simp

-- The nearest old endpoint lies between the new output and every old output.
private theorem Prefix.endpoints {K ρ : ℝ} {h : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ}
    {n : ℕ} (p : Prefix K ρ h n) :
    ∃ a b e : ℕ, a ≤ n + 1 ∧ b ≤ n + 1 ∧ e ≤ n ∧
      p.y a = min (p.y p.lo) (p.y (n + 1)) ∧ p.y b = max (p.y p.hi) (p.y (n + 1)) ∧
      p.y b - p.y a = p.y p.hi - p.y p.lo + |p.y (n + 1) - p.y e| ∧
      ∀ i ≤ n, |p.y (n + 1) - p.y i| = |p.y (n + 1) - p.y e| + |p.y e - p.y i| := by
  have hab := (p.between p.lo p.lo_le).2
  rcases p.fresh with hx | hx
  · refine ⟨n + 1, p.hi, p.lo, le_rfl, p.hi_le.trans (Nat.le_succ n), p.lo_le, ?_, ?_, ?_, ?_⟩
    · exact (min_eq_right hx.le).symm
    · exact (max_eq_left (hx.le.trans hab)).symm
    · rw [abs_of_nonpos (sub_nonpos.mpr hx.le)]
      ring
    · intro i hi
      have hai := (p.between i hi).1
      rw [abs_of_nonpos (sub_nonpos.mpr (hx.le.trans hai)),
        abs_of_nonpos (sub_nonpos.mpr hx.le), abs_of_nonpos (sub_nonpos.mpr hai)]
      ring
  · refine ⟨p.lo, n + 1, p.hi, p.lo_le.trans (Nat.le_succ n), le_rfl, p.hi_le, ?_, ?_, ?_, ?_⟩
    · exact (min_eq_left (hab.trans hx.le)).symm
    · exact (max_eq_right hx.le).symm
    · rw [abs_of_nonneg (sub_nonneg.mpr hx.le)]
      ring
    · intro i hi
      have hib := (p.between i hi).2
      rw [abs_of_nonneg (sub_nonneg.mpr (hib.trans hx.le)),
        abs_of_nonneg (sub_nonneg.mpr hx.le), abs_of_nonneg (sub_nonneg.mpr hib)]
      ring

-- Assign the plant on the side of the midpoint that makes the next excursion larger.
private theorem choose_plant {ρ a b v u r : ℝ} (hρ : 1 < ρ) (hw : 0 < b - a)
    (hr : (ρ - 1) * (b - a) + (b - a) / 2 ≤ r) :
    ∃ q : ℝ, |q - v| = r ∧ (q + u < a ∨ b < q + u) ∧
      ρ * (b - a) ≤ max b (q + u) - min a (q + u) := by
  have hg := mul_pos (sub_pos.mpr hρ) hw
  have hr₀ : 0 ≤ r := by linarith only [hg, hw, hr]
  by_cases hc : v + u ≤ (a + b) / 2
  · have hx : v - r + u < a := by linarith only [hc, hr, hg]
    refine ⟨v - r, ?_, Or.inl hx, ?_⟩
    · rw [show v - r - v = -r by ring, abs_neg, abs_of_nonneg hr₀]
    · rw [min_eq_right hx.le, max_eq_left (by linarith only [hx, hw])]
      linarith only [hc, hr]
  · have hx : b < v + r + u := by linarith only [le_of_not_ge hc, hr, hg]
    refine ⟨v + r, ?_, Or.inr hx, ?_⟩
    · rw [show v + r - v = r by ring, abs_of_nonneg hr₀]
    · rw [max_eq_right hx.le, min_eq_left (by linarith only [hx, hw])]
      linarith only [le_of_not_ge hc, hr]

private theorem Prefix.advance {K ρ : ℝ} {h : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ}
    {n : ℕ} (p : Prefix K ρ h n) (hρ : 1 < ρ) (hK : ρ ^ 2 = K) (hbal : K + 1 / 2 = 2 * ρ) :
    ∃ s : Prefix K ρ h (n + 1),
      (∀ i ≤ n + 1, s.y i = p.y i) ∧ (∀ i ≤ n, s.plant i = p.plant i) := by
  obtain ⟨a, b, e, ha, hb, he, hamin, hbmax, hwidth, hdist⟩ := p.endpoints
  -- At the critical constant, the previous width is still small enough to leave
  -- a radius of at least `(ρ - 1) * width + width / 2` for the new output.
  have hw : ρ ^ n ≤ p.y b - p.y a := by simpa only [hamin, hbmax] using p.growth
  have hr : (ρ - 1) * (p.y b - p.y a) + (p.y b - p.y a) / 2 ≤
      K * |p.y (n + 1) - p.y e| := by
    have hratio : ρ * (p.y p.hi - p.y p.lo) ≤ p.y b - p.y a := by
      simpa only [hamin, hbmax] using p.ratio
    have hm := mul_le_mul_of_nonneg_left hratio (show 0 ≤ ρ by linarith only [hρ])
    rw [← mul_assoc, ← pow_two, hK] at hm
    calc
      _ = (K - ρ) * (p.y b - p.y a) := by
        rw [show K - ρ = ρ - 1 / 2 by linarith only [hbal]]
        ring
      _ ≤ K * (p.y b - p.y a - (p.y p.hi - p.y p.lo)) := by linarith only [hm]
      _ = _ := by rw [hwidth]; ring
  let u := h (n + 1) (fun j => p.y j)
  have hρ₀ : 0 < ρ := by linarith only [hρ]
  obtain ⟨q, hq, hfresh, hgrow⟩ := choose_plant (v := p.plant e) (u := u) hρ
    ((pow_pos hρ₀ n).trans_le hw) hr
  let y' := Function.update p.y (n + 2) (q + u)
  let plant' := Function.update p.plant (n + 1) q
  have hy' (i : ℕ) (hi : i ≤ n + 1) : y' i = p.y i :=
    Function.update_of_ne (by omega) _ _
  have hp' (i : ℕ) (hi : i ≤ n) : plant' i = p.plant i :=
    Function.update_of_ne (by omega) _ _
  have hy'_last : y' (n + 1 + 1) = q + u := by simp [y']
  have hp'_last : plant' (n + 1) = q := by simp [plant']
  have hhist (i : ℕ) (hi : i ≤ n + 1) : (fun j : Fin (i + 1) => y' j) =
      (fun j : Fin (i + 1) => p.y j) := by
    funext j
    exact hy' j (by have := j.isLt; omega)
  have hnew (i : ℕ) (hi : i ≤ n) :
      |plant' (n + 1) - plant' i| ≤ K * |y' (n + 1) - y' i| := by
    rw [hp'_last, hp' i hi, hy' _ le_rfl, hy' i (hi.trans (Nat.le_succ n)), hdist i hi]
    calc
      |q - p.plant i| ≤ |q - p.plant e| + |p.plant e - p.plant i| := by
        simpa only [sub_add_sub_cancel] using abs_add_le (q - p.plant e) (p.plant e - p.plant i)
      _ ≤ K * |p.y (n + 1) - p.y e| + K * |p.y e - p.y i| := by
        rw [hq]
        exact add_le_add le_rfl (p.lip e he i hi)
      _ = _ := by rw [mul_add]
  refine ⟨⟨y', plant', a, b, ha, hb, ?_, ?_, ?_, ?_, ?_, ?_⟩, hy', hp'⟩
  · intro i hi
    rw [hy' a ha, hy' b hb, hy' i hi, hamin, hbmax]
    rcases eq_or_lt_of_le hi with rfl | hi
    · exact ⟨min_le_right .., le_max_right ..⟩
    · exact ⟨(min_le_left ..).trans (p.between i (by omega)).1,
        (p.between i (by omega)).2.trans (le_max_left ..)⟩
  · simpa only [hy' a ha, hy' b hb, hy'_last] using hfresh
  · simpa only [hy' a ha, hy' b hb, hy'_last] using hgrow
  · rw [hy' a ha, hy' b hb, hy'_last, pow_succ, mul_comm (ρ ^ n)]
    exact (mul_le_mul_of_nonneg_left hw hρ₀.le).trans hgrow
  · intro i hi j hj
    rcases eq_or_lt_of_le hi with rfl | hi <;> rcases eq_or_lt_of_le hj with rfl | hj
    · simp
    · exact hnew j (by omega)
    · rw [abs_sub_comm (plant' i), abs_sub_comm (y' i)]
      exact hnew i (by omega)
    · rw [hp' i (by omega), hp' j (by omega), hy' i (by omega), hy' j (by omega)]
      exact p.lip i (by omega) j (by omega)
  · intro i hi
    rw [hhist i hi]
    rcases eq_or_lt_of_le hi with rfl | hi
    · rw [hy'_last, hp'_last]
    · rw [hy' _ (by omega), hp' i (by omega)]
      exact p.recurrence i (by omega)

private theorem prefix_agrees (F : ℕ → ℕ → ℝ) {c : ℕ → ℕ} (hc : Monotone c)
    (hstep : ∀ n i, i ≤ c n → F (n + 1) i = F n i) {m n i : ℕ} (hmn : m ≤ n) (hi : i ≤ c m) :
    F n i = F m i := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih => exact (hstep n i (hi.trans (hc hmn))).trans ih

-- Assemble the consistent prefixes, then extend the assigned plant off the visited set.
private theorem exists_lipschitz_trajectory (K : NNReal) {ρ : ℝ} (hρ : 1 < ρ)
    (hK : ρ ^ 2 = K) (hbal : (K : ℝ) + 1 / 2 = 2 * ρ)
    (h : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ) (y₀ : ℝ) :
    ∃ f : ℝ → ℝ, LipschitzWith K f ∧
      ∃ y : ℕ → ℝ, y 0 = y₀ ∧ (∀ t, y (t + 1) = f (y t) + h t (fun i => y i)) ∧
        ¬ BddAbove (range fun t => |y t|) := by
  classical
  let p : (n : ℕ) → Prefix K ρ h n := fun n =>
    Nat.rec (start K ρ h y₀) (fun _ s => (s.advance hρ hK hbal).choose) n
  let y : ℕ → ℝ := fun i => (p i).y i
  let g : ℕ → ℝ := fun i => (p i).plant i
  have hy {i n : ℕ} (hi : i ≤ n) : (p n).y i = y i :=
    prefix_agrees (fun n => (p n).y) (c := fun n => n + 1) (fun _ _ hmn => Nat.succ_le_succ hmn)
      (fun n => ((p n).advance hρ hK hbal).choose_spec.1) hi (Nat.le_succ i)
  have hg {i n : ℕ} (hi : i ≤ n) : (p n).plant i = g i :=
    prefix_agrees (fun n => (p n).plant) (c := id) monotone_id
      (fun n => ((p n).advance hρ hK hbal).choose_spec.2) hi le_rfl
  have hlip (i j : ℕ) : |g i - g j| ≤ K * |y i - y j| := by
    have hi := le_max_left i j
    have hj := le_max_right i j
    simpa only [hg hi, hg hj, hy hi, hy hj] using (p (max i j)).lip i hi j hj
  let plant : ℝ → ℝ := fun x => if hx : x ∈ range y then g hx.choose else 0
  have hplant (i : ℕ) : plant (y i) = g i := by
    have hi : y i ∈ range y := mem_range_self i
    rw [show plant (y i) = g hi.choose by simp only [plant, dite_eq_left hi]]
    have hle := hlip hi.choose i
    rw [show y hi.choose = y i from hi.choose_spec, sub_self, abs_zero, mul_zero] at hle
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hle)
  have hpartial : LipschitzOnWith K plant (range y) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    simpa only [Real.dist_eq, hplant] using hlip i j
  obtain ⟨f, hf, hagree⟩ := hpartial.extend_real
  refine ⟨f, hf, y, rfl, ?_, ?_⟩
  · intro t
    have hist : (fun i : Fin (t + 1) => (p (t + 1)).y i) =
        (fun i : Fin (t + 1) => y i) := by
      funext i
      exact hy (by have := i.isLt; omega)
    have ht := (p (t + 1)).recurrence t (Nat.le_succ t)
    rw [hy le_rfl, hg (Nat.le_succ t), hist] at ht
    rw [← hagree (mem_range_self t), hplant]
    exact ht
  · rintro ⟨B, hB⟩
    have hbound (n i : ℕ) (hi : i ≤ n + 1) : -B ≤ (p n).y i ∧ (p n).y i ≤ B := by
      have habs (i : ℕ) : |y i| ≤ B := hB (mem_range_self i)
      rcases eq_or_lt_of_le hi with rfl | hi
      · have hlast : (p n).y (n + 1) = y (n + 1) := by
          exact (((p n).advance hρ hK hbal).choose_spec.1 _ le_rfl).symm
        rw [hlast]
        exact abs_le.mp (habs _)
      · rw [hy (by omega)]
        exact abs_le.mp (habs _)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * B) hρ
    have hlow := le_min (hbound n _ ((p n).lo_le.trans (Nat.le_succ n))).1 (hbound n _ le_rfl).1
    have hupp := max_le (hbound n _ ((p n).hi_le.trans (Nat.le_succ n))).2 (hbound n _ le_rfl).2
    linarith only [hn, (p n).growth, hlow, hupp]

/-- **No feedback stabilises every system with uncertainty at least `3/2 + √2`** (Xie and Guo,
IEEE Trans. Automat. Control 45 (2000); stated as Guo, Proc. ICM 2002, arXiv:math/0305011v1,
Theorem 4.1(ii)). Let `L ≥ 3/2 + √2` and `W > 0`. For every feedback law
`u_t = h_t(y_0, …, y_t)` with each `h_t` Lebesgue measurable, as in the source (so in
particular every Borel measurable law), and every initial value `y_0`, there are `f : ℝ → ℝ`
with generalized Lipschitz quasi-norm `‖f‖ ≤ L` and a noise sequence with `|w_t| ≤ W` such that
the closed loop `y_{t+1} = f(y_t) + u_t + w_{t+1}` is unbounded: `sup_t |y_t| = ∞`.
The proof uses zero noise and does not need the feedback law's measurability. -/
public theorem exists_unbounded_of_le (L : ℝ) (hL : 3 / 2 + √2 ≤ L) (W : ℝ) (hW : 0 < W)
    (h : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ) (_hh : ∀ t, NullMeasurable (h t) volume) (y₀ : ℝ) :
    ∃ f : ℝ → ℝ, (∀ L' > L, ∃ a : ℝ, ∀ x x', |f x - f x'| ≤ L' * (|x - x'| + a)) ∧
      ∃ w : ℕ → ℝ, (∀ t, |w t| ≤ W) ∧
      ∃ y u : ℕ → ℝ, y 0 = y₀ ∧ (∀ t, u t = h t (fun i => y i)) ∧
        (∀ t, y (t + 1) = f (y t) + u t + w (t + 1)) ∧
        ¬ BddAbove (range fun t => |y t|) := by
  let ρ : ℝ := 1 + √2 / 2
  let K : NNReal := ⟨3 / 2 + √2, by positivity⟩
  have hρ : 1 < ρ := by
    dsimp [ρ]
    have hpos : 0 < √(2 : ℝ) := by positivity
    linarith only [hpos]
  have hK : ρ ^ 2 = K := by
    change (1 + √2 / 2) ^ 2 = 3 / 2 + √2
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
  have hbal : (K : ℝ) + 1 / 2 = 2 * ρ := by
    change 3 / 2 + √2 + 1 / 2 = 2 * (1 + √2 / 2)
    ring
  obtain ⟨f, hf, y, hy₀, hy, hunbounded⟩ := exists_lipschitz_trajectory K hρ hK hbal h y₀
  refine ⟨f, ?_, fun _ => 0, ?_, y, fun t => h t (fun i => y i), hy₀, fun _ => rfl, ?_, hunbounded⟩
  · intro L' hL'
    refine ⟨0, fun x x' => ?_⟩
    rw [add_zero]
    have hdist : |f x - f x'| ≤ K * |x - x'| := by
      simpa only [Real.dist_eq] using hf.dist_le_mul x x'
    exact hdist.trans (mul_le_mul_of_nonneg_right (hL.trans hL'.le) (abs_nonneg _))
  · intro t
    simpa only [abs_zero] using hW.le
  · intro t
    simpa only [add_zero] using hy t

end MathlibExt.Analysis.Control.FeedbackCapabilityWanted
