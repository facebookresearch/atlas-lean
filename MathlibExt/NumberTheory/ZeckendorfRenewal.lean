/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ZeckendorfOdometer
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Probability.ConditionalProbability
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.LinearCombination

/-!
# Renewal of the Zeckendorf odometer's invariant measure

The theorem `zeckOdometer_invariant_measure_renewal` proves Hosten's renewal law
(Proposition 3.2 in arXiv:2309.14285v2). After an admissible prefix ending in zero, the
remaining digits have the original cylinder probabilities. A prefix ending in one forces
one more zero before renewal. The proof derives the prefix masses from odometer invariance.
-/

namespace MetaMathlibExt

open MeasureTheory

namespace zeckOdometer_invariant_measure_renewal

private abbrev Word := ℕ → Bool

-- Words are indexed from zero. Their first digit corresponds to digit 2 of the odometer.
private def cyl (n : ℕ) (w : Word) (offset : ℕ := 0) : Set Word :=
  {x | ∀ i < n, x (i + 2 + offset) = w i}

private lemma measurable_cyl (n : ℕ) (w : Word) (s : ℕ := 0) : MeasurableSet (cyl n w s) := by
  simp only [cyl, Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_eq_fun (measurable_pi_apply (i + 2 + s)) measurable_const

private def Admissible (w : Word) := ∀ i, w i = false ∨ w (i + 1) = false

private def clear (n : ℕ) (w : Word) : Word := fun i => if i < n then false else w i

-- Before the carry at j the digits alternate, ending in a one just below j.
private def predecessor (j : ℕ) (w : Word) : Word := fun i =>
  if i < j then decide ((j - i) % 2 = 1) else if i = j then false else w i

private lemma admissible_predecessor {w : Word} (hw : Admissible w) (j : ℕ) :
    Admissible (predecessor j w) := by
  intro i
  by_cases hi : i + 1 < j
  · simp only [predecessor, ite_eq_left hi, ite_eq_left (show i < j by omega),
      decide_eq_false_iff_not]
    omega
  · by_cases he : i + 1 = j
    · right
      simp [predecessor, he]
    · by_cases hij : i = j
      · left
        simp [predecessor, hij]
      · simpa [predecessor, show ¬ i < j by omega, hi, hij, he] using hw i

private def Stops (x : Word) (a : ℕ) := 2 ≤ a ∧ x a = false ∧ x (a + 1) = false

private lemma step_cases (x : Word) :
    (∀ i, zeckOdometer x (i + 2) = false) ∨
    ∃ j, Stops x (j + 2) ∧ (∀ i < j, ¬ Stops x (i + 2)) ∧
      ∀ i, zeckOdometer x (i + 2) = if i < j then false else if i = j then true else x (i + 2) := by
  classical
  unfold zeckOdometer
  split
  next h =>
    right
    have hs := Nat.find_spec h
    obtain ⟨j, hj⟩ : ∃ j, Nat.find h = j + 2 := ⟨Nat.find h - 2, by omega⟩
    refine ⟨j, hj ▸ hs, fun i hi => Nat.find_min h (by omega), fun i => ?_⟩
    simp [hj]
  next => exact Or.inl fun _ => rfl

private lemma before_stop {x : Word} (hx : x ∈ zeckAdic) {j : ℕ} (hs : Stops x (j + 2))
    (hm : ∀ i < j, ¬ Stops x (i + 2)) {i : ℕ} (hi : i ≤ j) :
    x (i + 2) = decide ((j - i) % 2 = 1) := by
  induction d : j - i generalizing i with
  | zero =>
    obtain rfl : i = j := by omega
    simpa using hs.2.1
  | succ d ih =>
    have hlt : i < j := by omega
    have hn := ih (i := i + 1) (by omega) (by omega)
    have ha := hx.2.2 (i + 2)
    have hno := hm i hlt
    simp only [Stops] at hno
    have he : i + 1 + 2 = i + 2 + 1 := by omega
    rw [he] at hn
    cases h : x (i + 2) <;> simp_all <;> omega

private lemma preimage_cyl {w : Word} (hw : Admissible w) {j L : ℕ}
    (hj : j + 1 < L) (hone : w j = true) {x : Word} (hx : x ∈ zeckAdic) :
    zeckOdometer x ∈ cyl L (clear j w) ↔ x ∈ cyl L (predecessor j w) := by
  have hz : w (j + 1) = false := (hw j).resolve_left (by simp [hone])
  have recover (h : x ∈ cyl L (predecessor j w)) :
      Stops x (j + 2) ∧ ∀ i < j, ¬ Stops x (i + 2) := by
    have h₁ := h j (by omega)
    have h₂ := h (j + 1) hj
    refine ⟨⟨by omega, by simpa [predecessor] using h₁, by simpa [predecessor, hz] using h₂⟩, ?_⟩
    intro i hi hs
    have ha := h i (by omega)
    have hb := h (i + 1) (by omega)
    simp only [predecessor, ite_eq_left hi, Nat.add_zero] at ha
    have hpar : (j - i) % 2 ≠ 1 := by simpa [hs.2.1] using ha.symm
    have hf : x (i + 1 + 2) = false := hs.2.2
    by_cases he : i + 1 < j
    · have := hb.symm
      simp [predecessor, he, hf] at this
      omega
    · omega
  constructor
  · intro h
    have hon : zeckOdometer x (j + 2) = true := by simpa [clear, hone] using h j (by omega)
    obtain hzero | ⟨b, hs, hm, hs'⟩ := step_cases x
    · simp [hzero] at hon
    have hb : b = j := by
      rcases lt_trichotomy b j with hb | hb | hb
      · have hh := h b (by omega)
        simp [clear, hb, hs'] at hh
      · exact hb
      · simp [hs', hb] at hon
    subst b
    intro i hi
    rcases lt_trichotomy i j with hij | rfl | hij
    · simpa [predecessor, hij] using before_stop hx hs hm hij.le
    · simpa [predecessor] using hs.2.1
    · simpa [predecessor, clear, hij.not_gt, hij.ne', hs'] using h i hi
  · intro h
    obtain ⟨hs, hm⟩ := recover h
    classical
    have hex : ∃ a, 2 ≤ a ∧ x a = false ∧ x (a + 1) = false := ⟨_, hs⟩
    have hfind : Nat.find hex = j + 2 := by
      apply le_antisymm (Nat.find_min' hex hs)
      have hf := Nat.find_spec hex
      by_contra! hlt
      obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 2 := ⟨Nat.find hex - 2, by omega⟩
      exact hm i (by omega) (hi ▸ hf)
    intro i hi
    simp only [cyl, Set.mem_ofPred_eq, Nat.add_zero] at h
    simp only [Nat.add_zero, zeckOdometer, dite_eq_left hex, hfind, Nat.add_lt_add_iff_right,
      Nat.add_left_inj, clear]
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [hij]
    · simp [hone]
    · simpa [predecessor, hij.not_gt, hij.ne'] using h i hi

private def join (n : ℕ) (u v : Word) : Word := fun i => if i < n then u i else v (i - n)

private lemma admissible_join {n : ℕ} {u v : Word} (hu : Admissible u) (hv : Admissible v)
    (hend : ∀ i, i + 1 = n → u i = false) : Admissible (join n u v) := by
  intro i
  rcases lt_trichotomy (i + 1) n with hi | hi | hi
  · simpa [join, hi, show i < n by omega] using hu i
  · left
    simp [join, show i < n by omega, hend i hi]
  · simpa [join, hi.not_gt, show ¬ i < n by omega, show i + 1 - n = i - n + 1 by omega]
      using hv (i - n)

private lemma cyl_join (n l : ℕ) (u v : Word) :
    cyl n u ∩ cyl l v n = cyl (n + l) (join n u v) := by
  ext x
  constructor
  · rintro ⟨hu, hv⟩ i hi
    by_cases h : i < n
    · simpa [join, h] using hu i h
    · simpa [join, h, show i - n + 2 + n = i + 2 by omega] using hv (i - n) (by omega)
  · intro h
    constructor
    · intro i hi
      simpa [join, hi] using h i (by omega)
    · intro i hi
      simpa [join, Nat.add_right_comm] using h (i + n) (by omega)

private lemma indexed_cyl (ℓ s : ℕ) (z : Word) :
    {x : Word | ∀ i, 2 ≤ i → i ≤ ℓ → x (i + s) = z i} =
      cyl (ℓ - 1) (fun i => z (i + 2)) s := by
  ext x
  constructor
  · intro h i hi
    exact h (i + 2) (by omega) (by omega)
  · intro h i hi hi'
    simpa [Nat.sub_add_cancel hi] using h (i - 2) (by omega)

variable {μ : Measure Word}
  (hX : μ zeckAdicᶜ = 0) (hT : MeasurePreserving zeckOdometer μ μ)

include hX hT

private lemma mass_clear {L n : ℕ} (hn : n < L) {w : Word} (hw : Admissible w) :
    μ (cyl L w) = μ (cyl L (clear n w)) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [ih (by omega) hw]
    cases hbit : w n with
    | false =>
      congr 2
      funext i
      unfold clear
      split_ifs <;> first | rfl | grind
    | true =>
      rw [← hT.measure_preimage (measurable_cyl L _).nullMeasurableSet]
      calc
        _ = μ (cyl L (predecessor n w)) := by
          apply measure_congr
          filter_upwards [ae_iff.mpr hX] with x hx
          exact preimage_cyl hw hn hbit hx
        _ = μ (cyl L (clear n (predecessor n w))) :=
          ih (by omega) (admissible_predecessor hw n)
        _ = _ := by
          congr 2
          funext i
          unfold clear predecessor
          split_ifs <;> first | rfl | omega

private abbrev zeros : Word := fun _ => false

-- Every admissible word whose last digit is zero has the mass of the all-zero word.
private lemma reset_mass {w : Word} (hw : Admissible w) {n : ℕ}
    (hend : ∀ i, i + 1 = n → w i = false) : μ (cyl n w) = μ (cyl n zeros) := by
  cases n with
  | zero => simp [cyl]
  | succ n =>
    rw [mass_clear hX hT (Nat.lt_succ_self n) hw]
    congr 1
    ext x
    have he (i : ℕ) (hi : i < n + 1) : clear n w i = false := by
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl <;> simp [clear, *]
    exact forall_congr' fun i => forall_congr' fun hi => by rw [he i hi]

private def zeroMass (μ : Measure Word) (n : ℕ) := μ.real (cyl n zeros)

variable [IsProbabilityMeasure μ]

private lemma zeroMass_add (n : ℕ) :
    zeroMass μ n = zeroMass μ (n + 1) + zeroMass μ (n + 2) := by
  let w : Word := fun i => decide (i = n)
  have hw : Admissible w := by intro i; simp [w]; omega
  have he := reset_mass hX hT hw (n := n + 2) (by intro i hi; simp [w]; omega)
  have splitC : cyl n zeros =ᵐ[μ] (cyl (n + 1) zeros ∪ cyl (n + 2) w) := by
    filter_upwards [ae_iff.mpr hX] with x hx
    change (∀ i < n, x (i + 2) = false) ↔
      (∀ i < n + 1, x (i + 2) = false) ∨ (∀ i < n + 2, x (i + 2) = w i)
    constructor
    · intro h
      cases hb : x (n + 2) with
      | false =>
        left
        intro i hi
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
        · exact h i hi
        · exact hb
      | true =>
        have hf := (hx.2.2 (n + 2)).resolve_left (by simp [hb])
        right
        intro i hi
        rcases lt_trichotomy i n with hi' | rfl | hi'
        · simp [w, hi'.ne, h i hi']
        · simp [w, hb]
        · obtain rfl : i = n + 1 := by omega
          simpa [w] using hf
    · rintro (h | h) i hi
      · exact h i (by omega)
      · simpa [w, hi.ne] using h i (by omega)
  have hd : Disjoint (cyl (n + 1) zeros) (cyl (n + 2) w) := by
    apply Set.disjoint_left.mpr
    intro x ha hb
    have h₀ := ha n (by omega)
    have h₁ := hb n (by omega)
    simp_all [zeros, w]
  unfold zeroMass
  rw [measureReal_congr splitC, measureReal_union hd (measurable_cyl _ w)]
  simp only [measureReal_def, he]

open scoped goldenRatio
open Filter Topology

-- The bounded solution of pₙ = pₙ₊₁ + pₙ₊₂ with p₀ = 1 is φ⁻ⁿ.
private lemma zeroMass_eq (n : ℕ) : zeroMass μ n = φ⁻¹ ^ n := by
  let p := zeroMass μ
  let r := φ⁻¹
  have hr : 0 < r := inv_pos.mpr Real.goldenRatio_pos
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hsq : r * r + r = 1 := by
    dsimp only [r]
    rw [Real.inv_goldenRatio]
    nlinarith only [Real.goldenConj_sq]
  let d := fun k => p (k + 1) - r * p k
  have recurrence (k : ℕ) : d k = -r * d (k + 1) := by
    have hp : p k = p (k + 1) + p (k + 2) := zeroMass_add hX hT k
    dsimp [d]
    rw [hp]
    linear_combination -(p (k + 1)) * hsq
  have bound (k : ℕ) : |d k| ≤ 2 := by
    have b (i : ℕ) : 0 ≤ p i ∧ p i ≤ 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
    dsimp [d]
    rw [abs_le]
    constructor <;> nlinarith [b k, b (k + 1), mul_nonneg hr.le (b k).1,
      mul_le_mul_of_nonneg_left (b k).2 hr.le]
  have ratio (k : ℕ) : p (k + 1) = r * p k := by
    have small (m : ℕ) (i : ℕ) : |d i| ≤ r ^ m * 2 := by
      induction m generalizing i with
      | zero => simpa using bound i
      | succ m ih =>
        rw [recurrence i, abs_mul, abs_neg, abs_of_pos hr, pow_succ]
        calc r * |d (i + 1)| ≤ r * (r ^ m * 2) := by gcongr; exact ih _
          _ = _ := by ring
    have lim := (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1).mul_const (2 : ℝ)
    have hle := ge_of_tendsto' lim (fun m => small m k)
    have hd : |d k| = 0 := le_antisymm (by simpa using hle) (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp hd)
  change p n = r ^ n
  induction n with
  | zero => simp [p, zeroMass, cyl]
  | succ n ih => rw [ratio, ih, pow_succ, mul_comm]

private lemma cyl_mass {w : Word} (hw : Admissible w) {n : ℕ}
    (hend : ∀ i, i + 1 = n → w i = false) :
    μ (cyl n w) = ENNReal.ofReal (φ⁻¹ ^ n) := by
  rw [reset_mass hX hT hw hend, ← zeroMass_eq hX hT n]
  exact (ofReal_measureReal (μ := μ) (s := cyl n zeros)).symm

omit hT [IsProbabilityMeasure μ] in
private lemma pad_cyl {m : ℕ} {v : Word} (hv : Admissible v) :
    ∃ l, (∀ i, i + 1 = l → v i = false) ∧ ∀ s, cyl m v s =ᵐ[μ] cyl l v s := by
  cases m with
  | zero => exact ⟨0, by omega, fun _ => .rfl⟩
  | succ m =>
    cases hb : v m with
    | false => exact ⟨m + 1, by simpa using hb, fun _ => .rfl⟩
    | true =>
      have hf := (hv m).resolve_left (by simp [hb])
      refine ⟨m + 2, fun i hi => by rwa [show i = m + 1 by omega], fun s => ?_⟩
      filter_upwards [ae_iff.mpr hX] with x hx
      refine ⟨fun h i hi => ?_, fun h i hi => h i (by omega)⟩
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
      · exact h i hi
      · have hone := (h m (Nat.lt_succ_self m)).trans hb
        have := (hx.2.2 (m + 2 + s)).resolve_left (by simp [hone])
        simpa only [hf, show m + 1 + 2 + s = m + 2 + s + 1 by omega] using this

private lemma conditional_reset {n m : ℕ} {u v : Word} (hu : Admissible u) (hv : Admissible v)
    (hend : ∀ i, i + 1 = n → u i = false) {E : Set Word} (hE : E =ᵐ[μ] cyl n u) :
    ProbabilityTheory.cond μ E (cyl m v n) = μ (cyl m v) := by
  obtain ⟨l, hl, heq⟩ := pad_cyl hX hv (m := m)
  have hj : ∀ i, i + 1 = n + l → join n u v i = false := by
    intro i hi
    by_cases h : i < n
    · simp [join, h, hend i (by omega)]
    · simp [join, h, hl (i - n) (by omega)]
  have hi := hE.inter (heq n)
  rw [ProbabilityTheory.cond_apply' (measurable_cyl _ _ _), measure_congr hE, measure_congr hi,
    cyl_join, measure_congr (heq 0), cyl_mass hX hT hu hend, cyl_mass hX hT hv hl,
    cyl_mass hX hT (admissible_join hu hv hend) hj, pow_add,
    ENNReal.ofReal_mul (pow_nonneg (inv_pos.mpr Real.goldenRatio_pos).le _), ← mul_assoc]
  rw [ENNReal.inv_mul_cancel _ ENNReal.ofReal_ne_top, one_mul]
  exact (ENNReal.ofReal_pos.mpr (pow_pos (inv_pos.mpr Real.goldenRatio_pos) _)).ne'

-- A terminal one forces a further zero, giving a reset prefix of length k + 1.
private lemma renewal (b : Bool) {k ℓ : ℕ} (hk : 2 ≤ k) {y z : Word}
    (hy : y ∈ zeckAdic) (hz : z ∈ zeckAdic) (hb : b = true → y k = false) :
    ProbabilityTheory.cond μ {x | x (k + 1) = b ∧ ∀ i, 2 ≤ i → i ≤ k → x i = y i}
      {x | ∀ i, 2 ≤ i → i ≤ ℓ → x (i + (k + b.toNat)) = z i} =
      μ {x | ∀ i, 2 ≤ i → i ≤ ℓ → x i = z i} := by
  let u : Word := fun i => if i + 2 ≤ k then y (i + 2) else if i + 2 = k + 1 then b else false
  have hu : Admissible u := by
    intro i
    rcases lt_trichotomy (i + 2) k with h | he | h
    · simpa [u, h.le, show i + 1 + 2 ≤ k by omega] using hy.2.2 (i + 2)
    · simp only [u, he, le_refl, ite_true, show i + 1 + 2 = k + 1 by omega]
      cases b <;> simp_all
    · right
      unfold u
      split_ifs <;> first | rfl | omega
  have hend (i : ℕ) (hi : i + 1 = k + b.toNat) : u i = false := by
    cases b <;> simp_all [u]
    omega
  have hz₀ := indexed_cyl ℓ 0 z
  simp only [Nat.add_zero] at hz₀
  rw [indexed_cyl, hz₀]
  apply conditional_reset hX hT hu (fun i => hz.2.2 (i + 2)) hend
  filter_upwards [ae_iff.mpr hX] with x hx
  constructor
  · rintro ⟨hbit, hy'⟩ i hi
    rcases lt_trichotomy (i + 2) (k + 1) with h | he | h
    · simpa [u, show i + 2 ≤ k by omega] using hy' (i + 2) (by omega) (by omega)
    · simpa only [Nat.add_zero, u, he, Nat.not_succ_le_self, ite_false, ite_true] using hbit
    · cases b with
      | false => simp at hi; omega
      | true =>
        have hf := (hx.2.2 (k + 1)).resolve_left (by simp [hbit])
        simp only [Bool.toNat_true] at hi
        simp only [Nat.add_zero, u, ite_eq_right (show ¬ i + 2 ≤ k by omega),
          ite_eq_right h.ne']
        simpa only [show i + 2 = k + 1 + 1 by omega] using hf
  · intro h
    constructor
    · have he : k - 1 + 2 = k + 1 := by omega
      simpa only [Nat.add_zero, u, he, Nat.not_succ_le_self, ite_false, ite_true]
        using h (k - 1) (by omega)
    · intro i hi hi'
      simpa [u, Nat.sub_add_cancel hi, hi'] using h (i - 2) (by omega)

end zeckOdometer_invariant_measure_renewal

open zeckOdometer_invariant_measure_renewal in
/-- **Renewal property of the invariant measure.** Let
$\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$ be the set of Zeckendorf-adic integers (sequences
with $x_0 = x_1 = 0$ and no two consecutive ones) and let $T$ be the Zeckendorf odometer. Let
$\mu$ be a probability measure on $\{0,1\}^{\mathbb{N}}$ with $\mu(\mathbb{X}^c) = 0$ that is
preserved by $T$. Let $k \ge 2$, $\ell_0 \in \mathbb{N}$ and $y, z \in \mathbb{X}$, and let
$C = \{x : x_i = z_i \text{ for } 2 \le i \le \ell_0\}$. Let
$E_0 = \{x : x_{k+1} = 0 \text{ and } x_i = y_i \text{ for } 2 \le i \le k\}$ and
$E_1 = \{x : x_{k+1} = 1 \text{ and } x_i = y_i \text{ for } 2 \le i \le k\}$. Then
$\mu(\{x : x_{i+k} = z_i \text{ for } 2 \le i \le \ell_0\} \mid E_0) = \mu(C)$, and if
$y_k = 0$, then also
$\mu(\{x : x_{i+k+1} = z_i \text{ for } 2 \le i \le \ell_0\} \mid E_1) = \mu(C)$.

With the shift $(\sigma x)_i = x_{i+1}$, the two conditioned events are $\sigma^k x \in C$ and
$\sigma^{k+1} x \in C$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 16 (`jis-2024-24.3.2-prop-16`). -/
public theorem zeckOdometer_invariant_measure_renewal (μ : Measure (ℕ → Bool))
    [IsProbabilityMeasure μ] (hX : μ zeckAdicᶜ = 0) (hT : MeasurePreserving zeckOdometer μ μ)
    {k ℓ₀ : ℕ} (hk : 2 ≤ k) {y z : ℕ → Bool} (hy : y ∈ zeckAdic) (hz : z ∈ zeckAdic) :
    ProbabilityTheory.cond μ {x | x (k + 1) = false ∧ ∀ i, 2 ≤ i → i ≤ k → x i = y i}
        {x | ∀ i, 2 ≤ i → i ≤ ℓ₀ → x (i + k) = z i} =
      μ {x | ∀ i, 2 ≤ i → i ≤ ℓ₀ → x i = z i} ∧
    (y k = false →
      ProbabilityTheory.cond μ {x | x (k + 1) = true ∧ ∀ i, 2 ≤ i → i ≤ k → x i = y i}
          {x | ∀ i, 2 ≤ i → i ≤ ℓ₀ → x (i + (k + 1)) = z i} =
        μ {x | ∀ i, 2 ≤ i → i ≤ ℓ₀ → x i = z i}) := by
  exact ⟨renewal hX hT false hk hy hz (by simp), fun h => renewal hX hT true hk hy hz (fun _ => h)⟩

end MetaMathlibExt
