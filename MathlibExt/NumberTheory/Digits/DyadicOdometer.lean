/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ProbabilityMassFunction.Uniform
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import MathlibExt.NumberTheory.Digits.QWeightedTrollopeDelange

import MathlibExt.Dynamics.Ergodic.BernoulliShift
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Limiting curves of the dyadic odometer

For almost every dyadic integer, the normalized fluctuations of the interpolated odometer sums
converge along a sequence of lengths to the negative Takagi–Landsberg function.

By ergodicity of the Bernoulli shift, a typical digit sequence contains arbitrarily long
blocks of zeros. If such a block ends just below position `m`, the value `d` of the
first `m` digits is small compared with `2 ^ m`. Take the length `2 ^ m - d` and the
scale `(2 * q) ^ m / 2`. The higher digits contribute a linear term that cancels on centering.
The dyadic fluctuation formula identifies the remaining grid values, and uniform continuity
of the Takagi–Landsberg function controls the chords between them.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- **Carry in adding a natural number to a dyadic integer.** Let $\omega$ be a dyadic integer,
written as its sequence $(\omega_0, \omega_1, \dots)$ of binary digits $\omega_i \in \{0, 1\}$
(least significant digit first), and let $j$ be a natural number with binary digits
$j_0, j_1, \dots$. The carry $c_i$ into digit $i$ in the binary addition of $j$ to $\omega$ is
defined by $c_0 = 0$ and $c_{i+1} = \lfloor (\omega_i + j_i + c_i)/2 \rfloor$.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 5 (dyadic integers and the odometer). -/
def dyadicAddNatCarry (ω : ℕ → Fin 2) (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => ((ω i : ℕ) + (j.testBit i).toNat + dyadicAddNatCarry ω j i) / 2

/-- **Adding a natural number to a dyadic integer.** Let $\omega$ be a dyadic integer, written as
its sequence $(\omega_0, \omega_1, \dots)$ of binary digits $\omega_i \in \{0, 1\}$ (least
significant digit first), and let $j$ be a natural number with binary digits $j_0, j_1, \dots$.
The dyadic integer $\omega + j$ has $i$-th digit $(\omega_i + j_i + c_i) \bmod 2$, where the
carries are given by $c_0 = 0$ and $c_{i+1} = \lfloor (\omega_i + j_i + c_i)/2 \rfloor$.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 5 (dyadic integers and the odometer). -/
def dyadicAddNat (ω : ℕ → Fin 2) (j : ℕ) : ℕ → Fin 2 := fun i =>
  ⟨((ω i : ℕ) + (j.testBit i).toNat + dyadicAddNatCarry ω j i) % 2, Nat.mod_lt _ two_pos⟩

/-- **Dyadic odometer.** The dyadic odometer is the map $T$ on the dyadic integers $\mathbb{Z}_2$,
viewed as binary digit sequences $\omega = (\omega_0, \omega_1, \dots)$ (least significant digit
first), given by $T\omega = \omega + 1$, binary addition of $1$ with carries.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 5. -/
def dyadicOdometer (ω : ℕ → Fin 2) : ℕ → Fin 2 := dyadicAddNat ω 1

/-- **First digits of the odometer at zero.** Let $T$ be the dyadic odometer $T\omega = \omega + 1$
on dyadic integers $\omega = (\omega_0, \omega_1, \dots)$, written as binary digit sequences. The
image $T(0)$ of the zero sequence $(0, 0, 0, \dots)$ has digits $T(0)_0 = 1$, $T(0)_1 = 0$ and
$T(0)_2 = 0$.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 5. -/
theorem dyadicOdometer_zero_apply :
    dyadicOdometer (fun _ => 0) 0 = 1 ∧ dyadicOdometer (fun _ => 0) 1 = 0 ∧
      dyadicOdometer (fun _ => 0) 2 = 0 := by
  decide

/-- **Haar measure on the dyadic integers.** The Haar measure on the dyadic integers
$\mathbb{Z}_2$, viewed as the space $\{0, 1\}^{\mathbb{N}}$ of binary digit sequences: the infinite
product of the uniform probability measures on $\{0, 1\}$, one for each digit.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 5. -/
noncomputable def dyadicHaar : MeasureTheory.Measure (ℕ → Fin 2) :=
  MeasureTheory.Measure.infinitePi fun _ => (PMF.uniformFintype (Fin 2)).toMeasure

/-- The Haar measure on `ℤ₂` is a probability measure.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 5. -/
instance : MeasureTheory.IsProbabilityMeasure dyadicHaar := by
  unfold dyadicHaar
  infer_instance

/-- **Odometer partial sums.** Let $q \in \mathbb{C}$, let $\omega = (\omega_0, \omega_1, \dots)$ be
a dyadic integer written as its binary digit sequence, let $T$ be the dyadic odometer
$T\omega = \omega + 1$, and let $s_q(\omega) = \sum_{i \ge 0} \omega_i q^{i+1}$, taken to be $0$
when the series is not absolutely summable. For real $x$ the odometer partial sum is

$$S_{q,\omega}(x) = \sum_{j < \lfloor x \rfloor_+} s_q(T^j \omega) +
\{x\} \, s_q(T^{\lfloor x \rfloor_+} \omega),$$

where $\lfloor x \rfloor_+ = \max(\lfloor x \rfloor, 0)$ and $\{x\} = x - \lfloor x \rfloor$. So
$S_{q,\omega}(n) = \sum_{j < n} s_q(T^j \omega)$ for every natural number $n$, and for $x \ge 0$
the function $S_{q,\omega}$ interpolates these values linearly between consecutive integers.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Sections 4 and 5. -/
noncomputable def odometerDigitPartialSum (q : ℂ) (ω : ℕ → Fin 2) (x : ℝ) : ℂ :=
  (∑ j ∈ range ⌊x⌋₊, ∑' i : ℕ, ((dyadicOdometer^[j] ω i : ℕ) : ℂ) * q ^ (i + 1)) +
    ((Int.fract x : ℝ) : ℂ) * ∑' i : ℕ, ((dyadicOdometer^[⌊x⌋₊] ω i : ℕ) : ℂ) * q ^ (i + 1)

/-- **The odometer partial sum vanishes at zero.** For every $q \in \mathbb{C}$ and every dyadic
integer $\omega$, the interpolated odometer partial sum satisfies $S_{q,\omega}(0) = 0$.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 5. -/
theorem odometerDigitPartialSum_zero (q : ℂ) (ω : ℕ → Fin 2) :
    odometerDigitPartialSum q ω 0 = 0 := by
  simp [odometerDigitPartialSum]

/-- **Maximal fluctuation of the odometer partial sums.** Let $q$ be a complex number, let
$\omega = (\omega_0, \omega_1, \dots)$ be a dyadic integer (a sequence of binary digits), let $l$
be a natural number, and let $S_{q,\omega}$ denote the interpolated odometer partial sums. The
maximal fluctuation is the supremum over $t \in [0, 1]$ of
$|S_{q,\omega}(t l) - t\,S_{q,\omega}(l)|$.

This is the scale of the canonical normalizing coefficient of the sources: "the normalizing
coefficient $R_n$ is canonically defined to be equal to the maximum in $t \in [0, 1]$ of
$|\mathcal{S}(t \cdot l_n(x)) - t \cdot \mathcal{S}(l_n)|$".

Source: Aleksei Minabutdinov, *Limiting curves for the dyadic odometer and the generalized
Trollope-Delange formula*, Section 2.2 (definition of `φ_n` and `R_n`), and *A q-Weighted
Analogue of the Trollope-Delange Formula*, INTEGERS 26 (2026), Article A61, Section 3
(definition of the normalization factor `R_n`). -/
noncomputable def odometerMaxFluctuation (q : ℂ) (ω : ℕ → Fin 2) (l : ℕ) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) 1,
    ‖odometerDigitPartialSum q ω ((t : ℝ) * (l : ℝ)) -
      (t : ℝ) * odometerDigitPartialSum q ω (l : ℝ)‖

/-- **Stabilizing sequence for the dyadic odometer.** Let $q \in \mathbb{C}$, let $\omega$ be a
dyadic integer, let $S_{q,\omega}$ be the interpolated odometer partial sum, and for a natural
number $l$ let $M_{q,\omega}(l) = \sup_{t \in [0, 1]} |S_{q,\omega}(tl) - t S_{q,\omega}(l)|$ be the
maximal fluctuation. A sequence $(l_n)$ of natural numbers is a stabilizing sequence for
$(q, \omega)$ with normalizing sequence $(R_n)$ of complex numbers and limiting curve
$\varphi : \mathbb{R} \to \mathbb{C}$ when: every $l_n$ is positive and $l_n \to \infty$; every
$R_n$ is nonzero and $|R_n| \to \infty$; there are real constants $c > 0$ and $C$ with
$c M_{q,\omega}(l_n) \le |R_n| \le C M_{q,\omega}(l_n)$ for all sufficiently large $n$;
$\varphi$ is continuous on $[0, 1]$; and the functions
$t \mapsto (S_{q,\omega}(t l_n) - t S_{q,\omega}(l_n))/R_n$ converge uniformly on $[0, 1]$ to
$\varphi$.

The normalizing sequence $R_n$ is chosen of the order of $M_{q,\omega}(l_n)$, not equal to it:
with equality every normalized fluctuation would have supremum norm at most $1$, so the limit in
Theorem 2 of Article A61 could not be the negative Takagi–Landsberg function $-\mathcal{T}_a$
(for example $\mathcal{T}_{3/4}(1/3) = 4/3$). This matches the sources' usage, where
$\varphi^{l_n,R_n}$ is parametrized by the chosen $R_n$ (e.g. $R_n = (2q)^{n-1}$ along
$l_n = 2^n$ in Article A61, Section 3); unbounded growth of $R_n$ is the necessary condition for
a limiting curve recorded in the odometer paper.

Source: Aleksei Minabutdinov, *Limiting curves for the dyadic odometer and the generalized
Trollope-Delange formula*, Definition 1 and Section 3.1, restated in *A q-Weighted
Analogue of the Trollope-Delange Formula*, INTEGERS 26 (2026), Article A61, Section 3. -/
def IsStabilizingSeq (q : ℂ) (ω : ℕ → Fin 2) (l : ℕ → ℕ) (R : ℕ → ℂ) (φ : ℝ → ℂ) : Prop :=
  (∀ n, 0 < l n) ∧ Filter.Tendsto l Filter.atTop Filter.atTop ∧
    (∀ n, R n ≠ 0) ∧
    Filter.Tendsto (fun n => ‖R n‖) Filter.atTop Filter.atTop ∧
    (∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in Filter.atTop,
      c * odometerMaxFluctuation q ω (l n) ≤ ‖R n‖ ∧
        ‖R n‖ ≤ C * odometerMaxFluctuation q ω (l n)) ∧
    ContinuousOn φ (Set.Icc 0 1) ∧
    TendstoUniformlyOn
      (fun n (t : ℝ) => (odometerDigitPartialSum q ω (t * l n) -
        t * odometerDigitPartialSum q ω (l n)) / R n)
      φ Filter.atTop (Set.Icc 0 1)

namespace odometer_limitingCurve_eq_neg_takagi

open MeasureTheory Filter Topology

/-! ### Finite prefixes before the first carry out of the block -/

private def prefixValue (ω : ℕ → Fin 2) : ℕ → ℕ
  | 0 => 0
  | m + 1 => prefixValue ω m + 2 ^ m * (ω m : ℕ)

private lemma prefix_lt (ω : ℕ → Fin 2) (m : ℕ) : prefixValue ω m < 2 ^ m := by
  induction m with
  | zero => simp [prefixValue]
  | succ m ih =>
    rw [prefixValue, pow_succ]
    have := Nat.mul_le_mul_left (2 ^ m) (Nat.le_of_lt_succ (ω m).isLt)
    omega

private def carry (ω : ℕ → Fin 2) : ℕ → ℕ
  | 0 => 1
  | i + 1 => ((ω i : ℕ) + carry ω i) / 2

private lemma carry_eq (ω : ℕ → Fin 2) (i : ℕ) :
    ((1 : ℕ).testBit i).toNat + dyadicAddNatCarry ω 1 i = carry ω i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [Nat.testBit_succ, Nat.reduceDiv, Nat.zero_testBit, Bool.toNat_false, zero_add]
    rw [dyadicAddNatCarry, carry, Nat.add_assoc, ih]

private lemma odometer_bit (ω : ℕ → Fin 2) (i : ℕ) :
    (dyadicOdometer ω i : ℕ) = ((ω i : ℕ) + carry ω i) % 2 := by
  change (_ + _ + _) % 2 = _
  rw [Nat.add_assoc, carry_eq]

private lemma add_prefix (ω : ℕ → Fin 2) (m : ℕ) :
    prefixValue (dyadicOdometer ω) m + 2 ^ m * carry ω m = prefixValue ω m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [prefixValue, prefixValue, odometer_bit, carry, pow_succ]
    have h := Nat.mod_add_div ((ω m : ℕ) + carry ω m) 2
    linear_combination (norm := ring_nf) ih + 2 ^ m * h

private lemma step_before_boundary (ω : ℕ → Fin 2) {m : ℕ}
    (h : prefixValue ω m + 1 < 2 ^ m) :
    prefixValue (dyadicOdometer ω) m = prefixValue ω m + 1 ∧
      ∀ i ≥ m, dyadicOdometer ω i = ω i := by
  have e := add_prefix ω m
  have hc : carry ω m = 0 := by
    by_contra! hn
    have := Nat.mul_le_mul_left (2 ^ m) (Nat.one_le_iff_ne_zero.mpr hn)
    simp only [mul_one] at this
    omega
  refine ⟨by simpa [hc] using e, fun i hi => ?_⟩
  have hz : carry ω i = 0 := by
    induction i, hi using Nat.le_induction with
    | base => exact hc
    | succ k _ ih => simp [carry, ih, Nat.div_eq_of_lt (ω k).isLt]
  apply Fin.ext
  rw [odometer_bit, hz, Nat.add_zero, Nat.mod_eq_of_lt (ω i).isLt]

private lemma orbit_prefix (ω : ℕ → Fin 2) (m j : ℕ) (h : prefixValue ω m + j < 2 ^ m) :
    prefixValue (dyadicOdometer^[j] ω) m = prefixValue ω m + j ∧
      ∀ i ≥ m, dyadicOdometer^[j] ω i = ω i := by
  induction j with
  | zero => exact ⟨rfl, fun _ _ => rfl⟩
  | succ j ih =>
    obtain ⟨hp, ht⟩ := ih (by omega)
    obtain ⟨hp', ht'⟩ := step_before_boundary (dyadicOdometer^[j] ω) (m := m) (by omega)
    rw [Function.iterate_succ_apply']
    exact ⟨by omega, fun i hi => (ht' i hi).trans (ht i hi)⟩

private lemma prefix_tail (ω : ℕ → Fin 2) (m : ℕ) :
    prefixValue ω (m + 1) = (ω 0 : ℕ) + 2 * prefixValue (fun i => ω (i + 1)) m := by
  induction m with
  | zero => simp [prefixValue]
  | succ m ih =>
    rw [prefixValue, ih, pow_succ]
    simp only [prefixValue]
    ring

private lemma prefix_weight (ω : ℕ → Fin 2) (q : ℂ) (m : ℕ) :
    ∑ i ∈ range m, ((ω i : ℕ) : ℂ) * q ^ (i + 1) = qWeightedDigitSum q (prefixValue ω m) := by
  induction m generalizing ω with
  | zero => simp [prefixValue, qWeightedDigitSum_zero]
  | succ m ih =>
    have digit_rec (k : ℕ) : qWeightedDigitSum q k =
        q * (k % 2 : ℕ) + q * qWeightedDigitSum q (k / 2) := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [qWeightedDigitSum_zero]
      · exact qWeightedDigitSum_of_pos q hk
    rw [sum_range_succ', prefix_tail, digit_rec, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (ω 0).isLt, Nat.add_mul_div_left _ _ two_pos,
      Nat.div_eq_of_lt (ω 0).isLt]
    simp only [Nat.zero_add]
    rw [← ih]
    simp only [mul_sum, pow_one]
    rw [add_comm]
    congr 1
    · ring
    · apply sum_congr rfl
      intro i _
      ring

private noncomputable abbrev digitValue (q : ℂ) (ω : ℕ → Fin 2) :=
  ∑' i : ℕ, ((ω i : ℕ) : ℂ) * q ^ (i + 1)

private lemma summable_digits (q : ℂ) (hq : ‖q‖ < 1) (ω : ℕ → Fin 2) :
    Summable fun i : ℕ => ((ω i : ℕ) : ℂ) * q ^ (i + 1) := by
  refine Summable.of_norm_bounded (g := fun i : ℕ => ‖q‖ ^ i * ‖q‖)
    ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right _) fun i => ?_
  rw [norm_mul, norm_pow, Complex.norm_natCast, pow_succ]
  exact mul_le_of_le_one_left (by positivity) (by exact_mod_cast Nat.le_of_lt_succ (ω i).isLt)

private lemma orbit_sum (q : ℂ) (hq : ‖q‖ < 1) (ω : ℕ → Fin 2) (m : ℕ) :
    ∃ b : ℂ, ∀ j, prefixValue ω m + j ≤ 2 ^ m →
      odometerDigitPartialSum q ω (j : ℝ) =
        qWeightedDigitPartialSum q (prefixValue ω m + j) -
          qWeightedDigitPartialSum q (prefixValue ω m) + j * b := by
  let b := ∑' i : ℕ, ((ω (i + m) : ℕ) : ℂ) * q ^ (i + m + 1)
  refine ⟨b, fun j hj => ?_⟩
  have step (k : ℕ) (hk : k < j) : digitValue q (dyadicOdometer^[k] ω) =
      qWeightedDigitSum q (prefixValue ω m + k) + b := by
    obtain ⟨hv, ht⟩ := orbit_prefix ω m k (by omega)
    rw [digitValue, ← (summable_digits q hq _).sum_add_tsum_nat_add m, prefix_weight, hv]
    congr 1
    exact tsum_congr fun i => by rw [ht (i + m) (by omega)]
  simp only [odometerDigitPartialSum, Nat.floor_natCast, Int.fract_natCast, Complex.ofReal_zero,
    zero_mul, add_zero]
  change ∑ k ∈ range j, digitValue q (dyadicOdometer^[k] ω) = _
  rw [sum_congr rfl (fun k hk => step k (mem_range.mp hk)), sum_add_distrib,
    sum_const, card_range, nsmul_eq_mul]
  unfold qWeightedDigitPartialSum
  rw [sum_range_add]
  ring

/-! ### Selecting long zero blocks in the Bernoulli shift -/

open MathlibExt.Dynamics.Ergodic.BernoulliShift in
private lemma ae_zero_blocks : ∀ᵐ ω ∂dyadicHaar, ∀ k : ℕ, ∃ b : ℕ, ∀ i < k, ω (i + b) = 0 := by
  refine ae_all_iff.mpr fun k => ?_
  let A : Set (ℕ → Fin 2) := Set.pi (range k : Set ℕ) fun _ => {0}
  have hA : MeasurableSet A := MeasurableSet.pi (range k).countable_toSet fun _ _ => .singleton 0
  have hpos : dyadicHaar A ≠ 0 := by
    rw [dyadicHaar, Measure.infinitePi_pi _ (fun _ _ => MeasurableSet.singleton _)]
    simp
  let U := ⋃ n : ℕ, shift^[n] ⁻¹' A
  have hU : MeasurableSet U := MeasurableSet.iUnion fun n => (measurable_shift.iterate n) hA
  have inv : shift ⁻¹' U ⊆ U := by
    intro ω h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨n + 1, by simpa [Function.iterate_succ_apply] using hn⟩
  have erg : Ergodic shift dyadicHaar := ergodic_shift _
  rcases erg.ae_empty_or_univ_of_preimage_ae_le hU.nullMeasurableSet
      (Eventually.of_forall inv) with he | hu
  · have hu0 : dyadicHaar U = 0 := (measure_congr he).trans measure_empty
    exact (hpos (measure_mono_null (fun ω h => Set.mem_iUnion.mpr ⟨0, h⟩ : A ⊆ U) hu0)).elim
  · filter_upwards [hu] with ω hω
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hω.mpr (Set.mem_univ ω))
    exact ⟨n, fun i hi => by simpa [shift_iterate_apply] using hn i (mem_range.mpr hi)⟩

private lemma prefix_zero_block (ω : ℕ → Fin 2) (b k : ℕ) (h : ∀ i < k, ω (i + b) = 0) :
    prefixValue ω (b + k) = prefixValue ω b := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, prefixValue, Nat.add_comm b k, h k (by omega)]
    simpa [Nat.add_comm] using ih (fun i hi => h i (by omega))

/-! ### The Takagi–Landsberg series and the dyadic grid -/

private lemma takagi_continuous {a : ℂ} (ha : ‖a‖ < 1) : Continuous (takagiLandsberg a) := by
  unfold takagiLandsberg
  apply continuous_tsum (u := fun n : ℕ => ‖a‖ ^ n)
  · intro i
    simp_rw [← UnitAddCircle.norm_eq]
    fun_prop
  · exact summable_geometric_of_lt_one (norm_nonneg _) ha
  · intro i x
    rw [norm_mul, norm_pow, RCLike.norm_ofReal, abs_abs]
    exact mul_le_of_le_one_right (by positivity) ((abs_sub_round _).trans (by norm_num))

private lemma tent_two_pow (n : ℕ) : (2 : ℝ) ^ n - round ((2 : ℝ) ^ n) = 0 := by
  rw [show (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) by norm_cast, round_natCast, Int.cast_natCast,
    sub_self]

private lemma takagi_one (a : ℂ) : takagiLandsberg a 1 = 0 := by
  unfold takagiLandsberg
  simp [tent_two_pow]

private lemma takagi_half (a : ℂ) : takagiLandsberg a (1 / 2) = 1 / 2 := by
  unfold takagiLandsberg
  rw [tsum_eq_single 0]
  · norm_num
  · rintro (_ | n) hn
    · exact (hn rfl).elim
    · rw [pow_succ (2 : ℝ)]
      simp [tent_two_pow]

private lemma double_sum (q : ℂ) (n : ℕ) :
    qWeightedDigitPartialSum q (2 * n) = 2 * q * qWeightedDigitPartialSum q n + n * q := by
  induction n with
  | zero => simp [qWeightedDigitPartialSum]
  | succ n ih =>
    have even : qWeightedDigitSum q (2 * n) = q * qWeightedDigitSum q n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [qWeightedDigitSum_zero]
      · rw [qWeightedDigitSum_of_pos q (by positivity : 0 < 2 * n)]
        simp
    have odd : qWeightedDigitSum q (2 * n + 1) = q + q * qWeightedDigitSum q n := by
      rw [qWeightedDigitSum_of_pos q (by omega : 0 < 2 * n + 1)]
      simp [Nat.mul_add_div two_pos]
    simp only [qWeightedDigitPartialSum] at ih ⊢
    rw [Nat.mul_succ, sum_range_succ, sum_range_succ, ih, even, odd, sum_range_succ]
    push_cast
    ring

private noncomputable abbrev scale (q : ℂ) (m : ℕ) : ℂ := (2 * q) ^ m / 2

private noncomputable abbrev curve (q : ℂ) := takagiLandsberg (1 / (2 * q))

private lemma grid (q : ℂ) (hq : 1 / 2 < ‖q‖) (m j : ℕ) (hj : j ≤ 2 ^ m) :
    qWeightedDigitPartialSum q j =
      ((j : ℂ) / 2 ^ m) * qWeightedDigitPartialSum q (2 ^ m) -
        scale q m * curve q (j / 2 ^ m) := by
  have hq0 : q ≠ 0 := by rintro rfl; norm_num at hq
  have h := qWeightedDigitPartialSum_dyadic_fluctuation q hq (m + 1) (by omega) j (by simpa)
  simp only [Nat.add_sub_cancel, pow_succ 2 m, mul_comm (2 ^ m : ℕ) 2, double_sum] at h
  rw [div_eq_iff (pow_ne_zero _ (mul_ne_zero two_ne_zero hq0))] at h
  push_cast at h
  unfold scale curve
  apply (mul_left_cancel₀ (show 2 * q ≠ 0 by simp [hq0]))
  linear_combination (norm := (field_simp; ring)) h

private lemma partial_on_grid (q : ℂ) (hq : 1 / 2 < ‖q‖) (hq1 : ‖q‖ < 1)
    (ω : ℕ → Fin 2) (m : ℕ) :
    ∃ B : ℂ, ∀ j, prefixValue ω m + j ≤ 2 ^ m →
      odometerDigitPartialSum q ω (j : ℝ) = j * B - scale q m *
        (curve q ((prefixValue ω m + j : ℝ) / 2 ^ m) -
          curve q ((prefixValue ω m : ℝ) / 2 ^ m)) := by
  obtain ⟨b, hb⟩ := orbit_sum q hq1 ω m
  refine ⟨qWeightedDigitPartialSum q (2 ^ m) / 2 ^ m + b, fun j hj => ?_⟩
  rw [hb j hj, grid q hq m _ hj, grid q hq m _ (prefix_lt ω m).le]
  push_cast
  ring

private lemma interpolate (q : ℂ) (ω : ℕ → Fin 2) (x : ℝ) (hx : 0 ≤ x) :
    let j := ⌊x⌋₊
    let u := (x - j : ℝ)
    odometerDigitPartialSum q ω x =
      (1 - (u : ℂ)) * odometerDigitPartialSum q ω (j : ℝ) +
        (u : ℂ) * odometerDigitPartialSum q ω ((j + 1 : ℕ) : ℝ) := by
  dsimp only
  simp only [odometerDigitPartialSum, Int.fract_natCast, Nat.floor_natCast, Complex.ofReal_zero,
    zero_mul, add_zero, sum_range_succ]
  rw [Int.fract, ← Int.natCast_floor_eq_floor hx, Int.cast_natCast]
  ring

private noncomputable abbrev fluct (q : ℂ) (ω : ℕ → Fin 2) (l : ℕ) (t : ℝ) : ℂ :=
  odometerDigitPartialSum q ω (t * l) - t * odometerDigitPartialSum q ω l

/-- At an interior point the centered curve is a chord between two neighboring grid values,
plus the correction for starting part-way through the dyadic block. -/
private lemma chord (q : ℂ) (hq : 1 / 2 < ‖q‖) (hq1 : ‖q‖ < 1)
    (ω : ℕ → Fin 2) (m l : ℕ) (hl : prefixValue ω m + l = 2 ^ m)
    (t : ℝ) (ht : t ∈ Set.Ico 0 1) (hl0 : 0 < l) :
    let d := prefixValue ω m
    let j := ⌊t * l⌋₊
    let u := t * l - j
    fluct q ω l t / scale q m + curve q t =
      (1 - (u : ℂ)) * (curve q t - curve q ((d + j : ℝ) / 2 ^ m)) +
      (u : ℂ) * (curve q t - curve q ((d + (j + 1 : ℕ) : ℝ) / 2 ^ m)) +
      (1 - (t : ℂ)) * curve q ((d : ℝ) / 2 ^ m) := by
  dsimp only
  let j := ⌊t * l⌋₊
  have hx : 0 ≤ t * l := mul_nonneg ht.1 (Nat.cast_nonneg _)
  have hj : j < l := (Nat.floor_lt hx).mpr (by
    simpa using mul_lt_mul_of_pos_right ht.2 (Nat.cast_pos.mpr hl0))
  obtain ⟨B, hB⟩ := partial_on_grid q hq hq1 ω m
  have hreal : (prefixValue ω m : ℝ) + l = 2 ^ m := by exact_mod_cast hl
  have hq0 : q ≠ 0 := by rintro rfl; norm_num at hq
  have hR : scale q m ≠ 0 := div_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero hq0)) two_ne_zero
  unfold fluct
  rw [interpolate q ω _ hx, hB j (by omega), hB (j + 1) (by omega), hB l hl.le,
    hreal, div_self (by positivity), show curve q 1 = 0 from takagi_one _]
  dsimp [j]
  push_cast
  field_simp [hR]
  ring

private lemma grid_point_close {P d l j t δ : ℝ} (hP : 0 < P) (hd : 0 ≤ d)
    (ht : t ∈ Set.Icc 0 1) (h : d + l = P) (hδ : (d + 1) / P < δ)
    (hj : |j - t * l| ≤ 1) : dist ((d + j) / P) t < δ := by
  rw [Real.dist_eq, abs_lt, lt_sub_iff_add_lt, sub_lt_iff_lt_add, lt_div_iff₀ hP, div_lt_iff₀ hP]
  subst P
  rw [div_lt_iff₀ hP] at hδ
  obtain ⟨hj₁, hj₂⟩ := abs_le.mp hj
  constructor <;> nlinarith [mul_nonneg ht.1 hd, mul_nonneg (sub_nonneg.mpr ht.2) hd]

private lemma close_fluct (q : ℂ) (hq : 1 / 2 < ‖q‖) (hq1 : ‖q‖ < 1)
    (ω : ℕ → Fin 2) (m l : ℕ) (hl : prefixValue ω m + l = 2 ^ m) (hl0 : 0 < l)
    {δ ε : ℝ} (hε : 0 < ε) (hδ : ((prefixValue ω m : ℝ) + 1) / 2 ^ m < δ)
    (hmod : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, dist x y < δ →
      dist (curve q x) (curve q y) < ε / 3) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    dist (-curve q t) (fluct q ω l t / scale q m) < ε := by
  rcases ht.2.lt_or_eq with ht1 | rfl
  swap
  · simpa [fluct, curve, takagi_one] using hε
  let d := prefixValue ω m
  let P := (2 : ℝ) ^ m
  have hP : 0 < P := by positivity
  have hl' : (d : ℝ) + l = P := by dsimp [d, P]; exact_mod_cast hl
  have hd : (0 : ℝ) ≤ d := by positivity
  let j := ⌊t * l⌋₊
  let u := t * l - j
  have hx : 0 ≤ t * l := mul_nonneg ht.1 (Nat.cast_nonneg _)
  have hu0 : 0 ≤ u := sub_nonneg.mpr (Nat.floor_le hx)
  have hu1 : u ≤ 1 := by dsimp [u, j]; linarith [Nat.lt_floor_add_one (t * l)]
  have hj : j < l := (Nat.floor_lt hx).mpr (by
    simpa using mul_lt_mul_of_pos_right ht1 (Nat.cast_pos.mpr hl0))
  have mem (k : ℕ) (hk : k ≤ l) : ((d : ℝ) + k) / P ∈ Set.Icc 0 1 := by
    refine ⟨by positivity, (div_le_iff₀ hP).mpr ?_⟩
    have : (k : ℝ) ≤ l := by exact_mod_cast hk
    linarith
  have near (k : ℕ) (hk : k ≤ l) (hkt : |(k : ℝ) - t * l| ≤ 1) :
      ‖curve q t - curve q (((d : ℝ) + k) / P)‖ < ε / 3 := by
    rw [← dist_eq_norm]
    apply hmod t ht _ (mem k hk)
    rw [dist_comm]
    exact grid_point_close hP hd ht hl' hδ hkt
  have h0 := near j hj.le (by rw [abs_le]; dsimp [u] at hu0 hu1; constructor <;> linarith)
  have h1 := near (j + 1) hj (by
    rw [abs_le]; push_cast; dsimp [u] at hu0 hu1; constructor <;> linarith)
  have hstart : ‖curve q ((d : ℝ) / P)‖ < ε / 3 := by
    have hz : (d : ℝ) / P ∈ Set.Icc 0 1 := by simpa using mem 0 (Nat.zero_le _)
    have hnear := hmod _ hz 0 (by constructor <;> norm_num) (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hz.1]
      exact lt_trans (div_lt_div_of_pos_right (by linarith) hP) hδ)
    simpa [curve, takagiLandsberg_zero, dist_eq_norm] using hnear
  rw [dist_comm, dist_eq_norm, sub_neg_eq_add, chord q hq hq1 ω m l hl t ⟨ht.1, ht1⟩ hl0]
  change ‖(1 - (u : ℂ)) * _ + (u : ℂ) * _ + (1 - (t : ℂ)) * _‖ < ε
  apply lt_of_le_of_lt norm_add₃_le
  simp only [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hu0, abs_of_nonneg (sub_nonneg.mpr hu1),
    abs_of_nonneg (sub_nonneg.mpr ht.2)]
  have hu' : 1 - u ≤ 1 := by linarith
  have ht' : 1 - t ≤ 1 := by linarith [ht.1]
  apply lt_of_le_of_lt (add_le_add (add_le_add (mul_le_of_le_one_left (norm_nonneg _) hu')
    (mul_le_of_le_one_left (norm_nonneg _) hu1)) (mul_le_of_le_one_left (norm_nonneg _) ht'))
  linarith only [h0, h1, hstart]

/-- A nonzero value of the uniform limit bounds the normalizing scale from above.
Boundedness on the whole interval bounds it from below. -/
private lemma comparable (q : ℂ) (ω : ℕ → Fin 2) (l : ℕ → ℕ) (R : ℕ → ℂ)
    (hR : ∀ n, R n ≠ 0) (hc : Continuous (curve q))
    (hlim : TendstoUniformlyOn (fun n t => fluct q ω (l n) t / R n)
      (fun t => -curve q t) atTop (Set.Icc 0 1)) :
    ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c * odometerMaxFluctuation q ω (l n) ≤ ‖R n‖ ∧
      ‖R n‖ ≤ C * odometerMaxFluctuation q ω (l n) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
    (s := Set.Icc (0 : ℝ) 1)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨1 / (K + 1), 4, by positivity, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim (1 / 4) (by norm_num)] with n hn
  have hpos := norm_pos_iff.mpr (hR n)
  have est (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      |‖curve q t‖ - ‖fluct q ω (l n) t‖ / ‖R n‖| < 1 / 4 := by
    have := (abs_norm_sub_norm_le _ _).trans_lt (show
        ‖-curve q t - fluct q ω (l n) t / R n‖ < 1 / 4 from by
      simpa only [dist_eq_norm] using hn t ht)
    simpa only [norm_neg, norm_div] using this
  have ub (t : Set.Icc (0 : ℝ) 1) : ‖fluct q ω (l n) t‖ ≤ (K + 1) * ‖R n‖ := by
    apply (div_le_iff₀ hpos).mp
    linarith [(abs_lt.mp (est t t.2)).1, hK t t.2]
  let mid : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩
  have lb := (abs_lt.mp (est mid mid.2)).2
  have hv : ‖curve q mid‖ = 1 / 2 := by
    change ‖takagiLandsberg _ (1 / 2)‖ = _
    rw [takagi_half, norm_div, norm_one]
    norm_num
  have low : 1 / 4 * ‖R n‖ ≤ ‖fluct q ω (l n) mid‖ := (le_div_iff₀ hpos).mp (by linarith)
  have hm : ‖fluct q ω (l n) mid‖ ≤ odometerMaxFluctuation q ω (l n) :=
    le_ciSup (f := fun t : Set.Icc (0 : ℝ) 1 => ‖fluct q ω (l n) t‖)
      ⟨_, Set.forall_mem_range.mpr ub⟩ mid
  constructor
  · rw [one_div, inv_mul_le_iff₀ (by positivity : 0 < K + 1)]
    exact ciSup_le ub
  · linarith

private lemma stabilize (q : ℂ) (hq : 1 / 2 < ‖q‖) (hq1 : ‖q‖ < 1)
    (ω : ℕ → Fin 2) (hω : ∀ k : ℕ, ∃ b : ℕ, ∀ i < k, ω (i + b) = 0) :
    ∃ (l : ℕ → ℕ) (R : ℕ → ℂ), IsStabilizingSeq q ω l R (fun t => -curve q t) := by
  choose b hb using hω
  let m (n : ℕ) := b (n + 1) + (n + 1)
  let l (n : ℕ) := 2 ^ m n - prefixValue ω (m n)
  have small (n : ℕ) : prefixValue ω (m n) < 2 ^ b (n + 1) := by
    dsimp only [m]
    rw [prefix_zero_block ω _ _ (hb _)]
    exact prefix_lt _ _
  have ends (n : ℕ) : prefixValue ω (m n) + l n = 2 ^ m n :=
    Nat.add_sub_of_le (prefix_lt ω _).le
  have len (n : ℕ) : n + 1 ≤ l n := by
    have hd := small n
    have H := ends n
    dsimp only [m] at H
    rw [pow_add, pow_succ 2 n] at H
    have hp : 1 ≤ 2 ^ b (n + 1) := Nat.one_le_two_pow
    have hn := Nat.lt_two_pow_self (n := n)
    have hprod := Nat.mul_le_mul_right (2 ^ n) hp
    have hprod' := Nat.mul_le_mul_left (2 ^ b (n + 1)) (Nat.one_le_two_pow (n := n))
    simp only [one_mul, mul_one] at hprod hprod'
    nlinarith
  have lm : Tendsto m atTop atTop := tendsto_atTop_mono (fun n => show n ≤ m n by dsimp [m]; omega)
    tendsto_id
  have hl : Tendsto l atTop atTop := tendsto_atTop_mono (fun n => (Nat.le_succ n).trans (len n))
    tendsto_id
  have hq0 : q ≠ 0 := by rintro rfl; norm_num at hq
  have h2q : 1 < ‖2 * q‖ := by rw [norm_mul]; norm_num; linarith
  have hc : Continuous (curve q) := takagi_continuous (by
    rw [norm_div, norm_one, div_lt_one (by linarith)]; exact h2q)
  have hR (n : ℕ) : scale q (m n) ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero hq0)) two_ne_zero
  have growth : Tendsto (fun n => ‖scale q (m n)‖) atTop atTop := by
    have h := ((tendsto_pow_atTop_atTop_of_one_lt h2q).comp lm).atTop_mul_const
      (by norm_num : 0 < (2 : ℝ)⁻¹)
    simpa [scale, norm_mul, div_eq_mul_inv, Function.comp_def] using h
  have mesh (n : ℕ) : ((prefixValue ω (m n) : ℝ) + 1) / 2 ^ m n ≤ (1 / 2 : ℝ) ^ (n + 1) := by
    have hd : (prefixValue ω (m n) : ℝ) + 1 ≤ 2 ^ b (n + 1) := by exact_mod_cast small n
    dsimp only [m]
    rw [div_le_iff₀ (by positivity), pow_add, div_pow, one_pow]
    apply hd.trans_eq
    field_simp
    rw [pow_add, pow_succ _ n, mul_assoc]
  have conv : TendstoUniformlyOn (fun n t => fluct q ω (l n) t / scale q (m n))
      (fun t => -curve q t) atTop (Set.Icc 0 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn) (ε / 3) (by positivity)
    have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).comp (tendsto_add_atTop_nat 1)
    filter_upwards [hpow.eventually_lt_const hδ] with n hn
    exact close_fluct q hq hq1 ω _ _ (ends n) (by have := len n; omega) hε
      (lt_of_le_of_lt (mesh n) hn) hmod
  exact ⟨l, fun n => scale q (m n), fun n => by have := len n; omega, hl, hR, growth,
    comparable q ω l _ hR hc conv, hc.neg.continuousOn, conv⟩

end odometer_limitingCurve_eq_neg_takagi

/-- **Odometer limiting curve is the negative Takagi–Landsberg function.** Let $q \in \mathbb{C}$
with $1/2 < |q| < 1$ and put $a = 1/(2q)$. Then for almost every dyadic integer $\omega$ with
respect to the Haar measure on $\mathbb{Z}_2$ there are a sequence $(l_n)$ of natural numbers and
a sequence $(R_n)$ of complex numbers such that $(l_n)$ is a stabilizing sequence for
$(q, \omega)$ with normalizing sequence $(R_n)$ and limiting curve $t \mapsto -\mathcal{T}_a(t)$,
where $\mathcal{T}_a$ is the Takagi–Landsberg function. In particular, with $S_{q,\omega}$ the
interpolated odometer partial sums, the normalized fluctuations
$(S_{q,\omega}(t l_n) - t S_{q,\omega}(l_n))/R_n$ converge uniformly on $[0, 1]$ to
$-\mathcal{T}_a(t)$.

This is Theorem 2 of the source, which quotes it from the author's earlier work, with the
normalizing sequence $(R_n)$ of the order of the maximal fluctuation $M_{q,\omega}(l_n)$, as in
`IsStabilizingSeq`, not equal to it. Section 4 of the source normalizes by that maximum itself,
but then every normalized fluctuation has supremum norm at most $1$, and so would the limit,
while $-\mathcal{T}_a$ can exceed $1$ in absolute value: for $q = 2/3$, so $a = 3/4$,
$\mathcal{T}_{3/4}(1/3) = 4/3$.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Theorem 2 (`integers-2026-A61-thm-2`). -/
public theorem odometer_limitingCurve_eq_neg_takagi (q : ℂ) (hq : 1 / 2 < ‖q‖)
    (hq1 : ‖q‖ < 1) :
    ∀ᵐ ω ∂dyadicHaar, ∃ (l : ℕ → ℕ) (R : ℕ → ℂ),
      IsStabilizingSeq q ω l R (fun t => -takagiLandsberg (1 / (2 * q)) t) := by
  filter_upwards [odometer_limitingCurve_eq_neg_takagi.ae_zero_blocks] with ω hω
  exact odometer_limitingCurve_eq_neg_takagi.stabilize q hq hq1 ω hω

end

end MetaMathlibExt
