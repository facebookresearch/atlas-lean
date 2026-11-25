/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Probability.ProbabilityMassFunction.Uniform
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import MathlibExt.NumberTheory.Digits.DyadicMantissa
public import MathlibExt.NumberTheory.Digits.QWeightedTrollopeDelange

namespace MetaMathlibExt

@[expose] public section

open Finset

-- The definitions `qWeightedDigitSum`, `qWeightedDigitPartialSum` and `takagiLandsberg`, with
-- their lemmas `qWeightedDigitSum_zero`, `qWeightedDigitSum_of_pos` and `takagiLandsberg_zero`,
-- moved to `MathlibExt.NumberTheory.Digits.QWeightedTrollopeDelange`, which this module imports.
-- The dyadic fluctuation identity and the q-weighted Trollope–Delange formula are proved there.

-- Girgensohn's lemma, `dyadicMantissa_wellDefined_iff_doubling_invariant`, is proved in
-- `MathlibExt.NumberTheory.Digits.DyadicMantissa`, which this module imports.

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

/-- **Odometer limiting curve is the negative Takagi–Landsberg function.** Let $q \in \mathbb{C}$
with $1/2 < |q| < 1$ and put $a = 1/(2q)$. Then for almost every dyadic integer $\omega$ with
respect to the Haar measure on $\mathbb{Z}_2$ there are a sequence $(l_n)$ of natural numbers and
a sequence $(R_n)$ of complex numbers such that $(l_n)$ is a stabilizing sequence for
$(q, \omega)$ with normalizing sequence $(R_n)$ and limiting curve $t \mapsto -\mathcal{T}_a(t)$,
where $\mathcal{T}_a$ is the Takagi–Landsberg function. In particular, with $S_{q,\omega}$ the
interpolated odometer partial sums, the normalized fluctuations
$(S_{q,\omega}(t l_n) - t S_{q,\omega}(l_n))/R_n$ converge uniformly on $[0, 1]$ to
$-\mathcal{T}_a(t)$.

This is Theorem 2 of the source, which quotes it from the author's earlier work.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Theorem 2 (`integers-2026-A61-thm-2`). -/
public theorem_wanted odometer_limitingCurve_eq_neg_takagi (q : ℂ) (hq : 1 / 2 < ‖q‖)
    (hq1 : ‖q‖ < 1) :
    ∀ᵐ ω ∂dyadicHaar, ∃ (l : ℕ → ℕ) (R : ℕ → ℂ),
      IsStabilizingSeq q ω l R (fun t => -takagiLandsberg (1 / (2 * q)) t)

end

end MetaMathlibExt
