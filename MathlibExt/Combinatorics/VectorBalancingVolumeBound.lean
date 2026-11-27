/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Banaszczyk's volume bound is not an upper bound for vector balancing

AimPL, Hereditary discrepancy and factorization norms, Section 1, Problem 1.5 (Vector balancing):
for norms `X, Y` on `ℝ^d`, `α(X, Y, d)` is the supremum, over `n` and vectors `v₁, …, vₙ` with
`‖vᵢ‖_X ≤ 1`, of the least `‖∑ εᵢ vᵢ‖_Y` over signs `εᵢ = ±1`. Banaszczyk proved
`α(X, Y, d) ≥ √d (vol B_X / vol B_Y)^{1/d}`, and the problem asks whether this lower bound is also
an upper bound for `α(X, Y, d)` up to `log d` factors.

S. Nikolov's remark on the problem shows that it is not: for `X = Y = ℓ₁^d` the volume bound is
`√d`, while every signing of the standard basis vectors `e₁, …, e_d` has `ℓ₁` norm `d`, and
`√d` is not bounded by a polylogarithmic factor in `d` (`(log d)^c = o(√d)`, from
`isLittleO_log_rpow_rpow_atTop`). Taking `X = Y` makes the volume ratio `1`, so no volume has to
be computed.

## Main declarations

* `volumeBoundIsUpperBound`: the volume bound is an upper bound up to a factor `C (log d)^c`.
* `l1Seminorm`: the `ℓ₁` norm `x ↦ ∑ i, |x i|` on `EuclideanSpace ℝ ι`, as a seminorm;
  `l1Seminorm_eq_zero_iff`: it is a norm.
* `l1Seminorm_sum_smul_single`: every signing of the standard basis has `ℓ₁` norm `card ι`.
* `volumeBoundIsUpperBound_refuted`: the volume bound is not such an upper bound.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.VectorBalancingVolumeBoundAIMCombinatoricsProblem42Wanted

/-!
Source: AimPL: Hereditary discrepancy and factorization norms, Section 1, Problem 1.5 (Vector
balancing), http://aimpl.org/hereddiscrep/1/. UnsolvedMath record UM-20000917
(`AIM-COMBINATORICS-0042`), dataset ulamai/UnsolvedMath v1.8.0.

'Up to log d factors' is read as up to a factor `C (log d)^c` with constants `C, c`, for `d ≥ 2` (at
`d = 1` the factor `log d` vanishes). Norms are definite seminorms on `EuclideanSpace ℝ (Fin d)`;
volumes are Lebesgue measures of the closed unit balls (finite and positive for norms). `α(X, Y, d)
≤ B` is stated as: every family `v₁, …, vₙ` with `X(vᵢ) ≤ 1` has signs with `Y(∑ εᵢ vᵢ) ≤ B` (the
least value over the finitely many signings is attained). The page's remark also proposes a
stronger, ellipsoid-based lower bound that may be an upper bound up to logarithmic factors; that
conjecture is not formalized here.
-/

open MeasureTheory

/-- **Banaszczyk's volume bound as an upper bound for vector balancing (statement).** This is the
proposition that there are real constants $C$ and $c$ such that for every natural number $d \ge 2$,
all norms $X$ and $Y$ on $\mathbb{R}^d$, every natural number $n$ and all vectors
$v_1, \dots, v_n \in \mathbb{R}^d$ with $X(v_i) \le 1$ for every $i$, there are signs
$\varepsilon_1, \dots, \varepsilon_n \in \{1, -1\}$ such that
$Y(\varepsilon_1 v_1 + \dots + \varepsilon_n v_n)$ is at most
$C (\log d)^c \sqrt{d} \, (\mathrm{vol}(B_X) / \mathrm{vol}(B_Y))^{1/d}$, where
$B_X = \{x : X(x) \le 1\}$ and $B_Y = \{x : Y(x) \le 1\}$ are the closed unit balls and
$\mathrm{vol}$ is Lebesgue measure.

Banaszczyk proved that $\sqrt{d} \, (\mathrm{vol}(B_X) / \mathrm{vol}(B_Y))^{1/d}$ is a lower bound
for the vector balancing constant of $X$ and $Y$; the AimPL question asks whether it is also an
upper bound up to polylogarithmic factors in $d$. -/
def volumeBoundIsUpperBound : Prop :=
  ∃ C c : ℝ, ∀ d : ℕ, 2 ≤ d → ∀ X Y : Seminorm ℝ (EuclideanSpace ℝ (Fin d)),
    (∀ x, X x = 0 → x = 0) → (∀ x, Y x = 0 → x = 0) →
    ∀ (n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)), (∀ i, X (v i) ≤ 1) →
      ∃ ε : Fin n → ℤˣ, Y (∑ i, ((ε i : ℤ) : ℝ) • v i) ≤
        C * Real.log d ^ c * Real.sqrt d *
          ((volume {x | X x ≤ 1}).toReal / (volume {x | Y x ≤ 1}).toReal) ^ ((1 : ℝ) / d)

section L1

variable (ι : Type*) [Fintype ι]

/-- For a finite index set $\iota$, the $\ell_1$ seminorm on $\mathbb R^\iota$ is
$x \mapsto \sum_{i\in\iota}|x_i|$. -/
noncomputable def l1Seminorm : Seminorm ℝ (EuclideanSpace ℝ ι) :=
  Seminorm.of (fun x => ∑ i, |x i|)
    (fun x y => (Finset.sum_le_sum fun i _ => abs_add_le (x i) (y i)).trans_eq
      Finset.sum_add_distrib)
    (fun a x => by simp [abs_mul, Finset.mul_sum])

variable {ι}

@[simp]
theorem l1Seminorm_apply (x : EuclideanSpace ℝ ι) : l1Seminorm ι x = ∑ i, |x i| := rfl

/-- The `ℓ₁` seminorm is a norm: it vanishes only at `0`. -/
theorem l1Seminorm_eq_zero_iff {x : EuclideanSpace ℝ ι} : l1Seminorm ι x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ map_zero _⟩
  rw [l1Seminorm_apply, Finset.sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg _] at h
  ext i
  simpa using h i (Finset.mem_univ i)

/-- The `ℓ₁` norm of `a • eᵢ` is `|a|`. -/
theorem l1Seminorm_single [DecidableEq ι] (i : ι) (a : ℝ) :
    l1Seminorm ι (EuclideanSpace.single i a) = |a| := by
  rw [l1Seminorm_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- For a finite index set $\iota$ and signs $\varepsilon_i\in\{-1,1\}$, the signed sum of
the standard basis vectors of $\mathbb R^\iota$ satisfies
$\bigl\|\sum_{i\in\iota}\varepsilon_i e_i\bigr\|_1=|\iota|$. -/
theorem l1Seminorm_sum_smul_single [DecidableEq ι] (ε : ι → ℤˣ) :
    l1Seminorm ι (∑ i, ((ε i : ℤ) : ℝ) • EuclideanSpace.single i (1 : ℝ)) = Fintype.card ι := by
  have hcoord (j : ι) : (∑ i, ((ε i : ℤ) : ℝ) • EuclideanSpace.single i (1 : ℝ)) j =
      ((ε j : ℤ) : ℝ) := by
    simp [Finset.sum_apply, Pi.single_apply]
  simp only [l1Seminorm_apply, hcoord]
  have habs (j : ι) : |((ε j : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (ε j) with h | h <;> simp [h]
  simp [habs]

end L1

/-- For all real constants `K` and `c` there is a natural number `d ≥ 2` with
`K (log d)^c √d < d`: the factor `√d` is not bounded by a polylogarithmic factor in `d`. -/
private theorem exists_mul_log_rpow_mul_sqrt_lt (K c : ℝ) :
    ∃ d : ℕ, 2 ≤ d ∧ K * Real.log d ^ c * Real.sqrt d < d := by
  have hε : (0 : ℝ) < 1 / (|K| + 1) := by positivity
  have h := ((isLittleO_log_rpow_rpow_atTop c (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
    tendsto_natCast_atTop_atTop).def hε
  obtain ⟨d, hd, h2⟩ := (h.and (Filter.eventually_ge_atTop 2)).exists
  refine ⟨d, h2, ?_⟩
  have hd0 : (0 : ℝ) < d := by positivity
  have hlog : 0 < Real.log d := Real.log_pos (by exact_mod_cast h2)
  have hL : Real.log d ^ c ≤ 1 / (|K| + 1) * Real.sqrt d := by
    simpa [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hlog c), Real.sqrt_eq_rpow,
      abs_of_nonneg (Real.rpow_nonneg hd0.le _)] using hd
  calc K * Real.log d ^ c * Real.sqrt d ≤ |K| * Real.log d ^ c * Real.sqrt d := by
        gcongr
        exact le_abs_self K
    _ ≤ |K| * (1 / (|K| + 1) * Real.sqrt d) * Real.sqrt d := by gcongr
    _ = |K| / (|K| + 1) * (Real.sqrt d * Real.sqrt d) := by ring
    _ = |K| / (|K| + 1) * d := by rw [Real.mul_self_sqrt hd0.le]
    _ < 1 * d := by
        gcongr
        rw [div_lt_one (by positivity)]
        linarith
    _ = d := one_mul _

/--
**Banaszczyk's volume bound is not an upper bound for vector balancing.** There are no real
constants $C$ and $c$ such that for every natural number $d \ge 2$, all norms $X$ and $Y$ on
$\mathbb{R}^d$, every natural number $n$ and all vectors $v_1, \dots, v_n \in \mathbb{R}^d$ with
$X(v_i) \le 1$ for every $i$, there are signs $\varepsilon_1, \dots, \varepsilon_n \in \{1, -1\}$
such that $Y(\varepsilon_1 v_1 + \dots + \varepsilon_n v_n)$ is at most
$C (\log d)^c \sqrt{d} \, (\mathrm{vol}(B_X) / \mathrm{vol}(B_Y))^{1/d}$, where
$B_X = \{x : X(x) \le 1\}$ and $B_Y = \{x : Y(x) \le 1\}$ are the closed unit balls and
$\mathrm{vol}$ is Lebesgue measure.

S. Nikolov's remark on the problem gives the counterexample $X = Y = \ell_1^d$ with the standard
basis vectors $e_1, \dots, e_d$: the volume bound is $\sqrt{d}$, while every choice of signs gives
$\|\pm e_1 \pm \dots \pm e_d\|_1 = d$, and a factor $\sqrt{d}$ is not polylogarithmic in $d$.

Source: AimPL: Hereditary discrepancy and factorization norms, Section 1,
Problem 1.5 (Vector balancing), http://aimpl.org/hereddiscrep/1/; resolution: AimPL: Hereditary
discrepancy and factorization norms, remark by S. Nikolov to Problem 1.5, remark: 'In fact, this
lower bound can be too small by a factor of √d, for example when X = Y = ℓ_1^d' (for X = Y the
volume bound is √d, while for the standard basis e_1, ..., e_d every signing has ‖∑ ±e_i‖_1 = d),
http://aimpl.org/hereddiscrep/1/.
-/
theorem volumeBoundIsUpperBound_refuted : ¬ volumeBoundIsUpperBound := by
  rintro ⟨C, c, h⟩
  obtain ⟨d, hd, hlt⟩ := exists_mul_log_rpow_mul_sqrt_lt |C| c
  obtain ⟨ε, hε⟩ := h d hd (l1Seminorm (Fin d)) (l1Seminorm (Fin d))
    (fun _ => l1Seminorm_eq_zero_iff.mp) (fun _ => l1Seminorm_eq_zero_iff.mp) d
    (fun i => EuclideanSpace.single i 1) (fun i => by rw [l1Seminorm_single, abs_one])
  rw [l1Seminorm_sum_smul_single, Fintype.card_fin] at hε
  -- Since `X = Y`, the volume ratio is `a / a ≤ 1`, whatever the volume `a` is.
  set a := (volume {x | l1Seminorm (Fin d) x ≤ 1}).toReal
  have ha : 0 ≤ a / a := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hr : (a / a) ^ ((1 : ℝ) / d) ≤ 1 :=
    Real.rpow_le_one ha (div_self_le_one a) (by positivity)
  have hbound : C * Real.log d ^ c * Real.sqrt d * (a / a) ^ ((1 : ℝ) / d) ≤
      |C| * Real.log d ^ c * Real.sqrt d :=
    calc C * Real.log d ^ c * Real.sqrt d * (a / a) ^ ((1 : ℝ) / d)
        ≤ |C| * Real.log d ^ c * Real.sqrt d * (a / a) ^ ((1 : ℝ) / d) := by
          gcongr
          exact le_abs_self C
      _ ≤ |C| * Real.log d ^ c * Real.sqrt d * 1 := by gcongr
      _ = |C| * Real.log d ^ c * Real.sqrt d := mul_one _
  linarith

end MathlibExt.Combinatorics.VectorBalancingVolumeBoundAIMCombinatoricsProblem42Wanted
