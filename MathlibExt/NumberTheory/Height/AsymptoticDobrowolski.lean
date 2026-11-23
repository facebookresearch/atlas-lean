/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Height.PrimitiveMahler
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.EReal.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Asymptotic Dobrowolski coefficients

The catalogue's C40b is the supremum of coefficients valid uniformly for all sufficiently large
degrees. Voutier, arXiv:1211.3110v1, Introduction, supplies the polynomial and Mahler-measure
conventions. No finite upper bound or attainment of the supremum is assumed.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.AsymptoticDobrowolski

open NumberField

/-- **Dobrowolski scale.** For a natural number $d$, the Dobrowolski scale is
$$\left(\frac{\log \log d}{\log d}\right)^3,$$
with natural logarithms and the conventions $\log 0 = 0$ and $x / 0 = 0$, so that it is $0$ for
$d \le 1$.

It is used only for degrees $d \ge 3$ in the definition of asymptotic Dobrowolski coefficients. -/
noncomputable def dobrowolskiScale (d : ℕ) : ℝ :=
  (Real.log (Real.log d) / Real.log d) ^ 3

/-- **Positivity of the Dobrowolski scale.** For every natural number $d \ge 3$, the Dobrowolski
scale $\left(\frac{\log \log d}{\log d}\right)^3$ is strictly positive. -/
theorem dobrowolskiScale_pos {d : ℕ} (hd : 3 ≤ d) : 0 < dobrowolskiScale d := by
  have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 1 < Real.log d :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (Real.exp_one_lt_three.trans_le hdreal)
  exact pow_pos (div_pos (Real.log_pos hlog) (zero_lt_one.trans hlog)) 3

/-- **Asymptotic Dobrowolski coefficients.** A real number $c$ is an asymptotic Dobrowolski
coefficient if for every $\varepsilon > 0$ there is a natural number $D \ge 3$ such that every
nonzero algebraic number $\alpha \in \mathbb{C}$ that is not a root of unity and whose minimal
polynomial over $\mathbb{Q}$ has degree $d \ge D$ satisfies
$$1 + (c - \varepsilon) \left(\frac{\log \log d}{\log d}\right)^3 \le M(\alpha),$$
where $M(\alpha)$ is the Mahler measure of $\alpha$.

The degree threshold $D$ may depend on $\varepsilon$ but is uniform over all such $\alpha$. -/
def IsAsymptoticDobrowolskiCoefficient (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, 3 ≤ D ∧
    ∀ α : ℂ, IsAlgebraic ℚ α → α ≠ 0 → ¬IsOfFinOrder α →
      D ≤ (minpoly ℚ α).natDegree →
        1 + (c - ε) * dobrowolskiScale (minpoly ℚ α).natDegree ≤
          algebraicMahlerMeasure α

/-- **Asymptotic Dobrowolski constant.** The asymptotic Dobrowolski constant is the supremum, in
the extended real numbers $[-\infty, +\infty]$, of the set of all real asymptotic Dobrowolski
coefficients.

The supremum would be $-\infty$ if there were no coefficient and is $+\infty$ if the coefficients
are unbounded above; neither attainment nor a finite upper bound is assumed. -/
noncomputable def asymptoticDobrowolskiConstant : EReal :=
  sSup {x : EReal | ∃ c : ℝ, IsAsymptoticDobrowolskiCoefficient c ∧ x = c}

/-- **Coefficients are bounded by the asymptotic Dobrowolski constant.** Every real asymptotic
Dobrowolski coefficient $c$ satisfies $c \le$ the asymptotic Dobrowolski constant, as extended
real numbers. -/
theorem coe_le_asymptoticDobrowolskiConstant {c : ℝ}
    (hc : IsAsymptoticDobrowolskiCoefficient c) :
    (c : EReal) ≤ asymptoticDobrowolskiConstant :=
  le_sSup ⟨c, hc, rfl⟩

/-- **Zero is an asymptotic Dobrowolski coefficient.** The real number $0$ is an asymptotic
Dobrowolski coefficient: for every real $\varepsilon > 0$ there is a natural number $D \ge 3$
such that every nonzero algebraic number $\alpha \in \mathbb{C}$ that is not a root of unity and
whose minimal polynomial over $\mathbb{Q}$ has degree $d \ge D$ satisfies
$1 - \varepsilon \left(\frac{\log \log d}{\log d}\right)^3 \le M(\alpha)$, where $M(\alpha)$ is the
Mahler measure of the primitive integer minimal polynomial of $\alpha$ with positive leading
coefficient. -/
theorem zero_isAsymptoticDobrowolskiCoefficient : IsAsymptoticDobrowolskiCoefficient 0 := by
  intro ε hε
  refine ⟨3, le_rfl, ?_⟩
  intro α _ _ _ hd
  have hscale := (dobrowolskiScale_pos hd).le
  have hmul : (0 - ε) * dobrowolskiScale (minpoly ℚ α).natDegree ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hscale
  exact le_trans (by linarith) (one_le_algebraicMahlerMeasure α)

/-- **Upper bounds for the asymptotic Dobrowolski constant.** For every extended real number $b$,
the asymptotic Dobrowolski constant is at most $b$ if and only if every real asymptotic
Dobrowolski coefficient $c$ satisfies $c \le b$. -/
theorem asymptoticDobrowolskiConstant_le_iff {b : EReal} :
    asymptoticDobrowolskiConstant ≤ b ↔
      ∀ c : ℝ, IsAsymptoticDobrowolskiCoefficient c → (c : EReal) ≤ b := by
  constructor
  · intro hb c hc
    exact (coe_le_asymptoticDobrowolskiConstant hc).trans hb
  · intro hb
    apply sSup_le
    rintro x ⟨c, hc, rfl⟩
    exact hb c hc

/-- **Coefficients are exactly the reals below the constant.** A real number $c$ is an asymptotic
Dobrowolski coefficient if and only if $c$ is at most the asymptotic Dobrowolski constant, as
extended real numbers.

The $\varepsilon$ in the definition makes the set of coefficients closed, so a finite constant is
itself a coefficient; this also covers the case where the coefficients are unbounded above. -/
theorem isAsymptoticDobrowolskiCoefficient_iff {c : ℝ} :
    IsAsymptoticDobrowolskiCoefficient c ↔ (c : EReal) ≤ asymptoticDobrowolskiConstant := by
  refine ⟨coe_le_asymptoticDobrowolskiConstant, ?_⟩
  intro hc ε hε
  have hslack : ((c - ε / 2 : ℝ) : EReal) < (c : EReal) := by
    exact_mod_cast (show c - ε / 2 < c by linarith)
  have hbelow : ((c - ε / 2 : ℝ) : EReal) < asymptoticDobrowolskiConstant :=
    hslack.trans_le hc
  obtain ⟨x, ⟨b, hb, rfl⟩, hxb⟩ := lt_sSup_iff.mp hbelow
  have hcb : c - ε / 2 < b := by exact_mod_cast hxb
  obtain ⟨D, hD, hbound⟩ := hb (ε / 2) (half_pos hε)
  refine ⟨D, hD, ?_⟩
  intro α hα hα0 hroot hd
  have hscale := (dobrowolskiScale_pos (hD.trans hd)).le
  have hcoef : c - ε ≤ b - ε / 2 := by linarith
  linarith [mul_le_mul_of_nonneg_right hcoef hscale, hbound α hα hα0 hroot hd]

/-- **Strict form of asymptotic Dobrowolski coefficients.** A real number $c$ is an asymptotic
Dobrowolski coefficient if and only if for every $\varepsilon > 0$ there is a natural number
$D \ge 3$ such that every nonzero algebraic number $\alpha \in \mathbb{C}$ that is not a root of
unity and whose minimal polynomial over $\mathbb{Q}$ has degree $d \ge D$ satisfies
$$1 + (c - \varepsilon) \left(\frac{\log \log d}{\log d}\right)^3 < M(\alpha),$$
where $M(\alpha)$ is the Mahler measure of $\alpha$.

So the strict bounds are equivalent to the non-strict bounds in the definition. -/
theorem isAsymptoticDobrowolskiCoefficient_iff_strict {c : ℝ} :
    IsAsymptoticDobrowolskiCoefficient c ↔
      ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, 3 ≤ D ∧
        ∀ α : ℂ, IsAlgebraic ℚ α → α ≠ 0 → ¬IsOfFinOrder α →
          D ≤ (minpoly ℚ α).natDegree →
            1 + (c - ε) * dobrowolskiScale (minpoly ℚ α).natDegree <
              algebraicMahlerMeasure α := by
  constructor
  · intro hc ε hε
    obtain ⟨D, hD, hbound⟩ := hc (ε / 2) (half_pos hε)
    refine ⟨D, hD, ?_⟩
    intro α hα hα0 hroot hd
    have hscale := dobrowolskiScale_pos (hD.trans hd)
    have hmul := mul_lt_mul_of_pos_right (show c - ε < c - ε / 2 by linarith) hscale
    linarith [hbound α hα hα0 hroot hd]
  · intro hc ε hε
    obtain ⟨D, hD, hbound⟩ := hc ε hε
    exact ⟨D, hD, fun α hα hα0 hroot hd => (hbound α hα hα0 hroot hd).le⟩

/-- **The asymptotic Dobrowolski constant is nonnegative.** The asymptotic Dobrowolski constant
is at least $0$.

The bound comes from the coefficient $0$, which is an asymptotic Dobrowolski coefficient because
every Mahler measure is at least $1$. -/
theorem asymptoticDobrowolskiConstant_nonneg : 0 ≤ asymptoticDobrowolskiConstant :=
  coe_le_asymptoticDobrowolskiConstant zero_isAsymptoticDobrowolskiCoefficient

/-- **Trivial upper bound for the asymptotic Dobrowolski constant.** The asymptotic Dobrowolski
constant is at most $+\infty$.

This is only the trivial bound in the extended reals, not a finite estimate. -/
theorem asymptoticDobrowolskiConstant_le_top : asymptoticDobrowolskiConstant ≤ ⊤ :=
  le_top

end MathlibExt.NumberTheory.AsymptoticDobrowolski
