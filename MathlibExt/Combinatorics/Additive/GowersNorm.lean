/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Analysis.Fourier.FiniteAbelianDFT

import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

/-!
# Gowers uniformity norms on a finite abelian group

The Gowers uniformity norms `‖f‖_{U^d}` of a function `f : G → ℂ` on a finite abelian group,
defined through the recursion `‖f‖_{U^0} = 𝔼 f`,
`‖f‖_{U^d}^{2^d} = 𝔼_h ‖Δ_h f‖_{U^{d-1}}^{2^{d-1}}` of Green and Tao, and their basic theory:
the cube-average formula, positivity, monotonicity in `d`, the Gowers–Cauchy–Schwarz and
triangle inequalities, the `U¹` and `U²` cases, the identity `‖f‖_{U²} = ‖f̂‖_{ℓ⁴}`, the `U²`
inverse theorem, and the generalized von Neumann theorem (counting `k`-term progressions is
controlled by `U^{k-1}`), with a separate Fourier-analytic proof for three-term progressions.

## Sources

* [G01] W. T. Gowers, *A new proof of Szemerédi's theorem*, Geom. Funct. Anal. 11 (2001)
  465–588. Numbering is that of the author's preprint `sz898.dvi` at
  https://www.dpmms.cam.ac.uk/~wtg10/papers.html; the journal numbering was not checked.
* [GT08] B. Green and T. Tao, *An inverse theorem for the Gowers `U³(G)` norm*, Proc. Edinb.
  Math. Soc. 51 (2008) 73–153; numbering of arXiv:math/0503014.
* [G10] W. T. Gowers, *Decompositions, approximate structure, transference, and the
  Hahn–Banach theorem*, Bull. London Math. Soc. 42 (2010) 573–606; numbering of
  arXiv:0811.3103.

## Conventions

Averages are expectations `𝔼` over `G`. The repository's Fourier transform is the unnormalised
`dftFun f ψ = ∑ x, ψ x * f x`; the normalised transform of [G10] and [GT08] is
`f̂(ψ) = 𝔼_x f(x) conj (ψ x)`, which equals `|G|⁻¹ * dftFun f ψ⁻¹`. Statements below use
`|G|⁻¹ * dftFun f ψ`; reindexing by `ψ ↦ ψ⁻¹` does not change any sum over the dual group.
The `U³` inverse theorem and Gowers's bound for Szemerédi's theorem are wanted theorems in
`WantedExt.Combinatorics.Additive.GowersUniformityWanted`.
-/

@[expose] public section

open scoped BigOperators ComplexConjugate
open Finset

namespace MathlibExt.Combinatorics.Additive.GowersNorm

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- **Multiplicative derivative.** `mulDeriv h f x = f x * conj (f (x + h))`. This is the
difference function `Δ(f; k)(s) = f(s) conj f(s - k)` of Gowers [G01, §3] with `k = -h`, and
the function `T^h f · conj f` of Green and Tao [GT08, (1.1)] up to complex conjugation;
neither change affects the Gowers norms built from it. -/
def mulDeriv (h : G) (f : G → ℂ) : G → ℂ := fun x => f x * conj (f (x + h))

/-- **Gowers uniformity norm, raised to the power `2 ^ d`.** For `f : G → ℂ` on a finite
abelian group, `gowersPow 0 f = 𝔼 x, f x` and
`gowersPow (d + 1) f = 𝔼 h, gowersPow d (mulDeriv h f)`. This is the recursive formula (1.1)
of Green and Tao [GT08], which they state as equivalent to the cube average
`𝔼_{x, h} ∏_{ω ∈ {0,1}^d} C^{|ω|} f(x + ω · h)` of their Definition 1.6; that equivalence is
proved as `gowersPow_eq_cubeAverage`. For `d ≥ 1` the value is a nonnegative real number
(`gowersPow_succ_re_nonneg`). -/
noncomputable def gowersPow : ℕ → (G → ℂ) → ℂ
  | 0, f => 𝔼 x, f x
  | d + 1, f => 𝔼 h, gowersPow d (mulDeriv h f)

/-- **Gowers uniformity norm.** `gowersNorm d f = ‖gowersPow d f‖ ^ (1 / 2 ^ d)`. For `d ≥ 1`
this is the `U^d(G)` norm of Green and Tao [GT08, Definition 1.6 and (1.1)], and Gowers's
`‖f‖_d` [G01, Lemma 3.9] divided by `|G| ^ ((d + 1) / 2 ^ d)` (Gowers sums where we average).
For `d = 0` it is `|𝔼 f|`, the modulus of Green and Tao's complex number `‖f‖_{U^0} = 𝔼 f`.
`U¹` is only a seminorm (`gowersNorm_one`); `U^d` is a norm for `d ≥ 2` [G01, Lemma 3.9]
(triangle inequality: `gowersNorm_add_le`). -/
noncomputable def gowersNorm (d : ℕ) (f : G → ℂ) : ℝ :=
  ‖gowersPow d f‖ ^ ((1 : ℝ) / 2 ^ d)

theorem gowersPow_zero (f : G → ℂ) : gowersPow 0 f = 𝔼 x, f x := rfl

theorem gowersPow_succ (d : ℕ) (f : G → ℂ) :
    gowersPow (d + 1) f = 𝔼 h, gowersPow d (mulDeriv h f) := rfl

/-- **The `U¹` power is the squared modulus of the mean.** `gowersPow 1 f = |𝔼 f| ^ 2`, the
case `d = 1` of the recursion (1.1) of Green and Tao [GT08]. -/
theorem gowersPow_one (f : G → ℂ) :
    gowersPow 1 f = ((‖𝔼 x, f x‖ ^ 2 : ℝ) : ℂ) := by
  have hshift : ∀ x : G, (𝔼 h, f (x + h)) = 𝔼 h, f h := fun x =>
    Fintype.expect_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
  calc gowersPow 1 f = 𝔼 h, 𝔼 x, f x * conj (f (x + h)) := rfl
    _ = 𝔼 x, 𝔼 h, f x * conj (f (x + h)) := Finset.expect_comm _ _ _
    _ = 𝔼 x, f x * conj (𝔼 h, f (x + h)) := by
        refine Finset.expect_congr rfl fun x _ => ?_
        rw [← Finset.mul_expect]
        congr 1
        simp only [Fintype.expect_eq_sum_div_card, map_div₀, map_sum, map_natCast]
    _ = 𝔼 x, f x * conj (𝔼 h, f h) := by simp_rw [hshift]
    _ = (𝔼 x, f x) * conj (𝔼 h, f h) := by rw [Finset.expect_mul]
    _ = ((‖𝔼 x, f x‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.mul_conj']; push_cast; rfl

/-- **Cauchy–Schwarz step for Gowers powers.** For every `d` and `f`, `gowersPow (d + 1) f` is
real and `‖gowersPow d f‖ ^ 2 ≤ re (gowersPow (d + 1) f)`. By induction on `d` from the
recursion (1.1) of Green and Tao [GT08]: `|𝔼_h a_h|² ≤ 𝔼_h |a_h|²`. This is the argument
behind their monotonicity (1.2). -/
theorem sq_norm_gowersPow_le_and_real (d : ℕ) :
    ∀ f : G → ℂ, ‖gowersPow d f‖ ^ 2 ≤ (gowersPow (d + 1) f).re ∧
      gowersPow (d + 1) f = (((gowersPow (d + 1) f).re : ℝ) : ℂ) := by
  induction d with
  | zero =>
    intro f
    rw [gowersPow_one, gowersPow_zero]
    refine ⟨?_, ?_⟩
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_re]
  | succ d ih =>
    intro f
    set r : G → ℝ := fun h => (gowersPow (d + 1) (mulDeriv h f)).re with hr
    have hreal : gowersPow (d + 2) f = ((𝔼 h, r h : ℝ) : ℂ) := by
      rw [gowersPow_succ, Complex.ofReal_expect]
      exact Finset.expect_congr rfl fun h _ => (ih (mulDeriv h f)).2
    refine ⟨?_, by rw [hreal, Complex.ofReal_re]⟩
    rw [hreal, Complex.ofReal_re, gowersPow_succ]
    calc ‖𝔼 h, gowersPow d (mulDeriv h f)‖ ^ 2
        ≤ (𝔼 h, ‖gowersPow d (mulDeriv h f)‖) ^ 2 := by
          gcongr
          exact RCLike.norm_expect_le (K := ℂ)
      _ = (𝔼 h, ‖gowersPow d (mulDeriv h f)‖ * 1) ^ 2 := by simp
      _ ≤ (𝔼 h, ‖gowersPow d (mulDeriv h f)‖ ^ 2) * 𝔼 h : G, (1 : ℝ) ^ 2 :=
          Finset.expect_mul_sq_le_sq_mul_sq _ _ _
      _ = 𝔼 h, ‖gowersPow d (mulDeriv h f)‖ ^ 2 := by simp
      _ ≤ 𝔼 h, r h := Finset.expect_le_expect fun h _ => (ih (mulDeriv h f)).1

/-- **Gowers powers are nonnegative.** For every `d`, `gowersPow (d + 1) f` has nonnegative real
part (and is real, by `sq_norm_gowersPow_le_and_real`), so the root taken in Definition 1.6 of
Green and Tao [GT08] is that of a nonnegative real number. -/
theorem gowersPow_succ_re_nonneg (d : ℕ) (f : G → ℂ) : 0 ≤ (gowersPow (d + 1) f).re :=
  (sq_nonneg _).trans (sq_norm_gowersPow_le_and_real d f).1

theorem norm_gowersPow_succ (d : ℕ) (f : G → ℂ) :
    ‖gowersPow (d + 1) f‖ = (gowersPow (d + 1) f).re := by
  rw [(sq_norm_gowersPow_le_and_real d f).2, Complex.norm_real, Complex.ofReal_re,
    Real.norm_of_nonneg (gowersPow_succ_re_nonneg d f)]

theorem sq_norm_gowersPow_le (d : ℕ) (f : G → ℂ) :
    ‖gowersPow d f‖ ^ 2 ≤ ‖gowersPow (d + 1) f‖ := by
  rw [norm_gowersPow_succ]
  exact (sq_norm_gowersPow_le_and_real d f).1

/-- **Monotonicity of the Gowers norms.** `‖f‖_{U^d} ≤ ‖f‖_{U^{d+1}}` for every `d`
(Green and Tao [GT08, (1.2)]). Gowers's Lemma 3.4 of [G01] is the same statement in the
language of `α`-uniformity: a function `α`-uniform of degree `d` is `α^{1/2}`-uniform of degree
`d - 1`. With the convention `gowersNorm 0 f = |𝔼 f|` the case `d = 0` is an equality. -/
theorem gowersNorm_le_gowersNorm_succ (d : ℕ) (f : G → ℂ) :
    gowersNorm d f ≤ gowersNorm (d + 1) f := by
  unfold gowersNorm
  have h0 : 0 ≤ ‖gowersPow d f‖ := norm_nonneg _
  have hexp : (1 : ℝ) / 2 ^ d = 2 * ((1 : ℝ) / 2 ^ (d + 1)) := by
    rw [pow_succ]; field_simp
  calc ‖gowersPow d f‖ ^ ((1 : ℝ) / 2 ^ d)
      = (‖gowersPow d f‖ ^ 2) ^ ((1 : ℝ) / 2 ^ (d + 1)) := by
        rw [hexp, Real.rpow_mul h0]; norm_cast
    _ ≤ ‖gowersPow (d + 1) f‖ ^ ((1 : ℝ) / 2 ^ (d + 1)) :=
        Real.rpow_le_rpow (by positivity) (sq_norm_gowersPow_le d f) (by positivity)

theorem gowersNorm_nonneg (d : ℕ) (f : G → ℂ) : 0 ≤ gowersNorm d f := by
  unfold gowersNorm; positivity

/-- **The `U¹` norm is the modulus of the mean.** `‖f‖_{U¹} = |𝔼 f|` (Green and Tao [GT08],
remark after Definition 1.6); in particular `U¹` vanishes on every mean-zero function. -/
theorem gowersNorm_one (f : G → ℂ) : gowersNorm 1 f = ‖𝔼 x, f x‖ := by
  unfold gowersNorm
  rw [gowersPow_one, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (norm_nonneg _)]
  norm_num

/-- **Gowers norms dominate the mean.** `|𝔼 f| ≤ ‖f‖_{U^d}` for every `d ≥ 1`, by
monotonicity from `‖f‖_{U¹} = |𝔼 f|`. For the indicator of a set of density `δ` this is
`‖1_A‖_{U^d} ≥ δ`, the normalised form of Lemma 3.7 of Gowers [G01] (a set of density `δ` in
`ℤ_N` contains at least `δ^{2^d} N^{d+1}` cubes of dimension `d`). -/
theorem norm_expect_le_gowersNorm (f : G → ℂ) {d : ℕ} (hd : 1 ≤ d) :
    ‖𝔼 x, f x‖ ≤ gowersNorm d f := by
  induction d, hd using Nat.le_induction with
  | base => exact (gowersNorm_one f).ge
  | succ d _ ih => exact ih.trans (gowersNorm_le_gowersNorm_succ d f)

/-- **The `U²` power as an average over two-dimensional cubes.**
`gowersPow 2 f = 𝔼_{x, a, b} f(x) conj f(x + a) conj f(x + b) f(x + a + b)`, the case `d = 2`
of the cube average in Definition 1.6 of Green and Tao [GT08], proved here from the recursion.
For the indicator of a set `A` it is `|G|⁻³` times the number of quadruples
`(a, b, c, d) ∈ A⁴` with `a - b = c - d` (Gowers [G01, §2, remark after Lemma 2.1]). -/
theorem gowersPow_two (f : G → ℂ) :
    gowersPow 2 f =
      𝔼 x, 𝔼 a, 𝔼 b, f x * conj (f (x + a)) * conj (f (x + b)) * f (x + a + b) := by
  calc gowersPow 2 f
      = 𝔼 b, 𝔼 a, 𝔼 x, f x * conj (f (x + a)) * conj (f (x + b)) * f (x + a + b) := by
        refine Finset.expect_congr rfl fun b _ => Finset.expect_congr rfl fun a _ =>
          Finset.expect_congr rfl fun x _ => ?_
        simp only [mulDeriv, map_mul, Complex.conj_conj]
        ring
    _ = 𝔼 b, 𝔼 x, 𝔼 a, f x * conj (f (x + a)) * conj (f (x + b)) * f (x + a + b) :=
        Finset.expect_congr rfl fun b _ => Finset.expect_comm _ _ _
    _ = 𝔼 x, 𝔼 b, 𝔼 a, f x * conj (f (x + a)) * conj (f (x + b)) * f (x + a + b) :=
        Finset.expect_comm _ _ _
    _ = 𝔼 x, 𝔼 a, 𝔼 b, f x * conj (f (x + a)) * conj (f (x + b)) * f (x + a + b) :=
        Finset.expect_congr rfl fun x _ => Finset.expect_comm _ _ _

/-- **Gowers `U²` inner product.** For four functions indexed by `{0,1}²`, the average
`gowersInnerTwo f₀₀ f₁₀ f₀₁ f₁₁ = 𝔼_{x,a,b} f₀₀(x) conj f₁₀(x+a) conj f₀₁(x+b) f₁₁(x+a+b)`:
the left-hand side of Gowers's Lemma 3.8 [G01] for `d = 2`, with averages in place of sums and
`+` in place of `-` in the shifts (a change of variables). -/
noncomputable def gowersInnerTwo (f₀₀ f₁₀ f₀₁ f₁₁ : G → ℂ) : ℂ :=
  𝔼 x, 𝔼 a, 𝔼 b, f₀₀ x * conj (f₁₀ (x + a)) * conj (f₀₁ (x + b)) * f₁₁ (x + a + b)

theorem gowersPow_two_eq_gowersInnerTwo (f : G → ℂ) : gowersPow 2 f = gowersInnerTwo f f f f :=
  gowersPow_two f

open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted in
private theorem sum_dftFun_four (fa fb fc fd : G → ℂ) :
    ∑ ψ : AddChar G ℂ, dftFun fa ψ * dftFun fb ψ * conj (dftFun fc ψ) * conj (dftFun fd ψ) =
      ∑ x : G, ∑ y : G, ∑ z : G,
        (Fintype.card G : ℂ) * (fb z * fa (x + y - z) * conj (fd x) * conj (fc y)) := by
  classical
  have hterm : ∀ ψ : AddChar G ℂ,
      dftFun fa ψ * dftFun fb ψ * conj (dftFun fc ψ) * conj (dftFun fd ψ) =
      ∑ x : G, ∑ y : G, ∑ z : G, ∑ w : G,
        ψ (w - (x + y - z)) * (fb z * fa w * conj (fd x) * conj (fc y)) := by
    intro ψ
    simp only [dftFun, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
    rw [show w - (x + y - z) = w + z + -x + -y by abel, AddChar.map_add_eq_mul,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj,
      AddChar.map_neg_eq_conj]
    ring
  simp_rw [hterm]
  calc ∑ ψ : AddChar G ℂ, ∑ x : G, ∑ y : G, ∑ z : G, ∑ w : G,
        ψ (w - (x + y - z)) * (fb z * fa w * conj (fd x) * conj (fc y))
      = ∑ x : G, ∑ y : G, ∑ z : G, ∑ w : G, ∑ ψ : AddChar G ℂ,
          ψ (w - (x + y - z)) * (fb z * fa w * conj (fd x) * conj (fc y)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ x : G, ∑ y : G, ∑ z : G, ∑ w : G,
          (if w = x + y - z then
            (Fintype.card G : ℂ) * (fb z * fa w * conj (fd x) * conj (fc y)) else 0) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
          Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
        rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite]
        simp only [sub_eq_zero, ite_mul, zero_mul]
    _ = ∑ x : G, ∑ y : G, ∑ z : G,
          (Fintype.card G : ℂ) * (fb z * fa (x + y - z) * conj (fd x) * conj (fc y)) := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted in
/-- **Fourier expansion of the Gowers `U²` inner product.**
`|G|⁴ ⟨f₀₀, f₁₀, f₀₁, f₁₁⟩ = ∑_ψ F₁₁(ψ) F₀₀(ψ) conj F₀₁(ψ) conj F₁₀(ψ)` with `F = dftFun` the
repository's unnormalised transform. Proof: expand the four transforms and collapse the sum over
characters by orthogonality, as in the proof of Lemma 2.4 of Gowers [G10]. -/
theorem card_pow_four_mul_gowersInnerTwo (f₀₀ f₁₀ f₀₁ f₁₁ : G → ℂ) :
    (Fintype.card G : ℂ) ^ 4 * gowersInnerTwo f₀₀ f₁₀ f₀₁ f₁₁ =
      ∑ ψ : AddChar G ℂ,
        dftFun f₁₁ ψ * dftFun f₀₀ ψ * conj (dftFun f₀₁ ψ) * conj (dftFun f₁₀ ψ) := by
  classical
  rw [sum_dftFun_four, gowersInnerTwo]
  have hreindex : ∑ z : G, ∑ a : G, ∑ b : G,
        f₀₀ z * conj (f₁₀ (z + a)) * conj (f₀₁ (z + b)) * f₁₁ (z + a + b) =
      ∑ x : G, ∑ y : G, ∑ z : G, f₀₀ z * f₁₁ (x + y - z) * conj (f₁₀ x) * conj (f₀₁ y) := by
    calc ∑ z : G, ∑ a : G, ∑ b : G,
          f₀₀ z * conj (f₁₀ (z + a)) * conj (f₀₁ (z + b)) * f₁₁ (z + a + b)
        = ∑ z : G, ∑ x : G, ∑ y : G, f₀₀ z * f₁₁ (x + y - z) * conj (f₁₀ x) * conj (f₀₁ y) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          refine Fintype.sum_equiv (Equiv.addLeft z) _ _ fun a => ?_
          refine Fintype.sum_equiv (Equiv.addLeft z) _ _ fun b => ?_
          simp only [Equiv.coe_addLeft]
          rw [show z + a + (z + b) - z = z + a + b by abel]
          ring
      _ = ∑ x : G, ∑ z : G, ∑ y : G, f₀₀ z * f₁₁ (x + y - z) * conj (f₁₀ x) * conj (f₀₁ y) :=
          Finset.sum_comm
      _ = ∑ x : G, ∑ y : G, ∑ z : G, f₀₀ z * f₁₁ (x + y - z) * conj (f₁₀ x) * conj (f₀₁ y) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
  simp only [Fintype.expect_eq_sum_div_card, ← Finset.sum_div, ← Finset.mul_sum]
  rw [← hreindex]
  field_simp

open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted in
/-- **Fourth moment of the Fourier transform.** `|G|⁴ ‖f‖_{U²}⁴ = ∑_ψ |dftFun f ψ|⁴`. On
`ℤ_N` with Gowers's unnormalised transform this is identity (6) of [G01, §2]:
`∑_r |Â(r)|⁴` is `N` times the number of additive quadruples in `A`. -/
theorem card_pow_four_mul_gowersPow_two (f : G → ℂ) :
    (Fintype.card G : ℂ) ^ 4 * gowersPow 2 f =
      ∑ ψ : AddChar G ℂ, (((‖dftFun f ψ‖ ^ 4 : ℝ)) : ℂ) := by
  rw [gowersPow_two_eq_gowersInnerTwo, card_pow_four_mul_gowersInnerTwo]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  have := Complex.mul_conj' (dftFun f ψ)
  rw [show ‖dftFun f ψ‖ ^ 4 = (‖dftFun f ψ‖ ^ 2) ^ 2 by ring]
  push_cast
  rw [← this]
  ring

open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted in
theorem norm_gowersPow_two_eq_sum (f : G → ℂ) :
    ‖gowersPow 2 f‖ = ∑ ψ : AddChar G ℂ, ‖(Fintype.card G : ℂ)⁻¹ * dftFun f ψ‖ ^ 4 := by
  have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h := card_pow_four_mul_gowersPow_two f
  have hG : gowersPow 2 f = (Fintype.card G : ℂ)⁻¹ ^ 4 *
      ∑ ψ : AddChar G ℂ, (((‖dftFun f ψ‖ ^ 4 : ℝ)) : ℂ) := by
    rw [← h, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero 4 hn)]
  rw [hG, ← Complex.ofReal_sum, norm_mul, Complex.norm_real, norm_pow, norm_inv,
    Complex.norm_natCast, Real.norm_of_nonneg (by positivity), Finset.mul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [norm_mul, norm_inv, Complex.norm_natCast, mul_pow]

open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted in
/-- **The `U²` norm is the `ℓ⁴` norm of the Fourier transform.**
`‖f‖_{U²} = (∑_ψ |f̂(ψ)|⁴)^{1/4}` with `f̂(ψ) = |G|⁻¹ dftFun f ψ`. This is Lemma 2.4 of
Gowers [G10] and identity (2.4) of Green and Tao [GT08]; their transform `𝔼_x f(x) conj ψ(x)`
is ours composed with `ψ ↦ ψ⁻¹`, which does not change the sum. -/
theorem gowersNorm_two_eq (f : G → ℂ) :
    gowersNorm 2 f =
      (∑ ψ : AddChar G ℂ, ‖(Fintype.card G : ℂ)⁻¹ * dftFun f ψ‖ ^ 4) ^ ((1 : ℝ) / 4) := by
  unfold gowersNorm
  rw [norm_gowersPow_two_eq_sum]
  norm_num

open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted in
theorem gowersNorm_two_pow_four (f : G → ℂ) :
    gowersNorm 2 f ^ 4 = ∑ ψ : AddChar G ℂ, ‖(Fintype.card G : ℂ)⁻¹ * dftFun f ψ‖ ^ 4 := by
  rw [gowersNorm_two_eq, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted in
/- Parseval in the normalisation used here. -/
private theorem sum_norm_sq_normalised_dft (f : G → ℂ) :
    ∑ ψ : AddChar G ℂ, ‖(Fintype.card G : ℂ)⁻¹ * dftFun f ψ‖ ^ 2 = 𝔼 x, ‖f x‖ ^ 2 := by
  have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hp := dft_plancherel f f
  have hl : (∑ x : G, star (f x) * f x) = ((∑ x : G, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Complex.conj_mul', Complex.star_def]
  have hr : (∑ ψ : AddChar G ℂ, star (dftFun f ψ) * dftFun f ψ) =
      ((∑ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [← Complex.conj_mul', Complex.star_def]
  rw [hl, hr] at hp
  have hreal : (∑ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ^ 2) =
      (Fintype.card G : ℝ) * ∑ x : G, ‖f x‖ ^ 2 := by
    have := congrArg (fun z : ℂ => (Fintype.card G : ℂ) * z) hp
    simp only [← mul_assoc, mul_inv_cancel₀ hn, one_mul] at this
    exact_mod_cast this.symm
  have hnr : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
  rw [← Finset.mul_sum, hreal, Fintype.expect_eq_sum_div_card]
  field_simp

open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted in
/-- **Inverse theorem for the `U²` norm.** If `𝔼 |f|² ≤ 1` and `0 ≤ c ≤ ‖f‖_{U²}`, then some
character `ψ` satisfies `|𝔼_x f(x) conj ψ(x)| ≥ c²`: Proposition 2.7 of Gowers [G10]
(stated there for `c > 0`; `c = 0` is trivial). Proof as in [G10]:
`c⁴ ≤ ∑ |f̂|⁴ ≤ ‖f̂‖_∞² ∑ |f̂|² ≤ ‖f̂‖_∞²` by Parseval. -/
theorem exists_character_correlation_of_le_gowersNorm_two (f : G → ℂ)
    (hf : 𝔼 x, ‖f x‖ ^ 2 ≤ 1) {c : ℝ} (hc : 0 ≤ c) (hU : c ≤ gowersNorm 2 f) :
    ∃ ψ : AddChar G ℂ, c ^ 2 ≤ ‖𝔼 x, f x * conj (ψ x)‖ := by
  classical
  set a : AddChar G ℂ → ℝ := fun ψ => ‖(Fintype.card G : ℂ)⁻¹ * dftFun f ψ‖ with ha
  obtain ⟨ψ₀, -, hψ₀⟩ := Finset.exists_max_image Finset.univ a Finset.univ_nonempty
  refine ⟨ψ₀⁻¹, ?_⟩
  have hcorr : ‖𝔼 x, f x * conj (ψ₀⁻¹ x)‖ = a ψ₀ := by
    rw [ha]
    simp only [dftFun, Fintype.expect_eq_sum_div_card, AddChar.inv_apply,
      AddChar.map_neg_eq_conj, Complex.conj_conj, div_eq_inv_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hcorr]
  have h4 : c ^ 4 ≤ ∑ ψ, a ψ ^ 4 := by
    rw [ha, ← gowersNorm_two_pow_four]
    exact pow_le_pow_left₀ hc hU 4
  have hle : ∑ ψ, a ψ ^ 4 ≤ a ψ₀ ^ 2 * ∑ ψ, a ψ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ψ _ => ?_
    have h0 : 0 ≤ a ψ := norm_nonneg _
    have h1 : a ψ ≤ a ψ₀ := hψ₀ ψ (Finset.mem_univ _)
    nlinarith [mul_le_mul h1 h1 h0 (h0.trans h1), sq_nonneg (a ψ)]
  have hpars : ∑ ψ, a ψ ^ 2 ≤ 1 := by
    rw [ha, sum_norm_sq_normalised_dft]; exact hf
  have hmax0 : 0 ≤ a ψ₀ := norm_nonneg _
  have : (c ^ 2) ^ 2 ≤ a ψ₀ ^ 2 := by
    calc (c ^ 2) ^ 2 = c ^ 4 := by ring
      _ ≤ a ψ₀ ^ 2 * ∑ ψ, a ψ ^ 2 := h4.trans hle
      _ ≤ a ψ₀ ^ 2 * 1 := by gcongr
      _ = a ψ₀ ^ 2 := mul_one _
  exact (pow_le_pow_iff_left₀ (by positivity) hmax0 two_ne_zero).mp this

/-- **Three-term progression count.**
`apCountThree f₀ f₁ f₂ = 𝔼_{x, r} f₀(x) f₁(x + r) f₂(x + 2r)`, the form `Λ₃` of Green and Tao
[GT08, §1]. For `f₀ = f₁ = f₂ = 1_A` it is `|G|⁻²` times the number of progressions
`(x, x + r, x + 2r)` in `A`, the trivial ones (`r = 0`) included. -/
noncomputable def apCountThree (f₀ f₁ f₂ : G → ℂ) : ℂ :=
  𝔼 x, 𝔼 r, f₀ x * f₁ (x + r) * f₂ (x + 2 • r)

open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted in
private theorem sum_dftFun_three (f₀ f₁ f₂ : G → ℂ) :
    ∑ ψ : AddChar G ℂ, dftFun f₀ ψ * dftFun f₁ (ψ⁻¹ ^ 2) * dftFun f₂ ψ =
      ∑ z : G, ∑ y : G, (Fintype.card G : ℂ) * (f₀ (2 • y - z) * f₁ y * f₂ z) := by
  classical
  have hterm : ∀ ψ : AddChar G ℂ, dftFun f₀ ψ * dftFun f₁ (ψ⁻¹ ^ 2) * dftFun f₂ ψ =
      ∑ z : G, ∑ y : G, ∑ x : G, ψ (x - (2 • y - z)) * (f₀ x * f₁ y * f₂ z) := by
    intro ψ
    simp only [dftFun, Finset.sum_mul, Finset.mul_sum, AddChar.pow_apply, AddChar.inv_apply]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun x _ => ?_
    rw [show x - (2 • y - z) = x + -y + -y + z by abel, AddChar.map_add_eq_mul,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    ring
  simp_rw [hterm]
  calc ∑ ψ : AddChar G ℂ, ∑ z : G, ∑ y : G, ∑ x : G,
        ψ (x - (2 • y - z)) * (f₀ x * f₁ y * f₂ z)
      = ∑ z : G, ∑ y : G, ∑ x : G, ∑ ψ : AddChar G ℂ,
          ψ (x - (2 • y - z)) * (f₀ x * f₁ y * f₂ z) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ z : G, ∑ y : G, ∑ x : G,
          (if x = 2 • y - z then (Fintype.card G : ℂ) * (f₀ x * f₁ y * f₂ z) else 0) := by
        refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ =>
          Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite]
        simp only [sub_eq_zero, ite_mul, zero_mul]
    _ = ∑ z : G, ∑ y : G, (Fintype.card G : ℂ) * (f₀ (2 • y - z) * f₁ y * f₂ z) := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted in
/-- **Fourier expansion of the three-term progression count.**
`|G|³ Λ₃(f₀, f₁, f₂) = ∑_ψ F₀(ψ) F₁(ψ⁻²) F₂(ψ)` with `F = dftFun`. Proof: expand the
transforms and collapse the sum over characters by orthogonality; the triples
`(x, y, z)` with `x + z = 2y` are exactly the progressions `(x, x + r, x + 2r)`. -/
theorem card_pow_three_mul_apCountThree (f₀ f₁ f₂ : G → ℂ) :
    (Fintype.card G : ℂ) ^ 3 * apCountThree f₀ f₁ f₂ =
      ∑ ψ : AddChar G ℂ, dftFun f₀ ψ * dftFun f₁ (ψ⁻¹ ^ 2) * dftFun f₂ ψ := by
  classical
  rw [sum_dftFun_three, apCountThree]
  have hreindex : ∑ x : G, ∑ r : G, f₀ x * f₁ (x + r) * f₂ (x + 2 • r) =
      ∑ z : G, ∑ y : G, f₀ (2 • y - z) * f₁ y * f₂ z := by
    calc ∑ x : G, ∑ r : G, f₀ x * f₁ (x + r) * f₂ (x + 2 • r)
        = ∑ x : G, ∑ y : G, f₀ x * f₁ y * f₂ (2 • y - x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun r => ?_
          simp only [Equiv.coe_addLeft]
          rw [show 2 • (x + r) - x = x + 2 • r by abel]
      _ = ∑ y : G, ∑ x : G, f₀ x * f₁ y * f₂ (2 • y - x) := Finset.sum_comm
      _ = ∑ y : G, ∑ z : G, f₀ (2 • y - z) * f₁ y * f₂ z := by
          refine Finset.sum_congr rfl fun y _ => ?_
          refine (Fintype.sum_equiv (Equiv.subLeft (2 • y)) _ _ fun z => ?_).symm
          simp only [Equiv.subLeft_apply, sub_sub_cancel]
      _ = ∑ z : G, ∑ y : G, f₀ (2 • y - z) * f₁ y * f₂ z := Finset.sum_comm
  simp only [Fintype.expect_eq_sum_div_card, ← Finset.sum_div, ← Finset.mul_sum]
  rw [hreindex]
  field_simp

private theorem sum_mul3_le_rpow {ι : Type*} [Fintype ι] (u v w : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i)
    (hv2 : ∑ i, v i ^ 2 ≤ 1) (hw2 : ∑ i, w i ^ 2 ≤ 1) :
    ∑ i, u i * v i * w i ≤ (∑ i, u i ^ 4) ^ ((1 : ℝ) / 4) := by
  set M := (∑ i, u i ^ 4) ^ ((1 : ℝ) / 4) with hM
  have hM0 : 0 ≤ M := by positivity
  have huM : ∀ i, u i ≤ M := by
    intro i
    have h1 : u i ^ 4 ≤ ∑ j, u j ^ 4 :=
      Finset.single_le_sum (f := fun j => u j ^ 4) (fun j _ => by positivity) (Finset.mem_univ i)
    calc u i = (u i ^ 4) ^ ((1 : ℝ) / 4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (hu i)]; norm_num
      _ ≤ M := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hvw : ∑ i, v i * w i ≤ 1 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w
    have hsq : (∑ i, v i * w i) ^ 2 ≤ 1 := by
      calc (∑ i, v i * w i) ^ 2 ≤ (∑ i, v i ^ 2) * ∑ i, w i ^ 2 := hcs
        _ ≤ 1 * 1 := by gcongr
        _ = 1 := one_mul 1
    nlinarith [sq_nonneg (∑ i, v i * w i - 1)]
  calc ∑ i, u i * v i * w i ≤ ∑ i, M * (v i * w i) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (huM i) (mul_nonneg (hv i) (hw i))
    _ = M * ∑ i, v i * w i := by rw [Finset.mul_sum]
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left hvw hM0
    _ = M := mul_one M

open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted in
private theorem sum_norm_sq_normalised_dft_le_one (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∑ ψ : AddChar G ℂ, ‖(Fintype.card G : ℂ)⁻¹ * dftFun f ψ‖ ^ 2 ≤ 1 := by
  rw [sum_norm_sq_normalised_dft]
  calc 𝔼 x, ‖f x‖ ^ 2 ≤ 𝔼 _x : G, (1 : ℝ) :=
        Finset.expect_le_expect fun x _ => by
          have := hf x; have := norm_nonneg (f x); nlinarith
    _ = 1 := Fintype.expect_const 1

open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted in
/-- **Generalized von Neumann theorem for three-term progressions.** If `|G|` is coprime to `2`
and `|f₀|, |f₁|, |f₂| ≤ 1`, then `|Λ₃(f₀, f₁, f₂)| ≤ ‖f_j‖_{U²}` for each `j ∈ {0, 1, 2}`.
This is the case `k = 3` of Proposition 1.7 of Green and Tao [GT08] (hypothesis
`(|G|, (k - 1)!) = 1`) and of Theorem 3.2 of Gowers [G01] (on `ℤ_N`, with the bound through
the last function only). The proof here is Fourier-analytic (Roth's argument): by the Fourier
expansion of `Λ₃`, Cauchy–Schwarz, Parseval and `‖f̂‖_∞ ≤ ‖f̂‖_{ℓ⁴}`; oddness makes
`ψ ↦ ψ⁻²` a bijection of the dual group. The same bound for every `k`, by Green and Tao's
Cauchy–Schwarz argument, is `norm_apCount_le_gowersNorm`. -/
theorem norm_apCountThree_le_gowersNorm_two (hG : (Fintype.card G).Coprime 2)
    (f₀ f₁ f₂ : G → ℂ) (h₀ : ∀ x, ‖f₀ x‖ ≤ 1) (h₁ : ∀ x, ‖f₁ x‖ ≤ 1)
    (h₂ : ∀ x, ‖f₂ x‖ ≤ 1) :
    ‖apCountThree f₀ f₁ f₂‖ ≤ gowersNorm 2 f₀ ∧ ‖apCountThree f₀ f₁ f₂‖ ≤ gowersNorm 2 f₁ ∧
      ‖apCountThree f₀ f₁ f₂‖ ≤ gowersNorm 2 f₂ := by
  have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hdual : (Nat.card (AddChar G ℂ)).Coprime 2 := by
    rwa [Nat.card_eq_fintype_card, AddChar.card_eq]
  set e : AddChar G ℂ ≃ AddChar G ℂ := (Equiv.inv _).trans (powCoprime hdual) with he
  have he_apply : ∀ ψ, e ψ = ψ⁻¹ ^ 2 := fun ψ => rfl
  set a : (G → ℂ) → AddChar G ℂ → ℝ := fun f ψ => ‖(Fintype.card G : ℂ)⁻¹ * dftFun f ψ‖
    with ha
  have hcount : apCountThree f₀ f₁ f₂ = ∑ ψ : AddChar G ℂ,
      ((Fintype.card G : ℂ)⁻¹ * dftFun f₀ ψ) * ((Fintype.card G : ℂ)⁻¹ * dftFun f₁ (e ψ)) *
        ((Fintype.card G : ℂ)⁻¹ * dftFun f₂ ψ) := by
    have h := card_pow_three_mul_apCountThree f₀ f₁ f₂
    have : apCountThree f₀ f₁ f₂ = (Fintype.card G : ℂ)⁻¹ ^ 3 * ∑ ψ : AddChar G ℂ,
        dftFun f₀ ψ * dftFun f₁ (ψ⁻¹ ^ 2) * dftFun f₂ ψ := by
      rw [← h, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero 3 hn)]
    rw [this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [he_apply]
    ring
  have hle : ‖apCountThree f₀ f₁ f₂‖ ≤ ∑ ψ : AddChar G ℂ, a f₀ ψ * a f₁ (e ψ) * a f₂ ψ := by
    rw [hcount]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun ψ _ => ?_
    simp only [ha, norm_mul]
  have hpar : ∀ f : G → ℂ, (∀ x, ‖f x‖ ≤ 1) → ∑ ψ, a f ψ ^ 2 ≤ 1 :=
    fun f hf => sum_norm_sq_normalised_dft_le_one f hf
  have hpar_e : ∀ f : G → ℂ, (∀ x, ‖f x‖ ≤ 1) → ∑ ψ, a f (e ψ) ^ 2 ≤ 1 := fun f hf => by
    rw [Equiv.sum_comp e (fun ψ => a f ψ ^ 2)]; exact hpar f hf
  have hnorm : ∀ f : G → ℂ, gowersNorm 2 f = (∑ ψ, a f ψ ^ 4) ^ ((1 : ℝ) / 4) :=
    fun f => gowersNorm_two_eq f
  have hnn : ∀ f ψ, 0 ≤ a f ψ := fun _ _ => norm_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · refine hle.trans ?_
    rw [hnorm]
    exact sum_mul3_le_rpow _ _ _ (hnn f₀) (fun ψ => hnn f₁ (e ψ)) (hnn f₂)
      (hpar_e f₁ h₁) (hpar f₂ h₂)
  · refine hle.trans ?_
    rw [hnorm, ← Equiv.sum_comp e (fun ψ => a f₁ ψ ^ 4)]
    calc ∑ ψ, a f₀ ψ * a f₁ (e ψ) * a f₂ ψ = ∑ ψ, a f₁ (e ψ) * a f₀ ψ * a f₂ ψ :=
          Finset.sum_congr rfl fun ψ _ => by ring
      _ ≤ _ := sum_mul3_le_rpow _ _ _ (fun ψ => hnn f₁ (e ψ)) (hnn f₀) (hnn f₂)
          (hpar f₀ h₀) (hpar f₂ h₂)
  · refine hle.trans ?_
    rw [hnorm]
    calc ∑ ψ, a f₀ ψ * a f₁ (e ψ) * a f₂ ψ = ∑ ψ, a f₂ ψ * a f₁ (e ψ) * a f₀ ψ :=
          Finset.sum_congr rfl fun ψ _ => by ring
      _ ≤ _ := sum_mul3_le_rpow _ _ _ (hnn f₂) (fun ψ => hnn f₁ (e ψ)) (hnn f₀)
          (hpar_e f₁ h₁) (hpar f₀ h₀)

/- `cpow n z` is `z` if `n` is even and `conj z` otherwise (`C^n z`). -/
private def cpow (n : ℕ) (z : ℂ) : ℂ := if Even n then z else conj z

private theorem cpow_mul (n : ℕ) (a b : ℂ) : cpow n (a * b) = cpow n a * cpow n b := by
  unfold cpow; split_ifs <;> simp

private theorem cpow_conj (n : ℕ) (b : ℂ) : cpow n (conj b) = cpow (n + 1) b := by
  unfold cpow
  by_cases h : Even n
  · simp [h, Nat.even_add_one]
  · simp [h, Nat.even_add_one]

private theorem card_filter_cons {d : ℕ} (b : Bool) (ω : Fin d → Bool) :
    (univ.filter fun i : Fin (d + 1) => (Fin.cons b ω : Fin (d + 1) → Bool) i = true).card =
      (if b then 1 else 0) + (univ.filter fun i => ω i = true).card := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

private theorem prod_fin_succ_bool {M : Type*} [CommMonoid M] {d : ℕ}
    (P : (Fin (d + 1) → Bool) → M) :
    ∏ ω, P ω = ∏ ω : Fin d → Bool, P (Fin.cons true ω) * P (Fin.cons false ω) := by
  rw [← (Fin.consEquiv fun _ => Bool).prod_comp, Fintype.prod_prod_type, Fintype.prod_bool,
    ← Finset.prod_mul_distrib]
  rfl

private theorem gowersPow_eq_cube_aux (d : ℕ) : ∀ f : G → ℂ,
    gowersPow d f = 𝔼 x, 𝔼 h : Fin d → G, ∏ ω : Fin d → Bool,
      cpow (univ.filter fun i => ω i = true).card (f (x + ∑ i, if ω i then h i else 0)) := by
  induction d with
  | zero =>
    intro f
    simp [gowersPow_zero, cpow]
  | succ d ih =>
    intro f
    have hsum : ∀ (b : Bool) (ω : Fin d → Bool) (t : G) (h : Fin d → G),
        (∑ i : Fin (d + 1), if (Fin.cons b ω : Fin (d + 1) → Bool) i
          then (Fin.cons t h : Fin (d + 1) → G) i else 0) =
          (if b then t else 0) + ∑ i, if ω i then h i else 0 := by
      intro b ω t h
      rw [Fin.sum_univ_succ]
      simp [Fin.cons_zero, Fin.cons_succ]
    have hcube : ∀ (x t : G) (h : Fin d → G),
        (∏ ω : Fin (d + 1) → Bool, cpow (univ.filter fun i => ω i = true).card
          (f (x + ∑ i, if ω i then (Fin.cons t h : Fin (d + 1) → G) i else 0))) =
        ∏ ω : Fin d → Bool, cpow (univ.filter fun i => ω i = true).card
          (mulDeriv t f (x + ∑ i, if ω i then h i else 0)) := by
      intro x t h
      rw [prod_fin_succ_bool]
      refine Finset.prod_congr rfl fun ω _ => ?_
      rw [card_filter_cons, card_filter_cons, hsum, hsum, mulDeriv, cpow_mul, cpow_conj]
      simp only [ite_true, Bool.false_eq_true, ite_false, zero_add]
      rw [mul_comm, add_comm 1, show x + (t + ∑ i, if ω i then h i else 0) =
        x + (∑ i, if ω i then h i else 0) + t by abel]
    calc gowersPow (d + 1) f = 𝔼 t, gowersPow d (mulDeriv t f) := rfl
      _ = 𝔼 t, 𝔼 x, 𝔼 h : Fin d → G, ∏ ω : Fin d → Bool,
            cpow (univ.filter fun i => ω i = true).card
              (mulDeriv t f (x + ∑ i, if ω i then h i else 0)) := by simp_rw [ih]
      _ = 𝔼 x, 𝔼 t, 𝔼 h : Fin d → G, ∏ ω : Fin d → Bool,
            cpow (univ.filter fun i => ω i = true).card
              (mulDeriv t f (x + ∑ i, if ω i then h i else 0)) := Finset.expect_comm _ _ _
      _ = 𝔼 x, 𝔼 t, 𝔼 h : Fin d → G, ∏ ω : Fin (d + 1) → Bool,
            cpow (univ.filter fun i => ω i = true).card
              (f (x + ∑ i, if ω i then (Fin.cons t h : Fin (d + 1) → G) i else 0)) := by
          simp_rw [hcube]
      _ = 𝔼 x, 𝔼 h : Fin (d + 1) → G, ∏ ω : Fin (d + 1) → Bool,
            cpow (univ.filter fun i => ω i = true).card
              (f (x + ∑ i, if ω i then h i else 0)) := by
          refine Finset.expect_congr rfl fun x _ => ?_
          rw [← Finset.expect_product' (s := univ) (t := univ)
            (f := fun t (h : Fin d → G) => ∏ ω : Fin (d + 1) → Bool,
              cpow (univ.filter fun i => ω i = true).card
                (f (x + ∑ i, if ω i then (Fin.cons t h : Fin (d + 1) → G) i else 0))),
            Finset.univ_product_univ]
          exact Fintype.expect_equiv (Fin.consEquiv fun _ => G) _ _ fun p => rfl

/-- **Gowers norms as cube averages.** For every `d`,
`gowersPow d f = 𝔼_{x ∈ G, h ∈ G^d} ∏_{ω ∈ {0,1}^d} C^{|ω|} f(x + ω · h)`, where `C` is complex
conjugation and `|ω|` the number of coordinates of `ω` equal to `1`. This is Definition 1.6 of
Green and Tao [GT08]; together with the definition of `gowersPow` it proves their remark that
the recursion (1.1) is an equivalent definition. -/
theorem gowersPow_eq_cubeAverage (d : ℕ) (f : G → ℂ) :
    gowersPow d f =
      𝔼 x, 𝔼 h : Fin d → G, ∏ ω : Fin d → Bool,
        (if Even (univ.filter fun i => ω i = true).card
          then f (x + ∑ i, if ω i then h i else 0)
          else conj (f (x + ∑ i, if ω i then h i else 0))) :=
  gowersPow_eq_cube_aux d f

/-- **Gowers inner product.** For functions `F ω : G → ℂ` indexed by `ω ∈ {0,1}^d`,
`gowersInner d F = 𝔼_{x ∈ G, h ∈ G^d} ∏_ω C^{|ω|} F ω (x + ω · h)`: the left-hand side of
Lemma 3.8 of Gowers [G01], with averages in place of sums and `+` in place of `-` in the
shifts (a change of variables). For `d = 2` it is `gowersInnerTwo` up to the indexing of
`{0,1}²`. -/
noncomputable def gowersInner (d : ℕ) (F : (Fin d → Bool) → G → ℂ) : ℂ :=
  𝔼 x, 𝔼 h : Fin d → G, ∏ ω : Fin d → Bool,
    (if Even (univ.filter fun i => ω i = true).card
      then F ω (x + ∑ i, if ω i then h i else 0)
      else conj (F ω (x + ∑ i, if ω i then h i else 0)))

private theorem cpow_conj' (n : ℕ) (b : ℂ) : cpow n (conj b) = conj (cpow n b) := by
  unfold cpow; split_ifs <;> simp

private theorem cpow_succ (n : ℕ) (b : ℂ) : cpow (n + 1) b = conj (cpow n b) := by
  rw [← cpow_conj, cpow_conj']

/- The face average used in the Cauchy–Schwarz step of the Gowers–Cauchy–Schwarz inequality. -/
private noncomputable def faceAvg {d : ℕ} (F : (Fin (d + 1) → Bool) → G → ℂ) (b : Bool)
    (h : Fin d → G) : ℂ :=
  𝔼 x, ∏ ω : Fin d → Bool,
    cpow (univ.filter fun i => ω i = true).card (F (Fin.cons b ω) (x + ∑ i, if ω i then h i else 0))

private theorem gowersInner_eq_cpow (d : ℕ) (F : (Fin d → Bool) → G → ℂ) :
    gowersInner d F = 𝔼 x, 𝔼 h : Fin d → G, ∏ ω : Fin d → Bool,
      cpow (univ.filter fun i => ω i = true).card (F ω (x + ∑ i, if ω i then h i else 0)) := rfl

private theorem gowersInner_succ {d : ℕ} (F : (Fin (d + 1) → Bool) → G → ℂ) :
    gowersInner (d + 1) F = 𝔼 h : Fin d → G, faceAvg F false h * conj (faceAvg F true h) := by
  have hsum : ∀ (b : Bool) (ω : Fin d → Bool) (t : G) (h : Fin d → G),
      (∑ i : Fin (d + 1), if (Fin.cons b ω : Fin (d + 1) → Bool) i
        then (Fin.cons t h : Fin (d + 1) → G) i else 0) =
        (if b then t else 0) + ∑ i, if ω i then h i else 0 := by
    intro b ω t h
    rw [Fin.sum_univ_succ]
    simp [Fin.cons_zero, Fin.cons_succ]
  set A : Bool → G → (Fin d → G) → ℂ := fun b y h => ∏ ω : Fin d → Bool,
    cpow (univ.filter fun i => ω i = true).card (F (Fin.cons b ω) (y + ∑ i, if ω i then h i else 0))
    with hA
  have hcube : ∀ (x t : G) (h : Fin d → G),
      (∏ ω : Fin (d + 1) → Bool, cpow (univ.filter fun i => ω i = true).card
        (F ω (x + ∑ i, if ω i then (Fin.cons t h : Fin (d + 1) → G) i else 0))) =
      A false x h * conj (A true (x + t) h) := by
    intro x t h
    rw [prod_fin_succ_bool, Finset.prod_mul_distrib, mul_comm, hA]
    simp only [map_prod]
    congr 1
    · refine Finset.prod_congr rfl fun ω _ => ?_
      rw [card_filter_cons, hsum]
      simp
    · refine Finset.prod_congr rfl fun ω _ => ?_
      rw [card_filter_cons, hsum]
      simp only [ite_true]
      rw [add_comm 1, cpow_succ, show x + (t + ∑ i, if ω i then h i else 0) =
        x + t + ∑ i, if ω i then h i else 0 by abel]
  have hshift : ∀ (x : G) (h : Fin d → G),
      (𝔼 t, conj (A true (x + t) h)) = conj (faceAvg F true h) := by
    intro x h
    have hs : (𝔼 t, A true (x + t) h) = 𝔼 y, A true y h :=
      Fintype.expect_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
    calc (𝔼 t, conj (A true (x + t) h)) = conj (𝔼 t, A true (x + t) h) := by
          simp only [Fintype.expect_eq_sum_div_card, map_div₀, map_sum, map_natCast]
      _ = conj (𝔼 y, A true y h) := by rw [hs]
      _ = conj (faceAvg F true h) := rfl
  rw [gowersInner_eq_cpow]
  calc 𝔼 x, 𝔼 h : Fin (d + 1) → G, ∏ ω : Fin (d + 1) → Bool,
        cpow (univ.filter fun i => ω i = true).card (F ω (x + ∑ i, if ω i then h i else 0))
      = 𝔼 x, 𝔼 t, 𝔼 h : Fin d → G, A false x h * conj (A true (x + t) h) := by
        refine Finset.expect_congr rfl fun x _ => ?_
        rw [← Finset.expect_product' (s := univ) (t := univ)
          (f := fun t (h : Fin d → G) => A false x h * conj (A true (x + t) h)),
          Finset.univ_product_univ]
        exact (Fintype.expect_equiv (Fin.consEquiv fun _ => G) _ _
          fun p => (hcube x p.1 p.2).symm).symm
    _ = 𝔼 x, 𝔼 h : Fin d → G, 𝔼 t, A false x h * conj (A true (x + t) h) :=
        Finset.expect_congr rfl fun x _ => Finset.expect_comm _ _ _
    _ = 𝔼 h : Fin d → G, 𝔼 x, 𝔼 t, A false x h * conj (A true (x + t) h) :=
        Finset.expect_comm _ _ _
    _ = 𝔼 h : Fin d → G, 𝔼 x, A false x h * 𝔼 t, conj (A true (x + t) h) := by
        refine Finset.expect_congr rfl fun h _ => Finset.expect_congr rfl fun x _ => ?_
        rw [Finset.mul_expect]
    _ = 𝔼 h : Fin d → G, faceAvg F false h * conj (faceAvg F true h) := by
        refine Finset.expect_congr rfl fun h _ => ?_
        simp_rw [hshift]
        rw [← Finset.expect_mul]
        rfl

private theorem expect_faceAvg_mul_conj {d : ℕ} (F : (Fin (d + 1) → Bool) → G → ℂ) (b : Bool) :
    (𝔼 h : Fin d → G, faceAvg F b h * conj (faceAvg F b h)) =
      𝔼 t, gowersInner d (fun ω => mulDeriv t (F (Fin.cons b ω))) := by
  set A : G → (Fin d → G) → ℂ := fun y h => ∏ ω : Fin d → Bool,
    cpow (univ.filter fun i => ω i = true).card (F (Fin.cons b ω) (y + ∑ i, if ω i then h i else 0))
    with hA
  have hshift : ∀ (x : G) (h : Fin d → G),
      conj (faceAvg F b h) = 𝔼 t, conj (A (x + t) h) := by
    intro x h
    have hs : (𝔼 t, A (x + t) h) = 𝔼 y, A y h :=
      Fintype.expect_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
    calc conj (faceAvg F b h) = conj (𝔼 y, A y h) := rfl
      _ = conj (𝔼 t, A (x + t) h) := by rw [hs]
      _ = 𝔼 t, conj (A (x + t) h) := by
          simp only [Fintype.expect_eq_sum_div_card, map_div₀, map_sum, map_natCast]
  have hprod : ∀ (x t : G) (h : Fin d → G), A x h * conj (A (x + t) h) =
      ∏ ω : Fin d → Bool, cpow (univ.filter fun i => ω i = true).card
        (mulDeriv t (F (Fin.cons b ω)) (x + ∑ i, if ω i then h i else 0)) := by
    intro x t h
    rw [hA]
    simp only [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ω _ => ?_
    rw [mulDeriv, cpow_mul, cpow_conj', show x + t + ∑ i, (if ω i then h i else 0) =
      x + (∑ i, if ω i then h i else 0) + t by abel]
  calc (𝔼 h : Fin d → G, faceAvg F b h * conj (faceAvg F b h))
      = 𝔼 h : Fin d → G, 𝔼 x, 𝔼 t, A x h * conj (A (x + t) h) := by
        refine Finset.expect_congr rfl fun h _ => ?_
        calc faceAvg F b h * conj (faceAvg F b h)
            = 𝔼 x, A x h * conj (faceAvg F b h) := by rw [← Finset.expect_mul]; rfl
          _ = 𝔼 x, 𝔼 t, A x h * conj (A (x + t) h) := by
              refine Finset.expect_congr rfl fun x _ => ?_
              rw [hshift x h, Finset.mul_expect]
    _ = 𝔼 x, 𝔼 h : Fin d → G, 𝔼 t, A x h * conj (A (x + t) h) := Finset.expect_comm _ _ _
    _ = 𝔼 x, 𝔼 t, 𝔼 h : Fin d → G, A x h * conj (A (x + t) h) :=
        Finset.expect_congr rfl fun x _ => Finset.expect_comm _ _ _
    _ = 𝔼 t, 𝔼 x, 𝔼 h : Fin d → G, A x h * conj (A (x + t) h) := Finset.expect_comm _ _ _
    _ = 𝔼 t, gowersInner d (fun ω => mulDeriv t (F (Fin.cons b ω))) := by
        refine Finset.expect_congr rfl fun t _ => ?_
        rw [gowersInner_eq_cpow]
        refine Finset.expect_congr rfl fun x _ => Finset.expect_congr rfl fun h _ => ?_
        exact hprod x t h

private theorem sq_norm_gowersInner_succ_le {d : ℕ} (F : (Fin (d + 1) → Bool) → G → ℂ) :
    ‖gowersInner (d + 1) F‖ ^ 2 ≤
      (𝔼 t, ‖gowersInner d (fun ω => mulDeriv t (F (Fin.cons false ω)))‖) *
        𝔼 t, ‖gowersInner d (fun ω => mulDeriv t (F (Fin.cons true ω)))‖ := by
  have hface : ∀ b : Bool, (𝔼 h : Fin d → G, ‖faceAvg F b h‖ ^ 2) ≤
      𝔼 t, ‖gowersInner d (fun ω => mulDeriv t (F (Fin.cons b ω)))‖ := by
    intro b
    have h1 : (𝔼 h : Fin d → G, ‖faceAvg F b h‖ ^ 2) =
        ‖𝔼 h : Fin d → G, faceAvg F b h * conj (faceAvg F b h)‖ := by
      have hmc : ∀ h : Fin d → G,
          faceAvg F b h * conj (faceAvg F b h) = ((‖faceAvg F b h‖ ^ 2 : ℝ) : ℂ) := by
        intro h; rw [Complex.mul_conj']; push_cast; rfl
      simp_rw [hmc]
      rw [← Complex.ofReal_expect, Complex.norm_real,
        Real.norm_of_nonneg (Finset.expect_nonneg fun _ _ => by positivity)]
    rw [h1, expect_faceAvg_mul_conj]
    exact RCLike.norm_expect_le (K := ℂ)
  rw [gowersInner_succ]
  calc ‖𝔼 h : Fin d → G, faceAvg F false h * conj (faceAvg F true h)‖ ^ 2
      ≤ (𝔼 h : Fin d → G, ‖faceAvg F false h‖ * ‖faceAvg F true h‖) ^ 2 := by
        gcongr
        refine (RCLike.norm_expect_le (K := ℂ)).trans (le_of_eq ?_)
        simp only [norm_mul, Complex.norm_conj]
    _ ≤ (𝔼 h : Fin d → G, ‖faceAvg F false h‖ ^ 2) * 𝔼 h : Fin d → G, ‖faceAvg F true h‖ ^ 2 :=
        Finset.expect_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ _ := mul_le_mul (hface false) (hface true)
        (Finset.expect_nonneg fun _ _ => by positivity)
        (Finset.expect_nonneg fun _ _ => norm_nonneg _)

/- Hölder's inequality for `2 ^ d` nonnegative functions indexed by `{0,1}^d`. -/
private theorem expect_prod_le_prod_rpow {T : Type*} [Fintype T] (d : ℕ) :
    ∀ g : (Fin d → Bool) → T → ℝ, (∀ ω t, 0 ≤ g ω t) →
      𝔼 t, ∏ ω, g ω t ≤ ∏ ω, (𝔼 t, g ω t ^ 2 ^ d) ^ ((1 : ℝ) / 2 ^ d) := by
  induction d with
  | zero =>
    intro g hg
    simp
  | succ d ih =>
    intro g hg
    set P : T → ℝ := fun t => ∏ ω : Fin d → Bool, g (Fin.cons true ω) t with hP
    set Q : T → ℝ := fun t => ∏ ω : Fin d → Bool, g (Fin.cons false ω) t with hQ
    have hP0 : ∀ t, 0 ≤ P t := fun t => Finset.prod_nonneg fun ω _ => hg _ _
    have hQ0 : ∀ t, 0 ≤ Q t := fun t => Finset.prod_nonneg fun ω _ => hg _ _
    have hsplit : ∀ t, ∏ ω, g ω t = P t * Q t := fun t => by
      rw [prod_fin_succ_bool, Finset.prod_mul_distrib]
    have hhalf : ∀ b : Bool,
        (𝔼 t, (∏ ω : Fin d → Bool, g (Fin.cons b ω) t) ^ 2) ^ ((1 : ℝ) / 2) ≤
          ∏ ω : Fin d → Bool,
            (𝔼 t, g (Fin.cons b ω) t ^ 2 ^ (d + 1)) ^ ((1 : ℝ) / 2 ^ (d + 1)) := by
      intro b
      have hih := ih (fun ω t => g (Fin.cons b ω) t ^ 2) (fun ω t => by positivity)
      simp only [Finset.prod_pow] at hih
      calc (𝔼 t, (∏ ω : Fin d → Bool, g (Fin.cons b ω) t) ^ 2) ^ ((1 : ℝ) / 2)
          ≤ (∏ ω : Fin d → Bool, (𝔼 t, (g (Fin.cons b ω) t ^ 2) ^ 2 ^ d) ^ ((1 : ℝ) / 2 ^ d))
              ^ ((1 : ℝ) / 2) :=
            Real.rpow_le_rpow (Finset.expect_nonneg fun _ _ => by positivity) hih (by norm_num)
        _ = ∏ ω : Fin d → Bool,
              (𝔼 t, g (Fin.cons b ω) t ^ 2 ^ (d + 1)) ^ ((1 : ℝ) / 2 ^ (d + 1)) := by
            rw [← Real.finsetProd_rpow _ _ (fun ω _ => by positivity)]
            refine Finset.prod_congr rfl fun ω _ => ?_
            rw [← Real.rpow_mul (Finset.expect_nonneg fun _ _ => by positivity)]
            congr 1
            · refine Finset.expect_congr rfl fun t _ => ?_
              rw [← pow_mul, pow_succ, mul_comm]
            · rw [pow_succ]; field_simp
    calc 𝔼 t, ∏ ω, g ω t = 𝔼 t, P t * Q t := Finset.expect_congr rfl fun t _ => hsplit t
      _ ≤ (𝔼 t, P t ^ 2) ^ ((1 : ℝ) / 2) * (𝔼 t, Q t ^ 2) ^ ((1 : ℝ) / 2) := by
          have hcs := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ P Q
          have h0 : 0 ≤ 𝔼 t, P t * Q t :=
            Finset.expect_nonneg fun t _ => mul_nonneg (hP0 t) (hQ0 t)
          rw [← Real.mul_rpow (Finset.expect_nonneg fun _ _ => by positivity)
            (Finset.expect_nonneg fun _ _ => by positivity)]
          calc 𝔼 t, P t * Q t = ((𝔼 t, P t * Q t) ^ 2) ^ ((1 : ℝ) / 2) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
            _ ≤ _ := Real.rpow_le_rpow (by positivity) hcs (by norm_num)
      _ ≤ (∏ ω : Fin d → Bool,
              (𝔼 t, g (Fin.cons true ω) t ^ 2 ^ (d + 1)) ^ ((1 : ℝ) / 2 ^ (d + 1))) *
            ∏ ω : Fin d → Bool,
              (𝔼 t, g (Fin.cons false ω) t ^ 2 ^ (d + 1)) ^ ((1 : ℝ) / 2 ^ (d + 1)) := by
          exact mul_le_mul (hhalf true) (hhalf false)
            (Real.rpow_nonneg (Finset.expect_nonneg fun _ _ => sq_nonneg _) _)
            (Finset.prod_nonneg fun _ _ => Real.rpow_nonneg
              (Finset.expect_nonneg fun _ _ => pow_nonneg (hg _ _) _) _)
      _ = ∏ ω, (𝔼 t, g ω t ^ 2 ^ (d + 1)) ^ ((1 : ℝ) / 2 ^ (d + 1)) := by
          rw [prod_fin_succ_bool, Finset.prod_mul_distrib]

private theorem expect_norm_gowersPow_mulDeriv (d : ℕ) (f : G → ℂ) :
    𝔼 t, ‖gowersPow (d + 1) (mulDeriv t f)‖ = ‖gowersPow (d + 2) f‖ := by
  rw [norm_gowersPow_succ (d + 1), gowersPow_succ]
  simp_rw [norm_gowersPow_succ d]
  have : (𝔼 t, gowersPow (d + 1) (mulDeriv t f)) =
      ((𝔼 t, (gowersPow (d + 1) (mulDeriv t f)).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_expect]
    exact Finset.expect_congr rfl fun t _ => (sq_norm_gowersPow_le_and_real d _).2
  rw [this, Complex.ofReal_re]

private theorem gowersNorm_pow_eq (d : ℕ) (f : G → ℂ) :
    gowersNorm d f ^ 2 ^ d = ‖gowersPow d f‖ := by
  unfold gowersNorm
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

/-- **Gowers–Cauchy–Schwarz inequality.** For functions `F ω : G → ℂ` indexed by
`ω ∈ {0,1}^d`, `|⟨F⟩_{U^d}| ≤ ∏_ω ‖F ω‖_{U^d}` where `⟨F⟩_{U^d} = gowersInner d F`: Lemma 3.8
of Gowers [G01], stated there on `ℤ_N` with sums (both sides scale by the same power of `N`),
here on any finite abelian group. Proof by induction on `d`: Cauchy–Schwarz in the first
coordinate of the cube, the induction hypothesis for the derivatives `Δ_t F`, and Hölder's
inequality over the `2^d` faces. For `d = 0, 1` both sides are equal. -/
theorem norm_gowersInner_le (d : ℕ) (F : (Fin d → Bool) → G → ℂ) :
    ‖gowersInner d F‖ ≤ ∏ ω, gowersNorm d (F ω) := by
  rcases d with _ | d
  · simp [gowersInner, gowersNorm, gowersPow_zero]
  induction d with
  | zero =>
    have hface : ∀ (b : Bool) (h : Fin 0 → G),
        faceAvg F b h = 𝔼 x, F (Fin.cons b fun _ => false) x := by
      intro b h
      simp only [faceAvg]
      refine Finset.expect_congr rfl fun x _ => ?_
      rw [Fintype.prod_unique]
      simp only [cpow]
      simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.card_empty, Finset.sum_empty,
        add_zero]
      rw [ite_eq_left_iff.mpr (fun h => absurd (by decide) h)]
      exact congrArg (fun ω : Fin 0 → Bool => F (Fin.cons b ω) x) (Subsingleton.elim _ _)
    rw [gowersInner_succ, prod_fin_succ_bool, Fintype.prod_unique]
    simp_rw [hface]
    simp only [Fintype.expect_const, norm_mul, Complex.norm_conj, zero_add, gowersNorm_one]
    rw [mul_comm]
    convert le_rfl using 6
  | succ d ih =>
    have hstep : ∀ b : Bool, 𝔼 t, ‖gowersInner (d + 1) (fun ω => mulDeriv t (F (Fin.cons b ω)))‖ ≤
        ∏ ω : Fin (d + 1) → Bool, gowersNorm (d + 2) (F (Fin.cons b ω)) ^ 2 := by
      intro b
      calc 𝔼 t, ‖gowersInner (d + 1) (fun ω => mulDeriv t (F (Fin.cons b ω)))‖
          ≤ 𝔼 t, ∏ ω : Fin (d + 1) → Bool, gowersNorm (d + 1) (mulDeriv t (F (Fin.cons b ω))) :=
            Finset.expect_le_expect fun t _ => ih _
        _ ≤ ∏ ω : Fin (d + 1) → Bool,
              (𝔼 t, gowersNorm (d + 1) (mulDeriv t (F (Fin.cons b ω))) ^ 2 ^ (d + 1)) ^
                ((1 : ℝ) / 2 ^ (d + 1)) :=
            expect_prod_le_prod_rpow (d + 1) _ fun _ _ => gowersNorm_nonneg _ _
        _ = ∏ ω : Fin (d + 1) → Bool, gowersNorm (d + 2) (F (Fin.cons b ω)) ^ 2 := by
            refine Finset.prod_congr rfl fun ω _ => ?_
            simp_rw [gowersNorm_pow_eq, expect_norm_gowersPow_mulDeriv]
            unfold gowersNorm
            rw [← Real.rpow_mul_natCast (norm_nonneg _)]
            congr 1
            push_cast
            rw [pow_succ 2 (d + 1)]
            field_simp
    have hsq : ‖gowersInner (d + 2) F‖ ^ 2 ≤ (∏ ω, gowersNorm (d + 2) (F ω)) ^ 2 := by
      calc ‖gowersInner (d + 2) F‖ ^ 2
          ≤ (𝔼 t, ‖gowersInner (d + 1) (fun ω => mulDeriv t (F (Fin.cons false ω)))‖) *
              𝔼 t, ‖gowersInner (d + 1) (fun ω => mulDeriv t (F (Fin.cons true ω)))‖ :=
            sq_norm_gowersInner_succ_le F
        _ ≤ (∏ ω : Fin (d + 1) → Bool, gowersNorm (d + 2) (F (Fin.cons false ω)) ^ 2) *
              ∏ ω : Fin (d + 1) → Bool, gowersNorm (d + 2) (F (Fin.cons true ω)) ^ 2 :=
            mul_le_mul (hstep false) (hstep true) (Finset.expect_nonneg fun _ _ => norm_nonneg _)
              (Finset.prod_nonneg fun _ _ => by positivity)
        _ = (∏ ω, gowersNorm (d + 2) (F ω)) ^ 2 := by
            rw [prod_fin_succ_bool (P := fun ω : Fin (d + 2) → Bool => gowersNorm (d + 2) (F ω)),
              Finset.prod_mul_distrib, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow, mul_comm]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (Finset.prod_nonneg fun _ _ => gowersNorm_nonneg _ _) two_ne_zero).mp hsq

private theorem cpow_add (n : ℕ) (a b : ℂ) : cpow n (a + b) = cpow n a + cpow n b := by
  unfold cpow; split_ifs <;> simp

/-- **Triangle inequality for the Gowers norms.** `‖f + g‖_{U^d} ≤ ‖f‖_{U^d} + ‖g‖_{U^d}` for
every `d`: Lemma 3.9 of Gowers [G01] (stated there for `d ≥ 2` on `ℤ_N`, where it shows that
`‖·‖_d` is a norm; for `d = 0, 1` it is the triangle inequality for `|𝔼 f|`). Proof as in [G01]:
expand `‖f + g‖_{U^d}^{2^d}` into `2^{2^d}` Gowers inner products and bound each by the
Gowers–Cauchy–Schwarz inequality `norm_gowersInner_le`. -/
theorem gowersNorm_add_le (d : ℕ) (f g : G → ℂ) :
    gowersNorm d (f + g) ≤ gowersNorm d f + gowersNorm d g := by
  classical
  have hpt : ∀ (x : G) (h : Fin d → G),
      (∏ ω : Fin d → Bool, cpow (univ.filter fun i => ω i = true).card
        ((f + g) (x + ∑ i, if ω i then h i else 0))) =
      ∑ t ∈ (univ : Finset (Fin d → Bool)).powerset, ∏ ω : Fin d → Bool,
        cpow (univ.filter fun i => ω i = true).card
          ((if ω ∈ t then f else g) (x + ∑ i, if ω i then h i else 0)) := by
    intro x h
    simp only [Pi.add_apply, cpow_add]
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_congr rfl fun ω _ => (show cpow (univ.filter fun i => ω i = true).card
        ((if ω ∈ t then f else g) (x + ∑ i, if ω i then h i else 0)) =
      if ω ∈ t then
          cpow (univ.filter fun i => ω i = true).card (f (x + ∑ i, if ω i then h i else 0))
        else cpow (univ.filter fun i => ω i = true).card (g (x + ∑ i, if ω i then h i else 0)) by
      split_ifs <;> rfl)]
    rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.filter_not,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hexpand : gowersPow d (f + g) = ∑ t ∈ (univ : Finset (Fin d → Bool)).powerset,
      gowersInner d (fun ω => if ω ∈ t then f else g) := by
    rw [gowersPow_eq_cube_aux]
    simp only [gowersInner_eq_cpow]
    simp_rw [hpt]
    rw [Finset.expect_congr rfl fun x _ => Finset.expect_sum_comm _ _ _]
    exact Finset.expect_sum_comm _ _ _
  have hbound : ‖gowersPow d (f + g)‖ ≤ (gowersNorm d f + gowersNorm d g) ^ 2 ^ d := by
    rw [hexpand]
    calc ‖∑ t ∈ (univ : Finset (Fin d → Bool)).powerset,
          gowersInner d (fun ω => if ω ∈ t then f else g)‖
        ≤ ∑ t ∈ (univ : Finset (Fin d → Bool)).powerset,
            ‖gowersInner d (fun ω => if ω ∈ t then f else g)‖ := norm_sum_le _ _
      _ ≤ ∑ t ∈ (univ : Finset (Fin d → Bool)).powerset,
            ∏ ω : Fin d → Bool, gowersNorm d (if ω ∈ t then f else g) :=
          Finset.sum_le_sum fun t _ => norm_gowersInner_le d _
      _ = ∏ _ω : Fin d → Bool, (gowersNorm d f + gowersNorm d g) := by
          rw [Finset.prod_add]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.prod_congr rfl fun ω _ => (show gowersNorm d (if ω ∈ t then f else g) =
            if ω ∈ t then gowersNorm d f else gowersNorm d g by split_ifs <;> rfl)]
          rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.filter_not,
            Finset.filter_mem_eq_inter, Finset.univ_inter]
      _ = (gowersNorm d f + gowersNorm d g) ^ 2 ^ d := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin]
  rw [← gowersNorm_pow_eq] at hbound
  exact (pow_le_pow_iff_left₀ (gowersNorm_nonneg _ _)
    (add_nonneg (gowersNorm_nonneg _ _) (gowersNorm_nonneg _ _)) (by positivity)).mp hbound

private theorem zsmul_bijective_of_coprime {c : ℤ} (hc : c.natAbs.Coprime (Fintype.card G)) :
    Function.Bijective fun h : G => c • h := by
  refine Finite.injective_iff_bijective.mp fun h₁ h₂ heq => ?_
  have h0 : c • (h₁ - h₂) = 0 := by simp only [smul_sub] at heq ⊢; rw [heq, sub_self]
  have hdvd : ((addOrderOf (h₁ - h₂) : ℕ) : ℤ) ∣ c := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h0
  have h1 : addOrderOf (h₁ - h₂) ∣ c.natAbs := Int.natCast_dvd.mp hdvd
  have h2 : addOrderOf (h₁ - h₂) ∣ Fintype.card G := addOrderOf_dvd_card
  have : addOrderOf (h₁ - h₂) = 1 := Nat.eq_one_of_dvd_coprimes hc h1 h2
  rw [AddMonoid.addOrderOf_eq_one_iff, sub_eq_zero] at this
  exact this

private theorem expect_zsmul_comp {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] {c : ℤ}
    (hc : c.natAbs.Coprime (Fintype.card G)) (φ : G → M) : 𝔼 k, φ (c • k) = 𝔼 h, φ h :=
  Fintype.expect_bijective _ (zsmul_bijective_of_coprime hc) _ _ fun _ => rfl

private theorem expect_le_rpow_expect_pow {T : Type*} [Fintype T] [Nonempty T] (d : ℕ) (G' : T → ℝ)
    (hG : ∀ t, 0 ≤ G' t) : 𝔼 t, G' t ≤ (𝔼 t, G' t ^ 2 ^ d) ^ ((1 : ℝ) / 2 ^ d) := by
  classical
  set ω₀ : Fin d → Bool := fun _ => false
  have h := expect_prod_le_prod_rpow d (fun ω t => if ω = ω₀ then G' t else 1)
    (fun ω t => by split_ifs <;> simp [hG])
  have hl : ∀ t, (∏ ω : Fin d → Bool, if ω = ω₀ then G' t else 1) = G' t := fun t => by
    rw [Finset.prod_ite_eq']; simp
  have hr : (∏ ω : Fin d → Bool,
      (𝔼 t, (if ω = ω₀ then G' t else 1) ^ 2 ^ d) ^ ((1 : ℝ) / 2 ^ d)) =
      (𝔼 t, G' t ^ 2 ^ d) ^ ((1 : ℝ) / 2 ^ d) := by
    rw [Finset.prod_eq_single ω₀]
    · simp
    · intro ω _ hω; simp [hω]
    · simp
  simp_rw [hl] at h
  rwa [hr] at h

private theorem expect_prod_shift {m : ℕ} (a : Fin m → ℤ) (f : Fin m → G → ℂ) (c : ℤ) :
    𝔼 x, 𝔼 h, ∏ j, f j (x + a j • h) = 𝔼 y, 𝔼 h, ∏ j, f j (y + (a j - c) • h) := by
  rw [Finset.expect_comm, Finset.expect_comm (s := univ) (t := univ)
    (f := fun y h => ∏ j, f j (y + (a j - c) • h))]
  refine Finset.expect_congr rfl fun h _ => ?_
  refine Fintype.expect_equiv (Equiv.addRight (c • h)) _ _ fun x => ?_
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Equiv.coe_addRight, sub_smul]
  congr 1
  abel

private theorem gowersNorm_sq_eq (n : ℕ) (f : G → ℂ) :
    ‖gowersPow (n + 2) f‖ ^ ((1 : ℝ) / 2 ^ (n + 1)) = gowersNorm (n + 2) f ^ 2 := by
  unfold gowersNorm
  rw [← Real.rpow_mul_natCast (norm_nonneg _)]
  congr 1
  push_cast
  rw [pow_succ 2 (n + 1)]
  field_simp

/-- **Generalized von Neumann theorem, general form.** Let `m ≥ 2`, let `a₀, …, a_{m-1}` be
integers whose pairwise differences are coprime to `|G|`, and let `f₀, …, f_{m-1} : G → ℂ` take
values in the closed unit disc. Then `|𝔼_{x, h} ∏_j f_j(x + a_j h)| ≤ ‖f_{j₀}‖_{U^{m-1}}` for
every `j₀`. This is statement (4.2) of Green and Tao [GT08, proof of Proposition 1.7], which
they prove by induction on `m` with the van der Corput inequality (4.1) and Hölder's
inequality; the proof here follows theirs, starting the induction at `m = 2`. -/
theorem norm_expect_prod_le_gowersNorm (n : ℕ) (a : Fin (n + 2) → ℤ)
    (ha : ∀ i j, i ≠ j → (a i - a j).natAbs.Coprime (Fintype.card G))
    (f : Fin (n + 2) → G → ℂ) (hf : ∀ j x, ‖f j x‖ ≤ 1) (j₀ : Fin (n + 2)) :
    ‖𝔼 x, 𝔼 h, ∏ j, f j (x + a j • h)‖ ≤ gowersNorm (n + 1) (f j₀) := by
  induction n with
  | zero =>
    set j₁ : Fin 2 := if j₀ = 0 then 1 else 0 with hj₁
    have hne : j₀ ≠ j₁ := by fin_cases j₀ <;> simp [hj₁]
    obtain ⟨i₀, hi₀⟩ := Fin.exists_succAbove_eq hne
    have hb : (a (j₁.succAbove i₀) - a j₁).natAbs.Coprime (Fintype.card G) := by
      rw [hi₀]; exact ha _ _ hne
    rw [expect_prod_shift a f (a j₁)]
    have hfac : ∀ y : G, (𝔼 h, ∏ j, f j (y + (a j - a j₁) • h)) =
        f j₁ y * 𝔼 x, f j₀ x := by
      intro y
      simp_rw [Fin.prod_univ_succAbove _ j₁, sub_self, zero_smul, add_zero, Fin.prod_univ_one]
      rw [← Finset.mul_expect]
      congr 1
      have hi : (0 : Fin 1) = i₀ := Subsingleton.elim _ _
      rw [hi, expect_zsmul_comp hb (fun h => f (j₁.succAbove i₀) (y + h)), hi₀]
      exact Fintype.expect_equiv (Equiv.addLeft y) _ _ fun _ => rfl
    simp_rw [hfac]
    rw [← Finset.expect_mul, norm_mul, gowersNorm_one]
    have h1 : ‖𝔼 y, f j₁ y‖ ≤ 1 :=
      (RCLike.norm_expect_le (K := ℂ)).trans
        ((Finset.expect_le_expect fun y _ => hf j₁ y).trans (Fintype.expect_const 1).le)
    calc ‖𝔼 y, f j₁ y‖ * ‖𝔼 x, f j₀ x‖ ≤ 1 * ‖𝔼 x, f j₀ x‖ := by gcongr
      _ = ‖𝔼 x, f j₀ x‖ := one_mul _
  | succ n ih =>
    set j₁ : Fin (n + 3) := if j₀ = 0 then 1 else 0 with hj₁
    have hne : j₀ ≠ j₁ := by
      by_cases h : j₀ = 0
      · simp only [hj₁, h, ite_true]; exact Fin.zero_ne_one
      · simp only [hj₁, h, ite_false]; exact h
    obtain ⟨i₀, hi₀⟩ := Fin.exists_succAbove_eq hne
    set b : Fin (n + 2) → ℤ := fun i => a (j₁.succAbove i) - a j₁ with hbdef
    set g : Fin (n + 2) → G → ℂ := fun i => f (j₁.succAbove i) with hg
    have hb0 : (b i₀).natAbs.Coprime (Fintype.card G) := by
      simp only [hbdef]; rw [hi₀]; exact ha _ _ hne
    set Q : G → ℂ := fun y => 𝔼 h, ∏ i, g i (y + b i • h) with hQ
    have hΛ : (𝔼 x, 𝔼 h, ∏ j, f j (x + a j • h)) = 𝔼 y, f j₁ y * Q y := by
      rw [expect_prod_shift a f (a j₁)]
      refine Finset.expect_congr rfl fun y _ => ?_
      simp_rw [Fin.prod_univ_succAbove _ j₁, sub_self, zero_smul, add_zero]
      rw [← Finset.mul_expect]
    have hQQ : (𝔼 y, Q y * conj (Q y)) = 𝔼 k, 𝔼 y, 𝔼 h,
        ∏ i, mulDeriv (b i • k) (g i) (y + b i • h) := by
      have hconj : ∀ y h, conj (Q y) = 𝔼 k, conj (∏ i, g i (y + b i • (h + k))) := by
        intro y h
        have hs : (𝔼 k, ∏ i, g i (y + b i • (h + k))) = Q y :=
          Fintype.expect_equiv (Equiv.addLeft h) _ _ fun _ => rfl
        rw [← hs]
        simp only [Fintype.expect_eq_sum_div_card, map_div₀, map_sum, map_natCast]
      have hpt : ∀ y h k, (∏ i, g i (y + b i • h)) * conj (∏ i, g i (y + b i • (h + k))) =
          ∏ i, mulDeriv (b i • k) (g i) (y + b i • h) := by
        intro y h k
        rw [map_prod, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [mulDeriv, smul_add, add_assoc]
      calc (𝔼 y, Q y * conj (Q y))
          = 𝔼 y, 𝔼 h, 𝔼 k, (∏ i, g i (y + b i • h)) *
              conj (∏ i, g i (y + b i • (h + k))) := by
            refine Finset.expect_congr rfl fun y _ => ?_
            change (𝔼 h, ∏ i, g i (y + b i • h)) * conj (Q y) = _
            rw [Finset.expect_mul]
            refine Finset.expect_congr rfl fun h _ => ?_
            rw [hconj y h, Finset.mul_expect]
        _ = 𝔼 y, 𝔼 h, 𝔼 k, ∏ i, mulDeriv (b i • k) (g i) (y + b i • h) := by
            simp_rw [hpt]
        _ = 𝔼 y, 𝔼 k, 𝔼 h, ∏ i, mulDeriv (b i • k) (g i) (y + b i • h) :=
            Finset.expect_congr rfl fun y _ => Finset.expect_comm _ _ _
        _ = 𝔼 k, 𝔼 y, 𝔼 h, ∏ i, mulDeriv (b i • k) (g i) (y + b i • h) :=
            Finset.expect_comm _ _ _
    have hinner : ∀ k, ‖𝔼 y, 𝔼 h, ∏ i, mulDeriv (b i • k) (g i) (y + b i • h)‖ ≤
        gowersNorm (n + 1) (mulDeriv (b i₀ • k) (g i₀)) := by
      intro k
      refine ih b (fun i j hij => ?_) (fun i => mulDeriv (b i • k) (g i)) (fun i x => ?_) i₀
      · simp only [hbdef, sub_sub_sub_cancel_right]
        exact ha _ _ (fun h => hij (Fin.succAbove_right_injective h))
      · simp only [mulDeriv, norm_mul, Complex.norm_conj]
        calc ‖g i x‖ * ‖g i (x + b i • k)‖ ≤ 1 * 1 :=
              mul_le_mul (hf _ _) (hf _ _) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    have hQnorm : 𝔼 y, ‖Q y‖ ^ 2 = ‖𝔼 y, Q y * conj (Q y)‖ := by
      have hmc : ∀ y, Q y * conj (Q y) = ((‖Q y‖ ^ 2 : ℝ) : ℂ) := by
        intro y; rw [Complex.mul_conj']; push_cast; rfl
      simp_rw [hmc]
      rw [← Complex.ofReal_expect, Complex.norm_real,
        Real.norm_of_nonneg (Finset.expect_nonneg fun _ _ => by positivity)]
    have hsq : ‖𝔼 x, 𝔼 h, ∏ j, f j (x + a j • h)‖ ^ 2 ≤ gowersNorm (n + 2) (f j₀) ^ 2 := by
      rw [hΛ]
      calc ‖𝔼 y, f j₁ y * Q y‖ ^ 2
          ≤ (𝔼 y, ‖Q y‖) ^ 2 := by
            gcongr
            refine (RCLike.norm_expect_le (K := ℂ)).trans
              (Finset.expect_le_expect fun y _ => ?_)
            rw [norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _) (hf j₁ y)
        _ = (𝔼 y, ‖Q y‖ * 1) ^ 2 := by simp
        _ ≤ (𝔼 y, ‖Q y‖ ^ 2) * 𝔼 y : G, (1 : ℝ) ^ 2 := Finset.expect_mul_sq_le_sq_mul_sq _ _ _
        _ = ‖𝔼 k, 𝔼 y, 𝔼 h, ∏ i, mulDeriv (b i • k) (g i) (y + b i • h)‖ := by
            rw [one_pow, Fintype.expect_const, mul_one, hQnorm, hQQ]
        _ ≤ 𝔼 k, ‖𝔼 y, 𝔼 h, ∏ i, mulDeriv (b i • k) (g i) (y + b i • h)‖ :=
            RCLike.norm_expect_le (K := ℂ)
        _ ≤ 𝔼 k, gowersNorm (n + 1) (mulDeriv (b i₀ • k) (g i₀)) :=
            Finset.expect_le_expect fun k _ => hinner k
        _ ≤ (𝔼 k, gowersNorm (n + 1) (mulDeriv (b i₀ • k) (g i₀)) ^ 2 ^ (n + 1)) ^
              ((1 : ℝ) / 2 ^ (n + 1)) :=
            expect_le_rpow_expect_pow (n + 1) _ fun _ => gowersNorm_nonneg _ _
        _ = ‖gowersPow (n + 2) (g i₀)‖ ^ ((1 : ℝ) / 2 ^ (n + 1)) := by
            simp_rw [gowersNorm_pow_eq]
            rw [expect_zsmul_comp hb0 (fun h => ‖gowersPow (n + 1) (mulDeriv h (g i₀))‖),
              expect_norm_gowersPow_mulDeriv]
        _ = gowersNorm (n + 2) (f j₀) ^ 2 := by
            rw [gowersNorm_sq_eq, hg]; simp only []; rw [hi₀]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (gowersNorm_nonneg _ _) two_ne_zero).mp hsq

/-- **Generalized von Neumann theorem.** Let `k ≥ 2`, let `|G|` be coprime to `(k - 1)!` and let
`f₀, …, f_{k-1} : G → ℂ` take values in the closed unit disc. Then
`|𝔼_{x, r} ∏_{i < k} f_i(x + i r)| ≤ ‖f_j‖_{U^{k-1}}` for every `j < k`: Proposition 1.7 of
Green and Tao [GT08], and Theorem 3.2 of Gowers [G01] on `ℤ_N` (where the bound is through the
last function). The restriction `k ≥ 2` avoids the degenerate `U⁰`. Deduced from
`norm_expect_prod_le_gowersNorm` with `a_i = i`: the differences `i - j` are at most `k - 1` in
absolute value, so they divide `(k - 1)!`. -/
theorem norm_apCount_le_gowersNorm (k : ℕ) (hk : 2 ≤ k)
    (hG : (Fintype.card G).Coprime (k - 1).factorial) (f : Fin k → G → ℂ)
    (hf : ∀ i x, ‖f i x‖ ≤ 1) (j : Fin k) :
    ‖𝔼 x, 𝔼 r, ∏ i : Fin k, f i (x + (i : ℕ) • r)‖ ≤ gowersNorm (k - 1) (f j) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have hcop : ∀ i j : Fin (n + 2), i ≠ j →
      (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)).natAbs.Coprime (Fintype.card G) := by
    intro i j hij
    have hpos : 0 < (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)).natAbs := by
      rw [Int.natAbs_pos, sub_ne_zero, Ne, Nat.cast_inj]
      exact fun h => hij (Fin.ext h)
    have hle : (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)).natAbs ≤ n + 1 := by
      have := i.isLt; have := j.isLt; omega
    have hdvd := Nat.dvd_factorial hpos hle
    exact Nat.Coprime.coprime_dvd_left hdvd (by simpa using hG.symm)
  have h := norm_expect_prod_le_gowersNorm n (fun i => ((i : ℕ) : ℤ)) hcop f hf j
  simp only [natCast_zsmul] at h
  simpa using h

end MathlibExt.Combinatorics.Additive.GowersNorm
