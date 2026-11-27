/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Chen–Stein Poisson approximation: two moments suffice

Arratia, Goldstein and Gordon (1989): let `I` be an index set and, for `α ∈ I`, let `X_α` be a
Bernoulli random variable with `p_α = P(X_α = 1) > 0`. Let `W = ∑_α X_α` and `λ = E W = ∑_α p_α`,
assumed to lie in `(0, ∞)`. For each `α` choose a neighbourhood `B_α ∋ α`, and set

* `b₁ = ∑_α ∑_{β ∈ B_α} p_α p_β`,
* `b₂ = ∑_α ∑_{β ∈ B_α, β ≠ α} E(X_α X_β)`,
* `b₃ = ∑_α E |E(X_α - p_α | σ(X_β : β ∉ B_α))|` and
  `b₃' = ∑_α E |E(X_α - p_α | ∑_{β ∉ B_α} X_β)|`.

With `Z` Poisson of mean `λ` and `‖L(W) - L(Z)‖ = sup_{‖h‖ ≤ 1} |E h(W) - E h(Z)| =
2 sup_A |P(W ∈ A) - P(Z ∈ A)|`, Theorem 1 gives
`‖L(W) - L(Z)‖ ≤ 2[(b₁ + b₂)(1 - e^{-λ})/λ + b₃'(1 ∧ 1.4 λ^{-1/2})] ≤ 2(b₁ + b₂ + b₃)` and
`|P(W = 0) - e^{-λ}| ≤ (b₁ + b₂ + b₃')(1 - e^{-λ})/λ`, and when `b₁ + b₂ + b₃ < ∞` this bound is
strictly `< (1 ∧ λ^{-1})(b₁ + b₂ + b₃)`. The process
version (Theorem 2) compares the law of `(X_α)_α` with independent Poisson variables of means `p_α`
and follows from the finite-dimensional bound (2) for a partition of `I` into `d` nonempty parts.
Lemma 1 bounds the solution of the Stein equation: for `h : ℕ → [0, 1]` and
`f = S(h - E h(Z))`, `‖Δ f‖ ≤ (1 - e^{-λ})/λ` and `‖f‖ ≤ 1 ∧ 1.4 λ^{-1/2}`.

Here `I` is nonempty and countable. In the dependent Bernoulli setting of the theorems every
`X_α` is measurable, so `W` is a countable sum of indicators, a random element of `ℕ∞` that is
finite almost surely since `λ < ∞`; its law on `ℕ` is taken as the law of `W.toNat`, where
`ENat.toNat` sends `⊤` to `0`, a null event here, and likewise for the block sums `W_j`. The
definitions themselves are raw formulas, read as laws and probabilities only under these
measurability hypotheses.
The coefficients `b₁, b₂, b₃, b₃'` are taken in `[0, ∞]`, so infinite sums are allowed, and the
total-variation norm `‖μ - ν‖` is Mathlib's `MeasureTheory.tvDist`, which for probability
measures is twice the largest difference over measurable sets
(`MathlibExt.InformationTheory.MeasurePinsker.tvDist_eq_two_mul_totalVariationDist`). When
`b₁ + b₂ + b₃ < ∞`, the strict inequality of Theorem 1 holds because `b₁ ≥ ∑ p_α² > 0` (without
finiteness, `b₂` can diverge even when `λ < ∞`). Not recorded here: the
Section 3 examples (Example 5 applies the theorems to the Erdős–Rényi law for sequence matching).

Sources: R. Arratia, L. Goldstein and L. Gordon, "Two moments suffice for Poisson approximations:
the Chen–Stein method", Annals of Probability 17 (1989) 9–25, doi:10.1214/aop/1176991491,
pp. 10–11 and 20, Theorems 1 and 2, equation (2) and Lemma 1; A. D. Barbour and G. K. Eagleson,
"Poisson approximation for some statistics based on exchangeable trials", Advances in Applied
Probability 15 (1983) 585–600 (appendix, proof of Lemma 1).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Topology.Instances.ENat

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.ChenSteinPoissonApproximationWanted

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

section Analytic

/-- **Poisson probability.** `P(Z = w)` for `Z` Poisson of mean `λ ≥ 0`: the mass of `{w}` under
Mathlib's `ProbabilityTheory.poissonMeasure λ`, which is `e^{-λ} λ^w / w!`
(`ProbabilityTheory.poissonMeasure_real_singleton`). -/
noncomputable def poissonProb (lam : ℝ≥0) (w : ℕ) : ℝ :=
  (poissonMeasure lam).real {w}

/-- **Poisson expectation.** `E h(Z)` for `Z` Poisson of mean `λ ≥ 0`, as the Bochner integral of
`h` against `ProbabilityTheory.poissonMeasure λ`: the ordinary, finite expectation when `h` is
integrable, and `0` otherwise, even when the expectation of a nonnegative `h` is `+∞` (for `λ = 1`
and `h(w) = e · w!` every term of the weighted sum is `1`). It is the series
`∑_w e^{-λ} λ^w / w! · h(w)`, read as `0` when not summable
(`ProbabilityTheory.integral_poissonMeasure`). -/
noncomputable def poissonMean (lam : ℝ≥0) (h : ℕ → ℝ) : ℝ :=
  ∫ w, h w ∂poissonMeasure lam

/-- **Stein solution.** For the Poisson law of mean `λ ≥ 0`, `S g` is given by `(S g)(0) = 0` and
`(S g)(w + 1) = -λ⁻¹ P(Z = w)⁻¹ E(g(Z); Z ≤ w)`. For `λ > 0` it is the inverse of
`(T f)(w) = w f(w) - λ f(w + 1)` on functions with `E g(Z) = 0`. -/
noncomputable def steinSol (lam : ℝ≥0) (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | w + 1 => -(lam : ℝ)⁻¹ * (poissonProb lam w)⁻¹ *
      ∑ v ∈ Finset.range (w + 1), g v * poissonProb lam v

/-- **Stein-solution bounds** (Arratia, Goldstein and Gordon 1989, Lemma 1, proved in the appendix
of Barbour and Eagleson 1983): for `λ > 0` and `h : ℕ → ℝ` with `0 ≤ h(w) ≤ 1` for every `w`,
the function `f = S(h - E h(Z))` satisfies `|f(w + 1) - f(w)| ≤ (1 - e^{-λ})/λ` and
`|f(w)| ≤ min 1 (1.4 λ^{-1/2})` for every `w ≥ 0`.

Source: Arratia, Goldstein and Gordon (1989), Lemma 1. -/
public theorem_wanted steinSol_bounds (lam : ℝ≥0) (hlam : 0 < lam) (h : ℕ → ℝ)
    (hh : ∀ w, h w ∈ Set.Icc (0 : ℝ) 1) (w : ℕ) :
    |steinSol lam (fun v => h v - poissonMean lam h) (w + 1) -
        steinSol lam (fun v => h v - poissonMean lam h) w| ≤
          (1 - Real.exp (-(lam : ℝ))) / lam ∧
      |steinSol lam (fun v => h v - poissonMean lam h) w| ≤ min 1 (1.4 / Real.sqrt lam)

end Analytic

section Norms

/-- **The two forms of the total-variation norm agree** (Arratia, Goldstein and Gordon 1989,
p.11): for probability measures `μ`, `ν` on `ℕ`, the supremum of `|∫ h dμ - ∫ h dν|` over
`h : ℕ → ℝ` with `|h(w)| ≤ 1` for every `w` equals `tvDist μ ν`, which for probability measures
is `2 sup_A |μ(A) - ν(A)|` (`MeasurePinsker.tvDist_eq_two_mul_totalVariationDist`).

Source: Arratia, Goldstein and Gordon (1989), p.11. -/
public theorem_wanted sSup_integral_eq_tvDist (μ ν : Measure ℕ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    sSup ((fun h : ℕ → ℝ => |∫ w, h w ∂μ - ∫ w, h w ∂ν|) '' {h | ∀ w, |h w| ≤ 1}) =
      tvDist μ ν

end Norms

variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I]

/-- The **dependent Bernoulli setting**: the index set `I` is nonempty, `X_α` takes values in
`{0, 1}` and is measurable, `p_α = P(X_α = 1) > 0`, `λ = ∑_α p_α` is finite (and positive, as `I`
is nonempty), and `α ∈ B_α`. -/
structure BernoulliSetting (P : Measure Ω) (X : I → Ω → ℕ) (B : I → Set I) : Prop where
  /-- The index set is nonempty, so `λ > 0`. -/
  nonempty : Nonempty I
  /-- Each `X_α` is measurable. -/
  measurable : ∀ a, Measurable (X a)
  /-- Each `X_α` takes values in `{0, 1}`. -/
  le_one : ∀ a ω, X a ω ≤ 1
  /-- `p_α > 0`. -/
  pos : ∀ a, 0 < ∫⁻ ω, (X a ω : ℝ≥0∞) ∂P
  /-- `λ < ∞`. -/
  sum_ne_top : ∑' a, ∫⁻ ω, (X a ω : ℝ≥0∞) ∂P ≠ ⊤
  /-- `α ∈ B_α`. -/
  mem : ∀ a, a ∈ B a

/-- `p_α = E X_α`, as the lower Lebesgue integral `∫⁻ X_α ∂P`. It is the expectation of `X_α`,
which is `P(X_α = 1)`, when `X_α` is measurable with values in `{0, 1}`, as in the dependent
Bernoulli setting. -/
noncomputable def pr (P : Measure Ω) (X : I → Ω → ℕ) (a : I) : ℝ≥0∞ :=
  ∫⁻ ω, (X a ω : ℝ≥0∞) ∂P

/-- **Sum of the means.** `λ = ∑_α p_α` as a real number: the `ENNReal.toReal` of the sum, so `0`
when the sum is infinite. In the dependent Bernoulli setting the sum is finite. -/
noncomputable def lam (P : Measure Ω) (X : I → Ω → ℕ) : ℝ :=
  (∑' a, pr P X a).toReal

/-- `W = ∑_α X_α`, pointwise, as a function `Ω → ℕ∞`. It is a random element of `ℕ∞` when it is
measurable, for example when every `X_α` is, as in the dependent Bernoulli setting. -/
noncomputable def W (X : I → Ω → ℕ) (ω : Ω) : ℕ∞ :=
  ∑' a, (X a ω : ℕ∞)

/-- The pushforward `P.map fun ω => (W X ω).toNat`, where `ENat.toNat` sends `⊤` to `0`. When
`W.toNat` is almost everywhere measurable it is the law on `ℕ` of `W.toNat`. In the dependent
Bernoulli setting every `X_α` is measurable and `λ = E W < ∞`, so `W < ⊤` almost surely and
this is the law of `W`. Without that measurability it is not a pushforward law: Mathlib's
`Measure.map` of a map that is not almost everywhere measurable is a Dirac mass at an arbitrary
point. -/
noncomputable def lawWToNat (P : Measure Ω) (X : I → Ω → ℕ) : Measure ℕ :=
  P.map fun ω => (W X ω).toNat

/-- `b₁ = ∑_α ∑_{β ∈ B_α} p_α p_β`. -/
noncomputable def b₁ (P : Measure Ω) (X : I → Ω → ℕ) (B : I → Set I) : ℝ≥0∞ :=
  ∑' a, ∑' b : B a, pr P X a * pr P X b

/-- `b₂ = ∑_α ∑_{β ∈ B_α, β ≠ α} E(X_α X_β)`, each term the lower Lebesgue integral of
`X_α X_β`, which is its expectation when the `X_α` are measurable, as in the dependent Bernoulli
setting. -/
noncomputable def b₂ (P : Measure Ω) (X : I → Ω → ℕ) (B : I → Set I) : ℝ≥0∞ :=
  ∑' a, ∑' b : (B a \ {a} : Set I), ∫⁻ ω, (X a ω * X b ω : ℝ≥0∞) ∂P

/-- The σ-algebra `σ(X_β : β ∉ B_α)`. -/
abbrev outsideSigma (X : I → Ω → ℕ) (B : I → Set I) (a : I) : MeasurableSpace Ω :=
  ⨆ b ∈ (B a)ᶜ, MeasurableSpace.comap (X b) inferInstance

/-- The σ-algebra generated by `∑_{β ∉ B_α} X_β`. -/
noncomputable abbrev outsideSumSigma (X : I → Ω → ℕ) (B : I → Set I) (a : I) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => ∑' b : ((B a)ᶜ : Set I), (X b ω : ℕ∞)) inferInstance

/-- **Coefficient b₃.** `b₃ = ∑_α E |E(X_α - p_α | σ(X_β : β ∉ B_α))|`. Mathlib's conditional
expectation is `0` in degenerate cases, such as a non-integrable function, and `p_α` enters
through `ENNReal.toReal`; in the dependent Bernoulli setting under a probability measure both are
the ordinary quantities. -/
noncomputable def b₃ (P : Measure Ω) (X : I → Ω → ℕ) (B : I → Set I) : ℝ≥0∞ :=
  ∑' a, ∫⁻ ω, ‖P[fun ω => (X a ω : ℝ) - (pr P X a).toReal | outsideSigma X B a] ω‖ₑ ∂P

/-- **Coefficient b₃'.** `b₃' = ∑_α E |E(X_α - p_α | ∑_{β ∉ B_α} X_β)|`, with the conventions of
`b₃`. -/
noncomputable def b₃' (P : Measure Ω) (X : I → Ω → ℕ) (B : I → Set I) : ℝ≥0∞ :=
  ∑' a, ∫⁻ ω, ‖P[fun ω => (X a ω : ℝ) - (pr P X a).toReal | outsideSumSigma X B a] ω‖ₑ ∂P

/-- **`b₃' ≤ b₃`** (Arratia, Goldstein and Gordon 1989, p.10): in the dependent Bernoulli setting
under a probability measure (nonempty countable `I`, measurable `X_α ∈ {0, 1}`, every `p_α > 0`,
`λ = ∑ p_α < ∞`, `α ∈ B_α`), `b₃' ≤ b₃`.

Source: Arratia, Goldstein and Gordon (1989), p.10. -/
public theorem_wanted b₃'_le_b₃ (P : Measure Ω) [IsProbabilityMeasure P] (X : I → Ω → ℕ)
    (B : I → Set I) (hX : BernoulliSetting P X B) :
    b₃' P X B ≤ b₃ P X B

/-- **Poisson approximation for the number of occurrences** (Arratia, Goldstein and Gordon 1989,
Theorem 1, first part): in the dependent Bernoulli setting under a probability measure
(nonempty countable `I`, measurable `X_α ∈ {0, 1}`, every `p_α > 0`, `λ = ∑ p_α < ∞`,
`α ∈ B_α`; then `λ > 0`), with `Z` Poisson of mean `λ` and `L(W)` the law of `W.toNat` (equal to
the law of `W`, as `W < ⊤` almost surely),
`‖L(W) - L(Z)‖ ≤ 2[(b₁ + b₂)(1 - e^{-λ})/λ + b₃'(1 ∧ 1.4 λ^{-1/2})] ≤ 2(b₁ + b₂ + b₃)`.

Source: Arratia, Goldstein and Gordon (1989), Theorem 1. -/
public theorem_wanted tvDist_lawWToNat_poisson_le (P : Measure Ω) [IsProbabilityMeasure P]
    (X : I → Ω → ℕ) (B : I → Set I) (hX : BernoulliSetting P X B) :
    ENNReal.ofReal (tvDist (lawWToNat P X) (poissonMeasure (lam P X).toNNReal)) ≤
        2 * ((b₁ P X B + b₂ P X B) *
            ENNReal.ofReal ((1 - Real.exp (-lam P X)) / lam P X) +
          b₃' P X B * ENNReal.ofReal (min 1 (1.4 / Real.sqrt (lam P X)))) ∧
      2 * ((b₁ P X B + b₂ P X B) *
            ENNReal.ofReal ((1 - Real.exp (-lam P X)) / lam P X) +
          b₃' P X B * ENNReal.ofReal (min 1 (1.4 / Real.sqrt (lam P X)))) ≤
        2 * (b₁ P X B + b₂ P X B + b₃ P X B)

/-- **Probability of no occurrence** (Arratia, Goldstein and Gordon 1989, Theorem 1, second part):
in the dependent Bernoulli setting under a probability measure (nonempty countable `I`, measurable
`X_α ∈ {0, 1}`, every `p_α > 0`, `λ = ∑ p_α < ∞`, `α ∈ B_α`),
`|P(W = 0) - e^{-λ}| ≤ (b₁ + b₂ + b₃')(1 - e^{-λ})/λ`, and if `b₁ + b₂ + b₃ < ∞` this is
`< (1 ∧ λ^{-1})(b₁ + b₂ + b₃)` (strict because `b₁ > 0`).

Source: Arratia, Goldstein and Gordon (1989), Theorem 1. -/
public theorem_wanted abs_prob_W_eq_zero_sub_exp_le (P : Measure Ω) [IsProbabilityMeasure P]
    (X : I → Ω → ℕ) (B : I → Set I) (hX : BernoulliSetting P X B) :
    ENNReal.ofReal |P.real {ω | W X ω = 0} - Real.exp (-lam P X)| ≤
        (b₁ P X B + b₂ P X B + b₃' P X B) *
          ENNReal.ofReal ((1 - Real.exp (-lam P X)) / lam P X) ∧
      (b₁ P X B + b₂ P X B + b₃ P X B ≠ ⊤ →
        (b₁ P X B + b₂ P X B + b₃' P X B) *
            ENNReal.ofReal ((1 - Real.exp (-lam P X)) / lam P X) <
          ENNReal.ofReal (min 1 (lam P X)⁻¹) * (b₁ P X B + b₂ P X B + b₃ P X B))

/-- **Finite-dimensional process bound** (Arratia, Goldstein and Gordon 1989, equation (2)): in
the dependent Bernoulli setting under a probability measure (nonempty countable `I`, measurable
`X_α ∈ {0, 1}`, every `p_α > 0`, `λ = ∑ p_α < ∞`, `α ∈ B_α`), for a partition of `I` into
`d ≥ 1` nonempty parts `I(j) = part⁻¹(j)` with `W_j = ∑_{α ∈ I(j)} X_α` and
`λ_j = ∑_{α ∈ I(j)} p_α`, the law of `(W_1, …, W_d)` (each `W_j` taken through `ENat.toNat`, which
sends `⊤` to `0`; `W_j < ⊤` almost surely) and the law of independent Poisson
variables of means `λ_1, …, λ_d` satisfy
`‖L(W_1, …, W_d) - L(Z_1, …, Z_d)‖ ≤ 2(1 ∧ 1.4 (min_j λ_j)^{-1/2})(2b₁ + 2b₂ + b₃)`.

Source: Arratia, Goldstein and Gordon (1989), equation (2). -/
public theorem_wanted tvDist_blockSums_le (P : Measure Ω) [IsProbabilityMeasure P]
    (X : I → Ω → ℕ) (B : I → Set I) (hX : BernoulliSetting P X B) (d : ℕ) (hd : 0 < d)
    (part : I → Fin d) (hpart : Function.Surjective part) :
    ENNReal.ofReal (tvDist
        (P.map fun ω j => (∑' a : {a // part a = j}, (X a ω : ℕ∞)).toNat)
        (Measure.pi fun j : Fin d =>
          poissonMeasure (∑' a : {a // part a = j}, pr P X a).toNNReal)) ≤
      2 * ENNReal.ofReal (min 1 (1.4 / Real.sqrt
          (⨅ j : Fin d, (∑' a : {a // part a = j}, pr P X a).toReal))) *
        (2 * b₁ P X B + 2 * b₂ P X B + b₃ P X B)

/-- **Poisson process approximation** (Arratia, Goldstein and Gordon 1989, Theorem 2): in the
dependent Bernoulli setting under a probability measure (nonempty countable `I`, measurable
`X_α ∈ {0, 1}`, every `p_α > 0`, `λ = ∑ p_α < ∞`, `α ∈ B_α`), the law of the process
`(X_α)_{α ∈ I}` and the law of independent Poisson variables `(Y_α)` of means `p_α` satisfy
`‖L(X) - L(Y)‖ ≤ 2(2b₁ + 2b₂ + b₃)`.

Source: Arratia, Goldstein and Gordon (1989), Theorem 2. -/
public theorem_wanted tvDist_process_le (P : Measure Ω) [IsProbabilityMeasure P]
    (X : I → Ω → ℕ) (B : I → Set I) (hX : BernoulliSetting P X B) :
    ENNReal.ofReal (tvDist (P.map fun ω a => X a ω)
        (Measure.infinitePi fun a => poissonMeasure (pr P X a).toNNReal)) ≤
      2 * (2 * b₁ P X B + 2 * b₂ P X B + b₃ P X B)

end WantedExt.Biology.ComputationalBiology.ChenSteinPoissonApproximationWanted
