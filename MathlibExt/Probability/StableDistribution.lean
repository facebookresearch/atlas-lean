/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.InfinitelyDivisible
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Indexed stable distributions and normalized weak limits

Indexed stability fixes the dilation of each positive convolution power to
`n^(1/α)`, for `0 < α ≤ 2`, with arbitrary centering. A nonzero-variance Gaussian
has index `2` and does not have index `1`. Dirac laws still admit degenerate
fixed-dilation identities at every admissible index; these do not identify a
unique nondegenerate limit index.

## Source and corrections

This repairs the definitions in
`v1/Atlas/TheoryOfProbability/code/DomainAttraction.lean` (`IsStable`,
`IsNondegenerate`, `InDomainOfAttraction`, `InDomainOfAttractionIndex`), related to
the Lecture 18 domain-of-attraction target. The archived stability definition left
its scale unconstrained by `α`, and indexed attraction omitted nondegeneracy of
its stable witness. Those two predicates are corrected here; no full equivalence
with the faulty indexed definitions is claimed.

The general normalized weak-limit relation keeps its original probability,
positive-normalizer and bounded-continuous-function clauses, and may have
Dirac limits. Indexed attraction adds `IsNondegenerate G` to its stable-law witness.
The old self-Dirac indexed witness is retired; its valid normalized weak-limit
identity remains.

## Canonical convolution and scope

Convolution powers and Dirac algebra use the existing `Measure.convPow` from
`InfinitelyDivisible`. The Gaussian convolution evaluation, fixed index-two
identity (including the explicitly degenerate zero-variance boundary),
nondegeneracy result and index-one exclusion are proved. Every stable law has
an exact inverse-affine normalized self-limit for positive orders; normalizer
one handles order zero, and eventual equality gives weak convergence.

Tail characterizations, limit-law classification and Lévy–Khinchin theorems
are not proved here.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Filter ProbabilityTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MathlibExt.Probability.StableDistribution

/-!
### Convolution powers
-/

/-- The convolution power of a Gaussian is Gaussian with the mean and the
variance multiplied by `n`: the law of the sum of `n` i.i.d.
`N(μ, v)` variables is `N(nμ, nv)`. -/
theorem convPow_gaussianReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    Measure.convPow (gaussianReal μ v) n =
      gaussianReal ((n : ℝ) * μ) ((n : ℝ≥0) * v) := by
  induction n with
  | zero =>
    simp [Measure.convPow_zero, gaussianReal_zero_var]
  | succ n ih =>
    rw [Measure.convPow_succ, ih, gaussianReal_conv_gaussianReal]
    congr 1
    · push_cast
      ring
    · push_cast
      ring

/-!
### Stable laws
-/

/-- Indexed stability fixes the positive-n dilation to `n^(1/α)` and allows
arbitrary centering. Degenerate Dirac identities may satisfy several indices. -/
def IsStable (μ : Measure ℝ) (α : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ 0 < α ∧ α ≤ 2 ∧
  ∀ n : ℕ, 0 < n → ∃ b : ℝ,
    μ.convPow n = μ.map (fun x => (n : ℝ) ^ (1 / α) * x + b)

/-- A Dirac law satisfies the fixed-dilation identity at every admissible index.
These are degenerate rescaling identities, with centering `na - n^(1/α)a`. -/
theorem isStable_dirac (a : ℝ) {α : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2) :
    IsStable (dirac a) α := by
  refine ⟨inferInstance, hα0, hα2, fun n _ => ?_⟩
  refine ⟨(n : ℝ) * a - (n : ℝ) ^ (1 / α) * a, ?_⟩
  rw [Measure.convPow_dirac, Measure.map_dirac]
  congr 1
  simp only [nsmul_eq_mul]
  ring

/-- Every real Gaussian measure is stable of index `2`: the sum of `n`
i.i.d. `N(μ, v)` variables is `N(nμ, nv)`, which is the pushforward of
`N(μ, v)` under `x ↦ √n · x + (n - √n) μ`. -/
theorem isStable_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    IsStable (gaussianReal μ v) 2 := by
  refine ⟨inferInstance, by norm_num, by norm_num, fun n _ => ?_⟩
  refine ⟨((n : ℝ) - Real.sqrt n) * μ, ?_⟩
  rw [← Real.sqrt_eq_rpow]
  rw [convPow_gaussianReal]
  have hmap : Measure.map (fun x => Real.sqrt (n : ℝ) * x +
        ((n : ℝ) - Real.sqrt n) * μ) (gaussianReal μ v) =
      Measure.map (fun y => y + ((n : ℝ) - Real.sqrt n) * μ)
        (Measure.map (fun x => Real.sqrt (n : ℝ) * x) (gaussianReal μ v)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hmap, gaussianReal_map_const_mul, gaussianReal_map_add_const]
  have hmk : (NNReal.mk ((Real.sqrt (n : ℝ)) ^ 2) (sq_nonneg _)) = (n : ℝ≥0) := by
    apply NNReal.coe_injective
    simp [Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hmk]
  congr 1
  ring

/-- A nondegenerate Gaussian cannot have fixed stability index one. The n=4
convolution variance is `4v`, while every such affine dilation has variance `16v`. -/
theorem not_isStable_gaussianReal_one {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    ¬ IsStable (gaussianReal μ v) 1 := by
  intro h
  obtain ⟨b, h4⟩ := h.2.2.2 4 (by norm_num)
  simp only [one_div_one, Real.rpow_one] at h4
  rw [convPow_gaussianReal] at h4
  norm_num at h4
  have hmap : (gaussianReal μ v).map (fun x => 4 * x + b) =
      ((gaussianReal μ v).map (fun x => 4 * x)).map (fun y => y + b) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hmap, gaussianReal_map_const_mul, gaussianReal_map_add_const] at h4
  have hvar := (gaussianReal_ext_iff.mp h4).2
  have hreal := congrArg (fun x : ℝ≥0 => (x : ℝ)) hvar
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_ofNat] at hreal
  have hz : (v : ℝ) = 0 := by nlinarith
  exact hv (NNReal.coe_injective hz)

/-- A measure `μ` on `ℝ` is *nondegenerate* if it is not a point mass
`δ_a` for any `a`. -/
def IsNondegenerate (μ : Measure ℝ) : Prop :=
  ¬ ∃ a : ℝ, μ = Measure.dirac a

/-- A Gaussian with nonzero variance is nondegenerate: it gives mass `0`
to every singleton, while `δ_a` gives mass `1` to `{a}`. -/
theorem isNondegenerate_gaussianReal {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    IsNondegenerate (gaussianReal μ v) := by
  rintro ⟨a, ha⟩
  have : NullSingletonClass (gaussianReal μ v) := nullSingletonClass_gaussianReal hv
  have h0 : gaussianReal μ v {a} = 0 :=
    NullSingletonClass.measure_singleton (μ := gaussianReal μ v) a
  rw [ha] at h0
  simp at h0

/-- A Dirac measure is degenerate, by definition. -/
theorem not_isNondegenerate_dirac (a : ℝ) :
    ¬ IsNondegenerate (Measure.dirac a) :=
  fun h => h ⟨a, rfl⟩

/-!
### Domains of attraction
-/

/-- The probability measure `μ` is *in the domain of attraction* of `G`
if there exist sequences of normalizing constants `a n > 0` and
centering constants `b n` such that the law of `(S_n - b n) / a n`
(where `S_n` has law `μ^{*n}`) converges weakly to `G`, expressed here
as integration against arbitrary bounded continuous functions. -/
def InDomainOfAttraction (μ G : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ IsProbabilityMeasure G ∧
  ∃ (a : ℕ → ℝ) (b : ℕ → ℝ),
    (∀ n, 0 < a n) ∧
    ∀ (f : ℝ →ᵇ ℝ),
      Tendsto
        (fun n => ∫ x, f x ∂(Measure.map (fun y => (y - b n) / a n)
          (Measure.convPow μ n)))
        atTop (𝓝 (∫ x, f x ∂G))

/-- A stable law is a normalized weak limit of its own convolution powers.
The positive-n inverse affine identity is exact; order zero uses normalizer one. -/
theorem IsStable.inDomainOfAttraction_self {μ : Measure ℝ} {α : ℝ}
    (h : IsStable μ α) : InDomainOfAttraction μ μ := by
  classical
  let a : ℕ → ℝ := fun n => if n = 0 then 1 else (n : ℝ) ^ (1 / α)
  let b : ℕ → ℝ := fun n => if hn : 0 < n then Classical.choose (h.2.2.2 n hn) else 0
  have ha : ∀ n, 0 < a n := by
    intro n
    by_cases hn : n = 0
    · simp [a, hn]
    · simp only [a, ite_eq_right hn]
      exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) _
  refine ⟨h.1, h.1, a, b, ha, fun f => ?_⟩
  have heq : ∀ᶠ n : ℕ in atTop,
      (μ.convPow n).map (fun y => (y - b n) / a n) = μ := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
    have hna : a n = (n : ℝ) ^ (1 / α) := by simp [a, Nat.ne_of_gt hnpos]
    have hnb : b n = Classical.choose (h.2.2.2 n hnpos) := by simp [b, hnpos]
    have hc := Classical.choose_spec (h.2.2.2 n hnpos)
    refine (congrArg (fun ν : Measure ℝ => ν.map (fun y => (y - b n) / a n)) hc).trans ?_
    rw [Measure.map_map (by fun_prop) (by fun_prop), hnb, hna]
    have hpositive : 0 < (n : ℝ) ^ (1 / α) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnpos) _
    have hfun : (fun x : ℝ =>
        (((n : ℝ) ^ (1 / α) * x + Classical.choose (h.2.2.2 n hnpos)) -
          Classical.choose (h.2.2.2 n hnpos)) / (n : ℝ) ^ (1 / α)) = id := by
      funext x
      dsimp only [id]
      field_simp [ne_of_gt hpositive]
      ring
    exact (congrArg (fun g : ℝ → ℝ => μ.map g) hfun).trans Measure.map_id
  apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [heq] with n hn
  rw [hn]

/-- Indexed attraction requires a nondegenerate stable limit of that index.
The general normalized weak-limit relation alone does not assign an index. -/
def InDomainOfAttractionIndex (μ : Measure ℝ) (α : ℝ) : Prop :=
  ∃ G : Measure ℝ, IsStable G α ∧ IsNondegenerate G ∧ InDomainOfAttraction μ G

/-- The Dirac measure is in its own domain of attraction: with
`a n = 1` and `b n = (n - 1) a`, the normalized law of `S_n` is
`δ_a` for every `n`. -/
theorem inDomainOfAttraction_dirac (a : ℝ) :
    InDomainOfAttraction (Measure.dirac a) (Measure.dirac a) := by
  refine ⟨inferInstance, inferInstance, fun _ => 1, fun n => ((n : ℝ) - 1) * a,
    fun _ => one_pos, fun f => ?_⟩
  have hterm : ∀ n : ℕ,
      ∫ x, f x ∂(Measure.map (fun y => (y - ((n : ℝ) - 1) * a) / 1)
        (Measure.convPow (Measure.dirac a) n)) = f a := by
    intro n
    rw [Measure.convPow_dirac, Measure.map_dirac]
    simp only [nsmul_eq_mul]
    rw [integral_dirac]
    congr 1
    field_simp
    ring
  simp_rw [hterm, integral_dirac]
  exact tendsto_const_nhds

end MathlibExt.Probability.StableDistribution
