/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Integration.RiemannPartition
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Riemann sums under refinement

If `T'` is a tagged refinement of `T`, then the Riemann sums of `f` with
respect to `T` and `T'` differ by at most the oscillation of `f` at the
mesh scale of `T` times the length `b - a` of the interval. The book states
this (Theorem II) with the oscillation measured by the modulus of
continuity `w_f(‖T‖)` and `f` continuous on `[a, b]`; here it is stated
with an explicit oscillation bound `ω`, which is both more general (no
continuity is needed, only the bound at the mesh scale) and independent of
the modulus-of-continuity API. The book's Theorem III, the bound for two
arbitrary tagged partitions in terms of a common refinement, follows by
the triangle inequality.

## Main definitions

* `TaggedPartition.IsTaggedRefinement`: `T'` is a tagged refinement of `T`
  when every subinterval of `T'` is contained in some subinterval of `T`
  (witnessed by `assign`), and the subintervals of `T'` assigned to each
  `T`-subinterval telescope to its length.

## Main results

* `riemannSum_eq_fiber`: the Riemann sum over `T` rewritten as a sum over
  the refinement `T'`, grouped by the parent subinterval.
* `riemannSum_sub_le_of_isTaggedRefinement`: Theorem II in oscillation form.
* `riemannSum_sub_le_of_commonRefinement`: Theorem III in oscillation form,
  given a common tagged refinement.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Theorems II and III, "The
Riemann Integral section", and
`v1/Atlas/RealAnalysis/code/Integration/ModulusContinuity.lean`
(`TaggedPartition.IsTaggedRefinement`, `riemannSum_eq_fiber`,
`riemannSum_sub_le_modulusOfContinuity_mul`,
`riemannSum_sub_le_modulusOfContinuity_add_mul_of_commonRefinement`).
In v1 the oscillation is `modulusOfContinuity f a b T.toPartition.mesh`
and `f` is assumed continuous on `[a, b]`; here the bound is an explicit
hypothesis `hω`, so continuity is not needed.
-/

@[expose] public section

namespace MathlibExt.Analysis.Integration

variable {a b : ℝ}

/-- `T'` is a tagged refinement of `T` when every subinterval of `T'` is
contained in some subinterval of `T` (witnessed by `assign`), and the
subintervals of `T'` assigned to each `T`-subinterval telescope to its
length. This captures the condition `x ⊂ x'` in Theorem II. -/
structure TaggedPartition.IsTaggedRefinement (T T' : TaggedPartition a b) where
  assign : Fin T'.n → Fin T.n
  contained_left : ∀ j : Fin T'.n, T.points (assign j).castSucc ≤ T'.points j.castSucc
  contained_right : ∀ j : Fin T'.n, T'.points j.succ ≤ T.points (assign j).succ
  telescope : ∀ k : Fin T.n,
    ∑ j ∈ Finset.univ.filter (fun j => assign j = k),
      (T'.points j.succ - T'.points j.castSucc) = T.points k.succ - T.points k.castSucc

/-- The Riemann sum `S_f(T)` can be rewritten by summing over the refinement
`T'`: each summand uses the tag of `T` at the parent subinterval and the
length of the finer `T'`-subinterval. -/
lemma riemannSum_eq_fiber (f : ℝ → ℝ) (T T' : TaggedPartition a b)
    (href : T.IsTaggedRefinement T') :
    riemannSum f T = ∑ j : Fin T'.n,
      f (T.tags (href.assign j)) * (T'.points j.succ - T'.points j.castSucc) := by
  unfold riemannSum
  conv_lhs => arg 2; ext k; rw [← href.telescope k, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := href.assign) (fun i _ => Finset.mem_univ _)]
  congr 1; ext k
  apply Finset.sum_congr rfl
  intro j hj; simp only [Finset.mem_filter] at hj; rw [← hj.2]

/-- **Theorem II (oscillation form).** If `T'` is a tagged refinement of
`T` and the oscillation of `f` on `[a, b]` at the mesh scale of `T` is at
most `ω`, then `|S_f(T) - S_f(T')| ≤ ω * (b - a)`. -/
theorem riemannSum_sub_le_of_isTaggedRefinement
    (f : ℝ → ℝ) (T T' : TaggedPartition a b) {ω : ℝ}
    (hω : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |x - y| ≤ T.toPartition.mesh → |f x - f y| ≤ ω)
    (href : T.IsTaggedRefinement T') :
    |riemannSum f T - riemannSum f T'| ≤ ω * (b - a) := by
  rw [riemannSum_eq_fiber f T T' href]
  have hdiff : (∑ j : Fin T'.n,
      f (T.tags (href.assign j)) * (T'.points j.succ - T'.points j.castSucc)) -
    riemannSum f T' =
    ∑ j : Fin T'.n, (f (T.tags (href.assign j)) - f (T'.tags j)) *
      (T'.points j.succ - T'.points j.castSucc) := by
    unfold riemannSum
    rw [← Finset.sum_sub_distrib]
    congr 1; ext j; ring
  rw [hdiff]
  calc |∑ j : Fin T'.n, (f (T.tags (href.assign j)) - f (T'.tags j)) *
        (T'.points j.succ - T'.points j.castSucc)|
      ≤ ∑ j : Fin T'.n, |(f (T.tags (href.assign j)) - f (T'.tags j)) *
        (T'.points j.succ - T'.points j.castSucc)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin T'.n, |f (T.tags (href.assign j)) - f (T'.tags j)| *
          (T'.points j.succ - T'.points j.castSucc) := by
            congr 1; ext j
            rw [abs_mul, abs_of_nonneg (T'.toPartition.succ_sub_castSucc_nonneg j)]
    _ ≤ ∑ j : Fin T'.n, ω *
          (T'.points j.succ - T'.points j.castSucc) := by
            apply Finset.sum_le_sum; intro j _
            apply mul_le_mul_of_nonneg_right _
              (T'.toPartition.succ_sub_castSucc_nonneg j)
            refine hω _ (T.tag_mem_Icc (href.assign j)) _
              (T'.tag_mem_Icc j) ?_
            set k := href.assign j
            have htk := T.tag_mem k
            have htj := T'.tag_mem j
            have hleft := href.contained_left j
            have hright := href.contained_right j
            have habs : |T.tags k - T'.tags j| ≤
                T.points k.succ - T.points k.castSucc := by
              rw [abs_le]
              exact ⟨by linarith [htk.1, htj.2, hright],
                     by linarith [htj.1, hleft, htk.2]⟩
            exact habs.trans (T.toPartition.le_mesh k)
    _ = ω * (b - a) := by
            rw [← Finset.mul_sum, T'.toPartition.sum_sub_eq]

/-- **Theorem III (oscillation form, given a common refinement).** For
tagged partitions `T₁, T₂` that share a common tagged refinement `T''`,
and oscillation bounds `ω₁, ω₂` at their respective mesh scales,
`|S_f(T₁) - S_f(T₂)| ≤ (ω₁ + ω₂) * (b - a)`. -/
theorem riemannSum_sub_le_of_commonRefinement
    (f : ℝ → ℝ) (T₁ T₂ : TaggedPartition a b) {ω₁ ω₂ : ℝ}
    (hω₁ : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |x - y| ≤ T₁.toPartition.mesh → |f x - f y| ≤ ω₁)
    (hω₂ : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |x - y| ≤ T₂.toPartition.mesh → |f x - f y| ≤ ω₂)
    (T'' : TaggedPartition a b)
    (href₁ : T₁.IsTaggedRefinement T'')
    (href₂ : T₂.IsTaggedRefinement T'') :
    |riemannSum f T₁ - riemannSum f T₂| ≤ (ω₁ + ω₂) * (b - a) := by
  have h1 := riemannSum_sub_le_of_isTaggedRefinement f T₁ T'' hω₁ href₁
  have h2 := riemannSum_sub_le_of_isTaggedRefinement f T₂ T'' hω₂ href₂
  calc |riemannSum f T₁ - riemannSum f T₂|
      = |(riemannSum f T₁ - riemannSum f T'') + (riemannSum f T'' - riemannSum f T₂)| := by
          ring_nf
    _ ≤ |riemannSum f T₁ - riemannSum f T''| + |riemannSum f T'' - riemannSum f T₂| :=
          abs_add_le _ _
    _ = |riemannSum f T₁ - riemannSum f T''| + |riemannSum f T₂ - riemannSum f T''| := by
          rw [abs_sub_comm (riemannSum f T'') (riemannSum f T₂)]
    _ ≤ ω₁ * (b - a) + ω₂ * (b - a) := by
          linarith
    _ = (ω₁ + ω₂) * (b - a) := by
          ring

end MathlibExt.Analysis.Integration
