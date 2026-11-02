/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.MonotoneLimit
public import PhyslibExt.StatisticalMechanics.RandomCluster.Limits
/-!
# Ordering of free and wired subsequential limits

Weak limits of free and wired box measures along a common subsequence are ordered.

## i. Overview

For `q ≥ 1`, `freeFiniteMeasure_dominated` gives `φ⁰_n(A) ≤ φ¹_n(A)` for every increasing event.
If `φ⁰_(ψ n) → ν₀` and `φ¹_(ψ n) → ν₁` weakly along the same subsequence `ψ`, the inequality
passes to the limit for clopen increasing events (cylinder events), whose indicators are
continuous. Prokhorov compactness, applied twice, provides such a common subsequence.

## ii. Key results

- `weakLimit_extremality_of_common_subseq` : `ν₀(A) ≤ ν₁(A)` for clopen increasing `A`.
- `exists_common_subseq_weak_limits` : a common subsequence along which both converge.
- `exists_infiniteVolume_extremal` : existence of an ordered pair of limits.

## iii. Table of contents

- A. Domination passes to weak limits
- B. Existence of ordered limit pairs

## iv. References

- G. R. Grimmett, *The Random-Cluster Model*, Springer, 2006.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

/-!
## A. Domination passes to weak limits
-/

/-- If free and wired box measures converge weakly to `ν₀` and `ν₁` along a common subsequence and
`q ≥ 1`, then `ν₀(A) ≤ ν₁(A)` for every clopen increasing event `A`. -/
lemma weakLimit_extremality_of_common_subseq (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {ν₀ ν₁ : ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))}
    {ψ : ℕ → ℕ}
    (h₀ : WeakConvergesTo
      (fun n => freeFiniteMeasure d (ψ n) hp hp1 (zero_lt_one.trans_le hq)) ν₀)
    (h₁ : WeakConvergesTo
      (fun n => wiredFiniteMeasure d (ψ n) hp hp1 (zero_lt_one.trans_le hq)) ν₁)
    {A : Set (ConfigSpace (Sym2 (Lattice.Site d)))}
    (hAclopen : IsClopen A) (hAinc : IsIncreasing A) :
    (ν₀ : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real A
      ≤ (ν₁ : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real A := by
  have ht₀ := h₀.tendsto_real_of_isClopen hAclopen
  have ht₁ := h₁.tendsto_real_of_isClopen hAclopen
  have hAmeas : MeasurableSet A := hAclopen.isOpen.measurableSet
  have hdom : ∀ n,
      (freeFiniteMeasure d (ψ n) hp hp1 (zero_lt_one.trans_le hq)
          : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real A
        ≤ (wiredFiniteMeasure d (ψ n) hp hp1 (zero_lt_one.trans_le hq)
          : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real A :=
    fun n => freeFiniteMeasure_dominated d (ψ n) hp hp1 hq A hAmeas hAinc
  exact le_of_tendsto_of_tendsto ht₀ ht₁ (Filter.Eventually.of_forall hdom)

/-!
## B. Existence of ordered limit pairs
-/

/-- Free and wired box measures have weak limits along a common strictly increasing subsequence. -/
lemma exists_common_subseq_weak_limits (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∃ (ψ : ℕ → ℕ) (ν₀ ν₁ : ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))),
      StrictMono ψ ∧
        WeakConvergesTo (fun n => freeFiniteMeasure d (ψ n) hp hp1 hq) ν₀ ∧
        WeakConvergesTo (fun n => wiredFiniteMeasure d (ψ n) hp hp1 hq) ν₁ := by
  obtain ⟨ν₀, φ, hφ, h₀⟩ :=
    CompactSpace.tendsto_subseq (fun n => freeFiniteMeasure d n hp hp1 hq)
  obtain ⟨ν₁, χ, hχ, h₁⟩ :=
    CompactSpace.tendsto_subseq (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
  exact ⟨φ ∘ χ, ν₀, ν₁, hφ.comp hχ, h₀.comp hχ.tendsto_atTop, h₁⟩

/-- For `q ≥ 1` there are a subsequence and weak limits `φ0` (free) and `φ1` (wired) along it with
`φ0(A) ≤ φ1(A)` for all clopen increasing `A`. -/
lemma exists_infiniteVolume_extremal (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    ∃ (ψ : ℕ → ℕ) (φ0 φ1 : ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))),
      StrictMono ψ ∧
        WeakConvergesTo
          (fun n => freeFiniteMeasure d (ψ n) hp hp1 (zero_lt_one.trans_le hq)) φ0 ∧
        WeakConvergesTo
          (fun n => wiredFiniteMeasure d (ψ n) hp hp1 (zero_lt_one.trans_le hq)) φ1 ∧
        ∀ A : Set (ConfigSpace (Sym2 (Lattice.Site d))),
          IsClopen A → IsIncreasing A →
            (φ0 : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real A
              ≤ (φ1 : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real A := by
  obtain ⟨ψ, ν₀, ν₁, hψ, h₀, h₁⟩ :=
    exists_common_subseq_weak_limits d hp hp1 (zero_lt_one.trans_le hq)
  refine ⟨ψ, ν₀, ν₁, hψ, h₀, h₁, ?_⟩
  intro A hAclopen hAinc
  exact weakLimit_extremality_of_common_subseq d hp hp1 hq h₀ h₁ hAclopen hAinc

end FK

end StatMech
