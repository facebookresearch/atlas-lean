/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.FStatistics
public import MathlibExt.Combinatorics.SimpleGraph.TreeMetric

/-!
# The quartet f4 trichotomy from the f2 pair sums

For square-integrable frequencies, write the three pair sums of a quartet
`A B C D` as `S1 = f2AB + f2CD`, `S2 = f2AC + f2BD`, `S3 = f2AD + f2BC`. The
three f4 permutations are the half-differences `(S3 - S2)/2`, `(S3 - S1)/2`,
`(S2 - S1)/2`. Hence under the four-point condition on `f2` (which a tree
metric supplies, by Buneman's theorem) at least one permutation vanishes; if
moreover `S1` is the smallest pair sum (split `AB|CD`) then `f4(A,B;C,D) = 0`
and the crossing permutations are equal to `(S2 - S1)/2 ≥ 0`; if all three
permutations are nonzero then `f2` is not a tree metric; and if
`S1 = S2 = S3` (zero internal branch) all three vanish.

These statements take the four-point condition or tree-metric property of
`f2` as hypotheses; deriving them from a tree-shaped admixture graph is a
separate bridge theorem.

## Main results

* `FStatistics.two_mul_f4_eq_sub`: f4 permutations as pair-sum differences.
* `FStatistics.f4_eq_zero_or_of_fourPointCondition`: one permutation vanishes
  under the four-point condition.
* `FStatistics.f4_split_of_isTreeMetric`: the split trichotomy.
* `FStatistics.not_isTreeMetric_of_f4_ne_zero`: all three nonzero excludes a
  tree metric.
* `FStatistics.f4_eq_zero_of_pairSums_eq`: the zero-internal-branch case.

## References

* P. Buneman, "The recovery of trees from measurements of dissimilarity",
  in *Mathematics in the Archaeological and Historical Sciences*, 1971.
* N. Patterson et al., "Ancient admixture in human history", *Genetics* 192
  (2012), 1065–1093 (f4 tests of treeness).
-/

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.Phylogenetics.Buneman
open scoped symmDiff

namespace MathlibExt.Biology.PopulationGenetics.FStatistics

variable {Ω P : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {p : P → Ω → ℝ}

/-- The three quartet pair sums and the f4 permutations: for square-integrable
frequencies,
`2 • f4(A,B;C,D) = (f2AD + f2BC) - (f2AC + f2BD)`, and likewise for the other
two pairings by relabelling. This is `f4_eq_f2` cleared of the denominator. -/
theorem two_mul_f4_eq_sub (hp : ∀ X, MemLp (p X) 2 μ) (A B C D : P) :
    2 * f4 μ p A B C D = (f2 μ p A D + f2 μ p B C) - (f2 μ p A C + f2 μ p B D) := by
  rw [f4_eq_f2 hp]
  ring

/-- For square-integrable frequencies, if `f2` satisfies the four-point
condition (as the `f2` matrix of a tree
model does, by `Buneman.IsTreeMetric.fourPointCondition`), then for every
four populations at least one of the three f4 permutations
`f4(A,B;C,D)`, `f4(A,C;B,D)`, `f4(A,D;B,C)` vanishes. The four-point
condition says each of the pair sums `S1 = f2AB+f2CD`, `S2 = f2AC+f2BD`,
`S3 = f2AD+f2BC` is at most the maximum of the other two, so two of them are
equal, and the f4 permutations are the half-differences of the pair sums. -/
theorem f4_eq_zero_or_of_fourPointCondition (hp : ∀ X, MemLp (p X) 2 μ)
    (h : FourPointCondition (f2 μ p)) (A B C D : P) :
    f4 μ p A B C D = 0 ∨ f4 μ p A C B D = 0 ∨ f4 μ p A D B C = 0 := by
  set s1 := f2 μ p A B + f2 μ p C D with hs1
  set s2 := f2 μ p A C + f2 μ p B D with hs2
  set s3 := f2 μ p A D + f2 μ p B C with hs3
  have h1 : s1 ≤ max s2 s3 := h A B C D
  have h2 : s2 ≤ max s1 s3 := by
    have := h A C B D
    rwa [f2_comm C B] at this
  have h3 : s3 ≤ max s1 s2 := by
    have := h A D B C
    rwa [f2_comm D C, f2_comm D B] at this
  have key : s1 = s2 ∨ s1 = s3 ∨ s2 = s3 := by
    by_contra hc
    push Not at hc
    obtain ⟨h12, h13, h23⟩ := hc
    rw [le_max_iff] at h1 h2 h3
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      first
        | exact h12 (by linarith)
        | exact h13 (by linarith)
        | exact h23 (by linarith)
  have e1 : 2 * f4 μ p A B C D = s3 - s2 := two_mul_f4_eq_sub hp A B C D
  have e2 : 2 * f4 μ p A C B D = s3 - s1 := by
    have := two_mul_f4_eq_sub hp A C B D
    rwa [f2_comm C B] at this
  have e3 : 2 * f4 μ p A D B C = s2 - s1 := by
    have := two_mul_f4_eq_sub hp A D B C
    rwa [f2_comm D B, f2_comm D C] at this
  rcases key with hh | hh | hh
  · exact Or.inr (Or.inr (by linarith))
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inl (by linarith)

/-- Quartet trichotomy for a split: for square-integrable frequencies, if `f2`
is a tree metric and the pair sum
`s1 = f2AB + f2CD` is at most the other two pair sums (the split is `AB|CD`),
then `f4(A,B;C,D) = 0` and the two crossing permutations are equal,
`f4(A,C;B,D) = f4(A,D;B,C) = ((f2AC + f2BD) - (f2AB + f2CD)) / 2 ≥ 0`, the
internal branch length of the quartet in pair-sum coordinates. -/
theorem f4_split_of_isTreeMetric (hp : ∀ X, MemLp (p X) 2 μ)
    (htree : IsTreeMetric (f2 μ p)) (A B C D : P)
    (h2 : f2 μ p A B + f2 μ p C D ≤ f2 μ p A C + f2 μ p B D)
    (h3 : f2 μ p A B + f2 μ p C D ≤ f2 μ p A D + f2 μ p B C) :
    f4 μ p A B C D = 0 ∧
      f4 μ p A C B D = ((f2 μ p A C + f2 μ p B D) - (f2 μ p A B + f2 μ p C D)) / 2 ∧
      f4 μ p A D B C = ((f2 μ p A C + f2 μ p B D) - (f2 μ p A B + f2 μ p C D)) / 2 ∧
      0 ≤ f4 μ p A C B D := by
  have h := htree.fourPointCondition
  set s1 := f2 μ p A B + f2 μ p C D with hs1
  set s2 := f2 μ p A C + f2 μ p B D with hs2
  set s3 := f2 μ p A D + f2 μ p B C with hs3
  have h3le : s3 ≤ max s1 s2 := by
    have := h A D B C
    rwa [f2_comm D C, f2_comm D B] at this
  have h2le : s2 ≤ max s1 s3 := by
    have := h A C B D
    rwa [f2_comm C B] at this
  have hs23 : s2 = s3 := by
    rw [le_max_iff] at h3le h2le
    rcases h3le with hh | hh <;> rcases h2le with hh2 | hh2 <;> linarith
  have e1 : 2 * f4 μ p A B C D = s3 - s2 := two_mul_f4_eq_sub hp A B C D
  have e2 : 2 * f4 μ p A C B D = s3 - s1 := by
    have := two_mul_f4_eq_sub hp A C B D
    rwa [f2_comm C B] at this
  have e3 : 2 * f4 μ p A D B C = s2 - s1 := by
    have := two_mul_f4_eq_sub hp A D B C
    rwa [f2_comm D B, f2_comm D C] at this
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- For square-integrable frequencies, if all three f4 permutations at some
four populations are nonzero, then
`f2` is not a tree metric, so the frequencies do not come from a drift model with
the lineage weights of a tree-shaped admixture graph. This is the contrapositive of
`f4_eq_zero_or_of_fourPointCondition` composed with Buneman's theorem. -/
theorem not_isTreeMetric_of_f4_ne_zero (hp : ∀ X, MemLp (p X) 2 μ) {A B C D : P}
    (h1 : f4 μ p A B C D ≠ 0) (h2 : f4 μ p A C B D ≠ 0) (h3 : f4 μ p A D B C ≠ 0) :
    ¬ IsTreeMetric (f2 μ p) := by
  intro htree
  rcases f4_eq_zero_or_of_fourPointCondition hp htree.fourPointCondition A B C D with
    hh | hh | hh
  · exact h1 hh
  · exact h2 hh
  · exact h3 hh

/-- Zero internal branch: for square-integrable frequencies, if the three
quartet pair sums are all equal, all
three f4 permutations vanish. No tree assumption is needed. -/
theorem f4_eq_zero_of_pairSums_eq (hp : ∀ X, MemLp (p X) 2 μ) (A B C D : P)
    (h1 : f2 μ p A B + f2 μ p C D = f2 μ p A C + f2 μ p B D)
    (h2 : f2 μ p A C + f2 μ p B D = f2 μ p A D + f2 μ p B C) :
    f4 μ p A B C D = 0 ∧ f4 μ p A C B D = 0 ∧ f4 μ p A D B C = 0 := by
  have e1 : 2 * f4 μ p A B C D =
      (f2 μ p A D + f2 μ p B C) - (f2 μ p A C + f2 μ p B D) := two_mul_f4_eq_sub hp A B C D
  have e2 : 2 * f4 μ p A C B D =
      (f2 μ p A D + f2 μ p B C) - (f2 μ p A B + f2 μ p C D) := by
    have := two_mul_f4_eq_sub hp A C B D
    rwa [f2_comm C B] at this
  have e3 : 2 * f4 μ p A D B C =
      (f2 μ p A C + f2 μ p B D) - (f2 μ p A B + f2 μ p C D) := by
    have := two_mul_f4_eq_sub hp A D B C
    rwa [f2_comm D B, f2_comm D C] at this
  refine ⟨by linarith, by linarith, by linarith⟩

end MathlibExt.Biology.PopulationGenetics.FStatistics
