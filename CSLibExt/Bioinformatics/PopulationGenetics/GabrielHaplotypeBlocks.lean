/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Interval.Basic
public import Mathlib.Order.Interval.Finset.Fin

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Region weights for Gabriel haplotype blocks

The SNPs of a chromosome are indexed in order by `Fin n`. Only input entries with `u < v`
are used for valid regions. They represent 90% confidence intervals for `|D'|`; the model
does not estimate the intervals or check their coverage. `NonemptyInterval ℝ` enforces
`C_L ≤ C_U` but not that the endpoints lie in `[0, 1]`: the results hold for any ordered
intervals, and valid confidence intervals are the caller's input.

We use the inclusive strong-LD cutoffs of Taliun, Gamper and Pattaro. Gabriel et al. describe
the strong-LD cutoffs with strict inequalities. Both use a strict cutoff for strong evidence
of historical recombination.

## References

* D. Taliun, J. Gamper and C. Pattaro, *Efficient haplotype block recognition of very long and
  dense genetic sequences*, BMC Bioinformatics 15 (2014), 10, Methods, Definitions 1 to 3
  and Theorem 1. <https://doi.org/10.1186/1471-2105-15-10>
* S. B. Gabriel et al., *The structure of haplotype blocks in the human genome*, Science 296
  (2002), 2225–2229. <https://doi.org/10.1126/science.1069424>
-/

@[expose] public section

open scoped BigOperators

namespace Cslib.Bioinformatics.PopulationGenetics.GabrielHaplotypeBlocks

/-- A SNP pair is in strong linkage disequilibrium, shows strong evidence of historical
recombination, or is non-informative. -/
inductive PairKind
  | strongLD
  | strongEHR
  | nonInformative
  deriving DecidableEq

/-- Classify a supplied 90% confidence interval `[C_L, C_U]` for `|D'|`. Strong LD requires
`C_L ≥ 0.7` and `C_U ≥ 0.98`. Strong evidence of historical recombination requires `C_U < 0.9`.
Every other interval is non-informative. The endpoint comparisons use exact real numbers. -/
noncomputable def classify (ci : NonemptyInterval ℝ) : PairKind :=
  if (0.7 : ℝ) ≤ ci.fst ∧ (0.98 : ℝ) ≤ ci.snd then .strongLD
  else if ci.snd < (0.9 : ℝ) then .strongEHR
  else .nonInformative

variable {n : ℕ}

/-- The pairs `(u, v)` with `i ≤ u < v ≤ j`, each listed once. Both endpoints are included. -/
def regionPairs (i j : Fin n) : Finset (Fin n × Fin n) :=
  ((Finset.Icc i j) ×ˢ (Finset.Icc i j)).filter (fun p => p.1 < p.2)

/-- The number of pairs of the given kind inside the inclusive region from `i` through `j`. -/
noncomputable def pairCount (ci : Fin n → Fin n → NonemptyInterval ℝ) (i j : Fin n)
    (kind : PairKind) : ℕ :=
  ((regionPairs i j).filter (fun p => classify (ci p.1 p.2) = kind)).card

/-- The pair weight at threshold `d`: `1 - d` for strong LD, `-d` for strong evidence of
historical recombination, and `0` for a non-informative pair. -/
def pairWeight (d : ℝ) : PairKind → ℝ
  | .strongLD => 1 - d
  | .strongEHR => -d
  | .nonInformative => 0

/-- The region weight at threshold `d`, summed over all pairs `i ≤ u < v ≤ j`. -/
noncomputable def regionWeight (ci : Fin n → Fin n → NonemptyInterval ℝ) (d : ℝ)
    (i j : Fin n) : ℝ :=
  ∑ p ∈ regionPairs i j, pairWeight d (classify (ci p.1 p.2))

/-- The inclusive region from `i` to `j` is a Gabriel haplotype block at threshold `d` if
`i < j`, its outer pair is in strong LD, and `l / (l + r) ≥ d` over the reals, where `l` counts
strong-LD pairs and `r` counts strong-EHR pairs inside the region. The outer pair then ensures
`l + r > 0`. -/
def IsHaplotypeBlock (ci : Fin n → Fin n → NonemptyInterval ℝ) (d : ℝ) (i j : Fin n) : Prop :=
  i < j ∧ classify (ci i j) = .strongLD ∧
    d ≤ (pairCount ci i j .strongLD : ℝ) /
      ((pairCount ci i j .strongLD : ℝ) + pairCount ci i j .strongEHR)

private theorem regionWeight_eq (ci : Fin n → Fin n → NonemptyInterval ℝ) (d : ℝ)
    (i j : Fin n) :
    regionWeight ci d i j = (pairCount ci i j .strongLD : ℝ) -
      d * ((pairCount ci i j .strongLD : ℝ) + pairCount ci i j .strongEHR) := by
  calc
    regionWeight ci d i j = ∑ p ∈ regionPairs i j,
        ((if classify (ci p.1 p.2) = .strongLD then 1 - d else 0) +
          (if classify (ci p.1 p.2) = .strongEHR then -d else 0)) := by
      apply Finset.sum_congr rfl
      intro p _
      cases classify (ci p.1 p.2) <;> simp [pairWeight]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
      simp only [pairCount, Finset.sum_const, nsmul_eq_mul]
      ring

/-- For chromosome indices `i < j` and `0 < d < 1`, the region from `i` through `j` is a Gabriel
haplotype block if and only if the outer pair has weight `1 - d` and the region weight is
nonnegative. Taliun, Gamper and Pattaro, Theorem 1, state the implication from the two weight
conditions to the block; this theorem also proves the converse.

The positive lower bound on `d` is part of the threshold convention, not needed for the
equivalence. At `d = 1`, a non-informative pair also has weight `1 - d`. The order `i < j`
ensures that the outer pair is counted. -/
theorem isHaplotypeBlock_iff_regionWeight (ci : Fin n → Fin n → NonemptyInterval ℝ)
    {d : ℝ} (hd : d ∈ Set.Ioo (0 : ℝ) 1) {i j : Fin n} (hij : i < j) :
    IsHaplotypeBlock ci d i j ↔
      pairWeight d (classify (ci i j)) = 1 - d ∧ 0 ≤ regionWeight ci d i j := by
  have hOuter : pairWeight d (classify (ci i j)) = 1 - d ↔
      classify (ci i j) = .strongLD := by
    cases classify (ci i j) <;> simp [pairWeight] <;> linarith [hd.2]
  rw [hOuter, IsHaplotypeBlock, and_iff_right hij]
  refine and_congr_right fun hLD => ?_
  have hcount : 0 < pairCount ci i j .strongLD := by
    refine Finset.card_pos.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨?_, hLD⟩⟩
    simp [regionPairs, hij, hij.le]
  have hpos : (0 : ℝ) < (pairCount ci i j .strongLD : ℝ) + pairCount ci i j .strongEHR := by
    exact_mod_cast Nat.add_pos_left hcount (pairCount ci i j .strongEHR)
  rw [le_div_iff₀ hpos, regionWeight_eq, sub_nonneg]

end Cslib.Bioinformatics.PopulationGenetics.GabrielHaplotypeBlocks
