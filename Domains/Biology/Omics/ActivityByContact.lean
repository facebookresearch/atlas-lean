/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Field

/-!
# The activity-by-contact (ABC) score

The activity-by-contact model of Fulco et al. (2019) predicts which candidate regulatory elements
regulate which genes in one cell type. A candidate element `E` has an **activity**

  `A E = √(DNase E * H3K27ac E)`,

the geometric mean of its nonnegative (quantile-normalized) chromatin-accessibility and H3K27ac
signals, the same for every gene. An element `E` and a gene `G` have a positive **contact**
`C E G`, the contact frequency between `E` and the transcription start site of `G`, measured by
Hi-C or approximated by a power law `C E G ∝ d(E, G)⁻¹` in the genomic distance; the self-contact
of the promoter of `G`, where that distance is zero, is set to a finite positive value. The
**ABC score** of the pair is

  `ABC E G = A E * C E G / ∑ e ∈ 𝓔 G, A e * C e G`,

where `𝓔 G` is the set of candidate elements within 5 Mb of the promoter of `G`, the promoter
included. Only the elements of `𝓔 G` are scored for `G`, and a gene whose denominator is not
positive gets no score. An element is predicted to regulate `G` when its score exceeds a chosen
threshold.

## Conventions

* The candidate elements of the cell type form a finite type `Element`. Each lies on a chromosome
  `chrom e` at a base-pair position `pos e : ℤ`, such as its midpoint. Two elements are within
  5 Mb of each other when they lie on the same chromosome and their positions differ by at most
  `5 * 10 ^ 6` base pairs.
* Each gene `G` has a promoter `promoter G`, itself a candidate element, so that `𝓔 G` is the set
  of elements within 5 Mb of `promoter G` and contains it.
* The signals `dnase`, `h3k27ac` and the contacts `contact` are real inputs. The source takes the
  signals nonnegative and the contacts positive; each theorem assumes only what it uses: positive
  contacts of the gene with the elements of `𝓔 G` in `isSome_abcScore_iff`, a nonnegative contact
  in `abcScore_nonneg`, and nothing in `exists_abcScore_sum_eq_one`.
* The score is an `Option ℝ`: `none` for an element outside `𝓔 G`, and for every element when the
  denominator of `G` is not positive, so that such a gene gets no score; otherwise every element
  of `𝓔 G` gets the value of the formula, and these values sum to `1`.

## Main definition

* `abcScore chrom pos promoter dnase h3k27ac contact E G`: the ABC score of the element `E` and
  the gene `G`.

## Main results

* `isSome_abcScore_iff`: with positive contacts in the window, an element gets a score for a gene
  exactly when it lies within 5 Mb of the gene's promoter and some element there has positive
  activity.
* `abcScore_nonneg`: a score is nonnegative when its contact is.
* `exists_abcScore_sum_eq_one`: when a gene gets a score, every element within 5 Mb of its
  promoter gets one, and these scores sum to `1`.

## References

* C. P. Fulco, J. Nasser, T. R. Jones et al., "Activity-by-contact model of enhancer–promoter
  regulation from thousands of CRISPR perturbations", Nat. Genet. 51 (2019), 1664–1669,
  <https://doi.org/10.1038/s41588-019-0538-0>: Results (the ABC model and Fig. 3) and Methods,
  "Calculating the contribution of one candidate element relative to others in the region".
-/

@[expose] public section

namespace Domains.Biology.Omics.ActivityByContact

variable {Chrom Element Gene : Type*} [Fintype Element] [DecidableEq Chrom]

/-- The **activity-by-contact (ABC) score** of a candidate regulatory element `E` and a gene `G`
in one cell type (Fulco et al. 2019):

  `ABC E G = A E * C E G / ∑ e ∈ 𝓔 G, A e * C e G`.

Here `A e = √(dnase e * h3k27ac e)` is the activity of `e`, the geometric mean of its nonnegative
(quantile-normalized) chromatin-accessibility signal `dnase e` and H3K27ac signal `h3k27ac e`, the
same for every gene, and `C e G = contact e G` is the positive contact frequency between `e` and
the transcription start site of `G` (from Hi-C, or a power law `∝ d(e, G)⁻¹` in the genomic
distance), including the finite positive self-contact of the promoter of `G`. The candidate
elements form the finite type `Element`; the element `e` lies on chromosome `chrom e` at base-pair
position `pos e`, and `𝓔 G` is the set of elements within 5 Mb of the promoter `promoter G` of
`G`: those on its chromosome whose position differs from its own by at most `5 * 10 ^ 6`, the
promoter included.

Only the elements of `𝓔 G` are scored for `G`: the score is `none` when `E` is not in `𝓔 G`,
and when the denominator `∑ e ∈ 𝓔 G, A e * C e G` is not positive, in which case the gene gets
no score at all. Otherwise every element `E` of `𝓔 G` gets the value of the formula, and these
scores sum to `1` (`exists_abcScore_sum_eq_one`). With positive contacts in the window, the
denominator is positive exactly when some element of `𝓔 G` has positive activity
(`isSome_abcScore_iff`). An element is predicted to regulate `G` when its score exceeds a chosen
threshold. -/
noncomputable def abcScore (chrom : Element → Chrom) (pos : Element → ℤ)
    (promoter : Gene → Element) (dnase h3k27ac : Element → ℝ) (contact : Element → Gene → ℝ)
    (E : Element) (G : Gene) : Option ℝ :=
  let activity : Element → ℝ := fun e => √(dnase e * h3k27ac e)
  let total : ℝ := ∑ e with chrom e = chrom (promoter G) ∧ |pos e - pos (promoter G)| ≤ 5 * 10 ^ 6,
    activity e * contact e G
  if (chrom E = chrom (promoter G) ∧ |pos E - pos (promoter G)| ≤ 5 * 10 ^ 6) ∧ 0 < total then
    some (activity E * contact E G / total)
  else none

variable {chrom : Element → Chrom} {pos : Element → ℤ} {promoter : Gene → Element}
  {dnase h3k27ac : Element → ℝ} {contact : Element → Gene → ℝ} {E : Element} {G : Gene}

/-- With positive contacts of the gene `G` with the candidate elements within 5 Mb of its promoter,
the ABC score of an element `E` and `G` is defined exactly when `E` lies within 5 Mb of the
promoter of `G` and some element there has positive activity `√(dnase e * h3k27ac e)`. -/
theorem isSome_abcScore_iff
    (hcontact : ∀ e, chrom e = chrom (promoter G) → |pos e - pos (promoter G)| ≤ 5 * 10 ^ 6 →
      0 < contact e G) :
    (abcScore chrom pos promoter dnase h3k27ac contact E G).isSome ↔
      (chrom E = chrom (promoter G) ∧ |pos E - pos (promoter G)| ≤ 5 * 10 ^ 6) ∧
        ∃ e, chrom e = chrom (promoter G) ∧ |pos e - pos (promoter G)| ≤ 5 * 10 ^ 6 ∧
          0 < √(dnase e * h3k27ac e) := by
  have hterm : ∀ e ∈ ({e | chrom e = chrom (promoter G) ∧
      |pos e - pos (promoter G)| ≤ 5 * 10 ^ 6} : Finset Element),
      0 < √(dnase e * h3k27ac e) * contact e G ↔ 0 < √(dnase e * h3k27ac e) := by
    intro e he
    rw [Finset.mem_filter] at he
    exact mul_pos_iff_of_pos_right (hcontact e he.2.1 he.2.2)
  have hsum : 0 < ∑ e with chrom e = chrom (promoter G) ∧ |pos e - pos (promoter G)| ≤ 5 * 10 ^ 6,
      √(dnase e * h3k27ac e) * contact e G ↔
      ∃ e, chrom e = chrom (promoter G) ∧ |pos e - pos (promoter G)| ≤ 5 * 10 ^ 6 ∧
        0 < √(dnase e * h3k27ac e) := by
    rw [Finset.sum_pos_iff_of_nonneg fun e he =>
      mul_nonneg (Real.sqrt_nonneg _) (hcontact e (Finset.mem_filter.1 he).2.1
        (Finset.mem_filter.1 he).2.2).le]
    constructor
    · rintro ⟨e, he, hpos⟩
      exact ⟨e, (Finset.mem_filter.1 he).2.1, (Finset.mem_filter.1 he).2.2, (hterm e he).1 hpos⟩
    · rintro ⟨e, h1, h2, hpos⟩
      have he : e ∈ ({e | chrom e = chrom (promoter G) ∧
          |pos e - pos (promoter G)| ≤ 5 * 10 ^ 6} : Finset Element) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ e, h1, h2⟩
      exact ⟨e, he, (hterm e he).2 hpos⟩
  simp only [abcScore]
  split_ifs with h
  · simp only [Option.isSome_some, true_iff]
    exact ⟨h.1, hsum.1 h.2⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun ⟨hE, hex⟩ => h ⟨hE, hsum.2 hex⟩

/-- An ABC score is nonnegative when its contact is: the activity, a square root, is nonnegative,
and the denominator of a defined score is positive. -/
theorem abcScore_nonneg (hcontact : 0 ≤ contact E G) {s : ℝ}
    (h : abcScore chrom pos promoter dnase h3k27ac contact E G = some s) : 0 ≤ s := by
  simp only [abcScore] at h
  split_ifs at h with htotal
  rw [Option.some_inj] at h
  rw [← h]
  exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hcontact) htotal.2.le

/-- When the gene `G` gets an ABC score for some element `E₀`, every candidate element `E` within
5 Mb of the promoter of `G` gets one, and these scores sum to `1`: they are the fractions of the
gene's total activity-by-contact that these elements contribute. -/
theorem exists_abcScore_sum_eq_one {E₀ : Element}
    (h : (abcScore chrom pos promoter dnase h3k27ac contact E₀ G).isSome) :
    ∃ s : Element → ℝ,
      (∀ E, chrom E = chrom (promoter G) → |pos E - pos (promoter G)| ≤ 5 * 10 ^ 6 →
        abcScore chrom pos promoter dnase h3k27ac contact E G = some (s E)) ∧
      ∑ E with chrom E = chrom (promoter G) ∧ |pos E - pos (promoter G)| ≤ 5 * 10 ^ 6, s E = 1 := by
  simp only [abcScore] at h ⊢
  split_ifs at h with htotal
  · exact ⟨_, fun E h1 h2 => ite_eq_left ⟨⟨h1, h2⟩, htotal.2⟩,
      by rw [← Finset.sum_div, div_self htotal.2.ne']⟩
  · simp at h

end Domains.Biology.Omics.ActivityByContact
