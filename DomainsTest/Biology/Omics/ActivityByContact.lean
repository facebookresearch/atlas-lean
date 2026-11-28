/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Omics.ActivityByContact
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Tests for the activity-by-contact (ABC) score.

One gene, whose promoter is element `0`, and five candidate elements, four on chromosome `0` and
one on chromosome `1`:

| element | chromosome | position | DNase | H3K27ac | activity | contact |
|---|---|---|---|---|---|---|
| `0` (promoter) | `0` | 1 000 000 | 1 | 4 | 2 | 1 |
| `1` | `0` | 1 100 000 | 9 | 4 | 6 | 1/2 |
| `2` | `0` | 6 000 000 | 2 | 0 | 0 | 1/4 |
| `3` | `1` | 1 000 000 | 4 | 4 | 4 | 1/10 |
| `4` | `0` | 6 000 001 | 1 | 1 | 1 | 1/4 |

* the window: element `2`, exactly 5 Mb from the promoter, is in it; element `4`, one base pair
  further, and element `3`, at the promoter's position on another chromosome, are not;
* ground truth from the definition: the denominator is `2 * 1 + 6 * (1/2) + 0 * (1/4) = 5`, so the
  promoter scores `2/5`, element `1` scores `3/5`, and element `2`, accessible but not acetylated,
  scores `0`; elements `3` and `4`, outside the window, get no score;
* the theorems on these data: their hypotheses hold, the scores are nonnegative and those of the
  window sum to `1`; contacts need only be positive within the window;
* a gene gets no score when no element of its window is acetylated, however accessible;
* positive activity needs both signals positive. -/

open Domains.Biology.Omics.ActivityByContact

namespace DomainsTest.Biology.Omics.ActivityByContact

/-- The chromosomes of the five elements. -/
def chrom : Fin 5 → Fin 2 := ![0, 0, 0, 1, 0]

/-- The base-pair positions of the five elements. -/
def pos : Fin 5 → ℤ := ![1000000, 1100000, 6000000, 1000000, 6000001]

/-- The promoter of the one gene is element `0`. -/
def promoter : Unit → Fin 5 := fun _ => 0

/-- The chromatin-accessibility signals. -/
noncomputable def dnase : Fin 5 → ℝ := ![1, 9, 2, 4, 1]

/-- The H3K27ac signals. -/
noncomputable def h3k27ac : Fin 5 → ℝ := ![4, 4, 0, 4, 1]

/-- The contacts with the gene, including the self-contact `1` of its promoter. -/
noncomputable def contact : Fin 5 → Unit → ℝ := fun e _ => ![1, 1 / 2, 1 / 4, 1 / 10, 1 / 4] e

/-! ### The window of 5 Mb around the promoter -/

/-- Whatever the data, the window of a gene contains its promoter. -/
example {Chrom Element Gene : Type*} (chrom : Element → Chrom) (pos : Element → ℤ)
    (promoter : Gene → Element) (G : Gene) :
    chrom (promoter G) = chrom (promoter G) ∧
      |pos (promoter G) - pos (promoter G)| ≤ 5 * 10 ^ 6 := by
  norm_num

/-- Elements `0`, `1` and `2` are within 5 Mb of the promoter, element `2` at exactly 5 Mb. -/
theorem window_eq :
    ({e | chrom e = chrom (promoter ()) ∧ |pos e - pos (promoter ())| ≤ 5 * 10 ^ 6} :
      Finset (Fin 5)) = {0, 1, 2} := by
  decide

/-- The element one base pair beyond 5 Mb is not in the window. -/
example : ¬ |pos 4 - pos (promoter ())| ≤ 5 * 10 ^ 6 := by decide

/-- The element at the promoter's position on another chromosome is not in the window. -/
example : chrom 3 ≠ chrom (promoter ()) ∧ pos 3 = pos (promoter ()) := by decide

/-! ### Ground truth from the definition -/

theorem activity_zero : √(dnase 0 * h3k27ac 0) = 2 := by
  rw [show dnase 0 * h3k27ac 0 = 2 ^ 2 by norm_num [dnase, h3k27ac], Real.sqrt_sq (by norm_num)]

theorem activity_one : √(dnase 1 * h3k27ac 1) = 6 := by
  rw [show dnase 1 * h3k27ac 1 = 6 ^ 2 by norm_num [dnase, h3k27ac], Real.sqrt_sq (by norm_num)]

theorem activity_two : √(dnase 2 * h3k27ac 2) = 0 := by
  simp [dnase, h3k27ac]

theorem activity_three : √(dnase 3 * h3k27ac 3) = 4 := by
  rw [show dnase 3 * h3k27ac 3 = 4 ^ 2 by norm_num [dnase, h3k27ac], Real.sqrt_sq (by norm_num)]

/-- The denominator: `2 * 1 + 6 * (1/2) + 0 * (1/4) = 5`. -/
theorem total_eq :
    ∑ e with chrom e = chrom (promoter ()) ∧ |pos e - pos (promoter ())| ≤ 5 * 10 ^ 6,
      √(dnase e * h3k27ac e) * contact e () = 5 := by
  rw [window_eq, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, activity_zero, activity_one, activity_two]
  norm_num [contact]

theorem abcScore_eq (E : Fin 5)
    (hE : chrom E = chrom (promoter ()) ∧ |pos E - pos (promoter ())| ≤ 5 * 10 ^ 6) :
    abcScore chrom pos promoter dnase h3k27ac contact E () =
      some (√(dnase E * h3k27ac E) * contact E () / 5) := by
  simp only [abcScore, total_eq, hE]
  norm_num

/-- The promoter scores `2 * 1 / 5`. -/
example : abcScore chrom pos promoter dnase h3k27ac contact 0 () = some (2 / 5) := by
  rw [abcScore_eq 0 (by decide), activity_zero]
  norm_num [contact]

/-- The acetylated element 100 kb away scores `6 * (1/2) / 5`. -/
example : abcScore chrom pos promoter dnase h3k27ac contact 1 () = some (3 / 5) := by
  rw [abcScore_eq 1 (by decide), activity_one]
  norm_num [contact]

/-- The accessible but unacetylated element, exactly 5 Mb away, scores `0`. -/
example : abcScore chrom pos promoter dnase h3k27ac contact 2 () = some 0 := by
  rw [abcScore_eq 2 (by decide), activity_two]
  norm_num

/-- The element on another chromosome gets no score, though its activity is `4`. -/
example : abcScore chrom pos promoter dnase h3k27ac contact 3 () = none := by
  have h : ¬ (chrom 3 = chrom (promoter ()) ∧ |pos 3 - pos (promoter ())| ≤ 5 * 10 ^ 6) := by
    decide
  simp only [abcScore, h, false_and, ↓reduceIte]

/-- The element one base pair beyond 5 Mb gets no score. -/
example : abcScore chrom pos promoter dnase h3k27ac contact 4 () = none := by
  have h : ¬ (chrom 4 = chrom (promoter ()) ∧ |pos 4 - pos (promoter ())| ≤ 5 * 10 ^ 6) := by
    decide
  simp only [abcScore, h, false_and, ↓reduceIte]

/-! ### The theorems on these data -/

theorem contact_pos (e : Fin 5) : 0 < contact e () := by
  fin_cases e <;> norm_num [contact]

/-- Element `1` gets a score: it is in the window, and the promoter has positive activity. -/
theorem isSome : (abcScore chrom pos promoter dnase h3k27ac contact 1 ()).isSome :=
  (isSome_abcScore_iff fun e _ _ => contact_pos e).2
    ⟨by decide, 0, by decide, by decide, by rw [activity_zero]; norm_num⟩

/-- Contacts that vanish outside the window. -/
noncomputable def contactInWindow : Fin 5 → Unit → ℝ := fun e _ => ![1, 1 / 2, 1 / 4, 0, 0] e

/-- Contacts need only be positive within the window. -/
example : (abcScore chrom pos promoter dnase h3k27ac contactInWindow 0 ()).isSome := by
  refine (isSome_abcScore_iff fun e h1 h2 => ?_).2
    ⟨by decide, 0, by decide, by decide, by rw [activity_zero]; norm_num⟩
  have he : e ∈ ({0, 1, 2} : Finset (Fin 5)) := by
    rw [← window_eq]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ e, h1, h2⟩
  fin_cases e <;> simp_all [contactInWindow]

example (E : Fin 5) {s : ℝ} (h : abcScore chrom pos promoter dnase h3k27ac contact E () = some s) :
    0 ≤ s :=
  abcScore_nonneg (contact_pos E).le h

/-- The scores of the window sum to `1`, as `2/5 + 3/5 + 0` does. -/
example : ∃ s : Fin 5 → ℝ,
    (∀ E, chrom E = chrom (promoter ()) → |pos E - pos (promoter ())| ≤ 5 * 10 ^ 6 →
      abcScore chrom pos promoter dnase h3k27ac contact E () = some (s E)) ∧
      ∑ E with chrom E = chrom (promoter ()) ∧ |pos E - pos (promoter ())| ≤ 5 * 10 ^ 6, s E = 1 :=
  exists_abcScore_sum_eq_one isSome

/-! ### No acetylation, no score -/

/-- With no H3K27ac signal anywhere, every activity vanishes and the gene gets no score, however
accessible its elements are. -/
example (E : Fin 5) : abcScore chrom pos promoter dnase (fun _ => 0) contact E () = none := by
  rw [← Option.not_isSome_iff_eq_none, isSome_abcScore_iff fun e _ _ => contact_pos e]
  simp

/-! ### Positive activity needs both signals -/

/-- For nonnegative signals, the activity `√(d * h)` is positive exactly when both are. -/
example (d h : ℝ) (hd : 0 ≤ d) : 0 < √(d * h) ↔ 0 < d ∧ 0 < h := by
  rw [Real.sqrt_pos]
  refine ⟨fun hdh => ?_, fun hdh => mul_pos hdh.1 hdh.2⟩
  exact (pos_and_pos_or_neg_and_neg_of_mul_pos hdh).resolve_right fun h' => hd.not_gt h'.1

end DomainsTest.Biology.Omics.ActivityByContact
