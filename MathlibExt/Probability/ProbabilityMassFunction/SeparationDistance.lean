/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Alexei Kopylov
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 689

/-!
# Separation distance between two PMFs

## References

* Riffle shuffles of a deck with repeated cards, Sami Assaf, Persi Diaconis, K. Soundararajan
  arXiv:0905.4698, §1, eq. 4. The separation distance defined by, $$, SEP(a) = \max_\sigma 1 -
  \frac{Q_a(\sigma)}{U(\sigma)}. $$ (for `separationDistance`)
-/

namespace MetaMathlibExt

-- Combinatorics 689: Separation distance between two PMFs

/-- Real-valued mass of a probability mass function at a point. -/

abbrev pmfReal  {α : Type*} (p : PMF α) (a : α) : ℝ := (p a).toReal

/- We need some auxilary lemmas to give the definition of separation distance. -/

theorem pmfReal_nonneg  {α : Type*} (p : PMF α) (a : α) : 0 ≤ pmfReal p a :=
  ENNReal.toReal_nonneg

theorem pmfReal_sum  {α : Type*} [Fintype α] (p : PMF α) : ∑ a, pmfReal p a = 1 := by
  have h1 : ∑ a, p a = (1 : ENNReal) := by
    have h := p.tsum_coe
    rwa [tsum_fintype] at h
  have h2 : (∑ a, p a).toReal = ∑ a, pmfReal p a := by
    have h := ENNReal.toReal_sum (s := Finset.univ) (f := fun a => p a)
      (fun a _ => p.apply_ne_top a)
    simpa [pmfReal, Finset.mem_univ] using h
  rw [h1] at h2
  simpa using h2.symm

theorem pmfReal_support_nonempty {α : Type*} [Fintype α] (q : PMF α) :
        (Finset.univ.filter fun a => pmfReal q a ≠ 0).Nonempty := by
      have hex : ∃ a, pmfReal q a ≠ 0 := by
        by_contra h
        have hall : ∀ a, pmfReal q a = 0 :=
          fun a => not_ne_iff.mp (fun ha => h ⟨a, ha⟩)
        have hsum : ∑ a, pmfReal q a = 0 :=
          Finset.sum_eq_zero fun a _ => hall a
        rw [pmfReal_sum q] at hsum
        exact one_ne_zero hsum
      obtain ⟨a, ha⟩ := hex
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩

/-- Separation distance between two PMFs (arXiv:0905.4698, §1, eq. 4): the maximum over
configurations of one minus the likelihood ratio. -/

noncomputable def separationDistance  {α : Type*} [Fintype α] (p q : PMF α) : ℝ :=
      Finset.max'
        ((Finset.univ.filter fun a => pmfReal q a ≠ 0).image
          fun a => 1 - pmfReal p a / pmfReal q a)
        (by
          obtain ⟨a, ha⟩ := pmfReal_support_nonempty q
          exact ⟨_, Finset.mem_image_of_mem _ ha⟩)

end MetaMathlibExt

end
