/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.Russo
public import MathlibExt.Probability.CorrelationInequalities.BK
public import MathlibExt.Probability.Configuration.CylinderDeriv
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.AizenmanBarsky
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABInequalities
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABPivotalFirstExit

/-!
# BK bounds on pivotal probabilities for connection events

The pivotal probability of an edge for a connection event is at most the sum of the two first-exit
products, and Russo's formula bounds the derivative of connection probabilities.

## i. Overview

Pivotality of `xy` for `u ↔ B` inside `A` implies one of two disjoint occurrences (`u ↔ x` with `y ↔
B`, or `u ↔ y` with `x ↔ B`), so by BK `P(xy pivotal) ≤ P(u ↔ x) P(y ↔ B) + P(u ↔ y) P(x ↔ B)`. With
Russo's formula this bounds `∂_p P(u ↔ B)`. The remaining results assemble the critical bound
`M(β_c, h) ≥ c √h` from the Russo–BK and mean-field inputs.

## ii. Key results

- `pivotalProb_le_union` : BK for a union of two disjoint occurrences
- `pivotalProb_connEvent_le` : the pivotal bound for connection events
- `deriv_prob_connEvent_le_sum` : Russo bound on the derivative
- `ab_perco_meanfield_sqrt_of_core` : the critical bound from Russo–BK inputs

## iii. Table of contents

- A. Pivotal probabilities
- B. The critical bound

## iv. References

- M. Aizenman, D. J. Barsky, "Sharpness of the phase transition in percolation models", Comm. Math.
  Phys. 108 (1987) 489–526
- J. van den Berg, H. Kesten, "Inequalities with applications to percolation and reliability", J.
  Appl. Probab. 22 (1985) 556–569

-/

@[expose] public section

open MeasureTheory Set Finset
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace StatMech SimpleGraph

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## A. Pivotal probabilities -/

lemma pivotalProb_le_union {p : ℝ≥0} (hp : p ≤ 1)
    {A B₁ C₁ B₂ C₂ : Set (ConfigSpace E)} {e : E}
    (hB₁ : IsIncreasing B₁) (hC₁ : IsIncreasing C₁)
    (hB₂ : IsIncreasing B₂) (hC₂ : IsIncreasing C₂)
    (hpiv : {ω | IsPivotal e A ω} ⊆ disjointOccurrence B₁ C₁ ∪ disjointOccurrence B₂ C₂) :
    pivotalProb (p : ℝ) A e ≤ prob (p : ℝ) B₁ * prob (p : ℝ) C₁
                            + prob (p : ℝ) B₂ * prob (p : ℝ) C₂ := by
  have hpivprob : pivotalProb (p : ℝ) A e = prob (p : ℝ) {ω | IsPivotal e A ω} := rfl
  rw [hpivprob]
  set μ := bernoulliProductMeasure (E := E) p hp with hμ
  rw [(finiteRealProb_eq_prob p hp {ω | IsPivotal e A ω}).symm,
      (finiteRealProb_eq_prob p hp B₁).symm, (finiteRealProb_eq_prob p hp C₁).symm,
      (finiteRealProb_eq_prob p hp B₂).symm, (finiteRealProb_eq_prob p hp C₂).symm]
  calc μ.real {ω | IsPivotal e A ω}
      ≤ μ.real (disjointOccurrence B₁ C₁ ∪ disjointOccurrence B₂ C₂) :=
        measureReal_mono hpiv (measure_ne_top _ _)
    _ ≤ μ.real (disjointOccurrence B₁ C₁) + μ.real (disjointOccurrence B₂ C₂) :=
        measureReal_union_le _ _
    _ ≤ μ.real B₁ * μ.real C₁ + μ.real B₂ * μ.real C₂ := by
        linarith [bk_inequality hp hB₁ hC₁, bk_inequality hp hB₂ hC₂]

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pivotalProb_connEvent_le {p : ℝ≥0} (hp : p ≤ 1)
    (G : SimpleGraph V) (A : Set V) (u : V) (B : Set V)
    (x y : V) (hu : u ∈ A) (hx : x ∈ A) (hy : y ∈ A) :
    pivotalProb (p : ℝ) (connEvent G A u B) s(x, y) ≤
      prob (p : ℝ) (connEvent G A u {x}) * prob (p : ℝ) (connEvent G A y B)
      + prob (p : ℝ) (connEvent G A u {y}) * prob (p : ℝ) (connEvent G A x B) :=
  pivotalProb_le_union hp
    (isIncreasing_connEvent G A u {x}) (isIncreasing_connEvent G A y B)
    (isIncreasing_connEvent G A u {y}) (isIncreasing_connEvent G A x B)
    (sab_pivotal_subset_firstExit G A u B x y hu hx hy)

lemma deriv_prob_connEvent_le_sum {p : ℝ≥0} (_hp : p ≤ 1)
    (G : SimpleGraph V) (A : Set V) (u : V) (B : Set V) (bnd : Sym2 V → ℝ)
    (hbnd : ∀ e, pivotalProb (p : ℝ) (connEvent G A u B) e ≤ bnd e) :
    deriv (fun q => prob q (connEvent G A u B)) (p : ℝ) ≤ ∑ e, bnd e := by
  rw [deriv_prob_eq_sum_pivotalProb _ (isIncreasing_connEvent G A u B)]
  exact Finset.sum_le_sum (fun e _ => hbnd e)

/-! ## B. The critical bound -/

lemma ab_perco_meanfield_sqrt_of_core (M : ℝ → ℝ → ℝ) (J βc : ℝ)
    (hβc : 0 < βc) (hJ : 0 < J)
    (hhu : ∀ β h, ∃ (ι : Type) (s : Finset ι) (Jcoef infl piv : ι → ℝ),
      (0 ≤ M β h) ∧ (∀ e ∈ s, 0 ≤ Jcoef e) ∧ (∀ e ∈ s, 0 ≤ infl e) ∧
      (deriv (fun β => M β h) β = ∑ e ∈ s, piv e) ∧
      (∀ e ∈ s, piv e ≤ Jcoef e * M β h * infl e) ∧
      (∑ e ∈ s, Jcoef e = J) ∧
      (∑ e ∈ s, infl e = deriv (fun h => M β h) h) ∧
      (∀ e ∈ s, Jcoef e ≤ J) ∧ (0 ≤ deriv (fun h => M β h) h))
    (hdiff : ∀ h ∈ Ici (0 : ℝ), DifferentiableAt ℝ (fun h => M βc h) h)
    (hmono : ∀ h ∈ Ici (0 : ℝ), 0 ≤ deriv (fun h => M βc h) h)
    (hmnn : ∀ h, 0 ≤ M βc h)
    (hm0 : M βc 0 = 0)
    (h6 : ∀ h ∈ Ici (0 : ℝ), ∃ pivsum : ℝ,
      (deriv (fun β => M β h) βc = pivsum) ∧
      ((1 / βc) * (1 - M βc h) ≤ pivsum)) :
    ∃ c > 0, ∀ h ∈ Ioc (0 : ℝ) (βc * J / 4),
      c * Real.sqrt h ≤ M βc h := by
  have hAB : AizenmanBarskyInequality M J :=
    aizenmanBarskyInequality_of_russo_bk M J (le_of_lt hJ) hhu
  have heq6 : ∀ h ∈ Ici (0 : ℝ), 1 - M βc h ≤ βc * deriv (fun β => M β h) βc :=
    eq6_of_russo_meanfield M βc hβc h6
  exact ab_perco_meanfield_sqrt M J βc hβc hJ hAB hdiff hmono hmnn hm0 heq6

lemma ab_perco_meanfield_sqrt_of_core_physical
    (M : ℝ → ℝ → ℝ) (J βc : ℝ)
    (hβc : 0 < βc) (hJ : 0 < J)
    (hhu : ∀ β h, ∃ (ι : Type) (s : Finset ι) (Jcoef infl piv : ι → ℝ),
      (0 ≤ M β h) ∧ (∀ e ∈ s, 0 ≤ Jcoef e) ∧ (∀ e ∈ s, 0 ≤ infl e) ∧
      (deriv (fun β => M β h) β = ∑ e ∈ s, piv e) ∧
      (∀ e ∈ s, piv e ≤ Jcoef e * M β h * infl e) ∧
      (∑ e ∈ s, Jcoef e = J) ∧
      (∑ e ∈ s, infl e = deriv (fun h => M β h) h) ∧
      (∀ e ∈ s, Jcoef e ≤ J) ∧ (0 ≤ deriv (fun h => M β h) h))
    (hdiff : ∀ h ∈ Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun t => M βc t) h)
    (hmono : ∀ h ∈ Ioi (0 : ℝ),
      0 ≤ deriv (fun t => M βc t) h)
    (hcont0 : ContinuousWithinAt (fun t => M βc t) (Ici (0 : ℝ)) 0)
    (hmnn : ∀ h, 0 ≤ M βc h) (hm0 : M βc 0 = 0)
    (h6 : ∀ h ∈ Ioi (0 : ℝ), ∃ pivsum : ℝ,
      (deriv (fun β => M β h) βc = pivsum) ∧
      ((1 / βc) * (1 - M βc h) ≤ pivsum)) :
    ∃ c > 0, ∀ h ∈ Ioc (0 : ℝ) (βc * J / 4),
      c * Real.sqrt h ≤ M βc h := by
  have hAB : AizenmanBarskyInequality M J :=
    aizenmanBarskyInequality_of_russo_bk M J hJ.le hhu
  have hABphysical : AizenmanBarskyInequalityPhysical M J := by
    intro β hβ h hh
    exact hAB β h
  have heq6 : ∀ h ∈ Ioi (0 : ℝ),
      1 - M βc h ≤ βc * deriv (fun β => M β h) βc := by
    intro h hh
    obtain ⟨pivsum, hpiv, hlb⟩ := h6 h hh
    calc
      1 - M βc h = βc * ((1 / βc) * (1 - M βc h)) := by
        field_simp [hβc.ne']
      _ ≤ βc * pivsum := mul_le_mul_of_nonneg_left hlb hβc.le
      _ = βc * deriv (fun β => M β h) βc := by rw [hpiv]
  exact ab_perco_meanfield_sqrt_physical M J βc hβc hJ hABphysical
    hdiff hmono hcont0 hmnn hm0 heq6

end Sharpness

end StatMech
