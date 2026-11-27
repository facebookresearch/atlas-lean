/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Rail-limited feedback amplifier

## i. Overview

A memoryless finite-gain negative-feedback amplifier whose output is
limited to a closed rail interval `[vmin, vmax]`: the output `vo`
satisfies `vo = railClamp vmin vmax (A * (vi - beta * vo))` with
gain `A > 0` and feedback factor `beta > 0`. This is a fixed-point
problem, not a dynamic stability claim: the clamp makes the
right-hand side piecewise (lower rail, linear region, upper rail),
and existence and uniqueness come from the clamp geometry. When the
unclamped linear candidate `A * vi / (1 + A * beta)` lands inside
the rails, it is the fixed point; below the lower rail the fixed
point is `vmin`, and above the upper rail it is `vmax`.

## ii. Key results

- `railClamp_mem_Icc`: the clamp always lands in the closed rail
  interval, with closed endpoint conventions at both rails.
- `existsUnique_fixedPoint`: for `vmin < vmax` there is exactly one
  fixed point of the rail-limited map.
- `fixedPoint_eq_linearCandidate_iff`: a fixed point equals the
  linear candidate if and only if that candidate lies in the rails.
- `fixedPoint_eq_vmin_of_candidate_lt` and
  `fixedPoint_eq_vmax_of_vmax_lt_candidate`: in the two saturated
  regimes the fixed point is the corresponding rail.

## iii. Table of contents

- A. The rail clamp and the fixed point

## iv. References

- A. S. Sedra and K. C. Smith, *Microelectronic Circuits*, eighth
  edition, Oxford University Press, 2020: the finite-gain feedback
  amplifier equation `vo = A * (vi - beta * vo)` and its closed-form
  solution, here composed with an ideal output limiter.

## A. The rail clamp and the fixed point
-/

@[expose] public section

namespace PhyslibExt.Electronics.RailLimitedFeedback

/-- The memoryless rail clamp with the closed endpoint convention:
`max vmin (min vmax x)`. Values at or below `vmin` give `vmin`,
values in the closed interval `[vmin, vmax]` are unchanged
(endpoints included), values at or above `vmax` give `vmax`.
Local to this leaf by design; see the header for why this is not a
generic saturation definition. -/
noncomputable def railClamp (vmin vmax x : ℝ) : ℝ :=
  max vmin (min vmax x)

/-- The rail-limited feedback map at input `vi`:
`F(vo) = clamp(vmin, vmax, A * (vi - beta * vo))`. A fixed point
`vo = F(vo)` is the leaf's operating point; no dynamics are modeled. -/
noncomputable def railLimitedMap (A beta vmin vmax vi vo : ℝ) : ℝ :=
  railClamp vmin vmax (A * (vi - beta * vo))

/-- The linear (unclamped) candidate `A * vi / (1 + A * beta)`: under
`0 < A` and `0 < beta` it is the unique solution of the unclamped
equation `vo = A * (vi - beta * vo)` (see `linearCandidate_satisfies`
and `fixedPoint_unique`). As a bare definition it carries no such
claim for nonpositive gain or feedback. -/
noncomputable def linearCandidate (A beta vi : ℝ) : ℝ :=
  A * vi / (1 + A * beta)

/-- The loop denominator `1 + A * beta` is strictly positive for
finite positive gain and feedback. -/
lemma one_add_mul_pos (A beta : ℝ) (hA : 0 < A) (hbeta : 0 < beta) :
    0 < 1 + A * beta := by
  have h : 0 < A * beta := mul_pos hA hbeta
  linarith

/-- The clamp always lands in the closed rail interval. -/
lemma railClamp_mem_Icc (vmin vmax x : ℝ) (h : vmin ≤ vmax) :
    railClamp vmin vmax x ∈ Set.Icc vmin vmax := by
  refine Set.mem_Icc.mpr ⟨le_max_left _ _, ?_⟩
  exact max_le h (min_le_left _ _)

/-- Clamp, lower branch with closed endpoint: at or below the lower
rail the value is exactly `vmin`; in particular `x = vmin` is a
fixed value of the clamp, which the exactly-on-rail case needs. -/
lemma railClamp_eq_vmin_of_le (vmin vmax x : ℝ) (h : x ≤ vmin) :
    railClamp vmin vmax x = vmin := by
  unfold railClamp
  apply max_eq_left
  exact le_trans (min_le_right _ _) h

/-- Clamp, linear branch with closed endpoints: a value already in
`[vmin, vmax]`, endpoints included, is returned unchanged. -/
lemma railClamp_eq_self_of_mem (vmin vmax x : ℝ)
    (h : x ∈ Set.Icc vmin vmax) : railClamp vmin vmax x = x := by
  rw [Set.mem_Icc] at h
  unfold railClamp
  rw [min_eq_right h.2, max_eq_right h.1]

/-- Clamp, upper branch with closed endpoint: for `vmin ≤ vmax`, at or
above the upper rail the value is exactly `vmax`. -/
lemma railClamp_eq_vmax_of_le (vmin vmax x : ℝ) (h : vmin ≤ vmax)
    (hx : vmax ≤ x) : railClamp vmin vmax x = vmax := by
  unfold railClamp
  rw [min_eq_left hx, max_eq_right h]

/-- Any fixed point of the rail-limited map lies in the closed rail
interval, because the clamp's range is that interval. -/
lemma fixedPoint_mem_Icc (A beta vmin vmax vi vo : ℝ)
    (hrail : vmin ≤ vmax)
    (hfix : vo = railLimitedMap A beta vmin vmax vi vo) :
    vo ∈ Set.Icc vmin vmax := by
  rw [hfix]
  unfold railLimitedMap
  exact railClamp_mem_Icc _ _ _ hrail

/-- The linear candidate indeed solves the unclamped equation; this
is the L1 closed form restated at the point L2 needs it. -/
lemma linearCandidate_satisfies (A beta vi : ℝ) (hA : 0 < A)
    (hbeta : 0 < beta) :
    linearCandidate A beta vi
      = A * (vi - beta * linearCandidate A beta vi) := by
  unfold linearCandidate
  have hD : (1 + A * beta) ≠ 0 := ne_of_gt (one_add_mul_pos A beta hA hbeta)
  field_simp
  ring

-- Feedback identity: the amplified error at `vo` equals the candidate
-- plus the loop gain times the distance back to the candidate.
private lemma feedback_key (A beta vi vo : ℝ) (hA : 0 < A)
    (hbeta : 0 < beta) :
    A * (vi - beta * vo) = linearCandidate A beta vi
      + A * beta * (linearCandidate A beta vi - vo) := by
  unfold linearCandidate
  have hD : (1 + A * beta) ≠ 0 := ne_of_gt (one_add_mul_pos A beta hA hbeta)
  field_simp
  ring

-- The clamp is monotone in its input.
private lemma railClamp_mono (vmin vmax x y : ℝ) (h : x ≤ y) :
    railClamp vmin vmax x ≤ railClamp vmin vmax y := by
  unfold railClamp
  exact max_le_max le_rfl (min_le_min le_rfl h)

/-- Existence: the rail-limited map has at least one fixed point in
the rails. The proof is an explicit three-regime case analysis on
the position of the linear candidate relative to the rails, not a
contraction argument. -/
lemma exists_fixedPoint (A beta vmin vmax vi : ℝ) (hA : 0 < A)
    (hbeta : 0 < beta) (hrail : vmin < vmax) :
    ∃ vo : ℝ, vo = railLimitedMap A beta vmin vmax vi vo := by
  have hk : 0 < A * beta := mul_pos hA hbeta
  by_cases hlow : linearCandidate A beta vi < vmin
  · refine ⟨vmin, ?_⟩
    have harg : A * (vi - beta * vmin) ≤ vmin := by
      rw [feedback_key A beta vi vmin hA hbeta]
      have hneg : A * beta * (linearCandidate A beta vi - vmin) < 0 :=
        mul_neg_of_pos_of_neg hk (by linarith)
      linarith
    unfold railLimitedMap
    exact (railClamp_eq_vmin_of_le vmin vmax _ harg).symm
  · by_cases hhigh : vmax < linearCandidate A beta vi
    · refine ⟨vmax, ?_⟩
      have harg : vmax ≤ A * (vi - beta * vmax) := by
        rw [feedback_key A beta vi vmax hA hbeta]
        have hpos : 0 < A * beta * (linearCandidate A beta vi - vmax) :=
          mul_pos hk (by linarith)
        linarith
      unfold railLimitedMap
      exact (railClamp_eq_vmax_of_le vmin vmax _ (le_of_lt hrail) harg).symm
    · refine ⟨linearCandidate A beta vi, ?_⟩
      have hmem : linearCandidate A beta vi ∈ Set.Icc vmin vmax :=
        Set.mem_Icc.mpr ⟨le_of_not_gt hlow, le_of_not_gt hhigh⟩
      have hc := linearCandidate_satisfies A beta vi hA hbeta
      unfold railLimitedMap
      rw [← hc]
      exact (railClamp_eq_self_of_mem vmin vmax _ hmem).symm

/-- Uniqueness: the rail-limited map has at most one fixed point,
because `vo ↦ F(vo) - vo` is strictly decreasing (the clamped
amplified error is nonincreasing in `vo` while `-vo` is strictly
decreasing). The sign of the feedback matters: this argument is not
claimed for a sign-flipped law. -/
lemma fixedPoint_unique (A beta vmin vmax vi : ℝ) (hA : 0 < A)
    (hbeta : 0 < beta) (hrail : vmin < vmax) (vo vo' : ℝ)
    (h : vo = railLimitedMap A beta vmin vmax vi vo)
    (h' : vo' = railLimitedMap A beta vmin vmax vi vo') :
    vo = vo' := by
  have _ := hrail
  by_contra hne
  have inner_strict : ∀ a b : ℝ, a < b →
      A * (vi - beta * b) < A * (vi - beta * a) := by
    intro a b hab
    have hbb : beta * a < beta * b := mul_lt_mul_of_pos_left hab hbeta
    have hsub : vi - beta * b < vi - beta * a := by linarith
    exact mul_lt_mul_of_pos_left hsub hA
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hu : A * (vi - beta * vo') ≤ A * (vi - beta * vo) :=
      le_of_lt (inner_strict vo vo' hlt)
    have hF : railLimitedMap A beta vmin vmax vi vo'
        ≤ railLimitedMap A beta vmin vmax vi vo :=
      railClamp_mono vmin vmax _ _ hu
    have hcon : railLimitedMap A beta vmin vmax vi vo' - vo'
        < railLimitedMap A beta vmin vmax vi vo - vo := by linarith
    rw [← h, ← h'] at hcon
    have hfalse : (0:ℝ) < 0 := by linarith
    exact lt_irrefl 0 hfalse
  · have hu : A * (vi - beta * vo) ≤ A * (vi - beta * vo') :=
      le_of_lt (inner_strict vo' vo hlt)
    have hF : railLimitedMap A beta vmin vmax vi vo
        ≤ railLimitedMap A beta vmin vmax vi vo' :=
      railClamp_mono vmin vmax _ _ hu
    have hcon : railLimitedMap A beta vmin vmax vi vo - vo
        < railLimitedMap A beta vmin vmax vi vo' - vo' := by linarith
    rw [← h, ← h'] at hcon
    have hfalse : (0:ℝ) < 0 := by linarith
    exact lt_irrefl 0 hfalse

/-- Headline existence-and-uniqueness: for `A, beta > 0` and
`vmin < vmax`, the map `vo = clamp(vmin, vmax, A * (vi - beta * vo))`
has exactly one fixed point. -/
lemma existsUnique_fixedPoint (A beta vmin vmax vi : ℝ) (hA : 0 < A)
    (hbeta : 0 < beta) (hrail : vmin < vmax) :
    ∃! vo : ℝ, vo = railLimitedMap A beta vmin vmax vi vo := by
  obtain ⟨vo, h⟩ := exists_fixedPoint A beta vmin vmax vi hA hbeta hrail
  exact ⟨vo, h, fun y hy => fixedPoint_unique A beta vmin vmax vi hA hbeta hrail y vo hy h⟩

/-- Linear-region characterization, forward direction: if the linear
candidate lies in the closed rail interval (endpoints included, the
exactly-on-rail case), then it is a fixed point, hence by uniqueness
it is the fixed point. -/
lemma eq_linearCandidate_of_mem (A beta vmin vmax vi vo : ℝ)
    (hA : 0 < A) (hbeta : 0 < beta) (hrail : vmin < vmax)
    (hfix : vo = railLimitedMap A beta vmin vmax vi vo)
    (hmem : linearCandidate A beta vi ∈ Set.Icc vmin vmax) :
    vo = linearCandidate A beta vi := by
  have hc := linearCandidate_satisfies A beta vi hA hbeta
  have hFc : linearCandidate A beta vi
      = railLimitedMap A beta vmin vmax vi (linearCandidate A beta vi) := by
    unfold railLimitedMap
    rw [← hc]
    exact (railClamp_eq_self_of_mem vmin vmax _ hmem).symm
  exact fixedPoint_unique A beta vmin vmax vi hA hbeta hrail vo _ hfix hFc

/-- Linear-region characterization, reverse direction: if a fixed
point equals the linear candidate, then that candidate lies in the
closed rail interval (every fixed point lies in the rails). -/
lemma linearCandidate_mem_of_eq (A beta vmin vmax vi vo : ℝ)
    (hrail : vmin ≤ vmax)
    (hfix : vo = railLimitedMap A beta vmin vmax vi vo)
    (heq : vo = linearCandidate A beta vi) :
    linearCandidate A beta vi ∈ Set.Icc vmin vmax := by
  rw [← heq]
  exact fixedPoint_mem_Icc A beta vmin vmax vi vo hrail hfix

/-- The leaf's "equals the linear candidate iff" clause, packaged for
an arbitrary fixed point `vo`: `vo` is the linear candidate exactly
when the candidate lies in the closed rail interval. -/
lemma fixedPoint_eq_linearCandidate_iff (A beta vmin vmax vi vo : ℝ)
    (hA : 0 < A) (hbeta : 0 < beta) (hrail : vmin < vmax)
    (hfix : vo = railLimitedMap A beta vmin vmax vi vo) :
    vo = linearCandidate A beta vi
      ↔ linearCandidate A beta vi ∈ Set.Icc vmin vmax := by
  constructor
  · intro heq
    exact linearCandidate_mem_of_eq A beta vmin vmax vi vo (le_of_lt hrail) hfix heq
  · intro hmem
    exact eq_linearCandidate_of_mem A beta vmin vmax vi vo hA hbeta hrail hfix hmem

/-- Lower saturation: if the linear candidate is strictly below the
lower rail, the unique fixed point sits exactly on the lower rail. -/
lemma fixedPoint_eq_vmin_of_candidate_lt (A beta vmin vmax vi vo : ℝ)
    (hA : 0 < A) (hbeta : 0 < beta) (hrail : vmin < vmax)
    (hfix : vo = railLimitedMap A beta vmin vmax vi vo)
    (hlt : linearCandidate A beta vi < vmin) : vo = vmin := by
  have hk : 0 < A * beta := mul_pos hA hbeta
  have harg : A * (vi - beta * vmin) ≤ vmin := by
    rw [feedback_key A beta vi vmin hA hbeta]
    have hneg : A * beta * (linearCandidate A beta vi - vmin) < 0 :=
      mul_neg_of_pos_of_neg hk (by linarith)
    linarith
  have hFv : vmin = railLimitedMap A beta vmin vmax vi vmin := by
    unfold railLimitedMap
    exact (railClamp_eq_vmin_of_le vmin vmax _ harg).symm
  exact fixedPoint_unique A beta vmin vmax vi hA hbeta hrail vo vmin hfix hFv

/-- Upper saturation: if the linear candidate is strictly above the
upper rail, the unique fixed point sits exactly on the upper rail. -/
lemma fixedPoint_eq_vmax_of_vmax_lt_candidate
    (A beta vmin vmax vi vo : ℝ) (hA : 0 < A) (hbeta : 0 < beta)
    (hrail : vmin < vmax)
    (hfix : vo = railLimitedMap A beta vmin vmax vi vo)
    (hlt : vmax < linearCandidate A beta vi) : vo = vmax := by
  have hk : 0 < A * beta := mul_pos hA hbeta
  have harg : vmax ≤ A * (vi - beta * vmax) := by
    rw [feedback_key A beta vi vmax hA hbeta]
    have hpos : 0 < A * beta * (linearCandidate A beta vi - vmax) :=
      mul_pos hk (by linarith)
    linarith
  have hFv : vmax = railLimitedMap A beta vmin vmax vi vmax := by
    unfold railLimitedMap
    exact (railClamp_eq_vmax_of_le vmin vmax _ (le_of_lt hrail) harg).symm
  exact fixedPoint_unique A beta vmin vmax vi hA hbeta hrail vo vmax hfix hFv

end PhyslibExt.Electronics.RailLimitedFeedback
