/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.ElementaryCompacts
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Algebra.Star.StarProjection

/-!
# Actual compact operators on countable scalar Hilbert space

The algebra is the actual compact-operator closed star ideal on lp(ℕ,ℂ,2).
A one-dimensional projection retains an actual compact operator, its star
projection laws, and the dimension of its literal operator range. Rank-one
operators and the standard coordinate projections are computed on this same
infinite Hilbert carrier.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ScalarHilbertCompacts

/-- The genuine countable scalar Hilbert space used for the compact algebra. -/
abbrev Hilbert := lp (fun _ : ℕ => ℂ) 2

/-- The actual compact-operator closed star ideal on countable scalar Hilbert space. -/
abbrev Algebra := (compactEndomorphismClosedStarIdeal (H := Hilbert)).carrier

/-- The C-star dictionary is the existing closed-ideal dictionary on that carrier. -/
noncomputable instance instNonUnitalCStarAlgebra : NonUnitalCStarAlgebra Algebra :=
  (compactEndomorphismClosedStarIdeal (H := Hilbert)).carrierCStarAlgebra

/-- A literal one-dimensional compact star projection on the original Hilbert space. -/
structure OneDimensionalProjection where
  /-- The actual compact operator, without a supplied representation or comparison. -/
  value : Algebra
  /-- The original operator is self-adjoint and idempotent. -/
  projection : IsStarProjection value
  /-- Its literal operator range has complex dimension one. -/
  finrank_range : Module.finrank ℂ
    (LinearMap.range (value : Hilbert →L[ℂ] Hilbert).toLinearMap) = 1

/-- The existing full-H compact rank-one constructor, specialized to scalar Hilbert space. -/
def rankOne (v w : Hilbert) : Algebra :=
  CStarModule.HilbertAmplification.hilbertCompactRankOne Hilbert v w

/-- The computed compact rank-one operator has its original Hilbert-space action. -/
@[simp]
theorem rankOne_apply (v w x : Hilbert) :
    (rankOne v w : Hilbert →L[ℂ] Hilbert) x = inner ℂ w x • v :=
  CStarModule.HilbertAmplification.hilbertCompactRankOne_apply Hilbert v w x

/-- Adjoint exchanges the two actual rank-one vectors. -/
@[simp]
theorem star_rankOne (v w : Hilbert) : star (rankOne v w) = rankOne w v :=
  CStarModule.HilbertAmplification.hilbertCompactRankOne_star Hilbert v w

/-- A unit-vector rank-one operator is an actual idempotent in the compact ideal. -/
theorem rankOne_mul_self {v : Hilbert} (hv : ‖v‖ = 1) :
    rankOne v v * rankOne v v = rankOne v v := by
  apply Subtype.ext
  exact InnerProductSpace.isIdempotentElem_rankOne_self (𝕜 := ℂ) hv

/-- The compact subtype retains the original rank-one operator norm. -/
@[simp]
theorem norm_rankOne (v w : Hilbert) :
    ‖(rankOne v w : Hilbert →L[ℂ] Hilbert)‖ = ‖v‖ * ‖w‖ :=
  InnerProductSpace.norm_rankOne v w

/-- A unit vector gives a computed actual projection with genuine one-dimensional range. -/
def rankOneProjection (v : Hilbert) (hv : ‖v‖ = 1) : OneDimensionalProjection where
  value := rankOne v v
  projection := ⟨rankOne_mul_self hv, star_rankOne v v⟩
  finrank_range := by
    have hv0 : v ≠ 0 := by
      intro h
      have h01 : (0 : ℝ) = 1 := by simpa only [h, norm_zero] using hv
      exact zero_ne_one h01
    change Module.finrank ℂ
      (LinearMap.range (InnerProductSpace.rankOne ℂ v v).toLinearMap) = 1
    apply Module.rank_eq_one_iff_finrank_eq_one.mp
    exact InnerProductSpace.rank_rankOne (𝕜 := ℂ) hv0 hv0

/-- The constructed projection is exactly the original rank-one compact operator. -/
@[simp]
theorem rankOneProjection_value (v : Hilbert) (hv : ‖v‖ = 1) :
    (rankOneProjection v hv).value = rankOne v v := rfl

/-- A standard Hilbert vector has its actual single-coordinate lp value. -/
def basisVector (i : ℕ) : Hilbert :=
  lp.single (E := fun _ : ℕ => ℂ) 2 i (1 : ℂ)

/-- Every standard coordinate vector has norm one in the genuine lp-two norm. -/
@[simp]
theorem norm_basisVector (i : ℕ) : ‖basisVector i‖ = 1 := by
  simpa only [basisVector, norm_one] using
    lp.norm_single (E := fun _ : ℕ => ℂ) (p := (2 : ENNReal)) (by norm_num) i (1 : ℂ)

/-- The original standard compact coordinate projection is a computed rank-one projection. -/
def coordinateProjection (i : ℕ) : OneDimensionalProjection :=
  rankOneProjection (basisVector i) (norm_basisVector i)

/-- The standard compact projection acts by the actual rank-one formula on every Hilbert vector. -/
theorem coordinateProjection_apply (i : ℕ) (x : Hilbert) :
    ((coordinateProjection i).value : Hilbert →L[ℂ] Hilbert) x =
      inner ℂ (basisVector i) x • basisVector i := rfl

end ScalarHilbertCompacts
