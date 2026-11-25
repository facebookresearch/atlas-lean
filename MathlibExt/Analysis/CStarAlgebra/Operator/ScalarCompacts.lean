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
# Compact operators on the scalar sequence Hilbert space

Let `H = lp(ℕ,ℂ,2)`. Its compact algebra is the closed ideal `K(H)` in bounded operators with
the inherited operator norm. Rank-one operators act by `θ_(v,w) x = ⟪w,x⟫_ℂ • v`, satisfy
`θ_(v,w)* = θ_(w,v)` and have norm `‖v‖ * ‖w‖`.

A unit vector `v` gives the self-adjoint rank-one projection `θ_(v,v)` with one-dimensional
range. Coordinate vectors `e_i` are the lp singles with entry `1` at `i`, have norm one, and
give coordinate projections onto their one-dimensional spans.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ScalarHilbertCompacts

/-- **Scalar sequence Hilbert space.** `Hilbert = lp (fun _ : ℕ => ℂ) 2`, the complex
square-summable sequence space. -/
abbrev Hilbert := lp (fun _ : ℕ => ℂ) 2

/-- **Compact algebra on scalar sequence space.** `Algebra` is `K(Hilbert)`, the closed star ideal
of compact operators on `lp(ℕ,ℂ,2)`, with the operator norm. -/
abbrev Algebra := (compactEndomorphismClosedStarIdeal (H := Hilbert)).carrier

/-- **C-star structure of scalar compacts.** The closed compact ideal of `lp(ℕ,ℂ,2)` is a
nonunital C-star algebra with its inherited bounded-operator norm. -/
noncomputable instance instNonUnitalCStarAlgebra : NonUnitalCStarAlgebra Algebra :=
  (compactEndomorphismClosedStarIdeal (H := Hilbert)).carrierCStarAlgebra

/-- **One-dimensional compact star projection.** This record contains a compact operator `p` on
`lp(ℕ,ℂ,2)` satisfying `p²=p`, `p*=p`, and `finrank ℂ (range p)=1`. -/
structure OneDimensionalProjection where
  /-- **Compact value of the projection.** The bounded operator `p` belongs to the compact ideal
  `K(lp(ℕ,ℂ,2))`. -/
  value : Algebra
  /-- **Star projection equations.** The compact value satisfies `p*p=p` and `star p=p`. -/
  projection : IsStarProjection value
  /-- **One-dimensional operator range.** The complex dimension of the linear range of the compact
  projection is one. -/
  finrank_range : Module.finrank ℂ
    (LinearMap.range (value : Hilbert →L[ℂ] Hilbert).toLinearMap) = 1

/-- **Scalar compact rank-one operator.** For `v,w : Hilbert = lp(ℕ,ℂ,2)`, `rankOne v w` is the
compact map `x ↦ inner ℂ w x • v`. -/
def rankOne (v w : Hilbert) : Algebra :=
  CStarModule.HilbertAmplification.hilbertCompactRankOne Hilbert v w

/-- **Action of the scalar rank-one operator.** `(rankOne v w) x = inner ℂ w x • v` on
`lp(ℕ,ℂ,2)`. -/
@[simp]
theorem rankOne_apply (v w x : Hilbert) :
    (rankOne v w : Hilbert →L[ℂ] Hilbert) x = inner ℂ w x • v :=
  CStarModule.HilbertAmplification.hilbertCompactRankOne_apply Hilbert v w x

/-- **Adjoint of the scalar rank-one operator.** `star (rankOne v w) = rankOne w v`. -/
@[simp]
theorem star_rankOne (v w : Hilbert) : star (rankOne v w) = rankOne w v :=
  CStarModule.HilbertAmplification.hilbertCompactRankOne_star Hilbert v w

/-- **Projection from a unit vector.** If `v : lp(ℕ,ℂ,2)` has `‖v‖=1`, then `rankOne v v * rankOne
v v = rankOne v v`. -/
theorem rankOne_mul_self {v : Hilbert} (hv : ‖v‖ = 1) :
    rankOne v v * rankOne v v = rankOne v v := by
  apply Subtype.ext
  exact InnerProductSpace.isIdempotentElem_rankOne_self (𝕜 := ℂ) hv

/-- **Norm of a scalar rank-one operator.** For `v,w : lp(ℕ,ℂ,2)`, the operator norm of `rankOne v
w` is `‖v‖ * ‖w‖`. -/
@[simp]
theorem norm_rankOne (v w : Hilbert) :
    ‖(rankOne v w : Hilbert →L[ℂ] Hilbert)‖ = ‖v‖ * ‖w‖ :=
  InnerProductSpace.norm_rankOne v w

/-- **One-dimensional projection of a unit vector.** For `v : lp(ℕ,ℂ,2)` with `‖v‖=1`, the
projection record has value `rankOne v v`, with range the complex span of `v`. -/
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

/-- **Value of the unit-vector projection.** `(rankOneProjection v hv).value = rankOne v v` when
`hv : ‖v‖=1`. -/
@[simp]
theorem rankOneProjection_value (v : Hilbert) (hv : ‖v‖ = 1) :
    (rankOneProjection v hv).value = rankOne v v := rfl

/-- **Coordinate vector of scalar sequence space.** `basisVector i` is `lp.single 2 i (1 : ℂ)`,
with entry `1` at coordinate `i` and zero elsewhere. -/
def basisVector (i : ℕ) : Hilbert :=
  lp.single (E := fun _ : ℕ => ℂ) 2 i (1 : ℂ)

/-- **Norm of a scalar coordinate vector.** `‖basisVector i‖ = 1` for every `i : ℕ`. -/
@[simp]
theorem norm_basisVector (i : ℕ) : ‖basisVector i‖ = 1 := by
  simpa only [basisVector, norm_one] using
    lp.norm_single (E := fun _ : ℕ => ℂ) (p := (2 : ENNReal)) (by norm_num) i (1 : ℂ)

/-- **Compact coordinate projection.** `coordinateProjection i` is the one-dimensional star
projection `rankOne (basisVector i) (basisVector i)`. -/
def coordinateProjection (i : ℕ) : OneDimensionalProjection :=
  rankOneProjection (basisVector i) (norm_basisVector i)

/-- **Action of a scalar coordinate projection.** For `x : lp(ℕ,ℂ,2)`, the projection value is
`inner ℂ (basisVector i) x • basisVector i`. -/
theorem coordinateProjection_apply (i : ℕ) (x : Hilbert) :
    ((coordinateProjection i).value : Hilbert →L[ℂ] Hilbert) x =
      inner ℂ (basisVector i) x • basisVector i := rfl

end ScalarHilbertCompacts
