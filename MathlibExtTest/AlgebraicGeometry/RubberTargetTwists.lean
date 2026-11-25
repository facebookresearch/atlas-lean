/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.RubberMapFamilies
import Mathlib.Algebra.Polynomial.Laurent

/-!
Over the base `ℙ¹` with coordinate `t`, the projective completion of `𝒪(1)`, with its zero and
infinity sections, is glued from two framed charts. On the overlap `t ≠ 0, ∞` the gluing is the
scaling `y ↦ t y` of the fibre coordinate. The scaling preserves both end ideals, `(y)` and, in
the coordinate `z = 1/y`, `(z)`, so it is a rubber isomorphism, but it moves the frame. The
zero section has normal bundle `𝒪(±1)`, so this target has no global frame. A rubber target is
framed only over the members of a covering, as `RubberTarget.ofCover` shows, so it includes
this twisted target.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry
open RelativeProjectiveLineModels ExpandedTargetChainGeometry StandardRelativeExpansionModels
open ExpandedRelativeFamilies RubberMapFamilies CoherentCurveLinearSeries
open Polynomial
open LaurentPolynomial (T isUnit_T)

noncomputable section

/-- The ring of the overlap. -/
private abbrev A := LaurentPolynomial ℚ

/-- The gluing `y ↦ t y`, and `z ↦ t⁻¹ z` in the coordinate at infinity. -/
private def twist (n : ℤ) : A[X] →ₐ[A] A[X] := aeval (Polynomial.C (T n) * X)

private theorem twist_end (n : ℤ) :
    Ideal.map (twist n) (Ideal.span {(X : A[X])}) = Ideal.span {X} := by
  rw [Ideal.map_span, Set.image_singleton]
  simp only [twist, aeval_X]
  exact Ideal.span_singleton_mul_left_unit ((isUnit_T n).map Polynomial.C) X

/-- The gluing preserves the zero end. -/
example : Ideal.map (twist 1) (Ideal.span {(X : A[X])}) = Ideal.span {X} := twist_end 1

/-- In the coordinate at infinity it preserves the end at infinity. -/
example : Ideal.map (twist (-1)) (Ideal.span {(X : A[X])}) = Ideal.span {X} := twist_end (-1)

variable {k : Type} [Field k]
  (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
  (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
  (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)

/-- A family framed over two members of an open covering is a rubber target, without a global
frame. -/
example {T X : Over (Spec (.of k))} (p : X ⟶ T) (zero : X.left.IdealSheafData)
    (boundary : prod P.divisor T ⟶ X) [IsClosedImmersion boundary.left]
    (cartier : CartierIdealModels.IsEffectiveCartier boundary.left.ker)
    (hp : boundary ≫ p = prod.snd) (U : Bool → Over (Spec (.of k))) (q : ∀ i, U i ⟶ T)
    [∀ i, IsOpenImmersion (q i).left] (cover : ∀ t : T.left, ∃ i, t ∈ Set.range (q i).left)
    (F : ∀ i, ExpandedFamily P R S (U i)) (e : ∀ i, pullback p (q i) ≅ (F i).scheme)
    (he : ∀ i, (e i).hom ≫ (F i).projection = pullback.snd p (q i))
    (hz : ∀ i, (zeroIdeal O P D R S (F i)).comap (e i).hom.left =
      zero.comap (pullback.fst p (q i)).left)
    (hb : ∀ i, (F i).boundary.left.ker.comap (e i).hom.left =
      boundary.left.ker.comap (pullback.fst p (q i)).left) :
    (RubberTarget.ofCover O P D R S p zero boundary cartier hp U q cover F e he hz hb).zero =
      zero := rfl

/-- A framed expanded target is a rubber target with the zero ideal of its contraction. -/
example {T : Over (Spec (.of k))} (F : ExpandedFamily P R S T) :
    (RubberTarget.ofFramed O P D R S F).zero = zeroIdeal O P D R S F ∧
      (RubberTarget.ofFramed O P D R S F).boundary = F.boundary := ⟨rfl, rfl⟩
