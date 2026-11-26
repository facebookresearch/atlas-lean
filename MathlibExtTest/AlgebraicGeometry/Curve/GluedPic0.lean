/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.GluedPic0
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.ComputeDegree
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaces

@[expose] public section

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (S : Finset (RationalPlace K F × RationalPlace K F))

-- `exactSource` consumers, with the nodes at `K`-rational places.
example : ↥(GluingData.admissible S) →+ GluedPic0 K F S :=
  GluedPic0.mk S

example : Function.Surjective (GluedPic0.mk S) :=
  GluedPic0.mk_surjective S

example (x : ↥(GluingData.admissible S)) :
    GluedPic0.mk S x = 0 ↔ GluingData.IsGluedPrincipal S (x : GluingData K F S) :=
  GluedPic0.mk_eq_zero_iff S x

example (x : ↥(GluingData.admissible S)) :
    GluedPic0.toPic0Pair S (GluedPic0.mk S x) =
      (Pic0.mk ⟨(x : GluingData K F S).1, GluingData.finiteDegZero_le_degZero x.2.1⟩,
        Pic0.mk ⟨(x : GluingData K F S).2.1, GluingData.finiteDegZero_le_degZero x.2.2.1⟩) :=
  GluedPic0.toPic0Pair_mk S x

example (w : ↥S → Additive Kˣ) :
    GluedPic0.toPic0Pair S (GluedPic0.nodeUnit S w) = 0 :=
  GluedPic0.toPic0Pair_nodeUnit S w

-- Boundary: constant node units are glued principal, hence vanish.
example (c : Kˣ) : GluedPic0.nodeUnit S (fun _ => Additive.ofMul c) = 0 :=
  GluedPic0.nodeUnit_const S c

-- Boundary: at a `K`-rational place a function of order zero has a value in `Kˣ`, so the node
-- units record every gluing relation, and the classes over the zero pair of Picard classes are
-- exactly the node units.
example (v : RationalPlace K F) {g : F} (hg : g ≠ 0) (h : (v : Place K F).ord g = 0) :
    ∃ a : Kˣ, (v : Place K F).HasValueAt g a :=
  v.exists_hasValueAt_of_ord_eq_zero hg h

example : (GluedPic0.toPic0Pair S).ker = (GluedPic0.nodeUnit S).range :=
  GluedPic0.ker_toPic0Pair S

-- Boundary: at a place whose residue field has infinite dimension over `K`, `Place.deg` is `0`,
-- so a single coefficient there has degree zero, but it is not admissible.
example (v : Place K F) (hv : ¬ Module.Finite K v.ResidueField) (w : ↥S → Additive Kˣ) :
    Divisor.degree (Finsupp.single v 1 : Divisor K F) = 0 ∧
      ((Finsupp.single v 1, 0, w) : GluingData K F S) ∉ GluingData.admissible S := by
  have h0 : v.deg = 0 := Module.finrank_of_not_finite hv
  refine ⟨by simp [h0], fun h => hv ((GluingData.mem_finiteDegZero.mp h.1).2 v ?_)⟩
  simp

-- At a place whose residue field is finite over `K`, a single coefficient has nonzero degree.
example (v : Place K F) [Module.Finite K v.ResidueField] (w : ↥S → Additive Kˣ) :
    ((Finsupp.single v 1, 0, w) : GluingData K F S) ∉ GluingData.admissible S := by
  have h0 : 0 < v.deg := Module.finrank_pos
  intro h
  have h1 := (GluingData.mem_finiteDegZero.mp h.1).1
  rw [Divisor.degree_single] at h1
  omega

section RealFunctionField

open Polynomial

/-- **Points of `ℝ(X)` as rational places.** The places of `ℝ(X)` at points have residue degree
`1`, so they are `ℝ`-rational. -/
private def pointPlace (a : ℝ) : RationalPlace ℝ (RatFunc ℝ) :=
  ⟨RationalFunctionField.placeOfPoint ℝ a,
    (Place.isRational_iff_deg_eq_one _).mpr (RationalFunctionField.deg_placeOfPoint ℝ a)⟩

-- A single node, made of the rational places of `ℝ(X)` at `0` and at `1`.
example (c : ℝˣ) :
    GluedPic0.nodeUnit {(pointPlace 0, pointPlace 1)} (fun _ => Additive.ofMul c) = 0 :=
  GluedPic0.nodeUnit_const _ c

example : (GluedPic0.toPic0Pair {(pointPlace 0, pointPlace 1)}).ker =
    (GluedPic0.nodeUnit {(pointPlace 0, pointPlace 1)}).range :=
  GluedPic0.ker_toPic0Pair _

private theorem natDegree_X_sq_add_one : (X ^ 2 + 1 : ℝ[X]).natDegree = 2 := by
  compute_degree!

private theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : ℝ[X]) := by
  refine irreducible_of_degree_le_three_of_not_isRoot
    (by rw [natDegree_X_sq_add_one]; decide) fun x hx => ?_
  rw [IsRoot, eval_add, eval_pow, eval_X, eval_one] at hx
  nlinarith [sq_nonneg x]

-- Boundary: the place of `ℝ(X)` at `X ^ 2 + 1` has residue degree `2`, so it is not rational:
-- it is not a `RationalPlace` and cannot be a node.
example : ¬ (RationalFunctionField.finitePlace ℝ irreducible_X_sq_add_one).IsRational := by
  rw [Place.isRational_iff_deg_eq_one, RationalFunctionField.deg_finitePlace,
    natDegree_X_sq_add_one]
  decide

end RealFunctionField

end AlgebraicCurve
