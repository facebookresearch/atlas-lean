/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DltBoundaryFlipModels

@[expose] public noncomputable section
namespace MathlibExtTest.AlgebraicGeometry.DltBoundaryFlipModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.DltBoundaryFlipModels

/-- An actual prime divisor on the identity of a threefold is not exceptional.
Its height two must not be confused with its codimension one. -/
example {k : Type} [Field k] (V : NormalVariety k 3) (p : PrimePoint V)
    (hheight : Order.height p.val = 2) :
    ¬IsExceptional (𝟙 V.X) p ∧
      Order.height ((𝟙 V.X : V.X ⟶ V.X).left p.val) ≠ 1 := by
  constructor
  · change ¬Order.coheight p.val ≠ 1
    exact not_not_intro p.property
  · change Order.height p.val ≠ 1
    rw [hheight]
    decide

/-- A divisor mapping to codimension two is exceptional even if its image has height one. -/
example {k : Type} [Field k] (V W : NormalVariety k 3) (f : V.X ⟶ W.X)
    (p : PrimePoint V) (hcodim : Order.coheight (f.left p.val) = 2)
    (hheight : Order.height (f.left p.val) = 1) :
    IsExceptional f p ∧ Order.height (f.left p.val) = 1 := by
  constructor
  · change Order.coheight (f.left p.val) ≠ 1
    rw [hcodim]
    decide
  · exact hheight

/-- Plt records the model calculus, so no proper birational model is omitted from
its discrepancy quantifier. -/
example {k : Type} [Field k] {n : ℕ} (P : LogPair k n) (h : IsPlt P) :
    HasModelCalculus P :=
  h.2.1

end MathlibExtTest.AlgebraicGeometry.DltBoundaryFlipModels
