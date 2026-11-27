/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Monoidal.GroupCompletion
public import MathlibExt.KTheory.Exact.K0.Split
public import MathlibExt.KTheory.Ring.K0.Projective

/-!
# Components of the projective S⁻¹S construction

For finitely generated projective modules, the connected components of the
additive `S⁻¹S` category are canonically equivalent to the existing
split-exact `RingK0`.

This is the degree-zero component comparison.  It does not assert the
space-level group-completion theorem or the Quillen `Q` comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory Algebra

universe u

namespace AlgebraicKTheory
namespace RingK0

variable (R : Type u) [Ring R]

/-- Connected components of projective `S⁻¹S` are `RingK0 R`. -/
noncomputable def sInverseSComponentsEquiv :
    ConnectedComponents
        (SInverseS.Pair (FGProjectiveCat.{u} R)) ≃
      RingK0 R :=
  (SInverseS.connectedComponentsEquivGrothendieck
      (C := FGProjectiveCat.{u} R)).trans
    (K0.splitIso (FGProjectiveCat.{u} R)).addCommGroupIsoToAddEquiv.toEquiv

@[simp]
theorem sInverseSComponentsEquiv_mk
    (X : SInverseS.Pair (FGProjectiveCat.{u} R)) :
    sInverseSComponentsEquiv R (ConnectedComponents.mk X) =
      (K0.splitIso (FGProjectiveCat.{u} R)).hom
        (X.difference) :=
  rfl

end RingK0
end AlgebraicKTheory
