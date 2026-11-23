/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCore
public import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.FundamentalGroupHurewiczIso
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Integral H1 of the original native universal cover

The native nerve-unit pullback is connected and has trivial fundamental group.
Its integral degree-one Hurewicz isomorphism therefore makes its first homology
zero. The original pullback and identity-path point are used throughout.

This supplies the universal-cover H1 input in Weibel, *The K-book*, IV,
Lemma 1.3.1, printed page 262. The second group homology of an acyclic space's
fundamental group still requires its separate group-homology comparison.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace SSet.KanComplex

/-- The original native cover of the component of a chosen vertex has zero
integral first homology. No connectedness assumption on the original Kan
complex is needed. -/
theorem nativeCoverHomologyOne_isZero
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    IsZero ((nativeCover X x).homology
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 1) := by
  let U := nativeCover X x
  let y := nativeCoverIdentityPoint X x
  let _ : KanComplex U := nativeCover_kanComplex X x
  let _ : U.IsConnected := nativeCover_isConnected (X := X) (x := x)
  let _ : Subsingleton (π 1 U y) := nativeCover_piOne_subsingleton (X := X) (x := x)
  let e := piOneMulEquivFundamentalGroupoidEnd (X := U) y
  let _ : Subsingleton (End (SSet.FundamentalGroupoid.mk y)) :=
    e.symm.injective.subsingleton
  let _ : Unique (End (SSet.FundamentalGroupoid.mk y)) :=
    { default := 1, uniq := fun g => Subsingleton.elim g 1 }
  let A := AddCommGrpCat.of
    (Additive (Abelianization (End (SSet.FundamentalGroupoid.mk y))))
  have hA : IsZero A := AddCommGrpCat.isZero_of_subsingleton A
  exact hA.of_iso (SSet.fundamentalGroupAbelianizationHomologyOneIso U y).symm

end SSet.KanComplex

end
