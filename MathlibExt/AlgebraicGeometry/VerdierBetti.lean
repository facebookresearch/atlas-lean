/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CompactSupportBetti

@[expose] public noncomputable section

/-!
# Fundamental classes and traces from actual dualizing representation

A purity isomorphism identifies the dualizing complex with the rational
constant complex shifted by the real dimension. Its inverse determines both
the Borel--Moore fundamental class and the compact-support trace below.
The trace is evaluated using the actual rational-linear representation
of derived compact-support sections. It is not a separate chosen linear map.

The purity isomorphism remains an explicit input; its algebraic construction
and complex-orientation normalization are separate mathematical work.
Reference: Kashiwara--Schapira, *Sheaves on Manifolds*, Chapter III.
-/

namespace MathlibExt.AlgebraicGeometry.VerdierBetti

open CategoryTheory CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.BettiRealization
open MathlibExt.AlgebraicGeometry.CompactSupportBetti

attribute [local instance] HasDerivedCategory.standard

/-- The actual constant coefficient complex in the bounded-below category. -/
abbrev unitPlus (Z : TopCat.{0}) : DerivedCategory.Plus (RationalSheaf Z) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj (rationalConstantSheaf Z)

/-- The fundamental class determined by a specified purity isomorphism. -/
def fundamentalClass (Z : TopCat.{0}) (D : DualizingComplex Z) (d : ℕ)
    (e : D.obj ≅ (rationalUnit Z)⟦(2 * d : ℤ)⟧) :
    BorelMoore Z D (2 * d) :=
  (shiftFunctorZero (RationalDerived Z) ℤ).inv.app (rationalUnit Z) ≫
    (shiftFunctorAdd' (RationalDerived Z) (2 * d : ℤ) (-(2 * d : ℤ)) 0
      (add_neg_cancel _)).hom.app (rationalUnit Z) ≫
    (shiftFunctor (RationalDerived Z) (-(2 * d : ℤ))).map e.inv

/-- Compact-support trace, derived from the same purity and representation. -/
def topTrace (Z : TopCat.{0}) (D : DualizingComplex Z) (d : ℕ)
    (e : D.obj ≅ (rationalUnit Z)⟦(2 * d : ℤ)⟧) :
    (derivedSections Z).obj ((unitPlus Z)⟦(2 * d : ℤ)⟧) ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{0} ℚ) 0).obj
        (ModuleCat.of ℚ ℚ) :=
  (D.representation.hom.app (op ((unitPlus Z)⟦(2 * d : ℤ)⟧))).hom
    ((DerivedCategory.Plus.ι.commShiftIso (2 * d : ℤ)).hom.app
      (unitPlus Z) ≫ e.inv)

end MathlibExt.AlgebraicGeometry.VerdierBetti
