/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HallSemiclassicalOperations

/-!
# The actual zero-sheaf Hall unit

The source is the actual represented Spec(C), and the moduli map
classifies the zero module on every parameter scheme. The Hall and
semiclassical units are the corresponding actual geometric symbols.
Unit laws are separate properties of the exact-sequence convolution.

Reference: Bridgeland, arXiv:1002.4372v1, §4.4.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HallZeroObjectModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open StackCycleGeometry GeometricHallStackFunctions HallFamilyStackModels
open HallConvolutionOperations HallSemiclassicalOperations HallProjectiveInverseModels

variable {X : Over base} (H : HallStacks X)

/-- The map is fixed on every family by the actual zero-module property. -/
structure ZeroObjectModel where
  point : FiniteTypeStack
  source : SchemeSource point
  normalized : source.scheme=pointScheme.scheme
  map : StackHom point.stack H.moduli
  zero : ∀ (T : Over base) (p : point.stack.Fibre T),
    IsZero ((H.families.fibre T).functor.obj ((component map T).obj p)).module

variable {H}

def zeroGenerator (Z : ZeroObjectModel H) : Generator H.moduli := ⟨Z.point,Z.map⟩

def hallUnit (Z : ZeroObjectModel H) : LefschetzStackFunctions H.moduli :=
  stageSymbol (zeroGenerator Z) 0

def regularUnit (Z : ZeroObjectModel H) : Regular H.moduli :=
  regularSymbol (zeroGenerator Z) Z.source 0

def semiclassicalUnit {D : ConvolutionModels H} {h : ConvolutionDescent D}
    {L : ∀ g : Generator H.moduli, LefschetzProduct g} {hL : LefschetzDescent L}
    (C : RegularClosure h hL) (Z : ZeroObjectModel H) : Semiclassical C :=
  (semiclassicalRelations C).mkQ (regularUnit Z)

end MathlibExt.AlgebraicGeometry.HallZeroObjectModels
