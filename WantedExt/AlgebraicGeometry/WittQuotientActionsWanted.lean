/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.WittQuotientActionModels
public import MathlibExt.AlgebraicGeometry.RelativeWittCoefficientDVRModels
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Source-normalized left actions on the actual Witt Grassmannian

Zhu, arXiv:1407.8519v3, Sections 0.5 and 1.1--1.2. The left action
is fixed by actual group multiplication on the original right-action
quotient. The native fpqc group sheaves retain the original coefficient
maps, and the actual Grassmannian sheaf action has the full unit,
associativity and raw-to-sheaf square. The positive action is the
original localization homomorphism followed by that same action.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.WittQuotientActions

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.RelativeWittCoefficientDVRModels
open MathlibExt.AlgebraicGeometry.WittQuotientActionModels

/-- Construct the genuine loop-group action and its actual fpqc descent dictionary. -/
public def_wanted nativeLoopQuotientActions
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (B : Type) [CommRing B] [IsDomain B] [Algebra (WittVector p k) B] (pi : B)
    (C : CoefficientData p k B pi)
    (G : Over (Spec (.of B))) [GrpObj G] [IsAffineHom G.hom]
    [LocallyOfFinitePresentation G.hom] [Smooth G.hom] [GeometricallyConnected G.hom] :
    QuotientActions p k B pi G

end WantedExt.AlgebraicGeometry.WittQuotientActions
