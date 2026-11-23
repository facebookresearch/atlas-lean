/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeProjectivity
public import MathlibExt.AlgebraicGeometry.DltBoundaryFlipModels
public import Batteries.Util.ProofWanted

/-!
# Standard-boundary dlt threefold flips in characteristic greater than five

Hacon--Xu, arXiv1302.0298v2, Theorem 1.1.
The output is an actual small projective flip with its normalized
codimension-one boundary, retaining dlt and coefficient-one scope.
It does not assume klt or assert arbitrary-characteristic flips.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.DltBoundaryFlipModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.RelativeMoriContracts
open MathlibExt.AlgebraicGeometry.MoriContractionModels
open MathlibExt.AlgebraicGeometry.RelativeProjectivity

def_wanted standardDltThreefoldFlip
    {k : Type} [Field k] [IsAlgClosed k] (p : ℕ) [CharP k p] (large : 5 < p)
    (P : LogPair k 3) [HasModelCalculus P] (dlt : IsDlt P)
    (qfactorial : IsQFactorial P.variety)
    (standard : ∀ d : PrimePoint P.variety,
      P.boundary d = 1 ∨ ∃ m : ℕ, 0 < m ∧ P.boundary d = 1 - 1 / (m : ℝ))
    (S : Over (Spec (.of k))) (base : IsQuasiProjectiveBase S)
    (q : P.variety.X ⟶ S) (projective : IsHProjectiveOver q)
    (v : RelativeN1 q) (extremal : IsExtremal v)
    (negative : combinationOnClass q P.adjoint v < 0)
    (C : RelativeContraction P q v) (small : IsSmall C.map.left 3)
    (antiAdjoint : IsRelativelyAmpleR C.map (negativeCombination P.adjoint)) :
    {F : BoundaryFlip C // IsDlt F.source}

end MathlibExt.AlgebraicGeometry.DltBoundaryFlipModels
