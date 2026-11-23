/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.HallTorsionAndSlopeModels

/-!
# Native torsion Hall identity and the corrected slope-window argument

The torsion identity is expressed in the actual infinite-type
geometric Hall presentation, restricted to Coh_{≤1}. Its factors
are the actual zero-dimensional and pure family cuts.

The second request is the concrete three-step-filtration claim in
the v3 correction. It controls the middle quotient inside the fixed
finite slope window with μ>r s. The false unrestricted convergence
statement (49) is not a declaration.

Reference: Bridgeland, arXiv:1002.4374v3, Lemma 4.1,
§7.4, equation (51) and the following filtration argument.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.HallWallCrossingSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open GeometricHallStackFunctions HallFamilyStackModels HallExactSequenceFamilies StablePairFamilies
open HallNumericalGradingModels HallTorsionAndSlopeModels ProjectiveLineSystems

def_wanted actual_zero_dimensional_family_cut {X : Over base} (HX : Threefold X)
    (H : HallStacks X) : ZeroDimensionalCut H

def_wanted actual_pure_family_cut {X : Over base} (HX : Threefold X)
    (H : HallStacks X) : PureCut H

def_wanted actual_infinite_exact_sequence_convolutions {X : Over base} (HX : Threefold X)
    (H : HallStacks X) : InfiniteHallStackFunctions.ConvolutionModels H

theorem_wanted actual_infinite_convolution_descent {X : Over base} (HX : Threefold X)
    {H : HallStacks X} (D : InfiniteHallStackFunctions.ConvolutionModels H) :
    InfiniteHallStackFunctions.ConvolutionDescent D

theorem_wanted actual_torsion_pair_hall_identity {X : Over base} (HX : Threefold X)
    {H : HallStacks X} (P : ZeroDimensionalCut H) (Q : PureCut H)
    {D : InfiniteHallStackFunctions.ConvolutionModels H}
    (h : InfiniteHallStackFunctions.ConvolutionDescent D) :
    InfiniteHallStackFunctions.symbol (fullGenerator H) =
      InfiniteHallStackFunctions.convolution h
        (InfiniteHallStackFunctions.symbol (cutGenerator P))
        (InfiniteHallStackFunctions.symbol (cutGenerator Q))

theorem_wanted actual_corrected_slope_window_middle {X : Over base} {HX : Threefold X}
    [IsNoetherian X.left] (N : NumericalData X HX) (L : LineBundle X.left) (hL : IsAmpleLine L)
    (F : ThreeStepFiltration (X := X) complexPoint) (s mu : ℝ) (hs : 0≤s) (hmu : 0<mu)
    (bound : (filtrationDegree N L F : ℝ)*s<mu)
    (hE : SlopeWindow L F.second.middle (-s) s)
    (hA : SlopeWindow L F.first.sub 0 mu)
    (hC : StrictUpperWindow L F.second.quotient (-mu) 0) :
    SlopeWindow L F.first.quotient (-mu) mu

end WantedExt.AlgebraicGeometry.HallWallCrossingSources
