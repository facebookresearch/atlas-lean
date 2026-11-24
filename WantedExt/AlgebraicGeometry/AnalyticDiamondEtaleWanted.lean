/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AnalyticDiamondEtaleSites

/-!
# Actual analytic and diamond etale-site comparison requests

These compare the prescribed diamondification functor on the native
etale slice sites. Source etaleness is the original finite-Tate-ring
chart condition; target etaleness uses actual perfectoid affine
pullbacks. Continuity and equivalence are results, not source inputs.

Source: Scholze, arXiv:1709.07343v4, Lemma 15.6.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AnalyticDiamondEtale

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.AnalyticTateAdicModels
open MathlibExt.AlgebraicGeometry.AnalyticAdicDiamondification
open MathlibExt.AlgebraicGeometry.AnalyticDiamondEtaleSites

/-- Actual analytic etale maps retain representable etaleness under diamondification. -/
public theorem_wanted etalePreservation (p : ℕ) [Fact p.Prime]
    (R : AffineRealization p) : PreservesEtale p R

/-- The prescribed etale-site functor is an equivalence. -/
public theorem_wanted etaleEquivalence (p : ℕ) [Fact p.Prime]
    (R : AffineRealization p) (Y : AnalyticAdicSpace p) (h : PreservesEtale p R) :
    (etaleDiamondification p R Y h).IsEquivalence

/-- Actual etale covers satisfy the continuity required by native inverse image. -/
public theorem_wanted etaleContinuity (p : ℕ) [Fact p.Prime]
    (R : AffineRealization p) (Y : AnalyticAdicSpace p) (h : PreservesEtale p R) :
    (etaleDiamondification p R Y h).IsContinuous (analyticEtaleTopology p Y)
      (diamondEtaleTopology p ((diamondFunctor p R).obj Y))

/-- Finite etaleness is preserved on the actual whole affinoid inverse images. -/
public theorem_wanted finiteEtalePreservation (p : ℕ) [Fact p.Prime]
    (R : AffineRealization p) : PreservesFiniteEtale p R

/-- The actual finite-etale site comparison is an equivalence. -/
public theorem_wanted finiteEtaleEquivalence (p : ℕ) [Fact p.Prime]
    (R : AffineRealization p) (Y : AnalyticAdicSpace p) (h : PreservesFiniteEtale p R) :
    (finiteEtaleDiamondification p R Y h).IsEquivalence

end WantedExt.AlgebraicGeometry.AnalyticDiamondEtale
