/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.MeasureTheory.OptimalTransport.KantorovichRubinstein
public import MathlibExt.MeasureTheory.OptimalTransport.WassersteinConvergence

/-!
# Wasserstein distances and weak convergence

The metrization of weak convergence in `P_p` (Theorem 6.9) of C. Villani,
*Optimal Transport: Old and New*, Grundlehren 338, Springer 2009,
for the Wasserstein distance of `MathlibExt.MeasureTheory.OptimalTransport.Wasserstein`.
A complete separable metric space with its Borel σ-algebra stands for Villani's Polish space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling)
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein (wasserstein transportCost)

namespace MathlibExt.MeasureTheory.WassersteinWanted

end MathlibExt.MeasureTheory.WassersteinWanted
