/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.FormalNearbyCycleModels
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Actual smooth formal generic-fibre and nearby source construction

The original O_C ring, finite model presentations, p-localizations, Banach
topologies, formal/generic overlaps and all coordinate maps are fixed by
the source types. These are source-normalized construction requests, with
generic étale objects and maps chosen together. The nearby right-derived
functor is the specified site pushforward; syntomic comparison is separate.

References: BMS19 arXiv:1802.03261v2, Theorem 10.1; BMS18
arXiv:1602.03148v3, Section 3; Huber's formal generic-fibre construction.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.FormalGenericFibreModels

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open FormalGenericFibreModels FormalNearbyCycleModels AnalyticTateAdicModels

public def_wanted smoothFormalGenericFibre
    (p : ℕ) [Fact p.Prime] (C : CompletePadicField p)
    (X : MathlibExt.AlgebraicGeometry.FormalGenericFibreModels.FormalScheme p C)
    (hSmooth : ∀ n : ℕ, Smooth (X.structureMap.app n)) :
    Σ G : AnalyticAdicSpace p, GenericAtlas p C X G

public def_wanted genericEtaleFibreFunctor
    (p : ℕ) [Fact p.Prime] (C : CompletePadicField p)
    (X : MathlibExt.AlgebraicGeometry.FormalGenericFibreModels.FormalScheme p C)
    (G : AnalyticAdicSpace p) (A : GenericAtlas p C X G)
    (hSmooth : ∀ n : ℕ, Smooth (X.structureMap.app n)) : GenericEtaleModel p C A

public theorem_wanted genericEtaleFibreContinuous
    (p : ℕ) [Fact p.Prime] (C : CompletePadicField p)
    (X : MathlibExt.AlgebraicGeometry.FormalGenericFibreModels.FormalScheme p C)
    (G : AnalyticAdicSpace p) (A : GenericAtlas p C X G) (E : GenericEtaleModel p C A) :
    E.functor.IsContinuous (formalEtaleTopology p C X) (AnalyticDiamondEtaleSites.analyticEtaleTopology p G)

public def_wanted nearbyDerivedSource
    (p : ℕ) [Fact p.Prime] (C : CompletePadicField p)
    (X : MathlibExt.AlgebraicGeometry.FormalGenericFibreModels.FormalScheme p C)
    (G : AnalyticAdicSpace p) (A : GenericAtlas p C X G) (E : GenericEtaleModel p C A)
    [E.functor.IsContinuous (formalEtaleTopology p C X) (AnalyticDiamondEtaleSites.analyticEtaleTopology p G)] :
    E.HasDerivedNearby

end WantedExt.AlgebraicGeometry.FormalGenericFibreModels
