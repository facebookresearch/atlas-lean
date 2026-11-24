/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.ShtukaPartialFrobenius

/-!
# Pole partial-Frobenius on actual right shtukas

Prove that the fixed module pushout defines the new rank-`r` family.
The shifted pole graph and the unchanged zero graph must be disjoint.
The base family is smooth over `F_p`, so its Frobenius pullback is exact.

The underlying product Frobenius, bundles, graphs, right-shtuka category,
candidate pushout and its maps are completed code. Injectivity and the
shifted graph-line cokernel are source-covered base-change facts
(`pullbackConditions`), combined with the canonical cokernel map of the
actual flipped pushout square. The main requested result is the remaining
geometric local-freeness/rank.

References: Patrick Bieker, *Compactification of level maps of moduli
spaces of Drinfeld shtukas*, Definition 2.2 and Remark 2.3, pp. 3–4.
https://arxiv.org/abs/2205.09371
Vincent Lafforgue, *Chtoucas pour les groupes réductifs et paramétrisation
de Langlands globale*, §3, p. 50, formula (3.1): rotation of modification
chains and Frobenius on the moved legs.
https://arxiv.org/abs/1209.5352v4
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ShtukaPartialFrobenius

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ShtukaPartialFrobenius
open MathlibExt.AlgebraicGeometry.CurveVectorBundles

/-- The Frobenius pullback of the pole modification stays injective, and its cokernel is the line
bundle on the graph of the shifted pole: for a separated curve the graph is closed, so the cokernel
of the original pole modification is a line bundle on a closed graph, hence flat over the base, and
base change along the partial Frobenius preserves the injection and the graph-line cokernel (the
base-change step of the source shtuka API, which assumes separatedness). -/
public theorem_wanted pullbackConditions
    (p : ℕ) [Fact p.Prime] (X S : PrimeFieldScheme p) [IsSeparated X.hom] (r : ℕ)
    (A : Shtuka p X S r) : A.PullbackConditions

/-- The normalized pole rotation is a shtuka on the disjoint-leg open. -/
public theorem_wanted partialFrobeniusModification
    (p : ℕ) [Fact p.Prime] (X S : PrimeFieldScheme p)
    [IsProper X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [GeometricallyConnected X.hom] [Smooth S.hom]
    (r : ℕ) (hr : 0 < r) (A : Shtuka p X S r)
    (hlegs : Disjoint (Set.range (graph A.rotationPole))
      (Set.range (graph A.zero))) : IsVectorBundle A.rotationModule r

end WantedExt.AlgebraicGeometry.ShtukaPartialFrobenius
