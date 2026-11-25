/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ComplexTorusTorsors

/-!
# Continuous-torus equivariant Betti realization for free algebraic torsors

The homotopy quotient is the actual geometric realization of the singular
diagonal of the topological orbit bar. The augmentation to the actual
scheme quotient is constructed from the invariant action equation. The
comparison concerns its literal rational derived-sheaf cohomology pullback.

The complex torus retains its continuous unit topology. The completed
TauCeti discrete-group classifying-space construction, at revision
62bbc0596dc3539d488232e4e924a338548ea0a9,
TauCeti/AlgebraicTopology/ClassifyingSpace/Action.lean, only uses translation
of a vertex-labeled countable join by a discrete group; it is excluded as an
already covered primitive, not identified with this continuous-torus target.
Algebraic Gm and generic torsor/quotient constructions in public Axiom/Mathlib
are also covered and reused as standing actual input data.

Reference: Segal, *Classifying spaces and spectral sequences*, Publ. Math.
IHES 34 (1968), §§2--3; Edidin--Graham, *Equivariant intersection theory*,
https://arxiv.org/abs/alg-geom/9603008, §2. This scope supplies the action,
continuous realization and restriction bridge for actual free Gm torsors.
General equivariant Chow products, integration and fixed-point localization
remain residual scope beyond this comparison.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ComplexTorusBorelComparisonWanted

open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.ComplexTorusTorsors
open MathlibExt.AlgebraicGeometry.BettiFunctoriality

/-- **Borel comparison for $\mathbb{G}_m$-torsors over complex varieties.** Let $X$ and $Y$ be
complex varieties (separated, of finite type and geometrically reduced over $\mathbb{C}$), $A$ an
action of $\mathbb{G}_m = \operatorname{Spec} \mathbb{C}[T, T^{-1}]$ on $X$ and $q : X \to Y$ a
$\mathbb{G}_m$-torsor for $A$ (`TorusTorsor`: $q$ is invariant, smooth and surjective,
$(g, x) \mapsto (x, g x)$ is an isomorphism onto $X \times_Y X$, and the induced action of
$\mathbb{C}^\times$ on the complex points of $X$ is continuous). Then for every $n \in \mathbb{Z}$,
pullback along the canonical map from the Borel model of the homotopy quotient of
$X(\mathbb{C})$ by $\mathbb{C}^\times$ (the realization of the diagonal of the singular sets of the
bar construction) to $Y(\mathbb{C})$ is bijective on degree-$n$ rational cohomology, the cohomology
of the constant sheaf $\mathbb{Q}$. -/
public theorem_wanted free_torus_quotient_comparison (X Y : ComplexScheme)
    [IsComplexVariety X] [IsComplexVariety Y] (A : CategoryTheory.ModObj Gm X) (q : X ⟶ Y)
    [T : TorusTorsor A q] (n : ℤ) :
    Function.Bijective (cohomologyPullback (borelQuotientMap A q) n)

end WantedExt.AlgebraicGeometry.ComplexTorusBorelComparisonWanted
