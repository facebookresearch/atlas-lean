/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
public import MathlibExt.AlgebraicGeometry.StableLineMaps

/-!
# Fine degree-one stable-map moduli and their actual deformation complexes

This scope is genus zero, one marking, and degree one in complex projective
space of positive dimension. The source allows nodal stable maps; it does
not assume that every family is already a projective-line bundle. The
comparison must reconstruct the family from its actual rank-two coordinate
quotient followed by its actual marking line quotient.

The equivalence is normalized by the two canonical sheaf arrows, so a free
moduli carrier or an unrelated equivalence cannot satisfy the target. The
proper-base-change map is the literal adjoint of the pulled-back counit.
The obstruction and tangent statements use the actual direct images of the
Euler cokernel pulled to the stable-map curve.

Reference: Fulton--Pandharipande, *Notes on stable maps and quantum
cohomology*, https://arxiv.org/abs/alg-geom/9608011, §§1--3. Ordinary marked
prestable families, dual-graph stability and generic projective-bundle
constructions are already covered support and are excluded from the request.
Higher-degree/genus GW, DT objects and gluing/invariant theory remain outside
this fine degree-one comparison; no claims about those theories are made.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.StableLineMapComparisonWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
open MathlibExt.AlgebraicGeometry.StableLineMaps

variable (r : ℕ)
    (X : ProjectiveBundle Point 0 r (targetGenerators r))
    (T : ComplexScheme)

/-- Fine moduli of degree-one stable lines: for $r > 0$, the projective space
$\mathbb{P}^r_{\mathbb{C}}$ given as the projective bundle `X` of the free module of rank $r + 1$
over a point, and a Noetherian complex scheme $T$, an equivalence between the groupoid of families
over $T$ of one-pointed genus-zero stable maps of degree one to $\mathbb{P}^r$ and the groupoid of
quotient flags $\mathcal{O}_T^{r+1} \to Q \to L$ (epimorphisms, $Q$ locally free of rank two, $L$ a
line bundle), under which the flag of a family $(\pi : C \to T, s, f)$ is identified with
$\mathcal{O}_T^{r+1} \to \pi_* f^* \mathcal{O}(1) \to s^* f^* \mathcal{O}(1)$, the coordinate
quotient followed by evaluation at the marking. -/
public def_wanted moduliComparison (_positive : 0 < r) [IsNoetherian T.left] :
    StableLineModuliComparison r X T

/-- Base change for the degree-one direct image: for $r > 0$, the projective space
$\mathbb{P}^r_{\mathbb{C}}$ given as the projective bundle `X` of the free module of rank $r + 1$
over a point, a family $(\pi : C \to T, f)$ of one-pointed genus-zero stable maps of degree one to
$\mathbb{P}^r$ over a Noetherian complex scheme $T$, a morphism $h : T' \to T$ from a Noetherian
complex scheme and a family $(\pi', f')$ over $T'$ identified with the pullback of the first
(`FamilyBaseChange`), the canonical base-change map
$h^* \pi_* f^* \mathcal{O}(1) \to \pi'_* f'^* \mathcal{O}(1)$ (adjoint to the pulled-back counit) is
an isomorphism. -/
public theorem_wanted quotient_base_change (_positive : 0 < r) [IsNoetherian T.left]
    (F : StableLineFamily r X T)
    (T' : ComplexScheme) [IsNoetherian T'.left] (h : T' ⟶ T)
    (F' : StableLineFamily r X T') (b : FamilyBaseChange F h F') :
    IsIso (quotientBaseChange F b)

/-- Vanishing of the obstruction sheaf: for $r > 0$, the projective space
$\mathbb{P}^r_{\mathbb{C}}$ given as the projective bundle `X` of the free module of rank $r + 1$
over a point, a family $(\pi : C \to T, f)$ of one-pointed genus-zero stable maps of degree one to
$\mathbb{P}^r$ over a Noetherian complex scheme $T$ and a quasi-coherent $\mathcal{O}_T$-module $J$,
$R^1 \pi_* (f^* T_{\mathbb{P}^r} \otimes \pi^* J) = 0$, where $T_{\mathbb{P}^r}$ is the cokernel of
the Euler map $\mathcal{O} \to \mathcal{O}(1)^{r+1}$. -/
public theorem_wanted relative_map_obstruction_vanishes (_positive : 0 < r)
    [IsNoetherian T.left] (F : StableLineFamily r X T)
    (J : T.left.Modules) [J.IsQuasicoherent] : IsZero (deformationModule F 1 J)

/-- The tangent sheaf of degree-one stable lines: for $r > 0$, the projective space
$\mathbb{P}^r_{\mathbb{C}}$ given as the projective bundle `X` of the free module of rank $r + 1$
over a point and a family $(\pi : C \to T, f)$ of one-pointed genus-zero stable maps of degree one
to $\mathbb{P}^r$ over a Noetherian complex scheme $T$, the sheaf
$\pi_* (f^* T_{\mathbb{P}^r} \otimes \pi^* \mathcal{O}_T)$ is locally free of rank $2r + 1$, where
$T_{\mathbb{P}^r}$ is the cokernel of the Euler map $\mathcal{O} \to \mathcal{O}(1)^{r+1}$. -/
public theorem_wanted relative_map_tangent_bundle (_positive : 0 < r) [IsNoetherian T.left]
    (F : StableLineFamily r X T) :
    IsBundle (deformationModule F 0 (SheafOfModules.unit T.left.ringCatSheaf)) (2 * r + 1)

end WantedExt.AlgebraicGeometry.StableLineMapComparisonWanted
