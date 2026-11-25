/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DerivedSelfIntersections

/-!
# The global first-neighborhood criterion for derived self-intersection formality

Arinkin--Căldăraru, https://arxiv.org/abs/1007.1671, Theorem 0.7,
underlying derived-object implication. A conormal extension is equivalent
to a normal extension by dualizing the actual finite locally free bundle.
No formality, exterior-Tor conclusion or splitting is an input assumption.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DerivedSelfIntersectionsWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.DerivedSelfIntersections

universe u

/-- **Formality criterion for derived self-intersections.** Arinkin–Căldăraru, Theorem 0.7: let
$k$ be an algebraically closed field of characteristic zero, $X$ and $Y$ smooth, quasi-compact,
separated $k$-schemes and $i : X → Y$ a closed immersion, and assume that derived pullbacks and
pushforwards of module sheaves exist. If the conormal sheaf of $i$ extends to a finite locally free
sheaf on the first infinitesimal neighbourhood of $X$ in $Y$ (`ConormalExtension`), then the
derived self-intersection $Li^* Ri_* \mathcal{O}_X$ is formal: it is isomorphic to the complex of
its cohomology sheaves with zero differential. -/
public theorem_wanted self_intersection_formal
    [HasDerivedPullbacks.{u}] [HasDerivedPushforwards.{u}]
    (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (X Y : Over (Spec (.of k))) [Smooth X.hom] [Smooth Y.hom]
    [QuasiCompact X.hom] [QuasiCompact Y.hom] [IsSeparated X.hom] [IsSeparated Y.hom]
    (i : X ⟶ Y) [IsClosedImmersion i.left] (N : ConormalExtension i.left) :
    IsFormal (selfIntersection i.left)

end WantedExt.AlgebraicGeometry.DerivedSelfIntersectionsWanted
