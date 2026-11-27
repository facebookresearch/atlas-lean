/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import MathlibExt.AlgebraicGeometry.PointedPicardFamilies

@[expose] public section

/-!
# Generalized Jacobians of pointed reduced curves

The request extends the pointed smooth-curve Picard interface to reduced
connected proper curves. The group need not be proper. Its dimension is
the actual coherent arithmetic genus, and its normalized universal family
represents Picard zero on arbitrary parameter schemes.

Source: Bosch--Lütkebohmert--Raynaud, *Néron Models*, Chapter 9,
generalized Jacobians and the relative Picard functor. See also SGA 6,
Exposé XII, and Stacks Project, Tag 0D25.
https://stacks.math.columbia.edu/tag/0D25
-/

namespace WantedExt.AlgebraicGeometry.GeneralizedJacobian

open CategoryTheory CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open _root_.MathlibExt.AlgebraicGeometry.PointedPicardFamilies

universe u

/-- **Generalized Jacobian of a pointed curve.** Let $k$ be an algebraically closed field of
characteristic zero and $C$ a proper curve over $k$ (proper, of dimension one) that is
geometrically reduced and geometrically connected, with a $k$-point $p$. Then: a Picard-zero model
of $(C, p)$ (`PicardZeroModel`), namely a geometrically connected commutative group scheme $J$
over $k$, smooth of relative dimension $\dim_k H^1(C, \mathcal{O}_C)$, with a line bundle on
$C × J$ that is normalized along $p$ and fibrewise algebraically trivial, whose pullbacks give
exactly such line bundles on $C × T$ for every $k$-scheme $T$ (each from a unique map $T → J$),
compatibly with the group structure: the identity gives the trivial bundle and addition gives the
tensor product. -/
public def_wanted generalizedJacobian
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (C : Over (Spec (.of k))) [IsProperCurve C.hom]
    [GeometricallyReduced C.hom] [GeometricallyConnected C.hom]
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ C) : PicardZeroModel C p

end WantedExt.AlgebraicGeometry.GeneralizedJacobian
