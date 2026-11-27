/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import MathlibExt.AlgebraicGeometry.PlurigenusFamilies

@[expose] public section

/-!
# Deformation invariance of higher-dimensional plurigenera

Authors: Yum-Tong Siu; Yujiro Kawamata.

Sources: Siu, *Invariance of Plurigenera*, Main Theorem,
https://arxiv.org/abs/alg-geom/9712016; Kawamata, *Deformations of
canonical singularities*, Theorem 6,
https://arxiv.org/abs/alg-geom/9712018v2.

This is their smooth projective general-type slice over a connected
smooth complex parameter curve, with local constancy propagated over
that connected curve. The canonical line is characterized on actual
scheme fibers by natural Serre duality. It does not request stable/slc
compactification or a Kollár condition on singular degenerations.
-/

namespace WantedExt.AlgebraicGeometry.PlurigenusFamilies

open CategoryTheory CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.PlurigenusFamilies

/-- **Deformation invariance of plurigenera over a smooth complex curve.** Let $n \ge 2$ and let
$P$ be a smooth projective family $f : X \to B$ of $n$-dimensional varieties of general type over a
smooth, geometrically irreducible, quasi-compact curve $B$ over $\mathbb{C}$
(`SmoothGeneralTypeFamilyOverCurve`), with a line bundle on $X$ restricting to the canonical line
of every geometric fibre. Then for every $m > 0$, the $m$-th plurigenus
$h^0(X_x, K_{X_x}^{\otimes m})$ of the fibre takes the same value at any two geometric points $x$,
$y$ of $B$, valued in algebraically closed fields (so over closed and nonclosed points alike). -/
public theorem_wanted deformationInvarianceOfPlurigenera
    (n : ℕ) (hn : 2 ≤ n) (P : SmoothGeneralTypeFamilyOverCurve (k := ℂ) n)
    (m : ℕ) (hm : 0 < m)
    (Ω Ω' : Type) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ P.B.left) (y : Spec (.of Ω') ⟶ P.B.left) :
    plurigenus P x m = plurigenus P y m

end WantedExt.AlgebraicGeometry.PlurigenusFamilies
