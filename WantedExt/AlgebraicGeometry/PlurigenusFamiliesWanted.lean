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

/-- Every positive plurigenus is constant in the actual smooth projective
general-type family. The dimension restriction selects the
higher-dimensional-variety packet. -/
public theorem_wanted deformationInvarianceOfPlurigenera
    (n : ℕ) (hn : 2 ≤ n) (P : SmoothGeneralTypeFamily (k := ℂ) n)
    (m : ℕ) (hm : 0 < m)
    (x y : 𝟙_ (Over (Spec (.of ℂ))) ⟶ P.B) :
    plurigenus P x m = plurigenus P y m

end WantedExt.AlgebraicGeometry.PlurigenusFamilies

