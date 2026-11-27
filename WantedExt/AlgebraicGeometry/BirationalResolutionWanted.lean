/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.BirationalResolution

/-!
# Resolution of singularities in characteristic zero

The requested resolution retains its locally projective proper map, dense-open
birational witness and normalization over the smooth locus.

General birational maps are already in Mathlib. The pinned Axiom source
implements resolution and normalized blowup chains in dimension two;
its algebraic-space resolution file defines the property. This request
is the all-dimensional characteristic-zero existence theorem.

References:
* Hironaka, *Resolution of singularities of an algebraic variety over a
  field of characteristic zero*, Ann. Math. 79 (1964), Parts I–II.
* Bierstone–Milman, *Functoriality in resolution of singularities*,
  Theorem 1.1, https://arxiv.org/abs/math/0702375v1.
* Covered surface source: AxiomMath/Stacks at
  c496df0d9beea9deaeabcea8492605f9a0a2313b,
  in `StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/Resolution/`,
  file `ExistenceByNormalizedBlowUps.lean`.
* Definition source: the same revision,
  `StacksFrontier/AlgebraicGeometry/Spaces/ResolutionOfSingularities.lean`.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.BirationalResolutionWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.BirationalResolution

universe u

/-- **Hironaka's resolution of singularities in characteristic zero.** Let $k$ be a field of
characteristic zero and $X$ an integral separated $k$-scheme of finite type. Then there is a smooth
integral $k$-scheme $\tilde X$ with a proper, locally projective, birational morphism
$\tilde X \to X$ that is an isomorphism over every open subscheme of $X$ smooth over $k$
(`ResolutionModel`). -/
def_wanted resolution (k : Type u) [Field k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] : ResolutionModel X

end WantedExt.AlgebraicGeometry.BirationalResolutionWanted
