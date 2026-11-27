/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RelativeModuliStackModels
public import MathlibExt.AlgebraicGeometry.RelativeRootEquivalenceGroups

/-!
# Base change of relative maps

Actual expansion families, full contact ideals, etale pure node equations,
disconnected groupoids, common target automorphisms and ordered root/leg
types are fixed in MathlibExt. The constructor supplies the actual Cartesian
pullbacks of relative maps. Moduli of relative maps are requested in
`LiExpandedGeometryWanted` with numerical classes: a fixed rational Chow class is
not locally constant in families, so it does not label a finite-type moduli
stack.
Sources: Jun Li arXiv:math/0009097v1, Section4.3;
arXiv:math/0110113v1, Sections1--3.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativeModuliStackModelsWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open ExpandedTargetChainGeometry RelativeProjectiveLineModels StandardRelativeExpansionModels
open ExpandedRelativeFamilies RelativeExpandedMapFamilies RelativeMapTypeModels RelativeModuliStackModels

def_wanted nativeRelativeMapReindex (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P : RelativePair (k := k)) (R : ProjectiveLine P.divisor.left (normalLineModule P))
    (S : StandardSystem P R) {T U : Over (Spec (.of k))} (h : T ⟶ U)
    {F : ExpandedFamily P R S U} {n r g : ℕ} {order : Fin r → ℕ}
    (f : RelativeMapOn P R S U F n r g order) (E : ExpandedReindex P R S h F) :
    MapReindex P R S h f E

end WantedExt.AlgebraicGeometry.RelativeModuliStackModelsWanted
