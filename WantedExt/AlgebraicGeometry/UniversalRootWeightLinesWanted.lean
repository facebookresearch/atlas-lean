/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.UniversalRootWeightLines

/-!
# Universal Lambda_v lines and sections on the actual denominator-root stack

Construct the actual finite-presentation rank-one cartesian stack modules,
whose affine values and section-induced arrows are the given root-family
groupified DF lines. Native positive root restriction, tensor/unit and
full weight/base naturality diagrams are fixed in the output type.

Source: Niels Borne and Angelo Vistoli,
https://arxiv.org/abs/1001.0466v2, Corollary 5.4 and Theorem 6.1 pp33–35.
The ordinary cartesian/QCoh and tensor/pullback producers retain the
completed source-integration attribution in the imported native modules.
-/

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
open MathlibExt.AlgebraicGeometry.DenominatorRootStacks
open MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage
open MathlibExt.AlgebraicGeometry.MonoidSheafCharts
open MathlibExt.AlgebraicGeometry.UniversalRootWeightLines

/-- Universal root weight lines with actual values, section arrows and complete native diagrams,
for a root model whose evaluated line comparisons are coherent on identities and composites. -/
def_wanted universalRootWeightLines
    [∀ (T Z : Scheme.{0}) (f : T ⟶ Z), HasInverseImage f]
    (I : NativeDFImages.{0}) (X : Scheme.{0})
    (A B : DeligneFaltingsSheaves.MonoidSheaf X) (D : Structure A)
    (j : DenominatorSystem A B)
    (U : X.Etale) (R : Model I D j.map U.hom)
    (identityLines : IdentityLineCoherent I D j.map U R)
    (compositionLines : CompositionLineCoherent I D j.map U R) : StackWeights I D j.map U R
