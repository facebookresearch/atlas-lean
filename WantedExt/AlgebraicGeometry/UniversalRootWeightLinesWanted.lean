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

/-- **Universal root weight lines on a denominator-root stack.** Assume that pullback of étale
sheaves of commutative monoids along every morphism of schemes exists (`HasInverseImage`). Let $X$
be a scheme, `I` inverse-image data for Deligne–Faltings structures, $D$ a Deligne–Faltings
structure on a monoid sheaf $A$ on $X$, $j : A \to B$ a locally Kummer map of coherent monoid
sheaves, $U \to X$ étale and $R$ a model of the root stack over $U$ whose root-line comparisons are
trivial on identity arrows and compatible with composites. Then: a functor $w \mapsto \Lambda_w$
from the weight category of $B(U)$ (elements of its groupification, with arrows labelled by
elements of $B(U)$) to quasi-coherent modules on the stack of $R$, each finitely presented of
constant rank one, with, at every affine point of the stack, an extension of the Deligne–Faltings
structure of its root family to the groupification and an identification of the sections of
$\Lambda_w$ there with the global sections of the resulting weight-$w$ line, natural in $w$ and in
arrows of affine points and compatible, through pullback comparisons, with the positive lines,
unit, multiplication, weight arrows, identities and composites (`StackWeights`). -/
def_wanted universalRootWeightLines
    [∀ (T Z : Scheme.{0}) (f : T ⟶ Z), HasInverseImage f]
    (I : NativeDFImages.{0}) (X : Scheme.{0})
    (A B : DeligneFaltingsSheaves.MonoidSheaf X) (D : Structure A)
    (j : DenominatorSystem A B)
    (U : X.Etale) (R : Model I D j.map U.hom)
    (identityLines : IdentityLineCoherent I D j.map U R)
    (compositionLines : CompositionLineCoherent I D j.map U R) : StackWeights I D j.map U R
