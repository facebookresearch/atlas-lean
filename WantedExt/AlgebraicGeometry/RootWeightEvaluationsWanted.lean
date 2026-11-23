/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RootWeightEvaluations

/-!
# Identity and composition for actual groupified DF weight arrows

The maps are the fixed root-section/tensor/unit/multiplication recipe in
RootWeightEvaluations.lineArrow. Prove the functor laws on these actual
module maps, retaining every labelled monoid arrow.

Source: Niels Borne and Angelo Vistoli,
https://arxiv.org/abs/1001.0466v2, Proposition 5.2/Corollary 5.4 and
the root-weight functor used in Theorem 6.1.
-/

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories
open MathlibExt.AlgebraicGeometry.ParabolicSheafCategories
open MathlibExt.AlgebraicGeometry.RootWeightEvaluations

universe u

/-- Prove laws for the fixed native line/section arrow recipe. -/
theorem_wanted groupifiedLineWeightFunctorLaws (Y : Scheme.{u}) (P : CommMonCat.{u})
    (D : DeligneFaltingsChart Y P) (G : GroupifiedChart D) : LineFunctorLaws G
