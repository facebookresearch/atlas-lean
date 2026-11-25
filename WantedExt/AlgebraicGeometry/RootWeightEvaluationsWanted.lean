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

/-- **Root-weight line arrows of a groupified chart are functorial.** Let $Y$ be a scheme, $P$ a
commutative monoid, $D$ a Deligne–Faltings chart of $Y$ over $P$ (line bundles $L_p$ with sections
$s_p$ for $p \in P$, compatible with units and tensor products) and $G$ an extension of $D$ to the
groupification $P^{\mathrm{gp}}$ (line bundles $L_v$ for $v \in P^{\mathrm{gp}}$, with unit and
multiplication isomorphisms and identifications $L_{[p]} \cong L_p$). For a weight arrow
$a : v \to w$ labelled by $p \in P$ with $[p]\,v = w$, let $L_v \to L_w$ (`lineArrow G a`) be
tensoring with the section $s_p$, followed by $L_p \cong L_{[p]}$ and the multiplication
$L_{[p]} \otimes L_v \cong L_w$. These arrows send identities to identities and composites to
composites (`LineFunctorLaws G`). -/
theorem_wanted groupifiedLineWeightFunctorLaws (Y : Scheme.{u}) (P : CommMonCat.{u})
    (D : DeligneFaltingsChart Y P) (G : GroupifiedChart D) : LineFunctorLaws G
