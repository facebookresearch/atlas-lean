/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation

/-!
# Wanted naturality of the fixed affine-family evaluation

Assemble the publicly computed evaluation on simplices into its actual
natural map. The augmentation, product and native enriched mapping
object are fixed inputs. Geometricity, orientations and closed-form
nondegeneracy are separate targets.

Reference: PTVV, arXiv:1111.3209v4, §2.1.
-/

open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation

universe u

/-- **The evaluation map of a mapping prestack.** For a commutative ring $k$, a cofibrant
replacement functor $Q$ for simplicial commutative $k$-algebras, prestacks $X$ and $F$ over $k$ and
a fibrant replacement $R$ of $F$, with fibrant model $R(F)$: a morphism of prestacks
$\operatorname{Map}(X, F) \times X \to R(F)$ (`EvaluationModel`) from the product of the mapping
prestack `mappingPrestackFunctor k Q X F R` with $X$, whose value on every simplicial commutative
$k$-algebra $A$, simplicial degree $n$, mapping simplex $a$ and $x \in X(A)_n$ is the evaluation
`evaluateDegree`: the degree-$n$ component of the family $a$ at $A$, applied to the augmentation
$QA \to A$ and to $x$. -/
def_wanted derived_prestack_evaluation (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (X F : Prestack k)
    (R : FibrantReplacement F) : EvaluationModel Q X F R
