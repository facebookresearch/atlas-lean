/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AbelianSchemes

/-!
# General relative dual abelian-scheme interface

The dual and Poincaré family are actual schemes and line-module sheaves over
an arbitrary base. Both zero sections, geometric algebraic triviality,
tensor addition and universality for every test scheme are explicit public
contracts. Their construction is a shared dependency; no field,
characteristic-zero or algebraic-closure restriction is built into the type.

Axiom/Stacks proves arbitrary abelian-scheme base change, and that primitive
is completed in MathlibExt. TauCeti's relative Picard/rigidification
constructors and curve degree-zero functors are available source support;
those curve statements do not identify the relative dual of a general
higher-dimensional abelian scheme.

Reference: Kleiman, *The Picard scheme*, in FGA Explained, the relative
Picard, rigidification and identity-component constructions.
https://arxiv.org/abs/math/0504020
Bosch–Lütkebohmert–Raynaud, *Néron Models*, Chapter 8.
https://doi.org/10.1007/978-3-642-51438-8
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DualAbelianSchemesWanted

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AbelianSchemes

universe u

def_wanted dual_abelian_scheme (S : Scheme.{u}) (A : AbelianScheme S) :
    DualAbelianScheme A

end WantedExt.AlgebraicGeometry.DualAbelianSchemesWanted
