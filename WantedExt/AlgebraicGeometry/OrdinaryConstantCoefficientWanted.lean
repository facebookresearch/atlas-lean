/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.OrdinaryConstantCoefficientModels
public import MathlibExt.AlgebraicGeometry.OrdinaryConstantCoefficient

/-!
# Native constant-ring module construction and full DG comparison

The constant simplicial ring, all native module complexes, scalar
actions, homogeneous maps and balanced Tor tests are fixed before
these requests. No Perf descent statement is a source hypothesis.

Sources: Keller Section2; Bhatt--Mathew1807.04725v4, Section5.4.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicGeometry.OrdinaryConstantCoefficientModels

open _root_.CategoryTheory
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open OrdinarySchemeModuleFamilies

/-- Identify the native normalization of every constant ordinary ring, including zero rings. -/
def_wanted ordinary_constant_ring_source (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ) :
  ConstantRingSource A N

/-- Assemble the complete native ordinary-to-DG module comparison with every action and homogeneous map fixed. -/
def_wanted ordinary_constant_module_source (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ)
    (C : ConstantRingSource A N) : OrdinaryModuleSource A N C

/-- Assemble the same native constant-ring module/action construction over all ordinary rings. -/
def_wanted ordinary_tor_system (N : ShuffleAlgebraFunctor ℤ) : OrdinaryTorSystem N

end MathlibExt.AlgebraicGeometry.OrdinaryConstantCoefficientModels
