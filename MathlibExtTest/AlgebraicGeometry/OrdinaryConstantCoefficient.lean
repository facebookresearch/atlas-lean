/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.OrdinaryConstantCoefficient

/-!
# Consequences of the ordinary constant-coefficient comparison

The comparison induces an equivalence on homotopy categories and isomorphisms
on Hom cohomology in every degree.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExtTest.AlgebraicGeometry.OrdinaryConstantCoefficient

open _root_.CategoryTheory
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.OrdinarySchemeModuleFamilies
open MathlibExt.AlgebraicGeometry.OrdinaryConstantCoefficientModels

example (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ)
    (C : ConstantRingSource A N) (J : OrdinaryModuleSource A N C) :
    letI := moduleDG A
    J.functor.mapDGHomotopyCategory.IsEquivalence := by
  let _ := moduleDG A
  exact (ordinary_constant_module_quasi_equivalence A N C J).isEquivalence_mapDGHomotopyCategory

example (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ)
    (C : ConstantRingSource A N) (J : OrdinaryModuleSource A N C)
    (F G : ModuleComplexes A) (n : ℤ) :
    letI := moduleDG A
    IsIso (HomologicalComplex.homologyMap (J.functor.map F G) n) := by
  let _ := moduleDG A
  exact (ordinary_constant_module_quasi_equivalence A N C J).isQuasiFullyFaithful.isIso_homologyMap
    F G n

end MathlibExtTest.AlgebraicGeometry.OrdinaryConstantCoefficient
