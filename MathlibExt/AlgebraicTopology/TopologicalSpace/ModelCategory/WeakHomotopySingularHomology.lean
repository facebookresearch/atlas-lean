/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.WeakHomotopySingularChains

/-!
# Singular-homology invariance under weak homotopy equivalences

A weak homotopy equivalence induces an isomorphism on ordinary singular
homology in every natural degree.  This is the direct homology-map
consequence of the existing singular-chain quasi-isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open AlgebraicTopology CategoryTheory HomologicalComplex Limits

universe w v u

namespace TopCat.weakHomotopyEquivalences

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C] [CategoryWithHomology C]

/-- A weak homotopy equivalence induces an isomorphism on ordinary singular
homology in every natural degree. -/
theorem isIso_singularHomologyFunctor_map
    {X Y : TopCat.{w}} {f : X ⟶ Y}
    (hf : TopCat.weakHomotopyEquivalences f) (A : C) (n : ℕ) :
    IsIso (((singularHomologyFunctor C n).obj A).map f) := by
  have hChain : QuasiIso
      (((singularChainComplexFunctor C).obj A).map f) :=
    hf.quasiIso_singularChainComplexMap A
  let _ : QuasiIso
      (((singularChainComplexFunctor C).obj A).map f) := hChain
  change IsIso (homologyMap
    (((singularChainComplexFunctor C).obj A).map f) n)
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance

end TopCat.weakHomotopyEquivalences

end
