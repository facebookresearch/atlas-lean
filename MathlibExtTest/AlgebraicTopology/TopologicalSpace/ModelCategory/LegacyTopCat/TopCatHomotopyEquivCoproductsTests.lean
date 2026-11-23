/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivCoproducts

@[expose] public section

/-!
# TopCat homotopy-equivalence coproduct client

Compile-time consumer checks for the coproduct closure
`TopCat.sigmaHomotopyEquiv` and `TopCat.sigma_map_mem_weakHomotopyEquivalences`
at symbolic, universe-one, and universe-zero levels. States no
arbitrary-colimit/pushout/transfinite stability,
no model structure, and no KQ4 `SSet` weak-equivalence claim.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHomotopyEquivCoproductsTests

section CoproductHomotopyEquiv

noncomputable def sigmaHomotopyEquiv_client {ι : Type 0} {X Y : ι → Type 0}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    ContinuousMap.HomotopyEquiv (Σ i, X i) (Σ i, Y i) :=
  TopCat.sigmaHomotopyEquiv e

#print axioms TopCat.sigmaHomotopyEquiv
#print axioms sigmaHomotopyEquiv_client

end CoproductHomotopyEquiv

section SigmaMap

theorem sigmaMap_client {ι : Type 0} {X Y : ι → Type 0}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    TopCat.weakHomotopyEquivalences
      (Limits.Sigma.map (fun i => TopCat.ofHom (e i).toFun)) :=
  TopCat.sigma_map_mem_weakHomotopyEquivalences e

#print axioms TopCat.sigma_map_mem_weakHomotopyEquivalences
#print axioms sigmaMap_client

end SigmaMap

section SymbolicUniverse

noncomputable def sigmaHomotopyEquiv_symbolic
    {ι : Type u} {X Y : ι → Type u}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    ContinuousMap.HomotopyEquiv (Σ i, X i) (Σ i, Y i) :=
  TopCat.sigmaHomotopyEquiv e

theorem sigmaMap_symbolic
    {ι : Type u} {X Y : ι → Type u}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    TopCat.weakHomotopyEquivalences
      (Limits.Sigma.map (fun i => TopCat.ofHom (e i).toFun)) :=
  TopCat.sigma_map_mem_weakHomotopyEquivalences e

noncomputable def sigmaHomotopyEquiv_u1
    {ι : Type 1} {X Y : ι → Type 1}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    ContinuousMap.HomotopyEquiv (Σ i, X i) (Σ i, Y i) :=
  TopCat.sigmaHomotopyEquiv e

end SymbolicUniverse

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHomotopyEquivCoproductsTests
