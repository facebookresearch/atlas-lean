/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence
public import MathlibExt.Topology.Category.TopCat.ZerothHomotopy

/-!
# Zeroth homotopy and weak homotopy equivalences

A weak homotopy equivalence of topological spaces induces a bijection on
zeroth homotopy.  This neutral bridge contains no loop-space, weakly pointed,
fundamental-group, application, or selected model structure.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

universe u

namespace TopCat.weakHomotopyEquivalences

/-- A weak homotopy equivalence induces a bijection on path components. -/
theorem bijective_zerothHomotopyMap
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : TopCat.weakHomotopyEquivalences f) :
    Function.Bijective (TopCat.zerothHomotopyMap f) := by
  have hs : Function.Bijective
      (SSet.mapπ₀ (TopCat.toSSet.map f)) :=
    ((TopCat.mem_weakHomotopyEquivalences_iff f).mp hf).bijective_mapπ₀
  constructor
  · intro a b hab
    apply TopCat.zerothHomotopyEquiv.injective
    apply hs.1
    simpa only [← TopCat.zerothHomotopyEquiv_naturality] using
      congrArg TopCat.zerothHomotopyEquiv hab
  · intro b
    obtain ⟨a, ha⟩ := hs.2 (TopCat.zerothHomotopyEquiv b)
    refine ⟨TopCat.zerothHomotopyEquiv.symm a, ?_⟩
    apply TopCat.zerothHomotopyEquiv.injective
    rw [TopCat.zerothHomotopyEquiv_naturality,
      TopCat.zerothHomotopyEquiv.apply_symm_apply, ha]

end TopCat.weakHomotopyEquivalences
