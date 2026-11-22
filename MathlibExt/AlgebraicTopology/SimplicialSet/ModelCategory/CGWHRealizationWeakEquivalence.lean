/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealization
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelClassComparison

/-!
# Realization weak equivalences in CGWH

Realizing a realization weak equivalence of simplicial sets in CGWH gives a
CGWH weak homotopy equivalence.  The proof uses the literal underlying
TopCat realization map and the inverse-image description of the CGWH weak
class.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v

namespace SSet

/-- Realization weak equivalences of simplicial sets become weak homotopy
equivalences after native CGWH realization. -/
theorem realizationWeakEquivalences_toCGWH
    {X Y : SSet.{v}} {f : X ⟶ Y}
    (hf : SSet.realizationWeakEquivalences f) :
    CGWH.weakHomotopyEquivalences
      (SSet.toCGWH.{u, v}.map f) := by
  rw [CGWH.weakHomotopyEquivalences_eq_inverseImage,
    CategoryTheory.MorphismProperty.inverseImage_iff]
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map f)
  change SSet.KanComplex.W
    (TopCat.toSSet.map (SSet.toTop.map f)) at hf ⊢
  exact hf

end SSet
