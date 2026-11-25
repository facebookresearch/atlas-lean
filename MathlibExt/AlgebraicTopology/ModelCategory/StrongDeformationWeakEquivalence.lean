/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
public import MathlibExt.AlgebraicTopology.ModelCategory.StrongDeformationData

/-!
# Weak equivalences from strong deformation data

A strong deformation retract is a weak equivalence as soon as the selected
precylinder projection on its target is a weak equivalence.  The proof uses the
actual localization at the model weak equivalences: the strict retract gives
one inverse equation and the supplied homotopy gives the other.

No cofibrancy, fibrancy, good-cylinder, enrichment, properness or anodyne-system
premise is needed.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe v u

open CategoryTheory CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.Precylinder.StrongDeformationData

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {P : Precylinder (𝟭 C)} {K L : C} {i : K ⟶ L}

/-- Strong deformation data exhibit the specified map as a weak equivalence
when the chosen target-cylinder projection is weak. -/
theorem weakEquivalence_of_projection
    (D : P.StrongDeformationData i)
    (hπ : weakEquivalences C (P.app L).π) :
    weakEquivalences C i := by
  let _ : WeakEquivalence (P.app L).π := (weakEquivalence_iff _).2 hπ
  let Q : Cylinder L :=
    { __ := P.app L
      weakEquivalence_π := inferInstance }
  have hrel : LeftHomotopyRel (𝟙 L : L ⟶ L) (D.retraction ≫ i) :=
    ⟨Q, ⟨D.homotopy.toLeftHomotopy⟩⟩
  let F := ((weakEquivalences C).Q)
  have hright : F.map (D.retraction ≫ i) = F.map (𝟙 L : L ⟶ L) :=
    ((LeftHomotopyRel.factorsThroughLocalization C hrel).map_eq F).symm
  apply (weakEquivalence_iff_isIso_map_of_isLocalization ((weakEquivalences C).Q) i).2
  exact ⟨⟨F.map D.retraction,
    by rw [← F.map_comp, D.retract, F.map_id],
    by rw [← F.map_comp, hright, F.map_id]⟩⟩

end HomotopicalAlgebra.Precylinder.StrongDeformationData
