/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainComplex.HomologyZero
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Native degree-zero homology of a chain map to a single object

The native class map of the single complex is inverse to its native homology
self-isomorphism. Naturality therefore identifies the actual degree-zero
component of any chain map to a single complex with its induced H0 map.
The category and morphism universes are independent, and only zero morphisms,
a zero object, and the indicated H0 are needed.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The actual native class of the degree-zero single complex returns the original object. -/
@[reassoc]
theorem homologyZeroClass_single_comp (X : C) :
    homologyZeroClass ((single₀ C).obj X) ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 X).hom = 𝟙 X := by
  rw [homologyZeroClass, ← HomologicalComplex.homologyι_singleObjOpcyclesSelfIso_inv]
  rw [Category.assoc, ← Category.assoc ((single₀ C).obj X).isoHomologyι₀.inv,
    HomologicalComplex.isoHomologyι_inv_hom_id, Category.id_comp,
    HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv, single₀ObjXSelf]
  rfl

/-- An actual chain map to a single complex has precisely its native H0 class square. -/
@[reassoc]
theorem homologyZeroClass_toSingle {K : ChainComplex C ℕ} [K.HasHomology 0]
    {X : C} (f : K ⟶ (single₀ C).obj X) :
    homologyZeroClass K ≫ (HomologicalComplex.homologyMap f 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 X).hom) = f.f 0 := by
  let f₀ : K.X 0 ⟶ X := f.f 0
  rw [← Category.assoc, homologyZeroClass_naturality, Category.assoc,
    homologyZeroClass_single_comp]
  exact Category.comp_id f₀

end ChainComplex
