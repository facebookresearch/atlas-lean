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
# Homology maps to a complex concentrated in degree zero

Let C have zero morphisms and a zero object. The degree-zero homology of the chain complex
concentrated at X in degree zero is canonically isomorphic to X, and its class map composed
with this isomorphism is the identity.

If a chain complex K has homology in degree zero, any chain map f : K → single₀(X) satisfies
c_K ≫ H₀(f) ≫ e_X = f₀, where c_K is the degree-zero class map and e_X is the homology
isomorphism for the concentrated complex.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- In a category C with zero morphisms and a zero object, let S_X be the chain complex of shape
down ℕ concentrated at X in degree zero. Its class map c_X : X ⟶ H₀(S_X), followed by the
canonical isomorphism singleObjHomologySelfIso : H₀(S_X) ≅ X, equals 𝟙 X. -/
@[reassoc]
theorem homologyZeroClass_single_comp (X : C) :
    homologyZeroClass ((single₀ C).obj X) ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 X).hom = 𝟙 X := by
  rw [homologyZeroClass, ← HomologicalComplex.homologyι_singleObjOpcyclesSelfIso_inv]
  rw [Category.assoc, ← Category.assoc ((single₀ C).obj X).isoHomologyι₀.inv,
    HomologicalComplex.isoHomologyι_inv_hom_id, Category.id_comp,
    HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv, single₀ObjXSelf]
  rfl

/-- In a category C with zero morphisms and a zero object, let K be a chain complex indexed by ℕ
with homology in degree zero, and let f : K ⟶ single₀(X) be a chain map. Then
homologyZeroClass K ≫ H₀(f) ≫ singleObjHomologySelfIso.hom = f.f 0 as morphisms K.X 0 ⟶ X. -/
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
