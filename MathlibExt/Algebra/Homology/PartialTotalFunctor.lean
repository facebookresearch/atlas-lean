/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.PartialTotalCoordinates

/-!
# The partial-total filtration functor

The first-coordinate partial totals form a functor from the ordered
category ℕ. Their inclusions into the full total form a compatible cocone.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- The increasing natural filtration of the total complex by
first-coordinate partial totals. -/
noncomputable def partialTotalFunctor : ℕ ⥤ ChainComplex C ℕ where
  obj p := B.partialTotal p
  map {p p'} f := B.partialTotalMap (leOfHom f)
  map_id p := by
    simpa only using B.partialTotalMap_refl p
  map_comp {p p' p''} f g := by
    simpa only using
      (B.partialTotalMap_comp (leOfHom f) (leOfHom g)).symm

@[simp]
theorem partialTotalFunctor_obj (p : ℕ) :
    (B.partialTotalFunctor).obj p = B.partialTotal p :=
  rfl

/-- The map of the partial-total functor associated to an inequality. -/
theorem partialTotalFunctor_map {p p' : ℕ} (h : p ≤ p') :
    B.partialTotalFunctor.map (homOfLE h) = B.partialTotalMap h :=
  rfl

/-- The successor map of the natural partial-total filtration. -/
theorem partialTotalFunctor_map_succ (p : ℕ) :
    B.partialTotalFunctor.map (homOfLE (Nat.le_succ p)) =
      B.partialTotalMap (Nat.le_succ p) :=
  rfl

variable {B}
variable {B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- A bicomplex morphism induces a natural transformation between its
partial-total filtrations. -/
noncomputable def partialTotalFunctorMap (φ : B ⟶ B') :
    B.partialTotalFunctor ⟶ B'.partialTotalFunctor where
  app p := B.partialTotalHom φ p
  naturality {p p'} f := by
    exact (B.partialTotalMap_naturality φ (leOfHom f)).symm

@[simp]
theorem partialTotalFunctorMap_app (φ : B ⟶ B') (p : ℕ) :
    (partialTotalFunctorMap φ).app p = B.partialTotalHom φ p :=
  rfl

variable (B)

/-- The natural transformation from the partial-total filtration to the
constant full total complex. -/
noncomputable def partialTotalToTotal :
    B.partialTotalFunctor ⟶
      (Functor.const ℕ).obj (B.total (ComplexShape.down ℕ)) where
  app p := B.partialTotalι p
  naturality {p p'} f := by
    change B.partialTotalMap (leOfHom f) ≫ B.partialTotalι p' =
      B.partialTotalι p ≫ 𝟙 _
    rw [B.partialTotalMap_comp_partialTotalι, Category.comp_id]

@[simp]
theorem partialTotalToTotal_app (p : ℕ) :
    B.partialTotalToTotal.app p = B.partialTotalι p :=
  rfl

/-- The cocone from the natural partial-total filtration to the full total
complex.  No colimit assertion is made. -/
noncomputable def partialTotalCocone : Cocone B.partialTotalFunctor where
  pt := B.total (ComplexShape.down ℕ)
  ι := B.partialTotalToTotal

@[simp]
theorem partialTotalCocone_pt :
    B.partialTotalCocone.pt = B.total (ComplexShape.down ℕ) :=
  rfl

@[simp]
theorem partialTotalCocone_ι_app (p : ℕ) :
    B.partialTotalCocone.ι.app p = B.partialTotalι p :=
  rfl

section BicomplexFunctor

variable [HasZeroObject C]

/-- The functor taking a first-quadrant bicomplex to its partial total at a
fixed filtration stage. This is the bicomplex-variable counterpart of
`partialTotalFunctor`, which varies the stage for one fixed bicomplex. -/
noncomputable abbrev partialTotalStageFunctor (p : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤
      ChainComplex C ℕ where
  obj B := B.partialTotal p
  map {B _} φ := B.partialTotalHom φ p
  map_id B := B.partialTotalHom_id p
  map_comp {B _ _} φ ψ := B.partialTotalHom_comp φ ψ p

@[simp]
theorem partialTotalStageFunctor_obj (p : ℕ)
    (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    (partialTotalStageFunctor (C := C) p).obj B = B.partialTotal p :=
  rfl

@[simp]
theorem partialTotalStageFunctor_map
    {B B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (p : ℕ) (φ : B ⟶ B') :
    (partialTotalStageFunctor (C := C) p).map φ =
      B.partialTotalHom φ p :=
  rfl

/-- At a fixed stage, the inclusions of partial totals into full totals form
a natural transformation in the bicomplex. -/
noncomputable abbrev partialTotalInclusionNatTrans (p : ℕ) :
    partialTotalStageFunctor (C := C) p ⟶
      HomologicalComplex₂.totalFunctor C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) where
  app B := B.partialTotalι p
  naturality _ _ φ := partialTotalHom_ι_naturality _ φ p

@[simp]
theorem partialTotalInclusionNatTrans_app (p : ℕ)
    (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    (partialTotalInclusionNatTrans (C := C) p).app B =
      B.partialTotalι p :=
  rfl

end BicomplexFunctor

end HomologicalComplex₂

end
