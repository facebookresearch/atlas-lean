/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.HomComplex.Map
public import Mathlib.Algebra.Homology.Additive

/-!
# Linear product Hom-complex bifunctors

For an R-linear preadditive category, the cochain family and linear
differential form a complex in ModuleCat R. Source and target complex maps
act by precomposition and postcomposition.
Scalar, object and morphism universes are independent; boundedness,
resolutions, finiteness and completeness are not required.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CochainComplex.HomComplex

universe uC vC uR

variable (R : Type uR) [Ring R]
  {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
  {K K' K'' L L' L'' : CochainComplex C ℤ}

/-- The native product cochains and the same native R-linear differential. -/
@[implicit_reducible]
def linearComplex (K L : CochainComplex C ℤ) : CochainComplex (ModuleCat.{vC} R) ℤ :=
  CochainComplex.linearHomComplex R K L

/-- Genuine original complex maps induce the actual R-linear Hom-complex map. -/
def linearComplexMap (f : K' ⟶ K) (g : L ⟶ L') :
    linearComplex R K L ⟶ linearComplex R K' L' where
  f n := ModuleCat.ofHom (mapLinearOver R f g n)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change δ i j (mapLinearOver R f g i z) = mapLinearOver R f g j (δ i j z)
    exact (mapLinearOver_δ R f g i j z).symm

@[simp]
theorem linearComplexMap_id (K L : CochainComplex C ℤ) :
    linearComplexMap R (𝟙 K) (𝟙 L) = 𝟙 (linearComplex R K L) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change mapLinearOver R (𝟙 K) (𝟙 L) n z = z
  exact congrArg (fun h : Cochain K L n →ₗ[R] Cochain K L n => h z)
    (mapLinearOver_id R K L n)

/-- Source composition is contravariant and target composition covariant. -/
theorem linearComplexMap_comp (f : K' ⟶ K) (f' : K'' ⟶ K')
    (g : L ⟶ L') (g' : L' ⟶ L'') :
    linearComplexMap R f g ≫ linearComplexMap R f' g' =
      linearComplexMap R (f' ≫ f) (g ≫ g') := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change mapLinearOver R f' g' n (mapLinearOver R f g n z) =
    mapLinearOver R (f' ≫ f) (g ≫ g') n z
  exact congrArg (fun h : Cochain K L n →ₗ[R] Cochain K'' L'' n => h z)
    (mapLinearOver_comp R f f' g g' n)

variable (C)

/-- The canonical curried unbounded Hom-complex bifunctor, on the original
product model with the native differential and actual pre/postcomposition. -/
@[implicit_reducible]
def linearFunctor : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤
    CochainComplex (ModuleCat.{vC} R) ℤ where
  obj K :=
    { obj := fun L => linearComplex R K.unop L
      map := fun g => linearComplexMap R (𝟙 K.unop) g
      map_id L := linearComplexMap_id R K.unop L
      map_comp g g' := by
        simpa only [Category.id_comp] using
          (linearComplexMap_comp R (𝟙 K.unop) (𝟙 K.unop) g g').symm }
  map f :=
    { app := fun L => linearComplexMap R f.unop (𝟙 L)
      naturality _ _ g := by
        rw [linearComplexMap_comp, linearComplexMap_comp]
        simp only [Category.id_comp, Category.comp_id] }
  map_id K := by
    apply NatTrans.ext
    funext L
    exact linearComplexMap_id R K.unop L
  map_comp f f' := by
    apply NatTrans.ext
    funext L
    simpa only [NatTrans.comp_app, CategoryTheory.unop_comp, Category.id_comp] using
      (linearComplexMap_comp R f.unop f'.unop (𝟙 L) (𝟙 L)).symm

instance linearFunctor_obj_additive (K : (CochainComplex C ℤ)ᵒᵖ) :
    ((linearFunctor R C).obj K).Additive where
  map_add {X Y f g} := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Cochain.ext
    intro p q hpq
    change (mapLinearOver R (𝟙 K.unop) (f + g) n z).v p q hpq =
      (mapLinearOver R (𝟙 K.unop) f n z + mapLinearOver R (𝟙 K.unop) g n z).v p q hpq
    rw [Cochain.add_v, mapLinearOver_v, mapLinearOver_v, mapLinearOver_v]
    simp only [HomologicalComplex.add_f_apply, HomologicalComplex.id_f,
      Category.id_comp, Preadditive.comp_add]

instance linearFunctor_additive : (linearFunctor R C).Additive where
  map_add {X Y f g} := by
    apply NatTrans.ext
    funext L
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Cochain.ext
    intro p q hpq
    change (mapLinearOver R (f + g).unop (𝟙 L) n z).v p q hpq =
      (mapLinearOver R f.unop (𝟙 L) n z + mapLinearOver R g.unop (𝟙 L) n z).v p q hpq
    rw [Cochain.add_v, mapLinearOver_v, mapLinearOver_v, mapLinearOver_v]
    change (f.unop.f p + g.unop.f p) ≫ z.v p q hpq ≫ 𝟙 _ =
      f.unop.f p ≫ z.v p q hpq ≫ 𝟙 _ + g.unop.f p ≫ z.v p q hpq ≫ 𝟙 _
    simp only [Category.comp_id, Preadditive.add_comp]

/-- The coefficient-forgotten complex is the same original native Hom complex.
Only scalar structure is forgotten; the cochain family and differential agree. -/
def linearComplexForgetIso (K L : CochainComplex C ℤ) :
    ((forget₂ (ModuleCat.{vC} R) AddCommGrpCat.{vC}).mapHomologicalComplex (.up ℤ)).obj
        (linearComplex R K L) ≅ HomComplex K L :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j _
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    rfl)

/-- Forgetting scalars retains the actual original two-variable Hom-complex map. -/
@[reassoc]
theorem linearComplexForgetIso_naturality {K K' L L' : CochainComplex C ℤ}
    (f : K' ⟶ K) (g : L ⟶ L') :
    ((forget₂ (ModuleCat.{vC} R) AddCommGrpCat.{vC}).mapHomologicalComplex (.up ℤ)).map
        (linearComplexMap R f g) ≫ (linearComplexForgetIso R C K' L').hom =
      (linearComplexForgetIso R C K L).hom ≫ HomComplex.map f g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  rfl

end CochainComplex.HomComplex

namespace ModuleCat

universe u v

variable (R : Type u) [CommRing R]

/-- The actual unbounded R-linear product Hom-complex bifunctor for modules,
with ring and module-carrier worlds independent. -/
abbrev homComplexFunctor : (CochainComplex (ModuleCat.{v} R) ℤ)ᵒᵖ ⥤
    CochainComplex (ModuleCat.{v} R) ℤ ⥤ CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.HomComplex.linearFunctor R (ModuleCat.{v} R)

end ModuleCat
