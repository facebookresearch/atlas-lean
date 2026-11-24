/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# External simplicial-set tensors and cotensors of simplicial spaces

For a simplicial set `K` and a simplicial space `X`, the external tensor
has bidegree carrier `K n × X n a`.  It is naturally the degreewise
copower of `X n` indexed by `K n` and represents the canonical outer
simplicial mapping object.

The matching cotensor is the explicit enriched end.  Its public projections
and extensionality theorem expose all computations without installing a
second enrichment or a monoidal-closed instance on simplicial spaces.

No model-category, Reedy, localization, or derived-mapping claim is made.
-/

@[expose] public section

noncomputable section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial MonoidalCategory

namespace SSet

/-- Embed an outer simplicial set as the simplicial space which is degreewise
the constant inner simplicial set. -/
noncomputable abbrev simplicialSpaceDiscrete :
    SSet.{u} ⥤ SimplicialObject SSet.{u} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) SSet.{u}).obj
    (SimplicialObject.const (Type u))

/-- The external tensor of an outer simplicial set with a simplicial space. -/
noncomputable abbrev simplicialSpaceTensor :
    SSet.{u} ⥤ SimplicialObject SSet.{u} ⥤ SimplicialObject SSet.{u} :=
  simplicialSpaceDiscrete ⋙
    tensoringLeft (SimplicialObject SSet.{u})

/-- Bidegree carrier of the external tensor. -/
@[simp]
theorem simplicialSpaceTensor_obj_obj
    (K : SSet.{u}) (X : SimplicialObject SSet.{u})
    (n a : SimplexCategoryᵒᵖ) :
    (((simplicialSpaceTensor.obj K).obj X).obj n).obj a =
      (K.obj n × (X.obj n).obj a) :=
  rfl

/-- A map in the simplicial-set variable acts on the first tensor factor. -/
@[simp]
theorem simplicialSpaceTensor_map_left_apply
    {K L : SSet.{u}} (f : K ⟶ L) (X : SimplicialObject SSet.{u})
    (n a : SimplexCategoryᵒᵖ) (k : K.obj n)
    (x : (X.obj n).obj a) :
    (((simplicialSpaceTensor.map f).app X).app n).app a (k, x) =
      (f.app n k, x) :=
  rfl

/-- A map in the simplicial-space variable acts on the second tensor factor. -/
@[simp]
theorem simplicialSpaceTensor_map_right_apply
    (K : SSet.{u}) {X Y : SimplicialObject SSet.{u}} (g : X ⟶ Y)
    (n a : SimplexCategoryᵒᵖ) (k : K.obj n)
    (x : (X.obj n).obj a) :
    ((((simplicialSpaceTensor.obj K).map g).app n).app a) (k, x) =
      (k, (g.app n).app a x) :=
  rfl

/-- The injection of one summand into an external tensor degree. -/
noncomputable def simplicialSpaceTensorι
    (K : SSet.{u}) (X : SimplicialObject SSet.{u})
    (n : SimplexCategoryᵒᵖ) (k : K.obj n) :
    X.obj n ⟶ ((simplicialSpaceTensor.obj K).obj X).obj n where
  app _ := ↾fun x ↦ (k, x)
  naturality _ _ _ := rfl

/-- Tensor injections commute with outer simplicial structure maps. -/
theorem simplicialSpaceTensorι_outer
    (K : SSet.{u}) (X : SimplicialObject SSet.{u})
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (k : K.obj n) :
    simplicialSpaceTensorι K X n k ≫
        ((simplicialSpaceTensor.obj K).obj X).map α =
      X.map α ≫
        simplicialSpaceTensorι K X m (K.map α k) := by
  ext a x
  rfl

/-- In every outer degree, the product presentation of the tensor is the
copower of that degree of `X` indexed by the simplices of `K`. -/
@[no_expose]
noncomputable def simplicialSpaceTensorCopowerIso
    (K : SSet.{u}) (X : SimplicialObject SSet.{u})
    (n : SimplexCategoryᵒᵖ) :
    ((simplicialSpaceTensor.obj K).obj X).obj n ≅
      (∐ fun _ : K.obj n ↦ X.obj n) := by
  let componentIso (a : SimplexCategoryᵒᵖ) :
      (((simplicialSpaceTensor.obj K).obj X).obj n).obj a ≅
        ((∐ fun _ : K.obj n ↦ X.obj n).obj a) :=
    ((Equiv.sigmaEquivProd
        (K.obj n) ((X.obj n).obj a)).symm.toIso.trans
      (Limits.Types.coproductIso
        (fun _ : K.obj n ↦ (X.obj n).obj a)).symm).trans
      (Limits.sigmaObjIso (fun _ : K.obj n ↦ X.obj n) a).symm
  have componentIso_hom_apply (a : SimplexCategoryᵒᵖ)
      (k : K.obj n) (x : (X.obj n).obj a) :
      (componentIso a).hom (k, x) =
        (Limits.Sigma.ι (fun _ : K.obj n ↦ X.obj n) k).app a x := by
    change ((Limits.sigmaObjIso
        (fun _ : K.obj n ↦ X.obj n) a).inv)
      ((Limits.Types.coproductIso
        (fun _ : K.obj n ↦ (X.obj n).obj a)).inv ⟨k, x⟩) = _
    rw [Limits.Types.coproductIso_mk_comp_inv_apply]
    exact ConcreteCategory.congr_hom
      (Limits.ι_comp_sigmaObjIso_inv
        (fun _ : K.obj n ↦ X.obj n) a k) x
  exact NatIso.ofComponents componentIso (by
    intro a b q
    apply ConcreteCategory.hom_ext
    rintro ⟨k, x⟩
    change (componentIso b).hom (k, (X.obj n).map q x) =
      ((∐ fun _ : K.obj n ↦ X.obj n).map q)
        ((componentIso a).hom (k, x))
    rw [componentIso_hom_apply, componentIso_hom_apply]
    exact ConcreteCategory.congr_hom
      ((Limits.Sigma.ι (fun _ : K.obj n ↦ X.obj n) k).naturality q) x)

/-- Under the copower comparison, a tensor injection is the categorical
coproduct injection. -/
theorem simplicialSpaceTensorι_comp_copowerIso_hom
    (K : SSet.{u}) (X : SimplicialObject SSet.{u})
    (n : SimplexCategoryᵒᵖ) (k : K.obj n) :
    simplicialSpaceTensorι K X n k ≫
        (simplicialSpaceTensorCopowerIso K X n).hom =
      Limits.Sigma.ι (fun _ : K.obj n ↦ X.obj n) k := by
  apply SSet.hom_ext
  intro a
  apply ConcreteCategory.hom_ext
  intro x
  change ((Limits.sigmaObjIso
      (fun _ : K.obj n ↦ X.obj n) a).inv)
    ((Limits.Types.coproductIso
      (fun _ : K.obj n ↦ (X.obj n).obj a)).inv ⟨k, x⟩) = _
  rw [Limits.Types.coproductIso_mk_comp_inv_apply]
  exact ConcreteCategory.congr_hom
    (Limits.ι_comp_sigmaObjIso_inv
      (fun _ : K.obj n ↦ X.obj n) a k) x

/-- The copower comparison intertwines every outer structure map with the
corresponding `Sigma.map'`. -/
theorem simplicialSpaceTensorCopowerIso_outer
    (K : SSet.{u}) (X : SimplicialObject SSet.{u})
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    ((simplicialSpaceTensor.obj K).obj X).map α ≫
        (simplicialSpaceTensorCopowerIso K X m).hom =
      (simplicialSpaceTensorCopowerIso K X n).hom ≫
        Limits.Sigma.map' (K.map α) (fun _ ↦ X.map α) := by
  apply SSet.hom_ext
  intro a
  apply ConcreteCategory.hom_ext
  rintro ⟨k, x⟩
  have h :
      (simplicialSpaceTensorι K X n k ≫
          ((simplicialSpaceTensor.obj K).obj X).map α) ≫
          (simplicialSpaceTensorCopowerIso K X m).hom =
        (simplicialSpaceTensorι K X n k ≫
          (simplicialSpaceTensorCopowerIso K X n).hom) ≫
          Limits.Sigma.map' (K.map α) (fun _ ↦ X.map α) := by
    calc
      _ = (X.map α ≫
            simplicialSpaceTensorι K X m (K.map α k)) ≫
            (simplicialSpaceTensorCopowerIso K X m).hom := by
              rw [simplicialSpaceTensorι_outer]
      _ = X.map α ≫
            (simplicialSpaceTensorι K X m (K.map α k) ≫
              (simplicialSpaceTensorCopowerIso K X m).hom) :=
            Category.assoc _ _ _
      _ = X.map α ≫
            Limits.Sigma.ι (fun _ : K.obj m ↦ X.obj m)
              (K.map α k) := by
              rw [simplicialSpaceTensorι_comp_copowerIso_hom]
      _ = Limits.Sigma.ι (fun _ : K.obj n ↦ X.obj n) k ≫
            Limits.Sigma.map' (K.map α) (fun _ ↦ X.map α) :=
          (Limits.Sigma.ι_comp_map'
            (f := fun _ : K.obj m ↦ X.obj m)
            (g := fun _ : K.obj n ↦ X.obj n)
            (p := K.map α) (q := fun _ ↦ X.map α) k).symm
      _ = (simplicialSpaceTensorι K X n k ≫
            (simplicialSpaceTensorCopowerIso K X n).hom) ≫
            Limits.Sigma.map' (K.map α) (fun _ ↦ X.map α) := by
              rw [simplicialSpaceTensorι_comp_copowerIso_hom]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h a) x

private noncomputable def simplicialSpaceTensorHomObjEquiv
    (K : SSet.{u}) (X Y : SimplicialObject SSet.{u}) :
    ((simplicialSpaceTensor.obj K).obj X ⟶ Y) ≃
      CategoryTheory.Functor.HomObj X Y K where
  toFun h :=
    { app := fun n k ↦
        { app := fun a ↦ ↾fun x ↦ (h.app n).app a (k, x)
          naturality := by
            intro a b q
            ext x
            have hn := ConcreteCategory.congr_hom ((h.app n).naturality q)
              (show (((simplicialSpaceTensor.obj K).obj X).obj n).obj a
                from (k, x))
            exact hn }
      naturality := by
        intro n m α k
        apply SSet.hom_ext
        intro a
        apply ConcreteCategory.hom_ext
        intro x
        have hn := ConcreteCategory.congr_hom
          (NatTrans.congr_app (h.naturality α) a)
            (show (((simplicialSpaceTensor.obj K).obj X).obj n).obj a
              from (k, x))
        change (h.app m).app a
            (K.map α k, (X.map α).app a x) =
          (Y.map α).app a ((h.app n).app a (k, x)) at hn
        exact hn }
  invFun q :=
    { app := fun n ↦
        { app := fun a ↦ ↾fun z ↦ (q.app n z.1).app a z.2
          naturality := by
            intro a b r
            ext z
            exact ConcreteCategory.congr_hom ((q.app n z.1).naturality r) z.2 }
      naturality := by
        intro n m α
        apply SSet.hom_ext
        intro a
        apply ConcreteCategory.hom_ext
        rintro ⟨k, x⟩
        exact ConcreteCategory.congr_hom
          (NatTrans.congr_app (q.naturality α k) a) x }
  left_inv h := by
    apply NatTrans.ext
    funext n
    apply SSet.hom_ext
    intro a
    apply ConcreteCategory.hom_ext
    rintro ⟨k, x⟩
    rfl
  right_inv q := by
    apply CategoryTheory.Functor.HomObj.ext
    funext n k
    apply SSet.hom_ext
    intro a
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- Maps out of the external tensor represent the canonical outer simplicial
mapping object. -/
@[no_expose]
noncomputable def simplicialSpaceTensorHomEquiv
    (K : SSet.{u}) (X Y : SimplicialObject SSet.{u}) :
    ((simplicialSpaceTensor.obj K).obj X ⟶ Y) ≃
      (K ⟶ CategoryTheory.SimplicialCategory.sHom X Y) :=
  (simplicialSpaceTensorHomObjEquiv K X Y).trans
    (CategoryTheory.Functor.functorHomEquiv X Y K).symm

/-- Naturality of tensor--Hom in the outer simplicial-set variable. -/
theorem simplicialSpaceTensorHomEquiv_naturality_K
    {K L : SSet.{u}} (f : L ⟶ K)
    (X Y : SimplicialObject SSet.{u})
    (h : (simplicialSpaceTensor.obj K).obj X ⟶ Y) :
    CategoryTheory.Functor.functorHomEquiv X Y L
        (simplicialSpaceTensorHomEquiv L X Y
          (((simplicialSpaceTensor.map f).app X) ≫ h)) =
      CategoryTheory.Functor.HomObj.map f
        (CategoryTheory.Functor.functorHomEquiv X Y K
          (simplicialSpaceTensorHomEquiv K X Y h)) := by
  simp only [simplicialSpaceTensorHomEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  apply CategoryTheory.Functor.HomObj.ext
  funext n k
  apply SSet.hom_ext
  intro a
  apply ConcreteCategory.hom_ext
  intro x
  change (h.app n).app a (f.app n k, x) =
    (h.app n).app a (f.app n k, x)
  rfl

/-- Naturality of tensor--Hom in its contravariant simplicial-space
variable. -/
theorem simplicialSpaceTensorHomEquiv_naturality_X
    (K : SSet.{u}) {X X' Y : SimplicialObject SSet.{u}}
    (g : X' ⟶ X) (h : (simplicialSpaceTensor.obj K).obj X ⟶ Y) :
    CategoryTheory.Functor.functorHomEquiv X' Y K
        (simplicialSpaceTensorHomEquiv K X' Y
          (((simplicialSpaceTensor.obj K).map g) ≫ h)) =
      (CategoryTheory.Functor.HomObj.ofNatTrans g :
          CategoryTheory.Functor.HomObj X' X K).comp
        (CategoryTheory.Functor.functorHomEquiv X Y K
          (simplicialSpaceTensorHomEquiv K X Y h)) := by
  simp only [simplicialSpaceTensorHomEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  apply CategoryTheory.Functor.HomObj.ext
  funext n k
  apply SSet.hom_ext
  intro a
  apply ConcreteCategory.hom_ext
  intro x
  change (h.app n).app a (k, (g.app n).app a x) =
    (h.app n).app a (k, (g.app n).app a x)
  rfl

/-- Naturality of tensor--Hom in its covariant simplicial-space variable. -/
theorem simplicialSpaceTensorHomEquiv_naturality_Y
    (K : SSet.{u}) {X Y Y' : SimplicialObject SSet.{u}}
    (h : (simplicialSpaceTensor.obj K).obj X ⟶ Y) (q : Y ⟶ Y') :
    CategoryTheory.Functor.functorHomEquiv X Y' K
        (simplicialSpaceTensorHomEquiv K X Y' (h ≫ q)) =
      (CategoryTheory.Functor.functorHomEquiv X Y K
          (simplicialSpaceTensorHomEquiv K X Y h)).comp
        (CategoryTheory.Functor.HomObj.ofNatTrans q :
          CategoryTheory.Functor.HomObj Y Y' K) := by
  simp only [simplicialSpaceTensorHomEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  apply CategoryTheory.Functor.HomObj.ext
  funext n k
  apply SSet.hom_ext
  intro a
  apply ConcreteCategory.hom_ext
  intro x
  change (q.app n).app a ((h.app n).app a (k, x)) =
    (q.app n).app a ((h.app n).app a (k, x))
  rfl

end SSet

end

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial MonoidalCategory

namespace SSet

private noncomputable abbrev simplicialSpaceEnrichedOrdinaryCategory :
    let _ : EnrichedCategory SSet.{u} SSet.{u} :=
      MonoidalClosed.enrichedCategorySelf SSet.{u}
    let _ : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
      MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
    PLift (∀ (F G : SimplicialObject SSet.{u}),
        Enriched.FunctorCategory.HasFunctorEnrichedHom SSet.{u} F G) ×
      PLift (∀ (F G : SimplicialObject SSet.{u}),
        Enriched.FunctorCategory.HasEnrichedHom SSet.{u} F G) := by
  letI : EnrichedCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedCategorySelf SSet.{u}
  letI : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
  let hFunctor : ∀ (F G : SimplicialObject SSet.{u}),
      Enriched.FunctorCategory.HasFunctorEnrichedHom SSet.{u} F G :=
    inferInstance
  let hOuter : ∀ (F G : SimplicialObject SSet.{u}),
      Enriched.FunctorCategory.HasEnrichedHom SSet.{u} F G :=
    inferInstance
  exact ⟨⟨hFunctor⟩, ⟨hOuter⟩⟩

end SSet

end

@[expose] public section

noncomputable section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial MonoidalCategory

namespace SSet

/-- The explicit enriched-end cotensor of a simplicial space by an outer
simplicial set. -/
@[no_expose]
noncomputable def simplicialSpaceCotensor :
    SSet.{u}ᵒᵖ ⥤ SimplicialObject SSet.{u} ⥤ SimplicialObject SSet.{u} :=
  by
    letI : EnrichedCategory SSet.{u} SSet.{u} :=
      MonoidalClosed.enrichedCategorySelf SSet.{u}
    letI : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
      MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
    let data := simplicialSpaceEnrichedOrdinaryCategory
    let _ : ∀ (F G : SimplicialObject SSet.{u}),
        Enriched.FunctorCategory.HasFunctorEnrichedHom SSet.{u} F G :=
      data.1.down
    let _ : ∀ (F G : SimplicialObject SSet.{u}),
        Enriched.FunctorCategory.HasEnrichedHom SSet.{u} F G :=
      data.2.down
    let _ : EnrichedOrdinaryCategory (SimplicialObject SSet.{u})
        (SimplicialObject SSet.{u}) :=
      Enriched.FunctorCategory.functorEnrichedOrdinaryCategory
        SSet.{u} SSet.{u} SimplexCategoryᵒᵖ
    exact simplicialSpaceDiscrete.op ⋙
      eHomFunctor (SimplicialObject SSet.{u})
        (SimplicialObject SSet.{u})

/-- Projection from one outer degree of the explicit cotensor end. Its
inferred type contains only public Mathlib declarations. -/
@[no_expose]
noncomputable def simplicialSpaceCotensorπ
    (K : SSet.{u}) (Y : SimplicialObject SSet.{u})
    (n : SimplexCategoryᵒᵖ) (a : Under n) :
    ((simplicialSpaceCotensor.obj (op K)).obj Y).obj n ⟶
      (ihom ((simplicialSpaceDiscrete.obj K).obj a.right)).obj
        (Y.obj a.right) :=
  by
    letI : EnrichedCategory SSet.{u} SSet.{u} :=
      MonoidalClosed.enrichedCategorySelf SSet.{u}
    letI : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
      MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
    let data := simplicialSpaceEnrichedOrdinaryCategory
    letI : ∀ (F G : SimplicialObject SSet.{u}),
        Enriched.FunctorCategory.HasFunctorEnrichedHom SSet.{u} F G :=
      data.1.down
    letI : ∀ (F G : SimplicialObject SSet.{u}),
        Enriched.FunctorCategory.HasEnrichedHom SSet.{u} F G :=
      data.2.down
    letI : Enriched.FunctorCategory.HasEnrichedHom SSet.{u}
        (Under.forget n ⋙ simplicialSpaceDiscrete.obj K)
        (Under.forget n ⋙ Y) := data.1.down _ _ n
    letI : EnrichedOrdinaryCategory (SimplicialObject SSet.{u})
        (SimplicialObject SSet.{u}) :=
      Enriched.FunctorCategory.functorEnrichedOrdinaryCategory
        SSet.{u} SSet.{u} SimplexCategoryᵒᵖ
    exact Enriched.FunctorCategory.enrichedHomπ SSet.{u}
      (Under.forget n ⋙ simplicialSpaceDiscrete.obj K)
      (Under.forget n ⋙ Y) a

set_option backward.isDefEq.respectTransparency false in
/-- Cotensor projections commute with outer simplicial structure maps. -/
theorem simplicialSpaceCotensorπ_outer
    (K : SSet.{u}) (Y : SimplicialObject SSet.{u})
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (a : Under m) :
    ((simplicialSpaceCotensor.obj (op K)).obj Y).map α ≫
        simplicialSpaceCotensorπ K Y m a =
      simplicialSpaceCotensorπ K Y n ((Under.map α).obj a) :=
  by
    let _ : EnrichedCategory SSet.{u} SSet.{u} :=
      MonoidalClosed.enrichedCategorySelf SSet.{u}
    let _ : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
      MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
    let data := simplicialSpaceEnrichedOrdinaryCategory
    let _ : ∀ (F G : SimplicialObject SSet.{u}),
        Enriched.FunctorCategory.HasFunctorEnrichedHom SSet.{u} F G :=
      data.1.down
    let _ : ∀ (F G : SimplicialObject SSet.{u}),
        Enriched.FunctorCategory.HasEnrichedHom SSet.{u} F G :=
      data.2.down
    let _ : EnrichedOrdinaryCategory (SimplicialObject SSet.{u})
        (SimplicialObject SSet.{u}) :=
      Enriched.FunctorCategory.functorEnrichedOrdinaryCategory
        SSet.{u} SSet.{u} SimplexCategoryᵒᵖ
    change (Enriched.FunctorCategory.functorEnrichedHom SSet.{u}
        (simplicialSpaceDiscrete.obj K) Y).map α ≫
          Enriched.FunctorCategory.enrichedHomπ SSet.{u}
            (Under.forget m ⋙ simplicialSpaceDiscrete.obj K)
            (Under.forget m ⋙ Y) a =
      Enriched.FunctorCategory.enrichedHomπ SSet.{u}
        (Under.forget n ⋙ simplicialSpaceDiscrete.obj K)
        (Under.forget n ⋙ Y) ((Under.map α).obj a)
    simp [Enriched.FunctorCategory.functorEnrichedHom,
      Enriched.FunctorCategory.precompEnrichedHom']

/-- Cotensor projections turn contravariance in `K` into internal-Hom
precomposition. -/
theorem simplicialSpaceCotensorπ_map_K
    {K L : SSet.{u}} (f : K ⟶ L) (Y : SimplicialObject SSet.{u})
    (n : SimplexCategoryᵒᵖ) (a : Under n) :
    (((simplicialSpaceCotensor.map f.op).app Y).app n) ≫
        simplicialSpaceCotensorπ K Y n a =
      simplicialSpaceCotensorπ L Y n a ≫
        (pre ((simplicialSpaceDiscrete.map f).app a.right)).app
          (Y.obj a.right) :=
  by
    let _ : EnrichedCategory SSet.{u} SSet.{u} :=
      MonoidalClosed.enrichedCategorySelf SSet.{u}
    let _ : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
      MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
    let data := simplicialSpaceEnrichedOrdinaryCategory
    let _ : ∀ (F G : SimplicialObject SSet.{u}),
        Enriched.FunctorCategory.HasFunctorEnrichedHom SSet.{u} F G :=
      data.1.down
    let _ : ∀ (F G : SimplicialObject SSet.{u}),
        Enriched.FunctorCategory.HasEnrichedHom SSet.{u} F G :=
      data.2.down
    let _ : Enriched.FunctorCategory.HasEnrichedHom SSet.{u}
        (Under.forget n ⋙ simplicialSpaceDiscrete.obj K)
        (Under.forget n ⋙ simplicialSpaceDiscrete.obj L) :=
      data.1.down _ _ n
    let _ : Enriched.FunctorCategory.HasEnrichedHom SSet.{u}
        (Under.forget n ⋙ simplicialSpaceDiscrete.obj L)
        (Under.forget n ⋙ Y) := data.1.down _ _ n
    let _ : Enriched.FunctorCategory.HasEnrichedHom SSet.{u}
        (Under.forget n ⋙ simplicialSpaceDiscrete.obj K)
        (Under.forget n ⋙ Y) := data.1.down _ _ n
    let _ : EnrichedOrdinaryCategory (SimplicialObject SSet.{u})
        (SimplicialObject SSet.{u}) :=
      Enriched.FunctorCategory.functorEnrichedOrdinaryCategory
        SSet.{u} SSet.{u} SimplexCategoryᵒᵖ
    change (eHomWhiskerRight (SimplicialObject SSet.{u})
        (Functor.whiskerRight f (SimplicialObject.const (Type u))) Y).app n ≫
          simplicialSpaceCotensorπ K Y n a = _
    dsimp only [eHomWhiskerRight]
    simp only [NatTrans.comp_app]
    let comp := @Enriched.FunctorCategory.enrichedComp
      SSet.{u} _ _ SSet.{u} _ (Under n) _
      (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
      (Under.forget n ⋙ simplicialSpaceDiscrete.obj K)
      (Under.forget n ⋙ simplicialSpaceDiscrete.obj L)
      (Under.forget n ⋙ Y)
      (data.1.down _ _ n) (data.1.down _ _ n)
      (data.1.down _ _ n)
    have hcomp :
        (eComp (SimplicialObject SSet.{u})
          (K ⋙ SimplicialObject.const (Type u))
          (L ⋙ SimplicialObject.const (Type u)) Y).app n =
        comp := rfl
    rw [hcomp]
    erw [Category.assoc]
    have hπraw := @Enriched.FunctorCategory.enrichedComp_π
      SSet.{u} _ _ SSet.{u} _ (Under n) _
      (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
      (Under.forget n ⋙ simplicialSpaceDiscrete.obj K)
      (Under.forget n ⋙ simplicialSpaceDiscrete.obj L)
      (Under.forget n ⋙ Y)
      (data.1.down _ _ n) (data.1.down _ _ n)
      (data.1.down _ _ n) a
    let πKY := @Enriched.FunctorCategory.enrichedHomπ
      SSet.{u} _ _ SSet.{u} _ (Under n) _
      (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
      (Under.forget n ⋙ simplicialSpaceDiscrete.obj K)
      (Under.forget n ⋙ Y) (data.1.down _ _ n) a
    let πLY := @Enriched.FunctorCategory.enrichedHomπ
      SSet.{u} _ _ SSet.{u} _ (Under n) _
      (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
      (Under.forget n ⋙ simplicialSpaceDiscrete.obj L)
      (Under.forget n ⋙ Y) (data.1.down _ _ n) a
    let πKL := @Enriched.FunctorCategory.enrichedHomπ
      SSet.{u} _ _ SSet.{u} _ (Under n) _
      (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
      (Under.forget n ⋙ simplicialSpaceDiscrete.obj K)
      (Under.forget n ⋙ simplicialSpaceDiscrete.obj L)
      (data.1.down _ _ n) a
    let HLY := @Enriched.FunctorCategory.enrichedHom
      SSet.{u} _ _ SSet.{u} _ (Under n) _
      (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
      (Under.forget n ⋙ simplicialSpaceDiscrete.obj L)
      (Under.forget n ⋙ Y) (data.1.down _ _ n)
    have hπKY : simplicialSpaceCotensorπ K Y n a = πKY := rfl
    have hπLY : simplicialSpaceCotensorπ L Y n a = πLY := rfl
    rw [hπKY, hπLY]
    erw [Category.assoc]
    dsimp only [comp]
    erw [hπraw]
    have hequiv :
        ((eHomEquiv (SimplicialObject SSet.{u}))
          (Functor.whiskerRight f
            (SimplicialObject.const (Type u)))).app n =
        ((Enriched.FunctorCategory.functorHomEquiv SSet.{u})
          (Functor.whiskerRight f
            (SimplicialObject.const (Type u)))).app n := rfl
    have hunitor :
        ((λ_ ((L ⋙ SimplicialObject.const (Type u)) ⟶[
          SimplicialObject SSet.{u}] Y)).inv).app n =
        (λ_ HLY).inv := rfl
    have hwhisk :
        (((eHomEquiv (SimplicialObject SSet.{u}))
            (Functor.whiskerRight f
              (SimplicialObject.const (Type u)))) ▷
          ((L ⋙ SimplicialObject.const (Type u)) ⟶[
            SimplicialObject SSet.{u}] Y)).app n =
        ((eHomEquiv (SimplicialObject SSet.{u}))
            (Functor.whiskerRight f
              (SimplicialObject.const (Type u)))).app n ▷
          HLY := rfl
    rw [hunitor, hwhisk, hequiv]
    have hmapπ :
        ((Enriched.FunctorCategory.functorHomEquiv SSet.{u})
            (Functor.whiskerRight f
              (SimplicialObject.const (Type u)))).app n ≫ πKL =
          (eHomEquiv SSet.{u})
            ((Functor.whiskerRight f
              (SimplicialObject.const (Type u))).app a.right) := by
      rw [Enriched.FunctorCategory.functorHomEquiv_apply_app]
      unfold Enriched.FunctorCategory.precompEnrichedHom
      unfold Enriched.FunctorCategory.precompEnrichedHom'
      dsimp only [πKL]
      erw [Category.assoc, end_.lift_π]
      dsimp [Enriched.FunctorCategory.diagram]
      erw [eHomWhiskerRight_id, eHomWhiskerLeft_id]
      exact @Enriched.FunctorCategory.homEquiv_apply_π
        SSet.{u} _ _ SSet.{u} _ SimplexCategoryᵒᵖ _
        (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
        (simplicialSpaceDiscrete.obj K)
        (simplicialSpaceDiscrete.obj L) (data.2.down _ _)
        (Functor.whiskerRight f (SimplicialObject.const (Type u))) a.right
    have hcombine :
        (((Enriched.FunctorCategory.functorHomEquiv SSet.{u})
            (Functor.whiskerRight f
              (SimplicialObject.const (Type u)))).app n ▷ HLY) ≫
          (πKL ⊗ₘ πLY) =
        ((((Enriched.FunctorCategory.functorHomEquiv SSet.{u})
            (Functor.whiskerRight f
              (SimplicialObject.const (Type u)))).app n ≫ πKL) ⊗ₘ πLY) :=
      MonoidalCategory.whiskerRight_comp_tensorHom _ _ _
    let cbase := eComp SSet.{u}
      ((simplicialSpaceDiscrete.obj K).obj a.right)
      ((simplicialSpaceDiscrete.obj L).obj a.right) (Y.obj a.right)
    have hcombine_assoc :
        (((Enriched.FunctorCategory.functorHomEquiv SSet.{u})
            (Functor.whiskerRight f
              (SimplicialObject.const (Type u)))).app n ▷ HLY) ≫
          ((πKL ⊗ₘ πLY) ≫ cbase) =
        (((((Enriched.FunctorCategory.functorHomEquiv SSet.{u})
            (Functor.whiskerRight f
              (SimplicialObject.const (Type u)))).app n ≫ πKL) ⊗ₘ
          πLY) ≫ cbase) := by
      exact (Category.assoc _ _ _).symm.trans (hcombine =≫ cbase)
    dsimp only [πKL, πLY, cbase,
      Enriched.FunctorCategory.enrichedHomπ] at hcombine_assoc
    slice_lhs 2 3 => erw [hcombine_assoc]
    rw [hmapπ]
    let fbase := (eHomEquiv SSet.{u})
        ((Functor.whiskerRight f
          (SimplicialObject.const (Type u))).app a.right)
    have hunit :
        (λ_ HLY).inv ≫ (fbase ⊗ₘ πLY) =
          πLY ≫ (λ_ _).inv ≫ fbase ▷ _ :=
      MonoidalCategory.leftUnitor_inv_comp_tensorHom fbase πLY
    calc
      _ = ((λ_ HLY).inv ≫ (fbase ⊗ₘ πLY)) ≫ cbase :=
        (Category.assoc _ _ _).symm
      _ = (πLY ≫ (λ_ _).inv ≫ fbase ▷ _) ≫ cbase :=
        hunit =≫ cbase
      _ = _ := by
        rw [← MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight]
        rfl

/-- Cotensor projections turn covariance in `Y` into internal-Hom mapping. -/
theorem simplicialSpaceCotensorπ_map_Y
    (K : SSet.{u}) {Y Y' : SimplicialObject SSet.{u}} (g : Y ⟶ Y')
    (n : SimplexCategoryᵒᵖ) (a : Under n) :
    (((simplicialSpaceCotensor.obj (op K)).map g).app n) ≫
        simplicialSpaceCotensorπ K Y' n a =
      simplicialSpaceCotensorπ K Y n a ≫
        (ihom ((simplicialSpaceDiscrete.obj K).obj a.right)).map
          (g.app a.right) :=
  by
    let _ : EnrichedCategory SSet.{u} SSet.{u} :=
      MonoidalClosed.enrichedCategorySelf SSet.{u}
    let _ : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
      MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
    let data := simplicialSpaceEnrichedOrdinaryCategory
    let _ : ∀ (F G : SimplicialObject SSet.{u}),
        Enriched.FunctorCategory.HasFunctorEnrichedHom SSet.{u} F G :=
      data.1.down
    let _ : ∀ (F G : SimplicialObject SSet.{u}),
        Enriched.FunctorCategory.HasEnrichedHom SSet.{u} F G :=
      data.2.down
    let _ : Enriched.FunctorCategory.HasEnrichedHom SSet.{u}
        (Under.forget n ⋙ simplicialSpaceDiscrete.obj K)
        (Under.forget n ⋙ Y) := data.1.down _ _ n
    let _ : Enriched.FunctorCategory.HasEnrichedHom SSet.{u}
        (Under.forget n ⋙ Y) (Under.forget n ⋙ Y') :=
      data.1.down _ _ n
    let _ : Enriched.FunctorCategory.HasEnrichedHom SSet.{u}
        (Under.forget n ⋙ simplicialSpaceDiscrete.obj K)
        (Under.forget n ⋙ Y') := data.1.down _ _ n
    let _ : EnrichedOrdinaryCategory (SimplicialObject SSet.{u})
        (SimplicialObject SSet.{u}) :=
      Enriched.FunctorCategory.functorEnrichedOrdinaryCategory
        SSet.{u} SSet.{u} SimplexCategoryᵒᵖ
    change (eHomWhiskerLeft (SimplicialObject SSet.{u})
        (simplicialSpaceDiscrete.obj K) g).app n ≫
          simplicialSpaceCotensorπ K Y' n a = _
    dsimp only [eHomWhiskerLeft]
    simp only [NatTrans.comp_app]
    let comp := @Enriched.FunctorCategory.enrichedComp
      SSet.{u} _ _ SSet.{u} _ (Under n) _
      (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
      (Under.forget n ⋙ simplicialSpaceDiscrete.obj K)
      (Under.forget n ⋙ Y) (Under.forget n ⋙ Y')
      (data.1.down _ _ n) (data.1.down _ _ n)
      (data.1.down _ _ n)
    have hcomp :
        (eComp (SimplicialObject SSet.{u})
          (simplicialSpaceDiscrete.obj K) Y Y').app n =
        comp := rfl
    rw [hcomp]
    erw [Category.assoc]
    have hπraw := @Enriched.FunctorCategory.enrichedComp_π
      SSet.{u} _ _ SSet.{u} _ (Under n) _
      (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
      (Under.forget n ⋙ simplicialSpaceDiscrete.obj K)
      (Under.forget n ⋙ Y) (Under.forget n ⋙ Y')
      (data.1.down _ _ n) (data.1.down _ _ n)
      (data.1.down _ _ n) a
    let πKY' := @Enriched.FunctorCategory.enrichedHomπ
      SSet.{u} _ _ SSet.{u} _ (Under n) _
      (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
      (Under.forget n ⋙ simplicialSpaceDiscrete.obj K)
      (Under.forget n ⋙ Y') (data.1.down _ _ n) a
    let πKY := @Enriched.FunctorCategory.enrichedHomπ
      SSet.{u} _ _ SSet.{u} _ (Under n) _
      (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
      (Under.forget n ⋙ simplicialSpaceDiscrete.obj K)
      (Under.forget n ⋙ Y) (data.1.down _ _ n) a
    let πYY' := @Enriched.FunctorCategory.enrichedHomπ
      SSet.{u} _ _ SSet.{u} _ (Under n) _
      (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
      (Under.forget n ⋙ Y) (Under.forget n ⋙ Y')
      (data.1.down _ _ n) a
    let HKY := @Enriched.FunctorCategory.enrichedHom
      SSet.{u} _ _ SSet.{u} _ (Under n) _
      (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
      (Under.forget n ⋙ simplicialSpaceDiscrete.obj K)
      (Under.forget n ⋙ Y) (data.1.down _ _ n)
    have hπKY' : simplicialSpaceCotensorπ K Y' n a = πKY' := rfl
    have hπKY : simplicialSpaceCotensorπ K Y n a = πKY := rfl
    rw [hπKY', hπKY]
    erw [Category.assoc]
    dsimp only [comp]
    erw [hπraw]
    have hequiv : ((eHomEquiv (SimplicialObject SSet.{u})) g).app n =
        ((Enriched.FunctorCategory.functorHomEquiv SSet.{u}) g).app n := rfl
    have hunitor :
        ((ρ_ ((simplicialSpaceDiscrete.obj K) ⟶[
          SimplicialObject SSet.{u}] Y)).inv).app n =
        (ρ_ HKY).inv := rfl
    have hwhisk :
        (((simplicialSpaceDiscrete.obj K) ⟶[
            SimplicialObject SSet.{u}] Y) ◁
          (eHomEquiv (SimplicialObject SSet.{u})) g).app n =
        HKY ◁ ((eHomEquiv (SimplicialObject SSet.{u})) g).app n := rfl
    rw [hunitor, hwhisk, hequiv]
    have hmapπ :
        ((Enriched.FunctorCategory.functorHomEquiv SSet.{u}) g).app n ≫
            πYY' =
          (eHomEquiv SSet.{u}) (g.app a.right) := by
      rw [Enriched.FunctorCategory.functorHomEquiv_apply_app]
      unfold Enriched.FunctorCategory.precompEnrichedHom
      unfold Enriched.FunctorCategory.precompEnrichedHom'
      dsimp only [πYY']
      erw [Category.assoc, end_.lift_π]
      dsimp [Enriched.FunctorCategory.diagram]
      erw [eHomWhiskerRight_id, eHomWhiskerLeft_id]
      exact @Enriched.FunctorCategory.homEquiv_apply_π
        SSet.{u} _ _ SSet.{u} _ SimplexCategoryᵒᵖ _
        (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
        Y Y' (data.2.down _ _) g a.right
    have hcombine :
        (HKY ◁ ((Enriched.FunctorCategory.functorHomEquiv SSet.{u})
          g).app n) ≫ (πKY ⊗ₘ πYY') =
        πKY ⊗ₘ (((Enriched.FunctorCategory.functorHomEquiv SSet.{u})
          g).app n ≫ πYY') :=
      MonoidalCategory.whiskerLeft_comp_tensorHom _ _ _
    let cbase := eComp SSet.{u}
      ((simplicialSpaceDiscrete.obj K).obj a.right)
      (Y.obj a.right) (Y'.obj a.right)
    have hcombine_assoc :
        (HKY ◁ ((Enriched.FunctorCategory.functorHomEquiv SSet.{u})
            g).app n) ≫ ((πKY ⊗ₘ πYY') ≫ cbase) =
        (πKY ⊗ₘ (((Enriched.FunctorCategory.functorHomEquiv SSet.{u})
            g).app n ≫ πYY')) ≫ cbase := by
      exact (Category.assoc _ _ _).symm.trans (hcombine =≫ cbase)
    dsimp only [πKY, πYY', cbase,
      Enriched.FunctorCategory.enrichedHomπ] at hcombine_assoc
    slice_lhs 2 3 => erw [hcombine_assoc]
    rw [hmapπ]
    let gbase := (eHomEquiv SSet.{u}) (g.app a.right)
    have hunit :
        (ρ_ HKY).inv ≫ (πKY ⊗ₘ gbase) =
          πKY ≫ (ρ_ _).inv ≫ _ ◁ gbase :=
      MonoidalCategory.rightUnitor_inv_comp_tensorHom πKY gbase
    calc
      _ = ((ρ_ HKY).inv ≫ (πKY ⊗ₘ gbase)) ≫ cbase :=
        (Category.assoc _ _ _).symm
      _ = (πKY ≫ (ρ_ _).inv ≫ _ ◁ gbase) ≫ cbase :=
        hunit =≫ cbase
      _ = _ := by
        rw [← MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
        rfl

set_option backward.isDefEq.respectTransparency false in
/-- Maps into a cotensor degree are equal when all end projections agree. -/
theorem simplicialSpaceCotensor_hom_ext
    (K : SSet.{u}) (Y : SimplicialObject SSet.{u})
    (n : SimplexCategoryᵒᵖ) {Z : SSet.{u}}
    {p q : Z ⟶ ((simplicialSpaceCotensor.obj (op K)).obj Y).obj n}
    (h : ∀ a : Under n,
      p ≫ simplicialSpaceCotensorπ K Y n a =
      q ≫ simplicialSpaceCotensorπ K Y n a) : p = q :=
  by
    let _ : EnrichedCategory SSet.{u} SSet.{u} :=
      MonoidalClosed.enrichedCategorySelf SSet.{u}
    let _ : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
      MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
    let data := simplicialSpaceEnrichedOrdinaryCategory
    let _ : ∀ (F G : SimplicialObject SSet.{u}),
        Enriched.FunctorCategory.HasFunctorEnrichedHom SSet.{u} F G :=
      data.1.down
    let _ : ∀ (F G : SimplicialObject SSet.{u}),
        Enriched.FunctorCategory.HasEnrichedHom SSet.{u} F G :=
      data.2.down
    let _ : EnrichedOrdinaryCategory (SimplicialObject SSet.{u})
        (SimplicialObject SSet.{u}) :=
      Enriched.FunctorCategory.functorEnrichedOrdinaryCategory
        SSet.{u} SSet.{u} SimplexCategoryᵒᵖ
    apply end_.hom_ext
    intro a
    simpa [simplicialSpaceCotensor, simplicialSpaceCotensorπ,
      Enriched.FunctorCategory.enrichedHomπ] using h a

/-- For fixed `K`, external tensor is left adjoint to the explicit end
cotensor. -/
@[no_expose]
noncomputable def simplicialSpaceTensorCotensorAdjunction (K : SSet.{u}) :
    simplicialSpaceTensor.obj K ⊣ simplicialSpaceCotensor.obj (op K) :=
  by
    letI : EnrichedCategory SSet.{u} SSet.{u} :=
      MonoidalClosed.enrichedCategorySelf SSet.{u}
    letI : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
      MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
    let data := simplicialSpaceEnrichedOrdinaryCategory
    letI : ∀ (F G : SimplicialObject SSet.{u}),
        Enriched.FunctorCategory.HasFunctorEnrichedHom SSet.{u} F G :=
      data.1.down
    letI : ∀ (F G : SimplicialObject SSet.{u}),
        Enriched.FunctorCategory.HasEnrichedHom SSet.{u} F G :=
      data.2.down
    letI : EnrichedOrdinaryCategory (SimplicialObject SSet.{u})
        (SimplicialObject SSet.{u}) :=
      Enriched.FunctorCategory.functorEnrichedOrdinaryCategory
        SSet.{u} SSet.{u} SimplexCategoryᵒᵖ
    change tensorLeft (simplicialSpaceDiscrete.obj K) ⊣
      (eHomFunctor (SimplicialObject SSet.{u})
        (SimplicialObject SSet.{u})).obj
          (op (simplicialSpaceDiscrete.obj K))
    exact MonoidalClosed.FunctorCategory.adj
      (simplicialSpaceDiscrete.obj K)

private theorem simplicialSpaceTensorCotensorAdjunction_naturality_K
    {K L : SSet.{u}} (f : L ⟶ K)
    (X Y : SimplicialObject SSet.{u})
    (h : X ⟶ (simplicialSpaceCotensor.obj (op K)).obj Y) :
    ((simplicialSpaceTensorCotensorAdjunction L).homEquiv X Y).symm
        (h ≫ ((simplicialSpaceCotensor.map f.op).app Y)) =
      ((simplicialSpaceTensor.map f).app X) ≫
        ((simplicialSpaceTensorCotensorAdjunction K).homEquiv X Y).symm h := by
  let _ : EnrichedCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedCategorySelf SSet.{u}
  let _ : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
  let data := simplicialSpaceEnrichedOrdinaryCategory
  let _ : ∀ (F G : SimplicialObject SSet.{u}),
      Enriched.FunctorCategory.HasFunctorEnrichedHom SSet.{u} F G :=
    data.1.down
  let _ : ∀ (F G : SimplicialObject SSet.{u}),
      Enriched.FunctorCategory.HasEnrichedHom SSet.{u} F G :=
    data.2.down
  let _ : EnrichedOrdinaryCategory (SimplicialObject SSet.{u})
      (SimplicialObject SSet.{u}) :=
    Enriched.FunctorCategory.functorEnrichedOrdinaryCategory
      SSet.{u} SSet.{u} SimplexCategoryᵒᵖ
  apply NatTrans.ext
  funext n
  change ((MonoidalClosed.FunctorCategory.homEquiv).symm
      (h ≫ ((simplicialSpaceCotensor.map f.op).app Y))).app n =
    ((((simplicialSpaceTensor.map f).app X) ≫
      (MonoidalClosed.FunctorCategory.homEquiv).symm h).app n)
  let a₀ : Under n := Under.mk (𝟙 n)
  change uncurry (((h.app n ≫
      ((simplicialSpaceCotensor.map f.op).app Y).app n) ≫
        simplicialSpaceCotensorπ L Y n a₀)) =
    ((simplicialSpaceDiscrete.map f).app n ▷ X.obj n) ≫
      uncurry (h.app n ≫ simplicialSpaceCotensorπ K Y n a₀)
  rw [Category.assoc, simplicialSpaceCotensorπ_map_K]
  exact uncurry_pre_app (Y.obj a₀.right)
    (h.app n ≫ simplicialSpaceCotensorπ K Y n a₀)
    ((simplicialSpaceDiscrete.map f).app n)

/-- Maps into a cotensor represent maps into the canonical outer simplicial
mapping object. -/
noncomputable def simplicialSpaceHomCotensorEquiv
    (K : SSet.{u}) (X Y : SimplicialObject SSet.{u}) :
    (X ⟶ (simplicialSpaceCotensor.obj (op K)).obj Y) ≃
      (K ⟶ CategoryTheory.SimplicialCategory.sHom X Y) :=
  ((simplicialSpaceTensorCotensorAdjunction K).homEquiv X Y).symm.trans
    (simplicialSpaceTensorHomEquiv K X Y)

/-- Naturality of Hom--cotensor in the outer simplicial-set variable. -/
theorem simplicialSpaceHomCotensorEquiv_naturality_K
    {K L : SSet.{u}} (f : L ⟶ K)
    (X Y : SimplicialObject SSet.{u})
    (h : X ⟶ (simplicialSpaceCotensor.obj (op K)).obj Y) :
    CategoryTheory.Functor.functorHomEquiv X Y L
        (simplicialSpaceHomCotensorEquiv L X Y
          (h ≫ ((simplicialSpaceCotensor.map f.op).app Y))) =
      CategoryTheory.Functor.HomObj.map f
        (CategoryTheory.Functor.functorHomEquiv X Y K
          (simplicialSpaceHomCotensorEquiv K X Y h)) := by
  dsimp only [simplicialSpaceHomCotensorEquiv, Equiv.trans_apply]
  rw [simplicialSpaceTensorCotensorAdjunction_naturality_K]
  exact simplicialSpaceTensorHomEquiv_naturality_K f X Y _

/-- Naturality of Hom--cotensor in its contravariant simplicial-space
variable. -/
theorem simplicialSpaceHomCotensorEquiv_naturality_X
    (K : SSet.{u}) {X X' Y : SimplicialObject SSet.{u}}
    (g : X' ⟶ X)
    (h : X ⟶ (simplicialSpaceCotensor.obj (op K)).obj Y) :
    CategoryTheory.Functor.functorHomEquiv X' Y K
        (simplicialSpaceHomCotensorEquiv K X' Y (g ≫ h)) =
      (CategoryTheory.Functor.HomObj.ofNatTrans g :
          CategoryTheory.Functor.HomObj X' X K).comp
        (CategoryTheory.Functor.functorHomEquiv X Y K
          (simplicialSpaceHomCotensorEquiv K X Y h)) := by
  dsimp only [simplicialSpaceHomCotensorEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left_symm
    (simplicialSpaceTensorCotensorAdjunction K) g h]
  exact simplicialSpaceTensorHomEquiv_naturality_X K g _

/-- Naturality of Hom--cotensor in its covariant simplicial-space variable. -/
theorem simplicialSpaceHomCotensorEquiv_naturality_Y
    (K : SSet.{u}) {X Y Y' : SimplicialObject SSet.{u}}
    (h : X ⟶ (simplicialSpaceCotensor.obj (op K)).obj Y)
    (q : Y ⟶ Y') :
    CategoryTheory.Functor.functorHomEquiv X Y' K
        (simplicialSpaceHomCotensorEquiv K X Y'
          (h ≫ (simplicialSpaceCotensor.obj (op K)).map q)) =
      (CategoryTheory.Functor.functorHomEquiv X Y K
          (simplicialSpaceHomCotensorEquiv K X Y h)).comp
        (CategoryTheory.Functor.HomObj.ofNatTrans q :
          CategoryTheory.Functor.HomObj Y Y' K) := by
  dsimp only [simplicialSpaceHomCotensorEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right_symm
    (simplicialSpaceTensorCotensorAdjunction K) h q]
  exact simplicialSpaceTensorHomEquiv_naturality_Y K _ q

/-- Unit of the fixed-`K` tensor--cotensor adjunction. -/
noncomputable def simplicialSpaceTensorCotensorUnit (K : SSet.{u}) :
    𝟭 (SimplicialObject SSet.{u}) ⟶
      simplicialSpaceTensor.obj K ⋙ simplicialSpaceCotensor.obj (op K) :=
  (simplicialSpaceTensorCotensorAdjunction K).unit

/-- Counit of the fixed-`K` tensor--cotensor adjunction. -/
noncomputable def simplicialSpaceTensorCotensorCounit (K : SSet.{u}) :
    simplicialSpaceCotensor.obj (op K) ⋙ simplicialSpaceTensor.obj K ⟶
      𝟭 (SimplicialObject SSet.{u}) :=
  (simplicialSpaceTensorCotensorAdjunction K).counit

/-- Characteristic formula for the forward adjunction equivalence. -/
theorem simplicialSpaceTensorCotensor_homEquiv_apply
    (K : SSet.{u}) (X Y : SimplicialObject SSet.{u})
    (f : (simplicialSpaceTensor.obj K).obj X ⟶ Y) :
    (simplicialSpaceTensorCotensorAdjunction K).homEquiv X Y f =
      (simplicialSpaceTensorCotensorUnit K).app X ≫
        (simplicialSpaceCotensor.obj (op K)).map f :=
  by
    simpa only [simplicialSpaceTensorCotensorUnit] using
      (simplicialSpaceTensorCotensorAdjunction K).homEquiv_unit X Y f

/-- Characteristic formula for the inverse adjunction equivalence. -/
theorem simplicialSpaceTensorCotensor_homEquiv_symm_apply
    (K : SSet.{u}) (X Y : SimplicialObject SSet.{u})
    (g : X ⟶ (simplicialSpaceCotensor.obj (op K)).obj Y) :
    ((simplicialSpaceTensorCotensorAdjunction K).homEquiv X Y).symm g =
      (simplicialSpaceTensor.obj K).map g ≫
        (simplicialSpaceTensorCotensorCounit K).app Y :=
  by
    simpa only [simplicialSpaceTensorCotensorCounit] using
      (simplicialSpaceTensorCotensorAdjunction K).homEquiv_counit X Y g

/-- Left triangle identity for the fixed-`K` adjunction. -/
theorem simplicialSpaceTensorCotensor_left_triangle
    (K : SSet.{u}) (X : SimplicialObject SSet.{u}) :
    (simplicialSpaceTensor.obj K).map
        ((simplicialSpaceTensorCotensorUnit K).app X) ≫
      (simplicialSpaceTensorCotensorCounit K).app
        ((simplicialSpaceTensor.obj K).obj X) = 𝟙 _ :=
  (simplicialSpaceTensorCotensorAdjunction K).left_triangle_components X

/-- Right triangle identity for the fixed-`K` adjunction. -/
theorem simplicialSpaceTensorCotensor_right_triangle
    (K : SSet.{u}) (Y : SimplicialObject SSet.{u}) :
    (simplicialSpaceTensorCotensorUnit K).app
        ((simplicialSpaceCotensor.obj (op K)).obj Y) ≫
      (simplicialSpaceCotensor.obj (op K)).map
        ((simplicialSpaceTensorCotensorCounit K).app Y) = 𝟙 _ :=
  (simplicialSpaceTensorCotensorAdjunction K).right_triangle_components Y

end SSet

end
