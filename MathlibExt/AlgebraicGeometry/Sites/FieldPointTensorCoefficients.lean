/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleTensorCoefficients
public import MathlibExt.AlgebraicGeometry.Sites.FieldModuleCohomologyCategory
public import MathlibExt.AlgebraicGeometry.Sites.FieldGeometricClosureComparison
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientCupProduct
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientLongExact

/-! # Tensor germs and their actual point and Galois actions -/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.DerivedSections

/-- The actual point map sends every germ to the germ at its image point element. -/
theorem pointHom_presheafFiber_germ (X : Scheme.{u})
    {p q : GrothendieckTopology.Point.{max u w} X.smallEtaleTopology} (h : p ⟶ q)
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (U : X.Etale) (x : q.fiber.obj U) :
    q.toPresheafFiber U x P ≫ h.presheafFiber.app P =
      p.toPresheafFiber U (h.hom.app U x) P := by
  exact q.toPresheafFiber_presheafFiberDesc
    (fun V y => p.toPresheafFiber V (h.hom.app V y) P)
    (by
      intro V Z f y
      refine (p.toPresheafFiber_w f (h.hom.app V y) P).trans ?_
      exact congrArg (fun z => p.toPresheafFiber Z z P)
        (h.hom.naturality_apply f y).symm)
    U x

set_option backward.isDefEq.respectTransparency.types false in
/-- The literal tensor of germs commutes with every actual map of points. -/
theorem smallEtalePointTensorStalkMap_point_naturality (X : Scheme.{u})
    {p q : GrothendieckTopology.Point.{max u w} X.smallEtaleTopology} (h : p ⟶ q)
    (F G : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) :
    h.presheafFiber.app (smallEtaleTensorPresheaf.{u, w} X F G) ≫
        smallEtalePointTensorStalkMap.{u, w} X p F G =
      smallEtalePointTensorStalkMap.{u, w} X q F G ≫
        AddCommGrpCat.ofHom (TensorProduct.map
          (h.presheafFiber.app F).hom.toIntLinearMap
          (h.presheafFiber.app G).hom.toIntLinearMap).toAddMonoidHom := by
  apply q.presheafFiber_hom_ext
  intro U x
  have ht := pointHom_presheafFiber_germ X h (smallEtaleTensorPresheaf.{u, w} X F G) U x
  have hp : p.toPresheafFiber U (h.hom.app U x) (smallEtaleTensorPresheaf.{u, w} X F G) ≫
      smallEtalePointTensorStalkMap.{u, w} X p F G =
      AddCommGrpCat.ofHom (TensorProduct.map
        (p.toPresheafFiber U (h.hom.app U x) F).hom.toIntLinearMap
        (p.toPresheafFiber U (h.hom.app U x) G).hom.toIntLinearMap).toAddMonoidHom :=
    p.toPresheafFiber_presheafFiberDesc _ _ U (h.hom.app U x)
  have hq : q.toPresheafFiber U x (smallEtaleTensorPresheaf.{u, w} X F G) ≫
      smallEtalePointTensorStalkMap.{u, w} X q F G =
      AddCommGrpCat.ofHom (TensorProduct.map
        (q.toPresheafFiber U x F).hom.toIntLinearMap
        (q.toPresheafFiber U x G).hom.toIntLinearMap).toAddMonoidHom :=
    q.toPresheafFiber_presheafFiberDesc _ _ U x
  have hv : TensorProduct.map
        (p.toPresheafFiber U (h.hom.app U x) F).hom.toIntLinearMap
        (p.toPresheafFiber U (h.hom.app U x) G).hom.toIntLinearMap =
      (TensorProduct.map (h.presheafFiber.app F).hom.toIntLinearMap
        (h.presheafFiber.app G).hom.toIntLinearMap).comp
        (TensorProduct.map (q.toPresheafFiber U x F).hom.toIntLinearMap
          (q.toPresheafFiber U x G).hom.toIntLinearMap) := by
    apply TensorProduct.ext'
    intro a b
    exact congrArg₂ (fun a b => a ⊗ₜ[ℤ] b)
      (ConcreteCategory.congr_hom (pointHom_presheafFiber_germ X h F U x) a).symm
      (ConcreteCategory.congr_hom (pointHom_presheafFiber_germ X h G U x) b).symm
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun l => l ≫ smallEtalePointTensorStalkMap.{u, w} X p F G) ht).trans
      (hp.trans ((congrArg (fun l => AddCommGrpCat.ofHom l.toAddMonoidHom) hv).trans
        ((congrArg (fun l => l ≫ AddCommGrpCat.ofHom (TensorProduct.map
          (h.presheafFiber.app F).hom.toIntLinearMap
          (h.presheafFiber.app G).hom.toIntLinearMap).toAddMonoidHom) hq).symm.trans
          (Category.assoc _ _ _)))))

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual tensor sheaf stalk isomorphism commutes with every map of points. -/
theorem smallEtalePointTensorSheafStalkIso_point_naturality (X : Scheme.{u})
    {p q : GrothendieckTopology.Point.{max u w} X.smallEtaleTopology} (h : p ⟶ q)
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    h.sheafFiber.app (smallEtaleTensorSheaf.{u, w} X F G) ≫
        (smallEtalePointTensorSheafStalkIso.{u, w} X p F G).hom =
      (smallEtalePointTensorSheafStalkIso.{u, w} X q F G).hom ≫
        AddCommGrpCat.ofHom (TensorProduct.map
          (h.sheafFiber.app F).hom.toIntLinearMap
          (h.sheafFiber.app G).hom.toIntLinearMap).toAddMonoidHom := by
  let T := smallEtaleTensorPresheaf.{u, w} X F.obj G.obj
  let ep := p.presheafToSheafCompSheafFiberIso AddCommGrpCat.{max u w}
  let eq := q.presheafToSheafCompSheafFiberIso AddCommGrpCat.{max u w}
  let ap := (p.presheafFiber (A := AddCommGrpCat.{max u w})).map (toSheafify X.smallEtaleTopology T)
  let aq := (q.presheafFiber (A := AddCommGrpCat.{max u w})).map (toSheafify X.smallEtaleTopology T)
  have hap : ap ≫ ep.hom.app T = 𝟙 _ := (ep.app T).inv_hom_id
  have haq : aq ≫ eq.hom.app T = 𝟙 _ := (eq.app T).inv_hom_id
  have hn : aq ≫ h.presheafFiber.app (sheafify X.smallEtaleTopology T) =
      h.presheafFiber.app T ≫ ap := h.presheafFiber.naturality (toSheafify X.smallEtaleTopology T)
  have ht := smallEtalePointTensorStalkMap_point_naturality.{u, w} X h F.obj G.obj
  apply (cancel_epi aq).1
  change aq ≫ (h.presheafFiber.app (sheafify X.smallEtaleTopology T) ≫
      (ep.hom.app T ≫ smallEtalePointTensorStalkMap.{u, w} X p F.obj G.obj)) =
    aq ≫ ((eq.hom.app T ≫ smallEtalePointTensorStalkMap.{u, w} X q F.obj G.obj) ≫ _)
  calc
    _ = (aq ≫ h.presheafFiber.app (sheafify X.smallEtaleTopology T)) ≫
        ep.hom.app T ≫ smallEtalePointTensorStalkMap.{u, w} X p F.obj G.obj := by
      simp only [Category.assoc]
    _ = (h.presheafFiber.app T ≫ ap) ≫ ep.hom.app T ≫
        smallEtalePointTensorStalkMap.{u, w} X p F.obj G.obj :=
      congrArg (fun f => f ≫ ep.hom.app T ≫ smallEtalePointTensorStalkMap.{u, w} X p F.obj G.obj) hn
    _ = h.presheafFiber.app T ≫ smallEtalePointTensorStalkMap.{u, w} X p F.obj G.obj := by
      rw [Category.assoc, ← Category.assoc ap, hap, Category.id_comp]
    _ = smallEtalePointTensorStalkMap.{u, w} X q F.obj G.obj ≫ _ := ht
    _ = _ := by
      rw [← Category.assoc aq, ← Category.assoc aq, haq, Category.id_comp]
      rfl

section Field

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
attribute [local instance] IsSepClosure.sep_closed

/-- The original Galois action preserves the actual binary integer tensor of germs. -/
theorem fieldPointTensorSheafStalkIso_galois
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (g : Gal(Ω/k)) :
    (fieldGaloisStalkMap.{u, w} k Ω g).app
        (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G) ≫
      (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k))
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)) F G).hom =
    (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k))
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)) F G).hom ≫
      AddCommGrpCat.ofHom (TensorProduct.map
        ((fieldGaloisStalkMap.{u, w} k Ω g).app F).hom.toIntLinearMap
        ((fieldGaloisStalkMap.{u, w} k Ω g).app G).hom.toIntLinearMap).toAddMonoidHom :=
  smallEtalePointTensorSheafStalkIso_point_naturality.{u, w} (Spec (.of k))
    (fieldGaloisPointEndomorphism.{u, w} k Ω g) F G

local instance fieldNativeModuleDiscrete (M : FieldCohomologyModule.{u, w} k Ω) :
    DiscreteTopology ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω)).obj M) := M.property

set_option backward.isDefEq.respectTransparency.types false in
/-- The original field coefficient representation of the actual binary tensor sheaf
is isomorphic to the actual continuous integer tensor of the original field fibers. -/
def fieldPointTensorTopRepIso
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G)) ≅
      ContinuousCohomology.discreteTensorCoefficient
        ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
          (InfiniteGalois.profiniteGalGrp k Ω)).obj
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F))
        ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
          (InfiniteGalois.profiniteGalGrp k Ω)).obj
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj G)) := by
  let A := (ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω)).obj ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)
  let B := (ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω)).obj ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj G)
  let S := (ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω)).obj ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
      (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G))
  let T := ContinuousCohomology.discreteTensorCoefficient A B
  letI : TopologicalSpace T := T.hV3
  letI : IsTopologicalAddGroup T := T.hV4
  letI : ContinuousSMul ℤ T := T.hV5
  letI : DiscreteTopology T := ContinuousCohomology.discreteTensorCoefficient_discrete A B
  let e : S ≃+ T :=
    (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k))
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)) F G).addCommGroupIsoToAddEquiv
  have he (g : Gal(Ω/k)) (x : S) : e (S.ρ g x) = T.ρ g (e x) := by
    exact ConcreteCategory.congr_hom (fieldPointTensorSheafStalkIso_galois.{u, w} k Ω F G g) x
  let f : S ⟶ T := ConcreteCategory.ofHom (X := S) (Y := T)
    { toContinuousLinearMap := DiscreteAbelianAction.addHomContinuousLinearMap
        (TopModuleCat.of ℤ S) (TopModuleCat.of ℤ T) e.toAddMonoidHom
      isIntertwining' g := by
        apply ContinuousLinearMap.ext
        intro x
        exact he g x }
  let i : T ⟶ S := ConcreteCategory.ofHom (X := T) (Y := S)
    { toContinuousLinearMap := DiscreteAbelianAction.addHomContinuousLinearMap
        (TopModuleCat.of ℤ T) (TopModuleCat.of ℤ S) e.symm.toAddMonoidHom
      isIntertwining' g := by
        apply ContinuousLinearMap.ext
        intro x
        apply e.injective
        change e (e.symm (T.ρ g x)) = e (S.ρ g (e.symm x))
        rw [e.apply_symm_apply, he]
        exact congrArg (T.ρ g) (e.apply_symm_apply x).symm }
  exact
    { hom := f
      inv := i
      hom_inv_id := by
        apply TopRep.hom_ext
        apply ContIntertwiningMap.ext
        apply ContinuousLinearMap.ext
        intro x
        change e.symm (e x) = x
        exact e.symm_apply_apply x
      inv_hom_id := by
        apply TopRep.hom_ext
        apply ContIntertwiningMap.ext
        apply ContinuousLinearMap.ext
        intro x
        exact e.apply_symm_apply x }

/-- The forward original representation map is the SAME tensor-of-germs map. -/
theorem fieldPointTensorTopRepIso_hom_apply
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (x : fieldGeometricStalkCarrier.{u, w} k Ω
      (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G)) :
    (fieldPointTensorTopRepIso.{u, w} k Ω F G).hom.hom x =
      (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k))
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)) F G).hom x := rfl

/-- Every pure section germ is sent to the pure tensor of the two original field germs. -/
theorem fieldPointTensorTopRepIso_original_germ_tmul
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (a : F.obj.obj (op U)) (b : G.obj.obj (op U)) :
    (fieldPointTensorTopRepIso.{u, w} k Ω F G).hom.hom
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G).obj
        (smallEtaleTensorSheafSectionMap.{u, w} (Spec (.of k)) F G (op U) (a ⊗ₜ[ℤ] b))) =
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) F.obj a) ⊗ₜ[ℤ]
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) G.obj b) :=
  smallEtalePointTensorSheafStalkIso_section_tmul.{u, w} (Spec (.of k))
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)) F G U (ULift.up z) a b

set_option backward.isDefEq.respectTransparency.types false in
/-- The original field tensor representation comparison respects every original coefficient
arrow. -/
theorem fieldPointTensorTopRepIso_naturality
    {F F' G G' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : F ⟶ F') (g : G ⟶ G') :
    let P := ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω)
    let J := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    P.map (J.map (smallEtaleTensorSheafMap.{u, w} (Spec (.of k)) f g)) ≫
        (fieldPointTensorTopRepIso.{u, w} k Ω F' G').hom =
      (fieldPointTensorTopRepIso.{u, w} k Ω F G).hom ≫
        ContinuousCohomology.discreteTensorCoefficientMap (P.map (J.map f)) (P.map (J.map g)) := by
  intro P J
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext
  apply ContinuousLinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom
    (smallEtalePointTensorSheafStalkIso_naturality.{u, w} (Spec (.of k))
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)) f g) x

/-- The actual diagonal integer tensor of two original discrete continuous Galois modules. -/
def fieldTensorCoefficientModule (M N : FieldCohomologyModule.{u, w} k Ω) :
    FieldCohomologyModule.{u, w} k Ω := by
  let P := ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω)
  let A := P.obj M
  let B := P.obj N
  let T := ContinuousCohomology.discreteTensorCoefficient A B
  have hA : ((TopRep.toActionTopModFunc (k := ℤ) (G := Gal(Ω/k))).obj A).IsContinuous := by
    change M.obj.obj.IsContinuous
    exact M.obj.property
  have hB : ((TopRep.toActionTopModFunc (k := ℤ) (G := Gal(Ω/k))).obj B).IsContinuous := by
    change N.obj.obj.IsContinuous
    exact N.obj.property
  exact ⟨⟨(TopRep.toActionTopModFunc (k := ℤ) (G := Gal(Ω/k))).obj T,
    ContinuousCohomology.discreteTensorCoefficient_action_isContinuous A B hA hB⟩,
      ContinuousCohomology.discreteTensorCoefficient_discrete A B⟩

/-- The original module tensor has exactly the original algebraic integer tensor carrier. -/
theorem fieldTensorCoefficientModule_carrier (M N : FieldCohomologyModule.{u, w} k Ω) :
    (DiscreteAbelianAction.underlying (fieldTensorCoefficientModule.{u, w} k Ω M N) : Type
        (max u w)) =
      TensorProduct ℤ (DiscreteAbelianAction.underlying M)
          (DiscreteAbelianAction.underlying N) := rfl

/-- Its literal Galois action on a pure tensor uses the original stored factor modules. -/
theorem fieldTensorCoefficientModule_action_tmul
    (M N : FieldCohomologyModule.{u, w} k Ω) (g : Gal(Ω/k)) :
    let P := ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω)
    let A := P.obj M
    let B := P.obj N
    letI : Module ℤ A := A.hV2
    letI : Module ℤ B := B.hV2
    ∀ (a : A) (b : B),
      ((fieldTensorCoefficientModule.{u, w} k Ω M N).obj.obj.ρ g).asHom.hom (a ⊗ₜ[ℤ] b) =
        A.ρ g a ⊗ₜ[ℤ] B.ρ g b := by
  intro P A B a b
  exact ContinuousCohomology.discreteTensorCoefficient_action_tmul A B g a b

/-- The original geometric-fiber tensor comparison also lies in the original Galois module
category. -/
def fieldPointTensorGaloisIso
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G) ≅
      fieldTensorCoefficientModule.{u, w} k Ω
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj G) := by
  let P := ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω)
  let A := P.obj ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)
  let B := P.obj ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj G)
  let T := ContinuousCohomology.discreteTensorCoefficient A B
  exact (DiscreteAbelianAction.toTopRep.{u, max u w} (G := Gal(Ω/k))).preimageIso
    (fieldPointTensorTopRepIso.{u, w} k Ω F G ≪≫ (TopRep.toActionFromAction T).symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- The original Galois module arrow retains the SAME actual tensor-of-germs value. -/
theorem fieldPointTensorGaloisIso_hom_apply
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (x : fieldGeometricStalkCarrier.{u, w} k Ω
      (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G)) :
    DiscreteAbelianAction.homToAdd (fieldPointTensorGaloisIso.{u, w} k Ω F G).hom x =
      (fieldPointTensorTopRepIso.{u, w} k Ω F G).hom.hom x := by
  let P := DiscreteAbelianAction.toTopRep.{u, max u w} (G := Gal(Ω/k))
  let e := fieldPointTensorTopRepIso.{u, w} k Ω F G
  let T := ContinuousCohomology.discreteTensorCoefficient
    ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω)).obj
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F))
    ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω)).obj
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj G))
  let M := (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
    (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G)
  let N := fieldTensorCoefficientModule.{u, w} k Ω
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj G)
  have h : P.map (fieldPointTensorGaloisIso.{u, w} k Ω F G).hom =
      (e ≪≫ (TopRep.toActionFromAction T).symm).hom :=
    P.map_preimage (X := M) (Y := N) (e ≪≫ (TopRep.toActionFromAction T).symm).hom
  exact congrArg (fun f : P.obj M ⟶ P.obj N => f.hom x) h

/-- The actual inverse sheaf equivalence identifies the tensor sheaf with the inverse
of the actual diagonal integer tensor of its two prescribed geometric fibers. -/
def fieldTensorSheafInverseIso
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G ≅
      (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj
        (fieldTensorCoefficientModule.{u, w} k Ω
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj G)) :=
  (fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.app
      (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G) ≪≫
    (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).mapIso
      (fieldPointTensorGaloisIso.{u, w} k Ω F G)

set_option backward.isDefEq.respectTransparency.types false in
/-- The original inverse sheaf tensor comparison has the literal tensor of the two
original germ values on every original pure section tensor. -/
theorem fieldTensorSheafInverseIso_original_germ_tmul
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (a : F.obj.obj (op U)) (b : G.obj.obj (op U)) :
    let V := fieldTensorCoefficientModule.{u, w} k Ω
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj G)
    let h : FieldEquivariantFunctions.{u, w} k Ω U V :=
      (fieldTensorSheafInverseIso.{u, w} k Ω F G).hom.hom.app (op U)
        (smallEtaleTensorSheafSectionMap.{u, w} (Spec (.of k)) F G (op U) (a ⊗ₜ[ℤ] b))
    h z =
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) F.obj a) ⊗ₜ[ℤ]
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) G.obj b) := by
  intro V h
  let T := smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G
  let M := (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj T
  let η : T ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M :=
    (fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.hom.app T
  let d : M ⟶ V := (fieldPointTensorGaloisIso.{u, w} k Ω F G).hom
  let c := smallEtaleTensorSheafSectionMap.{u, w} (Spec (.of k)) F G (op U) (a ⊗ₜ[ℤ] b)
  let h₀ : FieldEquivariantFunctions.{u, w} k Ω U M := η.hom.app (op U) c
  have hm := fieldSheafGaloisEquivalence_inverse_map.{u, w} k Ω d U h₀ z
  have hu : h₀ z =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) T.obj c :=
    fieldSheafGaloisEquivalence_unit_germ.{u, w} k Ω T U z c
  exact hm.trans ((congrArg (DiscreteAbelianAction.homToAdd d) hu).trans
    ((fieldPointTensorGaloisIso_hom_apply.{u, w} k Ω F G _).trans
      (fieldPointTensorTopRepIso_original_germ_tmul.{u, w} k Ω F G U z a b)))

variable (Ψ : Type u) [Field Ψ] [Algebra k Ψ] [IsSepClosed Ψ]

/-- An explicit closure embedding preserves the original binary integer tensor of germs. -/
theorem fieldClosureCommonStalkIso_tensor
    (σ : Ω →ₐ[k] Ψ)
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldClosureCommonStalkIso.{u, w} k Ω Ψ σ).hom.app
        (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G) ≫
      (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k))
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ψ)) F G).hom =
    (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k))
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)) F G).hom ≫
      AddCommGrpCat.ofHom (TensorProduct.map
        ((fieldClosureCommonStalkIso.{u, w} k Ω Ψ σ).hom.app F).hom.toIntLinearMap
        ((fieldClosureCommonStalkIso.{u, w} k Ω Ψ σ).hom.app
            G).hom.toIntLinearMap).toAddMonoidHom :=
  smallEtalePointTensorSheafStalkIso_point_naturality.{u, w} (Spec (.of k))
    (fieldClosureCommonPointIso.{u, w} k Ω Ψ σ).hom F G

end Field

end AlgebraicGeometry.Scheme.DerivedSections
