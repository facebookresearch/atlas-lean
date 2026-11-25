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

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.GroupAdjunction
public import Mathlib.Algebra.Ring.Equiv

/-!
# Currying balanced tensor in its left-module factor

The function object carries the domain action, with the Rᵐᵒᵖᵐᵒᵖ action
restricted along `RingEquiv.opOp`. The tensor object retains its integer
module structure.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite

universe u v

namespace ModuleCat.BalancedTensor

variable (R : Type u) [Ring R]

/-- The original pure balanced class, in the existing two-variable group object. -/
def groupPure (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R) (a : A) (b : B) :
    ((groupBifunctor R).obj A).obj B := by
  letI : Module ℤ B := Module.compHom B (algebraMap ℤ R)
  exact TensorProduct.Balanced.mk ℤ R A B a b

/-- The native double-opposite domain action gives the actual left R Hom module. -/
def leftHomGroupModule (A : ModuleCat.{v} Rᵐᵒᵖ) (I : AddCommGrpCat.{v}) :
    Module R ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I) := by
  letI := ChainComplex.homGroupModule Rᵐᵒᵖ A I
  exact Module.compHom _ (RingEquiv.opOp R).toRingHom

/-- The left scalar acts by the original right action on the domain. -/
theorem leftHomGroupModule_smul_apply (A : ModuleCat.{v} Rᵐᵒᵖ)
    (I : AddCommGrpCat.{v}) (r : R)
    (f : (forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I) (a : A) :
    letI := leftHomGroupModule R A I
    (r • f).hom a = f.hom (op r • a) := by
  let := ChainComplex.homGroupModule Rᵐᵒᵖ A I
  let := leftHomGroupModule R A I
  change (op (op r) • f).hom a = f.hom (op r • a)
  exact ChainComplex.homGroupModule_smul_apply Rᵐᵒᵖ A I (op (op r)) f a

/-- Original right-module precomposition is linear for the earned left Hom action. -/
def leftHomGroupPrecomp {A A' : ModuleCat.{v} Rᵐᵒᵖ} (g : A' ⟶ A)
    (I : AddCommGrpCat.{v}) :
    letI := leftHomGroupModule R A I
    letI := leftHomGroupModule R A' I
    ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I) →ₗ[R]
      ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A' ⟶ I) := by
  letI := ChainComplex.homGroupModule Rᵐᵒᵖ A I
  letI := ChainComplex.homGroupModule Rᵐᵒᵖ A' I
  letI := leftHomGroupModule R A I
  letI := leftHomGroupModule R A' I
  let f := homGroupPrecomp Rᵐᵒᵖ g I
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r x => f.map_smul (op (op r)) x }

/-- The same precomposition has its original pointwise value. -/
theorem leftHomGroupPrecomp_apply {A A' : ModuleCat.{v} Rᵐᵒᵖ} (g : A' ⟶ A)
    (I : AddCommGrpCat.{v})
    (f : (forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I) (a : A') :
    letI := leftHomGroupModule R A I
    letI := leftHomGroupModule R A' I
    (leftHomGroupPrecomp R g I f).hom a = f.hom (g.hom a) := rfl

/-- Original tensor currying in the left-module variable, retaining its domain action. -/
def groupCurryLeft (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R)
    (I : AddCommGrpCat.{v}) (f : ((groupBifunctor R).obj A).obj B ⟶ I) :
    letI := leftHomGroupModule R A I
    B →ₗ[R] ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I) := by
  letI : Module ℤ B := Module.compHom B (algebraMap ℤ R)
  letI := leftHomGroupModule R A I
  let μ := TensorProduct.Balanced.mk ℤ R A B
  refine
    { toFun := fun b => AddCommGrpCat.ofHom
        { toFun := fun a => f.hom (groupPure R A B a b)
          map_zero' := by
            have hZero : μ (0 : A) b = 0 :=
              (DFunLike.congr_fun μ.map_zero b).trans (LinearMap.zero_apply b)
            change f.hom (μ (0 : A) b) = 0
            exact (congrArg f.hom hZero).trans f.hom.map_zero
          map_add' := fun a a' => by
            have hPure : groupPure R A B (a + a') b =
                groupPure R A B a b + groupPure R A B a' b := by
              change μ (a + a') b = μ a b + μ a' b
              exact (DFunLike.congr_fun (μ.map_add a a') b).trans
                (LinearMap.add_apply (μ a) (μ a') b)
            exact (congrArg f.hom hPure).trans
              (f.hom.map_add (groupPure R A B a b) (groupPure R A B a' b)) }
      map_add' := ?_
      map_smul' := ?_ }
  · intro b b'
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    change f.hom (groupPure R A B a (b + b')) =
      f.hom (groupPure R A B a b) + f.hom (groupPure R A B a b')
    have hPure : groupPure R A B a (b + b') =
        groupPure R A B a b + groupPure R A B a b' := by
      change μ a (b + b') = μ a b + μ a b'
      exact (μ a).map_add b b'
    exact (congrArg f.hom hPure).trans
      (f.hom.map_add (groupPure R A B a b) (groupPure R A B a b'))
  · intro r b
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    rw [leftHomGroupModule_smul_apply]
    change f.hom (groupPure R A B a (r • b)) =
      f.hom (groupPure R A B (op r • a) b)
    exact congrArg f.hom (TensorProduct.Balanced.balance ℤ R A B r a b).symm

/-- Its actual evaluation is the original coefficient-first pure tensor value. -/
theorem groupCurryLeft_mk (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R)
    (I : AddCommGrpCat.{v}) (f : ((groupBifunctor R).obj A).obj B ⟶ I) (a : A) (b : B) :
    letI := leftHomGroupModule R A I
    (groupCurryLeft R A B I f b).hom a = f.hom (groupPure R A B a b) := rfl

/-- Transpose the original Hom function back to the existing right-module currying. -/
def transposeLeftHom (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R)
    (I : AddCommGrpCat.{v})
    (g : letI := leftHomGroupModule R A I
      B →ₗ[R] ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I)) :
    letI := ChainComplex.homGroupModule R B I
    A →ₗ[Rᵐᵒᵖ] ((forget₂ (ModuleCat R) AddCommGrpCat).obj B ⟶ I) := by
  letI := leftHomGroupModule R A I
  letI := ChainComplex.homGroupModule R B I
  refine
    { toFun := fun a => AddCommGrpCat.ofHom
        { toFun := fun b => (g b).hom a
          map_zero' := by simp only [g.map_zero, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
          map_add' := fun b b' => by
            simp only [g.map_add, AddCommGrpCat.hom_add, AddMonoidHom.add_apply] }
      map_add' := ?_
      map_smul' := ?_ }
  · intro a a'
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro b
    exact (g b).hom.map_add a a'
  · intro r a
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro b
    rw [ChainComplex.homGroupModule_smul_apply]
    change (g b).hom (r • a) = (g (r.unop • b)).hom a
    rw [g.map_smul, leftHomGroupModule_smul_apply]
    rfl

/-- Uncurrying uses the already proved group tensor–Hom map on the same quotient. -/
def groupUncurryLeft (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R)
    (I : AddCommGrpCat.{v})
    (g : letI := leftHomGroupModule R A I
      B →ₗ[R] ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I)) :
    ((groupBifunctor R).obj A).obj B ⟶ I :=
  groupUncurry R A B I (transposeLeftHom R A B I g)

/-- The inverse map has exactly the original two-variable evaluation. -/
theorem groupUncurryLeft_mk (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R)
    (I : AddCommGrpCat.{v})
    (g : letI := leftHomGroupModule R A I
      B →ₗ[R] ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I)) (a : A) (b : B) :
    (groupUncurryLeft R A B I g).hom (groupPure R A B a b) = (g b).hom a := by
  let : Module ℤ B := Module.compHom B (algebraMap ℤ R)
  let := leftHomGroupModule R A I
  let := ChainComplex.homGroupModule R B I
  change (groupUncurry R A B I (transposeLeftHom R A B I g)).hom
    (TensorProduct.Balanced.mk ℤ R A B a b) = (g b).hom a
  exact groupUncurry_mk R A B I (transposeLeftHom R A B I g) a b

/-- The actual left-domain Hom map is native additive postcomposition. -/
def leftHomGroupMap (A : ModuleCat.{v} Rᵐᵒᵖ) {I I' : AddCommGrpCat.{v}}
    (g : I ⟶ I') :
    letI := leftHomGroupModule R A I
    letI := leftHomGroupModule R A I'
    ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I) →ₗ[R]
      ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I') := by
  letI := leftHomGroupModule R A I
  letI := leftHomGroupModule R A I'
  refine
    { toFun := fun f => f ≫ g
      map_add' := fun f f' =>
        Preadditive.add_comp
          ((forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v}).obj A) I I' f f' g
      map_smul' := ?_ }
  intro r f
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  change g.hom ((r • f).hom a) = (r • (f ≫ g)).hom a
  rw [leftHomGroupModule_smul_apply, leftHomGroupModule_smul_apply]
  rfl

/-- The original Hom objects and postcomposition maps form the actual right adjoint. -/
def leftHomGroupFunctor (A : ModuleCat.{v} Rᵐᵒᵖ) :
    AddCommGrpCat.{v} ⥤ ModuleCat.{v} R where
  obj I := by
    letI := leftHomGroupModule R A I
    exact ModuleCat.of R ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I)
  map {I I'} g := by
    letI : Module R
        ((forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v}).obj A ⟶ I) :=
      leftHomGroupModule R A I
    letI : Module R
        ((forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v}).obj A ⟶ I') :=
      leftHomGroupModule R A I'
    exact ModuleCat.ofHom (leftHomGroupMap R A g)
  map_id I := by
    let : Module R
        ((forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v}).obj A ⟶ I) :=
      leftHomGroupModule R A I
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change f ≫ 𝟙 I = f
    exact Category.comp_id f
  map_comp {I I' I''} g h := by
    let : Module R
        ((forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v}).obj A ⟶ I) :=
      leftHomGroupModule R A I
    let : Module R
        ((forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v}).obj A ⟶ I') :=
      leftHomGroupModule R A I'
    let : Module R
        ((forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v}).obj A ⟶ I'') :=
      leftHomGroupModule R A I''
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change f ≫ (g ≫ h) = (f ≫ g) ≫ h
    exact (Category.assoc f g h).symm

/-- The actual native Hom functor map retains additive postcomposition on every value. -/
theorem leftHomGroupFunctor_map_apply (A : ModuleCat.{v} Rᵐᵒᵖ)
    {I I' : AddCommGrpCat.{v}} (g : I ⟶ I')
    (h : (leftHomGroupFunctor R A).obj I) (a : A) :
    (((leftHomGroupFunctor R A).map g).hom h).hom a = g.hom (h.hom a) := rfl

/-- The existing pure-evaluation curry/uncurry maps are inverse on the original objects. -/
def groupLeftTensorHomEquiv (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R)
    (I : AddCommGrpCat.{v}) :
    (((groupBifunctor R).obj A).obj B ⟶ I) ≃
      (B ⟶ (leftHomGroupFunctor R A).obj I) := by
  letI : Module R
      ((forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v}).obj A ⟶ I) :=
    leftHomGroupModule R A I
  exact
    { toFun := fun f => ModuleCat.ofHom (groupCurryLeft R A B I f)
      invFun := fun g => groupUncurryLeft R A B I g.hom
      left_inv := fun f => by
        let c := groupCurryLeft R A B I f
        let F : B ⟶ (leftHomGroupFunctor R A).obj I := ModuleCat.ofHom c
        let L : B →ₗ[R] ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I) := by
          let F₀ := F
          dsimp only [leftHomGroupFunctor] at F₀
          exact F₀.hom
        have hL : L = c := by
          simpa only [L, F, leftHomGroupFunctor] using ModuleCat.hom_ofHom c
        apply groupHom_ext R A B I
        intro a b
        let : Module ℤ B := Module.compHom B (algebraMap ℤ R)
        let z : ((groupBifunctor R).obj A).obj B := groupPure R A B a b
        have hTransport := congrArg
          (fun q : B →ₗ[R] ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I) =>
            (groupUncurryLeft R A B I q).hom z) hL
        have hValue := (groupUncurryLeft_mk R A B I c a b).trans
          (groupCurryLeft_mk R A B I f a b)
        simpa only [F, L, c, z, groupPure, leftHomGroupFunctor] using
          hTransport.trans hValue
      right_inv := fun g => by
        let L : B →ₗ[R] ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I) := by
          let g₀ := g
          dsimp only [leftHomGroupFunctor] at g₀
          exact g₀.hom
        let u := groupUncurryLeft R A B I L
        let c := groupCurryLeft R A B I u
        have hRaw : c = L := by
          apply LinearMap.ext
          intro b
          apply AddCommGrpCat.hom_ext
          apply AddMonoidHom.ext
          intro a
          exact (groupCurryLeft_mk R A B I u a b).trans
            (groupUncurryLeft_mk R A B I L a b)
        have hPack := congrArg
          (fun q : B →ₗ[R] ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I) =>
            (show B ⟶ (leftHomGroupFunctor R A).obj I from ModuleCat.ofHom q)) hRaw
        have hG : (ModuleCat.ofHom L : B ⟶ (leftHomGroupFunctor R A).obj I) = g := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro b
          rfl
        simpa only [u, c, L, leftHomGroupFunctor] using hPack.trans hG
    }

/-- The actual native hom-set equivalence evaluates the original pure tensor function. -/
theorem groupLeftTensorHomEquiv_apply (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R)
    (I : AddCommGrpCat.{v}) (f : ((groupBifunctor R).obj A).obj B ⟶ I) (b : B) (a : A) :
    (((groupLeftTensorHomEquiv R A B I) f).hom b).hom a =
      f.hom (groupPure R A B a b) := by
  let := leftHomGroupModule R A I
  let E := groupLeftTensorHomEquiv R A B I
  let F : B ⟶ (leftHomGroupFunctor R A).obj I := E.toFun f
  let c := groupCurryLeft R A B I f
  let C : B ⟶ (leftHomGroupFunctor R A).obj I := ModuleCat.ofHom c
  have hApply : E f = F := rfl
  have hPack : F = C := rfl
  have hValue := congrArg
    (fun m : B ⟶ (leftHomGroupFunctor R A).obj I => (m.hom b).hom a)
    (hApply.trans hPack)
  have hRaw : (C.hom b).hom a = (c b).hom a :=
    congrArg
      (fun L : B →ₗ[R] ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I) =>
        (L b).hom a) (ModuleCat.hom_ofHom c)
  exact hValue.trans (hRaw.trans (groupCurryLeft_mk R A B I f a b))

/-- The inverse native hom-set equivalence retains the original two-variable evaluation. -/
theorem groupLeftTensorHomEquiv_symm_apply (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R)
    (I : AddCommGrpCat.{v}) (g : B ⟶ (leftHomGroupFunctor R A).obj I) (a : A) (b : B) :
    ((groupLeftTensorHomEquiv R A B I).symm g).hom (groupPure R A B a b) =
      (g.hom b).hom a := by
  let := leftHomGroupModule R A I
  let E := groupLeftTensorHomEquiv R A B I
  let L : B →ₗ[R] ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I) := by
    let g₀ := g
    dsimp only [leftHomGroupFunctor] at g₀
    exact g₀.hom
  let F : ((groupBifunctor R).obj A).obj B ⟶ I := E.invFun g
  let C : ((groupBifunctor R).obj A).obj B ⟶ I := groupUncurryLeft R A B I L
  have hApply : E.symm g = F := rfl
  have hPack : F = C := rfl
  have hValue := congrArg
    (fun m : ((groupBifunctor R).obj A).obj B ⟶ I => m.hom (groupPure R A B a b))
    (hApply.trans hPack)
  have hRaw : (L b).hom a = (g.hom b).hom a := rfl
  exact hValue.trans ((groupUncurryLeft_mk R A B I L a b).trans hRaw)

/-- The computed group tensor is left adjoint to the computed original-domain Hom functor. -/
def groupLeftTensorAdjunction (A : ModuleCat.{v} Rᵐᵒᵖ) :
    (groupBifunctor R).obj A ⊣ leftHomGroupFunctor R A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun B I => groupLeftTensorHomEquiv R A B I
      homEquiv_naturality_left_symm := by
        intro B B' I f g
        apply groupHom_ext R A B I
        intro a b
        let : Module ℤ B := Module.compHom B (algebraMap ℤ R)
        let : Module ℤ B' := Module.compHom B' (algebraMap ℤ R)
        let := leftHomGroupModule R A I
        let z : ((groupBifunctor R).obj A).obj B := groupPure R A B a b
        let z' : ((groupBifunctor R).obj A).obj B' := groupPure R A B' a (f.hom b)
        let t : ((groupBifunctor R).obj A).obj B ⟶
            ((groupBifunctor R).obj A).obj B' := ((groupBifunctor R).obj A).map f
        let w := (groupLeftTensorHomEquiv R A B' I).symm g
        have hMap : t.hom z = z' := by
          change (((groupBifunctor R).obj A).map f).hom
            (TensorProduct.Balanced.mk ℤ R A B a b) =
              TensorProduct.Balanced.mk ℤ R A B' a (f.hom b)
          exact groupBifunctor_obj_map_mk R A f a b
        have hLeft := groupLeftTensorHomEquiv_symm_apply R A B I (f ≫ g) a b
        have hRight := groupLeftTensorHomEquiv_symm_apply R A B' I g a (f.hom b)
        have hComp : (f ≫ g).hom b = g.hom (f.hom b) :=
          (DFunLike.congr_fun (ModuleCat.hom_comp f g) b).trans
            (LinearMap.comp_apply g.hom f.hom b)
        have hValue := congrArg
          (fun h : (leftHomGroupFunctor R A).obj I =>
            (show (forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I from h).hom a) hComp
        have hEval : (t ≫ w).hom z = w.hom (t.hom z) :=
          (DFunLike.congr_fun (AddCommGrpCat.hom_comp t w) z).trans
            (AddMonoidHom.comp_apply w.hom t.hom z)
        exact hLeft.trans (hValue.trans (hRight.symm.trans
          ((congrArg w.hom hMap.symm).trans hEval.symm)))
      homEquiv_naturality_right := by
        intro B I I' f g
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro b
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro a
        let := leftHomGroupModule R A I
        let := leftHomGroupModule R A I'
        let : Module ℤ B := Module.compHom B (algebraMap ℤ R)
        let z : ((groupBifunctor R).obj A).obj B := groupPure R A B a b
        let F := (groupLeftTensorHomEquiv R A B I) f
        let G := (leftHomGroupFunctor R A).map g
        have hLeft := groupLeftTensorHomEquiv_apply R A B I' (f ≫ g) b a
        have hFirst := groupLeftTensorHomEquiv_apply R A B I f b a
        have hMap := leftHomGroupFunctor_map_apply R A g (F.hom b) a
        have hComp : (F ≫ G).hom b = G.hom (F.hom b) :=
          (DFunLike.congr_fun (ModuleCat.hom_comp F G) b).trans
            (LinearMap.comp_apply G.hom F.hom b)
        have hValue := congrArg
          (fun h : (leftHomGroupFunctor R A).obj I' =>
            (show (forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I' from h).hom a) hComp
        have hEval : (f ≫ g).hom z = g.hom (f.hom z) :=
          (DFunLike.congr_fun (AddCommGrpCat.hom_comp f g) z).trans
            (AddMonoidHom.comp_apply g.hom f.hom z)
        exact hLeft.trans (hEval.trans ((congrArg g.hom hFirst.symm).trans
          (hMap.symm.trans hValue.symm))) }

/-- Right exactness of the actual second-variable tensor is earned by its adjunction. -/
instance groupBifunctor_obj_isLeftAdjoint (A : ModuleCat.{v} Rᵐᵒᵖ) :
    ((groupBifunctor R).obj A).IsLeftAdjoint :=
  ⟨leftHomGroupFunctor R A, ⟨groupLeftTensorAdjunction R A⟩⟩

/-- Original-domain group Hom postcomposition with its existing Rᵐᵒᵖ action. -/
def rightHomGroupMap (B : ModuleCat.{v} R) {I I' : AddCommGrpCat.{v}} (g : I ⟶ I') :
    letI := ChainComplex.homGroupModule R B I
    letI := ChainComplex.homGroupModule R B I'
    ((forget₂ (ModuleCat R) AddCommGrpCat).obj B ⟶ I) →ₗ[Rᵐᵒᵖ]
      ((forget₂ (ModuleCat R) AddCommGrpCat).obj B ⟶ I') := by
  letI := ChainComplex.homGroupModule R B I
  letI := ChainComplex.homGroupModule R B I'
  refine
    { toFun := fun f => f ≫ g
      map_add' := fun f f' =>
        Preadditive.add_comp
          ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj B) I I' f f' g
      map_smul' := ?_ }
  intro r f
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro b
  change g.hom ((r • f).hom b) = (r • (f ≫ g)).hom b
  rw [ChainComplex.homGroupModule_smul_apply, ChainComplex.homGroupModule_smul_apply]
  rfl

/-- The actual native right-domain Hom right adjoint in the first tensor variable. -/
def rightHomGroupFunctor (B : ModuleCat.{v} R) :
    AddCommGrpCat.{v} ⥤ ModuleCat.{v} Rᵐᵒᵖ where
  obj I := by
    letI := ChainComplex.homGroupModule R B I
    exact ModuleCat.of Rᵐᵒᵖ ((forget₂ (ModuleCat R) AddCommGrpCat).obj B ⟶ I)
  map {I I'} g := by
    letI : Module Rᵐᵒᵖ
        ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj B ⟶ I) :=
      ChainComplex.homGroupModule R B I
    letI : Module Rᵐᵒᵖ
        ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj B ⟶ I') :=
      ChainComplex.homGroupModule R B I'
    exact ModuleCat.ofHom (rightHomGroupMap R B g)
  map_id I := by
    let : Module Rᵐᵒᵖ
        ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj B ⟶ I) :=
      ChainComplex.homGroupModule R B I
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact Category.comp_id f
  map_comp {I I' I''} g h := by
    let : Module Rᵐᵒᵖ
        ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj B ⟶ I) :=
      ChainComplex.homGroupModule R B I
    let : Module Rᵐᵒᵖ
        ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj B ⟶ I') :=
      ChainComplex.homGroupModule R B I'
    let : Module Rᵐᵒᵖ
        ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj B ⟶ I'') :=
      ChainComplex.homGroupModule R B I''
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (Category.assoc f g h).symm

/-- The actual right-domain Hom functor map retains original additive postcomposition. -/
theorem rightHomGroupFunctor_map_apply (B : ModuleCat.{v} R)
    {I I' : AddCommGrpCat.{v}} (g : I ⟶ I')
    (h : (rightHomGroupFunctor R B).obj I) (b : B) :
    (((rightHomGroupFunctor R B).map g).hom h).hom b = g.hom (h.hom b) := rfl

/-- The proved original group currying supplies the actual first-variable hom-set equivalence. -/
def groupRightTensorHomEquiv (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R)
    (I : AddCommGrpCat.{v}) :
    (((groupBifunctor R).obj A).obj B ⟶ I) ≃
      (A ⟶ (rightHomGroupFunctor R B).obj I) := by
  letI : Module Rᵐᵒᵖ
      ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj B ⟶ I) :=
    ChainComplex.homGroupModule R B I
  exact
    { toFun := fun f => ModuleCat.ofHom (groupCurry R A B I f)
      invFun := fun g => groupUncurry R A B I g.hom
      left_inv := fun f => by
        let c := groupCurry R A B I f
        let F : A ⟶ (rightHomGroupFunctor R B).obj I := ModuleCat.ofHom c
        let L : A →ₗ[Rᵐᵒᵖ] ((forget₂ (ModuleCat R) AddCommGrpCat).obj B ⟶ I) := by
          let F₀ := F
          dsimp only [rightHomGroupFunctor] at F₀
          exact F₀.hom
        have hL : L = c := by
          simpa only [L, F, rightHomGroupFunctor] using ModuleCat.hom_ofHom c
        apply groupHom_ext R A B I
        intro a b
        let : Module ℤ B := Module.compHom B (algebraMap ℤ R)
        let z : ((groupBifunctor R).obj A).obj B := groupPure R A B a b
        have hTransport := congrArg
          (fun q : A →ₗ[Rᵐᵒᵖ] ((forget₂ (ModuleCat R) AddCommGrpCat).obj B ⟶ I) =>
            (groupUncurry R A B I q).hom z) hL
        have hValue := (groupUncurry_mk R A B I c a b).trans
          (groupCurry_mk R A B I f a b)
        simpa only [F, L, c, z, rightHomGroupFunctor, groupPure] using
          hTransport.trans hValue
      right_inv := fun g => by
        let L : A →ₗ[Rᵐᵒᵖ] ((forget₂ (ModuleCat R) AddCommGrpCat).obj B ⟶ I) := by
          let g₀ := g
          dsimp only [rightHomGroupFunctor] at g₀
          exact g₀.hom
        let u := groupUncurry R A B I L
        let c := groupCurry R A B I u
        have hRaw : c = L := by
          apply LinearMap.ext
          intro a
          apply AddCommGrpCat.hom_ext
          apply AddMonoidHom.ext
          intro b
          exact (groupCurry_mk R A B I u a b).trans
            (groupUncurry_mk R A B I L a b)
        have hPack := congrArg
          (fun q : A →ₗ[Rᵐᵒᵖ] ((forget₂ (ModuleCat R) AddCommGrpCat).obj B ⟶ I) =>
            (show A ⟶ (rightHomGroupFunctor R B).obj I from ModuleCat.ofHom q)) hRaw
        have hG : (ModuleCat.ofHom L : A ⟶ (rightHomGroupFunctor R B).obj I) = g := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro a
          rfl
        simpa only [u, c, L, rightHomGroupFunctor] using hPack.trans hG
    }

/-- The actual native first-variable hom-set equivalence keeps the original tensor value. -/
theorem groupRightTensorHomEquiv_apply (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R)
    (I : AddCommGrpCat.{v}) (f : ((groupBifunctor R).obj A).obj B ⟶ I) (a : A) (b : B) :
    (((groupRightTensorHomEquiv R A B I) f).hom a).hom b =
      f.hom (groupPure R A B a b) := by
  let := ChainComplex.homGroupModule R B I
  let : Module ℤ B := Module.compHom B (algebraMap ℤ R)
  let E := groupRightTensorHomEquiv R A B I
  let F : A ⟶ (rightHomGroupFunctor R B).obj I := E.toFun f
  let c := groupCurry R A B I f
  let C : A ⟶ (rightHomGroupFunctor R B).obj I := ModuleCat.ofHom c
  have hApply : E f = F := rfl
  have hPack : F = C := rfl
  have hValue := congrArg
    (fun m : A ⟶ (rightHomGroupFunctor R B).obj I => (m.hom a).hom b)
    (hApply.trans hPack)
  have hRaw : (C.hom a).hom b = (c a).hom b :=
    congrArg
      (fun L : A →ₗ[Rᵐᵒᵖ] ((forget₂ (ModuleCat R) AddCommGrpCat).obj B ⟶ I) =>
        (L a).hom b) (ModuleCat.hom_ofHom c)
  exact hValue.trans (hRaw.trans (groupCurry_mk R A B I f a b))

/-- The inverse native first-variable hom-set map keeps the original function evaluation. -/
theorem groupRightTensorHomEquiv_symm_apply (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R)
    (I : AddCommGrpCat.{v}) (g : A ⟶ (rightHomGroupFunctor R B).obj I) (a : A) (b : B) :
    ((groupRightTensorHomEquiv R A B I).symm g).hom (groupPure R A B a b) =
      (g.hom a).hom b := by
  let := ChainComplex.homGroupModule R B I
  let : Module ℤ B := Module.compHom B (algebraMap ℤ R)
  let E := groupRightTensorHomEquiv R A B I
  let L : A →ₗ[Rᵐᵒᵖ] ((forget₂ (ModuleCat R) AddCommGrpCat).obj B ⟶ I) := by
    let g₀ := g
    dsimp only [rightHomGroupFunctor] at g₀
    exact g₀.hom
  let F : ((groupBifunctor R).obj A).obj B ⟶ I := E.invFun g
  let C : ((groupBifunctor R).obj A).obj B ⟶ I := groupUncurry R A B I L
  have hApply : E.symm g = F := rfl
  have hPack : F = C := rfl
  have hValue := congrArg
    (fun m : ((groupBifunctor R).obj A).obj B ⟶ I => m.hom (groupPure R A B a b))
    (hApply.trans hPack)
  have hRaw : (L a).hom b = (g.hom a).hom b := rfl
  exact hValue.trans ((groupUncurry_mk R A B I L a b).trans hRaw)

/-- Both first-variable adjunction maps are the existing original group maps. -/
def groupRightTensorAdjunction (B : ModuleCat.{v} R) :
    (groupBifunctor R).flip.obj B ⊣ rightHomGroupFunctor R B :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A I => groupRightTensorHomEquiv R A B I
      homEquiv_naturality_left_symm := by
        intro A A' I f g
        apply groupHom_ext R A B I
        intro a b
        let : Module ℤ B := Module.compHom B (algebraMap ℤ R)
        let := ChainComplex.homGroupModule R B I
        let z : ((groupBifunctor R).obj A).obj B := groupPure R A B a b
        let z' : ((groupBifunctor R).obj A').obj B := groupPure R A' B (f.hom a) b
        let t : ((groupBifunctor R).obj A).obj B ⟶
            ((groupBifunctor R).obj A').obj B := ((groupBifunctor R).map f).app B
        let w := (groupRightTensorHomEquiv R A' B I).symm g
        have hMap : t.hom z = z' := by
          change (((groupBifunctor R).map f).app B).hom
            (TensorProduct.Balanced.mk ℤ R A B a b) =
              TensorProduct.Balanced.mk ℤ R A' B (f.hom a) b
          exact groupBifunctor_map_mk R f B a b
        have hLeft := groupRightTensorHomEquiv_symm_apply R A B I (f ≫ g) a b
        have hRight := groupRightTensorHomEquiv_symm_apply R A' B I g (f.hom a) b
        have hComp : (f ≫ g).hom a = g.hom (f.hom a) :=
          (DFunLike.congr_fun (ModuleCat.hom_comp f g) a).trans
            (LinearMap.comp_apply g.hom f.hom a)
        have hValue := congrArg
          (fun h : (rightHomGroupFunctor R B).obj I =>
            (show (forget₂ (ModuleCat R) AddCommGrpCat).obj B ⟶ I from h).hom b) hComp
        have hEval : (t ≫ w).hom z = w.hom (t.hom z) :=
          (DFunLike.congr_fun (AddCommGrpCat.hom_comp t w) z).trans
            (AddMonoidHom.comp_apply w.hom t.hom z)
        exact hLeft.trans (hValue.trans (hRight.symm.trans
          ((congrArg w.hom hMap.symm).trans hEval.symm)))
      homEquiv_naturality_right := by
        intro A I I' f g
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro b
        let := ChainComplex.homGroupModule R B I
        let := ChainComplex.homGroupModule R B I'
        let : Module ℤ B := Module.compHom B (algebraMap ℤ R)
        let z : ((groupBifunctor R).obj A).obj B := groupPure R A B a b
        let F := (groupRightTensorHomEquiv R A B I) f
        let G := (rightHomGroupFunctor R B).map g
        have hLeft := groupRightTensorHomEquiv_apply R A B I' (f ≫ g) a b
        have hFirst := groupRightTensorHomEquiv_apply R A B I f a b
        have hMap := rightHomGroupFunctor_map_apply R B g (F.hom a) b
        have hComp : (F ≫ G).hom a = G.hom (F.hom a) :=
          (DFunLike.congr_fun (ModuleCat.hom_comp F G) a).trans
            (LinearMap.comp_apply G.hom F.hom a)
        have hValue := congrArg
          (fun h : (rightHomGroupFunctor R B).obj I' =>
            (show (forget₂ (ModuleCat R) AddCommGrpCat).obj B ⟶ I' from h).hom b) hComp
        have hEval : (f ≫ g).hom z = g.hom (f.hom z) :=
          (DFunLike.congr_fun (AddCommGrpCat.hom_comp f g) z).trans
            (AddMonoidHom.comp_apply g.hom f.hom z)
        exact hLeft.trans (hEval.trans ((congrArg g.hom hFirst.symm).trans
          (hMap.symm.trans hValue.symm))) }

/-- Right exactness in the first tensor variable follows from the actual adjunction. -/
instance groupBifunctor_flip_obj_isLeftAdjoint (B : ModuleCat.{v} R) :
    ((groupBifunctor R).flip.obj B).IsLeftAdjoint :=
  ⟨rightHomGroupFunctor R B, ⟨groupRightTensorAdjunction R B⟩⟩

end ModuleCat.BalancedTensor
