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
# Balanced tensor–Hom adjunctions in both module variables

Let `A` be a right `R`-module, `B` a left `R`-module, and `I` an additive commutative group.
The additive Hom group from `A` to `I` has left action `(r h)(a) = h(a r)`, while the Hom
group from `B` to `I` has right action `(h r)(b) = h(r b)`.

Evaluation identifies additive maps `A ⊗_R B → I` with `R`-linear maps `B → Hom_ℤ(A, I)` and
with `Rᵐᵒᵖ`-linear maps `A → Hom_ℤ(B, I)`. These coordinates are natural and give a right
adjoint to balanced tensor in each module variable. The Hom functors act on target-group maps
by postcomposition. The common carrier universe is independent of the ring universe.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite

universe u v

namespace ModuleCat.BalancedTensor

variable (R : Type u) [Ring R]

/-- Pure element of the group-valued balanced tensor.

For a right module `A`, a left module `B`, and elements `a` and `b`, `groupPure R A B a b` is
the integer-ground balanced class `[a ⊗ b]`. -/
def groupPure (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R) (a : A) (b : B) :
    ((groupBifunctor R).obj A).obj B := by
  letI : Module ℤ B := Module.compHom B (algebraMap ℤ R)
  exact TensorProduct.Balanced.mk ℤ R A B a b

/-- Left R action on additive Hom from a right module.

For a right `R`-module `A`, the additive maps from `A` to `I` form a left `R`-module by domain
precomposition. The action is obtained from the right-domain action and the double-opposite
ring equivalence. -/
def leftHomGroupModule (A : ModuleCat.{v} Rᵐᵒᵖ) (I : AddCommGrpCat.{v}) :
    Module R ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I) := by
  letI := ChainComplex.homGroupModule Rᵐᵒᵖ A I
  exact Module.compHom _ (RingEquiv.opOp R).toRingHom

/-- Left Hom action evaluates by the right domain action.

For `r : R`, an additive map `f : A → I`, and `a : A`, the induced left Hom action satisfies
`(r • f)(a) = f(op r • a)`. -/
theorem leftHomGroupModule_smul_apply (A : ModuleCat.{v} Rᵐᵒᵖ)
    (I : AddCommGrpCat.{v}) (r : R)
    (f : (forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I) (a : A) :
    letI := leftHomGroupModule R A I
    (r • f).hom a = f.hom (op r • a) := by
  let := ChainComplex.homGroupModule Rᵐᵒᵖ A I
  let := leftHomGroupModule R A I
  change (op (op r) • f).hom a = f.hom (op r • a)
  exact ChainComplex.homGroupModule_smul_apply Rᵐᵒᵖ A I (op (op r)) f a

/-- Left-linear precomposition on Hom from right modules.

A right-module morphism `g : A' ⟶ A` induces an `R`-linear map from additive maps `A → I` to
additive maps `A' → I` by precomposition. -/
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

/-- Evaluation of Hom precomposition from a right-module domain.

For an additive map `f : A → I` and `a : A'`, the precomposition map evaluates as `f(g a)`. -/
theorem leftHomGroupPrecomp_apply {A A' : ModuleCat.{v} Rᵐᵒᵖ} (g : A' ⟶ A)
    (I : AddCommGrpCat.{v})
    (f : (forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I) (a : A') :
    letI := leftHomGroupModule R A I
    letI := leftHomGroupModule R A' I
    (leftHomGroupPrecomp R g I f).hom a = f.hom (g.hom a) := rfl

/-- Currying a balanced tensor map in the left-module variable.

An additive map `f : A ⊗_R B → I` gives an `R`-linear map from `B` to additive maps `A → I`,
with the left action defined by precomposition using the right action on `A`. -/
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

/-- Left-variable currying evaluates on pure tensor classes.

For `a : A` and `b : B`, the map obtained by left-variable currying satisfies `(groupCurryLeft
f b)(a) = f([a ⊗ b])`. -/
theorem groupCurryLeft_mk (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R)
    (I : AddCommGrpCat.{v}) (f : ((groupBifunctor R).obj A).obj B ⟶ I) (a : A) (b : B) :
    letI := leftHomGroupModule R A I
    (groupCurryLeft R A B I f b).hom a = f.hom (groupPure R A B a b) := rfl

/-- Transposing a left-linear map into an additive Hom group.

A left-linear map `g : B → Hom_ℤ(A, I)` transposes to a right-linear map `A → Hom_ℤ(B, I)` by
interchanging its two evaluation variables. -/
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

/-- Uncurrying a left-linear map to an additive Hom group.

An `R`-linear map `B → Hom_ℤ(A, I)` defines an additive map from `A ⊗_R B` to `I`, by
transposition and balanced evaluation. -/
def groupUncurryLeft (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R)
    (I : AddCommGrpCat.{v})
    (g : letI := leftHomGroupModule R A I
      B →ₗ[R] ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I)) :
    ((groupBifunctor R).obj A).obj B ⟶ I :=
  groupUncurry R A B I (transposeLeftHom R A B I g)

/-- Left-variable uncurrying on pure tensor classes.

For a left-linear map `g : B → Hom_ℤ(A, I)`, the uncurried map sends `[a ⊗ b]` to `(g b)(a)`. -/
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

/-- Left-linear postcomposition on additive Hom groups.

A target-group morphism `g : I ⟶ I'` induces an `R`-linear map `Hom_ℤ(A, I) → Hom_ℤ(A, I')` by
postcomposition, for fixed right module `A`. -/
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

/-- Additive Hom from a right module as a left-module-valued functor.

For a fixed right `R`-module `A`, the functor from additive groups to left `R`-modules takes
`I` to `Hom_ℤ(A, I)` with domain-precomposition action and sends target maps to
postcomposition. -/
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

/-- Target map formula for the left-module-valued Hom functor.

For `g : I ⟶ I'`, an additive map `h : A → I`, and `a : A`, the Hom functor's image of `g`
evaluates as `g(h a)`. -/
theorem leftHomGroupFunctor_map_apply (A : ModuleCat.{v} Rᵐᵒᵖ)
    {I I' : AddCommGrpCat.{v}} (g : I ⟶ I')
    (h : (leftHomGroupFunctor R A).obj I) (a : A) :
    (((leftHomGroupFunctor R A).map g).hom h).hom a = g.hom (h.hom a) := rfl

/-- Hom-set equivalence for tensor in the left-module variable.

Additive maps `A ⊗_R B → I` are in bijection with morphisms `B ⟶ (leftHomGroupFunctor R A).obj
I` of left `R`-modules. -/
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

/-- Forward left-variable tensor–Hom equivalence on elements.

The morphism corresponding to an additive tensor map `f`, evaluated first at `b` and then at
`a`, gives `f([a ⊗ b])`. -/
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

/-- Inverse left-variable tensor–Hom equivalence on pure classes.

The additive tensor map corresponding to a left-module morphism `g : B ⟶ Hom_ℤ(A, I)` sends
`[a ⊗ b]` to `(g b)(a)`. -/
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

/-- Balanced tensor with fixed right factor has an additive Hom right adjoint.

For a fixed right module `A`, the functor `A ⊗_R -` to additive groups is left adjoint to
`leftHomGroupFunctor R A`. -/
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

/-- Tensoring with a fixed right module is a left adjoint.

For every right `R`-module `A`, the group-valued functor `(groupBifunctor R).obj A` is a left
adjoint, with right adjoint the left-module-valued additive Hom functor. -/
instance groupBifunctor_obj_isLeftAdjoint (A : ModuleCat.{v} Rᵐᵒᵖ) :
    ((groupBifunctor R).obj A).IsLeftAdjoint :=
  ⟨leftHomGroupFunctor R A, ⟨groupLeftTensorAdjunction R A⟩⟩

/-- Right-linear postcomposition on additive Hom groups.

A target-group morphism `g : I ⟶ I'` gives an `Rᵐᵒᵖ`-linear map `Hom_ℤ(B, I) → Hom_ℤ(B, I')`
by postcomposition, for fixed left module `B`. -/
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

/-- Additive Hom from a left module as a right-module-valued functor.

For fixed left `R`-module `B`, the functor from additive groups to right `R`-modules takes `I`
to `Hom_ℤ(B, I)` with domain-precomposition action and acts on target maps by postcomposition. -/
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

/-- Target map formula for the right-module-valued Hom functor.

For `g : I ⟶ I'`, an additive map `h : B → I`, and `b : B`, the right-module-valued Hom
functor's image of `g` evaluates as `g(h b)`. -/
theorem rightHomGroupFunctor_map_apply (B : ModuleCat.{v} R)
    {I I' : AddCommGrpCat.{v}} (g : I ⟶ I')
    (h : (rightHomGroupFunctor R B).obj I) (b : B) :
    (((rightHomGroupFunctor R B).map g).hom h).hom b = g.hom (h.hom b) := rfl

/-- Hom-set equivalence for tensor in the right-module variable.

Additive maps `A ⊗_R B → I` are in bijection with right-module morphisms `A ⟶
(rightHomGroupFunctor R B).obj I`. -/
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

/-- Forward right-variable tensor–Hom equivalence on elements.

The right-module morphism corresponding to an additive tensor map `f`, evaluated first at `a`
and then at `b`, gives `f([a ⊗ b])`. -/
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

/-- Inverse right-variable tensor–Hom equivalence on pure classes.

The additive tensor map corresponding to a right-module morphism `g : A ⟶ Hom_ℤ(B, I)` sends
`[a ⊗ b]` to `(g a)(b)`. -/
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

/-- Balanced tensor with fixed left factor has an additive Hom right adjoint.

For a fixed left `R`-module `B`, the functor `- ⊗_R B` from right modules to additive groups
is left adjoint to `rightHomGroupFunctor R B`. -/
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

/-- Tensoring with a fixed left module is a left adjoint.

For every left `R`-module `B`, the group-valued tensor functor with fixed left factor is a
left adjoint, with right adjoint the right-module-valued additive Hom functor. -/
instance groupBifunctor_flip_obj_isLeftAdjoint (B : ModuleCat.{v} R) :
    ((groupBifunctor R).flip.obj B).IsLeftAdjoint :=
  ⟨rightHomGroupFunctor R B, ⟨groupRightTensorAdjunction R B⟩⟩

end ModuleCat.BalancedTensor
