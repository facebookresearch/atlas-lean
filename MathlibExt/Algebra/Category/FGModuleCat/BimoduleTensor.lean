/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import MathlibExt.LinearAlgebra.Bimodule.TensorProduct
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorLeft
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.Flat
public import MathlibExt.Algebra.Module.NatInt
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors
public import Mathlib.Algebra.Module.Equiv.Opposite
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Associator
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorLeft.Morita
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.MoritaFinite
public import MathlibExt.RingTheory.Morita.Finite
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Finite-module tensor functors of noncommutative bimodules

Left finiteness of the coefficient makes the balanced tensor functor
finite-module-valued. Right-module Tor₁ vanishing implies preservation of
short exact sequences in the ambient module categories.
The acting rings are arbitrary associative rings.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MulOpposite

universe u

attribute [local instance] ModuleCat.BalancedTensor.Left.additive

namespace ModuleCat

variable {R S : Type u} [Ring R] [Ring S]
  (E : Type u) [AddCommGroup E] [Module S E] [Module Rᵐᵒᵖ E]
  [SMulCommClass S Rᵐᵒᵖ E]

/-- Original tensor output is finite over S when its coefficient and input are finite. -/
theorem isFG_bimoduleTensor [Module.Finite S E] (N : ModuleCat.{u} R)
    (hN : isFG R N) :
    isFG S ((BalancedTensor.Left.functor ℤ R S E).obj N) := by
  let : Module.Finite R N := hN
  let d : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  let d₀ : Module ℤ N := AddCommGroup.toIntModule N
  let P : Module ℤ N → Prop := fun d' =>
    letI := d'
    letI := TensorProduct.Balanced.leftModule ℤ R S E N
    Module.Finite S (TensorProduct.Balanced ℤ R E N)
  have h₀ : P d₀ := TensorProduct.Balanced.finite_left R S E N
  change P d
  exact (congrArg P (Subsingleton.elim d₀ d)).mp h₀

/-- Forgetting the actual outer module retains the existing original group tensor functor. -/
theorem bimoduleTensor_comp_forgetToGroup :
    BalancedTensor.Left.functor ℤ R S E ⋙
        forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u} =
      (BalancedTensor.groupBifunctor R).obj (ModuleCat.of Rᵐᵒᵖ E) := by
  rfl

/-- The actual S-module tensor functor preserves finite colimits by its original group action. -/
theorem bimoduleTensor_preservesFiniteColimits :
    PreservesFiniteColimits
      (BalancedTensor.Left.functor ℤ R S E : ModuleCat.{u} R ⥤ ModuleCat.{u} S) := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let U := forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}
  let : PreservesFiniteColimits (F ⋙ U) := by
    rw [bimoduleTensor_comp_forgetToGroup]
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves F U

/-- Canonical right-module Tor₁ vanishing gives finite limit preservation of this same tensor. -/
theorem bimoduleTensor_preservesFiniteLimits_of_torFirst_one
    (hE : ∀ N : ModuleCat.{u} R,
      IsZero (((BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ E)).obj N)) :
    PreservesFiniteLimits
      (BalancedTensor.Left.functor ℤ R S E : ModuleCat.{u} R ⥤ ModuleCat.{u} S) := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let U := forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}
  let : PreservesFiniteLimits (F ⋙ U) := by
    rw [bimoduleTensor_comp_forgetToGroup]
    exact (BalancedTensor.groupBifunctor_obj_preservesFiniteLimits_iff_torFirst_one
      R (ModuleCat.of Rᵐᵒᵖ E)).2 hE
  exact preservesFiniteLimits_of_reflects_of_preserves F U

/-- Every given original short exact row stays short exact under right-flat bimodule tensor. -/
theorem shortExact_bimoduleTensor_of_torFirst_one
    (hE : ∀ N : ModuleCat.{u} R,
      IsZero (((BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ E)).obj N))
    {C : ShortComplex (ModuleCat.{u} R)} (hC : C.ShortExact) :
    (C.map (BalancedTensor.Left.functor ℤ R S E)).ShortExact := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let : F.Additive := BalancedTensor.Left.additive ℤ R S E
  let : PreservesFiniteLimits F := bimoduleTensor_preservesFiniteLimits_of_torFirst_one E hE
  let : PreservesFiniteColimits F := bimoduleTensor_preservesFiniteColimits E
  exact hC.map_of_exact F

end ModuleCat

namespace FGModuleCat

variable {R S : Type u} [Ring R] [Ring S]
  (E : Type u) [AddCommGroup E] [Module S E] [Module Rᵐᵒᵖ E]
  [SMulCommClass S Rᵐᵒᵖ E] [Module.Finite S E]

/-- The existing actual tensor functor restricted to the original finite-module categories. -/
def bimoduleTensor : FGModuleCat.{u} R ⥤ FGModuleCat.{u} S :=
  (ModuleCat.isFG (R := S)).lift
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) ⋙
      ModuleCat.BalancedTensor.Left.functor ℤ R S E)
    (fun X => ModuleCat.isFG_bimoduleTensor E X.obj X.property)

/-- The original output object is literally that of the existing bimodule tensor functor. -/
@[simp]
theorem bimoduleTensor_obj_obj (X : FGModuleCat.{u} R) :
    ((bimoduleTensor E).obj X).obj =
      (ModuleCat.BalancedTensor.Left.functor ℤ R S E).obj X.obj := rfl

/-- Every native finite-module morphism maps through the same original quotient map. -/
@[simp]
theorem bimoduleTensor_map_hom {X Y : FGModuleCat.{u} R} (f : X ⟶ Y) :
    ((bimoduleTensor E).map f).hom =
      (ModuleCat.BalancedTensor.Left.functor ℤ R S E).map f.hom := rfl

/-- Every original pure class follows the actual finite-module tensor map. -/
theorem bimoduleTensor_map_mk {X Y : FGModuleCat.{u} R} (f : X ⟶ Y) (e : E) (x : X) :
    letI : Module ℤ X := Module.compHom X (algebraMap ℤ R)
    letI : Module ℤ Y := Module.compHom Y (algebraMap ℤ R)
    ((bimoduleTensor (R := R) (S := S) E).map f).hom.hom
        (TensorProduct.Balanced.mk ℤ R E X e x) =
      TensorProduct.Balanced.mk ℤ R E Y e (f.hom.hom x) := by
  let : Module ℤ X := Module.compHom X (algebraMap ℤ R)
  let : Module ℤ Y := Module.compHom Y (algebraMap ℤ R)
  exact ModuleCat.BalancedTensor.Left.map_mk ℤ R S E f.hom e x

/-- Forgetting finite generation recovers the whole original module tensor functor. -/
def bimoduleTensorCompForgetIso :
    bimoduleTensor E ⋙ forget₂ (FGModuleCat.{u} S) (ModuleCat.{u} S) ≅
      forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) ⋙
        ModuleCat.BalancedTensor.Left.functor ℤ R S E :=
  (ModuleCat.isFG (R := S)).liftCompιIso
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) ⋙
      ModuleCat.BalancedTensor.Left.functor ℤ R S E)
    (fun X => ModuleCat.isFG_bimoduleTensor E X.obj X.property)

/-- Additivity is inherited from the earned additivity of the original tensor functor. -/
instance bimoduleTensor_additive : (bimoduleTensor (R := R) (S := S) E).Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    change (ModuleCat.BalancedTensor.Left.functor ℤ R S E).map (f.hom + g.hom) =
      (ModuleCat.BalancedTensor.Left.functor ℤ R S E).map f.hom +
        (ModuleCat.BalancedTensor.Left.functor ℤ R S E).map g.hom
    exact Functor.map_add _

/-- The actual finite-module tensor preserves every given ambient short exact row. -/
theorem bimoduleTensor_forget_shortExact_of_torFirst_one
    (hE : ∀ N : ModuleCat.{u} R,
      IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ E)).obj N))
    (C : ShortComplex (FGModuleCat.{u} R))
    (hC : (C.map (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))).ShortExact) :
    ((C.map (bimoduleTensor E)).map
      (forget₂ (FGModuleCat.{u} S) (ModuleCat.{u} S))).ShortExact := by
  change ((C.map (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))).map
    (ModuleCat.BalancedTensor.Left.functor ℤ R S E)).ShortExact
  exact ModuleCat.shortExact_bimoduleTensor_of_torFirst_one E hE hC

end FGModuleCat


namespace ModuleCat

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]
  (E F : Type u) [AddCommGroup E] [AddCommGroup F]
  [Module S E] [Module Rᵐᵒᵖ E] [SMulCommClass S Rᵐᵒᵖ E]
  [Module T F] [Module Sᵐᵒᵖ F] [SMulCommClass T Sᵐᵒᵖ F]

/-- Tensor by the original composite coefficient, with its computed endpoint actions. -/
def bimoduleTensorCompositeFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} T := by
  let C := TensorProduct.Balanced ℤ S F E
  letI : Module T C := TensorProduct.Balanced.leftModule ℤ S T F E
  letI : Module Rᵐᵒᵖ C := TensorProduct.Balanced.rightModule ℤ S R F E
  letI : SMulCommClass T Rᵐᵒᵖ C :=
    TensorProduct.Balanced.leftRightSMulCommClass ℤ S R F E T
  letI : Module ℤ C := AddCommGroup.toIntModule C
  letI : @SMulCommClass T ℤ C (inferInstance : Module T C).toSMul
      (AddCommGroup.toIntModule C).toSMul :=
    Module.intModule_smulCommClass (dM := AddCommGroup.toIntModule C)
  exact BalancedTensor.Left.functor ℤ R T C

/-- The original left-parenthesized triple in tensor by the composite coefficient. -/
def bimoduleTensorCompPure (M : ModuleCat.{u} R) (f : F) (e : E) (m : M) :
    (bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F).obj M := by
  letI : Module ℤ M := Module.compHom M (algebraMap ℤ R)
  let C := TensorProduct.Balanced ℤ S F E
  letI : Module Rᵐᵒᵖ C := TensorProduct.Balanced.rightModule ℤ S R F E
  letI : Module ℤ C := AddCommGroup.toIntModule C
  exact TensorProduct.Balanced.mk ℤ R C M (TensorProduct.Balanced.mk ℤ S F E f e) m

/-- The same ordered triple in the actual successive module tensor functors. -/
def bimoduleTensorDoublePure (M : ModuleCat.{u} R) (f : F) (e : E) (m : M) :
    (BalancedTensor.Left.functor ℤ R S E ⋙ BalancedTensor.Left.functor ℤ S T F).obj M := by
  letI : Module ℤ M := Module.compHom M (algebraMap ℤ R)
  let D := (BalancedTensor.Left.functor ℤ R S E).obj M
  letI : Module ℤ D := Module.compHom D (algebraMap ℤ S)
  exact TensorProduct.Balanced.mk ℤ S F D f (TensorProduct.Balanced.mk ℤ R E M e m)

/-- The actual associator comparison with both original integer-coordinate readouts. -/
def bimoduleTensorCompData (M : ModuleCat.{u} R) :
    {i : (bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F).obj M ≅
        (BalancedTensor.Left.functor ℤ R S E ⋙ BalancedTensor.Left.functor ℤ S T F).obj M //
      ∀ (f : F) (e : E) (m : M),
        i.hom.hom (bimoduleTensorCompPure (S := S) (T := T) E F M f e m) =
          bimoduleTensorDoublePure (S := S) (T := T) E F M f e m} := by
  letI : Module ℤ M := Module.compHom M (algebraMap ℤ R)
  let C := TensorProduct.Balanced ℤ S F E
  let dC : Module ℤ C := inferInstance
  let dC₀ : Module ℤ C := AddCommGroup.toIntModule C
  letI : Module T C := TensorProduct.Balanced.leftModule ℤ S T F E
  letI : Module Rᵐᵒᵖ C := TensorProduct.Balanced.rightModule ℤ S R F E
  letI : SMulCommClass T Rᵐᵒᵖ C :=
    TensorProduct.Balanced.leftRightSMulCommClass ℤ S R F E T
  let KC : Module ℤ C → ModuleCat.{u} T := fun d =>
    letI : Module ℤ C := d
    letI : @SMulCommClass T ℤ C (inferInstance : Module T C).toSMul d.toSMul :=
      Module.intModule_smulCommClass (dM := d)
    letI := TensorProduct.Balanced.leftModule ℤ R T C M
    ModuleCat.of T (TensorProduct.Balanced ℤ R C M)
  let zC : ∀ d : Module ℤ C, F → E → M → KC d := fun d f e m =>
    letI : Module ℤ C := d
    TensorProduct.Balanced.mk ℤ R C M (TensorProduct.Balanced.mk ℤ S F E f e) m
  have compareC (d d' : Module ℤ C) (h : d = d') :
      {i : KC d ≅ KC d' // ∀ (f : F) (e : E) (m : M),
        i.hom.hom (zC d f e m) = zC d' f e m} := by
    cases h
    exact ⟨Iso.refl _, fun _ _ _ => rfl⟩
  let c := compareC dC₀ dC (Subsingleton.elim dC₀ dC)
  let D := TensorProduct.Balanced ℤ R E M
  let dD : Module ℤ D := inferInstance
  letI : Module S D := TensorProduct.Balanced.leftModule ℤ R S E M
  let dD₀ : Module ℤ D := Module.compHom D (algebraMap ℤ S)
  let KD : Module ℤ D → ModuleCat.{u} T := fun d =>
    letI : Module ℤ D := d
    letI := TensorProduct.Balanced.leftModule ℤ S T F D
    ModuleCat.of T (TensorProduct.Balanced ℤ S F D)
  let zD : ∀ d : Module ℤ D, F → E → M → KD d := fun d f e m =>
    letI : Module ℤ D := d
    TensorProduct.Balanced.mk ℤ S F D f (TensorProduct.Balanced.mk ℤ R E M e m)
  have compareD (d d' : Module ℤ D) (h : d = d') :
      {i : KD d ≅ KD d' // ∀ (f : F) (e : E) (m : M),
        i.hom.hom (zD d f e m) = zD d' f e m} := by
    cases h
    exact ⟨Iso.refl _, fun _ _ _ => rfl⟩
  let d := compareD dD dD₀ (Subsingleton.elim dD dD₀)
  letI : Module ℤ C := dC
  letI : @SMulCommClass T ℤ C (inferInstance : Module T C).toSMul dC.toSMul :=
    TensorProduct.Balanced.leftSMulCommClass ℤ S T F E
  letI := TensorProduct.Balanced.leftModule ℤ R T C M
  letI : Module ℤ D := dD
  letI := TensorProduct.Balanced.leftModule ℤ S T F D
  let A := TensorProduct.Balanced.assoc ℤ S R F E M
  let a : KC dC ≃ₗ[T] KD dD :=
    { toFun := A
      invFun := A.symm
      left_inv := A.left_inv
      right_inv := A.right_inv
      map_add' := A.map_add
      map_smul' := fun t x => TensorProduct.Balanced.assoc_left_smul ℤ S R F E M T t x }
  let j : KC dC ≅ KD dD := a.toModuleIso
  let i : (bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F).obj M ≅
      (BalancedTensor.Left.functor ℤ R S E ⋙ BalancedTensor.Left.functor ℤ S T F).obj M :=
    c.1 ≪≫ j ≪≫ d.1
  refine ⟨i, ?_⟩
  intro f e m
  change d.1.hom.hom (A (c.1.hom.hom (zC dC₀ f e m))) = zD dD₀ f e m
  rw [c.2]
  have hA : A (zC dC f e m) = zD dD f e m :=
    TensorProduct.Balanced.assoc_mk_mk ℤ S R F E M f e m
  rw [hA]
  exact d.2 f e m

/-- The whole original module Iso relating composite and successive tensoring. -/
def bimoduleTensorCompIso (M : ModuleCat.{u} R) :
    (bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F).obj M ≅
      (BalancedTensor.Left.functor ℤ R S E ⋙ BalancedTensor.Left.functor ℤ S T F).obj M :=
  (bimoduleTensorCompData (S := S) (T := T) E F M).1

/-- Composite tensoring retains the same ordered three pure factors under the actual comparison. -/
theorem bimoduleTensorCompIso_pure (M : ModuleCat.{u} R) (f : F) (e : E) (m : M) :
    (bimoduleTensorCompIso (S := S) (T := T) E F M).hom.hom
        (bimoduleTensorCompPure (S := S) (T := T) E F M f e m) =
      bimoduleTensorDoublePure (S := S) (T := T) E F M f e m :=
  (bimoduleTensorCompData (S := S) (T := T) E F M).2 f e m

/-- Ordered triple pure classes determine a map from the actual composite tensor object. -/
theorem bimoduleTensorCompHom_ext (M : ModuleCat.{u} R)
    {A : Type*} [AddCommMonoid A]
    {f g : (bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F).obj M →+ A}
    (h : ∀ (a : F) (b : E) (m : M),
      f (bimoduleTensorCompPure (S := S) (T := T) E F M a b m) =
        g (bimoduleTensorCompPure (S := S) (T := T) E F M a b m)) : f = g := by
  let : Module ℤ M := Module.compHom M (algebraMap ℤ R)
  let C := TensorProduct.Balanced ℤ S F E
  let : Module Rᵐᵒᵖ C := TensorProduct.Balanced.rightModule ℤ S R F E
  let : Module ℤ C := AddCommGroup.toIntModule C
  apply TensorProduct.Balanced.addHom_ext ℤ R C M
  intro c m
  have hc : f.comp (((TensorProduct.Balanced.mk ℤ R C M).flip m).toAddMonoidHom) =
      g.comp (((TensorProduct.Balanced.mk ℤ R C M).flip m).toAddMonoidHom) := by
    apply TensorProduct.Balanced.addHom_ext ℤ S F E
    intro a b
    exact h a b m
  exact DFunLike.congr_fun hc c

/-- The composite-coefficient tensor acts on the original module factor in every pure triple. -/
theorem bimoduleTensorCompositeFunctor_map_pure {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (f : F) (e : E) (m : M) :
    ((bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F).map g).hom
        (bimoduleTensorCompPure (S := S) (T := T) E F M f e m) =
      bimoduleTensorCompPure (S := S) (T := T) E F N f e (g.hom m) := by
  let : Module ℤ M := Module.compHom M (algebraMap ℤ R)
  let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  let C := TensorProduct.Balanced ℤ S F E
  let : Module T C := TensorProduct.Balanced.leftModule ℤ S T F E
  let : Module Rᵐᵒᵖ C := TensorProduct.Balanced.rightModule ℤ S R F E
  let : SMulCommClass T Rᵐᵒᵖ C :=
    TensorProduct.Balanced.leftRightSMulCommClass ℤ S R F E T
  let : Module ℤ C := AddCommGroup.toIntModule C
  let : @SMulCommClass T ℤ C (inferInstance : Module T C).toSMul
      (AddCommGroup.toIntModule C).toSMul :=
    Module.intModule_smulCommClass (dM := AddCommGroup.toIntModule C)
  exact BalancedTensor.Left.map_mk ℤ R T C g
    (TensorProduct.Balanced.mk ℤ S F E f e) m

/-- The actual successive functors preserve the same triple and given original module map. -/
theorem bimoduleTensorDouble_map_pure {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (f : F) (e : E) (m : M) :
    ((BalancedTensor.Left.functor ℤ R S E ⋙ BalancedTensor.Left.functor ℤ S T F).map g).hom
        (bimoduleTensorDoublePure (S := S) (T := T) E F M f e m) =
      bimoduleTensorDoublePure (S := S) (T := T) E F N f e (g.hom m) := by
  let : Module ℤ M := Module.compHom M (algebraMap ℤ R)
  let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  let A := (BalancedTensor.Left.functor ℤ R S E).obj M
  let B := (BalancedTensor.Left.functor ℤ R S E).obj N
  let : Module ℤ A := Module.compHom A (algebraMap ℤ S)
  let : Module ℤ B := Module.compHom B (algebraMap ℤ S)
  let a : A := TensorProduct.Balanced.mk ℤ R E M e m
  let b : B := TensorProduct.Balanced.mk ℤ R E N e (g.hom m)
  have hOuter :
      (BalancedTensor.Left.map ℤ S T F (BalancedTensor.Left.map ℤ R S E g)).hom
          (TensorProduct.Balanced.mk ℤ S F A f a) =
        TensorProduct.Balanced.mk ℤ S F B f ((BalancedTensor.Left.map ℤ R S E g).hom a) :=
    BalancedTensor.Left.map_mk (k := ℤ) (R := S) (S := T) (Q := F) (N := A) (N' := B)
      (BalancedTensor.Left.map ℤ R S E g) f a
  have hInner : (BalancedTensor.Left.map ℤ R S E g).hom a = b :=
    BalancedTensor.Left.map_mk (k := ℤ) (R := R) (S := S) (Q := E) (N := M) (N' := N) g e m
  change (BalancedTensor.Left.map ℤ S T F (BalancedTensor.Left.map ℤ R S E g)).hom
      (TensorProduct.Balanced.mk ℤ S F A f a) = TensorProduct.Balanced.mk ℤ S F B f b
  exact hOuter.trans (congrArg (fun x : B => TensorProduct.Balanced.mk ℤ S F B f x) hInner)

/-- The whole original module functors compose through the earned actual tensor associator. -/
def bimoduleTensorCompNatIso :
    bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F ≅
      BalancedTensor.Left.functor ℤ R S E ⋙ BalancedTensor.Left.functor ℤ S T F :=
  NatIso.ofComponents (bimoduleTensorCompIso (S := S) (T := T) E F) (by
    intro M N g
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply bimoduleTensorCompHom_ext (S := S) (T := T) E F M
    intro f e m
    change (bimoduleTensorCompIso (S := S) (T := T) E F N).hom.hom
        (((bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F).map g).hom
          (bimoduleTensorCompPure (S := S) (T := T) E F M f e m)) =
      ((BalancedTensor.Left.functor ℤ R S E ⋙ BalancedTensor.Left.functor ℤ S T F).map g).hom
        ((bimoduleTensorCompIso (S := S) (T := T) E F M).hom.hom
          (bimoduleTensorCompPure (S := S) (T := T) E F M f e m))
    rw [bimoduleTensorCompositeFunctor_map_pure, bimoduleTensorCompIso_pure,
      bimoduleTensorCompIso_pure, bimoduleTensorDouble_map_pure])

/-- Canonical right flatness is earned for the actual composite coefficient from both factors. -/
theorem bimoduleTensor_composite_flat
    (hE : ∀ N : ModuleCat.{u} R,
      IsZero (((BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ E)).obj N))
    (hF : ∀ N : ModuleCat.{u} S,
      IsZero (((BalancedTensor.torFirst S 1).obj (ModuleCat.of Sᵐᵒᵖ F)).obj N)) :
    PreservesFiniteLimits
        (bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F) ∧
      (let C := TensorProduct.Balanced ℤ S F E
       letI : Module Rᵐᵒᵖ C := TensorProduct.Balanced.rightModule ℤ S R F E
       ∀ N : ModuleCat.{u} R,
         IsZero (((BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ C)).obj N)) := by
  let C := TensorProduct.Balanced ℤ S F E
  let : Module T C := TensorProduct.Balanced.leftModule ℤ S T F E
  let : Module Rᵐᵒᵖ C := TensorProduct.Balanced.rightModule ℤ S R F E
  let : SMulCommClass T Rᵐᵒᵖ C :=
    TensorProduct.Balanced.leftRightSMulCommClass ℤ S R F E T
  let P : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let Q : ModuleCat.{u} S ⥤ ModuleCat.{u} T := BalancedTensor.Left.functor ℤ S T F
  let : PreservesFiniteLimits P := bimoduleTensor_preservesFiniteLimits_of_torFirst_one E hE
  let : PreservesFiniteLimits Q := bimoduleTensor_preservesFiniteLimits_of_torFirst_one F hF
  let : PreservesFiniteLimits (P ⋙ Q) := Limits.comp_preservesFiniteLimits P Q
  let A := bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F
  let : PreservesFiniteLimits A :=
    preservesFiniteLimits_of_natIso (bimoduleTensorCompNatIso (S := S) (T := T) E F).symm
  let V := forget₂ (ModuleCat.{u} T) AddCommGrpCat.{u}
  have h : PreservesFiniteLimits ((BalancedTensor.groupBifunctor R).obj (ModuleCat.of Rᵐᵒᵖ C)) := by
    have hA : PreservesFiniteLimits (A ⋙ V) := Limits.comp_preservesFiniteLimits A V
    change PreservesFiniteLimits (BalancedTensor.Left.functor ℤ R T C ⋙ V) at hA
    rw [bimoduleTensor_comp_forgetToGroup] at hA
    exact hA
  exact ⟨inferInstance,
    (BalancedTensor.groupBifunctor_obj_preservesFiniteLimits_iff_torFirst_one
      R (ModuleCat.of Rᵐᵒᵖ C)).1 h⟩

end ModuleCat

namespace FGModuleCat

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]
  (E F : Type u) [AddCommGroup E] [AddCommGroup F]
  [Module S E] [Module Rᵐᵒᵖ E] [SMulCommClass S Rᵐᵒᵖ E]
  [Module T F] [Module Sᵐᵒᵖ F] [SMulCommClass T Sᵐᵒᵖ F]
  [Module.Finite S E] [Module.Finite T F]

/-- The same original composite coefficient tensor functor on the native finite categories. -/
def bimoduleTensorCompositeFunctor : FGModuleCat.{u} R ⥤ FGModuleCat.{u} T := by
  let C := TensorProduct.Balanced ℤ S F E
  letI : Module T C := TensorProduct.Balanced.leftModule ℤ S T F E
  letI : Module Rᵐᵒᵖ C := TensorProduct.Balanced.rightModule ℤ S R F E
  letI : SMulCommClass T Rᵐᵒᵖ C :=
    TensorProduct.Balanced.leftRightSMulCommClass ℤ S R F E T
  letI : Module.Finite T C := TensorProduct.Balanced.finite_left S T F E
  exact bimoduleTensor (R := R) (S := T) C

/-- Additivity of the composite coefficient functor is that of the same original finite tensor. -/
instance bimoduleTensorCompositeFunctor_additive :
    (bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F).Additive := by
  let C := TensorProduct.Balanced ℤ S F E
  let : Module T C := TensorProduct.Balanced.leftModule ℤ S T F E
  let : Module Rᵐᵒᵖ C := TensorProduct.Balanced.rightModule ℤ S R F E
  let : SMulCommClass T Rᵐᵒᵖ C :=
    TensorProduct.Balanced.leftRightSMulCommClass ℤ S R F E T
  let : Module.Finite T C := TensorProduct.Balanced.finite_left S T F E
  change (bimoduleTensor (R := R) (S := T) C).Additive
  infer_instance

/-- The actual module associator restricts to the same original finite-module objects. -/
def bimoduleTensorCompIso (M : FGModuleCat.{u} R) :
    (bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F).obj M ≅
      (bimoduleTensor (R := R) (S := S) E ⋙ bimoduleTensor (R := S) (S := T) F).obj M := by
  let i := ModuleCat.bimoduleTensorCompIso (R := R) (S := S) (T := T) E F M.obj
  exact
    { hom := ⟨i.hom⟩
      inv := ⟨i.inv⟩
      hom_inv_id := by apply ObjectProperty.hom_ext; exact i.hom_inv_id
      inv_hom_id := by apply ObjectProperty.hom_ext; exact i.inv_hom_id }

/-- The whole finite-module tensor functors compose through the actual associator. -/
def bimoduleTensorCompNatIso :
    bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F ≅
      bimoduleTensor (R := R) (S := S) E ⋙ bimoduleTensor (R := S) (S := T) F :=
  NatIso.ofComponents (bimoduleTensorCompIso (S := S) (T := T) E F) (by
    intro M N f
    apply ObjectProperty.hom_ext
    exact (ModuleCat.bimoduleTensorCompNatIso (R := R) (S := S) (T := T) E F).hom.naturality f.hom)

end FGModuleCat

namespace ModuleCat

variable (R : Type u) [Ring R]

/-- Projectivity of the original right coefficient earns its canonical Tor₁ flatness condition. -/
theorem bimoduleTensor_torFirst_one_of_projective (E : Type u) [AddCommGroup E]
    [Module Rᵐᵒᵖ E] [Module.Projective Rᵐᵒᵖ E] :
    ∀ N : ModuleCat.{u} R,
      IsZero (((BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ E)).obj N) := by
  let P := ModuleCat.of Rᵐᵒᵖ E
  let F := (BalancedTensor.groupBifunctor R).obj P
  let : F.PreservesHomology :=
    BalancedTensor.groupBifunctor_obj_preservesHomology_of_projective R P
  have h : PreservesFiniteLimits F := Functor.preservesFiniteLimits_of_preservesHomology F
  exact (BalancedTensor.groupBifunctor_obj_preservesFiniteLimits_iff_torFirst_one R P).1 h

/-- The actual regular right module is projective, so its original tensor is right flat. -/
theorem bimoduleTensor_torFirst_one_regular :
    ∀ N : ModuleCat.{u} R,
      IsZero (((BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ R)).obj N) := by
  let e : Rᵐᵒᵖ ≃ₗ[Rᵐᵒᵖ] R := (MulOpposite.opLinearEquiv Rᵐᵒᵖ (M := R)).symm
  let : Module.Projective Rᵐᵒᵖ R := Module.Projective.of_equiv' e
  exact bimoduleTensor_torFirst_one_of_projective R R

end ModuleCat

namespace FGModuleCat

variable (R : Type u) [Ring R]

/-- The original regular-factor unitor and its pure value, with actual integer coordinates. -/
def bimoduleTensorUnitData (M : FGModuleCat.{u} R) :
    letI : Module ℤ R := AddCommGroup.toIntModule R
    letI : Module ℤ M := Module.compHom M (algebraMap ℤ R)
    {i : (bimoduleTensor (R := R) (S := R) R).obj M ≅ M //
      ∀ (r : R) (m : M), i.hom.hom.hom (TensorProduct.Balanced.mk ℤ R R M r m) = r • m} := by
  letI : Module ℤ M := Module.compHom M (algebraMap ℤ R)
  letI : @IsScalarTower ℤ R M (Algebra.toModule : Module ℤ R).toSMul
      (M.obj.isModule).toSMul (Module.compHom M (algebraMap ℤ R)).toSMul :=
    Module.intModule_isScalarTower
    (Algebra.toModule : Module ℤ R) (Module.compHom M (algebraMap ℤ R))
  let d₀ : Module ℤ R := AddCommGroup.toIntModule R
  let d₁ : Module ℤ R := Algebra.toModule
  let K : Module ℤ R → ModuleCat.{u} R := fun d =>
    letI : Module ℤ R := d
    letI : @SMulCommClass R ℤ R (inferInstance : Module R R).toSMul d.toSMul :=
      Module.intModule_smulCommClass (dM := d)
    letI := TensorProduct.Balanced.leftModule ℤ R R R M
    ModuleCat.of R (TensorProduct.Balanced ℤ R R M)
  let z : ∀ d : Module ℤ R, R → M → K d := fun d r m =>
    letI : Module ℤ R := d
    TensorProduct.Balanced.mk ℤ R R M r m
  have compare (d d' : Module ℤ R) (h : d = d') :
      {i : K d ≅ K d' // ∀ (r : R) (m : M), i.hom.hom (z d r m) = z d' r m} := by
    cases h
    exact ⟨Iso.refl _, fun _ _ => rfl⟩
  let c := compare d₀ d₁ (Subsingleton.elim d₀ d₁)
  letI : Module ℤ R := d₁
  letI : @SMulCommClass R ℤ R (inferInstance : Module R R).toSMul d₁.toSMul :=
    Module.intModule_smulCommClass (dM := d₁)
  letI := TensorProduct.Balanced.leftModule ℤ R R R M
  let U := TensorProduct.Balanced.leftUnitor ℤ R M
  have hS (a : R) (x : K d₁) : U (a • x) = a • U x := by
    have h : U.toLinearMap.toAddMonoidHom.comp
          (TensorProduct.Balanced.leftAction ℤ R R R M a).toAddMonoidHom =
        (DistribSMul.toAddMonoidHom M a).comp U.toLinearMap.toAddMonoidHom := by
      apply TensorProduct.Balanced.addHom_ext ℤ R R M
      intro r m
      change U (TensorProduct.Balanced.leftAction ℤ R R R M a
          (TensorProduct.Balanced.mk ℤ R R M r m)) =
        a • U (TensorProduct.Balanced.mk ℤ R R M r m)
      rw [TensorProduct.Balanced.leftAction_mk, TensorProduct.Balanced.leftUnitor_mk,
        TensorProduct.Balanced.leftUnitor_mk]
      change (a * r) • m = a • (r • m)
      exact mul_smul a r m
    exact DFunLike.congr_fun h x
  let er : K d₁ ≃ₗ[R] M :=
    { toFun := U
      invFun := U.symm
      left_inv := U.left_inv
      right_inv := U.right_inv
      map_add' := U.map_add
      map_smul' := hS }
  let j : K d₁ ≅ M.obj :=
    { hom := ModuleCat.ofHom (X := K d₁) (Y := M.obj) er.toLinearMap
      inv := ModuleCat.ofHom (X := M.obj) (Y := K d₁) er.symm.toLinearMap
      hom_inv_id := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact er.left_inv x
      inv_hom_id := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact er.right_inv x }
  let i : ((bimoduleTensor (R := R) (S := R) R).obj M).obj ≅ M.obj := c.1 ≪≫ j
  let e : (bimoduleTensor (R := R) (S := R) R).obj M ≅ M :=
    { hom := ⟨i.hom⟩
      inv := ⟨i.inv⟩
      hom_inv_id := by apply ObjectProperty.hom_ext; exact i.hom_inv_id
      inv_hom_id := by apply ObjectProperty.hom_ext; exact i.inv_hom_id }
  refine ⟨e, ?_⟩
  intro r m
  change U (c.1.hom.hom (z d₀ r m)) = r • m
  rw [c.2]
  exact TensorProduct.Balanced.leftUnitor_mk ℤ R M r m

/-- The actual regular-factor unitor on the original finite-module tensor object. -/
def bimoduleTensorUnitIso (M : FGModuleCat.{u} R) :
    (bimoduleTensor (R := R) (S := R) R).obj M ≅ M :=
  (bimoduleTensorUnitData R M).1

/-- The regular unitor applies the original R action to every actual ordered pure class. -/
theorem bimoduleTensorUnitIso_mk (M : FGModuleCat.{u} R) (r : R) (m : M) :
    letI : Module ℤ R := AddCommGroup.toIntModule R
    letI : Module ℤ M := Module.compHom M (algebraMap ℤ R)
    (bimoduleTensorUnitIso R M).hom.hom.hom
        (TensorProduct.Balanced.mk ℤ R R M r m) = r • m :=
  (bimoduleTensorUnitData R M).2 r m

/-- The whole original regular-bimodule tensor functor is naturally the identity. -/
def bimoduleTensorUnitNatIso :
    bimoduleTensor (R := R) (S := R) R ≅ 𝟭 (FGModuleCat.{u} R) :=
  NatIso.ofComponents (bimoduleTensorUnitIso R) (by
    intro M N f
    let : Module ℤ R := AddCommGroup.toIntModule R
    let : Module ℤ M := Module.compHom M (algebraMap ℤ R)
    let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    apply FGModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.addHom_ext ℤ R R M
    intro r m
    change (bimoduleTensorUnitIso R N).hom.hom.hom
        (((bimoduleTensor (R := R) (S := R) R).map f).hom.hom
          (TensorProduct.Balanced.mk ℤ R R M r m)) =
      f.hom.hom ((bimoduleTensorUnitIso R M).hom.hom.hom
        (TensorProduct.Balanced.mk ℤ R R M r m))
    rw [bimoduleTensor_map_mk, bimoduleTensorUnitIso_mk, bimoduleTensorUnitIso_mk]
    exact (f.hom.hom.map_smul r m).symm)

end FGModuleCat

namespace ModuleCat

variable {R S : Type u} [Ring R] [Ring S]
  {E E' : Type u} [AddCommGroup E] [AddCommGroup E']
  [Module S E] [Module S E'] [Module Rᵐᵒᵖ E] [Module Rᵐᵒᵖ E']

/-- An actual bimodule equivalence transports the canonical right-module Tor₁ flatness condition. -/
theorem bimoduleTensor_torFirst_one_of_equiv (e : E ≃ₗ[S] E')
    (hR : ∀ (r : R) (x : E), e (MulOpposite.op r • x) = MulOpposite.op r • e x)
    (hE : ∀ N : ModuleCat.{u} R,
      IsZero (((BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ E)).obj N)) :
    ∀ N : ModuleCat.{u} R,
      IsZero (((BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ E')).obj N) := by
  let er : E ≃ₗ[Rᵐᵒᵖ] E' := e.toAddEquiv.toLinearEquiv (by
    intro r x
    simpa only [MulOpposite.op_unop, LinearEquiv.coe_toAddEquiv,
      LinearEquiv.coe_addEquiv_apply] using hR r.unop x)
  let i : ModuleCat.of Rᵐᵒᵖ E ≅ ModuleCat.of Rᵐᵒᵖ E' := er.toModuleIso
  let : PreservesFiniteLimits
      ((BalancedTensor.groupBifunctor R).obj (ModuleCat.of Rᵐᵒᵖ E)) :=
    (BalancedTensor.groupBifunctor_obj_preservesFiniteLimits_iff_torFirst_one
      R (ModuleCat.of Rᵐᵒᵖ E)).2 hE
  have h : PreservesFiniteLimits
      ((BalancedTensor.groupBifunctor R).obj (ModuleCat.of Rᵐᵒᵖ E')) :=
    preservesFiniteLimits_of_natIso ((BalancedTensor.groupBifunctor R).mapIso i)
  exact (BalancedTensor.groupBifunctor_obj_preservesFiniteLimits_iff_torFirst_one
    R (ModuleCat.of Rᵐᵒᵖ E')).1 h

end ModuleCat

namespace FGModuleCat

variable {R S : Type u} [Ring R] [Ring S]
  {E E' E'' : Type u} [AddCommGroup E] [AddCommGroup E'] [AddCommGroup E'']
  [Module S E] [Module S E'] [Module S E'']
  [Module Rᵐᵒᵖ E] [Module Rᵐᵒᵖ E'] [Module Rᵐᵒᵖ E'']
  [SMulCommClass S Rᵐᵒᵖ E] [SMulCommClass S Rᵐᵒᵖ E']
  [SMulCommClass S Rᵐᵒᵖ E'']
  [Module.Finite S E] [Module.Finite S E'] [Module.Finite S E'']

/-- The actual quotient coefficient map between the two original finite tensor outputs. -/
def bimoduleTensorCoefficientComponent (f : E →ₗ[S] E')
    (hR : ∀ (r : R) (e : E), f (op r • e) = op r • f e) (M : FGModuleCat.{u} R) :
    (bimoduleTensor (S := S) E).obj M ⟶ (bimoduleTensor (S := S) E').obj M := by
  letI : Module ℤ M := Module.compHom M (algebraMap ℤ R)
  let f₀ : E →ₗ[ℤ] E' := f.toAddMonoidHom.toIntLinearMap
  letI := TensorProduct.Balanced.leftModule ℤ R S E M
  letI := TensorProduct.Balanced.leftModule ℤ R S E' M
  exact ⟨ModuleCat.ofHom
    (X := (ModuleCat.BalancedTensor.Left.functor ℤ R S E).obj M.obj)
    (Y := (ModuleCat.BalancedTensor.Left.functor ℤ R S E').obj M.obj)
    (TensorProduct.Balanced.mapLeft f₀ (LinearMap.id : M →ₗ[ℤ] M)
      (fun r e => hR r e) (fun _ _ => rfl) (fun s e => f.map_smul s e))⟩

/-- The coefficient map retains both ordered pure factors, applying only the given bimodule map. -/
theorem bimoduleTensorCoefficientComponent_mk (f : E →ₗ[S] E')
    (hR : ∀ (r : R) (e : E), f (op r • e) = op r • f e)
    (M : FGModuleCat.{u} R) (e : E) (m : M) :
    letI : Module ℤ M := Module.compHom M (algebraMap ℤ R)
    (bimoduleTensorCoefficientComponent f hR M).hom.hom
        (TensorProduct.Balanced.mk ℤ R E M e m) =
      TensorProduct.Balanced.mk ℤ R E' M (f e) m := by
  let : Module ℤ M := Module.compHom M (algebraMap ℤ R)
  let f₀ : E →ₗ[ℤ] E' := f.toAddMonoidHom.toIntLinearMap
  let := TensorProduct.Balanced.leftModule ℤ R S E M
  let := TensorProduct.Balanced.leftModule ℤ R S E' M
  exact TensorProduct.Balanced.mapLeft_mk f₀ (LinearMap.id : M →ₗ[ℤ] M)
    (fun r e => hR r e) (fun _ _ => rfl) (fun s e => f.map_smul s e) e m

/-- An actual bimodule map gives a natural transformation of the original finite tensor functors. -/
def bimoduleTensorTransformation (f : E →ₗ[S] E')
    (hR : ∀ (r : R) (e : E), f (op r • e) = op r • f e) :
    bimoduleTensor (R := R) (S := S) E ⟶ bimoduleTensor (R := R) (S := S) E' where
  app := bimoduleTensorCoefficientComponent f hR
  naturality M N g := by
    let : Module ℤ M := Module.compHom M (algebraMap ℤ R)
    let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    apply FGModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.addHom_ext ℤ R E M
    intro e m
    change (bimoduleTensorCoefficientComponent f hR N).hom.hom
        (((bimoduleTensor E).map g).hom.hom (TensorProduct.Balanced.mk ℤ R E M e m)) =
      ((bimoduleTensor E').map g).hom.hom
        ((bimoduleTensorCoefficientComponent f hR M).hom.hom
          (TensorProduct.Balanced.mk ℤ R E M e m))
    rw [bimoduleTensor_map_mk, bimoduleTensorCoefficientComponent_mk,
      bimoduleTensorCoefficientComponent_mk, bimoduleTensor_map_mk]

/-- Identity coefficient maps give the whole identity natural transformation. -/
@[simp]
theorem bimoduleTensorTransformation_id :
    bimoduleTensorTransformation (R := R) (LinearMap.id : E →ₗ[S] E) (fun _ _ => rfl) =
      𝟙 (bimoduleTensor (R := R) (S := S) E) := by
  apply NatTrans.ext
  funext M
  let : Module ℤ M := Module.compHom M (algebraMap ℤ R)
  apply FGModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R E M
  intro e m
  change (bimoduleTensorCoefficientComponent (LinearMap.id : E →ₗ[S] E)
      (fun _ _ => rfl) M).hom.hom (TensorProduct.Balanced.mk ℤ R E M e m) = _
  rw [bimoduleTensorCoefficientComponent_mk]
  rfl

/-- Coefficient transformations compose through the actual original quotient coefficient maps. -/
theorem bimoduleTensorTransformation_comp (f : E →ₗ[S] E') (g : E' →ₗ[S] E'')
    (hF : ∀ (r : R) (e : E), f (op r • e) = op r • f e)
    (hG : ∀ (r : R) (e : E'), g (op r • e) = op r • g e) :
    bimoduleTensorTransformation (g.comp f)
        (fun r e => (congrArg g (hF r e)).trans (hG r (f e))) =
      bimoduleTensorTransformation f hF ≫ bimoduleTensorTransformation g hG := by
  apply NatTrans.ext
  funext M
  let : Module ℤ M := Module.compHom M (algebraMap ℤ R)
  apply FGModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R E M
  intro e m
  change (bimoduleTensorCoefficientComponent (g.comp f)
      (fun r e => (congrArg g (hF r e)).trans (hG r (f e))) M).hom.hom
      (TensorProduct.Balanced.mk ℤ R E M e m) =
    (bimoduleTensorCoefficientComponent g hG M).hom.hom
      ((bimoduleTensorCoefficientComponent f hF M).hom.hom
        (TensorProduct.Balanced.mk ℤ R E M e m))
  rw [bimoduleTensorCoefficientComponent_mk, bimoduleTensorCoefficientComponent_mk,
    bimoduleTensorCoefficientComponent_mk]
  rfl

/-- An actual bimodule equivalence gives an earned natural isomorphism of finite tensor functors. -/
def bimoduleTensorIso (e : E ≃ₗ[S] E')
    (hR : ∀ (r : R) (x : E), e (op r • x) = op r • e x) :
    bimoduleTensor (R := R) (S := S) E ≅ bimoduleTensor (R := R) (S := S) E' := by
  have hR' : ∀ (r : R) (x : E'), e.symm (op r • x) = op r • e.symm x := by
    intro r x
    apply e.injective
    rw [e.apply_symm_apply, hR, e.apply_symm_apply]
  refine
    { hom := bimoduleTensorTransformation e.toLinearMap hR
      inv := bimoduleTensorTransformation e.symm.toLinearMap hR'
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply NatTrans.ext
    funext M
    let : Module ℤ M := Module.compHom M (algebraMap ℤ R)
    apply FGModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.addHom_ext ℤ R E M
    intro x m
    change (bimoduleTensorCoefficientComponent e.symm.toLinearMap hR' M).hom.hom
        ((bimoduleTensorCoefficientComponent e.toLinearMap hR M).hom.hom
          (TensorProduct.Balanced.mk ℤ R E M x m)) = _
    rw [bimoduleTensorCoefficientComponent_mk, bimoduleTensorCoefficientComponent_mk]
    change TensorProduct.Balanced.mk ℤ R E M (e.symm (e x)) m = _
    rw [e.symm_apply_apply]
    rfl
  · apply NatTrans.ext
    funext M
    let : Module ℤ M := Module.compHom M (algebraMap ℤ R)
    apply FGModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.addHom_ext ℤ R E' M
    intro x m
    change (bimoduleTensorCoefficientComponent e.toLinearMap hR M).hom.hom
        ((bimoduleTensorCoefficientComponent e.symm.toLinearMap hR' M).hom.hom
          (TensorProduct.Balanced.mk ℤ R E' M x m)) = _
    rw [bimoduleTensorCoefficientComponent_mk, bimoduleTensorCoefficientComponent_mk]
    change TensorProduct.Balanced.mk ℤ R E' M (e (e.symm x)) m = _
    rw [e.apply_symm_apply]
    rfl

end FGModuleCat


namespace ModuleCat

variable (R S P Q : Type u) [Ring R] [Ring S] [AddCommGroup P] [AddCommGroup Q]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  (a : letI := TensorProduct.Balanced.leftModule ℤ S R P Q
    letI := TensorProduct.Balanced.rightModule ℤ S R P Q
    TensorProduct.Balanced ℤ S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (ha : letI := TensorProduct.Balanced.leftModule ℤ S R P Q
    letI := TensorProduct.Balanced.rightModule ℤ S R P Q
    ∀ (r : R) (x : TensorProduct.Balanced ℤ S P Q), a (r • x) = r * a x)
  (b : letI := TensorProduct.Balanced.leftModule ℤ R S Q P
    letI := TensorProduct.Balanced.rightModule ℤ R S Q P
    TensorProduct.Balanced ℤ R Q P ≃ₗ[Sᵐᵒᵖ] S)
  (hb : letI := TensorProduct.Balanced.leftModule ℤ R S Q P
    letI := TensorProduct.Balanced.rightModule ℤ R S Q P
    ∀ (s : S) (x : TensorProduct.Balanced ℤ R Q P), b (s • x) = s * b x)

include a ha b hb in
/-- Original invertible-bimodule contractions earn finiteness and right-flatness on both sides. -/
theorem bimoduleTensorMorita_properties :
    Module.Finite R P ∧ Module.Finite S Q ∧
      (∀ N : ModuleCat.{u} S,
        IsZero (((BalancedTensor.torFirst S 1).obj (ModuleCat.of Sᵐᵒᵖ P)).obj N)) ∧
      (∀ N : ModuleCat.{u} R,
        IsZero (((BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ Q)).obj N)) := by
  let hP := TensorProduct.Balanced.Morita.p_left_finite_projective R S P Q a ha b hb
  let hQ := TensorProduct.Balanced.Morita.q_left_finite_projective R S P Q a ha b hb
  let : Module.Projective Sᵐᵒᵖ P :=
    (TensorProduct.Balanced.Morita.p_right_finite_projective R S P Q a ha b hb).2
  let : Module.Projective Rᵐᵒᵖ Q :=
    (TensorProduct.Balanced.Morita.q_right_finite_projective R S P Q a ha b hb).2
  exact ⟨hP.1, hQ.1, bimoduleTensor_torFirst_one_of_projective S P,
    bimoduleTensor_torFirst_one_of_projective R Q⟩

open scoped ModuleCat.Algebra

/-- Package the existing original left-module tensor equivalence as the canonical Morita input. -/
def bimoduleTensorMoritaEquivalence : MoritaEquivalence ℤ R S := by
  letI : CategoryTheory.Linear ℤ (ModuleCat.{u} R) := ModuleCat.Algebra.instLinear
  letI : CategoryTheory.Linear ℤ (ModuleCat.{u} S) := ModuleCat.Algebra.instLinear
  letI : Module ℤ P := AddCommGroup.toIntModule P
  letI : Module ℤ Q := AddCommGroup.toIntModule Q
  letI : @IsScalarTower ℤ R P (Algebra.toModule : Module ℤ R).toSMul
      (inferInstance : Module R P).toSMul (AddCommGroup.toIntModule P).toSMul :=
    Module.intModule_isScalarTower (Algebra.toModule : Module ℤ R) (AddCommGroup.toIntModule P)
  letI : @IsScalarTower ℤ Sᵐᵒᵖ P (Algebra.toModule : Module ℤ Sᵐᵒᵖ).toSMul
      (inferInstance : Module Sᵐᵒᵖ P).toSMul (AddCommGroup.toIntModule P).toSMul :=
    Module.intModule_isScalarTower
      (Algebra.toModule : Module ℤ Sᵐᵒᵖ) (AddCommGroup.toIntModule P)
  letI : @IsScalarTower ℤ S Q (Algebra.toModule : Module ℤ S).toSMul
      (inferInstance : Module S Q).toSMul (AddCommGroup.toIntModule Q).toSMul :=
    Module.intModule_isScalarTower (Algebra.toModule : Module ℤ S) (AddCommGroup.toIntModule Q)
  letI : @IsScalarTower ℤ Rᵐᵒᵖ Q (Algebra.toModule : Module ℤ Rᵐᵒᵖ).toSMul
      (inferInstance : Module Rᵐᵒᵖ Q).toSMul (AddCommGroup.toIntModule Q).toSMul :=
    Module.intModule_isScalarTower
      (Algebra.toModule : Module ℤ Rᵐᵒᵖ) (AddCommGroup.toIntModule Q)
  exact
    { eqv := BalancedTensor.Left.Morita.equivalence ℤ R S P Q a ha b hb
      linear := by
        refine ⟨?_⟩
        intro X Y f z
        let F := (BalancedTensor.Left.Morita.equivalence ℤ R S P Q a ha b hb).functor
        let : F.Additive := by
          change (BalancedTensor.Left.functor ℤ R S Q :
            ModuleCat.{u} R ⥤ ModuleCat.{u} S).Additive
          exact BalancedTensor.Left.additive ℤ R S Q
        let dX := (ModuleCat.Algebra.instLinear :
          CategoryTheory.Linear ℤ (ModuleCat.{u} R)).homModule X Y
        let dY := (ModuleCat.Algebra.instLinear :
          CategoryTheory.Linear ℤ (ModuleCat.{u} S)).homModule (F.obj X) (F.obj Y)
        change F.map (dX.smul z f) = dY.smul z (F.map f)
        rw [int_smul_eq_zsmul dX z f, int_smul_eq_zsmul dY z (F.map f)]
        exact F.mapAddHom.map_zsmul z f }

/-- The canonical Morita equivalence retains the whole original Q⊗R− functor. -/
theorem bimoduleTensorMoritaEquivalence_functor :
    (bimoduleTensorMoritaEquivalence R S P Q a ha b hb).eqv.functor =
      (BalancedTensor.Left.functor ℤ R S Q : ModuleCat.{u} R ⥤ ModuleCat.{u} S) := rfl

/-- Its original inverse is precisely the existing P⊗S− functor. -/
theorem bimoduleTensorMoritaEquivalence_inverse :
    (bimoduleTensorMoritaEquivalence R S P Q a ha b hb).eqv.inverse =
      (BalancedTensor.Left.functor ℤ S R P : ModuleCat.{u} S ⥤ ModuleCat.{u} R) := rfl

end ModuleCat

namespace FGModuleCat

variable (R S P Q : Type u) [Ring R] [Ring S] [AddCommGroup P] [AddCommGroup Q]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  (a : letI := TensorProduct.Balanced.leftModule ℤ S R P Q
    letI := TensorProduct.Balanced.rightModule ℤ S R P Q
    TensorProduct.Balanced ℤ S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (ha : letI := TensorProduct.Balanced.leftModule ℤ S R P Q
    letI := TensorProduct.Balanced.rightModule ℤ S R P Q
    ∀ (r : R) (x : TensorProduct.Balanced ℤ S P Q), a (r • x) = r * a x)
  (b : letI := TensorProduct.Balanced.leftModule ℤ R S Q P
    letI := TensorProduct.Balanced.rightModule ℤ R S Q P
    TensorProduct.Balanced ℤ R Q P ≃ₗ[Sᵐᵒᵖ] S)
  (hb : letI := TensorProduct.Balanced.leftModule ℤ R S Q P
    letI := TensorProduct.Balanced.rightModule ℤ R S Q P
    ∀ (s : S) (x : TensorProduct.Balanced ℤ R Q P), b (s • x) = s * b x)

/-- The same original forward tensor on finite modules, with coefficient finiteness earned. -/
def bimoduleTensorMoritaFunctor : FGModuleCat.{u} R ⥤ FGModuleCat.{u} S :=
  letI := (ModuleCat.bimoduleTensorMorita_properties R S P Q a ha b hb).2.1
  bimoduleTensor (R := R) (S := S) Q

/-- The same original inverse tensor on finite modules, with its earned left finiteness. -/
def bimoduleTensorMoritaInverseFunctor : FGModuleCat.{u} S ⥤ FGModuleCat.{u} R :=
  letI := (ModuleCat.bimoduleTensorMorita_properties R S P Q a ha b hb).1
  bimoduleTensor (R := S) (S := R) P

/-- Canonical Morita restriction is the whole actual finite-module coefficient tensor. -/
theorem bimoduleTensorMoritaFunctor_eq :
    bimoduleTensorMoritaFunctor R S P Q a ha b hb =
      (ModuleCat.bimoduleTensorMoritaEquivalence
        R S P Q a ha b hb).fgModuleCatEquivalence.functor :=
  rfl

/-- The inverse canonical Morita restriction retains the whole actual inverse tensor functor. -/
theorem bimoduleTensorMoritaInverseFunctor_eq :
    bimoduleTensorMoritaInverseFunctor R S P Q a ha b hb =
      (ModuleCat.bimoduleTensorMoritaEquivalence
        R S P Q a ha b hb).fgModuleCatEquivalence.inverse :=
  rfl

end FGModuleCat
