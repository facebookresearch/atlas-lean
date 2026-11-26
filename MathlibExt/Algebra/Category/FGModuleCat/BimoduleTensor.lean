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
# Bimodule tensor on finite-module categories

Let `R` and `S` be associative rings and `E` an `S`-left, `R`-right bimodule. If `E` is
finitely generated over `S`, then `E ⊗_R -` takes finite left `R`-modules to finite left
`S`-modules. The induced functor is additive. Vanishing of `Tor¹_R(E, N)` for every left
`R`-module `N` makes the ambient tensor functor preserve short exact sequences.

For a `T`-left, `S`-right bimodule `F`, tensoring by `F ⊗_S E` is naturally isomorphic to
successive tensoring by `E` and `F`, with `[[f ⊗ e] ⊗ m] ↦ [f ⊗ [e ⊗ m]]`. Left finiteness and
right Tor-one vanishing pass to the composite under the corresponding hypotheses. The regular
coefficient gives `[r ⊗ m] ↦ r • m`, and bimodule maps give coefficient natural
transformations.

Bimodule equivalences `P ⊗_S Q ≅ R` and `Q ⊗_R P ≅ S` give finite coefficients, right Tor-one
vanishing, and a Morita equivalence that restricts to finite-module categories. The rings,
coefficients, and module carriers here lie in the same universe `u`; each tensor is the
integer-ground balanced quotient.
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

/-- Finite coefficient and finite input give finite tensor output.

Let `E` be an `S`-left, `R`-right bimodule, finite over `S`. If the left `R`-module `N` is
finitely generated, then `E ⊗_R N` is finitely generated over `S`. -/
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

/-- Forgetting the outer action gives the balanced tensor group functor.

The functor `E ⊗_R -` to left `S`-modules, followed by forgetting to additive groups, equals
the group-valued balanced tensor functor with right `R`-coefficient `E`. -/
theorem bimoduleTensor_comp_forgetToGroup :
    BalancedTensor.Left.functor ℤ R S E ⋙
        forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u} =
      (BalancedTensor.groupBifunctor R).obj (ModuleCat.of Rᵐᵒᵖ E) := by
  rfl

/-- Bimodule tensor preserves finite colimits.

For an `S`-left, `R`-right bimodule `E`, the functor `E ⊗_R - : ModuleCat R ⥤ ModuleCat S`
preserves finite colimits. -/
theorem bimoduleTensor_preservesFiniteColimits :
    PreservesFiniteColimits
      (BalancedTensor.Left.functor ℤ R S E : ModuleCat.{u} R ⥤ ModuleCat.{u} S) := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let U := forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}
  let : PreservesFiniteColimits (F ⋙ U) := by
    rw [bimoduleTensor_comp_forgetToGroup]
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves F U

/-- Right Tor-one vanishing makes bimodule tensor preserve finite limits.

If `Tor¹_R(E, N)` vanishes for every left `R`-module `N`, then the left-module-valued functor
`E ⊗_R -` preserves finite limits. -/
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

/-- Bimodule tensor preserves short exact sequences under right flatness.

Suppose `Tor¹_R(E, N) = 0` for every left `R`-module `N`. Mapping a short exact sequence in
`ModuleCat R` through `E ⊗_R -` gives a short exact sequence in `ModuleCat S`. -/
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

/-- Tensor by a left-finite bimodule on finite-module categories.

For an `S`-left, `R`-right bimodule `E` that is finite over `S`, restrict `E ⊗_R -` to a
functor `FGModuleCat R ⥤ FGModuleCat S`. Finite generation of each output follows from finite
generation of the input and of `E` over `S`. -/
def bimoduleTensor : FGModuleCat.{u} R ⥤ FGModuleCat.{u} S :=
  (ModuleCat.isFG (R := S)).lift
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) ⋙
      ModuleCat.BalancedTensor.Left.functor ℤ R S E)
    (fun X => ModuleCat.isFG_bimoduleTensor E X.obj X.property)

/-- Underlying module of the finite bimodule tensor object.

For a finite `R`-module object `X`, the underlying `S`-module of `(FGModuleCat.bimoduleTensor
E).obj X` is the output of the ambient functor `E ⊗_R -` on `X.obj`. -/
@[simp]
theorem bimoduleTensor_obj_obj (X : FGModuleCat.{u} R) :
    ((bimoduleTensor E).obj X).obj =
      (ModuleCat.BalancedTensor.Left.functor ℤ R S E).obj X.obj := rfl

/-- Underlying map of the finite bimodule tensor functor.

For a morphism `f : X ⟶ Y` of finite `R`-module objects, the underlying morphism of its tensor
image is the ambient bimodule tensor map of `f.hom`. -/
@[simp]
theorem bimoduleTensor_map_hom {X Y : FGModuleCat.{u} R} (f : X ⟶ Y) :
    ((bimoduleTensor E).map f).hom =
      (ModuleCat.BalancedTensor.Left.functor ℤ R S E).map f.hom := rfl

/-- Finite bimodule tensor map on pure classes.

A finite-module morphism `f : X ⟶ Y` induces `[e ⊗ x] ↦ [e ⊗ f x]` on the integer-ground
balanced quotients defining tensor by `E`. -/
theorem bimoduleTensor_map_mk {X Y : FGModuleCat.{u} R} (f : X ⟶ Y) (e : E) (x : X) :
    letI : Module ℤ X := Module.compHom X (algebraMap ℤ R)
    letI : Module ℤ Y := Module.compHom Y (algebraMap ℤ R)
    ((bimoduleTensor (R := R) (S := S) E).map f).hom.hom
        (TensorProduct.Balanced.mk ℤ R E X e x) =
      TensorProduct.Balanced.mk ℤ R E Y e (f.hom.hom x) := by
  let : Module ℤ X := Module.compHom X (algebraMap ℤ R)
  let : Module ℤ Y := Module.compHom Y (algebraMap ℤ R)
  exact ModuleCat.BalancedTensor.Left.map_mk ℤ R S E f.hom e x

/-- Finite bimodule tensor commutes with forgetting finite generation.

Tensoring in the finite-module categories and then forgetting to `ModuleCat S` is naturally
isomorphic to forgetting the source to `ModuleCat R` and applying the ambient bimodule tensor
functor. -/
def bimoduleTensorCompForgetIso :
    bimoduleTensor E ⋙ forget₂ (FGModuleCat.{u} S) (ModuleCat.{u} S) ≅
      forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) ⋙
        ModuleCat.BalancedTensor.Left.functor ℤ R S E :=
  (ModuleCat.isFG (R := S)).liftCompιIso
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) ⋙
      ModuleCat.BalancedTensor.Left.functor ℤ R S E)
    (fun X => ModuleCat.isFG_bimoduleTensor E X.obj X.property)

/-- Finite-module bimodule tensor is additive.

The finite-module-valued functor `FGModuleCat.bimoduleTensor E` preserves sums of morphisms. -/
instance bimoduleTensor_additive : (bimoduleTensor (R := R) (S := S) E).Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    change (ModuleCat.BalancedTensor.Left.functor ℤ R S E).map (f.hom + g.hom) =
      (ModuleCat.BalancedTensor.Left.functor ℤ R S E).map f.hom +
        (ModuleCat.BalancedTensor.Left.functor ℤ R S E).map g.hom
    exact Functor.map_add _

/-- Finite bimodule tensor preserves ambient short exactness.

Suppose the right `R`-module `E` has zero `Tor¹` against every left module. A short complex of
finite `R`-modules that is short exact after forgetting to `ModuleCat R` remains short exact
in `ModuleCat S` after applying finite bimodule tensor and forgetting. -/
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

/-- Tensor functor of the composite bimodule coefficient.

Let `E` be `S`-left and `R`-right, and `F` be `T`-left and `S`-right. Their balanced tensor `F
⊗_S E` has induced left `T`- and right `R`-actions. Tensoring with it gives a functor from
left `R`-modules to left `T`-modules. -/
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

/-- Pure triple in tensor by the composite coefficient.

For `f : F`, `e : E`, and `m : M`, this element is `[[f ⊗ e] ⊗ m]` in `(F ⊗_S E) ⊗_R M`, with
the induced endpoint actions on the composite coefficient. -/
def bimoduleTensorCompPure (M : ModuleCat.{u} R) (f : F) (e : E) (m : M) :
    (bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F).obj M := by
  letI : Module ℤ M := Module.compHom M (algebraMap ℤ R)
  let C := TensorProduct.Balanced ℤ S F E
  letI : Module Rᵐᵒᵖ C := TensorProduct.Balanced.rightModule ℤ S R F E
  letI : Module ℤ C := AddCommGroup.toIntModule C
  exact TensorProduct.Balanced.mk ℤ R C M (TensorProduct.Balanced.mk ℤ S F E f e) m

/-- Pure triple in successive bimodule tensor functors.

For `f : F`, `e : E`, and `m : M`, this element is `[f ⊗ [e ⊗ m]]` in `F ⊗_S (E ⊗_R M)`. -/
def bimoduleTensorDoublePure (M : ModuleCat.{u} R) (f : F) (e : E) (m : M) :
    (BalancedTensor.Left.functor ℤ R S E ⋙ BalancedTensor.Left.functor ℤ S T F).obj M := by
  letI : Module ℤ M := Module.compHom M (algebraMap ℤ R)
  let D := (BalancedTensor.Left.functor ℤ R S E).obj M
  letI : Module ℤ D := Module.compHom D (algebraMap ℤ S)
  exact TensorProduct.Balanced.mk ℤ S F D f (TensorProduct.Balanced.mk ℤ R E M e m)

/-- Associator together with its pure-triple formula.

For a left `R`-module `M`, this data constructs an isomorphism `(F ⊗_S E) ⊗_R M ≅ F ⊗_S (E ⊗_R
M)` in `ModuleCat T` and records that its forward map sends `[[f ⊗ e] ⊗ m]` to `[f ⊗ [e ⊗
m]]`. -/
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

/-- Associator for composite bimodule tensor objects.

The module isomorphism `(F ⊗_S E) ⊗_R M ≅ F ⊗_S (E ⊗_R M)` is obtained from the balanced
tensor associator with the endpoint module actions. -/
def bimoduleTensorCompIso (M : ModuleCat.{u} R) :
    (bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F).obj M ≅
      (BalancedTensor.Left.functor ℤ R S E ⋙ BalancedTensor.Left.functor ℤ S T F).obj M :=
  (bimoduleTensorCompData (S := S) (T := T) E F M).1

/-- Composite bimodule associator on pure triples.

The forward composite coefficient isomorphism sends `bimoduleTensorCompPure E F M f e m` to
`bimoduleTensorDoublePure E F M f e m`, preserving the order `f, e, m`. -/
theorem bimoduleTensorCompIso_pure (M : ModuleCat.{u} R) (f : F) (e : E) (m : M) :
    (bimoduleTensorCompIso (S := S) (T := T) E F M).hom.hom
        (bimoduleTensorCompPure (S := S) (T := T) E F M f e m) =
      bimoduleTensorDoublePure (S := S) (T := T) E F M f e m :=
  (bimoduleTensorCompData (S := S) (T := T) E F M).2 f e m

/-- Pure triples determine additive maps from a composite tensor.

Two additive maps from `(F ⊗_S E) ⊗_R M` to an additive commutative monoid are equal if they
agree on every pure triple `[[f ⊗ e] ⊗ m]`. -/
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

/-- Composite coefficient tensor map on pure triples.

For a module morphism `g : M ⟶ N`, tensoring by `F ⊗_S E` sends `[[f ⊗ e] ⊗ m]` to `[[f ⊗ e] ⊗
g m]`. -/
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

/-- Successive bimodule tensor map on pure triples.

For `g : M ⟶ N`, the successive tensor functors send `[f ⊗ [e ⊗ m]]` to `[f ⊗ [e ⊗ g m]]`. -/
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

/-- Tensor by a composite coefficient equals successive tensoring naturally.

The associator gives a natural isomorphism from tensoring by `F ⊗_S E` to the composite of
tensoring first by `E` and then by `F`. -/
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

/-- Composite of right-flat bimodule coefficients is right-flat.

Assume `Tor¹_R(E, -)` and `Tor¹_S(F, -)` vanish for all respective left modules. Then
tensoring by `F ⊗_S E` preserves finite limits, and the induced right `R`-module on `F ⊗_S E`
has zero `Tor¹_R` against every left module. -/
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

/-- Composite coefficient tensor on finite-module categories.

If `E` is finite over `S` and `F` is finite over `T`, the coefficient `F ⊗_S E` is finite over
`T`. Its tensor functor restricts to `FGModuleCat R ⥤ FGModuleCat T`. -/
def bimoduleTensorCompositeFunctor : FGModuleCat.{u} R ⥤ FGModuleCat.{u} T := by
  let C := TensorProduct.Balanced ℤ S F E
  letI : Module T C := TensorProduct.Balanced.leftModule ℤ S T F E
  letI : Module Rᵐᵒᵖ C := TensorProduct.Balanced.rightModule ℤ S R F E
  letI : SMulCommClass T Rᵐᵒᵖ C :=
    TensorProduct.Balanced.leftRightSMulCommClass ℤ S R F E T
  letI : Module.Finite T C := TensorProduct.Balanced.finite_left S T F E
  exact bimoduleTensor (R := R) (S := T) C

/-- Composite coefficient tensor on finite modules is additive.

The finite-module tensor functor with coefficient `F ⊗_S E` preserves addition of morphisms. -/
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

/-- Finite-module associator for composite coefficients.

For a finite left `R`-module `M`, the ambient isomorphism `(F ⊗_S E) ⊗_R M ≅ F ⊗_S (E ⊗_R M)`
is an isomorphism in `FGModuleCat T`, using left finiteness of both coefficients. -/
def bimoduleTensorCompIso (M : FGModuleCat.{u} R) :
    (bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F).obj M ≅
      (bimoduleTensor (R := R) (S := S) E ⋙ bimoduleTensor (R := S) (S := T) F).obj M := by
  let i := ModuleCat.bimoduleTensorCompIso (R := R) (S := S) (T := T) E F M.obj
  exact
    { hom := ⟨i.hom⟩
      inv := ⟨i.inv⟩
      hom_inv_id := by apply ObjectProperty.hom_ext; exact i.hom_inv_id
      inv_hom_id := by apply ObjectProperty.hom_ext; exact i.inv_hom_id }

/-- Finite composite coefficient tensor equals successive tensoring naturally.

For left-finite coefficients `E` and `F`, tensor by `F ⊗_S E` on finite modules is naturally
isomorphic to tensoring by `E` followed by tensoring by `F`. -/
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

/-- Projective right coefficient has zero Tor one against every left module.

If the right `R`-module `E` is projective as an `Rᵐᵒᵖ`-module, then `Tor¹_R(E, N)` is zero for
every left `R`-module `N`. -/
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

/-- Regular right module has zero Tor one.

For every left `R`-module `N`, `Tor¹_R(R, N)` is zero when `R` is given its regular right
action. -/
theorem bimoduleTensor_torFirst_one_regular :
    ∀ N : ModuleCat.{u} R,
      IsZero (((BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ R)).obj N) := by
  let e : Rᵐᵒᵖ ≃ₗ[Rᵐᵒᵖ] R := (MulOpposite.opLinearEquiv Rᵐᵒᵖ (M := R)).symm
  let : Module.Projective Rᵐᵒᵖ R := Module.Projective.of_equiv' e
  exact bimoduleTensor_torFirst_one_of_projective R R

end ModuleCat

namespace FGModuleCat

variable (R : Type u) [Ring R]

/-- Regular coefficient unitor with its scalar-action formula.

For a finite left `R`-module `M`, this data constructs an isomorphism `R ⊗_R M ≅ M` in the
finite-module category and records its forward formula `[r ⊗ m] ↦ r • m`. -/
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

/-- Regular bimodule tensor is the finite-module identity object.

The regular coefficient gives an isomorphism from `(FGModuleCat.bimoduleTensor R).obj M` to
the finite left module `M`. -/
def bimoduleTensorUnitIso (M : FGModuleCat.{u} R) :
    (bimoduleTensor (R := R) (S := R) R).obj M ≅ M :=
  (bimoduleTensorUnitData R M).1

/-- Finite-module regular unitor on pure classes.

The forward map of the regular coefficient unitor sends `[r ⊗ m]` to `r • m`. -/
theorem bimoduleTensorUnitIso_mk (M : FGModuleCat.{u} R) (r : R) (m : M) :
    letI : Module ℤ R := AddCommGroup.toIntModule R
    letI : Module ℤ M := Module.compHom M (algebraMap ℤ R)
    (bimoduleTensorUnitIso R M).hom.hom.hom
        (TensorProduct.Balanced.mk ℤ R R M r m) = r • m :=
  (bimoduleTensorUnitData R M).2 r m

/-- Regular coefficient tensor is naturally the finite-module identity.

The regular unitor gives a natural isomorphism from `FGModuleCat.bimoduleTensor R` to the
identity functor on `FGModuleCat R`. -/
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

/-- Coefficient equivalence transports right Tor-one vanishing.

Let `e : E ≃ₗ[S] E'` also preserve the right `R`-action. If `Tor¹_R(E, N)` is zero for every
left `R`-module `N`, then `Tor¹_R(E', N)` is zero for every such `N`. -/
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

/-- Coefficient map on each finite tensor object.

An `S`-linear map `f : E → E'` preserving the right `R`-action induces a morphism `E ⊗_R M ⟶
E' ⊗_R M` in the finite `S`-module category. -/
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

/-- Finite tensor coefficient map on pure classes.

The component induced by a compatible coefficient map `f` sends `[e ⊗ m]` to `[f e ⊗ m]`. -/
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

/-- Bimodule coefficient map as a finite tensor natural transformation.

An `S`-linear coefficient map preserving the right `R`-action induces a natural transformation
from tensoring by `E` to tensoring by `E'` on finite left `R`-modules. -/
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

/-- Identity coefficient gives the identity finite tensor transformation.

The natural transformation induced by the identity map on `E` is the identity of
`FGModuleCat.bimoduleTensor E`. -/
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

/-- Finite tensor coefficient transformations preserve composition.

For compatible bimodule maps `f : E → E'` and `g : E' → E''`, the transformation of `g.comp f`
equals the transformation of `f` followed by that of `g`. -/
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

/-- Bimodule coefficient equivalence gives a finite tensor natural isomorphism.

An `S`-linear equivalence `E ≃ₗ[S] E'` preserving the right `R`-action induces a natural
isomorphism between their tensor functors on finite left `R`-modules. -/
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
/-- Invertible bimodule contractions give finiteness and right flatness.

Let `P` be `R`-left and `S`-right and `Q` be `S`-left and `R`-right. Given bimodule
equivalences `P ⊗_S Q ≅ R` and `Q ⊗_R P ≅ S`, the left modules `P` and `Q` are finite, and
their right coefficients have zero `Tor¹` against every left module over `S` and `R`,
respectively. -/
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

/-- Morita equivalence from two invertible bimodule contractions.

Bimodule equivalences `P ⊗_S Q ≅ R` and `Q ⊗_R P ≅ S` construct a Morita equivalence over the
integer ground ring. Its functor is `Q ⊗_R -` and its inverse is `P ⊗_S -`. -/
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

/-- Forward functor of the contraction-based Morita equivalence.

The forward functor of `bimoduleTensorMoritaEquivalence R S P Q a ha b hb` is tensoring left
`R`-modules by the `S`-left, `R`-right coefficient `Q`. -/
theorem bimoduleTensorMoritaEquivalence_functor :
    (bimoduleTensorMoritaEquivalence R S P Q a ha b hb).eqv.functor =
      (BalancedTensor.Left.functor ℤ R S Q : ModuleCat.{u} R ⥤ ModuleCat.{u} S) := rfl

/-- Inverse functor of the contraction-based Morita equivalence.

The inverse functor of the bimodule contraction Morita equivalence is tensoring left
`S`-modules by the `R`-left, `S`-right coefficient `P`. -/
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

/-- Forward Morita tensor functor on finite modules.

The bimodule contractions give finite generation of `Q` over `S`, so tensoring by `Q`
restricts to a functor `FGModuleCat R ⥤ FGModuleCat S`. -/
def bimoduleTensorMoritaFunctor : FGModuleCat.{u} R ⥤ FGModuleCat.{u} S :=
  letI := (ModuleCat.bimoduleTensorMorita_properties R S P Q a ha b hb).2.1
  bimoduleTensor (R := R) (S := S) Q

/-- Inverse Morita tensor functor on finite modules.

The bimodule contractions give finite generation of `P` over `R`, so tensoring by `P`
restricts to a functor `FGModuleCat S ⥤ FGModuleCat R`. -/
def bimoduleTensorMoritaInverseFunctor : FGModuleCat.{u} S ⥤ FGModuleCat.{u} R :=
  letI := (ModuleCat.bimoduleTensorMorita_properties R S P Q a ha b hb).1
  bimoduleTensor (R := S) (S := R) P

/-- Forward finite tensor functor agrees with the Morita restriction.

The finite-module functor tensoring by `Q` equals the forward functor of the finite-module
equivalence induced by the contraction-based Morita equivalence. -/
theorem bimoduleTensorMoritaFunctor_eq :
    bimoduleTensorMoritaFunctor R S P Q a ha b hb =
      (ModuleCat.bimoduleTensorMoritaEquivalence
        R S P Q a ha b hb).fgModuleCatEquivalence.functor :=
  rfl

/-- Inverse finite tensor functor agrees with the Morita restriction.

The finite-module functor tensoring by `P` equals the inverse functor of the finite-module
equivalence induced by the contraction-based Morita equivalence. -/
theorem bimoduleTensorMoritaInverseFunctor_eq :
    bimoduleTensorMoritaInverseFunctor R S P Q a ha b hb =
      (ModuleCat.bimoduleTensorMoritaEquivalence
        R S P Q a ha b hb).fgModuleCatEquivalence.inverse :=
  rfl

end FGModuleCat
