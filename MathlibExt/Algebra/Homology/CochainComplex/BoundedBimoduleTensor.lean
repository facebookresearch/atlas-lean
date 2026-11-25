/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BimoduleTensor
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedFunctor

/-!
# The original bounded finite-module bimodule tensor

The objects are the existing finite-support cochains of finite left
modules. Tensoring uses the existing finite-module functor in each
original degree. Forgetting finite generation gives the original ambient
cochain tensor with the same differentials and component maps.

The canonical right-flatness criterion earns preservation of ambient
quasi-isomorphisms. Original invertible bimodule contractions earn the
finite coefficients and give the actual bounded Morita equivalence.
Neither the bounded objects nor their ambient weak equivalences require
the finite-module categories to be abelian or their rings Noetherian.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace CochainComplex.Bounded

variable (R : Type u) [Ring R]

/-- The actual bounded finite-module inclusion, read in the original ambient module cochains. -/
abbrev fgModuleAmbient :
    Bounded (FGModuleCat.{u} R) ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  ι (FGModuleCat.{u} R) ⋙
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)

/-- The original ambient weak equivalences test the actual original bounded cochain map. -/
abbrev fgModuleQuasiIsomorphisms : MorphismProperty (Bounded (FGModuleCat.{u} R)) :=
  (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).inverseImage (fgModuleAmbient R)

/-- The whole weak-equivalence readout retains the original ambient cochain morphism. -/
theorem fgModuleQuasiIsomorphisms_iff {K L : Bounded (FGModuleCat.{u} R)} (f : K ⟶ L) :
    fgModuleQuasiIsomorphisms R f ↔ QuasiIso ((fgModuleAmbient R).map f) := Iff.rfl

variable {R}
variable {S : Type u} [Ring S]
  (E : Type u) [AddCommGroup E] [Module S E] [Module Rᵐᵒᵖ E]
  [SMulCommClass S Rᵐᵒᵖ E] [Module.Finite S E]

/-- Restrict the original finite-module tensor prolongation to its original bounded objects. -/
abbrev bimoduleTensor : Bounded (FGModuleCat.{u} R) ⥤ Bounded (FGModuleCat.{u} S) :=
  (FGModuleCat.bimoduleTensor (R := R) (S := S) E).mapCochainComplexBounded

/-- The actual output term is the existing original balanced tensor module. -/
theorem bimoduleTensor_obj_X_obj (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    (((bimoduleTensor (S := S) E).obj K).obj.X j).obj =
      (ModuleCat.BalancedTensor.Left.functor ℤ R S E).obj ((K.obj.X j).obj) := rfl

/-- The original bounded differential is the original module tensor of that differential. -/
theorem bimoduleTensor_obj_d_hom (K : Bounded (FGModuleCat.{u} R)) (i j : ℤ) :
    (((bimoduleTensor (S := S) E).obj K).obj.d i j).hom =
      (ModuleCat.BalancedTensor.Left.functor ℤ R S E).map ((K.obj.d i j).hom) := rfl

/-- The original bounded component map is the original module quotient map. -/
theorem bimoduleTensor_map_f_hom {K L : Bounded (FGModuleCat.{u} R)} (f : K ⟶ L) (j : ℤ) :
    (((bimoduleTensor (S := S) E).map f).hom.f j).hom =
      (ModuleCat.BalancedTensor.Left.functor ℤ R S E).map ((f.hom.f j).hom) := rfl

/-- Every actual bounded output term is finite on the target side. -/
theorem bimoduleTensor_obj_finite (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    Module.Finite S (((bimoduleTensor (S := S) E).obj K).obj.X j) := inferInstance

/-- The tensor preserves the same specified original support window term by term. -/
theorem bimoduleTensor_obj_isZero_outside (K : Bounded (FGModuleCat.{u} R)) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) (j : ℤ)
    (hj : j < a ∨ b < j) : IsZero (((bimoduleTensor (S := S) E).obj K).obj.X j) :=
  (FGModuleCat.bimoduleTensor (R := R) (S := S) E).map_isZero (hK j hj)

/-- Every actual bounded tensor differential retains the original ordered pure factors. -/
theorem bimoduleTensor_d_mk (K : Bounded (FGModuleCat.{u} R)) (i j : ℤ)
    (e : E) (x : K.obj.X i) :
    letI : Module ℤ (K.obj.X i) := Module.compHom (K.obj.X i) (algebraMap ℤ R)
    letI : Module ℤ (K.obj.X j) := Module.compHom (K.obj.X j) (algebraMap ℤ R)
    (((bimoduleTensor (S := S) E).obj K).obj.d i j).hom.hom
        (TensorProduct.Balanced.mk ℤ R E (K.obj.X i) e x) =
      TensorProduct.Balanced.mk ℤ R E (K.obj.X j) e ((K.obj.d i j).hom.hom x) := by
  let : Module ℤ (K.obj.X i) := Module.compHom (K.obj.X i) (algebraMap ℤ R)
  let : Module ℤ (K.obj.X j) := Module.compHom (K.obj.X j) (algebraMap ℤ R)
  exact FGModuleCat.bimoduleTensor_map_mk (R := R) (S := S) E (K.obj.d i j) e x

/-- An original bounded cochain map applies only its original module component to a pure class. -/
theorem bimoduleTensor_map_mk {K L : Bounded (FGModuleCat.{u} R)}
    (f : K ⟶ L) (j : ℤ) (e : E) (x : K.obj.X j) :
    letI : Module ℤ (K.obj.X j) := Module.compHom (K.obj.X j) (algebraMap ℤ R)
    letI : Module ℤ (L.obj.X j) := Module.compHom (L.obj.X j) (algebraMap ℤ R)
    (((bimoduleTensor (S := S) E).map f).hom.f j).hom.hom
        (TensorProduct.Balanced.mk ℤ R E (K.obj.X j) e x) =
      TensorProduct.Balanced.mk ℤ R E (L.obj.X j) e ((f.hom.f j).hom.hom x) := by
  let : Module ℤ (K.obj.X j) := Module.compHom (K.obj.X j) (algebraMap ℤ R)
  let : Module ℤ (L.obj.X j) := Module.compHom (L.obj.X j) (algebraMap ℤ R)
  exact FGModuleCat.bimoduleTensor_map_mk (R := R) (S := S) E (f.hom.f j) e x

/-- The original ambient square is the finite-tensor forgetting square prolonged degreewise. -/
def bimoduleTensorAmbientIso :
    bimoduleTensor (R := R) (S := S) E ⋙ fgModuleAmbient S ≅
      fgModuleAmbient R ⋙ ModuleCat.bimoduleTensorCochain (S := S) E := Iso.refl _

/-- The whole ambient comparison keeps the original tensor term identity. -/
theorem bimoduleTensorAmbientIso_hom_app_f (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    ((bimoduleTensorAmbientIso (S := S) E).hom.app K).f j =
      𝟙 ((ModuleCat.BalancedTensor.Left.functor ℤ R S E).obj ((K.obj.X j).obj)) := rfl

section RightFlat

variable (hE : ∀ N : ModuleCat.{u} R,
  IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ E)).obj N))

include hE

/-- Homology of the actual bounded output is tensor of the original ambient homology. -/
def bimoduleTensorAmbientHomologyIso (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    ((fgModuleAmbient S).obj ((bimoduleTensor (S := S) E).obj K)).homology j ≅
      (ModuleCat.BalancedTensor.Left.functor ℤ R S E).obj
        (((fgModuleAmbient R).obj K).homology j) :=
  ModuleCat.bimoduleTensorCochainHomologyIso E hE ((fgModuleAmbient R).obj K) j

/-- The whole original bounded ambient homology square uses the original cochain components. -/
theorem bimoduleTensorAmbientHomologyIso_hom_naturality
    {K L : Bounded (FGModuleCat.{u} R)} (f : K ⟶ L) (j : ℤ) :
    HomologicalComplex.homologyMap
        ((fgModuleAmbient S).map ((bimoduleTensor (S := S) E).map f)) j ≫
        (bimoduleTensorAmbientHomologyIso E hE L j).hom =
      (bimoduleTensorAmbientHomologyIso E hE K j).hom ≫
        (ModuleCat.BalancedTensor.Left.functor ℤ R S E).map
          (HomologicalComplex.homologyMap ((fgModuleAmbient R).map f) j) :=
  ModuleCat.bimoduleTensorCochainHomologyIso_hom_naturality E hE
    ((fgModuleAmbient R).map f) j

/-- Right flatness preserves every original ambient quasi-isomorphism of bounded finite modules. -/
theorem bimoduleTensor_ambientQuasiIso {K L : Bounded (FGModuleCat.{u} R)} (f : K ⟶ L)
    (hf : QuasiIso ((fgModuleAmbient R).map f)) :
    QuasiIso ((fgModuleAmbient S).map ((bimoduleTensor (S := S) E).map f)) := by
  let : QuasiIso ((fgModuleAmbient R).map f) := hf
  exact ModuleCat.bimoduleTensorCochain_quasiIso E hE ((fgModuleAmbient R).map f)

/-- The actual bounded tensor is a morphism of the original ambient quasi-isomorphism classes. -/
theorem bimoduleTensor_map_quasiIsomorphisms :
    fgModuleQuasiIsomorphisms R ≤
      (fgModuleQuasiIsomorphisms S).inverseImage (bimoduleTensor (S := S) E) := by
  intro K L f hf
  exact bimoduleTensor_ambientQuasiIso E hE f hf

end RightFlat

end CochainComplex.Bounded

namespace CochainComplex.Bounded

variable (R : Type u) [Ring R]

/-- The original regular unitor restricts to the actual bounded cochains. -/
def bimoduleTensorRegularIso :
    bimoduleTensor (R := R) (S := R) R ≅ 𝟭 (Bounded (FGModuleCat.{u} R)) :=
  NatIso.mapCochainComplexBounded (FGModuleCat.bimoduleTensorUnitNatIso R) ≪≫
    Functor.mapCochainComplexBoundedIdIso

/-- The bounded regular comparison retains the original regular component. -/
theorem bimoduleTensorRegularIso_hom_app_f (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    ((bimoduleTensorRegularIso R).hom.app K).hom.f j =
      (FGModuleCat.bimoduleTensorUnitIso R (K.obj.X j)).hom := by
  simp [bimoduleTensorRegularIso, Functor.mapCochainComplexBoundedIdIso,
    NatIso.mapCochainComplexBounded, NatTrans.mapCochainComplexBounded,
    FGModuleCat.bimoduleTensorUnitNatIso]

/-- The actual bounded regular unitor multiplies the original pure coefficient into the term. -/
theorem bimoduleTensorRegularIso_mk (K : Bounded (FGModuleCat.{u} R)) (j : ℤ)
    (r : R) (x : K.obj.X j) :
    letI : Module ℤ R := AddCommGroup.toIntModule R
    letI : Module ℤ (K.obj.X j) := Module.compHom (K.obj.X j) (algebraMap ℤ R)
    (((bimoduleTensorRegularIso R).hom.app K).hom.f j).hom.hom
        (TensorProduct.Balanced.mk ℤ R R (K.obj.X j) r x) = r • x := by
  rw [bimoduleTensorRegularIso_hom_app_f]
  exact FGModuleCat.bimoduleTensorUnitIso_mk R (K.obj.X j) r x

variable {R}
variable {S : Type u} [Ring S]
  {E E' : Type u} [AddCommGroup E] [AddCommGroup E']
  [Module S E] [Module S E'] [Module Rᵐᵒᵖ E] [Module Rᵐᵒᵖ E']
  [SMulCommClass S Rᵐᵒᵖ E] [SMulCommClass S Rᵐᵒᵖ E']
  [Module.Finite S E] [Module.Finite S E']

/-- The original coefficient map gives its actual original bounded cochain transformation. -/
def bimoduleTensorTransformation (f : E →ₗ[S] E')
    (hR : ∀ (r : R) (e : E), f (MulOpposite.op r • e) = MulOpposite.op r • f e) :
    bimoduleTensor (R := R) (S := S) E ⟶ bimoduleTensor (R := R) (S := S) E' :=
  NatTrans.mapCochainComplexBounded (FGModuleCat.bimoduleTensorTransformation f hR)

/-- Every actual bounded coefficient component is the original quotient coefficient map. -/
theorem bimoduleTensorTransformation_app_f (f : E →ₗ[S] E')
    (hR : ∀ (r : R) (e : E), f (MulOpposite.op r • e) = MulOpposite.op r • f e)
    (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    ((bimoduleTensorTransformation f hR).app K).hom.f j =
      FGModuleCat.bimoduleTensorCoefficientComponent f hR (K.obj.X j) := rfl

/-- An original coefficient isomorphism restricts with its actual original inverse. -/
def bimoduleTensorCoefficientIso (e : E ≃ₗ[S] E')
    (hR : ∀ (r : R) (x : E), e (MulOpposite.op r • x) = MulOpposite.op r • e x) :
    bimoduleTensor (R := R) (S := S) E ≅ bimoduleTensor (R := R) (S := S) E' :=
  NatIso.mapCochainComplexBounded (FGModuleCat.bimoduleTensorIso e hR)

/-- The original coefficient comparison remains the actual component on every bounded term. -/
theorem bimoduleTensorCoefficientIso_hom_app_f (e : E ≃ₗ[S] E')
    (hR : ∀ (r : R) (x : E), e (MulOpposite.op r • x) = MulOpposite.op r • e x)
    (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    ((bimoduleTensorCoefficientIso e hR).hom.app K).hom.f j =
      (FGModuleCat.bimoduleTensorIso e hR).hom.app (K.obj.X j) := rfl

end CochainComplex.Bounded

namespace CochainComplex.Bounded

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]
  (E F : Type u) [AddCommGroup E] [AddCommGroup F]
  [Module S E] [Module Rᵐᵒᵖ E] [SMulCommClass S Rᵐᵒᵖ E] [Module.Finite S E]
  [Module T F] [Module Sᵐᵒᵖ F] [SMulCommClass T Sᵐᵒᵖ F] [Module.Finite T F]

/-- The original composite coefficient is prolonged and restricted to original bounded cochains. -/
abbrev bimoduleTensorComposite : Bounded (FGModuleCat.{u} R) ⥤ Bounded (FGModuleCat.{u} T) :=
  Functor.mapCochainComplexBounded
    (FGModuleCat.bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F)

/-- The actual bounded associator is the original finite-module tensor associator in each degree. -/
def bimoduleTensorCompIso :
    bimoduleTensorComposite (R := R) (S := S) (T := T) E F ≅
      bimoduleTensor (R := R) (S := S) E ⋙ bimoduleTensor (R := S) (S := T) F :=
  NatIso.mapCochainComplexBounded
    (FGModuleCat.bimoduleTensorCompNatIso (R := R) (S := S) (T := T) E F) ≪≫
      (Functor.mapCochainComplexBoundedCompIso
        (FGModuleCat.bimoduleTensor (R := R) (S := S) E)
        (FGModuleCat.bimoduleTensor (R := S) (S := T) F)).symm

/-- The entire actual bounded associator component is the original finite-module component. -/
theorem bimoduleTensorCompIso_hom_app_f (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    ((bimoduleTensorCompIso (R := R) (S := S) (T := T) E F).hom.app K).hom.f j =
      (FGModuleCat.bimoduleTensorCompIso (R := R) (S := S) (T := T) E F (K.obj.X j)).hom := by
  simp [bimoduleTensorCompIso, Functor.mapCochainComplexBoundedCompIso,
    NatIso.mapCochainComplexBounded, NatTrans.mapCochainComplexBounded,
    FGModuleCat.bimoduleTensorCompNatIso]

end CochainComplex.Bounded

namespace CochainComplex.Bounded

variable (R S P Q : Type u) [Ring R] [Ring S]
  [AddCommGroup P] [AddCommGroup Q]
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

local notation "e₀" => ModuleCat.bimoduleTensorMoritaEquivalence R S P Q a ha b hb

/-- Original Morita contractions give the actual bounded finite-module tensor equivalence. -/
def bimoduleTensorMoritaEquivalence :
    Bounded (FGModuleCat.{u} R) ≌ Bounded (FGModuleCat.{u} S) :=
  (e₀).fgModuleCatEquivalence.mapCochainComplexBounded

/-- Its forward functor is precisely the original bounded Q tensor with earned finiteness. -/
theorem bimoduleTensorMoritaEquivalence_functor :
    (bimoduleTensorMoritaEquivalence R S P Q a ha b hb).functor =
      letI := (ModuleCat.bimoduleTensorMorita_properties R S P Q a ha b hb).2.1
      bimoduleTensor (R := R) (S := S) Q := rfl

/-- Its inverse is precisely the original bounded P tensor with earned finiteness. -/
theorem bimoduleTensorMoritaEquivalence_inverse :
    (bimoduleTensorMoritaEquivalence R S P Q a ha b hb).inverse =
      letI := (ModuleCat.bimoduleTensorMorita_properties R S P Q a ha b hb).1
      bimoduleTensor (R := S) (S := R) P := rfl

/-- The bounded unit is the original finite Morita unit on each original term. -/
theorem bimoduleTensorMoritaEquivalence_unitIso_hom_app_f
    (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    ((bimoduleTensorMoritaEquivalence R S P Q a ha b hb).unitIso.hom.app K).hom.f j =
      (e₀).fgModuleCatEquivalence.unitIso.hom.app (K.obj.X j) :=
  Equivalence.mapCochainComplexBounded_unitIso_hom_app_f _ K j

/-- The bounded counit is the original finite Morita counit on each original term. -/
theorem bimoduleTensorMoritaEquivalence_counitIso_hom_app_f
    (K : Bounded (FGModuleCat.{u} S)) (j : ℤ) :
    ((bimoduleTensorMoritaEquivalence R S P Q a ha b hb).counitIso.hom.app K).hom.f j =
      (e₀).fgModuleCatEquivalence.counitIso.hom.app (K.obj.X j) :=
  Equivalence.mapCochainComplexBounded_counitIso_hom_app_f _ K j

/-- Forgetting both finite and bounded restrictions retains the whole original module unit. -/
theorem bimoduleTensorMoritaEquivalence_unitIso_module
    (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    (((bimoduleTensorMoritaEquivalence R S P Q a ha b hb).unitIso.hom.app K).hom.f j).hom =
      (e₀).eqv.unitIso.hom.app ((K.obj.X j).obj) := by
  rw [bimoduleTensorMoritaEquivalence_unitIso_hom_app_f]
  rfl

/-- Forgetting both restrictions retains the whole original module contraction counit. -/
theorem bimoduleTensorMoritaEquivalence_counitIso_module
    (K : Bounded (FGModuleCat.{u} S)) (j : ℤ) :
    (((bimoduleTensorMoritaEquivalence R S P Q a ha b hb).counitIso.hom.app K).hom.f j).hom =
      (e₀).eqv.counitIso.hom.app ((K.obj.X j).obj) := by
  rw [bimoduleTensorMoritaEquivalence_counitIso_hom_app_f]
  rfl

/-- The actual original forward Morita tensor preserves every ambient weak equivalence. -/
theorem bimoduleTensorMoritaEquivalence_map_quasiIsomorphisms :
    fgModuleQuasiIsomorphisms R ≤ (fgModuleQuasiIsomorphisms S).inverseImage
      (bimoduleTensorMoritaEquivalence R S P Q a ha b hb).functor := by
  let H := ModuleCat.bimoduleTensorMorita_properties R S P Q a ha b hb
  let : Module.Finite S Q := H.2.1
  exact bimoduleTensor_map_quasiIsomorphisms (R := R) (S := S) Q H.2.2.2

/-- The actual original inverse Morita tensor preserves every ambient weak equivalence. -/
theorem bimoduleTensorMoritaEquivalence_inverse_map_quasiIsomorphisms :
    fgModuleQuasiIsomorphisms S ≤ (fgModuleQuasiIsomorphisms R).inverseImage
      (bimoduleTensorMoritaEquivalence R S P Q a ha b hb).inverse := by
  let H := ModuleCat.bimoduleTensorMorita_properties R S P Q a ha b hb
  let : Module.Finite R P := H.1
  exact bimoduleTensor_map_quasiIsomorphisms (R := S) (S := R) P H.2.2.1

end CochainComplex.Bounded

end
