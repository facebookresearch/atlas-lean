/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeTensorComparisons

/-!
# Canonical tensor sections of actual module sheaves

The section is the actual sectionwise tensor followed by the unit of the
native sheafification adjunction. It is not a supplied bilinear operation.
This integrates the completed native tensor/sheafification construction.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section


namespace MathlibExt.AlgebraicGeometry.SheafTensorSections

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry Opposite
open LineBundleTaskContracts AlgebraicLineBundleFamilies
open NativeTensorComparisons

variable (X : Scheme.{0}) (E F : X.Modules) (U : X.Opens)

abbrev Sections := E.val.obj (op U)

def tensorSection (e : E.val.obj (op U)) (f : F.val.obj (op U)) :
    (moduleTensor X E F).val.obj (op U) :=
  (((moduleAdjunction X).unit.app
    (((forgetModules X).obj E) ⊗ ((forgetModules X).obj F))).app (op U)).hom
      (e ⊗ₜ[Γ(X, U)] f)

@[simp] theorem tensorSection_zero_left (f : F.val.obj (op U)) :
    tensorSection X E F U 0 f = 0 := by
  rw [tensorSection, TensorProduct.zero_tmul]
  exact map_zero _

@[simp] theorem tensorSection_zero_right (e : E.val.obj (op U)) :
    tensorSection X E F U e 0 = 0 := by
  rw [tensorSection, TensorProduct.tmul_zero]
  exact map_zero _

@[simp] theorem tensorSection_add_left (a b : E.val.obj (op U)) (f : F.val.obj (op U)) :
    tensorSection X E F U (a + b) f =
      tensorSection X E F U a f + tensorSection X E F U b f := by
  simp only [tensorSection, TensorProduct.add_tmul]
  exact map_add _ _ _

@[simp] theorem tensorSection_add_right (e : E.val.obj (op U)) (a b : F.val.obj (op U)) :
    tensorSection X E F U e (a + b) =
      tensorSection X E F U e a + tensorSection X E F U e b := by
  simp only [tensorSection, TensorProduct.tmul_add]
  exact map_add _ _ _

@[simp] theorem tensorSection_smul_left (a : Γ(X, U))
    (e : E.val.obj (op U)) (f : F.val.obj (op U)) :
    tensorSection X E F U (a • e) f = a • tensorSection X E F U e f := by
  simp only [tensorSection, ← TensorProduct.smul_tmul']
  exact (((moduleAdjunction X).unit.app
    (((forgetModules X).obj E) ⊗ ((forgetModules X).obj F))).app (op U)).hom.map_smul a _

@[simp] theorem tensorSection_smul_right (a : Γ(X, U))
    (e : E.val.obj (op U)) (f : F.val.obj (op U)) :
    tensorSection X E F U e (a • f) = a • tensorSection X E F U e f := by
  simp only [tensorSection, TensorProduct.tmul_smul]
  exact map_smul _ _ _

theorem tensorSection_restriction (V : X.Opens) (h : V ≤ U)
    (e : E.val.obj (op U)) (f : F.val.obj (op U)) :
    ((moduleTensor X E F).val.map (homOfLE h).op).hom (tensorSection X E F U e f) =
      tensorSection X E F V ((E.val.map (homOfLE h).op).hom e)
        ((F.val.map (homOfLE h).op).hom f) := by
  symm
  exact PresheafOfModules.naturality_apply
    ((moduleAdjunction X).unit.app
      (((forgetModules X).obj E) ⊗ ((forgetModules X).obj F)))
    (homOfLE h).op (e ⊗ₜ[Γ(X, U)] f)

theorem tensorMap_tensorSection {E' F' : X.Modules} (a : E ⟶ E') (b : F ⟶ F')
    (e : E.val.obj (op U)) (f : F.val.obj (op U)) :
    ((tensorMap a b).val.app (op U)).hom (tensorSection X E F U e f) =
      tensorSection X E' F' U ((a.val.app (op U)).hom e) ((b.val.app (op U)).hom f) := by
  have h := (moduleAdjunction X).unit.naturality
    ((forgetModules X).map a ⊗ₘ (forgetModules X).map b)
  have he := congrArg (fun q ↦ (q.app (op U)).hom (e ⊗ₜ[Γ(X, U)] f)) h
  rw [tensorMap_eq]
  exact he.symm

def tensorCommutor : moduleTensor X E F ≅ moduleTensor X F E :=
  (sheafifyModules X).mapIso
    (β_ ((forgetModules X).obj E) ((forgetModules X).obj F))

theorem tensor_hom_ext {G : X.Modules} {f g : moduleTensor X E F ⟶ G}
    (h : ∀ (U : X.Opens) (e : E.val.obj (op U)) (s : F.val.obj (op U)),
      (f.val.app (op U)).hom (tensorSection X E F U e s) =
        (g.val.app (op U)).hom (tensorSection X E F U e s)) : f = g := by
  apply ((moduleAdjunction X).homEquiv
    (((forgetModules X).obj E) ⊗ ((forgetModules X).obj F)) G).injective
  ext1 U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro e s
  exact h U.unop e s

section Pullback

variable {Y Y' : Scheme.{0}}

/-- A section of `E` over `U`, pulled back along `f` to `f ⁻¹ᵁ U` through the unit of the
pullback/pushforward adjunction. -/
def pullSection (f : Y' ⟶ Y) (E : Y.Modules) (U : Y.Opens)
    (s : E.val.obj (op U)) : ((Scheme.Modules.pullback f).obj E).val.obj (op (f ⁻¹ᵁ U)) :=
  ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).val.app (op U)).hom s)

@[simp] theorem pullSection_zero (f : Y' ⟶ Y) (E : Y.Modules) (U : Y.Opens) :
    pullSection f E U 0 = 0 := map_zero _

@[simp] theorem pullSection_add (f : Y' ⟶ Y) (E : Y.Modules) (U : Y.Opens)
    (s t : E.val.obj (op U)) :
    pullSection f E U (s + t) = pullSection f E U s + pullSection f E U t := map_add _ _ _

/-- A comparison of the pullback of a tensor product with the tensor product of the pullbacks,
normalized on pulled-back pure tensor sections. -/
structure TensorPullbackComparison (f : Y' ⟶ Y) where
  iso : ∀ E F : Y.Modules,
    (Scheme.Modules.pullback f).obj (moduleTensor Y E F) ≅
      moduleTensor Y' ((Scheme.Modules.pullback f).obj E) ((Scheme.Modules.pullback f).obj F)
  pure : ∀ (E F : Y.Modules) (U : Y.Opens) (e : E.val.obj (op U)) (s : F.val.obj (op U)),
    (((iso E F).hom).val.app (op (f ⁻¹ᵁ U))).hom
      (pullSection f (moduleTensor Y E F) U (tensorSection Y E F U e s)) =
      tensorSection Y' ((Scheme.Modules.pullback f).obj E) ((Scheme.Modules.pullback f).obj F)
        (f ⁻¹ᵁ U) (pullSection f E U e) (pullSection f F U s)

end Pullback

end MathlibExt.AlgebraicGeometry.SheafTensorSections
