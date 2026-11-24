/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeDeRhamDifferential
public import MathlibExt.AlgebraicGeometry.IntegrableHiggsBundles

/-!
# Actual relative lambda-connections and their curvature

The parameter is a base section on T, pulled back to Y. Its actual relative
differential is zero. Connections act additively on every native bundle
section and satisfy the precise lambda-Leibniz rule. Their extended degree-one
operator is fixed on every actual tensor section by
`nabla(e⊗omega)=nabla(e)∧omega+lambda e⊗d(omega)` and restriction naturality.
Curvature is the literal composite of those two operators.

Source: Simpson, *The Hodge filtration on nonabelian cohomology*,
alg-geom/9604005v1, section 4 and Proposition 4.1. Ordinary de Rham differential
producer/normalization credits are in `RelativeDeRhamDifferential`.
Operators are linear over the actual pulled-back base coefficients.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section


namespace MathlibExt.AlgebraicGeometry.AlgebraicLambdaConnections

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry Opposite
open RelativeDifferentialForms RelativeDeRhamDifferential SheafTensorSections
open LineBundleTaskContracts AlgebraicLineBundleFamilies NativeTensorComparisons
open CoherentCurveLinearSeries CurveVectorBundles

variable {Y T : Scheme.{0}} (pi : Y ⟶ T) (lambda : Γ(T, ⊤)) (D : Differential pi)

def bundleWedge (E : Y.Modules) :
    moduleTensor Y (moduleTensor Y E (forms pi 1)) (forms pi 1) ⟶
      moduleTensor Y E (forms pi 2) :=
  (tensorAssociator Y E (forms pi 1) (forms pi 1)).hom ≫
    tensorMap (𝟙 E) (wedge pi)

def leftBundleWedge (E : Y.Modules) :
    moduleTensor Y (forms pi 1) (moduleTensor Y E (forms pi 1)) ⟶
      moduleTensor Y E (forms pi 2) :=
  (tensorAssociator Y (forms pi 1) E (forms pi 1)).inv ≫
    tensorMap (tensorCommutor Y (forms pi 1) E).hom (𝟙 (forms pi 1)) ≫ bundleWedge pi E

structure RawConnection where
  rank : ℕ
  object : Y.Modules
  bundle : IsVectorBundle object rank
  nabla0 : ∀ U : Y.Opens, object.val.obj (op U) →+
    (moduleTensor Y object (forms pi 1)).val.obj (op U)
  restriction0 : ∀ (U V : Y.Opens) (h : V ≤ U) (s : object.val.obj (op U)),
    nabla0 V ((object.val.map (homOfLE h).op).hom s) =
      ((moduleTensor Y object (forms pi 1)).val.map (homOfLE h).op).hom (nabla0 U s)
  leibniz : ∀ (U : Y.Opens) (a : Γ(Y, U)) (s : object.val.obj (op U)),
    nabla0 U (a • s) = lambdaOnOpen pi lambda U •
      tensorSection Y object (forms pi 1) U s ((d0 pi).d a) + a • nabla0 U s
  nabla1 : ∀ U : Y.Opens, (moduleTensor Y object (forms pi 1)).val.obj (op U) →+
    (moduleTensor Y object (forms pi 2)).val.obj (op U)
  restriction1 : ∀ (U V : Y.Opens) (h : V ≤ U)
      (s : (moduleTensor Y object (forms pi 1)).val.obj (op U)),
    nabla1 V (((moduleTensor Y object (forms pi 1)).val.map (homOfLE h).op).hom s) =
      ((moduleTensor Y object (forms pi 2)).val.map (homOfLE h).op).hom (nabla1 U s)
  extension : ∀ (U : Y.Opens) (s : object.val.obj (op U)) (omega : (forms pi 1).val.obj (op U)),
    nabla1 U (tensorSection Y object (forms pi 1) U s omega) =
      ((bundleWedge pi object).val.app (op U)).hom
        (tensorSection Y (moduleTensor Y object (forms pi 1)) (forms pi 1) U (nabla0 U s) omega) +
      lambdaOnOpen pi lambda U • tensorSection Y object (forms pi 2) U s (D.map U omega)
  leibniz1 : ∀ (U : Y.Opens) (a : Γ(Y, U))
      (s : (moduleTensor Y object (forms pi 1)).val.obj (op U)),
    nabla1 U (a • s) = lambdaOnOpen pi lambda U •
      ((leftBundleWedge pi object).val.app (op U)).hom
        (tensorSection Y (forms pi 1) (moduleTensor Y object (forms pi 1)) U ((d0 pi).d a) s) +
      a • nabla1 U s
  baseLinear1 : ∀ (V : T.Opens) (U : Y.Opens) (h : U ≤ pi ⁻¹ᵁ V) (a : Γ(T, V))
      (s : (moduleTensor Y object (forms pi 1)).val.obj (op U)),
    nabla1 U ((pi.appLE V U h).hom a • s) = (pi.appLE V U h).hom a • nabla1 U s

variable {pi lambda D}

def RawConnection.curvature (N : RawConnection pi lambda D) (U : Y.Opens) :
    N.object.val.obj (op U) →+ (moduleTensor Y N.object (forms pi 2)).val.obj (op U) :=
  (N.nabla1 U).comp (N.nabla0 U)

theorem RawConnection.baseLinear0 (N : RawConnection pi lambda D)
    (V : T.Opens) (U : Y.Opens) (h : U ≤ pi ⁻¹ᵁ V) (a : Γ(T, V))
    (s : N.object.val.obj (op U)) :
    N.nabla0 U ((pi.appLE V U h).hom a • s) = (pi.appLE V U h).hom a • N.nabla0 U s := by
  rw [N.leibniz, d0_base_section, tensorSection_zero_right, smul_zero, zero_add]

structure LambdaConnection (pi : Y ⟶ T) (lambda : Γ(T, ⊤)) (D : Differential pi)
    extends RawConnection pi lambda D where
  integrable : ∀ (U : Y.Opens) (s : object.val.obj (op U)), nabla1 U (nabla0 U s) = 0

namespace LambdaConnection

structure Hom (E F : LambdaConnection pi lambda D) where
  map : E.object ⟶ F.object
  connection : ∀ (U : Y.Opens) (s : E.object.val.obj (op U)),
    ((tensorMap map (𝟙 (forms pi 1))).val.app (op U)).hom (E.nabla0 U s) =
      F.nabla0 U ((map.val.app (op U)).hom s)

@[ext] theorem Hom.ext {E F : LambdaConnection pi lambda D} {f g : Hom E F}
    (h : f.map = g.map) : f = g := by cases f; cases g; cases h; rfl

def Hom.comp {E F G : LambdaConnection pi lambda D} (f : Hom E F) (g : Hom F G) : Hom E G where
  map := f.map ≫ g.map
  connection U s := by
    have hc : tensorMap (f.map ≫ g.map) (𝟙 (forms pi 1)) =
        tensorMap f.map (𝟙 (forms pi 1)) ≫ tensorMap g.map (𝟙 (forms pi 1)) := by
      rw [← Category.id_comp (𝟙 (forms pi 1)), tensorMap_comp]
      simp
    rw [hc]
    change ((tensorMap g.map (𝟙 (forms pi 1))).val.app (op U)).hom
      (((tensorMap f.map (𝟙 (forms pi 1))).val.app (op U)).hom (E.nabla0 U s)) =
        G.nabla0 U ((g.map.val.app (op U)).hom ((f.map.val.app (op U)).hom s))
    rw [f.connection, g.connection]

instance : Category (LambdaConnection pi lambda D) where
  Hom E F := Hom E F
  id E := ⟨𝟙 _, by intro U s; simp; rfl⟩
  comp f g := Hom.comp f g
  id_comp f := by apply Hom.ext; exact Category.id_comp _
  comp_id f := by apply Hom.ext; exact Category.comp_id _
  assoc f g h := by apply Hom.ext; exact Category.assoc _ _ _

def forget : LambdaConnection pi lambda D ⥤ Y.Modules where
  obj E := E.object
  map f := f.map
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (forget (pi := pi) (lambda := lambda) (D := D)).Faithful where
  map_injective h := by apply Hom.ext; exact h

end LambdaConnection

/-- For parameter zero the actual section operator is O-linear. -/
def zeroLinearMap (N : LambdaConnection pi 0 D) (U : Y.Opens) :
    N.object.val.obj (op U) →ₗ[Y.ringCatSheaf.obj.obj (op U)]
      (moduleTensor Y N.object (forms pi 1)).val.obj (op U) where
  toFun := N.nabla0 U
  map_add' := (N.nabla0 U).map_add
  map_smul' a s := by
    rw [N.leibniz]
    simp [lambdaOnOpen]

/-- The zero-fibre Higgs field is the actual same operator. -/
def zeroTheta (N : LambdaConnection pi 0 D) : N.object ⟶ moduleTensor Y N.object (forms pi 1) where
  val :=
    { app U := ConcreteCategory.ofHom (C := ModuleCat (Y.ringCatSheaf.obj.obj U))
        (zeroLinearMap N U.unop)
      naturality {U V} f := by
        apply ModuleCat.hom_ext
        ext s
        exact N.restriction0 U.unop V.unop f.unop.le s }

def relativeHiggsSquare {E : Y.Modules} (theta : E ⟶ moduleTensor Y E (forms pi 1)) :
    E ⟶ moduleTensor Y E (forms pi 2) :=
  theta ≫ tensorMap theta (𝟙 (forms pi 1)) ≫ bundleWedge pi E

def zeroLinearMap1 (N : LambdaConnection pi 0 D) (U : Y.Opens) :
    (moduleTensor Y N.object (forms pi 1)).val.obj (op U) →ₗ[Y.ringCatSheaf.obj.obj (op U)]
      (moduleTensor Y N.object (forms pi 2)).val.obj (op U) where
  toFun := N.nabla1 U
  map_add' := (N.nabla1 U).map_add
  map_smul' a s := by
    rw [N.leibniz1]
    simp [lambdaOnOpen]

def zeroExtendedTheta (N : LambdaConnection pi 0 D) :
    moduleTensor Y N.object (forms pi 1) ⟶ moduleTensor Y N.object (forms pi 2) where
  val :=
    { app U := ConcreteCategory.ofHom (C := ModuleCat (Y.ringCatSheaf.obj.obj U))
        (zeroLinearMap1 N U.unop)
      naturality {U V} f := by
        apply ModuleCat.hom_ext
        ext s
        exact N.restriction1 U.unop V.unop f.unop.le s }

theorem zeroExtendedTheta_eq (N : LambdaConnection pi 0 D) :
    zeroExtendedTheta N = tensorMap (zeroTheta N) (𝟙 (forms pi 1)) ≫
      bundleWedge pi N.object := by
  apply tensor_hom_ext Y N.object (forms pi 1)
  intro U e omega
  change N.nabla1 U (tensorSection Y N.object (forms pi 1) U e omega) =
    ((bundleWedge pi N.object).val.app (op U)).hom
      (((tensorMap (zeroTheta N) (𝟙 (forms pi 1))).val.app (op U)).hom
        (tensorSection Y N.object (forms pi 1) U e omega))
  rw [tensorMap_tensorSection]
  change N.nabla1 U (tensorSection Y N.object (forms pi 1) U e omega) =
    ((bundleWedge pi N.object).val.app (op U)).hom
      (tensorSection Y (moduleTensor Y N.object (forms pi 1)) (forms pi 1) U
        (N.nabla0 U e) omega)
  simpa only [lambdaOnOpen, map_zero, zero_smul, add_zero] using N.extension U e omega

theorem zeroTheta_integrable (N : LambdaConnection pi 0 D) :
    relativeHiggsSquare (zeroTheta N) = 0 := by
  rw [relativeHiggsSquare, ← zeroExtendedTheta_eq]
  apply SheafOfModules.hom_ext
  ext1 U
  apply ModuleCat.hom_ext
  ext s
  exact N.integrable U.unop s

/-- Parameter one is the ordinary integrable connection carrier with its
literal universal differential and extended curvature operator. -/
abbrev FlatConnection := LambdaConnection pi (1 : Γ(T, ⊤)) D

end MathlibExt.AlgebraicGeometry.AlgebraicLambdaConnections
