/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeRingInverseImages
public import MathlibExt.CategoryTheory.StructuralDeRhamPeriodSources

/-!
# Structural period connection source on native period objects

The target differential module is the actual original-form scalar
extension. The positive derivation is fixed by d on the ORIGINAL O_X,
zero on absolute B_dR+, naturality and theta-adic continuity using
actual ideal SHEAF powers. The one-form differential is fixed by the
original exact forms and the exterior Leibniz rule; integrability is
the literal square-zero equation.

Full structural periods invert local ABSOLUTE generators with derivative
zero. The full connection is fixed on every original local fraction.
No global generator, nonunit-p or prime-characteristic hypothesis is
imposed on all full-site section rings.

References: Scholze, arXiv:1205.3463v2, Definition 6.8,
Proposition 6.10 and Corollary 6.13; native Mathlib module/sheaf operators,
Apache 2.0, revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.StructuralPeriodConnectionSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry.GeneralPadicCoefficientFields
open RingedDerivedCoefficientOperations RingSheafModuleTensors NativeRingInverseImages
open SheafKernelCompletionMaps StructuralDeRhamPeriodSources
open SheafLocalGeneratorLocalization UntiltingSheafSources

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [UnivLE.{max u v, 1}] [HasSheafify J CommRingCat.{1}]
  [HasSheafify J AddCommGrpCat.{1}] [J.WEqualsLocallyBijective AddCommGrpCat.{1}]
  (p : ℕ) [Fact p.Prime] (K : BaseField p)
  (O Rplus : Sheaf J CommRingCat.{1}) (A : UntiltingData p Rplus)
  (W : WittScalarSource p K O Rplus A) (Ω : Modules O)
  [(pushforward (𝟭 C) O W.naiveStructuralPositive W.originalToPositive).IsRightAdjoint]
  [(pushforward (𝟭 C) W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).IsRightAdjoint]

def positiveForms : Modules W.naiveStructuralPositive :=
  (pullback (𝟭 C) O W.naiveStructuralPositive W.originalToPositive).obj Ω

def originalFormUnit (U : Cᵒᵖ) : Ω.val.obj U →+
    (positiveForms p K O Rplus A W Ω).val.obj U :=
  (((adjunction (𝟭 C) O W.naiveStructuralPositive W.originalToPositive).unit.app Ω).val.app U).hom.toAddMonoidHom

def fullForms : Modules W.naiveStructuralFull :=
  (pullback (𝟭 C) W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).obj
    (positiveForms p K O Rplus A W Ω)

def positiveFormUnit (U : Cᵒᵖ) : (positiveForms p K O Rplus A W Ω).val.obj U →+
    (fullForms p K O Rplus A W Ω).val.obj U :=
  (((adjunction (𝟭 C) W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).unit.app
    (positiveForms p K O Rplus A W Ω)).val.app U).hom.toAddMonoidHom

/-- The actual ideal-sheaf/module product: minimal native sheaf submodule containing its products. -/
def idealTimesForms (n : ℕ) : (positiveForms p K O Rplus A W Ω).Submodule :=
  sInf {N | ∀ (U : Cᵒᵖ) (r : W.naiveStructuralPositive.obj.obj U)
    (m : (positiveForms p K O Rplus A W Ω).val.obj U),
    r ∈ WittScalarSource.naiveStructuralPositiveFiltration p K O Rplus A W n U →
      r • m ∈ N.toSubmodule.obj U}

variable (d : ∀ U : Cᵒᵖ, O.obj.obj U →+ Ω.val.obj U)

structure PositiveConnectionSource where
  connection : ∀ U : Cᵒᵖ, W.naiveStructuralPositive.obj.obj U →+
    (positiveForms p K O Rplus A W Ω).val.obj U
  natural : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (r : W.naiveStructuralPositive.obj.obj U),
    connection V ((W.naiveStructuralPositive.obj.map f).hom r) =
      (positiveForms p K O Rplus A W Ω).val.map f (connection U r)
  leibniz : ∀ U r s, connection U (r * s) = r • connection U s + s • connection U r
  original_source : ∀ U a,
    connection U ((W.originalToPositive.hom.app U).hom a) = originalFormUnit p K O Rplus A W Ω U (d U a)
  absolute_source : ∀ U b, connection U ((W.absoluteToPositive.hom.app U).hom b) = 0
  theta_continuity : ∀ (n : ℕ) (U : Cᵒᵖ) (r : W.naiveStructuralPositive.obj.obj U),
    r ∈ WittScalarSource.naiveStructuralPositiveFiltration p K O Rplus A W (n + 1) U →
      connection U r ∈ (idealTimesForms p K O Rplus A W Ω n).toSubmodule.obj U
  oneFormDifferential : ∀ U : Cᵒᵖ, (positiveForms p K O Rplus A W Ω).val.obj U →+
    (exterior W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) 2).val.obj U
  oneForm_natural : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) m,
    oneFormDifferential V ((positiveForms p K O Rplus A W Ω).val.map f m) =
      (exterior W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) 2).val.map f
        (oneFormDifferential U m)
  oneForm_leibniz : ∀ (U : Cᵒᵖ) (r : W.naiveStructuralPositive.obj.obj U)
    (m : (positiveForms p K O Rplus A W Ω).val.obj U),
    oneFormDifferential U (r • m) = r • oneFormDifferential U m +
      exteriorUnit W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) 2 U
        (_root_.exteriorPower.ιMulti (W.naiveStructuralPositive.obj.obj U) 2
          (fun i : Fin 2 => if i = 0 then connection U r else m))
  oneForm_original : ∀ U a,
    oneFormDifferential U (originalFormUnit p K O Rplus A W Ω U (d U a)) = 0
  integrable : ∀ U r, oneFormDifferential U (connection U r) = 0

def localGeneratorPower (U : Cᵒᵖ) (t : A.deRhamPositive.obj.obj U)
    (ht : IsLocalGenerator A.deRhamPositive (completedRegular p Rplus) A.completedTheta U t)
    (j : ℤ) : W.naiveStructuralFull.obj.obj U :=
  Units.val (generatorUnit A.deRhamPositive (completedRegular p Rplus) W.naiveStructuralPositive
    A.completedTheta W.absoluteToPositive U t ht ^ j)

def formSemilinearUnit (U : Cᵒᵖ) :
    (positiveForms p K O Rplus A W Ω).val.obj U →ₛₗ[(W.positiveToFull.hom.app U).hom]
      (fullForms p K O Rplus A W Ω).val.obj U where
  toFun := positiveFormUnit p K O Rplus A W Ω U
  map_add' := map_add (positiveFormUnit p K O Rplus A W Ω U)
  map_smul' r m :=
    (((adjunction (𝟭 C) W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).unit.app
      (positiveForms p K O Rplus A W Ω)).val.app U).hom.map_smul r m

def originalFormSemilinearUnit (U : Cᵒᵖ) : Ω.val.obj U →ₛₗ[(W.originalToPositive.hom.app U).hom]
    (positiveForms p K O Rplus A W Ω).val.obj U where
  toFun := originalFormUnit p K O Rplus A W Ω U
  map_add' := map_add (originalFormUnit p K O Rplus A W Ω U)
  map_smul' r m :=
    (((adjunction (𝟭 C) O W.naiveStructuralPositive W.originalToPositive).unit.app Ω).val.app U).hom.map_smul r m

def originalFullFormSemilinearUnit (U : Cᵒᵖ) : Ω.val.obj U →ₛₗ[(W.originalToFull.hom.app U).hom]
    (fullForms p K O Rplus A W Ω).val.obj U := by
  letI : RingHomCompTriple (W.originalToPositive.hom.app U).hom (W.positiveToFull.hom.app U).hom
      (W.originalToFull.hom.app U).hom := ⟨by rfl⟩
  exact (formSemilinearUnit p K O Rplus A W Ω U).comp
    (originalFormSemilinearUnit p K O Rplus A W Ω U)

/-- Full connection source: every local absolute-generator fraction is normalized. -/
structure FullConnectionSource (P : PositiveConnectionSource p K O Rplus A W Ω d) where
  connection : ∀ U : Cᵒᵖ, W.naiveStructuralFull.obj.obj U →+
    (fullForms p K O Rplus A W Ω).val.obj U
  natural : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (r : W.naiveStructuralFull.obj.obj U),
    connection V ((W.naiveStructuralFull.obj.map f).hom r) =
      (fullForms p K O Rplus A W Ω).val.map f (connection U r)
  leibniz : ∀ U r s, connection U (r * s) = r • connection U s + s • connection U r
  local_fraction_source : ∀ (U : Cᵒᵖ) (t : A.deRhamPositive.obj.obj U)
    (ht : IsLocalGenerator A.deRhamPositive (completedRegular p Rplus) A.completedTheta U t)
    (j : ℤ) (r : W.naiveStructuralPositive.obj.obj U),
    connection U
      (localGeneratorPower p K O Rplus A W U t ht (-j) * (W.positiveToFull.hom.app U).hom r) =
      localGeneratorPower p K O Rplus A W U t ht (-j) •
        positiveFormUnit p K O Rplus A W Ω U (P.connection U r)
  positiveTwoMap : ∀ U : Cᵒᵖ,
    (exterior W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) 2).val.obj U →+
      (exterior W.naiveStructuralFull (fullForms p K O Rplus A W Ω) 2).val.obj U
  positiveTwo_source : ∀ (U : Cᵒᵖ)
    (w : ⋀[W.naiveStructuralPositive.obj.obj U]^2 ((positiveForms p K O Rplus A W Ω).val.obj U)),
    positiveTwoMap U (exteriorUnit W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) 2 U w) =
      exteriorUnit W.naiveStructuralFull (fullForms p K O Rplus A W Ω) 2 U
        (ExteriorAlgebra.powMapₛₗ 2 (W.positiveToFull.hom.app U).hom
          (formSemilinearUnit p K O Rplus A W Ω U) w)
  oneFormDifferential : ∀ U : Cᵒᵖ, (fullForms p K O Rplus A W Ω).val.obj U →+
    (exterior W.naiveStructuralFull (fullForms p K O Rplus A W Ω) 2).val.obj U
  oneForm_natural : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) m,
    oneFormDifferential V ((fullForms p K O Rplus A W Ω).val.map f m) =
      (exterior W.naiveStructuralFull (fullForms p K O Rplus A W Ω) 2).val.map f (oneFormDifferential U m)
  oneForm_leibniz : ∀ (U : Cᵒᵖ) (r : W.naiveStructuralFull.obj.obj U)
    (m : (fullForms p K O Rplus A W Ω).val.obj U),
    oneFormDifferential U (r • m) = r • oneFormDifferential U m +
      exteriorUnit W.naiveStructuralFull (fullForms p K O Rplus A W Ω) 2 U
        (_root_.exteriorPower.ιMulti (W.naiveStructuralFull.obj.obj U) 2
          (fun i : Fin 2 => if i = 0 then connection U r else m))
  oneForm_fraction_source : ∀ (U : Cᵒᵖ) (t : A.deRhamPositive.obj.obj U)
    (ht : IsLocalGenerator A.deRhamPositive (completedRegular p Rplus) A.completedTheta U t)
    (j : ℤ) (m : (positiveForms p K O Rplus A W Ω).val.obj U),
    oneFormDifferential U
      (localGeneratorPower p K O Rplus A W U t ht (-j) • positiveFormUnit p K O Rplus A W Ω U m) =
      localGeneratorPower p K O Rplus A W U t ht (-j) • positiveTwoMap U (P.oneFormDifferential U m)
  integrable : ∀ U r, oneFormDifferential U (connection U r) = 0

end MathlibExt.CategoryTheory.StructuralPeriodConnectionSources
