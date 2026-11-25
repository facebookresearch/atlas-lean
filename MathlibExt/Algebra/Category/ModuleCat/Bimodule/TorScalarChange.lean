/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Bimodule.TensorFunctor
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.UniverseNaturality
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Square
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# Canonical Tor scalar change between native bimodule coefficient families

The actual native coefficient Tor functors are reused. Arbitrary endpoint
ring maps act through exact source restriction, the proved underived tensor
square, and exact output restriction. Source restriction is not assigned
projective preservation. The projective source resolution maps into the
actual exact restricted target-ring resolution before taking mapped homology.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MulOpposite
open ModuleCat.BalancedTensorRight
open scoped TensorProduct

universe rGlobal rGlobal' rGlobal'' sGlobal sGlobal' sGlobal'' vGlobal aGlobal aGlobal' aGlobal'' bGlobal bGlobal'
  bGlobal'' zGlobal tGlobal

namespace ModuleCat.Bimodule.Tensor

variable (R : Type rGlobal) (S : Type sGlobal) [Ring R] [Ring S]

private theorem restriction_preservesHomology
    {P : Type rGlobal} {Q : Type rGlobal'} [Ring P] [Ring Q] (f : P →+* Q) :
    (ModuleCat.restrictScalars.{vGlobal} f).PreservesHomology :=
  Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} f)

/-- The original-carrier tensor factory agrees with the existing native coefficient provider.
Its actual endpoint restrictions are the same native tensor inclusions. -/
def nativeTensorFunctorIso (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S) :
    functor R S B ≅ (coefficientTensorObj R S B).obj := by
  letI := coefficientLeftModule R S B
  letI := coefficientRightModule R S B
  letI := coefficientActionsCommute R S B
  refine NatIso.ofComponents (fun A => Iso.refl _) ?_
  intro A A' g
  apply hom_ext R S B A
  intro x y
  change (map R S B g).hom (pairing R S B A x y) =
    (ModuleCat.BalancedTensorRight.tensorMap R S B g).hom
      (TensorProduct.Balanced.mk ℤ R A B x y)
  rw [map_pairing, ModuleCat.BalancedTensorRight.tensorMap_mk]
  rfl

/-- The native coefficient provider comparison retains the original pure class. -/
theorem nativeTensorFunctorIso_hom_pairing
    (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S) (A : ModuleCat.{vGlobal} Rᵐᵒᵖ) (x : A) (y : B) :
    ((nativeTensorFunctorIso R S B).hom.app A).hom (pairing R S B A x y) =
      pairing R S B A x y := rfl

/-- The actual native provider comparison carries the original stored outer action. -/
theorem nativeTensorFunctorIso_hom_smul_pairing
    (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S)
    (A : ModuleCat.{vGlobal} Rᵐᵒᵖ) (t : Sᵐᵒᵖ) (x : A) (y : B) :
    ((nativeTensorFunctorIso R S B).hom.app A).hom
        ((obj R S B A).isModule.smul t (pairing R S B A x y)) =
      (((coefficientTensorObj R S B).obj).obj A).isModule.smul t
        (pairing R S B A x y) := by
  have h := ((nativeTensorFunctorIso R S B).hom.app A).hom.map_smul' t
    (pairing R S B A x y)
  exact h.trans (congrArg
    ((((coefficientTensorObj R S B).obj).obj A).isModule.smul t)
    (nativeTensorFunctorIso_hom_pairing R S B A x y))

/-- The inverse comparison returns the same original outer action and pure factors. -/
theorem nativeTensorFunctorIso_inv_smul_pairing
    (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S)
    (A : ModuleCat.{vGlobal} Rᵐᵒᵖ) (t : Sᵐᵒᵖ) (x : A) (y : B) :
    ((nativeTensorFunctorIso R S B).inv.app A).hom
        ((((coefficientTensorObj R S B).obj).obj A).isModule.smul t
          (pairing R S B A x y)) =
      (obj R S B A).isModule.smul t (pairing R S B A x y) := by
  have h := ((nativeTensorFunctorIso R S B).inv.app A).hom.map_smul' t
    (pairing R S B A x y)
  have hPure : ((nativeTensorFunctorIso R S B).inv.app A).hom
      (pairing R S B A x y) = pairing R S B A x y := rfl
  exact h.trans (congrArg ((obj R S B A).isModule.smul t) hPure)

section Rings

variable {R' : Type rGlobal'} {S' : Type sGlobal'} [Ring R'] [Ring S']
  (φ : R →+* R') (ψ : S →+* S')
  (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S)
  (B' : coefficientCategory.{rGlobal', sGlobal', vGlobal} R' S')
  (f : B ⟶ (RingChange.restrictFunctor φ ψ).obj B')

/-- The actual scalar-change tensor square on the existing native coefficient providers. -/
def tensorRingChangeTransformation :
    ModuleCat.restrictScalars φ.op ⋙ (coefficientTensorObj R S B).obj ⟶
      (coefficientTensorObj R' S' B').obj ⋙ ModuleCat.restrictScalars ψ.op :=
  Functor.whiskerLeft (ModuleCat.restrictScalars φ.op) (nativeTensorFunctorIso R S B).inv ≫
    ringChangeTransformation R S φ ψ B B' f ≫
    Functor.whiskerRight (nativeTensorFunctorIso R' S' B').hom (ModuleCat.restrictScalars ψ.op)

/-- Its values are the original ordered balanced classes and coefficient map. -/
theorem tensorRingChangeTransformation_pairing
    (A : ModuleCat.{vGlobal} R'ᵐᵒᵖ) (x : A) (y : B) :
    ((tensorRingChangeTransformation R S φ ψ B B' f).app A).hom
        (pairing R S B ((ModuleCat.restrictScalars φ.op).obj A) x y) =
      pairing R' S' B' A x (f.hom y) := rfl

/-- The actual projective R-source resolution maps into restriction of the genuine
R'-resolution. The restricted target is used only as an exact augmented complex. -/
def restrictedResolutionComparison
    {A : ModuleCat.{vGlobal} Rᵐᵒᵖ} {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ}
    (P : ProjectiveResolution A) (Q : ProjectiveResolution A')
    (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A') :
    {aGlobal : P.complex ⟶
        ((ModuleCat.restrictScalars φ.op).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          Q.complex //
      aGlobal ≫ Functor.mapChainAugmentation (ModuleCat.restrictScalars φ.op) Q.π =
        P.π ≫ (ChainComplex.single₀ (ModuleCat.{vGlobal} Rᵐᵒᵖ)).map g} := by
  let U := ModuleCat.restrictScalars.{vGlobal} φ.op
  letI : U.PreservesHomology := Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} φ.op)
  letI : QuasiIso (Functor.mapChainAugmentation U Q.π) :=
    Functor.mapChainAugmentation_quasiIso U Q.π
  exact P.comparisonToAugmentedExact
    ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)
    (Functor.mapChainAugmentation U Q.π) g

/-- The actual chain map on the original tensor complexes, before taking homology. -/
def tensorRingChangeResolutionMap
    {A : ModuleCat.{vGlobal} Rᵐᵒᵖ} {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ}
    (P : ProjectiveResolution A) (Q : ProjectiveResolution A')
    (aGlobal : P.complex ⟶
      ((ModuleCat.restrictScalars φ.op).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        Q.complex) :
    (((coefficientTensorObj R S B).obj).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        P.complex ⟶
      ((ModuleCat.restrictScalars ψ.op).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((((coefficientTensorObj R' S' B').obj).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj Q.complex) :=
  (((coefficientTensorObj R S B).obj).mapHomologicalComplex (ComplexShape.down ℕ)).map aGlobal ≫
    (Functor.mapSquareHomologicalComplex (ModuleCat.restrictScalars φ.op)
      (ModuleCat.restrictScalars ψ.op) (coefficientTensorObj R S B).obj
      (coefficientTensorObj R' S' B').obj
      (tensorRingChangeTransformation R S φ ψ B B' f)).app Q.complex

/-- Each actual comparison component gives the ordered original tensor value. -/
theorem tensorRingChangeResolutionMap_pairing
    {A : ModuleCat.{vGlobal} Rᵐᵒᵖ} {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ}
    (P : ProjectiveResolution A) (Q : ProjectiveResolution A')
    (aGlobal : P.complex ⟶
      ((ModuleCat.restrictScalars φ.op).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        Q.complex) (i : ℕ) (x : P.complex.X i) (y : B) :
    ((tensorRingChangeResolutionMap R S φ ψ B B' f P Q aGlobal).f i).hom
        (pairing R S B (P.complex.X i) x y) =
      pairing R' S' B' (Q.complex.X i) ((aGlobal.f i).hom x) (f.hom y) := by
  letI := coefficientLeftModule R S B
  letI := coefficientRightModule R S B
  letI := coefficientActionsCommute R S B
  change ((tensorRingChangeTransformation R S φ ψ B B' f).app (Q.complex.X i)).hom
      ((ModuleCat.BalancedTensorRight.tensorMap R S B (aGlobal.f i)).hom
        (TensorProduct.Balanced.mk ℤ R (P.complex.X i) B x y)) = _
  have hMap := ModuleCat.BalancedTensorRight.tensorMap_mk R S B (aGlobal.f i) x y
  have hScalar := tensorRingChangeTransformation_pairing R S φ ψ B B' f
    (Q.complex.X i) (show Q.complex.X i from (aGlobal.f i).hom x) y
  exact (congrArg ((tensorRingChangeTransformation R S φ ψ B B' f).app
    (Q.complex.X i)).hom hMap).trans hScalar

section Derived

variable [HasProjectiveResolutions (ModuleCat.{vGlobal} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{vGlobal} R'ᵐᵒᵖ)]

/-- The canonical Tor ring-change transformation reuses the actual native coefficient Tor
families. Both restrictions are exact; neither is required to preserve projectives. -/
def torRingChangeTransformation (n : ℕ) :
    ModuleCat.restrictScalars φ.op ⋙ (coefficientTorFunctor R S n).obj B ⟶
      (coefficientTorFunctor R' S' n).obj B' ⋙ ModuleCat.restrictScalars ψ.op := by
  let U := ModuleCat.restrictScalars.{vGlobal} φ.op
  let V := ModuleCat.restrictScalars.{vGlobal} ψ.op
  let F := (coefficientTensorObj R S B).obj
  let G := (coefficientTensorObj R' S' B').obj
  letI : U.PreservesHomology := Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} φ.op)
  letI : V.PreservesHomology := Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} ψ.op)
  change U ⋙ F.leftDerived n ⟶ G.leftDerived n ⋙ V
  exact Functor.leftDerivedSquareHom U V F G
    (tensorRingChangeTransformation R S φ ψ B B' f) n

/-- An original right-module morphism into restriction of the target input gives the
canonical Tor map; the two native source categories are kept distinct. -/
def torRingChangeMap (n : ℕ) {A : ModuleCat.{vGlobal} Rᵐᵒᵖ}
    {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ} (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A') :
    ((coefficientTorFunctor R S n).obj B).obj A ⟶
      (ModuleCat.restrictScalars ψ.op).obj
        (((coefficientTorFunctor R' S' n).obj B').obj A') :=
  ((coefficientTorFunctor R S n).obj B).map g ≫
    (torRingChangeTransformation R S φ ψ B B' f n).app A'

/-- The same canonical morphism, read as semilinear for the original two outer rings. -/
def torRingChangeSemilinearMap (n : ℕ) {A : ModuleCat.{vGlobal} Rᵐᵒᵖ}
    {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ} (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A') :
    (((coefficientTorFunctor R S n).obj B).obj A).carrier →ₛₗ[ψ.op]
      (((coefficientTorFunctor R' S' n).obj B').obj A').carrier :=
  (ModuleCat.semilinearMapAddEquiv ψ.op
    (((coefficientTorFunctor R S n).obj B).obj A)
    (((coefficientTorFunctor R' S' n).obj B').obj A')).symm
      (torRingChangeMap R S φ ψ B B' f n g)

/-- Semilinearity acts on the original Tor values, without an action on an S-linear Hom space. -/
theorem torRingChangeSemilinearMap_smul (n : ℕ) {A : ModuleCat.{vGlobal} Rᵐᵒᵖ}
    {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ} (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A')
    (sGlobal : Sᵐᵒᵖ) (x : ((coefficientTorFunctor R S n).obj B).obj A) :
    torRingChangeSemilinearMap R S φ ψ B B' f n g (sGlobal • x) =
      ψ.op sGlobal • torRingChangeSemilinearMap R S φ ψ B B' f n g x :=
  (torRingChangeSemilinearMap R S φ ψ B B' f n g).map_smulₛₗ sGlobal x

/-- Any actual projective source/target resolutions and an augmentation-preserving
R-linear comparison into the exact restricted target compute the SAME canonical Tor map. -/
theorem torRingChangeMap_resolution (n : ℕ)
    {A : ModuleCat.{vGlobal} Rᵐᵒᵖ} {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ}
    (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A')
    (P : ProjectiveResolution A) (Q : ProjectiveResolution A')
    (aGlobal : P.complex ⟶
      ((ModuleCat.restrictScalars φ.op).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        Q.complex)
    (ha : aGlobal ≫ Functor.mapChainAugmentation (ModuleCat.restrictScalars φ.op) Q.π =
      P.π ≫ (ChainComplex.single₀ (ModuleCat.{vGlobal} Rᵐᵒᵖ)).map g) :
    torRingChangeMap R S φ ψ B B' f n g =
      (P.isoLeftDerivedObj (coefficientTensorObj R S B).obj n).hom ≫
        HomologicalComplex.homologyMap
          (tensorRingChangeResolutionMap R S φ ψ B B' f P Q aGlobal) n ≫
        (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n
          (ModuleCat.restrictScalars ψ.op)).hom.app
            ((((coefficientTensorObj R' S' B').obj).mapHomologicalComplex
              (ComplexShape.down ℕ)).obj Q.complex) ≫
        (ModuleCat.restrictScalars ψ.op).map
          (Q.isoLeftDerivedObj (coefficientTensorObj R' S' B').obj n).inv := by
  letI : (ModuleCat.restrictScalars.{vGlobal} φ.op).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} φ.op)
  letI : (ModuleCat.restrictScalars.{vGlobal} ψ.op).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} ψ.op)
  exact Functor.leftDerivedSquareHom_eq_with_source_lift
    (ModuleCat.restrictScalars φ.op) (ModuleCat.restrictScalars ψ.op)
    (coefficientTensorObj R S B).obj (coefficientTensorObj R' S' B').obj
    (tensorRingChangeTransformation R S φ ψ B B' f) n g P Q aGlobal ha

/-- The actual internally constructed comparison computes the canonical map without any
comparison data being supplied by aGlobal caller. -/
theorem torRingChangeMap_canonical_resolution (n : ℕ)
    {A : ModuleCat.{vGlobal} Rᵐᵒᵖ} {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ}
    (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A')
    (P : ProjectiveResolution A) (Q : ProjectiveResolution A') :
    torRingChangeMap R S φ ψ B B' f n g =
      (P.isoLeftDerivedObj (coefficientTensorObj R S B).obj n).hom ≫
        HomologicalComplex.homologyMap
          (tensorRingChangeResolutionMap R S φ ψ B B' f P Q
            (restrictedResolutionComparison R φ P Q g).val) n ≫
        (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n
          (ModuleCat.restrictScalars ψ.op)).hom.app
            ((((coefficientTensorObj R' S' B').obj).mapHomologicalComplex
              (ComplexShape.down ℕ)).obj Q.complex) ≫
        (ModuleCat.restrictScalars ψ.op).map
          (Q.isoLeftDerivedObj (coefficientTensorObj R' S' B').obj n).inv :=
  torRingChangeMap_resolution R S φ ψ B B' f n g P Q
    (restrictedResolutionComparison R φ P Q g).val
    (restrictedResolutionComparison R φ P Q g).property

/-- Source input maps compose by the actual canonical native Tor functor. -/
theorem torRingChangeMap_naturality_source (n : ℕ)
    {A₀ A : ModuleCat.{vGlobal} Rᵐᵒᵖ} {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ}
    (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A') (h : A₀ ⟶ A) :
    ((coefficientTorFunctor R S n).obj B).map h ≫ torRingChangeMap R S φ ψ B B' f n g =
      torRingChangeMap R S φ ψ B B' f n (h ≫ g) := by
  unfold torRingChangeMap
  rw [Functor.map_comp, Category.assoc]

/-- Target input maps give the corresponding actual ring-change naturality square. -/
theorem torRingChangeMap_naturality_target (n : ℕ)
    {A : ModuleCat.{vGlobal} Rᵐᵒᵖ} {A' A'' : ModuleCat.{vGlobal} R'ᵐᵒᵖ}
    (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A') (h : A' ⟶ A'') :
    torRingChangeMap R S φ ψ B B' f n g ≫
        (ModuleCat.restrictScalars ψ.op).map
          (((coefficientTorFunctor R' S' n).obj B').map h) =
      torRingChangeMap R S φ ψ B B' f n
        (g ≫ (ModuleCat.restrictScalars φ.op).map h) := by
  unfold torRingChangeMap
  rw [Functor.map_comp, Category.assoc]
  exact congrArg (fun aGlobal => ((coefficientTorFunctor R S n).obj B).map g ≫ aGlobal)
    ((torRingChangeTransformation R S φ ψ B B' f n).naturality h).symm

end Derived

/-- Original source coefficient maps commute with the actual underived ring-change square. -/
theorem tensorRingChangeTransformation_coefficient_left
    {B₀ : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S} (g : B₀ ⟶ B) :
    Functor.whiskerLeft (ModuleCat.restrictScalars φ.op) (coefficientTensorTransformation R S g) ≫
        tensorRingChangeTransformation R S φ ψ B B' f =
      tensorRingChangeTransformation R S φ ψ B₀ B' (g ≫ f) := by
  apply NatTrans.ext
  funext A
  apply hom_ext R S B₀ ((ModuleCat.restrictScalars φ.op).obj A)
  intro x y
  rfl

/-- Original target coefficient maps retain their native restricted coefficient square. -/
theorem tensorRingChangeTransformation_coefficient_right
    {B'' : coefficientCategory.{rGlobal', sGlobal', vGlobal} R' S'} (g : B' ⟶ B'') :
    tensorRingChangeTransformation R S φ ψ B B' f ≫
        Functor.whiskerRight (coefficientTensorTransformation R' S' g)
          (ModuleCat.restrictScalars ψ.op) =
      tensorRingChangeTransformation R S φ ψ B B''
        (f ≫ (RingChange.restrictFunctor φ ψ).map g) := by
  apply NatTrans.ext
  funext A
  apply hom_ext R S B ((ModuleCat.restrictScalars φ.op).obj A)
  intro x y
  rfl

section DerivedCoefficients

variable [HasProjectiveResolutions (ModuleCat.{vGlobal} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{vGlobal} R'ᵐᵒᵖ)]

/-- Native coefficient functoriality and directional exact precomposition earn the source
coefficient square in every Tor degree. -/
theorem torRingChangeTransformation_coefficient_left (n : ℕ)
    {B₀ : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S} (g : B₀ ⟶ B) :
    Functor.whiskerLeft (ModuleCat.restrictScalars φ.op) ((coefficientTorFunctor R S n).map g) ≫
        torRingChangeTransformation R S φ ψ B B' f n =
      torRingChangeTransformation R S φ ψ B₀ B' (g ≫ f) n := by
  letI : (ModuleCat.restrictScalars.{vGlobal} φ.op).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} φ.op)
  letI : (ModuleCat.restrictScalars.{vGlobal} ψ.op).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} ψ.op)
  change Functor.whiskerLeft (ModuleCat.restrictScalars φ.op)
      (NatTrans.leftDerived (coefficientTensorTransformation R S g) n) ≫
        Functor.leftDerivedSquareHom _ _ _ _
          (tensorRingChangeTransformation R S φ ψ B B' f) n = _
  rw [Functor.leftDerivedSquareHom_naturality_source_functor,
    tensorRingChangeTransformation_coefficient_left]
  rfl

/-- Exact output postcomposition earns the actual target coefficient square in every degree. -/
theorem torRingChangeTransformation_coefficient_right (n : ℕ)
    {B'' : coefficientCategory.{rGlobal', sGlobal', vGlobal} R' S'} (g : B' ⟶ B'') :
    torRingChangeTransformation R S φ ψ B B' f n ≫
        Functor.whiskerRight ((coefficientTorFunctor R' S' n).map g)
          (ModuleCat.restrictScalars ψ.op) =
      torRingChangeTransformation R S φ ψ B B''
        (f ≫ (RingChange.restrictFunctor φ ψ).map g) n := by
  letI : (ModuleCat.restrictScalars.{vGlobal} φ.op).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} φ.op)
  letI : (ModuleCat.restrictScalars.{vGlobal} ψ.op).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} ψ.op)
  change Functor.leftDerivedSquareHom _ _ _ _
      (tensorRingChangeTransformation R S φ ψ B B' f) n ≫
      Functor.whiskerRight (NatTrans.leftDerived (coefficientTensorTransformation R' S' g) n)
        (ModuleCat.restrictScalars ψ.op) = _
  rw [Functor.leftDerivedSquareHom_naturality_target_functor,
    tensorRingChangeTransformation_coefficient_right]
  rfl

end DerivedCoefficients

end Rings

/-- The existing native tensor adjunction identifies the native coefficient Tor family in zero. -/
def coefficientTorZeroIso [HasProjectiveResolutions (ModuleCat.{vGlobal} Rᵐᵒᵖ)]
    (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S) :
    (coefficientTorFunctor R S 0).obj B ≅ (coefficientTensorObj R S B).obj := by
  letI := coefficientLeftModule R S B
  letI := coefficientRightModule R S B
  letI := coefficientActionsCommute R S B
  exact ModuleCat.BalancedTensorRight.torZeroIso R S B

/-- Its forward map is the original native augmentation, rather than aGlobal supplied comparison. -/
theorem coefficientTorZeroIso_hom [HasProjectiveResolutions (ModuleCat.{vGlobal} Rᵐᵒᵖ)]
    (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S) :
    (coefficientTorZeroIso R S B).hom = (coefficientTensorObj R S B).obj.fromLeftDerivedZero :=
  rfl

section Zero

variable {R' : Type rGlobal'} {S' : Type sGlobal'} [Ring R'] [Ring S']
  (φ : R →+* R') (ψ : S →+* S')
  (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S)
  (B' : coefficientCategory.{rGlobal', sGlobal', vGlobal} R' S')
  (f : B ⟶ (RingChange.restrictFunctor φ ψ).obj B')
  [HasProjectiveResolutions (ModuleCat.{vGlobal} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{vGlobal} R'ᵐᵒᵖ)]

/-- Canonical Tor scalar change has the original ordered tensor map under both zero isos. -/
theorem torRingChangeTransformation_zero :
    torRingChangeTransformation R S φ ψ B B' f 0 ≫
        Functor.whiskerRight (coefficientTorZeroIso R' S' B').hom (ModuleCat.restrictScalars ψ.op) =
      Functor.whiskerLeft (ModuleCat.restrictScalars φ.op) (coefficientTorZeroIso R S B).hom ≫
        tensorRingChangeTransformation R S φ ψ B B' f := by
  letI : (ModuleCat.restrictScalars.{vGlobal} φ.op).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} φ.op)
  letI : (ModuleCat.restrictScalars.{vGlobal} ψ.op).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} ψ.op)
  rw [coefficientTorZeroIso_hom, coefficientTorZeroIso_hom]
  exact Functor.leftDerivedSquareHom_zero_augmentation _ _ _ _
    (tensorRingChangeTransformation R S φ ψ B B' f)

end Zero

section Identity

variable [HasProjectiveResolutions (ModuleCat.{vGlobal} Rᵐᵒᵖ)]

/-- Identity scalar change is the actual native output-restriction identity comparison
on every canonical Tor degree. The coefficient identity uses the earned enveloping identity. -/
theorem torRingChangeMap_id
    (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S) (A : ModuleCat.{vGlobal} Rᵐᵒᵖ) (n : ℕ) :
    torRingChangeMap R S (RingHom.id R) (RingHom.id S) B B
        ((RingChange.restrictId (R := R) (S := S)).inv.app B) n
        ((ModuleCat.restrictScalarsId' (RingHom.id R).op (by ext rGlobal; rfl)).inv.app A) =
      (ModuleCat.restrictScalarsId' (RingHom.id S).op (by ext sGlobal; rfl)).inv.app
        (((coefficientTorFunctor R S n).obj B).obj A) := by
  let U := ModuleCat.restrictScalars.{vGlobal} (RingHom.id R).op
  let V := ModuleCat.restrictScalars.{vGlobal} (RingHom.id S).op
  let rId := ModuleCat.restrictScalarsId' (RingHom.id R).op (by ext rGlobal; rfl)
  let sId := ModuleCat.restrictScalarsId' (RingHom.id S).op (by ext sGlobal; rfl)
  let F := (coefficientTensorObj R S B).obj
  let P := projectiveResolution A
  let aGlobal : P.complex ⟶ (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex :=
    (Functor.mapHomologicalComplexIdIso (ModuleCat.{vGlobal} Rᵐᵒᵖ) (ComplexShape.down ℕ)).inv.app
        P.complex ≫ (NatTrans.mapHomologicalComplex rId.inv (ComplexShape.down ℕ)).app P.complex
  have ha : aGlobal ≫ Functor.mapChainAugmentation U P.π =
      P.π ≫ (ChainComplex.single₀ (ModuleCat.{vGlobal} Rᵐᵒᵖ)).map (rId.inv.app A) := by
    apply HomologicalComplex.hom_ext
    intro i
    cases i with
    | zero =>
      have ha₀ : aGlobal.f 0 = rId.inv.app (P.complex.X 0) := by
        change (𝟙 _) ≫ rId.inv.app (P.complex.X 0) = _
        rw [Category.id_comp]
      change aGlobal.f 0 ≫ (Functor.mapChainAugmentation U P.π).f 0 =
        P.π.f 0 ≫ ((ChainComplex.single₀ (ModuleCat.{vGlobal} Rᵐᵒᵖ)).map (rId.inv.app A)).f 0
      rw [ha₀, Functor.mapChainAugmentation_f_zero, ChainComplex.single₀_map_f_zero]
      exact (rId.inv.naturality (P.π.f 0)).symm
    | succ i =>
      have hρ : (Functor.mapChainAugmentation U P.π).f (i + 1) = 0 :=
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 (U.obj A)
          (i + 1) (by omega)).eq_of_tgt _ _
      simp only [HomologicalComplex.comp_f, hρ, ProjectiveResolution.π_f_succ,
        Limits.comp_zero, Limits.zero_comp]
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let d : K ⟶ (V.mapHomologicalComplex (ComplexShape.down ℕ)).obj K :=
    (Functor.mapHomologicalComplexIdIso (ModuleCat.{vGlobal} Sᵐᵒᵖ) (ComplexShape.down ℕ)).inv.app K ≫
      (NatTrans.mapHomologicalComplex sId.inv (ComplexShape.down ℕ)).app K
  have hd : tensorRingChangeResolutionMap R S (RingHom.id R) (RingHom.id S) B B
      ((RingChange.restrictId (R := R) (S := S)).inv.app B) P P aGlobal = d := by
    apply HomologicalComplex.hom_ext
    intro i
    apply hom_ext R S B (P.complex.X i)
    intro x y
    rfl
  letI : V.PreservesHomology := Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} (RingHom.id S).op)
  letI : (𝟭 (ModuleCat.{vGlobal} Sᵐᵒᵖ)).PreservesHomology :=
    Functor.preservesHomologyOfExact (𝟭 (ModuleCat.{vGlobal} Sᵐᵒᵖ))
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{vGlobal} Sᵐᵒᵖ) (ComplexShape.down ℕ) n
  have hId : (Functor.mapHomologicalComplexIdIso (ModuleCat.{vGlobal} Sᵐᵒᵖ)
      (ComplexShape.down ℕ)).inv.app K = 𝟙 _ := by
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  have hH : H.map d ≫
      (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V).hom.app K =
        sId.inv.app (H.obj K) := by
    have h := HomologicalComplex.mapHomologyFunctorIso_naturality_transformation K n
      (𝟭 (ModuleCat.{vGlobal} Sᵐᵒᵖ)) V sId.inv
    have hD : H.map d = H.map ((NatTrans.mapHomologicalComplex sId.inv
        (ComplexShape.down ℕ)).app K) := by
      rw [show d = (𝟙 K) ≫ (NatTrans.mapHomologicalComplex sId.inv
        (ComplexShape.down ℕ)).app K from congrArg
        (fun f => f ≫ (NatTrans.mapHomologicalComplex sId.inv (ComplexShape.down ℕ)).app K) hId]
      rw [Category.id_comp]
    rw [hD]
    simpa only [HomologicalComplex.mapHomologyFunctorIso_id_hom, Category.id_comp] using h
  rw [torRingChangeMap_resolution R S (RingHom.id R) (RingHom.id S) B B
    ((RingChange.restrictId (R := R) (S := S)).inv.app B) n (rId.inv.app A) P P aGlobal ha, hd]
  change (P.isoLeftDerivedObj F n).hom ≫ H.map d ≫
      (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V).hom.app K ≫
      V.map (P.isoLeftDerivedObj F n).inv = _
  rw [← Category.assoc (H.map d), hH, ← sId.inv.naturality (P.isoLeftDerivedObj F n).inv]
  change (P.isoLeftDerivedObj F n).hom ≫ (P.isoLeftDerivedObj F n).inv ≫
    sId.inv.app ((F.leftDerived n).obj A) = _
  rw [Iso.hom_inv_id_assoc]
  rfl

end Identity

section IndependentCarriers

variable {R' : Type rGlobal'} {S' : Type sGlobal'} [Ring R'] [Ring S']

/-- The original coefficient identity is semilinear for the earned native enveloping identity. -/
def coefficientSemilinearIdentity (B : coefficientCategory.{rGlobal, sGlobal, bGlobal} R S) :
    B →ₛₗ[RingChange.envelopingRingHom (RingHom.id R) (RingHom.id S)] B :=
  (ModuleCat.semilinearMapAddEquiv
    (RingChange.envelopingRingHom (RingHom.id R) (RingHom.id S)) B B).symm
      ((RingChange.restrictId (R := R) (S := S)).inv.app B)

/-- The original input identity uses the actual native restriction identity comparison. -/
def inputSemilinearIdentity (A : ModuleCat.{aGlobal} Rᵐᵒᵖ) : A →ₛₗ[(RingHom.id R).op] A :=
  (ModuleCat.semilinearMapAddEquiv (RingHom.id R).op A A).symm
    ((ModuleCat.restrictScalarsId' (RingHom.id R).op (by ext rGlobal; rfl)).inv.app A)

/-- Lift the original native semilinear coefficient map into the common sufficient
working universe. The outer ring worlds do not enter its carrier bound. -/
def liftCoefficientRingChangeAt.{z, r, r', s, s', a, a', b, b'} (R : Type r) [Ring R] (S : Type s) [Ring S]
  {R' : Type r'} [Ring R'] {S' : Type s'} [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B') :
    (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B ⟶
      (RingChange.restrictFunctor φ ψ).obj
        ((ModuleCat.uliftFunctor.{max r r' a a' b b' z, b'}
          (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B') := by
  let X := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b}
    (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
  let Y := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b'}
    (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B'
  let eX : ULift.{max r r' a a' b b' z} B ≃ₗ[R ⊗[ℤ] Sᵐᵒᵖ] B := ULift.moduleEquiv
  let eY : ULift.{max r r' a a' b b' z} B' ≃ₗ[R' ⊗[ℤ] S'ᵐᵒᵖ] B' := ULift.moduleEquiv
  let g : X.carrier →ₛₗ[RingChange.envelopingRingHom φ ψ] Y.carrier :=
    eY.symm.toLinearMap.comp (f.comp eX.toLinearMap)
  exact ModuleCat.semilinearMapAddEquiv (RingChange.envelopingRingHom φ ψ) X Y g

/-- The actual lifted coefficient has the original up-f-down value. -/
theorem liftCoefficientRingChangeAt_up.{z, r, r', s, s', a, a', b, b'} (R : Type r) [Ring R] (S : Type s) [Ring S]
  {R' : Type r'} [Ring R'] {S' : Type s'} [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B') (x : B) :
    (liftCoefficientRingChangeAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f).hom
        (ULift.up x) = ULift.up (f x) := rfl

/-- Lift the original input semilinear map, keeping the two raw input categories distinct. -/
def liftInputRingChangeAt.{z, r, r', a, a', b, b'} (R : Type r) [Ring R] {R' : Type r'} [Ring R'] (φ : R →+* R')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A') :
    (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a} Rᵐᵒᵖ).obj A ⟶
      (ModuleCat.restrictScalars φ.op).obj
        ((ModuleCat.uliftFunctor.{max r r' a a' b b' z, a'} R'ᵐᵒᵖ).obj A') := by
  let X := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a} Rᵐᵒᵖ).obj A
  let Y := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a'} R'ᵐᵒᵖ).obj A'
  let eX : ULift.{max r r' a a' b b' z} A ≃ₗ[Rᵐᵒᵖ] A := ULift.moduleEquiv
  let eY : ULift.{max r r' a a' b b' z} A' ≃ₗ[R'ᵐᵒᵖ] A' := ULift.moduleEquiv
  let f : X.carrier →ₛₗ[φ.op] Y.carrier :=
    eY.symm.toLinearMap.comp (g.comp eX.toLinearMap)
  exact ModuleCat.semilinearMapAddEquiv φ.op X Y f

/-- The actual input lift has its original up-g-down value. -/
theorem liftInputRingChangeAt_up.{z, r, r', a, a', b, b'} (R : Type r) [Ring R] {R' : Type r'} [Ring R'] (φ : R →+* R')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A') (x : A) :
    (liftInputRingChangeAt.{z, r, r', a, a', b, b'} R φ A A' g).hom (ULift.up x) =
      ULift.up (g x) := rfl

/-- Canonical Tor scalar change on the original inputs and native coefficients.
Gamma = max(rGlobal,rGlobal',aGlobal,aGlobal',bGlobal,bGlobal',zGlobal) supplies both actual projective-resolution
  categories;
neither S nor S' is required to be small in Gamma. -/
def torRingChangeMapAt.{z, r, r', s, s', a, a', b, b'} (R : Type r) [Ring R] (S : Type s) [Ring S] {R' : Type r'}
  [Ring R'] {S' : Type s'} [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A') (n : ℕ) :
    (((torCoefficientFunctorAt.{max r' a' b' z, r, s, a, b} R S n).obj B).obj A) ⟶
      (ModuleCat.restrictScalars ψ.op).obj
        (((torCoefficientFunctorAt.{max r a b z, r', s', a', b'} R' S' n).obj B').obj A') := by
  letI : HasProjectiveResolutions (ModuleCat.{max r r' a a' b b' z} Rᵐᵒᵖ) := inferInstance
  letI : HasProjectiveResolutions (ModuleCat.{max r r' a a' b b' z} R'ᵐᵒᵖ) := inferInstance
  let C := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b}
    (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
  let D := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b'}
    (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B'
  exact torRingChangeMap R S φ ψ C D
    (liftCoefficientRingChangeAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f) n
    (liftInputRingChangeAt.{z, r, r', a, a', b, b'} R φ A A' g)

/-- The same original-carrier canonical map has the actual outer-ring semilinearity. -/
def torRingChangeSemilinearMapAt.{z, r, r', s, s', a, a', b, b'} (R : Type r) [Ring R] (S : Type s) [Ring S]
  {R' : Type r'} [Ring R'] {S' : Type s'} [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A') (n : ℕ) :
    ((((torCoefficientFunctorAt.{max r' a' b' z, r, s, a, b} R S n).obj B).obj A)).carrier
      →ₛₗ[ψ.op]
        ((((torCoefficientFunctorAt.{max r a b z, r', s', a', b'} R' S' n).obj B').obj A')).carrier :=
  (ModuleCat.semilinearMapAddEquiv ψ.op
    (((torCoefficientFunctorAt.{max r' a' b' z, r, s, a, b} R S n).obj B).obj A)
    (((torCoefficientFunctorAt.{max r a b z, r', s', a', b'} R' S' n).obj B').obj A')).symm
      (torRingChangeMapAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f A A' g n)

/-- Both actual outer scalar actions are retained on the original native Tor values. -/
theorem torRingChangeSemilinearMapAt_smul.{z, r, r', s, s', a, a', b, b'} (R : Type r) [Ring R] (S : Type s)
  [Ring S] {R' : Type r'} [Ring R'] {S' : Type s'} [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A') (n : ℕ)
    (s : Sᵐᵒᵖ)
    (x : ((torCoefficientFunctorAt.{max r' a' b' z, r, s, a, b} R S n).obj B).obj A) :
    torRingChangeSemilinearMapAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f A A' g n
        (s • x) = ψ.op s •
      torRingChangeSemilinearMapAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f A A' g n x :=
  (torRingChangeSemilinearMapAt.{z, r, r', s, s', a, a', b, b'}
    R S φ ψ B B' f A A' g n).map_smulₛₗ s x

/-- The actual lifted tensor scalar-change map, with the same working universe and providers. -/
def tensorRingChangeMapAt.{z, r, r', s, s', a, a', b, b'} (R : Type r) [Ring R] (S : Type s) [Ring S] {R' : Type r'}
  [Ring R'] {S' : Type s'} [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A') :
    (((tensorCoefficientFunctorAt.{max r' a' b' z, r, s, a, b} R S).obj B).obj A) ⟶
      (ModuleCat.restrictScalars ψ.op).obj
        (((tensorCoefficientFunctorAt.{max r a b z, r', s', a', b'} R' S').obj B').obj A') := by
  let Y := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a'} R'ᵐᵒᵖ).obj A'
  let C := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b}
    (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
  let D := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b'}
    (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B'
  let f₀ := liftCoefficientRingChangeAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f
  let g₀ := liftInputRingChangeAt.{z, r, r', a, a', b, b'} R φ A A' g
  exact (coefficientTensorObj R S C).obj.map g₀ ≫
    (tensorRingChangeTransformation R S φ ψ C D f₀).app Y

/-- The common working lift retains both original factor values on pure tensor classes. -/
theorem tensorRingChangeMapAt_pairing.{z, r, r', s, s', a, a', b, b'} (R : Type r) [Ring R] (S : Type s) [Ring S]
  {R' : Type r'} [Ring R'] {S' : Type s'} [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A')
    (x : A) (y : B) :
    let X := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a} Rᵐᵒᵖ).obj A
    let Y := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a'} R'ᵐᵒᵖ).obj A'
    let C := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b}
      (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
    let D := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b'}
      (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B'
    (tensorRingChangeMapAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f A A' g).hom
        (pairing R S C X (ULift.up x) (ULift.up y)) =
      pairing R' S' D Y (ULift.up (g x)) (ULift.up (f y)) := rfl

end IndependentCarriers

/-- The existing native coefficient zero iso is precomposed only after derivation in Gamma. -/
def coefficientTorZeroIsoAt.{z, r, s, a, b} (R : Type r) [Ring R] (S : Type s) [Ring S]
    (B : coefficientCategory.{r, s, b} R S) :
    (torCoefficientFunctorAt.{z, r, s, a, b} R S 0).obj B ≅
      (tensorCoefficientFunctorAt.{z, r, s, a, b} R S).obj B := by
  letI : HasProjectiveResolutions (ModuleCat.{max r a b z} Rᵐᵒᵖ) := inferInstance
  exact Functor.isoWhiskerLeft (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (coefficientTorZeroIso R S
      ((ModuleCat.uliftFunctor.{max r a b z, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B))

section IndependentZero

variable {R' : Type rGlobal'} {S' : Type sGlobal'} [Ring R'] [Ring S']

/-- The actual canonical original-carrier Tor map has the original ordered tensor map
under the two native degree-zero identifications. -/
theorem torRingChangeMapAt_zero.{z, r, r', s, s', a, a', b, b'} (R : Type r) [Ring R] (S : Type s) [Ring S]
  {R' : Type r'} [Ring R'] {S' : Type s'} [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A') :
    torRingChangeMapAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f A A' g 0 ≫
        (ModuleCat.restrictScalars ψ.op).map
          ((coefficientTorZeroIsoAt.{max r a b z, r', s', a', b'} R' S' B').hom.app A') =
      (coefficientTorZeroIsoAt.{max r' a' b' z, r, s, a, b} R S B).hom.app A ≫
        tensorRingChangeMapAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f A A' g := by
  letI : HasProjectiveResolutions (ModuleCat.{max r r' a a' b b' z} Rᵐᵒᵖ) := inferInstance
  letI : HasProjectiveResolutions (ModuleCat.{max r r' a a' b b' z} R'ᵐᵒᵖ) := inferInstance
  let X := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a} Rᵐᵒᵖ).obj A
  let Y := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a'} R'ᵐᵒᵖ).obj A'
  let C := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b}
    (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
  let D := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b'}
    (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B'
  let f₀ := liftCoefficientRingChangeAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f
  let g₀ := liftInputRingChangeAt.{z, r, r', a, a', b, b'} R φ A A' g
  have hT := congrArg (fun α => α.app Y)
    (torRingChangeTransformation_zero R S φ ψ C D f₀)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hT
  have hZ := (coefficientTorZeroIso R S C).hom.naturality g₀
  change ((((coefficientTorFunctor R S 0).obj C).map g₀) ≫
      (torRingChangeTransformation R S φ ψ C D f₀ 0).app Y) ≫
      (ModuleCat.restrictScalars ψ.op).map ((coefficientTorZeroIso R' S' D).hom.app Y) =
    (coefficientTorZeroIso R S C).hom.app X ≫
      ((coefficientTensorObj R S C).obj.map g₀ ≫
        (tensorRingChangeTransformation R S φ ψ C D f₀).app Y)
  rw [Category.assoc, hT, ← Category.assoc, hZ, Category.assoc]

end IndependentZero

/-- Identity ring change on all original carrier worlds is the native output-restriction
identity, in exactly the existing sufficient working universe. -/
theorem torRingChangeMapAt_id.{z, r, s, a, b} (R : Type r) [Ring R] (S : Type s) [Ring S]
    (B : coefficientCategory.{r, s, b} R S) (A : ModuleCat.{a} Rᵐᵒᵖ) (n : ℕ) :
    torRingChangeMapAt.{z, r, r, s, s, a, a, b, b} R S (RingHom.id R) (RingHom.id S) B B
        (coefficientSemilinearIdentity R S B) A A (inputSemilinearIdentity R A) n =
      (ModuleCat.restrictScalarsId' (RingHom.id S).op (by ext s; rfl)).inv.app
        (((torCoefficientFunctorAt.{z, r, s, a, b} R S n).obj B).obj A) := by
  letI : HasProjectiveResolutions (ModuleCat.{max r a b z} Rᵐᵒᵖ) := inferInstance
  let X := (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj A
  let C := (ModuleCat.uliftFunctor.{max r a b z, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
  let f₀ := liftCoefficientRingChangeAt.{z, r, r, s, s, a, a, b, b}
    R S (RingHom.id R) (RingHom.id S) B B (coefficientSemilinearIdentity R S B)
  let g₀ := liftInputRingChangeAt.{z, r, r, a, a, b, b}
    R (RingHom.id R) A A (inputSemilinearIdentity R A)
  have hf : f₀ = (RingChange.restrictId (R := R) (S := S)).inv.app C := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    cases x
    rfl
  have hg : g₀ =
      (ModuleCat.restrictScalarsId' (RingHom.id R).op (by ext r; rfl)).inv.app X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    cases x
    rfl
  change torRingChangeMap R S (RingHom.id R) (RingHom.id S) C C f₀ n g₀ = _
  rw [hf, hg]
  exact torRingChangeMap_id R S C X n

end ModuleCat.Bimodule.Tensor
