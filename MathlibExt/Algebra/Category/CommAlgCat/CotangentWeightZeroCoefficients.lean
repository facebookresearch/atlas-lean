/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentWeightZero
public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Whiskering

/-!
# Zero-weight cotangent coefficients

For an augmented simplicial algebra `P` over `A` and an `A`-module `M`,
the degreewise family `M ⊗[A] (A ⊗[P_n] P_n)` is naturally isomorphic to
constant `M`. The isomorphism sends `m ⊗ (a ⊗ p)` to
`(augmentation(p) * a) • m` and commutes with simplicial operators,
augmented-algebra maps and coefficient maps.

Normalization transports this isomorphism to the constant coefficient
complex, identifying its degree-zero homology and positive-degree vanishing.
Independent carrier universes are retained through the canonical universe lift.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial TensorProduct ChangeOfRings

universe u v t

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- Explicit lift of the original coefficient into the actual joint tensor carrier world. -/
abbrev cotangentWeightZeroCoefficientLift :
    ModuleCat.{t} A ⥤ ModuleCat.{max u v t} A :=
  ModuleCat.uliftFunctor.{max u v, t} A

/-- The native regular tensor unitor, with only the explicit coefficient carrier lift. -/
def cotangentWeightZeroCoefficientRegularIso (M : ModuleCat.{t} A) :
    ((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).obj
        (ModuleCat.of A A) ≅
      (cotangentWeightZeroCoefficientLift.{u, v, t} k A).obj M :=
  ((TensorProduct.rid A M).trans (ULift.moduleEquiv (R := A) (M := M)).symm).toModuleIso

/-- The actual coefficient tensor at an original algebra level is canonically the coefficient. -/
def cotangentWeightZeroCoefficientLevelIso (P : Over A) (M : ModuleCat.{t} A) :
    ((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).obj
        (cotangentWeightZeroLevel k A P) ≅
      (cotangentWeightZeroCoefficientLift.{u, v, t} k A).obj M :=
  ((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapIso
      (cotangentWeightZeroLevelIso k A P) ≪≫
    cotangentWeightZeroCoefficientRegularIso.{u, v, t} k A M

@[simp]
theorem cotangentWeightZeroCoefficientLevelIso_tmul
    (P : Over A) (M : ModuleCat.{t} A) (m : M) (x : cotangentWeightZeroLevel k A P) :
    (cotangentWeightZeroCoefficientLevelIso.{u, v, t} k A P M).hom.hom (m ⊗ₜ[A] x) =
      ULift.up ((cotangentWeightZeroLevelIso k A P).hom.hom x • m) := rfl

/-- The original nested tensor has the exact augmentation/action formula. -/
@[simp]
theorem cotangentWeightZeroCoefficientLevelIso_tmul_tmul
    (P : Over A) (M : ModuleCat.{t} A) (m : M) (a : A) (p : P.left) :
    (cotangentWeightZeroCoefficientLevelIso.{u, v, t} k A P M).hom.hom
      (m ⊗ₜ[A] (a ⊗ₜ[P.left,P.hom.hom.toRingHom] p)) =
        ULift.up ((P.hom.hom p * a) • m) := by
  let x : cotangentWeightZeroLevel k A P := a ⊗ₜ[P.left,P.hom.hom.toRingHom] p
  have h := cotangentWeightZeroCoefficientLevelIso_tmul.{u, v, t} k A P M m x
  have hx := cotangentWeightZeroLevelIso_tmul.{u, v} k A P a p
  exact h.trans (congrArg (fun a : A => ULift.up (a • m)) hx)

/-- The same actual isomorphism returns the original, independently sized coefficient carrier. -/
def cotangentWeightZeroCoefficientLevelLinearEquiv (P : Over A) (M : ModuleCat.{t} A) :
    (M ⊗[A] cotangentWeightZeroLevel k A P) ≃ₗ[A] M :=
  (cotangentWeightZeroCoefficientLevelIso.{u, v, t} k A P M).toLinearEquiv.trans ULift.moduleEquiv

@[simp]
theorem cotangentWeightZeroCoefficientLevelLinearEquiv_tmul_tmul
    (P : Over A) (M : ModuleCat.{t} A) (m : M) (a : A) (p : P.left) :
    cotangentWeightZeroCoefficientLevelLinearEquiv k A P M
      (m ⊗ₜ[A] (a ⊗ₜ[P.left,P.hom.hom.toRingHom] p)) = (P.hom.hom p * a) • m := by
  change ((cotangentWeightZeroCoefficientLevelIso.{u, v, t} k A P M).hom.hom
    (m ⊗ₜ[A] (a ⊗ₜ[P.left,P.hom.hom.toRingHom] p))).down = _
  rw [cotangentWeightZeroCoefficientLevelIso_tmul_tmul]

/-- The original zero-weight operator retains its actual regular unitor equation. -/
@[reassoc]
theorem cotangentWeightZeroTransport_comp_levelIso {P Q : Over A} (f : P ⟶ Q) :
    cotangentWeightZeroTransport k A f ≫ (cotangentWeightZeroLevelIso k A Q).hom =
      (cotangentWeightZeroLevelIso k A P).hom := by
  unfold cotangentWeightZeroTransport
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual coefficient tensor family, functorial in both original arguments. -/
def cotangentWeightZeroTensorFamily :
    ModuleCat.{t} A ⥤
      Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) ⥤
        SimplicialObject (ModuleCat.{max u v t} A) :=
  ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A ⋙
    SimplicialObject.whiskering (ModuleCat.{max u v} A) (ModuleCat.{max u v t} A) ⋙
      (Functor.whiskeringLeft
        (Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
        (SimplicialObject (ModuleCat.{max u v} A))
        (SimplicialObject (ModuleCat.{max u v t} A))).obj
          (cotangentWeightZeroResolutionFunctor k A)

/-- Constant original coefficients, explicitly realized in the joint carrier category. -/
def cotangentWeightZeroConstantCoefficientFamily :
    ModuleCat.{t} A ⥤
      Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) ⥤
        SimplicialObject (ModuleCat.{max u v t} A) :=
  cotangentWeightZeroCoefficientLift.{u, v, t} k A ⋙
    SimplicialObject.const (ModuleCat.{max u v t} A) ⋙
      Functor.const (Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))

/-- Every original simplicial operator commutes with the actual coefficient tensor unitors. -/
def cotangentWeightZeroTensorSimplicialIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (M : ModuleCat.{t} A) :
    ((cotangentWeightZeroTensorFamily.{u, v, t} k A).obj M).obj P ≅
      (SimplicialObject.const (ModuleCat.{max u v t} A)).obj
        ((cotangentWeightZeroCoefficientLift.{u, v, t} k A).obj M) :=
  let F := (ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M
  Functor.isoWhiskerRight (cotangentWeightZeroOnResolutionIso.{u, v} k A P) F ≪≫
    Functor.constComp SimplexCategoryᵒᵖ (ModuleCat.of A A) F ≪≫
      (SimplicialObject.const (ModuleCat.{max u v t} A)).mapIso
        (cotangentWeightZeroCoefficientRegularIso.{u, v, t} k A M)

/-- Its component is the original nested tensor, with the original augmentation coefficient. -/
@[simp]
theorem cotangentWeightZeroTensorSimplicialIso_tmul_tmul
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (M : ModuleCat.{t} A) (i : SimplexCategoryᵒᵖ) (m : M) (a : A)
    (p : (Over.mk (P.hom.app i) : Over A).left) :
    ((cotangentWeightZeroTensorSimplicialIso.{u, v, t} k A P M).hom.app i).hom
      (m ⊗ₜ[A] (a ⊗ₜ[(Over.mk (P.hom.app i) : Over A).left,
        (P.hom.app i).hom.toRingHom] p)) =
        ULift.up (((show A from (P.hom.app i).hom p) * a) • m) :=
  cotangentWeightZeroCoefficientLevelIso_tmul_tmul k A (Over.mk (P.hom.app i)) M m a p

/-- Maps of original augmented resolutions commute with the actual tensor-family isomorphism. -/
@[reassoc]
theorem cotangentWeightZeroTensorSimplicialIso_resolution_naturality
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
    (f : P ⟶ Q) (M : ModuleCat.{t} A) :
    ((cotangentWeightZeroTensorFamily.{u, v, t} k A).obj M).map f ≫
      (cotangentWeightZeroTensorSimplicialIso.{u, v, t} k A Q M).hom =
        (cotangentWeightZeroTensorSimplicialIso.{u, v, t} k A P M).hom := by
  apply NatTrans.ext
  funext i
  let F := (ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M
  change F.map ((cotangentWeightZeroOnResolutionMap k A f).app i) ≫
      (F.map (cotangentWeightZeroLevelIso k A (Over.mk (Q.hom.app i))).hom ≫
        (cotangentWeightZeroCoefficientRegularIso.{u, v, t} k A M).hom) =
    F.map (cotangentWeightZeroLevelIso k A (Over.mk (P.hom.app i))).hom ≫
      (cotangentWeightZeroCoefficientRegularIso.{u, v, t} k A M).hom
  have h := NatTrans.congr_app
    ((cotangentWeightZeroResolutionFunctorIso.{u, v} k A).hom.naturality f) i
  change (cotangentWeightZeroOnResolutionMap k A f).app i ≫
      (cotangentWeightZeroLevelIso k A (Over.mk (Q.hom.app i))).hom =
    (cotangentWeightZeroLevelIso k A (Over.mk (P.hom.app i))).hom at h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (cotangentWeightZeroCoefficientRegularIso.{u, v, t} k A M).hom)
      ((F.map_comp _ _).symm.trans (congrArg F.map h))))

/-- Coefficient maps commute with the actual level tensor unitor. -/
@[reassoc]
theorem cotangentWeightZeroCoefficientLevelIso_naturality
    (P : Over A) {M N : ModuleCat.{t} A} (f : M ⟶ N) :
    ((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).map f).app
        (cotangentWeightZeroLevel k A P) ≫
      (cotangentWeightZeroCoefficientLevelIso.{u, v, t} k A P N).hom =
        (cotangentWeightZeroCoefficientLevelIso.{u, v, t} k A P M).hom ≫
          (cotangentWeightZeroCoefficientLift.{u, v, t} k A).map f := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m x
  change ULift.up ((cotangentWeightZeroLevelIso k A P).hom.hom x • f.hom m) =
    ULift.up (f.hom ((cotangentWeightZeroLevelIso k A P).hom.hom x • m))
  exact congrArg ULift.up (f.hom.map_smul _ _).symm

/-- The original tensor family is naturally constant in resolution and coefficient maps together. -/
def cotangentWeightZeroTensorFamilyIso :
    cotangentWeightZeroTensorFamily.{u, v, t} k A ≅
      cotangentWeightZeroConstantCoefficientFamily k A :=
  NatIso.ofComponents
    (fun M => NatIso.ofComponents (fun P => cotangentWeightZeroTensorSimplicialIso.{u, v, t} k A P M)
      (by
        intro P Q f
        have h := cotangentWeightZeroTensorSimplicialIso_resolution_naturality k A f M
        exact h.trans (Category.comp_id _).symm))
    (by
      intro M N f
      apply NatTrans.ext
      funext P
      apply NatTrans.ext
      funext i
      exact cotangentWeightZeroCoefficientLevelIso_naturality k A (Over.mk (P.hom.app i)) f)

/-- Normalize the actual original degreewise coefficient tensor family. -/
def cotangentWeightZeroTensorComplexFunctor
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    ModuleCat.{t} A ⥤ ChainComplex (ModuleCat.{max u v t} A) ℕ :=
  cotangentWeightZeroTensorFamily.{u, v, t} k A ⋙
    (evaluation
      (Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
      (SimplicialObject (ModuleCat.{max u v t} A))).obj P ⋙
        normalizedMooreComplex (ModuleCat.{max u v t} A)

/-- The actual normalized tensor family is the chosen V4 constant coefficient model. -/
def cotangentWeightZeroTensorComplexIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (M : ModuleCat.{t} A) :
    (cotangentWeightZeroTensorComplexFunctor k A P).obj M ≅
      (cotangentWeightZeroCoefficientComplexFunctor k A).obj
        ((cotangentWeightZeroCoefficientLift.{u, v, t} k A).obj M) :=
  (normalizedMooreComplex (ModuleCat.{max u v t} A)).mapIso
    (cotangentWeightZeroTensorSimplicialIso.{u, v, t} k A P M)

/-- The normalization comparison is natural in original coefficient maps. -/
def cotangentWeightZeroTensorComplexNatIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    cotangentWeightZeroTensorComplexFunctor.{u, v, t} k A P ≅
      cotangentWeightZeroCoefficientLift.{u, v, t} k A ⋙
        cotangentWeightZeroCoefficientComplexFunctor k A :=
  NatIso.ofComponents (cotangentWeightZeroTensorComplexIso k A P) (by
    intro M N f
    let E := (cotangentWeightZeroTensorFamilyIso k A).hom.naturality f
    have h := NatTrans.congr_app E P
    change (normalizedMooreComplex (ModuleCat.{max u v t} A)).map _ ≫
        (normalizedMooreComplex (ModuleCat.{max u v t} A)).map _ =
      (normalizedMooreComplex (ModuleCat.{max u v t} A)).map _ ≫
        (normalizedMooreComplex (ModuleCat.{max u v t} A)).map _
    let F := normalizedMooreComplex (ModuleCat.{max u v t} A)
    exact (F.map_comp _ _).symm.trans
      ((congrArg F.map h).trans (F.map_comp _ _)))

/-- Original resolution maps also commute with the actual normalized comparison. -/
@[reassoc]
theorem cotangentWeightZeroTensorComplexIso_resolution_naturality
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
    (f : P ⟶ Q) (M : ModuleCat.{t} A) :
    (normalizedMooreComplex (ModuleCat.{max u v t} A)).map
        (((cotangentWeightZeroTensorFamily.{u, v, t} k A).obj M).map f) ≫
      (cotangentWeightZeroTensorComplexIso k A Q M).hom =
        (cotangentWeightZeroTensorComplexIso k A P M).hom := by
  let F := normalizedMooreComplex (ModuleCat.{max u v t} A)
  have h := cotangentWeightZeroTensorSimplicialIso_resolution_naturality.{u, v, t} k A f M
  exact (F.map_comp _ _).symm.trans (congrArg F.map h)

/-- Homology of the actual original coefficient tensor family, before any computation. -/
def cotangentWeightZeroTensorHomologyFunctor
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) (n : ℕ) :
    ModuleCat.{t} A ⥤ ModuleCat.{max u v t} A :=
  cotangentWeightZeroTensorComplexFunctor k A P ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{max u v t} A) (ComplexShape.down ℕ) n

/-- Every computed degree of the chosen constant model is transported from the actual tensor family. -/
def cotangentWeightZeroTensorHomologyNatIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) (n : ℕ) :
    cotangentWeightZeroTensorHomologyFunctor.{u, v, t} k A P n ≅
      cotangentWeightZeroCoefficientLift.{u, v, t} k A ⋙ andreQuillenWeightZeroHomologyFunctor k A n :=
  Functor.isoWhiskerRight (cotangentWeightZeroTensorComplexNatIso k A P)
    (HomologicalComplex.homologyFunctor (ModuleCat.{max u v t} A) (ComplexShape.down ℕ) n)

/-- H₀ of the actual coefficient tensor family is naturally the original lifted coefficient. -/
def cotangentWeightZeroTensorHomologyZeroNatIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    cotangentWeightZeroTensorHomologyFunctor.{u, v, t} k A P 0 ≅
      cotangentWeightZeroCoefficientLift.{u, v, t} k A :=
  cotangentWeightZeroTensorHomologyNatIso k A P 0 ≪≫
    Functor.isoWhiskerLeft (cotangentWeightZeroCoefficientLift.{u, v, t} k A)
      (andreQuillenWeightZeroHomologyZeroIso.{u, v, max u v t} k A) ≪≫
    NatIso.ofComponents (fun M => Iso.refl _) (by
      intro M N f
      change (𝟭 (ModuleCat.{max u v t} A)).map
        ((cotangentWeightZeroCoefficientLift.{u, v, t} k A).map f) =
        𝟙 _ ≫ (cotangentWeightZeroCoefficientLift.{u, v, t} k A).map f
      exact (Functor.id_map _).trans (Category.id_comp _).symm)

/-- H₀ also returns the actual original coefficient carrier, without a carrier-size constraint. -/
def cotangentWeightZeroTensorHomologyZeroLinearEquiv
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (M : ModuleCat.{t} A) :
    (cotangentWeightZeroTensorHomologyFunctor k A P 0).obj M ≃ₗ[A] M :=
  ((cotangentWeightZeroTensorHomologyZeroNatIso k A P).app M).toLinearEquiv.trans
    ULift.moduleEquiv

/-- Positive vanishing is transported through the actual tensor-family normalization isomorphism. -/
theorem cotangentWeightZeroTensorHomology_isZero_succ
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (M : ModuleCat.{t} A) (n : ℕ) :
    IsZero ((cotangentWeightZeroTensorHomologyFunctor k A P (n + 1)).obj M) :=
  (andreQuillenWeightZeroHomology_isZero_succ k A
    ((cotangentWeightZeroCoefficientLift.{u, v, t} k A).obj M) n).of_iso
      ((cotangentWeightZeroTensorHomologyNatIso k A P (n + 1)).app M)

end CommAlgCat

end
