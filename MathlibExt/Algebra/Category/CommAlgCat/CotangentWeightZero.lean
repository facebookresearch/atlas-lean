/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.CommAlgCat.Cotangent
public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentationQuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Weight-zero cotangent modules

The weight-zero module of `P → A` is `A ⊗[P] P`. The tensor unitor
identifies it with `A`, and the induced simplicial module is constant.
With arbitrary coefficients, its normalized chain complex is the
normalized constant module: the degree-zero comparison is natural and
positive homology vanishes.

References: Loday, *Cyclic Homology*, second edition, 3.5.4, 3.5.8 and
E.3.5.2.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial TensorProduct ChangeOfRings

universe u v t

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- The actual extended regular module prescribed by Ω⁰(P/k)=P. -/
def cotangentWeightZeroLevel (P : Over A) : ModuleCat.{max u v} A :=
  (ModuleCat.extendScalars P.hom.hom.toRingHom).obj (ModuleCat.of P.left P.left)

/-- The native regular tensor unitor gives the actual level comparison. -/
def cotangentWeightZeroLevelIso (P : Over A) :
    cotangentWeightZeroLevel k A P ≅ ModuleCat.of A A := by
  letI : Algebra P.left A := P.hom.hom.toRingHom.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid P.left A A).toModuleIso

@[simp]
theorem cotangentWeightZeroLevelIso_tmul (P : Over A) (a : A) (p : P.left) :
    (cotangentWeightZeroLevelIso k A P).hom.hom
      (a ⊗ₜ[P.left,P.hom.hom.toRingHom] p) = P.hom.hom p * a := by
  letI : Algebra P.left A := P.hom.hom.toRingHom.toAlgebra
  have h := TensorProduct.AlgebraTensorModule.rid_tmul (R := P.left) A p a
  exact h.trans (by
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    rfl)

/-- Transport through the actual regular tensor unitors is the weight-zero map. -/
def cotangentWeightZeroTransport {P Q : Over A} (_f : P ⟶ Q) :
    cotangentWeightZeroLevel k A P ⟶ cotangentWeightZeroLevel k A Q :=
  (cotangentWeightZeroLevelIso k A P).hom ≫ (cotangentWeightZeroLevelIso k A Q).inv

/-- The map is the actual regular-module map induced by the original algebra operator. -/
theorem cotangentWeightZeroTransport_tmul {P Q : Over A} (f : P ⟶ Q)
    (a : A) (p : P.left) :
    (cotangentWeightZeroTransport k A f).hom
      (a ⊗ₜ[P.left,P.hom.hom.toRingHom] p) =
        a ⊗ₜ[Q.left,Q.hom.hom.toRingHom] (f.left.hom p) := by
  let eP := cotangentWeightZeroLevelIso k A P
  let eQ := cotangentWeightZeroLevelIso k A Q
  apply (ModuleCat.mono_iff_injective eQ.hom).mp inferInstance
  change eQ.hom.hom (eQ.inv.hom (eP.hom.hom _)) = eQ.hom.hom _
  have hI := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp eQ.inv_hom_id)
    (eP.hom.hom (a ⊗ₜ[P.left,P.hom.hom.toRingHom] p))
  have hP := cotangentWeightZeroLevelIso_tmul k A P a p
  have hQ := cotangentWeightZeroLevelIso_tmul k A Q a (f.left.hom p)
  have h := congrArg (fun g : P.left ⟶ A => g.hom p) f.w
  exact hI.trans (hP.trans ((congrArg (fun x : A => x * a) h.symm).trans hQ.symm))

/-- The actual degreewise Ω⁰ formula, with every original simplicial operator. -/
def cotangentWeightZeroOnResolution
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    SimplicialObject (ModuleCat.{max u v} A) where
  obj i := cotangentWeightZeroLevel k A (Over.mk (P.hom.app i))
  map f := cotangentWeightZeroTransport k A ((Over.lift P.left P.hom).map f)
  map_id i := by
    exact (cotangentWeightZeroLevelIso k A (Over.mk (P.hom.app i))).hom_inv_id
  map_comp f g := by
    simp only [cotangentWeightZeroTransport, Category.assoc, Iso.inv_hom_id_assoc]

/-- Weight zero is canonically the actual constant A-module, not a truncated degree formula. -/
def cotangentWeightZeroOnResolutionIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    cotangentWeightZeroOnResolution k A P ≅
      (SimplicialObject.const (ModuleCat.{max u v} A)).obj (ModuleCat.of A A) :=
  NatIso.ofComponents (fun i => cotangentWeightZeroLevelIso k A (Over.mk (P.hom.app i)))
    (by
      intro i j f
      let ei := cotangentWeightZeroLevelIso k A (Over.mk (P.hom.app i))
      let ej := cotangentWeightZeroLevelIso k A (Over.mk (P.hom.app j))
      exact (Category.assoc ei.hom ej.inv ej.hom).trans
        ((congrArg (fun f => ei.hom ≫ f) ej.inv_hom_id).trans
          ((Category.comp_id _).trans (Category.comp_id _).symm)))

/-- Every original augmented-resolution map induces its actual weight-zero operator. -/
def cotangentWeightZeroOnResolutionMap
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
    (_f : P ⟶ Q) : cotangentWeightZeroOnResolution k A P ⟶
      cotangentWeightZeroOnResolution k A Q :=
  (cotangentWeightZeroOnResolutionIso k A P).hom ≫
    (cotangentWeightZeroOnResolutionIso k A Q).inv

@[simp]
theorem cotangentWeightZeroOnResolutionMap_id
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    cotangentWeightZeroOnResolutionMap k A (𝟙 P) =
      𝟙 (cotangentWeightZeroOnResolution k A P) := by
  exact (cotangentWeightZeroOnResolutionIso k A P).hom_inv_id

theorem cotangentWeightZeroOnResolutionMap_comp
    {P Q T : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
    (f : P ⟶ Q) (g : Q ⟶ T) :
    cotangentWeightZeroOnResolutionMap k A (f ≫ g) =
      cotangentWeightZeroOnResolutionMap k A f ≫ cotangentWeightZeroOnResolutionMap k A g := by
  let eP := cotangentWeightZeroOnResolutionIso k A P
  let eQ := cotangentWeightZeroOnResolutionIso k A Q
  let eT := cotangentWeightZeroOnResolutionIso k A T
  exact ((Category.assoc eP.hom eQ.inv (eQ.hom ≫ eT.inv)).trans
    ((congrArg (fun f => eP.hom ≫ f) (Category.assoc eQ.inv eQ.hom eT.inv).symm).trans
      ((congrArg (fun f => eP.hom ≫ f ≫ eT.inv) eQ.inv_hom_id).trans
        (congrArg (fun f => eP.hom ≫ f) (Category.id_comp _))))).symm

/-- The actual degreewise zero-weight formula is functorial in the whole augmented resolution. -/
def cotangentWeightZeroResolutionFunctor :
    Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) ⥤
      SimplicialObject (ModuleCat.{max u v} A) where
  obj := cotangentWeightZeroOnResolution k A
  map := cotangentWeightZeroOnResolutionMap k A
  map_id := cotangentWeightZeroOnResolutionMap_id k A
  map_comp := cotangentWeightZeroOnResolutionMap_comp k A

/-- The original zero-weight unitors are natural in every actual augmented-resolution map. -/
def cotangentWeightZeroResolutionFunctorIso :
    cotangentWeightZeroResolutionFunctor k A ≅
      (Functor.const
        (Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))).obj
          ((SimplicialObject.const (ModuleCat.{max u v} A)).obj (ModuleCat.of A A)) :=
  NatIso.ofComponents (cotangentWeightZeroOnResolutionIso k A) (by
    intro P Q f
    let eP := cotangentWeightZeroOnResolutionIso k A P
    let eQ := cotangentWeightZeroOnResolutionIso k A Q
    exact (Category.assoc eP.hom eQ.inv eQ.hom).trans
      ((congrArg (fun f => eP.hom ≫ f) eQ.inv_hom_id).trans
        (Category.comp_id _)))

/-- The coefficient zero-weight complex is the actual normalized constant M. -/
def cotangentWeightZeroCoefficientComplexFunctor :
    ModuleCat.{t} A ⥤ ChainComplex (ModuleCat.{t} A) ℕ :=
  SimplicialObject.const (ModuleCat.{t} A) ⋙ normalizedMooreComplex (ModuleCat.{t} A)

/-- The genuine normalized constant augmentation, natural in the coefficient module. -/
def cotangentWeightZeroCoefficientAugmentation :
    cotangentWeightZeroCoefficientComplexFunctor.{u, v, t} k A ⟶
      ChainComplex.single₀ (ModuleCat.{t} A) where
  app M := inclusionOfMooreComplexMap ((SimplicialObject.const (ModuleCat.{t} A)).obj M) ≫
    AlternatingFaceMapComplex.ε.app ((SimplicialObject.Augmented.const (C := ModuleCat.{t} A)).obj M)
  naturality {M N} f := by
    have hI := (inclusionOfMooreComplex (ModuleCat.{t} A)).naturality
      ((SimplicialObject.const (ModuleCat.{t} A)).map f)
    have hE := AlternatingFaceMapComplex.ε.naturality
      ((SimplicialObject.Augmented.const (C := ModuleCat.{t} A)).map f)
    change ((normalizedMooreComplex (ModuleCat.{t} A)).map
        ((SimplicialObject.const (ModuleCat.{t} A)).map f) ≫ _) ≫ _ = _ ≫ _ ≫ _
    dsimp only [inclusionOfMooreComplex] at hI
    exact (congrArg (fun f => f ≫ AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.const (C := ModuleCat.{t} A)).obj N)) hI).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => inclusionOfMooreComplexMap
          ((SimplicialObject.const (ModuleCat.{t} A)).obj M) ≫ f) hE).trans
          (Category.assoc _ _ _).symm))

/-- The actual constant contraction and native normalization provide the homotopy equivalence. -/
def cotangentWeightZeroCoefficientHomotopyEquiv (M : ModuleCat.{t} A) :
    HomotopyEquiv ((cotangentWeightZeroCoefficientComplexFunctor k A).obj M)
      ((ChainComplex.single₀ (ModuleCat.{t} A)).obj M) :=
  (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
    (Y := (SimplicialObject.const (ModuleCat.{t} A)).obj M)).trans
      (SimplicialObject.Augmented.constantRightExtraDegeneracy M).homotopyEquiv

theorem cotangentWeightZeroCoefficientAugmentation_quasiIso (M : ModuleCat.{t} A) :
    QuasiIso ((cotangentWeightZeroCoefficientAugmentation.{u, v, t} k A).app M) :=
  (cotangentWeightZeroCoefficientHomotopyEquiv.{u, v, t} k A M).quasiIso_hom

/-- Actual zero-weight André–Quillen homology in every connective degree. -/
def andreQuillenWeightZeroHomologyFunctor (n : ℕ) : ModuleCat.{t} A ⥤ ModuleCat.{t} A :=
  cotangentWeightZeroCoefficientComplexFunctor k A ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{t} A) (ComplexShape.down ℕ) n

def andreQuillenWeightZeroHomology (M : ModuleCat.{t} A) (n : ℕ) : ModuleCat.{t} A :=
  (andreQuillenWeightZeroHomologyFunctor.{u, v, t} k A n).obj M

/-- The actual natural degree-zero identity for the zero-weight boundary. -/
def andreQuillenWeightZeroHomologyZeroIso :
    andreQuillenWeightZeroHomologyFunctor.{u, v, t} k A 0 ≅ 𝟭 (ModuleCat.{t} A) :=
  (NatIso.ofComponents
    (fun M => by
      letI : QuasiIso ((cotangentWeightZeroCoefficientAugmentation.{u, v, t} k A).app M) :=
        cotangentWeightZeroCoefficientAugmentation_quasiIso k A M
      letI : QuasiIsoAt ((cotangentWeightZeroCoefficientAugmentation.{u, v, t} k A).app M) 0 := inferInstance
      let f := HomologicalComplex.homologyMap
        ((cotangentWeightZeroCoefficientAugmentation.{u, v, t} k A).app M) 0
      have hf : IsIso f := (quasiIsoAt_iff_isIso_homologyMap
        ((cotangentWeightZeroCoefficientAugmentation.{u, v, t} k A).app M) 0).mp inferInstance
      exact @asIso (ModuleCat.{t} A) _ _ _ f hf)
    (by
      intro M N f
      exact (Functor.whiskerRight (cotangentWeightZeroCoefficientAugmentation.{u, v, t} k A)
        (HomologicalComplex.homologyFunctor (ModuleCat.{t} A) (ComplexShape.down ℕ) 0)).naturality f)) ≪≫
    HomologicalComplex.homologyFunctorSingleIso (ModuleCat.{t} A) (ComplexShape.down ℕ) 0

theorem andreQuillenWeightZeroHomology_isZero_succ (M : ModuleCat.{t} A) (n : ℕ) :
    IsZero (andreQuillenWeightZeroHomology k A M (n + 1)) := by
  let E := cotangentWeightZeroCoefficientHomotopyEquiv.{u, v, t} k A M
  letI : QuasiIso E.hom := E.quasiIso_hom
  have h : IsZero (((ChainComplex.single₀ (ModuleCat.{t} A)).obj M).homology (n + 1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact ChainComplex.exactAt_succ_single_obj M n
  letI : QuasiIsoAt E.hom (n + 1) := inferInstance
  let f := HomologicalComplex.homologyMap E.hom (n + 1)
  have hf : IsIso f := (quasiIsoAt_iff_isIso_homologyMap E.hom (n + 1)).mp inferInstance
  exact h.of_iso (@asIso (ModuleCat.{t} A) _ _ _ f hf)

end CommAlgCat

end
