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
# Weight-zero cotangent modules and homology

Let `k` be a commutative ring and `P → A` an augmented commutative `k`-algebra. Since `Ω⁰[P/k]
= P`, its weight-zero module is `A ⊗[P] P`. The regular tensor unitor sends `a ⊗ p` to
`P.hom(p) * a` and identifies this module with `A`.

These unitors identify the weight-zero module of every augmented simplicial resolution with
the constant simplicial `A`-module. For an arbitrary coefficient module `M`, the normalized
constant complex is chain homotopy equivalent to `M` concentrated in degree zero. Consequently
its degree-zero homology is naturally `M` and all positive homology objects are zero. The
coefficient carrier universe is independent.

Reference: Loday, *Cyclic Homology*, second edition, Sections 3.5.4 and 3.5.8, and Exercise
E.3.5.2.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial TensorProduct ChangeOfRings

universe u v t

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- The regular module in cotangent weight zero.

For `P → A`, this is the scalar extension `A ⊗[P] P`, corresponding to `Ω⁰[P/k] = P`. -/
def cotangentWeightZeroLevel (P : Over A) : ModuleCat.{max u v} A :=
  (ModuleCat.extendScalars P.hom.hom.toRingHom).obj (ModuleCat.of P.left P.left)

/-- The regular tensor unitor for cotangent weight zero.

For `P → A`, this `A`-module isomorphism identifies `A ⊗[P] P` with `A`. -/
def cotangentWeightZeroLevelIso (P : Over A) :
    cotangentWeightZeroLevel k A P ≅ ModuleCat.of A A := by
  letI : Algebra P.left A := P.hom.hom.toRingHom.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid P.left A A).toModuleIso

/-- The coordinate formula for the weight-zero unitor.

The unitor sends `a ⊗ p` to `P.hom(p) * a`, where `P.hom : P → A` is the augmentation. -/
@[simp]
theorem cotangentWeightZeroLevelIso_tmul (P : Over A) (a : A) (p : P.left) :
    (cotangentWeightZeroLevelIso k A P).hom.hom
      (a ⊗ₜ[P.left,P.hom.hom.toRingHom] p) = P.hom.hom p * a := by
  letI : Algebra P.left A := P.hom.hom.toRingHom.toAlgebra
  have h := TensorProduct.AlgebraTensorModule.rid_tmul (R := P.left) A p a
  exact h.trans (by
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    rfl)

/-- The weight-zero map between augmented algebras.

For `f : P → Q` over `A`, compose the unitor `A ⊗[P] P → A` with the inverse unitor `A → A
⊗[Q] Q`. -/
def cotangentWeightZeroTransport {P Q : Over A} (_f : P ⟶ Q) :
    cotangentWeightZeroLevel k A P ⟶ cotangentWeightZeroLevel k A Q :=
  (cotangentWeightZeroLevelIso k A P).hom ≫ (cotangentWeightZeroLevelIso k A Q).inv

/-- The tensor formula for weight-zero transport.

A map `f : P → Q` over `A` induces `a ⊗ p ↦ a ⊗ f(p)` on the weight-zero modules. -/
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

/-- The weight-zero module of an augmented simplicial resolution.

For `P_• → A`, degree `i` is `A ⊗[P_i] P_i`, and each simplicial operator acts by the
corresponding weight-zero transport. -/
def cotangentWeightZeroOnResolution
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    SimplicialObject (ModuleCat.{max u v} A) where
  obj i := cotangentWeightZeroLevel k A (Over.mk (P.hom.app i))
  map f := cotangentWeightZeroTransport k A ((Over.lift P.left P.hom).map f)
  map_id i := by
    exact (cotangentWeightZeroLevelIso k A (Over.mk (P.hom.app i))).hom_inv_id
  map_comp f g := by
    simp only [cotangentWeightZeroTransport, Category.assoc, Iso.inv_hom_id_assoc]

/-- The constant-module comparison in cotangent weight zero.

The regular tensor unitors identify the weight-zero simplicial module of `P_• → A` with the
constant simplicial module on `A`. -/
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

/-- The weight-zero map of augmented simplicial resolutions.

A map between resolutions over `A` induces a simplicial module map by composing the source
comparison with the inverse target comparison to the constant module `A`. -/
def cotangentWeightZeroOnResolutionMap
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
    (_f : P ⟶ Q) : cotangentWeightZeroOnResolution k A P ⟶
      cotangentWeightZeroOnResolution k A Q :=
  (cotangentWeightZeroOnResolutionIso k A P).hom ≫
    (cotangentWeightZeroOnResolutionIso k A Q).inv

/-- The identity map on a weight-zero resolution module.

The identity of an augmented simplicial resolution induces the identity on its weight-zero
simplicial module. -/
@[simp]
theorem cotangentWeightZeroOnResolutionMap_id
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    cotangentWeightZeroOnResolutionMap k A (𝟙 P) =
      𝟙 (cotangentWeightZeroOnResolution k A P) := by
  exact (cotangentWeightZeroOnResolutionIso k A P).hom_inv_id

/-- Composition of weight-zero resolution maps.

For composable maps of augmented simplicial resolutions, the weight-zero map of their
composite equals the composite of their weight-zero maps. -/
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

/-- The weight-zero functor on augmented resolutions.

This functor assigns to `P_• → A` the simplicial module with degreewise value `A ⊗[P_i] P_i`. -/
def cotangentWeightZeroResolutionFunctor :
    Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) ⥤
      SimplicialObject (ModuleCat.{max u v} A) where
  obj := cotangentWeightZeroOnResolution k A
  map := cotangentWeightZeroOnResolutionMap k A
  map_id := cotangentWeightZeroOnResolutionMap_id k A
  map_comp := cotangentWeightZeroOnResolutionMap_comp k A

/-- The natural constant comparison for weight-zero resolutions.

The weight-zero resolution functor is naturally isomorphic to the constant functor with value
the constant simplicial `A`-module. -/
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

/-- The normalized weight-zero coefficient complex.

For an `A`-module `M`, this is the normalized Moore complex of the constant simplicial module
on `M`. Its construction retains the carrier universe of `M`. -/
def cotangentWeightZeroCoefficientComplexFunctor :
    ModuleCat.{t} A ⥤ ChainComplex (ModuleCat.{t} A) ℕ :=
  SimplicialObject.const (ModuleCat.{t} A) ⋙ normalizedMooreComplex (ModuleCat.{t} A)

/-- The augmentation of the weight-zero coefficient complex.

For each `M`, the inclusion into the alternating-face complex followed by the constant
augmentation gives a chain map from the normalized constant complex to `M` concentrated in
degree zero. These maps are natural in `M`. -/
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

/-- The contraction of the weight-zero coefficient complex.

The Dold–Kan normalization comparison and the constant extra degeneracy give a chain homotopy
equivalence from the normalized constant complex on `M` to `M` concentrated in degree zero. -/
def cotangentWeightZeroCoefficientHomotopyEquiv (M : ModuleCat.{t} A) :
    HomotopyEquiv ((cotangentWeightZeroCoefficientComplexFunctor k A).obj M)
      ((ChainComplex.single₀ (ModuleCat.{t} A)).obj M) :=
  (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
    (Y := (SimplicialObject.const (ModuleCat.{t} A)).obj M)).trans
      (SimplicialObject.Augmented.constantRightExtraDegeneracy M).homotopyEquiv

/-- The quasi-isomorphism of weight-zero coefficient augmentation.

For every `A`-module `M`, the normalized constant augmentation induces an isomorphism on
homology in every degree. -/
theorem cotangentWeightZeroCoefficientAugmentation_quasiIso (M : ModuleCat.{t} A) :
    QuasiIso ((cotangentWeightZeroCoefficientAugmentation.{u, v, t} k A).app M) :=
  (cotangentWeightZeroCoefficientHomotopyEquiv.{u, v, t} k A M).quasiIso_hom

/-- The weight-zero homology functor in a fixed degree.

For `n ∈ ℕ`, this sends a coefficient module `M` to the degree-`n` homology of its normalized
constant simplicial module. -/
def andreQuillenWeightZeroHomologyFunctor (n : ℕ) : ModuleCat.{t} A ⥤ ModuleCat.{t} A :=
  cotangentWeightZeroCoefficientComplexFunctor k A ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{t} A) (ComplexShape.down ℕ) n

/-- The weight-zero homology of a coefficient module.

For an `A`-module `M` and `n ∈ ℕ`, this is the degree-`n` homology object of the normalized
weight-zero coefficient complex. -/
def andreQuillenWeightZeroHomology (M : ModuleCat.{t} A) (n : ℕ) : ModuleCat.{t} A :=
  (andreQuillenWeightZeroHomologyFunctor.{u, v, t} k A n).obj M

/-- The natural degree-zero weight-zero homology comparison.

The normalized constant augmentation identifies the degree-zero weight-zero homology functor
naturally with the identity functor on `A`-modules. -/
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

/-- Vanishing of positive weight-zero homology.

For every coefficient module `M` and `n ∈ ℕ`, the weight-zero homology object in degree `n+1`
is zero. -/
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
