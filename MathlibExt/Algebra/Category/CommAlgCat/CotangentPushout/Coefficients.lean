/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentPushout.Chain
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentWeightZeroCoefficients
public import MathlibExt.Algebra.Category.ModuleCat.TensorRestriction

/-!
# Higher-form scalar change with arbitrary coefficients

Let `k → K` be a morphism of commutative rings, `A` a commutative `k`-algebra,
`B = K ⊗[k] A`, and `M` a `B`-module in an independent universe. For an augmentation
`P → const A`, the source coefficient diagram has terms
`M ⊗[A] (A ⊗[P] exteriorPower_P^n Ω(P/k))` in positive weight `n`, with the `B`-action
on the first factor. The target uses the higher forms of `K ⊗[k] P` over `K` and tensors
over `B` with the same module `M`.

Tensor cancellation and the higher-form scalar-change comparison identify these
simplicial diagrams. Their normalizations are isomorphic, and tensoring after
normalization gives a chain homotopy equivalent model for arbitrary `M`.

In weight zero the diagram is naturally constant on a universe lift of `M`. Its tensor
coordinate is `m ⊗ (a ⊗ p) ↦ (algebraMap A B (ε(p) * a)) • m`; degree-zero homology
is linearly equivalent to the original carrier `M`, and positive homology vanishes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicTopology
open scoped TensorProduct Simplicial

universe u v w t

namespace CommAlgCat.CotangentPushout

variable (k : Type u) (K : Type w) [CommRing k] [CommRing K] [Algebra k K]
  (A : CommAlgCat.{max u v w} k) (M : ModuleCat.{t} (target.{u, v, w} k K A))

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] tensorGroundAlgebra tensorRightAlgebra
attribute [local instance] overGroundAlgebra overRightAlgebra

/--
The tensor functor `X ↦ M ⊗[B] X` on `B = K ⊗[k] A`-modules, with coefficient
module `M` as the first factor and result carriers at height `max u v w t`.
-/
abbrev coefficientFunctor :
    ModuleCat.{max u v w} (target.{u, v, w} k K A) ⥤
      ModuleCat.{max u v w t} (target.{u, v, w} k K A) :=
  (ModuleCat.tensorBifunctorAt.{max u v w, t, max u v w} (target.{u, v, w} k K A)).obj M

/--
The functor `X ↦ M ⊗[A] X`, where the `A`-action on `M` is restricted along
`A → B = K ⊗[k] A` and the result is a `B`-module through its first tensor factor.
-/
abbrev restrictionCoefficientFunctor :
    ModuleCat.{max u v w} A ⥤ ModuleCat.{max u v w t} (target.{u, v, w} k K A) :=
  ModuleCat.TensorRestriction.functorAt.{max u v w, max u v w, t, max u v w} A (target.{u, v, w} k K A) M

/--
The natural tensor-cancellation isomorphism
`M ⊗[B] (B ⊗[A] X) ≅ M ⊗[A] X`, viewed as an isomorphism of `B`-module functors.
-/
def coefficientCancellation :
    moduleFunctor.{u, v, w} k K A ⋙ coefficientFunctor.{u, v, w, t} k K A M ≅
      restrictionCoefficientFunctor.{u, v, w, t} k K A M :=
  ModuleCat.TensorRestriction.cancellationNatIso.{max u v w, max u v w, t, max u v w} A (target.{u, v, w} k K A) M

/--
The simplicial `B`-module obtained by tensoring the degreewise weight-`n` higher forms
of `P` over `A` with the restricted coefficient module `M` as first factor.
-/
def sourceCoefficientSimplicial (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    SimplicialObject (ModuleCat.{max u v w t} (target.{u, v, w} k K A)) :=
  higherSimplicial.{u, v, w} k A n P ⋙ restrictionCoefficientFunctor.{u, v, w, t} k K A M

/--
The simplicial `B`-module obtained by tensoring the weight-`n` higher forms of the
scalar-changed augmentation over `K` with `M` over `B`, with `M` as first factor.
-/
def targetCoefficientSimplicial (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    SimplicialObject (ModuleCat.{max u v w t} (target.{u, v, w} k K A)) :=
  higherSimplicial.{w, v, u} K (target.{u, v, w} k K A) n (resolution.{u, v, w} k K A P) ⋙
    coefficientFunctor.{u, v, w, t} k K A M

/--
The simplicial isomorphism between the source coefficient diagram and the coefficient
diagram of the scalar-changed algebra, obtained from inverse tensor cancellation
followed by the higher-form scalar-change comparison.
-/
def coefficientDiagramIso (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    sourceCoefficientSimplicial.{u, v, w, t} k K A M n P ≅
      targetCoefficientSimplicial.{u, v, w, t} k K A M n P :=
  isoWhiskerLeft (higherSimplicial.{u, v, w} k A n P) (coefficientCancellation.{u, v, w, t} k K A M).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (higherSimplicialIso.{u, v, w} k K A n P) (coefficientFunctor.{u, v, w, t} k K A M)

/--
The component of the forward coefficient-diagram comparison is inverse tensor
cancellation followed by the coefficient tensor of the degreewise higher-form
scalar-change comparison.
-/
theorem coefficientDiagramIso_hom_app (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A))
    (i : SimplexCategoryᵒᵖ) :
    (coefficientDiagramIso.{u, v, w, t} k K A M n P).hom.app i =
      (coefficientCancellation.{u, v, w, t} k K A M).inv.app
          ((higherSimplicial.{u, v, w} k A n P).obj i) ≫
        (coefficientFunctor.{u, v, w, t} k K A M).map
          ((higherSimplicialIso.{u, v, w} k K A n P).hom.app i) := by
  let X := higherSimplicial.{u, v, w} k A n P
  let C := (coefficientCancellation.{u, v, w, t} k K A M).inv.app (X.obj i)
  let D := (coefficientFunctor.{u, v, w, t} k K A M).map
    ((higherSimplicialIso.{u, v, w} k K A n P).hom.app i)
  change C ≫ 𝟙 _ ≫ D = C ≫ D
  simp only [Category.id_comp]

/--
For an augmented-algebra map `f : P ⟶ Q`, the coefficient-diagram comparison commutes
with the higher-form map on the source and the scalar-changed higher-form map on the
target, with the same coefficient module `M`.
-/
@[reassoc]
theorem coefficientDiagramIso_naturality (n : ℕ)
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)}
    (f : P ⟶ Q) :
    whiskerRight (higherSimplicialMap.{u, v, w} k A n f) (restrictionCoefficientFunctor.{u, v, w, t} k K A M) ≫
        (coefficientDiagramIso.{u, v, w, t} k K A M n Q).hom =
      (coefficientDiagramIso.{u, v, w, t} k K A M n P).hom ≫
        whiskerRight (higherSimplicialMap.{w, v, u} K (target.{u, v, w} k K A) n (resolutionMap.{u, v, w} k K A f))
          (coefficientFunctor.{u, v, w, t} k K A M) := by
  apply NatTrans.ext
  funext i
  let sourceMap : sourceCoefficientSimplicial.{u, v, w, t} k K A M n P ⟶
      sourceCoefficientSimplicial.{u, v, w, t} k K A M n Q :=
    whiskerRight (higherSimplicialMap.{u, v, w} k A n f) (restrictionCoefficientFunctor.{u, v, w, t} k K A M)
  let targetMap : targetCoefficientSimplicial.{u, v, w, t} k K A M n P ⟶
      targetCoefficientSimplicial.{u, v, w, t} k K A M n Q :=
    whiskerRight (higherSimplicialMap.{w, v, u} K (target.{u, v, w} k K A) n
      (resolutionMap.{u, v, w} k K A f)) (coefficientFunctor.{u, v, w, t} k K A M)
  change (sourceMap ≫ (coefficientDiagramIso.{u, v, w, t} k K A M n Q).hom).app i =
    ((coefficientDiagramIso.{u, v, w, t} k K A M n P).hom ≫ targetMap).app i
  rw [NatTrans.comp_app, NatTrans.comp_app,
    coefficientDiagramIso_hom_app.{u, v, w, t} k K A M n Q i,
    coefficientDiagramIso_hom_app.{u, v, w, t} k K A M n P i]
  let P₀ := (Over.lift P.left P.hom).obj i
  let Q₀ := (Over.lift Q.left Q.hom).obj i
  let f₀ : P₀ ⟶ Q₀ := (Over.liftDiagramMap A f).app i
  let F := moduleFunctor.{u, v, w} k K A
  let G := coefficientFunctor.{u, v, w, t} k K A M
  let R := restrictionCoefficientFunctor.{u, v, w, t} k K A M
  let C := (coefficientCancellation.{u, v, w, t} k K A M).inv
  let a := cotangentHigherMap.{u, max v w} k A n f₀
  let b := cotangentHigherMap.{w, max u v} K (target.{u, v, w} k K A) n
    ((overFunctor.{u, v, w} k K A).map f₀)
  let eP := higherIso.{u, v, w} k K A n P₀
  let eQ := higherIso.{u, v, w} k K A n Q₀
  have hc : R.map a ≫ C.app _ = C.app _ ≫ G.map (F.map a) := C.naturality a
  have he : F.map a ≫ eQ.hom = eP.hom ≫ b :=
    higherIso_naturality.{u, v, w} k K A n f₀
  change R.map a ≫ (C.app _ ≫ G.map eQ.hom) =
    (C.app _ ≫ G.map eP.hom) ≫ G.map b
  calc
    R.map a ≫ (C.app _ ≫ G.map eQ.hom) = (R.map a ≫ C.app _) ≫ G.map eQ.hom :=
      (Category.assoc _ _ _).symm
    _ = (C.app _ ≫ G.map (F.map a)) ≫ G.map eQ.hom :=
      congrArg (fun z => z ≫ G.map eQ.hom) hc
    _ = C.app _ ≫ G.map (F.map a ≫ eQ.hom) :=
      (Category.assoc _ _ _).trans (congrArg (fun z => C.app _ ≫ z) (G.map_comp _ _).symm)
    _ = C.app _ ≫ G.map (eP.hom ≫ b) := congrArg (fun z => C.app _ ≫ G.map z) he
    _ = (C.app _ ≫ G.map eP.hom) ≫ G.map b :=
      (congrArg (fun z => C.app _ ≫ z) (G.map_comp _ _)).trans (Category.assoc _ _ _).symm

/--
The normalized Moore complex of the source coefficient diagram, with coefficient
tensor applied before normalization.
-/
def sourceCoefficientNormalizedDiagram (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    ChainComplex (ModuleCat.{max u v w t} (target.{u, v, w} k K A)) ℕ :=
  (normalizedMooreComplex (ModuleCat.{max u v w t} (target.{u, v, w} k K A))).obj
    (sourceCoefficientSimplicial.{u, v, w, t} k K A M n P)

/--
The normalized Moore complex of the coefficient higher-form diagram of the
scalar-changed augmented algebra.
-/
def targetCoefficientNormalizedDiagram (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    ChainComplex (ModuleCat.{max u v w t} (target.{u, v, w} k K A)) ℕ :=
  (normalizedMooreComplex (ModuleCat.{max u v w t} (target.{u, v, w} k K A))).obj
    (targetCoefficientSimplicial.{u, v, w, t} k K A M n P)

/--
The chain-complex isomorphism obtained by normalizing the coefficient simplicial
comparison in weight `n`.
-/
def coefficientDiagramChainIso (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    sourceCoefficientNormalizedDiagram.{u, v, w, t} k K A M n P ≅
      targetCoefficientNormalizedDiagram.{u, v, w, t} k K A M n P :=
  (normalizedMooreComplex (ModuleCat.{max u v w t} (target.{u, v, w} k K A))).mapIso
    (coefficientDiagramIso.{u, v, w, t} k K A M n P)

/--
The chain complex obtained by applying `X ↦ M ⊗[A] X` to the normalized weight-`n`
higher-form complex of `P`, with its resulting `B`-module structure.
-/
def sourceCoefficientMappedNormalized (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    ChainComplex (ModuleCat.{max u v w t} (target.{u, v, w} k K A)) ℕ :=
  ((restrictionCoefficientFunctor.{u, v, w, t} k K A M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    ((normalizedFunctor.{u, v, w} k A n).obj P)

/--
The chain complex obtained by applying `X ↦ M ⊗[B] X` after normalizing the
weight-`n` higher forms of the scalar-changed augmentation.
-/
def targetCoefficientMappedNormalized (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    ChainComplex (ModuleCat.{max u v w t} (target.{u, v, w} k K A)) ℕ :=
  ((coefficientFunctor.{u, v, w, t} k K A M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    ((targetNormalizedFunctor.{u, v, w} k K A n).obj P)

/--
The chain homotopy equivalence between the source and target models obtained by
tensoring after normalization, for an arbitrary coefficient module `M`.
-/
def coefficientMappedNormalizedHomotopyEquiv (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    HomotopyEquiv (sourceCoefficientMappedNormalized.{u, v, w, t} k K A M n P)
      (targetCoefficientMappedNormalized.{u, v, w, t} k K A M n P) :=
  (HomotopyEquiv.ofIso
    (((NatIso.mapHomologicalComplex (coefficientCancellation.{u, v, w, t} k K A M)
      (ComplexShape.down ℕ)).app ((normalizedFunctor.{u, v, w} k A n).obj P)).symm)).trans
    ((coefficientFunctor.{u, v, w, t} k K A M).mapHomotopyEquiv (normalizedHomotopyEquiv.{u, v, w} k K A n P))

/--
The chain homotopy equivalence between applying the source coefficient tensor functor
after normalization and normalizing the source coefficient simplicial diagram.
-/
def coefficientNormalizationHomotopyEquiv (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    HomotopyEquiv (sourceCoefficientMappedNormalized.{u, v, w, t} k K A M n P)
      (sourceCoefficientNormalizedDiagram.{u, v, w, t} k K A M n P) :=
  ((restrictionCoefficientFunctor.{u, v, w, t} k K A M).mapHomotopyEquiv
    (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := higherSimplicial.{u, v, w} k A n P))).trans
    ((HomotopyEquiv.ofIso
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso
        (restrictionCoefficientFunctor.{u, v, w, t} k K A M)).app (higherSimplicial.{u, v, w} k A n P))).trans
      (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
        (Y := sourceCoefficientSimplicial.{u, v, w, t} k K A M n P)).symm)

/--
The homology isomorphism in degree `i` induced by the coefficient comparison between
the two models that tensor after normalization, at weight `n`.
-/
def coefficientMappedHomologyIso (n i : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    (sourceCoefficientMappedNormalized.{u, v, w, t} k K A M n P).homology i ≅
      (targetCoefficientMappedNormalized.{u, v, w, t} k K A M n P).homology i :=
  (coefficientMappedNormalizedHomotopyEquiv.{u, v, w, t} k K A M n P).toHomologyIso i

/--
The simplicial isomorphism from the source weight-zero coefficient diagram to the
constant diagram on the canonical universe lift of the `B`-module `M`.
-/
def zeroCoefficientSimplicialIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    sourceCoefficientSimplicial.{u, v, w, t} k K A M 0 P ≅
      (SimplicialObject.const (ModuleCat.{max u v w t} (target.{u, v, w} k K A))).obj
        ((CommAlgCat.cotangentWeightZeroCoefficientLift.{w, max u v, t} K (target.{u, v, w} k K A)).obj M) :=
  coefficientDiagramIso.{u, v, w, t} k K A M 0 P ≪≫
    isoWhiskerRight (higherSimplicialZeroIso.{w, v, u} K (target.{u, v, w} k K A) (resolution.{u, v, w} k K A P))
      (coefficientFunctor.{u, v, w, t} k K A M) ≪≫
    CommAlgCat.cotangentWeightZeroTensorSimplicialIso.{w, max u v, t} K (target.{u, v, w} k K A)
      (resolution.{u, v, w} k K A P) M

/--
In simplicial degree `i`, the constant-diagram comparison sends
`m ⊗[A] (a ⊗[P_i] p)` to `ULift.up ((algebraMap A B (ε_i(p) * a)) • m)`, where
`B = K ⊗[k] A` and `ε_i` is the augmentation.
-/
@[simp]
theorem zeroCoefficientSimplicialIso_tmul
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A))
    (i : SimplexCategoryᵒᵖ) (m : M) (a : A) (p : P.left.obj i) :
    letI : Module A M := Module.compHom M (algebraMap A (target.{u, v, w} k K A))
    letI : Algebra (P.left.obj i) A :=
      CommAlgCat.cotangentAlgebra.{u, max v w} k A ((Over.lift P.left P.hom).obj i)
    let C := (ModuleCat.restrictScalars ((Over.lift P.left P.hom).obj i).hom.hom.toRingHom).obj
      (ModuleCat.of A A)
    letI : Module (P.left.obj i) C := C.isModule
    let D := ModuleCat.of ((Over.lift P.left P.hom).obj i).left ((Over.lift P.left P.hom).obj i).left
    letI : Module (P.left.obj i) D := D.isModule
    ((zeroCoefficientSimplicialIso.{u, v, w, t} k K A M P).hom.app i).hom
        (m ⊗ₜ[A] (a ⊗ₜ[P.left.obj i] p)) =
      ULift.up ((algebraMap A (target.{u, v, w} k K A) ((show A from (P.hom.app i).hom p) * a)) • m) := by
  letI : Module A M := Module.compHom M (algebraMap A (target.{u, v, w} k K A))
  letI : Algebra (P.left.obj i) A :=
    CommAlgCat.cotangentAlgebra.{u, max v w} k A ((Over.lift P.left P.hom).obj i)
  dsimp only
  let C := (ModuleCat.restrictScalars ((Over.lift P.left P.hom).obj i).hom.hom.toRingHom).obj
    (ModuleCat.of A A)
  letI : Module (P.left.obj i) C := C.isModule
  let D := ModuleCat.of ((Over.lift P.left P.hom).obj i).left ((Over.lift P.left P.hom).obj i).left
  letI : Module (P.left.obj i) D := D.isModule
  let R := resolution.{u, v, w} k K A P
  letI : Algebra (R.left.obj i) (target.{u, v, w} k K A) :=
    CommAlgCat.cotangentAlgebra.{w, max u v} K (target.{u, v, w} k K A)
      ((Over.lift R.left R.hom).obj i)
  let C' := (ModuleCat.restrictScalars ((Over.lift R.left R.hom).obj i).hom.hom.toRingHom).obj
    (ModuleCat.of (target.{u, v, w} k K A) (target.{u, v, w} k K A))
  letI : Module (R.left.obj i) C' := C'.isModule
  let D' := ModuleCat.of ((Over.lift R.left R.hom).obj i).left ((Over.lift R.left R.hom).obj i).left
  letI : Module (R.left.obj i) D' := D'.isModule
  letI : Algebra (R.left.obj i) ((algebraFunctor.{u, v, w} k K).obj (P.left.obj i)) :=
    Algebra.id (R.left.obj i)
  let L : ModuleCat.{max u v w} A := (higherSimplicial.{u, v, w} k A 0 P).obj i
  let X : ModuleCat.{max u v w} (target.{u, v, w} k K A) :=
    (moduleFunctor.{u, v, w} k K A).obj L
  let Y : ModuleCat.{max u v w} (target.{u, v, w} k K A) :=
    (higherSimplicial.{w, v, u} K (target.{u, v, w} k K A) 0 R).obj i
  let G := coefficientFunctor.{u, v, w, t} k K A M
  let c : (restrictionCoefficientFunctor.{u, v, w, t} k K A M).obj L ⟶ G.obj X :=
    (coefficientCancellation.{u, v, w, t} k K A M).inv.app L
  let e : X ⟶ Y := (higherSimplicialIso.{u, v, w} k K A 0 P).hom.app i
  let z : G.obj Y ⟶
      (CommAlgCat.cotangentWeightZeroCoefficientLift.{w, max u v, t}
        K (target.{u, v, w} k K A)).obj M :=
    (CommAlgCat.cotangentWeightZeroTensorSimplicialIso.{w, max u v, t}
      K (target.{u, v, w} k K A) R M).hom.app i
  let l : L := a ⊗ₜ[P.left.obj i] p
  let x : X := (1 : target.{u, v, w} k K A) ⊗ₜ[A] l
  let y : Y := algebraMap A (target.{u, v, w} k K A) a ⊗ₜ[R.left.obj i]
    algebraUnit.{u, v, w} k K (P.left.obj i) p
  have hc : c.hom (m ⊗ₜ[A] l) = (m ⊗ₜ[target.{u, v, w} k K A] x) :=
    ModuleCat.TensorRestriction.cancellationNatIso_inv_tmul
      A (target.{u, v, w} k K A) M L m l
  have he : e.hom x = y := by
    let P₀ := (Over.lift P.left P.hom).obj i
    let Q₀ := (Over.lift R.left R.hom).obj i
    let F := moduleFunctor.{u, v, w} k K A
    let rP : L ≅ ModuleCat.of A A :=
      CommAlgCat.cotangentWeightZeroLevelIso.{u, max v w} k A P₀
    let rQ : Y ≅ ModuleCat.of (target.{u, v, w} k K A) (target.{u, v, w} k K A) :=
      CommAlgCat.cotangentWeightZeroLevelIso.{w, max u v}
        K (target.{u, v, w} k K A) Q₀
    let r : F.obj (ModuleCat.of A A) ≅
        ModuleCat.of (target.{u, v, w} k K A) (target.{u, v, w} k K A) :=
      (TensorProduct.AlgebraTensorModule.rid A
        (target.{u, v, w} k K A) (target.{u, v, w} k K A)).toModuleIso
    let f : X ⟶ F.obj (ModuleCat.of A A) := F.map rP.hom
    have hcomp : e = f ≫ r.hom ≫ rQ.inv := rfl
    have hP : rP.hom.hom l = (show A from (P.hom.app i).hom p) * a :=
      CommAlgCat.cotangentWeightZeroLevelIso_tmul.{u, max v w} k A P₀ a p
    have hf : f.hom x = (1 : target.{u, v, w} k K A) ⊗ₜ[A]
        ((show A from (P.hom.app i).hom p) * a) :=
      (ModuleCat.ExtendScalars.map_tmul (algebraMap A (target.{u, v, w} k K A))
        rP.hom 1 l).trans
          (congrArg (fun z : ModuleCat.of A A =>
            (1 : target.{u, v, w} k K A) ⊗ₜ[A] z) hP)
    have hr : r.hom.hom ((1 : target.{u, v, w} k K A) ⊗ₜ[A]
        ((show A from (P.hom.app i).hom p) * a)) =
        algebraMap A (target.{u, v, w} k K A)
          ((show A from (P.hom.app i).hom p) * a) := by
      exact (TensorProduct.AlgebraTensorModule.rid_tmul (target.{u, v, w} k K A)
        ((show A from (P.hom.app i).hom p) * a) 1).trans
          ((Algebra.smul_def _ _).trans (mul_one _))
    have hQ : rQ.hom.hom y =
        (show target.{u, v, w} k K A from (R.hom.app i).hom
          (algebraUnit.{u, v, w} k K (P.left.obj i) p)) *
            algebraMap A (target.{u, v, w} k K A) a :=
      CommAlgCat.cotangentWeightZeroLevelIso_tmul.{w, max u v}
        K (target.{u, v, w} k K A) Q₀
        (algebraMap A (target.{u, v, w} k K A) a)
        (algebraUnit.{u, v, w} k K (P.left.obj i) p)
    have hAug : (show target.{u, v, w} k K A from (R.hom.app i).hom
        (algebraUnit.{u, v, w} k K (P.left.obj i) p)) =
        algebraMap A (target.{u, v, w} k K A) ((show A from (P.hom.app i).hom p)) :=
      algebraUnit_augmentation.{u, v, w} k K A P₀ p
    have hproduct : algebraMap A (target.{u, v, w} k K A)
        ((show A from (P.hom.app i).hom p) * a) =
        (show target.{u, v, w} k K A from (R.hom.app i).hom
          (algebraUnit.{u, v, w} k K (P.left.obj i) p)) *
            algebraMap A (target.{u, v, w} k K A) a :=
      (map_mul (algebraMap A (target.{u, v, w} k K A)) _ _).trans
        (congrArg (fun z : target.{u, v, w} k K A =>
          z * algebraMap A (target.{u, v, w} k K A) a) hAug.symm)
    have heApply : e.hom x = rQ.inv.hom (r.hom.hom (f.hom x)) :=
      congrArg (fun g : X ⟶ Y => g.hom x) hcomp
    apply (ModuleCat.mono_iff_injective rQ.hom).mp inferInstance
    exact (congrArg rQ.hom.hom heApply).trans
      ((ModuleCat.hom_inv_apply rQ (r.hom.hom (f.hom x))).trans
        ((congrArg r.hom.hom hf).trans (hr.trans (hproduct.trans hQ.symm))))
  have hg : (G.map e).hom (m ⊗ₜ[target.{u, v, w} k K A] x) =
      (m ⊗ₜ[target.{u, v, w} k K A] y) := by
    change (ModuleCat.tensorHomAt (target.{u, v, w} k K A) (𝟙 M) e).hom
        (m ⊗ₜ[target.{u, v, w} k K A] x) = _
    have hid : (𝟙 M : M ⟶ M).hom m = m := rfl
    exact (ModuleCat.tensorHomAt_tmul (target.{u, v, w} k K A) (𝟙 M) e m x).trans
      (congrArg₂ (fun a : M => fun b : Y => a ⊗ₜ[target.{u, v, w} k K A] b) hid he)
  have hz : z.hom (m ⊗ₜ[target.{u, v, w} k K A] y) =
      ULift.up (((show target.{u, v, w} k K A from (R.hom.app i).hom
        (algebraUnit.{u, v, w} k K (P.left.obj i) p)) *
          algebraMap A (target.{u, v, w} k K A) a) • m) :=
    CommAlgCat.cotangentWeightZeroTensorSimplicialIso_tmul_tmul.{w, max u v, t}
      K (target.{u, v, w} k K A) R M i m
      (algebraMap A (target.{u, v, w} k K A) a)
      (algebraUnit.{u, v, w} k K (P.left.obj i) p)
  let d : (restrictionCoefficientFunctor.{u, v, w, t} k K A M).obj L ⟶ G.obj Y :=
    (coefficientDiagramIso.{u, v, w, t} k K A M 0 P).hom.app i
  have hdiag : d.hom (m ⊗ₜ[A] l) = (m ⊗ₜ[target.{u, v, w} k K A] y) := by
    have hmap : d = c ≫ G.map e :=
      coefficientDiagramIso_hom_app.{u, v, w, t} k K A M 0 P i
    exact (congrArg (fun f : (restrictionCoefficientFunctor.{u, v, w, t} k K A M).obj L ⟶ G.obj Y =>
      f.hom (m ⊗ₜ[A] l)) hmap).trans
      ((congrArg (G.map e).hom hc).trans hg)
  let T := CommAlgCat.cotangentWeightZeroOnResolution.{w, max u v}
    K (target.{u, v, w} k K A) R
  let b : Y ⟶ T.obj i := (higherSimplicialZeroIso.{w, v, u}
    K (target.{u, v, w} k K A) R).hom.app i
  have hb : G.map b = 𝟙 (G.obj Y) := by
    change G.map (𝟙 Y) = 𝟙 (G.obj Y)
    exact G.map_id Y
  have hzero : (zeroCoefficientSimplicialIso.{u, v, w, t} k K A M P).hom.app i = d ≫ z := by
    change d ≫ G.map b ≫ z = d ≫ z
    exact (congrArg (fun f : G.obj Y ⟶ G.obj Y => d ≫ f ≫ z) hb).trans
      (congrArg (fun f => d ≫ f) (Category.id_comp z))
  have hvalue := congrArg
    (fun f : (sourceCoefficientSimplicial.{u, v, w, t} k K A M 0 P).obj i ⟶
        (CommAlgCat.cotangentWeightZeroCoefficientLift.{w, max u v, t}
          K (target.{u, v, w} k K A)).obj M => f.hom (m ⊗ₜ[A] l)) hzero
  refine hvalue.trans ?_
  change z.hom (d.hom (m ⊗ₜ[A] l)) = _
  rw [hdiag, hz]
  rw [algebraUnit_apply, resolution_augmentation_tmul]
  change ULift.up ((algebraMap A (target.{u, v, w} k K A) ((P.hom.app i).hom p) *
    algebraMap A (target.{u, v, w} k K A) a) • m) = _
  rw [map_mul]

/--
The `B`-linear equivalence from a degree of the weight-zero coefficient diagram to
the original module `M`, obtained from the constant-diagram comparison by removing
the universe lift.
-/
def zeroCoefficientLevelLinearEquiv
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A))
    (i : SimplexCategoryᵒᵖ) :
    (sourceCoefficientSimplicial.{u, v, w, t} k K A M 0 P).obj i ≃ₗ[target.{u, v, w} k K A] M :=
  ((zeroCoefficientSimplicialIso.{u, v, w, t} k K A M P).app i).toLinearEquiv.trans ULift.moduleEquiv

/--
The weight-zero level equivalence sends `m ⊗[A] (a ⊗[P_i] p)` to
`(algebraMap A B (ε_i(p) * a)) • m` in the original coefficient carrier.
-/
@[simp]
theorem zeroCoefficientLevelLinearEquiv_tmul
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A))
    (i : SimplexCategoryᵒᵖ) (m : M) (a : A) (p : P.left.obj i) :
    letI : Module A M := Module.compHom M (algebraMap A (target.{u, v, w} k K A))
    letI : Algebra (P.left.obj i) A :=
      CommAlgCat.cotangentAlgebra.{u, max v w} k A ((Over.lift P.left P.hom).obj i)
    let C := (ModuleCat.restrictScalars ((Over.lift P.left P.hom).obj i).hom.hom.toRingHom).obj
      (ModuleCat.of A A)
    letI : Module (P.left.obj i) C := C.isModule
    let D := ModuleCat.of ((Over.lift P.left P.hom).obj i).left ((Over.lift P.left P.hom).obj i).left
    letI : Module (P.left.obj i) D := D.isModule
    zeroCoefficientLevelLinearEquiv.{u, v, w, t} k K A M P i (m ⊗ₜ[A] (a ⊗ₜ[P.left.obj i] p)) =
      (algebraMap A (target.{u, v, w} k K A) ((show A from (P.hom.app i).hom p) * a)) • m := by
  exact congrArg ULift.down (zeroCoefficientSimplicialIso_tmul.{u, v, w, t} k K A M P i m a p)

/--
The normalized weight-zero coefficient diagram is chain homotopy equivalent to the
canonical universe lift of `M` concentrated in degree zero.
-/
def zeroCoefficientNormalizedHomotopyEquiv
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    HomotopyEquiv (sourceCoefficientNormalizedDiagram.{u, v, w, t} k K A M 0 P)
      ((ChainComplex.single₀ (ModuleCat.{max u v w t} (target.{u, v, w} k K A))).obj
        ((CommAlgCat.cotangentWeightZeroCoefficientLift.{w, max u v, t} K (target.{u, v, w} k K A)).obj M)) :=
  (HomotopyEquiv.ofIso
    ((normalizedMooreComplex (ModuleCat.{max u v w t} (target.{u, v, w} k K A))).mapIso
      (zeroCoefficientSimplicialIso.{u, v, w, t} k K A M P))).trans
    (CommAlgCat.cotangentWeightZeroCoefficientHomotopyEquiv.{w, max u v, max u v w t} K (target.{u, v, w} k K A)
      ((CommAlgCat.cotangentWeightZeroCoefficientLift.{w, max u v, t} K (target.{u, v, w} k K A)).obj M))

/--
The isomorphism from degree-zero homology of the normalized weight-zero coefficient
diagram to the canonical universe lift of `M` as a `B`-module.
-/
def zeroCoefficientHomologyIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    (sourceCoefficientNormalizedDiagram.{u, v, w, t} k K A M 0 P).homology 0 ≅
      (CommAlgCat.cotangentWeightZeroCoefficientLift.{w, max u v, t} K (target.{u, v, w} k K A)).obj M :=
  (zeroCoefficientNormalizedHomotopyEquiv.{u, v, w, t} k K A M P).toHomologyIso 0 ≪≫
    (HomologicalComplex.homologyFunctorSingleIso
      (ModuleCat.{max u v w t} (target.{u, v, w} k K A)) (ComplexShape.down ℕ) 0).app
        ((CommAlgCat.cotangentWeightZeroCoefficientLift.{w, max u v, t} K (target.{u, v, w} k K A)).obj M)

/--
The `B`-linear equivalence from degree-zero homology of the normalized weight-zero
coefficient diagram to the original carrier of `M`.
-/
def zeroCoefficientHomologyLinearEquiv
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    (sourceCoefficientNormalizedDiagram.{u, v, w, t} k K A M 0 P).homology 0 ≃ₗ[target.{u, v, w} k K A] M :=
  (zeroCoefficientHomologyIso.{u, v, w, t} k K A M P).toLinearEquiv.trans ULift.moduleEquiv

/--
The normalized weight-zero coefficient diagram has zero homology in every positive
degree `i + 1`, for any augmented diagram and any coefficient module `M`.
-/
theorem zeroCoefficientHomology_isZero_succ
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) (i : ℕ) :
    IsZero ((sourceCoefficientNormalizedDiagram.{u, v, w, t} k K A M 0 P).homology (i + 1)) := by
  have h : IsZero (((ChainComplex.single₀
      (ModuleCat.{max u v w t} (target.{u, v, w} k K A))).obj
        ((CommAlgCat.cotangentWeightZeroCoefficientLift.{w, max u v, t} K (target.{u, v, w} k K A)).obj M)).homology
          (i + 1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact ChainComplex.exactAt_succ_single_obj
      ((CommAlgCat.cotangentWeightZeroCoefficientLift.{w, max u v, t} K (target.{u, v, w} k K A)).obj M) i
  exact h.of_iso ((zeroCoefficientNormalizedHomotopyEquiv.{u, v, w, t} k K A M P).toHomologyIso (i + 1))

end CommAlgCat.CotangentPushout

end
