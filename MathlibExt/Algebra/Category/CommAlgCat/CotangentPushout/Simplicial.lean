/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentPushout.AlgebraModule
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentPushout.HigherForms
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentSimplicial

/-!
# Simplicial higher-form scalar-change comparison

For commutative rings `k → K`, set `B = K ⊗[k] A`. Scalar extension sends an augmented
simplicial `k`-algebra `P → const A` to an augmented simplicial `K`-algebra over `B`,
with every operator and augmentation component obtained by the corresponding tensor map.

In positive weight `n`, the degreewise form module is
`A ⊗[P] exteriorPower_P^n Ω(P/k)`; weight zero is the regular module `A ⊗[P] P`.
The degreewise scalar-change isomorphisms assemble to a natural isomorphism of these
simplicial higher-form diagrams. Weight one identifies with the cotangent simplicial
diagram. These comparisons are defined for arbitrary augmented diagrams, with the
ring and algebra-carrier universes independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Functor Opposite AlgebraicTopology
open scoped TensorProduct Simplicial

universe u v w

namespace CommAlgCat.CotangentPushout

variable (k : Type u) (K : Type w) [CommRing k] [CommRing K] [Algebra k K]
  (A : CommAlgCat.{max u v w} k)

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] tensorGroundAlgebra tensorRightAlgebra
attribute [local instance] overGroundAlgebra overRightAlgebra

/--
The map of scalar-changed augmented diagrams induced by an augmented-algebra map
`f : P ⟶ Q`, given degreewise by `K ⊗[k] f`.
-/
def resolutionMap
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)}
    (f : P ⟶ Q) : resolution.{u, v, w} k K A P ⟶ resolution.{u, v, w} k K A Q :=
  Over.homMk (whiskerRight f.left (algebraFunctor.{u, v, w} k K)) (by
    apply NatTrans.ext
    funext i
    change (algebraFunctor.{u, v, w} k K).map (f.left.app i) ≫
        (algebraFunctor.{u, v, w} k K).map (Q.hom.app i) =
      (algebraFunctor.{u, v, w} k K).map (P.hom.app i)
    let F := algebraFunctor.{u, v, w} k K
    have hw : f.left.app i ≫ Q.hom.app i = P.hom.app i := by
      simpa only [NatTrans.comp_app] using NatTrans.congr_app f.w i
    exact (F.map_comp (f.left.app i) (Q.hom.app i)).symm.trans
      (congrArg (fun a : P.left.obj i ⟶ A => F.map a) hw))

/--
Scalar change of the identity of an augmented diagram `P` is the identity of its
scalar-changed diagram.
-/
@[simp]
theorem resolutionMap_id
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    resolutionMap.{u, v, w} k K A (𝟙 P) = 𝟙 (resolution.{u, v, w} k K A P) := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext i
  change (algebraFunctor.{u, v, w} k K).map (𝟙 (P.left.obj i)) =
    𝟙 ((algebraFunctor.{u, v, w} k K).obj (P.left.obj i))
  exact (algebraFunctor.{u, v, w} k K).map_id (P.left.obj i)

/--
For augmented-algebra maps `f : P ⟶ Q` and `g : Q ⟶ T`, scalar change of `f ≫ g`
is the composite of their scalar-changed maps.
-/
theorem resolutionMap_comp
    {P Q T : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)}
    (f : P ⟶ Q) (g : Q ⟶ T) :
    resolutionMap.{u, v, w} k K A (f ≫ g) =
      resolutionMap.{u, v, w} k K A f ≫ resolutionMap.{u, v, w} k K A g := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext i
  change (algebraFunctor.{u, v, w} k K).map (f.left.app i ≫ g.left.app i) =
    (algebraFunctor.{u, v, w} k K).map (f.left.app i) ≫
      (algebraFunctor.{u, v, w} k K).map (g.left.app i)
  exact (algebraFunctor.{u, v, w} k K).map_comp (f.left.app i) (g.left.app i)

/--
The functor from augmented simplicial `k`-algebras over `A` to augmented simplicial
`K`-algebras over `K ⊗[k] A`, obtained by tensoring each diagram and augmentation.
-/
def resolutionFunctor :
    Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A) ⥤
      Over ((SimplicialObject.const (CommAlgCat.{max u v w} K)).obj (target.{u, v, w} k K A)) where
  obj := resolution.{u, v, w} k K A
  map := resolutionMap.{u, v, w} k K A
  map_id := resolutionMap_id.{u, v, w} k K A
  map_comp := resolutionMap_comp.{u, v, w} k K A

/--
A simplicial operator of the scalar-changed diagram sends `x ⊗[k] p` to
`x ⊗[k] P(θ)(p)`, preserving the extension-ring factor.
-/
@[simp]
theorem resolution_map_tmul
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A))
    {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) (x : K) (p : P.left.obj i) :
    ((resolution.{u, v, w} k K A P).left.map θ).hom (x ⊗ₜ[k] p) =
      x ⊗ₜ[k] (P.left.map θ).hom p :=
  algebraFunctor_map_tmul.{u, v, w} k K (P.left.map θ) x p

/--
The degree-`i` scalar-changed augmentation sends `x ⊗[k] p` to
`x ⊗[k] ε_i(p)` in `K ⊗[k] A`.
-/
@[simp]
theorem resolution_augmentation_tmul
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A))
    (i : SimplexCategoryᵒᵖ) (x : K) (p : P.left.obj i) :
    ((resolution.{u, v, w} k K A P).hom.app i).hom (x ⊗ₜ[k] p) =
      x ⊗ₜ[k] (P.hom.app i).hom p :=
  algebraFunctor_map_tmul.{u, v, w} k K (P.hom.app i) x p

/--
For `f : P ⟶ Q`, its scalar-changed degree-`i` map sends `x ⊗[k] p` to
`x ⊗[k] f_i(p)`.
-/
@[simp]
theorem resolutionMap_tmul
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)}
    (f : P ⟶ Q) (i : SimplexCategoryᵒᵖ) (x : K) (p : P.left.obj i) :
    ((resolutionMap.{u, v, w} k K A f).left.app i).hom (x ⊗ₜ[k] p) =
      x ⊗ₜ[k] (f.left.app i).hom p :=
  algebraFunctor_map_tmul.{u, v, w} k K (f.left.app i) x p

/--
The simplicial `A`-module obtained by applying the weight-`n` higher-form functor
to every degree of the augmented algebra `P → const A`. Positive weights use exterior
powers of Kähler differentials; weight zero uses the regular coefficient module.
-/
def higherSimplicial (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    SimplicialObject (ModuleCat.{max u v w} A) :=
  Over.lift P.left P.hom ⋙ cotangentHigherFunctor.{u, max v w} k A n

/--
The map between weight-`n` higher-form diagrams induced degreewise by an
augmented-algebra map `f : P ⟶ Q`.
-/
def higherSimplicialMap (n : ℕ)
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)}
    (f : P ⟶ Q) : higherSimplicial.{u, v, w} k A n P ⟶ higherSimplicial.{u, v, w} k A n Q :=
  Functor.whiskerRight (Over.liftDiagramMap A f) (cotangentHigherFunctor.{u, max v w} k A n)

/--
The higher-form map induced by the identity of `P` is the identity of its weight-`n`
simplicial higher-form diagram.
-/
@[simp]
theorem higherSimplicialMap_id (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    higherSimplicialMap.{u, v, w} k A n (𝟙 P) = 𝟙 (higherSimplicial.{u, v, w} k A n P) := by
  simpa only [higherSimplicialMap, Over.liftDiagramMap_id, higherSimplicial] using
    Functor.whiskerRight_id' (G := Over.lift P.left P.hom) (cotangentHigherFunctor.{u, max v w} k A n)

/--
The higher-form map induced by `f ≫ g` is the composite of the higher-form maps
induced by `f` and `g`, in the same weight.
-/
theorem higherSimplicialMap_comp (n : ℕ)
    {P Q T : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)}
    (f : P ⟶ Q) (g : Q ⟶ T) :
    higherSimplicialMap.{u, v, w} k A n (f ≫ g) =
      higherSimplicialMap.{u, v, w} k A n f ≫ higherSimplicialMap.{u, v, w} k A n g := by
  simp only [higherSimplicialMap, Over.liftDiagramMap_comp, Functor.whiskerRight_comp]
  rfl

/--
The functor sending an augmented simplicial algebra over `A` to its degreewise
weight-`n` higher-form diagram and augmented maps to their induced higher-form maps.
-/
def higherSimplicialFunctor (n : ℕ) :
    Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A) ⥤
      SimplicialObject (ModuleCat.{max u v w} A) where
  obj := higherSimplicial.{u, v, w} k A n
  map := higherSimplicialMap.{u, v, w} k A n
  map_id := higherSimplicialMap_id.{u, v, w} k A n
  map_comp := higherSimplicialMap_comp.{u, v, w} k A n

/--
In weight `n + 1`, a simplicial operator sends
`a ⊗ (d p₀ ∧ ⋯ ∧ d pₙ)` to `a ⊗ (d P(θ)(p₀) ∧ ⋯ ∧ d P(θ)(pₙ))`.
-/
@[simp]
theorem higherSimplicial_map_tensor (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A))
    {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j)
    (a : A) (p : Fin (n + 1) → P.left.obj i) :
    ((higherSimplicial.{u, v, w} k A (n + 1) P).map θ).hom
        (cotangentHigherTensor.{u, max v w} k A n (Over.mk (P.hom.app i)) a p) =
      cotangentHigherTensor.{u, max v w} k A n (Over.mk (P.hom.app j)) a
        (fun l => (P.left.map θ).hom (p l)) :=
  cotangentHigherMap_tensor.{u, max v w} k A n ((Over.lift P.left P.hom).map θ) a p

/--
The isomorphism between the weight-zero higher-form diagram and the regular
coefficient-module diagram of the same augmented algebra.
-/
def higherSimplicialZeroIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    higherSimplicial.{u, v, w} k A 0 P ≅ cotangentWeightZeroOnResolution.{u, max v w} k A P :=
  NatIso.ofComponents (fun i => Iso.refl _) (by
    intro i j θ
    change cotangentHigherMap.{u, max v w} k A 0 ((Over.lift P.left P.hom).map θ) =
      cotangentWeightZeroTransport.{u, max v w} k A ((Over.lift P.left P.hom).map θ)
    exact cotangentHigherMap_zero_eq_weightZero.{u, max v w} k A ((Over.lift P.left P.hom).map θ))

/--
The simplicial isomorphism from the weight-one higher-form diagram to the ordinary
cotangent simplicial diagram.
-/
def higherSimplicialOneIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    higherSimplicial.{u, v, w} k A 1 P ≅ CommAlgCat.cotangentSimplicial.{u, max v w} k A P :=
  isoWhiskerLeft (Over.lift P.left P.hom) (cotangentHigherOneNatIso.{u, max v w} k A)

/--
The simplicial isomorphism between scalar extension of the weight-`n` higher-form
diagram of `P` and the weight-`n` higher-form diagram of its scalar-changed augmentation.
-/
def higherSimplicialIso (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    higherSimplicial.{u, v, w} k A n P ⋙ moduleFunctor.{u, v, w} k K A ≅
      higherSimplicial.{w, v, u} K (target.{u, v, w} k K A) n (resolution.{u, v, w} k K A P) :=
  NatIso.ofComponents
    (fun i => higherIso.{u, v, w} k K A n ((Over.lift P.left P.hom).obj i))
    (by
      intro i j θ
      exact (higherNatIso.{u, v, w} k K A n).hom.naturality ((Over.lift P.left P.hom).map θ))

/--
In weight `n + 1`, the comparison sends
`b ⊗[A] (a ⊗ (d p₀ ∧ ⋯ ∧ d pₙ))` to
`(b * algebraMap A B a) ⊗ (d (1 ⊗ p₀) ∧ ⋯ ∧ d (1 ⊗ pₙ))`, where `B = K ⊗[k] A`.
-/
@[simp]
theorem higherSimplicialIso_tensor (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A))
    (i : SimplexCategoryᵒᵖ) (b : target.{u, v, w} k K A) (a : A)
    (p : Fin (n + 1) → P.left.obj i) :
    ((higherSimplicialIso.{u, v, w} k K A (n + 1) P).hom.app i).hom
        (b ⊗ₜ[A] cotangentHigherTensor.{u, max v w} k A n (Over.mk (P.hom.app i)) a p) =
      cotangentHigherTensor.{w, max u v} K (target.{u, v, w} k K A) n
        (Over.mk ((resolution.{u, v, w} k K A P).hom.app i))
        (b * algebraMap A (target.{u, v, w} k K A) a)
        (fun l => algebraUnit.{u, v, w} k K (P.left.obj i) (p l)) :=
  higherIso_tensor.{u, v, w} k K A n ((Over.lift P.left P.hom).obj i) b a p

/--
In simplicial degree `i`, the weight-zero comparison sends `b ⊗[A] (a ⊗[P_i] p)`
to `(b * algebraMap A B a) ⊗[K ⊗[k] P_i] (1 ⊗[k] p)`.
-/
@[simp]
theorem higherSimplicialIso_zero_tmul
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A))
    (i : SimplexCategoryᵒᵖ) (b : target.{u, v, w} k K A) (a : A) (p : P.left.obj i) :
    letI : Algebra (P.left.obj i) A :=
      CommAlgCat.cotangentAlgebra.{u, max v w} k A ((Over.lift P.left P.hom).obj i)
    letI : Algebra ((resolution.{u, v, w} k K A P).left.obj i) (target.{u, v, w} k K A) :=
      CommAlgCat.cotangentAlgebra.{w, max u v} K (target.{u, v, w} k K A)
        ((Over.lift (resolution.{u, v, w} k K A P).left (resolution.{u, v, w} k K A P).hom).obj i)
    let C := (ModuleCat.restrictScalars ((Over.lift P.left P.hom).obj i).hom.hom.toRingHom).obj
      (ModuleCat.of A A)
    letI : Module (P.left.obj i) C := C.isModule
    let D := ModuleCat.of ((Over.lift P.left P.hom).obj i).left ((Over.lift P.left P.hom).obj i).left
    letI : Module (P.left.obj i) D := D.isModule
    letI : Algebra ((resolution.{u, v, w} k K A P).left.obj i)
        ((algebraFunctor.{u, v, w} k K).obj (P.left.obj i)) :=
      Algebra.id ((resolution.{u, v, w} k K A P).left.obj i)
    ((higherSimplicialIso.{u, v, w} k K A 0 P).hom.app i).hom
        (b ⊗ₜ[A] (a ⊗ₜ[P.left.obj i] p)) =
      (b * algebraMap A (target.{u, v, w} k K A) a) ⊗ₜ[(resolution.{u, v, w} k K A P).left.obj i]
        algebraUnit.{u, v, w} k K (P.left.obj i) p :=
  zeroIso_tmul.{u, v, w} k K A ((Over.lift P.left P.hom).obj i) b a p

/--
For an augmented-algebra map `f : P ⟶ Q`, scalar extension of its higher-form map
commutes with the higher-form comparison and the map induced by the scalar change of `f`.
-/
@[reassoc]
theorem higherSimplicialIso_naturality (n : ℕ)
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)}
    (f : P ⟶ Q) :
    whiskerRight (higherSimplicialMap.{u, v, w} k A n f) (moduleFunctor.{u, v, w} k K A) ≫
        (higherSimplicialIso.{u, v, w} k K A n Q).hom =
      (higherSimplicialIso.{u, v, w} k K A n P).hom ≫
        higherSimplicialMap.{w, v, u} K (target.{u, v, w} k K A) n
          (resolutionMap.{u, v, w} k K A f) := by
  apply NatTrans.ext
  funext i
  let a : (Over.lift P.left P.hom).obj i ⟶ (Over.lift Q.left Q.hom).obj i :=
    (Over.liftDiagramMap A f).app i
  exact (higherNatIso.{u, v, w} k K A n).hom.naturality a

/--
The natural isomorphism, in augmented simplicial algebras, between extending the
scalars of the weight-`n` higher-form diagram and taking the higher forms after algebra
scalar change.
-/
def higherSimplicialNatIso (n : ℕ) :
    higherSimplicialFunctor.{u, v, w} k A n ⋙
        (SimplicialObject.whiskering (ModuleCat.{max u v w} A)
          (ModuleCat.{max u v w} (target.{u, v, w} k K A))).obj (moduleFunctor.{u, v, w} k K A) ≅
      resolutionFunctor.{u, v, w} k K A ⋙
        higherSimplicialFunctor.{w, v, u} K (target.{u, v, w} k K A) n :=
  NatIso.ofComponents (higherSimplicialIso.{u, v, w} k K A n)
    (higherSimplicialIso_naturality.{u, v, w} k K A n)

end CommAlgCat.CotangentPushout

end
