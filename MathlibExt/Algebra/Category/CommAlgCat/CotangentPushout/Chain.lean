/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentPushout.Simplicial
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Alternating and normalized higher-form scalar-change complexes

Let `k → K` be a morphism of commutative rings, `A` a commutative `k`-algebra, and
`B = K ⊗[k] A`. For each weight `n`, the degreewise higher forms of an augmented
simplicial algebra `P → const A` give both an alternating-face complex and a normalized
Moore complex. The alternating differential is the alternating sum of the face maps.

Scalar extension to `B` identifies the alternating complexes and gives a chain homotopy
equivalence between the scalar-extended normalized complex and the normalized model
of the scalar-changed diagram. The induced homology comparison is natural in augmented
maps and concerns the homology of the scalar-extended complex. In weight zero the
normalized complex is homotopy equivalent to the regular module `A` in degree zero.
The ground-ring, extension-ring, and algebra-carrier universes remain independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial TensorProduct

universe u v w

namespace CommAlgCat.CotangentPushout

variable (k : Type u) (K : Type w) [CommRing k] [CommRing K] [Algebra k K]
  (A : CommAlgCat.{max u v w} k)

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] tensorGroundAlgebra tensorRightAlgebra
attribute [local instance] overGroundAlgebra overRightAlgebra

/--
The alternating-face complex of the degreewise weight-`n` higher forms of an augmented
simplicial algebra over `A`, with differential given by the alternating sum of its faces.
-/
def alternatingFunctor (n : ℕ) :
    Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A) ⥤
      ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  higherSimplicialFunctor.{u, v, w} k A n ⋙ alternatingFaceMapComplex (ModuleCat.{max u v w} A)

/--
The normalized Moore complex of the degreewise weight-`n` higher forms of an augmented
simplicial algebra over `A`.
-/
def normalizedFunctor (n : ℕ) :
    Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A) ⥤
      ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  higherSimplicialFunctor.{u, v, w} k A n ⋙ normalizedMooreComplex (ModuleCat.{max u v w} A)

/--
The functor obtained by extending the scalars of the alternating weight-`n` higher-form
complex from `A` to `B = K ⊗[k] A` in every chain degree.
-/
def mappedAlternatingFunctor (n : ℕ) :
    Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A) ⥤
      ChainComplex (ModuleCat.{max u v w} (target.{u, v, w} k K A)) ℕ :=
  alternatingFunctor.{u, v, w} k A n ⋙ (moduleFunctor.{u, v, w} k K A).mapHomologicalComplex (ComplexShape.down ℕ)

/--
The functor obtained by extending scalars from `A` to `B = K ⊗[k] A` after forming the
normalized weight-`n` higher-form complex.
-/
def mappedNormalizedFunctor (n : ℕ) :
    Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A) ⥤
      ChainComplex (ModuleCat.{max u v w} (target.{u, v, w} k K A)) ℕ :=
  normalizedFunctor.{u, v, w} k A n ⋙ (moduleFunctor.{u, v, w} k K A).mapHomologicalComplex (ComplexShape.down ℕ)

/--
The alternating weight-`n` higher-form complex over `K` of the scalar-changed augmented
algebra `K ⊗[k] P → const (K ⊗[k] A)`.
-/
def targetAlternatingFunctor (n : ℕ) :
    Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A) ⥤
      ChainComplex (ModuleCat.{max u v w} (target.{u, v, w} k K A)) ℕ :=
  resolutionFunctor.{u, v, w} k K A ⋙ alternatingFunctor.{w, v, u} K (target.{u, v, w} k K A) n

/--
The normalized weight-`n` higher-form complex over `K` of the scalar-changed augmented
algebra `K ⊗[k] P → const (K ⊗[k] A)`.
-/
def targetNormalizedFunctor (n : ℕ) :
    Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A) ⥤
      ChainComplex (ModuleCat.{max u v w} (target.{u, v, w} k K A)) ℕ :=
  resolutionFunctor.{u, v, w} k K A ⋙ normalizedFunctor.{w, v, u} K (target.{u, v, w} k K A) n

/--
The isomorphism from scalar extension of the alternating higher-form complex of `P`
to the alternating higher-form complex of its scalar-changed diagram, at weight `n`.
-/
def alternatingIso (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    (mappedAlternatingFunctor.{u, v, w} k K A n).obj P ≅
      (targetAlternatingFunctor.{u, v, w} k K A n).obj P :=
  (alternatingFaceMapComplexCompMapHomologicalComplexIso (moduleFunctor.{u, v, w} k K A)).app
      (higherSimplicial.{u, v, w} k A n P) ≪≫
    (alternatingFaceMapComplex (ModuleCat.{max u v w} (target.{u, v, w} k K A))).mapIso
      (higherSimplicialIso.{u, v, w} k K A n P)

/--
In chain degree `i`, the forward alternating-complex comparison is the degree-`i`
component of the higher-form simplicial comparison.
-/
@[simp]
theorem alternatingIso_hom_f (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) (i : ℕ) :
    (alternatingIso.{u, v, w} k K A n P).hom.f i =
      (higherSimplicialIso.{u, v, w} k K A n P).hom.app (op ⦋i⦌) := by
  let X := higherSimplicial.{u, v, w} k A n P
  let F := moduleFunctor.{u, v, w} k K A
  let e := (alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X
  let m := (alternatingFaceMapComplex (ModuleCat.{max u v w} (target.{u, v, w} k K A))).mapIso
    (higherSimplicialIso.{u, v, w} k K A n P)
  have he : e.hom.f i = 𝟙 _ := rfl
  have hm : m.hom.f i = (higherSimplicialIso.{u, v, w} k K A n P).hom.app (op ⦋i⦌) := rfl
  change (e.hom ≫ m.hom).f i = _
  rw [HomologicalComplex.comp_f, he, hm, Category.id_comp]

/--
The natural isomorphism between the scalar-extended alternating weight-`n` complex
and the alternating complex of the scalar-changed augmented diagram.
-/
def alternatingNatIso (n : ℕ) :
    mappedAlternatingFunctor.{u, v, w} k K A n ≅ targetAlternatingFunctor.{u, v, w} k K A n :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (higherSimplicialFunctor.{u, v, w} k A n)
      (alternatingFaceMapComplexCompMapHomologicalComplexIso (moduleFunctor.{u, v, w} k K A)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (higherSimplicialNatIso.{u, v, w} k K A n)
      (alternatingFaceMapComplex (ModuleCat.{max u v w} (target.{u, v, w} k K A))) ≪≫
    Functor.associator _ _ _

/--
At an augmented diagram `P`, the forward component of `alternatingNatIso` is the
forward map of `alternatingIso`.
-/
theorem alternatingNatIso_hom_app (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    (alternatingNatIso.{u, v, w} k K A n).hom.app P = (alternatingIso.{u, v, w} k K A n P).hom := by
  let X := higherSimplicial.{u, v, w} k A n P
  let F := moduleFunctor.{u, v, w} k K A
  let e := (alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X
  let m := (alternatingFaceMapComplex (ModuleCat.{max u v w} (target.{u, v, w} k K A))).mapIso
    (higherSimplicialIso.{u, v, w} k K A n P)
  change 𝟙 _ ≫ e.hom ≫ 𝟙 _ ≫ m.hom ≫ 𝟙 _ = e.hom ≫ m.hom
  simp only [Category.id_comp, Category.comp_id]

/--
The isomorphism obtained by normalizing the simplicial comparison between the
scalar-extended higher-form diagram of `P` and the higher-form diagram of its scalar
change. Scalar extension here is applied before normalization.
-/
def normalizedDiagramIso (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    (normalizedMooreComplex (ModuleCat.{max u v w} (target.{u, v, w} k K A))).obj
        (higherSimplicial.{u, v, w} k A n P ⋙ moduleFunctor.{u, v, w} k K A) ≅
      (targetNormalizedFunctor.{u, v, w} k K A n).obj P :=
  (normalizedMooreComplex (ModuleCat.{max u v w} (target.{u, v, w} k K A))).mapIso
    (higherSimplicialIso.{u, v, w} k K A n P)

/--
The chain homotopy equivalence between scalar extension of the normalized higher-form
complex and normalization of the scalar-changed higher-form diagram, constructed
through the respective alternating-face complexes.
-/
def normalizedHomotopyEquiv (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    HomotopyEquiv ((mappedNormalizedFunctor.{u, v, w} k K A n).obj P)
      ((targetNormalizedFunctor.{u, v, w} k K A n).obj P) :=
  ((moduleFunctor.{u, v, w} k K A).mapHomotopyEquiv
    (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := higherSimplicial.{u, v, w} k A n P))).trans
    ((HomotopyEquiv.ofIso (alternatingIso.{u, v, w} k K A n P)).trans
      (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
        (Y := higherSimplicial.{w, v, u} K (target.{u, v, w} k K A) n (resolution.{u, v, w} k K A P))).symm)

/--
The forward normalized comparison is the composite of the scalar-extended inclusion
into the alternating complex, the alternating scalar-change isomorphism, and the
projection from the target alternating complex to its normalized Moore complex.
-/
theorem normalizedHomotopyEquiv_hom (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    (normalizedHomotopyEquiv.{u, v, w} k K A n P).hom =
      ((moduleFunctor.{u, v, w} k K A).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (inclusionOfMooreComplexMap (higherSimplicial.{u, v, w} k A n P)) ≫
        (alternatingIso.{u, v, w} k K A n P).hom ≫
          DoldKan.PInftyToNormalizedMooreComplex
            (higherSimplicial.{w, v, u} K (target.{u, v, w} k K A) n (resolution.{u, v, w} k K A P)) := rfl

/--
The natural inclusion from the scalar-extended normalized weight-`n` higher-form
complex to its scalar-extended alternating-face complex.
-/
def sourceNormalization (n : ℕ) :
    mappedNormalizedFunctor.{u, v, w} k K A n ⟶ mappedAlternatingFunctor.{u, v, w} k K A n :=
  whiskerRight
    (whiskerLeft (higherSimplicialFunctor.{u, v, w} k A n)
      (inclusionOfMooreComplex (ModuleCat.{max u v w} A)))
    ((moduleFunctor.{u, v, w} k K A).mapHomologicalComplex (ComplexShape.down ℕ))

/--
The natural inclusion from the normalized weight-`n` higher-form complex of the
scalar-changed diagram to its alternating-face complex.
-/
def targetNormalization (n : ℕ) :
    targetNormalizedFunctor.{u, v, w} k K A n ⟶ targetAlternatingFunctor.{u, v, w} k K A n :=
  whiskerLeft (resolutionFunctor.{u, v, w} k K A)
    (whiskerLeft (higherSimplicialFunctor.{w, v, u} K (target.{u, v, w} k K A) n)
      (inclusionOfMooreComplex (ModuleCat.{max u v w} (target.{u, v, w} k K A))))

/--
The natural isomorphism on homology in degree `i` induced by the normalization
inclusion after scalar extension, at higher-form weight `n`.
-/
def sourceNormalizationHomologyIso (n i : ℕ) :
    mappedNormalizedFunctor.{u, v, w} k K A n ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} (target.{u, v, w} k K A))
          (ComplexShape.down ℕ) i ≅
      mappedAlternatingFunctor.{u, v, w} k K A n ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} (target.{u, v, w} k K A))
          (ComplexShape.down ℕ) i :=
  NatIso.ofComponents
    (fun P => ((moduleFunctor.{u, v, w} k K A).mapHomotopyEquiv
      (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
        (Y := higherSimplicial.{u, v, w} k A n P))).toHomologyIso i)
    (by
      intro P Q f
      exact (whiskerRight (sourceNormalization.{u, v, w} k K A n)
        (HomologicalComplex.homologyFunctor
          (ModuleCat.{max u v w} (target.{u, v, w} k K A)) (ComplexShape.down ℕ) i)).naturality f)

/--
The natural isomorphism on homology in degree `i` between the normalized and
alternating weight-`n` higher-form complexes of the scalar-changed diagram.
-/
def targetNormalizationHomologyIso (n i : ℕ) :
    targetNormalizedFunctor.{u, v, w} k K A n ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} (target.{u, v, w} k K A))
          (ComplexShape.down ℕ) i ≅
      targetAlternatingFunctor.{u, v, w} k K A n ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} (target.{u, v, w} k K A))
          (ComplexShape.down ℕ) i :=
  NatIso.ofComponents
    (fun P => (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := higherSimplicial.{w, v, u} K (target.{u, v, w} k K A) n (resolution.{u, v, w} k K A P))).toHomologyIso i)
    (by
      intro P Q f
      exact (whiskerRight (targetNormalization.{u, v, w} k K A n)
        (HomologicalComplex.homologyFunctor
          (ModuleCat.{max u v w} (target.{u, v, w} k K A)) (ComplexShape.down ℕ) i)).naturality f)

/--
The natural isomorphism in homological degree `i` between the homology of the
scalar-extended normalized weight-`n` complex and that of the normalized scalar-changed
model.
-/
def homologyNatIso (n i : ℕ) :
    mappedNormalizedFunctor.{u, v, w} k K A n ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} (target.{u, v, w} k K A))
          (ComplexShape.down ℕ) i ≅
      targetNormalizedFunctor.{u, v, w} k K A n ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} (target.{u, v, w} k K A))
          (ComplexShape.down ℕ) i :=
  sourceNormalizationHomologyIso.{u, v, w} k K A n i ≪≫
    isoWhiskerRight (alternatingNatIso.{u, v, w} k K A n)
      (HomologicalComplex.homologyFunctor
        (ModuleCat.{max u v w} (target.{u, v, w} k K A)) (ComplexShape.down ℕ) i) ≪≫
    (targetNormalizationHomologyIso.{u, v, w} k K A n i).symm

/--
The component of `homologyNatIso` at `P` is the homology isomorphism induced by
`normalizedHomotopyEquiv` in the same weight and homological degree.
-/
theorem homologyNatIso_app (n i : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    (homologyNatIso.{u, v, w} k K A n i).app P =
      (normalizedHomotopyEquiv.{u, v, w} k K A n P).toHomologyIso i := by
  apply Iso.ext
  let F := moduleFunctor.{u, v, w} k K A
  let X := higherSimplicial.{u, v, w} k A n P
  let Y := higherSimplicial.{w, v, u} K (target.{u, v, w} k K A) n
    (resolution.{u, v, w} k K A P)
  let J := HomologicalComplex.homologyFunctor
    (ModuleCat.{max u v w} (target.{u, v, w} k K A)) (ComplexShape.down ℕ) i
  have hs : (sourceNormalizationHomologyIso.{u, v, w} k K A n i).hom.app P =
      J.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X)) := rfl
  have ht : (targetNormalizationHomologyIso.{u, v, w} k K A n i).inv.app P =
      J.map (DoldKan.PInftyToNormalizedMooreComplex Y) := rfl
  change (sourceNormalizationHomologyIso.{u, v, w} k K A n i).hom.app P ≫
      J.map ((alternatingNatIso.{u, v, w} k K A n).hom.app P) ≫
      (targetNormalizationHomologyIso.{u, v, w} k K A n i).inv.app P =
        J.map (normalizedHomotopyEquiv.{u, v, w} k K A n P).hom
  rw [hs, ht, alternatingNatIso_hom_app, normalizedHomotopyEquiv_hom]
  let sourceI := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X)
  let middle := (alternatingIso.{u, v, w} k K A n P).hom
  let targetP := DoldKan.PInftyToNormalizedMooreComplex Y
  exact ((J.map_comp sourceI (middle ≫ targetP)).trans
    (congrArg (fun z => J.map sourceI ≫ z) (J.map_comp middle targetP))).symm

/--
For an augmented-algebra map `f : P ⟶ Q`, the comparison of normalized higher-form
homology commutes with the two induced homology maps in weight `n` and degree `i`.
-/
@[reassoc]
theorem normalizedHomology_naturality (n i : ℕ)
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)}
    (f : P ⟶ Q) :
    HomologicalComplex.homologyMap ((mappedNormalizedFunctor.{u, v, w} k K A n).map f) i ≫
        ((normalizedHomotopyEquiv.{u, v, w} k K A n Q).toHomologyIso i).hom =
      ((normalizedHomotopyEquiv.{u, v, w} k K A n P).toHomologyIso i).hom ≫
        HomologicalComplex.homologyMap ((targetNormalizedFunctor.{u, v, w} k K A n).map f) i := by
  let J := HomologicalComplex.homologyFunctor
    (ModuleCat.{max u v w} (target.{u, v, w} k K A)) (ComplexShape.down ℕ) i
  have h : J.map ((mappedNormalizedFunctor.{u, v, w} k K A n).map f) ≫
      (homologyNatIso.{u, v, w} k K A n i).hom.app Q =
      (homologyNatIso.{u, v, w} k K A n i).hom.app P ≫
        J.map ((targetNormalizedFunctor.{u, v, w} k K A n).map f) :=
    (homologyNatIso.{u, v, w} k K A n i).hom.naturality f
  have hP : (homologyNatIso.{u, v, w} k K A n i).hom.app P =
      ((normalizedHomotopyEquiv.{u, v, w} k K A n P).toHomologyIso i).hom :=
    congrArg Iso.hom (homologyNatIso_app.{u, v, w} k K A n i P)
  have hQ : (homologyNatIso.{u, v, w} k K A n i).hom.app Q =
      ((normalizedHomotopyEquiv.{u, v, w} k K A n Q).toHomologyIso i).hom :=
    congrArg Iso.hom (homologyNatIso_app.{u, v, w} k K A n i Q)
  rw [hP, hQ] at h
  exact h

/--
The normalized weight-zero higher-form complex of any augmented diagram over `A` is
chain homotopy equivalent to the regular `A`-module concentrated in degree zero.
-/
def zeroNormalizedHomotopyEquiv
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    HomotopyEquiv ((normalizedFunctor.{u, v, w} k A 0).obj P)
      ((ChainComplex.single₀ (ModuleCat.{max u v w} A)).obj (ModuleCat.of A A)) :=
  (HomotopyEquiv.ofIso
    ((normalizedMooreComplex (ModuleCat.{max u v w} A)).mapIso
      (higherSimplicialZeroIso.{u, v, w} k A P ≪≫ cotangentWeightZeroOnResolutionIso.{u, max v w} k A P))).trans
    (CommAlgCat.cotangentWeightZeroCoefficientHomotopyEquiv.{u, max v w, max u v w} k A (ModuleCat.of A A))

/--
The isomorphism from degree-zero homology of the normalized weight-zero higher-form
complex to the regular module `A`.
-/
def zeroNormalizedHomologyIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    ((normalizedFunctor.{u, v, w} k A 0).obj P).homology 0 ≅ ModuleCat.of A A :=
  (zeroNormalizedHomotopyEquiv.{u, v, w} k A P).toHomologyIso 0 ≪≫
    (HomologicalComplex.homologyFunctorSingleIso
      (ModuleCat.{max u v w} A) (ComplexShape.down ℕ) 0).app (ModuleCat.of A A)

/--
For every augmented diagram over `A`, the normalized weight-zero higher-form complex
has zero homology in each positive degree `i + 1`.
-/
theorem zeroNormalizedHomology_isZero_succ
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) (i : ℕ) :
    IsZero (((normalizedFunctor.{u, v, w} k A 0).obj P).homology (i + 1)) := by
  have h : IsZero (((ChainComplex.single₀ (ModuleCat.{max u v w} A)).obj
      (ModuleCat.of A A)).homology (i + 1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact ChainComplex.exactAt_succ_single_obj (ModuleCat.of A A) i
  exact h.of_iso ((zeroNormalizedHomotopyEquiv.{u, v, w} k A P).toHomologyIso (i + 1))

end CommAlgCat.CotangentPushout

end
