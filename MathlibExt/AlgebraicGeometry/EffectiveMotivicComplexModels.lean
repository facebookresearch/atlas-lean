/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NisnevichTransferModels
public import MathlibExt.AlgebraicGeometry.MotivicStandardSchemes
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.TruncLE
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Source-normalized Tate cycle complexes and motivic hypercohomology

The reduced torus presheaf is the actual cokernel of all unit-coordinate
insertions. Suslin singular terms are the actual presheaves on U×Delta^n,
with maps fixed by the algebraic-simplex ordinal maps. The cycle complex
uses the native alternating-face complex and negative-index extension.
Z(q) is C_* Z_tr(G_m^wedge q)[-q]; negative weights are zero.

Coefficient complexes have the actual sheafified tensor terms and
differential. Motivic cohomology is an independent native derived Hom
from the free Nisnevich representable. It is not defined by a proposed
A1 representability comparison.

Sources: Mazza--Voevodsky--Weibel, Definitions 2.12--2.14 and 3.1;
Voevodsky, arXiv:math/0107109v1, §2 pp.3--6.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EffectiveMotivicComplexModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open FiniteTransferCycleModels FiniteTransferProductModels
open NisnevichTransferModels MotivicStandardSchemes
open CochainComplex.HomComplex
open scoped Simplicial ZeroObject

variable {k : Type} [Field k]
variable (D : CompositionSystem k) (G : GraphSystem k)
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
variable (P : SmoothProductSystem k) (E : ExternalSystem P)
  (C : CorrespondenceProductModel D G P E) (A : StandardSchemes P)
  (R : RepresentableSystem D G)

def reducedTorusPresheaf : ℕ → TransferPresheaves D G
  | 0 => (R.functor.obj ⟨A.torus 0⟩).obj
  | n + 1 => cokernel (Sigma.desc (fun i : Fin (n + 1) =>
      (R.functor.map (show (⟨A.torus n⟩ : CorrespondenceObject D G) ⟶ ⟨A.torus (n + 1)⟩ from
        graphCycle G (A.unitInsertion n i))).hom))

def affineQuotientPresheaf (q : ℕ) : TransferPresheaves D G :=
  cokernel (R.functor.map (show (⟨A.complement q⟩ : CorrespondenceObject D G) ⟶ ⟨A.affine q⟩ from
    graphCycle G (A.complementInclusion q))).hom

/-- The reduced presheaf is required to retain its actual cokernel and transfer maps. -/
structure ReducedTorusModel (q : ℕ) where
  object : AdditiveTransferPresheaves D G
  iso : object.obj ≅ reducedTorusPresheaf (D := D) (G := G) (P := P) (A := A) (R := R) q

/-- Singular terms and all simplex maps are fixed by the genuine product and ordinal functors. -/
structure SingularModel (F : AdditiveTransferPresheaves D G) where
  object : SimplexCategoryᵒᵖ ⥤ AdditiveTransferPresheaves D G
  degreeIso : ∀ n : SimplexCategoryᵒᵖ,
    (object.obj n).obj ≅ ((C.tensor.obj ⟨A.simplex.obj n.unop⟩).op ⋙ F.obj)
  map_eq : ∀ {n m : SimplexCategoryᵒᵖ} (a : n ⟶ m),
    (degreeIso n).inv ≫ (object.map a).hom ≫ (degreeIso m).hom =
      Functor.whiskerRight
        (NatTrans.op (C.tensor.map (show (⟨A.simplex.obj m.unop⟩ : CorrespondenceObject D G) ⟶
          ⟨A.simplex.obj n.unop⟩ from graphCycle G (A.simplex.map a.unop)))) F.obj

/-- The embedding of complex shapes `n ↦ -n` from `ComplexShape.down ℕ` to `ComplexShape.up ℤ`
(`ComplexShape.embeddingUpIntLE 0`): it places a chain complex indexed by `ℕ` in nonpositive
cohomological degrees. -/
abbrev negativeEmbedding : ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.up ℤ) :=
  ComplexShape.embeddingUpIntLE 0

variable [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  (S : TransferSheafificationModel D G)

/-- All raw Tate complexes use the actual reduced cycle presheaf and its singular construction. -/
structure CycleComplexSystem where
  reduced : ∀ q : ℕ, ReducedTorusModel (D := D) (G := G) (P := P) (A := A) (R := R) q
  singular : ∀ q : ℕ, SingularModel (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (reduced q).object

def singularNis (T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (R := R)) (q : ℕ) :
    SimplicialObject (NisModules (k := k)) :=
  (T.singular q).object ⋙ S.functor ⋙ forgetNisnevich D G

def naturalTateComplex (T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (R := R)) (q : ℕ) :
    CochainComplex (NisModules (k := k)) ℤ :=
  ((negativeEmbedding.extendFunctor (NisModules (k := k))).obj
    ((AlgebraicTopology.alternatingFaceMapComplex (NisModules (k := k))).obj
      (singularNis (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (R := R) (S := S) T q)))⟦-(q : ℤ)⟧

def tateComplex (T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (R := R)) (q : ℤ) :
    CochainComplex (NisModules (k := k)) ℤ :=
  if 0 ≤ q then naturalTateComplex (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (R := R) (S := S) T q.toNat else 0

/-- The tensor uses actual pointwise module tensor groups and native sheafification.
All presheaf arrows and all tensor-map components are fixed on pure tensors. -/
structure NisTensorSystem (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] where
  functor : NisModules (k := k) ⥤ NisModules (k := k) ⥤ NisModules (k := k)
  presheaf : ∀ F H : NisModules (k := k), (SmoothScheme k)ᵒᵖ ⥤ ModuleCat.{1} ℤ
  termIso : ∀ (F H : NisModules (k := k)) (U : (SmoothScheme k)ᵒᵖ),
    (presheaf F H).obj U ≅ ModuleCat.of ℤ (TensorProduct ℤ (F.obj.obj U) (H.obj.obj U))
  presheaf_action : ∀ (F H : NisModules (k := k)) (U V : (SmoothScheme k)ᵒᵖ) (a : U ⟶ V)
    (x : F.obj.obj U) (y : H.obj.obj U),
    (termIso F H V).hom ((presheaf F H).map a ((termIso F H U).inv (TensorProduct.tmul ℤ x y))) =
      TensorProduct.tmul ℤ ((F.obj.map a) x) ((H.obj.map a) y)
  rawMap : ∀ (F F' H H' : NisModules (k := k)) (f : F ⟶ F') (h : H ⟶ H'),
    presheaf F H ⟶ presheaf F' H'
  rawMap_eq : ∀ (F F' H H' : NisModules (k := k)) (f : F ⟶ F') (h : H ⟶ H')
    (U : (SmoothScheme k)ᵒᵖ) (x : F.obj.obj U) (y : H.obj.obj U),
    (termIso F' H' U).hom ((rawMap F F' H H' f h).app U
      ((termIso F H U).inv (TensorProduct.tmul ℤ x y))) =
        TensorProduct.tmul ℤ ((f.hom.app U) x) ((h.hom.app U) y)
  objectIso : ∀ F H : NisModules (k := k),
    (functor.obj F).obj H ≅
      (presheafToSheaf (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)).obj (presheaf F H)
  map_eq : ∀ (F F' H H' : NisModules (k := k)) (f : F ⟶ F') (h : H ⟶ H'),
    ((functor.map f).app H ≫ (functor.obj F').map h) ≫ (objectIso F' H').hom =
      (objectIso F H).hom ≫
        (presheafToSheaf (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)).map (rawMap F F' H H' f h)

def constantCoefficient (B : ModuleCat.{1} ℤ) : NisModules (k := k) :=
  (constantSheaf (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)).obj B

/-- Coefficient tensoring is normalized in every term, differential and coefficient map. -/
structure CoefficientComplexSystem (T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (R := R)) (N : NisTensorSystem k) where
  weightFunctor : ∀ _q : ℤ, ModuleCat.{1} ℤ ⥤ CochainComplex (NisModules (k := k)) ℤ
  termIso : ∀ (B : ModuleCat.{1} ℤ) (q n : ℤ),
    ((weightFunctor q).obj B).X n ≅
      (N.functor.obj ((tateComplex (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (R := R) (S := S) T q).X n)).obj (constantCoefficient B)
  differential_eq : ∀ (B : ModuleCat.{1} ℤ) (q n : ℤ),
    ((weightFunctor q).obj B).d n (n + 1) ≫ (termIso B q (n + 1)).hom =
      (termIso B q n).hom ≫
        (N.functor.map ((tateComplex (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (R := R) (S := S) T q).d n (n + 1))).app (constantCoefficient B)
  coefficient_eq : ∀ (B B' : ModuleCat.{1} ℤ) (f : B ⟶ B') (q n : ℤ),
    ((weightFunctor q).map f).f n ≫ (termIso B' q n).hom =
      (termIso B q n).hom ≫
        (N.functor.obj ((tateComplex (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (R := R) (S := S) T q).X n)).map
          ((constantSheaf (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)).map f)

def freeNisRepresentableFunctor : SmoothScheme k ⥤ NisModules (k := k) :=
  yoneda ⋙ (Functor.whiskeringRight (SmoothScheme k)ᵒᵖ (Type 0) (ModuleCat.{1} ℤ)).obj
    (ModuleCat.free ℤ ⋙ ModuleCat.uliftFunctor.{1} ℤ) ⋙
      presheafToSheaf (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)

attribute [local instance] HasDerivedCategory.standard

/-- Motivic cohomology is native Nisnevich hypercohomology of the actual coefficient complex. -/
abbrev MotivicCohomology {T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (R := R)} {N : NisTensorSystem k}
    (B : CoefficientComplexSystem (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (R := R) (S := S) T N) (U : SmoothScheme k)
    (p q : ℤ) (V : ModuleCat.{1} ℤ) :=
  ((DerivedCategory.singleFunctor (NisModules (k := k)) 0).obj
    ((freeNisRepresentableFunctor (k := k)).obj U)) ⟶
      (DerivedCategory.Q.obj ((B.weightFunctor q).obj V))⟦p⟧

end MathlibExt.AlgebraicGeometry.EffectiveMotivicComplexModels
