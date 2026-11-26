/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.DoldKan.FunctorHomology
public import MathlibExt.AlgebraicTopology.SimplicialObject.RightExtraDegeneracyHomotopy
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Functor.Const

/-!
# Normalized augmentations and additive transport

Let P be an augmented simplicial object in an abelian category C, with point A and simplicial
augmentation P.left → const(A). Its normalized complex is N(P.left), and the chain
augmentation ε_P : N(P.left) → A[0] is Moore inclusion followed by the alternating-complex
augmentation.

This map is natural in augmented morphisms and factors through N(const(A)) by normalization of
the simplicial augmentation. The constant-point augmentation is a quasi-isomorphism, using its
extra degeneracy. Hence a quasi-isomorphism ε_P implies that the normalized map to const(A) is
a quasi-isomorphism as well.

For additive F : C ⥤ D between abelian categories, applying F to the augmented diagram uses
the canonical constant comparison const(A) ⋙ F ≅ const(F(A)). If F preserves homology, a
quasi-isomorphism of the given normalized augmentation is preserved. Source and target
category worlds are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe uC vC uD vD

namespace AlgebraicTopology.NormalizedAugmentation

variable {C : Type uC} [Category.{vC} C] [Abelian C]

/-- Normalized complex of an augmented simplicial object.

For augmented P in an abelian category, complex P is the normalized Moore chain complex
N(P.left), indexed by ℕ. -/
abbrev complex (P : SimplicialObject.Augmented C) : ChainComplex C ℕ :=
  (normalizedMooreComplex C).obj P.left

/-- Chain augmentation of a normalized simplicial complex.

For augmented P with point A, define ε_P : N(P.left) → A[0] as the Moore inclusion N(P.left) →
A(P.left) followed by the alternating face-map augmentation to the chain complex concentrated
in degree zero at A. -/
def augmentation (P : SimplicialObject.Augmented C) :
    complex P ⟶ (ChainComplex.single₀ C).obj P.right :=
  inclusionOfMooreComplexMap P.left ≫ AlternatingFaceMapComplex.ε.app P

/-- Augmented map to the constant augmentation point.

For augmented P, its simplicial augmentation P.hom and identity on P.right define a morphism P
→ const(P.right) of augmented simplicial objects. -/
def toConstant (P : SimplicialObject.Augmented C) :
    P ⟶ (SimplicialObject.Augmented.const (C := C)).obj P.right where
  left := P.hom
  right := 𝟙 P.right
  w := by
    change P.hom ≫ 𝟙 ((SimplicialObject.const C).obj P.right) =
      P.hom ≫ (SimplicialObject.const C).map (𝟙 P.right)
    exact (congrArg (fun a => P.hom ≫ a) ((SimplicialObject.const C).map_id P.right)).symm

/-- Normalized chain map of a simplicial augmentation.

For augmented P with point A, apply the Moore normalization functor to P.hom : P.left →
const(A). This gives N(P.left) → N(const(A)). -/
def normalizationMap (P : SimplicialObject.Augmented C) :
    complex P ⟶ complex ((SimplicialObject.Augmented.const (C := C)).obj P.right) :=
  (normalizedMooreComplex C).map P.hom

/-- Naturality of normalized chain augmentations.

For an augmented morphism f : P → Q in an abelian category, N(f.left) ≫ ε_Q = ε_P ≫ (single₀
C).map(f.right). This retains the full simplicial and point components of f. -/
@[reassoc]
theorem augmentation_naturality {P Q : SimplicialObject.Augmented C} (f : P ⟶ Q) :
    (normalizedMooreComplex C).map f.left ≫ augmentation Q =
      augmentation P ≫ (ChainComplex.single₀ C).map f.right := by
  have hI : (normalizedMooreComplex C).map f.left ≫ inclusionOfMooreComplexMap Q.left =
      inclusionOfMooreComplexMap P.left ≫ (alternatingFaceMapComplex C).map f.left :=
    (inclusionOfMooreComplex C).naturality f.left
  have hE : (alternatingFaceMapComplex C).map f.left ≫ AlternatingFaceMapComplex.ε.app Q =
      AlternatingFaceMapComplex.ε.app P ≫ (ChainComplex.single₀ C).map f.right :=
    AlternatingFaceMapComplex.ε.naturality f
  change (normalizedMooreComplex C).map f.left ≫
      (inclusionOfMooreComplexMap Q.left ≫ AlternatingFaceMapComplex.ε.app Q) =
    (inclusionOfMooreComplexMap P.left ≫ AlternatingFaceMapComplex.ε.app P) ≫
      (ChainComplex.single₀ C).map f.right
  calc
    _ = ((normalizedMooreComplex C).map f.left ≫ inclusionOfMooreComplexMap Q.left) ≫
        AlternatingFaceMapComplex.ε.app Q := (Category.assoc _ _ _).symm
    _ = (inclusionOfMooreComplexMap P.left ≫ (alternatingFaceMapComplex C).map f.left) ≫
        AlternatingFaceMapComplex.ε.app Q := congrArg (fun a => a ≫ _) hI
    _ = inclusionOfMooreComplexMap P.left ≫
        ((alternatingFaceMapComplex C).map f.left ≫ AlternatingFaceMapComplex.ε.app Q) :=
      Category.assoc _ _ _
    _ = inclusionOfMooreComplexMap P.left ≫
        (AlternatingFaceMapComplex.ε.app P ≫ (ChainComplex.single₀ C).map f.right) :=
      congrArg (fun a => inclusionOfMooreComplexMap P.left ≫ a) hE
    _ = _ := (Category.assoc _ _ _).symm

/-- Factorization through the normalized constant point.

For augmented P with point A, normalizationMap P followed by the normalized augmentation of
const(A) equals ε_P. This follows by naturality for the augmented map P → const(A) with
identity point map. -/
theorem factorization (P : SimplicialObject.Augmented C) :
    normalizationMap P ≫ augmentation ((SimplicialObject.Augmented.const (C := C)).obj P.right) =
      augmentation P := by
  have h : normalizationMap P ≫
      augmentation ((SimplicialObject.Augmented.const (C := C)).obj P.right) =
        augmentation P ≫ (ChainComplex.single₀ C).map (𝟙 P.right) :=
    augmentation_naturality (toConstant P)
  exact h.trans
    ((congrArg (fun a => augmentation P ≫ a) ((ChainComplex.single₀ C).map_id P.right)).trans
      (Category.comp_id _))

/-- Quasi-isomorphism of a normalized constant augmentation.

For an object M of an abelian category, the augmentation N(const(M)) → M[0] is a
quasi-isomorphism. The constant extra degeneracy supplies its homotopy equivalence through the
alternating complex. -/
theorem constant_quasiIso (M : C) :
    QuasiIso (augmentation ((SimplicialObject.Augmented.const (C := C)).obj M)) :=
  ((DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
    (Y := (SimplicialObject.const C).obj M)).trans
      (SimplicialObject.Augmented.ExtraDegeneracy.const M).homotopyEquiv).quasiIso_hom

/-- Quasi-isomorphism of normalization to the point from an augmentation quasi-isomorphism.

If ε_P : N(P.left) → P.right[0] is a quasi-isomorphism, then normalizationMap P : N(P.left) →
N(const(P.right)) is a quasi-isomorphism. Its composite with the constant augmentation is ε_P,
and the constant augmentation is itself a quasi-isomorphism. -/
theorem normalizationMap_quasiIso (P : SimplicialObject.Augmented C)
    (hP : QuasiIso (augmentation P)) : QuasiIso (normalizationMap P) := by
  let _ : QuasiIso (augmentation ((SimplicialObject.Augmented.const (C := C)).obj P.right)) :=
    constant_quasiIso P.right
  let _ : QuasiIso
      (normalizationMap P ≫ augmentation ((SimplicialObject.Augmented.const (C := C)).obj P.right)) := by
    rw [factorization]
    exact hP
  exact quasiIso_of_comp_right (normalizationMap P)
    (augmentation ((SimplicialObject.Augmented.const (C := C)).obj P.right))

/-- Augmentation quasi-isomorphism transported by an augmented isomorphism.

For an isomorphism P ≅ Q of augmented simplicial objects in an abelian category, a
quasi-isomorphism ε_P implies a quasi-isomorphism ε_Q. The normalized diagram map and the
degree-zero point map induced by the isomorphism are invertible. -/
theorem augmentation_quasiIso_of_iso {P Q : SimplicialObject.Augmented C}
    (e : P ≅ Q) (hP : QuasiIso (augmentation P)) : QuasiIso (augmentation Q) := by
  let _ : QuasiIso (augmentation P) := hP
  let _ : QuasiIso ((normalizedMooreComplex C).map e.hom.left) := inferInstance
  let _ : QuasiIso ((ChainComplex.single₀ C).map e.hom.right) := inferInstance
  let _ : QuasiIso ((normalizedMooreComplex C).map e.hom.left ≫ augmentation Q) := by
    rw [augmentation_naturality]
    infer_instance
  exact quasiIso_of_comp_left ((normalizedMooreComplex C).map e.hom.left) (augmentation Q)

variable {D : Type uD} [Category.{vD} D] [Abelian D] (F : C ⥤ D) [F.Additive]

/-- Augmented simplicial diagram after applying a functor.

For a functor F : C ⥤ D and augmented P in C, apply F to its diagram and point, using the
canonical comparison of a transported constant diagram with the constant diagram on
F(P.right). -/
abbrev mapped (P : SimplicialObject.Augmented C) : SimplicialObject.Augmented D :=
  ((SimplicialObject.Augmented.whiskering C D).obj F).obj P

/-- Constant-diagram comparison for a functor.

For F : C ⥤ D and M : C, the constant diagram const_C(M) followed by F is canonically
isomorphic to const_D(F(M)). Its components are identity maps. -/
def constantMapIso (M : C) :
    (SimplicialObject.const C).obj M ⋙ F ≅
      (SimplicialObject.const D).obj (F.obj M) :=
  Functor.constComp (J := SimplexCategoryᵒᵖ) M F

omit [Abelian C] [Abelian D] [F.Additive] in
/-- Augmentation map after functorial transport.

For any functor F : C ⥤ D and augmented P, the augmentation of mapped F P is the whiskered map
P.hom ⋙ F followed by the hom of constantMapIso F P.right. This equation requires only the
category and functor structures. -/
theorem mapped_hom (P : SimplicialObject.Augmented C) :
    (mapped F P).hom = Functor.whiskerRight P.hom F ≫ (constantMapIso F P.right).hom := by
  rfl

/-- Preservation of normalized augmentation quasi-isomorphisms.

Let F be additive and homology preserving between abelian categories. If ε_P is a
quasi-isomorphism for an augmented P, then the normalized augmentation ε_{mapped F P} is a
quasi-isomorphism. Transport the normalized map to the point, then use the constant-diagram
comparison and the constant-point augmentation. -/
theorem mapped_augmentation_quasiIso [F.PreservesHomology]
    (P : SimplicialObject.Augmented C) (hP : QuasiIso (augmentation P)) :
    QuasiIso (augmentation (mapped F P)) := by
  have hN := normalizationMap_quasiIso P hP
  have hF : QuasiIso ((normalizedMooreComplex D).map (Functor.whiskerRight P.hom F)) :=
    DoldKan.quasiIso_normalizedMap_of_preservesHomology F P.hom hN
  let N : SimplicialObject D ⥤ ChainComplex D ℕ := normalizedMooreComplex D
  have hcomp : normalizationMap (mapped F P) =
      N.map (Functor.whiskerRight P.hom F) ≫ N.map (constantMapIso F P.right).hom :=
    (congrArg (fun a => N.map a) (mapped_hom F P)).trans
      (N.map_comp (Functor.whiskerRight P.hom F) (constantMapIso F P.right).hom)
  let _ : QuasiIso (N.map (Functor.whiskerRight P.hom F)) := hF
  let _ : QuasiIso (N.map (constantMapIso F P.right).hom) := inferInstance
  have hq : QuasiIso (N.map (Functor.whiskerRight P.hom F) ≫
      N.map (constantMapIso F P.right).hom) := inferInstance
  have hMapped : QuasiIso (normalizationMap (mapped F P)) := hcomp.symm ▸ hq
  have hPoint : QuasiIso
      (augmentation ((SimplicialObject.Augmented.const (C := D)).obj (mapped F P).right)) :=
    constant_quasiIso _
  have hWhole : QuasiIso (normalizationMap (mapped F P) ≫
      augmentation ((SimplicialObject.Augmented.const (C := D)).obj (mapped F P).right)) :=
    quasiIso_comp _ _ (hφ := hMapped) (hφ' := hPoint)
  exact (factorization (mapped F P)) ▸ hWhole

end AlgebraicTopology.NormalizedAugmentation

end
