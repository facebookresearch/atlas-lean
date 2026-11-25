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
# Actual normalized augmentations under exact additive functors

The augmentation is the original Moore inclusion followed by the original
alternating augmentation.  Its full naturality and factorization through
the normalized constant point are proved from native natural transformations.
The constant point has the native constant extra degeneracy.

An actually homology-preserving additive functor therefore preserves the
quasi-isomorphism of a GIVEN original normalized augmentation.  Only that
source resolution property is input; no desired mapped augmentation,
exactness, contraction, or resolution comparison certificate is supplied.
Native verification is unexecuted for this source proposal.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe uC vC uD vD

namespace AlgebraicTopology.NormalizedAugmentation

variable {C : Type uC} [Category.{vC} C] [Abelian C]

/-- The actual native normalized complex of the original augmented object. -/
abbrev complex (P : SimplicialObject.Augmented C) : ChainComplex C ℕ :=
  (normalizedMooreComplex C).obj P.left

/-- The original chain augmentation, without a replacement model. -/
def augmentation (P : SimplicialObject.Augmented C) :
    complex P ⟶ (ChainComplex.single₀ C).obj P.right :=
  inclusionOfMooreComplexMap P.left ≫ AlternatingFaceMapComplex.ε.app P

/-- The original whole augmentation induces its actual map to the constant point. -/
def toConstant (P : SimplicialObject.Augmented C) :
    P ⟶ (SimplicialObject.Augmented.const (C := C)).obj P.right where
  left := P.hom
  right := 𝟙 P.right
  w := by
    change P.hom ≫ 𝟙 ((SimplicialObject.const C).obj P.right) =
      P.hom ≫ (SimplicialObject.const C).map (𝟙 P.right)
    exact (congrArg (fun a => P.hom ≫ a) ((SimplicialObject.const C).map_id P.right)).symm

/-- Native normalization of the original simplicial augmentation. -/
def normalizationMap (P : SimplicialObject.Augmented C) :
    complex P ⟶ complex ((SimplicialObject.Augmented.const (C := C)).obj P.right) :=
  (normalizedMooreComplex C).map P.hom

/-- Full naturality of the actual normalized augmentation. -/
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

/-- The original augmentation factors through its actual normalized constant point. -/
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

/-- Native constant extra degeneracy supplies this specific constant augmentation's contraction. -/
theorem constant_quasiIso (M : C) :
    QuasiIso (augmentation ((SimplicialObject.Augmented.const (C := C)).obj M)) :=
  ((DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
    (Y := (SimplicialObject.const C).obj M)).trans
      (SimplicialObject.Augmented.ExtraDegeneracy.const M).homotopyEquiv).quasiIso_hom

/-- The given original augmentation quasi-isomorphism earns its normalized map to the point. -/
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

/-- An actual isomorphism of augmented objects transports the original augmentation property. -/
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

/-- Actual native application of the functor to the entire original augmentation. -/
abbrev mapped (P : SimplicialObject.Augmented C) : SimplicialObject.Augmented D :=
  ((SimplicialObject.Augmented.whiskering C D).obj F).obj P

/-- The exact constant-point comparison, with actual identity components. -/
def constantMapIso (M : C) :
    (SimplicialObject.const C).obj M ⋙ F ≅
      (SimplicialObject.const D).obj (F.obj M) :=
  Functor.constComp (J := SimplexCategoryᵒᵖ) M F

omit [Abelian C] [Abelian D] [F.Additive] in
/-- The mapped augmentation is the literal original map, followed only by the constant comparison. -/
theorem mapped_hom (P : SimplicialObject.Augmented C) :
    (mapped F P).hom = Functor.whiskerRight P.hom F ≫ (constantMapIso F P.right).hom := by
  rfl

/-- Exact additive transport earns the actual mapped normalized augmentation quasi-isomorphism. -/
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
