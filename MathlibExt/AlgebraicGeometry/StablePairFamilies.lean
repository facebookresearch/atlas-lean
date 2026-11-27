/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory
public import MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual coherent stable-pair families and their native complexes

The source is the actual product X × T. A pair is an actual coherent
module and a section O → F. Purity quantifies over nonzero coherent
subobjects and uses the dimension of their actual stalk support.
The cokernel condition uses the actual abelian cokernel. Relative
flatness tests the actual affine section modules over the base rings.

The native complex is formed from the section in degrees 0 and 1.
The negative cone input compensates the native shift sign, retaining
the section's original sign in its differential.

Reference: Pandharipande–Thomas, arXiv:0707.2348v5,
§1.1 and §2.3, equation (2.9). Generic coherent/pullback families are
existing native module operations and completed public Axiom source.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairFamilies

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open CoherentCurveLinearSeries LineBundleTaskContracts GlobalPerfectObstructionTheory
open AlgebraicBundleGeometry
attribute [local instance] HasDerivedCategory.standard

/-- A genuine projective embedding and nonsingular relative dimension three. -/
structure Threefold (X : Over (Spec (.of ℂ))) where
  projectiveDimension : ℕ
  projectiveSpace : ProjectiveBundle (Over.mk (𝟙 (Spec (.of ℂ)))) 0 projectiveDimension
    (SheafOfModules.free (R := (Spec (.of ℂ)).ringCatSheaf) (Fin (projectiveDimension + 1)))
  embedding : X ⟶ projectiveSpace.total
  [closed : IsClosedImmersion embedding.left]
  [smooth : SmoothOfRelativeDimension 3 X.hom]
  [proper : IsProper X.hom]
  [noetherian : IsNoetherian X.left]

/-- The actual stalk support of a module sheaf. -/
def support {Y : Scheme} (F : Y.Modules) : Set Y :=
  {y | ¬ IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).obj F.presheaf)}

def supportDimension {Y : Scheme} (F : Y.Modules) :=
  topologicalKrullDim (support F)

def coherent {Y : Scheme} (F : Y.Modules) : Prop :=
  SheafOfModules.IsQuasicoherent F ∧ SheafOfModules.IsFinitePresentation F

/-- Purity uses actual coherent subobjects, including embedded support tests. -/
def PureDimension {Y : Scheme} (F : Y.Modules) (d : ℕ) : Prop :=
  coherent F ∧ supportDimension F = d ∧
    ∀ A : Subobject F, coherent (A : Y.Modules) → ¬ IsZero (A : Y.Modules) →
      supportDimension (A : Y.Modules) = d

/-- Flatness over the parameter uses native affine restriction of scalars. -/
def FlatOver {Y T : Scheme} (p : Y ⟶ T) (F : Y.Modules) : Prop :=
  ∀ a : AffineChart p,
    Module.Flat a.base
      ((ModuleCat.restrictScalars (p.appLE a.target a.source a.over).hom).obj
        ((moduleSections a.source).obj F))

@[implicit_reducible]
def total (X T : Over (Spec (.of ℂ))) : Scheme := pullback X.hom T.hom

def projection (X T : Over (Spec (.of ℂ))) : total X T ⟶ T.left :=
  pullback.snd X.hom T.hom

/-- The ordinary coherent section pair on the actual product. -/
structure RawPair (X T : Over (Spec (.of ℂ))) where
  module : (total X T).Modules
  sectionMap : Section module

variable {X T : Over (Spec (.of ℂ))}

def fibre (F : RawPair X T) (Ω : Type) [Field Ω] (p : Spec (.of Ω) ⟶ T.left) :
    (pullback (projection X T) p).Modules :=
  (Scheme.Modules.pullback (pullback.fst (projection X T) p)).obj F.module

def fibreSection (F : RawPair X T) (Ω : Type) [Field Ω] (p : Spec (.of Ω) ⟶ T.left) :
    Section (fibre F Ω p) :=
  LineBundleTaskContracts.pullbackSection (pullback.fst (projection X T) p) F.sectionMap

/-- A source-faithful stable-pair family before selecting numerical components. -/
structure Family (X T : Over (Spec (.of ℂ))) extends RawPair X T where
  coherent : StablePairFamilies.coherent module
  flat : FlatOver (projection X T) module
  geometric : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ T.left),
    PureDimension (fibre toRawPair Ω p) 1 ∧
      supportDimension (cokernel (fibreSection toRawPair Ω p)) ≤ (0 : ℕ)

/-- The actual native two-term pair complex, with the shift sign compensated. -/
def complex (F : RawPair X T) : CochainComplex (total X T).Modules ℤ :=
  (CochainComplex.mappingCone
    (-((CochainComplex.singleFunctor (total X T).Modules 0).map F.sectionMap)))⟦(-1 : ℤ)⟧

/-- The literal degree-zero source of the pair section. -/
def zeroInclusion (F : RawPair X T) : structureModule (total X T) ⟶ (complex F).X 0 :=
  let a := -((CochainComplex.singleFunctor (total X T).Modules 0).map F.sectionMap)
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (structureModule (total X T))).inv ≫
    (CochainComplex.mappingCone.inl a).v 0 (-1) (by omega) ≫
      ((CochainComplex.mappingCone a).shiftFunctorObjXIso (-1) 0 (-1) rfl).inv

/-- The literal degree-one target of the same pair section. -/
def oneProjection (F : RawPair X T) : (complex F).X 1 ⟶ F.module :=
  let a := -((CochainComplex.singleFunctor (total X T).Modules 0).map F.sectionMap)
  ((CochainComplex.mappingCone a).shiftFunctorObjXIso (-1) 1 0 (by omega)).hom ≫
    (CochainComplex.mappingCone.snd a).v 0 0 (by omega) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F.module).hom

/-- The cone and shift conventions retain the original stable-pair section's sign. -/
theorem complex_differential (F : RawPair X T) :
    zeroInclusion F ≫ (complex F).d 0 1 ≫ oneProjection F = F.sectionMap := by
  let a := -((CochainComplex.singleFunctor (total X T).Modules 0).map F.sectionMap)
  have h : (CochainComplex.mappingCone.inl a).v 0 (-1) (by omega) ≫
      (CochainComplex.mappingCone a).d (-1) 0 ≫
        (CochainComplex.mappingCone.snd a).v 0 0 (by omega) = a.f 0 := by
    rw [CochainComplex.mappingCone.inl_v_d_assoc a 0 (-1) 1 (by omega) (by omega)]
    simp
  have h' := congrArg (fun m =>
    -(HomologicalComplex.singleObjXSelf (.up ℤ) 0 (structureModule (total X T))).inv ≫
      m ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F.module).hom) h
  simpa [zeroInclusion, oneProjection, complex, a, Category.assoc,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq,
    CochainComplex.singleFunctor, HomologicalComplex.single_map_f_self] using h'

def derivedComplex (F : RawPair X T) : DerivedCategory (total X T).Modules :=
  DerivedCategory.Q.obj (complex F)

/-- Actual pair isomorphisms preserve the original section. -/
structure PairIso (F G : Family X T) where
  iso : F.module ≅ G.module
  section_eq : F.sectionMap ≫ iso.hom = G.sectionMap

@[ext]
theorem PairIso.ext {F G : Family X T} {a b : PairIso F G} (h : a.iso.hom = b.iso.hom) :
    a = b := by
  have hi : a.iso = b.iso := Iso.ext h
  cases a
  cases b
  cases hi
  rfl

instance pairCategory : Category (Family X T) where
  Hom := PairIso
  id F := ⟨Iso.refl _, by simp⟩
  comp a b := ⟨a.iso ≪≫ b.iso, by simp [← Category.assoc, a.section_eq, b.section_eq]⟩
  id_comp a := by apply PairIso.ext; exact Category.id_comp _
  comp_id a := by apply PairIso.ext; exact Category.comp_id _
  assoc a b c := by apply PairIso.ext; exact Category.assoc _ _ _

instance pairIsGroupoid : IsGroupoid (Family X T) where
  all_isIso a := by
    refine ⟨⟨⟨a.iso.symm, ?_⟩, ?_, ?_⟩⟩
    · rw [← a.section_eq]
      simp
    · apply PairIso.ext
      exact a.iso.hom_inv_id
    · apply PairIso.ext
      exact a.iso.inv_hom_id

end MathlibExt.AlgebraicGeometry.StablePairFamilies
