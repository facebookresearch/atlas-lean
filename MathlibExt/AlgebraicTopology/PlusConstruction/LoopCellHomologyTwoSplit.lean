/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellPerfectHomology
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# The actual H₂ splitting of the perfect-subgroup two-cell attachment

Weibel, *The K-book*, Exercise IV.1.4 (printed p. 273), explicitly states
the H₂ direct sum. The calculated noncanonical section, retraction, inverse
maps and generator-coordinate laws here are project-derived refinements of
that assertion. Its later spherical representatives and three-cell plus
construction are not proved by this module.

The original inclusion and relative-chain projection form a short exact
sequence with the free abelian group on every original subgroup element.
Projectivity of that free group constructs a section, the corresponding
coordinate retraction, and both maps of the H₂ direct-sum isomorphism.
Each chosen absolute generator projects to its original characteristic
relative class. The chosen section is not asserted spherical or canonical.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open TopPair.HomologyTheoryData.IsExact

universe u

namespace AlgebraicTopology.LoopCellAttachment

variable (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x))

/-- The actual free abelian coefficient group with one generator for every original `p : P`. -/
abbrev homologyTwoCells : AddCommGrpCat.{u} :=
  ∐ fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{u})

/-- The original relative-chain projection expressed in the actual indexed free-cell coordinate. -/
def homologyTwoProjection :
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (space X x P)) ⟶
        homologyTwoCells X x P :=
  absoluteToRelativeHomologyTwo X x P ≫
    (relativeHomologyTwoIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u})).inv

/-- The computed projection is exactly the original chain quotient followed by the existing cell
coordinate. -/
theorem homologyTwoProjection_eq :
    homologyTwoProjection X x P = absoluteToRelativeHomologyTwo X x P ≫
      (relativeHomologyTwoIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u})).inv :=
  rfl

private abbrev absoluteNatIso (Z : TopCat.{u}) :=
  (show
    (singularHomologyIntFunctor AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) (2 : ℤ)).obj Z ≅
      (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).obj Z) from
    (singularHomologyNatToIntIso AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).app Z)

private abbrev integerShortComplex : ShortComplex AddCommGrpCat.{u} := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let Y : TopCat.{u} := space X x P
  let A : TopPair.{u} := relativePair X x P
  let E : TopPair.HomologyTheoryData.{u} AddCommGrpCat.{u} :=
    singularHomologyIntData AddCommGrpCat.{u} R
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
    singularHomologyIntFunctor AddCommGrpCat.{u} R (2 : ℤ)
  let Q : AddCommGrpCat.{u} :=
    (relativeSingularHomologyIntFunctor AddCommGrpCat.{u} R (2 : ℤ)).obj A
  let f : H.obj X ⟶ H.obj Y := E.subspaceMap 2 A
  let g : H.obj Y ⟶ Q := E.toRelative 2 A
  let d : homologyTwoCells X x P ≅ Q :=
    CellFamilyAttachment.attachmentRelativeDiagonalIntIso X 1 (attachingMap X x P) R
  have hZero : f ≫ g = 0 := subspaceMap_comp_toRelative E 2 A
  exact ShortComplex.mk f (g ≫ d.inv) (by
    calc
      f ≫ (g ≫ d.inv) = (f ≫ g) ≫ d.inv := (Category.assoc f g d.inv).symm
      _ = 0 ≫ d.inv := congrArg (fun h : H.obj X ⟶ Q => h ≫ d.inv) hZero
      _ = 0 := by simp only [Limits.zero_comp])

private theorem integerShortComplex_exact : (integerShortComplex X x P).Exact :=
  CellFamilyAttachment.exact_attachment_toRelative_diagonal
    X 1 (attachingMap X x P) (singularIntegralCoefficients : AddCommGrpCat.{u})

private theorem integerInclusion_naturality :
    (integerShortComplex X x P).f ≫ (absoluteNatIso (space X x P)).hom =
      (absoluteNatIso X).hom ≫
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map (inclusion X x P)) :=
  (singularHomologyNatToIntIso AddCommGrpCat.{u}
    (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom.naturality (inclusion X x P)

private theorem naturalInclusion_comp_integer :
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).map (inclusion X x P)) ≫
        (absoluteNatIso (space X x P)).inv =
      (absoluteNatIso X).inv ≫ (integerShortComplex X x P).f := by
  let S : ShortComplex AddCommGrpCat.{u} := integerShortComplex X x P
  let N : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
    (singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})
  let eX : S.X₁ ≅ N.obj X := absoluteNatIso X
  let eY : S.X₂ ≅ N.obj (space X x P) := absoluteNatIso (space X x P)
  let f : N.obj X ⟶ N.obj (space X x P) := N.map (inclusion X x P)
  have hn : S.f ≫ eY.hom = eX.hom ≫ f := integerInclusion_naturality X x P
  have hComp : (f ≫ eY.inv) ≫ eY.hom = (eX.inv ≫ S.f) ≫ eY.hom := by
    calc
      (f ≫ eY.inv) ≫ eY.hom = f := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = eX.inv ≫ (eX.hom ≫ f) := (eX.inv_hom_id_assoc f).symm
      _ = eX.inv ≫ (S.f ≫ eY.hom) :=
        congrArg (fun h : S.X₁ ⟶ N.obj (space X x P) => eX.inv ≫ h) hn.symm
      _ = (eX.inv ≫ S.f) ≫ eY.hom := (Category.assoc eX.inv S.f eY.hom).symm
  exact (cancel_mono eY.hom).mp hComp

private theorem homologyTwoProjection_eq_integer :
    homologyTwoProjection X x P =
      (absoluteNatIso (space X x P)).inv ≫ (integerShortComplex X x P).g := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let A : TopPair.{u} := relativePair X x P
  let E : TopPair.HomologyTheoryData.{u} AddCommGrpCat.{u} :=
    singularHomologyIntData AddCommGrpCat.{u} R
  let QI : AddCommGrpCat.{u} :=
    (relativeSingularHomologyIntFunctor AddCommGrpCat.{u} R (2 : ℤ)).obj A
  let QN : AddCommGrpCat.{u} :=
    (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).obj A
  let HI : AddCommGrpCat.{u} :=
    (singularHomologyIntFunctor AddCommGrpCat.{u} R (2 : ℤ)).obj (space X x P)
  let HN : AddCommGrpCat.{u} :=
    ((singularHomologyFunctor AddCommGrpCat.{u} 2).obj R).obj (space X x P)
  let a : HI ≅ HN := absoluteNatIso (space X x P)
  let c : QI ≅ QN :=
    (relativeSingularHomologyNatToIntIso AddCommGrpCat.{u} R 2).app A
  let dN : homologyTwoCells X x P ≅ QN := relativeHomologyTwoIso X x P R
  let dI : homologyTwoCells X x P ≅ QI :=
    CellFamilyAttachment.attachmentRelativeDiagonalIntIso X 1 (attachingMap X x P) R
  let g : HI ⟶ QI := E.toRelative 2 A
  have hProjection : absoluteToRelativeHomologyTwo X x P = a.inv ≫ g ≫ c.hom :=
    absoluteToRelativeHomologyTwo_eq_int_projection X x P
  have hDiagonal : dI.inv = c.hom ≫ dN.inv := rfl
  calc
    homologyTwoProjection X x P = absoluteToRelativeHomologyTwo X x P ≫ dN.inv := rfl
    _ = (a.inv ≫ g ≫ c.hom) ≫ dN.inv :=
      congrArg (fun h : HN ⟶ QN => h ≫ dN.inv) hProjection
    _ = a.inv ≫ (g ≫ (c.hom ≫ dN.inv)) := by simp only [Category.assoc]
    _ = a.inv ≫ (g ≫ dI.inv) :=
      congrArg (fun h : QI ⟶ homologyTwoCells X x P => a.inv ≫ (g ≫ h))
        hDiagonal.symm
    _ = (absoluteNatIso (space X x P)).inv ≫ (integerShortComplex X x P).g := rfl

/-- The original H₂ inclusion followed by the full free-cell projection is zero. -/
theorem inclusion_comp_homologyTwoProjection :
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).map (inclusion X x P)) ≫
        homologyTwoProjection X x P = 0 := by
  let S : ShortComplex AddCommGrpCat.{u} := integerShortComplex X x P
  let N : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
    (singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})
  let eX : S.X₁ ≅ N.obj X := absoluteNatIso X
  let eY : S.X₂ ≅ N.obj (space X x P) := absoluteNatIso (space X x P)
  let f : N.obj X ⟶ N.obj (space X x P) := N.map (inclusion X x P)
  let q : N.obj (space X x P) ⟶ S.X₃ := homologyTwoProjection X x P
  have hq : q = eY.inv ≫ S.g := homologyTwoProjection_eq_integer X x P
  have hf : f ≫ eY.inv = eX.inv ≫ S.f := naturalInclusion_comp_integer X x P
  calc
    f ≫ q = f ≫ (eY.inv ≫ S.g) :=
      congrArg (fun h : N.obj (space X x P) ⟶ S.X₃ => f ≫ h) hq
    _ = (f ≫ eY.inv) ≫ S.g := (Category.assoc f eY.inv S.g).symm
    _ = (eX.inv ≫ S.f) ≫ S.g :=
      congrArg (fun h : N.obj X ⟶ S.X₂ => h ≫ S.g) hf
    _ = eX.inv ≫ (S.f ≫ S.g) := Category.assoc eX.inv S.f S.g
    _ = eX.inv ≫ 0 := congrArg (fun h : S.X₁ ⟶ S.X₃ => eX.inv ≫ h) S.zero
    _ = 0 := by simp only [Limits.comp_zero]

/-- The original natural H₂ inclusion and complete free-cell projection,
packaged as the computed short complex. -/
abbrev homologyTwoShortComplex : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).map (inclusion X x P))
    (homologyTwoProjection X x P) (inclusion_comp_homologyTwoProjection X x P)

private def integerToNaturalShortComplexIso :
    integerShortComplex X x P ≅ homologyTwoShortComplex X x P := by
  let S : ShortComplex AddCommGrpCat.{u} := integerShortComplex X x P
  let T : ShortComplex AddCommGrpCat.{u} := homologyTwoShortComplex X x P
  let eX : S.X₁ ≅ T.X₁ := absoluteNatIso X
  let eY : S.X₂ ≅ T.X₂ := absoluteNatIso (space X x P)
  have hq : T.g = eY.inv ≫ S.g := homologyTwoProjection_eq_integer X x P
  have hg : eY.hom ≫ T.g = S.g := by
    calc
      eY.hom ≫ T.g = eY.hom ≫ (eY.inv ≫ S.g) :=
        congrArg (fun h : T.X₂ ⟶ S.X₃ => eY.hom ≫ h) hq
      _ = S.g := eY.hom_inv_id_assoc S.g
  exact ShortComplex.isoMk eX eY (Iso.refl (homologyTwoCells X x P))
    (integerInclusion_naturality X x P).symm
    (hg.trans (Category.comp_id S.g).symm)

private theorem integerInclusion_mono : Mono (integerShortComplex X x P).f := by
  let S : ShortComplex AddCommGrpCat.{u} := integerShortComplex X x P
  let N : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
    (singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})
  let eX : S.X₁ ≅ N.obj X := absoluteNatIso X
  let eY : S.X₂ ≅ N.obj (space X x P) := absoluteNatIso (space X x P)
  let f : N.obj X ⟶ N.obj (space X x P) := N.map (inclusion X x P)
  have : Mono f :=
    mono_inclusionHomologyMap_two X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  have hn : S.f ≫ eY.hom = eX.hom ≫ f := integerInclusion_naturality X x P
  have hMono : Mono (eX.hom ≫ f) := by infer_instance
  have : Mono (S.f ≫ eY.hom) := hn.symm ▸ hMono
  exact mono_of_mono S.f eY.hom

private theorem integralCoefficient_projective :
    Projective (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  let M : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let E : ModuleCat.{u} ℤ ≌ AddCommGrpCat.{u} :=
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence
  have : Module.Projective ℤ M := by infer_instance
  have : Projective M := by infer_instance
  change Projective (E.functor.obj M)
  exact (E.map_projective_iff M).mpr inferInstance

section PerfectKernel

variable [hX : PathConnectedSpace X] [hP : P.Normal] [hperfect : Group.IsPerfect P]
include hX hP hperfect

private theorem integerShortExact : (integerShortComplex X x P).ShortExact := by
  let S : ShortComplex AddCommGrpCat.{u} := integerShortComplex X x P
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let A : TopPair.{u} := relativePair X x P
  let E : TopPair.HomologyTheoryData.{u} AddCommGrpCat.{u} :=
    singularHomologyIntData AddCommGrpCat.{u} R
  let Q : AddCommGrpCat.{u} :=
    (relativeSingularHomologyIntFunctor AddCommGrpCat.{u} R (2 : ℤ)).obj A
  let g : S.X₂ ⟶ Q := E.toRelative 2 A
  let d : S.X₃ ≅ Q :=
    CellFamilyAttachment.attachmentRelativeDiagonalIntIso X 1 (attachingMap X x P) R
  have : Mono S.f := integerInclusion_mono X x P
  have : Epi g := absoluteToRelativeHomologyTwoInt_epi_of_perfect X x P
  have hEpi : Epi (g ≫ d.inv) := by infer_instance
  have hg : S.g = g ≫ d.inv := rfl
  have : Epi S.g := hg.symm ▸ hEpi
  exact ⟨integerShortComplex_exact X x P⟩

/-- The original inclusion and free-cell projection form the computed short exact sequence. -/
theorem homologyTwoShortExact : (homologyTwoShortComplex X x P).ShortExact :=
  ShortComplex.shortExact_of_iso (integerToNaturalShortComplexIso X x P)
    (integerShortExact X x P)

/-- The splitting computed from the original short exact sequence and
projectivity of every free cell. -/
def homologyTwoSplitting : (homologyTwoShortComplex X x P).Splitting := by
  letI : Projective (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
    exact integralCoefficient_projective.{u}
  letI : Projective (homologyTwoShortComplex X x P).X₃ := by
    change Projective (∐ fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{u}))
    infer_instance
  have hShortExact : (homologyTwoShortComplex X x P).ShortExact := by
    exact homologyTwoShortExact X x P
  exact hShortExact.splittingOfProjective

/-- The computed section of the original H₂ free-cell projection. -/
def homologyTwoSection :
    homologyTwoCells X x P ⟶
      (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (space X x P)) :=
  (homologyTwoSplitting X x P).s

/-- The original-space H₂ coordinate retraction supplied by the computed splitting. -/
def homologyTwoRetraction :
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (space X x P)) ⟶
      (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).obj X) :=
  (homologyTwoSplitting X x P).r

/-- The actual direct-sum H₂ isomorphism, retaining the original inclusion and all free cells. -/
def homologyTwoSplitIso :
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (space X x P)) ≅
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).obj X) ⊞ homologyTwoCells X x P :=
  (homologyTwoSplitting X x P).isoBinaryBiproduct

/-- The section is a strict right inverse of the whole original free-cell projection. -/
@[reassoc]
theorem homologyTwoSection_projection :
    homologyTwoSection X x P ≫ homologyTwoProjection X x P = 𝟙 (homologyTwoCells X x P) :=
  (homologyTwoSplitting X x P).s_g

/-- The coordinate retraction is a strict left inverse of the original inclusion on H₂. -/
@[reassoc]
theorem inclusion_homologyTwoRetraction :
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).map (inclusion X x P)) ≫
        homologyTwoRetraction X x P = 𝟙 _ :=
  (homologyTwoSplitting X x P).f_r

/-- The original-space and free-cell coordinates sum to the identity on every H₂ class. -/
theorem homologyTwo_decomposition :
    homologyTwoRetraction X x P ≫
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map (inclusion X x P)) +
      homologyTwoProjection X x P ≫ homologyTwoSection X x P = 𝟙 _ :=
  (homologyTwoSplitting X x P).id

/-- The forward direct-sum map consists of the computed coordinate retraction and original
projection. -/
theorem homologyTwoSplitIso_hom :
    (homologyTwoSplitIso X x P).hom =
      biprod.lift (homologyTwoRetraction X x P) (homologyTwoProjection X x P) :=
  rfl

/-- The inverse direct-sum map uses exactly the original inclusion and computed section. -/
theorem homologyTwoSplitIso_inv :
    (homologyTwoSplitIso X x P).inv =
      biprod.desc
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map (inclusion X x P))
        (homologyTwoSection X x P) :=
  rfl

/-- The two computed coordinate maps are inverse on every original H₂ class. -/
theorem homologyTwoSplitIso_hom_inv :
    (homologyTwoSplitIso X x P).hom ≫ (homologyTwoSplitIso X x P).inv = 𝟙 _ :=
  (homologyTwoSplitIso X x P).hom_inv_id

/-- The two computed coordinate maps are inverse on both complete direct-sum coordinates. -/
theorem homologyTwoSplitIso_inv_hom :
    (homologyTwoSplitIso X x P).inv ≫ (homologyTwoSplitIso X x P).hom = 𝟙 _ :=
  (homologyTwoSplitIso X x P).inv_hom_id

/-- The original inclusion is exactly the first summand of the constructed H₂ isomorphism. -/
@[reassoc]
theorem homologyTwoSplitIso_inclusion :
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).map (inclusion X x P)) ≫
        (homologyTwoSplitIso X x P).hom = biprod.inl := by
  apply biprod.hom_ext
  · simp only [Category.assoc, homologyTwoSplitIso_hom, biprod.lift_fst,
      inclusion_homologyTwoRetraction, biprod.inl_fst]
  · simp only [Category.assoc, homologyTwoSplitIso_hom, biprod.lift_snd,
      inclusion_comp_homologyTwoProjection, biprod.inl_snd]

/-- The whole original free-cell projection is the second summand of the constructed isomorphism. -/
@[reassoc]
theorem homologyTwoSplitIso_projection :
    (homologyTwoSplitIso X x P).hom ≫ biprod.snd = homologyTwoProjection X x P := by
  rw [homologyTwoSplitIso_hom, biprod.lift_snd]

/-- The computed section is exactly the free-cell summand of the constructed isomorphism. -/
@[reassoc]
theorem homologyTwoSection_splitIso :
    homologyTwoSection X x P ≫ (homologyTwoSplitIso X x P).hom = biprod.inr := by
  apply biprod.hom_ext
  · simp only [Category.assoc, homologyTwoSplitIso_hom, biprod.lift_fst, biprod.inr_fst]
    exact (homologyTwoSplitting X x P).s_r
  · simp only [Category.assoc, homologyTwoSplitIso_hom, biprod.lift_snd,
      homologyTwoSection_projection, biprod.inr_snd]

/-- Returning the computed section to the original relative homology recovers the complete cell
coordinate. -/
@[reassoc]
theorem homologyTwoSection_relative :
    homologyTwoSection X x P ≫ absoluteToRelativeHomologyTwo X x P =
      (relativeHomologyTwoIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u})).hom := by
  apply (cancel_mono
    (relativeHomologyTwoIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u})).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id]
  change homologyTwoSection X x P ≫ homologyTwoProjection X x P = 𝟙 _
  exact homologyTwoSection_projection X x P

/-- The chosen absolute H₂ generator for the original indexed characteristic cell. -/
def homologyTwoGeneratorLift (p : P) :
    (singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (space X x P)) :=
  Sigma.ι (fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{u})) p ≫
    homologyTwoSection X x P

/-- Every chosen absolute generator projects to its actual indexed free-cell basis morphism. -/
@[reassoc]
theorem homologyTwoGeneratorLift_projection (p : P) :
    homologyTwoGeneratorLift X x P p ≫ homologyTwoProjection X x P =
      Sigma.ι (fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{u})) p := by
  rw [homologyTwoGeneratorLift, Category.assoc, homologyTwoSection_projection, Category.comp_id]

/-- Every chosen absolute generator recovers the SAME original characteristic relative class. -/
@[reassoc]
theorem homologyTwoGeneratorLift_relative (p : P) :
    homologyTwoGeneratorLift X x P p ≫ absoluteToRelativeHomologyTwo X x P =
      relativeGenerator X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) p := by
  rw [homologyTwoGeneratorLift, Category.assoc, homologyTwoSection_relative,
    ← relativeGenerator_desc, Sigma.ι_comp_desc]

/-- The complete direct-sum coordinate of each original added generator is `(0,e_p)`. -/
@[reassoc]
theorem homologyTwoGeneratorLift_coordinate (p : P) :
    homologyTwoGeneratorLift X x P p ≫ (homologyTwoSplitIso X x P).hom =
      Sigma.ι (fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{u})) p ≫
        biprod.inr := by
  rw [homologyTwoGeneratorLift, Category.assoc, homologyTwoSection_splitIso]

end PerfectKernel
end AlgebraicTopology.LoopCellAttachment
end
