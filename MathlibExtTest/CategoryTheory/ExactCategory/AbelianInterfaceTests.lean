/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.ExactCategory.Abelian
import MathlibExt.CategoryTheory.ExactCategory.Bicartesian
import MathlibExt.CategoryTheory.ExactCategory.Functor
import Mathlib.Algebra.Category.ModuleCat.Abelian
import MathlibExt.CategoryTheory.HomologicalComplex.FunctorRelativeResolutionComparison.Homology
import Mathlib.Algebra.Homology.SingleHomology
meta import Mathlib.Tactic.NormNum

/-!
# Tests of the maximal exact structure on integer modules

The canonical Abelian instance supplies the exact structure on `ModuleCat ℤ`.
The split sequence `ℤ → ℤ ⊞ ℤ → ℤ` has nonzero inclusion and projection.
A triangular middle map with identity endpoints gives both a pullback and
a pushout. Exact identity functors preserve the sequence and these maps.
An arbitrary short exact complex is admissible for the inferred instance,
distinguishing this maximal structure from the split exact structure.

The identity-augmented degree-zero integer complex supplies a genuine
relative-resolution comparison over multiplication by two. Its full chain
augmentation equation and degree-zero homology map retain that endpoint map;
the canonical homology coordinate sends `1` to `2` and is nonzero.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.ExactCategory

noncomputable section

namespace MathlibExtTest.CategoryTheory.ExactCategory.AbelianInterface

abbrev Z := ModuleCat.of ℤ ℤ

/-- The nonzero split exact sequence with first inclusion and second projection. -/
def S : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (biprod.inl : Z ⟶ Z ⊞ Z) biprod.snd (by simp)

/-- A triangular endomorphism of the middle module. -/
def middle : Z ⊞ Z ⟶ Z ⊞ Z :=
  biprod.lift (biprod.fst + biprod.snd) biprod.snd

/-- The endpoints are identities while the middle map adds the second coordinate to the first. -/
def shear : S ⟶ S where
  τ₁ := 𝟙 Z
  τ₂ := middle
  τ₃ := 𝟙 Z
  comm₁₂ := by
    apply biprod.hom_ext
    · simp [S, middle]
    · simp [S, middle]
  comm₂₃ := by simp [S, middle]

/-- Admissibility is derived from the split-sequence axiom of the inferred exact structure. -/
lemma admissible_S : IsAdmissibleExact S := isAdmissibleExact_split Z Z

/-- The priority-100 Abelian instance is available without an exact-category assumption. -/
example : ExactCategory (ModuleCat ℤ) := inferInstance

/-- The first nonzero inclusion is admissible. -/
example : IsAdmissibleMono (biprod.inl : Z ⟶ Z ⊞ Z) :=
  isAdmissibleMono_f admissible_S

/-- The second nonzero projection is admissible. -/
example : IsAdmissibleEpi (biprod.snd : Z ⊞ Z ⟶ Z) :=
  isAdmissibleEpi_g admissible_S

/-- The triangular map gives a pullback square on the final two terms. -/
example : IsPullback S.g middle (𝟙 Z) S.g := by
  let : IsIso shear.τ₁ := by change IsIso (𝟙 Z); infer_instance
  exact isPullback_g_of_isAdmissibleExact_of_isIso_left shear admissible_S admissible_S

/-- Its identity right endpoint gives a pushout square on the first two terms. -/
example : IsPushout S.f (𝟙 Z) middle S.f := by
  let : IsIso shear.τ₃ := by change IsIso (𝟙 Z); infer_instance
  exact isPushout_f_of_isAdmissibleExact_of_isIso_right shear admissible_S admissible_S

/-- Exactness of the identity functor is inferred. -/
example : (𝟭 (ModuleCat ℤ)).IsExact := inferInstance

/-- Applying the exact identity functor preserves the concrete admissible sequence. -/
example : IsAdmissibleExact (S.map (𝟭 (ModuleCat ℤ))) :=
  (𝟭 (ModuleCat ℤ)).map_admissibleExact S admissible_S

/-- The exact-functor pushout interface preserves the triangular square along its admissible
inclusion. -/
example : IsPushout ((𝟭 (ModuleCat ℤ)).map (𝟙 Z))
    ((𝟭 (ModuleCat ℤ)).map S.f) ((𝟭 (ModuleCat ℤ)).map S.f)
    ((𝟭 (ModuleCat ℤ)).map middle) := by
  let : IsIso shear.τ₃ := by change IsIso (𝟙 Z); infer_instance
  have hpo : IsPushout S.f (𝟙 Z) middle S.f :=
    isPushout_f_of_isAdmissibleExact_of_isIso_right shear admissible_S admissible_S
  exact (𝟭 (ModuleCat ℤ)).map_isPushout_of_isAdmissibleMono hpo.flip
    (isAdmissibleMono_f admissible_S)


/-- The inferred abelian exact structure admits every short exact complex. -/
example (T : ShortComplex (ModuleCat ℤ)) (hT : T.ShortExact) :
    IsAdmissibleExact T := hT

namespace RelativeComparison

/-- The identity restriction functor on integer modules. -/
abbrev U : ModuleCat ℤ ⥤ ModuleCat ℤ := 𝟭 _

/-- The integer complex concentrated in degree zero. -/
abbrev Q : ChainComplex (ModuleCat ℤ) ℕ := (ChainComplex.single₀ (ModuleCat ℤ)).obj Z

/-- Its identity augmentation has an actual contracting splitting. -/
def splitting : Functor.AugmentationSplit U Q Z (𝟙 Q) where
  section_ := 𝟙 Z
  s _ := 0
  section_comp := by simp
  zero := by
    change (𝟙 Z) ≫ (𝟙 Z) + (0 : Z ⟶ Q.X 1) ≫ 0 = 𝟙 Z
    rw [Category.id_comp, Limits.zero_comp, add_zero]
  succ n := by
    have hz : IsZero (Q.X (n + 1)) :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 Z (n + 1) (by simp)
    exact hz.eq_of_src _ _

/-- The identity adjunction proves relative projectivity of every source term. -/
lemma relativeTerms (n : ℕ) : U.IsRelativeProjective (Q.X n) :=
  (Adjunction.id (C := ModuleCat ℤ)).isRelativeProjective_obj (Q.X n)

/-- Identity restriction preserves each displayed differential kernel. -/
lemma preservesKernels (n : ℕ) : PreservesLimit (parallelPair (Q.d (n + 1) n) 0) U :=
  inferInstance

/-- The prescribed endpoint map doubles integers. -/
def twice : Z ⟶ Z := (2 : ℤ) • 𝟙 Z

/-- The prescribed module map sends the integer `1` to `2`. -/
lemma twice_one : twice.hom (1 : ℤ) = (2 : ℤ) := by
  unfold twice
  rw [ModuleCat.hom_zsmul]
  change (2 : ℤ) • (1 : ℤ) = (2 : ℤ)
  norm_num

/-- The general relative-resolution constructor lifts the doubling map. -/
def comparisonTwice : Q ⟶ Q :=
  Functor.comparison U Q Q Z Z (𝟙 Q) (𝟙 Q) splitting relativeTerms preservesKernels twice

/-- The complete chain augmentation equation includes the specified endpoint map. -/
example : comparisonTwice ≫ 𝟙 Q =
    𝟙 Q ≫ (ChainComplex.single₀ (ModuleCat ℤ)).map twice :=
  Functor.comparison_augmentation U Q Q Z Z (𝟙 Q) (𝟙 Q)
    splitting relativeTerms preservesKernels twice

/-- Identity augmentation forces the entire comparison to be the single-complex map. -/
lemma comparisonTwice_eq : comparisonTwice =
    (ChainComplex.single₀ (ModuleCat ℤ)).map twice := by
  have h := Functor.comparison_augmentation U Q Q Z Z (𝟙 Q) (𝟙 Q)
    splitting relativeTerms preservesKernels twice
  simpa only [comparisonTwice, Q, Category.comp_id, Category.id_comp] using h

/-- The chain comparison has a nonzero degree-zero coordinate. -/
example : (comparisonTwice.f 0).hom (1 : ℤ) = (2 : ℤ) := by
  rw [comparisonTwice_eq, ChainComplex.single₀_map_f_zero]
  exact twice_one

/-- The general homology API induces the comparison map in degree zero. -/
def homologyTwice : (Functor.mappedResolution U Q).homology 0 ⟶
    (Functor.mappedResolution U Q).homology 0 :=
  Functor.comparisonHomologyMap U U Q Q Z Z (𝟙 Q) (𝟙 Q)
    splitting relativeTerms preservesKernels twice 0

/-- This homology map equals the native homology map of the known augmented lift. -/
lemma homologyTwice_eq : homologyTwice =
    HomologicalComplex.homologyMap
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).map
        ((ChainComplex.single₀ (ModuleCat ℤ)).map twice)) 0 :=
  Functor.comparisonHomologyMap_eq_of_augmentation U U Q Q Z Z (𝟙 Q) (𝟙 Q)
    splitting relativeTerms preservesKernels twice
    ((ChainComplex.single₀ (ModuleCat ℤ)).map twice) (by simp) 0

/-- Canonical identity-functor transport followed by the native single-complex homology coordinate.
-/
def homologyIso : (Functor.mappedResolution U Q).homology 0 ≅ Z :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 0).mapIso
    ((Functor.mapHomologicalComplexIdIso (ModuleCat ℤ) (ComplexShape.down ℕ)).app Q) ≪≫
      HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 Z

/-- The comparison homology map retains doubling under that canonical coordinate. -/
lemma homologyTwice_naturality : homologyTwice ≫ homologyIso.hom = homologyIso.hom ≫ twice := by
  rw [homologyTwice_eq]
  have hn := congrArg
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 0).map
    ((Functor.mapHomologicalComplexIdIso (ModuleCat ℤ) (ComplexShape.down ℕ)).hom.naturality
      ((ChainComplex.single₀ (ModuleCat ℤ)).map twice))
  simp only [Functor.map_comp] at hn
  have hnat : HomologicalComplex.homologyMap
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).map
        ((ChainComplex.single₀ (ModuleCat ℤ)).map twice)) 0 ≫
      ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 0).mapIso
        ((Functor.mapHomologicalComplexIdIso (ModuleCat ℤ) (ComplexShape.down ℕ)).app Q)).hom =
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 0).mapIso
      ((Functor.mapHomologicalComplexIdIso (ModuleCat ℤ) (ComplexShape.down ℕ)).app Q)).hom ≫
        HomologicalComplex.homologyMap ((ChainComplex.single₀ (ModuleCat ℤ)).map twice) 0 := by
    simpa only [U, Q, Functor.mapIso_hom, Iso.app_hom,
      HomologicalComplex.homologyFunctor_map, Functor.id_map] using hn
  change HomologicalComplex.homologyMap
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).map
        ((ChainComplex.single₀ (ModuleCat ℤ)).map twice)) 0 ≫
    (((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 0).mapIso
      ((Functor.mapHomologicalComplexIdIso (ModuleCat ℤ) (ComplexShape.down ℕ)).app Q)).hom ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 Z).hom) =
    (((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 0).mapIso
      ((Functor.mapHomologicalComplexIdIso (ModuleCat ℤ) (ComplexShape.down ℕ)).app Q)).hom ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 Z).hom) ≫ twice
  rw [← Category.assoc, hnat, Category.assoc,
    HomologicalComplex.singleObjHomologySelfIso_hom_naturality, ← Category.assoc]

/-- Conjugating the comparison homology map by its canonical coordinate gives doubling. -/
lemma homologyTwice_coordinate : homologyIso.inv ≫ homologyTwice ≫ homologyIso.hom = twice := by
  rw [homologyTwice_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The actual degree-zero homology map sends the coordinate `1` to `2`. -/
example : (homologyIso.inv ≫ homologyTwice ≫ homologyIso.hom).hom (1 : ℤ) = (2 : ℤ) := by
  rw [homologyTwice_coordinate]
  exact twice_one

/-- The induced homology map is genuinely nonzero. -/
example : homologyTwice ≠ 0 := by
  intro h
  have hc : (homologyIso.inv ≫ homologyTwice ≫ homologyIso.hom).hom (1 : ℤ) = (2 : ℤ) := by
    rw [homologyTwice_coordinate]
    exact twice_one
  rw [h] at hc
  norm_num at hc

end RelativeComparison

end MathlibExtTest.CategoryTheory.ExactCategory.AbelianInterface
