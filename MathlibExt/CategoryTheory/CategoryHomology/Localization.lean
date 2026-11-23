/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import MathlibExt.Algebra.Category.ModuleCat.LocalizationColimits
public import MathlibExt.Algebra.Homology.Functor
public import MathlibExt.CategoryTheory.CategoryHomology.BarFunctoriality

/-!
# Localization of category homology coefficients

For a module-valued coefficient system `M`, localization commutes with its
category homology.  The comparison is built in four layers.

1. In every simplicial degree, preservation of coproducts identifies the
   localization of the coefficient-bar coproduct with the bar coproduct of
   the objectwise-localized coefficients.
2. The coproduct comparison commutes separately with every face and every
   degeneracy.  On each summand this is functoriality of localization applied
   to the corresponding coefficient map.
3. The resulting simplicial isomorphism induces an isomorphism of alternating
   face complexes.  Thus all signs are handled by the existing additive
   alternating-complex comparison.
4. The source and target Dold--Kan homotopy equivalences transport this to a
   homotopy equivalence of normalized complexes.  Composing its homology
   isomorphism with the inverse of `mapHomologyFunctorIso` gives the final
   localization formula.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace CategoryTheory.CategoryHomology

variable {C : Type u} [Category.{u} C]
  {R : Type u} [CommRing R]
  (S : Submonoid R) (M : C ⥤ ModuleCat.{u} R)

local notation "L" => ModuleCat.localizedModuleFunctor S

/-- Degreewise coproduct comparison between localization of the coefficient
bar and the bar of objectwise-localized coefficients. -/
noncomputable def coefficientBarLocalizationObjIso (n : ℕ) :
    (L).obj (coefficientBarObj M n) ≅
      coefficientBarObj (M ⋙ L) n := by
  change (L).obj (∐ coefficientBarFamily M n) ≅
    ∐ fun F ↦ (L).obj ((coefficientBarFamily M n) F)
  exact PreservesCoproduct.iso L (coefficientBarFamily M n)

/-- The hom of the degreewise coproduct comparison sends a mapped source
summand inclusion to the corresponding target inclusion. -/
@[reassoc (attr := simp)]
theorem map_coefficientBarι_comp_coefficientBarLocalizationObjIso_hom
    {n : ℕ} (F : ComposableArrows C n) :
    (L).map (coefficientBarι M F) ≫
        (coefficientBarLocalizationObjIso S M n).hom =
      coefficientBarι (M ⋙ L) F := by
  change (L).map (Sigma.ι (coefficientBarFamily M n) F) ≫
      (PreservesCoproduct.iso L (coefficientBarFamily M n)).hom =
    Sigma.ι (fun F ↦ (L).obj ((coefficientBarFamily M n) F)) F
  rw [← cancel_mono
    (PreservesCoproduct.iso L (coefficientBarFamily M n)).inv]
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [PreservesCoproduct.inv_hom] using
    (ι_comp_sigmaComparison L (coefficientBarFamily M n) F).symm

/-- The inverse degreewise comparison followed by localization of a source
summand inclusion is the corresponding target inclusion. -/
@[reassoc (attr := simp)]
theorem coefficientBarι_comp_coefficientBarLocalizationObjIso_inv
    {n : ℕ} (F : ComposableArrows C n) :
    coefficientBarι (M ⋙ L) F ≫
        (coefficientBarLocalizationObjIso S M n).inv =
      (L).map (coefficientBarι M F) := by
  change Sigma.ι (fun F ↦ (L).obj ((coefficientBarFamily M n) F)) F ≫
      (PreservesCoproduct.iso L (coefficientBarFamily M n)).inv =
    (L).map (Sigma.ι (coefficientBarFamily M n) F)
  simpa only [PreservesCoproduct.inv_hom] using
    ι_comp_sigmaComparison L (coefficientBarFamily M n) F

/-- The degreewise coproduct comparisons assemble into an isomorphism of
simplicial bar data. -/
noncomputable def coefficientBarLocalizationDataIso :
    SimplicialObject.Data.mapObj L (coefficientBarData M) ≅
      coefficientBarData (M ⋙ L) where
  hom :=
    { app := fun n ↦ (coefficientBarLocalizationObjIso S M n).hom
      w_δ := by
        intro n i
        change (coefficientBarLocalizationObjIso S M (n + 1)).hom ≫
            coefficientBarFace (M ⋙ L) i =
          (L).map (coefficientBarFace M i) ≫
            (coefficientBarLocalizationObjIso S M n).hom
        rw [← cancel_epi
          (coefficientBarLocalizationObjIso S M (n + 1)).inv]
        rw [Iso.inv_hom_id_assoc]
        apply coefficientBar_hom_ext (M ⋙ L)
        intro F
        rw [coefficientBarι_face]
        rw [← Category.assoc,
          coefficientBarι_comp_coefficientBarLocalizationObjIso_inv]
        rw [← Category.assoc, ← (L).map_comp]
        rw [coefficientBarι_face]
        rw [(L).map_comp]
        rw [Category.assoc,
          map_coefficientBarι_comp_coefficientBarLocalizationObjIso_hom
            S M ((nerve C).δ i F)]
        rfl
      w_σ := by
        intro n i
        change (coefficientBarLocalizationObjIso S M n).hom ≫
            coefficientBarDegeneracy (M ⋙ L) i =
          (L).map (coefficientBarDegeneracy M i) ≫
            (coefficientBarLocalizationObjIso S M (n + 1)).hom
        rw [← cancel_epi (coefficientBarLocalizationObjIso S M n).inv]
        rw [Iso.inv_hom_id_assoc]
        apply coefficientBar_hom_ext (M ⋙ L)
        intro F
        rw [coefficientBarι_degeneracy]
        rw [← Category.assoc,
          coefficientBarι_comp_coefficientBarLocalizationObjIso_inv]
        rw [← Category.assoc, ← (L).map_comp]
        rw [coefficientBarι_degeneracy]
        rw [(L).map_comp]
        rw [Category.assoc,
          map_coefficientBarι_comp_coefficientBarLocalizationObjIso_hom
            S M ((nerve C).σ i F)]
        rfl }
  inv :=
    { app := fun n ↦ (coefficientBarLocalizationObjIso S M n).inv
      w_δ := by
        intro n i
        change (coefficientBarLocalizationObjIso S M (n + 1)).inv ≫
            (L).map (coefficientBarFace M i) =
          coefficientBarFace (M ⋙ L) i ≫
            (coefficientBarLocalizationObjIso S M n).inv
        apply coefficientBar_hom_ext (M ⋙ L)
        intro F
        rw [← Category.assoc,
          coefficientBarι_comp_coefficientBarLocalizationObjIso_inv
            S M F]
        rw [← (L).map_comp]
        rw [coefficientBarι_face]
        rw [(L).map_comp]
        rw [← Category.assoc, coefficientBarι_face]
        rw [Category.assoc,
          coefficientBarι_comp_coefficientBarLocalizationObjIso_inv
            S M ((nerve C).δ i F)]
        rfl
      w_σ := by
        intro n i
        change (coefficientBarLocalizationObjIso S M n).inv ≫
            (L).map (coefficientBarDegeneracy M i) =
          coefficientBarDegeneracy (M ⋙ L) i ≫
            (coefficientBarLocalizationObjIso S M (n + 1)).inv
        apply coefficientBar_hom_ext (M ⋙ L)
        intro F
        rw [← Category.assoc,
          coefficientBarι_comp_coefficientBarLocalizationObjIso_inv S M F]
        rw [← (L).map_comp]
        rw [coefficientBarι_degeneracy]
        rw [(L).map_comp]
        rw [← Category.assoc, coefficientBarι_degeneracy]
        rw [Category.assoc,
          coefficientBarι_comp_coefficientBarLocalizationObjIso_inv
            S M ((nerve C).σ i F)]
        rfl }
  hom_inv_id := by
    apply SimplicialObject.Data.Hom.ext
    intro n
    exact (coefficientBarLocalizationObjIso S M n).hom_inv_id
  inv_hom_id := by
    apply SimplicialObject.Data.Hom.ext
    intro n
    exact (coefficientBarLocalizationObjIso S M n).inv_hom_id

/-- Localization of a coefficient bar is canonically isomorphic to the bar
of the objectwise-localized coefficient system. -/
noncomputable def coefficientBarLocalizationSimplicialIso :
    coefficientBarSimplicial M ⋙ L ≅
      coefficientBarSimplicial (M ⋙ L) :=
  SimplicialObject.Data.toSimplicialObject_mapObjIso L
      (coefficientBarData M) ≪≫
    (SimplicialObject.Data.toSimplicialFunctor
      (C := ModuleCat.{u} (Localization S))).mapIso
        (coefficientBarLocalizationDataIso S M)

/-- The alternating-face complex of the localized coefficient bar is the
localization of the alternating-face coefficient-bar complex.  In
particular, the signs in the differential are transported by the standard
additive-functor comparison. -/
noncomputable def coefficientBarComplexLocalizationIso :
    ((L).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (coefficientBarComplex M) ≅
      coefficientBarComplex (M ⋙ L) :=
  (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      L).app (coefficientBarSimplicial M) ≪≫
    (AlgebraicTopology.alternatingFaceMapComplex
      (ModuleCat.{u} (Localization S))).mapIso
        (coefficientBarLocalizationSimplicialIso S M)

/-- Localization of the normalized coefficient-bar complex is homotopy
equivalent to the normalized bar complex of the localized coefficients.

The comparison passes through alternating-face complexes: map the source
Dold--Kan equivalence through localization, use
`coefficientBarComplexLocalizationIso`, and then use the inverse target
Dold--Kan equivalence. -/
noncomputable def normalizedCoefficientBarLocalizationHomotopyEquiv :
    HomotopyEquiv
      (((L).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (normalizedCoefficientBarComplex M))
      (normalizedCoefficientBarComplex (M ⋙ L)) :=
  ((L).mapHomotopyEquiv
      (AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
          (Y := coefficientBarSimplicial M))).trans
    ((HomotopyEquiv.ofIso (coefficientBarComplexLocalizationIso S M)).trans
      (AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
          (Y := coefficientBarSimplicial (M ⋙ L))).symm)

/-- Localization commutes with category homology with coefficients. -/
noncomputable def homologyWithCoefficientsLocalizationIso (n : ℕ) :
    (L).obj (homologyWithCoefficients M n) ≅
      homologyWithCoefficients (M ⋙ L) n :=
  ((HomologicalComplex.mapHomologyFunctorIso n L).app
      (normalizedCoefficientBarComplex M)).symm ≪≫
    (normalizedCoefficientBarLocalizationHomotopyEquiv S M).toHomologyIso n

end CategoryTheory.CategoryHomology

end
