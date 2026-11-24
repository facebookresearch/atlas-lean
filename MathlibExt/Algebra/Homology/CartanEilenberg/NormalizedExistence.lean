/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ProjectiveResolutionNormalization
public import MathlibExt.Algebra.Homology.CartanEilenberg.Existence
public import MathlibExt.Algebra.Homology.CartanEilenberg.Bicomplex

/-!
# Zero-normalized Cartan–Eilenberg resolutions

A Cartan–Eilenberg resolution can be chosen so that every zero term of the original complex
has a zero resolution column. Normalize a projective resolution to `ProjectiveResolution.self`
when its resolved object is zero, and use the horseshoe constructions with those normalized
endpoints. Each normalized endpoint resolution is homotopy equivalent to the given resolution.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Definition 5.7.1 and Lemma 5.7.2.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits



namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CartanEilenbergResolution

/-- Cartan--Eilenberg resolution data from supplied endpoint resolutions,
using the trivial resolution whenever a boundary or homology object is zero. -/
noncomputable def ofResolutionsNormalized (L : ChainComplex C ℕ)
    (PB : ∀ j : ℕ, ProjectiveResolution (L.boundaryFrom j))
    (PH : ∀ j : ℕ, ProjectiveResolution (L.homology j)) :
    CartanEilenbergResolution L :=
  ofResolutions L (fun j => (PB j).zeroNormalized)
    (fun j => (PH j).zeroNormalized)

@[simp]
theorem ofResolutionsNormalized_boundaryResolution (L : ChainComplex C ℕ)
    (PB : ∀ j : ℕ, ProjectiveResolution (L.boundaryFrom j))
    (PH : ∀ j : ℕ, ProjectiveResolution (L.homology j)) (j : ℕ) :
    (ofResolutionsNormalized L PB PH).boundaryResolution j =
      (PB j).zeroNormalized :=
  rfl

@[simp]
theorem ofResolutionsNormalized_homologyResolution (L : ChainComplex C ℕ)
    (PB : ∀ j : ℕ, ProjectiveResolution (L.boundaryFrom j))
    (PH : ∀ j : ℕ, ProjectiveResolution (L.homology j)) (j : ℕ) :
    (ofResolutionsNormalized L PB PH).homologyResolution j =
      (PH j).zeroNormalized :=
  rfl

/-- The chosen Cartan--Eilenberg resolution with zero-normalized endpoint
resolutions. -/
noncomputable def ofNormalized [HasProjectiveResolutions C]
    (L : ChainComplex C ℕ) : CartanEilenbergResolution L :=
  ofResolutionsNormalized L
    (fun j => CategoryTheory.projectiveResolution (L.boundaryFrom j))
    (fun j => CategoryTheory.projectiveResolution (L.homology j))

@[simp]
theorem ofNormalized_boundaryResolution [HasProjectiveResolutions C]
    (L : ChainComplex C ℕ) (j : ℕ) :
    (ofNormalized L).boundaryResolution j =
      (CategoryTheory.projectiveResolution (L.boundaryFrom j)).zeroNormalized :=
  rfl

@[simp]
theorem ofNormalized_homologyResolution [HasProjectiveResolutions C]
    (L : ChainComplex C ℕ) (j : ℕ) :
    (ofNormalized L).homologyResolution j =
      (CategoryTheory.projectiveResolution (L.homology j)).zeroNormalized :=
  rfl

/-- The normalized boundary resolution is homotopy equivalent to the boundary
resolution used by `CartanEilenbergResolution.of`. -/
noncomputable def ofNormalizedBoundaryHomotopyEquiv
    [HasProjectiveResolutions C] (L : ChainComplex C ℕ) (j : ℕ) :
    HomotopyEquiv ((ofNormalized L).boundaryResolution j).complex
      ((of L).boundaryResolution j).complex :=
  ProjectiveResolution.homotopyEquiv _ _

/-- The normalized boundary comparison commutes with the augmentations. -/
@[reassoc]
theorem ofNormalizedBoundaryHomotopyEquiv_hom_π
    [HasProjectiveResolutions C] (L : ChainComplex C ℕ) (j : ℕ) :
    (ofNormalizedBoundaryHomotopyEquiv L j).hom ≫
        ((of L).boundaryResolution j).π =
      ((ofNormalized L).boundaryResolution j).π :=
  ProjectiveResolution.homotopyEquiv_hom_π _ _

/-- The normalized homology resolution is homotopy equivalent to the homology
resolution used by `CartanEilenbergResolution.of`. -/
noncomputable def ofNormalizedHomologyHomotopyEquiv
    [HasProjectiveResolutions C] (L : ChainComplex C ℕ) (j : ℕ) :
    HomotopyEquiv ((ofNormalized L).homologyResolution j).complex
      ((of L).homologyResolution j).complex :=
  ProjectiveResolution.homotopyEquiv _ _

/-- The normalized homology comparison commutes with the augmentations. -/
@[reassoc]
theorem ofNormalizedHomologyHomotopyEquiv_hom_π
    [HasProjectiveResolutions C] (L : ChainComplex C ℕ) (j : ℕ) :
    (ofNormalizedHomologyHomotopyEquiv L j).hom ≫
        ((of L).homologyResolution j).π =
      ((ofNormalized L).homologyResolution j).π :=
  ProjectiveResolution.homotopyEquiv_hom_π _ _

private theorem boundaryFrom_isZero_of_isZero_X
    (L : ChainComplex C ℕ) (j : ℕ) (hX : IsZero (L.X j)) :
    IsZero (L.boundaryFrom j) :=
  IsZero.of_epi (factorThruImage (L.dFrom j)) hX

private theorem cycles_isZero_of_isZero_X
    (L : ChainComplex C ℕ) (j : ℕ) (hX : IsZero (L.X j)) :
    IsZero (L.cycles j) :=
  IsZero.of_mono (L.iCycles j) hX

private theorem boundaryFrom_succ_isZero_of_isZero_X
    (L : ChainComplex C ℕ) (j : ℕ) (hX : IsZero (L.X j)) :
    IsZero (L.boundaryFrom (j + 1)) :=
  IsZero.of_mono (L.boundaryToCycles j)
    (cycles_isZero_of_isZero_X L j hX)

private theorem homology_isZero_of_isZero_X
    (L : ChainComplex C ℕ) (j : ℕ) (hX : IsZero (L.X j)) :
    IsZero (L.homology j) :=
  IsZero.of_epi (L.homologyπ j) (cycles_isZero_of_isZero_X L j hX)

/-- Every term of the normalized resolution of `L.X j` is zero whenever the
original term `L.X j` is zero. This applies at internal zero terms as well as
outside a bounded range. -/
theorem ofResolutionsNormalized_termResolution_X_isZero_of_isZero_X
    (L : ChainComplex C ℕ)
    (PB : ∀ j : ℕ, ProjectiveResolution (L.boundaryFrom j))
    (PH : ∀ j : ℕ, ProjectiveResolution (L.homology j))
    (j a : ℕ) (hX : IsZero (L.X j)) :
    IsZero (((ofResolutionsNormalized L PB PH).termResolution j).complex.X a) := by
  let P := ofResolutionsNormalized L PB PH
  have hBj : IsZero ((P.boundaryResolution j).complex.X a) := by
    change IsZero ((PB j).zeroNormalized.complex.X a)
    exact (PB j).zeroNormalized_complex_X_isZero
      (boundaryFrom_isZero_of_isZero_X L j hX) a
  have hBsucc : IsZero ((P.boundaryResolution (j + 1)).complex.X a) := by
    change IsZero ((PB (j + 1)).zeroNormalized.complex.X a)
    exact (PB (j + 1)).zeroNormalized_complex_X_isZero
      (boundaryFrom_succ_isZero_of_isZero_X L j hX) a
  have hHj : IsZero ((P.homologyResolution j).complex.X a) := by
    change IsZero ((PH j).zeroNormalized.complex.X a)
    exact (PH j).zeroNormalized_complex_X_isZero
      (homology_isZero_of_isZero_X L j hX) a
  have hCycles : IsZero ((P.cyclesResolution j).complex.X a) := by
    apply (Iso.isZero_iff ((P.cyclesSpec j).middleXIso a)).2
    rw [biprod_isZero_iff]
    exact ⟨hBsucc, hHj⟩
  apply (Iso.isZero_iff ((P.termSpec j).middleXIso a)).2
  rw [biprod_isZero_iff]
  exact ⟨hCycles, hBj⟩

/-- Every bicomplex object over a zero term of the original complex is zero. -/
theorem ofResolutionsNormalized_bicomplex_X_isZero_of_isZero_X
    (L : ChainComplex C ℕ)
    (PB : ∀ j : ℕ, ProjectiveResolution (L.boundaryFrom j))
    (PH : ∀ j : ℕ, ProjectiveResolution (L.homology j))
    (a j : ℕ) (hX : IsZero (L.X j)) :
    IsZero ((((ofResolutionsNormalized L PB PH).bicomplex.X a).X j)) := by
  change IsZero (((ofResolutionsNormalized L PB PH).termResolution j).complex.X a)
  exact ofResolutionsNormalized_termResolution_X_isZero_of_isZero_X
    L PB PH j a hX

/-- Every term of the chosen normalized resolution column over a zero term
of the original complex is zero. -/
theorem ofNormalized_termResolution_X_isZero_of_isZero_X
    [HasProjectiveResolutions C] (L : ChainComplex C ℕ)
    (j a : ℕ) (hX : IsZero (L.X j)) :
    IsZero (((ofNormalized L).termResolution j).complex.X a) :=
  ofResolutionsNormalized_termResolution_X_isZero_of_isZero_X L _ _ j a hX

/-- The chosen normalized Cartan--Eilenberg bicomplex is zero in every
resolution degree over each zero term of the original complex. -/
theorem ofNormalized_bicomplex_X_isZero_of_isZero_X
    [HasProjectiveResolutions C] (L : ChainComplex C ℕ)
    (a j : ℕ) (hX : IsZero (L.X j)) :
    IsZero ((((ofNormalized L).bicomplex.X a).X j)) :=
  ofResolutionsNormalized_bicomplex_X_isZero_of_isZero_X L _ _ a j hX

end CartanEilenbergResolution

end HomologicalComplex

end
