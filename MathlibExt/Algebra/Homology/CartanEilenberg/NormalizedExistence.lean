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

Let C be abelian and L a nonnegative chain complex. For specified boundary and homology
projective resolutions, replace every endpoint resolution P by P.zeroNormalized, using the
degree-zero resolution when the resolved object is zero. The two horseshoe constructions give
normalized Cartan–Eilenberg data.

Every endpoint normalization is homotopy equivalent to its original resolution, and the forward
maps preserve augmentation. Whenever Lⱼ is zero, its entire normalized resolution column is zero
in every resolution degree, including zero terms inside the support of L.

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

/-- Let C be abelian and L a nonnegative chain complex. Let PBⱼ and PHⱼ be specified projective
resolutions of its outgoing boundaries and homology objects. Normalize each endpoint by the
specific operation P.zeroNormalized, replacing it by the degree-zero resolution when its
resolved object is zero. The two horseshoes on these normalized endpoints define a
Cartan–Eilenberg resolution of L, reusing the first cycles resolution as the second horseshoe's
left endpoint. -/
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

/-- Let C be abelian with projective resolutions for every object, and L a nonnegative chain
complex. The globally chosen boundary and homology resolutions, each replaced by its
zeroNormalized resolution at zero objects, give the chosen normalized Cartan–Eilenberg
resolution of L. -/
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

/-- Let C be abelian with projective resolutions for every object, and L a nonnegative chain
complex. For j ∈ ℕ, let Z be the outgoing boundary of L in degree j and PBⱼ the projective
resolution of Z used by the ordinary chosen resolution. The normalized boundary resolution is
PBⱼ.zeroNormalized, and its complex is homotopy equivalent to PBⱼ.complex. -/
noncomputable def ofNormalizedBoundaryHomotopyEquiv
    [HasProjectiveResolutions C] (L : ChainComplex C ℕ) (j : ℕ) :
    HomotopyEquiv ((ofNormalized L).boundaryResolution j).complex
      ((of L).boundaryResolution j).complex :=
  ProjectiveResolution.homotopyEquiv _ _

/-- Let C be abelian with projective resolutions for every object, and L a nonnegative chain
complex. For the outgoing boundary object Z in degree j, let PBⱼ resolve Z and let h :
PBⱼ.zeroNormalized.complex → PBⱼ.complex be the normalization homotopy equivalence's forward
map. It satisfies h ≫ π_PB=π_normalized, preserving the actual augmentations to Z[0]. -/
@[reassoc]
theorem ofNormalizedBoundaryHomotopyEquiv_hom_π
    [HasProjectiveResolutions C] (L : ChainComplex C ℕ) (j : ℕ) :
    (ofNormalizedBoundaryHomotopyEquiv L j).hom ≫
        ((of L).boundaryResolution j).π =
      ((ofNormalized L).boundaryResolution j).π :=
  ProjectiveResolution.homotopyEquiv_hom_π _ _

/-- Let C be abelian with projective resolutions for every object, and L a nonnegative chain
complex. For j ∈ ℕ, let Z=Hⱼ(L) and let PHⱼ be its chosen projective resolution. The normalized
homology endpoint is PHⱼ.zeroNormalized, whose complex is homotopy equivalent to PHⱼ.complex. -/
noncomputable def ofNormalizedHomologyHomotopyEquiv
    [HasProjectiveResolutions C] (L : ChainComplex C ℕ) (j : ℕ) :
    HomotopyEquiv ((ofNormalized L).homologyResolution j).complex
      ((of L).homologyResolution j).complex :=
  ProjectiveResolution.homotopyEquiv _ _

/-- Let C be abelian with projective resolutions for every object, and L a nonnegative chain
complex. For Z=Hⱼ(L), let PHⱼ resolve Z and h : PHⱼ.zeroNormalized.complex → PHⱼ.complex be the
forward normalization equivalence. Then h ≫ π_PH=π_normalized as augmentations to Z[0]. -/
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

/-- Let C be abelian and L a nonnegative chain complex. Let PBⱼ and PHⱼ be specified projective
resolutions of its outgoing boundaries and homology objects. Normalize each endpoint by the
specific operation P.zeroNormalized, replacing it by the degree-zero resolution when its
resolved object is zero. If Lⱼ is a zero object, every resolution-degree-a term of the
normalized term resolution of Lⱼ is a zero object, for all j,a ∈ ℕ. This includes internal zero
terms of L. -/
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

/-- Let C be abelian and L a nonnegative chain complex. Let PBⱼ and PHⱼ be specified projective
resolutions of its outgoing boundaries and homology objects. Normalize each endpoint by the
specific operation P.zeroNormalized, replacing it by the degree-zero resolution when its
resolved object is zero. If Lⱼ is zero, the normalized Cartan–Eilenberg bicomplex entry (a,j) is
zero for every resolution degree a ∈ ℕ. -/
theorem ofResolutionsNormalized_bicomplex_X_isZero_of_isZero_X
    (L : ChainComplex C ℕ)
    (PB : ∀ j : ℕ, ProjectiveResolution (L.boundaryFrom j))
    (PH : ∀ j : ℕ, ProjectiveResolution (L.homology j))
    (a j : ℕ) (hX : IsZero (L.X j)) :
    IsZero ((((ofResolutionsNormalized L PB PH).bicomplex.X a).X j)) := by
  change IsZero (((ofResolutionsNormalized L PB PH).termResolution j).complex.X a)
  exact ofResolutionsNormalized_termResolution_X_isZero_of_isZero_X
    L PB PH j a hX

/-- Let C be abelian with projective resolutions for every object, and L a nonnegative chain
complex. If Lⱼ is a zero object, the term-resolution column of the chosen normalized
Cartan–Eilenberg resolution is zero in every resolution degree a. -/
theorem ofNormalized_termResolution_X_isZero_of_isZero_X
    [HasProjectiveResolutions C] (L : ChainComplex C ℕ)
    (j a : ℕ) (hX : IsZero (L.X j)) :
    IsZero (((ofNormalized L).termResolution j).complex.X a) :=
  ofResolutionsNormalized_termResolution_X_isZero_of_isZero_X L _ _ j a hX

/-- Let C be abelian with projective resolutions for every object, and L a nonnegative chain
complex. For all a,j ∈ ℕ with Lⱼ zero, the entry (a,j) of the chosen normalized Cartan–Eilenberg
bicomplex is a zero object. -/
theorem ofNormalized_bicomplex_X_isZero_of_isZero_X
    [HasProjectiveResolutions C] (L : ChainComplex C ℕ)
    (a j : ℕ) (hX : IsZero (L.X j)) :
    IsZero ((((ofNormalized L).bicomplex.X a).X j)) :=
  ofResolutionsNormalized_bicomplex_X_isZero_of_isZero_X L _ _ a j hX

end CartanEilenbergResolution

end HomologicalComplex

end
