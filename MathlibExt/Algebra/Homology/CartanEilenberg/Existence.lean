/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module


public import MathlibExt.Algebra.Homology.CartanEilenberg.Basic

/-!
# Existence of Cartan–Eilenberg resolution data

Let C be an abelian category in which every object has a projective resolution. Every
nonnegative chain complex L admits Cartan–Eilenberg resolution data: chosen boundary and
homology resolutions and the two compatible horseshoes resolving cycles and terms.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CartanEilenbergResolution

/-- Let C be abelian and assume every object of C has a projective resolution. For each ℕ-indexed
chain complex L, the chosen boundary and homology resolutions, followed by the two horseshoe
constructions, define a Cartan–Eilenberg resolution of L. -/
noncomputable def of [HasProjectiveResolutions C]
    (L : ChainComplex C ℕ) : CartanEilenbergResolution L :=
  ofResolutions L
    (fun j : ℕ =>
      (CategoryTheory.projectiveResolution (L.boundaryFrom j) :
        ProjectiveResolution (L.boundaryFrom j)))
    (fun j : ℕ =>
      (CategoryTheory.projectiveResolution (L.homology j) :
        ProjectiveResolution (L.homology j)))

@[simp]
theorem of_boundaryResolution [HasProjectiveResolutions C]
    (L : ChainComplex C ℕ) (j : ℕ) :
    (of L).boundaryResolution j =
      CategoryTheory.projectiveResolution (L.boundaryFrom j) := by
  simp [of]

@[simp]
theorem of_homologyResolution [HasProjectiveResolutions C]
    (L : ChainComplex C ℕ) (j : ℕ) :
    (of L).homologyResolution j =
      CategoryTheory.projectiveResolution (L.homology j) := by
  simp [of]

/-- Let C be abelian with projective resolutions for all objects. Every nonnegative chain complex L
has Cartan–Eilenberg resolution data; equivalently the type of such resolution data is nonempty. -/
theorem nonempty [HasProjectiveResolutions C]
    (L : ChainComplex C ℕ) :
    Nonempty (CartanEilenbergResolution L) :=
  ⟨of L⟩

end CartanEilenbergResolution

end HomologicalComplex

end
