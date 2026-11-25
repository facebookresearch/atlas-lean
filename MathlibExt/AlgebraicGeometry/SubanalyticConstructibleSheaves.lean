/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SubanalyticCoordinateModels
public import MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Actual finite-rank constructibility on subanalytic partitions

On each original locally closed stratum, the native sheaf pullback is
locally isomorphic to the actual finite-rank constant coefficient sheaf.
Partitions are locally finite and subanalytic in the original coordinate
atlas. Compact constructible generators form a full subcategory of the
same compact-support sheaf category used for Ind.

Source: DK arXiv:1311.2374v2, Sections 2.3--2.4 and 4.9.
Native sheaf pullbacks/constants/Ind lifts: Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SubanalyticConstructibleSheaves

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves SubanalyticCoordinateModels

variable [∀ Z : TopCat.{0}, HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]

def openInclusion (Z : TopCat.{0}) (U : Opens Z) : TopCat.of U ⟶ Z :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Local finite rank is an actual constant-sheaf isomorphism on a neighborhood. -/
def LocallyFiniteRank (Z : TopCat.{0}) (F : OrdinarySheaf ℂ Z) : Prop :=
  ∀ x : Z, ∃ U : Opens Z, x ∈ U ∧ ∃ r : ℕ,
    Nonempty ((TopCat.Sheaf.pullback (ModuleCat.{0} ℂ) (openInclusion Z U)).obj F ≅
      (constantSheaf (Opens.grothendieckTopology (TopCat.of U)) (ModuleCat.{0} ℂ)).obj
        (ModuleCat.of ℂ (Fin r → ℂ)))

variable (n : ℕ) (M : Type) [TopologicalSpace M]
  [ChartedSpace (ComplexCoordinates n) M]

def stratumInclusion (P : SubanalyticPartition n M) (i : P.index) :
    TopCat.of (P.stratum i) ⟶ TopCat.of M :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The original cohomological constructibility condition on actual subanalytic strata. -/
def IsRConstructible (F : OrdinarySheaf ℂ (TopCat.of M)) : Prop :=
  ∃ P : SubanalyticPartition n M, ∀ i : P.index,
    LocallyFiniteRank (TopCat.of (P.stratum i))
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℂ) (stratumInclusion n M P i)).obj F)

def compactSubanalytic : ObjectProperty (OrdinarySheaf ℂ (TopCat.of M)) :=
  fun F => IsCompactSupported ℂ (TopCat.of M) F ∧ IsRConstructible n M F

abbrev CompactSubanalyticSheaf := (compactSubanalytic n M).FullSubcategory

/-- The full native compact inclusion forgets only the verified constructibility proof. -/
def compactSubanalyticToCompact :
    CompactSubanalyticSheaf n M ⥤ CompactSheaf ℂ (TopCat.of M) where
  obj F := ⟨F.obj, F.property.1⟩
  map f := ObjectProperty.homMk f.hom
  map_id F := by apply ObjectProperty.hom_ext; rfl
  map_comp f g := by apply ObjectProperty.hom_ext; rfl

end MathlibExt.AlgebraicGeometry.SubanalyticConstructibleSheaves
