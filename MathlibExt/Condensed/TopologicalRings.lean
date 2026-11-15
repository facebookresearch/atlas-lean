/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Condensed.TopComparison
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# Actual topological condensed rings and their module sheaves

The coefficient ring has C(S,A) as its sections on each compact Hausdorff
space S, with pointwise ring operations and actual continuous precomposition.
Sheaf descent is the existing topological Yoneda descent theorem. Modules
are the native sheaves of modules over this ring, rather than condensed
modules over a constant discrete coefficient ring.

Original adapters to native Mathlib constructions. References:
Clausen--Scholze, *Lectures on Condensed Mathematics*, Lecture II;
Anschuetz--Mann, arXiv:2403.01951v2, Definition 2.1.
-/

@[expose] public noncomputable section

namespace MathlibExt.Condensed.TopologicalRings

open CategoryTheory CategoryTheory.Limits Opposite

variable (A : Type 1) [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A]

/-- The real continuous-function structural ring on compact test spaces. -/
def presheaf : CompHaus.{0}ᵒᵖ ⥤ CommRingCat.{1} where
  obj S := CommRingCat.of C(S.unop, A)
  map f := CommRingCat.ofHom
    { toFun g := g.comp f.unop.hom.hom
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := by ext g x; rfl
  map_comp _ _ := by ext g x; rfl

/-- Actual continuous functions satisfy the native compact descent law. -/
theorem isSheaf : Presheaf.IsSheaf (coherentTopology CompHaus.{0})
    (presheaf A) := by
  let : ReflectsLimitsOfSize.{0, 1} (forget CommRingCat.{1}) :=
    reflectsLimits_of_reflectsIsomorphisms
  have h : Presheaf.IsSheaf (coherentTopology CompHaus.{0})
      (presheaf A ⋙ forget CommRingCat.{1}) := by
    change Presheaf.IsSheaf (coherentTopology CompHaus.{0})
      (ContinuousMap.yonedaPresheaf compHausToTop A)
    exact (TopCat.toCondensedSet (TopCat.of A)).property
  exact Presheaf.isSheaf_of_isSheaf_comp _ _ _ h

/-- The actual condensed topological ring. -/
def ring : Condensed.{0} CommRingCat.{1} := ⟨presheaf A, isSheaf A⟩

/-- Its actual RingCat-valued sheaf, for native module constructions. -/
def ringSheaf : Sheaf (coherentTopology CompHaus.{0}) RingCat.{1} where
  obj := (ring A).obj ⋙ forget₂ CommRingCat.{1} RingCat.{1}
  property := Presheaf.isSheaf_comp_of_isSheaf _ _ _ (ring A).property

/-- Modules over C(-,A), with actual sectionwise scalar actions. -/
abbrev Modules := SheafOfModules (ringSheaf A)

end MathlibExt.Condensed.TopologicalRings
