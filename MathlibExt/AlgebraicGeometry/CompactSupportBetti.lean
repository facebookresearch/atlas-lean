/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Topology.Compactness.Compact
public import MathlibExt.AlgebraicGeometry.BettiRealization

@[expose] public noncomputable section

/-!
# Actual compact-support rational Betti complexes

For a rational sheaf, sections with compact support are the submodule of
global sections for which the closure of the nonzero-germ locus is compact.
This construction and its action on morphisms are proved here. Compact-support
cohomology is the right-derived functor of those sections; no arbitrary
homology carrier or unnormalized scalar action is supplied.

Reference: Kashiwara--Schapira, *Sheaves on Manifolds*, §§2.5--3.1.
-/

namespace MathlibExt.AlgebraicGeometry.CompactSupportBetti

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.BettiRealization

attribute [local instance] HasDerivedCategory.standard

variable {Z : TopCat.{0}}

/-- The actual global-section module of a rational sheaf. -/
abbrev GlobalSections (F : RationalSheaf Z) :=
  F.presheaf.obj (op (⊤ : Opens Z))

/-- Points at which the germ of a section is nonzero. -/
def germSupport (F : RationalSheaf Z) (s : GlobalSections F) : Set Z :=
  {x | F.presheaf.germ ⊤ x (by trivial) s ≠ 0}

/-- Sections whose nonzero germs have compact closure. -/
def compactSections (F : RationalSheaf Z) : Submodule ℚ (GlobalSections F) where
  carrier := {s | IsCompact (closure (germSupport F s))}
  zero_mem' := by simp [germSupport]
  add_mem' := by
    intro s t hs ht
    have hsub : germSupport F (s + t) ⊆ germSupport F s ∪ germSupport F t := by
      intro x hx
      by_contra h
      simp only [Set.mem_union, not_or, germSupport, Set.mem_ofPred_eq,
        ne_eq, not_not] at h
      exact hx (by simp [map_add, h.1, h.2])
    apply (hs.union ht).of_isClosed_subset isClosed_closure
    exact (closure_mono hsub).trans closure_union.le
  smul_mem' := by
    intro r s hs
    have hsub : germSupport F (r • s) ⊆ germSupport F s := by
      intro x hx hsx
      exact hx (by simp [map_smul, hsx])
    exact hs.of_isClosed_subset isClosed_closure (closure_mono hsub)

/-- A sheaf morphism cannot enlarge the support of a global section. -/
def compactSectionsMap {F G : RationalSheaf Z} (a : F ⟶ G) :
    compactSections F →ₗ[ℚ] compactSections G where
  toFun s := ⟨a.hom.app (op ⊤) s.1, by
    have hsub : germSupport G (a.hom.app (op ⊤) s.1) ⊆ germSupport F s.1 := by
      intro x hx hsx
      apply hx
      rw [← Presheaf.stalkFunctor_map_germ_apply, hsx]
      exact ((Presheaf.stalkFunctor (ModuleCat ℚ) x).map a.hom).hom.map_zero
    exact s.2.of_isClosed_subset isClosed_closure (closure_mono hsub)⟩
  map_add' s t := by ext; exact map_add _ _ _
  map_smul' r s := by ext; exact map_smul _ _ _

/-- The functor of actual sections with compact support. -/
def sections (Z : TopCat.{0}) : RationalSheaf Z ⥤ ModuleCat.{0} ℚ where
  obj F := ModuleCat.of ℚ (compactSections F)
  map a := ModuleCat.ofHom (compactSectionsMap a)
  map_id F := by ext s; rfl
  map_comp a b := by ext s; rfl

/-- The section functor is additive. -/
instance sections_additive (Z : TopCat.{0}) : (sections Z).Additive where
  map_add := by intro F G a b; ext s; rfl

/-- The actual bounded-below derived compact-support section functor. -/
abbrev derivedSections (Z : TopCat.{0}) :
    DerivedCategory.Plus (RationalSheaf Z) ⥤ DerivedCategory (ModuleCat.{0} ℚ) :=
  (sections Z).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι

/-- Compact-support cohomology with rational coefficients. -/
abbrev Cohomology (Z : TopCat.{0}) (n : ℕ) : ModuleCat.{0} ℚ :=
  ((sections Z).rightDerived n).obj (rationalConstantSheaf Z)

/-- Its rational dual is the coefficient carrier used for Borel--Moore comparison. -/
abbrev DualCohomology (Z : TopCat.{0}) (n : ℕ) := Module.Dual ℚ (Cohomology Z n)

/-- A dualizing complex is characterized by representation of the dual of the
actual derived compact-support section functor. This is a universal property,
not a supplied family of arbitrary homology groups. -/
structure DualizingComplex (Z : TopCat.{0}) where
  /-- The object belongs to the actual derived category of rational sheaves. -/
  obj : RationalDerived Z
  /-- Representation, natural in every bounded-below rational complex. -/
  representation : DerivedCategory.Plus.ι.op ⋙
      (linearYoneda ℚ (RationalDerived Z)).obj obj ≅
    (derivedSections Z).op ⋙
      (linearYoneda ℚ (DerivedCategory (ModuleCat.{0} ℚ))).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{0} ℚ) 0).obj
        (ModuleCat.of ℚ ℚ))

/-- Derived-Hom Borel--Moore homology attached to a characterized dualizing complex. -/
abbrev BorelMoore (Z : TopCat.{0}) (D : DualizingComplex Z) (n : ℤ) : Type 1 :=
  rationalUnit Z ⟶ D.obj⟦-n⟧

end MathlibExt.AlgebraicGeometry.CompactSupportBetti
