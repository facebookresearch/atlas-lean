/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.AugmentationExact
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Abelian.LeftDerived

/-!
# The enveloping Chevalley–Eilenberg projective resolution

Let `R` be a commutative ring and `L` an `R`-Lie algebra whose underlying `R`-module is free.
The enveloping Chevalley–Eilenberg complex consists of projective `U_R(L)`-modules, and its
canonical augmentation to the trivial enveloping module is a quasi-isomorphism. It therefore
defines a projective resolution of that trivial module.

The resolution is chain homotopy equivalent to every other projective resolution of the same
target. For an additive functor from the enveloping-module category to an abelian category,
homology of the mapped complex computes the corresponding left-derived functors on the trivial
module. The target category and morphism universes are independent.

Reference: Weibel, *An Introduction to Homological Algebra*, Chapter 7.
-/

@[expose] public section

noncomputable section

universe u v a c

open CategoryTheory CategoryTheory.Limits

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- The augmentation quasi-isomorphism for a free underlying Lie module.

If `Module.Free R L`, the enveloping Chevalley–Eilenberg augmentation to the trivial module is
a quasi-isomorphism in every connective degree. -/
theorem envelopingAugmentation_quasiIso_of_free [Module.Free R L] :
    QuasiIso (envelopingAugmentation R L) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso
          (S₂ := envelopingAugmentationShortComplex R L) ?_).mpr
          ⟨envelopingAugmentationShortComplex_exact R L, inferInstance⟩
        refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
        · rfl
        · change 𝟙 ((envelopingComplex R L).X 0) ≫
            ModuleCat.ofHom (X := (envelopingComplex R L).X 0)
              (Y := envelopingTrivialObject R L) (envelopingAugmentationComponent R L) =
              (envelopingAugmentation R L).f 0 ≫ 𝟙 (envelopingTrivialObject R L)
          exact (Category.id_comp _).trans
            ((envelopingAugmentation_f_zero R L).symm.trans (Category.comp_id _).symm)
      all_goals rfl
  | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact envelopingComplex_exactAt_succ R L n
      · exact ChainComplex.exactAt_succ_single_obj _ _

/-- The enveloping projective resolution of the trivial module.

For `Module.Free R L`, this projective resolution has the enveloping Chevalley–Eilenberg
complex and its canonical augmentation to the trivial `U_R(L)`-module. -/
def envelopingProjectiveResolution [Module.Free R L] :
    ProjectiveResolution (envelopingTrivialObject R L) where
  complex := envelopingComplex R L
  projective := fun n => inferInstance
  π := envelopingAugmentation R L
  quasiIso := envelopingAugmentation_quasiIso_of_free R L

/-- The chain complex of the enveloping projective resolution.

The underlying complex of this resolution is the enveloping Chevalley–Eilenberg complex. -/
@[simp]
theorem envelopingProjectiveResolution_complex [Module.Free R L] :
    (envelopingProjectiveResolution R L).complex = envelopingComplex R L := rfl

/-- The augmentation of the enveloping projective resolution.

The resolution augmentation is the canonical enveloping Chevalley–Eilenberg augmentation. -/
@[simp]
theorem envelopingProjectiveResolution_π [Module.Free R L] :
    (envelopingProjectiveResolution R L).π = envelopingAugmentation R L := rfl

/-- The homotopy comparison with another enveloping resolution.

For any projective resolution `Q` of the trivial `U_R(L)`-module, the enveloping
Chevalley–Eilenberg complex is chain homotopy equivalent to `Q.complex`, assuming `Module.Free
R L`. -/
def envelopingResolutionHomotopyEquiv [Module.Free R L]
    (Q : ProjectiveResolution (envelopingTrivialObject R L)) :
    HomotopyEquiv (envelopingComplex R L) Q.complex :=
  ProjectiveResolution.homotopyEquiv (envelopingProjectiveResolution R L) Q

section DerivedComparison

variable [Module.Free R L] {D : Type a} [Category.{c} D] [Abelian D]

/-- The left-derived comparison for mapped enveloping chains.

If `Module.Free R L` and `F` is an additive functor to an abelian category, the degree-`n`
homology of `F` applied to the enveloping chain complex is isomorphic to the degree-`n` left-
derived value of `F` on the trivial module. -/
def envelopingHomologyIsoLeftDerived (F : ModuleCat.{max u v} U ⥤ D) [F.Additive] (n : ℕ) :
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (envelopingComplex R L)).homology n) ≅
      (F.leftDerived n).obj (envelopingTrivialObject R L) :=
  ((envelopingProjectiveResolution R L).isoLeftDerivedObj F n).symm

end DerivedComparison

end ChevalleyEilenberg
