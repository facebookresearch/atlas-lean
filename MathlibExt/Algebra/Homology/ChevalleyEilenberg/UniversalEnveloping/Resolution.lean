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
# The free enveloping Chevalley–Eilenberg projective resolution

Under `Module.Free R L`, exactness at the augmentation and the filtered
PBW/Koszul boundary construction give a projective resolution of the trivial
enveloping module. Its comparison with any other projective resolution is a
homotopy equivalence.

For an additive functor to an abelian category, the homology of the mapped
complex computes its left-derived functors on the trivial module.
-/

@[expose] public section

noncomputable section

universe u v a c

open CategoryTheory CategoryTheory.Limits

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- The original native enveloping CE augmentation is a quasi-isomorphism
under freeness of the original underlying Lie module. -/
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

/-- The original enveloping CE complex resolves its original trivial
enveloping module. The augmentation is the canonical enveloping augmentation. -/
def envelopingProjectiveResolution [Module.Free R L] :
    ProjectiveResolution (envelopingTrivialObject R L) where
  complex := envelopingComplex R L
  projective := fun n => inferInstance
  π := envelopingAugmentation R L
  quasiIso := envelopingAugmentation_quasiIso_of_free R L

@[simp]
theorem envelopingProjectiveResolution_complex [Module.Free R L] :
    (envelopingProjectiveResolution R L).complex = envelopingComplex R L := rfl

@[simp]
theorem envelopingProjectiveResolution_π [Module.Free R L] :
    (envelopingProjectiveResolution R L).π = envelopingAugmentation R L := rfl

/-- The constructed original CE resolution has the standard native
homotopy comparison with any other projective resolution of the same target. -/
def envelopingResolutionHomotopyEquiv [Module.Free R L]
    (Q : ProjectiveResolution (envelopingTrivialObject R L)) :
    HomotopyEquiv (envelopingComplex R L) Q.complex :=
  ProjectiveResolution.homotopyEquiv (envelopingProjectiveResolution R L) Q

section DerivedComparison

variable [Module.Free R L] {D : Type a} [Category.{c} D] [Abelian D]

/-- The mapped enveloping CE homology computes the ordinary native
left derived functor on the original trivial enveloping module. -/
def envelopingHomologyIsoLeftDerived (F : ModuleCat.{max u v} U ⥤ D) [F.Additive] (n : ℕ) :
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (envelopingComplex R L)).homology n) ≅
      (F.leftDerived n).obj (envelopingTrivialObject R L) :=
  ((envelopingProjectiveResolution R L).isoLeftDerivedObj F n).symm

end DerivedComparison

end ChevalleyEilenberg
