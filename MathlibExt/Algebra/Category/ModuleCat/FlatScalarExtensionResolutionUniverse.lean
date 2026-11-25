/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.FlatHomology
public import MathlibExt.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import MathlibExt.Algebra.Category.ModuleCat.Monoidal.UniverseCompatibility

/-!
# Genuine projective resolutions under flat scalar extension

The actual extension-of-scalars functor is exact for the original flat
ring map and preserves projectives through its actual adjunction with
restriction of scalars. It therefore sends an original projective
resolution to an actual projective resolution over the scalar algebra.
This supplies the genuine flat base-change Tor comparison.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v w

open scoped ModuleCat.UniverseTensor ChangeOfRings

namespace ModuleCat.UniverseTensor

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/-- Flat scalar extension of the original projective resolution, through
the real scalar-extension adjunction and exact functor. -/
def flatScalarExtensionProjectiveResolution
    {M : ModuleCat.{max u v w} R} (P : ProjectiveResolution M) :
    ProjectiveResolution ((extendScalars.{u,v,max u v w} (algebraMap R S)).obj M) := by
  let F : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} S :=
    extendScalars.{u,v,max u v w} (algebraMap R S)
  let G : ModuleCat.{max u v w} S ⥤ ModuleCat.{max u v w} R :=
    restrictScalars.{max u v w,u,v} (algebraMap R S)
  letI : G.PreservesEpimorphisms :=
    { preserves := fun g _ => (ModuleCat.epi_iff_surjective _).mpr
        ((ModuleCat.epi_iff_surjective g).mp inferInstance) }
  letI : F.PreservesHomology := ModuleCat.preservesHomology_extendScalars_of_flat.{u,v,w} (algebraMap R S) (by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance)
  letI : F.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (extendRestrictScalarsAdj.{max u v w,u,v} (algebraMap R S))
  exact F.mapProjectiveResolution P

/-- The actual scalar-extended resolution uses the original scalar-extension
complex, with no independently chosen replacement resolution. -/
theorem flatScalarExtensionProjectiveResolution_complex
    {M : ModuleCat.{max u v w} R} (P : ProjectiveResolution M) :
    (flatScalarExtensionProjectiveResolution R S P).complex =
      ((extendScalars.{u,v,max u v w} (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex := rfl

end ModuleCat.UniverseTensor
