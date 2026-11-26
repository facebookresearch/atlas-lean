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
# Projective resolutions transported by flat scalar extension

Let R,S be commutative rings, S an R-algebra flat as an R-module,
and Γ=max(u,v,w). Extension of scalars sends a projective resolution
P of an R-module M in world Γ to a projective resolution of S⊗[R]M
in the S-module category at the same height.

Its complex is the termwise scalar extension of P. Flatness preserves
the augmentation quasi-isomorphism, while the extension/restriction
adjunction preserves projective terms. The ring worlds u,v and the
additional carrier height w are independent.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v w

open scoped ModuleCat.UniverseTensor ChangeOfRings

namespace ModuleCat.UniverseTensor

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/-- For commutative rings R,S with S flat over R and
M∈ModuleCat^Γ(R), a projective resolution P of M maps to
a projective resolution of S⊗[R]M.
Here Γ=max(u,v,w), with independent ring and carrier heights. -/
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

/-- For S flat over the commutative ring R and a projective
resolution P of M at height Γ=max(u,v,w), the complex of
the extended resolution is (S⊗[R]−)(P) term by term.
Its differential and augmentation are the scalar extensions
of those of P. -/
theorem flatScalarExtensionProjectiveResolution_complex
    {M : ModuleCat.{max u v w} R} (P : ProjectiveResolution M) :
    (flatScalarExtensionProjectiveResolution R S P).complex =
      ((extendScalars.{u,v,max u v w} (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex := rfl

end ModuleCat.UniverseTensor
