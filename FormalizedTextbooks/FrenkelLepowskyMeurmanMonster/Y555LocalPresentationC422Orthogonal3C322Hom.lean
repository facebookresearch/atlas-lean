/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine linear eight-dimensional lift of the original C322 source parabolic. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3C322Data

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Original C322 source letters interpreted as the actual eight-dimensional reflections. -/
def y422Orthogonal3C322Generator (i : Fin 8) : Matrix.GeneralLinearGroup (Fin 8) (ZMod 3) :=
  y422Orthogonal3Generator (y422C322Letter i)

/-- Every original C322 relation holds in its actual linear eight-dimensional lift. -/
theorem y422Orthogonal3C322Relations_valid (r : FreeGroup (Fin 8)) (hr : r ∈ y322Relations) :
    FreeGroup.lift y422Orthogonal3C322Generator r = 1 := by
  rcases hr with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩ | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of, y422Orthogonal3C322Generator] using
      y422Orthogonal3Generator_square (y422C322Letter v)
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of, y422Orthogonal3C322Generator,
      y422C322Letter_vertex, y444Adjacent, y444C322Vertex_embed] using
      y422Orthogonal3Generator_coxeter (y422C322Letter u) (y422C322Letter v)
        (fun h => huv (y422C322Letter_injective h))
  · rw [map_pow]
    apply Units.ext
    have hs : (FreeGroup.lift y422Orthogonal3C322Generator y322Spider).val =
        y422Orthogonal3Spider := by
      simp [y322Spider, y422Orthogonal3C322Generator, y422C322Letter,
        y422Orthogonal3Spider, map_mul, FreeGroup.lift_apply_of, Units.val_mul]
      rfl
    change (FreeGroup.lift y422Orthogonal3C322Generator y322Spider).val ^ 10 = 1
    rw [hs]
    exact y422Orthogonal3Spider_tenth

/-- The genuine linear eight-dimensional homomorphism of the original C322 source. -/
def y422Orthogonal3C322Hom : Y322Presentation →* Matrix.GeneralLinearGroup (Fin 8) (ZMod 3) :=
  PresentedGroup.toGroup y422Orthogonal3C322Relations_valid

/-- Every original source generator retains its exact declared eight-dimensional reflection. -/
@[simp] theorem y422Orthogonal3C322Hom_generator (i : Fin 8) :
    y422Orthogonal3C322Hom (PresentedGroup.of i) = y422Orthogonal3C322Generator i :=
  PresentedGroup.toGroup.of y422Orthogonal3C322Relations_valid

/-- The quotient composed with the actual linear hom is the exact original-source lift. -/
theorem y422Orthogonal3C322Hom_quotient :
    y422Orthogonal3C322Hom.comp (PresentedGroup.mk y322Relations) =
      FreeGroup.lift y422Orthogonal3C322Generator := by
  apply FreeGroup.ext_hom
  intro i
  simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
  exact y422Orthogonal3C322Hom_generator i

/-- The projective parabolic inclusion equals projection of the genuine linear source lift. -/
theorem y422Orthogonal3C322Hom_projective :
    y422Orthogonal3ProjectiveHom.comp y422C322Hom =
      Matrix.ProjGenLinGroup.mk.comp y422Orthogonal3C322Hom := by
  apply PresentedGroup.ext
  intro i
  simp only [MonoidHom.comp_apply, y422C322Hom_generator,
    y422Orthogonal3ProjectiveHom_generator, y422Orthogonal3C322Hom_generator]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
