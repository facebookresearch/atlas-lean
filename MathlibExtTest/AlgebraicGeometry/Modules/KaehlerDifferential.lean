/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Modules.KaehlerDifferential

@[expose] public section

universe u

open CategoryTheory Opposite

private local instance {X : AlgebraicGeometry.Scheme.{u}} (U : (X.Opens)ᵒᵖ) :
    CommRing ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U) :=
  inferInstanceAs (CommRing (X.sheaf.obj.obj U))

namespace AlgebraicGeometry.Scheme.Hom

-- `exactSource` consumer with the original binders: the presheaf of
-- relative differentials is pointwise the Kähler differential module.
private theorem exactSource {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (U : (X.Opens)ᵒᵖ) :
    f.kaehlerPresheaf.obj U =
      CommRingCat.KaehlerDifferential (f.constToPresheaf.app U) :=
  f.kaehlerPresheaf_obj U

-- Sections comparison is additive.
example {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (U : X.Opens)
    (s t : f.kaehlerPresheaf.obj (op U)) :
    f.kaehlerToSections U (s + t) =
      f.kaehlerToSections U s + f.kaehlerToSections U t :=
  f.kaehlerToSections_add U s t

-- The comparison functions are the linear maps, so there is one implementation of each.
example {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (U : X.Opens) :
    f.kaehlerToSections U = ⇑(f.kaehlerToSectionsₗ U) := rfl

example {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ) (U : X.Opens) :
    f.topToSections d U = ⇑(f.topToSectionsₗ d U) := rfl

-- On a wedge `ω₁ ∧ ⋯ ∧ ω_d`, `topToSectionsₗ` sends each `ωᵢ` to the Kähler sheaf and then applies
-- the sheafification unit of the exterior power of `kaehler`.
example {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ) (U : X.Opens)
    (m : Fin d → f.kaehlerPresheaf.obj (op U)) :
    f.topToSectionsₗ d U (exteriorPower.ιMulti _ d m) =
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower X d).obj f.kaehler.val)).app (op U)).hom
        (exteriorPower.ιMulti _ d fun i => f.kaehlerToSections U (m i)) := by
  change (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      ((Scheme.Modules.presheafExteriorPower X d).obj f.kaehler.val)).app (op U)).hom
      (exteriorPower.map d (f.kaehlerToSectionsₗ U) (exteriorPower.ιMulti _ d m)) = _
  rw [exteriorPower.map_apply_ιMulti]
  rfl

-- The top power sheaf is the sheafified sectionwise exterior power of the Kähler sheaf.
example {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ) :
    f.topDifferentials d = (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModules.extPow (O := X.sheaf.obj) d f.kaehler.val) := rfl

-- The scheme-level functor acts on morphisms through `PresheafOfModules.exteriorPowerMap`.
example {X : Scheme.{u}} (d : ℕ) {M N : X.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.exteriorPower X d).map φ =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.exteriorPowerMap (R := X.sheaf.obj) d
          ((Scheme.Modules.toPresheafOfModules X).map φ)) := rfl

-- Restricting a wedge of differentials in the top power presheaf restricts each factor.
example {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ) {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V)
    (m : Fin d → f.kaehlerPresheaf.obj U) :
    (f.topPresheaf d).map i (exteriorPower.ιMulti _ d m) =
      exteriorPower.ιMulti _ d fun j => f.kaehlerPresheaf.map i (m j) :=
  PresheafOfModules.extPow_map_ιMulti d _ i m

end AlgebraicGeometry.Scheme.Hom

-- Boundary example: for `Spec A[X] ⟶ Spec A` with `A` nontrivial, the
-- presheaf of differentials on global sections is nontrivial; this uses
-- that the module of polynomial differentials is nontrivial.
example : Nontrivial
    (let f : AlgebraicGeometry.Spec (CommRingCat.of (Polynomial ℚ)) ⟶
        AlgebraicGeometry.Spec (CommRingCat.of ℚ) :=
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℚ (Polynomial ℚ)))
    (f.kaehlerPresheaf.obj (op ⊤))) :=
  AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_nontrivial_polynomial ℚ

-- Degree `1`: the first exterior power of those global differentials, the global sections of
-- `topPresheaf 1`, is nontrivial too.
example : Nontrivial
    (let f : AlgebraicGeometry.Spec (CommRingCat.of (Polynomial ℚ)) ⟶
        AlgebraicGeometry.Spec (CommRingCat.of ℚ) :=
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℚ (Polynomial ℚ)))
    ((f.topPresheaf 1).obj (op ⊤))) := by
  let f : AlgebraicGeometry.Spec (CommRingCat.of (Polynomial ℚ)) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of ℚ) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℚ (Polynomial ℚ)))
  have := AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_nontrivial_polynomial ℚ
  exact (exteriorPower.oneEquiv _ (f.kaehlerPresheaf.obj (op ⊤))).toEquiv.nontrivial
