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

namespace AlgebraicGeometry.Scheme.Hom

-- `exactSource` consumer with the original binders: the presheaf of
-- relative differentials is pointwise the Kähler differential module.
theorem exactSource {A : Type u} [CommRing A] {X : Scheme.{u}}
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

-- The top exterior power sheaf exists for every degree.
example {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ) : Nonempty X.Modules :=
  ⟨f.topDifferentials d⟩

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
