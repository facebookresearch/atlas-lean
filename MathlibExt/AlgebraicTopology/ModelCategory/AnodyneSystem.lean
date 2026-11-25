/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorialCylinder

/-!
# Anodyne systems for exact functorial cylinders

An anodyne system records a small monic generating family and the endpoint
and boundary corner conditions for the native exact precylinder. The
generating-family size and the preserved colimit size are the same explicit
universe. All corner maps are the maps from the specified pushouts.

The interface applies to categories with binary coproducts and pushouts.
Monicity of the anodyne class is recorded explicitly. In a presheaf category,
it follows from the generating-family condition and the monomorphism lifting
system. This is the datum of Cisinski, Higher Categories and Homotopical
Algebra, Definition 2.4.11 (July 30, 2026 version).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomotopicalAlgebra.Precylinder

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]

/-- An exact cylinder with a small monic generating family and both anodyne
corner axioms. Monicity is explicit for the general categorical interface. -/
class IsAnodyneSystem (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
    (An : MorphismProperty C) : Prop where
  /-- Every anodyne map is a monomorphism. -/
  le_monomorphisms : An ≤ MorphismProperty.monomorphisms C
  /-- An0: a small monic family generates the class by double orthogonality. -/
  exists_generators : ∃ (ι : Type w) (X Y : ι → C) (f : ∀ j, X j ⟶ Y j),
    (∀ j, Mono (f j)) ∧ An = (MorphismProperty.ofHoms f).rlp.llp
  /-- An1: endpoint corners of monomorphisms are anodyne. -/
  endpoint_corner {X Y : C} (i : X ⟶ Y) [Mono i] (ε : Fin 2) :
    An (P.endpointCorner i ε)
  /-- An2: boundary corners of anodyne maps are anodyne. -/
  boundary_corner {X Y : C} (i : X ⟶ Y) (hi : An i) : An (P.boundaryCorner i)

namespace IsAnodyneSystem

/-- The same small generating family also specifies the right lifting class. -/
lemma exists_generators_rlp_eq (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
    (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An] :
    ∃ (ι : Type w) (X Y : ι → C) (f : ∀ j, X j ⟶ Y j),
      (∀ j, Mono (f j)) ∧ An = (MorphismProperty.ofHoms f).rlp.llp ∧
        An.rlp = (MorphismProperty.ofHoms f).rlp := by
  obtain ⟨ι, X, Y, f, hf, hAn⟩ := exists_generators (P := P) (An := An)
  refine ⟨ι, X, Y, f, hf, hAn, ?_⟩
  rw [hAn, MorphismProperty.rlp_llp_rlp]

/-- An anodyne class is fixed by left orthogonality after right orthogonality. -/
lemma llp_rlp_eq (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
    (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An] : An.rlp.llp = An := by
  obtain ⟨ι, X, Y, f, _, hAn⟩ := exists_generators (P := P) (An := An)
  rw [hAn, MorphismProperty.rlp_llp_rlp]

end IsAnodyneSystem

end HomotopicalAlgebra.Precylinder
