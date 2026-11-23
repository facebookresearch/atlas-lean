/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.StackChowGroups

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.StackChowGroups AlgebraicGeometry.StackCycleGeometry
open AlgebraicGeometry.StackFibreModels AlgebraicGeometry.StackVectorBundles

namespace StackChowGroupsTest

section Colimits

variable {I : Type} (G : I → Type) [∀ i, AddCommGroup (G i)] (A : I → I → Type)
  (t : ∀ {i j}, A i j → G i →+ G j)

/-- Every arrow of the diagram identifies a class with its transition, in this direction. -/
example {i j : I} (a : A i j) (x : G i) :
    colimitClass G A t j (t a x) = colimitClass G A t i x :=
  QuotientAddGroup.eq_iff_sub_mem.mpr (AddSubgroup.subset_closure ⟨i, j, a, x, rfl⟩)

/-- Classes are additive. -/
example (i : I) (x y : G i) :
    colimitClass G A t i (x + y) = colimitClass G A t i x + colimitClass G A t i y :=
  map_add _ _ _

end Colimits

variable {S : Scheme.{0}}

/-- A projective atlas lift has a 2-Cartesian square: every object of the fibre category has a
unique map to the square's own object. An étale self-cover of the atlas would fail this. -/
example {T X : Stack S} {p : StackHom T X} {a : CycleAtlas X} (L : ProjectiveAtlasLift p a)
    (q : FibreCategory p a.atlas.U a.atlas.point) :
    Subsingleton (q ⟶ CostructuredArrow.mk (S := totalMap p) (T := point a.atlas.U a.atlas.point)
      (Y := point L.atlas.atlas.U L.atlas.atlas.point)
      (⟨L.map, L.pointIso.hom⟩ : (totalMap p).obj (point L.atlas.atlas.U L.atlas.atlas.point) ⟶
        point a.atlas.U a.atlas.point)) :=
  ⟨fun f g ↦ L.universal.hom_ext f g⟩

/-- The sections of a pulled-back bundle are identified linearly with the pulled sections, so
the zero section goes to the zero section (a translation of a trivial line is excluded). -/
example {T X : Stack S} {p : StackHom T X} {E : VectorBundle X} (P : BundlePullback p E)
    (b : (StackAffineModules.AffinePoint T)ᵒᵖ) :
    P.sections.hom.app b 0 = 0 :=
  map_zero _

example {T X : Stack S} {p : StackHom T X} {E : VectorBundle X} (P : BundlePullback p E)
    (b : (StackAffineModules.AffinePoint T)ᵒᵖ) (m n : P.bundle.module.val.presheaf.obj b) :
    P.sections.hom.app b (m + n) = P.sections.hom.app b m + P.sections.hom.app b n :=
  map_add _ _ _

end StackChowGroupsTest
