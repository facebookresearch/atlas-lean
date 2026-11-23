/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.StackChowGroups
import MathlibExt.AlgebraicGeometry.GeometricChowOperators

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

/-- The total-space comparison of a pulled-back bundle lies over the given 2-cell: projected to
affine points of the base, its component is pinned by the `overBase` comparisons and the inverse of
`commutes` (so it cannot hide an automorphism of a stabilizer). -/
example {T X : Stack S} {p : StackHom T X} {E : VectorBundle X} (P : BundlePullback p E)
    (b : StackAffineModules.AffinePoint P.bundle.total) :
    ((sectionForget E.module.val).map (P.normalized.hom.app b)).hom.base =
      ((affineMap p).map (P.bundle.overBase.hom.app b)).hom.base ≫
        (P.commutes.pointInv b).hom.base ≫
          (E.overBase.inv.app ((affineMap P.map).obj b)).hom.base := by
  rw [P.based b]; rfl

/-- The inverse cell of a modification is over the identity of the base scheme. -/
example {X Y : Stack S} {p q : StackHom X Y} (e : TwoIso p q)
    (a : StackAffineModules.AffinePoint X) :
    (e.pointInv a).hom.base = 𝟙 a.obj.base := rfl

/-- The same holds for every bundle map over the identity. -/
example {X : Stack S} {F E : VectorBundle X} (f : BundleMap F E)
    (b : StackAffineModules.AffinePoint F.total) :
    (sectionForget E.module.val).map (f.normalized.hom.app b) =
      F.overBase.hom.app b ≫ f.overBase.pointInv b ≫
        E.overBase.inv.app ((affineMap f.total).obj b) :=
  f.based b

/-- Two component-transition providers for the same restricted data have the same push, so the
stage colimit does not depend on the provider. -/
example {scope : Stack S → Prop} {D : StackCycleRelations.CycleConstructionData S scope}
    {B : BundleTransitions D} {R : RestrictedBundleSystem D} {I : RestrictedComparison D B R}
    {P : RestrictedProjectiveSystem D B R} (C C' : ComponentTransitions D B R I P) (Y : Stack S)
    (A A' : ProjectiveStage (scope := scope) Y) (g : ProjectiveArrow A A') (d : ℤ)
    (z : BundleChowGroup D B A.source A.inScope d) :
    C.push Y A A' g d z = C'.push Y A A' g d z := by
  rw [C.push_eq_of_iota C' Y A A' g d]

/-- The flat pullback of Chow groups is only available for flat maps of pure relative dimension. -/
example (X Y : MathlibExt.AlgebraicGeometry.GeometricChow.ComplexScheme) [IsNoetherian X.left] [IsNoetherian Y.left]
    (f : Y ⟶ X) (r : ℕ) (D : MathlibExt.AlgebraicGeometry.GeometricChowOperators.FlatCycleDescent
      X Y f r) : Flat f.left := D.flat

end StackChowGroupsTest
