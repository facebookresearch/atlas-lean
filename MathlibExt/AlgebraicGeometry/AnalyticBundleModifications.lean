/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.UntiltingCartierModels
public import MathlibExt.AlgebraicGeometry.AnalyticBundlePrestackModels

/-!
# Actual punctured bundle comparisons along a Cartier divisor

The puncture is an actual open subspace with exactly the complement of
the actual divisor image. A modification consists of two native
G-torsors and an isomorphism of their actual punctured pullbacks.
Morphisms are equivariant torsor isomorphisms making the punctured
square commute. Both correspondence legs are the actual projections.
The meromorphic condition for the Hecke subcategory is additional.
No unrelated modification groupoid or puncture functor is selected.
Source: Fargues--Scholze, arXiv:2102.13459v4, Sections I.2 and VI.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticBundleModifications

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticTorsorPullbacks AnalyticBundlePrestackModels

variable (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
  (G : Over (Spec (.of E))) [GrpObj G]
  (H : ∀ X : ESpace p E, GroupDescent p E G X)
  (P : PullbackPreservation p E G H)
  {X D : ESpace p E} (d : D ⟶ X)

structure Puncture where
  space : ESpace p E
  map : space ⟶ X
  open_embedding : IsOpenEmbedding map.left.hom.val.base
  stalk_iso : ∀ x, IsIso (map.left.hom.val.stalkMap x)
  complement : Set.range map.left.hom.val.base = (Set.range d.left.hom.val.base)ᶜ

variable (U : Puncture p E d)

structure Modification where
  left : Bundles p E G H X
  right : Bundles p E G H X
  punctured : (bundlePullback p E G H P U.map).obj left ≅
    (bundlePullback p E G H P U.map).obj right

def ModificationHom (M N : Modification p E G H P d U) :=
  {f : (M.left ⟶ N.left) × (M.right ⟶ N.right) //
    (bundlePullback p E G H P U.map).map f.1 ≫ N.punctured.hom =
      M.punctured.hom ≫ (bundlePullback p E G H P U.map).map f.2}

instance : Category (Modification p E G H P d U) where
  Hom := ModificationHom p E G H P d U
  id M := ⟨(𝟙 M.left, 𝟙 M.right), by simp⟩
  comp {M N Q} f g := ⟨(f.val.1 ≫ g.val.1, f.val.2 ≫ g.val.2), by
    rw [_root_.CategoryTheory.Functor.map_comp, _root_.CategoryTheory.Functor.map_comp]
    calc
      _ = (bundlePullback p E G H P U.map).map f.val.1 ≫
          ((bundlePullback p E G H P U.map).map g.val.1 ≫ Q.punctured.hom) :=
        Category.assoc _ _ _
      _ = (bundlePullback p E G H P U.map).map f.val.1 ≫
          (N.punctured.hom ≫ (bundlePullback p E G H P U.map).map g.val.2) :=
        congrArg (fun a ↦ (bundlePullback p E G H P U.map).map f.val.1 ≫ a) g.property
      _ = (M.punctured.hom ≫ (bundlePullback p E G H P U.map).map f.val.2) ≫
          (bundlePullback p E G H P U.map).map g.val.2 := by
        rw [← Category.assoc, f.property]
      _ = _ := Category.assoc _ _ _⟩
  id_comp f := Subtype.ext (Prod.ext (Category.id_comp _) (Category.id_comp _))
  comp_id f := Subtype.ext (Prod.ext (Category.comp_id _) (Category.comp_id _))
  assoc f g h := Subtype.ext (Prod.ext (Category.assoc _ _ _) (Category.assoc _ _ _))

def leftLeg : Modification p E G H P d U ⥤ Bundles p E G H X where
  obj M := M.left
  map f := f.val.1

def rightLeg : Modification p E G H P d U ⥤ Bundles p E G H X where
  obj M := M.right
  map f := f.val.2

abbrev PuncturedGroupoid := Core (Modification p E G H P d U)

def puncturedLeft : PuncturedGroupoid p E G H P d U ⥤ Bundles p E G H X :=
  Core.inclusion _ ⋙ leftLeg p E G H P d U

def puncturedRight : PuncturedGroupoid p E G H P d U ⥤ Bundles p E G H X :=
  Core.inclusion _ ⋙ rightLeg p E G H P d U

end MathlibExt.AlgebraicGeometry.AnalyticBundleModifications
