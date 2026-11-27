/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.SheafHypercoverModels
public import MathlibExt.AlgebraicGeometry.PerfectoidSliceSites

/-!
# Native matching objects for perfectoid v-hypercovers

The matching object is the actual limit over every simplex of the
boundary of the standard n-simplex, in the category of v-sheaves over
the fixed base. Its comparison map uses the actual simplex maps of the
given diagram. A v-hypercover requires that map to be an epimorphism
of sheaves in every degree, including degree zero.

References: Scholze, arXiv:1709.07343v4, Proposition 17.3;
Anschuetz--Mann, arXiv:2403.01951v2, Theorems 1.1 and 4.7.
Only the matching objects/maps and hypercover language are supplied;
coefficient hyperdescent is a separate comparison theorem.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PerfectoidVHypercoverModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open AffinePerfectoidVSite PerfectoidSliceSites

variable (p : ℕ) [Fact p.Prime] (F : VSheaf p)

/-- Actual simplicial v-sheaves with augmentation to the given base. -/
abbrev Diagram := MathlibExt.CategoryTheory.SheafHypercoverModels.Diagram F

variable {p F}

/-- Every simplex of the native boundary indexes a matching component. -/
abbrev boundaryDiagram (H : Diagram p F) (n : ℕ) :=
  MathlibExt.CategoryTheory.SheafHypercoverModels.boundaryDiagram H n

/-- The native boundary-matching cone, with the original simplex maps. -/
abbrev boundaryCone (H : Diagram p F) (n : ℕ) :=
  MathlibExt.CategoryTheory.SheafHypercoverModels.boundaryCone H n

/-- The actual relative matching object. -/
abbrev matchingObject (H : Diagram p F) (n : ℕ) :=
  MathlibExt.CategoryTheory.SheafHypercoverModels.matchingObject H n

/-- Its map from the actual degree-n v-sheaf. -/
abbrev matchingMap (H : Diagram p F) (n : ℕ) :=
  MathlibExt.CategoryTheory.SheafHypercoverModels.matchingMap H n

/-- Every projection of the matching comparison is the original face map. -/
theorem matchingMap_projection (H : Diagram p F) (n : ℕ)
    (x : (SSet.boundary.{0} n).toSSet.Elements) :
    matchingMap H n ≫ limit.π (boundaryDiagram H n) x =
      H.map (((SSet.boundary.{0} n).ι.app x.obj x.val).down.op) :=
  MathlibExt.CategoryTheory.SheafHypercoverModels.matchingMap_projection H n x

/-- A genuine simplicial v-hypercover of the specified v-sheaf. -/
structure VHypercover (p : ℕ) [Fact p.Prime] (F : VSheaf p) where
  diagram : Diagram p F
  small : ∀ n : ℕ, HasPerfectoidCover p (diagram.obj (op (SimplexCategory.mk n))).left
  covers : ∀ n : ℕ, Epi (matchingMap diagram n).left

end MathlibExt.AlgebraicGeometry.PerfectoidVHypercoverModels
