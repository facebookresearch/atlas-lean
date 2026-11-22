/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeCylinderRelations

/-!
# Actual descended cylinder of the original right-cube quotient

The original path cylinder respects the defining whole front-prefix
relations. It therefore gives a genuine scalar simplicial cylinder on
the constructed right-cube quotient. Its original zero endpoint is the
identity, and its one endpoint is the full original path class.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeQuotientCylinder
open PathLastMaximum RightCubeRelations RightCubeCylinder RightCubeCylinderRelations RightCubeFullPath
variable {n : ℕ}

/-- The actual original full-path scalar class in every degree of the right-cube quotient. -/
def fullClass (q : SimplexCategoryᵒᵖ) : (RightCubeRelations.object.{u} n).obj q :=
  _root_.Quotient.mk _ ((Functor.const (Fin (q.unop.len + 1))).obj (fullPath.{u} (0 : Fin (n + 1))))

/-- The actual whole original quotient cylinder map, constructed from the proved relation-compatible path chart. -/
def map (n : ℕ) : RightCubeRelations.object.{u} n ⊗ (Δ[1] : SSet.{u}) ⟶ RightCubeRelations.object.{u} n where
  app q := ↾fun x => _root_.Quotient.lift
    (fun p => _root_.Quotient.mk _ (chain 0 p x.2))
    (fun a b h => _root_.Quotient.sound (compatible h x.2)) x.1
  naturality q r θ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    induction a using _root_.Quotient.inductionOn with
    | _ a =>
      change _root_.Quotient.mk _ _ = _root_.Quotient.mk _ _
      congr 1

/-- The actual original quotient cylinder evaluates every represented original path through the same original chart. -/
theorem map_representative (q : SimplexCategoryᵒᵖ)
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) (t : (Δ[1] : SSet.{u}).obj q) :
    (map n).app q (_root_.Quotient.mk _ p, t) = _root_.Quotient.mk _ (chain 0 p t) := rfl

/-- The constant whole original full-path-class map of the right-cube quotient. -/
def constantMap (n : ℕ) : RightCubeRelations.object.{u} n ⟶ RightCubeRelations.object.{u} n where
  app q := ↾fun _ => fullClass q
  naturality q r θ := by
    ext a
    congr 1

/-- The actual original zero endpoint of the descended quotient cylinder is the entire identity. -/
theorem map_zero (n : ℕ) : SSet.ι₀ ≫ map.{u} n = 𝟙 (RightCubeRelations.object n) := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro a
  induction a using _root_.Quotient.inductionOn with
  | _ a =>
    change _root_.Quotient.mk _ _ = _root_.Quotient.mk _ a
    congr 1

/-- The actual original one endpoint of the descended quotient cylinder is the whole full-path-class map. -/
theorem map_one (n : ℕ) : SSet.ι₁ ≫ map.{u} n = constantMap n := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro a
  induction a using _root_.Quotient.inductionOn with
  | _ a =>
    change _root_.Quotient.mk _ _ = _root_.Quotient.mk _ _
    congr 1

/-- The genuine original quotient homotopy from the identity to its actual full-path class. -/
def homotopy (n : ℕ) : SSet.Homotopy (𝟙 (RightCubeRelations.object.{u} n)) (constantMap n) where
  h := map n
  h₀ := map_zero n
  h₁ := map_one n
  rel := by
    ext q a
    exact a.1.2.elim

end CategoryTheory.CoherentRealization.RightCubeQuotientCylinder
