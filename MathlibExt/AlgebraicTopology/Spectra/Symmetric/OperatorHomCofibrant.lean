/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorHomCopower
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSpherePowers
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Cofibrancy of the actual native symmetric operator Hom objects

The original native coend is the proved finite orbit copower of the actual
residual sphere tensor power. Native sphere-power cofibrancy and ordinary
model-category coproduct closure prove the full operator-Hom contract.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open PointedCGWH.SymmetricOperatorHom
open CategoryTheory.Operad.SmallFinBijGroupoid
open scoped CGWH.modelCategory

namespace PointedCGWH.SymmetricOperatorHom

/-- The actual coproduct of original initial objects is initial. -/
def initialCopowerIsInitial (Q : Type) :
    IsInitial (∐ (fun _ : Q => ⊥_ PointedCGWH.{u, v})) :=
  IsInitial.ofUniqueHom
    (fun Y => Sigma.desc (fun _ : Q => initial.to Y))
    (by
      intro Y f
      apply Sigma.hom_ext
      intro q
      exact initialIsInitial.hom_ext _ _)

/-- Native pointed coproduct closure derives cofibrancy from each actual coefficient. -/
theorem cofibrantCopower (Q : Type) (Z : PointedCGWH.{u, v}) [IsCofibrant Z] :
    IsCofibrant (∐ (fun _ : Q => Z)) := by
  let f : ∀ _ : Q, (⊥_ PointedCGWH.{u, v}) ⟶ Z := fun _ => initial.to Z
  let _ : ∀ q : Q, Cofibration (f q) := fun _ => inferInstance
  have hf : Cofibration (CategoryTheory.Limits.Sigma.map f) := inferInstance
  exact (isCofibrant_iff_of_isInitial
    (CategoryTheory.Limits.Sigma.map f) (initialCopowerIsInitial Q)).2 hf

/-- Actual source and target objects transfer cofibrancy through the full supplied Iso maps. -/
theorem isCofibrant_of_actualIso {X Y : PointedCGWH.{u, v}}
    (e : X ≅ Y) [IsCofibrant Y] : IsCofibrant X := by
  have h : Cofibration (initial.to Y ≫ e.inv) := inferInstance
  exact (isCofibrant_iff_of_isInitial (initial.to Y ≫ e.inv) initialIsInitial).2 h

/-- Each original residual sphere coefficient is genuinely cofibrant in the selected model. -/
theorem sphereCoefficient_isCofibrant (r : ℕ) :
    IsCofibrant (sphere.{u, v}.obj (card r)) := by
  change IsCofibrant (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} r)
  exact PointedCGWH.modelCategory.tensorPowObj_sphereOne_isCofibrant r

/-- The actual orbit copower of the original residual sphere is cofibrant. -/
theorem sphereCopower_isCofibrant (n m : ℕ) :
    IsCofibrant (sphereCopower.{u, v} n m) := by
  let _ : IsCofibrant (sphere.{u, v}.obj (card (m - n))) :=
    sphereCoefficient_isCofibrant (m - n)
  exact cofibrantCopower (cosetIndex n m)
    (sphere.{u, v}.obj (card (m - n)))

/-- The actual block-colimit below the source cardinality is initial. -/
def blockBelowIsInitial {n m : ℕ} (h : m < n) :
    IsInitial (colimit (blockDiagram.{u, v} (card n) (card m))) := by
  let _ : IsEmpty (BlockDecomposition (card n) (card m)) :=
    blockDecomposition_isEmpty_of_gt h
  let D := blockDiagram.{u, v} (card n) (card m)
  let c (Y : PointedCGWH.{u, v}) : Cocone D :=
    { pt := Y
      ι :=
        { app := fun d => False.elim (IsEmpty.false d)
          naturality := by
            intro d e f
            exact False.elim (IsEmpty.false d) } }
  exact IsInitial.ofUniqueHom (fun Y => colimit.desc D (c Y))
    (by
      intro Y f
      apply colimit.hom_ext
      intro d
      exact False.elim (IsEmpty.false d))

/-- The full original native Hom below the source cardinality is initial. -/
def nativeBelowIsInitial {n m : ℕ} (h : m < n) :
    IsInitial (nativeHom.{u, v} (card n) (card m)) :=
  (blockBelowIsInitial h).ofIso
    (nativeToBlockIso (card n) (card m)).symm

/-- Every original native Hom at cardinal objects is cofibrant, including its empty case. -/
theorem cardinalNativeHom_isCofibrant (n m : ℕ) :
    IsCofibrant (nativeHom.{u, v} (card n) (card m)) := by
  by_cases h : n ≤ m
  · let _ : IsCofibrant (sphereCopower.{u, v} n m) := sphereCopower_isCofibrant n m
    exact isCofibrant_of_actualIso (nativeSphereCopowerIso h)
  · have hInitial :
        IsInitial (nativeHom.{u, v} (card n) (card m)) :=
      nativeBelowIsInitial (Nat.lt_of_not_ge h)
    exact (isCofibrant_iff_of_isInitial
      (𝟙 (nativeHom.{u, v} (card n) (card m))) hInitial).2
        (by infer_instance)

/-- The full actual native symmetric operator-Hom contract, before any sphere/model inputs. -/
theorem nativeSymmetricOperatorHom_isCofibrant
    (a b : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    IsCofibrant (a ⟶[PointedCGWH.{u, v}] b) := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  let a₀ : CategoryTheory.Operad.SmallFinBijGroupoid := a
  let b₀ : CategoryTheory.Operad.SmallFinBijGroupoid := b
  change IsCofibrant (nativeHom.{u, v} a₀ b₀)
  have h := cardinalNativeHom_isCofibrant.{u, v} a₀.of.len b₀.of.len
  have ha : card a₀.of.len = a₀ := by
    cases a₀
    congr 1
  have hb : card b₀.of.len = b₀ := by
    cases b₀
    congr 1
  simpa only [ha, hb] using h

/-- The whole native symmetric Hom-cofibrancy function uses the actual enriched instance. -/
abbrev nativeSymmetricHomCofibrancyFunction :
    ∀ a b : PointedCGWH.SymmetricOperatorIndex.{u, v},
      IsCofibrant (a ⟶[PointedCGWH.{u, v}] b) :=
  nativeSymmetricOperatorHom_isCofibrant

end PointedCGWH.SymmetricOperatorHom
