/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.IntervalPrism

import Mathlib.Topology.Instances.Rat

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Opposite

open scoped Simplicial

universe u

namespace IntervalPrismTests

private abbrev D (n : ℕ) : TopCat.{u} :=
  SimplexCategory.toTop.{u}.obj ⦋n⦌

section Zero

variable {A Z : TopCat.{u}}
variable (phi : Fin 1 → (A ⊗ D.{u} 1 ⟶ Z))

example :
    (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} 0 0) ≫
        TopCat.IntervalPrism.desc 0 phi (fun i => Fin.elim0 i) = phi 0 :=
  TopCat.IntervalPrism.cell_desc 0 phi (fun i => Fin.elim0 i) 0

example :
    (𝟙 A ⊗ₘ (TopCat.ι₀ : D.{u} 0 ⟶ D 0 ⊗ TopCat.I)) ≫
        TopCat.IntervalPrism.desc 0 phi (fun i => Fin.elim0 i) =
      (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
        (SimplexCategory.δ (Fin.last 1))) ≫ phi 0 :=
  TopCat.IntervalPrism.zero_desc 0 phi (fun i => Fin.elim0 i)

example :
    (𝟙 A ⊗ₘ (TopCat.ι₁ : D.{u} 0 ⟶ D 0 ⊗ TopCat.I)) ≫
        TopCat.IntervalPrism.desc 0 phi (fun i => Fin.elim0 i) =
      (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
        (SimplexCategory.δ 0)) ≫ phi 0 :=
  TopCat.IntervalPrism.one_desc 0 phi (fun i => Fin.elim0 i)

end Zero

section One

variable {A Z : TopCat.{u}}
variable (phi : Fin 2 → (A ⊗ D.{u} 2 ⟶ Z))
variable (hphi : ∀ i : Fin 1,
  (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
      (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.castSucc =
    (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
      (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.succ)

example :
    ((𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} 1 0) ≫
        TopCat.IntervalPrism.desc 1 phi hphi = phi 0) ∧
      ((𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} 1 1) ≫
        TopCat.IntervalPrism.desc 1 phi hphi = phi 1) :=
  ⟨TopCat.IntervalPrism.cell_desc 1 phi hphi 0,
    TopCat.IntervalPrism.cell_desc 1 phi hphi 1⟩

example :
    (𝟙 A ⊗ₘ (TopCat.ι₀ : D.{u} 1 ⟶ D 1 ⊗ TopCat.I)) ≫
        TopCat.IntervalPrism.desc 1 phi hphi =
      (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
        (SimplexCategory.δ (Fin.last 2))) ≫ phi 1 :=
  TopCat.IntervalPrism.zero_desc 1 phi hphi

example :
    (𝟙 A ⊗ₘ (TopCat.ι₁ : D.{u} 1 ⟶ D 1 ⊗ TopCat.I)) ≫
        TopCat.IntervalPrism.desc 1 phi hphi =
      (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
        (SimplexCategory.δ 0)) ≫ phi 0 :=
  TopCat.IntervalPrism.one_desc 1 phi hphi

-- The exact descent target cannot be constructed without the adjacent-cell
-- equation; the failure is not caused by the surrounding `True` goal.
example : True := by
  fail_if_success
    have _ : A ⊗ (D.{u} 1 ⊗ TopCat.I) ⟶ Z :=
      TopCat.IntervalPrism.desc 1 phi
  trivial

end One

section NonLocallyCompactCoefficient

private abbrev RatSpace : TopCat := TopCat.of ℚ
private abbrev PointSpace : TopCat := TopCat.of PUnit

private noncomputable def ratPhi :
    Fin 1 → (RatSpace ⊗ D 1 ⟶ PointSpace) :=
  fun _ => TopCat.const PUnit.unit

example : RatSpace ⊗ (D 0 ⊗ TopCat.I) ⟶ PointSpace :=
  TopCat.IntervalPrism.desc 0 ratPhi (fun i => Fin.elim0 i)

example : True := by
  fail_if_success
    let _ : LocallyCompactSpace ℚ := inferInstance
  trivial

end NonLocallyCompactCoefficient

-- Symbolic, universe-one, and universe-zero clients of the exact public API.
#check TopCat.IntervalPrism.cell.{u}
#check TopCat.IntervalPrism.desc.{u}
#check TopCat.IntervalPrism.cell_desc.{u}
#check TopCat.IntervalPrism.zero_desc.{u}
#check TopCat.IntervalPrism.one_desc.{u}

#check TopCat.IntervalPrism.cell.{1}
#check TopCat.IntervalPrism.desc.{1}
#check TopCat.IntervalPrism.cell_desc.{1}
#check TopCat.IntervalPrism.zero_desc.{1}
#check TopCat.IntervalPrism.one_desc.{1}

#check TopCat.IntervalPrism.cell.{0}
#check TopCat.IntervalPrism.desc.{0}
#check TopCat.IntervalPrism.cell_desc.{0}
#check TopCat.IntervalPrism.zero_desc.{0}
#check TopCat.IntervalPrism.one_desc.{0}

#print axioms TopCat.IntervalPrism.cell
#print axioms TopCat.IntervalPrism.desc
#print axioms TopCat.IntervalPrism.cell_desc
#print axioms TopCat.IntervalPrism.zero_desc
#print axioms TopCat.IntervalPrism.one_desc

end IntervalPrismTests
