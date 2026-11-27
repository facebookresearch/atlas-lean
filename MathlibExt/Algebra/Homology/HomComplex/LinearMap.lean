/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Linear maps on Hom cochains

Precomposition and postcomposition by complex morphisms define linear
maps on the product cochains. Component formulas prove compatibility
with the differential and the identity and composition laws. A ring
and a linear preadditive category suffice.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CochainComplex.HomComplex

universe uC vC uR

variable (R : Type uR) [Ring R]
  {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
  {K K' K'' L L' L'' : CochainComplex C ℤ}

/-- The cochain component, with both map components. -/
def mapLinearOver (f : K' ⟶ K) (g : L ⟶ L') (n : ℤ) :
    Cochain K L n →ₗ[R] Cochain K' L' n where
  toFun z := ((Cochain.ofHom f).comp z (zero_add n)).comp
    (Cochain.ofHom g) (add_zero n)
  map_add' z z' := by rw [Cochain.comp_add, Cochain.add_comp]
  map_smul' r z := by rw [RingHom.id_apply, Cochain.comp_smul, Cochain.smul_comp]

/-- Each product coordinate is the source component, original
cochain component and target component, in that order. -/
theorem mapLinearOver_v (f : K' ⟶ K) (g : L ⟶ L') (n p q : ℤ)
    (hpq : p + n = q) (z : Cochain K L n) :
    (mapLinearOver R f g n z).v p q hpq = f.f p ≫ z.v p q hpq ≫ g.f q := by
  change (((Cochain.ofHom f).comp z (zero_add n)).comp
    (Cochain.ofHom g) (add_zero n)).v p q hpq = _
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v, Category.assoc]

/-- Differential naturality for complex maps in every integer degree. -/
theorem mapLinearOver_δ (f : K' ⟶ K) (g : L ⟶ L') (n m : ℤ)
    (z : Cochain K L n) :
    mapLinearOver R f g m (δ n m z) = δ n m (mapLinearOver R f g n z) := by
  change ((Cochain.ofHom f).comp (δ n m z) (zero_add m)).comp
      (Cochain.ofHom g) (add_zero m) =
    δ n m (((Cochain.ofHom f).comp z (zero_add n)).comp
      (Cochain.ofHom g) (add_zero n))
  rw [δ_comp_ofHom, δ_ofHom_comp]

/-- Identity morphisms act identically on the product cochains. -/
@[simp]
theorem mapLinearOver_id (K L : CochainComplex C ℤ) (n : ℤ) :
    mapLinearOver R (𝟙 K) (𝟙 L) n = LinearMap.id := by
  apply LinearMap.ext
  intro z
  change ((Cochain.ofHom (𝟙 K)).comp z (zero_add n)).comp
    (Cochain.ofHom (𝟙 L)) (add_zero n) = z
  rw [Cochain.id_comp, Cochain.comp_id]

/-- The cochain map has contravariant source and covariant target order. -/
theorem mapLinearOver_comp (f : K' ⟶ K) (f' : K'' ⟶ K')
    (g : L ⟶ L') (g' : L' ⟶ L'') (n : ℤ) :
    (mapLinearOver R f' g' n).comp (mapLinearOver R f g n) =
      mapLinearOver R (f' ≫ f) (g ≫ g') n := by
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  change (mapLinearOver R f' g' n (mapLinearOver R f g n z)).v p q hpq =
    (mapLinearOver R (f' ≫ f) (g ≫ g') n z).v p q hpq
  rw [mapLinearOver_v, mapLinearOver_v, mapLinearOver_v]
  simp only [HomologicalComplex.comp_f, Category.assoc]

end CochainComplex.HomComplex
