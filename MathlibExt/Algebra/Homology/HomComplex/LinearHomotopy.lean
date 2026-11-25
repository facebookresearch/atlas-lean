/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.HomComplex.LinearFunctor

/-!
# Original linear Hom maps preserve homotopies

Native cochain composition and its Leibniz law construct the actual
homotopies. Postcomposition uses the original degree -1 target cochain.
Precomposition uses the native `n.negOnePow` coefficient. Both equations
are on the original linear Hom complex, in every integer degree.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory HomologicalComplex

namespace CochainComplex.HomComplex

universe uR uC vC

variable (R : Type uR) [Ring R]
  {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]

/-- Original target composition, expressed by native cochain composition. -/
theorem mapLinearOver_post {P L L' : CochainComplex C ℤ} (g : L ⟶ L')
    (n : ℤ) (z : Cochain P L n) :
    mapLinearOver R (𝟙 P) g n z = z.comp (Cochain.ofHom g) (add_zero n) := by
  apply Cochain.ext
  intro p q hpq
  simp only [mapLinearOver_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    HomologicalComplex.id_f, Category.id_comp]

/-- Original source composition, expressed by native cochain composition. -/
theorem mapLinearOver_pre {P P' L : CochainComplex C ℤ} (f : P' ⟶ P)
    (n : ℤ) (z : Cochain P L n) :
    mapLinearOver R f (𝟙 L) n z = (Cochain.ofHom f).comp z (zero_add n) := by
  apply Cochain.ext
  intro p q hpq
  simp only [mapLinearOver_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    HomologicalComplex.id_f, Category.comp_id]

/-- The original postcomposition homotopy cochain; there is no extra sign. -/
def linearPostHomotopyCochain (P : CochainComplex C ℤ)
    {L L' : CochainComplex C ℤ} {g₀ g₁ : L ⟶ L'} (h : Homotopy g₀ g₁) :
    Cochain (linearComplex R P L) (linearComplex R P L') (-1) :=
  Cochain.mk fun _n _m hnm => ModuleCat.ofHom
    { toFun := fun z => z.comp (Cochain.ofHomotopy h) hnm
      map_add' z z' := Cochain.add_comp z z' (Cochain.ofHomotopy h) hnm
      map_smul' r z := Cochain.smul_comp r z (Cochain.ofHomotopy h) hnm }

@[simp]
theorem linearPostHomotopyCochain_v (P : CochainComplex C ℤ)
    {L L' : CochainComplex C ℤ} {g₀ g₁ : L ⟶ L'} (h : Homotopy g₀ g₁)
    (n m : ℤ) (hnm : n + (-1) = m) (z : Cochain P L n) :
    (linearPostHomotopyCochain R P h).v n m hnm z =
      z.comp (Cochain.ofHomotopy h) hnm := rfl

/-- Native delta gives exactly the difference of the original target maps. -/
theorem linearPostHomotopyCochain_delta (P : CochainComplex C ℤ)
    {L L' : CochainComplex C ℤ} {g₀ g₁ : L ⟶ L'} (h : Homotopy g₀ g₁) :
    δ (-1) 0 (linearPostHomotopyCochain R P h) =
      Cochain.ofHom (linearComplexMap R (𝟙 P) g₀) -
        Cochain.ofHom (linearComplexMap R (𝟙 P) g₁) := by
  apply Cochain.ext₀
  intro n
  rw [δ_v (-1) 0 (by decide) _ n n (add_zero n) (n - 1) (n + 1) rfl rfl]
  simp only [Int.negOnePow_zero, one_smul, Cochain.sub_v, Cochain.ofHom_v]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change δ (n - 1) n (z.comp (Cochain.ofHomotopy h) (by omega)) +
      (δ n (n + 1) z).comp (Cochain.ofHomotopy h) (by omega) =
    mapLinearOver R (𝟙 P) g₀ n z - mapLinearOver R (𝟙 P) g₁ n z
  rw [δ_comp z (Cochain.ofHomotopy h) (show n + (-1) = n - 1 by omega)
    (n + 1) 0 n (by omega) rfl (by decide)]
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul]
  rw [δ_ofHomotopy, Cochain.comp_sub, mapLinearOver_post, mapLinearOver_post]
  abel

/-- An actual homotopy between the original postcomposition maps. -/
def linearComplexMapPostHomotopy (P : CochainComplex C ℤ)
    {L L' : CochainComplex C ℤ} {g₀ g₁ : L ⟶ L'} (h : Homotopy g₀ g₁) :
    Homotopy (linearComplexMap R (𝟙 P) g₀) (linearComplexMap R (𝟙 P) g₁) :=
  (Cochain.equivHomotopy _ _).symm
    ⟨linearPostHomotopyCochain R P h, by
      rw [linearPostHomotopyCochain_delta, sub_add_cancel]⟩

/-- The original precomposition homotopy cochain, with its native degree sign. -/
def linearPreHomotopyCochain {P P' : CochainComplex C ℤ}
    {f₀ f₁ : P' ⟶ P} (h : Homotopy f₀ f₁) (L : CochainComplex C ℤ) :
    Cochain (linearComplex R P L) (linearComplex R P' L) (-1) :=
  Cochain.mk fun n m hnm => ModuleCat.ofHom
    { toFun := fun z => n.negOnePow • (Cochain.ofHomotopy h).comp z (by omega)
      map_add' z z' := by
        simp only [Cochain.comp_add, smul_add]
      map_smul' r z := by
        simp only [Cochain.comp_smul, smul_comm n.negOnePow r, RingHom.id_apply] }

@[simp]
theorem linearPreHomotopyCochain_v {P P' : CochainComplex C ℤ}
    {f₀ f₁ : P' ⟶ P} (h : Homotopy f₀ f₁) (L : CochainComplex C ℤ)
    (n m : ℤ) (hnm : n + (-1) = m) (z : Cochain P L n) :
    (linearPreHomotopyCochain R h L).v n m hnm z =
      n.negOnePow • (Cochain.ofHomotopy h).comp z (by omega) := rfl

/-- Native delta and the successive degree signs give exactly the
difference of the original source maps. -/
theorem linearPreHomotopyCochain_delta {P P' : CochainComplex C ℤ}
    {f₀ f₁ : P' ⟶ P} (h : Homotopy f₀ f₁) (L : CochainComplex C ℤ) :
    δ (-1) 0 (linearPreHomotopyCochain R h L) =
      Cochain.ofHom (linearComplexMap R f₀ (𝟙 L)) -
        Cochain.ofHom (linearComplexMap R f₁ (𝟙 L)) := by
  apply Cochain.ext₀
  intro n
  rw [δ_v (-1) 0 (by decide) _ n n (add_zero n) (n - 1) (n + 1) rfl rfl]
  simp only [Int.negOnePow_zero, one_smul, Cochain.sub_v, Cochain.ofHom_v]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change δ (n - 1) n (n.negOnePow •
      (Cochain.ofHomotopy h).comp z (by omega)) +
      (n + 1).negOnePow • (Cochain.ofHomotopy h).comp (δ n (n + 1) z) (by omega) =
    mapLinearOver R f₀ (𝟙 L) n z - mapLinearOver R f₁ (𝟙 L) n z
  rw [δ_units_smul,
    δ_comp (Cochain.ofHomotopy h) z (show (-1) + n = n - 1 by omega)
      0 (n + 1) n (by omega) (by decide) rfl,
    Int.negOnePow_succ, smul_add, smul_smul, Int.units_mul_self, one_smul,
    Units.neg_smul, δ_ofHomotopy, Cochain.sub_comp,
    mapLinearOver_pre, mapLinearOver_pre]
  abel

/-- An actual homotopy between the original precomposition maps. -/
def linearComplexMapPreHomotopy {P P' : CochainComplex C ℤ}
    {f₀ f₁ : P' ⟶ P} (h : Homotopy f₀ f₁) (L : CochainComplex C ℤ) :
    Homotopy (linearComplexMap R f₀ (𝟙 L)) (linearComplexMap R f₁ (𝟙 L)) :=
  (Cochain.equivHomotopy _ _).symm
    ⟨linearPreHomotopyCochain R h L, by
      rw [linearPreHomotopyCochain_delta, sub_add_cancel]⟩

end CochainComplex.HomComplex
