/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainGradedPairing
public import MathlibExt.Algebra.Homology.TensorDifferentialDownNat
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The actual positive component images of a chain pairing

The degree-n relation submodule is the sum of the images of the original
pairing components with both degrees positive and an explicit equality
of their sum with n. The original tensor differential and chain-map law
prove differential closure when both degree-one boundaries vanish.

The tensor structure is the one already used by the given chain pairing.
No submodule inclusion is assumed to remain injective under tensoring.
The original maps of pairings also preserve these actual image families.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped MonoidalCategory

universe u v

namespace HomologicalComplex.ChainGradedPairing

variable {R : Type u} [Ring R]
  [MonoidalCategory (ModuleCat.{v} R)] [CategoryTheory.MonoidalPreadditive (ModuleCat.{v} R)]
  {K₁ K₂ K₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃)

/-- The original component at an explicitly equal target degree. -/
def pairAt (p q n : ℕ) (h : p + q = n) : K₁.X p ⊗ K₂.X q ⟶ K₃.X n :=
  ιTensorObj K₁ K₂ p q n h ≫ P.f n

/-- The component at its original sum degree is the existing public pairing component. -/
@[simp]
theorem pairAt_rfl (p q : ℕ) : pairAt P p q (p + q) rfl = pair P p q := rfl

/-- The exact image sum indexed by two positive degrees and the original degree equality. -/
def positiveImages (n : ℕ) : Submodule R (K₃.X n) :=
  ⨆ z : {pq : ℕ × ℕ // 0 < pq.1 ∧ 0 < pq.2 ∧ pq.1 + pq.2 = n},
    LinearMap.range (pairAt P z.1.1 z.1.2 n z.2.2.2).hom

/-- Every original positive component image belongs to the exact relation family. -/
theorem pairAt_mem_positiveImages (p q n : ℕ) (h : p + q = n)
    (hp : 0 < p) (hq : 0 < q) (x : ↥(K₁.X p ⊗ K₂.X q)) :
    (pairAt P p q n h).hom x ∈ positiveImages P n := by
  let z : {pq : ℕ × ℕ // 0 < pq.1 ∧ 0 < pq.2 ∧ pq.1 + pq.2 = n} := ⟨(p, q), hp, hq, h⟩
  apply (le_iSup
    (fun z : {pq : ℕ × ℕ // 0 < pq.1 ∧ 0 < pq.2 ∧ pq.1 + pq.2 = n} =>
      LinearMap.range (pairAt P z.1.1 z.1.2 n z.2.2.2).hom) z)
  exact ⟨x, rfl⟩

/-- Positive component images vanish in degree zero. -/
@[simp]
theorem positiveImages_zero : positiveImages P 0 = ⊥ := by
  apply eq_bot_iff.mpr
  apply iSup_le
  rintro ⟨⟨p, q⟩, hp, hq, h⟩
  exfalso
  omega

/-- Positive component images vanish in degree one. -/
@[simp]
theorem positiveImages_one : positiveImages P 1 = ⊥ := by
  apply eq_bot_iff.mpr
  apply iSup_le
  rintro ⟨⟨p, q⟩, hp, hq, h⟩
  exfalso
  omega

/-- The actual signed boundary preserves positive images when both endpoint boundaries vanish. -/
theorem positiveImages_d (h₁ : K₁.d 1 0 = 0) (h₂ : K₂.d 1 0 = 0) (n : ℕ) :
    positiveImages P (n + 1) ≤ (positiveImages P n).comap (K₃.d (n + 1) n).hom := by
  have hboundary : ∀ (p q : ℕ) (h : p + q = n + 1) (hp : p ≠ 0) (hq : q ≠ 0),
      pairAt P p q (n + 1) h ≫ K₃.d (n + 1) n =
        (K₁.d p (p - 1) ⊗ₘ 𝟙 (K₂.X q)) ≫ pairAt P (p - 1) q n (by omega) +
        ((-1 : ℤ) ^ p) •
          ((𝟙 (K₁.X p) ⊗ₘ K₂.d q (q - 1)) ≫ pairAt P p (q - 1) n (by omega)) := by
    intro p q h hp hq
    dsimp only [pairAt]
    rw [Category.assoc, P.comm, ← Category.assoc,
      ιTensorObj_comp_d_down_nat K₁ K₂ p q n h]
    simp only [dite_eq_right hp, dite_eq_right hq, Preadditive.add_comp,
      Preadditive.zsmul_comp, Category.assoc]
  have hmem : ∀ (p q : ℕ) (h : p + q = n + 1) (hp : 0 < p) (hq : 0 < q)
      (x : ↥(K₁.X p ⊗ K₂.X q)),
      (K₃.d (n + 1) n).hom ((pairAt P p q (n + 1) h).hom x) ∈ positiveImages P n := by
    intro p q h hp hq x
    have hp0 : p ≠ 0 := Nat.ne_of_gt hp
    have hq0 : q ≠ 0 := Nat.ne_of_gt hq
    have hleft :
        ((K₁.d p (p - 1) ⊗ₘ 𝟙 (K₂.X q)) ≫ pairAt P (p - 1) q n (by omega)).hom x ∈
          positiveImages P n := by
      by_cases hp1 : p = 1
      · subst p
        simp [h₁]
      · have hp' : 0 < p - 1 := by omega
        change (pairAt P (p - 1) q n (by omega)).hom
          ((K₁.d p (p - 1) ⊗ₘ 𝟙 (K₂.X q)).hom x) ∈ _
        exact pairAt_mem_positiveImages P (p - 1) q n (by omega) hp' hq _
    have hright :
        ((𝟙 (K₁.X p) ⊗ₘ K₂.d q (q - 1)) ≫ pairAt P p (q - 1) n (by omega)).hom x ∈
          positiveImages P n := by
      by_cases hq1 : q = 1
      · subst q
        simp [h₂]
      · have hq' : 0 < q - 1 := by omega
        change (pairAt P p (q - 1) n (by omega)).hom
          ((𝟙 (K₁.X p) ⊗ₘ K₂.d q (q - 1)).hom x) ∈ _
        exact pairAt_mem_positiveImages P p (q - 1) n (by omega) hp hq' _
    have heq := ConcreteCategory.congr_hom (hboundary p q h hp0 hq0) x
    change (K₃.d (n + 1) n).hom ((pairAt P p q (n + 1) h).hom x) =
      ((K₁.d p (p - 1) ⊗ₘ 𝟙 (K₂.X q)) ≫ pairAt P (p - 1) q n (by omega)).hom x +
      ((-1 : ℤ) ^ p) •
        ((𝟙 (K₁.X p) ⊗ₘ K₂.d q (q - 1)) ≫ pairAt P p (q - 1) n (by omega)).hom x at heq
    rw [heq]
    exact (positiveImages P n).add_mem hleft
      ((positiveImages P n).toAddSubgroup.zsmul_mem hright _)
  change (⨆ z : {pq : ℕ × ℕ // 0 < pq.1 ∧ 0 < pq.2 ∧ pq.1 + pq.2 = n + 1},
      LinearMap.range (pairAt P z.1.1 z.1.2 (n + 1) z.2.2.2).hom) ≤ _
  apply iSup_le
  intro z
  rintro _ ⟨x, rfl⟩
  exact hmem z.1.1 z.1.2 z.2.2.2 z.2.1 z.2.2.1 x

/-- Genuine morphisms of the original pairings preserve their actual positive component images. -/
theorem positiveImages_naturality
    {L₁ L₂ L₃ : ChainComplex (ModuleCat.{v} R) ℕ}
    (Q : ChainGradedPairing L₁ L₂ L₃)
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (h : tensorHom f₁ f₂ ≫ Q = P ≫ f₃) (n : ℕ) :
    positiveImages P n ≤ (positiveImages Q n).comap (f₃.f n).hom := by
  change (⨆ z : {pq : ℕ × ℕ // 0 < pq.1 ∧ 0 < pq.2 ∧ pq.1 + pq.2 = n},
      LinearMap.range (pairAt P z.1.1 z.1.2 n z.2.2.2).hom) ≤ _
  apply iSup_le
  rintro ⟨⟨p, q⟩, hp, hq, hn⟩
  subst n
  rintro _ ⟨x, rfl⟩
  have heq := ConcreteCategory.congr_hom (pair_naturality P Q f₁ f₂ f₃ h p q) x
  change (pair Q p q).hom ((f₁.f p ⊗ₘ f₂.f q).hom x) =
    (f₃.f (p + q)).hom ((pair P p q).hom x) at heq
  change (f₃.f (p + q)).hom ((pair P p q).hom x) ∈ positiveImages Q (p + q)
  rw [← heq]
  exact pairAt_mem_positiveImages Q p q (p + q) rfl hp hq _

end HomologicalComplex.ChainGradedPairing
