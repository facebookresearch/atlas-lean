/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/Algebra/Homology/Monoidal/Tensor/Differential.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# The differential of a tensor product of complexes

Mathlib's `HomologicalComplex.monoidalCategory` totalizes the degreewise tensor product of
complexes, with the tensor signs `ε₁ = 1` and `ε₂ (p, q) = (-1)^p`.  This file records the
resulting differential on a homogeneous summand, `d (x ⊗ y) = d x ⊗ y + (-1)^p x ⊗ d y` for `x` of
degree `p`: as a single rewrite rule for cochain complexes of modules indexed by `ℤ`, and as its two
parts `HomologicalComplex.mapBifunctor.D₁` and `HomologicalComplex.mapBifunctor.D₂` for chain
complexes indexed by `ℕ` in any monoidal preadditive category, where a part vanishes on a summand
whose factor of degree zero it would differentiate.

## Main results

* `HomologicalComplex.ι_tensorObj_d`: the differential of `X ⊗ Y` restricted to the summand
  `X.X p ⊗ Y.X q`, for cochain complexes of modules, and `HomologicalComplex.ι_tensorObj_d'`,
  the same formula with arbitrary names for the successor degrees.
* `ChainComplex.ιTensorObj_D₁_succ`, `ChainComplex.ιTensorObj_D₁_zero`,
  `ChainComplex.ιTensorObj_D₂_succ` and `ChainComplex.ιTensorObj_D₂_zero`: the two parts of the
  differential of `K₁ ⊗ K₂` on a homogeneous summand, for chain complexes indexed by `ℕ`.

## Implementation notes

`Mathlib.CategoryTheory.Monoidal.Closed.Braided` is imported for the colimit-preservation
instances that make the tensor product of cochain complexes exist at all, exactly as in
`MathlibExt/CategoryTheory/DGSource/CochainBraiding.lean`.
-/

public section

open CategoryTheory Limits MonoidalCategory

universe v

namespace HomologicalComplex

variable {R : Type v} [CommRing R]

/-- The differential of a tensor product of cochain complexes on a homogeneous summand is the
sum of the two factor differentials, with the Koszul sign on the second term. -/
@[reassoc (attr := simp)]
lemma ι_tensorObj_d (X Y : CochainComplex (ModuleCat.{v} R) ℤ) (p q j : ℤ)
    (hpq : p + q = j) :
    ιTensorObj X Y p q j hpq ≫ (X ⊗ Y).d j (j + 1) =
      ((curriedTensor (ModuleCat.{v} R)).map (X.d p (p + 1))).app (Y.X q) ≫
        ιTensorObj X Y (p + 1) q (j + 1) (by omega) +
      p.negOnePow •
        ((curriedTensor (ModuleCat.{v} R)).obj (X.X p)).map (Y.d q (q + 1)) ≫
          ιTensorObj X Y p (q + 1) (j + 1) (by omega) := by
  have hd : (X ⊗ Y).d j (j + 1) =
      mapBifunctor.D₁ X Y (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) j (j + 1) +
        mapBifunctor.D₂ X Y (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) j (j + 1) :=
    mapBifunctor.d_eq _ _ _ _ j (j + 1)
  rw [hd, Preadditive.comp_add,
    mapBifunctor.ι_D₁,
    mapBifunctor.d₁_eq _ _ _ _
      (ComplexShape.up_mk p (p + 1) rfl) q (j + 1) (by dsimp; omega),
    mapBifunctor.ι_D₂,
    mapBifunctor.d₂_eq _ _ _ _ p
      (ComplexShape.up_mk q (q + 1) rfl) (j + 1) (by dsimp; omega)]
  simp only [ComplexShape.ε₁_def, one_smul, ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ]

/-- `HomologicalComplex.ι_tensorObj_d` with arbitrary indices `p'`, `q'` and `j'` for the
successors of `p`, `q` and `j`, in whiskered form. -/
@[reassoc]
lemma ι_tensorObj_d' (X Y : CochainComplex (ModuleCat.{v} R) ℤ) {p q j p' q' j' : ℤ}
    (hpq : p + q = j) (hp : p + 1 = p') (hq : q + 1 = q') (hj : j + 1 = j') :
    ιTensorObj X Y p q j hpq ≫ (X ⊗ Y).d j j' =
      (X.d p p' ▷ Y.X q) ≫ ιTensorObj X Y p' q j' (by omega) +
        p.negOnePow • ((X.X p ◁ Y.d q q') ≫ ιTensorObj X Y p q' j' (by omega)) := by
  subst hp hq hj
  simp

end HomologicalComplex

namespace ChainComplex

open HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  (K₁ K₂ : ChainComplex C ℕ) [K₁.HasTensor K₂]

/-- The first part of the differential of a tensor product of chain complexes, on a summand whose
first factor has positive degree, is the differential of the first factor. -/
@[reassoc]
lemma ιTensorObj_D₁_succ (r s n : ℕ) (h : r + 1 + s = n + 1) :
    ιTensorObj K₁ K₂ (r + 1) s (n + 1) h ≫
        mapBifunctor.D₁ K₁ K₂ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n =
      (K₁.d (r + 1) r ▷ K₂.X s) ≫ ιTensorObj K₁ K₂ r s n (by omega) := by
  have hr : (ComplexShape.down ℕ).Rel (r + 1) r := by simp
  rw [mapBifunctor.ι_D₁, mapBifunctor.d₁_eq _ _ _ _
    hr _ _ (by simp; omega)]
  simp

/-- The first part of the differential of a tensor product of chain complexes vanishes on a
summand whose first factor has degree zero. -/
@[reassoc]
lemma ιTensorObj_D₁_zero (n : ℕ) :
    ιTensorObj K₁ K₂ 0 (n + 1) (n + 1) (by omega) ≫
        mapBifunctor.D₁ K₁ K₂ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n = 0 := by
  rw [mapBifunctor.ι_D₁, mapBifunctor.d₁_eq_zero]
  simp

/-- The second part of the differential of a tensor product of chain complexes, on a summand whose
second factor has positive degree, is the differential of the second factor with the Koszul sign
`(-1)^r` of the degree `r` of the first factor. -/
@[reassoc]
lemma ιTensorObj_D₂_succ (r s n : ℕ) (h : r + (s + 1) = n + 1) :
    ιTensorObj K₁ K₂ r (s + 1) (n + 1) h ≫
        mapBifunctor.D₂ K₁ K₂ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n =
      ((-1 : ℤ) ^ r) •
        (K₁.X r ◁ K₂.d (s + 1) s) ≫ ιTensorObj K₁ K₂ r s n (by omega) := by
  have hs : (ComplexShape.down ℕ).Rel (s + 1) s := by simp
  rw [mapBifunctor.ι_D₂, mapBifunctor.d₂_eq _ _ _ _ _
    hs _ (by simp; omega)]
  simp [Units.smul_def]

/-- The second part of the differential of a tensor product of chain complexes vanishes on a
summand whose second factor has degree zero. -/
@[reassoc]
lemma ιTensorObj_D₂_zero (n : ℕ) :
    ιTensorObj K₁ K₂ (n + 1) 0 (n + 1) (by omega) ≫
        mapBifunctor.D₂ K₁ K₂ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n = 0 := by
  rw [mapBifunctor.ι_D₂, mapBifunctor.d₂_eq_zero]
  simp

end ChainComplex
