/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SemiSimplicialObject.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Homotopy

import Mathlib.Tactic.Abel

/-!
# Alternating-face complexes with the last face omitted

For a semisimplicial object X in a preadditive category, use the terms X_n and boundaries
d'_(n+1,n) = ∑ i : Fin (n + 1), (−1)^i δ_i, omitting the final face δ_(n+1). The face
relations imply that these boundaries compose to zero, including in the lowest degrees, so
they define a chain complex indexed by ℕ and a functor on semisimplicial objects.

Maps s_n : X_n → X_(n+1) contract this complex when s_n δ₀ = 𝟙 and s_(n+1) δ_(i+1) = δ_i s_n
for the retained faces. The contraction has component s_n in degree (n, n + 1). Its bottom
equation is s₀ d'₁₀ = 𝟙, and its positive-degree equation is d'_(n+1,n) s_n + s_(n+1)
d'_(n+2,n+1) = 𝟙.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open CategoryTheory.Category CategoryTheory.Preadditive
open scoped Simplicial

universe u v

namespace AlgebraicTopology

namespace TruncatedAlternatingFaceMapComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (X Y : SemiSimplicialObject C)

/-- For a semisimplicial object X in a preadditive category C, the morphism objD X n : X_(n+1) ⟶
X_n is ∑ i : Fin (n + 1), (−1 : ℤ)^i • X.δ i.castSucc. It includes faces 0 through n and omits
face n + 1; in degree one to zero it is δ₀. -/
def objD (n : ℕ) : X _⦋n + 1⦌ₛ ⟶ X _⦋n⦌ₛ :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • X.δ i.castSucc

/-- For a semisimplicial object X in a preadditive category C, one has objD X (n + 1) ≫ objD X n =
0 for every n : ℕ, where objD X n is the alternating sum of faces 0 through n. Thus the
composition X_(n+2) ⟶ X_n vanishes, including for n = 0. -/
theorem d_squared (n : ℕ) : objD X (n + 1) ≫ objD X n = 0 := by
  dsimp only [objD]
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  let P := Fin (n + 1) × Fin (n + 2)
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)),
      ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    lia
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using! congr_arg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred <| ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'
    · simpa [S] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, pow_add, pow_one, mul_neg, neg_neg, mul_one]
      apply mul_comm
    · have hji : j ≤ i.castSucc := by
        exact Fin.le_iff_val_le_val.mpr (Finset.mem_filter.mp hij).right
      have hcast : i.castSucc.succ = i.succ.castSucc := by
        apply Fin.ext
        rfl
      simpa only [φ, Fin.castSucc_castLT, hcast] using
        (SemiSimplicialObject.δ_comp_δ X hji).symm

/-- For a semisimplicial object X in a preadditive category C, define a chain complex of shape
down ℕ with degree-n term X_n and boundary from n + 1 to n equal to ∑ i : Fin (n + 1), (−1)^i
• X.δ i.castSucc. The degree-zero term is X₀ and all nonadjacent differentials are zero. -/
def obj : ChainComplex C ℕ :=
  ChainComplex.of (fun n => X _⦋n⦌ₛ) (objD X) (d_squared X)

/-- For a semisimplicial object X in a preadditive category C, the degree-n object of the
last-face-omitted complex obj X is X _⦋n⦌ₛ for every n : ℕ, including n = 0. -/
@[simp]
theorem obj_X (n : ℕ) : (obj X).X n = X _⦋n⦌ₛ := rfl

/-- For a semisimplicial object X in a preadditive category C, the differential (obj X).d (n + 1)
n is objD X n = ∑ i : Fin (n + 1), (−1)^i • X.δ i.castSucc, for every n : ℕ. -/
@[simp]
theorem obj_d (n : ℕ) : (obj X).d (n + 1) n = objD X n := by
  simp only [obj, ChainComplex.of_d]

variable {X Y}

/-- For semisimplicial objects X and Y in a preadditive category C, a natural transformation f : X
⟶ Y defines a chain map between their last-face-omitted complexes. Its degree-n component is
f.app (op ⦋n⦌ₛ), and it commutes with the alternating sums of the retained faces. -/
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom (fun n => f.app (op ⦋n⦌ₛ)) fun n => by
    simp only [obj, ChainComplex.of_d, objD]
    rw [comp_sum, sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [comp_zsmul, zsmul_comp]
    congr 1
    exact (f.naturality (SemiSimplexCategory.δ i.castSucc).op).symm

/-- For a semisimplicial map f : X ⟶ Y in a preadditive category C and n : ℕ, the degree-n
component of the induced map between last-face-omitted complexes is (map f).f n = f.app (op
⦋n⦌ₛ). -/
@[simp]
theorem map_f (f : X ⟶ Y) (n : ℕ) : (map f).f n = f.app (op ⦋n⦌ₛ) := rfl


section FrontInsertion

variable (X : SemiSimplicialObject C)
  (s : ∀ n : ℕ, X _⦋n⦌ₛ ⟶ X _⦋n + 1⦌ₛ)
  (hFirst : ∀ n : ℕ, s n ≫ X.δ (0 : Fin (n + 2)) = 𝟙 (X _⦋n⦌ₛ))
  (hShift : ∀ (n : ℕ) (i : Fin (n + 1)),
    s (n + 1) ≫ X.δ i.succ.castSucc = X.δ i.castSucc ≫ s n)

include hFirst in
/-- Let X be a semisimplicial object in a preadditive category C and let s_n : X_n ⟶ X_(n+1)
satisfy s_n ≫ X.δ 0 = 𝟙 X_n for all n : ℕ. The truncated bottom differential satisfies s₀ ≫
objD X 0 = 𝟙 X₀, since objD X 0 is the first face δ₀. -/
theorem frontInsertion_sum_zero : s 0 ≫ objD X 0 = 𝟙 (X _⦋0⦌ₛ) := by
  change s 0 ≫ (∑ i : Fin 1, (-1 : ℤ) ^ i.val • X.δ i.castSucc) = 𝟙 (X _⦋0⦌ₛ)
  rw [Fin.sum_univ_one]
  simpa only [Fin.val_zero, Fin.castSucc_zero, pow_zero, one_smul] using hFirst 0

include hFirst hShift in
/-- Let X be a semisimplicial object in a preadditive category C, with maps s_n : X_n ⟶ X_(n+1).
Assume s_n ≫ δ₀ = 𝟙 X_n for every n, and s_(n+1) ≫ δ_(i+1) = δ_i ≫ s_n for every i : Fin (n +
1), where the faces have the casts i.succ.castSucc and i.castSucc. For every n : ℕ, the
truncated boundaries satisfy objD X n ≫ s_n + s_(n+1) ≫ objD X (n + 1) = 𝟙 X_(n+1). -/
theorem frontInsertion_sum_succ (n : ℕ) :
    objD X n ≫ s n + s (n + 1) ≫ objD X (n + 1) = 𝟙 (X _⦋n + 1⦌ₛ) := by
  have hs : s (n + 1) ≫ objD X (n + 1) =
      𝟙 (X _⦋n + 1⦌ₛ) - objD X n ≫ s n := by
    calc
      _ = (s (n + 1) ≫ X.δ (0 : Fin (n + 3))) +
          ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i.val + 1) •
            (s (n + 1) ≫ X.δ i.succ.castSucc) := by
        rw [objD, comp_sum, Fin.sum_univ_succ]
        simp only [Fin.val_zero, pow_zero, one_smul, Fin.castSucc_zero,
          comp_zsmul, Fin.val_succ]
      _ = 𝟙 (X _⦋n + 1⦌ₛ) +
          ∑ i : Fin (n + 1), -(((-1 : ℤ) ^ i.val • X.δ i.castSucc) ≫ s n) := by
        rw [hFirst (n + 1)]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [hShift n i, pow_succ]
        simp only [mul_neg, mul_one, neg_smul, zsmul_comp]
      _ = _ := by
        simp only [objD, sum_comp, sub_eq_add_neg, Finset.sum_neg_distrib]
  rw [hs]
  abel

include hFirst hShift in
/-- Let X be a semisimplicial object in a preadditive category C, with maps s_n : X_n ⟶ X_(n+1).
Assume s_n ≫ δ₀ = 𝟙 X_n for every n, and s_(n+1) ≫ δ_(i+1) = δ_i ≫ s_n for every i : Fin (n +
1), where the faces have the casts i.succ.castSucc and i.castSucc. These maps define a chain
homotopy from 𝟙 (obj X) to the zero chain map on the last-face-omitted complex. Its adjacent
component in degree (n, n + 1) is s_n; the contraction equations hold in degree zero and in
every positive degree. -/
def contractingHomotopy : Homotopy (𝟙 (obj X)) 0 := by
  let H (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel j i) :
      (obj X).X i ⟶ (obj X).X j := by
    change i + 1 = j at hij
    cases hij
    exact s i
  have hH (i : ℕ) : H i (i + 1) rfl = s i := rfl
  have h : Homotopy.nullHomotopicMap' H = 𝟙 (obj X) := by
    apply HomologicalComplex.hom_ext
    intro n
    cases n with
    | zero =>
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left
        (k₁ := 1) (k₀ := 0) (by rfl) (by intro l; simp [ComplexShape.down_Rel]) H]
      simp only [hH, HomologicalComplex.id_f, obj_d]
      change s 0 ≫ objD X 0 = 𝟙 (X _⦋0⦌ₛ)
      exact frontInsertion_sum_zero X s hFirst
    | succ n =>
      rw [Homotopy.nullHomotopicMap'_f
        (k₂ := n + 2) (k₁ := n + 1) (k₀ := n) (by rfl) (by rfl) H]
      simp only [hH, HomologicalComplex.id_f, obj_d]
      change objD X n ≫ s n + s (n + 1) ≫ objD X (n + 1) = 𝟙 (X _⦋n + 1⦌ₛ)
      exact frontInsertion_sum_succ X s hFirst hShift n
  exact (Homotopy.ofEq h.symm).trans (Homotopy.nullHomotopy' H)

/-- Let X be a semisimplicial object in a preadditive category C, with maps s_n : X_n ⟶ X_(n+1).
Assume s_n ≫ δ₀ = 𝟙 X_n for every n, and s_(n+1) ≫ δ_(i+1) = δ_i ≫ s_n for every i : Fin (n +
1), where the faces have the casts i.succ.castSucc and i.castSucc. For every n : ℕ,
(contractingHomotopy X s hFirst hShift).hom n (n + 1) = s_n. This identifies the sign and the
degree-raising map of the contraction of the truncated identity to zero. -/
@[simp]
theorem contractingHomotopy_hom (n : ℕ) :
    (contractingHomotopy X s hFirst hShift).hom n (n + 1) = s n := by
  dsimp only [contractingHomotopy, Homotopy.trans, Homotopy.ofEq,
    Homotopy.nullHomotopy', Homotopy.nullHomotopy]
  simp only [Pi.add_apply, Pi.zero_apply, zero_add]
  split
  · rfl
  · rename_i hij
    exact (hij rfl).elim

end FrontInsertion

end TruncatedAlternatingFaceMapComplex

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- For a preadditive category C, the functor SemiSimplicialObject C ⥤ ChainComplex C ℕ sends X to
its last-face-omitted alternating complex with terms X_n and boundaries ∑ i : Fin (n + 1),
(−1)^i • X.δ i.castSucc. It sends each semisimplicial morphism to the chain map given by its
degree components. -/
def truncatedAlternatingFaceMapComplex : SemiSimplicialObject C ⥤ ChainComplex C ℕ where
  obj := TruncatedAlternatingFaceMapComplex.obj
  map f := TruncatedAlternatingFaceMapComplex.map f

/-- For a semisimplicial object X in a preadditive category C and every n : ℕ, the degree-n term
of (truncatedAlternatingFaceMapComplex C).obj X is X _⦋n⦌ₛ. -/
@[simp]
theorem truncatedAlternatingFaceMapComplex_obj_X (X : SemiSimplicialObject C) (n : ℕ) :
    ((truncatedAlternatingFaceMapComplex C).obj X).X n = X _⦋n⦌ₛ := rfl

/-- For a semisimplicial object X in a preadditive category C, the differential from n + 1 to n in
(truncatedAlternatingFaceMapComplex C).obj X equals ∑ i : Fin (n + 1), (−1 : ℤ)^i • X.δ
i.castSucc, the alternating sum with the final face omitted. -/
@[simp]
theorem truncatedAlternatingFaceMapComplex_obj_d (X : SemiSimplicialObject C) (n : ℕ) :
    ((truncatedAlternatingFaceMapComplex C).obj X).d (n + 1) n =
      TruncatedAlternatingFaceMapComplex.objD X n := by
  exact TruncatedAlternatingFaceMapComplex.obj_d X n

/-- For a morphism f : X ⟶ Y of semisimplicial objects in a preadditive category C, the degree-n
component of (truncatedAlternatingFaceMapComplex C).map f equals f.app (op ⦋n⦌ₛ) for every n :
ℕ. -/
@[simp]
theorem truncatedAlternatingFaceMapComplex_map_f {X Y : SemiSimplicialObject C}
    (f : X ⟶ Y) (n : ℕ) :
    ((truncatedAlternatingFaceMapComplex C).map f).f n = f.app (op ⦋n⦌ₛ) := rfl

/-- For a preadditive category C, the last-face-omitted alternating-complex functor is additive.
It sends f + g to map f + map g and the zero semisimplicial morphism to the zero chain map;
these equalities hold in every degree. -/
instance truncatedAlternatingFaceMapComplexAdditive :
    (truncatedAlternatingFaceMapComplex C).Additive where

end AlgebraicTopology
