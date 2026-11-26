/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Scalar detection in finite split decompositions

Let C be preadditive and linear over a semiring R. Suppose maps i_j : F_j → X and p_j : X →
F_j satisfy i_j ≫ p_j = id_{F_j}, i_j ≫ p_k = 0 for j ≠ k, p_j = 0 for j > N and Σ_{j≤N} p_j ≫
i_j = id_X. For d : X → Y, m : Y → X and scalars a_j, assume i_j ≫ d ≫ m = a_j • i_j for j ≤
N.

The finite decomposition implies d ≫ m ≫ p_j = a_j • p_j for every j. If multiplication by a_j
on F_j is monic, every map f with f ≫ d = 0 has f ≫ p_j = 0. If all other supported scalar
maps are monic, such f satisfies f ≫ p_j ≫ i_j = f. When also i_j ≫ d = 0, the maps i_j and
p_j identify F_j with Ker(d), provided that kernel exists. Scalar, object and morphism
universes are independent.
-/

@[expose] public section

noncomputable section

universe r u v

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace CategoryTheory.Limits

variable {R : Type r} [Semiring R]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
    (F : ℕ → C) {X Y : C}
    (i : ∀ j, F j ⟶ X) (p : ∀ j, X ⟶ F j)
    (hsplit : ∀ j, i j ≫ p j = 𝟙 (F j))
    (hcross : ∀ j k, j ≠ k → i j ≫ p k = 0)
    (N : ℕ) (hsupport : ∀ j, N < j → p j = 0)
    (hsum : (∑ j : Fin (N + 1), p j.val ≫ i j.val) = 𝟙 X)
    (d : X ⟶ Y) (m : Y ⟶ X) (a : ℕ → R)
    (hweight : ∀ j, j ≤ N → i j ≫ d ≫ m = a j • i j)

include hsplit hcross hsupport hsum hweight in
/-- Scalar action on projections of a finite split decomposition.

Let C be R-linear and preadditive, and let (i_j,p_j) be an orthogonal split decomposition of X
with p_j = 0 for j > N and Σ_{j≤N} p_j ≫ i_j = id_X. If i_j ≫ d ≫ m = a_j • i_j on every
supported summand, then d ≫ m ≫ p_j = a_j • p_j for all j : ℕ. Here R is any semiring. -/
theorem finiteSplit_operator_projection (j : ℕ) :
    d ≫ m ≫ p j = a j • p j := by
  classical
  calc
    d ≫ m ≫ p j =
        (∑ k : Fin (N + 1), p k.val ≫ i k.val) ≫ (d ≫ m) ≫ p j := by
      rw [hsum, Category.id_comp, Category.assoc]
    _ = ∑ k : Fin (N + 1), p k.val ≫ i k.val ≫ (d ≫ m) ≫ p j := by
      simp only [Preadditive.sum_comp, Category.assoc]
    _ = ∑ k : Fin (N + 1), a k.val • (p k.val ≫ i k.val ≫ p j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Category.assoc (i k.val) (d ≫ m) (p j),
        hweight k.val (Nat.le_of_lt_succ k.isLt)]
      simp only [Linear.comp_smul, Linear.smul_comp]
    _ = a j • p j := by
      by_cases hj : j ≤ N
      · let j₀ : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
        rw [Finset.sum_eq_single j₀]
        · simp only [j₀, hsplit j, Category.comp_id]
        · intro k _ hne
          have hkj : k.val ≠ j := fun h => hne (Fin.ext h)
          rw [hcross k.val j hkj, comp_zero, smul_zero]
        · simp
      · have hj' : N < j := Nat.lt_of_not_ge hj
        rw [hsupport j hj']
        simp only [comp_zero, smul_zero, Finset.sum_const_zero]

include hsplit hcross hsupport hsum hweight in
/-- Vanishing of a projection detected by a monic scalar action.

For a finite orthogonal split decomposition of X in an R-linear preadditive category, suppose
d ≫ m acts on each inclusion by its scalar a_j. If f : Z → X satisfies f ≫ d = 0 and a_j •
id_{F_j} is monic, then f ≫ p_j = 0. The projection equation and cancellation of the scalar
endomorphism give the conclusion. -/
theorem finiteSplit_projection_zero_of_annihilated_map {Z : C}
    (f : Z ⟶ X) (hf : f ≫ d = 0) (j : ℕ)
    [Mono (a j • 𝟙 (F j))] : f ≫ p j = 0 := by
  apply (cancel_mono (a j • 𝟙 (F j))).mp
  rw [zero_comp]
  calc
    (f ≫ p j) ≫ (a j • 𝟙 (F j)) = f ≫ (a j • p j) := by
      simp only [Linear.comp_smul, Category.comp_id]
    _ = f ≫ d ≫ m ≫ p j := by
      rw [← finiteSplit_operator_projection F i p hsplit hcross N hsupport hsum d m a hweight j]
    _ = 0 := by
      rw [← Category.assoc f d (m ≫ p j), hf, zero_comp]

include hsplit hcross hsupport hsum hweight in
/-- Distinguished projector fixes maps annihilated by the given morphism.

For a finite orthogonal split decomposition indexed through N and scalar action i_k ≫ d ≫ m =
a_k • i_k, fix j. If a_k • id_{F_k} is monic for all k ≤ N with k ≠ j, every f satisfying f ≫
d = 0 obeys f ≫ p_j ≫ i_j = f. All other components vanish by scalar cancellation. -/
theorem finiteSplit_single_projector_of_annihilated_map {Z : C}
    (f : Z ⟶ X) (hf : f ≫ d = 0) (j : ℕ)
    (hregular : ∀ k, k ≤ N → k ≠ j → Mono (a k • 𝟙 (F k))) :
    f ≫ p j ≫ i j = f := by
  classical
  have hoff (k : ℕ) (hk : k ≤ N) (hkj : k ≠ j) : f ≫ p k = 0 := by
    let _ := hregular k hk hkj
    exact finiteSplit_projection_zero_of_annihilated_map
      F i p hsplit hcross N hsupport hsum d m a hweight f hf k
  have hs : f = ∑ k : Fin (N + 1), (f ≫ p k.val) ≫ i k.val := by
    calc
      f = f ≫ (∑ k : Fin (N + 1), p k.val ≫ i k.val) := by
        rw [hsum, Category.comp_id]
      _ = _ := by simp only [Preadditive.comp_sum, Category.assoc]
  by_cases hj : j ≤ N
  · let j₀ : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    have hsumj : (∑ k : Fin (N + 1), (f ≫ p k.val) ≫ i k.val) =
        (f ≫ p j) ≫ i j := by
      refine Finset.sum_eq_single j₀ ?_ ?_
      · intro k _ hne
        have hkj : k.val ≠ j := fun h => hne (Fin.ext h)
        rw [hoff k.val (Nat.le_of_lt_succ k.isLt) hkj, zero_comp]
      · simp
    exact (Category.assoc f (p j) (i j)).symm.trans (hs.trans hsumj).symm
  · have hzero : (∑ k : Fin (N + 1), (f ≫ p k.val) ≫ i k.val) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hkj : k.val ≠ j := by
        intro hkj
        exact hj (hkj ▸ Nat.le_of_lt_succ k.isLt)
      rw [hoff k.val (Nat.le_of_lt_succ k.isLt) hkj, zero_comp]
    have hfzero : f = 0 := hs.trans hzero
    simp only [hfzero, zero_comp]

include hsplit hcross hsupport hsum hweight in
/-- Kernel isomorphism from a distinguished split summand.

In an R-linear preadditive category, suppose X has the finite orthogonal split decomposition
and scalar action i_k ≫ d ≫ m = a_k • i_k. Fix j such that all other supported scalar maps are
monic and i_j ≫ d = 0. If Ker(d) exists, define F_j ≅ Ker(d) with hom kernel.lift d i_j and
inverse kernel.ι d ≫ p_j. -/
def finiteSplitScalarKernelIso [HasKernel d] (j : ℕ)
    (hregular : ∀ k, k ≤ N → k ≠ j → Mono (a k • 𝟙 (F k)))
    (hzero : i j ≫ d = 0) : F j ≅ kernel d where
  hom := kernel.lift d (i j) hzero
  inv := kernel.ι d ≫ p j
  hom_inv_id := by
    rw [← Category.assoc, kernel.lift_ι, hsplit j]
  inv_hom_id := by
    apply (cancel_mono (kernel.ι d)).mp
    rw [Category.assoc, kernel.lift_ι, Category.id_comp]
    simpa only [Category.assoc] using finiteSplit_single_projector_of_annihilated_map
      F i p hsplit hcross N hsupport hsum d m a hweight
      (kernel.ι d) (kernel.condition d) j hregular

include hsplit hcross hsupport hsum hweight in
/-- Inclusion equation for the scalar-detected kernel isomorphism.

Under the finite split-decomposition and scalar-action hypotheses, with all other supported
scalar maps monic and i_j ≫ d = 0, the comparison e_j : F_j ≅ Ker(d) satisfies e_j.hom ≫
kernel.ι d = i_j. Thus its forward map retains the given distinguished inclusion. -/
@[reassoc]
theorem finiteSplitScalarKernelIso_hom_ι [HasKernel d] (j : ℕ)
    (hregular : ∀ k, k ≤ N → k ≠ j → Mono (a k • 𝟙 (F k)))
    (hzero : i j ≫ d = 0) :
    (finiteSplitScalarKernelIso F i p hsplit hcross N hsupport hsum d m a hweight
      j hregular hzero).hom ≫ kernel.ι d = i j :=
  kernel.lift_ι _ _ _

end CategoryTheory.Limits
