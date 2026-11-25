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
# Scalar detection on an actual finite split family

A recombination operator that acts by prescribed scalars on actual split
images also acts by those scalars after each actual projection. The finite
projector sum and the cross-image equations prove this second equation;
commutation with the projections is not an additional input.

If the scalar on an image is monic, every map annihilated by the original
map has zero projection to that image. When exactly one image is allowed
to survive, the actual kernel inclusion is fixed by its projector. If that
image is itself annihilated, its actual inclusion and projection construct
an isomorphism with the actual kernel.

The category is preadditive and linear over an arbitrary semiring. A kernel
is required only for the kernel isomorphism. No countable coproduct or
exactness hypothesis is needed.
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
/-- Scalar action on the actual image inclusions implies the corresponding
post-projection equation, by the actual finite split decomposition. -/
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
/-- Monic scalar action on an actual image detects the corresponding
projection of every map annihilated by the original map. -/
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
/-- If all other scalar actions are monic, every annihilated map is fixed
by the actual distinguished image projector. -/
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
/-- The actual distinguished inclusion and projection give an actual
kernel isomorphism when that image is annihilated and the other image
scalars are monic. This concerns the kernel of the supplied map. -/
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
@[reassoc]
theorem finiteSplitScalarKernelIso_hom_ι [HasKernel d] (j : ℕ)
    (hregular : ∀ k, k ≤ N → k ≠ j → Mono (a k • 𝟙 (F k)))
    (hzero : i j ≫ d = 0) :
    (finiteSplitScalarKernelIso F i p hsplit hcross N hsupport hsum d m a hweight
      j hregular hzero).hom ≫ kernel.ι d = i j :=
  kernel.lift_ι _ _ _

end CategoryTheory.Limits
