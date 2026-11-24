/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.ShuffleFilling

/-!
# Shuffle Filling Test
-/

set_option pp.universes true

open CategoryTheory Limits MonoidalCategory Opposite

namespace SSet

open MonoidalClosed

/-! # Smoke / regression tests for `ShuffleFilling` (the supporting result)

Checks:
(a) The two cell inputs of `ShuffleBridges.lean` hold for
    every quasicategory, in both named and unfolded form,
    including the corner cases `n = 0` (where the diagonal
    phases are empty).
(b) The unconditional corollaries: horn-prism extension along
    `∂Δ[n].ι` through the `ShuffleBridges` functor bridges.
(c) Diagonal coordinate functions, the lexicographic code,
    filtration endpoints, attaching-horn signatures, and the
    special-edge identifications compute as stated.
(d) The cells are used at their stated types only: the
    extension conclusions are about `shuffleInit0` /
    `shuffleInit2`, with the special edges `v₀` / `v₂` as in
    `ShuffleBridges.lean`.
-/

universe u

open scoped Simplicial

-- (a) the two cell extensions, named form.

example (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    ShuffleHornZeroCellExtension n C :=
  shuffleHornZeroCellExtension_of_quasicategory n C

example (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    ShuffleHornTwoCellExtension n C :=
  shuffleHornTwoCellExtension_of_quasicategory n C

example (C : SSet.{u}) [Quasicategory C] :
    ShuffleHornZeroCellExtension 0 C :=
  shuffleHornZeroCellExtension_of_quasicategory 0 C

example (C : SSet.{u}) [Quasicategory C] :
    ShuffleHornTwoCellExtension 0 C :=
  shuffleHornTwoCellExtension_of_quasicategory 0 C

-- (a) unfolded form: extension over `Δ[n] ⊗ Δ[2]` extending
-- only the initial datum along `(shuffleInit0 n).ι`.

example (n : ℕ) (C : SSet.{u}) [Quasicategory C]
    (φ₀ : ((shuffleInit0 n :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : (Edge.mk' (φ₀.app _ ⟨shuffleVert0 n,
        shuffleVert0_mem_shuffleInit0 n⟩)).IsEquivalence) :
    ∃ P : (Δ[n] ⊗ Δ[2] : SSet.{u}) ⟶ C,
      (shuffleInit0 n).ι ≫ P = φ₀ :=
  exists_extension_of_unionProd_boundary_horn_zero φ₀ hVert

example (n : ℕ) (C : SSet.{u}) [Quasicategory C]
    (φ₀ : ((shuffleInit2 n :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : (Edge.mk' (φ₀.app _ ⟨shuffleVert2 n,
        shuffleVert2_mem_shuffleInit2 n⟩)).IsEquivalence) :
    ∃ P : (Δ[n] ⊗ Δ[2] : SSet.{u}) ⟶ C,
      (shuffleInit2 n).ι ≫ P = φ₀ :=
  exists_extension_of_unionProd_boundary_horn_two φ₀ hVert

-- (b) unconditional horn-prism extension along `∂Δ[n].ι`.

example (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    PrismTwoHornZeroExtension ∂Δ[n].ι C :=
  prismTwoHornZeroExtension_boundary_of_shuffleCell
    (shuffleHornZeroCellExtension_of_quasicategory n C)

example (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    PrismTwoHornTwoExtension ∂Δ[n].ι C :=
  prismTwoHornTwoExtension_boundary_of_shuffleCell
    (shuffleHornTwoCellExtension_of_quasicategory n C)

-- (c) diagonal coordinate functions and the code compute.

example : shuffleDiagSnd 0 2 1 = 1 := rfl

example : shuffleDiagSnd 1 2 3 = 2 := rfl

example : shuffleDiagFst 1 3 = 2 := rfl

example : shuffleDiagFst' 2 3 = 2 := rfl

example : shuffleCode 2 1 2 = 5 := rfl

example : shuffleCode 3 0 2 = 2 := rfl

example (n a b : ℕ) : shuffleCode n a (b + 1) =
    shuffleCode n a b + 1 :=
  shuffleCode_succ_right n a b

example {n a b a' b' : ℕ} (hb : b ≤ n) (hb' : b' ≤ n)
    (h : shuffleCode n a b = shuffleCode n a' b') :
    a = a' ∧ b = b' :=
  shuffleCode_inj hb hb' h

-- (c) filtration endpoints.

example (n : ℕ) : shuffleDiagFilt0 n ((n + 1) * (n + 1)) =
    shuffleInit0 n :=
  shuffleDiagFilt0_top

example (n : ℕ) : shuffleTopFilt0 n 0 = ⊤ :=
  shuffleTopFilt0_zero

example (n : ℕ) : shuffleTopFilt0 n ((n + 1) * (n + 1)) =
    shuffleDiagFilt0 n 0 :=
  shuffleTopFilt0_top

example (n : ℕ) : shuffleDiagFilt2 n 0 = shuffleInit2 n :=
  shuffleDiagFilt2_zero

example (n : ℕ) : shuffleTopFilt2 n 0 =
    shuffleDiagFilt2 n ((n + 1) * (n + 1)) :=
  shuffleTopFilt2_zero

example (n : ℕ) : shuffleTopFilt2 n ((n + 1) * (n + 1)) = ⊤ :=
  shuffleTopFilt2_bound

example (_n : ℕ) : shuffleTopFilt0 2 0 = ⊤ :=
  shuffleTopFilt0_zero

-- (c) attaching horns at concrete indices, at stated types.

example :
    (shuffleDiagFilt0 2 (shuffleCode 2 0 2 + 1)).preimage
        (shuffleDiagWMap.{u} 2 0 2 (by omega) (le_refl 2)) =
      (Λ[3, ⟨0, by omega⟩] : (Δ[3] : SSet.{u}).Subcomplex) :=
  shuffleDiagFilt0_preimage_shuffleDiagWMap (by omega) (le_refl 2)

example :
    (shuffleTopFilt0 2 (shuffleCode 2 1 2 + 1)).preimage
        (shuffleTauMap.{u} 2 1 2 (by omega) (le_refl 2)) =
      (Λ[4, ⟨1, by omega⟩] : (Δ[4] : SSet.{u}).Subcomplex) :=
  shuffleTopFilt0_preimage_shuffleTauMap (by omega) (le_refl 2)

example :
    (shuffleDiagFilt2 2 (shuffleCode 2 0 1)).preimage
        (shuffleDiagW'Map.{u} 2 0 1 (by omega) (by omega)) =
      (Λ[3, ⟨2, by omega⟩] : (Δ[3] : SSet.{u}).Subcomplex) :=
  shuffleDiagFilt2_preimage_shuffleDiagW'Map (by omega) (by omega)

example :
    (shuffleTopFilt2 2 (shuffleCode 2 0 1)).preimage
        (shuffleTauMap.{u} 2 0 1 (by omega) (by omega)) =
      (Λ[4, ⟨3, by omega⟩] : (Δ[4] : SSet.{u}).Subcomplex) :=
  shuffleTopFilt2_preimage_shuffleTauMap (by omega) (by omega)

-- (c) special-edge identifications at concrete indices.

example :
    (shuffleTauMap.{u} 1 0 1 (Nat.zero_le 1) (le_refl 1)).app _
        (stdSimplex.edge 3 0 ⟨1, by omega⟩ (Fin.zero_le _)) =
      shuffleVert0 1 :=
  shuffleTauMap_zero_app_edge (le_refl 1)

example :
    (shuffleDiagWMap.{u} 2 0 1 (Nat.zero_le 1) (by omega)).app _
        (stdSimplex.edge 3 0 ⟨1, by omega⟩ (Fin.zero_le _)) =
      shuffleVert0 2 :=
  shuffleDiagWMap_zero_app_edge (by omega) (by omega)

example :
    (shuffleTauMap.{u} 1 0 1 (Nat.zero_le 1) (le_refl 1)).app _
        (stdSimplex.edge 3 ⟨2, by omega⟩ ⟨3, by omega⟩
          (by simp [Fin.le_def])) =
      shuffleVert2 1 :=
  shuffleTauMap_last_app_edge (Nat.zero_le 1)

example :
    (shuffleDiagW'Map.{u} 2 0 2 (Nat.zero_le 2) (le_refl 2)).app _
        (stdSimplex.edge 3 ⟨2, by omega⟩ ⟨3, by omega⟩
          (by simp [Fin.le_def])) =
      shuffleVert2 2 :=
  shuffleDiagW'Map_last_app_edge (by omega)

-- (c) injectivity and face-sharing signatures.

example {n a b : ℕ} (hab : a < b) (hb : b ≤ n) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a + 1, by omega⟩
        (shuffleTau n a b (le_of_lt hab) hb) =
      (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a + 1, by omega⟩
        (shuffleTau n (a + 1) b hab hb) :=
  shuffleTau_δ_succ_left hab hb

example {n a b : ℕ} (hab : a + 1 < b) (hb : b ≤ n) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a + 1, by omega⟩
        (shuffleDiagW n a b (by omega) hb) =
      (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a + 1, by omega⟩
        (shuffleDiagW n (a + 1) b (le_of_lt hab) hb) :=
  shuffleDiagW_δ_succ hab hb

example {n a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) :
    Function.Injective
      (prodStdSimplex.objEquiv.{u} (shuffleTau.{u} n a b hab hb)) :=
  shuffleTau_objEquiv_injective.{u} hab hb

example {n : ℕ}
    {z : (Δ[n] ⊗ Δ[2] : SSet.{u}) _⦋n + 2⦌}
    (hz : z ∈ (Δ[n] ⊗ Δ[2]).nonDegenerate (n + 2)) :
    ∃ (a b : ℕ) (hab : a ≤ b) (hb : b ≤ n),
      shuffleTau n a b hab hb = z :=
  exists_shuffleTau_of_nonDegenerate hz

-- Signature checks for the main declarations.

end SSet
