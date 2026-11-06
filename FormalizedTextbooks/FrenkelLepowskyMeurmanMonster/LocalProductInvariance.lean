/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Product preservation for the actual local Griess representation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortSumCovariance

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

noncomputable def conwayMatrixMatrixProduct (a b : Matrix (Fin 24) (Fin 24) ℝ) :
    Matrix (Fin 24) (Fin 24) ℝ := (2 : ℝ) • (a * b + b * a)

noncomputable def conwayMatrixShortProduct (a : Matrix (Fin 24) (Fin 24) ℝ)
    (x : GriessShortIndex → ℝ) : GriessShortIndex → ℝ :=
  fun r => conwayShortPairing a r * x r

theorem conwayMatrixMatrixProduct_covariant (f : localFiberSubgroup)
    (a b : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayMatrixAction f.val.2 (conwayMatrixMatrixProduct a b) =
      conwayMatrixMatrixProduct (conwayMatrixAction f.val.2 a) (conwayMatrixAction f.val.2 b) := by
  simp only [conwayMatrixMatrixProduct, map_smul, map_add, conwayMatrixAction_mul]

theorem conwayMatrixShortProduct_covariant (f : localFiberSubgroup)
    (a : Matrix (Fin 24) (Fin 24) ℝ) (x : GriessShortIndex → ℝ) :
    localShortRepresentation f (conwayMatrixShortProduct a x) =
      conwayMatrixShortProduct (conwayMatrixAction f.val.2 a) (localShortRepresentation f x) :=
  localShortRepresentation_matrix_product f a x

/-- Conway's raw product is exactly the sum of its six prescribed block rules. -/
theorem conwayRawProduct_eq_blocks (x y : ConwayRawSpace) :
    conwayRawProduct x y =
      (conwayMatrixMatrixProduct x.1 y.1 + conwayShortShortMatrix x.2.1 y.2.1 +
        conwayTensorTensorMatrix x.2.2 y.2.2,
      (conwayMatrixShortProduct x.1 y.2.1 + conwayMatrixShortProduct y.1 x.2.1 +
        conwayShortShortProduct x.2.1 y.2.1 + conwayTensorTensorShort x.2.2 y.2.2,
      conwayMatrixTensorProduct x.1 y.2.2 + conwayMatrixTensorProduct y.1 x.2.2 +
        conwayShortTensorProduct x.2.1 y.2.2 + conwayShortTensorProduct y.2.1 x.2.2)) := by
  apply Prod.ext
  · funext i j
    change (conwayRawProduct x y).1 i j =
      conwayMatrixMatrixProduct x.1 y.1 i j + conwayShortShortMatrix x.2.1 y.2.1 i j +
        conwayTensorTensorMatrix x.2.2 y.2.2 i j
    rw [conwayShortShortMatrix_apply, conwayTensorTensorMatrix_apply]
    simp only [conwayRawProduct, conwayMatrixMatrixProduct, Matrix.smul_apply,
      Matrix.add_apply, Matrix.mul_apply, smul_eq_mul, Finset.sum_add_distrib]
  · apply Prod.ext
    · funext r
      change (conwayRawProduct x y).2.1 r =
        conwayMatrixShortProduct x.1 y.2.1 r + conwayMatrixShortProduct y.1 x.2.1 r +
          conwayShortShortProduct x.2.1 y.2.1 r + conwayTensorTensorShort x.2.2 y.2.2 r
      rw [conwayTensorTensorShort_apply]
      rfl
    · funext t i
      change (conwayRawProduct x y).2.2 t i =
        conwayMatrixTensorProduct x.1 y.2.2 t i + conwayMatrixTensorProduct y.1 x.2.2 t i +
          conwayShortTensorProduct x.2.1 y.2.2 t i + conwayShortTensorProduct y.2.1 x.2.2 t i
      rw [conwayMatrixTensorProduct_apply, conwayMatrixTensorProduct_apply,
        conwayShortTensorProduct_apply, conwayShortTensorProduct_apply]
      simp only [conwayRawProduct, add_mul, Finset.sum_add_distrib]
      ring

/-- Each of Conway's six rules commutes with the actual local fiber-product action. -/
theorem localConwayRawRepresentation_product (f : localFiberSubgroup)
    (x y : ConwayRawSpace) :
    localConwayRawRepresentation f (conwayRawProduct x y) =
      conwayRawProduct (localConwayRawRepresentation f x) (localConwayRawRepresentation f y) := by
  rw [conwayRawProduct_eq_blocks, localConwayRawRepresentation_apply,
    localConwayRawRepresentation_apply, localConwayRawRepresentation_apply,
    conwayRawProduct_eq_blocks]
  simp only [map_add, conwayMatrixMatrixProduct_covariant,
    conwayShortShortMatrix_covariant, conwayTensorTensorMatrix_covariant,
    conwayMatrixShortProduct_covariant, conwayShortShortProduct_covariant,
    conwayTensorTensorShort_covariant, conwayMatrixTensorProduct_covariant,
    conwayShortTensorProduct_covariant]


theorem conwayMatrixMatrixProduct_symmetric (a b : Matrix (Fin 24) (Fin 24) ℝ)
    (ha : ∀ i j, a i j = a j i) (hb : ∀ i j, b i j = b j i) :
    ∀ i j, conwayMatrixMatrixProduct a b i j = conwayMatrixMatrixProduct a b j i := by
  have hta : a.transpose = a := by ext i j; exact ha j i
  have htb : b.transpose = b := by ext i j; exact hb j i
  have ht : (conwayMatrixMatrixProduct a b).transpose = conwayMatrixMatrixProduct a b := by
    simp only [conwayMatrixMatrixProduct, Matrix.transpose_smul, Matrix.transpose_add,
      Matrix.transpose_mul, hta, htb]
    rw [add_comm]
  intro i j
  exact congrArg (fun m : Matrix (Fin 24) (Fin 24) ℝ => m j i) ht

theorem conwayShortShortMatrix_symmetric (x y : GriessShortIndex → ℝ) :
    ∀ i j, conwayShortShortMatrix x y i j = conwayShortShortMatrix x y j i := by
  intro i j
  rw [conwayShortShortMatrix_apply, conwayShortShortMatrix_apply]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  split <;> ring

theorem conwayTensorTensorMatrix_symmetric (x y : SpinIndex → Fin 24 → ℝ) :
    ∀ i j, conwayTensorTensorMatrix x y i j = conwayTensorTensorMatrix x y j i := by
  intro i j
  rw [conwayTensorTensorMatrix_apply, conwayTensorTensorMatrix_apply]
  apply congrArg (fun z : ℝ => z / 8)
  apply Finset.sum_congr rfl
  intro t _
  simp only [eq_comm]
  ring

/-- Conway's six rules close on the symmetric-matrix subspace. -/
theorem conwayRawProduct_symmetric (x y : ConwayRawSpace)
    (hx : ∀ i j, x.1 i j = x.1 j i) (hy : ∀ i j, y.1 i j = y.1 j i) :
    ∀ i j, (conwayRawProduct x y).1 i j = (conwayRawProduct x y).1 j i := by
  intro i j
  rw [conwayRawProduct_eq_blocks]
  change conwayMatrixMatrixProduct x.1 y.1 i j +
      conwayShortShortMatrix x.2.1 y.2.1 i j + conwayTensorTensorMatrix x.2.2 y.2.2 i j =
    conwayMatrixMatrixProduct x.1 y.1 j i +
      conwayShortShortMatrix x.2.1 y.2.1 j i + conwayTensorTensorMatrix x.2.2 y.2.2 j i
  rw [conwayMatrixMatrixProduct_symmetric x.1 y.1 hx hy i j,
    conwayShortShortMatrix_symmetric x.2.1 y.2.1 i j,
    conwayTensorTensorMatrix_symmetric x.2.2 y.2.2 i j]

/-- The raw product and dictionary product intertwine in both directions. -/
theorem griessProd_encode (x y : GriessSpace) :
    griessConwayEncode (griessProd x y) =
      conwayRawProduct (griessConwayEncode x) (griessConwayEncode y) := by
  rw [griessProd_eq_conwayRawProduct]
  exact griessConwayEncode_decode _
    (conwayRawProduct_symmetric _ _ (griessConwayEncode_symmetric x)
      (griessConwayEncode_symmetric y))

/-- The actual local Griess action preserves Conway's multiplication. -/
theorem localGriessRepresentation_product (f : localFiberSubgroup) (x y : GriessSpace) :
    localGriessRepresentation f (griessProd x y) =
      griessProd (localGriessRepresentation f x) (localGriessRepresentation f y) := by
  apply griessConwayLinear_bijective.1
  apply Subtype.ext
  change griessConwayEncode (localGriessRepresentation f (griessProd x y)) =
    griessConwayEncode (griessProd (localGriessRepresentation f x) (localGriessRepresentation f y))
  rw [localGriessRepresentation_encode, griessProd_encode, griessProd_encode,
    localGriessRepresentation_encode, localGriessRepresentation_encode,
    localConwayRawRepresentation_product]

/-- Product preservation descends to the actual quotient local group H. -/
theorem rhoLocal_product (h : H) (x y : GriessSpace) :
    rhoLocal h (griessProd x y) = griessProd (rhoLocal h x) (rhoLocal h y) := by
  refine Quotient.inductionOn h ?_
  intro f
  exact localGriessRepresentation_product f x y

/-- Every element of the concrete local group acts by a Griess automorphism. -/
theorem rhoLocal_isGriessAuto (h : H) : IsGriessAuto (rhoLocal h) :=
  ⟨rhoLocal_product h, rhoLocal_form h⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
