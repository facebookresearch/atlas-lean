/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestOps
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMasks
public import Mathlib.LinearAlgebra.StdBasis

/-! Row operations on masks are linear maps on the actual binary coordinate vectors.

Decoding a mask turns each row operation into the linear map `v ↦ v + ⟨r, v⟩ e_j`, and a list
of row operations into the composite. A composite that agrees with a linear map on the 24 basis
masks therefore agrees with it on every mask. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

private theorem zmod_xor (a c : Bool) :
    (if (a ^^ c) = true then (1 : ZMod 2) else 0) =
      (if c = true then 1 else 0) + (if a = true then 1 else 0) := by
  cases a <;> cases c <;> decide

/-- The mask parity against `r` is the binary inner product with the coordinates of `r`. -/
theorem tenthForestParityUpTo_zmod (r b n : ℕ) :
    (if tenthForestParityUpTo r b n then (1 : ZMod 2) else 0) =
      ∑ i : Fin n, if r.testBit i.val && b.testBit i.val then (1 : ZMod 2) else 0 := by
  induction n with
  | zero => simp [tenthForestParityUpTo]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih]
    simp only [tenthForestParityUpTo]
    exact zmod_xor _ _

/-- The linear map of one row operation on binary coordinate vectors. -/
def tenthForestRowLinear (j r : ℕ) : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun v := v + (∑ i : Fin 24, if r.testBit i.val then v i else 0) •
    monsterCo1GeometryBinaryMaskDecode (2 ^ j)
  map_add' v w := by
    simp only [Pi.add_apply]
    rw [show (∑ i : Fin 24, if r.testBit i.val then v i + w i else 0) =
        (∑ i : Fin 24, if r.testBit i.val then v i else 0) +
          (∑ i : Fin 24, if r.testBit i.val then w i else 0) by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp]
    rw [add_smul]
    abel
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show (∑ i : Fin 24, if r.testBit i.val then a * v i else 0) =
        a * ∑ i : Fin 24, if r.testBit i.val then v i else 0 by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp]
    rw [smul_add, mul_smul]

theorem tenthForestRowMap_decode (j r b : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (tenthForestRowMap j r b) =
      tenthForestRowLinear j r (monsterCo1GeometryBinaryMaskDecode b) := by
  have hpar : (if tenthForestParity r b then (1 : ZMod 2) else 0) =
      ∑ i : Fin 24, if r.testBit i.val then monsterCo1GeometryBinaryMaskDecode (n := 24) b i
        else 0 := by
    rw [tenthForestParity, tenthForestParityUpTo_zmod]
    apply Finset.sum_congr rfl
    intro i _
    simp only [monsterCo1GeometryBinaryMaskDecode]
    cases r.testBit i.val <;> cases b.testBit i.val <;> simp
  change _ = monsterCo1GeometryBinaryMaskDecode b + _ • _
  rw [← hpar, tenthForestRowMap]
  cases tenthForestParity r b with
  | false => simp
  | true =>
    simp only [↓reduceIte, one_smul]
    exact monsterCo1GeometryBinaryMaskDecode_xor b (2 ^ j)

/-- The composite linear map of a list of row operations (the last one acts first). -/
def tenthForestOpsLinear (ops : List (ℕ × ℕ)) : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  ops.foldr (fun o L => (tenthForestRowLinear o.1 o.2).comp L) LinearMap.id

theorem tenthForestOpsMap_decode (ops : List (ℕ × ℕ)) (b : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (tenthForestOpsMap ops b) =
      tenthForestOpsLinear ops (monsterCo1GeometryBinaryMaskDecode b) := by
  induction ops with
  | nil => rfl
  | cons o ops ih =>
    simp only [tenthForestOpsMap, List.foldr_cons, tenthForestOpsLinear, LinearMap.comp_apply]
      at ih ⊢
    rw [tenthForestRowMap_decode, ih]

theorem tenthForest_decode_two_pow (j : Fin 24) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val) = Pi.single j 1 := by
  funext k
  simp only [monsterCo1GeometryBinaryMaskDecode, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : k = j
  · subst h; simp
  · have : j.val ≠ k.val := fun e => h (Fin.ext e.symm)
    simp [h, this]

/-- Agreement on the 24 basis masks gives agreement on every mask. -/
theorem tenthForestOpsMap_decode_of_basis (ops : List (ℕ × ℕ))
    (R : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hbasis : ∀ j : Fin 24, monsterCo1GeometryBinaryMaskDecode (n := 24)
      (tenthForestOpsMap ops (2 ^ j.val)) = R (monsterCo1GeometryBinaryMaskDecode (2 ^ j.val)))
    (b : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (tenthForestOpsMap ops b) =
      R (monsterCo1GeometryBinaryMaskDecode b) := by
  have hL : tenthForestOpsLinear ops = R := by
    apply (Pi.basisFun (ZMod 2) (Fin 24)).ext
    intro j
    have h := hbasis j
    rw [tenthForestOpsMap_decode, tenthForest_decode_two_pow] at h
    simpa only [Pi.basisFun_apply] using h
  rw [tenthForestOpsMap_decode, hL]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
