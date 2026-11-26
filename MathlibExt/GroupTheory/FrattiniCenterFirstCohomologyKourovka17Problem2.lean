/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Frattini
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Vanishing `H¹(G/Φ(G), Z(Φ(G)))` for a non-abelian `p`-group (Kourovka Notebook Problem 17.2)

Kourovka Notebook, Archive of Solved Problems, Problem 17.2 (A. Abdollahi): (P. Schmid). Does there
exist a finite non-abelian `p`-group `G` such that `H¹(G/Φ(G), Z(Φ(G))) = 0`?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.2 (A.
Abdollahi). UnsolvedMath record UM-00701304 (`KOU-17.2`), dataset ulamai/UnsolvedMath v1.8.0.

`Φ(G)` is `frattini G` and `G/Φ(G)` acts on `Z(Φ(G))` by conjugation. A 1-cocycle of `G/Φ(G)` is
recorded by its inflation to `G`: a map `δ : G → Z(Φ(G))` with `δ(gh) = δ(g) · g δ(h) g⁻¹` that is
trivial on `Φ(G)`; these maps are exactly the inflated cocycles, since `Φ(G)` centralizes `Z(Φ(G))`.
`H¹ = 0` says each such map is a coboundary `δ(g) = g a g⁻¹ a⁻¹`, `a ∈ Z(Φ(G))`.

A. Abdollahi (J. Algebra 342 (2011), 154–160) gives examples of order 2^8.
Here `nonabelianPGroupFrattiniCenterH1Trivial_holds` is proved using the order-2^8 subgroup
of unitriangular `5 × 5` matrices over `ZMod 2` defined by `a₁₂ = a₂₃` and `a₃₄ = a₄₅`.
-/

open Matrix

namespace MathlibExt.GroupTheory.FrattiniCenterFirstCohomologyKourovka17Problem2Wanted

namespace UT5

/-- Unitriangular `5 × 5` matrices over `ZMod 2` whose superdiagonal lies in the
two-dimensional subspace `a₁₂ = a₂₃`, `a₃₄ = a₄₅`. -/
def UT5Pred (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Prop :=
  (∀ i, M i i = 1) ∧ (∀ i j, M i j = 0 ∨ i ≤ j) ∧ M 0 1 = M 1 2 ∧ M 2 3 = M 3 4

instance decidableUT5Pred : DecidablePred UT5Pred := fun M =>
  @instDecidableAnd _ _
    (@Fintype.decidableForallFintype _ _ (fun _ => inferInstance) inferInstance)
    (@instDecidableAnd _ _
      (@Fintype.decidableForallFintype _ _ (fun i =>
        @Fintype.decidableForallFintype _ _ (fun _ => inferInstance) inferInstance) inferInstance)
      (@instDecidableAnd _ _ inferInstance inferInstance))

/-- The lower-triangular entries of a matrix satisfying `UT5Pred` vanish. -/
theorem UT5Pred.lower {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : UT5Pred M)
    {i j : Fin 5} (hij : j < i) : M i j = 0 :=
  (h.2.1 i j).resolve_right (not_le_of_gt hij)

abbrev G5 := { M : Matrix (Fin 5) (Fin 5) (ZMod 2) // UT5Pred M }

theorem mul_two_zmod2 (a : ZMod 2) : a * 2 = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [h, mul_zero]

theorem two_mul_zmod2 (a : ZMod 2) : 2 * a = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [h, zero_mul]

namespace Lemmas

def invMat (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, M 0 1, M 0 2 + M 0 1 * M 1 2,
      M 0 3 + M 0 1 * M 1 3 + M 0 2 * M 2 3 + M 0 1 * M 1 2 * M 2 3,
      M 0 4 + M 0 1 * M 1 4 + M 0 2 * M 2 4 + M 0 3 * M 3 4
        + M 0 1 * M 1 2 * M 2 4 + M 0 1 * M 1 3 * M 3 4
        + M 0 2 * M 2 3 * M 3 4 + M 0 1 * M 1 2 * M 2 3 * M 3 4;
    0, 1, M 1 2, M 1 3 + M 1 2 * M 2 3,
      M 1 4 + M 1 2 * M 2 4 + M 1 3 * M 3 4 + M 1 2 * M 2 3 * M 3 4;
    0, 0, 1, M 2 3, M 2 4 + M 2 3 * M 3 4;
    0, 0, 0, 1, M 3 4;
    0, 0, 0, 0, 1]

theorem mul_invMat (M : Matrix (Fin 5) (Fin 5) (ZMod 2))
    (hdiag : ∀ i, M i i = 1) (hlow : ∀ i j, j < i → M i j = 0) :
    M * invMat M = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invMat, Matrix.mul_apply, Fin.sum_univ_five, hdiag, hlow,
      CharTwo.add_self_eq_zero] <;> ring_nf <;> simp [mul_two_zmod2]

theorem invMat_mul (M : Matrix (Fin 5) (Fin 5) (ZMod 2))
    (hdiag : ∀ i, M i i = 1) (hlow : ∀ i j, j < i → M i j = 0) :
    invMat M * M = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invMat, Matrix.mul_apply, Fin.sum_univ_five, hdiag, hlow,
      CharTwo.add_self_eq_zero] <;> ring_nf <;> simp [mul_two_zmod2]
end Lemmas

namespace Lemmas

theorem mul_diag (a b : G5) (i : Fin 5) : (a.1 * b.1) i i = 1 := by
  obtain ⟨hda, hla0, -, -⟩ := a.2
  obtain ⟨hdb, hlb0, -, -⟩ := b.2
  have hla : ∀ i j, j < i → a.1 i j = 0 := fun i j h =>
    UT5Pred.lower ⟨hda, hla0, a.2.2.2.1, a.2.2.2.2⟩ h
  have hlb : ∀ i j, j < i → b.1 i j = 0 := fun i j h =>
    UT5Pred.lower ⟨hdb, hlb0, b.2.2.2.1, b.2.2.2.2⟩ h
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · simp [hda, hdb]
  · intro k _ hki
    rcases lt_trichotomy k i with h | h | h
    · simp [hla i k h]
    · exact absurd h hki
    · simp [hlb k i h]
  · simp

theorem mul_lower (a b : G5) (i j : Fin 5) (h : j < i) : (a.1 * b.1) i j = 0 := by
  obtain ⟨-, hla0, -, -⟩ := a.2
  obtain ⟨-, hlb0, -, -⟩ := b.2
  have hla : ∀ i j, j < i → a.1 i j = 0 := fun i j h => UT5Pred.lower a.2 h
  have hlb : ∀ i j, j < i → b.1 i j = 0 := fun i j h => UT5Pred.lower b.2 h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rcases lt_trichotomy k i with hki | hki | hki
  · simp [hla i k hki]
  · subst hki; simp [hlb k j h]
  · simp [hlb k j (lt_trans h hki)]

theorem mul_sup01 (a b : G5) : (a.1 * b.1) 0 1 = a.1 0 1 + b.1 0 1 := by
  obtain ⟨hda, -, -, -⟩ := a.2
  obtain ⟨hdb, hlb, -, -⟩ := b.2
  have hla : ∀ i j, j < i → a.1 i j = 0 := fun i j h => UT5Pred.lower a.2 h
  have hlb : ∀ i j, j < i → b.1 i j = 0 := fun i j h => UT5Pred.lower b.2 h
  rw [Matrix.mul_apply, Fin.sum_univ_five]
  simp [hda 0, hdb 1, hlb 2 1 (by decide), hlb 3 1 (by decide), hlb 4 1 (by decide)]
  ring

theorem mul_sup12 (a b : G5) : (a.1 * b.1) 1 2 = a.1 1 2 + b.1 1 2 := by
  obtain ⟨hda, hla, -, -⟩ := a.2
  obtain ⟨hdb, hlb, -, -⟩ := b.2
  have hla : ∀ i j, j < i → a.1 i j = 0 := fun i j h => UT5Pred.lower a.2 h
  have hlb : ∀ i j, j < i → b.1 i j = 0 := fun i j h => UT5Pred.lower b.2 h
  rw [Matrix.mul_apply, Fin.sum_univ_five]
  simp [hda 1, hdb 2, hla 1 0 (by decide), hlb 3 2 (by decide), hlb 4 2 (by decide)]
  ring

theorem mul_sup23 (a b : G5) : (a.1 * b.1) 2 3 = a.1 2 3 + b.1 2 3 := by
  obtain ⟨hda, hla, -, -⟩ := a.2
  obtain ⟨hdb, hlb, -, -⟩ := b.2
  have hla : ∀ i j, j < i → a.1 i j = 0 := fun i j h => UT5Pred.lower a.2 h
  have hlb : ∀ i j, j < i → b.1 i j = 0 := fun i j h => UT5Pred.lower b.2 h
  rw [Matrix.mul_apply, Fin.sum_univ_five]
  simp [hda 2, hdb 3, hla 2 0 (by decide), hla 2 1 (by decide), hlb 4 3 (by decide)]
  ring

theorem mul_sup34 (a b : G5) : (a.1 * b.1) 3 4 = a.1 3 4 + b.1 3 4 := by
  obtain ⟨hda, hla, -, -⟩ := a.2
  obtain ⟨hdb, -, -, -⟩ := b.2
  have hla : ∀ i j, j < i → a.1 i j = 0 := fun i j h => UT5Pred.lower a.2 h
  have hlb : ∀ i j, j < i → b.1 i j = 0 := fun i j h => UT5Pred.lower b.2 h
  rw [Matrix.mul_apply, Fin.sum_univ_five]
  simp [hda 3, hdb 4, hla 3 0 (by decide), hla 3 1 (by decide), hla 3 2 (by decide)]
  ring

theorem mul_pred (a b : G5) : UT5Pred (a.1 * b.1) :=
  ⟨fun i => mul_diag a b i,
    fun i j => by
      by_cases h : j < i
      · exact Or.inl (mul_lower a b i j h)
      · exact Or.inr (not_lt.mp h),
    by rw [mul_sup01, mul_sup12, a.2.2.2.1, b.2.2.2.1],
    by rw [mul_sup23, mul_sup34, a.2.2.2.2, b.2.2.2.2]⟩

theorem inv_pred (a : G5) : UT5Pred (invMat a.1) := by
  obtain ⟨hda, _hla, hra, hrb⟩ := a.2
  refine ⟨fun i => by fin_cases i <;> simp [invMat], fun i j => ?_, ?_, ?_⟩
  · by_cases h : j < i
    · fin_cases i <;> fin_cases j <;> simp [invMat] at h ⊢
    · exact Or.inr (not_lt.mp h)
  · simp [invMat, hra]
  · simp [invMat, hrb]

instance instMulG5 : Mul G5 := ⟨fun a b => ⟨a.1 * b.1, mul_pred a b⟩⟩

instance instOneG5 : One G5 := ⟨⟨1, by
  refine ⟨fun i => by simp, fun i j => ?_, ?_, ?_⟩
  · by_cases h : j < i
    · exact Or.inl (Matrix.one_apply_ne (Ne.symm (ne_of_lt h)))
    · exact Or.inr (not_lt.mp h)
  · simp
  · simp⟩⟩

instance instInvG5 : Inv G5 := ⟨fun a => ⟨invMat a.1, inv_pred a⟩⟩

instance instGroupG5 : Group G5 where
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc _ _ _)
  one_mul a := Subtype.ext (Matrix.one_mul _)
  mul_one a := Subtype.ext (Matrix.mul_one _)
  inv_mul_cancel a := Subtype.ext (invMat_mul a.1 a.2.1 (fun i j h => UT5Pred.lower a.2 h))

/-- The superdiagonal-zero subgroup: the matrices whose `(0, 1)` and `(2, 3)`
entries vanish. -/
private def phiSub : Subgroup G5 where
  carrier := {g | g.1 0 1 = 0 ∧ g.1 2 3 = 0}
  one_mem' := ⟨by show (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 1 = 0; simp,
    by show (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) 2 3 = 0; simp⟩
  mul_mem' := by
    intro a b ha hb
    refine ⟨?_, ?_⟩
    · show (a.1 * b.1) 0 1 = 0
      rw [mul_sup01, ha.1, hb.1]; simp
    · show (a.1 * b.1) 2 3 = 0
      rw [mul_sup23, ha.2, hb.2]; simp
  inv_mem' := by
    intro a ha
    refine ⟨?_, ?_⟩
    · show (invMat a.1) 0 1 = 0
      simp [invMat, ha.1]
    · show (invMat a.1) 2 3 = 0
      simp [invMat, ha.2]

private theorem mem_phiSub {g : G5} : g ∈ phiSub ↔ g.1 0 1 = 0 ∧ g.1 2 3 = 0 :=
  Iff.rfl

private theorem inv_sup01 (g : G5) : (g⁻¹).1 0 1 = g.1 0 1 := by
  have hi : (g⁻¹).1 = invMat g.1 := rfl
  rw [hi]; simp [invMat]

private theorem inv_sup23 (g : G5) : (g⁻¹).1 2 3 = g.1 2 3 := by
  have hi : (g⁻¹).1 = invMat g.1 := rfl
  rw [hi]; simp [invMat]

private theorem inv_entry02 (g : G5) : (g⁻¹).1 0 2 = g.1 0 2 + g.1 0 1 * g.1 1 2 := by
  have hi : (g⁻¹).1 = invMat g.1 := rfl
  rw [hi]; simp [invMat]

private theorem inv_entry24 (g : G5) : (g⁻¹).1 2 4 = g.1 2 4 + g.1 2 3 * g.1 3 4 := by
  have hi : (g⁻¹).1 = invMat g.1 := rfl
  rw [hi]; simp [invMat]

/-- Every element of `ZMod 2` is `0` or `1`. -/
private theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-- Product formulas for the `(0, 3)`, `(0, 4)`, `(1, 3)`, `(1, 4)` entries of a
product of two superdiagonal-zero matrices. -/
private theorem phi_mul_coords {a b : G5} (ha : a ∈ phiSub) (hb : b ∈ phiSub) :
    (a.1 * b.1) 0 3 = a.1 0 3 + b.1 0 3 ∧
    (a.1 * b.1) 0 4 = a.1 0 4 + b.1 0 4 + a.1 0 2 * b.1 2 4 ∧
    (a.1 * b.1) 1 3 = a.1 1 3 + b.1 1 3 ∧
    (a.1 * b.1) 1 4 = a.1 1 4 + b.1 1 4 := by
  have hda : ∀ i, a.1 i i = 1 := a.2.1
  have hdb : ∀ i, b.1 i i = 1 := b.2.1
  have hla : ∀ i j, j < i → a.1 i j = 0 := fun i j h => UT5Pred.lower a.2 h
  have hlb : ∀ i j, j < i → b.1 i j = 0 := fun i j h => UT5Pred.lower b.2 h
  have ha01 : a.1 0 1 = 0 := ha.1
  have ha23 : a.1 2 3 = 0 := ha.2
  have hb01 : b.1 0 1 = 0 := hb.1
  have hb23 : b.1 2 3 = 0 := hb.2
  have ha12 : a.1 1 2 = 0 := by rw [← a.2.2.2.1]; exact ha.1
  have ha34 : a.1 3 4 = 0 := by rw [← a.2.2.2.2]; exact ha.2
  have hb12 : b.1 1 2 = 0 := by rw [← b.2.2.2.1]; exact hb.1
  have hb34 : b.1 3 4 = 0 := by rw [← b.2.2.2.2]; exact hb.2
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, hda, hdb, hla, hlb, ha01, ha23,
      hb01, hb23, ha12, ha34, hb12, hb34] <;>
    ring_nf <;> simp [mul_two_zmod2, two_mul_zmod2]


end Lemmas

namespace Lemmas

/-- The first generator: superdiagonal `(1, 1, 0, 0)`, all other upper entries `0`. -/
def xMat : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 1, 0, 0, 0;
     0, 1, 1, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1]

/-- The second generator: superdiagonal `(0, 0, 1, 1)`, all other upper entries `0`. -/
def yMat : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 1, 1, 0;
     0, 0, 0, 1, 1;
     0, 0, 0, 0, 1]

def x : G5 := ⟨xMat, by
  refine ⟨fun i => by fin_cases i <;> simp [xMat], fun i j => ?_, ?_, ?_⟩
  · by_cases h : j < i
    · fin_cases i <;> fin_cases j <;> simp [xMat] at h ⊢
    · exact Or.inr (not_lt.mp h)
  · simp [xMat]
  · simp [xMat]⟩

def y : G5 := ⟨yMat, by
  refine ⟨fun i => by fin_cases i <;> simp [yMat], fun i j => ?_, ?_, ?_⟩
  · by_cases h : j < i
    · fin_cases i <;> fin_cases j <;> simp [yMat] at h ⊢
    · exact Or.inr (not_lt.mp h)
  · simp [yMat]
  · simp [yMat]⟩



end Lemmas

namespace Lemmas

private theorem xy_ne : x * y ≠ y * x := by decide

/-- Coordinates on `G5`: the eight free upper-triangular entries. -/
def coordEquiv : G5 ≃ (Fin 8 → ZMod 2) where
  toFun g := ![g.1 0 1, g.1 0 2, g.1 0 3, g.1 0 4, g.1 1 3, g.1 1 4, g.1 2 3, g.1 2 4]
  invFun c := ⟨!![1, c 0, c 1, c 2, c 3;
      0, 1, c 0, c 4, c 5;
      0, 0, 1, c 6, c 7;
      0, 0, 0, 1, c 6;
      0, 0, 0, 0, 1], by
    refine ⟨fun i => by fin_cases i <;> simp, fun i j => ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;>
        first | exact Or.inr (by decide) | exact Or.inl (by simp)
    · simp
    · simp⟩
  left_inv g := by
    obtain ⟨hda, -, hra, hrb⟩ := g.2
    have hlow : ∀ i j, j < i → g.1 i j = 0 := fun i j h => UT5Pred.lower g.2 h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hlow, hda, hra, hrb]
  right_inv c := by
    funext i
    fin_cases i <;> simp

theorem card_eq : Nat.card G5 = 256 := by
  rw [Nat.card_congr coordEquiv]
  simp [Nat.card_eq_fintype_card]

/-- The coordinate matrix with a single `1` at `(0, 2)`. -/
private def e13 : G5 := ⟨!![1, 0, 1, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1], by decide⟩

/-- The coordinate matrix with a single `1` at `(0, 3)`. -/
private def e14 : G5 := ⟨!![1, 0, 0, 1, 0;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1], by decide⟩

/-- The coordinate matrix with a single `1` at `(0, 4)`. -/
private def e15 : G5 := ⟨!![1, 0, 0, 0, 1;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1], by decide⟩

/-- The coordinate matrix with a single `1` at `(1, 3)`. -/
private def e24 : G5 := ⟨!![1, 0, 0, 0, 0;
    0, 1, 0, 1, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1], by decide⟩

/-- The coordinate matrix with a single `1` at `(1, 4)`. -/
private def e25 : G5 := ⟨!![1, 0, 0, 0, 0;
    0, 1, 0, 0, 1;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1], by decide⟩

/-- The coordinate matrix with a single `1` at `(2, 4)`. -/
private def e35 : G5 := ⟨!![1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, 1;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1], by decide⟩

private theorem word_e13 : e13 = x * x := by decide

private theorem word_e35 : e35 = y * y := by decide

private theorem word_e14 : e14 = (y * y) * ((y * x * x) * (y * x * x)) := by decide

private theorem word_e15 : e15 = ((y * x) * (y * x)) * ((y * x) * (y * x)) := by decide

private theorem word_e24 : e24 = ((y * x) * (y * x)) * (x * x) * (y * y) := by
  decide

private theorem word_e25 : e25 = ((y * x * x) * (y * x * x)) * ((x * y * x) * (x * y * x)) := by decide


/-- The factor matrix with `(2, 4)` entry `φ.1 2 4` and no other nonzero
upper-triangular entries. -/
private def f35 (φ : G5) : G5 := ⟨!![1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, φ.1 2 4;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1], by
  refine ⟨fun i => by fin_cases i <;> simp, fun i j => ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first | exact Or.inr (by decide) | exact Or.inl (by simp)
  · simp
  · simp⟩

/-- The factor matrix with `(0, 2)` entry `φ.1 0 2` and no other nonzero
upper-triangular entries. -/
private def f13 (φ : G5) : G5 := ⟨!![1, 0, φ.1 0 2, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1], by
  refine ⟨fun i => by fin_cases i <;> simp, fun i j => ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first | exact Or.inr (by decide) | exact Or.inl (by simp)
  · simp
  · simp⟩

/-- The factor matrix with `(0, 3)` entry `φ.1 0 3` and no other nonzero
upper-triangular entries. -/
private def f14 (φ : G5) : G5 := ⟨!![1, 0, 0, φ.1 0 3, 0;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1], by
  refine ⟨fun i => by fin_cases i <;> simp, fun i j => ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first | exact Or.inr (by decide) | exact Or.inl (by simp)
  · simp
  · simp⟩

/-- The factor matrix with `(1, 3)` entry `φ.1 1 3` and no other nonzero
upper-triangular entries. -/
private def f24 (φ : G5) : G5 := ⟨!![1, 0, 0, 0, 0;
    0, 1, 0, φ.1 1 3, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1], by
  refine ⟨fun i => by fin_cases i <;> simp, fun i j => ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first | exact Or.inr (by decide) | exact Or.inl (by simp)
  · simp
  · simp⟩

/-- The factor matrix with `(1, 4)` entry `φ.1 1 4` and no other nonzero
upper-triangular entries. -/
private def f25 (φ : G5) : G5 := ⟨!![1, 0, 0, 0, 0;
    0, 1, 0, 0, φ.1 1 4;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1], by
  refine ⟨fun i => by fin_cases i <;> simp, fun i j => ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first | exact Or.inr (by decide) | exact Or.inl (by simp)
  · simp
  · simp⟩

/-- The factor matrix with `(0, 4)` entry `φ.1 0 4` and no other nonzero
upper-triangular entries. -/
private def f15 (φ : G5) : G5 := ⟨!![1, 0, 0, 0, φ.1 0 4;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1], by
  refine ⟨fun i => by fin_cases i <;> simp, fun i j => ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first | exact Or.inr (by decide) | exact Or.inl (by simp)
  · simp
  · simp⟩

/-- Every superdiagonal-zero matrix is the product of its six factor matrices,
with the `(2, 4)` factor first so that no cross term appears in the `(0, 4)`
entry. -/
private theorem phi_decomp (φ : G5) (hφ : φ ∈ phiSub) :
    φ = f35 φ * f13 φ * f14 φ * f24 φ * f25 φ * f15 φ := by
  have hda : ∀ i, φ.1 i i = 1 := φ.2.1
  have hla : ∀ i j, j < i → φ.1 i j = 0 := fun i j h => UT5Pred.lower φ.2 h
  have h01 : φ.1 0 1 = 0 := hφ.1
  have h23 : φ.1 2 3 = 0 := hφ.2
  have h12 : φ.1 1 2 = 0 := by rw [← φ.2.2.2.1]; exact h01
  have h34 : φ.1 3 4 = 0 := by rw [← φ.2.2.2.2]; exact h23
  have hmul : ∀ a b : G5, (a * b).1 = a.1 * b.1 := fun a b => rfl
  have hf35 : (f35 φ).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, φ.1 2 4;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  have hf13 : (f13 φ).1 = !![1, 0, φ.1 0 2, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  have hf14 : (f14 φ).1 = !![1, 0, 0, φ.1 0 3, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  have hf24 : (f24 φ).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, φ.1 1 3, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  have hf25 : (f25 φ).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, 0, φ.1 1 4;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  have hf15 : (f15 φ).1 = !![1, 0, 0, 0, φ.1 0 4;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hmul, hf35, hf13, hf14, hf24, hf25, hf15, hda, hla, h01, h23, h12, h34,
      Matrix.mul_apply, Fin.sum_univ_five]


private theorem hx_mem : x ∈ Subgroup.closure ({x, y} : Set G5) :=
  Subgroup.subset_closure (Set.mem_insert x {y})

private theorem hy_mem : y ∈ Subgroup.closure ({x, y} : Set G5) :=
  Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr rfl))

private theorem e13_mem : e13 ∈ Subgroup.closure ({x, y} : Set G5) := by
  rw [word_e13]; exact mul_mem hx_mem hx_mem

private theorem e35_mem : e35 ∈ Subgroup.closure ({x, y} : Set G5) := by
  rw [word_e35]; exact mul_mem hy_mem hy_mem

private theorem e14_mem : e14 ∈ Subgroup.closure ({x, y} : Set G5) := by
  rw [word_e14]
  exact mul_mem (mul_mem hy_mem hy_mem)
    (mul_mem (mul_mem (mul_mem hy_mem hx_mem) hx_mem)
      (mul_mem (mul_mem hy_mem hx_mem) hx_mem))

private theorem e15_mem : e15 ∈ Subgroup.closure ({x, y} : Set G5) := by
  rw [word_e15]
  exact mul_mem
    (mul_mem (mul_mem hy_mem hx_mem) (mul_mem hy_mem hx_mem))
    (mul_mem (mul_mem hy_mem hx_mem) (mul_mem hy_mem hx_mem))

private theorem e24_mem : e24 ∈ Subgroup.closure ({x, y} : Set G5) := by
  rw [word_e24]
  exact mul_mem
    (mul_mem
      (mul_mem (mul_mem hy_mem hx_mem) (mul_mem hy_mem hx_mem))
      (mul_mem hx_mem hx_mem))
    (mul_mem hy_mem hy_mem)

private theorem e25_mem : e25 ∈ Subgroup.closure ({x, y} : Set G5) := by
  rw [word_e25]
  exact mul_mem
    (mul_mem (mul_mem (mul_mem hy_mem hx_mem) hx_mem)
      (mul_mem (mul_mem hy_mem hx_mem) hx_mem))
    (mul_mem (mul_mem (mul_mem hx_mem hy_mem) hx_mem)
      (mul_mem (mul_mem hx_mem hy_mem) hx_mem))

private theorem f35_mem (φ : G5) : f35 φ ∈ Subgroup.closure ({x, y} : Set G5) := by
  rcases zmod2_cases (φ.1 2 4) with h | h
  · have heq : f35 φ = 1 := by
      have hf : (f35 φ).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, φ.1 2 4;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      have h1 : (1 : G5).1 = (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) := rfl
      apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, h1, h]
    rw [heq]; exact Subgroup.one_mem _
  · have heq : f35 φ = e35 := by
      have hf : (f35 φ).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, φ.1 2 4;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      have he : (e35 : G5).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, he, h]
    rw [heq]; exact e35_mem

private theorem f13_mem (φ : G5) : f13 φ ∈ Subgroup.closure ({x, y} : Set G5) := by
  rcases zmod2_cases (φ.1 0 2) with h | h
  · have heq : f13 φ = 1 := by
      have hf : (f13 φ).1 = !![1, 0, φ.1 0 2, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      have h1 : (1 : G5).1 = (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) := rfl
      apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, h1, h]
    rw [heq]; exact Subgroup.one_mem _
  · have heq : f13 φ = e13 := by
      have hf : (f13 φ).1 = !![1, 0, φ.1 0 2, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      have he : (e13 : G5).1 = !![1, 0, 1, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, he, h]
    rw [heq]; exact e13_mem

private theorem f14_mem (φ : G5) : f14 φ ∈ Subgroup.closure ({x, y} : Set G5) := by
  rcases zmod2_cases (φ.1 0 3) with h | h
  · have heq : f14 φ = 1 := by
      have hf : (f14 φ).1 = !![1, 0, 0, φ.1 0 3, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      have h1 : (1 : G5).1 = (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) := rfl
      apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, h1, h]
    rw [heq]; exact Subgroup.one_mem _
  · have heq : f14 φ = e14 := by
      have hf : (f14 φ).1 = !![1, 0, 0, φ.1 0 3, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      have he : (e14 : G5).1 = !![1, 0, 0, 1, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, he, h]
    rw [heq]; exact e14_mem

private theorem f24_mem (φ : G5) : f24 φ ∈ Subgroup.closure ({x, y} : Set G5) := by
  rcases zmod2_cases (φ.1 1 3) with h | h
  · have heq : f24 φ = 1 := by
      have hf : (f24 φ).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, φ.1 1 3, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      have h1 : (1 : G5).1 = (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) := rfl
      apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, h1, h]
    rw [heq]; exact Subgroup.one_mem _
  · have heq : f24 φ = e24 := by
      have hf : (f24 φ).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, φ.1 1 3, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      have he : (e24 : G5).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, he, h]
    rw [heq]; exact e24_mem

private theorem f25_mem (φ : G5) : f25 φ ∈ Subgroup.closure ({x, y} : Set G5) := by
  rcases zmod2_cases (φ.1 1 4) with h | h
  · have heq : f25 φ = 1 := by
      have hf : (f25 φ).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, 0, φ.1 1 4;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      have h1 : (1 : G5).1 = (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) := rfl
      apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, h1, h]
    rw [heq]; exact Subgroup.one_mem _
  · have heq : f25 φ = e25 := by
      have hf : (f25 φ).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, 0, φ.1 1 4;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      have he : (e25 : G5).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, 0, 1;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, he, h]
    rw [heq]; exact e25_mem

private theorem f15_mem (φ : G5) : f15 φ ∈ Subgroup.closure ({x, y} : Set G5) := by
  rcases zmod2_cases (φ.1 0 4) with h | h
  · have heq : f15 φ = 1 := by
      have hf : (f15 φ).1 = !![1, 0, 0, 0, φ.1 0 4;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      have h1 : (1 : G5).1 = (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) := rfl
      apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, h1, h]
    rw [heq]; exact Subgroup.one_mem _
  · have heq : f15 φ = e15 := by
      have hf : (f15 φ).1 = !![1, 0, 0, 0, φ.1 0 4;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      have he : (e15 : G5).1 = !![1, 0, 0, 0, 1;
      0, 1,  0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
      apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, he, h]
    rw [heq]; exact e15_mem

private theorem phiSub_le_closure : phiSub ≤ Subgroup.closure ({x, y} : Set G5) := by
  intro φ hφ
  rw [phi_decomp φ hφ]
  exact mul_mem
    (mul_mem
      (mul_mem
        (mul_mem (mul_mem (f35_mem φ) (f13_mem φ)) (f14_mem φ))
        (f24_mem φ))
      (f25_mem φ))
    (f15_mem φ)

private theorem mem_closure_of_superdiag {g : G5} (w : G5)
    (hw : w ∈ Subgroup.closure ({x, y} : Set G5))
    (hw01 : w.1 0 1 = g.1 0 1) (hw23 : w.1 2 3 = g.1 2 3) :
    g ∈ Subgroup.closure ({x, y} : Set G5) := by
  have hwg : w⁻¹ * g ∈ phiSub := by
    rw [mem_phiSub]
    refine ⟨?_, ?_⟩
    · show ((w⁻¹).1 * g.1) 0 1 = 0
      rw [mul_sup01, inv_sup01, hw01]
      exact CharTwo.add_self_eq_zero _
    · show ((w⁻¹).1 * g.1) 2 3 = 0
      rw [mul_sup23, inv_sup23, hw23]
      exact CharTwo.add_self_eq_zero _
  have hg : g = w * (w⁻¹ * g) := by group
  rw [hg]
  exact mul_mem hw (phiSub_le_closure hwg)

private theorem closure_eq_top : Subgroup.closure ({x, y} : Set G5) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hx01 : x.1 0 1 = 1 := rfl
  have hx23 : x.1 2 3 = 0 := rfl
  have hy01 : y.1 0 1 = 0 := rfl
  have hy23 : y.1 2 3 = 1 := rfl
  have hxy01 : (x * y).1 0 1 = 1 := by
    show (x.1 * y.1) 0 1 = 1
    rw [mul_sup01, hx01, hy01]; simp
  have hxy23 : (x * y).1 2 3 = 1 := by
    show (x.1 * y.1) 2 3 = 1
    rw [mul_sup23, hx23, hy23]; simp
  rcases zmod2_cases (g.1 0 1) with ha | ha <;> rcases zmod2_cases (g.1 2 3) with hb | hb
  · exact mem_closure_of_superdiag (g := g) 1 (Subgroup.one_mem _)
      (by show (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 1 = g.1 0 1; simp [ha])
      (by show (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) 2 3 = g.1 2 3; simp [hb])
  · exact mem_closure_of_superdiag (g := g) y hy_mem
      (by rw [hy01]; exact ha.symm) (by rw [hy23]; exact hb.symm)
  · exact mem_closure_of_superdiag (g := g) x hx_mem
      (by rw [hx01]; exact ha.symm) (by rw [hx23]; exact hb.symm)
  · exact mem_closure_of_superdiag (g := g) (x * y) (mul_mem hx_mem hy_mem)
      (by rw [hxy01]; exact ha.symm) (by rw [hxy23]; exact hb.symm)


private def hom1 : G5 →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (g.1 0 1)
  map_one' := by
    show Multiplicative.ofAdd ((1 : G5).1 0 1) = 1
    show Multiplicative.ofAdd ((1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 1) = 1
    simp
  map_mul' a b := by
    show Multiplicative.ofAdd ((a * b).1 0 1) =
      Multiplicative.ofAdd (a.1 0 1) * Multiplicative.ofAdd (b.1 0 1)
    show Multiplicative.ofAdd ((a.1 * b.1) 0 1) =
      Multiplicative.ofAdd (a.1 0 1 + b.1 0 1)
    rw [mul_sup01]

private def hom2 : G5 →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (g.1 2 3)
  map_one' := by
    show Multiplicative.ofAdd ((1 : G5).1 2 3) = 1
    show Multiplicative.ofAdd ((1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) 2 3) = 1
    simp
  map_mul' a b := by
    show Multiplicative.ofAdd ((a * b).1 2 3) =
      Multiplicative.ofAdd (a.1 2 3) * Multiplicative.ofAdd (b.1 2 3)
    show Multiplicative.ofAdd ((a.1 * b.1) 2 3) =
      Multiplicative.ofAdd (a.1 2 3 + b.1 2 3)
    rw [mul_sup23]

private theorem mem_ker_hom1 (g : G5) : g ∈ hom1.ker ↔ g.1 0 1 = 0 := by
  constructor
  · intro h
    have h2 := congrArg Multiplicative.toAdd h
    simpa [hom1] using h2
  · intro h
    show hom1 g = 1
    simp [hom1, h]

private theorem mem_ker_hom2 (g : G5) : g ∈ hom2.ker ↔ g.1 2 3 = 0 := by
  constructor
  · intro h
    have h2 := congrArg Multiplicative.toAdd h
    simpa [hom2] using h2
  · intro h
    show hom2 g = 1
    simp [hom2, h]


private theorem isPGroup : IsPGroup 2 G5 := by
  rw [IsPGroup.iff_card]
  exact ⟨8, by rw [card_eq]; norm_num⟩

private theorem surjective_hom1 : Function.Surjective hom1 := by
  intro t
  rcases zmod2_cases (Multiplicative.toAdd t) with h | h
  · refine ⟨1, ?_⟩
    have ht : t = 1 := by
      have h2 := (ofAdd_toAdd t).symm
      rw [h] at h2
      exact h2.trans rfl
    rw [ht]; exact map_one hom1
  · refine ⟨x, ?_⟩
    have ht : t = Multiplicative.ofAdd 1 := by
      have h2 := (ofAdd_toAdd t).symm
      rw [h] at h2; exact h2
    rw [ht]; rfl

private theorem surjective_hom2 : Function.Surjective hom2 := by
  intro t
  rcases zmod2_cases (Multiplicative.toAdd t) with h | h
  · refine ⟨1, ?_⟩
    have ht : t = 1 := by
      have h2 := (ofAdd_toAdd t).symm
      rw [h] at h2
      exact h2.trans rfl
    rw [ht]; exact map_one hom2
  · refine ⟨y, ?_⟩
    have ht : t = Multiplicative.ofAdd 1 := by
      have h2 := (ofAdd_toAdd t).symm
      rw [h] at h2; exact h2
    rw [ht]; rfl

private theorem index_ker_hom1 : hom1.ker.index = 2 := by
  have heq : G5 ⧸ hom1.ker ≃* Multiplicative (ZMod 2) :=
    QuotientGroup.quotientKerEquivOfSurjective hom1 surjective_hom1
  rw [Subgroup.index_eq_card, Nat.card_congr heq.toEquiv]
  simp

private theorem index_ker_hom2 : hom2.ker.index = 2 := by
  have heq : G5 ⧸ hom2.ker ≃* Multiplicative (ZMod 2) :=
    QuotientGroup.quotientKerEquivOfSurjective hom2 surjective_hom2
  rw [Subgroup.index_eq_card, Nat.card_congr heq.toEquiv]
  simp

private theorem isCoatom_ker_hom1 : IsCoatom hom1.ker :=
  Subgroup.isCoatom_of_index_prime (by rw [index_ker_hom1]; exact Nat.prime_two)

private theorem isCoatom_ker_hom2 : IsCoatom hom2.ker :=
  Subgroup.isCoatom_of_index_prime (by rw [index_ker_hom2]; exact Nat.prime_two)

private theorem ker_inf_eq_phiSub : hom1.ker ⊓ hom2.ker = phiSub := by
  ext g
  simp only [Subgroup.mem_inf, mem_ker_hom1, mem_ker_hom2, mem_phiSub]

private theorem sq_mem_of_coatom {M : Subgroup G5} (hM : IsCoatom M) (g : G5) :
    g ^ 2 ∈ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent G5 := isPGroup.isNilpotent
  have hidx : M.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime isPGroup).mp hM
  have hnorm : M.Normal := Subgroup.normal_of_index_eq_two hidx
  have hcard : Nat.card (G5 ⧸ M) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hsq : (QuotientGroup.mk' M g) ^ 2 = 1 := by
    have h := (pow_card_eq_one' : (QuotientGroup.mk' M g) ^ Nat.card (G5 ⧸ M) = 1)
    rwa [hcard] at h
  have hmem : QuotientGroup.mk' M (g ^ 2) = 1 := by rw [map_pow, hsq]
  have hker : g ^ 2 ∈ (QuotientGroup.mk' M).ker := MonoidHom.mem_ker.mpr hmem
  rwa [QuotientGroup.ker_mk'] at hker

private theorem comm_mem_of_coatom {M : Subgroup G5} (hM : IsCoatom M) (g h : G5) :
    g * h * g⁻¹ * h⁻¹ ∈ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent G5 := isPGroup.isNilpotent
  have hidx : M.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime isPGroup).mp hM
  have hnorm : M.Normal := Subgroup.normal_of_index_eq_two hidx
  have hcard : Nat.card (G5 ⧸ M) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hsq : ∀ a : G5 ⧸ M, a ^ 2 = 1 := fun a => by
    have h := (pow_card_eq_one' : a ^ Nat.card (G5 ⧸ M) = 1)
    rwa [hcard] at h
  have hinv : ∀ a : G5 ⧸ M, a⁻¹ = a := fun a => by
    have h2 : a * a = 1 := by rw [← pow_two]; exact hsq a
    exact (eq_inv_of_mul_eq_one_left h2).symm
  have hmem : QuotientGroup.mk' M (g * h * g⁻¹ * h⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hinv, hinv, mul_assoc, ← pow_two]
    exact hsq _
  have hker : g * h * g⁻¹ * h⁻¹ ∈ (QuotientGroup.mk' M).ker := MonoidHom.mem_ker.mpr hmem
  rwa [QuotientGroup.ker_mk'] at hker

private theorem sq_mem_phiSub (g : G5) : g ^ 2 ∈ phiSub := by
  rw [mem_phiSub, pow_two]
  refine ⟨?_, ?_⟩
  · show (g.1 * g.1) 0 1 = 0
    rw [mul_sup01]
    exact CharTwo.add_self_eq_zero _
  · show (g.1 * g.1) 2 3 = 0
    rw [mul_sup23]
    exact CharTwo.add_self_eq_zero _

private theorem comm_mem_phiSub (g h : G5) : g * h * g⁻¹ * h⁻¹ ∈ phiSub := by
  rw [mem_phiSub]
  have hda : ∀ i, g.1 i i = 1 := g.2.1
  have hdb : ∀ i, h.1 i i = 1 := h.2.1
  have hla : ∀ i j, j < i → g.1 i j = 0 := fun i j hh => UT5Pred.lower g.2 hh
  have hlb : ∀ i j, j < i → h.1 i j = 0 := fun i j hh => UT5Pred.lower h.2 hh
  have hmul : ∀ a b : G5, (a * b).1 = a.1 * b.1 := fun a b => rfl
  have hinv : ∀ a : G5, (a⁻¹).1 = invMat a.1 := fun a => rfl
  refine ⟨?_, ?_⟩ <;>
    simp [hmul, hinv, invMat, Matrix.mul_apply, Fin.sum_univ_five, hda, hdb, hla, hlb] <;>
    ring_nf <;> simp [mul_two_zmod2, two_mul_zmod2]

/-- Each factor matrix is `1` or the corresponding coordinate matrix. -/
private theorem f35_eq (φ : G5) : f35 φ = 1 ∨ f35 φ = e35 := by
  have hf : (f35 φ).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, φ.1 2 4;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  have h1 : (1 : G5).1 = (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) := rfl
  have he : (e35 : G5).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  rcases zmod2_cases (φ.1 2 4) with h | h
  · left
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, h1, h]
  · right
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, he, h]

private theorem f13_eq (φ : G5) : f13 φ = 1 ∨ f13 φ = e13 := by
  have hf : (f13 φ).1 = !![1, 0, φ.1 0 2, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  have h1 : (1 : G5).1 = (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) := rfl
  have he : (e13 : G5).1 = !![1, 0, 1, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  rcases zmod2_cases (φ.1 0 2) with h | h
  · left
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, h1, h]
  · right
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, he, h]

private theorem f14_eq (φ : G5) : f14 φ = 1 ∨ f14 φ = e14 := by
  have hf : (f14 φ).1 = !![1, 0, 0, φ.1 0 3, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  have h1 : (1 : G5).1 = (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) := rfl
  have he : (e14 : G5).1 = !![1, 0, 0, 1, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  rcases zmod2_cases (φ.1 0 3) with h | h
  · left
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, h1, h]
  · right
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, he, h]

private theorem f24_eq (φ : G5) : f24 φ = 1 ∨ f24 φ = e24 := by
  have hf : (f24 φ).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, φ.1 1 3, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  have h1 : (1 : G5).1 = (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) := rfl
  have he : (e24 : G5).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  rcases zmod2_cases (φ.1 1 3) with h | h
  · left
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, h1, h]
  · right
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, he, h]

private theorem f25_eq (φ : G5) : f25 φ = 1 ∨ f25 φ = e25 := by
  have hf : (f25 φ).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, 0, φ.1 1 4;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  have h1 : (1 : G5).1 = (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) := rfl
  have he : (e25 : G5).1 = !![1, 0, 0, 0, 0;
      0, 1, 0, 0, 1;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  rcases zmod2_cases (φ.1 1 4) with h | h
  · left
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, h1, h]
  · right
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, he, h]

private theorem f15_eq (φ : G5) : f15 φ = 1 ∨ f15 φ = e15 := by
  have hf : (f15 φ).1 = !![1, 0, 0, 0, φ.1 0 4;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  have h1 : (1 : G5).1 = (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) := rfl
  have he : (e15 : G5).1 = !![1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := rfl
  rcases zmod2_cases (φ.1 0 4) with h | h
  · left
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, h1, h]
  · right
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [hf, he, h]

private theorem mul_self_mem_of_coatom {M : Subgroup G5} (hM : IsCoatom M) (g : G5) :
    g * g ∈ M := by
  simpa [pow_two] using sq_mem_of_coatom hM g

private theorem e13_mem_of_coatom {M : Subgroup G5} (hM : IsCoatom M) :
    e13 ∈ M := by
  rw [word_e13]; exact mul_self_mem_of_coatom hM x

private theorem e35_mem_of_coatom {M : Subgroup G5} (hM : IsCoatom M) :
    e35 ∈ M := by
  rw [word_e35]; exact mul_self_mem_of_coatom hM y

private theorem e14_mem_of_coatom {M : Subgroup G5} (hM : IsCoatom M) :
    e14 ∈ M := by
  rw [word_e14]
  exact mul_mem (mul_self_mem_of_coatom hM y) (mul_self_mem_of_coatom hM (y * x * x))

private theorem e15_mem_of_coatom {M : Subgroup G5} (hM : IsCoatom M) :
    e15 ∈ M := by
  rw [word_e15]
  exact mul_mem (mul_self_mem_of_coatom hM (y * x)) (mul_self_mem_of_coatom hM (y * x))

private theorem e24_mem_of_coatom {M : Subgroup G5} (hM : IsCoatom M) :
    e24 ∈ M := by
  rw [word_e24]
  exact mul_mem (mul_mem (mul_self_mem_of_coatom hM (y * x)) (mul_self_mem_of_coatom hM x))
    (mul_self_mem_of_coatom hM y)

private theorem e25_mem_of_coatom {M : Subgroup G5} (hM : IsCoatom M) :
    e25 ∈ M := by
  rw [word_e25]
  exact mul_mem (mul_self_mem_of_coatom hM (y * x * x)) (mul_self_mem_of_coatom hM (x * y * x))

private theorem phiSub_le_coatom {M : Subgroup G5} (hM : IsCoatom M) : phiSub ≤ M := by
  intro φ hφ
  rw [phi_decomp φ hφ]
  apply mul_mem
  · apply mul_mem
    · apply mul_mem
      · apply mul_mem
        · apply mul_mem
          · rcases f35_eq φ with h | h
            · rw [h]; exact Subgroup.one_mem _
            · rw [h]; exact e35_mem_of_coatom hM
          · rcases f13_eq φ with h | h
            · rw [h]; exact Subgroup.one_mem _
            · rw [h]; exact e13_mem_of_coatom hM
        · rcases f14_eq φ with h | h
          · rw [h]; exact Subgroup.one_mem _
          · rw [h]; exact e14_mem_of_coatom hM
      · rcases f24_eq φ with h | h
        · rw [h]; exact Subgroup.one_mem _
        · rw [h]; exact e24_mem_of_coatom hM
    · rcases f25_eq φ with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact e25_mem_of_coatom hM
  · rcases f15_eq φ with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact e15_mem_of_coatom hM

/-- The Frattini subgroup of `G5` is the superdiagonal-zero subgroup. -/
private theorem frattini_eq : frattini G5 = phiSub := by
  apply le_antisymm
  · -- `frattini ≤ phiSub`: the Frattini subgroup lies in both coordinate kernels.
    rw [← ker_inf_eq_phiSub]
    exact le_inf (frattini_le_coatom isCoatom_ker_hom1)
      (frattini_le_coatom isCoatom_ker_hom2)
  · -- `phiSub ≤ frattini`: `phiSub` lies in every maximal subgroup.
    rw [frattini, Order.radical]
    refine le_iInf fun M => le_iInf fun hM => ?_
    exact phiSub_le_coatom hM


end Lemmas


end UT5

/-- **Centre of the Frattini subgroup.** An element $x$ of a group $G$ lies in the centre
$Z(\Phi(G))$ of the Frattini subgroup $\Phi(G)$ when $x \in \Phi(G)$ and $xy = yx$ for every
$y \in \Phi(G)$. -/
@[expose] public def InFrattiniCenter {G : Type*} [Group G] (x : G) : Prop :=
  x ∈ frattini G ∧ ∀ y ∈ frattini G, x * y = y * x

/-- **Vanishing first cohomology of $G/\Phi(G)$ in $Z(\Phi(G))$.** Let $G$ be a group, let
$\Phi(G)$ be its Frattini subgroup and let $Z(\Phi(G))$ be the centre of $\Phi(G)$. The property
holds when every map $\delta \colon G \to Z(\Phi(G))$ with
$\delta(gh) = \delta(g)\, g\, \delta(h)\, g^{-1}$ for all $g, h \in G$ and $\delta(g) = 1$ for all
$g \in \Phi(G)$ is a coboundary: there is an $a \in Z(\Phi(G))$ with $\delta(g) = g a g^{-1} a^{-1}$
for all $g \in G$.

Such maps $\delta$ are exactly the inflations to $G$ of the 1-cocycles of $G/\Phi(G)$ with values
in $Z(\Phi(G))$ for the conjugation action, so the property says
$H^1(G/\Phi(G), Z(\Phi(G))) = 0$. -/
@[expose] public def FrattiniCenterH1Trivial (G : Type*) [Group G] : Prop :=
  ∀ δ : G → G, (∀ g, InFrattiniCenter (δ g)) → (∀ g h, δ (g * h) = δ g * (g * δ h * g⁻¹)) →
    (∀ g ∈ frattini G, δ g = 1) → ∃ a : G, InFrattiniCenter a ∧ ∀ g, δ g = g * a * g⁻¹ * a⁻¹

/-- **Kourovka Problem 17.2 (a non-abelian $p$-group with trivial $H^1$).** The statement, a
question of P. Schmid recorded by A. Abdollahi, that there exist a prime $p$ and a finite
non-abelian $p$-group $G$ such that, writing $\Phi(G)$ for the Frattini subgroup of $G$ and
$Z(\Phi(G))$ for its centre, the first cohomology group $H^1(G/\Phi(G), Z(\Phi(G)))$ for the
conjugation action of $G/\Phi(G)$ on $Z(\Phi(G))$ is trivial. -/
@[expose] public def nonabelianPGroupFrattiniCenterH1Trivial : Prop :=
  ∃ (p : ℕ) (G : Type) (_ : Group G) (_ : Finite G), p.Prime ∧ IsPGroup p G ∧
    (∃ a b : G, a * b ≠ b * a) ∧ FrattiniCenterH1Trivial G


namespace H1Proof

open UT5
open UT5.Lemmas

private theorem e35_mem_phiSub : e35 ∈ phiSub := by
  rw [mem_phiSub]; exact ⟨rfl, rfl⟩

private theorem e13_mem_phiSub : e13 ∈ phiSub := by
  rw [mem_phiSub]; exact ⟨rfl, rfl⟩

/-- An element of `G5` lies in the centre of the Frattini subgroup exactly when it
is superdiagonal-zero and its `(0, 2)` and `(2, 4)` entries vanish. -/
private theorem mem_center_iff (g : G5) :
    InFrattiniCenter g ↔ g ∈ phiSub ∧ g.1 0 2 = 0 ∧ g.1 2 4 = 0 := by
  constructor
  · intro h
    have hfr : g ∈ frattini G5 := h.1
    rw [frattini_eq] at hfr
    refine ⟨hfr, ?_, ?_⟩
    · have hcomm := h.2 e35 (by rw [frattini_eq]; exact e35_mem_phiSub)
      have h04 : (g.1 * e35.1) 0 4 = (e35.1 * g.1) 0 4 :=
        congrArg (fun m : G5 => m.1 0 4) hcomm
      have hc1 := (phi_mul_coords hfr e35_mem_phiSub).2.1
      have hc2 := (phi_mul_coords e35_mem_phiSub hfr).2.1
      rw [hc1, hc2] at h04
      simp only [show (e35 : G5).1 0 4 = 0 from rfl, show (e35 : G5).1 2 4 = 1 from rfl,
        show (e35 : G5).1 0 2 = 0 from rfl, add_zero, zero_add, mul_one, mul_zero, zero_mul] at h04
      -- `h04 : g.1 0 4 + g.1 0 2 = g.1 0 4`
      exact add_left_cancel (a := g.1 0 4) (b := g.1 0 2) (c := 0)
        (by rw [add_zero]; exact h04)
    · have hcomm := h.2 e13 (by rw [frattini_eq]; exact e13_mem_phiSub)
      have h04 : (g.1 * e13.1) 0 4 = (e13.1 * g.1) 0 4 :=
        congrArg (fun m : G5 => m.1 0 4) hcomm
      have hc1 := (phi_mul_coords hfr e13_mem_phiSub).2.1
      have hc2 := (phi_mul_coords e13_mem_phiSub hfr).2.1
      rw [hc1, hc2] at h04
      simp only [show (e13 : G5).1 0 4 = 0 from rfl, show (e13 : G5).1 2 4 = 0 from rfl,
        show (e13 : G5).1 0 2 = 1 from rfl, add_zero, zero_add, mul_zero, one_mul] at h04
      -- `h04 : g.1 0 4 = g.1 0 4 + g.1 2 4`
      exact add_left_cancel (a := g.1 0 4) (b := g.1 2 4) (c := 0)
        (by rw [add_zero]; exact h04.symm)
  · rintro ⟨hfr, h02, h24⟩
    refine ⟨?_, ?_⟩
    · rw [frattini_eq]; exact hfr
    · intro y hy
      rw [frattini_eq] at hy
      have hda : ∀ i, g.1 i i = 1 := g.2.1
      have hdb : ∀ i, y.1 i i = 1 := y.2.1
      have hla : ∀ i j, j < i → g.1 i j = 0 := fun i j hh => UT5Pred.lower g.2 hh
      have hlb : ∀ i j, j < i → y.1 i j = 0 := fun i j hh => UT5Pred.lower y.2 hh
      have hmul : ∀ a b : G5, (a * b).1 = a.1 * b.1 := fun a b => rfl
      have g01 : g.1 0 1 = 0 := hfr.1
      have g23 : g.1 2 3 = 0 := hfr.2
      have g12 : g.1 1 2 = 0 := by rw [← g.2.2.2.1]; exact g01
      have g34 : g.1 3 4 = 0 := by rw [← g.2.2.2.2]; exact g23
      have y01 : y.1 0 1 = 0 := hy.1
      have y23 : y.1 2 3 = 0 := hy.2
      have y12 : y.1 1 2 = 0 := by rw [← y.2.2.2.1]; exact y01
      have y34 : y.1 3 4 = 0 := by rw [← y.2.2.2.2]; exact y23
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hmul, Matrix.mul_apply, Fin.sum_univ_five, hda, hdb, hla, hlb,
          g01, g23, g12, g34, y01, y23, y12, y34, h02, h24] <;>
        ring_nf <;> simp [mul_two_zmod2, two_mul_zmod2]

private theorem center_mul_coords {a b : G5} (ha : InFrattiniCenter a)
    (hb : InFrattiniCenter b) :
    (a.1 * b.1) 0 3 = a.1 0 3 + b.1 0 3 ∧ (a.1 * b.1) 0 4 = a.1 0 4 + b.1 0 4 ∧
    (a.1 * b.1) 1 3 = a.1 1 3 + b.1 1 3 ∧ (a.1 * b.1) 1 4 = a.1 1 4 + b.1 1 4 := by
  obtain ⟨haφ, ha02, -⟩ := (mem_center_iff a).mp ha
  obtain ⟨hbφ, -, -⟩ := (mem_center_iff b).mp hb
  have h := phi_mul_coords haφ hbφ
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2⟩
  rw [h.2.1, ha02]
  simp

private theorem center_eq {a b : G5} (ha : InFrattiniCenter a) (hb : InFrattiniCenter b)
    (h03 : a.1 0 3 = b.1 0 3) (h04 : a.1 0 4 = b.1 0 4) (h13 : a.1 1 3 = b.1 1 3)
    (h14 : a.1 1 4 = b.1 1 4) : a = b := by
  obtain ⟨haφ, ha02, ha24⟩ := (mem_center_iff a).mp ha
  obtain ⟨hbφ, hb02, hb24⟩ := (mem_center_iff b).mp hb
  have hda : ∀ i, a.1 i i = 1 := a.2.1
  have hdb : ∀ i, b.1 i i = 1 := b.2.1
  have hla : ∀ i j, j < i → a.1 i j = 0 := fun i j hh => UT5Pred.lower a.2 hh
  have hlb : ∀ i j, j < i → b.1 i j = 0 := fun i j hh => UT5Pred.lower b.2 hh
  have a01 : a.1 0 1 = 0 := haφ.1
  have a23 : a.1 2 3 = 0 := haφ.2
  have a12 : a.1 1 2 = 0 := by rw [← a.2.2.2.1]; exact a01
  have a34 : a.1 3 4 = 0 := by rw [← a.2.2.2.2]; exact a23
  have b01 : b.1 0 1 = 0 := hbφ.1
  have b23 : b.1 2 3 = 0 := hbφ.2
  have b12 : b.1 1 2 = 0 := by rw [← b.2.2.2.1]; exact b01
  have b34 : b.1 3 4 = 0 := by rw [← b.2.2.2.2]; exact b23
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hda, hdb, hla, hlb, a01, a23, a12, a34, b01, b23, b12, b34, ha02, ha24,
      hb02, hb24, h03, h04, h13, h14]

private theorem center_mul {a b : G5} (ha : InFrattiniCenter a) (hb : InFrattiniCenter b) :
    InFrattiniCenter (a * b) := by
  obtain ⟨haφ, ha02, ha24⟩ := (mem_center_iff a).mp ha
  obtain ⟨hbφ, hb02, hb24⟩ := (mem_center_iff b).mp hb
  have hda : ∀ i, a.1 i i = 1 := a.2.1
  have hdb : ∀ i, b.1 i i = 1 := b.2.1
  have hla : ∀ i j, j < i → a.1 i j = 0 := fun i j hh => UT5Pred.lower a.2 hh
  have hlb : ∀ i j, j < i → b.1 i j = 0 := fun i j hh => UT5Pred.lower b.2 hh
  have a01 : a.1 0 1 = 0 := haφ.1
  have a23 : a.1 2 3 = 0 := haφ.2
  have b01 : b.1 0 1 = 0 := hbφ.1
  have b23 : b.1 2 3 = 0 := hbφ.2
  rw [mem_center_iff]
  refine ⟨mul_mem haφ hbφ, ?_, ?_⟩
  · show (a.1 * b.1) 0 2 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_five, hda, hdb, hla, hlb, a01, ha02, hb02]
  · show (a.1 * b.1) 2 4 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_five, hda, hdb, hla, hlb, a23, ha24, hb24]

private theorem center_sq {a : G5} (ha : InFrattiniCenter a) : a * a = 1 := by
  have h1 : InFrattiniCenter (1 : G5) := by
    refine ⟨Subgroup.one_mem _, fun y _ => by simp⟩
  apply center_eq (center_mul ha ha) h1
  · show (a.1 * a.1) 0 3 = 0
    rw [(center_mul_coords ha ha).1]
    exact CharTwo.add_self_eq_zero _
  · show (a.1 * a.1) 0 4 = 0
    rw [(center_mul_coords ha ha).2.1]
    exact CharTwo.add_self_eq_zero _
  · show (a.1 * a.1) 1 3 = 0
    rw [(center_mul_coords ha ha).2.2.1]
    exact CharTwo.add_self_eq_zero _
  · show (a.1 * a.1) 1 4 = 0
    rw [(center_mul_coords ha ha).2.2.2]
    exact CharTwo.add_self_eq_zero _

private theorem center_inv {a : G5} (ha : InFrattiniCenter a) : a⁻¹ = a :=
  (eq_inv_of_mul_eq_one_left (center_sq ha)).symm


private theorem center_conj {g a : G5} (ha : InFrattiniCenter a) :
    InFrattiniCenter (g * a * g⁻¹) := by
  rw [mem_center_iff]
  have hda : ∀ i, a.1 i i = 1 := a.2.1
  have hdg : ∀ i, g.1 i i = 1 := g.2.1
  have hla : ∀ i j, j < i → a.1 i j = 0 := fun i j hh => UT5Pred.lower a.2 hh
  have hlg : ∀ i j, j < i → g.1 i j = 0 := fun i j hh => UT5Pred.lower g.2 hh
  obtain ⟨haφ, ha02, ha24⟩ := (mem_center_iff a).mp ha
  have a01 : a.1 0 1 = 0 := haφ.1
  have a23 : a.1 2 3 = 0 := haφ.2
  have a12 : a.1 1 2 = 0 := by rw [← a.2.2.2.1]; exact a01
  have a34 : a.1 3 4 = 0 := by rw [← a.2.2.2.2]; exact a23
  have hmul : ∀ u v : G5, (u * v).1 = u.1 * v.1 := fun u v => rfl
  have hinv : ∀ u : G5, (u⁻¹).1 = invMat u.1 := fun u => rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- `(g * a * g⁻¹).1 0 1 = 0`
    show ((g.1 * a.1) * invMat g.1) 0 1 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_five, hda, hdg, hla, hlg, a01, a23, a12, a34,
      invMat] <;>
      ring_nf <;> simp [mul_two_zmod2, two_mul_zmod2]
  · -- `(g * a * g⁻¹).1 2 3 = 0`
    show ((g.1 * a.1) * invMat g.1) 2 3 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_five, hda, hdg, hla, hlg, a01, a23, a12, a34,
      invMat] <;>
      ring_nf <;> simp [mul_two_zmod2, two_mul_zmod2]
  · -- `(g * a * g⁻¹).1 0 2 = 0`
    show ((g.1 * a.1) * invMat g.1) 0 2 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_five, hda, hdg, hla, hlg, a01, a23, a12, a34,
      ha02, invMat] <;>
      ring_nf <;> simp [mul_two_zmod2, two_mul_zmod2]
  · -- `(g * a * g⁻¹).1 2 4 = 0`
    show ((g.1 * a.1) * invMat g.1) 2 4 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_five, hda, hdg, hla, hlg, a01, a23, a12, a34,
      ha24, invMat] <;>
      ring_nf <;> simp [mul_two_zmod2, two_mul_zmod2]

private theorem xinv_val : (x⁻¹ : G5).1 = !![1, 1, 1, 0, 0;
    0, 1, 1, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1] := by decide

private theorem yinv_val : (y⁻¹ : G5).1 = !![1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 1, 1, 1;
    0, 0, 0, 1, 1;
    0, 0, 0, 0, 1] := by decide

private theorem conj_x_coords {a : G5} (ha : InFrattiniCenter a) :
    (x * a * x⁻¹).1 0 3 = a.1 0 3 + a.1 1 3 ∧
    (x * a * x⁻¹).1 0 4 = a.1 0 4 + a.1 1 4 ∧
    (x * a * x⁻¹).1 1 3 = a.1 1 3 ∧
    (x * a * x⁻¹).1 1 4 = a.1 1 4 := by
  obtain ⟨haφ, ha02, ha24⟩ := (mem_center_iff a).mp ha
  have hda : ∀ i, a.1 i i = 1 := a.2.1
  have hla : ∀ i j, j < i → a.1 i j = 0 := fun i j hh => UT5Pred.lower a.2 hh
  have a01 : a.1 0 1 = 0 := haφ.1
  have a23 : a.1 2 3 = 0 := haφ.2
  have a12 : a.1 1 2 = 0 := by rw [← a.2.2.2.1]; exact a01
  have a34 : a.1 3 4 = 0 := by rw [← a.2.2.2.2]; exact a23
  have hxentry : ∀ i j, x.1 i j = xMat i j := fun i j => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((x.1 * a.1) * invMat x.1) 0 3 = a.1 0 3 + a.1 1 3
    simp [Matrix.mul_apply, Fin.sum_univ_five, hda, hla, a01, a23, a12, a34, ha02, ha24,
      hxentry, xMat, invMat] <;>
      ring_nf <;> simp [mul_two_zmod2, two_mul_zmod2]
  · show ((x.1 * a.1) * invMat x.1) 0 4 = a.1 0 4 + a.1 1 4
    simp [Matrix.mul_apply, Fin.sum_univ_five, hda, hla, a01, a23, a12, a34, ha02, ha24,
      hxentry, xMat, invMat] <;>
      ring_nf <;> simp [mul_two_zmod2, two_mul_zmod2]
  · show ((x.1 * a.1) * invMat x.1) 1 3 = a.1 1 3
    simp [Matrix.mul_apply, Fin.sum_univ_five, hda, hla, a01, a23, a12, a34, ha02, ha24,
      hxentry, xMat, invMat] <;>
      ring_nf <;> simp [mul_two_zmod2, two_mul_zmod2]
  · show ((x.1 * a.1) * invMat x.1) 1 4 = a.1 1 4
    simp [Matrix.mul_apply, Fin.sum_univ_five, hda, hla, a01, a23, a12, a34, ha02, ha24,
      hxentry, xMat, invMat] <;>
      ring_nf <;> simp [mul_two_zmod2, two_mul_zmod2]

private theorem conj_y_coords {a : G5} (ha : InFrattiniCenter a) :
    (y * a * y⁻¹).1 0 3 = a.1 0 3 ∧
    (y * a * y⁻¹).1 0 4 = a.1 0 3 + a.1 0 4 ∧
    (y * a * y⁻¹).1 1 3 = a.1 1 3 ∧
    (y * a * y⁻¹).1 1 4 = a.1 1 3 + a.1 1 4 := by
  obtain ⟨haφ, ha02, ha24⟩ := (mem_center_iff a).mp ha
  have hda : ∀ i, a.1 i i = 1 := a.2.1
  have hla : ∀ i j, j < i → a.1 i j = 0 := fun i j hh => UT5Pred.lower a.2 hh
  have a01 : a.1 0 1 = 0 := haφ.1
  have a23 : a.1 2 3 = 0 := haφ.2
  have a12 : a.1 1 2 = 0 := by rw [← a.2.2.2.1]; exact a01
  have a34 : a.1 3 4 = 0 := by rw [← a.2.2.2.2]; exact a23
  have hyentry : ∀ i j, y.1 i j = yMat i j := fun i j => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((y.1 * a.1) * invMat y.1) 0 3 = a.1 0 3
    simp [Matrix.mul_apply, Fin.sum_univ_five, hda, hla, a01, a23, a12, a34, ha02, ha24,
      hyentry, yMat, invMat] <;>
      ring_nf <;> simp [mul_two_zmod2, two_mul_zmod2]
  · show ((y.1 * a.1) * invMat y.1) 0 4 = a.1 0 3 + a.1 0 4
    simp [Matrix.mul_apply, Fin.sum_univ_five, hda, hla, a01, a23, a12, a34, ha02, ha24,
      hyentry, yMat, invMat] <;>
      ring_nf <;> simp [mul_two_zmod2, two_mul_zmod2]
  · show ((y.1 * a.1) * invMat y.1) 1 3 = a.1 1 3
    simp [Matrix.mul_apply, Fin.sum_univ_five, hda, hla, a01, a23, a12, a34, ha02, ha24,
      hyentry, yMat, invMat] <;>
      ring_nf <;> simp [mul_two_zmod2, two_mul_zmod2]
  · show ((y.1 * a.1) * invMat y.1) 1 4 = a.1 1 3 + a.1 1 4
    simp [Matrix.mul_apply, Fin.sum_univ_five, hda, hla, a01, a23, a12, a34, ha02, ha24,
      hyentry, yMat, invMat] <;>
      ring_nf <;> simp [mul_two_zmod2, two_mul_zmod2]


private theorem delta_one {δ : G5 → G5}
    (hcen : ∀ g, InFrattiniCenter (δ g))
    (hcoc : ∀ g h, δ (g * h) = δ g * (g * δ h * g⁻¹)) : δ 1 = 1 := by
  have h := hcoc 1 1
  simp only [mul_one, one_mul, inv_one] at h
  have h1 : δ 1 * 1 = δ 1 * δ 1 := by rw [mul_one]; exact h
  exact (mul_left_cancel h1).symm

private theorem delta_factor_right {δ : G5 → G5}
    (hcen : ∀ g, InFrattiniCenter (δ g))
    (hcoc : ∀ g h, δ (g * h) = δ g * (g * δ h * g⁻¹))
    (hφ : ∀ g ∈ frattini G5, δ g = 1) {g φ : G5} (hφmem : φ ∈ frattini G5) :
    δ (g * φ) = δ g := by
  rw [hcoc g φ, hφ φ hφmem]
  simp

private theorem delta_factor_left {δ : G5 → G5}
    (hcen : ∀ g, InFrattiniCenter (δ g))
    (hcoc : ∀ g h, δ (g * h) = δ g * (g * δ h * g⁻¹))
    (hφ : ∀ g ∈ frattini G5, δ g = 1) {g φ : G5} (hφmem : φ ∈ frattini G5) :
    δ (φ * g) = δ g := by
  have hcomm : δ g * φ = φ * δ g := (hcen g).2 φ hφmem
  rw [hcoc φ g, hφ φ hφmem, one_mul]
  calc φ * δ g * φ⁻¹ = (δ g * φ) * φ⁻¹ := by rw [← hcomm]
    _ = δ g := by rw [mul_assoc, mul_inv_cancel, mul_one]

private theorem inv_mul_mem_phiSub {g : G5} (w : G5)
    (hw01 : w.1 0 1 = g.1 0 1) (hw23 : w.1 2 3 = g.1 2 3) : w⁻¹ * g ∈ phiSub := by
  rw [mem_phiSub]
  refine ⟨?_, ?_⟩
  · show ((w⁻¹).1 * g.1) 0 1 = 0
    rw [mul_sup01, inv_sup01, hw01]
    exact CharTwo.add_self_eq_zero _
  · show ((w⁻¹).1 * g.1) 2 3 = 0
    rw [mul_sup23, inv_sup23, hw23]
    exact CharTwo.add_self_eq_zero _

private theorem decomp (g : G5) :
    ∃ w φ : G5, φ ∈ phiSub ∧ (w = 1 ∨ w = x ∨ w = y ∨ w = x * y) ∧ g = w * φ := by
  have hx01 : x.1 0 1 = 1 := rfl
  have hx23 : x.1 2 3 = 0 := rfl
  have hy01 : y.1 0 1 = 0 := rfl
  have hy23 : y.1 2 3 = 1 := rfl
  have hxy01 : (x * y).1 0 1 = 1 := by
    show (x.1 * y.1) 0 1 = 1
    rw [mul_sup01, hx01, hy01]; simp
  have hxy23 : (x * y).1 2 3 = 1 := by
    show (x.1 * y.1) 2 3 = 1
    rw [mul_sup23, hx23, hy23]; simp
  rcases zmod2_cases (g.1 0 1) with ha | ha <;> rcases zmod2_cases (g.1 2 3) with hb | hb
  · refine ⟨1, 1⁻¹ * g, ?_, Or.inl rfl, by group⟩
    apply inv_mul_mem_phiSub
    · show (1 : G5).1 0 1 = g.1 0 1
      show (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 1 = g.1 0 1
      simp [ha]
    · show (1 : G5).1 2 3 = g.1 2 3
      show (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) 2 3 = g.1 2 3
      simp [hb]
  · refine ⟨y, y⁻¹ * g, inv_mul_mem_phiSub y ?_ ?_, Or.inr (Or.inr (Or.inl rfl)), by group⟩
    · rw [hy01]; exact ha.symm
    · rw [hy23]; exact hb.symm
  · refine ⟨x, x⁻¹ * g, inv_mul_mem_phiSub x ?_ ?_, Or.inr (Or.inl rfl), by group⟩
    · rw [hx01]; exact ha.symm
    · rw [hx23]; exact hb.symm
  · refine ⟨x * y, (x * y)⁻¹ * g, inv_mul_mem_phiSub (x * y) ?_ ?_,
      Or.inr (Or.inr (Or.inr rfl)), by group⟩
    · rw [hxy01]; exact ha.symm
    · rw [hxy23]; exact hb.symm

private theorem norm_x {δ : G5 → G5}
    (hcen : ∀ g, InFrattiniCenter (δ g))
    (hcoc : ∀ g h, δ (g * h) = δ g * (g * δ h * g⁻¹))
    (hφ : ∀ g ∈ frattini G5, δ g = 1) :
    (δ x).1 1 3 = 0 ∧ (δ x).1 1 4 = 0 := by
  have hx2 : x * x ∈ frattini G5 := by
    rw [frattini_eq, mem_phiSub]
    exact ⟨by decide, by decide⟩
  have h1 : δ x * (x * δ x * x⁻¹) = 1 := by
    have h := hcoc x x
    rw [hφ _ hx2] at h
    exact h.symm
  have hU : InFrattiniCenter (δ x) := hcen x
  have hX : InFrattiniCenter (x * δ x * x⁻¹) := center_conj hU
  have e03 : ((δ x).1 * (x * δ x * x⁻¹).1) 0 3 = 0 :=
    congrArg (fun m : G5 => m.1 0 3) h1
  have e04 : ((δ x).1 * (x * δ x * x⁻¹).1) 0 4 = 0 :=
    congrArg (fun m : G5 => m.1 0 4) h1
  rw [(center_mul_coords hU hX).1, (conj_x_coords hU).1] at e03
  rw [(center_mul_coords hU hX).2.1, (conj_x_coords hU).2.1] at e04
  refine ⟨?_, ?_⟩
  · have h2 : (δ x).1 0 3 + ((δ x).1 0 3 + (δ x).1 1 3) = (δ x).1 1 3 := by
      ring_nf
      simp [mul_two_zmod2, two_mul_zmod2]
    rw [h2] at e03
    exact e03
  · have h2 : (δ x).1 0 4 + ((δ x).1 0 4 + (δ x).1 1 4) = (δ x).1 1 4 := by
      ring_nf
      simp [mul_two_zmod2, two_mul_zmod2]
    rw [h2] at e04
    exact e04

private theorem norm_y {δ : G5 → G5}
    (hcen : ∀ g, InFrattiniCenter (δ g))
    (hcoc : ∀ g h, δ (g * h) = δ g * (g * δ h * g⁻¹))
    (hφ : ∀ g ∈ frattini G5, δ g = 1) :
    (δ y).1 0 3 = 0 ∧ (δ y).1 1 3 = 0 := by
  have hy2 : y * y ∈ frattini G5 := by
    rw [frattini_eq, mem_phiSub]
    exact ⟨by decide, by decide⟩
  have h1 : δ y * (y * δ y * y⁻¹) = 1 := by
    have h := hcoc y y
    rw [hφ _ hy2] at h
    exact h.symm
  have hV : InFrattiniCenter (δ y) := hcen y
  have hY : InFrattiniCenter (y * δ y * y⁻¹) := center_conj hV
  have e04 : ((δ y).1 * (y * δ y * y⁻¹).1) 0 4 = 0 :=
    congrArg (fun m : G5 => m.1 0 4) h1
  have e14 : ((δ y).1 * (y * δ y * y⁻¹).1) 1 4 = 0 :=
    congrArg (fun m : G5 => m.1 1 4) h1
  rw [(center_mul_coords hV hY).2.1, (conj_y_coords hV).2.1] at e04
  rw [(center_mul_coords hV hY).2.2.2, (conj_y_coords hV).2.2.2] at e14
  refine ⟨?_, ?_⟩
  · have h2 : (δ y).1 0 4 + ((δ y).1 0 3 + (δ y).1 0 4) = (δ y).1 0 3 := by
      ring_nf
      simp [mul_two_zmod2, two_mul_zmod2]
    rw [h2] at e04
    exact e04
  · have h2 : (δ y).1 1 4 + ((δ y).1 1 3 + (δ y).1 1 4) = (δ y).1 1 3 := by
      ring_nf
      simp [mul_two_zmod2, two_mul_zmod2]
    rw [h2] at e14
    exact e14

private theorem comm_rel {δ : G5 → G5}
    (hcen : ∀ g, InFrattiniCenter (δ g))
    (hcoc : ∀ g h, δ (g * h) = δ g * (g * δ h * g⁻¹))
    (hφ : ∀ g ∈ frattini G5, δ g = 1) :
    (δ y).1 1 4 = (δ x).1 0 3 := by
  have hmem : (y * x)⁻¹ * (x * y) ∈ frattini G5 := by
    rw [frattini_eq, mem_phiSub]
    exact ⟨by decide, by decide⟩
  have heq : δ (x * y) = δ (y * x) := by
    have h1 : x * y = (y * x) * ((y * x)⁻¹ * (x * y)) := by group
    rw [h1]
    exact delta_factor_right hcen hcoc hφ hmem
  have hxy : δ (x * y) = δ x * (x * δ y * x⁻¹) := hcoc x y
  have hyx : δ (y * x) = δ y * (y * δ x * y⁻¹) := hcoc y x
  have hU : InFrattiniCenter (δ x) := hcen x
  have hV : InFrattiniCenter (δ y) := hcen y
  have hX : InFrattiniCenter (x * δ y * x⁻¹) := center_conj hV
  have hY : InFrattiniCenter (y * δ x * y⁻¹) := center_conj hU
  have e : ((δ x).1 * (x * δ y * x⁻¹).1) 0 4 = ((δ y).1 * (y * δ x * y⁻¹).1) 0 4 :=
    congrArg (fun m : G5 => m.1 0 4) (hxy.symm.trans (heq.trans hyx))
  rw [(center_mul_coords hU hX).2.1, (conj_x_coords hV).2.1,
    (center_mul_coords hV hY).2.1, (conj_y_coords hU).2.1] at e
  have h2 : (δ y).1 1 4 + ((δ x).1 0 4 + (δ y).1 0 4) =
      (δ x).1 0 3 + ((δ x).1 0 4 + (δ y).1 0 4) := by
    linear_combination e
  exact add_right_cancel_iff.mp h2

/-- The cobounding element, assembled from the coordinates of `δ x` and `δ y`. -/
private def cobound (U V : G5) : G5 := ⟨!![1, 0, 0, V.1 0 4, 0;
    0, 1, 0, V.1 1 4, U.1 0 4;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1], by
  refine ⟨fun i => by fin_cases i <;> simp, fun i j => ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first | exact Or.inr (by decide) | exact Or.inl (by simp)
  · simp
  · simp⟩

private theorem cobound_center (U V : G5) : InFrattiniCenter (cobound U V) := by
  rw [mem_center_iff]
  refine ⟨?_, rfl, rfl⟩
  rw [mem_phiSub]
  exact ⟨rfl, rfl⟩

private theorem cobound_x {δ : G5 → G5}
    (hcen : ∀ g, InFrattiniCenter (δ g))
    (hcoc : ∀ g h, δ (g * h) = δ g * (g * δ h * g⁻¹))
    (hφ : ∀ g ∈ frattini G5, δ g = 1)
    (hU13 : (δ x).1 1 3 = 0) (hU14 : (δ x).1 1 4 = 0)
    (hVU : (δ y).1 1 4 = (δ x).1 0 3) :
    x * cobound (δ x) (δ y) * x⁻¹ * (cobound (δ x) (δ y))⁻¹ = δ x := by
  have ha : InFrattiniCenter (cobound (δ x) (δ y)) := cobound_center _ _
  have hX : InFrattiniCenter (x * cobound (δ x) (δ y) * x⁻¹) := center_conj ha
  rw [center_inv ha]
  apply center_eq (center_mul hX ha) (hcen x)
  · show ((x * cobound (δ x) (δ y) * x⁻¹).1 * (cobound (δ x) (δ y)).1) 0 3 = (δ x).1 0 3
    rw [(center_mul_coords hX ha).1, (conj_x_coords ha).1]
    show ((δ y).1 0 4 + (δ y).1 1 4) + (δ y).1 0 4 = (δ x).1 0 3
    have h2 : ((δ y).1 0 4 + (δ y).1 1 4) + (δ y).1 0 4 = (δ y).1 1 4 := by
      ring_nf
      simp [mul_two_zmod2, two_mul_zmod2]
    rw [h2]
    exact hVU
  · show ((x * cobound (δ x) (δ y) * x⁻¹).1 * (cobound (δ x) (δ y)).1) 0 4 = (δ x).1 0 4
    rw [(center_mul_coords hX ha).2.1, (conj_x_coords ha).2.1]
    show ((0 + (δ x).1 0 4) + 0) = (δ x).1 0 4
    simp
  · show ((x * cobound (δ x) (δ y) * x⁻¹).1 * (cobound (δ x) (δ y)).1) 1 3 = (δ x).1 1 3
    rw [(center_mul_coords hX ha).2.2.1, (conj_x_coords ha).2.2.1]
    show (δ y).1 1 4 + (δ y).1 1 4 = (δ x).1 1 3
    rw [CharTwo.add_self_eq_zero]
    exact hU13.symm
  · show ((x * cobound (δ x) (δ y) * x⁻¹).1 * (cobound (δ x) (δ y)).1) 1 4 = (δ x).1 1 4
    rw [(center_mul_coords hX ha).2.2.2, (conj_x_coords ha).2.2.2]
    show (δ x).1 0 4 + (δ x).1 0 4 = (δ x).1 1 4
    rw [CharTwo.add_self_eq_zero]
    exact hU14.symm

private theorem cobound_y {δ : G5 → G5}
    (hcen : ∀ g, InFrattiniCenter (δ g))
    (hcoc : ∀ g h, δ (g * h) = δ g * (g * δ h * g⁻¹))
    (hφ : ∀ g ∈ frattini G5, δ g = 1)
    (hV03 : (δ y).1 0 3 = 0) (hV13 : (δ y).1 1 3 = 0)
    (hVU : (δ y).1 1 4 = (δ x).1 0 3) :
    y * cobound (δ x) (δ y) * y⁻¹ * (cobound (δ x) (δ y))⁻¹ = δ y := by
  have ha : InFrattiniCenter (cobound (δ x) (δ y)) := cobound_center _ _
  have hY : InFrattiniCenter (y * cobound (δ x) (δ y) * y⁻¹) := center_conj ha
  rw [center_inv ha]
  apply center_eq (center_mul hY ha) (hcen y)
  · show ((y * cobound (δ x) (δ y) * y⁻¹).1 * (cobound (δ x) (δ y)).1) 0 3 = (δ y).1 0 3
    rw [(center_mul_coords hY ha).1, (conj_y_coords ha).1]
    show (δ y).1 0 4 + (δ y).1 0 4 = (δ y).1 0 3
    rw [CharTwo.add_self_eq_zero]
    exact hV03.symm
  · show ((y * cobound (δ x) (δ y) * y⁻¹).1 * (cobound (δ x) (δ y)).1) 0 4 = (δ y).1 0 4
    rw [(center_mul_coords hY ha).2.1, (conj_y_coords ha).2.1]
    show (((δ y).1 0 4 + 0) + 0) = (δ y).1 0 4
    simp
  · show ((y * cobound (δ x) (δ y) * y⁻¹).1 * (cobound (δ x) (δ y)).1) 1 3 = (δ y).1 1 3
    rw [(center_mul_coords hY ha).2.2.1, (conj_y_coords ha).2.2.1]
    show (δ y).1 1 4 + (δ y).1 1 4 = (δ y).1 1 3
    rw [CharTwo.add_self_eq_zero]
    exact hV13.symm
  · show ((y * cobound (δ x) (δ y) * y⁻¹).1 * (cobound (δ x) (δ y)).1) 1 4 = (δ y).1 1 4
    rw [(center_mul_coords hY ha).2.2.2, (conj_y_coords ha).2.2.2]
    show (((δ y).1 1 4 + (δ x).1 0 4) + (δ x).1 0 4) = (δ y).1 1 4
    have h2 : (((δ y).1 1 4 + (δ x).1 0 4) + (δ x).1 0 4) = (δ y).1 1 4 := by
      ring_nf
      simp [mul_two_zmod2, two_mul_zmod2]
    exact h2

private theorem h1_trivial : FrattiniCenterH1Trivial G5 := by
  intro δ hcen hcoc hφ
  obtain ⟨hU13, hU14⟩ := norm_x hcen hcoc hφ
  obtain ⟨hV03, hV13⟩ := norm_y hcen hcoc hφ
  have hVU := comm_rel hcen hcoc hφ
  have ha : InFrattiniCenter (cobound (δ x) (δ y)) := cobound_center _ _
  refine ⟨cobound (δ x) (δ y), ha, fun g => ?_⟩
  obtain ⟨w, φ, hφmem, hw, hg⟩ := decomp g
  have hφfr : φ ∈ frattini G5 := by rw [frattini_eq]; exact hφmem
  have hδ : δ g = δ w := by
    rw [hg]
    exact delta_factor_right hcen hcoc hφ hφfr
  have hφa : φ * cobound (δ x) (δ y) * φ⁻¹ = cobound (δ x) (δ y) := by
    calc φ * cobound (δ x) (δ y) * φ⁻¹ = (cobound (δ x) (δ y) * φ) * φ⁻¹ := by
          rw [← ha.2 φ hφfr]
      _ = cobound (δ x) (δ y) := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have hRHS : g * cobound (δ x) (δ y) * g⁻¹ * (cobound (δ x) (δ y))⁻¹ =
      w * cobound (δ x) (δ y) * w⁻¹ * (cobound (δ x) (δ y))⁻¹ := by
    calc g * cobound (δ x) (δ y) * g⁻¹ * (cobound (δ x) (δ y))⁻¹
        = (w * φ) * cobound (δ x) (δ y) * (w * φ)⁻¹ * (cobound (δ x) (δ y))⁻¹ := by
          rw [hg]
      _ = w * (φ * cobound (δ x) (δ y) * φ⁻¹) * w⁻¹ * (cobound (δ x) (δ y))⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = w * cobound (δ x) (δ y) * w⁻¹ * (cobound (δ x) (δ y))⁻¹ := by rw [hφa]
  rw [hδ, hRHS]
  rcases hw with rfl | rfl | rfl | rfl
  · have hrhs : (1 : G5) * cobound (δ x) (δ y) * (1 : G5)⁻¹ * (cobound (δ x) (δ y))⁻¹
        = 1 := by simp
    rw [hrhs]
    exact delta_one hcen hcoc
  · exact (cobound_x hcen hcoc hφ hU13 hU14 hVU).symm
  · exact (cobound_y hcen hcoc hφ hV03 hV13 hVU).symm
  · have hxy : δ (x * y) = δ x * (x * δ y * x⁻¹) := hcoc x y
    rw [hxy]
    have hY : y * cobound (δ x) (δ y) * y⁻¹ = δ y * cobound (δ x) (δ y) := by
      calc y * cobound (δ x) (δ y) * y⁻¹
          = (y * cobound (δ x) (δ y) * y⁻¹ * (cobound (δ x) (δ y))⁻¹) *
            cobound (δ x) (δ y) := by
            conv_rhs => rw [mul_assoc, center_inv ha, center_sq ha, mul_one]
        _ = δ y * cobound (δ x) (δ y) := by
            rw [cobound_y hcen hcoc hφ hV03 hV13 hVU]
    symm
    calc (x * y) * cobound (δ x) (δ y) * (x * y)⁻¹ * (cobound (δ x) (δ y))⁻¹
        = x * (y * cobound (δ x) (δ y) * y⁻¹) * x⁻¹ * (cobound (δ x) (δ y))⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = x * (δ y * cobound (δ x) (δ y)) * x⁻¹ * (cobound (δ x) (δ y))⁻¹ := by rw [hY]
      _ = (x * δ y * x⁻¹) * (x * cobound (δ x) (δ y) * x⁻¹) *
          (cobound (δ x) (δ y))⁻¹ := by group
      _ = (x * δ y * x⁻¹) * ((x * cobound (δ x) (δ y) * x⁻¹) *
          (cobound (δ x) (δ y))⁻¹) := mul_assoc _ _ _
      _ = (x * δ y * x⁻¹) * δ x := by rw [cobound_x hcen hcoc hφ hU13 hU14 hVU]
      _ = δ x * (x * δ y * x⁻¹) := by
          have hcomm : δ x * (x * δ y * x⁻¹) = (x * δ y * x⁻¹) * δ x :=
            (hcen x).2 _ (center_conj (hcen y)).1
          exact hcomm.symm


end H1Proof


/--
**A non-abelian $p$-group with $H^1(G/\Phi(G), Z(\Phi(G))) = 0$ (Kourovka 17.2).** There exist a
prime $p$ and a finite non-abelian $p$-group $G$ such that, writing $\Phi(G)$ for the Frattini
subgroup of $G$ and $Z(\Phi(G))$ for its centre, the first cohomology group
$H^1(G/\Phi(G), Z(\Phi(G)))$ for the conjugation action of $G/\Phi(G)$ on $Z(\Phi(G))$ is trivial.

This answers Kourovka Problem 17.2 in the affirmative: the Kourovka Archive answers "Yes, it does",
citing Abdollahi (2011).

Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.2 (A. Abdollahi); resolution: A.
Abdollahi, J. Algebra 342 (2011), 154-160, Kourovka Archive, Problem 17.2 (Yes, it does).
-/
public theorem nonabelianPGroupFrattiniCenterH1Trivial_holds :
    nonabelianPGroupFrattiniCenterH1Trivial := by
  refine ⟨2, UT5.G5, inferInstance, inferInstance, Nat.prime_two, UT5.Lemmas.isPGroup,
    ⟨UT5.Lemmas.x, UT5.Lemmas.y, UT5.Lemmas.xy_ne⟩, H1Proof.h1_trivial⟩


end MathlibExt.GroupTheory.FrattiniCenterFirstCohomologyKourovka17Problem2Wanted
