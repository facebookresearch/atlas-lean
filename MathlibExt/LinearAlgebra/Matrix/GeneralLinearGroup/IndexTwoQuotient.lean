/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# `GL₂` is not a quotient of a group with an abelian subgroup of index at most two

Let `R` be a commutative ring in which `4 ≠ 0`. A group `G` with an abelian subgroup of index at
most `2` admits no surjective homomorphism onto `GL₂(R)`
(`Matrix.GeneralLinearGroup.not_surjective_of_isMulCommutative_of_index_le_two`). For `R = ℤ/nℤ`
this holds whenever `n ∤ 4`, in particular for `n = p` an odd prime
(`Matrix.GeneralLinearGroup.not_surjective_zmod_of_isMulCommutative_of_index_le_two`).

This is the fact Gross uses in the proof of Lemma 4.3 for the Galois group of a ring class field
over `ℚ`, which contains the abelian group `Gal(K_n/K)` with index `2` (a group of "dihedral"
type).

## Proof

A subgroup of index at most `2` contains the square of every element. Lifting `u = (1 1; 0 1)` and
`l = (1 0; 1 1)` to `x, y ∈ G`, the squares `x²` and `y²` lie in the abelian subgroup and commute,
so `u² l² = l² u²`. The `(0, 0)` entries are `5` and `1`, so `4 = 0` in `R`.

## References

* B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic*
  (Durham, 1989), London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991,
  235–256: proof of Lemma 4.3, p. 242.
-/

@[expose] public section

open Matrix

namespace Matrix.GeneralLinearGroup

/-- A subgroup of index `1` or `2` contains the square of every element. -/
private theorem sq_mem_of_index_le_two {G : Type*} [Group G] (A : Subgroup G) [A.FiniteIndex]
    (hA : A.index ≤ 2) (g : G) : g ^ 2 ∈ A := by
  have h0 : A.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  rcases (by omega : A.index = 1 ∨ A.index = 2) with h | h
  · rw [Subgroup.index_eq_one] at h
    rw [h]
    exact Subgroup.mem_top _
  · exact Subgroup.sq_mem_of_index_two h g

/-- **`GL₂(R)` is not a quotient of a group with an abelian subgroup of index at most `2`.** Let `R`
be a commutative ring with `(4 : R) ≠ 0`, `G` a group and `A` a commutative subgroup of `G` of
finite index at most `2`. Then no group homomorphism `f : G →* GL₂(R)` is surjective. -/
theorem not_surjective_of_isMulCommutative_of_index_le_two {R : Type*} [CommRing R]
    (h4 : (4 : R) ≠ 0) {G : Type*} [Group G] (A : Subgroup G) [IsMulCommutative A]
    [A.FiniteIndex] (hA : A.index ≤ 2) (f : G →* GL (Fin 2) R) : ¬ Function.Surjective f := by
  intro hf
  let u : GL (Fin 2) R := ⟨!![1, 1; 0, 1], !![1, -1; 0, 1], by simp [one_fin_two],
    by simp [one_fin_two]⟩
  let l : GL (Fin 2) R := ⟨!![1, 0; 1, 1], !![1, 0; -1, 1], by simp [one_fin_two],
    by simp [one_fin_two]⟩
  obtain ⟨x, hx⟩ := hf u
  obtain ⟨y, hy⟩ := hf l
  have hc : x ^ 2 * y ^ 2 = y ^ 2 * x ^ 2 := by
    have := mul_comm' (⟨x ^ 2, sq_mem_of_index_le_two A hA x⟩ : A)
      ⟨y ^ 2, sq_mem_of_index_le_two A hA y⟩
    exact congrArg Subtype.val this
  have h00 := congrArg (fun g : G => ((f g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0) hc
  simp only [map_mul, map_pow, hx, hy, Units.val_mul, Units.val_pow_eq_pow_val, u, l] at h00
  simp only [sq, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, one_smul,
    tail_cons, empty_vecMul, add_zero, add_cons, empty_add_empty, symm_of, zero_smul, zero_add,
    empty_mul, coe_rowEquiv, row_of, Fin.isValue, Matrix.mul_apply, of_apply, cons_val',
    cons_val_fin_one, cons_val_zero, Fin.sum_univ_two, mul_one, cons_val_one, mul_zero,
    add_eq_left] at h00
  exact h4 (by linear_combination h00)

/-- **`GL₂(ℤ/nℤ)` is not a quotient of a group with an abelian subgroup of index at most `2`
when `n ∤ 4`.** Let `n` be a natural number not dividing `4` (for instance an odd prime), `G` a
group and `A` a commutative subgroup of `G` of finite index at most `2`. Then no group
homomorphism `G →* GL₂(ℤ/nℤ)` is surjective. -/
theorem not_surjective_zmod_of_isMulCommutative_of_index_le_two {n : ℕ} (hn : ¬ n ∣ 4)
    {G : Type*} [Group G] (A : Subgroup G) [IsMulCommutative A] [A.FiniteIndex]
    (hA : A.index ≤ 2) (f : G →* GL (Fin 2) (ZMod n)) : ¬ Function.Surjective f := by
  refine not_surjective_of_isMulCommutative_of_index_le_two ?_ A hA f
  intro h
  apply hn
  have : ((4 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
  exact (ZMod.natCast_eq_zero_iff 4 n).mp this

end Matrix.GeneralLinearGroup

end
