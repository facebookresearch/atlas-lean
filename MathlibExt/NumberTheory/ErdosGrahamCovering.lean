/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import MathlibExt.NumberTheory.CoveringSystem
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Cast.Field

/-!
# Covering systems have reciprocal-moduli sum at least one

If the residue classes `a i (mod d i)`, for `i : Fin t`, with positive moduli cover the integers,
then `1 ≤ ∑ i, 1 / d i` (`one_le_sum_inv_moduli`). This is Lemma 2.2 of Sarosh Adenwalla's paper
on a question of Erdős and Graham about covering systems. The paper's covering sets have distinct
moduli greater than `1`, but neither condition is used, so the moduli here are only positive and
may repeat; the sum runs over the indices, so a repeated class counts once for each index.

## Proof outline

Let `N = ∏ i, d i`, so that every `d i` divides `N`. The map `x ↦ x / d i` sends the integers of
`[0, N)` in the class `a i (mod d i)` into `[0, N / d i)`, injectively because two such integers
have the same remainder modulo `d i`; so the class holds at most `N / d i` of them. The classes
cover `[0, N)`, hence `N ≤ ∑ i, N / d i`, and dividing by `N` gives the bound. The paper counts
residue classes modulo the least common multiple of the moduli instead of their product.

## Implementation notes

`one_le_sum_inv_moduli` keeps the full name and the statement it had as a wanted theorem in
`WantedExt.NumberTheory.ErdosGrahamCoveringWanted`, so its namespace reads
`ErdosGrahamCoveringWanted`.

## References

* Sarosh Adenwalla, *A Question of Erdős and Graham on Covering Systems*, arXiv:2501.15170v3,
  Lemma 2.2 and its proof (<https://arxiv.org/abs/2501.15170>).
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosGrahamCoveringWanted

/-- When `d ∣ N`, at most `N / d` naturals below `N` lie in a given residue class modulo `d`:
`x ↦ x / d` maps them injectively into `[0, N / d)`. -/
private theorem card_filter_range_modEq_le {d N : ℕ} (hd : 0 < d) (hdN : d ∣ N) (v : ℤ) :
    ((Finset.range N).filter fun x : ℕ => (x : ℤ) ≡ v [ZMOD (d : ℤ)]).card ≤ N / d := by
  calc _ ≤ (Finset.range (N / d)).card := by
        refine Finset.card_le_card_of_injOn (fun x => x / d) (fun x hx => ?_)
          fun x hx y hy hxy => ?_
        · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
          simp only [Finset.mem_coe, Finset.mem_range]
          rw [Nat.div_lt_iff_lt_mul hd, Nat.div_mul_cancel hdN]
          exact hx.1
        · rw [Finset.mem_coe, Finset.mem_filter] at hx hy
          have hmod : x % d = y % d := Int.natCast_modEq_iff.mp (hx.2.trans hy.2.symm)
          have hdiv : x / d = y / d := hxy
          rw [← Nat.div_add_mod x d, ← Nat.div_add_mod y d, hmod, hdiv]
    _ = N / d := Finset.card_range _

/-- **Lemma 2.2**: for any covering set
`{a_1 (mod d_1), …, a_t (mod d_t)}`,
`∑_{i=1}^t 1 / d_i ≥ 1`.

Source: Sarosh Adenwalla, "A Question of Erdős and
Graham on Covering Systems", Lemma 2.2. -/
theorem one_le_sum_inv_moduli {t : ℕ}
    (moduli : Fin t → ℕ) (residues : Fin t → ℤ)
    (hpos : ∀ i, 0 < moduli i)
    (hcov : Int.IsCoveringSystem
      (Int.indexedCoveringClasses moduli residues)) :
    (1 : ℚ) ≤ ∑ i, (1 : ℚ) / (moduli i : ℚ) := by
  rw [Int.indexedCoveringClasses_isCoveringSystem_iff] at hcov
  set N := ∏ i, moduli i
  have hN : 0 < N := Finset.prod_pos fun i _ => hpos i
  have hdvd (i : Fin t) : moduli i ∣ N := Finset.dvd_prod_of_mem moduli (Finset.mem_univ i)
  -- Every natural below `N` lies in one of the classes.
  have hsub : Finset.range N ⊆ Finset.univ.biUnion fun i =>
      (Finset.range N).filter fun x : ℕ => (x : ℤ) ≡ residues i [ZMOD (moduli i : ℤ)] := by
    intro x hx
    obtain ⟨i, hi⟩ := hcov x
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hx, hi⟩⟩
  have hcount : N ≤ ∑ i, N / moduli i :=
    calc N = (Finset.range N).card := (Finset.card_range N).symm
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum fun i _ => card_filter_range_modEq_le (hpos i) (hdvd i) _
  have key : (N : ℚ) * 1 ≤ N * ∑ i, (1 : ℚ) / (moduli i : ℚ) :=
    calc (N : ℚ) * 1 = N := mul_one _
      _ ≤ ((∑ i, N / moduli i : ℕ) : ℚ) := by exact_mod_cast hcount
      _ = ∑ i, (N : ℚ) / (moduli i : ℚ) := by
        rw [Nat.cast_sum]
        exact Finset.sum_congr rfl fun i _ =>
          Nat.cast_div (hdvd i) (Nat.cast_ne_zero.mpr (hpos i).ne')
      _ = N * ∑ i, (1 : ℚ) / (moduli i : ℚ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => (mul_one_div _ _).symm
  exact le_of_mul_le_mul_left key (Nat.cast_pos.mpr hN)

end MathlibExt.NumberTheory.ErdosGrahamCoveringWanted
