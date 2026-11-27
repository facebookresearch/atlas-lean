/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Torsion
public import MathlibExt.Combinatorics.SumsetSetsOfSizeK
import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Sumset sizes between `hk - h + 1` and `hk`

`sumsetSizes_inter_Icc_of_isAddTorsionFree` shows that, in a nontrivial torsion-free group and
for `h ≥ 1` and `k ≥ 4`, the sizes of `h`-fold sumsets of `k`-element sets that lie in
`[h * k - h + 1, h * k]` are exactly the two endpoints.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Corollary 1.
-/

open scoped Pointwise

namespace MetaMathlibExt

private theorem range_add_range (m k : ℕ) :
    Finset.range (m + 1) + Finset.range (k + 1) = Finset.range (m + k + 1) := by
  ext x
  simp only [Finset.mem_add, Finset.mem_range]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    omega
  · intro hx
    by_cases hm : x ≤ m
    · exact ⟨x, by omega, 0, by omega, by omega⟩
    · exact ⟨m, by omega, x - m, by omega, by omega⟩

private theorem nsmul_range (h k : ℕ) :
    h • Finset.range (k + 1) = Finset.range (h * k + 1) := by
  induction h with
  | zero =>
    simp only [zero_nsmul, Nat.zero_mul, Nat.zero_add]
    rfl
  | succ h ih => rw [succ_nsmul, ih, range_add_range, Nat.succ_mul]

private theorem lift_sumset_witness
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] [Nontrivial G] [DecidableEq G]
    (h k n : ℕ) (B : Finset ℤ) (hB : B.card = k) (hn : (h • B).card = n) :
    ∃ A : Finset G, A.card = k ∧ (h • A).card = n := by
  obtain ⟨g, hg⟩ := exists_ne (0 : G)
  let f := zmultiplesHom G g
  have hf : Function.Injective f := IsAddTorsionFree.zsmul_left_injective hg
  refine ⟨B.image f, ?_, ?_⟩
  · rwa [Finset.card_image_of_injective _ hf]
  · rwa [← Finset.image_nsmul, Finset.card_image_of_injective _ hf]

@[expose] public section

/-- **Sumset sizes between $hk - h + 1$ and $hk$.** Let $G$ be a nontrivial torsion-free
additive commutative group and let $h \ge 1$ and $k \ge 4$ be natural numbers. For a finite
set $A \subseteq G$ write $hA$ for its $h$-fold sumset, the set of sums of $h$ elements of $A$,
and write $R_G(h, k)$ for the set of sizes $|hA|$ of $k$-element sets $A \subseteq G$. Then
$R_G(h, k) \cap [hk - h + 1, hk] = \{hk - h + 1, hk\}$.

The hypotheses that $G$ is nontrivial (otherwise there is no $k$-element set and
$R_G(h, k)$ is empty) and that $h \ge 1$ (for $h = 0$ the interval $[1, 0]$ is empty while
the right side is $\{1, 0\}$) are added. The arXiv version states only $hk \in R_G(h, k)$
(Corollary 3.8); the rest combines Theorem 4 with the arithmetic-progression size
$hk - h + 1$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Corollary 1 (`integers-2026-A31-cor-1`). -/
public theorem sumsetSizes_inter_Icc_of_isAddTorsionFree
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] [Nontrivial G] [DecidableEq G]
    (h k : ℕ) (hk : 4 ≤ k) (hh : 1 ≤ h) :
    {n : ℕ | ∃ A : Finset G, A.card = k ∧ (h • A).card = n} ∩
        Set.Icc (h * k - h + 1) (h * k) = {h * k - h + 1, h * k} := by
  have hlo : ∃ A : Finset G, A.card = k ∧ (h • A).card = h * k - h + 1 := by
    let f := multiplesHom ℤ (1 : ℤ)
    have hf : Function.Injective f :=
      (nsmul_left_strictMono (by decide : 0 < (1 : ℤ))).injective
    apply lift_sumset_witness h k _ ((Finset.range k).image f)
    · rw [Finset.card_image_of_injective _ hf, Finset.card_range]
    · rw [← Finset.image_nsmul, Finset.card_image_of_injective _ hf]
      have hr : h • Finset.range k = Finset.range (h * (k - 1) + 1) := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega]
        exact nsmul_range h (k - 1)
      rw [hr, Finset.card_range, Nat.mul_sub, Nat.mul_one]
  have hhi : ∃ A : Finset G, A.card = k ∧ (h • A).card = h * k := by
    let B : Finset ℤ :=
      insert (k • (1 : ℤ)) ((Finset.range (k - 1)).image fun i => i • (1 : ℤ))
    apply lift_sumset_witness h k _ B
    · simpa only [one_nsmul, one_mul] using
        card_nsmul_arithProg_skip_penultimate (1 : ℤ) (by decide) k 1 (by omega) (by decide)
    · exact card_nsmul_arithProg_skip_penultimate (1 : ℤ) (by decide) k h (by omega) hh
  have hle : h * k - h + 1 ≤ h * k := by
    have hm : h ≤ h * k := by
      calc h = h * 1 := (Nat.mul_one h).symm
           _ ≤ h * k := Nat.mul_le_mul_left h (by omega)
    omega
  ext n
  constructor
  · rintro ⟨⟨A, hA, hn⟩, hinterval⟩
    have hgap := card_nsmul_notMem_Icc_of_isAddTorsionFree h k hk A hA
    rw [hn, Set.mem_Icc] at hgap
    simp only [Set.mem_Icc] at hinterval
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl)
    · exact ⟨hlo, le_rfl, hle⟩
    · exact ⟨hhi, hle, le_rfl⟩

end

end MetaMathlibExt
