/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.ZMod
public import MathlibExt.Combinatorics.Additive.GDifferenceBases

/-!
# Difference bases modulo a prime

For `k = ⌈√p⌉`, use the residues of `k * q` and `-r` for `q, r < k`. Translating by `k`
places these elements in the Rédei–Rényi set. Division with remainder represents every residue
as the difference of a multiple and a negated remainder.
-/

namespace MetaMathlibExt

/-- **Difference bases of the integers modulo a prime.** For every prime $p$, the least size
$\eta_1(\mathbb{Z}/p\mathbb{Z})$ of a set $A \subseteq \mathbb{Z}/p\mathbb{Z}$ such that every
residue modulo $p$ is a difference $a - a'$ of two elements of $A$ satisfies
$\eta_1(\mathbb{Z}/p\mathbb{Z}) \le 2 \lceil \sqrt{p} \rceil$.

The bound comes from reducing the Rédei–Rényi set modulo $p$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, equation (5) after Lemma 5 (`integers-2025-A77-lem-5`). -/
public theorem groupDiffBasisNumber_zmod_le (p : ℕ) [Fact p.Prime] :
    groupDiffBasisNumber 1 (ZMod p) ≤ 2 * ⌈Real.sqrt p⌉₊ := by
  let k := ⌈Real.sqrt p⌉₊
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hk : 0 < k := Nat.ceil_pos.mpr (Real.sqrt_pos.2 (by exact_mod_cast hp))
  have hsq : p ≤ k * k := by
    have h : Real.sqrt p ≤ (k : ℝ) := Nat.le_ceil _
    rw [← sq]
    exact_mod_cast (Real.sqrt_le_iff.mp h).2
  let multiples := (Finset.range k).image fun q => ((k * q : ℕ) : ZMod p)
  let negRemainders := (Finset.range k).image fun r : ℕ => -(r : ZMod p)
  let A := multiples ∪ negRemainders
  calc
    groupDiffBasisNumber 1 (ZMod p) ≤ A.card := by
      apply Nat.sInf_le
      refine ⟨A, rfl, fun x => ?_⟩
      have hq : x.val / k < k := (Nat.div_lt_iff_lt_mul hk).2 (x.val_lt.trans_le hsq)
      apply Finset.card_pos.mpr
      refine ⟨(↑(k * (x.val / k)), -(↑(x.val % k) : ZMod p)), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩⟩
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hq))
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
          (Finset.mem_range.mpr (Nat.mod_lt _ hk)))
      · simp only [sub_neg_eq_add, ← Nat.cast_add, Nat.div_add_mod, ZMod.natCast_zmod_val]
    _ ≤ multiples.card + negRemainders.card := Finset.card_union_le _ _
    _ ≤ (Finset.range k).card + (Finset.range k).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * k := by simp [two_mul]

end MetaMathlibExt
