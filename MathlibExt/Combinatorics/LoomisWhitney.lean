/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The discrete Loomis–Whitney inequality in three dimensions

For a finite set `V` of triples, the square of its cardinality is at most the product of the
cardinalities of its three coordinate projections onto pairs:
`|V|² ≤ |V_{yz}| · |V_{xz}| · |V_{xy}|`.

This is the special case used in communication lower bounds for matrix multiplication
(L. H. Loomis and H. Whitney, *An inequality related to the isoperimetric inequality*,
Bull. Amer. Math. Soc. 55 (1949), 961–962; stated for lattice points as Lemma 1 of
G. Ballard, J. Demmel, O. Holtz and O. Schwartz, *Minimizing communication in numerical linear
algebra*, arXiv:0905.2485, and as Theorem 2.1 of M. Christ, J. Demmel, N. Knight, T. Scanlon and
K. Yelick, *Communication lower bounds and optimal algorithms for programs that reference arrays,
Part 1*, arXiv:1308.0068). No lattice structure is needed: the coordinates may come from any
three types.

The proof slices `V` by its last coordinate `z`. A slice has at most `|V_{xy}|` points and at
most `a_z b_z` points, where `a_z` and `b_z` count the points of `V_{xz}` and `V_{yz}` at height
`z`; so `s_z² ≤ |V_{xy}| a_z b_z`, and the Cauchy–Schwarz inequality
`(∑ s_z)² ≤ (∑ |V_{xy}| a_z)(∑ b_z)` finishes the proof.

## Main results

* `card_sq_le_card_mul_card_mul_card`: `|V|² ≤ |V_{yz}| |V_{xz}| |V_{xy}|`, in `ℕ`.
* `card_le_sqrt_mul_mul`: the same inequality in the square-root form
  `|V| ≤ √(|V_{yz}| |V_{xz}| |V_{xy}|)` of the sources.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.LoomisWhitney

open Finset

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- **Projection onto the last two coordinates.** A triple `(x, y, z)` is sent to `(y, z)`. -/
def projYZ (p : α × β × γ) : β × γ := (p.2.1, p.2.2)

/-- **Projection onto the first and last coordinates.** A triple `(x, y, z)` is sent to
`(x, z)`. -/
def projXZ (p : α × β × γ) : α × γ := (p.1, p.2.2)

/-- **Projection onto the first two coordinates.** A triple `(x, y, z)` is sent to `(x, y)`. -/
def projXY (p : α × β × γ) : α × β := (p.1, p.2.1)

omit [DecidableEq β] in
/-- Sum over heights of a projection: the points of `V.image projXZ` sorted by height. -/
private theorem card_image_projXZ_eq_sum (V : Finset (α × β × γ)) :
    (V.image projXZ).card =
      ∑ z ∈ V.image (fun p => p.2.2), ((V.image projXZ).filter (fun q => q.2 = z)).card := by
  rw [card_eq_sum_card_image Prod.snd (V.image projXZ), image_image]
  rfl

omit [DecidableEq α] in
private theorem card_image_projYZ_eq_sum (V : Finset (α × β × γ)) :
    (V.image projYZ).card =
      ∑ z ∈ V.image (fun p => p.2.2), ((V.image projYZ).filter (fun q => q.2 = z)).card := by
  rw [card_eq_sum_card_image Prod.snd (V.image projYZ), image_image]
  rfl

/-- A slice at height `z` has at most `|V_{xy}|` points. -/
private theorem card_slice_le_xy (V : Finset (α × β × γ)) (z : γ) :
    (V.filter (fun p => p.2.2 = z)).card ≤ (V.image projXY).card := by
  refine card_le_card_of_injOn projXY ?_ ?_
  · intro p hp
    exact mem_image_of_mem _ (mem_filter.1 hp).1
  · intro p hp q hq hpq
    have hpz := (mem_filter.1 hp).2
    have hqz := (mem_filter.1 hq).2
    simp only [projXY, Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (Prod.ext hpq.2 (hpz.trans hqz.symm))

/-- A slice at height `z` has at most `a_z b_z` points. -/
private theorem card_slice_le_mul (V : Finset (α × β × γ)) (z : γ) :
    (V.filter (fun p => p.2.2 = z)).card ≤
      ((V.image projXZ).filter (fun q => q.2 = z)).card *
        ((V.image projYZ).filter (fun q => q.2 = z)).card := by
  calc (V.filter (fun p => p.2.2 = z)).card
      ≤ ((((V.image projXZ).filter (fun q => q.2 = z)).image Prod.fst) ×ˢ
          (((V.image projYZ).filter (fun q => q.2 = z)).image Prod.fst)).card := by
        refine card_le_card_of_injOn projXY ?_ ?_
        · intro p hp
          have hpV := (mem_filter.1 hp).1
          have hpz := (mem_filter.1 hp).2
          refine mem_product.2 ⟨?_, ?_⟩
          · exact mem_image.2 ⟨projXZ p, mem_filter.2 ⟨mem_image_of_mem _ hpV, hpz⟩, rfl⟩
          · exact mem_image.2 ⟨projYZ p, mem_filter.2 ⟨mem_image_of_mem _ hpV, hpz⟩, rfl⟩
        · intro p hp q hq hpq
          have hpz := (mem_filter.1 hp).2
          have hqz := (mem_filter.1 hq).2
          simp only [projXY, Prod.mk.injEq] at hpq
          exact Prod.ext hpq.1 (Prod.ext hpq.2 (hpz.trans hqz.symm))
    _ = (((V.image projXZ).filter (fun q => q.2 = z)).image Prod.fst).card *
          (((V.image projYZ).filter (fun q => q.2 = z)).image Prod.fst).card :=
        card_product _ _
    _ ≤ _ := Nat.mul_le_mul card_image_le card_image_le

/-- **Discrete Loomis–Whitney inequality (three dimensions).** For every finite set `V` of
triples, `|V|² ≤ |V_{yz}| · |V_{xz}| · |V_{xy}|`, where `V_{yz}`, `V_{xz}` and `V_{xy}` are the
images of `V` under the three projections onto pairs of coordinates (Loomis and Whitney 1949;
Ballard, Demmel, Holtz and Schwartz, arXiv:0905.2485, Lemma 1; Christ, Demmel, Knight, Scanlon
and Yelick, arXiv:1308.0068, Theorem 2.1). -/
theorem card_sq_le_card_mul_card_mul_card (V : Finset (α × β × γ)) :
    V.card ^ 2 ≤ (V.image projYZ).card * (V.image projXZ).card * (V.image projXY).card := by
  set Z := V.image (fun p => p.2.2)
  set c := (V.image projXY).card
  have hV : V.card = ∑ z ∈ Z, (V.filter (fun p => p.2.2 = z)).card :=
    card_eq_sum_card_image (fun p => p.2.2) V
  have key : (∑ z ∈ Z, (V.filter (fun p => p.2.2 = z)).card) ^ 2 ≤
      (∑ z ∈ Z, c * ((V.image projXZ).filter (fun q => q.2 = z)).card) *
        ∑ z ∈ Z, ((V.image projYZ).filter (fun q => q.2 = z)).card := by
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul Z (fun _ _ => Nat.zero_le _)
      (fun _ _ => Nat.zero_le _) ?_
    intro z _
    rw [sq, mul_assoc]
    exact Nat.mul_le_mul (card_slice_le_xy V z) (card_slice_le_mul V z)
  rw [hV]
  calc _ ≤ _ := key
    _ = c * (V.image projXZ).card * (V.image projYZ).card := by
        rw [← mul_sum, ← card_image_projXZ_eq_sum, ← card_image_projYZ_eq_sum]
    _ = _ := by ring

/-- **Discrete Loomis–Whitney inequality, square-root form.** For every finite set `V` of
triples, `|V| ≤ √(|V_{yz}| · |V_{xz}| · |V_{xy}|)` (Ballard, Demmel, Holtz and Schwartz,
arXiv:0905.2485, Lemma 1). -/
theorem card_le_sqrt_mul_mul (V : Finset (α × β × γ)) :
    (V.card : ℝ) ≤
      √((V.image projYZ).card * (V.image projXZ).card * (V.image projXY).card : ℝ) := by
  refine Real.le_sqrt_of_sq_le ?_
  exact_mod_cast card_sq_le_card_mul_card_mul_card V

end MathlibExt.Combinatorics.LoomisWhitney
