/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.HomDensity

/-!
# The Frieze–Kannan weak regularity lemma

For every `ε > 0`, every weighted graph `w : Sym2 V → ℝ` on a finite vertex set (unit node
weights) has a partition `P` of `V` into at most `4 ^ (1 / ε²)` classes such that the cut distance
between `w` and its partition average `w_P` is at most `ε ‖w‖₂`
(Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences of dense graphs I*, Adv. Math. 219
(2008), Lemma 2.4, inequality (2.10); Frieze and Kannan, *Quick approximation to matrices and
applications*, Combinatorica 19 (1999)).

The proof is the energy increment argument. The *energy* of `P` is `∑_{x,y} w_P(x, y)²`. Since
`w - w_P` is orthogonal to every function that is constant on the blocks `Vᵢ × Vⱼ` of `P`, the
energy is at most `∑ w²`, and refining `P` raises it by `‖w_Q - w_P‖²`. If `w_P` is not
`ε`-close to `w` in the cut norm, refining `P` by the two sets `S, T` of a witnessing rectangle
multiplies the number of classes by at most `4` and, by the Cauchy–Schwarz inequality, raises the
energy by more than `ε² ∑ w²`; so after at most `1 / ε²` refinements the partition is good.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.GraphLimits

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Block-constant functions.** A function `g : V → V → ℝ` is constant on the blocks
`Vᵢ × Vⱼ` of a partition `P` of `V`. -/
def IsBlockConstant (P : Finpartition (univ : Finset V)) (g : V → V → ℝ) : Prop :=
  ∀ x x' y y', P.part x = P.part x' → P.part y = P.part y' → g x y = g x' y'

theorem partitionAverage_apply (P : Finpartition (univ : Finset V)) (w : Sym2 V → ℝ) (x y : V) :
    partitionAverage P w s(x, y) = (∑ a ∈ P.part x, ∑ b ∈ P.part y, w s(a, b)) /
      (((P.part x).card : ℝ) * (P.part y).card) := rfl

/-- **The partition average is block-constant.** The partition average `w_P` is constant on the
blocks of `P`. -/
theorem isBlockConstant_partitionAverage (P : Finpartition (univ : Finset V))
    (w : Sym2 V → ℝ) : IsBlockConstant P fun x y => partitionAverage P w s(x, y) := by
  intro x x' y y' hx hy
  simp only [partitionAverage_apply, hx, hy]

/-- **Orthogonality of the partition average.** `w - w_P` is orthogonal to every function that is
constant on the blocks of `P`: `∑_{x,y} (w - w_P)(x, y) g(x, y) = 0`. -/
theorem sum_sub_partitionAverage_mul_eq_zero (P : Finpartition (univ : Finset V))
    (w : Sym2 V → ℝ) {g : V → V → ℝ} (hg : IsBlockConstant P g) :
    ∑ x, ∑ y, (w s(x, y) - partitionAverage P w s(x, y)) * g x y = 0 := by
  have hsplit : ∀ f : V → ℝ, ∑ x, f x = ∑ A ∈ P.parts, ∑ x ∈ A, f x := by
    intro f
    conv_lhs => rw [← P.biUnion_parts]
    rw [sum_biUnion P.disjoint]
    rfl
  rw [hsplit]
  refine sum_eq_zero fun A hA => ?_
  rw [sum_comm, hsplit]
  refine sum_eq_zero fun B hB => ?_
  obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hA
  obtain ⟨b, hb⟩ := P.nonempty_of_mem_parts hB
  have hA0 : (0 : ℝ) < A.card := by exact_mod_cast (P.nonempty_of_mem_parts hA).card_pos
  have hB0 : (0 : ℝ) < B.card := by exact_mod_cast (P.nonempty_of_mem_parts hB).card_pos
  have key : ∀ x ∈ A, ∀ y ∈ B,
      (w s(x, y) - partitionAverage P w s(x, y)) * g x y =
        (w s(x, y) - (∑ a ∈ A, ∑ b ∈ B, w s(a, b)) / ((A.card : ℝ) * B.card)) * g a b := by
    intro x hx y hy
    have hpx : P.part x = A := P.part_eq_of_mem hA hx
    have hpy : P.part y = B := P.part_eq_of_mem hB hy
    have hpa : P.part a = A := P.part_eq_of_mem hA ha
    have hpb : P.part b = B := P.part_eq_of_mem hB hb
    rw [partitionAverage_apply, hpx, hpy, hg x a y b (hpx.trans hpa.symm) (hpy.trans hpb.symm)]
  rw [sum_comm]
  rw [sum_congr rfl fun x hx => sum_congr rfl fun y hy => key x hx y hy]
  simp only [← sum_mul, sum_sub_distrib, sum_const, nsmul_eq_mul]
  field_simp
  ring

/-- **Energy of a partition.** `∑_{x,y} w_P(x, y)²`, the squared `L²` mass of the partition
average. -/
noncomputable def partitionEnergy (P : Finpartition (univ : Finset V)) (w : Sym2 V → ℝ) : ℝ :=
  ∑ x, ∑ y, partitionAverage P w s(x, y) ^ 2

/-- **The energy is bounded by the total mass.** The energy of every partition is at most
`∑_{x,y} w(x, y)²`. -/
theorem partitionEnergy_le (P : Finpartition (univ : Finset V)) (w : Sym2 V → ℝ) :
    partitionEnergy P w ≤ ∑ x, ∑ y, w s(x, y) ^ 2 := by
  have horth := sum_sub_partitionAverage_mul_eq_zero P w (isBlockConstant_partitionAverage P w)
  have h : ∑ x, ∑ y, w s(x, y) ^ 2 - partitionEnergy P w =
      ∑ x, ∑ y, (w s(x, y) - partitionAverage P w s(x, y)) ^ 2 +
        2 * ∑ x, ∑ y, (w s(x, y) - partitionAverage P w s(x, y)) *
          partitionAverage P w s(x, y) := by
    simp only [partitionEnergy, ← sum_sub_distrib, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
  have h2 : 0 ≤ ∑ x, ∑ y, (w s(x, y) - partitionAverage P w s(x, y)) ^ 2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- **Common refinement relation.** Two vertices are related when they lie in the same class of `P`
and on the same side of `S` and of `T`. -/
def refineSetoid (P : Finpartition (univ : Finset V)) (S T : Finset V) : Setoid V where
  r x y := P.part x = P.part y ∧ (x ∈ S ↔ y ∈ S) ∧ (x ∈ T ↔ y ∈ T)
  iseqv :=
    ⟨fun _ => ⟨rfl, Iff.rfl, Iff.rfl⟩, fun h => ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩,
      fun h h' => ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩⟩

instance (P : Finpartition (univ : Finset V)) (S T : Finset V) :
    DecidableRel (refineSetoid P S T).r := fun x y =>
  inferInstanceAs (Decidable (P.part x = P.part y ∧ (x ∈ S ↔ y ∈ S) ∧ (x ∈ T ↔ y ∈ T)))

/-- **Refinement by two sets.** The common refinement of `P` with the partitions `{S, Sᶜ}` and
`{T, Tᶜ}`. -/
noncomputable def refineBy (P : Finpartition (univ : Finset V)) (S T : Finset V) :
    Finpartition (univ : Finset V) :=
  Finpartition.ofSetoid (refineSetoid P S T)

theorem refineBy_part_eq {P : Finpartition (univ : Finset V)} {S T : Finset V} {x x' : V}
    (h : (refineBy P S T).part x = (refineBy P S T).part x') :
    P.part x = P.part x' ∧ (x ∈ S ↔ x' ∈ S) ∧ (x ∈ T ↔ x' ∈ T) := by
  have hx' : x' ∈ (refineBy P S T).part x := by
    rw [h]
    exact (refineBy P S T).mem_part (mem_univ x')
  exact Finpartition.mem_part_ofSetoid_iff_rel.1 hx'

/-- **Refinement multiplies the number of classes by at most four.** Refining by two sets
multiplies the number of classes by at most `4`. -/
theorem card_refineBy_parts_le (P : Finpartition (univ : Finset V)) (S T : Finset V) :
    (refineBy P S T).parts.card ≤ 4 * P.parts.card := by
  classical
  set h : Finset V × Bool × Bool → Finset V := fun k =>
    univ.filter fun y => y ∈ k.1 ∧ (y ∈ S ↔ k.2.1 = true) ∧ (y ∈ T ↔ k.2.2 = true)
  have hsub : (refineBy P S T).parts ⊆ (P.parts ×ˢ (univ ×ˢ univ)).image h := by
    intro C hC
    have hC' : C ∈ univ.image fun a => univ.filter fun b => (refineSetoid P S T) a b := hC
    obtain ⟨a, -, rfl⟩ := mem_image.1 hC'
    refine mem_image.2 ⟨(P.part a, decide (a ∈ S), decide (a ∈ T)), ?_, ?_⟩
    · simp only [mem_product, mem_univ, and_true]
      exact P.part_mem.2 (mem_univ a)
    · ext b
      have hb : b ∈ P.part a ↔ P.part b = P.part a :=
        P.mem_part_iff_part_eq_part (mem_univ b) (mem_univ a)
      simp only [h, mem_filter, mem_univ, true_and, hb, decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1.symm, h2.symm, h3.symm⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1.symm, h2.symm, h3.symm⟩
  calc (refineBy P S T).parts.card ≤ ((P.parts ×ˢ (univ ×ˢ univ)).image h).card :=
        card_le_card hsub
    _ ≤ (P.parts ×ˢ (univ ×ˢ univ : Finset (Bool × Bool))).card := card_image_le
    _ = 4 * P.parts.card := by simp [card_product]; ring

/-- **Energy increment.** Refining `P` by the two sets `S, T` raises the energy by at least
`|V|⁻² (∑_{x ∈ S, y ∈ T} (w - w_P)(x, y))²`. -/
theorem sq_sum_sub_partitionAverage_le (P : Finpartition (univ : Finset V)) (w : Sym2 V → ℝ)
    (S T : Finset V) :
    (∑ x ∈ S, ∑ y ∈ T, (w - partitionAverage P w) s(x, y)) ^ 2 ≤
      (Fintype.card V : ℝ) ^ 2 * (partitionEnergy (refineBy P S T) w - partitionEnergy P w) := by
  set Q := refineBy P S T
  set WP : V → V → ℝ := fun x y => partitionAverage P w s(x, y)
  set WQ : V → V → ℝ := fun x y => partitionAverage Q w s(x, y)
  set g : V → V → ℝ := fun x y => if x ∈ S ∧ y ∈ T then 1 else 0
  have hgQ : IsBlockConstant Q g := by
    intro x x' y y' hx hy
    have h1 := refineBy_part_eq hx
    have h2 := refineBy_part_eq hy
    simp only [g, h1.2.1, h2.2.2]
  have hPQ : IsBlockConstant Q WP := by
    intro x x' y y' hx hy
    exact isBlockConstant_partitionAverage P w x x' y y' (refineBy_part_eq hx).1
      (refineBy_part_eq hy).1
  -- the rectangle sum as an inner product with the indicator `g`
  have hrect' : ∑ x, ∑ y, (w s(x, y) - WP x y) * g x y =
      ∑ x ∈ S, ∑ y ∈ T, (w - partitionAverage P w) s(x, y) := by
    rw [← sum_subset (subset_univ S) (fun x _ hx => sum_eq_zero fun y _ => by simp [g, hx])]
    refine sum_congr rfl fun x hx => ?_
    rw [← sum_subset (subset_univ T) (fun y _ hy => by simp [g, hy])]
    refine sum_congr rfl fun y hy => ?_
    simp [g, hx, hy, WP]
  have hrect := hrect'.symm
  have horthQg := sum_sub_partitionAverage_mul_eq_zero Q w hgQ
  have horthQP := sum_sub_partitionAverage_mul_eq_zero Q w hPQ
  have horthP := sum_sub_partitionAverage_mul_eq_zero P w (isBlockConstant_partitionAverage P w)
  -- `w - w_P = (w - w_Q) + (w_Q - w_P)` against `g`
  have h1 : ∑ x, ∑ y, (w s(x, y) - WP x y) * g x y =
      ∑ x, ∑ y, (WQ x y - WP x y) * g x y := by
    have : ∑ x, ∑ y, (w s(x, y) - WP x y) * g x y - ∑ x, ∑ y, (WQ x y - WP x y) * g x y =
        ∑ x, ∑ y, (w s(x, y) - WQ x y) * g x y := by
      simp only [← sum_sub_distrib]
      exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
    linarith
  -- the energy gain is `∑ (w_Q - w_P)²`
  have h2 : partitionEnergy Q w - partitionEnergy P w = ∑ x, ∑ y, (WQ x y - WP x y) ^ 2 := by
    have : partitionEnergy Q w - partitionEnergy P w - ∑ x, ∑ y, (WQ x y - WP x y) ^ 2 =
        2 * (∑ x, ∑ y, (w s(x, y) - WP x y) * WP x y -
          ∑ x, ∑ y, (w s(x, y) - WQ x y) * WP x y) := by
      simp only [partitionEnergy, ← sum_sub_distrib, mul_sum]
      exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
    have e1 : ∑ x, ∑ y, (w s(x, y) - WP x y) * WP x y = 0 := horthP
    have e2 : ∑ x, ∑ y, (w s(x, y) - WQ x y) * WP x y = 0 := horthQP
    rw [e1, e2] at this
    linarith
  -- Cauchy–Schwarz over pairs
  have hcs : (∑ x, ∑ y, (WQ x y - WP x y) * g x y) ^ 2 ≤
      (∑ x, ∑ y, (WQ x y - WP x y) ^ 2) * ∑ x, ∑ y, g x y ^ 2 := by
    have := sum_mul_sq_le_sq_mul_sq (univ : Finset (V × V)) (fun p => WQ p.1 p.2 - WP p.1 p.2)
      (fun p => g p.1 p.2)
    have e1 := Fintype.sum_prod_type' (fun x y => (WQ x y - WP x y) * g x y)
    have e2 := Fintype.sum_prod_type' (fun x y => (WQ x y - WP x y) ^ 2)
    have e3 := Fintype.sum_prod_type' (fun x y => g x y ^ 2)
    rw [← e1, ← e2, ← e3]
    exact this
  have hg2 : ∑ x, ∑ y, g x y ^ 2 ≤ (Fintype.card V : ℝ) ^ 2 := by
    calc ∑ x, ∑ y, g x y ^ 2 ≤ ∑ _x : V, ∑ _y : V, (1 : ℝ) :=
          sum_le_sum fun x _ => sum_le_sum fun y _ => by
            simp only [g]; split_ifs <;> norm_num
      _ = (Fintype.card V : ℝ) ^ 2 := by simp [sq]
  have hD : 0 ≤ ∑ x, ∑ y, (WQ x y - WP x y) ^ 2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  rw [hrect, h1, h2]
  calc (∑ x, ∑ y, (WQ x y - WP x y) * g x y) ^ 2
      ≤ (∑ x, ∑ y, (WQ x y - WP x y) ^ 2) * ∑ x, ∑ y, g x y ^ 2 := hcs
    _ ≤ (∑ x, ∑ y, (WQ x y - WP x y) ^ 2) * (Fintype.card V : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hg2 hD
    _ = (Fintype.card V : ℝ) ^ 2 * ∑ x, ∑ y, (WQ x y - WP x y) ^ 2 := mul_comm _ _

/-- **One refinement step.** If `w_P` is not `ε`-close to `w` in the cut norm, some refinement
with at most four times as many classes has energy larger by more than `ε² ∑ w²`. -/
theorem exists_refinement_of_lt_cutNorm (hV : 0 < Fintype.card V)
    (P : Finpartition (univ : Finset V)) (w : Sym2 V → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hP : ε * kernelL2Norm w < cutNorm (w - partitionAverage P w)) :
    ∃ Q : Finpartition (univ : Finset V), Q.parts.card ≤ 4 * P.parts.card ∧
      partitionEnergy P w + ε ^ 2 * ∑ x, ∑ y, w s(x, y) ^ 2 < partitionEnergy Q w := by
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  have hn : 0 < n := by rw [hn_def]; exact_mod_cast hV
  set A2 := ∑ x, ∑ y, w s(x, y) ^ 2 with hA2
  have hA2nn : 0 ≤ A2 := sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨⟨S, T⟩, -, hST⟩ := exists_mem_eq_sup' (univ_nonempty (α := Finset V × Finset V))
    (fun p => |∑ x ∈ p.1, ∑ y ∈ p.2, (w - partitionAverage P w) s(x, y)|)
  refine ⟨refineBy P S T, card_refineBy_parts_le P S T, ?_⟩
  have hinc := sq_sum_sub_partitionAverage_le P w S T
  -- the witnessing rectangle exceeds `ε n √A2`
  have hL2 : kernelL2Norm w = Real.sqrt A2 / n := by
    rw [kernelL2Norm, ← hA2, ← hn_def, Real.sqrt_div' _ (sq_nonneg n), Real.sqrt_sq hn.le]
  have hcut : cutNorm (w - partitionAverage P w) =
      |∑ x ∈ S, ∑ y ∈ T, (w - partitionAverage P w) s(x, y)| / n ^ 2 := by
    rw [cutNorm, cutMax, hST]
  rw [hcut, hL2, lt_div_iff₀ (by positivity)] at hP
  have hbig : ε * n * Real.sqrt A2 < |∑ x ∈ S, ∑ y ∈ T, (w - partitionAverage P w) s(x, y)| := by
    have : ε * (Real.sqrt A2 / n) * n ^ 2 = ε * n * Real.sqrt A2 := by field_simp
    linarith
  have h0 : 0 ≤ ε * n * Real.sqrt A2 := by positivity
  have hsq : (ε * n * Real.sqrt A2) ^ 2 <
      (∑ x ∈ S, ∑ y ∈ T, (w - partitionAverage P w) s(x, y)) ^ 2 := by
    rw [← sq_abs (∑ x ∈ S, ∑ y ∈ T, (w - partitionAverage P w) s(x, y))]
    exact pow_lt_pow_left₀ hbig h0 two_ne_zero
  have hexp : (ε * n * Real.sqrt A2) ^ 2 = n ^ 2 * (ε ^ 2 * A2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hA2nn]
    ring
  rw [hexp] at hsq
  have := lt_of_lt_of_le hsq hinc
  have h' := lt_of_mul_lt_mul_left this (by positivity : (0 : ℝ) ≤ n ^ 2)
  linarith

/-- **Weak regularity lemma (Frieze–Kannan).** For every `ε > 0`, every weighted graph `w` on a
finite vertex set `V` (unit node weights) has a partition `P` of `V` into at most `4 ^ (1 / ε²)`
classes with `d_□(G, G_P) ≤ ε ‖G‖₂`, where `G_P` is the partition average of `G`
(Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences of dense graphs I*, Adv. Math. 219
(2008), Lemma 2.4, inequality (2.10), after Frieze and Kannan, *Quick approximation to matrices
and applications*, Combinatorica 19 (1999)). -/
theorem exists_cutNorm_sub_partitionAverage_le (w : Sym2 V → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Finpartition (univ : Finset V), (P.parts.card : ℝ) ≤ (4 : ℝ) ^ (1 / ε ^ 2) ∧
      cutNorm (w - partitionAverage P w) ≤ ε * kernelL2Norm w := by
  have hL2nn : 0 ≤ kernelL2Norm w := Real.sqrt_nonneg _
  have hpow : 0 < (4 : ℝ) ^ (1 / ε ^ 2) := Real.rpow_pos_of_pos (by norm_num) _
  rcases (Fintype.card V).eq_zero_or_pos with hV | hV
  · -- no vertices: the empty partition
    refine ⟨⊥, ?_, ?_⟩
    · have := (⊥ : Finpartition (univ : Finset V)).card_parts_le_card
      rw [card_univ, hV, Nat.le_zero] at this
      rw [this, Nat.cast_zero]
      exact hpow.le
    · rw [cutNorm, hV, Nat.cast_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero]
      positivity
  set A2 := ∑ x, ∑ y, w s(x, y) ^ 2 with hA2
  set m₀ := ⌊1 / ε ^ 2⌋₊ with hm₀
  -- after `m` steps: at most `4 ^ m` classes, and either good or energy at least `m ε² A2`
  have claim : ∀ m : ℕ, ∃ P : Finpartition (univ : Finset V),
      (P.parts.card : ℝ) ≤ 4 ^ m ∧
        (cutNorm (w - partitionAverage P w) ≤ ε * kernelL2Norm w ∨
          m * (ε ^ 2 * A2) ≤ partitionEnergy P w) := by
    intro m
    induction m with
    | zero =>
      have hne : (univ : Finset V) ≠ ⊥ := (univ_nonempty_iff.2 (Fintype.card_pos_iff.1 hV)).ne_empty
      refine ⟨Finpartition.indiscrete hne, ?_, Or.inr ?_⟩
      · simp [Finpartition.indiscrete]
      · simp only [CharP.cast_eq_zero, zero_mul]
        exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
    | succ m ih =>
      obtain ⟨P, hcard, hgood | hE⟩ := ih
      · exact ⟨P, hcard.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ m)), Or.inl hgood⟩
      by_cases hP : cutNorm (w - partitionAverage P w) ≤ ε * kernelL2Norm w
      · exact ⟨P, hcard.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ m)), Or.inl hP⟩
      obtain ⟨Q, hQc, hQE⟩ := exists_refinement_of_lt_cutNorm hV P w hε (not_le.1 hP)
      refine ⟨Q, ?_, Or.inr ?_⟩
      · calc (Q.parts.card : ℝ) ≤ 4 * P.parts.card := by exact_mod_cast hQc
          _ ≤ 4 * 4 ^ m := by linarith
          _ = 4 ^ (m + 1) := by ring
      · push_cast
        linarith
  obtain ⟨P, hcard, hPE⟩ := claim m₀
  have hcard' : (P.parts.card : ℝ) ≤ (4 : ℝ) ^ (1 / ε ^ 2) := by
    refine hcard.trans ?_
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le (by positivity))
  by_cases hP : cutNorm (w - partitionAverage P w) ≤ ε * kernelL2Norm w
  · exact ⟨P, hcard', hP⟩
  -- otherwise one more step would exceed the maximal energy `A2`
  exfalso
  have hE : (m₀ : ℝ) * (ε ^ 2 * A2) ≤ partitionEnergy P w := hPE.resolve_left hP
  obtain ⟨Q, -, hQE⟩ := exists_refinement_of_lt_cutNorm hV P w hε (not_le.1 hP)
  have hA2nn : 0 ≤ A2 := sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have hfl : 1 < ((m₀ : ℝ) + 1) * ε ^ 2 := by
    have := Nat.lt_floor_add_one (1 / ε ^ 2)
    rw [← hm₀] at this
    have hε2 : 0 < ε ^ 2 := by positivity
    rw [div_lt_iff₀ hε2] at this
    linarith
  have hQle := partitionEnergy_le Q w
  nlinarith

end MathlibExt.Combinatorics.SimpleGraph.GraphLimits
