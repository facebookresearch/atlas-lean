/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.FastVanDerWaerdenGame
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A fast Maker win forces symmetry

Defines the winning condition, bounded Maker strategies, and symmetry, and proves that
a win in the cardinality of the target set forces symmetry.

Hannah Alpert, Liam Barham, Brian Freidin, Ian Tan, and Alexandra Weiner,
"Fast Winning Strategies in a Generalized van der Waerden Game",
*INTEGERS* 26 (2026), Article A40 (arXiv:2309.11367), Lemma 1.
-/

set_option autoImplicit false

namespace MetaMathlibExt.FastVanDerWaerdenGame

open Finset

@[expose] public section

/-- **Containing a homothetic copy.** Let $S$ and $M$ be finite sets of natural numbers. $M$
contains a homothetic copy of $S$ if there are a natural number $a > 0$ and an integer $b$ such
that $as + b \in M$ for every $s \in S$, that is, $aS + b \subseteq M$. This is Maker's winning
condition.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 1. -/
def ContainsCopy (S M : Finset ℕ) : Prop :=
  ∃ a : ℕ, 0 < a ∧ ∃ b : ℤ, ∀ s ∈ S, ∃ m ∈ M, (m : ℤ) = a * s + b

/-- **Maker wins within $p$ moves.** Let $S$ be a finite set of natural numbers. In the
$S$-game, Maker and Breaker alternately claim unclaimed natural numbers, and Maker wins once the
numbers Maker has claimed contain a copy $aS + b = \{as + b : s \in S\}$ of $S$, where $a$ is a
positive integer and $b$ is an integer. Let $M$ and $B$ be finite sets of natural numbers
(claimed by Maker and by Breaker) and $p$ a natural number, with Maker to move. Maker wins
within $p$ moves if $M$ already contains such a copy of $S$, or if $p \ge 1$ and there is a
number $x \notin M \cup B$ such that for every number $y \ne x$ with $y \notin M \cup B$, Maker
wins within $p - 1$ moves from the position where Maker has claimed $M \cup \{x\}$ and Breaker
has claimed $B \cup \{y\}$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Sections 1
and 5 (`p`-move strategy). -/
def MakerWinsWithin (S : Finset ℕ) : ℕ → Finset ℕ → Finset ℕ → Prop
  | 0, M, _ => ContainsCopy S M
  | p + 1, M, B => ContainsCopy S M ∨
      ∃ x : ℕ, x ∉ M ∧ x ∉ B ∧
        ∀ y : ℕ, y ≠ x → y ∉ M → y ∉ B → MakerWinsWithin S p (insert x M) (insert y B)

/-- **Symmetric sets of rationals.** A finite set $S$ of rational numbers is symmetric if it is
symmetric of some type $(i, j)$ with $i, j < |S|$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 2. -/
def IsSymmetric (S : Finset ℚ) : Prop :=
  ∃ i j : Fin S.card, IsSymmetricOfType S i j

end

private theorem affine_injective (a b : ℚ) (ha : 0 < a) :
    Function.Injective (fun x : ℚ => a * x + b) := by
  intro x y h
  exact (mul_left_cancel₀ ha.ne' (add_right_cancel h))

private theorem containsCopy_subset (S M : Finset ℕ) (h : ContainsCopy S M) :
    ∃ a b : ℚ, 0 < a ∧
      (S.image fun s : ℕ => (s : ℚ)).image (fun x => a * x + b) ⊆
        M.image (fun m : ℕ => (m : ℚ)) := by
  obtain ⟨a, ha, b, h⟩ := h
  refine ⟨a, b, by exact_mod_cast ha, ?_⟩
  intro x hx
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hx
  obtain ⟨s, hs, rfl⟩ := mem_image.mp hq
  obtain ⟨m, hm, he⟩ := h s hs
  exact mem_image.mpr ⟨m, hm, by exact_mod_cast he⟩

private theorem containsCopy_card_le (S M : Finset ℕ) (h : ContainsCopy S M) :
    S.card ≤ M.card := by
  obtain ⟨a, b, ha, hs⟩ := containsCopy_subset S M h
  have hc := card_le_card hs
  simpa only [card_image_of_injective _ (affine_injective a b ha),
    card_image_of_injective _ Nat.cast_injective] using hc

private theorem containsCopy_ratCopy (S M : Finset ℕ) (h : ContainsCopy S M)
    (hc : M.card = S.card) :
    IsRatCopy (S.image fun s : ℕ => (s : ℚ)) (M.image fun m : ℕ => (m : ℚ)) := by
  obtain ⟨a, b, ha, hs⟩ := containsCopy_subset S M h
  refine ⟨a, b, ha, (eq_of_subset_of_card_le hs ?_).symm⟩
  simp only [card_image_of_injective _ (affine_injective a b ha),
    card_image_of_injective _ Nat.cast_injective, hc, le_refl]

private theorem legal_response (M B : Finset ℕ) (x : ℕ) :
    ∃ y : ℕ, y ≠ x ∧ y ∉ M ∧ y ∉ B := by
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (insert x (M ∪ B))
  refine ⟨y, ?_⟩
  simpa only [mem_insert, mem_union, not_or] using hy

private theorem one_move_completion (S M B : Finset ℕ) (hc : M.card + 1 = S.card)
    (h : MakerWinsWithin S 1 M B) :
    ∃ x : ℕ, x ∉ M ∧ x ∉ B ∧ ContainsCopy S (insert x M) := by
  rcases h with h | ⟨x, hxM, hxB, h⟩
  · have := containsCopy_card_le S M h
    omega
  · obtain ⟨y, hyx, hyM, hyB⟩ := legal_response M B x
    exact ⟨x, hxM, hxB, h y hyx hyM hyB⟩

private theorem two_completions (S : Finset ℕ) (p : ℕ) (M B : Finset ℕ)
    (hc : M.card + (p + 2) = S.card) (h : MakerWinsWithin S (p + 2) M B) :
    ∃ T : Finset ℕ, ∃ x y : ℕ, T.card + 1 = S.card ∧ x ∉ T ∧ y ∉ T ∧ x ≠ y ∧
      ContainsCopy S (insert x T) ∧ ContainsCopy S (insert y T) := by
  induction p generalizing M B with
  | zero =>
    rcases h with h | ⟨z, hzM, hzB, h⟩
    · have := containsCopy_card_le S M h
      omega
    · have hT : (insert z M).card + 1 = S.card := by
        rw [card_insert_of_notMem hzM]
        omega
      obtain ⟨b, hbz, hbM, hbB⟩ := legal_response M B z
      obtain ⟨x, hxT, hxB, hx⟩ :=
        one_move_completion S (insert z M) (insert b B) hT (h b hbz hbM hbB)
      have hxT' : x ≠ z ∧ x ∉ M := by simpa only [mem_insert, not_or] using hxT
      have hxB' : x ≠ b ∧ x ∉ B := by simpa only [mem_insert, not_or] using hxB
      obtain ⟨y, hyT, hyB, hy⟩ :=
        one_move_completion S (insert z M) (insert x B) hT (h x hxT'.1 hxT'.2 hxB'.2)
      have hyB' : y ≠ x ∧ y ∉ B := by simpa only [mem_insert, not_or] using hyB
      exact ⟨insert z M, x, y, hT, hxT, hyT, hyB'.1.symm, hx, hy⟩
  | succ p ih =>
    rcases h with h | ⟨x, hxM, hxB, h⟩
    · have := containsCopy_card_le S M h
      omega
    · obtain ⟨y, hyx, hyM, hyB⟩ := legal_response M B x
      apply ih (insert x M) (insert y B) _ (h y hyx hyM hyB)
      rw [card_insert_of_notMem hxM]
      omega

private theorem affine_eq_of_image_eq (A : Finset ℚ) (hA : 2 ≤ A.card)
    (a b c d : ℚ) (ha : 0 < a) (hc : 0 < c)
    (he : A.image (fun x => a * x + b) = A.image (fun x => c * x + d)) :
    a = c ∧ b = d := by
  have hcard : (A.image (fun x => a * x + b)).card = A.card :=
    card_image_of_injective A (affine_injective a b ha)
  have hf := orderEmbOfFin_unique hcard
    (fun i => mem_image.mpr ⟨_, A.orderEmbOfFin_mem rfl i, rfl⟩)
    (show StrictMono (fun i : Fin A.card => a * A.orderEmbOfFin rfl i + b) from
      fun i j hij => (add_lt_add_iff_right b).2
        (mul_lt_mul_of_pos_left ((A.orderEmbOfFin rfl).strictMono hij) ha))
  have hg := orderEmbOfFin_unique hcard
    (fun i => by
      rw [he]
      exact mem_image.mpr ⟨_, A.orderEmbOfFin_mem rfl i, rfl⟩)
    (show StrictMono (fun i : Fin A.card => c * A.orderEmbOfFin rfl i + d) from
      fun i j hij => (add_lt_add_iff_right d).2
        (mul_lt_mul_of_pos_left ((A.orderEmbOfFin rfl).strictMono hij) hc))
  have h0 := congrFun (hf.trans hg.symm) ⟨0, by omega⟩
  have h1 := congrFun (hf.trans hg.symm) ⟨1, by omega⟩
  have h01 := (A.orderEmbOfFin rfl).strictMono
    (show (⟨0, by omega⟩ : Fin A.card) < ⟨1, by omega⟩ from Nat.zero_lt_one)
  have hz : (a - c) * (A.orderEmbOfFin rfl ⟨1, by omega⟩ -
      A.orderEmbOfFin rfl ⟨0, by omega⟩) = 0 := by
    nlinarith only [h0, h1]
  have hac := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr h01.ne'))
  exact ⟨hac, by simpa only [hac, add_right_inj] using h0⟩

private theorem ratCopy_of_equal_images (A B : Finset ℚ) (a b c d : ℚ)
    (ha : 0 < a) (hc : 0 < c)
    (he : A.image (fun x => a * x + b) = B.image (fun x => c * x + d)) :
    IsRatCopy A B := by
  refine ⟨a / c, (b - d) / c, div_pos ha hc, ?_⟩
  have hleft : (A.image (fun x => a * x + b)).image (fun x => (x - d) / c) =
      A.image (fun x => a / c * x + (b - d) / c) := by
    rw [image_image]
    congr 1
    funext x
    dsimp only [Function.comp_apply]
    field_simp
    ring
  have hright : (B.image (fun x => c * x + d)).image (fun x => (x - d) / c) = B := by
    rw [image_image]
    have hid : (fun x : ℚ => (c * x + d - d) / c) = id := by
      funext x
      dsimp only [id_eq]
      field_simp
      ring
    change B.image (fun x => (c * x + d - d) / c) = B
    rw [hid, image_id]
  exact hright.symm.trans ((congrArg (fun T : Finset ℚ => T.image
    (fun x => (x - d) / c)) he).symm.trans hleft)

private theorem symmetric_of_erasure_images (Q T : Finset ℚ) (u v : ℚ)
    (hu : u ∈ Q) (hv : v ∈ Q) (huv : u ≠ v) (a b c d : ℚ)
    (ha : 0 < a) (hc : 0 < c)
    (hf : (Q.erase u).image (fun x => a * x + b) = T)
    (hg : (Q.erase v).image (fun x => c * x + d) = T) : IsSymmetric Q := by
  let i := (Q.orderIsoOfFin rfl).symm ⟨u, hu⟩
  let j := (Q.orderIsoOfFin rfl).symm ⟨v, hv⟩
  have hi : Q.orderEmbOfFin rfl i = u := by
    exact congrArg Subtype.val ((Q.orderIsoOfFin rfl).apply_symm_apply ⟨u, hu⟩)
  have hj : Q.orderEmbOfFin rfl j = v := by
    exact congrArg Subtype.val ((Q.orderIsoOfFin rfl).apply_symm_apply ⟨v, hv⟩)
  have hij : i ≠ j := by
    intro h
    exact huv (hi.symm.trans ((congrArg (Q.orderEmbOfFin rfl) h).trans hj))
  rcases lt_or_gt_of_ne hij with hij | hji
  · refine ⟨i, j, hij, ?_⟩
    rw [hi, hj]
    exact ratCopy_of_equal_images _ _ c d a b hc ha (hg.trans hf.symm)
  · refine ⟨j, i, hji, ?_⟩
    rw [hi, hj]
    exact ratCopy_of_equal_images _ _ a b c d ha hc (hf.trans hg.symm)

private theorem symmetric_of_card_two (Q : Finset ℚ) (hQ : Q.card = 2) : IsSymmetric Q := by
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hQ
  apply symmetric_of_erasure_images {u, v} {0} u v (by simp) (by simp) huv
    1 (-v) 1 (-u) zero_lt_one zero_lt_one
  · simp [huv]
  · rw [erase_insert_of_ne huv]
    simp

private theorem symmetric_of_two_copies (Q T : Finset ℚ) (hQ : 2 ≤ Q.card)
    (x y : ℚ) (hx : x ∉ T) (hy : y ∉ T) (hxy : x ≠ y)
    (hf : IsRatCopy Q (insert x T)) (hg : IsRatCopy Q (insert y T)) : IsSymmetric Q := by
  by_cases htwo : Q.card = 2
  · exact symmetric_of_card_two Q htwo
  obtain ⟨a, b, ha, hf⟩ := hf
  obtain ⟨c, d, hc, hg⟩ := hg
  obtain ⟨u, hu, hux⟩ := mem_image.mp (hf ▸ mem_insert_self x T)
  obtain ⟨v, hv, hvy⟩ := mem_image.mp (hg ▸ mem_insert_self y T)
  have hFu : (Q.erase u).image (fun z => a * z + b) = T := by
    rw [image_erase (affine_injective a b ha), ← hf, hux, erase_insert hx]
  have hGv : (Q.erase v).image (fun z => c * z + d) = T := by
    rw [image_erase (affine_injective c d hc), ← hg, hvy, erase_insert hy]
  have huv : u ≠ v := by
    intro huv
    subst v
    have hcard : 2 ≤ (Q.erase u).card := by
      rw [card_erase_of_mem hu]
      omega
    obtain ⟨rfl, rfl⟩ := affine_eq_of_image_eq (Q.erase u) hcard a b c d ha hc
      (hFu.trans hGv.symm)
    exact hxy (hux.symm.trans hvy)
  exact symmetric_of_erasure_images Q T u v hu hv huv a b c d ha hc hFu hGv

/-- **A fast Maker win forces symmetry.** Let $S$ be a finite set of natural numbers with at
least two elements. If Maker, moving first with no numbers claimed, can force a win in the
game on $S$ within $|S|$ selections, then $S$, viewed as a set of rational numbers, is
symmetric.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Lemma 1
(`integers-2026-A40-lem-1`). -/
public theorem isSymmetric_of_makerWinsWithin_card (S : Finset ℕ)
    (hS : 2 ≤ S.card) (h : MakerWinsWithin S S.card ∅ ∅) :
    IsSymmetric (S.image fun s : ℕ => (s : ℚ)) := by
  have hp : S.card - 2 + 2 = S.card := by omega
  obtain ⟨T, x, y, hT, hx, hy, hxy, hf, hg⟩ :=
    two_completions S (S.card - 2) ∅ ∅ (by simpa only [card_empty, zero_add] using hp)
      (by simpa only [hp] using h)
  have hxQ : (x : ℚ) ∉ T.image (fun s : ℕ => (s : ℚ)) := by
    rintro hx'
    obtain ⟨z, hz, hzx⟩ := mem_image.mp hx'
    exact hx ((Nat.cast_injective hzx) ▸ hz)
  have hyQ : (y : ℚ) ∉ T.image (fun s : ℕ => (s : ℚ)) := by
    rintro hy'
    obtain ⟨z, hz, hzy⟩ := mem_image.mp hy'
    exact hy ((Nat.cast_injective hzy) ▸ hz)
  apply symmetric_of_two_copies _ (T.image fun s : ℕ => (s : ℚ))
    (by simpa only [card_image_of_injective _ Nat.cast_injective] using hS)
    x y hxQ hyQ (fun he => hxy (Nat.cast_injective he))
  · simpa only [image_insert] using
      containsCopy_ratCopy S (insert x T) hf (by rw [card_insert_of_notMem hx]; exact hT)
  · simpa only [image_insert] using
      containsCopy_ratCopy S (insert y T) hg (by rw [card_insert_of_notMem hy]; exact hT)

end MetaMathlibExt.FastVanDerWaerdenGame
