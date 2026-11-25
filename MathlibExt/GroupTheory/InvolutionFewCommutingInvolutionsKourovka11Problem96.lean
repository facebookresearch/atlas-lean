/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# An involution commuting only with itself in an infinite simple group

The image of the quarter-turn matrix in `PSL(2, ℝ)` has order two and commutes with no other
involution. This gives a counterexample to Kourovka Problem 11.96(b).
-/

@[expose] public section

namespace MathlibExt.GroupTheory.InvolutionFewCommutingInvolutionsKourovka11Problem96Wanted

/-- **Involutions commuting with an element.** For an element $t$ of a group $G$, this is the
set of involutions of $G$ that commute with $t$: the elements $s \in G$ of order $2$ with
$st = ts$. -/
def commutingInvolutions {G : Type*} [Group G] (t : G) : Set G :=
  {s | orderOf s = 2 ∧ s * t = t * s}

/-- **Strunkov's question on infinite simple groups (Kourovka 11.96(b)).** This is the statement
that for every natural number $n$, no infinite simple group $G$ contains an involution $t$ that
commutes with at most $n$ involutions of $G$ (counting $t$ itself). -/
def noInfiniteSimpleFewCommutingInvolutions : Prop :=
  ∀ n : ℕ, ∀ (G : Type) [Group G], Infinite G → IsSimpleGroup G →
    ¬ ∃ t : G, orderOf t = 2 ∧ (commutingInvolutions t).encard ≤ n

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

private lemma center_iff {A : SL(2, ℝ)} : A ∈ Subgroup.center SL(2, ℝ) ↔ A = 1 ∨ A = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  simp only [Fintype.card_fin, sq_eq_one_iff]
  have hneg : scalar (Fin 2) (-1 : ℝ) = -1 := by
    rw [map_neg, map_one]
  constructor
  · rintro ⟨r, rfl | rfl, h⟩
    · exact Or.inl (Subtype.ext (by simpa using h.symm))
    · exact Or.inr (Subtype.ext (by simpa only [hneg, coe_neg, coe_one] using h.symm))
  · rintro (rfl | rfl)
    · exact ⟨1, Or.inl rfl, by simp⟩
    · exact ⟨-1, Or.inr rfl, hneg⟩

private lemma projective_eq_iff (A B : SL(2, ℝ)) :
    (A : PSL(2, ℝ)) = B ↔ A = B ∨ A = -B := by
  rw [QuotientGroup.eq_iff_div_mem, center_iff, div_eq_one, div_eq_iff_eq_mul]
  simp

private lemma psl_infinite : Infinite PSL(2, ℝ) := by
  let T := transvection (ι := Fin 2) (F := ℝ) (i := 0) (j := 1) zero_ne_one
  apply Infinite.of_injective (fun r : ℝ ↦ (T r : PSL(2, ℝ)))
  intro r s h
  have hmem := QuotientGroup.eq.mp h
  change (T r)⁻¹ * T s ∈ Subgroup.center SL(2, ℝ) at hmem
  rw [show (T r)⁻¹ = T (-r) from transvection_inv .., ← transvection_add,
    transvection_mem_center_iff] at hmem
  linarith

private noncomputable def quarterTurn : SL(2, ℝ) := ModularGroup.S

private lemma coe_quarterTurn :
    (quarterTurn : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [quarterTurn, coe_matrix_coe]

private lemma sl_eq_iff (A B : SL(2, ℝ)) :
    A = B ↔ (A : Matrix (Fin 2) (Fin 2) ℝ) = B := Subtype.ext_iff

private lemma orderOf_quarterTurn : orderOf (quarterTurn : PSL(2, ℝ)) = 2 := by
  apply orderOf_eq_prime
  · rw [sq]
    change ((quarterTurn * quarterTurn : SL(2, ℝ)) : PSL(2, ℝ)) = (1 : SL(2, ℝ))
    refine (projective_eq_iff ..).2 (Or.inr ?_)
    simp [sl_eq_iff, coe_quarterTurn, ← Matrix.ext_iff, Fin.forall_fin_two]
  · change ¬ ((quarterTurn : PSL(2, ℝ)) = (1 : SL(2, ℝ)))
    rw [projective_eq_iff]
    simp [sl_eq_iff, coe_quarterTurn, ← Matrix.ext_iff, Fin.forall_fin_two]

private lemma eq_quarterTurn_of_commuting {x : PSL(2, ℝ)} (hx : orderOf x = 2)
    (hc : x * (quarterTurn : PSL(2, ℝ)) = quarterTurn * x) :
    x = (quarterTurn : PSL(2, ℝ)) := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  induction A using Matrix.SpecialLinearGroup.fin_two_induction with
  | h a b c d hdet =>
    have ⟨hsq, hne⟩ := orderOf_eq_prime_iff.mp hx
    rw [sq, ← eq_inv_iff_mul_eq_one] at hsq
    rw [← QuotientGroup.mk_inv, projective_eq_iff] at hsq
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, projective_eq_iff] at hc
    change ¬ (_ : PSL(2, ℝ)) = (1 : SL(2, ℝ)) at hne
    rw [projective_eq_iff] at hne ⊢
    -- Commutation in the quotient lifts to commutation or anticommutation in SL.
    have hshape : (b = -c ∧ a = d) ∨ (b = c ∧ d = -a) := by
      simp [sl_eq_iff, coe_quarterTurn] at hc
      tauto
    rcases hshape with ⟨hb, ha⟩ | ⟨hb, hd⟩
    · subst b a
      -- The lift has rows (d, -c) and (c, d). It equals its inverse up to sign.
      have haxis : c = 0 ∨ d = 0 := by
        simp [sl_eq_iff, adjugate_fin_two_of] at hsq
        grind
      rcases haxis with rfl | rfl
      · have hd : d ^ 2 = 1 := by nlinarith
        rcases sq_eq_one_iff.mp hd with rfl | rfl <;>
          simp [sl_eq_iff, ← Matrix.ext_iff, Fin.forall_fin_two] at hne
      · have hc : c ^ 2 = 1 := by nlinarith
        rcases sq_eq_one_iff.mp hc with rfl | rfl <;> simp [sl_eq_iff, coe_quarterTurn]
    · -- An anticommuting lift would have determinant -(a² + c²).
      rw [hb, hd] at hdet
      nlinarith [sq_nonneg a, sq_nonneg c]

/--
**An infinite simple group with an involution commuting with few involutions.** There exist a
natural number $n$ and an infinite simple group $G$ containing an involution $t$ that commutes
with at most $n$ involutions of $G$ (counting $t$ itself). This answers Kourovka Problem 11.96(b)
in the negative.

For example, $\mathrm{PSL}_2(\mathbb{R})$ is an infinite simple group that contains an involution
but no Klein four-subgroup, so each of its involutions commutes with no involution other than
itself ($n = 1$); the Kourovka Notebook (21st issue) marks 11.96(b) solved, "No", citing Skresanov.

Source: E. I. Khukhro
and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Problem 11.96 (S. P. Strunkov); resolution: S. V. Skresanov, J. Group
Theory 27, no. 6 (2024), 1197-1202, the Kourovka Notebook (21st issue) marks 11.96 solved: (a) yes
(mod CFSG), and a locally finite group with such an involution is finite of `n`-bounded order; (b)
no, `PSL_2(ℝ)` is an infinite simple group with an involution and no Klein four-subgroup,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem noInfiniteSimpleFewCommutingInvolutions_refuted :
    ¬ noInfiniteSimpleFewCommutingInvolutions := by
  intro h
  have hs : IsSimpleGroup PSL(2, ℝ) :=
    ProjectiveSpecialLinearGroup.rank_two_simple' ⟨2, by norm_num, by norm_num⟩
  apply h 1 PSL(2, ℝ) psl_infinite hs
  refine ⟨quarterTurn, orderOf_quarterTurn, ?_⟩
  have hsub : commutingInvolutions (quarterTurn : PSL(2, ℝ)) ⊆ {(quarterTurn : PSL(2, ℝ))} :=
    fun _ hx ↦ eq_quarterTurn_of_commuting hx.1 hx.2
  simpa using Set.encard_mono hsub

end MathlibExt.GroupTheory.InvolutionFewCommutingInvolutionsKourovka11Problem96Wanted
