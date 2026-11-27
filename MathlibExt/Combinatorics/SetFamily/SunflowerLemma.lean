/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Erdős–Rado sunflower lemma

A *sunflower* (or `Δ`-system) is a family of sets whose pairwise intersections all coincide.
Erdős and Rado proved that a family of more than `w! (p - 1) ^ w` sets, each of size `w`,
contains a sunflower with `p` petals. The lemma is the combinatorial core of Razborov's
approximation method for monotone circuit lower bounds, where it controls the error of
replacing a gate by a small approximator.

The proof is the classical induction on `w`: a maximal pairwise disjoint subfamily either has
`p` members (a sunflower with empty kernel) or covers at most `(p - 1) w` points, one of which
lies in more than `(w - 1)! (p - 1) ^ (w - 1)` members; removing it and applying induction gives
the sunflower.

## References

* P. Erdős and R. Rado, *Intersection theorems for systems of sets*, J. London Math. Soc. 35
  (1960), 85-90.
* R. Alweiss, S. Lovett, K. Wu and J. Zhang, *Improved bounds for the sunflower lemma*,
  Ann. of Math. 194 (2021), arXiv:1908.08483v3, introduction (history and the improved bound).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SetFamily.SunflowerLemma

open Finset

variable {α : Type*} [DecidableEq α]

/-- **Δ-system (sunflower).** A finite family `S` of finite sets is a Δ-system, or sunflower,
when all pairwise intersections of distinct members are equal to one set `Y`, the kernel:
`A ∩ B = Y` for all distinct `A, B ∈ S`. The members are the petals. Erdős and Rado called such
families Δ-systems. (`WantedExt` has a `Set`-valued notion with a prescribed number of petals,
`Set.IsSunflower` in `MathlibExt.Combinatorics.ImprovedBoundsSunflowerLemmaWanted`, which
proved libraries cannot import.) -/
def IsDeltaSystem (S : Finset (Finset α)) : Prop :=
  ∃ Y : Finset α, ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = Y

/-- A family of pairwise disjoint sets is a sunflower with empty kernel. -/
private theorem isDeltaSystem_of_pairwise_disjoint {S : Finset (Finset α)}
    (h : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → Disjoint A B) : IsDeltaSystem S :=
  ⟨∅, fun A hA B hB hAB => disjoint_iff_inter_eq_empty.mp (h A hA B hB hAB)⟩

/-- Adding a common point `x` to every petal of a sunflower gives a sunflower. -/
private theorem isDeltaSystem_image_insert {S : Finset (Finset α)} (x : α) (h : IsDeltaSystem S) :
    IsDeltaSystem (S.image (insert x)) := by
  obtain ⟨Y, hY⟩ := h
  refine ⟨insert x Y, ?_⟩
  simp only [mem_image]
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hAB
  have hne : A ≠ B := fun h => hAB (h ▸ rfl)
  rw [← insert_inter_distrib, hY A hA B hB hne]

/-- **Erdős–Rado sunflower lemma.** Let `F` be a finite family of finite sets, each with exactly
`w` elements. If `F` has more than `w! (p - 1) ^ w` members, then `F` contains a sunflower with
`p` petals: a subfamily `S ⊆ F` with `|S| = p` whose pairwise intersections are all equal
(P. Erdős and R. Rado, *Intersection theorems for systems of sets*, J. London Math. Soc. 35
(1960), 85-90). The bound is sharp up to the factor `w!`: the `(p - 1) ^ w` sets that contain
exactly one element of each of `w` disjoint blocks of size `p - 1` contain no sunflower with `p`
petals. -/
theorem exists_isDeltaSystem (w p : ℕ) (F : Finset (Finset α)) (hF : ∀ A ∈ F, A.card = w)
    (hcard : w.factorial * (p - 1) ^ w < F.card) :
    ∃ S ⊆ F, S.card = p ∧ IsDeltaSystem S := by
  induction w generalizing F with
  | zero =>
    exfalso
    have hsub : F ⊆ {∅} := fun A hA => by
      rw [mem_singleton, ← card_eq_zero]; exact hF A hA
    have := card_le_card hsub
    simp at hcard this
    omega
  | succ w ih =>
    -- A pairwise disjoint subfamily of maximal size.
    set P := F.powerset.filter (fun M => ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B) with hP
    have hPne : P.Nonempty := ⟨∅, by simp [hP]⟩
    obtain ⟨M, hMP, hMmax⟩ := exists_max_image P card hPne
    simp only [hP, mem_filter, mem_powerset] at hMP
    obtain ⟨hMF, hMdisj⟩ := hMP
    by_cases hp : p ≤ M.card
    · obtain ⟨S, hSM, hScard⟩ := exists_subset_card_eq hp
      exact ⟨S, hSM.trans hMF, hScard,
        isDeltaSystem_of_pairwise_disjoint fun A hA B hB hAB => hMdisj A (hSM hA) B (hSM hB) hAB⟩
    push Not at hp
    -- Every member of `F` meets the union `U` of `M`.
    set U := M.biUnion id with hU
    have hmeet : ∀ A ∈ F, ∃ x ∈ U, x ∈ A := by
      intro A hA
      by_cases hAM : A ∈ M
      · have hpos : 0 < A.card := by rw [hF A hA]; omega
        obtain ⟨x, hx⟩ := card_pos.mp hpos
        exact ⟨x, mem_biUnion.mpr ⟨A, hAM, hx⟩, hx⟩
      · by_contra hno
        push Not at hno
        have hins : insert A M ∈ P := by
          simp only [hP, mem_filter, mem_powerset]
          refine ⟨insert_subset hA hMF, ?_⟩
          have hdisj : ∀ B ∈ M, Disjoint A B := fun B hB =>
            disjoint_left.mpr fun x hxA hxB => hno x (mem_biUnion.mpr ⟨B, hB, hxB⟩) hxA
          intro C hC D hD hCD
          rw [mem_insert] at hC hD
          rcases hC with rfl | hC <;> rcases hD with rfl | hD
          · exact absurd rfl hCD
          · exact hdisj D hD
          · exact (hdisj C hC).symm
          · exact hMdisj C hC D hD hCD
        have := hMmax _ hins
        rw [card_insert_of_notMem hAM] at this
        omega
    -- `U` is small.
    have hUcard : U.card ≤ (p - 1) * (w + 1) := by
      calc U.card ≤ ∑ A ∈ M, (id A).card := card_biUnion_le
        _ = M.card * (w + 1) := by
          exact sum_const_nat fun A hA => hF A (hMF hA)
        _ ≤ (p - 1) * (w + 1) := Nat.mul_le_mul_right _ (by omega)
    -- Some point of `U` lies in many members of `F`.
    obtain ⟨x, hxU, hx⟩ : ∃ x ∈ U, w.factorial * (p - 1) ^ w < (F.filter (x ∈ ·)).card := by
      by_contra hno
      push Not at hno
      have hcover : F ⊆ U.biUnion (fun x => F.filter (x ∈ ·)) := fun A hA => by
        obtain ⟨x, hxU, hxA⟩ := hmeet A hA
        exact mem_biUnion.mpr ⟨x, hxU, mem_filter.mpr ⟨hA, hxA⟩⟩
      have h1 : F.card ≤ U.card * (w.factorial * (p - 1) ^ w) :=
        (card_le_card hcover).trans (card_biUnion_le.trans (sum_le_card_nsmul _ _ _ hno))
      have h2 : U.card * (w.factorial * (p - 1) ^ w) ≤
          (w + 1).factorial * (p - 1) ^ (w + 1) := by
        calc U.card * (w.factorial * (p - 1) ^ w)
            ≤ (p - 1) * (w + 1) * (w.factorial * (p - 1) ^ w) := Nat.mul_le_mul_right _ hUcard
          _ = (w + 1).factorial * (p - 1) ^ (w + 1) := by
            rw [Nat.factorial_succ, pow_succ]; ring
      omega
    -- Remove `x` and apply the induction hypothesis.
    set Fx := F.filter (x ∈ ·)
    have hinj : Set.InjOn (fun A : Finset α => A.erase x) Fx := by
      intro A hA B hB hAB
      simp only [Fx, coe_filter, Set.mem_ofPred_eq] at hA hB
      rw [← insert_erase hA.2, ← insert_erase hB.2]
      exact congrArg (insert x) hAB
    have hG : ∀ B ∈ Fx.image (fun A => A.erase x), B.card = w := by
      simp only [mem_image]
      rintro _ ⟨A, hA, rfl⟩
      simp only [Fx, mem_filter] at hA
      rw [card_erase_of_mem hA.2, hF A hA.1]; rfl
    have hGcard : w.factorial * (p - 1) ^ w < (Fx.image (fun A => A.erase x)).card := by
      rwa [card_image_of_injOn hinj]
    obtain ⟨S, hSG, hScard, hSsun⟩ := ih _ hG hGcard
    refine ⟨S.image (insert x), ?_, ?_, isDeltaSystem_image_insert x hSsun⟩
    · intro A hA
      simp only [mem_image] at hA
      obtain ⟨B, hB, rfl⟩ := hA
      have := hSG hB
      simp only [mem_image] at this
      obtain ⟨C, hC, rfl⟩ := this
      simp only [Fx, mem_filter] at hC
      rw [insert_erase hC.2]; exact hC.1
    · rw [card_image_of_injOn, hScard]
      intro B hB C hC hBC
      have hB' := hSG hB
      have hC' := hSG hC
      simp only [mem_image] at hB' hC'
      obtain ⟨B₀, -, rfl⟩ := hB'
      obtain ⟨C₀, -, rfl⟩ := hC'
      have := congrArg (fun D => D.erase x) hBC
      simpa [erase_insert_eq_erase] using this

end MathlibExt.Combinatorics.SetFamily.SunflowerLemma
