/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Interval.Finset.Basic
import MathlibExt.Combinatorics.RamseyWitnessTensorSquare

/-!
# Ultrafilter witnesses of the pairwise sum family

An ultrafilter witnesses the pairwise sum family exactly when it is the common image of a
Ramsey witness under the two projections and addition.
-/

open Filter Set

namespace MetaMathlibExt

/-- **PR-witnesses of the pairwise sum family.** An ultrafilter $W$ on
$\mathbb{N} \times \mathbb{N}$, where $\mathbb{N} = \{0, 1, 2, \dots\}$, is a Ramsey's witness
when every $X \in W$ contains $\{(h, h') \in H \times H : h < h'\}$ for some infinite
$H \subseteq \mathbb{N}$. For an ultrafilter $U$ on $\mathbb{N}$ the following are equivalent:
(1) every $A \in U$ contains an infinite set $B$ together with all sums $b + b'$ of distinct
$b, b' \in B$ ($U$ is a PR-witness of the pairwise sum family); (2) there is a Ramsey's witness
$W$ on $\mathbb{N} \times \mathbb{N}$ whose images under the projections $(a, b) \mapsto a$ and
$(a, b) \mapsto b$ and under the sum map $(a, b) \mapsto a + b$ all equal $U$.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Proposition 3.6 (`integers-2025-A105-prop-3-6`). -/
public theorem pairwiseSums_witness_iff_exists_ramseyWitness (U : Ultrafilter ℕ) :
    (∀ A ∈ U, ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ ∀ b ∈ B, ∀ b' ∈ B, b < b' → b + b' ∈ A) ↔
      ∃ W : Ultrafilter (ℕ × ℕ),
        (∀ X ∈ W, ∃ H : Set ℕ, H.Infinite ∧ ∀ h ∈ H, ∀ h' ∈ H, h < h' → (h, h') ∈ X) ∧
        W.map Prod.fst = U ∧ W.map Prod.snd = U ∧ W.map (fun p => p.1 + p.2) = U := by
  let pairsIn (A : Set ℕ) := {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 ∈ A}
  constructor
  · intro hU
    let squares := {W : Ultrafilter (ℕ × ℕ) | ∃ V : Ultrafilter ℕ, (V : Filter ℕ) ≤ cofinite ∧
      W = V.bind fun n => V.map (Prod.mk n)}
    let C (A : U.sets) := {W : Ultrafilter (ℕ × ℕ) | pairsIn A.1 ∈ W}
    have hfinite (t : Finset U.sets) : (closure squares ∩ ⋂ i ∈ t, C i).Nonempty := by
      let A := ⋂ i ∈ t, (i.1 : Set ℕ)
      have hA : A ∈ U := (biInter_finset_mem t).2 fun i _ => i.2
      obtain ⟨B, hB, hBA, hsum⟩ := hU A hA
      -- A free ultrafilter on B has a tensor square concentrating on increasing pairs from B.
      have := cofinite_inf_principal_neBot_iff.2 hB
      let V := Ultrafilter.of (cofinite ⊓ 𝓟 B)
      have hV : (V : Filter ℕ) ≤ cofinite ⊓ 𝓟 B := Ultrafilter.of_le _
      have hBV : B ∈ V := hV (mem_inf_of_right (mem_principal_self B))
      refine ⟨V.bind fun n => V.map (Prod.mk n), subset_closure ⟨V, hV.trans inf_le_left, rfl⟩,
        mem_iInter₂.mpr fun i hi => ?_⟩
      have hAi : A ⊆ i.1 := iInter₂_subset i hi
      apply mem_of_superset hBV
      intro b hb
      have htail : Ioi b ∈ V := hV (mem_inf_of_left (Nat.cofinite_eq_atTop ▸ Ioi_mem_atTop b))
      exact mem_of_superset (inter_mem hBV htail) fun c hc =>
        ⟨hAi (hBA hb), hAi (hBA hc.1), hAi (hsum b hb c hc.1 hc.2)⟩
    -- Compactness gives a Ramsey witness meeting the constraints for every member of U.
    obtain ⟨W, hW, hC⟩ := isClosed_closure.isCompact.inter_iInter_nonempty C
      (fun A => ultrafilter_isClosed_basic _) hfinite
    have hpairs (A : Set ℕ) (hA : A ∈ U) : pairsIn A ∈ W := mem_iInter.mp hC ⟨A, hA⟩
    have map_eq (f : ℕ × ℕ → ℕ) (hf : ∀ A, pairsIn A ⊆ f ⁻¹' A) : W.map f = U :=
      Ultrafilter.eq_of_le fun A hA =>
        Ultrafilter.mem_map.mpr (mem_of_superset (hpairs A hA) (hf A))
    exact ⟨W, (ramseyWitness_iff_mem_closure_tensor_squares W).2 hW,
      map_eq Prod.fst fun _ _ hp => hp.1, map_eq Prod.snd fun _ _ hp => hp.2.1,
      map_eq (fun p => p.1 + p.2) fun _ _ hp => hp.2.2⟩
  · rintro ⟨W, hW, hfst, hsnd, hsum⟩ A hA
    have h₁ : Prod.fst ⁻¹' A ∈ W := Ultrafilter.mem_map.mp (hfst ▸ hA)
    have h₂ : Prod.snd ⁻¹' A ∈ W := Ultrafilter.mem_map.mp (hsnd ▸ hA)
    have h₃ : (fun p : ℕ × ℕ => p.1 + p.2) ⁻¹' A ∈ W := Ultrafilter.mem_map.mp (hsum ▸ hA)
    obtain ⟨H, hH, hpair⟩ := hW (pairsIn A) (inter_mem h₁ (inter_mem h₂ h₃))
    refine ⟨H, hH, ?_, fun b hb c hc hbc => (hpair b hb c hc hbc).2.2⟩
    intro b hb
    obtain ⟨c, hc, hbc⟩ := hH.exists_gt b
    exact (hpair b hb c hc hbc).1

end MetaMathlibExt
