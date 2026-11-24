/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleRetractionCombinatorics

@[expose] public section

set_option autoImplicit false

open CategoryTheory Simplicial

namespace AlgebraicTopology.EilenbergZilber.Shuffle

open AlgebraicTopology.AlexanderWhitney

theorem eq_blockShuffle_of_left_mono (p q : ℕ) (s : Shuffle p q)
    [Mono (frontInclusion p q (p + q) rfl ≫ s.leftHom)] :
    s = blockShuffle p q := by
  have hcomp : frontInclusion p q (p + q) rfl ≫ s.leftHom = 𝟙 ⦋p⦌ :=
    SimplexCategory.eq_id_of_mono _
  have hcount := congrArg (fun f => (f.toOrderHom (Fin.last p)).val) hcomp
  simp only [SimplexCategory.comp_toOrderHom,
    SimplexCategory.id_toOrderHom] at hcount
  have hfront :
      ((frontInclusion p q (p + q) rfl).toOrderHom (Fin.last p)).val = p := by
    rw [frontInclusion_toOrderHom, Fin.val_last]
  have hleft := leftHom_val_eq_card_filter_leftPositions s
    ((frontInclusion p q (p + q) rfl).toOrderHom (Fin.last p))
  rw [hfront] at hleft
  have hfilter_card :
      (s.leftPositions.val.filter (fun x => x.val < p)).card = p :=
    hleft.symm.trans hcount
  have htotal := s.leftPositions.property
  have hcards : (s.leftPositions.val.filter (fun x => x.val < p)).card
      = s.leftPositions.val.card := by
    rw [hfilter_card, htotal]
  have hle := le_of_eq hcards.symm
  have hfilter : s.leftPositions.val.filter (fun x => x.val < p)
      = s.leftPositions.val := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hle
  have hbound (i : Fin p) : (s.perm (Fin.castAdd q i)).val < p := by
    have hmem : s.perm (Fin.castAdd q i) ∈ s.leftPositions :=
      (mem_leftPositions_iff s _).mpr ⟨i, rfl⟩
    have hval : s.perm (Fin.castAdd q i) ∈ s.leftPositions.val := by
      change s.perm (Fin.castAdd q i) ∈ s.leftPositions
      exact hmem
    have hmemF : s.perm (Fin.castAdd q i) ∈
        s.leftPositions.val.filter (fun x => x.val < p) := by
      rw [hfilter]
      exact hval
    exact (Finset.mem_filter.mp hmemF).2
  let f : Fin p → Fin p := fun i =>
    ⟨(s.perm (Fin.castAdd q i)).val, hbound i⟩
  have hf : StrictMono f := by
    intro i j hij
    exact s.isShuffle.1 hij
  have hf_eq : f = id := by
    funext i
    apply le_antisymm
    · simpa using (((Fin.rev_strictAnti.comp_strictMono hf).comp
        Fin.rev_strictAnti).id_le (Fin.rev i))
    · exact hf.id_le i
  have hperm (i : Fin p) : s.perm (Fin.castAdd q i) = Fin.castAdd q i := by
    have hi : (f i).val = i.val := congrArg Fin.val (congrFun hf_eq i)
    exact Fin.ext hi
  apply (equivLeftPositions (p := p) (q := q)).injective
  apply Subtype.ext
  ext k
  change (k ∈ s.leftPositions ↔ k ∈ (blockShuffle p q).leftPositions)
  simp only [mem_leftPositions_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp [blockShuffle, hperm]⟩
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simpa [blockShuffle, hperm] using hi
end AlgebraicTopology.EilenbergZilber.Shuffle
