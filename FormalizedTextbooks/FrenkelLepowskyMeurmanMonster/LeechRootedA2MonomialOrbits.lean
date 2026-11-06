/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2OddMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2OctadMonomial

/-! All three genuine neighboring short families form root-line monomial orbits. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A common integral target identifies short labels using a root-line-preserving monomial word. -/
theorem leechRootedA2_monomial_common_target (r s : GriessShortIndex)
    (a b : leechIsomSubgroup) (ha : a ∈ golayMonomialSubgroup)
    (hb : b ∈ golayMonomialSubgroup)
    (haroot : leechRootedA2PreservesRootLine a) (hbroot : leechRootedA2PreservesRootLine b)
    (hv : leechIntegralAction a (griessShortLatticeVector r) =
      leechIntegralAction b (griessShortLatticeVector s)) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      leechRootedA2PreservesRootLine e ∧ griessShortPermutation e r = s := by
  let e := b⁻¹ * a
  have hvec : a.val (griessShortVector r) = b.val (griessShortVector s) := by
    have h := congrArg (fun u : leechIntegral => leechCoordinateEmbedding u.val) hv
    rw [leechIntegralAction_embedding, leechIntegralAction_embedding] at h
    exact h
  have he : e.val (griessShortVector r) = griessShortVector s := by
    change b.val.symm (a.val (griessShortVector r)) = _
    rw [hvec, b.val.symm_apply_apply]
  refine ⟨e, golayMonomialSubgroup.mul_mem (golayMonomialSubgroup.inv_mem hb) ha,
    leechRootedA2PreservesRootLine_mul _ _ (leechRootedA2PreservesRootLine_inv b hbroot)
      haroot, ?_⟩
  apply centralizer_shortVector_sign_unique
  rcases griessShortPermutation_vector e r with h | h
  · exact Or.inl (h.symm.trans he)
  · exact Or.inr (by
      rw [he] at h
      have hn := congrArg Neg.neg h
      simpa only [neg_neg] using hn.symm)

/-- All actual pair-family neighbors lie in one root-line-preserving monomial orbit. -/
theorem leechRootedA2Pair_monomial_transitive (a b : Fin 2) (p q : Fin 276)
    (hp : leechRootedA2NeighborPredicate (Sum.inl (a, p)))
    (hq : leechRootedA2NeighborPredicate (Sum.inl (b, q))) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      leechRootedA2PreservesRootLine e ∧
      griessShortPermutation e (Sum.inl (a, p)) = Sum.inl (b, q) := by
  obtain ⟨e, he, heroot, hev⟩ := leechRootedA2Pair_monomial_reduction a p hp
  obtain ⟨f, hf, hfroot, hfv⟩ := leechRootedA2Pair_monomial_reduction b q hq
  exact leechRootedA2_monomial_common_target _ _ e f he hf heroot hfroot
    (Subtype.ext (hev.trans hfv.symm))

/-- All actual odd-family neighbors lie in one root-line-preserving monomial orbit. -/
theorem leechRootedA2Odd_monomial_transitive (d e : Fin 2048) (i j : Fin 24)
    (hi : leechRootedA2NeighborPredicate (Sum.inr (Sum.inr (d, i))))
    (hj : leechRootedA2NeighborPredicate (Sum.inr (Sum.inr (e, j)))) :
    ∃ a : leechIsomSubgroup, a ∈ golayMonomialSubgroup ∧
      leechRootedA2PreservesRootLine a ∧
      griessShortPermutation a (Sum.inr (Sum.inr (d, i))) = Sum.inr (Sum.inr (e, j)) := by
  obtain ⟨a, ha, haroot, hav⟩ := leechRootedA2Odd_monomial_reduction d i hi
  obtain ⟨b, hb, hbroot, hbv⟩ := leechRootedA2Odd_monomial_reduction e j hj
  exact leechRootedA2_monomial_common_target _ _ a b ha hb haroot hbroot
    (Subtype.ext (hav.trans hbv.symm))

/-- The three original catalogue family tags. -/
def leechRootedA2NeighborFamily : GriessShortIndex → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

/-- Within each actual neighbor family, the root-line monomial action is transitive. -/
theorem leechRootedA2Neighbor_same_family_transitive (r s : leechRootedA2NeighborAddress)
    (hf : leechRootedA2NeighborFamily r.val = leechRootedA2NeighborFamily s.val) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      leechRootedA2PreservesRootLine e ∧ griessShortPermutation e r.val = s.val := by
  obtain ⟨r, hr⟩ := r
  obtain ⟨s, hs⟩ := s
  rcases r with ⟨a, p⟩ | (⟨d, i⟩ | ⟨d, i⟩) <;>
    rcases s with ⟨b, q⟩ | (⟨e, j⟩ | ⟨e, j⟩)
  · exact leechRootedA2Pair_monomial_transitive a b p q hr hs
  · norm_num [leechRootedA2NeighborFamily] at hf
  · norm_num [leechRootedA2NeighborFamily] at hf
  · norm_num [leechRootedA2NeighborFamily] at hf
  · exact leechRootedA2Octad_monomial_transitive d e i j hr hs
  · norm_num [leechRootedA2NeighborFamily] at hf
  · norm_num [leechRootedA2NeighborFamily] at hf
  · norm_num [leechRootedA2NeighborFamily] at hf
  · exact leechRootedA2Odd_monomial_transitive d e i j hr hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
