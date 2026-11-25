/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SylverCoinage
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.Ideal.NatInt

/-!
# Enders in Sylver Coinage

A Sylver Coinage position is winning if its greatest legal move exceeds one and is its only end.
The proof uses strategy stealing and determinacy for finite sets of legal moves.
-/

namespace MetaMathlibExt

namespace isSylverNPosition_of_ender

private theorem legalMoves_insert_subset (M : Set ℕ) (x : ℕ) :
    sylverLegalMoves (insert x M) ⊆ sylverLegalMoves M :=
  fun _ hy hmem => hy (AddSubmonoid.closure_mono (Set.subset_insert x M) hmem)

-- Equal generated submonoids give the same legal moves before and after a common move.
-- Ruling out a win on one side gives a losing position on the other by induction on the gap count.
private theorem p_of_not_n {M M' : Set ℕ} (hclosure : AddSubmonoid.closure M =
    AddSubmonoid.closure M') (hfin : (sylverLegalMoves M).Finite)
    (hn : ¬ IsSylverNPosition M') : IsSylverPPosition M := by
  classical
  have hlegal : sylverLegalMoves M = sylverLegalMoves M' := by simp [sylverLegalMoves, hclosure]
  have h1 : 1 ∉ M := fun h => hn (.one_mem (Nat.one_mem_closure_iff.mp
    (hclosure ▸ AddSubmonoid.subset_closure h)))
  refine .intro h1 fun x hx => ?_
  have hx' : x ∈ sylverLegalMoves M' := hlegal ▸ hx
  have hsub : sylverLegalMoves (insert x M') ⊂ sylverLegalMoves M := by
    rw [hlegal]
    exact Set.ssubset_iff_exists.mpr
      ⟨legalMoves_insert_subset M' x, x, hx',
        fun h => h (AddSubmonoid.subset_closure (Set.mem_insert x M'))⟩
  by_contra hnext
  apply hn (.move hx' ?_)
  exact p_of_not_n (by simp only [Set.insert_eq, AddSubmonoid.closure_union, hclosure])
    (hfin.subset hsub.subset) hnext
termination_by (sylverLegalMoves M).ncard
decreasing_by exact Set.ncard_lt_ncard hsub hfin

end isSylverNPosition_of_ender

open isSylverNPosition_of_ender in
/-- **Enders with largest legal move above 1 are N-positions.** Let $M$ be a position of Sylver
Coinage whose set of legal moves $L(M)$ has a greatest element $F$ with $F > 1$. If every end of
$M$ equals $F$ (that is, $M$ is an ender), then $M$ is an N-position.

Source: Morgan Boyers, Natalie Burton, Jeff Rushall, James Warner and Tara Zurick, *On Winning
Strategies in Sylver Coinage When 4 Has Been Chosen*, INTEGERS 24 (2024), Article G2,
Proposition 2 (`integers-2024-G2-prop-2`). -/
public theorem isSylverNPosition_of_ender {M : Set ℕ} {F : ℕ}
    (hF : IsGreatest (sylverLegalMoves M) F) (hender : ∀ x, IsSylverEnd M x → x = F)
    (hF1 : 1 < F) :
    IsSylverNPosition M := by
  by_contra hn
  apply hn (.move hF.1 (.intro ?_ ?_))
  · simp only [Set.mem_insert_iff, not_or]
    exact ⟨hF1.ne, fun h => hn (.one_mem h)⟩
  intro x hx
  have hxM := legalMoves_insert_subset M F hx
  have hFnot : F ∉ sylverLegalMoves (insert F M) :=
    fun h => h (AddSubmonoid.subset_closure (Set.mem_insert F M))
  have hxF := lt_of_le_of_ne (hF.2 hxM) (ne_of_mem_of_not_mem hx hFnot)
  have hgen : F ∈ AddSubmonoid.closure (insert x M) := by
    by_contra hgap
    exact sylverEnder_eliminates_largest_move hF hender hF1 x hxM hxF hgap
  -- A winning reply to F would also win if played directly, since it generates F.
  by_contra hnext
  apply hn (.move hxM ?_)
  have hfin : (sylverLegalMoves M).Finite := (Set.finite_le_nat F).subset hF.2
  refine p_of_not_n ?_ (hfin.subset (legalMoves_insert_subset M x)) hnext
  rw [Set.insert_comm x F, Set.insert_eq F, AddSubmonoid.closure_union,
    sup_eq_right.mpr ((AddSubmonoid.closure_singleton_le_iff_mem ..).mpr hgen)]

end MetaMathlibExt
