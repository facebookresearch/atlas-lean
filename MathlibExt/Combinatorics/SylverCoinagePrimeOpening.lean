/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SylverCoinage
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.FrobeniusNumber
import MathlibExt.NumberTheory.TwoGeneratedNumericalSemigroup

/-!
# Prime openings in Sylver Coinage

Hutchings' theorem says that opening with any prime greater than three wins. After a reply
other than one, the two generators are coprime. Adding any gap to them generates their
Frobenius number. If playing the Frobenius number gives the opponent a winning reply, the
opener can play that reply directly.
-/

namespace MetaMathlibExt

namespace isSylverPPosition_prime_opening

private theorem legalMoves_insert_ssubset {x : ℕ} {M : Set ℕ} (hx : x ∈ sylverLegalMoves M) :
    sylverLegalMoves (insert x M) ⊂ sylverLegalMoves M := by
  apply Set.ssubset_iff_exists.mpr
  exact ⟨fun _ hy hmem => hy (AddSubmonoid.closure_mono (Set.subset_insert x M) hmem),
    x, hx, fun h => h (AddSubmonoid.subset_closure (Set.mem_insert x M))⟩

-- Finite-game determinacy, allowing two generating sets for the same position.
-- A move decreases the number of gaps, and gives the same new closure on both sides.
private theorem p_of_not_n {M M' : Set ℕ} (heq : AddSubmonoid.closure M = AddSubmonoid.closure M')
    (hfin : (sylverLegalMoves M).Finite) (hn : ¬ IsSylverNPosition M') : IsSylverPPosition M := by
  classical
  have hlegal : sylverLegalMoves M = sylverLegalMoves M' := by simp [sylverLegalMoves, heq]
  have h1 : 1 ∉ M := by
    intro h
    apply hn (.one_mem ?_)
    rwa [← Nat.one_mem_closure_iff, ← heq, Nat.one_mem_closure_iff]
  refine .intro h1 fun x hx => ?_
  have hx' : x ∈ sylverLegalMoves M' := hlegal ▸ hx
  have hsub : sylverLegalMoves (insert x M') ⊂ sylverLegalMoves M := by
    rw [hlegal]
    exact legalMoves_insert_ssubset hx'
  by_contra hnext
  apply hn (.move hx' ?_)
  exact p_of_not_n (by simp only [Set.insert_eq, AddSubmonoid.closure_union, heq])
    (hfin.subset hsub.subset) hnext
termination_by (sylverLegalMoves M).ncard
decreasing_by exact Set.ncard_lt_ncard hsub hfin

end isSylverPPosition_prime_opening

open isSylverPPosition_prime_opening in
/-- **Hutchings' theorem.** For every prime $p > 3$, the position $\{p\}$ of Sylver Coinage is a
P-position: a first player who opens with $p$ wins.

Source: Morgan Boyers, Natalie Burton, Jeff Rushall, James Warner and Tara Zurick, *On Winning
Strategies in Sylver Coinage When 4 Has Been Chosen*, INTEGERS 24 (2024), Article G2,
Theorem 1 (`integers-2024-G2-thm-1`). -/
public theorem isSylverPPosition_prime_opening {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    IsSylverPPosition {p} := by
  classical
  refine .intro (by simpa using (show 1 ≠ p by omega)) fun q hq => ?_
  by_cases h1 : q = 1
  · exact .one_mem (by simp [h1])
  have hq0 : q ≠ 0 := fun h => zero_notMem_sylverLegalMoves _ (h ▸ hq)
  have hq2 : 2 ≤ q := by omega
  have hcop : p.Coprime q := hp.coprime_iff_not_dvd.mpr fun ⟨k, hk⟩ =>
    hq (AddSubmonoid.mem_closure_singleton.mpr
      ⟨k, by simpa [smul_eq_mul, Nat.mul_comm] using hk.symm⟩)
  let F := q * p - q - p
  have hF : FrobeniusNumber F {q, p} := frobeniusNumber_pair hcop.symm hq2 hp.one_lt
  have hF1 : 1 < F := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hq2
    dsimp [F]
    rw [Nat.add_mul]
    have := Nat.le_mul_of_pos_right k hp.pos
    omega
  have hfin : (sylverLegalMoves {q, p}).Finite := (Set.finite_le_nat F).subset hF.2
  -- Try the largest gap F. Any winning reply x to F would already win before F was played.
  by_contra hn
  apply hn (.move hF.1 (.intro (by simp; omega) ?_))
  intro x hx
  have hx₀ := (legalMoves_insert_ssubset (M := {q, p}) hF.1).subset hx
  have hxF := hF.2 hx₀
  have hreflect : F - x ∈ AddSubmonoid.closure ({q, p} : Set ℕ) := by
    by_contra hgap
    exact hx₀ ((numericalSemigroup_two_generated_symmetric hF.1
      (frobeniusNumber_iff.mp hF).2 x hxF).mpr hgap)
  have hgen : F ∈ AddSubmonoid.closure (insert x ({q, p} : Set ℕ)) := by
    simpa only [Nat.add_sub_of_le hxF] using
      add_mem (AddSubmonoid.subset_closure (Set.mem_insert x ({q, p} : Set ℕ)))
        (AddSubmonoid.closure_mono (Set.subset_insert x _) hreflect)
  by_contra hnext
  apply hn (.move hx₀ ?_)
  apply p_of_not_n _ (hfin.subset (legalMoves_insert_ssubset hx₀).subset) hnext
  rw [Set.insert_comm x F, Set.insert_eq F, AddSubmonoid.closure_union, sup_eq_right.mpr
    ((AddSubmonoid.closure_singleton_le_iff_mem ..).mpr hgen)]

end MetaMathlibExt
