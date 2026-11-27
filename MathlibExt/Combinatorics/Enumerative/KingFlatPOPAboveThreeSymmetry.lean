/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
public import MathlibExt.Combinatorics.Enumerative.KingFlatPOPSymmetry
import all MathlibExt.Combinatorics.Enumerative.KingFlatPOPSymmetry
import all MathlibExt.Combinatorics.Enumerative.KingPermutationPatterns

/-!
# The king generating function avoiding $Q_3$

Position reversal takes $P_2$-avoiding king permutations to $P_3$-avoiding ones. It swaps
ascents and descents and interchanges the two maximum statistics. Value complement applies
the ascent/descent swap again and turns the maxima into minima.

## References

* Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
  INTEGERS 26 (2026), Article A59, pp. 1–18, Corollary 6 and the reversal and complement
  arguments of Corollaries 4 and 5 (p. 15).
* Sergey Kitaev, *Partially ordered generalized patterns*, Discrete Mathematics 298 (2005),
  pp. 212–229, Section 1, for the partially ordered pattern framework cited in Section 1.1.
* John Riordan, *A recurrence for permutations without rising or falling successions*,
  The Annals of Mathematical Statistics 36 (1965), pp. 708–710. Li and Kitaev cite this early
  enumeration of king permutations in Section 1.3; the symmetry does not use the recurrence.
-/

namespace MetaMathlibExt

private theorem reversePositions_involutive {n : ℕ} :
    Function.Involutive (fun σ : Equiv.Perm (Fin n) => Fin.revPerm.trans σ) := by
  intro σ
  ext i
  simp

private theorem containsFlatPOPBelow_of_reversePositions {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {j : Fin 4} (h : ContainsFlatPOPBelow σ j) :
    ContainsFlatPOPBelow (Fin.revPerm.trans σ) j.rev := by
  obtain ⟨f, hf⟩ := h
  let g : Fin 4 ↪o Fin n := OrderEmbedding.ofStrictMono (fun i => (f i.rev).rev)
    (fun _ _ hij => Fin.rev_lt_rev.mpr (f.strictMono (Fin.rev_lt_rev.mpr hij)))
  refine ⟨g, fun m hm => ?_⟩
  change σ ((f j.rev.rev).rev.rev) < σ ((f m.rev).rev.rev)
  have hmr : m.rev ≠ j := by
    intro he
    apply hm
    simpa only [Fin.rev_rev] using congrArg Fin.rev he
  simpa only [Fin.rev_rev] using hf m.rev hmr

private theorem containsFlatPOPBelow_reversePositions {n : ℕ} (σ : Equiv.Perm (Fin n))
    (j : Fin 4) : ContainsFlatPOPBelow (Fin.revPerm.trans σ) j.rev ↔ ContainsFlatPOPBelow σ j := by
  refine ⟨fun h => ?_, containsFlatPOPBelow_of_reversePositions⟩
  simpa only [reversePositions_involutive σ, Fin.rev_rev] using
    containsFlatPOPBelow_of_reversePositions h

private theorem permAscentCount_reversePositions {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permAscentCount (Fin.revPerm.trans σ) = permDescentCount σ := by
  -- Reverse the two endpoints of an edge, then use the new left endpoint as its index.
  let edge (i : Fin n) : Fin n := ⟨(i.rev : ℕ) - 1, (Nat.sub_le ..).trans_lt i.rev.isLt⟩
  have edge_eq {i j : Fin n} (h : (j : ℕ) = i + 1) : edge i = j.rev := by
    apply Fin.ext
    change (i.rev : ℕ) - 1 = j.rev
    rw [rev_adjacent h, Nat.add_sub_cancel]
  have edge_inv {i j : Fin n} (h : (j : ℕ) = i + 1) : edge (edge i) = i := by
    rw [edge_eq h, edge_eq (rev_adjacent h), Fin.rev_rev]
  unfold permAscentCount permDescentCount
  refine Finset.card_nbij' edge edge ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.trans_apply, Fin.revPerm_apply] at hi ⊢
    obtain ⟨j, hj, hlt⟩ := hi
    exact ⟨i.rev, by rw [edge_eq hj]; exact rev_adjacent hj, by simpa only [edge_eq hj] using hlt⟩
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.trans_apply, Fin.revPerm_apply] at hi ⊢
    obtain ⟨j, hj, hlt⟩ := hi
    exact ⟨i.rev, by rw [edge_eq hj]; exact rev_adjacent hj,
      by simpa only [edge_eq hj, Fin.rev_rev] using hlt⟩
  · intro i hi
    obtain ⟨j, hj, _⟩ := (Finset.mem_filter.mp hi).2
    exact edge_inv hj
  · intro i hi
    obtain ⟨j, hj, _⟩ := (Finset.mem_filter.mp hi).2
    exact edge_inv hj

private theorem permLeftToRightMaxCount_reversePositions {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permLeftToRightMaxCount (Fin.revPerm.trans σ) = permRightToLeftMaxCount σ := by
  unfold permLeftToRightMaxCount permRightToLeftMaxCount
  apply Finset.card_equiv Fin.revPerm
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.trans_apply, Fin.revPerm_apply]
  constructor
  · intro h j hj
    have hj' : j.rev < i := by simpa only [Fin.rev_rev] using Fin.rev_lt_rev.mpr hj
    simpa only [Fin.rev_rev] using h j.rev hj'
  · intro h j hj
    exact h j.rev (Fin.rev_lt_rev.mpr hj)

private theorem belowGF_two_of_reversePositions :
    kingFlatPOPBelowGF 2 =
      PowerSeries.map (MvPolynomial.rename
          ⇑(Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4))).toRingHom
        (kingFlatPOPBelowGF 1) := by
  classical
  apply PowerSeries.ext
  intro n
  simp only [kingFlatPOPBelowGF, PowerSeries.coeff_mk, PowerSeries.coeff_map, map_sum]
  symm
  let e : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
    reversePositions_involutive.toPerm _
  have hre (σ : Equiv.Perm (Fin n)) : e σ = Fin.revPerm.trans σ := rfl
  apply Finset.sum_equiv e
  · intro σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hre]
    have hk : IsKingPerm (Fin.revPerm.trans σ) ↔ IsKingPerm σ :=
      ⟨fun h => reversePositions_involutive σ ▸ king_reverse h, king_reverse⟩
    have hp := containsFlatPOPBelow_reversePositions σ 1
    change ContainsFlatPOPBelow (Fin.revPerm.trans σ) 2 ↔ ContainsFlatPOPBelow σ 1 at hp
    rw [hk, hp]
  · intro σ _
    have hd : permDescentCount (Fin.revPerm.trans σ) = permAscentCount σ := by
      simpa only [reversePositions_involutive σ] using
        (permAscentCount_reversePositions (Fin.revPerm.trans σ)).symm
    have hm : permRightToLeftMaxCount (Fin.revPerm.trans σ) = permLeftToRightMaxCount σ := by
      simpa only [reversePositions_involutive σ] using
        (permLeftToRightMaxCount_reversePositions (Fin.revPerm.trans σ)).symm
    let r : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
    have hX (i : Fin 4) : (MvPolynomial.rename ⇑r).toRingHom (MvPolynomial.X i) =
        (MvPolynomial.X (r i) : MvPolynomial (Fin 4) ℤ) := MvPolynomial.rename_X _ _
    change (MvPolynomial.rename ⇑r).toRingHom _ = _
    simp only [map_mul, map_pow]
    rw [hX 0, hX 1, hX 2, hX 3]
    simp only [show r 0 = 1 by decide, show r 1 = 0 by decide, show r 2 = 3 by decide,
      show r 3 = 2 by decide, hre, permAscentCount_reversePositions,
      hd, permLeftToRightMaxCount_reversePositions, hm]
    ac_rfl

/-- **The king generating function avoiding $Q_3$.** Let $A_{P_2}(x, p, q, u, v)$ be the
generating function of king permutations avoiding the flat pattern $P_2$ (label $2$ below labels
$1, 3, 4$), where $x, p, q, u, v$ mark length, ascents, descents, left-to-right maxima and
right-to-left maxima, and let $\bar A_{Q_3}(x, p, q, s, t)$ be the generating function of king
permutations avoiding the flat pattern $Q_3$ (label $3$ above labels $1, 2, 4$), where
$x, p, q, s, t$ mark length, ascents, descents, left-to-right minima and right-to-left minima.
Then $\bar A_{Q_3}(x, p, q, s, t) = A_{P_2}(x, p, q, t, s)$: the coefficient of each power of $x$
in $\bar A_{Q_3}$ is obtained from the corresponding coefficient of $A_{P_2}$ by exchanging the
last two variables.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Corollary 6. -/
public theorem kingFlatPOPAboveGF_two_eq_rename :
    kingFlatPOPAboveGF 2 =
      PowerSeries.map (MvPolynomial.rename ⇑(Equiv.swap (2 : Fin 4) 3)).toRingHom
        (kingFlatPOPBelowGF 1) := by
  rw [kingFlatPOPAboveGF_eq_rename 2, belowGF_two_of_reversePositions]
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    MvPolynomial.rename_rename]
  have h : (⇑(Equiv.swap (0 : Fin 4) 1)) ∘
      (⇑(Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4))) = ⇑(Equiv.swap (2 : Fin 4) 3) := by
    funext i
    fin_cases i <;> decide
  rw [h]

end MetaMathlibExt
