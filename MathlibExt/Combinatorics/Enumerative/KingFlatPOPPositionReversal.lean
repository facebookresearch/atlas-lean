/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.KingFlatPOPSymmetry
import MathlibExt.Combinatorics.Enumerative.KingPermutationPatterns
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Position reversal for flat patterns in king permutations

Reversing positions preserves the king condition and reflects the bottom label of a
flat pattern. It swaps ascents with descents and left-to-right with right-to-left maxima.

## References

* Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
  INTEGERS 26 (2026), Article A59, pp. 1–18, Corollary 4 (p. 15).
* John Riordan, *A Recurrence for Permutations without Rising or Falling Successions*,
  The Annals of Mathematical Statistics 36 (1965), no. 2, pp. 708–710. This is the
  original study of king permutations credited by Li and Kitaev in Section 1.3.
-/

namespace MetaMathlibExt

open Finset

private def positionReverse {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  Fin.revPerm.trans σ

private theorem positionReverse_involutive {n : ℕ} :
    Function.Involutive (positionReverse (n := n)) := by
  intro σ
  ext i
  simp [positionReverse]

private theorem isKingPerm_positionReverse {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    IsKingPerm (positionReverse σ) ↔ IsKingPerm σ := by
  rw [isKingPerm_iff, isKingPerm_iff]
  constructor
  · intro h
    have hh := king_reverse h
    rwa [show Fin.revPerm.trans (positionReverse σ) = σ from positionReverse_involutive σ] at hh
  · exact king_reverse

private theorem containsFlatPOPBelow_positionReverse {n : ℕ} (σ : Equiv.Perm (Fin n))
    (j : Fin 4) : ContainsFlatPOPBelow (positionReverse σ) j ↔ ContainsFlatPOPBelow σ j.rev := by
  have reflect (τ : Equiv.Perm (Fin n)) (k : Fin 4) :
      ContainsFlatPOPBelow (positionReverse τ) k → ContainsFlatPOPBelow τ k.rev := by
    rw [containsFlatPOPBelow_iff, containsFlatPOPBelow_iff]
    rintro ⟨f, hf⟩
    refine ⟨OrderEmbedding.ofStrictMono (fun i => (f i.rev).rev) (fun i l hil =>
      Fin.rev_lt_rev.mpr (f.strictMono (Fin.rev_lt_rev.mpr hil))), ?_⟩
    intro m hm
    have hmk : m.rev ≠ k := by
      intro e
      exact hm (by simpa only [Fin.rev_rev] using congrArg Fin.rev e)
    change τ (f k.rev.rev).rev < τ (f m.rev).rev
    rw [Fin.rev_rev]
    exact hf m.rev hmk
  refine ⟨reflect σ j, ?_⟩
  intro h
  have h' : ContainsFlatPOPBelow (positionReverse (positionReverse σ)) j.rev := by
    rwa [positionReverse_involutive σ]
  simpa only [Fin.rev_rev] using reflect (positionReverse σ) j.rev h'

private theorem permAscentCount_positionReverse {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permAscentCount (positionReverse σ) = permDescentCount σ :=
  permAscentCount_rev σ

private theorem permDescentCount_positionReverse {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permDescentCount (positionReverse σ) = permAscentCount σ := by
  rw [← permAscentCount_positionReverse (positionReverse σ), positionReverse_involutive σ]

private theorem permLeftToRightMaxCount_positionReverse {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permLeftToRightMaxCount (positionReverse σ) = permRightToLeftMaxCount σ :=
  permLeftToRightMaxCount_rev σ

private theorem permRightToLeftMaxCount_positionReverse {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permRightToLeftMaxCount (positionReverse σ) = permLeftToRightMaxCount σ := by
  rw [← permLeftToRightMaxCount_positionReverse (positionReverse σ), positionReverse_involutive σ]

/-- **The generating functions for $P_3$ and $P_2$ differ by a change of variables.** For $k = 2$
and $k = 3$ let $P_k$ be the flat partially ordered pattern of length $4$ whose $k$-th element lies
below each of the other three, and let $A_{P_k}(x; p, q, u, v)$ be the generating function of king
permutations avoiding $P_k$, in which $x$ marks length and $p$, $q$, $u$, $v$ mark ascents,
descents, left-to-right maxima and right-to-left maxima. Then
$A_{P_3}(x; p, q, u, v) = A_{P_2}(x; q, p, v, u)$: the series $A_{P_3}$ is obtained from
$A_{P_2}$ by exchanging $p$ with $q$ and $u$ with $v$ in every coefficient.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Corollary 4. -/
public theorem kingFlatPOPBelowGF_two_eq_rename :
    kingFlatPOPBelowGF 2 =
      PowerSeries.map (MvPolynomial.rename
          ⇑(Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4))).toRingHom
        (kingFlatPOPBelowGF 1) := by
  classical
  apply PowerSeries.ext
  intro n
  simp only [coeff_kingFlatPOPBelowGF, PowerSeries.coeff_map, map_sum]
  symm
  have hrev : (2 : Fin 4).rev = 1 := by decide
  refine sum_bij (fun σ _ => positionReverse σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simpa only [mem_filter, mem_univ, true_and, isKingPerm_positionReverse,
      containsFlatPOPBelow_positionReverse, hrev] using hσ
  · intro σ _ τ _ h
    exact positionReverse_involutive.injective h
  · intro τ hτ
    refine ⟨positionReverse τ, ?_, positionReverse_involutive τ⟩
    simp only [mem_filter, mem_univ, true_and] at hτ ⊢
    rw [← isKingPerm_positionReverse (positionReverse τ), ← hrev,
      ← containsFlatPOPBelow_positionReverse, positionReverse_involutive τ]
    exact hτ
  · intro σ _
    set e : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
    have h₀ : e 0 = 1 := by decide
    have h₁ : e 1 = 0 := by decide
    have h₂ : e 2 = 3 := by decide
    have h₃ : e 3 = 2 := by decide
    have rename_X (i : Fin 4) :
        (MvPolynomial.rename ⇑e).toRingHom (MvPolynomial.X i) =
          (MvPolynomial.X (e i) : MvPolynomial (Fin 4) ℤ) := MvPolynomial.rename_X _ _
    simp only [map_mul, map_pow, rename_X, h₀, h₁, h₂, h₃,
      permAscentCount_positionReverse, permDescentCount_positionReverse,
      permLeftToRightMaxCount_positionReverse, permRightToLeftMaxCount_positionReverse]
    ac_rfl

end MetaMathlibExt
