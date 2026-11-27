/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HardyLittlewoodPrimeTuple
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Admissibility of a finite set is decided by the primes up to its size

A finite set `H` of integers is admissible (`MetaMathlibExt.IsAdmissibleFinset`) when for every
prime `p` some residue class modulo `p` contains no element of `H`. For a prime `p > #H` this is
automatic, since `#H` integers occupy at most `#H < p` classes. Hence only the finitely many primes
`p ≤ #H` need to be checked, and admissibility is decidable.

Sources: D. A. Goldston, J. Pintz and C. Y. Yıldırım, *Primes in tuples I*, Ann. of Math. 170
(2009), 819-862 (arXiv:math/0508185v1, p. 2, discussion before (1.6)); J. Maynard, *Small gaps
between primes*, Ann. of Math. 181 (2015), 383-413 (arXiv:1311.4600v3, Section 4, proof of
Theorem 1.1).
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Admissibility needs only the primes up to the size of the set.** A finite set `H` of
integers is admissible if and only if, for every prime `p ≤ #H`, some residue class modulo `p`
contains no element of `H`; every prime `p > #H` is automatically avoided because `#H` integers
meet at most `#H < p` residue classes (Goldston, Pintz and Yıldırım, *Primes in tuples I*,
arXiv:math/0508185v1, p. 2: "This is immediately true for all primes `p > k`, so to test this
condition we need only to examine small primes"). -/
theorem isAdmissibleFinset_iff_forall_prime_le_card (H : Finset ℤ) :
    IsAdmissibleFinset H ↔
      ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  refine ⟨fun hH p hp _ => hH p hp, fun hsmall p hp => ?_⟩
  by_cases hpk : p ≤ H.card
  · exact hsmall p hp hpk
  · have := Fact.mk hp
    push Not at hpk
    -- The image of `H` in `ZMod p` has at most `#H < p` elements, so it misses a class.
    have himg : (H.image fun h : ℤ => (h : ZMod p)).card < Fintype.card (ZMod p) := by
      rw [ZMod.card]
      exact (Finset.card_image_le).trans_lt hpk
    obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := H.image fun h : ℤ => (h : ZMod p)) (t := Finset.univ)
      (by simpa using himg)
    exact ⟨r, fun h hh hEq => hr (Finset.mem_image.mpr ⟨h, hh, hEq⟩)⟩

/-- **Bounded search form of admissibility.** A finite set `H` of integers is admissible if and
only if for every prime `p ≤ #H` there is `r < p` such that no `h ∈ H` is congruent to `r`
modulo `p`. Every quantifier ranges over a finite set, which makes admissibility decidable
(Goldston, Pintz and Yıldırım, *Primes in tuples I*, arXiv:math/0508185v1, (1.6) and the
remark before it). -/
theorem isAdmissibleFinset_iff_bounded (H : Finset ℤ) :
    IsAdmissibleFinset H ↔
      ∀ p ∈ Finset.range (H.card + 1), p.Prime →
        ∃ r ∈ Finset.range p, ∀ h ∈ H, (h : ZMod p) ≠ (r : ZMod p) := by
  rw [isAdmissibleFinset_iff_forall_prime_le_card]
  refine forall_congr' fun p => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff]
  refine ⟨fun h hpk hp => ?_, fun h hp hpk => ?_⟩
  · obtain ⟨r, hr⟩ := h hp hpk
    have := Fact.mk hp
    refine ⟨r.val, Finset.mem_range.mpr r.val_lt, fun x hx => ?_⟩
    rw [ZMod.natCast_zmod_val]
    exact hr x hx
  · obtain ⟨r, -, hr⟩ := h hpk hp
    exact ⟨r, hr⟩

/-- **Admissibility of a finite set of integers is decidable**, by checking the finitely many
primes `p ≤ #H` and residues `r < p` (`isAdmissibleFinset_iff_bounded`). -/
instance decidableIsAdmissibleFinset : DecidablePred IsAdmissibleFinset := fun H =>
  decidable_of_iff _ (isAdmissibleFinset_iff_bounded H).symm

end MetaMathlibExt
