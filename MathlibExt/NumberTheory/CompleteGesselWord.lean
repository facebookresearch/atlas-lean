/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GesselWord

/-!
# Complete Gessel words

A complete Gessel word is a Gessel word in which each letter occurs as often as its
barred counterpart.

## References

- [A. Ayyer, *Towards a Human Proof of Gessel's Conjecture*](https://cs.uwaterloo.ca/journals/JIS/VOL12/Ayyer/ayyer7.tex),
  Definition 3 (source statement `jis_b68f59060d4f5b144b4dc9e5`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Complete Gessel words.** A word $w$ over the Gessel alphabet of $S = [n] = \{1, \dots, n\}$
is a complete Gessel word when it is a Gessel word and, for every $m \in [n]$, the unbarred
letter $m$ and the barred letter $\bar m$ occur the same number of times in $w$. -/
def IsCompleteGesselWord (n : ℕ) (w : List (GesselAlphabet n)) : Prop :=
  IsGesselWord n w ∧
    ∀ i : Fin n,
      gesselUnbarredCount n w (i.val + 1) = gesselBarredCount n w (i.val + 1)

/-- **Complete Gessel words are the Gessel words of zero balance.** A word $w$ over the Gessel
alphabet of $[n] = \{1, \dots, n\}$ is a complete Gessel word if and only if it is a Gessel word
and, for every $m \in [n]$, the signed balance of $m$ in $w$ (the number of occurrences of the
unbarred letter $m$ minus the number of occurrences of the barred letter $\bar m$) is zero. -/
theorem isCompleteGesselWord_iff_balance_eq_zero (n : ℕ) (w : List (GesselAlphabet n)) :
    IsCompleteGesselWord n w ↔
      IsGesselWord n w ∧ ∀ i : Fin n, gesselBalance n w (i.val + 1) = 0 := by
  constructor
  · rintro ⟨hg, hcount⟩
    refine ⟨hg, fun i => ?_⟩
    have hi := hcount i
    unfold gesselBalance
    omega
  · rintro ⟨hg, hbalance⟩
    refine ⟨hg, fun i => ?_⟩
    have hi := hbalance i
    unfold gesselBalance at hi
    omega

end

end MetaMathlibExt
