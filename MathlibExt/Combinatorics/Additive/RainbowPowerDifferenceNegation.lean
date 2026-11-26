/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.Parity

/-!
# Negation symmetry of rainbow-free power-difference colorings

If `a` and `-a` have different colors, a step of size `a ^ k` from a point of the third color
must preserve that color. Indeed, the step gives solutions with both `a` and `-a` as the third
entry, reversing its orientation for odd `k`. Since `a ^ k` is nonzero, its additive multiples
reach the whole prime residue field, contradicting the presence of the other colors.

## References

* Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free Colorings and
  Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, pp. 1–16, Lemmas 9 and 10.
-/

namespace MetaMathlibExt

/-- **Rainbow-free colorings modulo a prime are symmetric under negation.** Let $p$ be a prime and
$k$ a natural number, and let $c$ be a coloring of $\mathbb{Z}/p\mathbb{Z}$ with three colors that
uses every color and is rainbow-free for $x - y = z^k$: no $x, y, z \in \mathbb{Z}/p\mathbb{Z}$
with $x - y = z^k$ have $c(x), c(y), c(z)$ pairwise distinct. Then $c(-a) = c(a)$ for every
$a \in \mathbb{Z}/p\mathbb{Z}$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 10
(`integers-2024-A105-lem-10`). -/
public theorem color_neg_eq_of_rainbowFree_powDiff
    (p k : ℕ) [Fact p.Prime] (c : ZMod p → Fin 3) (hc : Function.Surjective c)
    (hrf : ∀ x y z : ZMod p, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (a : ZMod p) : c (-a) = c a := by
  by_contra hne
  have ha : a ≠ 0 := by
    intro ha
    exact hne (by simp [ha])
  let d := a ^ k
  have hd : d ≠ 0 := pow_ne_zero _ ha
  -- The two distinct colors leave a third color, which surjectivity realizes at `x₀`.
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {c (-a), c a}) (t := Finset.univ)
    (by simp [Finset.card_pair_eq_two_iff.mpr hne])
  have ⟨hiNeg, hiPos⟩ : i ≠ c (-a) ∧ i ≠ c a := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hi
  obtain ⟨x₀, hx₀⟩ := hc i
  have hstep (x : ZMod p) (hx : c x = i) : c (x + d) = i := by
    by_contra hxi
    have hedge : c (x + d) ≠ c x := fun h => hxi (h.trans hx)
    have hxPos : c x ≠ c a := fun h => hiPos (hx.symm.trans h)
    have hxNeg : c x ≠ c (-a) := fun h => hiNeg (hx.symm.trans h)
    have hdiff : (x + d) - x = a ^ k := add_sub_cancel_left x d
    have hpos : c (x + d) = c a := by
      by_contra hpos
      exact hrf (x + d) x a hdiff ⟨hedge, hxPos, hpos⟩
    have hneg : c (x + d) = c (-a) := by
      by_contra hneg
      rcases Nat.even_or_odd k with hk | hk
      · have hdiff' : (x + d) - x = (-a) ^ k := (hk.neg_pow a).symm ▸ hdiff
        exact hrf (x + d) x (-a) hdiff' ⟨hedge, hxNeg, hneg⟩
      · have hdiff' : x - (x + d) = (-a) ^ k := by
          rw [hk.neg_pow, ← hdiff, neg_sub]
        exact hrf x (x + d) (-a) hdiff' ⟨hedge.symm, hneg, hxNeg⟩
    exact hne (hneg.symm.trans hpos)
  have hiterate (n : ℕ) : c (x₀ + (n : ZMod p) * d) = i := by
    induction n with
    | zero => simpa using hx₀
    | succ n ih =>
      simpa only [Nat.cast_succ, add_mul, one_mul, add_assoc] using hstep _ ih
  -- In the prime residue field, `(x - x₀) / d` gives the required step count modulo `p`.
  have hall (x : ZMod p) : c x = i := by
    simpa only [ZMod.natCast_zmod_val, div_mul_cancel₀ _ hd, add_comm x₀, sub_add_cancel] using
      hiterate ((x - x₀) / d).val
  exact hiPos (hall a).symm

end MetaMathlibExt
