/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import MathlibExt.Combinatorics.Enumerative.StableMatchingSequences
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Counting disjoint stable-matching preference profiles

The map from participant pairs to mutual ranks determines both sets of preference lists.
For disjoint profiles it is a permutation. Independent relabeling of the men and women
precomposes this permutation, so each relabeling orbit has size `(n!) ^ 2`.

## References

* Matvey Borodin, Aidan Duncan, Boyan Litchev, Jiahe Liu, Veronika Moroz, Matthew Qian,
  Rohith Raghavan, Garima Rastogi, Michael Voigt, and Tanya Khovanova,
  [Sequences of the Stable Matching Problem](https://cs.uwaterloo.ca/journals/JIS/VOL27/Khovanova/khova32.pdf),
  *Journal of Integer Sequences* 27 (2024), Article 24.2.2, pp. 1–24, Section 3.8, Proposition 3.
-/

set_option autoImplicit false

namespace MetaMathlibExt.StableMatchingSequences

open Nat

variable {n : ℕ}

private def rankPair (P : PreferenceProfile n) (ij : Fin n × Fin n) : Fin n × Fin n :=
  ((P.1 ij.1).symm ij.2, (P.2 ij.2).symm ij.1)

private theorem rankPair_injective : Function.Injective (rankPair (n := n)) := by
  intro P Q h
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · have hinv : (P.1 i).symm = (Q.1 i).symm :=
      Equiv.ext fun j => congrArg Prod.fst (congrFun h (i, j))
    exact congrArg Equiv.symm hinv
  · have hinv : (P.2 j).symm = (Q.2 j).symm :=
      Equiv.ext fun i => congrArg Prod.snd (congrFun h (i, j))
    exact congrArg Equiv.symm hinv

private abbrev DisjointProfile (n : ℕ) :=
  {P : PreferenceProfile n // Function.Bijective (rankPair P)}

private noncomputable def rankPermutation (P : DisjointProfile n) : Equiv.Perm (Fin n × Fin n) :=
  Equiv.ofBijective (rankPair P.val) P.property

private theorem rankPermutation_injective : Function.Injective (rankPermutation (n := n)) := by
  intro P Q h
  exact Subtype.ext (rankPair_injective (congrArg (fun e : Equiv.Perm (Fin n × Fin n) => ⇑e) h))

private abbrev Relabeling (n : ℕ) := Equiv.Perm (Fin n) × Equiv.Perm (Fin n)

private def relabel (g : Relabeling n) (P : DisjointProfile n) : DisjointProfile n :=
  ⟨(fun i => (P.val.1 (g.1.symm i)).trans g.2,
    fun j => (P.val.2 (g.2.symm j)).trans g.1),
    P.property.comp (Equiv.prodCongr g.1.symm g.2.symm).bijective⟩

private theorem rankPair_relabel (g : Relabeling n) (P : DisjointProfile n) (ij : Fin n × Fin n) :
    rankPair (relabel g P).val ij = rankPair P.val (g.1.symm ij.1, g.2.symm ij.2) := rfl

private instance : MulAction (Relabeling n) (DisjointProfile n) where
  smul := relabel
  one_smul P := by
    apply Subtype.ext
    apply rankPair_injective
    funext ij
    exact rankPair_relabel 1 P ij
  mul_smul g h P := by
    apply Subtype.ext
    apply rankPair_injective
    funext ij
    change rankPair (relabel (g * h) P).val ij = rankPair (relabel g (relabel h P)).val ij
    rfl

private theorem stabilizer_eq_bot (P : DisjointProfile n) :
    MulAction.stabilizer (Relabeling n) P = ⊥ := by
  refine le_antisymm (fun g hg => ?_) bot_le
  rw [Subgroup.mem_bot]
  have hfix : relabel g P = P := hg
  have h (i j : Fin n) : (g.1.symm i, g.2.symm j) = (i, j) :=
    P.property.injective <| by rw [← rankPair_relabel g P (i, j), hfix]
  -- The two projections of the diagonal suffice; for `n = 0` both are vacuous.
  have hm : g.1.symm = (1 : Equiv.Perm (Fin n)).symm :=
    Equiv.ext fun i => congrArg Prod.fst (h i i)
  have hw : g.2.symm = (1 : Equiv.Perm (Fin n)).symm :=
    Equiv.ext fun j => congrArg Prod.snd (h j j)
  exact Prod.ext (congrArg Equiv.symm hm) (congrArg Equiv.symm hw)

/-- **Counting disjoint preference profiles.** Call a preference profile for $n$ men and $n$ women
disjoint if for every pair of positions $(r, s)$ there is exactly one man–woman pair in which the
man ranks the woman at position $r$ and the woman ranks the man at position $s$. For every natural
number $n$, the number of disjoint profiles is at most $(n^2)!$ and is divisible by $(n!)^2$.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 3
(`jis-2024-24.2.2-prop-3`). -/
public theorem disjoint_profiles_card_le_and_dvd (n : ℕ) :
    Nat.card {P : PreferenceProfile n //
        Function.Bijective fun ij : Fin n × Fin n => ((P.1 ij.1).symm ij.2, (P.2 ij.2).symm ij.1)} ≤
        (n ^ 2)! ∧
      (n ! ) ^ 2 ∣ Nat.card {P : PreferenceProfile n //
        Function.Bijective fun ij : Fin n × Fin n =>
          ((P.1 ij.1).symm ij.2, (P.2 ij.2).symm ij.1)} := by
  change Nat.card (DisjointProfile n) ≤ (n ^ 2)! ∧ (n ! ) ^ 2 ∣ Nat.card (DisjointProfile n)
  constructor
  · simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_prod, Fintype.card_fin,
      pow_two] using Nat.card_le_card_of_injective rankPermutation rankPermutation_injective
  · have hcard : Nat.card (Relabeling n) = (n ! ) ^ 2 := by
      simp only [Relabeling, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm,
        Fintype.card_fin, pow_two]
    let e := MulAction.selfEquivOrbitsQuotientProd (stabilizer_eq_bot (n := n))
    rw [Nat.card_congr e, Nat.card_prod, hcard]
    exact dvd_mul_left _ _

end MetaMathlibExt.StableMatchingSequences
