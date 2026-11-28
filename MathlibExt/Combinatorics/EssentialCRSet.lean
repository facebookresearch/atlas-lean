/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Hindman
public import MathlibExt.Combinatorics.CRSetArithmeticProgression
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Combinatorics.HalesJewett
import MathlibExt.Combinatorics.EssentialSetSequence
import MathlibExt.Combinatorics.RamseyFamilyDecreasingSequenceIdempotent

/-!
# Essential CR-sets via decreasing sequences

In a countable commutative semigroup, an essential CR-set is exactly a set containing a
nested sequence of CR-sets in which each element of a term translates some term into that term.
The equivalence includes the empty carrier: there are neither ultrafilters nor CR-sets there.

For partition regularity, group the rows of a matrix into blocks indexed by the coordinates of
Hales–Jewett words. Fix a monochromatic line and absorb its fixed coordinates and the block seeds
into the common shift. The remaining rows, at the variable coordinates, give witnesses in one cell.
An adjoined zero lets us sum over possibly empty collections of fixed coordinates.

## References

* Dibyendu De and Pintu Debnath, *Abundance of Arithmetic Progressions in CR-Sets*,
  INTEGERS **25** (2025), Article A4, pp. 1–8, Theorems 4, 6 and 7 (§2).
  <https://math.colgate.edu/~integers/z4/z4.pdf>
* Vitaly Bergelson and Daniel Glasscock, *On the interplay between notions of additive
  and multiplicative largeness and its combinatorial applications*, Journal of
  Combinatorial Theory, Series A **172** (2020), Article 105203, Lemma 2.14 (§2.1),
  for the partition argument cited in Theorem 7.
* A. W. Hales and R. I. Jewett, *Regularity and positional games*, Transactions of the
  American Mathematical Society **106** (1963), pp. 222–229, for the finite Hales–Jewett theorem
  (Bergelson and Glasscock, Theorem 2.13). We use Mathlib's
  `Combinatorics.Line.exists_mono_in_high_dimension`.
* Cory Christopherson, *Closed Ideals in the Stone–Čech Compactification of a Countable
  Semigroup and Some Applications to Ergodic Theory and Topological Dynamics*, PhD thesis,
  The Ohio State University, 2014, Theorem 5.1.2, as cited for the left-ideal criterion.
* Dibyendu De, Pintu Debnath and Sayan Goswami, *Elementary characterization of essential
  $\mathcal{F}$-sets and its combinatorial consequences*, Semigroup Forum **104** (2022),
  pp. 45–57, Theorem 5, as cited for the general decreasing-sequence characterization.
-/

namespace MetaMathlibExt

open scoped BigOperators

attribute [local instance] Ultrafilter.addSemigroup Ultrafilter.semigroup

@[expose] public section

variable {S : Type*} [AddCommSemigroup S]

/-- **Essential CR-set.** Let $(S, +)$ be a commutative semigroup, and add ultrafilters on $S$ by
the rule that $E \in p + q$ if and only if $\{x \in S : \{y \in S : x + y \in E\} \in q\} \in p$.
A subset $A$ of $S$ is an essential CR-set when there is an ultrafilter $p$ on $S$ with
$p + p = p$, all of whose members are CR-sets, such that $A \in p$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 2 (definition of essential CR-sets before Theorem 7). -/
def IsEssentialCRSet (A : Set S) : Prop :=
  ∃ p : Ultrafilter S, p + p = p ∧ (∀ B ∈ p, IsCRSet B) ∧ A ∈ p

end

section

variable {S : Type*} [AddCommSemigroup S] {A B : Set S}

private theorem coe_foldl_eq_sum {ι : Type*} (R : Finset ι) (f : ι → S) (s : S) :
    (↑((R.toList.map f).foldl (· + ·) s) : WithZero S) = (s : WithZero S) + ∑ i ∈ R, ↑(f i) := by
  rw [← Finset.sum_map_toList, List.sum_eq_foldl]
  simp only [List.foldl_map]
  calc
    _ = R.toList.foldl (fun x i => x + (f i : WithZero S)) (s : WithZero S) :=
      (List.foldl_hom (fun x : S => (x : WithZero S))
        (fun x i => (WithZero.coe_add x (f i)).symm)).symm
    _ = _ := by
      simpa only [add_zero] using
        List.foldl_hom ((s : WithZero S) + ·) (l := R.toList) (init := 0)
          (g₁ := fun x i => x + (f i : WithZero S))
          (fun x i => add_assoc _ x (f i : WithZero S))

private theorem exists_mono_matrix (t : S) (hAB : IsCRSet (A ∪ B)) (κ : Type) [Finite κ] :
    ∃ r : ℕ, ∀ M : Fin r → κ → S, ∃ R : Finset (Fin r), R.Nonempty ∧ ∃ s : S,
      (∀ j, (R.toList.map fun i => M i j).foldl (· + ·) s ∈ A) ∨
      (∀ j, (R.toList.map fun i => M i j).foldl (· + ·) s ∈ B) := by
  classical
  let := Fintype.ofFinite κ
  obtain ⟨ι, _, hHJ⟩ := Combinatorics.Line.exists_mono_in_high_dimension κ Bool
  obtain ⟨r, hr⟩ := isCRSet_iff_fintype.mp hAB (ι → κ)
  let e := Fintype.equivFin (Fin r × ι)
  refine ⟨Fintype.card (Fin r × ι), fun M => ?_⟩
  let block (i : Fin r) (w : ι → κ) : S :=
    (Finset.univ.toList.map fun k => M (e (i, k)) (w k)).foldl (· + ·) t
  obtain ⟨I, hI, s, hs⟩ := hr block
  let value (w : ι → κ) := (I.toList.map fun i => block i w).foldl (· + ·) s
  obtain ⟨l, b, hmono⟩ := hHJ fun w => decide (value w ∈ A)
  let V : Finset ι := Finset.univ.filter fun k => l.idxFun k = none
  have hV : V.Nonempty := by
    obtain ⟨k, hk⟩ := l.proper
    exact ⟨k, by simp [V, hk]⟩
  let R := (I ×ˢ V).map e.toEmbedding
  have hR : R.Nonempty := (hI.product hV).map
  -- Only the rows in variable coordinates depend on the letter inserted in the line.
  let fixed (i : Fin r) (k : ι) : WithZero S :=
    ((l.idxFun k).map fun j => (M (e (i, k)) j : WithZero S)).getD 0
  let offset (i : Fin r) : WithZero S := (t : WithZero S) + ∑ k ∈ Vᶜ, fixed i k
  have hblock (i : Fin r) (j : κ) : (block i (l j) : WithZero S) =
      offset i + ∑ k ∈ V, (M (e (i, k)) j : WithZero S) := by
    dsimp only [block, offset]
    rw [coe_foldl_eq_sum, ← Finset.sum_add_sum_compl Vᶜ, compl_compl, add_assoc]
    congr 2
    · apply Finset.sum_congr rfl
      intro k hk
      have h : l.idxFun k ≠ none := by simpa [V] using hk
      obtain ⟨a, ha⟩ := Option.ne_none_iff_exists.mp h
      simp [fixed, ← ha]
    · apply Finset.sum_congr rfl
      intro k hk
      exact congrArg (fun a => (M (e (i, k)) a : WithZero S))
        (l.apply_none _ _ (Finset.mem_filter.mp hk).2)
  let d : WithZero S := ∑ i ∈ I, offset i
  obtain ⟨s', hs'⟩ : ∃ s' : S, (s' : WithZero S) = (s : WithZero S) + d := by
    cases d using WithZero.cases_on with
    | zero => exact ⟨s, by simp⟩
    | coe a => exact ⟨s + a, WithZero.coe_add _ _⟩
  have hvalue (j : κ) : value (l j) = (R.toList.map fun i => M i j).foldl (· + ·) s' := by
    apply WithZero.coe_injective
    dsimp only [value]
    rw [coe_foldl_eq_sum, coe_foldl_eq_sum, hs']
    simp_rw [hblock, Finset.sum_add_distrib, add_assoc]
    congr 2
    rw [Finset.sum_map, Finset.sum_product]
    rfl
  refine ⟨R, hR, s', ?_⟩
  cases b with
  | false =>
    right
    intro j
    rw [← hvalue]
    exact (hs (l j)).resolve_left (of_decide_eq_false (hmono j))
  | true =>
    left
    intro j
    rw [← hvalue]
    exact of_decide_eq_true (hmono j)

private theorem cr_union_iff (t : S) : IsCRSet (A ∪ B) ↔ IsCRSet A ∨ IsCRSet B := by
  classical
  constructor
  · intro hAB
    by_contra h
    obtain ⟨hA, hB⟩ := not_or.mp h
    rw [isCRSet_iff_fintype] at hA hB
    push Not at hA hB
    obtain ⟨κ, iκ, hκ⟩ := hA
    obtain ⟨θ, iθ, hθ⟩ := hB
    obtain ⟨r, hr⟩ := exists_mono_matrix t hAB (κ ⊕ θ)
    obtain ⟨M, hM⟩ := hκ r
    obtain ⟨N, hN⟩ := hθ r
    obtain ⟨R, hR, s, hcol | hcol⟩ := hr fun i => Sum.elim (M i) (N i)
    · obtain ⟨j, hj⟩ := hM R hR s
      exact hj (hcol (Sum.inl j))
    · obtain ⟨j, hj⟩ := hN R hR s
      exact hj (hcol (Sum.inr j))
  · intro h
    apply isCRSet_iff_fintype.mpr
    intro κ _
    rcases h with h | h
    · obtain ⟨r, hr⟩ := isCRSet_iff_fintype.mp h κ
      refine ⟨r, fun M => ?_⟩
      obtain ⟨R, hR, s, hs⟩ := hr M
      exact ⟨R, hR, s, fun j => Or.inl (hs j)⟩
    · obtain ⟨r, hr⟩ := isCRSet_iff_fintype.mp h κ
      refine ⟨r, fun M => ?_⟩
      obtain ⟨R, hR, s, hs⟩ := hr M
      exact ⟨R, hR, s, fun j => Or.inr (hs j)⟩

end

/-- **Essential CR-sets via decreasing sequences.** Let $S$ be a countable commutative semigroup
and let $A \subseteq S$. Then $A$ is an essential CR-set if and only if there is a decreasing
sequence $C_0 \supseteq C_1 \supseteq C_2 \supseteq \cdots$ of CR-sets contained in $A$ such that
for every $n$ and every $x \in C_n$ there is an $m$ with $C_m \subseteq -x + C_n$, where
$-x + C_n = \{y \in S : x + y \in C_n\}$.

The sequence is indexed from $0$ rather than $1$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 7 (`integers-2025-A4-thm-7`). -/
public theorem isEssentialCRSet_iff_exists_decreasing_sequence {S : Type*}
    [AddCommSemigroup S] [Countable S] (A : Set S) :
    IsEssentialCRSet A ↔ ∃ C : ℕ → Set S, Antitone C ∧ (∀ n, C n ⊆ A) ∧
      (∀ n, ∀ x ∈ C n, ∃ m, C m ⊆ {y : S | x + y ∈ C n}) ∧ ∀ n, IsCRSet (C n) := by
  cases isEmpty_or_nonempty S with
  | inl h =>
    have hn (B : Set S) : ¬ IsCRSet B := by
      intro hB
      obtain ⟨r, hr⟩ := isCRSet_iff_fintype.mp hB (Fin 0)
      obtain ⟨_, _, t, _⟩ := hr fun _ => Fin.elim0
      exact isEmptyElim t
    constructor
    · rintro ⟨p, _, hp, _⟩
      exact (hn Set.univ (hp _ Filter.univ_mem)).elim
    · rintro ⟨C, _, _, _, hC⟩
      exact (hn (C 0) (hC 0)).elim
  | inr h =>
    obtain ⟨t⟩ := h
    have : Countable (Multiplicative S) := ‹Countable S›
    let F : Set (Set (Multiplicative S)) := {B | IsCRSet (S := S) B}
    have hF : IsRamseyFamily F := by
      apply isRamseyFamily_iff_univ_empty_union.mpr
      refine ⟨isCRSet_iff_fintype.mpr fun _ _ => ⟨1, fun _ =>
        ⟨Finset.univ, Finset.univ_nonempty, t, fun _ => Set.mem_univ _⟩⟩, ?_, ?_⟩
      · intro h₀
        obtain ⟨r, hr⟩ := isCRSet_iff_fintype.mp (show IsCRSet (∅ : Set S) from h₀) (Fin 1)
        obtain ⟨_, _, _, hs⟩ := hr fun _ _ => t
        exact hs 0
      · intro B C
        exact cr_union_iff t
    have hsub : ∀ p ∈ betaFamily F, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F := by
      have hleft := (betaFamily_isLeftIdeal_iff hF).mpr (by
        intro x B hB
        apply isCRSet_iff_fintype.mpr
        intro κ _
        obtain ⟨r, hr⟩ := isCRSet_iff_fintype.mp (show IsCRSet (S := S) B from hB) κ
        refine ⟨r, fun M => ?_⟩
        obtain ⟨R, hR, s, hs⟩ := hr M
        refine ⟨R, hR, x.toAdd + s, fun j => ⟨_, hs j, ?_⟩⟩
        exact (List.foldl_hom (x.toAdd + ·) (g₁ := (· + ·)) (g₂ := (· + ·))
          (fun a b => add_assoc _ a b)).symm)
      exact fun p _ q hq => hleft p q hq
    constructor
    · rintro ⟨p, hpp, hp, hA⟩
      exact exists_decreasing_sequence_of_idempotent_mem hF hsub
        ⟨(p : Ultrafilter (Multiplicative S)), mem_betaFamily.mpr hp, hpp, hA⟩
    · rintro ⟨C, hanti, hCA, hshift, hCF⟩
      obtain ⟨p, hp, hpp, hA⟩ := exists_idempotent_mem_of_decreasing_sequence hF hsub
        (C : ℕ → Set (Multiplicative S)) hanti hCA hshift hCF
      exact ⟨(p : Ultrafilter S), hpp, mem_betaFamily.mp hp, hA⟩

end MetaMathlibExt
