/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Hindman

/-!
# Ultrafilters in Ramsey families

The ultrafilters contained in a Ramsey family form a closed set.
A Ramsey family of sets is invariant under left translation exactly when its ultrafilters
form a left ideal under the ultrafilter product.
-/

namespace MetaMathlibExt

@[expose] public section

variable {S : Type*}

/-- **Families with the Ramsey property.** Let $S$ be a set. A collection $F$ of subsets of $S$ is
a family with the Ramsey property when $F$ is nonempty, $\emptyset \notin F$, $F$ is closed under
supersets (if $A \in F$ and $A \subseteq B$, then $B \in F$), and whenever $A \cup B \in F$, then
$A \in F$ or $B \in F$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 2 (families and the Ramsey property). -/
def IsRamseyFamily (F : Set (Set S)) : Prop :=
  F.Nonempty ∧ ∅ ∉ F ∧ (∀ A B, A ∈ F → A ⊆ B → B ∈ F) ∧
    ∀ A B, A ∪ B ∈ F → A ∈ F ∨ B ∈ F

/-- **The set β(F) of ultrafilters inside a family.** For a family $\mathcal F$ of subsets of a
set $S$, $\beta(\mathcal F)$ is the set of ultrafilters $p$ on $S$ all of whose members lie in
$\mathcal F$, that is, $A \in \mathcal F$ for every $A \in p$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 2 (definition of `β(F)`). -/
def betaFamily (F : Set (Set S)) : Set (Ultrafilter S) :=
  {p | ∀ A ∈ p, A ∈ F}

/-- **Membership in β(F).** Let $F$ be a collection of subsets of a set $S$ and let $p$ be an
ultrafilter on $S$. Then $p \in \beta(F)$ if and only if every member of $p$ belongs to $F$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 2 (definition of `β(F)`). -/
theorem mem_betaFamily {F : Set (Set S)} {p : Ultrafilter S} :
    p ∈ betaFamily F ↔ ∀ A ∈ p, A ∈ F :=
  Iff.rfl

/-- **β of the nonempty sets is all of βS.** For every set $S$, every ultrafilter on $S$ lies in
$\beta(\mathcal F)$, where $\mathcal F$ is the family of all nonempty subsets of $S$; that is,
$\beta(\mathcal F) = \beta S$, the set of all ultrafilters on $S$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 2 (definition of `β(F)`). -/
theorem betaFamily_nonempty_sets :
    betaFamily {A : Set S | A.Nonempty} = Set.univ :=
  Set.eq_univ_of_forall fun _ _ hA => Ultrafilter.nonempty_of_mem hA

/-- **Ultrafilters inside a Ramsey family form a closed set.** Let $F$ be a family of subsets of a
set $S$ with the Ramsey property. Then the set $\beta(F)$ of ultrafilters on $S$ all of whose
members lie in $F$ is closed in the space $\beta S$ of all ultrafilters on $S$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 3 (`integers-2025-A4-thm-3`). -/
theorem isClosed_betaFamily {F : Set (Set S)} (_hF : IsRamseyFamily F) :
    IsClosed (betaFamily F) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro p hp
  simp only [Set.mem_compl_iff, mem_betaFamily, not_forall] at hp
  obtain ⟨A, hAp, hAF⟩ := hp
  exact ⟨{q | A ∈ q}, fun q hAq hq => hAF (hq A hAq), ultrafilter_isOpen_basic A, hAp⟩

namespace betaFamily_isLeftIdeal_iff

private theorem exists_ultrafilter {F : Set (Set S)} (hF : IsRamseyFamily F)
    {E : Set S} (hE : E ∈ F) : ∃ q ∈ betaFamily F, E ∈ q := by
  classical
  obtain ⟨_, hempty, hsuperset, hunion⟩ := hF
  -- The complements of sets outside the family form its dual filter.
  let dual : Filter S := {
    sets := {A | Aᶜ ∉ F}
    univ_sets := by simpa using hempty
    sets_of_superset := fun hA hAB hB => hA (hsuperset _ _ hB (Set.compl_subset_compl.mpr hAB))
    inter_sets := by
      intro A B hA hB
      change (A ∩ B)ᶜ ∉ F
      rw [Set.compl_inter]
      exact fun h => (hunion _ _ h).elim hA hB }
  have hEc : Eᶜ ∉ dual := by simpa [dual] using hE
  rw [Filter.mem_iff_ultrafilter] at hEc
  push Not at hEc
  obtain ⟨q, hq, hEq⟩ := hEc
  refine ⟨q, ?_, Ultrafilter.compl_notMem_iff.mp hEq⟩
  intro A hA
  by_contra h
  exact Filter.compl_notMem hA (hq (show Aᶜ ∈ dual by simpa [dual] using h))

end betaFamily_isLeftIdeal_iff

attribute [local instance] Ultrafilter.semigroup

/-- **Left-ideal criterion for β(F).** Let $S$ be a semigroup and $\mathcal F$ a family of subsets
of $S$ with the Ramsey property. Multiply ultrafilters on $S$ by $E \in pq$ iff
$\{x \in S : \{y \in S : xy \in E\} \in q\} \in p$. Then $pq \in \beta(\mathcal F)$ for every
ultrafilter $p$ on $S$ and every $q \in \beta(\mathcal F)$ (that is, $\beta(\mathcal F)$ is a
left ideal of $\beta S$) if and only if $sE = \{se : e \in E\}$ lies in $\mathcal F$ for every
$s \in S$ and every $E \in \mathcal F$.

The paper's second sentence (right ideal iff right shift-invariant) is omitted: with this
convention it fails. Let $L$ be a minimal left ideal of $\beta\mathbb{N}$ and $\mathcal F_L$ the
family of sets belonging to some member of $L$. By the left half $\mathcal F_L$ is
shift-invariant ($\mathbb{N}$ is commutative), yet $L$ is not a right ideal, since a two-sided
ideal contains the smallest ideal $K(\beta\mathbb{N})$, a union of more than one minimal left
ideal.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 4 (`integers-2025-A4-thm-4`). -/
theorem betaFamily_isLeftIdeal_iff [Semigroup S] {F : Set (Set S)}
    (hF : IsRamseyFamily F) :
    (∀ p : Ultrafilter S, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F) ↔
      ∀ s : S, ∀ E ∈ F, (fun e => s * e) '' E ∈ F := by
  constructor
  · intro hleft s E hE
    obtain ⟨q, hq, hEq⟩ := betaFamily_isLeftIdeal_iff.exists_ultrafilter hF hE
    apply hleft (pure s) q hq
    change (s * ·) ⁻¹' ((s * ·) '' E) ∈ q
    exact Filter.mem_of_superset hEq (Set.subset_preimage_image _ _)
  · intro hshift p q hq A hA
    obtain ⟨s, hs⟩ := ((Ultrafilter.eventually_mul p q (· ∈ A)).mp hA).exists
    exact hF.2.2.1 _ _ (hshift s _ (hq _ hs)) (Set.image_preimage_subset _ _)

end

end MetaMathlibExt
