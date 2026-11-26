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

A Ramsey family is the union of the ultrafilters it contains. These ultrafilters form a
closed set, and every nonempty closed set of ultrafilters arises this way.
A Ramsey family of sets is invariant under left translation exactly when its ultrafilters
form a left ideal under the ultrafilter product. Closure under the ultrafilter product has
a weaker criterion in terms of finite intersections of inverse left translates.

## References

* Dibyendu De and Pintu Debnath, *Abundance of Arithmetic Progressions in CR-Sets*,
  INTEGERS 25 (2025), Article A4, pp. 1–8, Theorem 5 (p. 4).
* Cory Christopherson, *Closed Ideals in the Stone–Čech Compactification of a Countable
  Semigroup and Some Applications to Ergodic Theory and Topological Dynamics*, PhD thesis,
  The Ohio State University, 2014, Theorem 5.1.10 (p. 74), gives the compactness proof
  of the subsemigroup criterion.
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

/-- **Nonempty closed sets of ultrafilters come from Ramsey families.** Let $S$ be a set, let
$\beta S$ be the space of ultrafilters on $S$, and let $K$ be a nonempty closed subset of
$\beta S$. Let $\mathcal F_K$ be the collection of the sets $E \subseteq S$ with $E \in p$ for
some $p \in K$. Then $\mathcal F_K$ is a family with the Ramsey property, and
$\beta(\mathcal F_K) = K$, where $\beta(\mathcal F_K)$ is the set of ultrafilters on $S$ all of
whose members lie in $\mathcal F_K$.

The paper omits $K \ne \emptyset$; for $K = \emptyset$ the collection $\mathcal F_K$ is empty,
hence not a family.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 3 (`integers-2025-A4-thm-3`). -/
theorem isRamseyFamily_and_betaFamily_eq_of_isClosed {K : Set (Ultrafilter S)}
    (hK : IsClosed K) (hne : K.Nonempty) :
    IsRamseyFamily {E : Set S | ∃ p ∈ K, E ∈ p} ∧ betaFamily {E : Set S | ∃ p ∈ K, E ∈ p} = K := by
  constructor
  · obtain ⟨p, hp⟩ := hne
    refine ⟨⟨Set.univ, p, hp, Filter.univ_mem⟩, ?_, ?_, ?_⟩
    · rintro ⟨q, _, h⟩
      exact q.empty_notMem h
    · rintro A B ⟨q, hq, hA⟩ hAB
      exact ⟨q, hq, Filter.mem_of_superset hA hAB⟩
    · rintro A B ⟨q, hq, hAB⟩
      exact (Ultrafilter.union_mem_iff.mp hAB).imp
        (fun hA => ⟨q, hq, hA⟩) (fun hB => ⟨q, hq, hB⟩)
  · apply Set.Subset.antisymm
    · intro p hp
      rw [← hK.closure_eq, ultrafilterBasis_is_basis.mem_closure_iff]
      rintro _ ⟨A, rfl⟩ hA
      obtain ⟨q, hq, hAq⟩ := hp A hA
      exact ⟨q, hAq, hq⟩
    · exact fun p hp A hA => ⟨p, hp, hA⟩

/-- **Theorem 3, part 2: a Ramsey family is the union of its ultrafilters.** Let $F$ be a family
of subsets of a set $S$ with the Ramsey property, and let $\beta(F)$ be the set of ultrafilters on
$S$ all of whose members lie in $F$. Then a set $A \subseteq S$ lies in $F$ if and only if
$A \in p$ for some $p \in \beta(F)$; that is, $F = \bigcup \beta(F)$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 3 (`integers-2025-A4-thm-3`). -/
theorem mem_iff_exists_mem_betaFamily {F : Set (Set S)} (hF : IsRamseyFamily F)
    (A : Set S) : A ∈ F ↔ ∃ p ∈ betaFamily F, A ∈ p := by
  classical
  refine ⟨fun hA => ?_, fun ⟨_, hp, hAp⟩ => hp A hAp⟩
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
  have hAc : Aᶜ ∉ dual := by simpa [dual] using hA
  rw [Filter.mem_iff_ultrafilter] at hAc
  push Not at hAc
  obtain ⟨q, hq, hAq⟩ := hAc
  refine ⟨q, ?_, Ultrafilter.compl_notMem_iff.mp hAq⟩
  intro B hB
  by_contra h
  exact Filter.compl_notMem hB (hq (show Bᶜ ∈ dual by simpa [dual] using h))

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
    obtain ⟨q, hq, hEq⟩ := (mem_iff_exists_mem_betaFamily hF E).mp hE
    apply hleft (pure s) q hq
    change (s * ·) ⁻¹' ((s * ·) '' E) ∈ q
    exact Filter.mem_of_superset hEq (Set.subset_preimage_image _ _)
  · intro hshift p q hq A hA
    obtain ⟨s, hs⟩ := ((Ultrafilter.eventually_mul p q (· ∈ A)).mp hA).exists
    exact hF.2.2.1 _ _ (hshift s _ (hq _ hs)) (Set.image_preimage_subset _ _)

/-- **Subsemigroup criterion for β(F).** Let $S$ be a semigroup and $\mathcal F$ a family of
subsets of $S$ with the Ramsey property. For $x \in S$ and $E \subseteq S$ write
$x^{-1}E = \{y \in S : xy \in E\}$, and multiply ultrafilters on $S$ by $E \in pq$ iff
$\{x \in S : x^{-1}E \in q\} \in p$. Then $pq \in \beta(\mathcal F)$ for all
$p, q \in \beta(\mathcal F)$ if and only if every $E \subseteq S$ has the following property: if
there is $A \in \mathcal F$ such that $\bigcap_{x \in H} x^{-1}E \in \mathcal F$ for every finite
$H \subseteq A$, then $E \in \mathcal F$.

The source's intersection $\bigcap_{q \in H} x^{-1}E$ is read as $\bigcap_{x \in H} x^{-1}E$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 5 (`integers-2025-A4-thm-5`). -/
theorem betaFamily_isSubsemigroup_iff [Semigroup S] {F : Set (Set S)}
    (hF : IsRamseyFamily F) :
    (∀ p ∈ betaFamily F, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F) ↔
      ∀ E : Set S, (∃ A ∈ F, ∀ H : Finset S, ↑H ⊆ A →
        (⋂ x ∈ H, {y : S | x * y ∈ E}) ∈ F) → E ∈ F := by
  classical
  constructor
  · rintro hmul E ⟨A, hA, hfinite⟩
    obtain ⟨p, hp, hAp⟩ := (mem_iff_exists_mem_betaFamily hF A).mp hA
    let C (x : A) : Set (Ultrafilter S) := {q | {y : S | x.val * y ∈ E} ∈ q}
    have hC (x : A) : IsClosed (C x) := ultrafilter_isClosed_basic _
    -- A finite intersection of translate-membership conditions is witnessed by one ultrafilter.
    have hCfinite (H : Finset A) : (betaFamily F ∩ ⋂ x ∈ H, C x).Nonempty := by
      have hHA : ↑(H.image Subtype.val) ⊆ A := by
        intro x hx
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
        exact a.property
      obtain ⟨q, hq, hHq⟩ := (mem_iff_exists_mem_betaFamily hF _).mp (hfinite _ hHA)
      refine ⟨q, hq, Set.mem_iInter₂.mpr fun x hx => ?_⟩
      exact Filter.mem_of_superset hHq (Set.biInter_subset_of_mem (Finset.mem_image_of_mem _ hx))
    obtain ⟨q, hq, hqC⟩ := (isClosed_betaFamily hF).isCompact.inter_iInter_nonempty C hC hCfinite
    apply hmul p hp q hq E
    apply (Ultrafilter.eventually_mul p q (· ∈ E)).mpr
    exact Filter.mem_of_superset hAp fun x hx => Set.mem_iInter.mp hqC ⟨x, hx⟩
  · intro hcriterion p hp q hq E hE
    have hA : {x : S | {y : S | x * y ∈ E} ∈ q} ∈ p :=
      (Ultrafilter.eventually_mul p q (· ∈ E)).mp hE
    refine hcriterion E ⟨_, hp _ hA, fun H hH => hq _ ?_⟩
    exact (Filter.biInter_finset_mem H).mpr fun x hx => hH hx

end

end MetaMathlibExt
