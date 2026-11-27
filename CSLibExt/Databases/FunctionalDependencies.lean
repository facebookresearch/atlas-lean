/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Union

/-!
# Functional dependencies

Attributes range over a finite type `A`. A functional dependency `X → Y` (`FD.mk X Y`, for
attribute sets `X Y : Finset A`) holds in a relation `r`, given as a set of tuples `A → V`, when
any two tuples of `r` that agree on `X` also agree on `Y` (`FD.HoldsIn`). A set of dependencies
`F` entails `X → Y` (`Entails`) when `X → Y` holds in every relation in which all of `F` holds.

`Derives F f` is derivability with **Armstrong's axioms** (reflexivity, augmentation,
transitivity) from the dependencies in `F`.
* `Derives.sound`: Armstrong's axioms are sound.
* `Derives.union`, `Derives.decompose`, `Derives.pseudotrans`: the derived rules.
* `attrClosure F X` is the attribute-closure algorithm: starting from `X`, repeatedly add the
  right side of every dependency whose left side is already included, until nothing changes.
  `derives_iff_subset_attrClosure`: `F` derives `X → Y` exactly when `Y ⊆ attrClosure F X`, so
  the algorithm computes `X⁺` (`mem_attrClosure`) and decides derivability.
* `holdsIn_closureWitnessRelation`: the relation of at most two tuples that agree exactly on
  `attrClosure F X` satisfies `F` (the usual witness in the completeness proof; it is not an
  Armstrong relation for `F` in the sense of satisfying exactly the consequences of `F`).
* `derives_iff_entails` (**Armstrong's theorem**): the axioms are sound and complete.
  `derives_of_forall_two_tuple` is the sharper completeness statement: a dependency holding in
  every two-tuple `Bool`-valued relation that satisfies `F` is derivable.

Keys: `IsSuperkey F K` (`K` determines all attributes) and `IsCandidateKey F K` (a minimal
superkey).
* `isSuperkey_iff_attrClosure` and `isCandidateKey_iff` reduce both to closure computations;
  `IsSuperkey.eq_of_agree` is the meaning of a superkey in every relation satisfying `F`.
* `findKey F l` removes the attributes of `l` one at a time from the full attribute set,
  dropping each one whose removal leaves a superkey; `findKey_isCandidateKey`: when `l` lists all
  attributes it returns a candidate key. `exists_isCandidateKey_subset`: every superkey contains
  a candidate key.

## References

* W. W. Armstrong, *Dependency structures of data base relationships*, IFIP Congress 1974.
* S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995,
  Section 8.2 (functional and key dependencies).
* J. D. Ullman, *Principles of Database and Knowledge-Base Systems*, Vol. I, Computer Science
  Press, 1988, Chapter 7 (Armstrong's axioms and the attribute-closure algorithm).
-/

@[expose] public section

namespace Cslib.Databases

/-- **Functional dependency.** A functional dependency $X \to Y$ over a type $A$ of attributes
consists of two finite sets of attributes $X, Y \subseteq A$: the determining attributes $X$
(its left side) and the determined attributes $Y$ (its right side). -/
structure FD (A : Type*) where
  /-- The determining attributes. -/
  lhs : Finset A
  /-- The determined attributes. -/
  rhs : Finset A
deriving DecidableEq

variable {A : Type*}

namespace FD

/-- **A functional dependency holds in a relation.** Let $A$ be a type of attributes and $V$ a
type of values. A functional dependency $X \to Y$ on $A$ holds in a relation $r$, a set of tuples
$A \to V$, when any two tuples $t, u \in r$ that agree on every attribute of $X$ also agree on
every attribute of $Y$. -/
def HoldsIn {V : Type*} (f : FD A) (r : Set (A → V)) : Prop :=
  ∀ t ∈ r, ∀ u ∈ r, (∀ a ∈ f.lhs, t a = u a) → ∀ a ∈ f.rhs, t a = u a

end FD

/-- **A relation satisfies a set of dependencies.** Let $F$ be a finite set of functional
dependencies over attributes $A$, and let $r$ be a relation, given as a set of tuples $A \to V$
with values in a type $V$. Then $r$ satisfies $F$ when every dependency of $F$ holds in $r$. -/
def Satisfies {V : Type*} (r : Set (A → V)) (F : Finset (FD A)) : Prop := ∀ f ∈ F, f.HoldsIn r

/-- **Entailment of functional dependencies.** Let $A$ be a type of attributes. A finite set $F$
of functional dependencies on $A$ entails a functional dependency $f$ on $A$ when, for every
type $V$ and every relation $r$ with values in $V$ (a set of tuples $A \to V$) that satisfies
$F$, the dependency $f$ holds in $r$. -/
def Entails (F : Finset (FD A)) (f : FD A) : Prop :=
  ∀ (V : Type) (r : Set (A → V)), Satisfies r F → f.HoldsIn r

variable [DecidableEq A]

/-- **Derivability with Armstrong's axioms.** Let $F$ be a finite set of functional
dependencies over a set $A$ of attributes. Derivability from $F$ is the least property of
functional dependencies over $A$ such that, for all finite sets $X$, $Y$, $Z$ of attributes:
every dependency of $F$ is derivable; $X \to Y$ is derivable whenever $Y \subseteq X$
(reflexivity); if $X \to Y$ is derivable, then so is $X \cup Z \to Y \cup Z$ (augmentation);
and if $X \to Y$ and $Y \to Z$ are derivable, then so is $X \to Z$ (transitivity). -/
inductive Derives (F : Finset (FD A)) : FD A → Prop
  /-- The dependencies of `F` are derivable. -/
  | mem {f : FD A} : f ∈ F → Derives F f
  /-- Reflexivity: `X → Y` whenever `Y ⊆ X`. -/
  | refl {X Y : Finset A} : Y ⊆ X → Derives F ⟨X, Y⟩
  /-- Augmentation: from `X → Y` derive `X ∪ Z → Y ∪ Z`. -/
  | augment {X Y : Finset A} (Z : Finset A) : Derives F ⟨X, Y⟩ → Derives F ⟨X ∪ Z, Y ∪ Z⟩
  /-- Transitivity: from `X → Y` and `Y → Z` derive `X → Z`. -/
  | trans {X Y Z : Finset A} : Derives F ⟨X, Y⟩ → Derives F ⟨Y, Z⟩ → Derives F ⟨X, Z⟩

namespace Derives

variable {F : Finset (FD A)}

/-- **Armstrong's axioms are sound**: a derivable dependency holds in every relation satisfying
`F`. -/
theorem sound {V : Type*} {r : Set (A → V)} (hr : Satisfies r F) :
    ∀ {f : FD A}, Derives F f → f.HoldsIn r
  | _, mem h => hr _ h
  | _, refl hYX => fun _ _ _ _ h a ha => h a (hYX ha)
  | _, augment Z h => fun t ht u hu hagree a ha => by
    rcases Finset.mem_union.mp ha with ha | ha
    · exact sound hr h t ht u hu (fun b hb => hagree b (Finset.mem_union_left _ hb)) a ha
    · exact hagree a (Finset.mem_union_right _ ha)
  | _, trans h₁ h₂ => fun t ht u hu hagree =>
    sound hr h₂ t ht u hu (sound hr h₁ t ht u hu hagree)

/-- **Decomposition rule.** Let $F$ be a finite set of functional dependencies and $X$, $Y$, $Z$
finite sets of attributes with $Z \subseteq Y$. If $X \to Y$ is derivable from $F$ with
Armstrong's axioms, then so is $X \to Z$. -/
theorem decompose {X Y Z : Finset A} (h : Derives F ⟨X, Y⟩) (hZ : Z ⊆ Y) : Derives F ⟨X, Z⟩ :=
  trans h (refl hZ)

/-- **Union rule.** Let $F$ be a finite set of functional dependencies and $X, Y, Z$ finite sets
of attributes. If $X \to Y$ and $X \to Z$ are derivable from $F$ with Armstrong's axioms, then so
is $X \to Y \cup Z$. -/
theorem union {X Y Z : Finset A} (hY : Derives F ⟨X, Y⟩) (hZ : Derives F ⟨X, Z⟩) :
    Derives F ⟨X, Y ∪ Z⟩ := by
  have h₁ := augment X hZ
  rw [Finset.union_self, Finset.union_comm] at h₁
  have h₂ := augment Z hY
  exact trans h₁ h₂

/-- **Pseudotransitivity rule.** Let $F$ be a finite set of functional dependencies and
$X, Y, W, Z$ finite sets of attributes. If $X \to Y$ and $Y \cup W \to Z$ are derivable from $F$
with Armstrong's axioms, then so is $X \cup W \to Z$. -/
theorem pseudotrans {X Y W Z : Finset A} (h₁ : Derives F ⟨X, Y⟩) (h₂ : Derives F ⟨Y ∪ W, Z⟩) :
    Derives F ⟨X ∪ W, Z⟩ :=
  trans (augment W h₁) h₂

/-- **Adding the left side to the right side.** Let $F$ be a finite set of functional dependencies
and $X, Y$ finite sets of attributes. If $X \to Y$ is derivable from $F$ with Armstrong's axioms,
then so is $X \to X \cup Y$. -/
theorem union_left {X Y : Finset A} (h : Derives F ⟨X, Y⟩) : Derives F ⟨X, X ∪ Y⟩ :=
  union (refl subset_rfl) h

private theorem biUnion {ι : Type*} {X : Finset A} (s : Finset ι)
    (g : ι → Finset A) (h : ∀ i ∈ s, Derives F ⟨X, g i⟩) : Derives F ⟨X, s.biUnion g⟩ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact refl (Finset.empty_subset _)
  | insert i s hi ih =>
    rw [Finset.biUnion_insert]
    exact union (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Derives

/-! ### The attribute-closure algorithm -/

/-- **One round of the attribute-closure algorithm.** For a finite set $F$ of functional
dependencies and a finite set $Y$ of attributes, one closure round returns $Y$ together with the
right side of every dependency of $F$ whose left side is contained in $Y$, that is, the set
$Y \cup \bigcup \{R : (L \to R) \in F,\ L \subseteq Y\}$. -/
def closureStep (F : Finset (FD A)) (Y : Finset A) : Finset A :=
  Y ∪ (F.filter fun f => f.lhs ⊆ Y).biUnion FD.rhs

/-- **Iterated closure rounds.** Let $F$ be a finite set of functional dependencies, $n$ a
natural number and $Y$ a finite set of attributes. The loop returns $Y$ if $n = 0$ or if one
closure round for $F$ leaves $Y$ unchanged; otherwise it returns the loop with $n - 1$ rounds
started from the result of one closure round applied to $Y$. Thus it repeats closure rounds from
$Y$ until nothing changes, for at most $n$ rounds. -/
def closureLoop (F : Finset (FD A)) : ℕ → Finset A → Finset A
  | 0, Y => Y
  | n + 1, Y => if closureStep F Y = Y then Y else closureLoop F n (closureStep F Y)

variable [Fintype A]

/-- **Attribute closure.** Let $A$ be a finite set of attributes, $F$ a finite set of functional
dependencies over $A$ and $X \subseteq A$. The attribute closure $X^+$ of $X$ under $F$ is
computed by the closure algorithm: starting from $X$, repeat closure rounds (each adds the right
side of every dependency of $F$ whose left side is already included) until nothing changes, for
at most $|A|$ rounds. -/
def attrClosure (F : Finset (FD A)) (X : Finset A) : Finset A :=
  closureLoop F (Fintype.card A) X

omit [Fintype A] in
private theorem subset_closureStep (F : Finset (FD A)) (Y : Finset A) : Y ⊆ closureStep F Y :=
  Finset.subset_union_left

omit [Fintype A] in
private theorem subset_closureLoop (F : Finset (FD A)) :
    ∀ (n : ℕ) (Y : Finset A), Y ⊆ closureLoop F n Y
  | 0, _ => subset_rfl
  | n + 1, Y => by
    simp only [closureLoop]
    split_ifs
    · exact subset_rfl
    · exact (subset_closureStep F Y).trans (subset_closureLoop F n _)

omit [Fintype A] in
private theorem derives_closureStep {F : Finset (FD A)} {X Y : Finset A}
    (h : Derives F ⟨X, Y⟩) : Derives F ⟨X, closureStep F Y⟩ := by
  refine h.union (Derives.biUnion _ _ fun g hg => ?_)
  obtain ⟨hgF, hgY⟩ := Finset.mem_filter.mp hg
  exact Derives.trans (h.decompose hgY) (Derives.mem hgF)

omit [Fintype A] in
private theorem derives_closureLoop {F : Finset (FD A)} {X : Finset A} :
    ∀ (n : ℕ) {Y : Finset A}, Derives F ⟨X, Y⟩ → Derives F ⟨X, closureLoop F n Y⟩
  | 0, _, h => h
  | n + 1, Y, h => by
    simp only [closureLoop]
    split_ifs
    · exact h
    · exact derives_closureLoop n (derives_closureStep h)

/-- After enough rounds the loop reaches a fixed point of `closureStep`. -/
private theorem closureStep_closureLoop (F : Finset (FD A)) :
    ∀ (n : ℕ) (Y : Finset A), Fintype.card A ≤ n + Y.card →
      closureStep F (closureLoop F n Y) = closureLoop F n Y
  | 0, Y, h => by
    have hY : Y = Finset.univ := Finset.eq_univ_of_card Y (le_antisymm (Finset.card_le_univ Y)
      (by simpa using h))
    subst hY
    exact Finset.eq_univ_iff_forall.mpr fun a => subset_closureStep F _ (Finset.mem_univ a)
  | n + 1, Y, h => by
    simp only [closureLoop]
    split_ifs with hfix
    · exact hfix
    · have hlt : Y.card < (closureStep F Y).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_closureStep F Y,
          fun h => hfix h.symm⟩)
      exact closureStep_closureLoop F n _ (by omega)

/-- **The attribute closure is a fixed point of a closure round.** Let $A$ be a finite set of
attributes, $F$ a finite set of functional dependencies over $A$ and $X \subseteq A$. Applying
one closure round for $F$ to the attribute closure $X^+$ of $X$ under $F$ returns $X^+$. -/
theorem closureStep_attrClosure (F : Finset (FD A)) (X : Finset A) :
    closureStep F (attrClosure F X) = attrClosure F X :=
  closureStep_closureLoop F _ X (Nat.le_add_right _ _)

theorem subset_attrClosure (F : Finset (FD A)) (X : Finset A) : X ⊆ attrClosure F X :=
  subset_closureLoop F _ X

/-- **The attribute closure is closed under the dependencies.** Let $F$ be a finite set of
functional dependencies over a finite set of attributes, $X$ a set of attributes and $X^+$ its
attribute closure under $F$. For every dependency $Y \to Z$ in $F$ with $Y \subseteq X^+$, also
$Z \subseteq X^+$. -/
theorem rhs_subset_attrClosure {F : Finset (FD A)} {X : Finset A} {g : FD A} (hg : g ∈ F)
    (hlhs : g.lhs ⊆ attrClosure F X) : g.rhs ⊆ attrClosure F X := by
  rw [← closureStep_attrClosure F X]
  intro a ha
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr
    ⟨hg, hlhs⟩, ha⟩)

theorem derives_attrClosure (F : Finset (FD A)) (X : Finset A) :
    Derives F ⟨X, attrClosure F X⟩ :=
  derives_closureLoop _ (Derives.refl subset_rfl)

/-- **Closure witness relation.** Let $A$ be a finite set of attributes, $F$ a finite set of
functional dependencies over $A$ and $X \subseteq A$. The closure witness relation for $X$ is the
relation with values in $\{\mathrm{true}, \mathrm{false}\}$ whose tuples are the tuple that is
$\mathrm{true}$ on every attribute and the tuple that is $\mathrm{true}$ exactly on the attribute
closure $X^+$ of $X$ under $F$. These two tuples agree exactly on $X^+$, and they coincide when
$X^+ = A$. -/
def closureWitnessRelation (F : Finset (FD A)) (X : Finset A) : Finset (A → Bool) :=
  {fun _ => true, fun a => decide (a ∈ attrClosure F X)}

/-- **The closure witness satisfies the dependencies.** Let $F$ be a finite set of functional
dependencies on a finite set of attributes $A$. For every set $X \subseteq A$ of attributes, the
closure witness relation for $X$ under $F$ satisfies $F$. -/
theorem holdsIn_closureWitnessRelation (F : Finset (FD A)) (X : Finset A) :
    Satisfies (↑(closureWitnessRelation F X) : Set (A → Bool)) F := by
  have key : ∀ g ∈ F, (∀ a ∈ g.lhs, true = decide (a ∈ attrClosure F X)) →
      ∀ a ∈ g.rhs, true = decide (a ∈ attrClosure F X) := fun g hg h a ha => by
    have hsub : g.lhs ⊆ attrClosure F X := fun b hb => by simpa using h b hb
    simpa using rhs_subset_attrClosure hg hsub ha
  intro g hg t ht u hu hagree
  simp only [closureWitnessRelation, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ht hu
  rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
  · exact fun _ _ => rfl
  · exact key g hg hagree
  · exact fun a ha => (key g hg (fun b hb => (hagree b hb).symm) a ha).symm
  · exact fun _ _ => rfl

/-- **The closure algorithm decides derivability.** Let $A$ be a finite set of attributes, $F$ a
finite set of functional dependencies over $A$ and $X, Y \subseteq A$. Then $X \to Y$ is
derivable from $F$ with Armstrong's axioms if and only if $Y \subseteq X^+$, where $X^+$ is the
attribute closure of $X$ under $F$ computed by the closure algorithm. -/
theorem derives_iff_subset_attrClosure {F : Finset (FD A)} {X Y : Finset A} :
    Derives F ⟨X, Y⟩ ↔ Y ⊆ attrClosure F X := by
  constructor
  · intro h a ha
    have := h.sound (holdsIn_closureWitnessRelation F X) (fun _ => true)
      (by simp [closureWitnessRelation]) (fun a => decide (a ∈ attrClosure F X))
      (by simp [closureWitnessRelation])
      (fun b hb => by simpa using subset_attrClosure F X hb) a ha
    simpa using this
  · exact (derives_attrClosure F X).decompose

/-- **The closure algorithm computes the attribute closure.** Let $F$ be a finite set of
functional dependencies over a finite set of attributes and $X$ a set of attributes. An
attribute $a$ lies in the attribute closure $X^+$ of $X$ under $F$, as computed by the closure
algorithm, if and only if the dependency $X \to \{a\}$ is derivable from $F$ with Armstrong's
axioms. -/
theorem mem_attrClosure {F : Finset (FD A)} {X : Finset A} {a : A} :
    a ∈ attrClosure F X ↔ Derives F ⟨X, {a}⟩ := by
  rw [derives_iff_subset_attrClosure, Finset.singleton_subset_iff]

instance (F : Finset (FD A)) (f : FD A) : Decidable (Derives F f) :=
  decidable_of_iff (f.rhs ⊆ attrClosure F f.lhs) derives_iff_subset_attrClosure.symm

omit [Fintype A] in
/-- **Completeness of Armstrong's axioms, two-tuple form.** Let $A$ be a finite set of
attributes, $F$ a finite set of functional dependencies over $A$ and $f$ a functional
dependency over $A$. If $f$ holds in every relation with values in
$\{\mathrm{true}, \mathrm{false}\}$ that has at most two tuples and satisfies every dependency
of $F$, then $f$ is derivable from $F$ with Armstrong's axioms. -/
theorem derives_of_forall_two_tuple [Finite A] {F : Finset (FD A)} {f : FD A}
    (h : ∀ r : Finset (A → Bool), r.card ≤ 2 → Satisfies (↑r : Set (A → Bool)) F →
      f.HoldsIn (↑r : Set (A → Bool))) : Derives F f := by
  cases nonempty_fintype A
  obtain ⟨X, Y⟩ := f
  rw [derives_iff_subset_attrClosure]
  intro a ha
  have := h (closureWitnessRelation F X) (Finset.card_le_two) (holdsIn_closureWitnessRelation F X)
    (fun _ => true) (by simp [closureWitnessRelation]) (fun a => decide (a ∈ attrClosure F X))
    (by simp [closureWitnessRelation]) (fun b hb => by simpa using subset_attrClosure F X hb) a ha
  simpa using this

omit [Fintype A] in
/-- **Armstrong's theorem.** Let $A$ be a finite set of attributes, $F$ a finite set of
functional dependencies over $A$ and $f$ a functional dependency over $A$. Then $f$ is
derivable from $F$ with Armstrong's axioms if and only if $F$ entails $f$, that is, $f$ holds
in every relation (with values in any type) that satisfies every dependency of $F$. In other
words, Armstrong's axioms are sound and complete for functional dependencies. -/
theorem derives_iff_entails [Finite A] {F : Finset (FD A)} {f : FD A} :
    Derives F f ↔ Entails F f :=
  ⟨fun h _ _ hr => h.sound hr, fun h => derives_of_forall_two_tuple fun r _ hr => h Bool r hr⟩

/-! ### Keys -/

/-- **Superkey.** Let $F$ be a finite set of functional dependencies over a finite set of
attributes $A$. A set of attributes $K$ is a superkey for $F$ when the dependency $K \to A$ is
derivable from $F$ with Armstrong's axioms, that is, $K$ determines every attribute. -/
def IsSuperkey (F : Finset (FD A)) (K : Finset A) : Prop := Derives F ⟨K, Finset.univ⟩

/-- **Candidate key.** Let $F$ be a finite set of functional dependencies on a finite set of
attributes $A$. A set $K \subseteq A$ of attributes is a candidate key for $F$ when $K$ is a
superkey for $F$ and no proper subset of $K$ is a superkey for $F$. -/
def IsCandidateKey (F : Finset (FD A)) (K : Finset A) : Prop :=
  IsSuperkey F K ∧ ∀ K' ⊂ K, ¬ IsSuperkey F K'

theorem isSuperkey_iff_attrClosure {F : Finset (FD A)} {K : Finset A} :
    IsSuperkey F K ↔ attrClosure F K = Finset.univ := by
  rw [IsSuperkey, derives_iff_subset_attrClosure, Finset.univ_subset_iff]

instance (F : Finset (FD A)) (K : Finset A) : Decidable (IsSuperkey F K) :=
  decidable_of_iff _ isSuperkey_iff_attrClosure.symm

/-- **Supersets of superkeys are superkeys.** Let $F$ be a finite set of functional dependencies
over a finite set of attributes. If $K$ is a superkey for $F$ and $K \subseteq K'$, then $K'$ is a
superkey for $F$. -/
theorem IsSuperkey.mono {F : Finset (FD A)} {K K' : Finset A} (h : IsSuperkey F K)
    (hKK' : K ⊆ K') : IsSuperkey F K' :=
  Derives.trans (Derives.refl hKK') h

/-- **Tuples that agree on a superkey are equal.** Let $F$ be a finite set of functional
dependencies on a finite set of attributes $A$, and let $K$ be a superkey for $F$. Let $V$ be a
type of values. If a relation $r$, a set of tuples $A \to V$, satisfies $F$, then any two tuples
$t, u \in r$ that agree on every attribute of $K$ are equal. -/
theorem IsSuperkey.eq_of_agree {V : Type*} {F : Finset (FD A)} {K : Finset A}
    (h : IsSuperkey F K) {r : Set (A → V)} (hr : Satisfies r F) {t u : A → V} (ht : t ∈ r)
    (hu : u ∈ r) (hagree : ∀ a ∈ K, t a = u a) : t = u :=
  funext fun a => h.sound hr t ht u hu hagree a (Finset.mem_univ a)

/-- **Candidate keys are the superkeys minimal under single removals.** Let $F$ be a finite set
of functional dependencies on a finite set of attributes $A$. A set $K \subseteq A$ of attributes
is a candidate key for $F$ if and only if $K$ is a superkey for $F$ and, for every $a \in K$, the
set $K \setminus \{a\}$ is not a superkey for $F$. -/
theorem isCandidateKey_iff {F : Finset (FD A)} {K : Finset A} :
    IsCandidateKey F K ↔ IsSuperkey F K ∧ ∀ a ∈ K, ¬ IsSuperkey F (K.erase a) := by
  constructor
  · rintro ⟨hK, hmin⟩
    exact ⟨hK, fun a ha => hmin _ (Finset.erase_ssubset ha)⟩
  · rintro ⟨hK, hmin⟩
    refine ⟨hK, fun K' hK' hsk => ?_⟩
    obtain ⟨a, haK, haK'⟩ := Finset.exists_of_ssubset hK'
    exact hmin a haK (hsk.mono fun b hb => Finset.mem_erase.mpr
      ⟨fun hba => haK' (hba ▸ hb), hK'.subset hb⟩)

instance (F : Finset (FD A)) (K : Finset A) : Decidable (IsCandidateKey F K) :=
  decidable_of_iff _ isCandidateKey_iff.symm

/-- **Shrinking a key along a list.** Let $F$ be a finite set of functional dependencies over a
finite set of attributes. Given a list $l$ of attributes and a set of attributes $K$, go through
$l$ in order and, for each attribute $a$, remove $a$ from the current set whenever the attribute
closure under $F$ of the current set without $a$ is the set of all attributes (that is, the set
without $a$ is still a superkey); the result is the set reached at the end of the list. -/
def shrinkKey (F : Finset (FD A)) : List A → Finset A → Finset A
  | [], K => K
  | a :: l, K =>
    shrinkKey F l (if attrClosure F (K.erase a) = Finset.univ then K.erase a else K)

/-- **Key-finding algorithm.** Let $F$ be a finite set of functional dependencies on a finite set
of attributes $A$, and let $l$ be a list of attributes. The key-finding algorithm starts from the
set $K = A$ of all attributes and goes through $l$ in order: for each listed attribute $a$, it
replaces $K$ by $K \setminus \{a\}$ when the attribute closure of $K \setminus \{a\}$ under $F$ is
all of $A$, and keeps $K$ otherwise. It returns the final set $K$. -/
def findKey (F : Finset (FD A)) (l : List A) : Finset A := shrinkKey F l Finset.univ

private theorem shrinkKey_spec (F : Finset (FD A)) :
    ∀ (l : List A) (K : Finset A), IsSuperkey F K →
      IsSuperkey F (shrinkKey F l K) ∧ shrinkKey F l K ⊆ K ∧
        ∀ a ∈ l, a ∈ shrinkKey F l K → ¬ IsSuperkey F ((shrinkKey F l K).erase a)
  | [], K, hK => ⟨hK, subset_rfl, fun _ ha => absurd ha List.not_mem_nil⟩
  | a :: l, K, hK => by
    set K₁ := if attrClosure F (K.erase a) = Finset.univ then K.erase a else K with hK₁
    have hK₁sk : IsSuperkey F K₁ := by
      rw [hK₁]
      split_ifs with h
      · exact isSuperkey_iff_attrClosure.mpr h
      · exact hK
    have hK₁sub : K₁ ⊆ K := by
      rw [hK₁]
      split_ifs
      · exact Finset.erase_subset a K
      · exact subset_rfl
    obtain ⟨hR, hRsub, hRmin⟩ := shrinkKey_spec F l K₁ hK₁sk
    refine ⟨hR, hRsub.trans hK₁sub, fun b hb hbR => ?_⟩
    simp only [shrinkKey] at hbR ⊢
    rcases List.mem_cons.mp hb with rfl | hb
    · intro hsk
      have hbK₁ : b ∈ K₁ := hRsub hbR
      rw [hK₁] at hbK₁
      split_ifs at hbK₁ with h
      · exact Finset.notMem_erase b K hbK₁
      · exact h (isSuperkey_iff_attrClosure.mp (hsk.mono (Finset.erase_subset_erase b
          (hRsub.trans hK₁sub))))
    · exact hRmin b hb hbR

/-- **The key-finding algorithm returns a candidate key.** Let $F$ be a finite set of functional
dependencies on a finite set of attributes $A$, and let $l$ be a list in which every attribute
of $A$ occurs. Then the output of the key-finding algorithm on $F$ and $l$, which starts from the
set of all attributes and goes through $l$ in order, removing each listed attribute whenever
what remains is still a superkey, is a candidate key for $F$. -/
theorem findKey_isCandidateKey (F : Finset (FD A)) {l : List A} (hl : ∀ a, a ∈ l) :
    IsCandidateKey F (findKey F l) := by
  obtain ⟨hR, -, hRmin⟩ := shrinkKey_spec F l Finset.univ (Derives.refl subset_rfl)
  exact isCandidateKey_iff.mpr ⟨hR, fun a ha => hRmin a (hl a) ha⟩

/-- **Every superkey contains a candidate key.** Let $F$ be a finite set of functional
dependencies on a finite set of attributes $A$. Every superkey $K$ for $F$ has a subset
$K' \subseteq K$ that is a candidate key for $F$. -/
theorem exists_isCandidateKey_subset {F : Finset (FD A)} {K : Finset A} (hK : IsSuperkey F K) :
    ∃ K' ⊆ K, IsCandidateKey F K' := by
  obtain ⟨hR, hRsub, hRmin⟩ := shrinkKey_spec F Finset.univ.toList K hK
  exact ⟨_, hRsub, isCandidateKey_iff.mpr ⟨hR, fun a ha => hRmin a (by simp) ha⟩⟩

end Cslib.Databases
