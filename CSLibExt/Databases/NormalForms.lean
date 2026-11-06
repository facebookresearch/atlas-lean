/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.RelationalAlgebra
public import CSLibExt.Databases.FunctionalDependencies
public import Mathlib.Data.Finset.Powerset

/-!
# Lossless decompositions and normal forms

Relations are those of `RelationalAlgebra` (finite sets of tuples `A → Option D` over a schema)
and dependencies those of `FunctionalDependencies`. A decomposition of a schema into a list of
schemes is **lossless** when every relation satisfying the dependencies is the natural join of
its projections onto the schemes (`joinProjections`).

* `join_project_eq_of_holdsIn` (**Heath's theorem**): if `R₁ ∩ R₂ → R₁` holds in a relation `r`
  over `R₁ ∪ R₂`, then `r = π_{R₁} r ⋈ π_{R₂} r`.
* `losslessJoin_iff`: a decomposition of all attributes into two schemes `R₁`, `R₂` is lossless for
  `F` exactly when `F` derives `R₁ ∩ R₂ → R₁` or `R₁ ∩ R₂ → R₂` (for any value type with two
  distinct values); the "if" direction holds for decompositions of any schema. On a schema `S`,
  "satisfying `F`" means satisfying the dependencies derivable from `F` between attributes of `S`
  (`SatisfiesOn`, the projection of `F⁺` onto `S`).
* **Boyce–Codd normal form**: `IsBCNF F S` says every nontrivial dependency `X → Y` derivable from
  `F` with `X, Y ⊆ S` has `X` a superkey of `S`; `isBCNF_iff` reduces it to the absence of a
  violating `X ⊆ S`, which makes it decidable. `bcnfDecomposition F l S` is the BCNF decomposition
  algorithm: while a scheme has a violation `X` (found by enumerating the subsets of the attributes
  listed in `l`), split it into `X⁺ ∩ S` and `S \ (X⁺ \ X)`.
  `bcnfDecomposition_lossless`: the decomposition is lossless, by Heath's theorem at every split;
  `isBCNF_of_mem_bcnfDecomposition`: when `l` lists all attributes, every output scheme is in
  BCNF.
* **Synthesis** (the 3NF synthesis algorithm of Bernstein): `synthesize G K` has one scheme
  `lhs ∪ rhs` for each dependency of a cover `G` of `F`, plus a candidate key `K` of all
  attributes. `synthesize_lossless` and `synthesize_dependencyPreserving`: it is lossless and
  dependency-preserving (`DependencyPreserving`: `F` is derivable from the projections of the
  derivable dependencies onto the schemes). That the schemes are in third normal form needs `G` to
  be a minimal cover and is not formalized here.

## References

* I. J. Heath, *Unacceptable file operations in a relational data base*, ACM SIGFIDET Workshop
  1971.
* P. A. Bernstein, *Synthesizing third normal form relations from functional dependencies*, ACM
  Transactions on Database Systems 1(4), 1976.
* J. Biskup, U. Dayal and P. A. Bernstein, *Synthesizing independent database schemas*, SIGMOD
  1979 (adding a key scheme makes the synthesis lossless).
* S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995,
  Section 11.2 (normal forms).
-/

@[expose] public section

namespace Cslib.Databases

open Tuple

variable {A D : Type*} [Fintype A] [DecidableEq A] [DecidableEq D]

omit [Fintype A] [DecidableEq D] in
private theorem restrict_eq_restrict_iff {T : Finset A} {t u : Tuple A D} :
    t.restrict T = u.restrict T ↔ ∀ a ∈ T, t a = u a := by
  constructor
  · intro h a ha
    simpa [ha] using congrFun h a
  · intro h
    funext a
    by_cases ha : a ∈ T <;> simp [ha, h a]

private theorem mem_project {T : Finset A} {r : Finset (Tuple A D)} {t : Tuple A D} :
    t ∈ project T r ↔ ∃ u ∈ r, u.restrict T = t := by
  simp [project]

private theorem project_self {S : Finset A} {r : Finset (Tuple A D)} (hr : IsOver S r) :
    project S r = r := by
  ext t
  rw [mem_project]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rwa [(hr u hu).restrict_self]
  · intro ht
    exact ⟨t, ht, (hr t ht).restrict_self⟩

/-! ### Heath's theorem -/

/-- **Heath's theorem**: if the dependency `R₁ ∩ R₂ → R₁` holds in a relation `r` over
`R₁ ∪ R₂`, then `r` is the natural join of its projections onto `R₁` and `R₂`. -/
theorem join_project_eq_of_holdsIn {R₁ R₂ : Finset A} {r : Finset (Tuple A D)}
    (hr : IsOver (R₁ ∪ R₂) r) (h : FD.HoldsIn ⟨R₁ ∩ R₂, R₁⟩ (↑r : Set (Tuple A D))) :
    join (project R₁ r) (project R₂ r) = r := by
  have h₁ : IsOver R₁ (project R₁ r) := isOver_project hr Finset.subset_union_left
  have h₂ : IsOver R₂ (project R₂ r) := isOver_project hr Finset.subset_union_right
  ext t
  rw [mem_join_iff h₁ h₂]
  constructor
  · rintro ⟨ht, hu, hv⟩
    obtain ⟨u, hu, hut⟩ := mem_project.mp hu
    obtain ⟨v, hv, hvt⟩ := mem_project.mp hv
    have hut' := restrict_eq_restrict_iff.mp hut
    have hvt' := restrict_eq_restrict_iff.mp hvt
    have huv : ∀ a ∈ R₁, u a = v a := h u hu v hv fun a ha => by
      obtain ⟨ha₁, ha₂⟩ := Finset.mem_inter.mp ha
      rw [hut' a ha₁, hvt' a ha₂]
    have htv : t = v := by
      funext a
      by_cases ha₁ : a ∈ R₁
      · rw [← hut' a ha₁, huv a ha₁]
      · by_cases ha₂ : a ∈ R₂
        · rw [hvt' a ha₂]
        · have hnot : a ∉ R₁ ∪ R₂ := by simp [ha₁, ha₂]
          rw [ht.eq_none hnot, (hr v hv).eq_none hnot]
    exact htv ▸ hv
  · intro ht
    exact ⟨hr t ht, mem_project.mpr ⟨t, ht, rfl⟩, mem_project.mpr ⟨t, ht, rfl⟩⟩

/-- **Satisfying a set of dependencies on a scheme.** A relation $r$ satisfies a finite set $F$ of
functional dependencies on a set $S$ of attributes when every dependency $X \to Y$ with
$X, Y \subseteq S$ that is derivable from $F$ by Armstrong's axioms holds in $r$. -/
def SatisfiesOn (F : Finset (FD A)) (S : Finset A) (r : Finset (Tuple A D)) : Prop :=
  ∀ X ⊆ S, ∀ Y ⊆ S, Derives F ⟨X, Y⟩ → FD.HoldsIn ⟨X, Y⟩ (↑r : Set (Tuple A D))

omit [Fintype A] [DecidableEq D] in
theorem Satisfies.satisfiesOn {F : Finset (FD A)} {r : Finset (Tuple A D)}
    (h : Satisfies (↑r : Set (Tuple A D)) F) (S : Finset A) : SatisfiesOn F S r :=
  fun _ _ _ _ hXY => hXY.sound h

instance (F : Finset (FD A)) (S : Finset A) (r : Finset (Tuple A D)) :
    Decidable (SatisfiesOn F S r) :=
  decidable_of_iff (∀ X ∈ S.powerset, ∀ Y ∈ S.powerset, Derives F ⟨X, Y⟩ →
      ∀ t ∈ r, ∀ u ∈ r, (∀ a ∈ X, t a = u a) → ∀ a ∈ Y, t a = u a)
    (by simp [SatisfiesOn, FD.HoldsIn])

theorem SatisfiesOn.project {F : Finset (FD A)} {S T : Finset A} {r : Finset (Tuple A D)}
    (h : SatisfiesOn F S r) (hTS : T ⊆ S) : SatisfiesOn F T (project T r) := by
  intro X hXT Y hYT hXY t ht u hu hagree a ha
  obtain ⟨t', ht', rfl⟩ := mem_project.mp ht
  obtain ⟨u', hu', rfl⟩ := mem_project.mp hu
  have hagree' : ∀ b ∈ X, t' b = u' b := fun b hb => by
    simpa [hXT hb] using hagree b hb
  simpa [hYT ha] using h X (hXT.trans hTS) Y (hYT.trans hTS) hXY t' ht' u' hu' hagree' a ha

variable (D) in
/-- **Lossless decomposition into two schemes.** Let $F$ be a finite set of functional
dependencies, let $R_1$ and $R_2$ be finite sets of attributes, and let $D$ be a type of values.
The decomposition of $R_1 \cup R_2$ into $R_1$ and $R_2$ is lossless for $F$ with values in $D$
when every relation $r$ over $R_1 \cup R_2$ with values in $D$ that satisfies $F$ on
$R_1 \cup R_2$ (every dependency $X \to Y$ with $X, Y \subseteq R_1 \cup R_2$ that is derivable
from $F$ by Armstrong's axioms holds in $r$) is the natural join of its projections:
$\pi_{R_1}(r) \bowtie \pi_{R_2}(r) = r$. -/
def LosslessJoin (F : Finset (FD A)) (R₁ R₂ : Finset A) : Prop :=
  ∀ r : Finset (Tuple A D), IsOver (R₁ ∪ R₂) r → SatisfiesOn F (R₁ ∪ R₂) r →
    join (project R₁ r) (project R₂ r) = r

/-- **Lossless binary decompositions from derivable dependencies.** Let $F$ be a finite set of
functional dependencies and let $R_1$, $R_2$ be sets of attributes. If $R_1 \cap R_2 \to R_1$ or
$R_1 \cap R_2 \to R_2$ is derivable from $F$ by Armstrong's axioms, then for every value type $D$
the decomposition of $R_1 \cup R_2$ into $R_1$ and $R_2$ is lossless for $F$ with values in $D$. -/
theorem losslessJoin_of_derives {F : Finset (FD A)} {R₁ R₂ : Finset A}
    (h : Derives F ⟨R₁ ∩ R₂, R₁⟩ ∨ Derives F ⟨R₁ ∩ R₂, R₂⟩) : LosslessJoin D F R₁ R₂ := by
  intro r hr hF
  have hX : R₁ ∩ R₂ ⊆ R₁ ∪ R₂ := Finset.inter_subset_left.trans Finset.subset_union_left
  rcases h with h | h
  · exact join_project_eq_of_holdsIn hr (hF _ hX _ Finset.subset_union_left h)
  · rw [join_comm]
    have h' := hF _ hX _ Finset.subset_union_right h
    rw [Finset.union_comm] at hr
    rw [Finset.inter_comm] at h'
    exact join_project_eq_of_holdsIn hr h'

/-- **Converse of the lossless-join test for two schemes.** Let $F$ be a set of functional
dependencies, let $R_1$ and $R_2$ be schemes whose union is the set of all attributes, and let
$D$ be a value type containing at least two distinct elements. If the decomposition of
$R_1 \cup R_2$ into $R_1$ and $R_2$ is lossless for $F$ with values in $D$, then $F$ derives
$R_1 \cap R_2 \to R_1$ or $R_1 \cap R_2 \to R_2$. -/
theorem derives_of_losslessJoin {F : Finset (FD A)} {R₁ R₂ : Finset A} {d₀ d₁ : D}
    (hd : d₀ ≠ d₁) (hR : R₁ ∪ R₂ = Finset.univ) (h : LosslessJoin D F R₁ R₂) :
    Derives F ⟨R₁ ∩ R₂, R₁⟩ ∨ Derives F ⟨R₁ ∩ R₂, R₂⟩ := by
  set C := attrClosure F (R₁ ∩ R₂)
  simp only [derives_iff_subset_attrClosure]
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨c, hcR₁, hcC⟩, ⟨b, hbR₂, hbC⟩⟩ :=
    And.intro (Finset.not_subset.mp hcon.1) (Finset.not_subset.mp hcon.2)
  -- two tuples over all attributes that agree exactly on the closure `C`
  let t₀ : Tuple A D := fun _ => some d₀
  let t₁ : Tuple A D := fun a => if a ∈ C then some d₀ else some d₁
  let m : Tuple A D := fun a => if a ∈ R₁ then some d₀ else t₁ a
  have hagree : ∀ a, t₀ a = t₁ a ↔ a ∈ C := fun a => by
    by_cases ha : a ∈ C <;> simp [t₀, t₁, ha, hd]
  have hover : ∀ t : Tuple A D, (∀ a, (t a).isSome) → t.IsOver (R₁ ∪ R₂) := fun t ht a => by
    simp [hR, ht a]
  have hr : IsOver (R₁ ∪ R₂) ({t₀, t₁} : Finset (Tuple A D)) := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hover _ fun _ => rfl
    · exact hover _ fun a => by by_cases ha : a ∈ C <;> simp [t₁, ha]
  have hF : Satisfies (↑({t₀, t₁} : Finset (Tuple A D)) : Set (Tuple A D)) F := by
    intro g hg t ht u hu hlhs a ha
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ht hu
    have key : (∀ a ∈ g.lhs, t₀ a = t₁ a) → t₀ a = t₁ a := fun hl =>
      (hagree a).mpr (rhs_subset_attrClosure hg (fun b hb => (hagree b).mp (hl b hb)) ha)
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
    · rfl
    · exact key hlhs
    · exact (key fun b hb => (hlhs b hb).symm).symm
    · rfl
  have hmem : m ∈ join (project R₁ {t₀, t₁}) (project R₂ {t₀, t₁}) := by
    rw [mem_join_iff (isOver_project hr Finset.subset_union_left)
      (isOver_project hr Finset.subset_union_right)]
    refine ⟨hover _ fun a => by by_cases ha : a ∈ R₁ <;> by_cases ha' : a ∈ C <;>
      simp [m, t₁, ha, ha'], mem_project.mpr ⟨t₀, by simp, ?_⟩, mem_project.mpr ⟨t₁, by simp, ?_⟩⟩
    · exact restrict_eq_restrict_iff.mpr fun a ha => by simp [m, t₀, ha]
    · refine restrict_eq_restrict_iff.mpr fun a ha => ?_
      by_cases ha₁ : a ∈ R₁
      · have : a ∈ C := subset_attrClosure F _ (Finset.mem_inter.mpr ⟨ha₁, ha⟩)
        simp [m, t₁, ha₁, this]
      · simp [m, ha₁]
  rw [h _ hr (hF.satisfiesOn _)] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hm | hm
  · have hbR₁ : b ∉ R₁ := fun hb₁ =>
      hbC (subset_attrClosure F _ (Finset.mem_inter.mpr ⟨hb₁, hbR₂⟩))
    have := congrFun hm b
    simp only [hbR₁, ↓reduceIte, ite_eq_left_iff, Option.some.injEq, hd.symm, imp_false,
      Decidable.not_not, m, t₁, t₀] at this
    exact hbC this
  · have := congrFun hm c
    simp only [hcR₁, ↓reduceIte, left_eq_ite_iff, Option.some.injEq, hd, imp_false,
      Decidable.not_not, m, t₁] at this
    exact hcC this

/-- **Lossless binary decompositions.** Let $F$ be a finite set of functional dependencies, let
$R_1$ and $R_2$ be sets of attributes whose union is the set of all attributes, and suppose that
the value type $D$ has two distinct elements. Then the decomposition into $R_1$ and $R_2$ is
lossless for $F$ with values in $D$ if and only if $R_1 \cap R_2 \to R_1$ or
$R_1 \cap R_2 \to R_2$ is derivable from $F$ by Armstrong's axioms. -/
theorem losslessJoin_iff {F : Finset (FD A)} {R₁ R₂ : Finset A} {d₀ d₁ : D} (hd : d₀ ≠ d₁)
    (hR : R₁ ∪ R₂ = Finset.univ) :
    LosslessJoin D F R₁ R₂ ↔ Derives F ⟨R₁ ∩ R₂, R₁⟩ ∨ Derives F ⟨R₁ ∩ R₂, R₂⟩ :=
  ⟨derives_of_losslessJoin hd hR, losslessJoin_of_derives⟩

/-! ### Joins of projections -/

variable (D) in
/-- The relation containing only the empty tuple, the unit of the natural join. -/
def joinUnit : Finset (Tuple A D) := {fun _ => none}

omit [DecidableEq A] in
theorem join_joinUnit (r : Finset (Tuple A D)) : join r (joinUnit D) = r := by
  ext t
  simp only [mem_join, joinUnit, Finset.mem_singleton, exists_eq_left]
  constructor
  · rintro ⟨u, hu, -, rfl⟩
    have : merge u (fun _ => none) = u := by
      funext a
      simp only [merge]
      cases u a <;> rfl
    rwa [this]
  · intro ht
    refine ⟨t, ht, fun a => Or.inr (Or.inl rfl), ?_⟩
    funext a
    simp only [merge]
    cases t a <;> rfl

/-- **Join of the projections of a relation.** For a relation $r$ (a finite set of tuples) and a
list of schemes $S_1, \dots, S_n$, this is the natural join of the projections
$\pi_{S_1} r, \dots, \pi_{S_n} r$, computed as
$\pi_{S_1} r \bowtie (\pi_{S_2} r \bowtie (\cdots \bowtie (\pi_{S_n} r \bowtie U)))$, where $U$ is
the relation containing only the empty tuple; for the empty list it is $U$. -/
def joinProjections (l : List (Finset A)) (r : Finset (Tuple A D)) : Finset (Tuple A D) :=
  l.foldr (fun S acc => join (project S r) acc) (joinUnit D)

theorem joinProjections_cons (S : Finset A) (l : List (Finset A)) (r : Finset (Tuple A D)) :
    joinProjections (S :: l) r = join (project S r) (joinProjections l r) := rfl

theorem joinProjections_append (l₁ l₂ : List (Finset A)) (r : Finset (Tuple A D)) :
    joinProjections (l₁ ++ l₂) r = join (joinProjections l₁ r) (joinProjections l₂ r) := by
  induction l₁ with
  | nil => simp [joinProjections, join_comm (joinUnit D), join_joinUnit]
  | cons S l ih =>
    simp only [joinProjections, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, join_assoc]

theorem joinProjections_singleton {S : Finset A} {r : Finset (Tuple A D)} (hr : IsOver S r) :
    joinProjections [S] r = r := by
  simp [joinProjections, join_joinUnit, project_self hr]

theorem joinProjections_congr {R : Finset A} (l : List (Finset A)) (hl : ∀ S ∈ l, S ⊆ R)
    (r : Finset (Tuple A D)) : joinProjections l (project R r) = joinProjections l r := by
  induction l with
  | nil => rfl
  | cons S l ih =>
    simp only [joinProjections, List.foldr_cons] at ih ⊢
    rw [ih fun T hT => hl T (List.mem_cons_of_mem _ hT),
      project_project_of_subset (hl S List.mem_cons_self)]

/-- **Union of a list of schemes.** For a list $S_1, \dots, S_n$ of schemes (finite sets of
attributes), this is the union $S_1 \cup \dots \cup S_n$; for the empty list it is the empty set. -/
def schemaUnion (l : List (Finset A)) : Finset A := l.foldr (· ∪ ·) ∅

omit [Fintype A] in
private theorem mem_schemaUnion {l : List (Finset A)} {a : A} :
    a ∈ schemaUnion l ↔ ∃ S ∈ l, a ∈ S := by
  induction l with
  | nil => simp [schemaUnion]
  | cons S l ih =>
    simp only [schemaUnion, List.foldr_cons, Finset.mem_union] at ih ⊢
    rw [ih]
    simp

omit [Fintype A] in
private theorem subset_schemaUnion {l : List (Finset A)} {T : Finset A} (hT : T ∈ l) :
    T ⊆ schemaUnion l := fun _ ha => mem_schemaUnion.mpr ⟨T, hT, ha⟩

theorem isOver_joinProjections {r : Finset (Tuple A D)} {R : Finset A} (hr : IsOver R r) :
    ∀ l : List (Finset A), (∀ S ∈ l, S ⊆ R) → IsOver (schemaUnion l) (joinProjections l r)
  | [], _ => by
    intro t ht
    simp only [joinProjections, List.foldr_nil, joinUnit, Finset.mem_singleton] at ht
    subst ht
    intro a
    simp [schemaUnion]
  | S :: l, hl => isOver_join (isOver_project hr (hl S List.mem_cons_self))
      (isOver_joinProjections hr l fun T hT => hl T (List.mem_cons_of_mem _ hT))

/-- **Membership in a join of projections.** Let $r$ be a relation over a schema $R$ and let
$S_1, \dots, S_n$ be a list of schemes, each contained in $R$. A tuple $t$ belongs to the natural
join of the projections $\pi_{S_1} r, \dots, \pi_{S_n} r$ if and only if $t$ is a tuple over
$S_1 \cup \dots \cup S_n$ and, for every $i$, the restriction of $t$ to $S_i$ belongs to
$\pi_{S_i} r$. -/
theorem mem_joinProjections {r : Finset (Tuple A D)} {R : Finset A} (hr : IsOver R r) :
    ∀ (l : List (Finset A)), (∀ S ∈ l, S ⊆ R) → ∀ {t : Tuple A D},
      t ∈ joinProjections l r ↔ t.IsOver (schemaUnion l) ∧ ∀ S ∈ l, t.restrict S ∈ project S r
  | [], _, t => by
    simp only [joinProjections, List.foldr_nil, joinUnit, Finset.mem_singleton, schemaUnion,
      List.not_mem_nil, false_implies, implies_true, and_true]
    constructor
    · rintro rfl a
      simp
    · intro ht
      funext a
      exact ht.eq_none (Finset.notMem_empty a)
  | S :: l, hl, t => by
    have hlS : ∀ T ∈ l, T ⊆ R := fun T hT => hl T (List.mem_cons_of_mem _ hT)
    have hU : ∀ T ∈ l, T ⊆ schemaUnion l := fun T hT => subset_schemaUnion hT
    rw [joinProjections_cons, mem_join_iff (isOver_project hr (hl S List.mem_cons_self))
      (isOver_joinProjections hr l hlS)]
    change t.IsOver (S ∪ schemaUnion l) ∧ t.restrict S ∈ project S r ∧
        t.restrict (schemaUnion l) ∈ joinProjections l r ↔
      t.IsOver (S ∪ schemaUnion l) ∧ ∀ T ∈ S :: l, t.restrict T ∈ project T r
    rw [mem_joinProjections hr l hlS]
    constructor
    · rintro ⟨ht, hS, -, hl'⟩
      refine ⟨ht, fun T hT => ?_⟩
      rcases List.mem_cons.mp hT with rfl | hT
      · exact hS
      · rw [show t.restrict T = (t.restrict (schemaUnion l)).restrict T by
          rw [restrict_restrict, Finset.inter_eq_left.mpr (hU T hT)]]
        exact hl' T hT
    · rintro ⟨ht, hall⟩
      refine ⟨ht, hall S List.mem_cons_self, ht.restrict Finset.subset_union_right, fun T hT => ?_⟩
      rw [restrict_restrict, Finset.inter_eq_left.mpr (hU T hT)]
      exact hall T (List.mem_cons_of_mem _ hT)

/-! ### Boyce–Codd normal form -/

/-- **Boyce–Codd normal form.** A scheme $S$ is in Boyce–Codd normal form for a set $F$ of
functional dependencies when, for every dependency $X \to Y$ derivable from $F$ with
$X, Y \subseteq S$, either $Y \subseteq X$ or $F$ derives $X \to S$ (that is, $X$ is a superkey of
$S$). -/
def IsBCNF (F : Finset (FD A)) (S : Finset A) : Prop :=
  ∀ X ⊆ S, ∀ Y ⊆ S, Derives F ⟨X, Y⟩ → Y ⊆ X ∨ Derives F ⟨X, S⟩

/-- **BCNF violations.** Let $F$ be a set of functional dependencies and $S$ a scheme, and write
$X^+$ for the attribute closure of a set $X$ of attributes under $F$. A set $X \subseteq S$
violates BCNF in $S$ when $S \not\subseteq X^+$ and $X^+ \cap S \not\subseteq X$, that is, when
the closure $X^+ \cap S$ of $X$ within $S$ is neither $X$ nor $S$. -/
def IsBCNFViolation (F : Finset (FD A)) (S X : Finset A) : Prop :=
  X ⊆ S ∧ ¬ S ⊆ attrClosure F X ∧ ¬ attrClosure F X ∩ S ⊆ X

instance (F : Finset (FD A)) (S X : Finset A) : Decidable (IsBCNFViolation F S X) := by
  unfold IsBCNFViolation
  infer_instance

theorem isBCNF_iff {F : Finset (FD A)} {S : Finset A} :
    IsBCNF F S ↔ ∀ X ∈ S.powerset, ¬ IsBCNFViolation F S X := by
  constructor
  · rintro h X - ⟨hXS, hS, hX⟩
    rcases h X hXS _ Finset.inter_subset_right
      ((derives_attrClosure F X).decompose Finset.inter_subset_left) with h' | h'
    · exact hX h'
    · exact hS (derives_iff_subset_attrClosure.mp h')
  · intro h X hXS Y hYS hXY
    have hY : Y ⊆ attrClosure F X := derives_iff_subset_attrClosure.mp hXY
    by_cases hS : S ⊆ attrClosure F X
    · exact Or.inr (derives_iff_subset_attrClosure.mpr hS)
    · by_cases hX : attrClosure F X ∩ S ⊆ X
      · exact Or.inl fun a ha => hX (Finset.mem_inter.mpr ⟨hY ha, hYS ha⟩)
      · exact absurd ⟨hXS, hS, hX⟩ (h X (Finset.mem_powerset.mpr hXS))

instance (F : Finset (FD A)) (S : Finset A) : Decidable (IsBCNF F S) :=
  decidable_of_iff _ isBCNF_iff.symm

/-- **Candidate BCNF violations.** Given a list $l$ of attributes and a set $S$ of attributes, the
candidate violations of BCNF in $S$ are all subsets of the set of attributes that occur in $l$ and
lie in $S$, listed once each. Duplicates in $l$ are removed first, so there are $2^k$ candidates
when $k$ distinct attributes of $l$ lie in $S$. -/
def bcnfCandidates (l : List A) (S : Finset A) : List (Finset A) :=
  ((l.filter (· ∈ S)).dedup.sublists).map List.toFinset

/-- **BCNF decomposition with bounded depth.** Let $F$ be a set of functional dependencies, $l$ a
list of attributes, $n$ a natural number and $S$ a scheme. For $n = 0$ the result is the list $[S]$.
For $n > 0$, the candidate violations of BCNF in $S$ built from $l$ are searched in order for the
first $X$ that violates BCNF in $S$ for $F$. If there is none, the result is $[S]$. Otherwise, with
$X^+$ the attribute closure of $X$ under $F$, the result is the decomposition of $X^+ \cap S$
followed by the decomposition of $S \setminus (X^+ \setminus X)$, both computed with depth bound
$n - 1$. -/
def bcnfDecompose (F : Finset (FD A)) (l : List A) : ℕ → Finset A → List (Finset A)
  | 0, S => [S]
  | n + 1, S =>
    match (bcnfCandidates l S).find? (fun X => decide (IsBCNFViolation F S X)) with
    | none => [S]
    | some X => bcnfDecompose F l n (attrClosure F X ∩ S) ++
        bcnfDecompose F l n (S \ (attrClosure F X \ X))

/-- **BCNF decomposition.** Let $F$ be a set of functional dependencies, $l$ a list of attributes
and $S$ a scheme. The BCNF decomposition of $S$ for $F$ and $l$ is the BCNF decomposition with
bounded depth run on $S$ with depth bound $|S|$. At each step, if some candidate violation of BCNF
in the current scheme $T$ built from $l$ violates BCNF in $T$ for $F$, the first such $X$ is used:
with $X^+$ the attribute closure of $X$ under $F$, $T$ is replaced by the decomposition of
$X^+ \cap T$ followed by the decomposition of $T \setminus (X^+ \setminus X)$. Otherwise, or once
the depth bound is reached, $T$ is kept as it is. -/
def bcnfDecomposition (F : Finset (FD A)) (l : List A) (S : Finset A) : List (Finset A) :=
  bcnfDecompose F l S.card S

private theorem split_facts {F : Finset (FD A)} {S X : Finset A}
    (hv : IsBCNFViolation F S X) :
    (attrClosure F X ∩ S) ∪ (S \ (attrClosure F X \ X)) = S ∧
      (attrClosure F X ∩ S) ∩ (S \ (attrClosure F X \ X)) = X ∧
      (attrClosure F X ∩ S).card < S.card ∧ (S \ (attrClosure F X \ X)).card < S.card := by
  obtain ⟨hXS, hS, hX⟩ := hv
  have hXC := subset_attrClosure F X
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext a
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, not_and, not_not]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩) <;> exact h
    · intro haS
      by_cases haC : a ∈ attrClosure F X
      · exact Or.inl ⟨haC, haS⟩
      · exact Or.inr ⟨haS, fun h => absurd h haC⟩
  · ext a
    simp only [Finset.mem_inter, Finset.mem_sdiff, not_and, not_not]
    constructor
    · rintro ⟨⟨haC, -⟩, -, h⟩
      exact h haC
    · intro haX
      exact ⟨⟨hXC haX, hXS haX⟩, hXS haX, fun _ => haX⟩
  · refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, ?_⟩)
    intro heq
    exact hS (heq ▸ Finset.inter_subset_left)
  · refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩)
    intro heq
    obtain ⟨a, ha, haX⟩ := Finset.not_subset.mp hX
    obtain ⟨haC, haS⟩ := Finset.mem_inter.mp ha
    rw [← heq] at haS
    exact (Finset.mem_sdiff.mp haS).2 (Finset.mem_sdiff.mpr ⟨haC, haX⟩)

private theorem subset_of_mem_bcnfDecompose (F : Finset (FD A)) (l : List A) :
    ∀ (n : ℕ) (S T : Finset A), T ∈ bcnfDecompose F l n S → T ⊆ S
  | 0, S, T, h => by
    simp only [bcnfDecompose, List.mem_singleton] at h
    exact h ▸ subset_rfl
  | n + 1, S, T, h => by
    simp only [bcnfDecompose] at h
    split at h
    · simp only [List.mem_singleton] at h
      exact h ▸ subset_rfl
    · rename_i X _
      rcases List.mem_append.mp h with h | h
      · exact (subset_of_mem_bcnfDecompose F l n _ T h).trans Finset.inter_subset_right
      · exact (subset_of_mem_bcnfDecompose F l n _ T h).trans Finset.sdiff_subset

private theorem joinProjections_bcnfDecompose (F : Finset (FD A)) (l : List A) :
    ∀ (n : ℕ) (S : Finset A) (r : Finset (Tuple A D)), IsOver S r → SatisfiesOn F S r →
      joinProjections (bcnfDecompose F l n S) r = r
  | 0, S, r, hr, _ => joinProjections_singleton hr
  | n + 1, S, r, hr, hF => by
    simp only [bcnfDecompose]
    split
    · exact joinProjections_singleton hr
    · rename_i X hX
      have hv : IsBCNFViolation F S X := by
        simpa using List.find?_some hX
      obtain ⟨hunion, hinter, -, -⟩ := split_facts hv
      set R₁ := attrClosure F X ∩ S
      set R₂ := S \ (attrClosure F X \ X)
      have hR₁ : R₁ ⊆ S := Finset.inter_subset_right
      have hR₂ : R₂ ⊆ S := Finset.sdiff_subset
      rw [joinProjections_append,
        ← joinProjections_congr _ (subset_of_mem_bcnfDecompose F l n R₁) r,
        ← joinProjections_congr _ (subset_of_mem_bcnfDecompose F l n R₂) r,
        joinProjections_bcnfDecompose F l n R₁ _ (isOver_project hr hR₁) (hF.project hR₁),
        joinProjections_bcnfDecompose F l n R₂ _ (isOver_project hr hR₂) (hF.project hR₂)]
      refine join_project_eq_of_holdsIn (hunion.symm ▸ hr) ?_
      rw [hinter]
      exact hF X hv.1 R₁ hR₁ ((derives_attrClosure F X).decompose Finset.inter_subset_left)

/-- **The BCNF decomposition is lossless.** Let $F$ be a set of functional dependencies, $l$ a list
of attributes and $S$ a set of attributes, and let $r$ be a relation over $S$ that satisfies every
dependency $X \to Y$ derivable from $F$ with $X, Y \subseteq S$. Then $r$ is the natural join of
its projections onto the schemes of the BCNF decomposition of $S$ for $F$ and $l$. -/
theorem bcnfDecomposition_lossless (F : Finset (FD A)) (l : List A) {S : Finset A}
    {r : Finset (Tuple A D)} (hr : IsOver S r) (hF : SatisfiesOn F S r) :
    joinProjections (bcnfDecomposition F l S) r = r :=
  joinProjections_bcnfDecompose F l _ S r hr hF

omit [Fintype A] in
private theorem mem_bcnfCandidates {l : List A} (hl : ∀ a, a ∈ l) {S X : Finset A}
    (hXS : X ⊆ S) : X ∈ bcnfCandidates l S := by
  refine List.mem_map.mpr ⟨(l.filter (· ∈ S)).dedup.filter (· ∈ X),
    List.mem_sublists.mpr List.filter_sublist, ?_⟩
  ext a
  simp only [List.mem_toFinset, List.mem_filter, List.mem_dedup, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨⟨hl a, hXS h⟩, h⟩⟩

private theorem isBCNF_of_mem_bcnfDecompose (F : Finset (FD A)) {l : List A} (hl : ∀ a, a ∈ l) :
    ∀ (n : ℕ) (S T : Finset A), S.card ≤ n → T ∈ bcnfDecompose F l n S → IsBCNF F T
  | 0, S, T, hcard, h => by
    simp only [bcnfDecompose, List.mem_singleton] at h
    subst h
    have : T = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst this
    intro X hX Y hY _
    exact Or.inl (hY.trans (Finset.empty_subset X))
  | n + 1, S, T, hcard, h => by
    simp only [bcnfDecompose] at h
    split at h
    · rename_i hnone
      simp only [List.mem_singleton] at h
      subst h
      refine isBCNF_iff.mpr fun X hX hv => ?_
      have := List.find?_eq_none.mp hnone X (mem_bcnfCandidates hl (Finset.mem_powerset.mp hX))
      simp [hv] at this
    · rename_i X hX
      have hv : IsBCNFViolation F S X := by
        simpa using List.find?_some hX
      obtain ⟨-, -, h₁, h₂⟩ := split_facts hv
      rcases List.mem_append.mp h with h | h
      · exact isBCNF_of_mem_bcnfDecompose F hl n _ T (by omega) h
      · exact isBCNF_of_mem_bcnfDecompose F hl n _ T (by omega) h

/-- **The BCNF decomposition produces BCNF schemes.** Let $F$ be a set of functional dependencies
and $l$ a list containing every attribute. Then for every scheme $S$, every scheme in the BCNF
decomposition of $S$ for $F$ and $l$ is in Boyce–Codd normal form for $F$. -/
theorem isBCNF_of_mem_bcnfDecomposition (F : Finset (FD A)) {l : List A} (hl : ∀ a, a ∈ l)
    {S T : Finset A} (hT : T ∈ bcnfDecomposition F l S) : IsBCNF F T :=
  isBCNF_of_mem_bcnfDecompose F hl _ S T le_rfl hT

/-! ### Synthesis -/

/-- **Equivalent sets of functional dependencies.** Two sets $F$ and $G$ of functional dependencies
are equivalent when $F$ derives every dependency of $G$ and $G$ derives every dependency of $F$. -/
def Equivalent (F G : Finset (FD A)) : Prop := (∀ g ∈ G, Derives F g) ∧ ∀ f ∈ F, Derives G f

instance (F G : Finset (FD A)) : Decidable (Equivalent F G) := by
  unfold Equivalent
  infer_instance

/-- **Projection of the dependency closure onto a scheme.** For a finite set $F$ of functional
dependencies and a set $S$ of attributes, this is the finite set of all dependencies $X \to Y$
with $X, Y \subseteq S$ that are derivable from $F$ by Armstrong's axioms, that is, the projection
onto $S$ of the closure $F^+$ of $F$. -/
def projectFDs (F : Finset (FD A)) (S : Finset A) : Finset (FD A) :=
  ((S.powerset ×ˢ S.powerset).filter fun p => Derives F ⟨p.1, p.2⟩).image fun p => ⟨p.1, p.2⟩

/-- **Dependency-preserving decompositions.** A list $l$ of schemes is dependency-preserving for a
set $F$ of functional dependencies when every dependency of $F$ is derivable from the union, over
the schemes $S$ of $l$, of the sets of dependencies $X \to Y$ derivable from $F$ with
$X, Y \subseteq S$. -/
def DependencyPreserving (F : Finset (FD A)) (l : List (Finset A)) : Prop :=
  ∀ f ∈ F, Derives ((l.map (projectFDs F)).foldr (· ∪ ·) ∅) f

instance (F : Finset (FD A)) (l : List (Finset A)) : Decidable (DependencyPreserving F l) := by
  unfold DependencyPreserving
  infer_instance

/-- **Synthesis.** Given a list $G$ of functional dependencies and a set of attributes $K$, the
synthesized decomposition is the list of schemes consisting of $K$ followed by, for each
dependency $X \to Y$ of $G$ in order, the scheme $X \cup Y$. -/
def synthesize (G : List (FD A)) (K : Finset A) : List (Finset A) :=
  K :: G.map fun g => g.lhs ∪ g.rhs

omit [Fintype A] in
private theorem Derives.of_forall {F H : Finset (FD A)} (hH : ∀ g ∈ F, Derives H g) :
    ∀ {f : FD A}, Derives F f → Derives H f
  | _, .mem h => hH _ h
  | _, .refl h => .refl h
  | _, .augment Z h => .augment Z (Derives.of_forall hH h)
  | _, .trans h₁ h₂ => .trans (Derives.of_forall hH h₁) (Derives.of_forall hH h₂)

/-- The closure of `X` is contained in every set that contains `X` and is closed under `F`. -/
private theorem attrClosure_subset_of_closed {F : Finset (FD A)} {X C : Finset A} (hX : X ⊆ C)
    (hC : ∀ g ∈ F, g.lhs ⊆ C → g.rhs ⊆ C) : attrClosure F X ⊆ C := by
  let t₀ : A → Bool := fun _ => true
  let t₁ : A → Bool := fun a => decide (a ∈ C)
  have hr : Satisfies ({t₀, t₁} : Set (A → Bool)) F := by
    have key : ∀ g ∈ F, (∀ a ∈ g.lhs, t₀ a = t₁ a) → ∀ a ∈ g.rhs, t₀ a = t₁ a :=
      fun g hg hl a ha => by
        have : g.lhs ⊆ C := fun b hb => by simpa [t₀, t₁] using hl b hb
        simpa [t₀, t₁] using hC g hg this ha
    intro g hg t ht u hu hagree
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht hu
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
    · exact fun _ _ => rfl
    · exact key g hg hagree
    · exact fun a ha => (key g hg (fun b hb => (hagree b hb).symm) a ha).symm
    · exact fun _ _ => rfl
  intro a ha
  have := (derives_attrClosure F X).sound hr t₀ (by simp) t₁ (by simp)
    (fun b hb => by simpa [t₀, t₁] using hX hb) a ha
  simpa [t₀, t₁] using this

/-- **Synthesis is dependency-preserving.** Let $F$ be a finite set of functional dependencies and
$G$ a list of functional dependencies equivalent to $F$ (each derives every dependency of the
other). Then for every set of attributes $K$, the decomposition synthesized from $G$ and $K$,
with one scheme $X \cup Y$ for each dependency $X \to Y$ of $G$ together with the scheme $K$, is
dependency-preserving for $F$. -/
theorem synthesize_dependencyPreserving {F : Finset (FD A)} {G : List (FD A)}
    (hG : Equivalent F G.toFinset) (K : Finset A) : DependencyPreserving F (synthesize G K) := by
  intro f hf
  refine Derives.of_forall (fun g hg => Derives.mem ?_) (hG.2 f hf)
  have hgG : g ∈ G := List.mem_toFinset.mp hg
  have hmem : g ∈ projectFDs F (g.lhs ∪ g.rhs) := by
    refine Finset.mem_image.mpr ⟨(g.lhs, g.rhs), Finset.mem_filter.mpr ⟨?_, hG.1 g hg⟩, rfl⟩
    simp [Finset.subset_union_left, Finset.subset_union_right]
  have hl : projectFDs F (g.lhs ∪ g.rhs) ∈ (synthesize G K).map (projectFDs F) :=
    List.mem_map.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨g, hgG, rfl⟩), rfl⟩
  revert hl
  generalize (synthesize G K).map (projectFDs F) = L
  intro hl
  induction L with
  | nil => exact absurd hl List.not_mem_nil
  | cons P L ih =>
    simp only [List.foldr_cons, Finset.mem_union]
    rcases List.mem_cons.mp hl with rfl | hl
    · exact Or.inl hmem
    · exact Or.inr (ih hl)

/-- **Synthesis is lossless**: for a cover `G` of `F` and a superkey `K` of all attributes, every
relation over all attributes satisfying `F` is the join of its projections onto the synthesized
schemes. -/
theorem synthesize_lossless {F : Finset (FD A)} {G : List (FD A)} (hG : Equivalent F G.toFinset)
    {K : Finset A} (hK : IsSuperkey F K) {r : Finset (Tuple A D)} (hr : IsOver Finset.univ r)
    (hF : Satisfies (↑r : Set (Tuple A D)) F) :
    joinProjections (synthesize G K) r = r := by
  have hsub : ∀ S ∈ synthesize G K, S ⊆ Finset.univ := fun _ _ => Finset.subset_univ _
  have hGF : ∀ g ∈ G, FD.HoldsIn g (↑r : Set (Tuple A D)) := fun g hg =>
    (hG.1 g (List.mem_toFinset.mpr hg)).sound hF
  have hKG : attrClosure G.toFinset K = Finset.univ := by
    rw [← isSuperkey_iff_attrClosure]
    exact Derives.of_forall hG.2 hK
  -- the schemes cover all attributes
  have hcover : schemaUnion (synthesize G K) = Finset.univ := by
    refine Finset.eq_univ_iff_forall.mpr fun a => mem_schemaUnion.mpr ?_
    have hclosed : attrClosure G.toFinset K ⊆ schemaUnion (synthesize G K) := by
      refine attrClosure_subset_of_closed (fun b hb => mem_schemaUnion.mpr ⟨K, by simp [synthesize],
        hb⟩) fun g hg _ b hb => mem_schemaUnion.mpr ⟨g.lhs ∪ g.rhs, ?_, Finset.mem_union_right _ hb⟩
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨g, List.mem_toFinset.mp hg, rfl⟩)
    exact mem_schemaUnion.mp (hclosed (hKG ▸ Finset.mem_univ a))
  ext t
  rw [mem_joinProjections hr _ hsub, hcover]
  constructor
  · rintro ⟨ht, hall⟩
    obtain ⟨u, hu, hut⟩ := mem_project.mp (hall K (by simp [synthesize]))
    -- `t` and `u` agree on a set containing `K` and closed under `G`, hence everywhere
    have hagree : attrClosure G.toFinset K ⊆ (Finset.univ.filter fun a => t a = u a) := by
      refine attrClosure_subset_of_closed (fun a ha => ?_) fun g hg hlhs a ha => ?_
      · simpa using (restrict_eq_restrict_iff.mp hut a ha).symm
      · have hgG := List.mem_toFinset.mp hg
        obtain ⟨v, hv, hvt⟩ := mem_project.mp
          (hall (g.lhs ∪ g.rhs) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨g, hgG, rfl⟩)))
        have hvt' := restrict_eq_restrict_iff.mp hvt
        have huv : ∀ b ∈ g.lhs, v b = u b := fun b hb => by
          rw [hvt' b (Finset.mem_union_left _ hb)]
          simpa using hlhs hb
        simpa [← hvt' a (Finset.mem_union_right _ ha)] using hGF g hgG v hv u hu huv a ha
    have htu : t = u := funext fun a => by
      simpa using hagree (hKG ▸ Finset.mem_univ a)
    exact htu ▸ hu
  · intro ht
    exact ⟨hr t ht, fun S _ => mem_project.mpr ⟨t, ht, rfl⟩⟩

end Cslib.Databases
