/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.NormalForms

/-!
# Multivalued and join dependencies

Relations are those of `RelationalAlgebra` (finite sets of tuples `A → Option D`), and joins of
projections are `joinProjections` from `NormalForms`.

* `JD`: a join dependency `⋈[X₁, …, Xₙ]`, given by its list of schemes. It holds in a relation `r`
  when `r` is the join of its projections onto the schemes (`JD.HoldsIn`).
* `MVD`: a multivalued dependency `X ↠ Y`. Over a schema `U` it is the binary join dependency
  `⋈[X ∪ Y, X ∪ (U \ Y)]` (`MVD.toJD`, `MVD.HoldsIn`), as in Abiteboul–Hull–Vianu,
  Definition 8.3.2. `MVD.holdsIn_iff_exchange`: in a relation over `U`, `X ↠ Y` holds if and only
  if for any two tuples that agree on `X` some tuple of the relation agrees with the first on
  `X ∪ Y` and with the second on `U \ Y`.
* `join_project_eq_iff_mvd`: a relation is the join of its projections onto `R₁` and `R₂` if and
  only if `R₁ ∩ R₂ ↠ R₁` holds in it over `R₁ ∪ R₂`. `losslessJoin_iff_mvd` is the version for
  the relations satisfying a set of functional dependencies, and `mvd_implied_iff_derives`
  combines it with `losslessJoin_iff` (Abiteboul–Hull–Vianu, Proposition 8.3.3).
* `MVD.holdsIn_of_holdsIn_fd`: a functional dependency `X → Y` implies `X ↠ Y` (rule FMVD1).
  `MVD.holdsIn_of_rhs_subset` and `MVD.holdsIn_of_union_eq`: the trivial multivalued
  dependencies; `MVD.holdsIn_compl`: complementation (rule MVD0).
* `ImpliesFD`, `ImpliesJD`: logical implication by a set of functional and join dependencies,
  relative to the relations over `U` with values in `D`. `IsFourthNF`: fourth normal form
  (Definition 11.2.2, with the nontriviality condition `X ∪ Y ≠ U` for multivalued
  dependencies). `IsPJNF`: project-join normal form (Exercise 11.6).

## References

* R. Fagin, *Multivalued dependencies and a new normal form for relational databases*, ACM
  Transactions on Database Systems 2(3), 1977.
* S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995,
  Section 8.3 and Section 11.2.
-/

@[expose] public section

namespace Cslib.Databases

/-- **Join dependency.** A join dependency $\bowtie[X_1, \dots, X_n]$ over a type $A$ of
attributes is given by its list of schemes $X_1, \dots, X_n$, finite sets of attributes. -/
structure JD (A : Type*) where
  /-- The schemes $X_1, \dots, X_n$. -/
  schemes : List (Finset A)
deriving DecidableEq

/-- **Multivalued dependency.** A multivalued dependency $X \twoheadrightarrow Y$ over a type $A$
of attributes consists of two finite sets of attributes: its left side $X$ and its right side
$Y$. -/
structure MVD (A : Type*) where
  /-- The left side $X$. -/
  lhs : Finset A
  /-- The right side $Y$. -/
  rhs : Finset A
deriving DecidableEq

variable {A D : Type*} [Fintype A] [DecidableEq A] [DecidableEq D]

/-- **A join dependency holds in a relation.** The join dependency $\bowtie[X_1, \dots, X_n]$
holds in a finite set $r$ of tuples when $r$ is the natural join of its projections
$\pi_{X_1}(r), \dots, \pi_{X_n}(r)$ (`joinProjections`). -/
def JD.HoldsIn (j : JD A) (r : Finset (Tuple A D)) : Prop := joinProjections j.schemes r = r

omit [Fintype A] in
/-- **The join dependency of a multivalued dependency.** Over a schema $U$, the multivalued
dependency $X \twoheadrightarrow Y$ is the binary join dependency
$\bowtie[X \cup Y, X \cup (U \setminus Y)]$. -/
def MVD.toJD (U : Finset A) (m : MVD A) : JD A := ⟨[m.lhs ∪ m.rhs, m.lhs ∪ (U \ m.rhs)]⟩

/-- **A multivalued dependency holds in a relation.** Over a schema $U$, the multivalued
dependency $X \twoheadrightarrow Y$ holds in a finite set $r$ of tuples when
$r = \pi_{X \cup Y}(r) \bowtie \pi_{X \cup (U \setminus Y)}(r)$, that is, when the join dependency
$\bowtie[X \cup Y, X \cup (U \setminus Y)]$ holds in $r$ (Abiteboul–Hull–Vianu,
Definition 8.3.2). -/
def MVD.HoldsIn (U : Finset A) (m : MVD A) (r : Finset (Tuple A D)) : Prop :=
  (m.toJD U).HoldsIn r

instance (j : JD A) (r : Finset (Tuple A D)) : Decidable (j.HoldsIn r) := by
  unfold JD.HoldsIn
  infer_instance

instance (U : Finset A) (m : MVD A) (r : Finset (Tuple A D)) :
    Decidable (MVD.HoldsIn U m r) := by
  unfold MVD.HoldsIn JD.HoldsIn
  infer_instance

private theorem mem_project {T : Finset A} {r : Finset (Tuple A D)} {t : Tuple A D} :
    t ∈ project T r ↔ ∃ u ∈ r, u.restrict T = t := by
  simp [project]

private theorem joinProjections_pair (S₁ S₂ : Finset A) (r : Finset (Tuple A D)) :
    joinProjections [S₁, S₂] r = join (project S₁ r) (project S₂ r) := by
  have hnil : joinProjections ([] : List (Finset A)) r = joinUnit D := rfl
  rw [joinProjections_cons, joinProjections_cons, hnil, join_joinUnit]

private theorem mvd_holdsIn_eq_join {U X Y : Finset A} {r : Finset (Tuple A D)} :
    MVD.HoldsIn U ⟨X, Y⟩ r ↔
      join (project (X ∪ Y) r) (project (X ∪ (U \ Y)) r) = r := by
  change joinProjections [X ∪ Y, X ∪ (U \ Y)] r = r ↔
    join (project (X ∪ Y) r) (project (X ∪ (U \ Y)) r) = r
  rw [joinProjections_pair]

/-- **Tuple-exchange form of a multivalued dependency.** Let $r$ be a relation over $U$ and
$X, Y \subseteq U$. Then $X \twoheadrightarrow Y$ holds in $r$ over $U$ if and only if, for all
tuples $t, u \in r$ that agree on $X$, some tuple $w \in r$ agrees with $t$ on $X \cup Y$ and
with $u$ on $U \setminus Y$. -/
theorem MVD.holdsIn_iff_exchange {U X Y : Finset A} {r : Finset (Tuple A D)} (hr : IsOver U r)
    (hX : X ⊆ U) (hY : Y ⊆ U) :
    MVD.HoldsIn U ⟨X, Y⟩ r ↔ ∀ t ∈ r, ∀ u ∈ r, (∀ a ∈ X, t a = u a) →
      ∃ w ∈ r, (∀ a ∈ X ∪ Y, w a = t a) ∧ ∀ a ∈ U \ Y, w a = u a := by
  have hS₁U : X ∪ Y ⊆ U := fun a ha => by
    rcases Finset.mem_union.mp ha with hx | hy
    · exact hX hx
    · exact hY hy
  have hS₂U : X ∪ (U \ Y) ⊆ U := fun a ha => by
    rcases Finset.mem_union.mp ha with hx | haD
    · exact hX hx
    · exact (Finset.mem_sdiff.mp haD).1
  have hU12 : (X ∪ Y) ∪ (X ∪ (U \ Y)) = U := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (h | h)
      · rcases h with hx | hy
        · exact hX hx
        · exact hY hy
      · rcases h with hx | ⟨hxU, -⟩
        · exact hX hx
        · exact hxU
    · intro hxU
      by_cases hx : x ∈ X
      · exact Or.inl (Or.inl hx)
      · by_cases hy : x ∈ Y
        · exact Or.inl (Or.inr hy)
        · exact Or.inr (Or.inr ⟨hxU, hy⟩)
  have hI12 : (X ∪ Y) ∩ (X ∪ (U \ Y)) = X := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hx | hy, hx' | ⟨-, hy'⟩⟩
      · exact hx
      · exact hx
      · exact hx'
      · exact absurd hy hy'
    · intro hx
      exact ⟨Or.inl hx, Or.inl hx⟩
  rw [mvd_holdsIn_eq_join]
  constructor
  · intro hjoin t ht u hu hagree
    have htS₁ : (t.restrict (X ∪ Y)).IsOver (X ∪ Y) := (hr t ht).restrict hS₁U
    have huS₂ : (u.restrict (X ∪ (U \ Y))).IsOver (X ∪ (U \ Y)) :=
      (hr u hu).restrict hS₂U
    have hcompat : Tuple.Compatible (t.restrict (X ∪ Y))
        (u.restrict (X ∪ (U \ Y))) := by
      intro a
      by_cases ha₁ : a ∈ X ∪ Y
      · by_cases ha₂ : a ∈ X ∪ (U \ Y)
        · have haX : a ∈ X := hI12 ▸ Finset.mem_inter.mpr ⟨ha₁, ha₂⟩
          refine Or.inr (Or.inr ?_)
          simp only [Tuple.restrict_apply, ha₁, ha₂]
          exact hagree a haX
        · exact Or.inr (Or.inl (by simp [Tuple.restrict_apply, ha₂]))
      · exact Or.inl (by simp [Tuple.restrict_apply, ha₁])
    have hwmem : Tuple.merge (t.restrict (X ∪ Y)) (u.restrict (X ∪ (U \ Y))) ∈ r := by
      have hmem : Tuple.merge (t.restrict (X ∪ Y)) (u.restrict (X ∪ (U \ Y))) ∈
          join (project (X ∪ Y) r) (project (X ∪ (U \ Y)) r) :=
        mem_join.mpr ⟨t.restrict (X ∪ Y), mem_project.mpr ⟨t, ht, rfl⟩,
          u.restrict (X ∪ (U \ Y)), mem_project.mpr ⟨u, hu, rfl⟩, hcompat, rfl⟩
      rwa [hjoin] at hmem
    have hwag1 : ∀ a ∈ X ∪ Y,
        Tuple.merge (t.restrict (X ∪ Y)) (u.restrict (X ∪ (U \ Y))) a = t a := by
      intro a ha
      have h := congrFun (Tuple.restrict_merge_left (u := u.restrict (X ∪ (U \ Y))) htS₁) a
      simpa [ha] using h
    have hwag2 : ∀ a ∈ U \ Y,
        Tuple.merge (t.restrict (X ∪ Y)) (u.restrict (X ∪ (U \ Y))) a = u a := by
      intro a ha
      have ha₂ : a ∈ X ∪ (U \ Y) := Finset.mem_union.mpr (Or.inr ha)
      have h := congrFun (Tuple.restrict_merge_right huS₂ hcompat) a
      simpa [ha₂] using h
    exact ⟨_, hwmem, hwag1, hwag2⟩
  · intro hexch
    ext s
    constructor
    · intro hs
      rw [mem_join_iff (isOver_project hr hS₁U) (isOver_project hr hS₂U)] at hs
      obtain ⟨hsU12, htmem, humem⟩ := hs
      obtain ⟨t, ht, htS⟩ := mem_project.mp htmem
      obtain ⟨u, hu, huS⟩ := mem_project.mp humem
      have hts : ∀ a ∈ X ∪ Y, t a = s a := fun a ha => by
        simpa [ha] using congrFun htS a
      have hus : ∀ a ∈ X ∪ (U \ Y), u a = s a := fun a ha => by
        simpa [ha] using congrFun huS a
      have hagree : ∀ a ∈ X, t a = u a := fun a ha =>
        (hts a (Finset.mem_union.mpr (Or.inl ha))).trans
          (hus a (Finset.mem_union.mpr (Or.inl ha))).symm
      obtain ⟨w, hw, hwag1, hwag2⟩ := hexch t ht u hu hagree
      have hsU : s.IsOver U := by simpa [hU12] using hsU12
      have hws : w = s := by
        funext a
        by_cases haU : a ∈ U
        · by_cases haY : a ∈ Y
          · have ha₁ : a ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr haY)
            rw [hwag1 a ha₁, hts a ha₁]
          · have haD : a ∈ U \ Y := Finset.mem_sdiff.mpr ⟨haU, haY⟩
            have ha₂ : a ∈ X ∪ (U \ Y) := Finset.mem_union.mpr (Or.inr haD)
            rw [hwag2 a haD, hus a ha₂]
        · rw [(hr w hw).eq_none haU, hsU.eq_none haU]
      exact hws ▸ hw
    · intro hs
      rw [mem_join_iff (isOver_project hr hS₁U) (isOver_project hr hS₂U)]
      refine ⟨by simpa [hU12] using hr s hs, mem_project.mpr ⟨s, hs, rfl⟩,
        mem_project.mpr ⟨s, hs, rfl⟩⟩

/-- **Binary decompositions and multivalued dependencies.** For every finite set $r$ of tuples
and all sets of attributes $R_1$, $R_2$, the relation $r$ is the natural join of its
projections onto $R_1$ and $R_2$ if and only if the multivalued dependency
$R_1 \cap R_2 \twoheadrightarrow R_1$ holds in $r$ over $R_1 \cup R_2$. -/
theorem join_project_eq_iff_mvd {R₁ R₂ : Finset A} {r : Finset (Tuple A D)} :
    join (project R₁ r) (project R₂ r) = r ↔ MVD.HoldsIn (R₁ ∪ R₂) ⟨R₁ ∩ R₂, R₁⟩ r := by
  have h1 : (R₁ ∩ R₂) ∪ R₁ = R₁ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  have h2 : (R₁ ∩ R₂) ∪ ((R₁ ∪ R₂) \ R₁) = R₂ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  rw [mvd_holdsIn_eq_join, h1, h2]

/-- **Lossless binary decompositions and multivalued dependencies.** Let $F$ be a finite set of
functional dependencies and $R_1$, $R_2$ sets of attributes. The decomposition of
$R_1 \cup R_2$ into $R_1$ and $R_2$ is lossless for $F$ with values in $D$ if and only if
$R_1 \cap R_2 \twoheadrightarrow R_1$ holds over $R_1 \cup R_2$ in every relation over
$R_1 \cup R_2$ with values in $D$ that satisfies $F$ on $R_1 \cup R_2$. -/
theorem losslessJoin_iff_mvd {F : Finset (FD A)} {R₁ R₂ : Finset A} :
    LosslessJoin D F R₁ R₂ ↔ ∀ r : Finset (Tuple A D), IsOver (R₁ ∪ R₂) r →
      SatisfiesOn F (R₁ ∪ R₂) r → MVD.HoldsIn (R₁ ∪ R₂) ⟨R₁ ∩ R₂, R₁⟩ r := by
  change (∀ r : Finset (Tuple A D), IsOver (R₁ ∪ R₂) r → SatisfiesOn F (R₁ ∪ R₂) r →
      join (project R₁ r) (project R₂ r) = r) ↔
    (∀ r : Finset (Tuple A D), IsOver (R₁ ∪ R₂) r → SatisfiesOn F (R₁ ∪ R₂) r →
      MVD.HoldsIn (R₁ ∪ R₂) ⟨R₁ ∩ R₂, R₁⟩ r)
  constructor
  · intro h r hr hF
    exact join_project_eq_iff_mvd.mp (h r hr hF)
  · intro h r hr hF
    exact join_project_eq_iff_mvd.mpr (h r hr hF)

/-- **Multivalued dependencies implied by functional dependencies** (Abiteboul–Hull–Vianu,
Proposition 8.3.3). Let $F$ be a finite set of functional dependencies, let $R_1$ and $R_2$ be
schemes whose union is the set of all attributes, and let $D$ contain two distinct values. Then
$R_1 \cap R_2 \twoheadrightarrow R_1$ holds in every relation over $R_1 \cup R_2$ with values in
$D$ satisfying $F$ on $R_1 \cup R_2$ if and only if $F$ derives $R_1 \cap R_2 \to R_1$ or
$R_1 \cap R_2 \to R_2$. -/
theorem mvd_implied_iff_derives {F : Finset (FD A)} {R₁ R₂ : Finset A} {d₀ d₁ : D}
    (hd : d₀ ≠ d₁) (hR : R₁ ∪ R₂ = Finset.univ) :
    (∀ r : Finset (Tuple A D), IsOver (R₁ ∪ R₂) r → SatisfiesOn F (R₁ ∪ R₂) r →
      MVD.HoldsIn (R₁ ∪ R₂) ⟨R₁ ∩ R₂, R₁⟩ r) ↔
      Derives F ⟨R₁ ∩ R₂, R₁⟩ ∨ Derives F ⟨R₁ ∩ R₂, R₂⟩ := by
  exact losslessJoin_iff_mvd.symm.trans (losslessJoin_iff hd hR)

/-- **A functional dependency implies the multivalued dependency** (rule FMVD1). Let $r$ be a
relation over $U$ and $X, Y \subseteq U$. If $X \to Y$ holds in $r$, then $X \twoheadrightarrow Y$
holds in $r$ over $U$. -/
theorem MVD.holdsIn_of_holdsIn_fd {U X Y : Finset A} {r : Finset (Tuple A D)} (hr : IsOver U r)
    (hX : X ⊆ U) (hY : Y ⊆ U) (h : FD.HoldsIn ⟨X, Y⟩ (↑r : Set (Tuple A D))) :
    MVD.HoldsIn U ⟨X, Y⟩ r := by
  rw [MVD.holdsIn_iff_exchange hr hX hY]
  intro t ht u hu hagree
  refine ⟨u, hu, fun a ha => ?_, fun a _ => rfl⟩
  rcases Finset.mem_union.mp ha with haX | haY
  · exact (hagree a haX).symm
  · exact (h t ht u hu hagree a haY).symm

/-- **Trivial multivalued dependencies, right side in the left side** (rule MVD1). If
$Y \subseteq X \subseteq U$, then $X \twoheadrightarrow Y$ holds over $U$ in every relation over
$U$. -/
theorem MVD.holdsIn_of_rhs_subset {U X Y : Finset A} {r : Finset (Tuple A D)} (hr : IsOver U r)
    (hX : X ⊆ U) (hYX : Y ⊆ X) : MVD.HoldsIn U ⟨X, Y⟩ r := by
  rw [MVD.holdsIn_iff_exchange hr hX (hYX.trans hX)]
  intro t ht u hu hagree
  refine ⟨u, hu, fun a ha => ?_, fun a _ => rfl⟩
  rcases Finset.mem_union.mp ha with haX | haY
  · exact (hagree a haX).symm
  · exact (hagree a (hYX haY)).symm

/-- **Trivial multivalued dependencies, both sides covering the schema.** If $X \cup Y = U$, then
$X \twoheadrightarrow Y$ holds over $U$ in every relation over $U$. -/
theorem MVD.holdsIn_of_union_eq {U X Y : Finset A} {r : Finset (Tuple A D)} (hr : IsOver U r)
    (hXY : X ∪ Y = U) : MVD.HoldsIn U ⟨X, Y⟩ r := by
  have hX : X ⊆ U := hXY ▸ Finset.subset_union_left
  have hY : Y ⊆ U := hXY ▸ Finset.subset_union_right
  rw [MVD.holdsIn_iff_exchange hr hX hY]
  intro t ht u hu hagree
  refine ⟨t, ht, fun a _ => rfl, fun a ha => ?_⟩
  have haU : a ∈ X ∪ Y := hXY.symm ▸ (Finset.mem_sdiff.mp ha).1
  rcases Finset.mem_union.mp haU with haX | haY
  · exact hagree a haX
  · exact absurd haY (Finset.mem_sdiff.mp ha).2

/-- **Complementation** (rule MVD0). If $Y \subseteq U$, then $X \twoheadrightarrow Y$ holds in a
finite set $r$ of tuples over $U$ if and only if $X \twoheadrightarrow U \setminus Y$ does. -/
theorem MVD.holdsIn_compl {U X Y : Finset A} {r : Finset (Tuple A D)} (hY : Y ⊆ U) :
    MVD.HoldsIn U ⟨X, Y⟩ r ↔ MVD.HoldsIn U ⟨X, U \ Y⟩ r := by
  have hU : U \ (U \ Y) = Y := Finset.sdiff_sdiff_eq_self hY
  rw [mvd_holdsIn_eq_join, mvd_holdsIn_eq_join, hU, join_comm]

/-! ### Implication and normal forms -/

variable (D) in
/-- **Implication of a functional dependency.** A finite set $F$ of functional dependencies and a
finite set $J$ of join dependencies imply the functional dependency $f$ over the schema $U$, for
values in $D$, when $f$ holds in every relation over $U$ with values in $D$ that satisfies every
dependency of $F$ and every join dependency of $J$. -/
def ImpliesFD (U : Finset A) (F : Finset (FD A)) (J : Finset (JD A)) (f : FD A) : Prop :=
  ∀ r : Finset (Tuple A D), IsOver U r → Satisfies (↑r : Set (Tuple A D)) F →
    (∀ j ∈ J, j.HoldsIn r) → f.HoldsIn (↑r : Set (Tuple A D))

variable (D) in
/-- **Implication of a join dependency.** A finite set $F$ of functional dependencies and a
finite set $J$ of join dependencies imply the join dependency $j$ over the schema $U$, for
values in $D$, when $j$ holds in every relation over $U$ with values in $D$ that satisfies every
dependency of $F$ and every join dependency of $J$. -/
def ImpliesJD (U : Finset A) (F : Finset (FD A)) (J : Finset (JD A)) (j : JD A) : Prop :=
  ∀ r : Finset (Tuple A D), IsOver U r → Satisfies (↑r : Set (Tuple A D)) F →
    (∀ j' ∈ J, j'.HoldsIn r) → j.HoldsIn r

variable (D) in
/-- **Fourth normal form.** The schema $U$ with functional dependencies $F$ and join dependencies
$J$ (multivalued dependencies enter $J$ through `MVD.toJD`) is in fourth normal form, for values
in $D$, when (a) for all $X, Y \subseteq U$ with $Y \not\subseteq X$, if $X \to Y$ is implied
then $X \to U$ is implied, and (b) for all $X, Y \subseteq U$ with $Y \not\subseteq X$ and
$X \cup Y \neq U$, if $X \twoheadrightarrow Y$ is implied then $X \to U$ is implied
(Abiteboul–Hull–Vianu, Definition 11.2.2, with the nontriviality condition $X \cup Y \neq U$ of
Fagin). -/
def IsFourthNF (U : Finset A) (F : Finset (FD A)) (J : Finset (JD A)) : Prop :=
  (∀ X ⊆ U, ∀ Y ⊆ U, ¬ Y ⊆ X → ImpliesFD D U F J ⟨X, Y⟩ → ImpliesFD D U F J ⟨X, U⟩) ∧
    ∀ X ⊆ U, ∀ Y ⊆ U, ¬ Y ⊆ X → X ∪ Y ≠ U → ImpliesJD D U F J (MVD.toJD U ⟨X, Y⟩) →
      ImpliesFD D U F J ⟨X, U⟩

variable (D) in
/-- **Project-join normal form.** The schema $U$ with functional dependencies $F$ and join
dependencies $J$ is in project-join normal form, for values in $D$, when every join dependency
implied by $F$ and $J$ holds in every relation over $U$ with values in $D$ that satisfies every
key dependency $X \to U$ (with $X \subseteq U$) implied by $F$ and $J$ (Abiteboul–Hull–Vianu,
Exercise 11.6). -/
def IsPJNF (U : Finset A) (F : Finset (FD A)) (J : Finset (JD A)) : Prop :=
  ∀ j : JD A, ImpliesJD D U F J j → ∀ r : Finset (Tuple A D), IsOver U r →
    (∀ X ⊆ U, ImpliesFD D U F J ⟨X, U⟩ → FD.HoldsIn ⟨X, U⟩ (↑r : Set (Tuple A D))) →
      j.HoldsIn r

end Cslib.Databases
