/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.FunctionalDependencies
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Fin.VecNotation

/-!
# Inclusion dependencies and finite implication

The two sides of an inclusion dependency may name different relations, with different
attributes. Their projections are comparable because both produce tuples indexed by the same
`Fin k`. The embeddings selecting columns enforce distinctness on each side, not across sides.

An instance gives one extent (set of rows) per relation. Both implication predicates are
relative to a fixed common value type `V`, of any universe level; take `V = ℕ` for the book's
countably infinite domain. They differ only in which instances are quantified over, not in the
type of values allowed. Functional dependencies use `FD.HoldsIn` on the named extent.

Over `ℕ` (the book's countably infinite domain), finite implication is strictly weaker than
unrestricted implication; over a finite value type every instance is finite, so the two
notions coincide. In the separating example of Theorem 9.2.2 (namespace `FiniteImplication`),
`{A → B, R[A] ⊆ R[B]}` finitely implies both `R[B] ⊆ R[A]` and `B → A` over every value type,
but implies neither over `ℕ`: two infinite instances (Figure 9.1) are counter-models.

## References

* S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995,
  §§3.1–3.3 (schemas, tuples and instances), Definition 9.1.1 (inclusion dependency),
  Definition 9.2.1 (unrestricted and finite implication), and Theorem 9.2.2 with Figure 9.1.
-/

@[expose] public section

namespace Cslib.Databases

universe u v

/-- **Relational schema.**
A relational schema has a nonempty finite type of relation names and, for each name, a
finite type of attributes. A relation may have no attributes. -/
structure RelationalSchema where
  /-- Names of the relations in the schema. -/
  Name : Type u
  /-- Attributes belonging to each relation name. -/
  Attr : Name → Type v
  [nonempty_name : Nonempty Name]
  [finite_name : Finite Name]
  [finite_attr : ∀ R, Finite (Attr R)]

attribute [instance] RelationalSchema.nonempty_name RelationalSchema.finite_name
  RelationalSchema.finite_attr

/-- **Database instance.**
An instance over a value domain $V$ assigns to each relation name $R$ a set of rows.
Each row is a total function from the attributes of $R$ to $V$. The extent of a relation
may be empty, finite or infinite. -/
abbrev RelationalSchema.Instance (S : RelationalSchema) (V : Type*) :=
  (R : S.Name) → Set (S.Attr R → V)

variable {S : RelationalSchema} {V : Type*}

/-- **Finite database instance.**
A database instance is finite when the extent of every relation in the schema is a finite
set of rows. This imposes no finiteness assumption on the ambient value domain. -/
def RelationalSchema.Instance.IsFinite (I : S.Instance V) : Prop := ∀ R, (I R).Finite

/-- **Active domain of a database instance.**
The active domain of an instance is the set of values that actually occur in a row of
some relation, in at least one of its attributes. -/
def RelationalSchema.Instance.activeDomain (I : S.Instance V) : Set V :=
  ⋃ R, ⋃ t ∈ I R, Set.range t

/-- **Finite extents and finite active domain.**
On a finite schema with finitely many attributes per relation, the extents of an instance
are all finite if and only if its active domain is finite. -/
theorem RelationalSchema.Instance.isFinite_iff_finite_activeDomain (I : S.Instance V) :
    I.IsFinite ↔ I.activeDomain.Finite := by
  constructor
  · intro h
    exact Set.finite_iUnion fun R => (h R).biUnion fun t _ => Set.finite_range t
  · intro h R
    refine (Set.Finite.pi' fun _ : S.Attr R => h).subset ?_
    intro t ht a
    exact Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht, ⟨a, rfl⟩⟩⟩⟩

/-- **Ordered projection of a relation.**
Project a set of rows onto an ordered sequence of $k$ distinct attributes. The result
consists of the functions on the $k$ positions obtained by reading a row at those attributes,
in order. -/
def orderedProjection {A : Type*} {k : ℕ} (cols : Fin k ↪ A) (r : Set (A → V)) :
    Set (Fin k → V) := (fun t => t ∘ cols) '' r

/-- **Syntax of an inclusion dependency.**
An inclusion dependency on a schema consists of relation names $R,S$ (possibly equal), a
common arity $k$, and two ordered sequences of $k$ distinct attributes, one of $R$ and one of
$S$. Distinctness is required separately within each sequence. -/
structure IND (S : RelationalSchema) where
  /-- Relation from which projected rows must be matched. -/
  source : S.Name
  /-- Relation in which to find the matching rows. -/
  target : S.Name
  /-- Common length of the two attribute sequences. -/
  arity : ℕ
  /-- Ordered source attributes, without repetition. -/
  lhs : Fin arity ↪ S.Attr source
  /-- Ordered target attributes, without repetition. -/
  rhs : Fin arity ↪ S.Attr target

/-- **Satisfaction of an inclusion dependency.**
An instance satisfies the inclusion dependency $R[A_1,\ldots,A_k]\subseteq S[B_1,\ldots,B_k]$
when the projection of the extent of $R$ on the indicated sequence is a subset of the
corresponding projection of the extent of $S$. The projected objects are whole ordered tuples. -/
def IND.HoldsIn (d : IND S) (I : S.Instance V) : Prop :=
  orderedProjection d.lhs (I d.source) ⊆ orderedProjection d.rhs (I d.target)

/-- **A joint witness for a projected row.**
Projection inclusion is equivalent to the joint witness condition: for every source row
there is a single target row agreeing at *all* corresponding positions. -/
theorem IND.holdsIn_iff_exists_row (d : IND S) (I : S.Instance V) :
    d.HoldsIn I ↔ ∀ t ∈ I d.source, ∃ s ∈ I d.target, ∀ i, t (d.lhs i) = s (d.rhs i) := by
  constructor
  · intro h t ht
    obtain ⟨s, hs, he⟩ := h ⟨t, ht, rfl⟩
    exact ⟨s, hs, fun i => congrFun he.symm i⟩
  · rintro h _ ⟨t, ht, rfl⟩
    obtain ⟨s, hs, he⟩ := h t ht
    exact ⟨s, hs, funext fun i => (he i).symm⟩

/-- **Reflexivity of projection inclusion.**
Every instance satisfies self-inclusion on the same ordered sequence of attributes. -/
theorem IND.holdsIn_refl (I : S.Instance V) (R : S.Name) {k : ℕ} (X : Fin k ↪ S.Attr R) :
    (IND.mk R R k X X).HoldsIn I := fun _ h => h

/-- **Transitivity of projection inclusion.**
In one instance, inclusion from $R[X]$ to $T[Z]$ follows from inclusions from $R[X]$ to
$S[Y]$ and from that very same ordered projection $S[Y]$ to $T[Z]$. -/
theorem IND.holdsIn_trans {I : S.Instance V} {R P T : S.Name} {k : ℕ}
    {X : Fin k ↪ S.Attr R} {Y : Fin k ↪ S.Attr P} {Z : Fin k ↪ S.Attr T}
    (h₁ : (IND.mk R P k X Y).HoldsIn I) (h₂ : (IND.mk P T k Y Z).HoldsIn I) :
    (IND.mk R T k X Z).HoldsIn I := fun _ h => h₂ (h₁ h)

/-- **Functional and inclusion dependencies on a schema.**
A schema dependency is either a functional dependency on one named relation's attributes
or an inclusion dependency between ordered projections on the schema. -/
inductive Dependency (S : RelationalSchema) where
  | functional (R : S.Name) (f : FD (S.Attr R))
  | inclusion (d : IND S)

/-- **Satisfaction of a schema dependency.**
A functional dependency on $R$ holds in a database instance when it holds in the extent
of $R$. An inclusion dependency holds when the indicated projection inclusion holds in that
same instance. -/
def Dependency.HoldsIn (d : Dependency S) (I : S.Instance V) : Prop :=
  match d with
  | .functional R f => f.HoldsIn (I R)
  | .inclusion i => i.HoldsIn I

/-- **Unrestricted implication of dependencies.**
Over a fixed common value domain, a set of dependencies implies a dependency without
restriction if every instance satisfying every hypothesis also satisfies the conclusion.
Relation extents may be infinite. -/
def Dependency.Implies (V : Type*) (F : Set (Dependency S)) (d : Dependency S) : Prop :=
  ∀ I : S.Instance V, (∀ f ∈ F, f.HoldsIn I) → d.HoldsIn I

/-- **Finite implication of dependencies.**
Over a fixed common value domain, a set of dependencies finitely implies a dependency if
every instance with finite relation extents satisfying every hypothesis also satisfies the
conclusion. The value domain itself need not be finite. -/
def Dependency.FinitelyImplies (V : Type*) (F : Set (Dependency S)) (d : Dependency S) : Prop :=
  ∀ I : S.Instance V, I.IsFinite → (∀ f ∈ F, f.HoldsIn I) → d.HoldsIn I

/-- **Unrestricted implication gives finite implication.**
Unrestricted implication over a value domain entails finite implication over the same domain
and schema, with the same hypotheses and conclusion. -/
theorem Dependency.finitelyImplies_of_implies {F : Set (Dependency S)} {d : Dependency S}
    (h : Implies V F d) : FinitelyImplies V F d := fun I _ hF => h I hF

/-! ### Over the natural numbers, finite implication is strictly weaker -/

namespace FiniteImplication

/-- **Schema of the separating example.**
A single relation $R$, named `()`, with the two attributes $A = 0$ and $B = 1$. -/
def schema : RelationalSchema.{0, 0} where
  Name := Unit
  Attr _ := Fin 2

/-- **The column sequence $[A]$.** The one-attribute sequence of $R$ reading $A$. -/
def colA : Fin 1 ↪ schema.Attr () := ⟨fun _ => (0 : Fin 2), fun _ _ _ => Subsingleton.elim _ _⟩

/-- **The column sequence $[B]$.** The one-attribute sequence of $R$ reading $B$. -/
def colB : Fin 1 ↪ schema.Attr () := ⟨fun _ => (1 : Fin 2), fun _ _ _ => Subsingleton.elim _ _⟩

/-- **The functional dependency $A \to B$ on $R$.** -/
def fdAB : Dependency schema := .functional () (⟨{0}, {1}⟩ : FD (Fin 2))

/-- **The functional dependency $B \to A$ on $R$.** -/
def fdBA : Dependency schema := .functional () (⟨{1}, {0}⟩ : FD (Fin 2))

/-- **The inclusion dependency $R[A] \subseteq R[B]$.** -/
def indAB : IND schema := ⟨(), (), 1, colA, colB⟩

/-- **The inclusion dependency $R[B] \subseteq R[A]$.** -/
def indBA : IND schema := ⟨(), (), 1, colB, colA⟩

/-- **Hypotheses of the separating example.**
The set $F = \{A \to B,\ R[A] \subseteq R[B]\}$ from the proof of Theorem 9.2.2. -/
def deps : Set (Dependency schema) := {fdAB, .inclusion indAB}

/-- **The instance of Figure 9.1(a).**
The infinite extent of $R$ consisting of the rows $(A, B) = (n + 1, n)$ for all
$n \in \mathbb{N}$. -/
def descending : schema.Instance ℕ := fun _ => Set.range fun n : ℕ => ![n + 1, n]

/-- **The instance of Figure 9.1(b).**
The infinite extent of $R$ consisting of the row $(1, 1)$ and the rows $(n + 2, n + 1)$ for all
$n \in \mathbb{N}$. -/
def descendingWithLoop : schema.Instance ℕ :=
  fun _ => insert ![1, 1] (Set.range fun n : ℕ => ![n + 2, n + 1])

/-- **Row form of the inclusion dependency $R[A] \subseteq R[B]$.** -/
private theorem holdsIn_indAB_iff {V : Type*} (I : schema.Instance V) :
    indAB.HoldsIn I ↔ ∀ t ∈ I (), ∃ s ∈ I (), t (0 : Fin 2) = s (1 : Fin 2) := by
  rw [indAB.holdsIn_iff_exists_row I]
  constructor
  · intro h t ht
    obtain ⟨s, hs, he⟩ := h t ht
    exact ⟨s, hs, he (0 : Fin 1)⟩
  · intro h t ht
    obtain ⟨s, hs, he⟩ := h t ht
    refine ⟨s, hs, ?_⟩
    simp only [indAB, Fin.forall_fin_one]
    exact he

/-- **Row form of the inclusion dependency $R[B] \subseteq R[A]$.** -/
private theorem holdsIn_indBA_iff {V : Type*} (I : schema.Instance V) :
    indBA.HoldsIn I ↔ ∀ t ∈ I (), ∃ s ∈ I (), t (1 : Fin 2) = s (0 : Fin 2) := by
  rw [indBA.holdsIn_iff_exists_row I]
  constructor
  · intro h t ht
    obtain ⟨s, hs, he⟩ := h t ht
    exact ⟨s, hs, he (0 : Fin 1)⟩
  · intro h t ht
    obtain ⟨s, hs, he⟩ := h t ht
    refine ⟨s, hs, ?_⟩
    simp only [indBA, Fin.forall_fin_one]
    exact he

/-- **Row form of the functional dependency $A \to B$.** -/
private theorem holdsIn_fdAB_iff {V : Type*} (I : schema.Instance V) :
    fdAB.HoldsIn I ↔
      ∀ t ∈ I (), ∀ u ∈ I (), t (0 : Fin 2) = u (0 : Fin 2) → t (1 : Fin 2) = u (1 : Fin 2) := by
  change (⟨{0}, {1}⟩ : FD (Fin 2)).HoldsIn (I ()) ↔ _
  constructor
  · intro h t ht u hu htu
    refine h t ht u hu (fun a ha => ?_) 1 (Finset.mem_singleton_self 1)
    have ha0 : a = 0 := Finset.mem_singleton.mp ha
    rw [ha0]
    exact htu
  · intro h t ht u hu hagree a ha
    have ha1 : a = 1 := Finset.mem_singleton.mp ha
    rw [ha1]
    apply h t ht u hu
    exact hagree 0 (Finset.mem_singleton_self 0)

/-- **Row form of the functional dependency $B \to A$.** -/
private theorem holdsIn_fdBA_iff {V : Type*} (I : schema.Instance V) :
    fdBA.HoldsIn I ↔
      ∀ t ∈ I (), ∀ u ∈ I (), t (1 : Fin 2) = u (1 : Fin 2) → t (0 : Fin 2) = u (0 : Fin 2) := by
  change (⟨{1}, {0}⟩ : FD (Fin 2)).HoldsIn (I ()) ↔ _
  constructor
  · intro h t ht u hu htu
    refine h t ht u hu (fun a ha => ?_) 0 (Finset.mem_singleton_self 0)
    have ha1 : a = 1 := Finset.mem_singleton.mp ha
    rw [ha1]
    exact htu
  · intro h t ht u hu hagree a ha
    have ha0 : a = 0 := Finset.mem_singleton.mp ha
    rw [ha0]
    apply h t ht u hu
    exact hagree 1 (Finset.mem_singleton_self 1)

/-- **The finite projections on $A$ and on $B$ coincide.**
In a finite instance satisfying $\{A \to B, R[A] \subseteq R[B]\}$, the finite set of values
occurring under $A$ equals the finite set of values occurring under $B$: the inclusion gives
one direction, and the functional dependency makes the choice of $B$-values from $A$-values
surjective, so both sides have the same cardinality. -/
private theorem proj_image_eq {V : Type*} [DecidableEq V] (I : schema.Instance V)
    (hfin : I.IsFinite) (h : ∀ f ∈ deps, f.HoldsIn I) :
    (hfin ()).toFinset.image (fun t : Fin 2 → V => t (0 : Fin 2)) =
      (hfin ()).toFinset.image (fun t : Fin 2 → V => t (1 : Fin 2)) := by
  have hFD : ∀ t ∈ I (), ∀ u ∈ I (),
      t (0 : Fin 2) = u (0 : Fin 2) → t (1 : Fin 2) = u (1 : Fin 2) :=
    (holdsIn_fdAB_iff I).mp (h fdAB (Set.mem_insert _ _))
  have hIND : ∀ t ∈ I (), ∃ s ∈ I (), t (0 : Fin 2) = s (1 : Fin 2) :=
    (holdsIn_indAB_iff I).mp (h (.inclusion indAB) (Set.mem_insert_of_mem _ rfl))
  set r : Finset (Fin 2 → V) := (hfin ()).toFinset with hr
  set pA : Finset V := r.image (fun t : Fin 2 → V => t (0 : Fin 2)) with hpA
  set pB : Finset V := r.image (fun t : Fin 2 → V => t (1 : Fin 2)) with hpB
  have hsub : pA ⊆ pB := by
    intro v hv
    rw [hpA, Finset.mem_image] at hv
    obtain ⟨t, htr, htv⟩ := hv
    have htI : t ∈ I () := ((hfin ()).mem_toFinset).mp htr
    obtain ⟨s, hsI, hst⟩ := hIND t htI
    have hsR : s ∈ r := ((hfin ()).mem_toFinset).mpr hsI
    rw [hpB, Finset.mem_image]
    exact ⟨s, hsR, hst.symm.trans htv⟩
  have hex : ∀ a : { v // v ∈ pA }, ∃ t : Fin 2 → V, t ∈ r ∧ t (0 : Fin 2) = a.val := by
    intro a
    exact Finset.mem_image.mp a.property
  choose g hg using hex
  have hsurj : Set.SurjOn
      (fun a => if h : a ∈ pA then (g ⟨a, h⟩) (1 : Fin 2) else a) ↑pA ↑pB := by
    intro b hb
    have hb' : b ∈ pB := Finset.mem_coe.mp hb
    rw [hpB, Finset.mem_image] at hb'
    obtain ⟨u, hur, hub⟩ := hb'
    have huI : u ∈ I () := ((hfin ()).mem_toFinset).mp hur
    have ha : u (0 : Fin 2) ∈ pA := by
      rw [hpA, Finset.mem_image]
      exact ⟨u, hur, rfl⟩
    rw [Set.mem_image]
    refine ⟨u (0 : Fin 2), Finset.mem_coe.mpr ha, ?_⟩
    rw [dite_eq_left ha]
    have htI : g ⟨u (0 : Fin 2), ha⟩ ∈ I () :=
      ((hfin ()).mem_toFinset).mp (hg ⟨u (0 : Fin 2), ha⟩).1
    have h0 : (g ⟨u (0 : Fin 2), ha⟩) (0 : Fin 2) = u (0 : Fin 2) :=
      (hg ⟨u (0 : Fin 2), ha⟩).2
    have h1 : (g ⟨u (0 : Fin 2), ha⟩) (1 : Fin 2) = u (1 : Fin 2) := hFD _ htI _ huI h0
    exact h1.trans hub
  have hcard : pB.card ≤ pA.card := Finset.card_le_card_of_surjOn _ hsurj
  exact Finset.eq_of_subset_of_card_le hsub hcard

/-- **Figure 9.1(a) satisfies the hypotheses.** -/
theorem descending_holdsIn_deps : ∀ f ∈ deps, f.HoldsIn descending := by
  intro f hf
  simp only [deps, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl
  · rw [holdsIn_fdAB_iff descending]
    intro t ht u hu htu
    have ht' : t ∈ Set.range (fun n : ℕ => ![n + 1, n]) := ht
    have hu' : u ∈ Set.range (fun n : ℕ => ![n + 1, n]) := hu
    obtain ⟨n, rfl⟩ := Set.mem_range.mp ht'
    obtain ⟨m, rfl⟩ := Set.mem_range.mp hu'
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at htu ⊢
    omega
  · change indAB.HoldsIn descending
    rw [holdsIn_indAB_iff descending]
    intro t ht
    have ht' : t ∈ Set.range (fun n : ℕ => ![n + 1, n]) := ht
    obtain ⟨n, rfl⟩ := Set.mem_range.mp ht'
    refine ⟨![n + 2, n + 1], ?_, ?_⟩
    · exact Set.mem_range.mpr ⟨n + 1, rfl⟩
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Figure 9.1(a) violates $R[B] \subseteq R[A]$.** The value $0$ occurs under $B$ only. -/
theorem not_holdsIn_indBA_descending : ¬ indBA.HoldsIn descending := by
  intro h
  rw [holdsIn_indBA_iff descending] at h
  have hmem : ![1, 0] ∈ descending () := Set.mem_range.mpr ⟨0, rfl⟩
  obtain ⟨s, hs, he⟩ := h _ hmem
  have hs' : s ∈ Set.range (fun n : ℕ => ![n + 1, n]) := hs
  obtain ⟨m, rfl⟩ := Set.mem_range.mp hs'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at he
  omega

/-- **Figure 9.1(b) satisfies the hypotheses.** -/
theorem descendingWithLoop_holdsIn_deps : ∀ f ∈ deps, f.HoldsIn descendingWithLoop := by
  intro f hf
  simp only [deps, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl
  · rw [holdsIn_fdAB_iff descendingWithLoop]
    intro t ht u hu htu
    rcases Set.mem_insert_iff.mp ht with rfl | hmem_t
    · rcases Set.mem_insert_iff.mp hu with rfl | hmem_u
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at htu ⊢
      · obtain ⟨m, rfl⟩ := Set.mem_range.mp hmem_u
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at htu ⊢; omega
    · obtain ⟨n, rfl⟩ := Set.mem_range.mp hmem_t
      rcases Set.mem_insert_iff.mp hu with rfl | hmem_u
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at htu ⊢; omega
      · obtain ⟨m, rfl⟩ := Set.mem_range.mp hmem_u
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at htu ⊢; omega
  · change indAB.HoldsIn descendingWithLoop
    rw [holdsIn_indAB_iff descendingWithLoop]
    intro t ht
    rcases Set.mem_insert_iff.mp ht with rfl | hmem_t
    · refine ⟨![1, 1], Set.mem_insert_iff.mpr (Or.inl rfl), ?_⟩
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    · obtain ⟨n, rfl⟩ := Set.mem_range.mp hmem_t
      refine ⟨![n + 3, n + 2], Set.mem_insert_iff.mpr (Or.inr ⟨n + 1, rfl⟩), ?_⟩
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Figure 9.1(b) violates $B \to A$.** The rows $(1, 1)$ and $(2, 1)$ agree on $B$ only. -/
theorem not_holdsIn_fdBA_descendingWithLoop : ¬ fdBA.HoldsIn descendingWithLoop := by
  intro h
  rw [holdsIn_fdBA_iff descendingWithLoop] at h
  have hmem_loop : ![1, 1] ∈ descendingWithLoop () :=
    Set.mem_insert_iff.mpr (Or.inl rfl)
  have hmem0 : ![2, 1] ∈ descendingWithLoop () :=
    Set.mem_insert_iff.mpr (Or.inr ⟨0, rfl⟩)
  have hcon := h _ hmem_loop _ hmem0 (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one])
  simp only [Matrix.cons_val_zero] at hcon
  omega

/-- **Finite implication of an inclusion dependency** (Theorem 9.2.2(a)).
Over any value domain, $\{A \to B,\ R[A] \subseteq R[B]\}$ finitely implies
$R[B] \subseteq R[A]$. -/
theorem finitelyImplies_indBA (V : Type*) :
    Dependency.FinitelyImplies V deps (.inclusion indBA) := by
  classical
  intro I hfin h
  have hpApB := proj_image_eq I hfin h
  change indBA.HoldsIn I
  rw [holdsIn_indBA_iff I]
  intro t ht
  have htR : t ∈ (hfin ()).toFinset := ((hfin ()).mem_toFinset).mpr ht
  have h1B : t (1 : Fin 2) ∈ (hfin ()).toFinset.image (fun t : Fin 2 → V => t (1 : Fin 2)) :=
    Finset.mem_image.mpr ⟨t, htR, rfl⟩
  rw [← hpApB] at h1B
  obtain ⟨s, hsR, hst⟩ := Finset.mem_image.mp h1B
  exact ⟨s, ((hfin ()).mem_toFinset).mp hsR, hst.symm⟩

/-- **No unrestricted implication of the inclusion dependency** (Theorem 9.2.2(a)).
Over $\mathbb{N}$, $\{A \to B,\ R[A] \subseteq R[B]\}$ does not imply $R[B] \subseteq R[A]$:
Figure 9.1(a) is a counter-model. -/
theorem not_implies_indBA : ¬ Dependency.Implies ℕ deps (.inclusion indBA) := by
  intro h
  exact not_holdsIn_indBA_descending (h descending descending_holdsIn_deps)

/-- **Finite implication of a functional dependency** (Theorem 9.2.2(b)).
Over any value domain, $\{A \to B,\ R[A] \subseteq R[B]\}$ finitely implies $B \to A$. -/
theorem finitelyImplies_fdBA (V : Type*) : Dependency.FinitelyImplies V deps fdBA := by
  classical
  intro I hfin h
  have hFD : ∀ t ∈ I (), ∀ u ∈ I (),
      t (0 : Fin 2) = u (0 : Fin 2) → t (1 : Fin 2) = u (1 : Fin 2) :=
    (holdsIn_fdAB_iff I).mp (h fdAB (Set.mem_insert _ _))
  set r : Finset (Fin 2 → V) := (hfin ()).toFinset with hr
  have hpApB : r.image (fun t : Fin 2 → V => t (0 : Fin 2)) =
      r.image (fun t : Fin 2 → V => t (1 : Fin 2)) := proj_image_eq I hfin h
  have hinj0 : Set.InjOn (fun t : Fin 2 → V => t (0 : Fin 2)) ↑r := by
    intro t ht u hu htu
    have htR : t ∈ r := Finset.mem_coe.mp ht
    have huR : u ∈ r := Finset.mem_coe.mp hu
    have htI : t ∈ I () := ((hfin ()).mem_toFinset).mp htR
    have huI : u ∈ I () := ((hfin ()).mem_toFinset).mp huR
    have htu' : t (0 : Fin 2) = u (0 : Fin 2) := htu
    have h1 : t (1 : Fin 2) = u (1 : Fin 2) := hFD t htI u huI htu'
    have hall : ∀ a : Fin 2, t a = u a := by
      simp only [Fin.forall_fin_two]
      exact ⟨htu', h1⟩
    exact funext hall
  have hcardA : (r.image (fun t : Fin 2 → V => t (0 : Fin 2))).card = r.card :=
    Finset.card_image_of_injOn hinj0
  have hcardB : (r.image (fun t : Fin 2 → V => t (1 : Fin 2))).card = r.card := by
    rw [← hpApB]
    exact hcardA
  have hinj1 : Set.InjOn (fun t : Fin 2 → V => t (1 : Fin 2)) ↑r :=
    Finset.injOn_of_card_image_eq hcardB
  rw [holdsIn_fdBA_iff I]
  intro t ht u hu htu
  have htR : t ∈ r := ((hfin ()).mem_toFinset).mpr ht
  have huR : u ∈ r := ((hfin ()).mem_toFinset).mpr hu
  have heq : t = u := hinj1 (Finset.mem_coe.mpr htR) (Finset.mem_coe.mpr huR) htu
  rw [heq]

/-- **No unrestricted implication of the functional dependency** (Theorem 9.2.2(b)).
Over $\mathbb{N}$, $\{A \to B,\ R[A] \subseteq R[B]\}$ does not imply $B \to A$:
Figure 9.1(b) is a counter-model. -/
theorem not_implies_fdBA : ¬ Dependency.Implies ℕ deps fdBA := by
  intro h
  exact not_holdsIn_fdBA_descendingWithLoop (h descendingWithLoop descendingWithLoop_holdsIn_deps)

end FiniteImplication

/-- **Finite implication does not give unrestricted implication.**
Over $\mathbb{N}$, some finite set of functional and inclusion dependencies on a schema finitely
implies a dependency that it does not imply without restriction; compare
`finitelyImplies_of_implies`. -/
theorem Dependency.exists_finitelyImplies_not_implies :
    ∃ (S : RelationalSchema.{0, 0}) (F : Set (Dependency S)) (d : Dependency S),
      F.Finite ∧ FinitelyImplies ℕ F d ∧ ¬ Implies ℕ F d := by
  exact ⟨FiniteImplication.schema, FiniteImplication.deps,
    Dependency.inclusion FiniteImplication.indBA, (Set.finite_singleton _).insert _,
    FiniteImplication.finitelyImplies_indBA ℕ, FiniteImplication.not_implies_indBA⟩

end Cslib.Databases
