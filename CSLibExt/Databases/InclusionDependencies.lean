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

/-!
# Inclusion dependencies and finite implication

The two sides of an inclusion dependency may name different relations, with different
attributes. Their projections are comparable because both produce tuples indexed by the same
`Fin k`. The embeddings selecting columns enforce distinctness on each side, not across sides.

An instance gives one extent (set of rows) per relation. Both implication predicates are
relative to a fixed common value type `V`, of any universe level; take `V = ℕ` for the book's
countably infinite domain. They differ only in which instances are quantified over, not in the
type of values allowed. Functional dependencies use `FD.HoldsIn` on the named extent.

## References

* S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995,
  §§3.1–3.3 (schemas, tuples and instances), Definition 9.1.1 (inclusion dependency) and
  Definition 9.2.1 (unrestricted and finite implication).
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

end Cslib.Databases
