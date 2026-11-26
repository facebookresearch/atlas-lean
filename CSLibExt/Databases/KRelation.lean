/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.RelationalAlgebra
public import Mathlib.Data.Finsupp.Basic

/-!
# Positive algebra of K-relations

In the named model, a tuple over a heading is defined on exactly its attributes. The possible
values and the set of such tuples need not be finite: it is the set of *nonzero annotations*
that must be finite. `KRelation.positiveAlgebra` implements the six operations on these maps.
With Boolean disjunction and conjunction they give set semantics; with natural-number coefficients
they count multiplicities. In a polynomial semiring over `ℕ`, projection can add two different
input variables and a compatible join can multiply them into a monomial.

Finite support does not require a nonempty fibre to have nonzero sum or a product of nonzero
coefficients to be nonzero. Selection and bijective renaming filter and transport support exactly;
union, projection and join give support bounds instead. In particular, a join tuple is determined
by two restrictions, one in each input support whenever their product is nonzero.

Reference: T. J. Green, G. Karvounarakis and V. Tannen, *Provenance Semirings*, PODS 2007,
§3, Definitions 3.1–3.2 and Proposition 3.3; §4, Definition 4.1 and Figure 5 (polynomial tags).
-/

@[expose] public section

namespace Cslib.Databases

variable {A : Type*}

local notation "Rows(" D ", " S ")" => Subtype (Tuple.IsOver (D := D) S)

/-- A $K$-relation on a finite heading $S$ assigns a coefficient to each tuple defined exactly
on $S$. Its support consists of the tuples with nonzero coefficient and must be finite. Only a
distinguished zero in $K$ is needed here (Green, Karvounarakis and Tannen, Definition 3.1). -/
abbrev KRelation (D K : Type*) [Zero K] (S : Finset A) := Rows(D, S) →₀ K

namespace KRelation

variable {D K : Type*} {S T : Finset A}

/-- Restrict a schema tuple to a subheading: keep its values on the smaller heading and be
undefined elsewhere. -/
def onSubheading [DecidableEq A] (h : T ⊆ S) (t : Rows(D, S)) : Rows(D, T) :=
  ⟨t.val.restrict T, t.property.restrict h⟩

/-- Move a tuple along a bijection of headings: read at the inverse image of each target
attribute, and leave the tuple undefined outside the target heading. -/
def reindexTuple [DecidableEq A] {U V : Finset A} (f : U ≃ V) (q : Rows(D, U)) : Rows(D, V) :=
  ⟨fun a => if ha : a ∈ V then q.val (f.symm ⟨a, ha⟩) else none, fun a => by
    by_cases ha : a ∈ V
    · simpa [ha] using (q.property _).2 (f.symm ⟨a, ha⟩).property
    · simp [ha]⟩

/-- A bijection $e:S\simeq T$ of the attributes induces a bijection of schema tuples. The
forward map gives attribute $e(a)$ the old value at $a$ and is undefined outside $T$. Its
inverse reindexes by the inverse bijection; no extension to a permutation of all names is needed. -/
def relabel [DecidableEq A] (e : S ≃ T) : Rows(D, S) ≃ Rows(D, T) where
  toFun := reindexTuple e
  invFun := reindexTuple e.symm
  left_inv := undo e
  right_inv := undo e.symm
where
  undo {U V : Finset A} (f : U ≃ V) (q : Rows(D, U)) :
      reindexTuple f.symm (reindexTuple f q) = q := by
    apply Subtype.ext
    funext a
    by_cases ha : a ∈ U
    · simp [reindexTuple, ha]
    · simp [reindexTuple, ha, q.property.eq_none ha]

@[simp] theorem relabel_val [DecidableEq A] (e : S ≃ T) (t : Rows(D, S)) (a : T) :
    (relabel e t).val a = t.val (e.symm a) := by simp [relabel, reindexTuple, a.property]

/-- A tuple over the union of two headings is determined by its two restrictions. This is the
injection that bounds the support of a join by pairs of supported inputs. -/
theorem restrictions_injective [DecidableEq A] :
    Function.Injective (fun t : Rows(D, S ∪ T) =>
      (onSubheading (Finset.subset_union_left (s₂ := T)) t,
        onSubheading (Finset.subset_union_right (s₁ := S)) t)) := by
  intro t u h
  apply Subtype.ext
  funext a
  by_cases hs : a ∈ S
  · simpa [onSubheading, hs] using congrArg (fun p => p.1.val a) h
  by_cases ht : a ∈ T
  · simpa [onSubheading, ht] using congrArg (fun p => p.2.val a) h
  · have ha : a ∉ S ∪ T := by simp [hs, ht]
    rw [t.property.eq_none ha, u.property.eq_none ha]

/-- The signature of the positive operations on a heading-indexed family of $K$-relations:
empty and union at one heading, projection to a subheading, selection by a predicate, join to
the union heading and transport to a bijectively renamed heading. -/
structure PositiveSignature (A D K : Type*) [DecidableEq A] [Zero K] where
  empty {S : Finset A} : KRelation D K S
  union {S : Finset A} : KRelation D K S → KRelation D K S → KRelation D K S
  project {S T : Finset A} : T ⊆ S → KRelation D K S → KRelation D K T
  select {S : Finset A} : (Rows(D, S) → Prop) → KRelation D K S → KRelation D K S
  join {S T : Finset A} : KRelation D K S → KRelation D K T → KRelation D K (S ∪ T)
  rename {S T : Finset A} : (S ≃ T) → KRelation D K S → KRelation D K T

/-- For a commutative semiring $K$, the empty relation has all coefficients zero, union adds
coefficients, projection sums over the supported restriction fibre, and selection keeps a
coefficient where its predicate holds and gives zero elsewhere. At a union-heading tuple, join
multiplies the coefficients of its two restrictions; bijective renaming pulls coefficients back
along the induced tuple bijection. All six outputs have finite support (Green, Karvounarakis
and Tannen, §3, Definition 3.2 and Proposition 3.3). -/
noncomputable def positiveAlgebra (A D K : Type*) [DecidableEq A] [CommSemiring K] :
    PositiveSignature A D K := by
  classical
  exact {
    empty := 0
    union := (· + ·)
    project := fun h => Finsupp.mapDomain (onSubheading h)
    select := fun p => Finsupp.filter p
    join := fun {S T} r s => by
      let split := fun t : Rows(D, S ∪ T) =>
        (onSubheading (Finset.subset_union_left (s₂ := T)) t,
          onSubheading (Finset.subset_union_right (s₁ := S)) t)
      refine Finsupp.ofSupportFinite (fun t => r (split t).1 * s (split t).2) ?_
      have finitePairs := (r.support ×ˢ s.support).finite_toSet
      refine (finitePairs.preimage (f := split) restrictions_injective.injOn).subset ?_
      intro t ht
      exact Finset.mem_product.mpr
        ⟨Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul ht),
         Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul ht)⟩
    rename := fun e => Finsupp.equivMapDomain (relabel e) }

variable [DecidableEq A] [CommSemiring K]

/-- The empty $K$-relation on any heading gives coefficient zero to every tuple. -/
@[simp] theorem empty_apply (t : Rows(D, S)) : (positiveAlgebra A D K).empty t = 0 := rfl

/-- At each tuple, union on a common heading adds the two coefficients in $K$. -/
@[simp] theorem union_apply (r s : KRelation D K S) (t : Rows(D, S)) :
    (positiveAlgebra A D K).union r s t = r t + s t := rfl

open scoped Classical in
/-- Projection sums over the finite subset of the input support whose restriction is the output
tuple. In particular, several different source tuples can contribute to the same coefficient. -/
theorem project_apply (h : T ⊆ S) (r : KRelation D K S) (t : Rows(D, T)) :
    (positiveAlgebra A D K).project h r t = ∑ u ∈ r.support with onSubheading h u = t, r u := by
  simp [positiveAlgebra, Finsupp.mapDomain_apply, Finsupp.sum, Finsupp.single_apply, Finset.sum_ite]

open scoped Classical in
/-- Selection retains a tuple’s coefficient if its predicate holds and gives zero otherwise,
equivalently multiplying the coefficient by the predicate’s one-or-zero indicator. -/
@[simp] theorem select_apply (p : Rows(D, S) → Prop) (r : KRelation D K S) (t : Rows(D, S)) :
    (positiveAlgebra A D K).select p r t = if p t then r t else 0 := rfl

/-- The coefficient of a join at a union-heading tuple is the product of the two input
coefficients at its restrictions. These restrictions agree on every shared attribute. -/
@[simp] theorem join_apply (r : KRelation D K S) (s : KRelation D K T) (t : Rows(D, S ∪ T)) :
    (positiveAlgebra A D K).join r s t = r (onSubheading Finset.subset_union_left t) *
      s (onSubheading Finset.subset_union_right t) := rfl

/-- After renaming attributes by a bijection, the coefficient at a target tuple is the original
coefficient at the tuple pulled back to the source heading. -/
@[simp] theorem rename_apply (e : S ≃ T) (r : KRelation D K S) (t : Rows(D, T)) :
    (positiveAlgebra A D K).rename e r t = r ((relabel e).symm t) := rfl

open scoped Classical in
/-- The support of a union is contained in the union of the supports. Equality need not hold:
nonzero summands at the same tuple can add to zero. -/
theorem support_union_subset (r s : KRelation D K S) :
    ((positiveAlgebra A D K).union r s).support ⊆ r.support ∪ s.support :=
  Finsupp.support_add

open scoped Classical in
/-- Every supported projection is the restriction of a supported input. The reverse inclusion
need not hold: a finite nonempty fibre can have total coefficient zero. -/
theorem support_project_subset (h : T ⊆ S) (r : KRelation D K S) :
    ((positiveAlgebra A D K).project h r).support ⊆ r.support.image (onSubheading h) :=
  Finsupp.mapDomain_support

open scoped Classical in
/-- Selection filters the actual input support exactly, for every commutative semiring. -/
theorem support_select (p : Rows(D, S) → Prop) (r : KRelation D K S) :
    ((positiveAlgebra A D K).select p r).support = r.support.filter p := rfl

/-- Both restrictions of a supported join tuple belong to the corresponding input supports.
The converse need not hold when two nonzero coefficients can multiply to zero. -/
theorem restrictions_mem_of_mem_join (r : KRelation D K S) (s : KRelation D K T)
    {t : Rows(D, S ∪ T)} (ht : t ∈ ((positiveAlgebra A D K).join r s).support) :
    onSubheading Finset.subset_union_left t ∈ r.support ∧
      onSubheading Finset.subset_union_right t ∈ s.support := by
  have h := Finsupp.mem_support_iff.mp ht
  rw [join_apply] at h
  exact ⟨Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul h),
    Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul h)⟩

/-- A bijective renaming maps the input support exactly onto the output support. -/
theorem support_rename (e : S ≃ T) (r : KRelation D K S) :
    ((positiveAlgebra A D K).rename e r).support = r.support.map (relabel e).toEmbedding := rfl

end KRelation

end Cslib.Databases
