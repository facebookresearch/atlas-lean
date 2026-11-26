/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.RelationalAlgebra
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Indicator

/-!
# Bag relations and bag relational algebra

`Tuple.Over D S` is the type of tuples with values in `D` defined exactly on the finite schema `S`.
`BagRelation D S` assigns a natural-number multiplicity to each such tuple, with finite support.
Neither the attribute type nor the value type needs to be finite.

* `BagRelation.select` keeps an entire multiplicity when a condition on the schema is true.
* `BagRelation.project` sums the multiplicities in each fiber of tuple restriction.
* `BagRelation.join` multiplies the multiplicities of the two restrictions of an output tuple.
* `BagRelation.union` adds multiplicities on a common schema.
* `BagRelation.rename` transports multiplicities along a permutation of the attributes.
* `BagRelation.ofFinset` embeds a finite set relation by assigning multiplicity one to its members.

## References

* T. J. Green, G. Karvounarakis and V. Tannen, *Provenance semirings*, PODS 2007, §3,
  Definition 3.2 and Proposition 3.3, specialized to the semiring of natural numbers.
-/

@[expose] public section

namespace Cslib.Databases

variable {A D : Type*}

namespace Tuple

abbrev Over (D : Type*) (S : Finset A) := {t : Tuple A D // t.IsOver S}

def Over.restrict [DecidableEq A] {S T : Finset A} (h : T ⊆ S) (t : Over D S) : Over D T :=
  ⟨t.val.restrict T, t.property.restrict h⟩

def Over.rename (f : Equiv.Perm A) (S : Finset A) : Over D S ≃ Over D (S.map f.toEmbedding) where
  toFun t := ⟨t.val ∘ f.symm, fun a => by
    simpa [Finset.mem_map_equiv] using t.property (f.symm a)⟩
  invFun t := ⟨t.val ∘ f, fun a => by
    simpa [Finset.mem_map_equiv] using t.property (f a)⟩
  left_inv t := Subtype.ext (funext fun a => by simp)
  right_inv t := Subtype.ext (funext fun a => by simp)

end Tuple

-- A bag relation assigns finitely supported natural-number multiplicities to exact-schema tuples.
abbrev BagRelation (D : Type*) (S : Finset A) := Tuple.Over D S →₀ ℕ

namespace BagRelation

open scoped BigOperators

variable {S T : Finset A}

section Selection

variable [DecidableEq A] [DecidableEq D]

def select (c : Cond A D) (_hc : c.attrs ⊆ S) (r : BagRelation D S) : BagRelation D S :=
  r.filter fun t => c.eval t.val = true

@[simp] theorem select_apply (c : Cond A D) (hc : c.attrs ⊆ S) (r : BagRelation D S)
    (t : Tuple.Over D S) : select c hc r t = if c.eval t.val = true then r t else 0 :=
  Finsupp.filter_apply _ _ _

theorem support_select (c : Cond A D) (hc : c.attrs ⊆ S) (r : BagRelation D S) :
    (select c hc r).support = r.support.filter (fun t => c.eval t.val = true) :=
  Finsupp.support_filter _ _

end Selection

section Projection

variable [DecidableEq A]

noncomputable def project (h : T ⊆ S) (r : BagRelation D S) : BagRelation D T :=
  r.mapDomain (Tuple.Over.restrict h)

open Classical in
theorem project_apply (h : T ⊆ S) (r : BagRelation D S) (t : Tuple.Over D T) :
    project h r t = ∑ u ∈ r.support with u.restrict h = t, r u := by
  simp [project, Finsupp.mapDomain_apply, Finsupp.sum, Finsupp.single_apply, Finset.sum_ite]

open Classical in
theorem support_project (h : T ⊆ S) (r : BagRelation D S) :
    (project h r).support = r.support.image (Tuple.Over.restrict h) :=
  Finsupp.mapDomain_support_of_subsingletonAddUnits _ _

end Projection

section Join

variable [DecidableEq A]

theorem merge_restrictions (t : Tuple.Over D (S ∪ T)) :
    Tuple.merge (t.val.restrict S) (t.val.restrict T) = t.val := by
  funext a
  by_cases hs : a ∈ S
  · cases ha : t.val a <;> simp [Tuple.merge, hs, ha]
  · by_cases ht : a ∈ T
    · simp [Tuple.merge, hs, ht]
    · have hn := t.property.eq_none (a := a) (by simp [hs, ht])
      simp [Tuple.merge, hs, ht, hn]

-- The two restrictions of a tuple agree wherever they are both defined.
theorem compatible_restrictions (t : Tuple.Over D (S ∪ T)) :
    (t.val.restrict S).Compatible (t.val.restrict T) := by
  intro a
  by_cases hs : a ∈ S <;> by_cases ht : a ∈ T <;> simp [hs, ht]

noncomputable def join (r : BagRelation D S) (s : BagRelation D T) : BagRelation D (S ∪ T) := by
  classical
  let pairs := (r.support ×ˢ s.support).filter fun p => p.1.val.Compatible p.2.val
  refine Finsupp.onFinset (pairs.image fun p =>
    ⟨p.1.val.merge p.2.val, Tuple.isOver_merge p.1.property p.2.property⟩)
    (fun t => r (t.restrict Finset.subset_union_left) * s (t.restrict Finset.subset_union_right)) ?_
  intro t ht
  have hl : r (t.restrict Finset.subset_union_left) ≠ 0 := fun h => ht (by simp [h])
  have hr : s (t.restrict Finset.subset_union_right) ≠ 0 := fun h => ht (by simp [h])
  refine Finset.mem_image.mpr ⟨(t.restrict Finset.subset_union_left,
    t.restrict Finset.subset_union_right), ?_, Subtype.ext (merge_restrictions t)⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finsupp.mem_support_iff.mpr hl, Finsupp.mem_support_iff.mpr hr⟩, compatible_restrictions t⟩

@[simp] theorem join_apply (r : BagRelation D S) (s : BagRelation D T)
    (t : Tuple.Over D (S ∪ T)) :
    join r s t =
      r (t.restrict Finset.subset_union_left) * s (t.restrict Finset.subset_union_right) := by
  simp only [join, Finsupp.onFinset_apply]

theorem mem_support_join (r : BagRelation D S) (s : BagRelation D T)
    (t : Tuple.Over D (S ∪ T)) :
    t ∈ (join r s).support ↔
      t.restrict Finset.subset_union_left ∈ r.support ∧
      t.restrict Finset.subset_union_right ∈ s.support := by
  simp only [Finsupp.mem_support_iff, join_apply, ne_eq, mul_eq_zero, not_or]

theorem join_apply_merge (r : BagRelation D S) (s : BagRelation D T)
    (u : Tuple.Over D S) (v : Tuple.Over D T) (h : u.val.Compatible v.val) :
    join r s ⟨u.val.merge v.val, Tuple.isOver_merge u.property v.property⟩ = r u * s v := by
  rw [join_apply]
  exact congrArg₂ (fun a b => r a * s b) (Subtype.ext (Tuple.restrict_merge_left u.property))
    (Subtype.ext (Tuple.restrict_merge_right v.property h))

end Join

noncomputable def union (r s : BagRelation D S) : BagRelation D S := r + s

@[simp] theorem union_apply (r s : BagRelation D S) (t : Tuple.Over D S) :
    union r s t = r t + s t := Finsupp.add_apply _ _ _

theorem mem_support_union (r s : BagRelation D S) (t : Tuple.Over D S) :
    t ∈ (union r s).support ↔ t ∈ r.support ∨ t ∈ s.support := by
  simp only [Finsupp.mem_support_iff, union_apply, ne_eq, Nat.add_eq_zero_iff, not_and_or]

noncomputable def rename (f : Equiv.Perm A) (r : BagRelation D S) :
    BagRelation D (S.map f.toEmbedding) :=
  r.embDomain (Tuple.Over.rename f S).toEmbedding

@[simp] theorem rename_apply (f : Equiv.Perm A) (r : BagRelation D S)
    (t : Tuple.Over D (S.map f.toEmbedding)) :
    rename f r t = r ((Tuple.Over.rename f S).symm t) := by
  obtain ⟨u, rfl⟩ := (Tuple.Over.rename f S).surjective t
  rw [Equiv.symm_apply_apply]
  exact Finsupp.embDomain_apply_self _ _ _

theorem support_rename (f : Equiv.Perm A) (r : BagRelation D S) :
    (rename f r).support = r.support.map (Tuple.Over.rename f S).toEmbedding :=
  Finsupp.support_embDomain _ _

noncomputable def ofFinset (r : Finset (Tuple A D)) (_hr : IsOver S r) : BagRelation D S :=
  Finsupp.indicator (r.preimage Subtype.val Subtype.coe_injective.injOn) fun _ _ => 1

open Classical in
@[simp] theorem ofFinset_apply (r : Finset (Tuple A D)) (hr : IsOver S r) (t : Tuple.Over D S) :
    ofFinset r hr t = if t.val ∈ r then 1 else 0 := by
  simp [ofFinset, Finsupp.indicator_apply, Finset.mem_preimage]

theorem mem_support_ofFinset (r : Finset (Tuple A D)) (hr : IsOver S r) (t : Tuple.Over D S) :
    t ∈ (ofFinset r hr).support ↔ t.val ∈ r := by
  classical
  by_cases h : t.val ∈ r <;> simp [Finsupp.mem_support_iff, h]

-- Forgetting the typing proofs in the support recovers the original set relation.
theorem support_ofFinset (r : Finset (Tuple A D)) (hr : IsOver S r) :
    (ofFinset r hr).support.map ⟨Subtype.val, Subtype.coe_injective⟩ = r := by
  ext t
  rw [Finset.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (mem_support_ofFinset r hr u).mp hu
  · intro ht
    exact ⟨⟨t, hr t ht⟩, (mem_support_ofFinset r hr _).mpr ht, rfl⟩

end BagRelation

-- The schema-indexed operations of the positive algebra on bags.
structure BagAlgebra (A D : Type*) where
  empty (S : Finset A) : BagRelation D S
  select [DecidableEq A] [DecidableEq D] {S : Finset A} (c : Cond A D) (hc : c.attrs ⊆ S)
    (r : BagRelation D S) : BagRelation D S
  project [DecidableEq A] {S T : Finset A} (h : T ⊆ S) (r : BagRelation D S) : BagRelation D T
  join [DecidableEq A] {S T : Finset A} (r : BagRelation D S) (s : BagRelation D T) :
    BagRelation D (S ∪ T)
  union {S : Finset A} (r s : BagRelation D S) : BagRelation D S
  rename {S : Finset A} (f : Equiv.Perm A) (r : BagRelation D S) :
    BagRelation D (S.map f.toEmbedding)
  ofFinset {S : Finset A} (r : Finset (Tuple A D)) (hr : IsOver S r) : BagRelation D S

/-- **Bag relations and bag relational algebra.** Over a finite schema, a bag is a finitely
supported natural-number function on exact-schema tuples. The empty bag is zero. Selection on
schema attributes retains or zeros each entire count, projection to a sub-schema sums each
restriction fiber, natural join on the schema union multiplies the counts of the two restrictions,
and same-schema union adds counts. Attribute permutations transport counts to the renamed schema.
Finite set relations on the exact schema embed by their zero-one indicator functions. -/
noncomputable def bagRelationalAlgebra (A D : Type*) : BagAlgebra A D where
  empty _ := 0
  select := BagRelation.select
  project := BagRelation.project
  join := BagRelation.join
  union := BagRelation.union
  rename := BagRelation.rename
  ofFinset := BagRelation.ofFinset

end Cslib.Databases
