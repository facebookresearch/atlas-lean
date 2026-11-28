/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.RelationalAlgebra
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Set.Finite.Basic

/-!
# Relational calculus and its interpretations

Input atoms use the named schemas and finite relations of `Cslib.Databases`: an atom has one
term for each attribute of its relation. A head has *ordered* slots, indexed by `Fin k`, which
can contain constants and repeated variables. Answers live in the same `Tuple (Fin k) D` for
all choices of underlying domain, not in a different type of tuples for each choice.

Variables are well-scoped de Bruijn levels. The first `n` levels of a query name exactly its
free variables; a quantifier appends a fresh last level, as in Mathlib's `BoundedFormula`.
We retain the surface connectives: safe range inspects conjunction and disjunction, not their
classically equivalent encodings using only implication and falsum.

Reference: S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, §5.3, pp. 74–79.
-/

@[expose] public section

namespace Cslib.Databases.RelationalCalculus

variable {N A D : Type*} {S : N → Finset A} {n k : ℕ}

/-- An instance on a named schema, in the sense of `Expr.Conforms`. -/
structure Instance (S : N → Finset A) (D : Type*) where
  rows : N → Finset (Tuple A D)
  conforms : Expr.Conforms S rows

/-- All values occurring in the instance, not just in the relations mentioned by a query. -/
noncomputable def Instance.values [Fintype N] (I : Instance S D) : Finset D := by
  classical
  exact Finset.univ.biUnion fun r => (I.rows r).biUnion fun t => (S r).biUnion fun a =>
    (t a).toFinset

theorem Instance.mem_values [Fintype N] (I : Instance S D) {v : D} :
    v ∈ I.values ↔ ∃ r, ∃ t ∈ I.rows r, ∃ a : S r, t a = some v := by
  classical
  simp [Instance.values, Option.mem_def]

/-- Terms of domain calculus in a context of `n` variables. -/
inductive Term (D : Type*) (n : ℕ) where
  | var (i : Fin n)
  | const (c : D)

namespace Term

def eval (v : Fin n → D) : Term D n → D
  | .var i => v i
  | .const c => c

def vars : Term D n → Finset (Fin n)
  | .var i => {i}
  | .const _ => ∅

def constants : Term D n → Finset D
  | .var _ => ∅
  | .const c => {c}

end Term

/-- First-order formulas over `S`. An atom supplies exactly the attributes of its table;
quantifiers bind the new level `Fin.last n`, never another free or bound occurrence. -/
inductive Formula (S : N → Finset A) (D : Type*) : ℕ → Type _ where
  | rel {n : ℕ} (r : N) (ts : S r → Term D n) : Formula S D n
  | eq {n : ℕ} (s t : Term D n) : Formula S D n
  | conj {n : ℕ} (p q : Formula S D n) : Formula S D n
  | disj {n : ℕ} (p q : Formula S D n) : Formula S D n
  | neg {n : ℕ} (p : Formula S D n) : Formula S D n
  | ex {n : ℕ} (p : Formula S D (n + 1)) : Formula S D n
  | all {n : ℕ} (p : Formula S D (n + 1)) : Formula S D n

namespace Formula

/-- Implication is surface notation for disjunction with a negated antecedent. -/
def impl (p q : Formula S D n) := p.neg.disj q

/-- The calculus abbreviation for a biconditional (AHV p. 75). -/
def bicond (p q : Formula S D n) := (p.conj q).disj (p.neg.conj q.neg)

/-- Drop the newly bound last level. -/
def outerVars (s : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.castSucc ∈ s

/-- Free occurrences in the current context, excluding variables locally quantified. -/
def vars {n : ℕ} (p : Formula S D n) : Finset (Fin n) := match p with
  | .rel _ ts => Finset.univ.biUnion fun a => (ts a).vars
  | .eq s t => s.vars ∪ t.vars
  | .conj p q | .disj p q => p.vars ∪ q.vars
  | .neg p => p.vars
  | .ex p | .all p => outerVars p.vars

/-- All data constants appearing in the body, including below quantifiers and negations. -/
noncomputable def constants {n : ℕ} (p : Formula S D n) : Finset D := by
  classical
  exact match p with
    | .rel _ ts => Finset.univ.biUnion fun a => (ts a).constants
    | .eq s t => s.constants ∪ t.constants
    | .conj p q | .disj p q => p.constants ∪ q.constants
    | .neg p => p.constants
    | .ex p | .all p => p.constants

/-- Tarski satisfaction with witnesses in `d`. The environment assigns only the current levels;
`imageOn` additionally checks that its free valuation has range in `d`. -/
def Sat (I : Instance S D) (d : Set D) {n : ℕ} (p : Formula S D n) (v : Fin n → D) : Prop :=
  match p with
  | .rel r ts => ∃ t ∈ I.rows r, ∀ a : S r, t a = some ((ts a).eval v)
  | .eq s t => s.eval v = t.eval v
  | .conj p q => p.Sat I d v ∧ q.Sat I d v
  | .disj p q => p.Sat I d v ∨ q.Sat I d v
  | .neg p => ¬p.Sat I d v
  | .ex p => ∃ x ∈ d, p.Sat I d (Fin.snoc v x)
  | .all p => ∀ x ∈ d, p.Sat I d (Fin.snoc v x)

end Formula

/-- A query whose `k` head terms mention exactly the `n` free variables of the body. Enumerating
these variables in advance avoids extending an empty valuation to a total assignment of names. -/
structure Query (S : N → Finset A) (D : Type*) (n k : ℕ) where
  head : Fin k → Term D n
  body : Formula S D n
  head_vars : (Finset.univ.biUnion fun j => (head j).vars) = Finset.univ
  body_vars : body.vars = Finset.univ

namespace Query

variable (q : Query S D n k) (I : Instance S D)

/-- The ordered, everywhere-defined output tuple of a head valuation. -/
def output (v : Fin n → D) : Tuple (Fin k) D := fun j => some ((q.head j).eval v)

/-- The image on a specified underlying set, before adjoining any missing data values. -/
def imageOn (d : Set D) : Set (Tuple (Fin k) D) :=
  {t | ∃ v : Fin n → D, (∀ i, v i ∈ d) ∧ q.body.Sat I d v ∧ q.output v = t}

/-- Any finite underlying set gives a finite image (including for a closed query on `∅`). -/
theorem finite_imageOn {d : Set D} (hd : d.Finite) : (q.imageOn I d).Finite := by
  let _ := hd.fintype
  let emit (v : Fin n → d) := q.output fun i => v i
  refine ((Set.finite_univ.image emit).subset ?_)
  rintro t ⟨v, hv, _, rfl⟩
  exact ⟨fun i => ⟨v i, hv i⟩, Set.mem_univ _, rfl⟩

noncomputable section

variable [Fintype N]

/-- The active domain of the *whole* query and instance. -/
noncomputable def activeDomain : Finset D := by
  classical
  exact I.values ∪ q.body.constants ∪ Finset.univ.biUnion fun j => (q.head j).constants

/-- Relativization at *arbitrary* `d`: evaluation takes place on `d ∪ adom(q,I)`. -/
def relativeImage (d : Set D) := q.imageOn I (d ∪ ↑(q.activeDomain I))

theorem relativeImage_of_subset {d : Set D} (h : ↑(q.activeDomain I) ⊆ d) :
    q.relativeImage I d = q.imageOn I d := by simp [relativeImage, Set.union_eq_left.mpr h]

/-- AHV Definition 5.3.5: evaluation using precisely the active domain. -/
def activeImage := q.imageOn I (q.activeDomain I)

theorem finite_activeImage : (q.activeImage I).Finite :=
  q.finite_imageOn I (q.activeDomain I).finite_toSet

/-- AHV Definition 5.3.4. In contrast with the unrestricted *image* `imageOn I Set.univ`, the
natural interpretation is a partial finite database result, undefined on infinite images. -/
noncomputable def naturalAnswer : Option (Finset (Tuple (Fin k) D)) := by
  classical
  exact if h : (q.imageOn I Set.univ).Finite then some h.toFinset else none

omit [Fintype N] in
theorem naturalAnswer_eq_none : q.naturalAnswer I = none ↔ (q.imageOn I Set.univ).Infinite := by
  classical
  unfold naturalAnswer
  split <;> simp_all only [Set.Infinite, Option.some_ne_none, not_true_eq_false, not_false_eq_true]

/-- AHV Definition 5.3.7: invariance over every input instance and pair of relativizations. -/
def DomainIndependent : Prop := ∀ I : Instance S D, ∀ d e : Set D,
  q.relativeImage I d = q.relativeImage I e

/-- Equivalently, compare just underlying domains containing all instance and query values. -/
theorem domainIndependent_iff : q.DomainIndependent ↔
    ∀ I : Instance S D, ∀ d e : Set D, ↑(q.activeDomain I) ⊆ d → ↑(q.activeDomain I) ⊆ e →
      q.imageOn I d = q.imageOn I e := by
  constructor
  · intro h I d e hd he
    simpa [q.relativeImage_of_subset I hd, q.relativeImage_of_subset I he] using h I d e
  · intro h I d e
    exact h I _ _ Set.subset_union_right Set.subset_union_right

/-- The natural answer of a domain-independent query exists and is its finite active image. -/
theorem DomainIndependent.naturalAnswer_eq_some {q : Query S D n k} (h : q.DomainIndependent)
    (I : Instance S D) : q.naturalAnswer I = some (q.finite_activeImage I).toFinset := by
  classical
  have he : q.imageOn I Set.univ = q.activeImage I :=
    (q.domainIndependent_iff.mp h) I _ _ (Set.subset_univ _) (Set.Subset.rfl)
  simp [naturalAnswer, he, q.finite_activeImage I]

end

end Query
end Cslib.Databases.RelationalCalculus
