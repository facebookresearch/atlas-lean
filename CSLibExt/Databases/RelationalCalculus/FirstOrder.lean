/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.RelationalCalculus
public import Mathlib.ModelTheory.Semantics

/-!
# Relativized calculus as ordinary first-order satisfaction

A unary predicate names the chosen quantification domain inside the ambient value type. A
relation's finite set of named attributes is enumerated only at the interface to Mathlib's
positional relation symbols; the same enumeration is inverted in the structure. Literal data
values are fixed parameters (interpreted by the identity valuation), not quantified variables.
-/

@[expose] public section

namespace Cslib.Databases.RelationalCalculus

variable {N A D : Type*} {S : N → Finset A} {n : ℕ}

/-- One predicate per table and one unary predicate for the underlying domain. -/
inductive Symbol (S : N → Finset A) : ℕ → Type _ where
  | table (r : N) : Symbol S (Fintype.card (S r))
  | domain : Symbol S 1

def language (S : N → Finset A) : FirstOrder.Language where
  Functions _ := Empty
  Relations := Symbol S

/-- Interpret the table symbols by the finite instance and the unary guard by `d`. -/
@[instance_reducible]
noncomputable def model (I : Instance S D) (d : Set D) : (language S).Structure D where
  funMap f := nomatch f
  RelMap := fun {k} (R : Symbol S k) => match R with
    | .domain => fun v => v 0 ∈ d
    | .table r => fun v => ∃ t ∈ I.rows r, ∀ a : S r, t a = some (v (Fintype.equivFin _ a))

def termFO : Term D n → (language S).Term (D ⊕ Fin n)
  | .var i => .var (.inr i)
  | .const c => .var (.inl c)

def guardFO (S : N → Finset A) (n : ℕ) : (language S).BoundedFormula D (n + 1) :=
  .rel (Symbol.domain (S := S)) fun _ => .var (.inr (Fin.last n))

/-- Compile a surface formula into a Mathlib bounded formula, guarding its quantifiers. -/
noncomputable def Formula.toFirstOrder {n : ℕ} (p : Formula S D n) :
    (language S).BoundedFormula D n := match p with
  | .rel r ts => .rel (Symbol.table r) fun i => termFO (ts ((Fintype.equivFin _).symm i))
  | .eq s t => .equal (termFO s) (termFO t)
  | .conj p q => p.toFirstOrder ⊓ q.toFirstOrder
  | .disj p q => p.toFirstOrder ⊔ q.toFirstOrder
  | .neg p => p.toFirstOrder.not
  | .ex p => (guardFO S _ ⊓ p.toFirstOrder).ex
  | .all p => ((guardFO S _).imp p.toFirstOrder).all

/-- Relativized satisfaction agrees with realization in the guarded first-order structure,
even when the guard is empty. -/
theorem Formula.realize_toFirstOrder (I : Instance S D) (d : Set D) (p : Formula S D n)
    (v : Fin n → D) : letI := model I d; p.toFirstOrder.Realize id v ↔ p.Sat I d v := by
  let _ := model I d
  have ht {m : ℕ} (w : Fin m → D) (t : Term D m) :
      (termFO (S := S) t).realize (Sum.elim id w) = t.eval w := by cases t <;> rfl
  have hg {m : ℕ} (w : Fin m → D) (x : D) :
      (guardFO S m).Realize id (Fin.snoc w x) ↔ x ∈ d := by
    change (Fin.snoc (α := fun _ => D) w x (Fin.last m)) ∈ d ↔ x ∈ d
    rw [Fin.snoc_last]
  induction p with
  | rel r ts =>
    change (∃ t ∈ I.rows r, ∀ a : S r, t a = some (_ : D)) ↔ _
    simp [Sat, ht]
  | eq s t => exact (congrArg₂ Eq (ht v s) (ht v t)).to_iff
  | conj _ _ ih jh => simp [toFirstOrder, Sat, ih, jh]
  | disj _ _ ih jh => simp [toFirstOrder, Sat, ih, jh]
  | neg _ ih => simp [toFirstOrder, Sat, ih]
  | ex _ ih => simp [toFirstOrder, Sat, hg, ih]
  | all _ ih => simp [toFirstOrder, Sat, hg, ih]

end Cslib.Databases.RelationalCalculus
