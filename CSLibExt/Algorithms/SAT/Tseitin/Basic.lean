/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tseitin transformation to conjunctive normal form
-/
module

public import CSLibExt.Logics.Propositional.CNF.Semantics
public import CSLibExt.Logics.Propositional.NaturalDeduction.Semantics

/-!
# Tseitin transformation to conjunctive normal form

The Tseitin transformation turns a propositional formula into an
equisatisfiable CNF formula of linear size by naming every compound
subformula with a fresh variable and adding three clauses that force the name
to agree with its connective.

Formulas are upstream CSLib's `Proposition Atom` (atoms, `∧`, `∨`, `→`), read by
`Proposition.evalBool`.  CNF variables are natural numbers
(`CSLibExt/Logics/Propositional/CNF`, shared with the DPLL solver): an injective
`ι : Atom → ℕ` sends the atom `a` to the variable `2 * ι a`, and the compound
subformula numbered `k` in post-order gets the variable `2 * k + 1`.  The two
families never collide.

## Main definitions

- `Proposition.tseitinAux ι A k` : the literal naming `A`, the defining clauses
  of the compound subformulas of `A`, and the next free gate number, when
  gates are numbered from `k`.
- `Proposition.tseitinAcc ι A k acc` : the linear-time builder, which prepends each
  gate's clauses to an accumulator; `tseitinAcc_eq` shows it returns the same literal
  and next gate as `tseitinAux` and a permutation of its clauses.
- `Proposition.tseitin ι A` : the defining clauses (built by `tseitinAcc`) plus the
  unit clause asserting `A`.
- `Proposition.tseitinBot ι A` : `tseitin` plus the unit clause making the atom
  `⊥` false, for the classical reading of `⊥`.

The transformation and its theorems live in `Cslib.Logic.PL.Proposition`, so they
apply with dot notation (`A.tseitin ι`); the gate clauses and the invariant of one
encoding step (`Tseitin.Spec`) live in `Cslib.Algorithms.SAT.Tseitin`.

## Main results

- `Proposition.evalBool_iff_exists_satisfies_tseitin` : for every valuation
  `v` of the atoms, `A` is true under `v` iff some assignment that agrees with
  `v` on the atom variables satisfies `tseitin ι A`.
- `Proposition.cnfSat_tseitinBot_iff` : `tseitinBot ι A` is satisfiable iff `A`
  is true under some valuation with `⊥` false.
- `Proposition.length_tseitin`, `Proposition.length_le_three_of_mem_tseitin` :
  the output has `3 * A.connectiveCount + 1` clauses, each with at most three
  literals.

## References

- G. S. Tseitin, *On the complexity of derivation in propositional calculus*,
  in *Studies in Constructive Mathematics and Mathematical Logic, Part II*,
  1968 (English translation 1970), 115-125.
-/

@[expose] public section

universe u

variable {Atom : Type u}

namespace Cslib.Algorithms.SAT.Tseitin

open Cslib.Logic.PL

/-- The complementary literal. -/
abbrev negLit (l : Nat × Bool) : Nat × Bool := (l.1, !l.2)

/-- Defining clauses for the gate literal `g` of a conjunction of literals `a` and `b`. -/
def andClauses (g a b : Nat × Bool) : CNF :=
  [[negLit g, a], [negLit g, b], [g, negLit a, negLit b]]

/-- Defining clauses for the gate literal `g` of a disjunction of literals `a` and `b`. -/
def orClauses (g a b : Nat × Bool) : CNF :=
  [[negLit g, a, b], [g, negLit a], [g, negLit b]]

/-- Defining clauses for the gate literal `g` of an implication of literals `a` and `b`. -/
def impClauses (g a b : Nat × Bool) : CNF :=
  [[negLit g, negLit a, b], [g, a], [g, negLit b]]

/-- One Tseitin step for a binary connective with defining clauses `cl`: name the
compound by the gate after the results `ra` and `rb` of its two operands. -/
def tseitinStep (cl : Nat × Bool → Nat × Bool → Nat × Bool → CNF)
    (ra rb : (Nat × Bool) × CNF × ℕ) : (Nat × Bool) × CNF × ℕ :=
  ((2 * rb.2.2 + 1, true), ra.2.1 ++ rb.2.1 ++ cl (2 * rb.2.2 + 1, true) ra.1 rb.1,
    rb.2.2 + 1)

/-- One step of the linear-time builder: prepend the three defining clauses of the new gate
to the clause list accumulated so far (which already holds both operands' clauses). -/
def accStep (cl : Nat × Bool → Nat × Bool → Nat × Bool → CNF)
    (ra rb : (Nat × Bool) × CNF × ℕ) : (Nat × Bool) × CNF × ℕ :=
  ((2 * rb.2.2 + 1, true), cl (2 * rb.2.2 + 1, true) ra.1 rb.1 ++ rb.2.1, rb.2.2 + 1)

end Cslib.Algorithms.SAT.Tseitin

namespace Cslib.Logic.PL.Proposition

open Cslib.Algorithms.SAT.Tseitin

/-- The number of binary connectives in a proposition. -/
def connectiveCount : Proposition Atom → ℕ
  | atom _ => 0
  | and A B => A.connectiveCount + B.connectiveCount + 1
  | or A B => A.connectiveCount + B.connectiveCount + 1
  | imp A B => A.connectiveCount + B.connectiveCount + 1

/-- The Tseitin encoding of `A` with gates numbered from `k`: the literal naming `A`, the
defining clauses of its compound subformulas, and the next unused gate number. This is the
reference form used in the proofs; its list concatenations make it quadratic, and `tseitin`
runs the linear-time builder `tseitinAcc` instead. -/
def tseitinAux (ι : Atom → ℕ) : Proposition Atom → ℕ → (Nat × Bool) × CNF × ℕ
  | atom a, k => ((2 * ι a, true), [], k)
  | and A B, k =>
    let ra := tseitinAux ι A k
    tseitinStep andClauses ra (tseitinAux ι B ra.2.2)
  | or A B, k =>
    let ra := tseitinAux ι A k
    tseitinStep orClauses ra (tseitinAux ι B ra.2.2)
  | imp A B, k =>
    let ra := tseitinAux ι A k
    tseitinStep impClauses ra (tseitinAux ι B ra.2.2)

/-- The linear-time Tseitin builder: like `tseitinAux`, but prepends each gate's defining
clauses to an accumulator `acc` instead of concatenating the operands' clause lists. The
clauses come out in a different order (`tseitinAcc_eq`). -/
def tseitinAcc (ι : Atom → ℕ) : Proposition Atom → ℕ → CNF → (Nat × Bool) × CNF × ℕ
  | atom a, k, acc => ((2 * ι a, true), acc, k)
  | and A B, k, acc =>
    let ra := tseitinAcc ι A k acc
    accStep andClauses ra (tseitinAcc ι B ra.2.2 ra.2.1)
  | or A B, k, acc =>
    let ra := tseitinAcc ι A k acc
    accStep orClauses ra (tseitinAcc ι B ra.2.2 ra.2.1)
  | imp A B, k, acc =>
    let ra := tseitinAcc ι A k acc
    accStep impClauses ra (tseitinAcc ι B ra.2.2 ra.2.1)

/-- The builder computes the same literal and next gate as the reference `tseitinAux`, and
its clauses are a permutation of the reference clauses followed by the accumulator. -/
theorem tseitinAcc_eq (ι : Atom → ℕ) (A : Proposition Atom) (k : ℕ) (acc : CNF) :
    ∃ X : CNF, X.Perm (tseitinAux ι A k).2.1 ∧
      tseitinAcc ι A k acc = ((tseitinAux ι A k).1, X ++ acc, (tseitinAux ι A k).2.2) := by
  induction A generalizing k acc with
  | atom a => exact ⟨[], by simp [tseitinAux], by simp [tseitinAcc, tseitinAux]⟩
  | and A B ihA ihB =>
    obtain ⟨XA, hXA, hA⟩ := ihA k acc
    obtain ⟨XB, hXB, hB⟩ := ihB (tseitinAux ι A k).2.2 (XA ++ acc)
    refine ⟨andClauses (2 * (tseitinAux ι B (tseitinAux ι A k).2.2).2.2 + 1, true)
      (tseitinAux ι A k).1 (tseitinAux ι B (tseitinAux ι A k).2.2).1 ++ (XB ++ XA), ?_, ?_⟩
    · exact List.perm_append_comm.trans
        (((hXB.append hXA).trans List.perm_append_comm).append_right _)
    · simp only [tseitinAcc, hA, hB, accStep, tseitinAux, tseitinStep, List.append_assoc]
  | or A B ihA ihB =>
    obtain ⟨XA, hXA, hA⟩ := ihA k acc
    obtain ⟨XB, hXB, hB⟩ := ihB (tseitinAux ι A k).2.2 (XA ++ acc)
    refine ⟨orClauses (2 * (tseitinAux ι B (tseitinAux ι A k).2.2).2.2 + 1, true)
      (tseitinAux ι A k).1 (tseitinAux ι B (tseitinAux ι A k).2.2).1 ++ (XB ++ XA), ?_, ?_⟩
    · exact List.perm_append_comm.trans
        (((hXB.append hXA).trans List.perm_append_comm).append_right _)
    · simp only [tseitinAcc, hA, hB, accStep, tseitinAux, tseitinStep, List.append_assoc]
  | imp A B ihA ihB =>
    obtain ⟨XA, hXA, hA⟩ := ihA k acc
    obtain ⟨XB, hXB, hB⟩ := ihB (tseitinAux ι A k).2.2 (XA ++ acc)
    refine ⟨impClauses (2 * (tseitinAux ι B (tseitinAux ι A k).2.2).2.2 + 1, true)
      (tseitinAux ι A k).1 (tseitinAux ι B (tseitinAux ι A k).2.2).1 ++ (XB ++ XA), ?_, ?_⟩
    · exact List.perm_append_comm.trans
        (((hXB.append hXA).trans List.perm_append_comm).append_right _)
    · simp only [tseitinAcc, hA, hB, accStep, tseitinAux, tseitinStep, List.append_assoc]

/-- The Tseitin CNF of `A`: the unit clause asserting the literal naming `A`, followed by
the defining clauses, built in linear time by `tseitinAcc`. -/
def tseitin (ι : Atom → ℕ) (A : Proposition Atom) : CNF :=
  let r := tseitinAcc ι A 0 []
  [r.1] :: r.2.1

/-- `tseitin` is the unit clause for `A` followed by a permutation of the reference
clauses `(tseitinAux ι A 0).2.1`. -/
theorem tseitin_eq (ι : Atom → ℕ) (A : Proposition Atom) :
    ∃ X : CNF, X.Perm (tseitinAux ι A 0).2.1 ∧ tseitin ι A = [(tseitinAux ι A 0).1] :: X := by
  obtain ⟨X, hX, h⟩ := tseitinAcc_eq ι A 0 []
  exact ⟨X, hX, by simp [tseitin, h]⟩

/-- The Tseitin CNF together with the unit clause making the atom `⊥` false. -/
def tseitinBot [Bot Atom] (ι : Atom → ℕ) (A : Proposition Atom) : CNF :=
  [(2 * ι ⊥, false)] :: tseitin ι A

/-! ### Size -/

theorem length_tseitinAux (ι : Atom → ℕ) (A : Proposition Atom) (k : ℕ) :
    (tseitinAux ι A k).2.1.length = 3 * A.connectiveCount := by
  induction A generalizing k with
  | atom a => rfl
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    simp only [tseitinAux, tseitinStep, andClauses, orClauses, impClauses, List.length_append,
      ihA, ihB, connectiveCount, List.length_cons, List.length_nil]
    omega

/-- The Tseitin CNF has three clauses per connective plus the unit clause. -/
theorem length_tseitin (ι : Atom → ℕ) (A : Proposition Atom) :
    (tseitin ι A).length = 3 * A.connectiveCount + 1 := by
  obtain ⟨X, hX, h⟩ := tseitin_eq ι A
  simp [h, hX.length_eq, length_tseitinAux]

theorem length_le_three_of_mem_tseitinAux (ι : Atom → ℕ) (A : Proposition Atom) (k : ℕ)
    {C : CNFClause} (hC : C ∈ (tseitinAux ι A k).2.1) : C.length ≤ 3 := by
  induction A generalizing k with
  | atom a => simp [tseitinAux] at hC
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    simp only [tseitinAux, tseitinStep, andClauses, orClauses, impClauses, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with (hC | hC) | hC
    · exact ihA _ hC
    · exact ihB _ hC
    · rcases hC with rfl | rfl | rfl <;> simp

/-- Every clause of the Tseitin CNF has at most three literals. -/
theorem length_le_three_of_mem_tseitin (ι : Atom → ℕ) (A : Proposition Atom)
    {C : CNFClause} (hC : C ∈ tseitin ι A) : C.length ≤ 3 := by
  obtain ⟨X, hX, h⟩ := tseitin_eq ι A
  rw [h] at hC
  rcases List.mem_cons.mp hC with rfl | hC
  · simp
  · exact length_le_three_of_mem_tseitinAux ι A 0 (hX.mem_iff.mp hC)

end Cslib.Logic.PL.Proposition

namespace Cslib.Algorithms.SAT.Tseitin

open Cslib.Logic.PL Cslib.Logic.PL.Proposition

/-! ### Literal semantics and gate clauses -/

/-- The truth value of a literal under an assignment. -/
abbrev litVal (σ : ℕ → Bool) (l : Nat × Bool) : Bool := σ l.1 == l.2

theorem litVal_eq_true_iff {σ : ℕ → Bool} {l : Nat × Bool} :
    litVal σ l = true ↔ CNFLiteral.Satisfies σ l := by
  simp [litVal, CNFLiteral.Satisfies]

@[simp]
theorem litVal_negLit (σ : ℕ → Bool) (l : Nat × Bool) :
    litVal σ (negLit l) = !litVal σ l := by
  obtain ⟨x, b⟩ := l
  cases h : σ x <;> cases b <;> simp [litVal, h]

theorem clauseSatisfies_iff {σ : ℕ → Bool} {C : CNFClause} :
    C.Satisfies σ ↔ ∃ l ∈ C, litVal σ l = true := by
  simp only [CNFClause.Satisfies, litVal_eq_true_iff]

/-- Deprecated forwarder for the shared `Cslib.Logic.PL.CNF.satisfies_append`. Kept so existing
fully qualified references to `Tseitin.satisfies_append` keep elaborating; new code should use
the shared name. -/
@[deprecated "use Cslib.Logic.PL.CNF.satisfies_append instead" (since := "2026-10-15")]
theorem satisfies_append {σ : ℕ → Bool} {φ ψ : CNF} :
    (φ ++ ψ).Satisfies σ ↔ φ.Satisfies σ ∧ ψ.Satisfies σ :=
  CNF.satisfies_append

theorem satisfies_andClauses_iff (σ : ℕ → Bool) (g a b : Nat × Bool) :
    (andClauses g a b).Satisfies σ ↔ litVal σ g = (litVal σ a && litVal σ b) := by
  simp only [andClauses, CNF.satisfies_cons, CNF.satisfies_nil, and_true, clauseSatisfies_iff,
    List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    litVal_negLit]
  cases litVal σ g <;> cases litVal σ a <;> cases litVal σ b <;> simp

theorem satisfies_orClauses_iff (σ : ℕ → Bool) (g a b : Nat × Bool) :
    (orClauses g a b).Satisfies σ ↔ litVal σ g = (litVal σ a || litVal σ b) := by
  simp only [orClauses, CNF.satisfies_cons, CNF.satisfies_nil, and_true, clauseSatisfies_iff,
    List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    litVal_negLit]
  cases litVal σ g <;> cases litVal σ a <;> cases litVal σ b <;> simp

theorem satisfies_impClauses_iff (σ : ℕ → Bool) (g a b : Nat × Bool) :
    (impClauses g a b).Satisfies σ ↔ litVal σ g = (!litVal σ a || litVal σ b) := by
  simp only [impClauses, CNF.satisfies_cons, CNF.satisfies_nil, and_true, clauseSatisfies_iff,
    List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    litVal_negLit]
  cases litVal σ g <;> cases litVal σ a <;> cases litVal σ b <;> simp

theorem vars_andClauses (g a b : Nat × Bool) :
    ∀ C ∈ andClauses g a b, ∀ l ∈ C, l.1 = g.1 ∨ l.1 = a.1 ∨ l.1 = b.1 := by
  simp only [andClauses, List.mem_cons, List.not_mem_nil, or_false]
  rintro C (rfl | rfl | rfl) l hl <;> simp at hl <;> rcases hl with rfl | rfl | rfl <;> simp

theorem vars_orClauses (g a b : Nat × Bool) :
    ∀ C ∈ orClauses g a b, ∀ l ∈ C, l.1 = g.1 ∨ l.1 = a.1 ∨ l.1 = b.1 := by
  simp only [orClauses, List.mem_cons, List.not_mem_nil, or_false]
  rintro C (rfl | rfl | rfl) l hl <;> simp at hl <;> rcases hl with rfl | rfl | rfl <;> simp

theorem vars_impClauses (g a b : Nat × Bool) :
    ∀ C ∈ impClauses g a b, ∀ l ∈ C, l.1 = g.1 ∨ l.1 = a.1 ∨ l.1 = b.1 := by
  simp only [impClauses, List.mem_cons, List.not_mem_nil, or_false]
  rintro C (rfl | rfl | rfl) l hl <;> simp at hl <;> rcases hl with rfl | rfl | rfl <;> simp

/-! ### The invariant of one encoding step -/

/-- A variable is a *gate in range* `[k, k')` if it is `2 * j + 1` with `k ≤ j < k'`. -/
def IsGate (k k' x : ℕ) : Prop := ∃ j, k ≤ j ∧ j < k' ∧ x = 2 * j + 1

/-- A variable is *allowed* for gate range `[k, k')` if it names an atom (it is even) or a
gate in range. -/
def Allowed (k k' x : ℕ) : Prop := (∃ n, x = 2 * n) ∨ IsGate k k' x

/-- A value computed from an assignment that depends only on the atom (even) variables. -/
def AtomDependent (val : (ℕ → Bool) → Bool) : Prop :=
  ∀ σ τ : ℕ → Bool, (∀ n, σ (2 * n) = τ (2 * n)) → val σ = val τ

/-- The invariant of an encoding result `r = (literal, clauses, next gate)` produced with
gates from `k`, for target value `val`: gates stay in range, every satisfying assignment
gives the literal the value `val`, and every assignment can be repaired on the gates in
range to satisfy the clauses with the literal taking the value `val`. -/
structure Spec (k : ℕ) (r : (Nat × Bool) × CNF × ℕ) (val : (ℕ → Bool) → Bool) : Prop where
  le : k ≤ r.2.2
  allowed_lit : Allowed k r.2.2 r.1.1
  allowed_clauses : ∀ C ∈ r.2.1, ∀ l ∈ C, Allowed k r.2.2 l.1
  sound : ∀ σ, r.2.1.Satisfies σ → litVal σ r.1 = val σ
  complete : ∀ σ, ∃ τ, (∀ x, ¬ IsGate k r.2.2 x → τ x = σ x) ∧ r.2.1.Satisfies τ ∧
    litVal τ r.1 = val σ

/-- Satisfaction of a clause list depends only on the assignment at the variables its
literals use. -/
theorem satisfies_of_agree {φ : CNF} {σ τ : ℕ → Bool}
    (hagree : ∀ C ∈ φ, ∀ l ∈ C, σ l.1 = τ l.1) (hσ : φ.Satisfies σ) : φ.Satisfies τ := by
  intro C hC
  obtain ⟨l, hl, hsat⟩ := hσ C hC
  exact ⟨l, hl, by simpa [CNFLiteral.Satisfies, ← hagree C hC l hl] using hsat⟩

theorem Spec.step {cl : Nat × Bool → Nat × Bool → Nat × Bool → CNF} {op : Bool → Bool → Bool}
    (hcl : ∀ σ g a b, (cl g a b).Satisfies σ ↔ litVal σ g = op (litVal σ a) (litVal σ b))
    (hclv : ∀ g a b, ∀ C ∈ cl g a b, ∀ l ∈ C, l.1 = g.1 ∨ l.1 = a.1 ∨ l.1 = b.1)
    {k : ℕ} {ra rb : (Nat × Bool) × CNF × ℕ} {va vb : (ℕ → Bool) → Bool}
    (hA : Spec k ra va) (hB : Spec ra.2.2 rb vb) (hvb : AtomDependent vb) :
    Spec k (tseitinStep cl ra rb) (fun σ ↦ op (va σ) (vb σ)) := by
  obtain ⟨hk₁, hla, hca, hsa, hxa⟩ := hA
  obtain ⟨hk₂, hlb, hcb, hsb, hxb⟩ := hB
  set ka := ra.2.2
  set kb := rb.2.2
  have hmonoA : ∀ x, Allowed k ka x → Allowed k (kb + 1) x := by
    rintro x (h | ⟨j, hj, hj', rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, by omega, rfl⟩
  have hmonoB : ∀ x, Allowed ka kb x → Allowed k (kb + 1) x := by
    rintro x (h | ⟨j, hj, hj', rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, by omega, by omega, rfl⟩
  have hg : Allowed k (kb + 1) (2 * kb + 1) := Or.inr ⟨kb, by omega, by omega, rfl⟩
  refine ⟨by simp only [tseitinStep]; omega, hg, ?_, ?_, ?_⟩
  · intro C hC l hl
    simp only [tseitinStep, List.mem_append] at hC
    rcases hC with (hC | hC) | hC
    · exact hmonoA _ (hca C hC l hl)
    · exact hmonoB _ (hcb C hC l hl)
    · rcases hclv _ _ _ C hC l hl with h | h | h <;> rw [h]
      · exact hg
      · exact hmonoA _ hla
      · exact hmonoB _ hlb
  · intro σ hσ
    simp only [tseitinStep, CNF.satisfies_append, hcl] at hσ ⊢
    rw [hσ.2, hsa σ hσ.1.1, hsb σ hσ.1.2]
  · intro σ
    obtain ⟨τ₁, hτ₁, hsat₁, hval₁⟩ := hxa σ
    obtain ⟨τ₂, hτ₂, hsat₂, hval₂⟩ := hxb τ₁
    have hevens : ∀ n, τ₁ (2 * n) = σ (2 * n) := fun n ↦
      hτ₁ _ fun ⟨j, _, _, h⟩ ↦ by omega
    rw [hvb τ₁ σ hevens] at hval₂
    obtain ⟨τ, hτdef⟩ : ∃ τ, τ = Function.update τ₂ (2 * kb + 1) (op (va σ) (vb σ)) :=
      ⟨_, rfl⟩
    have hτg : τ (2 * kb + 1) = op (va σ) (vb σ) := by rw [hτdef, Function.update_self]
    -- `τ` agrees with `τ₂` away from the new gate, and with `τ₁` on `A`'s variables
    have h2 : ∀ x, Allowed ka kb x → τ x = τ₂ x := by
      intro x hx
      rw [hτdef]
      apply Function.update_of_ne
      rintro rfl
      rcases hx with ⟨n, hn⟩ | ⟨j, -, hj, hj'⟩ <;> omega
    have h1 : ∀ x, Allowed k ka x → τ x = τ₁ x := by
      intro x hx
      rw [hτdef, Function.update_of_ne, hτ₂]
      · rintro ⟨j, hj, -, rfl⟩
        rcases hx with ⟨n, hn⟩ | ⟨i, -, hi, hi'⟩ <;> omega
      · rintro rfl
        rcases hx with ⟨n, hn⟩ | ⟨j, -, hj, hj'⟩ <;> omega
    have hlitA : litVal τ ra.1 = va σ := by rw [← hval₁, litVal, litVal, h1 _ hla]
    have hlitB : litVal τ rb.1 = vb σ := by rw [← hval₂, litVal, litVal, h2 _ hlb]
    have hlitG : litVal τ (2 * kb + 1, true) = op (va σ) (vb σ) := by simp [litVal, hτg]
    refine ⟨τ, fun x hx ↦ ?_, ?_, hlitG⟩
    · change ¬ IsGate k (kb + 1) x at hx
      have hx₂ : x ≠ 2 * kb + 1 := fun h ↦ hx ⟨kb, by omega, by omega, h⟩
      rw [hτdef, Function.update_of_ne hx₂,
        hτ₂ x fun ⟨j, hj, hj', h⟩ ↦ hx ⟨j, by omega, by omega, h⟩,
        hτ₁ x fun ⟨j, hj, hj', h⟩ ↦ hx ⟨j, hj, by omega, h⟩]
    · simp only [tseitinStep, CNF.satisfies_append, hcl]
      refine ⟨⟨satisfies_of_agree (fun C hC l hl ↦ (h1 _ (hca C hC l hl)).symm) hsat₁,
        satisfies_of_agree (fun C hC l hl ↦ (h2 _ (hcb C hC l hl)).symm) hsat₂⟩, ?_⟩
      rw [hlitA, hlitB]
      exact hlitG

/-- The value of `A` under the valuation read off the atom variables. -/
abbrev atomVal (ι : Atom → ℕ) (A : Proposition Atom) (σ : ℕ → Bool) : Bool :=
  A.evalBool (fun a ↦ σ (2 * ι a))

theorem atomDependent_atomVal (ι : Atom → ℕ) (A : Proposition Atom) :
    AtomDependent (atomVal ι A) := fun σ τ h ↦ by
  simp only [atomVal, h]

/-- The invariant holds for the encoding of every proposition. -/
theorem spec_tseitinAux (ι : Atom → ℕ) (A : Proposition Atom) (k : ℕ) :
    Spec k (tseitinAux ι A k) (atomVal ι A) := by
  induction A generalizing k with
  | atom a =>
    refine ⟨le_rfl, Or.inl ⟨ι a, rfl⟩, by simp [tseitinAux], fun σ _ ↦ ?_, fun σ ↦ ?_⟩
    · simp [tseitinAux, litVal, atomVal]
    · exact ⟨σ, fun _ _ ↦ rfl, by simp [tseitinAux], by simp [tseitinAux, litVal, atomVal]⟩
  | and A B ihA ihB =>
    exact Spec.step (op := (· && ·)) satisfies_andClauses_iff vars_andClauses (ihA k) (ihB _)
      (atomDependent_atomVal ι B)
  | or A B ihA ihB =>
    exact Spec.step (op := (· || ·)) satisfies_orClauses_iff vars_orClauses (ihA k) (ihB _)
      (atomDependent_atomVal ι B)
  | imp A B ihA ihB =>
    exact Spec.step (op := fun a b ↦ !a || b) satisfies_impClauses_iff vars_impClauses
      (ihA k) (ihB _)
      (atomDependent_atomVal ι B)

end Cslib.Algorithms.SAT.Tseitin

namespace Cslib.Logic.PL.Proposition

open Cslib.Algorithms.SAT.Tseitin

/-! ### Main theorems -/

/-- **Tseitin correctness**: for every valuation `v` of the atoms, `A` is true under `v`
iff some assignment agreeing with `v` on the atom variables satisfies the Tseitin CNF. -/
theorem evalBool_iff_exists_satisfies_tseitin {ι : Atom → ℕ} (hι : Function.Injective ι)
    (A : Proposition Atom) (v : Atom → Bool) :
    A.evalBool v = true ↔
      ∃ σ : ℕ → Bool, (∀ a, σ (2 * ι a) = v a) ∧ (tseitin ι A).Satisfies σ := by
  have hspec := spec_tseitinAux ι A 0
  obtain ⟨X, hX, htseitin⟩ := tseitin_eq ι A
  have hperm : ∀ σ, X.Satisfies σ ↔ (tseitinAux ι A 0).2.1.Satisfies σ := fun σ ↦ by
    simp only [CNF.Satisfies, hX.mem_iff]
  rw [htseitin]
  constructor
  · intro hA
    classical
    -- an assignment that is `v` on the atom variables
    let σ₀ : ℕ → Bool := fun x ↦ if h : ∃ a, 2 * ι a = x then v h.choose else false
    have hσ₀ : ∀ a, σ₀ (2 * ι a) = v a := by
      intro a
      have h : ∃ a', 2 * ι a' = 2 * ι a := ⟨a, rfl⟩
      simp only [σ₀, h, dite_true]
      congr 1
      exact hι (by have := h.choose_spec; omega)
    obtain ⟨τ, hτ, hsat, hval⟩ := hspec.complete σ₀
    have hatoms : ∀ a, τ (2 * ι a) = v a := fun a ↦ by
      rw [hτ _ fun ⟨j, _, _, h⟩ ↦ by omega, hσ₀]
    refine ⟨τ, hatoms, ?_⟩
    simp only [CNF.satisfies_cons, (hperm τ).mpr hsat, and_true]
    refine ⟨_, List.mem_singleton_self _, litVal_eq_true_iff.mp ?_⟩
    rw [hval, atomVal]
    simpa [hσ₀] using hA
  · rintro ⟨σ, hσ, hsat⟩
    simp only [CNF.satisfies_cons] at hsat
    obtain ⟨⟨l, hl, hlsat⟩, hrest⟩ := hsat
    rw [List.mem_singleton.mp hl] at hlsat
    have := hspec.sound σ ((hperm σ).mp hrest)
    rw [litVal_eq_true_iff.mpr hlsat, atomVal] at this
    simpa [hσ] using this.symm

/-- **Equisatisfiability**: the Tseitin CNF with `⊥` forced false is satisfiable iff `A` is
true under some valuation with `⊥` false. -/
theorem cnfSat_tseitinBot_iff [Bot Atom] {ι : Atom → ℕ} (hι : Function.Injective ι)
    (A : Proposition Atom) :
    CNFSat (tseitinBot ι A) ↔ ∃ v : Atom → Bool, v ⊥ = false ∧ A.evalBool v = true := by
  rw [cnfSat_iff_exists_satisfies]
  constructor
  · rintro ⟨σ, hσ⟩
    simp only [tseitinBot, CNF.satisfies_cons, CNFClause.satisfies_def, List.mem_singleton,
      exists_eq_left] at hσ
    exact ⟨fun a ↦ σ (2 * ι a), hσ.1,
      (evalBool_iff_exists_satisfies_tseitin hι A _).mpr ⟨σ, fun _ ↦ rfl, hσ.2⟩⟩
  · rintro ⟨v, hv, hA⟩
    obtain ⟨σ, hσ, hsat⟩ := (evalBool_iff_exists_satisfies_tseitin hι A v).mp hA
    refine ⟨σ, ?_⟩
    simp only [tseitinBot, CNF.satisfies_cons, CNFClause.satisfies_def, List.mem_singleton,
      exists_eq_left, hσ, hv, hsat, and_true]

end Cslib.Logic.PL.Proposition
