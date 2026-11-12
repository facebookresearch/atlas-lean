/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Peano arithmetic and Robinson's Q in first-order logic
-/
module

public import CSLibExt.Logics.FirstOrder.Syntax
public import Mathlib.ModelTheory.Semantics

/-!
# Peano arithmetic and Robinson's Q in first-order logic

The first-order language of arithmetic, with function symbols `0`, `S`, `+`, `*`
and no relation symbols besides equality (Mathlib's built-in equality). Bound
variables are Mathlib's de Bruijn levels: in a body with `m + 1` bound variables
in scope, index `0` is the outermost one, and a new quantifier binds the highest
index (see `FirstOrder.Language.BoundedFormula.all` and `realize_all`).

* `ArithmeticFunctions`, `ArithmeticLanguage` : the language.
* `numeral n` : the closed term for `n`.
* `substBoundTerm`, `substBoundFormula` (in `CSLibExt/Logics/FirstOrder/Syntax.lean`,
  neutral `Cslib.Logic.FOL` namespace): substitute a one-variable term for the
  outermost bound variable, keeping the bound-variable count: the term the
  induction schema needs, since in `∀x (φ(x) → φ(S x))` the term `S x` still
  mentions the bound variable `x`. Polymorphic in the free-variable type, so they
  apply to bodies with parameters (`BoundedFormula (Fin k) 1`) as well as to
  parameter-free bodies.
* `qAxiomOne` … `qAxiomSeven` : Robinson's Q axioms.
* `QTheory` : the finite theory of the Q axioms.
* `inductionAxiom φ` : the induction axiom for a body `φ` with `k` parameters
  (`φ : BoundedFormula (Fin k) 1`): the parameters stay free while the induction
  variable is substituted and quantified, then the whole axiom is universally
  closed over the parameters via `BoundedFormula.relabel` + `.alls`.
* `PATheory` : `QTheory` together with all induction axioms, for all `k` and all
  bodies. This is full Peano arithmetic, with induction for formulas with
  parameters.
* `Arithmetic.instNat` : the standard structure on `ℕ`.
* `nat_models_Q`, `nat_models_PA` : `ℕ` is a model of Q and of PA; in
  particular PA is consistent by soundness.

## References

- H. Enderton, *A Mathematical Introduction to Logic*, 2nd ed., Academic Press, 2001, §3.1
  (Robinson's Q) and §3.4 (Peano arithmetic).
- G. Boolos, J. Burgess, R. Jeffrey, *Computability and Logic*, 5th ed., Cambridge University
  Press, 2007, Chapters 14-16.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Logic.FOL

open FirstOrder FirstOrder.Language

/-- Function symbols of arithmetic: `0`, `S`, `+`, `*`. -/
inductive ArithmeticFunctions : ℕ → Type
  /-- The constant `0`. -/
  | zero : ArithmeticFunctions 0
  /-- The successor function `S`. -/
  | succ : ArithmeticFunctions 1
  /-- Addition. -/
  | add : ArithmeticFunctions 2
  /-- Multiplication. -/
  | mul : ArithmeticFunctions 2

/-- The first-order language of arithmetic: function symbols `0`, `S`, `+`, `*`, and no
relation symbols besides equality. -/
def ArithmeticLanguage : FirstOrder.Language where
  Functions := ArithmeticFunctions
  Relations := fun _ => Empty

namespace Arithmetic

/-- The term `0` with free variables of any type. -/
def zeroTerm {α : Type*} : ArithmeticLanguage.Term α :=
  Term.func .zero fun i => i.elim0

/-- The successor of a term. -/
def succTerm (t : ArithmeticLanguage.Term Empty) : ArithmeticLanguage.Term Empty :=
  Term.func .succ ![t]

/-- The sum of two terms. -/
def addTerm (s t : ArithmeticLanguage.Term Empty) : ArithmeticLanguage.Term Empty :=
  Term.func .add ![s, t]

/-- The product of two terms. -/
def mulTerm (s t : ArithmeticLanguage.Term Empty) : ArithmeticLanguage.Term Empty :=
  Term.func .mul ![s, t]

/-- The numeral for `n`: `0`, `S 0`, `S (S 0)`, …. -/
def numeral : ℕ → ArithmeticLanguage.Term Empty
  | 0 => zeroTerm
  | n + 1 => succTerm (numeral n)

/-- The bound variable `i` as a term, in a context with `n` bound variables in scope. -/
def bvar {n : ℕ} (i : Fin n) : ArithmeticLanguage.Term (Empty ⊕ Fin n) :=
  Term.var (Sum.inr i)

/-- The term `S x` where `x` is the outermost bound variable. -/
def succBvar {α : Type*} : ArithmeticLanguage.Term (α ⊕ Fin 1) :=
  Term.func .succ ![Term.var (Sum.inr (0 : Fin 1))]

/-- The term `0` with no bound variables, viewed in a context with `n` bound variables. -/
def zeroTermBound {n : ℕ} : ArithmeticLanguage.Term (Empty ⊕ Fin n) :=
  Term.func .zero fun i => i.elim0

/-! ### Robinson's Q -/

/-- The successor of a term in a bounded context. -/
def tSucc {n : ℕ} (t : ArithmeticLanguage.Term (Empty ⊕ Fin n)) :
    ArithmeticLanguage.Term (Empty ⊕ Fin n) :=
  Term.func .succ ![t]

/-- The sum of two terms in a bounded context. -/
def tAdd {n : ℕ} (s t : ArithmeticLanguage.Term (Empty ⊕ Fin n)) :
    ArithmeticLanguage.Term (Empty ⊕ Fin n) :=
  Term.func .add ![s, t]

/-- The product of two terms in a bounded context. -/
def tMul {n : ℕ} (s t : ArithmeticLanguage.Term (Empty ⊕ Fin n)) :
    ArithmeticLanguage.Term (Empty ⊕ Fin n) :=
  Term.func .mul ![s, t]

/-- Equality of two terms as a bounded formula. -/
def eqF {n : ℕ} (s t : ArithmeticLanguage.Term (Empty ⊕ Fin n)) :
    ArithmeticLanguage.BoundedFormula Empty n :=
  BoundedFormula.equal s t

/-- Q1: `∀x. ¬ S x = 0`. -/
def qAxiomOne : ArithmeticLanguage.Sentence :=
  ((eqF (tSucc (bvar (0 : Fin 1))) zeroTermBound).not).all

/-- Q2: `∀x ∀y. S x = S y → x = y`. -/
def qAxiomTwo : ArithmeticLanguage.Sentence :=
  ((eqF (tSucc (bvar (0 : Fin 2))) (tSucc (bvar (1 : Fin 2)))).imp
    (eqF (bvar (0 : Fin 2)) (bvar (1 : Fin 2)))).all.all

/-- Q3: `∀x. x + 0 = x`. -/
def qAxiomThree : ArithmeticLanguage.Sentence :=
  (eqF (tAdd (bvar (0 : Fin 1)) zeroTermBound) (bvar (0 : Fin 1))).all

/-- Q4: `∀x ∀y. x + S y = S (x + y)`. -/
def qAxiomFour : ArithmeticLanguage.Sentence :=
  (eqF (tAdd (bvar (0 : Fin 2)) (tSucc (bvar (1 : Fin 2))))
    (tSucc (tAdd (bvar (0 : Fin 2)) (bvar (1 : Fin 2))))).all.all

/-- Q5: `∀x. x * 0 = 0`. -/
def qAxiomFive : ArithmeticLanguage.Sentence :=
  (eqF (tMul (bvar (0 : Fin 1)) zeroTermBound) zeroTermBound).all

/-- Q6: `∀x ∀y. x * S y = x * y + x`. -/
def qAxiomSix : ArithmeticLanguage.Sentence :=
  (eqF (tMul (bvar (0 : Fin 2)) (tSucc (bvar (1 : Fin 2))))
    (tAdd (tMul (bvar (0 : Fin 2)) (bvar (1 : Fin 2))) (bvar (0 : Fin 2)))).all.all

/-- Q7: `∀x. x = 0 ∨ ∃y. x = S y`. -/
def qAxiomSeven : ArithmeticLanguage.Sentence :=
  ((eqF (bvar (0 : Fin 1)) zeroTermBound).not.imp
    ((eqF (bvar (0 : Fin 2)) (tSucc (bvar (1 : Fin 2)))).ex)).all

/-- Robinson's Q: the finite theory of the seven axioms above. -/
def QTheory : ArithmeticLanguage.Theory :=
  {qAxiomOne, qAxiomTwo, qAxiomThree, qAxiomFour, qAxiomFive, qAxiomSix, qAxiomSeven}

/-! ### Peano arithmetic -/

/-- The induction axiom for a body `φ` with `k` parameters, where `φ : BoundedFormula
(Fin k) 1` has one bound variable (the induction variable `x`) and `k` free variables
(the parameters `y⃗`):
`∀y⃗ [φ(0, y⃗) → (∀x (φ(x, y⃗) → φ(S x, y⃗))) → ∀x φ(x, y⃗)]`.
The body is built with the parameters free (using `instantiate` and
`substBoundFormula`, which substitute and quantify the induction variable while the
parameters stay free), then `BoundedFormula.relabel` turns the parameters into bound
variables and `.alls` universally closes over them. For `k = 0` this is the
parameter-free induction axiom.
Source: H. Enderton, A Mathematical Introduction to Logic, 2nd ed., Academic Press, 2001,
§3.4. -/
def inductionAxiom {k : ℕ} (φ : ArithmeticLanguage.BoundedFormula (Fin k) 1) :
    ArithmeticLanguage.Sentence :=
  (((instantiate zeroTerm φ).relabel (Sum.inr : Fin k → Empty ⊕ Fin k)).imp
    ((((φ.imp (substBoundFormula succBvar φ)).all).relabel
      (Sum.inr : Fin k → Empty ⊕ Fin k)).imp
      (φ.all.relabel (Sum.inr : Fin k → Empty ⊕ Fin k)))).alls

/-- Peano arithmetic: Q together with the induction axiom for every body with any
number `k` of parameters. This is full Peano arithmetic: induction is available for
formulas with parameters, as in the textbook. -/
def PATheory : ArithmeticLanguage.Theory :=
  QTheory ∪ ⋃ k : ℕ, Set.range (inductionAxiom (k := k))

/-! ### The standard model -/

/-- The standard structure on `ℕ`: `0`, `S`, `+`, `*` with their usual meanings. -/
instance instNat : ArithmeticLanguage.Structure ℕ where
  funMap f ts := match f with
    | .zero => 0
    | .succ => ts 0 + 1
    | .add => ts 0 + ts 1
    | .mul => ts 0 * ts 1
  RelMap R _ := R.elim

/-- A numeral realizes to the number it names. -/
theorem realize_numeral (n : ℕ) (v : Empty → ℕ) :
    (numeral n).realize v = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [numeral, succTerm, Term.realize]
    change (fun i => Term.realize v (![numeral n] i)) 0 + 1 = n + 1
    simp only [Matrix.cons_val_zero, ih]

/-- A bound variable realizes to the assigned value. -/
theorem realize_bvar {n : ℕ} (i : Fin n) (v : Empty → ℕ) (xs : Fin n → ℕ) :
    (bvar i).realize (Sum.elim v xs) = xs i := rfl

/-- The term `0` realizes to `0`. -/
theorem realize_zeroTermBound {n : ℕ} (v : Empty → ℕ) (xs : Fin n → ℕ) :
    (zeroTermBound).realize (Sum.elim v xs) = 0 := rfl

/-- The successor of a term realizes to one more than the term. -/
theorem realize_tSucc {n : ℕ} (t : ArithmeticLanguage.Term (Empty ⊕ Fin n))
    (v : Empty → ℕ) (xs : Fin n → ℕ) :
    (tSucc t).realize (Sum.elim v xs) = (t.realize (Sum.elim v xs)) + 1 := rfl

/-- The sum of two terms realizes to the sum of their values. -/
theorem realize_tAdd {n : ℕ} (s t : ArithmeticLanguage.Term (Empty ⊕ Fin n))
    (v : Empty → ℕ) (xs : Fin n → ℕ) :
    (tAdd s t).realize (Sum.elim v xs) =
      (s.realize (Sum.elim v xs)) + (t.realize (Sum.elim v xs)) := rfl

/-- The product of two terms realizes to the product of their values. -/
theorem realize_tMul {n : ℕ} (s t : ArithmeticLanguage.Term (Empty ⊕ Fin n))
    (v : Empty → ℕ) (xs : Fin n → ℕ) :
    (tMul s t).realize (Sum.elim v xs) =
      (s.realize (Sum.elim v xs)) * (t.realize (Sum.elim v xs)) := rfl

/-- A sentence holds in `ℕ` iff it holds under the eliminator assignment: truth of a
sentence does not depend on the (necessarily empty) assignment. -/
theorem sentence_realize_iff (ψ : ArithmeticLanguage.Sentence) :
    (ℕ ⊨ ψ) ↔ Formula.Realize ψ (fun x => (x.elim : ℕ)) := by
  constructor
  · intro h
    exact (realize_congr (φ := ψ) (fun a _ => a.elim) _).mp h
  · intro h
    exact (realize_congr (φ := ψ) (fun a _ => a.elim) _).mpr h

/-- `ℕ` is a model of Robinson's Q. -/
theorem nat_models_Q : ∀ ψ ∈ QTheory, (ℕ ⊨ ψ) := by
  intro ψ hψ
  simp only [QTheory, Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
  rcases hψ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [sentence_realize_iff, qAxiomOne, realize_all_formula]
    intro a
    change ¬ ((tSucc (bvar (0 : Fin 1))).realize
        (Sum.elim (fun x => x.elim) (fun _ => a)) =
      (zeroTermBound).realize (Sum.elim (fun x => x.elim) (fun _ => a)))
    rw [realize_tSucc, realize_bvar, realize_zeroTermBound]
    omega
  · rw [sentence_realize_iff, qAxiomTwo, realize_all_formula]
    intro a
    rw [BoundedFormula.realize_all]
    intro b
    change ((tSucc (bvar (0 : Fin 2))).realize
        (Sum.elim (fun x => x.elim) (@Fin.snoc 1 (fun _ => ℕ) (fun _ => a) b)) =
      (tSucc (bvar (1 : Fin 2))).realize
        (Sum.elim (fun x => x.elim) (@Fin.snoc 1 (fun _ => ℕ) (fun _ => a) b))) →
      ((bvar (0 : Fin 2)).realize (Sum.elim (fun x => x.elim)
          (@Fin.snoc 1 (fun _ => ℕ) (fun _ => a) b)) =
        (bvar (1 : Fin 2)).realize (Sum.elim (fun x => x.elim)
            (@Fin.snoc 1 (fun _ => ℕ) (fun _ => a) b)))
    rw [realize_tSucc, realize_tSucc, realize_bvar, realize_bvar]
    have h0 : @Fin.snoc 1 (fun _ => ℕ) (fun _ => a) b 0 = a := by simp only [Fin.snoc_apply_zero]
    have hlast : (1 : Fin 2) = Fin.last 1 := by decide
    have h1 : @Fin.snoc 1 (fun _ => ℕ) (fun _ => a) b 1 = b := by rw [hlast, Fin.snoc_last]
    rw [h0, h1]
    intro h
    omega
  · rw [sentence_realize_iff, qAxiomThree, realize_all_formula]
    intro a
    change ((tAdd (bvar (0 : Fin 1)) zeroTermBound).realize
        (Sum.elim (fun x => x.elim) (fun _ => a)) =
      (bvar (0 : Fin 1)).realize (Sum.elim (fun x => x.elim) (fun _ => a)))
    rw [realize_tAdd, realize_bvar, realize_zeroTermBound]
    omega
  · rw [sentence_realize_iff, qAxiomFour, realize_all_formula]
    intro a
    rw [BoundedFormula.realize_all]
    intro b
    change ((tAdd (bvar (0 : Fin 2)) (tSucc (bvar (1 : Fin 2)))).realize
        (Sum.elim (fun x => x.elim) (@Fin.snoc 1 (fun _ => ℕ) (fun _ => a) b)) =
      (tSucc (tAdd (bvar (0 : Fin 2)) (bvar (1 : Fin 2)))).realize
        (Sum.elim (fun x => x.elim) (@Fin.snoc 1 (fun _ => ℕ) (fun _ => a) b)))
    rw [realize_tAdd, realize_tSucc, realize_tSucc, realize_tAdd, realize_bvar, realize_bvar]
    have h0 : @Fin.snoc 1 (fun _ => ℕ) (fun _ => a) b 0 = a := by simp only [Fin.snoc_apply_zero]
    have hlast : (1 : Fin 2) = Fin.last 1 := by decide
    have h1 : @Fin.snoc 1 (fun _ => ℕ) (fun _ => a) b 1 = b := by rw [hlast, Fin.snoc_last]
    rw [h0, h1]
    omega
  · rw [sentence_realize_iff, qAxiomFive, realize_all_formula]
    intro a
    change ((tMul (bvar (0 : Fin 1)) zeroTermBound).realize
        (Sum.elim (fun x => x.elim) (fun _ => a)) =
      (zeroTermBound).realize (Sum.elim (fun x => x.elim) (fun _ => a)))
    rw [realize_tMul, realize_bvar, realize_zeroTermBound]
    omega
  · rw [sentence_realize_iff, qAxiomSix, realize_all_formula]
    intro a
    rw [BoundedFormula.realize_all]
    intro b
    change ((tMul (bvar (0 : Fin 2)) (tSucc (bvar (1 : Fin 2)))).realize
        (Sum.elim (fun x => x.elim) (@Fin.snoc 1 (fun _ => ℕ) (fun _ => a) b)) =
      (tAdd (tMul (bvar (0 : Fin 2)) (bvar (1 : Fin 2))) (bvar (0 : Fin 2))).realize
        (Sum.elim (fun x => x.elim) (@Fin.snoc 1 (fun _ => ℕ) (fun _ => a) b)))
    rw [realize_tMul, realize_tSucc, realize_tAdd, realize_tMul, realize_bvar, realize_bvar]
    have h0 : @Fin.snoc 1 (fun _ => ℕ) (fun _ => a) b 0 = a := by simp only [Fin.snoc_apply_zero]
    have hlast : (1 : Fin 2) = Fin.last 1 := by decide
    have h1 : @Fin.snoc 1 (fun _ => ℕ) (fun _ => a) b 1 = b := by rw [hlast, Fin.snoc_last]
    rw [h0, h1]
    exact Nat.mul_succ a b
  · rw [sentence_realize_iff, qAxiomSeven, realize_all_formula]
    intro a
    rw [BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_ex]
    intro hne
    refine ⟨a - 1, ?_⟩
    change (bvar (0 : Fin 2)).realize
        (Sum.elim (fun x => x.elim) (@Fin.snoc 1 (fun _ => ℕ) (fun _ => a) (a - 1))) =
      (tSucc (bvar (1 : Fin 2))).realize
        (Sum.elim (fun x => x.elim) (@Fin.snoc 1 (fun _ => ℕ) (fun _ => a) (a - 1)))
    rw [realize_bvar, realize_tSucc, realize_bvar]
    have h0 : @Fin.snoc 1 (fun _ => ℕ) (fun _ => a) (a - 1) 0 = a := by
      simp only [Fin.snoc_apply_zero]
    have hlast : (1 : Fin 2) = Fin.last 1 := by decide
    have h1 : @Fin.snoc 1 (fun _ => ℕ) (fun _ => a) (a - 1) 1 = a - 1 := by
      rw [hlast, Fin.snoc_last]
    rw [h0, h1]
    have hne' : a ≠ 0 := hne
    omega

/-- `ℕ` is a model of Peano arithmetic, including the induction axioms with
parameters: fix the parameter values `ys`, then induct on the induction variable. -/
theorem nat_models_PA : ∀ ψ ∈ PATheory, (ℕ ⊨ ψ) := by
  intro ψ hψ
  rcases hψ with hψ | hψ
  · exact nat_models_Q ψ hψ
  · rw [Set.mem_iUnion] at hψ
    obtain ⟨k, φ, rfl⟩ := hψ
    rw [sentence_realize_iff, inductionAxiom, BoundedFormula.realize_alls]
    intro ys
    rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp]
    intro hbase hstep
    rw [Formula.realize_relabel_sumInr, realize_all_formula]
    intro a
    induction a with
    | zero =>
      rw [Formula.realize_relabel_sumInr] at hbase
      have h := (realize_instantiate_formula (M := ℕ) zeroTerm φ ys).mp hbase
      have hz : (zeroTerm : ArithmeticLanguage.Term (Fin k)).realize ys = 0 := rfl
      rw [hz] at h
      exact h
    | succ n ih =>
      rw [Formula.realize_relabel_sumInr] at hstep
      have hstep' := (realize_all_formula (φ.imp (substBoundFormula succBvar φ)) ys).mp hstep
      have himp := (BoundedFormula.realize_imp.mp (hstep' n))
      have hsubst := (realize_substBoundFormula (α := Fin k)
        (succBvar (α := Fin k)) φ ys (fun _ => n)).mp (himp ih)
      have hsucc : (succBvar (α := Fin k)).realize (Sum.elim ys fun _ => (fun _ => n) 0) =
          n + 1 := rfl
      have hupd : Function.update (fun _ => n) (0 : Fin 1) (n + 1) = fun _ => n + 1 := by
        funext j
        rw [Fin.fin_one_eq_zero j]
        simp only [Function.update_self]
      rw [hsucc, hupd] at hsubst
      exact hsubst

end Arithmetic

end Cslib.Logic.FOL
