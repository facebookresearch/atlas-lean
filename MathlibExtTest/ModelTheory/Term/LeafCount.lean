/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.ModelTheory.Term.LeafCount
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.ModelTheory.Semantics

open scoped BigOperators

namespace FirstOrder.Language.Term

namespace LeafCountTest

inductive GenericFunction : Nat → Type
  | nullary : GenericFunction 0
  | unary : GenericFunction 1
  | ternary : GenericFunction 3

def genericLanguage : FirstOrder.Language where
  Functions := GenericFunction
  Relations := fun _ => Empty

def genericNullary : genericLanguage.Term PUnit :=
  .func .nullary ![]

def genericUnary : genericLanguage.Term PUnit :=
  .func .unary ![genericNullary]

def genericTernary : genericLanguage.Term PUnit :=
  .func .ternary ![.var (), genericUnary, genericNullary]

example : genericNullary.leafCount = 1 := by decide
example : genericUnary.leafCount = 1 := by decide
example : genericTernary.leafCount = 3 := by decide

inductive ArithmeticFunction : Nat → Type
  | constant (z : Int) : ArithmeticFunction 0
  | add : ArithmeticFunction 2
  | mul : ArithmeticFunction 2

def arithmeticLanguage : FirstOrder.Language where
  Functions := ArithmeticFunction
  Relations := fun _ => Empty

noncomputable instance arithmeticIntStructure : arithmeticLanguage.Structure Int where
  funMap := by
    intro n f xs
    cases f with
    | constant z => exact z
    | add => exact xs 0 + xs 1
    | mul => exact xs 0 * xs 1
  RelMap := by
    intro n r
    exact nomatch r

@[simp]
private theorem arithmetic_funMap_constant (z : Int) (xs : Fin 0 → Int) :
    FirstOrder.Language.Structure.funMap (L := arithmeticLanguage)
      (ArithmeticFunction.constant z) xs = z := rfl

@[simp]
private theorem arithmetic_funMap_add (xs : Fin 2 → Int) :
    FirstOrder.Language.Structure.funMap (L := arithmeticLanguage) ArithmeticFunction.add xs =
      xs 0 + xs 1 := rfl

@[simp]
private theorem arithmetic_funMap_mul (xs : Fin 2 → Int) :
    FirstOrder.Language.Structure.funMap (L := arithmeticLanguage) ArithmeticFunction.mul xs =
      xs 0 * xs 1 := rfl

inductive SourceFormula (V : Type) : Type
  | var (v : V)
  | constant (z : Int)
  | add (a b : SourceFormula V)
  | mul (a b : SourceFormula V)

namespace SourceFormula

def size {V : Type} : SourceFormula V → Nat
  | .var _ => 1
  | .constant _ => 1
  | .add a b => a.size + b.size
  | .mul a b => a.size + b.size

def eval {V : Type} (x : V → Int) : SourceFormula V → Int
  | .var v => x v
  | .constant z => z
  | .add a b => a.eval x + b.eval x
  | .mul a b => a.eval x * b.eval x

def toTerm {V : Type} : SourceFormula V → arithmeticLanguage.Term V
  | .var v => .var v
  | .constant z => .func (.constant z) ![]
  | .add a b => FirstOrder.Language.Functions.apply₂ ArithmeticFunction.add a.toTerm b.toTerm
  | .mul a b => FirstOrder.Language.Functions.apply₂ ArithmeticFunction.mul a.toTerm b.toTerm

noncomputable def ofTerm {V : Type} : arithmeticLanguage.Term V → SourceFormula V
  | .var v => .var v
  | .func (.constant z) _ => .constant z
  | .func .add terms => .add (ofTerm (terms 0)) (ofTerm (terms 1))
  | .func .mul terms => .mul (ofTerm (terms 0)) (ofTerm (terms 1))

theorem ofTerm_toTerm {V : Type} (p : SourceFormula V) :
    ofTerm p.toTerm = p := by
  induction p <;> simp [toTerm, ofTerm, FirstOrder.Language.Functions.apply₂, *]

theorem toTerm_ofTerm {V : Type} (t : arithmeticLanguage.Term V) :
    (ofTerm t).toTerm = t := by
  induction t using FirstOrder.Language.Term.rec with
  | var => rfl
  | @func n f ts ih =>
    cases f with
    | constant z =>
      simp only [ofTerm, toTerm]
      congr
      funext i
      exact Fin.elim0 i
    | add =>
      simp only [ofTerm, toTerm, FirstOrder.Language.Functions.apply₂]
      congr
      funext i
      refine Fin.cases (ih 0) ?_ i
      intro j
      refine Fin.cases (ih 1) ?_ j
      intro k
      exact Fin.elim0 k
    | mul =>
      simp only [ofTerm, toTerm, FirstOrder.Language.Functions.apply₂]
      congr
      funext i
      refine Fin.cases (ih 0) ?_ i
      intro j
      refine Fin.cases (ih 1) ?_ j
      intro k
      exact Fin.elim0 k

noncomputable def termEquiv {V : Type} :
    SourceFormula V ≃ arithmeticLanguage.Term V where
  toFun := toTerm
  invFun := ofTerm
  left_inv := ofTerm_toTerm
  right_inv := toTerm_ofTerm

private theorem size_eq_leafCount {V : Type} (p : SourceFormula V) :
    p.size = p.toTerm.leafCount := by
  induction p <;>
    simp [size, toTerm, FirstOrder.Language.Functions.apply₂,
      FirstOrder.Language.Term.leafCount, Fin.sum_univ_two, *]

private theorem eval_eq_realize {V : Type} (x : V → Int)
    (p : SourceFormula V) : p.eval x = p.toTerm.realize x := by
  induction p <;>
    simp [eval, toTerm, FirstOrder.Language.Functions.apply₂,
      FirstOrder.Language.Term.realize, *]

def sourceExample : SourceFormula (Fin 2) :=
  .mul (.add (.var 0) (.constant 3)) (.add (.var 1) (.constant (-2)))

example : sourceExample.size = 4 := by decide
example : sourceExample.toTerm.leafCount = 4 := by decide
example : sourceExample.eval ![5, 7] = 40 := by decide
example : sourceExample.toTerm.realize (![5, 7] : Fin 2 → Int) = 40 := by decide
example : (SourceFormula.constant (-3) : SourceFormula (Fin 2)).toTerm.leafCount = 1 := by
  decide

def relabeledExample : arithmeticLanguage.Term PUnit :=
  sourceExample.toTerm.relabel (fun _ => ())

example : relabeledExample.leafCount = 4 := by decide
example : relabeledExample.realize (fun _ => (5 : Int)) = 24 := by decide
example : relabeledExample.leafCount = sourceExample.toTerm.leafCount :=
  leafCount_relabel _ _

end SourceFormula

end LeafCountTest

#print axioms FirstOrder.Language.Term.leafCount
#print axioms FirstOrder.Language.Term.leafCount_var
#print axioms FirstOrder.Language.Term.leafCount_func
#print axioms FirstOrder.Language.Term.leafCount_relabel

end FirstOrder.Language.Term
