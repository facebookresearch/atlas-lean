/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.ArithmeticCircuit
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import MathlibExt.LinearAlgebra.Matrix.FinPowReindex

/-!
# Arithmetic circuit composition and block reindexing

Substitution of subcircuits into circuit inputs and parallel copies of a circuit,
with evaluation and size lemmas, plus block reindexing of matrices for recursive
constructions.
-/

set_option autoImplicit false

universe u v w v'

namespace Cslib.Complexity.Algebraic

@[expose] public section

namespace ArithmeticCircuit

def embedOperand {F : Type u} {A' : Type v'} {m n : ℕ} (h : m ≤ n) :
    ArithmeticOperand F A' m → ArithmeticOperand F A' n
  | .constant x => .constant x
  | .input a' => .input a'
  | .node k => .node ⟨k.val, Nat.lt_of_lt_of_le k.isLt h⟩

def substOperand {F : Type u} {A : Type v} {A' : Type v'}
    (D : ArithmeticCircuit F A' A) {jval N : ℕ} (h1 : D.size ≤ N)
    (h2 : jval + D.size ≤ N) : ArithmeticOperand F A jval → ArithmeticOperand F A' N
  | .constant x => .constant x
  | .input a => embedOperand h1 (D.output a)
  | .node k => .node ⟨k.val + D.size, Nat.lt_of_lt_of_le (Nat.add_lt_add_right k.isLt D.size) h2⟩

def substGate {F : Type u} {A : Type v} {A' : Type v'}
    (D : ArithmeticCircuit F A' A) {jval N : ℕ} (h1 : D.size ≤ N)
    (h2 : jval + D.size ≤ N) : ArithmeticGate F A jval → ArithmeticGate F A' N
  | .add a b => .add (substOperand D h1 h2 a) (substOperand D h1 h2 b)
  | .sub a b => .sub (substOperand D h1 h2 a) (substOperand D h1 h2 b)
  | .mul a b => .mul (substOperand D h1 h2 a) (substOperand D h1 h2 b)

/-- Composition by substitution: D's gates first, then C's gates with inputs replaced by D's outputs and node references shifted by `D.size`. -/
def subst {F : Type u} {A : Type v} {A' : Type v'} {B : Type w}
    (C : ArithmeticCircuit F A B) (D : ArithmeticCircuit F A' A) :
    ArithmeticCircuit F A' B where
  size := D.size + C.size
  gate := fun i =>
    if h : i.val < D.size then
      D.gate ⟨i.val, h⟩
    else
      have hle : D.size ≤ i.val := Nat.le_of_not_gt h
      have hj : i.val - D.size < C.size := by omega
      have h2 : (i.val - D.size) + D.size ≤ i.val := by omega
      substGate D hle h2 (C.gate ⟨i.val - D.size, hj⟩)
  output := fun b =>
    substOperand D (Nat.le_add_right D.size C.size) (by omega) (C.output b)

/-- Size of composition is the sum of sizes. -/
theorem size_subst {F : Type u} {A : Type v} {A' : Type v'} {B : Type w}
    (C : ArithmeticCircuit F A B) (D : ArithmeticCircuit F A' A) :
    (C.subst D).size = D.size + C.size := rfl

private theorem operandEval_congr {F : Type u} {A' : Type v'} {N : ℕ}
    (x : A' → F) {c1 c2 : Fin N → F} (h : ∀ k, c1 k = c2 k)
    (o : ArithmeticOperand F A' N) :
    o.evaluate x c1 = o.evaluate x c2 := by
  cases o with
  | constant _ => rfl
  | input _ => rfl
  | node k => exact h k

private theorem gateEval_congr {F : Type u} {A' : Type v'} {N : ℕ}
    [Add F] [Sub F] [Mul F] (x : A' → F) {c1 c2 : Fin N → F}
    (h : ∀ k, c1 k = c2 k) (g : ArithmeticGate F A' N) :
    g.evaluate x c1 = g.evaluate x c2 := by
  cases g with
  | add a b =>
    simp [ArithmeticGate.evaluate, operandEval_congr x h a, operandEval_congr x h b]
  | sub a b =>
    simp [ArithmeticGate.evaluate, operandEval_congr x h a, operandEval_congr x h b]
  | mul a b =>
    simp [ArithmeticGate.evaluate, operandEval_congr x h a, operandEval_congr x h b]

private theorem eval_embedOperand {F : Type u} {A' : Type v'} {m N : ℕ}
    (x : A' → F) (h1 : m ≤ N) (o : ArithmeticOperand F A' m)
    (cS : Fin N → F) (cD : Fin m → F)
    (hag : ∀ k : Fin m, ∀ hk : k.val < N, cS ⟨k.val, hk⟩ = cD k) :
    (embedOperand h1 o).evaluate x cS = o.evaluate x cD := by
  cases o with
  | constant _ => rfl
  | input _ => rfl
  | node k =>
    simp [embedOperand, ArithmeticOperand.evaluate]
    exact hag k _

private theorem eval_substOperand {F : Type u} {A : Type v} {A' : Type v'}
    [Add F] [Sub F] [Mul F]
    (D : ArithmeticCircuit F A' A) {jval N : ℕ} (h1 : D.size ≤ N)
    (h2 : jval + D.size ≤ N)
    (x : A' → F) (o : ArithmeticOperand F A jval)
    (cS : Fin N → F) (cC : Fin jval → F)
    (hD : ∀ k : Fin D.size, ∀ hk : k.val < N, cS ⟨k.val, hk⟩ = D.evaluateNode x k)
    (hC : ∀ k : Fin jval, ∀ hk : k.val + D.size < N, cS ⟨k.val + D.size, hk⟩ = cC k) :
    (substOperand D h1 h2 o).evaluate x cS = o.evaluate (fun a => D.evaluate x a) cC := by
  cases o with
  | constant _ => rfl
  | input a =>
    exact eval_embedOperand x h1 (D.output a) cS (D.evaluateNode x)
      (fun k hk => hD k hk)
  | node k =>
    simp [substOperand, ArithmeticOperand.evaluate]
    exact hC k _

private theorem eval_substGate {F : Type u} {A : Type v} {A' : Type v'}
    [Add F] [Sub F] [Mul F]
    (D : ArithmeticCircuit F A' A) {jval N : ℕ} (h1 : D.size ≤ N)
    (h2 : jval + D.size ≤ N)
    (x : A' → F) (g : ArithmeticGate F A jval)
    (cS : Fin N → F) (cC : Fin jval → F)
    (hD : ∀ k : Fin D.size, ∀ hk : k.val < N, cS ⟨k.val, hk⟩ = D.evaluateNode x k)
    (hC : ∀ k : Fin jval, ∀ hk : k.val + D.size < N, cS ⟨k.val + D.size, hk⟩ = cC k) :
    (substGate D h1 h2 g).evaluate x cS = g.evaluate (fun a => D.evaluate x a) cC := by
  cases g with
  | add a b =>
    simp [substGate, ArithmeticGate.evaluate,
      eval_substOperand D h1 h2 x a cS cC hD hC,
      eval_substOperand D h1 h2 x b cS cC hD hC]
  | sub a b =>
    simp [substGate, ArithmeticGate.evaluate,
      eval_substOperand D h1 h2 x a cS cC hD hC,
      eval_substOperand D h1 h2 x b cS cC hD hC]
  | mul a b =>
    simp [substGate, ArithmeticGate.evaluate,
      eval_substOperand D h1 h2 x a cS cC hD hC,
      eval_substOperand D h1 h2 x b cS cC hD hC]

private theorem evaluateNode_subst_aux {F : Type u} {A : Type v} {A' : Type v'} {B : Type w}
    [Add F] [Sub F] [Mul F]
    (C : ArithmeticCircuit F A B) (D : ArithmeticCircuit F A' A)
    (x : A' → F) (n : ℕ) :
    ∀ (i : Fin (C.subst D).size), i.val < n →
      (∀ h : i.val < D.size, (C.subst D).evaluateNode x i = D.evaluateNode x ⟨i.val, h⟩) ∧
      (∀ (_hle : D.size ≤ i.val) (hj : i.val - D.size < C.size),
        (C.subst D).evaluateNode x i =
          C.evaluateNode (fun a => D.evaluate x a) ⟨i.val - D.size, hj⟩) := by
  induction n with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intro i hi
    by_cases hlt : i.val < n
    · exact ih i hlt
    · have heq : i.val = n := by omega
      constructor
      · intro h
        have hS := evaluateNode.eq_1 (C.subst D) x i
        have hD := evaluateNode.eq_1 D x ⟨i.val, h⟩
        rw [hS, hD]
        have hgate : (C.subst D).gate i = D.gate ⟨i.val, h⟩ := by simp [subst, h]
        rw [hgate]
        apply gateEval_congr
        intro k
        have hk : k.val < n := by omega
        have hltS : k.val < (C.subst D).size := Nat.lt_trans k.isLt i.isLt
        have hDlt : k.val < D.size := Nat.lt_trans k.isLt h
        have hih := (ih ⟨k.val, hltS⟩ hk).1 hDlt
        exact hih
      · intro hle hj
        have hnlt : ¬ i.val < D.size := Nat.not_lt_of_ge hle
        have hS := evaluateNode.eq_1 (C.subst D) x i
        have hC := evaluateNode.eq_1 C (fun a => D.evaluate x a) ⟨i.val - D.size, hj⟩
        rw [hS, hC]
        have h2 : (i.val - D.size) + D.size ≤ i.val := by omega
        have hgate : (C.subst D).gate i =
            substGate D hle h2 (C.gate ⟨i.val - D.size, hj⟩) := by simp [subst, hnlt]
        rw [hgate]
        apply eval_substGate
        · intro k hk
          have hklt : k.val < n := by omega
          have hltS : k.val < (C.subst D).size := Nat.lt_trans hk i.isLt
          have hih := (ih ⟨k.val, hltS⟩ hklt).1 k.isLt
          exact hih
        · intro k hk
          have hsumlt : k.val + D.size < n := by omega
          have hltS : k.val + D.size < (C.subst D).size :=
            Nat.lt_trans hk i.isLt
          have hle' : D.size ≤ k.val + D.size := Nat.le_add_left D.size k.val
          have hj' : (k.val + D.size) - D.size < C.size := by
            have hsub : (k.val + D.size) - D.size = k.val := Nat.add_sub_cancel k.val D.size
            rw [hsub]
            exact Nat.lt_trans k.isLt hj
          have hih := (ih ⟨k.val + D.size, hltS⟩ hsumlt).2 hle' hj'
          have hsub : (k.val + D.size) - D.size = k.val := Nat.add_sub_cancel k.val D.size
          have hFinEq : (⟨(k.val + D.size) - D.size, hj'⟩ : Fin C.size) =
              ⟨k.val, Nat.lt_trans k.isLt hj⟩ := Fin.ext hsub
          rw [hFinEq] at hih
          exact hih

/-- Evaluation of a substituted circuit equals substituted evaluation. -/
theorem evaluate_subst {F : Type u} {A : Type v} {A' : Type v'} {B : Type w}
    [Add F] [Sub F] [Mul F]
    (C : ArithmeticCircuit F A B) (D : ArithmeticCircuit F A' A)
    (x : A' → F) (b : B) :
    (C.subst D).evaluate x b = C.evaluate (fun a => D.evaluate x a) b := by
  have h1 : D.size ≤ (C.subst D).size := by simp [subst]
  have h2 : C.size + D.size ≤ (C.subst D).size := by simp [subst]; omega
  have hall := evaluateNode_subst_aux C D x ((C.subst D).size + 1)
  have hD : ∀ k : Fin D.size, ∀ hk : k.val < (C.subst D).size,
      (C.subst D).evaluateNode x ⟨k.val, hk⟩ = D.evaluateNode x k := by
    intro k hk
    have hklt : k.val < (C.subst D).size + 1 := by omega
    have hih := (hall ⟨k.val, hk⟩ hklt).1 k.isLt
    exact hih
  have hC : ∀ k : Fin C.size, ∀ hk : k.val + D.size < (C.subst D).size,
      (C.subst D).evaluateNode x ⟨k.val + D.size, hk⟩ =
        C.evaluateNode (fun a => D.evaluate x a) k := by
    intro k hk
    have hsumlt : k.val + D.size < (C.subst D).size + 1 := by omega
    have hle' : D.size ≤ k.val + D.size := Nat.le_add_left D.size k.val
    have hj' : (k.val + D.size) - D.size < C.size := by
      have hsub : (k.val + D.size) - D.size = k.val := Nat.add_sub_cancel k.val D.size
      rw [hsub]
      exact k.isLt
    have hih := (hall ⟨k.val + D.size, hk⟩ hsumlt).2 hle' hj'
    have hsub : (k.val + D.size) - D.size = k.val := Nat.add_sub_cancel k.val D.size
    have hFinEq : (⟨(k.val + D.size) - D.size, hj'⟩ : Fin C.size) = k := Fin.ext hsub
    rw [hFinEq] at hih
    exact hih
  exact eval_substOperand D h1 h2 x (C.output b)
    ((C.subst D).evaluateNode x) (C.evaluateNode (fun a => D.evaluate x a))
    (fun k hk => hD k hk) (fun k hk => hC k hk)

def parallelOperand {F : Type u} {A : Type v} {B : Type w}
    (c : ArithmeticCircuit F A B) (r : ℕ) (t : Fin r)
    {n N : ℕ} (hn : n ≤ c.size)
    (hN : ∀ j : Fin n,
      (finProdFinEquiv (t, ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩) : Fin (r * c.size)).val < N) :
    ArithmeticOperand F A n → ArithmeticOperand F (Fin r × A) N
  | .constant x => .constant x
  | .input a => .input (t, a)
  | .node j => .node ⟨(finProdFinEquiv (t, ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩)).val, hN j⟩

def parallelGate {F : Type u} {A : Type v} {B : Type w}
    (c : ArithmeticCircuit F A B) (r : ℕ) (t : Fin r)
    {n N : ℕ} (hn : n ≤ c.size)
    (hN : ∀ j : Fin n,
      (finProdFinEquiv (t, ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩) : Fin (r * c.size)).val < N) :
    ArithmeticGate F A n → ArithmeticGate F (Fin r × A) N
  | .add a b => .add (parallelOperand c r t hn hN a) (parallelOperand c r t hn hN b)
  | .sub a b => .sub (parallelOperand c r t hn hN a) (parallelOperand c r t hn hN b)
  | .mul a b => .mul (parallelOperand c r t hn hN a) (parallelOperand c r t hn hN b)

/-- Parallel copies of a circuit: `r` consecutive copies of `c`, copy `t`
reading inputs `(t, a)` and writing outputs `(t, b)`. Gates are laid out in
`finProdFinEquiv` order over `Fin r × Fin c.size`. -/
def parallel {F : Type u} {A : Type v} {B : Type w}
    (c : ArithmeticCircuit F A B) (r : ℕ) :
    ArithmeticCircuit F (Fin r × A) (Fin r × B) where
  size := r * c.size
  gate := fun i =>
    let t := (finProdFinEquiv.symm i).1
    let k := (finProdFinEquiv.symm i).2
    have hn : k.val ≤ c.size := Nat.le_of_lt k.isLt
    have hval : (finProdFinEquiv (t, k)).val = i.val := by
      have h : finProdFinEquiv (finProdFinEquiv.symm i) = i :=
        Equiv.apply_symm_apply _ _
      have hp : (finProdFinEquiv.symm i) = (t, k) := (Prod.eta _).symm
      rw [hp] at h
      exact congrArg Fin.val h
    have hN : ∀ j : Fin k.val,
        (finProdFinEquiv (t, ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩) : Fin (r * c.size)).val < i.val := by
      intro j
      have hj : j.val < k.val := j.isLt
      have hlt : (finProdFinEquiv (t, ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩) : Fin (r * c.size)).val <
          (finProdFinEquiv (t, k) : Fin (r * c.size)).val := by
        show j.val + c.size * t.val < k.val + c.size * t.val
        exact Nat.add_lt_add_right hj _
      rw [hval] at hlt
      exact hlt
    parallelGate c r t hn hN (c.gate k)
  output := fun tb =>
    match tb with
    | (t, b) =>
      parallelOperand c r t (Nat.le_refl c.size)
        (fun j => (finProdFinEquiv (t, ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_refl c.size)⟩)).isLt)
        (c.output b)

/-- Size of parallel copies is the number of copies times the size. -/
theorem size_parallel {F : Type u} {A : Type v} {B : Type w}
    (c : ArithmeticCircuit F A B) (r : ℕ) :
    (c.parallel r).size = r * c.size := rfl

private theorem eval_parallelOperand {F : Type u} {A : Type v} {B : Type w}
    [Add F] [Sub F] [Mul F]
    (c : ArithmeticCircuit F A B) (r : ℕ) (t : Fin r)
    {n N : ℕ} (hn : n ≤ c.size)
    (hN : ∀ j : Fin n,
      (finProdFinEquiv (t, ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩) : Fin (r * c.size)).val < N)
    (x : Fin r × A → F) (o : ArithmeticOperand F A n)
    (cP : Fin N → F) (cC : Fin n → F)
    (h : ∀ j : Fin n,
      cP ⟨(finProdFinEquiv (t, ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩)).val, hN j⟩ = cC j) :
    (parallelOperand c r t hn hN o).evaluate x cP = o.evaluate (fun a => x (t, a)) cC := by
  cases o with
  | constant _ => rfl
  | input _ => rfl
  | node j =>
    simp [parallelOperand, ArithmeticOperand.evaluate]
    exact h j

private theorem eval_parallelGate {F : Type u} {A : Type v} {B : Type w}
    [Add F] [Sub F] [Mul F]
    (c : ArithmeticCircuit F A B) (r : ℕ) (t : Fin r)
    {n N : ℕ} (hn : n ≤ c.size)
    (hN : ∀ j : Fin n,
      (finProdFinEquiv (t, ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩) : Fin (r * c.size)).val < N)
    (x : Fin r × A → F) (g : ArithmeticGate F A n)
    (cP : Fin N → F) (cC : Fin n → F)
    (h : ∀ j : Fin n,
      cP ⟨(finProdFinEquiv (t, ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩)).val, hN j⟩ = cC j) :
    (parallelGate c r t hn hN g).evaluate x cP = g.evaluate (fun a => x (t, a)) cC := by
  cases g with
  | add a b =>
    simp [parallelGate, ArithmeticGate.evaluate,
      eval_parallelOperand c r t hn hN x a cP cC h,
      eval_parallelOperand c r t hn hN x b cP cC h]
  | sub a b =>
    simp [parallelGate, ArithmeticGate.evaluate,
      eval_parallelOperand c r t hn hN x a cP cC h,
      eval_parallelOperand c r t hn hN x b cP cC h]
  | mul a b =>
    simp [parallelGate, ArithmeticGate.evaluate,
      eval_parallelOperand c r t hn hN x a cP cC h,
      eval_parallelOperand c r t hn hN x b cP cC h]

private theorem evaluateNode_parallel_aux {F : Type u} {A : Type v} {B : Type w}
    [Add F] [Sub F] [Mul F]
    (c : ArithmeticCircuit F A B) (r : ℕ)
    (x : Fin r × A → F) (n : ℕ) :
    ∀ (i : Fin (c.parallel r).size), i.val < n →
      (c.parallel r).evaluateNode x i =
        c.evaluateNode (fun a => x ((finProdFinEquiv.symm i).1, a))
          (finProdFinEquiv.symm i).2 := by
  induction n with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intro i hi
    by_cases hlt : i.val < n
    · exact ih i hlt
    · have heq : i.val = n := by omega
      have hS := evaluateNode.eq_1 (c.parallel r) x i
      have hC := evaluateNode.eq_1 c (fun a => x ((finProdFinEquiv.symm i).1, a))
        (finProdFinEquiv.symm i).2
      rw [hS, hC]
      have hn : (finProdFinEquiv.symm i).2.val ≤ c.size :=
        Nat.le_of_lt (finProdFinEquiv.symm i).2.isLt
      have hval : (finProdFinEquiv ((finProdFinEquiv.symm i).1, (finProdFinEquiv.symm i).2)).val = i.val := by
        have h : finProdFinEquiv (finProdFinEquiv.symm i) = i :=
          Equiv.apply_symm_apply _ _
        have hp : (finProdFinEquiv.symm i) =
            ((finProdFinEquiv.symm i).1, (finProdFinEquiv.symm i).2) := (Prod.eta _).symm
        rw [hp] at h
        exact congrArg Fin.val h
      have hN : ∀ j : Fin (finProdFinEquiv.symm i).2.val,
          (finProdFinEquiv ((finProdFinEquiv.symm i).1,
            ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩) : Fin (r * c.size)).val < i.val := by
        intro j
        have hj : j.val < (finProdFinEquiv.symm i).2.val := j.isLt
        have hlt' : (finProdFinEquiv ((finProdFinEquiv.symm i).1,
              ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩) : Fin (r * c.size)).val <
            (finProdFinEquiv ((finProdFinEquiv.symm i).1, (finProdFinEquiv.symm i).2)
              : Fin (r * c.size)).val := by
          show j.val + c.size * ((finProdFinEquiv.symm i).1).val <
            ((finProdFinEquiv.symm i).2).val + c.size * ((finProdFinEquiv.symm i).1).val
          exact Nat.add_lt_add_right hj _
        rw [hval] at hlt'
        exact hlt'
      have hgate : (c.parallel r).gate i =
          parallelGate c r (finProdFinEquiv.symm i).1 hn hN
            (c.gate (finProdFinEquiv.symm i).2) := rfl
      rw [hgate]
      apply eval_parallelGate
      intro j
      show (c.parallel r).evaluateNode x
          ⟨(finProdFinEquiv ((finProdFinEquiv.symm i).1,
            ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩)).val,
            Nat.lt_trans (hN j) i.isLt⟩ =
        c.evaluateNode (fun a => x ((finProdFinEquiv.symm i).1, a))
          ⟨j.val, Nat.lt_trans j.isLt (finProdFinEquiv.symm i).2.isLt⟩
      have hmap : (finProdFinEquiv ((finProdFinEquiv.symm i).1,
          ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩) : Fin (r * c.size)).val < n := by
        have := hN j
        omega
      have hltS : (finProdFinEquiv ((finProdFinEquiv.symm i).1,
          ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩) : Fin (r * c.size)).val <
          (c.parallel r).size := Nat.lt_trans (hN j) i.isLt
      have hih := ih ⟨(finProdFinEquiv ((finProdFinEquiv.symm i).1,
          ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩)).val, hltS⟩ hmap
      have hpeq : (⟨(finProdFinEquiv ((finProdFinEquiv.symm i).1,
          ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩)).val, hltS⟩ : Fin (c.parallel r).size) =
          (finProdFinEquiv ((finProdFinEquiv.symm i).1,
            ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩) : Fin (r * c.size)) := Fin.ext rfl
      have hsym : finProdFinEquiv.symm
          (⟨(finProdFinEquiv ((finProdFinEquiv.symm i).1,
            ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩)).val, hltS⟩ : Fin (c.parallel r).size) =
          ((finProdFinEquiv.symm i).1, ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩) := by
        rw [hpeq]
        exact Equiv.symm_apply_apply _ _
      rw [hsym] at hih
      exact hih

/-- Evaluation of parallel copies is copywise evaluation. -/
theorem evaluate_parallel {F : Type u} {A : Type v} {B : Type w}
    [Add F] [Sub F] [Mul F] (c : ArithmeticCircuit F A B) (r : ℕ)
    (x : Fin r × A → F) (t : Fin r) (b : B) :
    (c.parallel r).evaluate x (t, b) = c.evaluate (fun a => x (t, a)) b := by
  have hall := evaluateNode_parallel_aux c r x ((c.parallel r).size + 1)
  have h : ∀ k : Fin c.size, ∀ hk : (finProdFinEquiv (t, k)).val < (c.parallel r).size,
      (c.parallel r).evaluateNode x ⟨(finProdFinEquiv (t, k)).val, hk⟩ =
        c.evaluateNode (fun a => x (t, a)) k := by
    intro k hk
    have hklt : (finProdFinEquiv (t, k)).val < (c.parallel r).size + 1 := by omega
    have hih := hall ⟨(finProdFinEquiv (t, k)).val, hk⟩ hklt
    have hpeq : (⟨(finProdFinEquiv (t, k)).val, hk⟩ : Fin (c.parallel r).size) =
        (finProdFinEquiv (t, k) : Fin (r * c.size)) := Fin.ext rfl
    have hsym : finProdFinEquiv.symm
        (⟨(finProdFinEquiv (t, k)).val, hk⟩ : Fin (c.parallel r).size) = (t, k) := by
      rw [hpeq]
      exact Equiv.symm_apply_apply _ _
    rw [hsym] at hih
    exact hih
  have hout : (c.parallel r).output (t, b) =
      parallelOperand c r t (Nat.le_refl c.size)
        (fun j => (finProdFinEquiv (t, ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_refl c.size)⟩)).isLt)
        (c.output b) := rfl
  simp only [evaluate, hout]
  exact eval_parallelOperand c r t (Nat.le_refl c.size)
    (fun j => (finProdFinEquiv (t, ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_refl c.size)⟩)).isLt)
    x (c.output b) ((c.parallel r).evaluateNode x) (c.evaluateNode (fun a => x (t, a)))
    (fun j => h ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_refl c.size)⟩ _)

end ArithmeticCircuit

end

end Cslib.Complexity.Algebraic
