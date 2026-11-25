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
public import Mathlib.Data.Fintype.BigOperators

/-!
# Arithmetic circuit composition and block reindexing

Substitution of subcircuits into circuit inputs, parallel copies of a circuit, and
linear-combination circuits, with evaluation and size lemmas, plus block reindexing of
matrices for recursive constructions.
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
        (fun j => (finProdFinEquiv (t,
          ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_refl c.size)⟩)).isLt)
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
      have hval : (finProdFinEquiv ((finProdFinEquiv.symm i).1,
          (finProdFinEquiv.symm i).2)).val = i.val := by
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
      change (c.parallel r).evaluateNode x
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
        (fun j => (finProdFinEquiv (t,
          ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_refl c.size)⟩)).isLt)
        (c.output b) := rfl
  simp only [evaluate, hout]
  exact eval_parallelOperand c r t (Nat.le_refl c.size)
    (fun j => (finProdFinEquiv (t, ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_refl c.size)⟩)).isLt)
    x (c.output b) ((c.parallel r).evaluateNode x) (c.evaluateNode (fun a => x (t, a)))
    (fun j => h ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_refl c.size)⟩ _)

/-- Linear-combination circuit: output `b` computes `∑ s, coeff b s * x (src b s)`,
one block of alternating multiply/add gates per output, blocks in `Fintype.equivFin`
order. -/
noncomputable def linearCombination {F : Type u} {A : Type v} {B : Type w}
    {S : Type v'} [Ring F] [Fintype B] [Fintype S]
    (coeff : B → S → F) (src : B → S → A) :
    ArithmeticCircuit F A B where
  size := Fintype.card B * (2 * Fintype.card S)
  gate := fun i =>
    let bi := (finProdFinEquiv.symm i).1
    let p := (finProdFinEquiv.symm i).2
    have hp : p.val < 2 * Fintype.card S := p.isLt
    have hval : (finProdFinEquiv (bi, p)).val = i.val := by
      have h : finProdFinEquiv (finProdFinEquiv.symm i) = i :=
        Equiv.apply_symm_apply _ _
      have hpeta : (finProdFinEquiv.symm i) = (bi, p) := (Prod.eta _).symm
      rw [hpeta] at h
      exact congrArg Fin.val h
    have hlt : ∀ q : ℕ, ∀ hq : q < p.val,
        (finProdFinEquiv (bi,
          (⟨q, by omega⟩ : Fin (2 * Fintype.card S)))).val < i.val := by
      intro q hq
      have hlt' : (finProdFinEquiv (bi,
            (⟨q, by omega⟩ : Fin (2 * Fintype.card S)))).val <
          (finProdFinEquiv (bi, p)).val := by
        show q + (2 * Fintype.card S) * bi.val <
          p.val + (2 * Fintype.card S) * bi.val
        exact Nat.add_lt_add_right hq _
      rw [hval] at hlt'
      exact hlt'
    have hj : p.val / 2 < Fintype.card S := by omega
    let b := (Fintype.equivFin B).symm bi
    let s := (Fintype.equivFin S).symm ⟨p.val / 2, hj⟩
    if hpar : p.val % 2 = 0 then
      .mul (.constant (coeff b s)) (.input (src b s))
    else
      have hodd : p.val % 2 = 1 := by omega
      have hpos : 1 ≤ p.val := by omega
      have hm : (finProdFinEquiv (bi,
          (⟨p.val - 1, by omega⟩ : Fin (2 * Fintype.card S)))).val < i.val :=
        hlt _ (by omega)
      let m : Fin i.val :=
        ⟨(finProdFinEquiv (bi,
          (⟨p.val - 1, by omega⟩ : Fin (2 * Fintype.card S)))).val, hm⟩
      let prev : ArithmeticOperand F A i.val :=
        if hj0 : p.val / 2 = 0 then .constant 0
        else .node ⟨(finProdFinEquiv (bi,
          (⟨p.val - 2, by omega⟩ : Fin (2 * Fintype.card S)))).val,
          hlt _ (by omega)⟩
      .add prev (.node m)
  output := fun b =>
    let bi := (Fintype.equivFin B) b
    if hnS : Fintype.card S = 0 then .constant 0
    else .node (finProdFinEquiv (bi,
      (⟨2 * Fintype.card S - 1, by omega⟩ : Fin (2 * Fintype.card S))))

/-- Size of a linear-combination circuit: two gates (multiply, add) per
(output, source) pair. -/
theorem size_linearCombination {F : Type u} {A : Type v} {B : Type w}
    {S : Type v'} [Ring F] [Fintype B] [Fintype S]
    (coeff : B → S → F) (src : B → S → A) :
    (linearCombination coeff src).size = Fintype.card B * (2 * Fintype.card S) :=
  rfl

private noncomputable def linCombTerm {F : Type u} {A : Type v} {B : Type w}
    {S : Type v'} [Ring F] [Fintype B] [Fintype S]
    (coeff : B → S → F) (src : B → S → A) (x : A → F) (b : B) : ℕ → F :=
  fun k => if hk : k < Fintype.card S then
    coeff b ((Fintype.equivFin S).symm ⟨k, hk⟩) *
      x (src b ((Fintype.equivFin S).symm ⟨k, hk⟩)) else 0

private theorem linCombTerm_eq {F : Type u} {A : Type v} {B : Type w}
    {S : Type v'} [Ring F] [Fintype B] [Fintype S]
    (coeff : B → S → F) (src : B → S → A) (x : A → F) (b : B)
    (k : ℕ) (hk : k < Fintype.card S) :
    linCombTerm coeff src x b k =
      coeff b ((Fintype.equivFin S).symm ⟨k, hk⟩) *
        x (src b ((Fintype.equivFin S).symm ⟨k, hk⟩)) := by
  simp [linCombTerm, hk]

private theorem evaluateNode_linearCombination_aux {F : Type u} {A : Type v}
    {B : Type w} {S : Type v'} [Ring F] [Fintype B] [Fintype S]
    (coeff : B → S → F) (src : B → S → A)
    (x : A → F) (n : ℕ) :
    ∀ (i : Fin (linearCombination coeff src).size), i.val < n →
      (∀ _ : (finProdFinEquiv.symm i).2.val % 2 = 0,
        (linearCombination coeff src).evaluateNode x i =
          linCombTerm coeff src x
            ((Fintype.equivFin B).symm (finProdFinEquiv.symm i).1)
            ((finProdFinEquiv.symm i).2.val / 2)) ∧
      (∀ _ : (finProdFinEquiv.symm i).2.val % 2 = 1,
        (linearCombination coeff src).evaluateNode x i =
          ∑ k ∈ Finset.range ((finProdFinEquiv.symm i).2.val / 2 + 1),
            linCombTerm coeff src x
              ((Fintype.equivFin B).symm (finProdFinEquiv.symm i).1) k) := by
  induction n with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intro i hi
    by_cases hlt : i.val < n
    · exact ih i hlt
    · have heq : i.val = n := by omega
      have hS := evaluateNode.eq_1 (linearCombination coeff src) x i
      have hp : (finProdFinEquiv.symm i).2.val < 2 * Fintype.card S :=
        (finProdFinEquiv.symm i).2.isLt
      have hj : (finProdFinEquiv.symm i).2.val / 2 < Fintype.card S := by omega
      have hval : (finProdFinEquiv ((finProdFinEquiv.symm i).1,
          (finProdFinEquiv.symm i).2)).val = i.val := by
        have h : finProdFinEquiv (finProdFinEquiv.symm i) = i :=
          Equiv.apply_symm_apply _ _
        have hpeta : (finProdFinEquiv.symm i) =
            ((finProdFinEquiv.symm i).1, (finProdFinEquiv.symm i).2) :=
          (Prod.eta _).symm
        rw [hpeta] at h
        exact congrArg Fin.val h
      have hlt : ∀ q : ℕ, ∀ hq : q < (finProdFinEquiv.symm i).2.val,
          (finProdFinEquiv ((finProdFinEquiv.symm i).1,
            (⟨q, by omega⟩ : Fin (2 * Fintype.card S)))).val < i.val := by
        intro q hq
        have hlt' : (finProdFinEquiv ((finProdFinEquiv.symm i).1,
              (⟨q, by omega⟩ : Fin (2 * Fintype.card S)))).val <
            (finProdFinEquiv ((finProdFinEquiv.symm i).1,
              (finProdFinEquiv.symm i).2)).val := by
          show q + (2 * Fintype.card S) * (finProdFinEquiv.symm i).1.val <
            (finProdFinEquiv.symm i).2.val + (2 * Fintype.card S) *
              (finProdFinEquiv.symm i).1.val
          exact Nat.add_lt_add_right hq _
        rw [hval] at hlt'
        exact hlt'
      constructor
      · -- multiply gate: value is the single term
        intro hpar
        rw [hS]
        have hgate : (linearCombination coeff src).gate i =
            .mul (.constant (coeff
              ((Fintype.equivFin B).symm (finProdFinEquiv.symm i).1)
              ((Fintype.equivFin S).symm
                ⟨(finProdFinEquiv.symm i).2.val / 2, hj⟩)))
              (.input (src
                ((Fintype.equivFin B).symm (finProdFinEquiv.symm i).1)
                ((Fintype.equivFin S).symm
                  ⟨(finProdFinEquiv.symm i).2.val / 2, hj⟩))) := by
          simp [linearCombination, hpar]
        rw [hgate]
        simp only [ArithmeticGate.evaluate, ArithmeticOperand.evaluate]
        rw [linCombTerm_eq _ _ _ _ _ hj]
      · -- add gate: value is the partial sum
        intro hpar
        have hpos : 1 ≤ (finProdFinEquiv.symm i).2.val := by omega
        have h1 : (finProdFinEquiv.symm i).2.val - 1 <
            (finProdFinEquiv.symm i).2.val := by omega
        have hm : (finProdFinEquiv ((finProdFinEquiv.symm i).1,
            (⟨(finProdFinEquiv.symm i).2.val - 1, by omega⟩ :
              Fin (2 * Fintype.card S)))).val < i.val := hlt _ h1
        have h1lt : (finProdFinEquiv ((finProdFinEquiv.symm i).1,
            (⟨(finProdFinEquiv.symm i).2.val - 1, by omega⟩ :
              Fin (2 * Fintype.card S)))).val < n :=
          Nat.lt_of_lt_of_le hm (le_of_eq heq)
        have h1ltS : (finProdFinEquiv ((finProdFinEquiv.symm i).1,
            (⟨(finProdFinEquiv.symm i).2.val - 1, by omega⟩ :
              Fin (2 * Fintype.card S)))).val <
            (linearCombination coeff src).size :=
          (finProdFinEquiv ((finProdFinEquiv.symm i).1,
            (⟨(finProdFinEquiv.symm i).2.val - 1, by omega⟩ :
              Fin (2 * Fintype.card S)))).isLt
        let g1 : Fin (linearCombination coeff src).size :=
          ⟨(finProdFinEquiv ((finProdFinEquiv.symm i).1,
            (⟨(finProdFinEquiv.symm i).2.val - 1, by omega⟩ :
              Fin (2 * Fintype.card S)))).val, h1ltS⟩
        have h1peq : g1 = (finProdFinEquiv ((finProdFinEquiv.symm i).1,
            (⟨(finProdFinEquiv.symm i).2.val - 1, by omega⟩ :
              Fin (2 * Fintype.card S))) :
            Fin (Fintype.card B * (2 * Fintype.card S))) := Fin.ext rfl
        have h1sym : finProdFinEquiv.symm g1 =
            ((finProdFinEquiv.symm i).1,
              (⟨(finProdFinEquiv.symm i).2.val - 1, by omega⟩ :
                Fin (2 * Fintype.card S))) := by
          rw [h1peq]
          exact Equiv.symm_apply_apply _ _
        have hpar1 : (finProdFinEquiv.symm g1).2.val % 2 = 0 := by
          rw [h1sym]
          change ((finProdFinEquiv.symm i).2.val - 1) % 2 = 0
          omega
        have hIH1 := (ih g1 h1lt).1 hpar1
        simp only [h1sym] at hIH1
        have hdiv1 : ((finProdFinEquiv.symm i).2.val - 1) / 2 =
            (finProdFinEquiv.symm i).2.val / 2 := by omega
        rw [hdiv1] at hIH1
        by_cases hj0 : (finProdFinEquiv.symm i).2.val / 2 = 0
        · -- first source: previous sum is zero
          rw [hS]
          have hgate0 : (linearCombination coeff src).gate i =
              .add (.constant 0)
                (.node ⟨(finProdFinEquiv ((finProdFinEquiv.symm i).1,
                  (⟨(finProdFinEquiv.symm i).2.val - 1, by omega⟩ :
                    Fin (2 * Fintype.card S)))).val, hm⟩) := by
            simp [linearCombination, hpar, hj0]
          rw [hgate0]
          simp only [ArithmeticGate.evaluate, ArithmeticOperand.evaluate]
          rw [hj0] at hIH1 ⊢
          rw [Finset.sum_range_succ, Finset.sum_range_zero]
          congr 1
        · -- later source: add onto the previous partial sum
          have h2 : (finProdFinEquiv.symm i).2.val - 2 <
              (finProdFinEquiv.symm i).2.val := by omega
          have hm2 : (finProdFinEquiv ((finProdFinEquiv.symm i).1,
              (⟨(finProdFinEquiv.symm i).2.val - 2, by omega⟩ :
                Fin (2 * Fintype.card S)))).val < i.val := hlt _ h2
          have h2lt : (finProdFinEquiv ((finProdFinEquiv.symm i).1,
              (⟨(finProdFinEquiv.symm i).2.val - 2, by omega⟩ :
                Fin (2 * Fintype.card S)))).val < n :=
            Nat.lt_of_lt_of_le hm2 (le_of_eq heq)
          have h2ltS : (finProdFinEquiv ((finProdFinEquiv.symm i).1,
              (⟨(finProdFinEquiv.symm i).2.val - 2, by omega⟩ :
                Fin (2 * Fintype.card S)))).val <
              (linearCombination coeff src).size :=
            (finProdFinEquiv ((finProdFinEquiv.symm i).1,
              (⟨(finProdFinEquiv.symm i).2.val - 2, by omega⟩ :
                Fin (2 * Fintype.card S)))).isLt
          let g2 : Fin (linearCombination coeff src).size :=
            ⟨(finProdFinEquiv ((finProdFinEquiv.symm i).1,
              (⟨(finProdFinEquiv.symm i).2.val - 2, by omega⟩ :
                Fin (2 * Fintype.card S)))).val, h2ltS⟩
          have h2peq : g2 = (finProdFinEquiv ((finProdFinEquiv.symm i).1,
              (⟨(finProdFinEquiv.symm i).2.val - 2, by omega⟩ :
                Fin (2 * Fintype.card S))) :
              Fin (Fintype.card B * (2 * Fintype.card S))) := Fin.ext rfl
          have h2sym : finProdFinEquiv.symm g2 =
              ((finProdFinEquiv.symm i).1,
                (⟨(finProdFinEquiv.symm i).2.val - 2, by omega⟩ :
                  Fin (2 * Fintype.card S))) := by
            rw [h2peq]
            exact Equiv.symm_apply_apply _ _
          have hpar2 : (finProdFinEquiv.symm g2).2.val % 2 = 1 := by
            rw [h2sym]
            change ((finProdFinEquiv.symm i).2.val - 2) % 2 = 1
            omega
          have hIH2 := (ih g2 h2lt).2 hpar2
          simp only [h2sym] at hIH2
          have hdiv2 : ((finProdFinEquiv.symm i).2.val - 2) / 2 + 1 =
              (finProdFinEquiv.symm i).2.val / 2 := by omega
          rw [hdiv2] at hIH2
          rw [hS]
          have hgate1 : (linearCombination coeff src).gate i =
              .add (.node ⟨(finProdFinEquiv ((finProdFinEquiv.symm i).1,
                  (⟨(finProdFinEquiv.symm i).2.val - 2, by omega⟩ :
                    Fin (2 * Fintype.card S)))).val, hm2⟩)
                (.node ⟨(finProdFinEquiv ((finProdFinEquiv.symm i).1,
                  (⟨(finProdFinEquiv.symm i).2.val - 1, by omega⟩ :
                    Fin (2 * Fintype.card S)))).val, hm⟩) := by
            simp [linearCombination, hpar, hj0]
          rw [hgate1]
          simp only [ArithmeticGate.evaluate, ArithmeticOperand.evaluate]
          rw [Finset.sum_range_succ]
          congr 1

/-- Evaluation of a linear-combination circuit is the stated sum. -/
theorem evaluate_linearCombination {F : Type u} {A : Type v} {B : Type w}
    {S : Type v'} [Ring F] [Fintype B] [Fintype S]
    (coeff : B → S → F) (src : B → S → A) (x : A → F) (b : B) :
    (linearCombination coeff src).evaluate x b = ∑ s, coeff b s * x (src b s) := by
  by_cases hnS : Fintype.card S = 0
  · -- empty source type: output is constant zero and the sum is empty
    have hout : (linearCombination coeff src).output b = .constant 0 := by
      simp [linearCombination, hnS]
    simp only [evaluate, hout, ArithmeticOperand.evaluate]
    symm
    have hpos : ¬ 0 < Fintype.card S := by omega
    rw [Fintype.card_pos_iff] at hpos
    let : IsEmpty S := ⟨fun s => hpos ⟨s⟩⟩
    rw [Finset.univ_eq_empty]
    exact Finset.sum_empty
  · -- nonempty: the output is the last add gate, a complete partial sum
    have hk : (finProdFinEquiv ((Fintype.equivFin B) b,
        (⟨2 * Fintype.card S - 1, by omega⟩ : Fin (2 * Fintype.card S)))).val <
        (linearCombination coeff src).size :=
      (finProdFinEquiv ((Fintype.equivFin B) b,
        (⟨2 * Fintype.card S - 1, by omega⟩ : Fin (2 * Fintype.card S)))).isLt
    let gL : Fin (linearCombination coeff src).size :=
      ⟨(finProdFinEquiv ((Fintype.equivFin B) b,
        (⟨2 * Fintype.card S - 1, by omega⟩ : Fin (2 * Fintype.card S)))).val,
        hk⟩
    have hmap : gL.val < (linearCombination coeff src).size + 1 :=
      Nat.lt_of_lt_of_le hk (Nat.le_succ _)
    have hpeq : gL = (finProdFinEquiv ((Fintype.equivFin B) b,
        (⟨2 * Fintype.card S - 1, by omega⟩ : Fin (2 * Fintype.card S))) :
        Fin (Fintype.card B * (2 * Fintype.card S))) := Fin.ext rfl
    have hsym : finProdFinEquiv.symm gL = ((Fintype.equivFin B) b,
        (⟨2 * Fintype.card S - 1, by omega⟩ : Fin (2 * Fintype.card S))) := by
      rw [hpeq]
      exact Equiv.symm_apply_apply _ _
    have hpar1 : (finProdFinEquiv.symm gL).2.val % 2 = 1 := by
      rw [hsym]
      change (2 * Fintype.card S - 1) % 2 = 1
      omega
    have hall := evaluateNode_linearCombination_aux coeff src x
      ((linearCombination coeff src).size + 1)
    have hIH := (hall gL hmap).2 hpar1
    simp only [hsym] at hIH
    have hdiv : (2 * Fintype.card S - 1) / 2 + 1 = Fintype.card S := by omega
    rw [hdiv] at hIH
    simp only [Equiv.symm_apply_apply] at hIH
    have hout : (linearCombination coeff src).output b =
        .node (finProdFinEquiv ((Fintype.equivFin B) b,
          (⟨2 * Fintype.card S - 1, by omega⟩ :
            Fin (2 * Fintype.card S)))) := by
      simp [linearCombination, hnS]
    simp only [evaluate, hout, ArithmeticOperand.evaluate]
    refine hIH.trans ?_
    calc (∑ k ∈ Finset.range (Fintype.card S), linCombTerm coeff src x b k)
        = ∑ i : Fin (Fintype.card S), linCombTerm coeff src x b ↑i :=
          (Fin.sum_univ_eq_sum_range _ _).symm
      _ = ∑ i : Fin (Fintype.card S),
          coeff b ((Fintype.equivFin S).symm i) *
            x (src b ((Fintype.equivFin S).symm i)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [linCombTerm_eq _ _ _ _ _ i.isLt]
      _ = ∑ s, coeff b s * x (src b s) :=
        Equiv.sum_comp (Fintype.equivFin S).symm
          (fun s => coeff b s * x (src b s))

end ArithmeticCircuit

end

end Cslib.Complexity.Algebraic
