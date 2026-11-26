/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.RectangularCircuitExponent
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Linarith
import CSLibExt.Complexity.Algebraic.CircuitComposition

@[expose] public section

set_option autoImplicit false

namespace Cslib.Complexity.Algebraic.SquareMatrixMultiplicationBoundsWanted

open Cslib.Complexity.Algebraic

universe u v

private noncomputable def mixed {F : Type u} {A B : Type v} [Field F]
    (p : MvPolynomial (A ⊕ B) F) (a : A) (b : B) : F :=
  MvPolynomial.eval 0 (MvPolynomial.pderiv (.inl a) (MvPolynomial.pderiv (.inr b) p))

private theorem mixed_mul {F : Type u} {A B : Type v} [Field F]
    (p q : MvPolynomial (A ⊕ B) F) (a : A) (b : B) :
    mixed (p * q) a b =
      mixed p a b * MvPolynomial.eval 0 q + MvPolynomial.eval 0 p * mixed q a b +
        MvPolynomial.eval 0 (MvPolynomial.pderiv (.inl a) p) *
          MvPolynomial.eval 0 (MvPolynomial.pderiv (.inr b) q) +
        MvPolynomial.eval 0 (MvPolynomial.pderiv (.inl a) q) *
          MvPolynomial.eval 0 (MvPolynomial.pderiv (.inr b) p) := by
  simp only [mixed, MvPolynomial.pderiv_mul, map_add, map_mul]
  ring

private noncomputable def cross {F : Type u} {A B : Type v} [Field F]
    (p q : MvPolynomial (A ⊕ B) F) : A → B → F := fun a b =>
  MvPolynomial.eval 0 (MvPolynomial.pderiv (.inl a) p) *
    MvPolynomial.eval 0 (MvPolynomial.pderiv (.inr b) q) +
  MvPolynomial.eval 0 (MvPolynomial.pderiv (.inl a) q) *
    MvPolynomial.eval 0 (MvPolynomial.pderiv (.inr b) p)

private theorem mixed_mul_eq {F : Type u} {A B : Type v} [Field F]
    (p q : MvPolynomial (A ⊕ B) F) :
    mixed (p * q) = MvPolynomial.eval 0 q • mixed p +
      MvPolynomial.eval 0 p • mixed q + cross p q := by
  funext a b
  rw [mixed_mul]
  simp [cross, mul_comm, add_assoc]

private theorem mixed_X {F : Type u} {A B : Type v} [Field F]
    (t : A ⊕ B) (a : A) (b : B) : mixed (MvPolynomial.X t : MvPolynomial (A ⊕ B) F) a b = 0 := by
  classical
  cases t with
  | inl t => simp [mixed]
  | inr t =>
    by_cases h : b = t
    · subst t
      simp [mixed]
    · simp [mixed, h]

private theorem mixed_X_mul_X {F : Type u} {A B : Type v} [Field F]
    [DecidableEq A] [DecidableEq B] (a a' : A) (b b' : B) :
    mixed (MvPolynomial.X (.inl a') * MvPolynomial.X (.inr b') :
      MvPolynomial (A ⊕ B) F) a b = if a = a' ∧ b = b' then 1 else 0 := by
  classical
  rw [mixed_mul]
  simp only [mixed_X, MvPolynomial.eval_X, Pi.zero_apply, mul_zero, zero_add]
  by_cases ha : a = a' <;> by_cases hb : b = b' <;>
    simp [MvPolynomial.pderiv_X, ha, hb]

private noncomputable def polynomialOperand {F : Type u} {A : Type v} {n : ℕ} [Field F]
    (o : ArithmeticOperand F A n) : ArithmeticOperand (MvPolynomial A F) A n :=
  match o with
  | .constant a => .constant (MvPolynomial.C a)
  | .input a => .input a
  | .node i => .node i

private theorem polynomialOperand_evaluate {F : Type u} {A : Type v} {n : ℕ} [Field F]
    (o : ArithmeticOperand F A n) (x : A → F) (p : Fin n → MvPolynomial A F) :
    MvPolynomial.eval x ((polynomialOperand o).evaluate MvPolynomial.X p) =
      o.evaluate x (fun i => MvPolynomial.eval x (p i)) := by
  cases o <;> simp [polynomialOperand, ArithmeticOperand.evaluate]

private noncomputable def polynomialGate {F : Type u} {A : Type v} {n : ℕ} [Field F]
    (g : ArithmeticGate F A n) : ArithmeticGate (MvPolynomial A F) A n :=
  match g with
  | .add a b => .add (polynomialOperand a) (polynomialOperand b)
  | .sub a b => .sub (polynomialOperand a) (polynomialOperand b)
  | .mul a b => .mul (polynomialOperand a) (polynomialOperand b)

private theorem polynomialGate_evaluate {F : Type u} {A : Type v} {n : ℕ} [Field F]
    (g : ArithmeticGate F A n) (x : A → F) (p : Fin n → MvPolynomial A F) :
    MvPolynomial.eval x ((polynomialGate g).evaluate MvPolynomial.X p) =
      g.evaluate x (fun i => MvPolynomial.eval x (p i)) := by
  cases g <;> simp [polynomialGate, ArithmeticGate.evaluate, polynomialOperand_evaluate]

private noncomputable def gateFactors {F : Type u} {A B : Type v} {n : ℕ} [Field F]
    (g : ArithmeticGate F (A ⊕ B) n) (p : Fin n → MvPolynomial (A ⊕ B) F) :
    MvPolynomial (A ⊕ B) F × MvPolynomial (A ⊕ B) F :=
  match g with
  | .mul a b => ((polynomialOperand a).evaluate MvPolynomial.X p,
    (polynomialOperand b).evaluate MvPolynomial.X p)
  | _ => (0, 0)

private theorem mixed_add {F : Type u} {A B : Type v} [Field F]
    (p q : MvPolynomial (A ⊕ B) F) : mixed (p + q) = mixed p + mixed q := by
  funext a b
  simp [mixed]

private theorem mixed_sub {F : Type u} {A B : Type v} [Field F]
    (p q : MvPolynomial (A ⊕ B) F) : mixed (p - q) = mixed p - mixed q := by
  funext a b
  simp [mixed]

private theorem mixed_gate_mem {F : Type u} {A B : Type v} {n : ℕ} [Field F]
    (g : ArithmeticGate F (A ⊕ B) n) (p : Fin n → MvPolynomial (A ⊕ B) F)
    (S : Submodule F (A → B → F))
    (h : ∀ o : ArithmeticOperand F (A ⊕ B) n,
      mixed ((polynomialOperand o).evaluate MvPolynomial.X p) ∈ S)
    (hx : cross (gateFactors g p).1 (gateFactors g p).2 ∈ S) :
    mixed ((polynomialGate g).evaluate MvPolynomial.X p) ∈ S := by
  cases g with
  | add a b =>
    simpa [polynomialGate, ArithmeticGate.evaluate, mixed_add] using S.add_mem (h a) (h b)
  | sub a b =>
    simpa [polynomialGate, ArithmeticGate.evaluate, mixed_sub] using S.sub_mem (h a) (h b)
  | mul a b =>
    change mixed (_ * _) ∈ S
    rw [mixed_mul_eq]
    exact S.add_mem (S.add_mem (S.smul_mem _ (h a)) (S.smul_mem _ (h b))) hx

private theorem mixed_operand_mem {F : Type u} {A B : Type v} {n : ℕ} [Field F]
    (o : ArithmeticOperand F (A ⊕ B) n) (p : Fin n → MvPolynomial (A ⊕ B) F)
    (S : Submodule F (A → B → F)) (h : ∀ i, mixed (p i) ∈ S) :
    mixed ((polynomialOperand o).evaluate MvPolynomial.X p) ∈ S := by
  cases o with
  | constant t =>
    convert S.zero_mem using 1
    funext a b
    simp [polynomialOperand, ArithmeticOperand.evaluate, mixed]
  | input t =>
    convert S.zero_mem using 1
    funext a b
    exact mixed_X t a b
  | node i => exact h i

private noncomputable def polynomialCircuit {F : Type u} {A : Type v} {B : Type}
    [Field F] (c : ArithmeticCircuit F A B) : ArithmeticCircuit (MvPolynomial A F) A B where
  size := c.size
  gate i := polynomialGate (c.gate i)
  output b := polynomialOperand (c.output b)

private noncomputable def circuitFactors {F : Type u} {A B : Type v} {C : Type} [Field F]
    (c : ArithmeticCircuit F (A ⊕ B) C) (i : Fin c.size) :
    MvPolynomial (A ⊕ B) F × MvPolynomial (A ⊕ B) F :=
  gateFactors (c.gate i) (fun j =>
    (polynomialCircuit c).evaluateNode MvPolynomial.X ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)

private theorem mixed_node_mem_span {F : Type u} {A B : Type v} {C : Type} [Field F]
    (c : ArithmeticCircuit F (A ⊕ B) C) (i : Fin c.size) :
    mixed ((polynomialCircuit c).evaluateNode MvPolynomial.X i) ∈
      Submodule.span F (Set.range fun j : Fin c.size =>
        cross (circuitFactors c j).1 (circuitFactors c j).2) := by
  rw [ArithmeticCircuit.evaluateNode.eq_1 (polynomialCircuit c) MvPolynomial.X i]
  change mixed ((polynomialGate (c.gate i)).evaluate MvPolynomial.X
    (fun j : Fin i.val => (polynomialCircuit c).evaluateNode MvPolynomial.X
      ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)) ∈ _
  apply mixed_gate_mem
  · intro o
    apply mixed_operand_mem
    intro j
    exact mixed_node_mem_span c ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
  · exact Submodule.subset_span ⟨i, rfl⟩
termination_by i.val
decreasing_by exact j.isLt

private theorem mixed_output_coefficients {F : Type u} {A B : Type v} {C : Type} [Field F]
    (c : ArithmeticCircuit F (A ⊕ B) C) (o : C) :
    ∃ w : Fin c.size → F, ∀ a b,
      mixed ((polynomialCircuit c).evaluate MvPolynomial.X o) a b =
        ∑ j, w j * cross (circuitFactors c j).1 (circuitFactors c j).2 a b := by
  have h := mixed_operand_mem (c.output o)
    (fun i : Fin c.size => (polynomialCircuit c).evaluateNode MvPolynomial.X i)
    (Submodule.span F (Set.range fun j : Fin c.size =>
      cross (circuitFactors c j).1 (circuitFactors c j).2)) (mixed_node_mem_span c)
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp h
  refine ⟨w, fun a b => ?_⟩
  have he := congrFun (congrFun hw a) b
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ArithmeticCircuit.evaluate,
    polynomialCircuit] using he.symm

private theorem polynomialCircuit_evaluateNode {F : Type u} {A : Type v} {B : Type}
    [Field F] (c : ArithmeticCircuit F A B) (x : A → F) (i : Fin c.size) :
    MvPolynomial.eval x ((polynomialCircuit c).evaluateNode MvPolynomial.X i) =
      c.evaluateNode x i := by
  rw [ArithmeticCircuit.evaluateNode.eq_1 (polynomialCircuit c) MvPolynomial.X i,
    ArithmeticCircuit.evaluateNode.eq_1 c x i]
  change MvPolynomial.eval x ((polynomialGate (c.gate i)).evaluate MvPolynomial.X _) = _
  rw [polynomialGate_evaluate]
  congr 1
  funext j
  exact polynomialCircuit_evaluateNode c x ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
termination_by i.val
decreasing_by exact j.isLt

private theorem polynomialCircuit_evaluate {F : Type u} {A : Type v} {B : Type}
    [Field F] (c : ArithmeticCircuit F A B) (x : A → F) (b : B) :
    MvPolynomial.eval x ((polynomialCircuit c).evaluate MvPolynomial.X b) =
      c.evaluate x b := by
  change MvPolynomial.eval x ((polynomialOperand (c.output b)).evaluate MvPolynomial.X
    (fun i : Fin c.size => (polynomialCircuit c).evaluateNode MvPolynomial.X i)) = _
  rw [polynomialOperand_evaluate]
  simp only [polynomialCircuit_evaluateNode, ArithmeticCircuit.evaluate]

private theorem polynomialCircuit_matrix {F : Type u} [Field F] [Infinite F] {n : ℕ}
    (c : MatrixArithmeticCircuit F n n n) (hc : IsMatrixMultiplication c)
    (i j : Fin n) :
    (polynomialCircuit c).evaluate MvPolynomial.X (i, j) =
      ∑ k : Fin n, MvPolynomial.X (.inl (i, k)) * MvPolynomial.X (.inr (k, j)) := by
  apply MvPolynomial.funext
  intro x
  rw [polynomialCircuit_evaluate]
  let A : Matrix (Fin n) (Fin n) F := fun a b => x (.inl (a, b))
  let B : Matrix (Fin n) (Fin n) F := fun a b => x (.inr (a, b))
  have hx : matrixInput A B = x := by
    funext a
    cases a <;> rfl
  rw [← hx, hc, Matrix.mul_apply]
  simp [A, B, matrixInput]

private theorem mixed_sum {F : Type u} {A B : Type v} {J : Type} [Field F] [Fintype J]
    (p : J → MvPolynomial (A ⊕ B) F) (a : A) (b : B) :
    mixed (∑ j, p j) a b = ∑ j, mixed (p j) a b := by
  simp only [mixed, map_sum]

private theorem mixed_matrix {F : Type u} [Field F] [Infinite F] {n : ℕ}
    (c : MatrixArithmeticCircuit F n n n) (hc : IsMatrixMultiplication c)
    (a b d : Fin n × Fin n) :
    mixed ((polynomialCircuit c).evaluate MvPolynomial.X (d.2, d.1)) a b =
      MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F n a b d := by
  classical
  rw [polynomialCircuit_matrix c hc]
  rw [mixed_sum]
  simp_rw [mixed_X_mul_X]
  rcases a with ⟨ai, aj⟩
  rcases b with ⟨bi, bj⟩
  rcases d with ⟨dj, di⟩
  by_cases hi : ai = di <;> by_cases hj : bj = dj <;> by_cases hk : aj = bi <;>
    simp [MatrixMultiplicationExponent.squareMatrixMultiplicationTensor,
      MatrixMultiplicationExponent.matrixMultiplicationTensor, Prod.mk.injEq, hi, hj, hk, eq_comm]
  have h (k : Fin n) : ¬ (aj = k ∧ bi = k) := by
    rintro ⟨ha, hb⟩
    exact hk (ha.trans hb.symm)
  simp [h]

private theorem rank_of_cross {F : Type u} {A B C : Type v} [Field F] (r : ℕ)
    (T : A → B → C → F) (L L' : Fin r → A → F) (R R' : Fin r → B → F)
    (w : C → Fin r → F)
    (h : ∀ a b d, T a b d = ∑ j, w d j * (L j a * R j b + L' j a * R' j b)) :
    MatrixMultiplicationExponent.HasTrilinearRankAtMost T (2 * r) := by
  classical
  let term (j : Fin r × Bool) : MatrixMultiplicationExponent.RankOneTrilinearTerm F A B C := {
    left := if j.2 then L' j.1 else L j.1
    middle := if j.2 then R' j.1 else R j.1
    right := fun d => w d j.1 }
  refine ⟨Finset.univ.toList.map term, by simp [Nat.mul_comm], ?_⟩
  intro a b d
  rw [h]
  simp only [List.map_map, Finset.sum_map_toList, Function.comp_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp [term, MatrixMultiplicationExponent.RankOneTrilinearTerm.eval]
  ring

/-- A circuit computing matrix multiplication supplies at most two rank-one terms per gate. -/
private theorem circuit_rank_bound {F : Type u} [Field F] [Infinite F] {n : ℕ}
    (c : MatrixArithmeticCircuit F n n n) (hc : IsMatrixMultiplication c) :
    MatrixMultiplicationExponent.HasTrilinearRankAtMost
      (MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F n) (2 * c.size) := by
  classical
  choose w hw using fun d : Fin n × Fin n => mixed_output_coefficients c (d.2, d.1)
  refine rank_of_cross c.size _
    (fun j a => MvPolynomial.eval 0 (MvPolynomial.pderiv (.inl a) (circuitFactors c j).1))
    (fun j a => MvPolynomial.eval 0 (MvPolynomial.pderiv (.inl a) (circuitFactors c j).2))
    (fun j b => MvPolynomial.eval 0 (MvPolynomial.pderiv (.inr b) (circuitFactors c j).2))
    (fun j b => MvPolynomial.eval 0 (MvPolynomial.pderiv (.inr b) (circuitFactors c j).1)) w ?_
  intro a b d
  rw [← mixed_matrix c hc a b d, hw d]
  rfl

private theorem rank_exponent_of_circuit {F : Type u} [Field F] [Infinite F] {w : ℝ}
    (h : HasRectangularCircuitExponent F 1 w) :
    MatrixMultiplicationExponent.matrixMultiplicationExponent F ≤ ENNReal.ofReal w := by
  apply (MatrixMultiplicationExponent.matrixMultiplicationExponent_le_iff F w h.2.1).mpr
  intro ε hε
  obtain ⟨C, hC, N, hN, hb⟩ := h.2.2 ε hε
  refine ⟨by linarith [h.2.1], 2 * C, by positivity, N, hN, ?_⟩
  intro n hn
  have hb' := hb n hn
  rw [MatrixMultiplicationExponent.rectangularInnerDimension_one] at hb'
  obtain ⟨c, hc, hs⟩ := hb'
  change (c.size : ℝ) ≤ C * Real.rpow (n : ℝ) (w + ε) at hs
  refine ⟨2 * c.size, circuit_rank_bound c hc, ?_⟩
  push_cast
  nlinarith [hs]

private noncomputable def encodeBlocks {F : Type u} {J : Type v} [Field F] [Fintype J]
    {q r : ℕ} (t : Fin r → MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (Fin q × Fin q) (Fin q × Fin q) (Fin q × Fin q)) :
    ArithmeticCircuit F (((Fin q × J) × (Fin q × J)) ⊕ ((Fin q × J) × (Fin q × J)))
      (Fin r × ((J × J) ⊕ (J × J))) :=
  ArithmeticCircuit.linearCombination
    (fun s a => match s.2 with
      | .inl _ => (t s.1).left a
      | .inr _ => (t s.1).middle a)
    (fun s a => match s.2 with
      | .inl ij => .inl ((a.1, ij.1), (a.2, ij.2))
      | .inr ij => .inr ((a.1, ij.1), (a.2, ij.2)))

private noncomputable def decodeBlocks {F : Type u} {J : Type v} [Field F] [Fintype J]
    {q r : ℕ} (t : Fin r → MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (Fin q × Fin q) (Fin q × Fin q) (Fin q × Fin q)) :
    ArithmeticCircuit F (Fin r × (J × J)) ((Fin q × J) × (Fin q × J)) :=
  ArithmeticCircuit.linearCombination
    (fun ij s => (t s).right (ij.2.1, ij.1.1))
    (fun ij s => (s, (ij.1.2, ij.2.2)))

private noncomputable def rankStep {F : Type u} {J : Type v} [Field F] [Fintype J]
    {q r : ℕ} (t : Fin r → MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (Fin q × Fin q) (Fin q × Fin q) (Fin q × Fin q))
    (c : ArithmeticCircuit F ((J × J) ⊕ (J × J)) (J × J)) :
    ArithmeticCircuit F (((Fin q × J) × (Fin q × J)) ⊕ ((Fin q × J) × (Fin q × J)))
      ((Fin q × J) × (Fin q × J)) :=
  (decodeBlocks t).subst ((c.parallel r).subst (encodeBlocks t))

private theorem rankStep_size {F : Type u} {J : Type v} [Field F] [Fintype J]
    {q r : ℕ} (t : Fin r → MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (Fin q × Fin q) (Fin q × Fin q) (Fin q × Fin q))
    (c : ArithmeticCircuit F ((J × J) ⊕ (J × J)) (J × J)) :
    (rankStep t c).size = r * c.size + 6 * r * q ^ 2 * Fintype.card J ^ 2 := by
  simp only [rankStep, ArithmeticCircuit.size_subst, ArithmeticCircuit.size_parallel,
    encodeBlocks, decodeBlocks, ArithmeticCircuit.size_linearCombination,
    Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  ring

private theorem rank_contract {F : Type u} [Field F] {q r : ℕ}
    (t : Fin r → MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (Fin q × Fin q) (Fin q × Fin q) (Fin q × Fin q))
    (ht : ∀ a b d, MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F q a b d =
      ∑ s, (t s).eval a b d)
    (A B : Matrix (Fin q) (Fin q) F) (i j : Fin q) :
    (∑ s, (t s).right (j, i) * (∑ a : Fin q × Fin q, (t s).left a * A a.1 a.2) *
      (∑ b : Fin q × Fin q, (t s).middle b * B b.1 b.2)) = (A * B) i j := by
  rw [← MatrixMultiplicationExponent.matrixMultiplicationTensorContraction_eq_mul F A B i j,
    MatrixMultiplicationExponent.matrixMultiplicationTensorContraction]
  change _ = ∑ a : Fin q × Fin q, ∑ b : Fin q × Fin q,
    MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F q a b (j, i) *
      A a.1 a.2 * B b.1 b.2
  simp_rw [ht, Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext b
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro s _
  simp only [MatrixMultiplicationExponent.RankOneTrilinearTerm.eval]
  ring

private theorem rankStep_correct {F : Type u} {J : Type v} [Field F] [Fintype J]
    {q r : ℕ} (t : Fin r → MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (Fin q × Fin q) (Fin q × Fin q) (Fin q × Fin q))
    (ht : ∀ a b d, MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F q a b d =
      ∑ s, (t s).eval a b d)
    (c : ArithmeticCircuit F ((J × J) ⊕ (J × J)) (J × J))
    (hc : ∀ x i j, c.evaluate x (i, j) = ∑ k, x (.inl (i, k)) * x (.inr (k, j)))
    (x : (((Fin q × J) × (Fin q × J)) ⊕ ((Fin q × J) × (Fin q × J))) → F)
    (i j : Fin q × J) :
    (rankStep t c).evaluate x (i, j) =
      ∑ k : Fin q × J, x (.inl (i, k)) * x (.inr (k, j)) := by
  classical
  simp only [rankStep, ArithmeticCircuit.evaluate_subst, decodeBlocks,
    ArithmeticCircuit.evaluate_linearCombination]
  simp_rw [ArithmeticCircuit.evaluate_parallel, hc]
  simp only [encodeBlocks, ArithmeticCircuit.evaluate_linearCombination]
  conv_lhs =>
    arg 2
    ext s
    rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ k : J, ∑ l : Fin q,
        x (.inl (i, (l, k))) * x (.inr ((l, k), j)) := by
      apply Finset.sum_congr rfl
      intro k _
      have h := rank_contract t ht
        (Matrix.of fun a b => x (.inl ((a, i.2), (b, k))))
        (Matrix.of fun a b => x (.inr ((a, k), (b, j.2)))) i.1 j.1
      rw [Matrix.mul_apply] at h
      simpa [mul_assoc] using h
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]

private theorem rank_output_bound {F : Type u} [Field F] {q r : ℕ}
    (hq : 1 ≤ q)
    (t : Fin r → MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (Fin q × Fin q) (Fin q × Fin q) (Fin q × Fin q))
    (ht : ∀ a b d, MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F q a b d =
      ∑ s, (t s).eval a b d) : q ^ 2 ≤ r := by
  classical
  let S := Submodule.span F (Set.range fun s => (t s).right)
  have hb (d : Fin q × Fin q) : Pi.single d (1 : F) ∈ S := by
    let z : Fin q := ⟨0, by omega⟩
    have he : Pi.single d (1 : F) =
        ∑ s, ((t s).left (d.2, z) * (t s).middle (z, d.1)) • (t s).right := by
      funext e
      simpa [MatrixMultiplicationExponent.squareMatrixMultiplicationTensor,
        MatrixMultiplicationExponent.matrixMultiplicationTensor, Pi.single_apply,
        Prod.ext_iff, and_comm, eq_comm,
        MatrixMultiplicationExponent.RankOneTrilinearTerm.eval] using ht (d.2, z) (z, d.1) e
    rw [he]
    exact S.sum_mem fun s _ => S.smul_mem _ (Submodule.subset_span ⟨s, rfl⟩)
  have hs : S = ⊤ := by
    apply top_unique
    intro f _
    have he : f = ∑ d, f d • Pi.single d (1 : F) := by
      funext e
      simp [Pi.single_apply]
    rw [he]
    exact S.sum_mem fun d _ => S.smul_mem _ (hb d)
  simpa [Module.finrank_pi, Fintype.card_prod, pow_two] using finrank_le_of_span_eq_top hs

private def BlockIndex (q : ℕ) : ℕ → Type
  | 0 => Unit
  | k + 1 => Fin q × BlockIndex q k

private instance blockIndexFintype (q k : ℕ) : Fintype (BlockIndex q k) :=
  match k with
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 => @instFintypeProd (Fin q) (BlockIndex q k) inferInstance (blockIndexFintype q k)

private theorem blockIndex_card (q k : ℕ) : Fintype.card (BlockIndex q k) = q ^ k := by
  induction k with
  | zero =>
    change Fintype.card Unit = 1
    exact Fintype.card_unique
  | succ k ih =>
    change Fintype.card (Fin q × BlockIndex q k) = _
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]
    exact Nat.mul_comm _ _

private noncomputable def rankCircuit {F : Type u} [Field F] {q r : ℕ}
    (t : Fin r → MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (Fin q × Fin q) (Fin q × Fin q) (Fin q × Fin q)) :
    (k : ℕ) → ArithmeticCircuit F
      ((BlockIndex q k × BlockIndex q k) ⊕ (BlockIndex q k × BlockIndex q k))
      (BlockIndex q k × BlockIndex q k)
  | 0 => { size := 1
           gate := fun _ => .mul (.input (.inl ((), ()))) (.input (.inr ((), ())))
           output := fun _ => .node 0 }
  | k + 1 => rankStep t (rankCircuit t k)

private theorem rankCircuit_correct {F : Type u} [Field F] {q r : ℕ}
    (t : Fin r → MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (Fin q × Fin q) (Fin q × Fin q) (Fin q × Fin q))
    (ht : ∀ a b d, MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F q a b d =
      ∑ s, (t s).eval a b d) (k : ℕ)
    (x : ((BlockIndex q k × BlockIndex q k) ⊕
      (BlockIndex q k × BlockIndex q k)) → F) (i j : BlockIndex q k) :
    (rankCircuit t k).evaluate x (i, j) = ∑ l, x (.inl (i, l)) * x (.inr (l, j)) := by
  induction k with
  | zero =>
    cases i
    cases j
    simp only [rankCircuit, ArithmeticCircuit.evaluate, ArithmeticOperand.evaluate]
    rw [ArithmeticCircuit.evaluateNode.eq_1]
    change x (.inl ((), ())) * x (.inr ((), ())) =
      ∑ l : Unit, x (.inl ((), l)) * x (.inr (l, ()))
    rw [Fintype.sum_unique]
  | succ k ih => exact rankStep_correct t ht _ (fun x i j => ih x i j) x i j

private theorem rankCircuit_size {F : Type u} [Field F] {q r : ℕ}
    (t : Fin r → MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (Fin q × Fin q) (Fin q × Fin q) (Fin q × Fin q)) (hqr : q ^ 2 ≤ r) (k : ℕ) :
    (rankCircuit t k).size ≤ (1 + 6 * r * q ^ 2) * (r + 1) ^ k := by
  induction k with
  | zero => simp [rankCircuit]
  | succ k ih =>
    change (rankStep t (rankCircuit t k)).size ≤ _
    rw [rankStep_size, blockIndex_card, ← pow_mul, Nat.mul_comm k 2, pow_mul]
    have hp := Nat.pow_le_pow_left (hqr.trans (Nat.le_succ r)) k
    calc
      _ ≤ r * ((1 + 6 * r * q ^ 2) * (r + 1) ^ k) +
          6 * r * q ^ 2 * (r + 1) ^ k :=
        Nat.add_le_add (Nat.mul_le_mul_left r ih) (Nat.mul_le_mul_left _ hp)
      _ ≤ (1 + 6 * r * q ^ 2) * (r + 1) ^ (k + 1) := by
        conv_rhs => rw [pow_succ]
        ring_nf
        omega

private def freeCircuit {F : Type u} {A : Type*} {B : Type*}
    (f : B → ArithmeticOperand F A 0) : ArithmeticCircuit F A B where
  size := 0
  gate := fun i => Fin.elim0 i
  output := f

private noncomputable def padInput {F : Type u} {J : Type v} [Field F] [Fintype J]
    {n : ℕ} (e : (Fin n ⊕ Fin (Fintype.card J - n)) ≃ J) :
    ArithmeticCircuit F ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ((J × J) ⊕ (J × J)) :=
  freeCircuit fun o : (J × J) ⊕ (J × J) => match o with
    | .inl (i, j) => match e.symm i, e.symm j with
      | .inl a, .inl b => .input (.inl (a, b))
      | _, _ => .constant 0
    | .inr (i, j) => match e.symm i, e.symm j with
      | .inl a, .inl b => .input (.inr (a, b))
      | _, _ => .constant 0

private noncomputable def padCircuit {F : Type u} {J : Type v} [Field F] [Fintype J]
    {n : ℕ} (e : (Fin n ⊕ Fin (Fintype.card J - n)) ≃ J)
    (c : ArithmeticCircuit F ((J × J) ⊕ (J × J)) (J × J)) :
    MatrixArithmeticCircuit F n n n :=
  (freeCircuit fun ij : Fin n × Fin n => .input (e (.inl ij.1), e (.inl ij.2))).subst
    (c.subst (padInput e))

private theorem padCircuit_size {F : Type u} {J : Type v} [Field F] [Fintype J]
    {n : ℕ} (e : (Fin n ⊕ Fin (Fintype.card J - n)) ≃ J)
    (c : ArithmeticCircuit F ((J × J) ⊕ (J × J)) (J × J)) :
    (padCircuit e c).size = c.size := by
  simp [padCircuit, ArithmeticCircuit.size_subst, padInput, freeCircuit]

private theorem padCircuit_correct {F : Type u} {J : Type v} [Field F] [Fintype J]
    {n : ℕ} (e : (Fin n ⊕ Fin (Fintype.card J - n)) ≃ J)
    (c : ArithmeticCircuit F ((J × J) ⊕ (J × J)) (J × J))
    (hc : ∀ x i j, c.evaluate x (i, j) = ∑ k, x (.inl (i, k)) * x (.inr (k, j))) :
    IsMatrixMultiplication (padCircuit e c) := by
  classical
  intro A B i j
  simp only [padCircuit, ArithmeticCircuit.evaluate_subst]
  change c.evaluate ((padInput e).evaluate (matrixInput A B))
    (e (.inl i), e (.inl j)) = _
  rw [hc]
  rw [← e.sum_comp]
  simp [padInput, freeCircuit, ArithmeticCircuit.evaluate, ArithmeticOperand.evaluate,
    Fintype.sum_sum_type, Matrix.mul_apply, matrixInput]

private theorem rank_circuits_bound {F : Type u} [Field F] {q r : ℕ}
    (t : Fin r → MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (Fin q × Fin q) (Fin q × Fin q) (Fin q × Fin q))
    (ht : ∀ a b d, MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F q a b d =
      ∑ s, (t s).eval a b d) (hq : 1 < q) {p : ℝ} (hp : 0 ≤ p)
    (hrp : (r + 1 : ℕ) ≤ (q : ℝ) ^ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∃ c : MatrixArithmeticCircuit F n n n,
      IsMatrixMultiplication c ∧ (c.size : ℝ) ≤ C * (n : ℝ) ^ p := by
  classical
  have hqr := rank_output_bound (by omega) t ht
  let K := 1 + 6 * r * q ^ 2
  refine ⟨(K * (r + 1) : ℕ), by dsimp [K]; positivity, ?_⟩
  intro n hn
  let k := Nat.log q n
  have hnq : n ≤ q ^ (k + 1) := (Nat.lt_pow_succ_log_self hq n).le
  have hj : n ≤ Fintype.card (BlockIndex q (k + 1)) := by
    rwa [blockIndex_card]
  let e : (Fin n ⊕ Fin (Fintype.card (BlockIndex q (k + 1)) - n)) ≃
      BlockIndex q (k + 1) :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  refine ⟨padCircuit e (rankCircuit t (k + 1)),
    padCircuit_correct e _ (rankCircuit_correct t ht (k + 1)), ?_⟩
  have hpow : ((r + 1 : ℕ) : ℝ) ^ k ≤ (n : ℝ) ^ p := by
    calc
      _ ≤ ((q : ℝ) ^ p) ^ k := pow_le_pow_left₀ (by positivity) hrp k
      _ = ((q : ℝ) ^ k) ^ p := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
          mul_comm p (k : ℝ), Real.rpow_mul (by positivity), Real.rpow_natCast]
      _ ≤ (n : ℝ) ^ p := by
        apply Real.rpow_le_rpow (by positivity) _ hp
        exact_mod_cast Nat.pow_log_le_self q (by omega : n ≠ 0)
  rw [padCircuit_size]
  calc
    _ ≤ ((K * (r + 1) ^ (k + 1) : ℕ) : ℝ) := by
      exact_mod_cast rankCircuit_size t hqr (k + 1)
    _ = ((K * (r + 1) : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) ^ k := by
      push_cast
      rw [pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

private theorem circuit_exponent_of_rank {F : Type u} [Field F] {w : ℝ}
    (h : MatrixMultiplicationExponent.HasMatrixMultiplicationRankExponent F w) :
    HasRectangularCircuitExponent F 1 w := by
  classical
  refine ⟨by norm_num, h.1, ?_⟩
  intro ε hε
  obtain ⟨C, hC, N, hN, hb⟩ := h.2
  have hd : Filter.Tendsto (fun q : ℕ => (q : ℝ) ^ ε) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨q, ⟨hqC, hqN⟩, hq⟩ :=
    (((hd.eventually (Filter.eventually_gt_atTop (C + 1))).and
      (Filter.eventually_ge_atTop N)).and (Filter.eventually_gt_atTop 1)).exists
  obtain ⟨r, ⟨ts, hlen, ht⟩, hr⟩ := hb q hqN
  change (r : ℝ) ≤ C * (q : ℝ) ^ w at hr
  have ht' : ∀ a b d,
      MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F q a b d =
        ∑ s, (ts.get s).eval a b d := by
    intro a b d
    conv_lhs => rw [ht a b d, ← List.ofFn_get ts, List.map_ofFn, List.sum_ofFn]
    rfl
  have hqw : 1 ≤ (q : ℝ) ^ w := Real.one_le_rpow (by exact_mod_cast hq.le) h.1
  have hqp : ((ts.length + 1 : ℕ) : ℝ) ≤ (q : ℝ) ^ (w + ε) := by
    have hlen' : (ts.length : ℝ) ≤ r := by exact_mod_cast hlen
    calc
      _ ≤ C * (q : ℝ) ^ w + 1 := by
        simp only [Nat.cast_add, Nat.cast_one]
        simpa only [add_comm] using add_le_add_right (hlen'.trans hr) (1 : ℝ)
      _ ≤ (C + 1) * (q : ℝ) ^ w := by nlinarith
      _ ≤ (q : ℝ) ^ ε * (q : ℝ) ^ w :=
        mul_le_mul_of_nonneg_right hqC.le (by positivity)
      _ = (q : ℝ) ^ (w + ε) := by
        rw [mul_comm, ← Real.rpow_add (by exact_mod_cast (by omega : 0 < q))]
  obtain ⟨D, hD, hd⟩ := rank_circuits_bound ts.get ht' hq (by linarith [h.1]) hqp
  refine ⟨D, hD, 1, by norm_num, ?_⟩
  intro n hn
  rw [MatrixMultiplicationExponent.rectangularInnerDimension_one]
  exact hd n hn

/-- **Circuit size and tensor rank give the same square exponent.** For every infinite field $F$,
the square matrix multiplication exponent of $F$ defined by arithmetic-circuit size equals the
matrix multiplication exponent of $F$ defined by tensor rank.

Source: C15a additional comments and [B2013]: the arithmetic-operation
exponent agrees with the tensor-rank exponent. This bridge is not proved. -/
theorem squareOperationRankBridge :
    ∀ (F : Type u) [Field F] [Infinite F],
      squareMatrixMultiplicationCircuitExponent F =
        MatrixMultiplicationExponent.matrixMultiplicationExponent F
    := by
  intro F _ _
  apply le_antisymm
  · exact MatrixMultiplicationExponent.le_matrixMultiplicationExponent F
      (fun _ h => rectangularCircuitExponent_le_of_admissible F (circuit_exponent_of_rank h))
  · exact le_rectangularCircuitExponent F (fun _ h => rank_exponent_of_circuit h)

end Cslib.Complexity.Algebraic.SquareMatrixMultiplicationBoundsWanted
