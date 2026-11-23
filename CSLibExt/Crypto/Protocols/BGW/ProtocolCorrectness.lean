/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Circuit.Basic
public import Cslib.Computability.Circuit.Program
public import Cslib.Computability.Circuit.Signature
public import Cslib.Computability.Circuit.Wire
public import Cslib.Crypto.Protocols.SecretSharing.Shamir
public import Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial
public import CSLibExt.Crypto.Protocols.BGW.ShareAlgebra
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.WithBot

/-!
# BGW protocol correctness under honest execution

For arithmetic circuits over a field, the BGW protocol evaluates every gate on
Shamir-shared values. Addition gates are evaluated locally on shares, since a
sum of low-degree sharings is again a low-degree sharing of the sum.
Multiplication gates locally multiply shares, which doubles the degree, and
then reshare each product share and recombine the resharings with a fixed
recombination vector to restore the degree bound.

This file proves honest-execution correctness: one recombination vector, fixed
before the circuit, the inputs, and the randomness tapes are chosen, makes
every output wire reconstruct to the value the circuit computes on the inputs,
for every circuit, every input assignment, and every randomness tape.

## Main results

* `protocol_correct_exists`: there is a recombination vector such that every
  circuit, input assignment, input tape, multiplication tape, and output index
  evaluates correctly.
-/

@[expose] public section

open Cslib.Circuits
open Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial

namespace CSLibExt.Crypto.Protocols.BGW

/-- Arithmetic gate labels: binary addition and multiplication. -/
inductive ArithOp where
  | add : ArithOp
  | mul : ArithOp

/-- The signature with binary addition and multiplication. -/
abbrev arithSignature : Cslib.Circuits.Signature where
  Op := ArithOp
  Arity
    | .add => 2
    | .mul => 2

/-- Evaluate arithmetic gates in a type with addition and multiplication. -/
def arithInterp {F : Type*} [Add F] [Mul F] :
    Cslib.Circuits.Interpretation arithSignature F
  | .add, x => x 0 + x 1
  | .mul, x => x 0 * x 1

/-- From a degree bound below `t + 1` to a natural-degree bound by `t`. -/
theorem polyNatDegree_le_of_degree_lt_succ {F : Type*} [Field F]
    (p : Polynomial F) (t : ℕ) (h : p.degree < (t + 1 : WithBot ℕ)) :
    p.natDegree ≤ t := by
  haveI : Decidable (p = 0) := Classical.propDecidable _
  by_cases hp0 : p = 0
  · subst hp0
    simp [Polynomial.natDegree_zero]
  · rw [Polynomial.degree_eq_natDegree hp0] at h
    have hlt : p.natDegree < t + 1 := by exact_mod_cast h
    exact Nat.lt_succ_iff.mp hlt

/-- From a natural-degree bound by `t` to a degree bound below `t + 1`. -/
theorem polyDegree_lt_succ_of_natDegree_le {F : Type*} [Field F]
    (p : Polynomial F) (t : ℕ) (h : p.natDegree ≤ t) :
    p.degree < ((t + 1 : ℕ) : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le h) ?_
  have hlt : t < t + 1 := Nat.lt_succ_self t
  exact_mod_cast hlt

/-- The constant coefficient is evaluation at zero. -/
theorem polyConstantCoeff_eq_eval_zero {F : Type*} [Field F] (p : Polynomial F) :
    p.constantCoeff = p.eval 0 := by
  rw [Polynomial.constantCoeff_apply, Polynomial.coeff_zero_eq_eval_zero]

/-- Recombination vector from the share-algebra provider, in the form used by
    the multiplication handler: a fixed linear combination of the shares that
    recovers the secret of every polynomial of natural degree at most twice
    the threshold. -/
theorem recombination_vector_spec {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    (h2t : 2 * params.threshold < Fintype.card Party) :
    ∃ lam : Party → F, ∀ p : Polynomial F, p.natDegree ≤ 2 * params.threshold →
      (∑ i ∈ Finset.univ, lam i * p.eval (params.point i)) = p.eval 0 := by
  obtain ⟨r, hr⟩ := CSLibExt.Crypto.Protocols.BGW.shamir_exists_recombination_vector params h2t
  exact ⟨r, fun p hp => (hr p hp).symm⟩

/-- The sharing polynomial for a new gate, from its operation, argument wires,
    the wire polynomials computed so far, fresh reshare randomness, and the
    fixed recombination vector. For multiplication, the reshared secret is the
    product polynomial evaluated at each party's point, which equals the
    product of the argument shares. -/
noncomputable def newGatePoly {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    (lam : Party → F) {inputCount gateCount : Nat}
    (op : ArithOp) (wires : Fin (arithSignature.Arity op) → Wire inputCount gateCount)
    (wirePoly : Wire inputCount gateCount → Polynomial F)
    (tape : Party → Fin params.threshold → F) : Polynomial F :=
  match op, wires with
  | .add, wires => wirePoly (wires 0) + wirePoly (wires 1)
  | .mul, wires =>
      ∑ i ∈ Finset.univ,
        Polynomial.C (lam i) *
          sharingPolynomial
            ((wirePoly (wires 0) * wirePoly (wires 1)).eval (params.point i))
            (tailPolynomial params.threshold (tape i))

/-- Gate sharing polynomials for a straight-line program. Inputs are shared
    with `inPolys`; each multiplication gate consumes one fresh reshare tape
    per party. -/
noncomputable def gatePolys {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    (lam : Party → F) {inputCount : Nat} {gateCount : Nat}
    (prog : Program arithSignature inputCount gateCount)
    (inPolys : Fin inputCount → Polynomial F)
    (tapeMul : Fin gateCount → Party → Fin params.threshold → F) :
    Fin gateCount → Polynomial F :=
  match prog with
  | .empty => Fin.elim0
  | @Program.gate _ _ g p line =>
      Fin.lastCases
        (newGatePoly params lam line.op line.wires
          (Wire.elim inPolys
            (gatePolys params lam p inPolys (fun g' => tapeMul g'.castSucc)))
          (tapeMul (Fin.last g)))
        (gatePolys params lam p inPolys (fun g' => tapeMul g'.castSucc))

/-- Input sharing polynomials: each input shared with its tape. -/
noncomputable def inputPolys {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    {inputCount : Nat} (x : Fin inputCount → F)
    (tapeIn : Fin inputCount → Fin params.threshold → F) :
    Fin inputCount → Polynomial F :=
  fun k => sharingPolynomial (x k) (tailPolynomial params.threshold (tapeIn k))

/-- Each input polynomial shares its input value with degree at most the
    threshold. -/
theorem inputPolys_ok {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    {inputCount : Nat} (x : Fin inputCount → F)
    (tapeIn : Fin inputCount → Fin params.threshold → F) (k : Fin inputCount) :
    ((inputPolys params x tapeIn k).eval 0 = x k) ∧
      ((inputPolys params x tapeIn k).natDegree ≤ params.threshold) := by
  refine ⟨?_, ?_⟩
  · show (sharingPolynomial (x k)
        (tailPolynomial params.threshold (tapeIn k))).eval 0 = x k
    simp [sharingPolynomial_eval]
  · show (sharingPolynomial (x k)
        (tailPolynomial params.threshold (tapeIn k))).natDegree ≤ params.threshold
    exact polyNatDegree_le_of_degree_lt_succ _ _
      (degree_sharingPolynomial_tailPolynomial_lt_succ _ _ _)

/-- The new gate polynomial shares the gate's true value with degree at most
    the threshold, whenever the wire polynomials do. -/
theorem newGatePoly_ok {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    (lam : Party → F)
    (hlam : ∀ p : Polynomial F, p.natDegree ≤ 2 * params.threshold →
      (∑ i ∈ Finset.univ, lam i * p.eval (params.point i)) = p.eval 0)
    {inputCount gateCount : Nat}
    (op : ArithOp) (wires : Fin (arithSignature.Arity op) → Wire inputCount gateCount)
    (x : Fin inputCount → F) (P : Fin gateCount → F)
    (WP : Wire inputCount gateCount → Polynomial F)
    (hWP : ∀ w, (WP w).eval 0 = (Wire.elim x P) w ∧
      (WP w).natDegree ≤ params.threshold)
    (tape : Party → Fin params.threshold → F) :
    ((newGatePoly params lam op wires WP tape).eval 0 =
      Line.eval ⟨op, wires⟩ arithInterp x P) ∧
    ((newGatePoly params lam op wires WP tape).natDegree ≤ params.threshold) := by
  cases op
  · refine ⟨?_, ?_⟩
    · show ((WP (wires 0) + WP (wires 1)).eval 0) =
          Line.eval ⟨ArithOp.add, wires⟩ arithInterp x P
      rw [Polynomial.eval_add, (hWP (wires 0)).1, (hWP (wires 1)).1]
      simp [Line.eval, arithInterp]
    · show ((WP (wires 0) + WP (wires 1)).natDegree) ≤ params.threshold
      refine (Polynomial.natDegree_add_le _ _).trans ?_
      rw [max_le_iff]
      exact ⟨(hWP (wires 0)).2, (hWP (wires 1)).2⟩
  · have hD : ((WP (wires 0) * WP (wires 1))).natDegree ≤ 2 * params.threshold :=
      natDegree_mul_le_two_mul _ _ _ (hWP (wires 0)).2 (hWP (wires 1)).2
    have hrec := hlam _ hD
    have hBr : ∀ i, (sharingPolynomial
          ((WP (wires 0) * WP (wires 1)).eval (params.point i))
          (tailPolynomial params.threshold (tape i))).eval 0 =
          ((WP (wires 0) * WP (wires 1)).eval (params.point i)) := by
      intro i
      simp [sharingPolynomial_eval]
    have hCr : ∀ i, (sharingPolynomial
          ((WP (wires 0) * WP (wires 1)).eval (params.point i))
          (tailPolynomial params.threshold (tape i))).natDegree ≤
          params.threshold := by
      intro i
      exact polyNatDegree_le_of_degree_lt_succ _ _
        (degree_sharingPolynomial_tailPolynomial_lt_succ _ _ _)
    refine ⟨?_, ?_⟩
    · show (∑ i ∈ Finset.univ,
            Polynomial.C (lam i) *
              sharingPolynomial ((WP (wires 0) * WP (wires 1)).eval (params.point i))
                (tailPolynomial params.threshold (tape i))).eval 0 =
          Line.eval ⟨ArithOp.mul, wires⟩ arithInterp x P
      rw [Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_C_mul]
      simp only [hBr]
      rw [hrec]
      rw [Polynomial.eval_mul, (hWP (wires 0)).1, (hWP (wires 1)).1]
      simp [Line.eval, arithInterp]
    · show (∑ i ∈ Finset.univ,
            Polynomial.C (lam i) *
              sharingPolynomial ((WP (wires 0) * WP (wires 1)).eval (params.point i))
                (tailPolynomial params.threshold (tape i))).natDegree ≤
          params.threshold
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
      exact (Polynomial.natDegree_C_mul_le _ _).trans (hCr i)

/-- Every gate polynomial shares the gate's true value with degree at most the
    threshold. -/
theorem gatePolys_ok {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    (lam : Party → F)
    (hlam : ∀ p : Polynomial F, p.natDegree ≤ 2 * params.threshold →
      (∑ i ∈ Finset.univ, lam i * p.eval (params.point i)) = p.eval 0)
    {inputCount : Nat} {gateCount : Nat}
    (prog : Program arithSignature inputCount gateCount)
    (x : Fin inputCount → F)
    (inPolys : Fin inputCount → Polynomial F)
    (hin : ∀ k, (inPolys k).eval 0 = x k ∧
      (inPolys k).natDegree ≤ params.threshold) :
    ∀ (tapeMul : Fin gateCount → Party → Fin params.threshold → F) (g : Fin gateCount),
      (((gatePolys params lam prog inPolys tapeMul) g).eval 0 =
        (prog.eval arithInterp x) g) ∧
      (((gatePolys params lam prog inPolys tapeMul) g).natDegree ≤
        params.threshold) := by
  induction prog with
  | empty => intro tapeMul g; exact Fin.elim0 g
  | gate p line ih =>
      intro tapeMul g
      refine Fin.lastCases ?_ (fun g' => ?_) g
      · have hred : (gatePolys params lam (p.gate line) inPolys tapeMul) (Fin.last _) =
            newGatePoly params lam line.op line.wires
              (Wire.elim inPolys
                (gatePolys params lam p inPolys (fun g => tapeMul g.castSucc)))
              (tapeMul (Fin.last _)) := by simp [gatePolys]
        rw [hred, Program.eval_gate_last]
        have hWP : ∀ w,
              ((Wire.elim inPolys
                (gatePolys params lam p inPolys
                  (fun g => tapeMul g.castSucc))) w).eval 0 =
                ((Wire.elim x (Program.eval p arithInterp x)) w) ∧
              ((Wire.elim inPolys
                (gatePolys params lam p inPolys
                  (fun g => tapeMul g.castSucc))) w).natDegree ≤
                params.threshold := by
          intro w
          cases w with
          | input k =>
              simp only [Wire.elim_input]
              exact hin k
          | gate g' =>
              simp only [Wire.elim_gate]
              exact ih _ g'
        exact newGatePoly_ok params lam hlam line.op line.wires x _ _ hWP _
      · have hred : ∀ g', (gatePolys params lam (p.gate line) inPolys tapeMul) g'.castSucc =
            (gatePolys params lam p inPolys (fun g => tapeMul g.castSucc)) g' :=
          fun g' => by simp [gatePolys]
        rw [hred _, Program.eval_gate_castSucc]
        exact ih _ _

/-- Every wire polynomial, input or gate, shares the wire's trace value with
    degree at most the threshold. -/
theorem wirePoly_ok {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    {inputCount gateCount : Nat}
    (prog : Program arithSignature inputCount gateCount)
    (x : Fin inputCount → F)
    (inPolys : Fin inputCount → Polynomial F)
    (hin : ∀ k, (inPolys k).eval 0 = x k ∧
      (inPolys k).natDegree ≤ params.threshold)
    (P : Fin gateCount → Polynomial F)
    (hP : ∀ g, (P g).eval 0 = (prog.eval arithInterp x) g ∧
      (P g).natDegree ≤ params.threshold)
    (w : Wire inputCount gateCount) :
    (((Wire.elim inPolys P) w).eval 0 = (prog.trace arithInterp x) w) ∧
      (((Wire.elim inPolys P) w).natDegree ≤ params.threshold) := by
  cases w with
  | input k =>
      simp only [Wire.elim_input, Program.trace_input]
      exact hin k
  | gate g =>
      simp only [Wire.elim_gate, Program.trace_gateWire, Program.gateFunction_apply]
      exact hP g

/-- Share-level execution of inputs: party `j`'s share of input `k` is the Shamir
    share of `x k` under `tapeIn k`. -/
noncomputable def inputShares {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    {inputCount : Nat} (x : Fin inputCount → F)
    (tapeIn : Fin inputCount → Fin params.threshold → F) :
    Fin inputCount → Party → F :=
  fun k j => Cslib.Crypto.Protocols.SecretSharing.Shamir.share params (tapeIn k) (x k) j

/-- Share-level execution of one new gate from the operand wires' share
    functions: addition is pointwise on shares; multiplication reshares each
    party's local product and recombines the resharings. -/
noncomputable def newGateShare {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    (lam : Party → F) {inputCount gateCount : Nat}
    (op : ArithOp) (wires : Fin (arithSignature.Arity op) → Wire inputCount gateCount)
    (wireShare : Wire inputCount gateCount → Party → F)
    (tape : Party → Fin params.threshold → F) : Party → F :=
  match op, wires with
  | .add, wires => fun j => wireShare (wires 0) j + wireShare (wires 1) j
  | .mul, wires => fun j => ∑ i ∈ Finset.univ,
        lam i * Cslib.Crypto.Protocols.SecretSharing.Shamir.share params (tape i)
          (wireShare (wires 0) i * wireShare (wires 1) i) j

/-- Share-level execution of every gate in a straight-line program. -/
noncomputable def gateShares {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    (lam : Party → F) {inputCount : Nat} {gateCount : Nat}
    (prog : Program arithSignature inputCount gateCount)
    (inShares : Fin inputCount → Party → F)
    (tapeMul : Fin gateCount → Party → Fin params.threshold → F) :
    Fin gateCount → Party → F :=
  match prog with
  | .empty => Fin.elim0
  | @Program.gate _ _ g p line =>
      Fin.lastCases
        (newGateShare params lam line.op line.wires
          (Wire.elim inShares
            (gateShares params lam p inShares (fun g' => tapeMul g'.castSucc)))
          (tapeMul (Fin.last g)))
        (gateShares params lam p inShares (fun g' => tapeMul g'.castSucc))

/-- Share-level execution: the share function `Party → F` of each wire. -/
noncomputable def execShare {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    (lam : Party → F) {inputCount gateCount : Nat}
    (prog : Program arithSignature inputCount gateCount)
    (x : Fin inputCount → F)
    (tapeIn : Fin inputCount → Fin params.threshold → F)
    (tapeMul : Fin gateCount → Party → Fin params.threshold → F) :
    Wire inputCount gateCount → Party → F :=
  Wire.elim (inputShares params x tapeIn)
    (gateShares params lam prog (inputShares params x tapeIn) tapeMul)

/-- Input shares agree with input-polynomial evaluations. -/
theorem inputShares_bridge {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    {inputCount : Nat} (x : Fin inputCount → F)
    (tapeIn : Fin inputCount → Fin params.threshold → F)
    (k : Fin inputCount) (j : Party) :
    inputShares params x tapeIn k j =
      (inputPolys params x tapeIn k).eval (params.point j) := rfl

/-- One gate's shares agree with its witness-polynomial evaluations. -/
theorem newGateShare_bridge {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    (lam : Party → F)
    {inputCount gateCount : Nat}
    (op : ArithOp) (wires : Fin (arithSignature.Arity op) → Wire inputCount gateCount)
    (WS : Wire inputCount gateCount → Party → F)
    (WP : Wire inputCount gateCount → Polynomial F)
    (hW : ∀ w j, WS w j = (WP w).eval (params.point j))
    (tape : Party → Fin params.threshold → F) (j : Party) :
    newGateShare params lam op wires WS tape j =
      (newGatePoly params lam op wires WP tape).eval (params.point j) := by
  cases op
  · show WS (wires 0) j + WS (wires 1) j =
        ((WP (wires 0) + WP (wires 1)).eval (params.point j))
    rw [Polynomial.eval_add, hW, hW]
  · have hsec : ∀ i, ((WP (wires 0) * WP (wires 1)).eval (params.point i)) =
        WS (wires 0) i * WS (wires 1) i := by
      intro i
      rw [Polynomial.eval_mul, ← hW, ← hW]
    show (∑ i ∈ Finset.univ, lam i *
          Cslib.Crypto.Protocols.SecretSharing.Shamir.share params (tape i)
            (WS (wires 0) i * WS (wires 1) i) j) =
        ((∑ i ∈ Finset.univ,
            Polynomial.C (lam i) *
              sharingPolynomial ((WP (wires 0) * WP (wires 1)).eval (params.point i))
                (tailPolynomial params.threshold (tape i))).eval (params.point j))
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Polynomial.eval_C_mul, hsec i]
    rfl

/-- Every gate's shares agree with its witness-polynomial evaluations. -/
theorem gateShares_bridge {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    (lam : Party → F)
    {inputCount : Nat} {gateCount : Nat}
    (prog : Program arithSignature inputCount gateCount)
    (inShares : Fin inputCount → Party → F)
    (inPolys : Fin inputCount → Polynomial F)
    (hin : ∀ k j, inShares k j = (inPolys k).eval (params.point j)) :
    ∀ (tapeMul : Fin gateCount → Party → Fin params.threshold → F) (g : Fin gateCount)
      (j : Party),
      (gateShares params lam prog inShares tapeMul g) j =
        ((gatePolys params lam prog inPolys tapeMul g).eval (params.point j)) := by
  induction prog with
  | empty => intro tapeMul g; exact Fin.elim0 g
  | gate p line ih =>
      intro tapeMul g j
      refine Fin.lastCases ?_ (fun g' => ?_) g
      · have hredS : (gateShares params lam (p.gate line) inShares tapeMul) (Fin.last _) =
            newGateShare params lam line.op line.wires
              (Wire.elim inShares
                (gateShares params lam p inShares (fun g => tapeMul g.castSucc)))
              (tapeMul (Fin.last _)) := by simp [gateShares]
        have hredP : (gatePolys params lam (p.gate line) inPolys tapeMul) (Fin.last _) =
            newGatePoly params lam line.op line.wires
              (Wire.elim inPolys
                (gatePolys params lam p inPolys (fun g => tapeMul g.castSucc)))
              (tapeMul (Fin.last _)) := by simp [gatePolys]
        rw [hredS, hredP]
        have hW : ∀ w j,
              ((Wire.elim inShares
                (gateShares params lam p inShares
                  (fun g => tapeMul g.castSucc))) w) j =
                (((Wire.elim inPolys
                  (gatePolys params lam p inPolys
                    (fun g => tapeMul g.castSucc))) w).eval (params.point j)) := by
          intro w j
          cases w with
          | input k =>
              simp only [Wire.elim_input]
              exact hin k j
          | gate g' =>
              simp only [Wire.elim_gate]
              exact ih _ g' j
        exact newGateShare_bridge params lam line.op line.wires _ _ hW _ j
      · have hredS : ∀ g', (gateShares params lam (p.gate line) inShares tapeMul) g'.castSucc =
            (gateShares params lam p inShares (fun g => tapeMul g.castSucc)) g' :=
          fun g' => by simp [gateShares]
        have hredP : ∀ g', (gatePolys params lam (p.gate line) inPolys tapeMul) g'.castSucc =
            (gatePolys params lam p inPolys (fun g => tapeMul g.castSucc)) g' :=
          fun g' => by simp [gatePolys]
        rw [hredS _, hredP _]
        exact ih _ _ _

/-- Every wire's share function agrees with its witness-polynomial evaluations. -/
theorem execShare_bridge {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    (lam : Party → F)
    {inputCount gateCount : Nat}
    (prog : Program arithSignature inputCount gateCount)
    (x : Fin inputCount → F)
    (tapeIn : Fin inputCount → Fin params.threshold → F)
    (tapeMul : Fin gateCount → Party → Fin params.threshold → F)
    (w : Wire inputCount gateCount) (j : Party) :
    execShare params lam prog x tapeIn tapeMul w j =
      ((Wire.elim (inputPolys params x tapeIn)
        (gatePolys params lam prog (inputPolys params x tapeIn) tapeMul) w).eval
        (params.point j)) := by
  cases w with
  | input k => exact inputShares_bridge params x tapeIn k j
  | gate g =>
      exact gateShares_bridge params lam prog _ _
        (fun k j => inputShares_bridge params x tapeIn k j) tapeMul g j

/-- Output shares: each party's share of the output wire. -/
noncomputable def protoShares {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    (lam : Party → F) {inputCount outputCount : Nat}
    (circ : Circuit arithSignature inputCount outputCount)
    (x : Fin inputCount → F)
    (tapeIn : Fin inputCount → Fin params.threshold → F)
    (tapeMul : Fin circ.size → Party → Fin params.threshold → F)
    (j : Fin outputCount) : (↥(Finset.univ : Finset Party) → F) :=
  fun i => execShare params lam circ.program x tapeIn tapeMul (circ.outputs j) i

/-- Honest-execution correctness for a fixed recombination vector: every
    output reconstructs to the circuit's value on every input and tape. -/
theorem protocol_correct {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    (lam : Party → F)
    (hlam : ∀ p : Polynomial F, p.natDegree ≤ 2 * params.threshold →
      (∑ i ∈ Finset.univ, lam i * p.eval (params.point i)) = p.eval 0)
    {inputCount outputCount : Nat}
    (circ : Circuit arithSignature inputCount outputCount)
    (x : Fin inputCount → F)
    (tapeIn : Fin inputCount → Fin params.threshold → F)
    (tapeMul : Fin circ.size → Party → Fin params.threshold → F)
    (j : Fin outputCount) :
    Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct params Finset.univ
        (protoShares params lam circ x tapeIn tapeMul j) =
      (circ.eval arithInterp x) j := by
  have hP := gatePolys_ok params lam hlam circ.program x
    (inputPolys params x tapeIn) (inputPolys_ok params x tapeIn) tapeMul
  have hwire := wirePoly_ok params circ.program x _ (inputPolys_ok params x tapeIn) _
    hP (circ.outputs j)
  have hfun : protoShares params lam circ x tapeIn tapeMul j =
      fun (i : ↥(Finset.univ : Finset Party)) => ((Wire.elim (inputPolys params x tapeIn)
        (gatePolys params lam circ.program (inputPolys params x tapeIn) tapeMul))
        (circ.outputs j)).eval (params.point i) := by
    funext i
    exact execShare_bridge params lam circ.program x tapeIn tapeMul (circ.outputs j) i
  rw [hfun]
  have hx : Function.Injective
      (fun i : ↥(Finset.univ : Finset Party) => params.point i) := by
    intro i j hij
    exact Subtype.ext (params.point_injective hij)
  have hcard : Fintype.card ↥(Finset.univ : Finset Party) = Fintype.card Party := by
    simp [Fintype.card_coe]
  have hle : params.threshold + 1 ≤ Fintype.card ↥(Finset.univ : Finset Party) := by
    rw [hcard]
    have hlt := params.threshold_lt_card
    omega
  have hdeg : ((Wire.elim (inputPolys params x tapeIn)
        (gatePolys params lam circ.program (inputPolys params x tapeIn) tapeMul))
        (circ.outputs j)).degree < Fintype.card ↥(Finset.univ : Finset Party) :=
    lt_of_lt_of_le
      (polyDegree_lt_succ_of_natDegree_le _ _ hwire.2)
      (by exact_mod_cast hle)
  have hrec := reconstruct_eq_constantCoeff_of_eval_eq
    (x := fun i : ↥(Finset.univ : Finset Party) => params.point i)
    (p := (Wire.elim (inputPolys params x tapeIn)
      (gatePolys params lam circ.program (inputPolys params x tapeIn) tapeMul))
      (circ.outputs j)) hx hdeg
  have hcc : ((Wire.elim (inputPolys params x tapeIn)
        (gatePolys params lam circ.program (inputPolys params x tapeIn) tapeMul))
        (circ.outputs j)).constantCoeff = (circ.eval arithInterp x) j :=
    (polyConstantCoeff_eq_eval_zero _).trans hwire.1
  exact hrec.trans hcc

/-- Honest-execution correctness: one recombination vector works for every
    circuit, input, and randomness tape. -/
theorem protocol_correct_exists {F : Type*} [Field F] {Party : Type*} [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    (h2t : 2 * params.threshold < Fintype.card Party) :
    ∃ lam : Party → F, ∀ {inputCount outputCount : Nat}
      (circ : Circuit arithSignature inputCount outputCount)
      (x : Fin inputCount → F)
      (tapeIn : Fin inputCount → Fin params.threshold → F)
      (tapeMul : Fin circ.size → Party → Fin params.threshold → F)
      (j : Fin outputCount),
      Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct params Finset.univ
        (protoShares params lam circ x tapeIn tapeMul j) =
        (circ.eval arithInterp x) j := by
  obtain ⟨lam, hlam⟩ := recombination_vector_spec params h2t
  exact ⟨lam, fun circ x tapeIn tapeMul j =>
    protocol_correct params lam hlam circ x tapeIn tapeMul j⟩

end CSLibExt.Crypto.Protocols.BGW
