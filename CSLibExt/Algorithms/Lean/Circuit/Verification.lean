/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Circuit.Boolean
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Checking a Boolean circuit certificate

The CLRS4 section 34.3 verifier (printed pages 1067-1068) checks every gate
against a supplied input-and-gate valuation and checks the designated output.
The counted events are the length check, each argument visit, each gate equality
check and the final output check; allocation and bit-machine costs are separate.
-/

namespace Cslib.Circuits.Wire

/-- **Certificate position of a wire.** For a wire that refers to one of $n$ inputs or one of $g$
gates, its position in $\{0, \dots, n + g - 1\}$ is $k$ if it is input $k$ and $n + j$ if it is
gate $j$, so the inputs come first and the gates follow. -/
@[expose] public def toFin {i g : Nat} (wire : Wire i g) : Fin (i + g) :=
  finSumFinEquiv (Wire.equiv i g wire)

@[simp] public theorem toFin_input {i g : Nat} (k : Fin i) :
    (Wire.input k : Wire i g).toFin = k.castAdd g := rfl

@[simp] public theorem toFin_gate {i g : Nat} (k : Fin g) :
    (Wire.gate k : Wire i g).toFin = k.natAdd i := rfl

@[simp] public theorem toFin_castSucc_val {i g : Nat} (wire : Wire i g) :
    wire.castSucc.toFin.val = wire.toFin.val := by
  cases wire <;> rfl

end Cslib.Circuits.Wire

namespace Cslib.Circuits.Circuit

open Cslib.Algorithms.Lean
open scoped BigOperators

private lemma fold_args_spec (n : Nat) (f : Fin n → Bool) :
    Fin.foldl n (fun acc k => do
      let values ← acc
      TimeM.tick 1
      pure (values.push (f k))) (pure #[] : TimeM Nat (Array Bool)) =
      ⟨Array.ofFn f, n⟩ := by
  induction n with
  | zero =>
      apply TimeM.ext
      · simp
      · simp
  | succ n ih =>
      rw [Fin.foldl_succ_last, ih]
      apply TimeM.ext
      · simp [Array.ofFn_succ, Fin.last]
      · simp

private def suppliedArgs {i g : Nat} (line : Line booleanSignature i g)
    (cert : Array Bool) : TimeM Nat (Array Bool) :=
  Fin.foldl (booleanSignature.Arity line.op) (fun acc k => do
    let values ← acc
    TimeM.tick 1
    let value := cert.getD (line.wires k).toFin.val false
    pure (values.push value)) (pure #[])

private lemma suppliedArgs_eq {i g : Nat} (line : Line booleanSignature i g)
    (cert : Array Bool) :
    suppliedArgs line cert =
      ⟨Array.ofFn (fun k => cert.getD (line.wires k).toFin.val false),
        booleanSignature.Arity line.op⟩ :=
  fold_args_spec _ _

private def checkLine {i g : Nat} (line : Line booleanSignature i g)
    (cert : Array Bool) : TimeM Nat Bool := do
  let values ← suppliedArgs line cert
  let computed := booleanInterpretation line.op (fun k => values.getD k.val false)
  TimeM.tick 1
  pure (computed == cert.getD (i + g) false)

private lemma checkLine_eq {i g : Nat} (line : Line booleanSignature i g)
    (cert : Array Bool) :
    checkLine line cert =
      ⟨booleanInterpretation line.op (fun k => cert.getD (line.wires k).toFin.val false) ==
        cert.getD (i + g) false, booleanSignature.Arity line.op + 1⟩ := by
  apply TimeM.ext
  · simp [checkLine, suppliedArgs_eq, Array.getD]
  · simp [checkLine, suppliedArgs_eq]

private def checkProgram {i : Nat} :
    {g : Nat} → Program booleanSignature i g → Array Bool → TimeM Nat Bool
  | _, .empty, _ => pure true
  | _, .gate p line, cert => do
      let prior ← checkProgram p cert
      let equal ← checkLine line cert
      pure (prior && equal)

/-- **Boolean certificate verifier.** Let $c$ be a circuit over the Boolean signature with $n$
inputs, $s$ gates and one output, and let $b = (b_0, \dots, b_{m-1})$ be an array of truth values,
read as a value for each wire: input $k$ at position $k$ and gate $j$ at position $n + j$. The
verifier is a computation with a counted cost. It first checks whether $m = n + s$, at cost $1$;
if not, it returns false. Otherwise, for each gate $j < s$ in order, it reads the entries of $b$
at the positions of the argument wires of gate $j$, at cost $1$ per argument, and compares the
Boolean interpretation of the operation of gate $j$ on these values with $b_{n+j}$, at cost $1$;
finally it reads the entry at the position of the output wire, at cost $1$. It returns true
exactly when every comparison succeeds and that output entry is true. -/
public def verifyBooleanCertificate {i : Nat}
    (c : Circuit booleanSignature i 1) (cert : Array Bool) : TimeM Nat Bool := do
  TimeM.tick 1
  if cert.size = i + c.size then
    let gatesOK ← checkProgram c.program cert
    TimeM.tick 1
    let output := cert.getD (c.outputs 0).toFin.val false
    pure (gatesOK && output)
  else
    pure false

private def lineValue {i g : Nat} (line : Line booleanSignature i g)
    (cert : Array Bool) : Bool :=
  booleanInterpretation line.op (fun k => cert.getD (line.wires k).toFin.val false)

private lemma lineValue_castSucc {i g : Nat} (line : Line booleanSignature i g)
    (cert : Array Bool) :
    lineValue (line.mapWires Wire.Renaming.castSucc) cert = lineValue line cert := by
  unfold lineValue Line.mapWires
  congr 1
  funext k
  simp [Wire.Renaming.castSucc_apply]

private def argumentCount {i : Nat} : {g : Nat} → Program booleanSignature i g → Nat
  | _, .empty => 0
  | _, .gate p line => argumentCount p + booleanSignature.Arity line.op

private lemma checkProgram_ret_iff {i g : Nat} (p : Program booleanSignature i g)
    (cert : Array Bool) :
    (checkProgram p cert).ret = true ↔
      ∀ j : Fin g, lineValue (p.lines j) cert = cert.getD (i + j.val) false := by
  induction p with
  | empty => simp [checkProgram]
  | @gate g p line ih =>
      have hl : (checkLine line cert).ret = true ↔
          lineValue line cert = cert.getD (i + g) false := by
        simp [checkLine_eq, lineValue]
      change ((checkProgram p cert).ret && (checkLine line cert).ret) = true ↔ _
      rw [Bool.and_eq_true, ih, hl, Fin.forall_fin_succ']
      simp [Program.lines_gate_castSucc, Program.lines_gate_last, lineValue_castSucc]

private lemma trace_eq_of_checkProgram {i g : Nat} (p : Program booleanSignature i g)
    (cert : Array Bool) :
    (checkProgram p cert).ret = true →
      ∀ w : Wire i g, p.trace booleanInterpretation (fun k => cert.getD k.val false) w =
        cert.getD w.toFin.val false := by
  induction p with
  | empty =>
      intro _ w
      cases w with
      | input k =>
        exact Program.trace_input Program.empty booleanInterpretation
          (fun k => cert.getD k.val false) k
      | gate k => exact Fin.elim0 k
  | @gate g p line ih =>
      intro h w
      have hp : (checkProgram p cert).ret = true ∧
          lineValue line cert = cert.getD (i + g) false := by
        simpa [checkProgram, checkLine_eq, lineValue] using h
      have he : line.eval booleanInterpretation (fun k => cert.getD k.val false)
          (p.eval booleanInterpretation (fun k => cert.getD k.val false)) =
            lineValue line cert := by
        unfold Line.eval lineValue
        congr 1
        funext k
        exact ih hp.1 (line.wires k)
      refine Wire.lastCases ?_ (fun old => ?_) w
      · exact (Program.eval_gate_last p line booleanInterpretation
          (fun k => cert.getD k.val false)).trans (he.trans hp.2)
      · rw [Program.trace_gate_castSucc, Wire.toFin_castSucc_val]
        exact ih hp.1 old

private lemma argumentCount_eq_sum {i g : Nat} (p : Program booleanSignature i g) :
    argumentCount p = ∑ j : Fin g, booleanSignature.Arity (p.lines j).op := by
  induction p with
  | empty => simp [argumentCount]
  | gate p line ih =>
      simp [argumentCount, Fin.sum_univ_castSucc, ih]

private lemma getD_ofFn {n : Nat} (f : Fin n → Bool) (k : Fin n) :
    (Array.ofFn f).getD k.val false = f k := by
  simp [Array.getD, k.isLt]

private lemma getD_trace {i g : Nat} (p : Program booleanSignature i g)
    (input : Fin i → Bool) (wire : Wire i g) :
    (Array.ofFn (Fin.addCases input (p.eval booleanInterpretation input))).getD
      wire.toFin.val false = p.trace booleanInterpretation input wire := by
  rw [getD_ofFn]
  cases wire <;> simp [Program.trace]

private lemma lineValue_trace {i g : Nat} (p : Program booleanSignature i g)
    (input : Fin i → Bool) (j : Fin g) :
    lineValue (p.lines j) (Array.ofFn (Fin.addCases input (p.eval booleanInterpretation input))) =
      (Array.ofFn (Fin.addCases input (p.eval booleanInterpretation input))).getD
        (i + j.val) false := by
  have he :
      lineValue (p.lines j) (Array.ofFn (Fin.addCases input (p.eval booleanInterpretation input))) =
        (p.lines j).eval booleanInterpretation input (p.eval booleanInterpretation input) := by
    unfold lineValue Line.eval
    congr 1
    funext k
    exact getD_trace p input _
  rw [he, Program.lines_eval]
  exact ((getD_trace p input (Wire.gate j)).trans
    (Program.trace_gateWire p booleanInterpretation input j)).symm

private lemma checkProgram_time {i g : Nat} (p : Program booleanSignature i g)
    (cert : Array Bool) : (checkProgram p cert).time = g + argumentCount p := by
  induction p with
  | empty => simp [checkProgram, argumentCount]
  | gate p line ih =>
      simp [checkProgram, checkLine_eq, argumentCount, ih]
      omega

private lemma argumentCount_le {i g K : Nat} (p : Program booleanSignature i g)
    (h : p.FanInAtMost K) : argumentCount p ≤ g * K := by
  induction p with
  | empty => simp [argumentCount]
  | @gate g p line ih =>
      have prior := ih h.1
      have last := h.2
      simp only [argumentCount, Nat.add_mul, Nat.one_mul]
      omega

/-- **Characterization of accepted certificates.** Let $c$ be a circuit over the Boolean signature
with $n$ inputs, $s$ gates and one output, and let $b = (b_0, \dots, b_{m-1})$ be an array of truth
values, where an entry at a position at or beyond $m$ is read as false and the position of a wire
is $k$ for input $k$ and $n + j$ for gate $j$. The Boolean certificate verifier accepts $b$ if and
only if $m = n + s$, for every gate $j < s$ the Boolean interpretation of the operation of gate $j$
applied to the entries of $b$ at the positions of its argument wires equals $b_{n+j}$, and the
entry of $b$ at the position of the output wire is true. -/
public theorem verifyBooleanCertificate_iff {i : Nat}
    (c : Circuit booleanSignature i 1) (cert : Array Bool) :
    (verifyBooleanCertificate c cert).ret = true ↔
      cert.size = i + c.size ∧
      (∀ j : Fin c.size, booleanInterpretation (c.program.lines j).op
        (fun k => cert.getD ((c.program.lines j).wires k).toFin.val false) =
          cert.getD (i + j.val) false) ∧ cert.getD (c.outputs 0).toFin.val false = true := by
  by_cases h : cert.size = i + c.size
  · simp [verifyBooleanCertificate, h, checkProgram_ret_iff, lineValue]
  · simp [verifyBooleanCertificate, h]

/-- **Soundness of the Boolean certificate verifier.** Let $c$ be a circuit over the Boolean
signature with $n$ inputs, $s$ gates and one output, and let $b = (b_0, \dots, b_{m-1})$ be an array
of truth values, where an entry at a position at or beyond $m$ is read as false and the position
of a wire is $k$ for input $k$ and $n + j$ for gate $j$. If the Boolean certificate verifier
accepts $b$, then, writing $x = (b_0, \dots, b_{n-1})$, the value of every wire of $c$ on input $x$
under the Boolean interpretation equals the entry of $b$ at the position of that wire, and the
output of $c$ on input $x$ is true. -/
public theorem verifyBooleanCertificate_sound {i : Nat}
    (c : Circuit booleanSignature i 1) (cert : Array Bool)
    (h : (verifyBooleanCertificate c cert).ret = true) :
    (∀ w : Wire i c.size, c.program.trace booleanInterpretation
      (fun k => cert.getD k.val false) w = cert.getD w.toFin.val false) ∧
      c.eval booleanInterpretation (fun k => cert.getD k.val false) 0 = true := by
  obtain ⟨_, hg, ho⟩ := (verifyBooleanCertificate_iff c cert).mp h
  have hp : (checkProgram c.program cert).ret = true :=
    (checkProgram_ret_iff c.program cert).mpr (by simpa [lineValue] using hg)
  have hw := trace_eq_of_checkProgram c.program cert hp
  refine ⟨hw, ?_⟩
  exact (hw (c.outputs 0)).trans ho

/-- **Completeness of the Boolean certificate verifier.** Let $c$ be a circuit over the Boolean
signature with $n$ inputs, $s$ gates and one output, and let $x = (x_0, \dots, x_{n-1})$ be truth
values on which the output of $c$ under the Boolean interpretation is true. Let $b$ be the array
$(x_0, \dots, x_{n-1}, v_0, \dots, v_{s-1})$, where $v_j$ is the value of gate $j$ of $c$ on input
$x$. Then $b$ has length $n + s$ and the Boolean certificate verifier accepts $b$. -/
public theorem verifyBooleanCertificate_complete {i : Nat}
    (c : Circuit booleanSignature i 1) (input : Fin i → Bool)
    (h : c.eval booleanInterpretation input 0 = true) :
    let cert := Array.ofFn (Fin.addCases input (c.program.eval booleanInterpretation input))
    cert.size = i + c.size ∧ (verifyBooleanCertificate c cert).ret = true := by
  dsimp only
  have hs : (Array.ofFn (Fin.addCases input (c.program.eval booleanInterpretation input))).size =
      i + c.size := by
    simp
  refine ⟨hs, (verifyBooleanCertificate_iff c _).mpr ⟨hs, ?_, ?_⟩⟩
  · intro j
    exact lineValue_trace c.program input j
  · exact (getD_trace c.program input (c.outputs 0)).trans h

/-- **Short accepted certificates exist exactly for satisfiable circuits.** Let $c$ be a circuit
over the Boolean signature with $n$ inputs, $s$ gates and one output. The Boolean certificate
verifier accepts some array of at most $n + 2s$ truth values if and only if there are truth
values $x_0, \dots, x_{n-1}$ on which the output of $c$ under the Boolean interpretation is
true. -/
public theorem verifyBooleanCertificate_satisfiable_iff {i : Nat}
    (c : Circuit booleanSignature i 1) :
    (∃ cert : Array Bool, (verifyBooleanCertificate c cert).ret = true ∧
      cert.size ≤ i + 2 * c.size) ↔
      ∃ input : Fin i → Bool, c.eval booleanInterpretation input 0 = true := by
  constructor
  · rintro ⟨cert, h, _⟩
    exact ⟨fun k => cert.getD k.val false, (verifyBooleanCertificate_sound c cert h).2⟩
  · rintro ⟨input, h⟩
    obtain ⟨hs, hv⟩ := verifyBooleanCertificate_complete c input h
    refine ⟨Array.ofFn (Fin.addCases input (c.program.eval booleanInterpretation input)), hv, ?_⟩
    omega

/-- **Cost of the Boolean certificate verifier.** Let $c$ be a circuit over the Boolean signature
with $n$ inputs, $s$ gates and one output, and let $b$ be an array of $m$ truth values. The cost
counted by the Boolean certificate verifier on $b$ is $2 + s + \sum_{j < s} a_j$ if $m = n + s$,
where $a_j$ is the number of arguments of gate $j$, and $1$ otherwise. -/
public theorem verifyBooleanCertificate_time {i : Nat}
    (c : Circuit booleanSignature i 1) (cert : Array Bool) :
    (verifyBooleanCertificate c cert).time =
      if cert.size = i + c.size then
        2 + c.size + ∑ j : Fin c.size, booleanSignature.Arity (c.program.lines j).op
      else 1 := by
  by_cases h : cert.size = i + c.size
  · simp [verifyBooleanCertificate, h, checkProgram_time, argumentCount_eq_sum]
    omega
  · simp [verifyBooleanCertificate, h]

/-- **Linear cost of the Boolean certificate verifier.** Let $K$ be a natural number and let $c$ be
a circuit over the Boolean signature with $n$ inputs, $s$ gates and one output in which every gate
has at most $K$ arguments. Then for every array $b$ of truth values, the cost counted by the
Boolean certificate verifier on $b$ is at most $2 + (K + 1)s$. -/
public theorem verifyBooleanCertificate_time_le_of_fanInAtMost {i K : Nat}
    (c : Circuit booleanSignature i 1) (cert : Array Bool) (hfan : c.FanInAtMost K) :
    (verifyBooleanCertificate c cert).time ≤ 2 + (K + 1) * c.size := by
  rw [verifyBooleanCertificate_time]
  by_cases h : cert.size = i + c.size
  · have hc := argumentCount_le c.program hfan
    rw [argumentCount_eq_sum, Nat.mul_comm c.size K] at hc
    simp only [ite_eq_left h, Nat.add_mul, Nat.one_mul]
    omega
  · simp only [ite_eq_right h]
    omega

end Cslib.Circuits.Circuit
