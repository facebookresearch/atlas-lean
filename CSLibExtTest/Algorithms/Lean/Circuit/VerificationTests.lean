/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.Circuit.Verification
public meta import CSLibExt.Computability.Circuit.Boolean
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Cslib.Computability.Circuit.Program
public meta import Mathlib.Data.Fintype.Defs

/-! Ordinary-import runtime checks for the all-gate Boolean certificate verifier. -/

open Cslib.Circuits Cslib.Circuits.Circuit Cslib.Algorithms.Lean
open scoped BigOperators

public meta section

private def runOne {i : Nat} (name : String) (c : Circuit booleanSignature i 1)
    (cert : Array Bool) (expectedRet : Bool) (expectedTime : Nat) : IO Unit := do
  let actual := verifyBooleanCertificate c cert
  unless actual.ret == expectedRet && actual.time == expectedTime do
    let expected := s!"expected ({expectedRet},{expectedTime})"
    let observed := s!"actual ({actual.ret},{actual.time})"
    throw (IO.userError s!"U118 assertion {name}: {expected}, {observed}")
  let input := fun k : Fin i => cert.getD k.val false
  let trace := Array.ofFn (Fin.addCases input (c.program.eval booleanInterpretation input))
  let data := s!"{name}|cert={repr cert.toList}|ret={actual.ret}|time={actual.time}"
  let state := s!"|trace={repr trace.toList}|inputCount={i}|gateCount={c.size}"
  let arguments := ∑ j : Fin c.size, booleanSignature.Arity (c.program.lines j).op
  let source := s!"|arguments={arguments}|sourceSize={i + 2 * c.size}"
  IO.println (data ++ state ++ source)

private def circuit0 : Circuit booleanSignature 3 1 :=
  let p0 : Program booleanSignature 3 0 := .empty
  let p1 : Program booleanSignature 3 1 :=
    .gate p0 ⟨.or 1, fun k =>
        if k.val = 0 then .input ⟨0, by decide⟩ else
        .input ⟨1, by decide⟩⟩
  let p2 : Program booleanSignature 3 2 :=
    .gate p1 ⟨.not, fun k =>
        .input ⟨2, by decide⟩⟩
  let p3 : Program booleanSignature 3 3 :=
    .gate p2 ⟨.and 2, fun k =>
        if k.val = 0 then .input ⟨0, by decide⟩ else
        if k.val = 1 then .input ⟨1, by decide⟩ else
        .gate ⟨1, by decide⟩⟩
  let p4 : Program booleanSignature 3 4 :=
    .gate p3 ⟨.not, fun k =>
        .gate ⟨1, by decide⟩⟩
  let p5 : Program booleanSignature 3 5 :=
    .gate p4 ⟨.or 1, fun k =>
        if k.val = 0 then .gate ⟨0, by decide⟩ else
        .gate ⟨3, by decide⟩⟩
  let p6 : Program booleanSignature 3 6 :=
    .gate p5 ⟨.or 1, fun k =>
        if k.val = 0 then .gate ⟨3, by decide⟩ else
        .gate ⟨2, by decide⟩⟩
  let p7 : Program booleanSignature 3 7 :=
    .gate p6 ⟨.and 2, fun k =>
        if k.val = 0 then .gate ⟨4, by decide⟩ else
        if k.val = 1 then .gate ⟨5, by decide⟩ else
        .gate ⟨2, by decide⟩⟩
  ⟨p7, fun _ => .gate ⟨6, by decide⟩⟩

private def circuit1 : Circuit booleanSignature 3 1 :=
  let p0 : Program booleanSignature 3 0 := .empty
  let p1 : Program booleanSignature 3 1 :=
    .gate p0 ⟨.or 1, fun k =>
        if k.val = 0 then .input ⟨0, by decide⟩ else
        .input ⟨1, by decide⟩⟩
  let p2 : Program booleanSignature 3 2 :=
    .gate p1 ⟨.not, fun k =>
        .input ⟨2, by decide⟩⟩
  let p3 : Program booleanSignature 3 3 :=
    .gate p2 ⟨.and 2, fun k =>
        if k.val = 0 then .input ⟨0, by decide⟩ else
        if k.val = 1 then .input ⟨1, by decide⟩ else
        .gate ⟨1, by decide⟩⟩
  let p4 : Program booleanSignature 3 4 :=
    .gate p3 ⟨.not, fun k =>
        .gate ⟨1, by decide⟩⟩
  let p5 : Program booleanSignature 3 5 :=
    .gate p4 ⟨.and 1, fun k =>
        if k.val = 0 then .gate ⟨0, by decide⟩ else
        .gate ⟨3, by decide⟩⟩
  let p6 : Program booleanSignature 3 6 :=
    .gate p5 ⟨.or 1, fun k =>
        if k.val = 0 then .gate ⟨3, by decide⟩ else
        .gate ⟨2, by decide⟩⟩
  let p7 : Program booleanSignature 3 7 :=
    .gate p6 ⟨.and 2, fun k =>
        if k.val = 0 then .gate ⟨4, by decide⟩ else
        if k.val = 1 then .gate ⟨5, by decide⟩ else
        .gate ⟨2, by decide⟩⟩
  ⟨p7, fun _ => .gate ⟨6, by decide⟩⟩

private def circuit2 : Circuit booleanSignature 1 1 :=
  let p0 : Program booleanSignature 1 0 := .empty
  let p1 : Program booleanSignature 1 1 :=
    .gate p0 ⟨.and 0, fun k =>
        .input ⟨0, by decide⟩⟩
  let p2 : Program booleanSignature 1 2 :=
    .gate p1 ⟨.or 0, fun k =>
        .gate ⟨0, by decide⟩⟩
  ⟨p2, fun _ => .gate ⟨1, by decide⟩⟩

private def circuit3 : Circuit booleanSignature 1 1 :=
  let p0 : Program booleanSignature 1 0 := .empty
  ⟨p0, fun _ => .input ⟨0, by decide⟩⟩

private def circuit4 : Circuit booleanSignature 1 1 :=
  let p0 : Program booleanSignature 1 0 := .empty
  let p1 : Program booleanSignature 1 1 :=
    .gate p0 ⟨.not, fun k =>
        .input ⟨0, by decide⟩⟩
  ⟨p1, fun _ => .input ⟨0, by decide⟩⟩

private def runAllCases : IO Unit := do
  runOne "figure34.8a" circuit0
    #[true, true, false, true, true, true, false, true, true, true] true 23
  runOne "figure34.8b-0" circuit1
    #[false, false, false, false, true, false, false, false, false, false] false 23
  runOne "figure34.8b-1" circuit1
    #[true, false, false, true, true, false, false, false, false, false] false 23
  runOne "figure34.8b-2" circuit1
    #[false, true, false, true, true, false, false, false, false, false] false 23
  runOne "figure34.8b-3" circuit1
    #[true, true, false, true, true, true, false, false, true, false] false 23
  runOne "figure34.8b-4" circuit1
    #[false, false, true, false, false, false, true, false, true, false] false 23
  runOne "figure34.8b-5" circuit1
    #[true, false, true, true, false, false, true, true, true, false] false 23
  runOne "figure34.8b-6" circuit1
    #[false, true, true, true, false, false, true, true, true, false] false 23
  runOne "figure34.8b-7" circuit1
    #[true, true, true, true, false, false, true, true, true, false] false 23
  runOne "short" circuit0
    #[true, true, false, true, true, true, false, true, true] false 1
  runOne "trailing" circuit0
    #[true, true, false, true, true, true, false, true, true, true, false] false 1
  runOne "inconsistent-early-all-gates-still-visited" circuit0
    #[true, true, false, false, true, true, false, true, true, true] false 23
  runOne "inconsistent-output" circuit0
    #[true, true, false, true, true, true, false, true, true, false] false 23
  runOne "unary-gates" circuit2
    #[true, true, true] true 6
  runOne "zero-gate-input-output-true" circuit3
    #[true] true 2
  runOne "zero-gate-input-output-false" circuit3
    #[false] false 2
  runOne "unused-inconsistent-gate-still-rejected" circuit4
    #[true, true] false 4
  runOne "unused-consistent-gate" circuit4
    #[true, false] true 4

#eval runAllCases
