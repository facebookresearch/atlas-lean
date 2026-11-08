/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Circuit.Verification

/-! Ordinary-import type and proposition coverage for the Boolean certificate API. -/

open Cslib.Circuits Cslib.Circuits.Circuit Cslib.Algorithms.Lean
open scoped BigOperators

example {i : Nat} (c : Circuit booleanSignature i 1) (cert : Array Bool) :
    TimeM Nat Bool := verifyBooleanCertificate c cert

example {i : Nat} (c : Circuit booleanSignature i 1) (cert : Array Bool) :
    (verifyBooleanCertificate c cert).ret = true ↔
      cert.size = i + c.size ∧
      (∀ j : Fin c.size, booleanInterpretation (c.program.lines j).op
        (fun k => cert.getD ((c.program.lines j).wires k).toFin.val false) =
          cert.getD (i + j.val) false) ∧ cert.getD (c.outputs 0).toFin.val false = true :=
  verifyBooleanCertificate_iff c cert

example {i : Nat} (c : Circuit booleanSignature i 1) (cert : Array Bool)
    (h : (verifyBooleanCertificate c cert).ret = true) :
    (∀ w : Wire i c.size, c.program.trace booleanInterpretation
      (fun k => cert.getD k.val false) w = cert.getD w.toFin.val false) ∧
      c.eval booleanInterpretation (fun k => cert.getD k.val false) 0 = true :=
  verifyBooleanCertificate_sound c cert h

example {i : Nat} (c : Circuit booleanSignature i 1) (input : Fin i → Bool)
    (h : c.eval booleanInterpretation input 0 = true) :
    let cert := Array.ofFn (Fin.addCases input (c.program.eval booleanInterpretation input))
    cert.size = i + c.size ∧ (verifyBooleanCertificate c cert).ret = true :=
  verifyBooleanCertificate_complete c input h

example {i : Nat} (c : Circuit booleanSignature i 1) :
    (∃ cert : Array Bool, (verifyBooleanCertificate c cert).ret = true ∧
      cert.size ≤ i + 2 * c.size) ↔
      ∃ input : Fin i → Bool, c.eval booleanInterpretation input 0 = true :=
  verifyBooleanCertificate_satisfiable_iff c

example {i : Nat} (c : Circuit booleanSignature i 1) (cert : Array Bool) :
    (verifyBooleanCertificate c cert).time =
      if cert.size = i + c.size then
        2 + c.size + ∑ j : Fin c.size, booleanSignature.Arity (c.program.lines j).op
      else 1 := verifyBooleanCertificate_time c cert

example {i K : Nat} (c : Circuit booleanSignature i 1) (cert : Array Bool)
    (hfan : c.FanInAtMost K) :
    (verifyBooleanCertificate c cert).time ≤ 2 + (K + 1) * c.size :=
  verifyBooleanCertificate_time_le_of_fanInAtMost c cert hfan

example (f : Fin 1 → Bool) : booleanInterpretation .not f = !(f 0) :=
  booleanInterpretation_not f

example (a : Nat) (f : Fin (a + 1) → Bool) :
    booleanInterpretation (.and a) f =
      Fin.foldl (a + 1) (fun acc k => acc && f k) true := booleanInterpretation_and a f

example (a : Nat) (f : Fin (a + 1) → Bool) :
    booleanInterpretation (.or a) f =
      Fin.foldl (a + 1) (fun acc k => acc || f k) false := booleanInterpretation_or a f
