/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.SatTimeM

@[expose] public section

set_option autoImplicit false

open Cslib.CookLevin

#check varsOf
#check lookupVar
#check checkClause
#check checkCNF
#check satVerifier
#check lookupVar_time_le
#check lookupVar_ret_map
#check checkClause_ret
#check checkClause_time_le
#check checkCNF_ret
#check checkCNF_time_le
#check varsOf_length
#check mem_varsOf
#check sum_length_le_encodeCNF_length
#check satVerifier_time_le
#check satVerifier_verifierInDeclaredPolyTime
#check satVerifier_verifies
#check satDec_mem_NP_of_isPolyTime

example : Cslib.TimeMComplexity.Verifies satVerifier satDec Polynomial.X :=
  satVerifier_verifies

example : Cslib.TimeMComplexity.VerifierInDeclaredPolyTime satVerifier :=
  satVerifier_verifierInDeclaredPolyTime

example
    (h : MetaMathlibExt.ComplexityTheory.IsPolyTime
      fun xw => (satVerifier xw).ret) :
    satDec ∈ MetaMathlibExt.ComplexityTheory.NP :=
  satDec_mem_NP_of_isPolyTime h

example : varsOf [[(0, true), (1, false)], [(1, true)]] = [0, 1, 1] := rfl

example : (lookupVar [2, 2] [true, false] 2).ret = true := rfl
example : (lookupVar [2] [] 2).ret = false := rfl
example : (lookupVar [] [true] 0).ret = false := rfl
example : (lookupVar [1, 2] [false, true] 2).ret = true := rfl
example : (lookupVar [1, 2] [false, true] 3).ret = false := rfl

example : (satVerifier (encodeCNF [[(0, true)]], [true])).ret = true := rfl
example : (satVerifier (encodeCNF [[(0, true)]], [false])).ret = false :=
  rfl

example :
    (satVerifier
      (encodeCNF [[(0, true), (1, false)], [(1, true)]],
        [true, true, true])).ret = true := rfl

example :
    (satVerifier
      (encodeCNF [[(0, true), (1, false)], [(1, true)]],
        [true, false, true])).ret = false := rfl

example : (satVerifier ([], [true])).ret = false := rfl

example (xw : List Bool × List Bool) :
    (satVerifier xw).time ≤
      (Polynomial.X ^ 2 + Polynomial.X).eval
        (xw.1.length + xw.2.length) :=
  satVerifier_time_le xw

example (vars : List Nat) (w : List Bool) (φ : CNF) :
    (checkCNF vars w φ).ret = true ↔
      φ.Satisfies (fun x => (lookupVar vars w x).ret) :=
  checkCNF_ret vars w φ

#print axioms Cslib.CookLevin.satVerifier_verifies
#print axioms Cslib.CookLevin.satDec_mem_NP_of_isPolyTime
