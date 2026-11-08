/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Mahaney's theorem: sparse NP-complete sets imply P = NP

Source:
S. R. Mahaney, "Sparse complete sets for NP: solution of a conjecture of Berman and Hartmanis",
Journal of Computer and System Sciences 25 (1982), 130-143.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Mahaney

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Mahaney's theorem: sparse NP-complete sets imply P = NP

If there exists a sparse `NP`-complete language, then `P = NP`. Sparse means the number of
accepted strings of length at most `n` is bounded by a polynomial in `n`. `NP`-completeness is
canonical `NP` membership plus polynomial-time many-one hardness
(`Cslib.CookLevin.PolyManyOneRed`).
-/


/-- A sparse language: at most polynomially many accepted strings up to each length. -/
def Sparse (L : MetaMathlibExt.ComplexityTheory.DecisionProblem) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n,
    Set.Finite {x : List Bool | x.length ≤ n ∧ L x = true} ∧
    Set.ncard {x : List Bool | x.length ≤ n ∧ L x = true} ≤ p.eval n

/-- `NP`-completeness in the canonical sense. -/
def NPComplete (L : MetaMathlibExt.ComplexityTheory.DecisionProblem) : Prop :=
  L ∈ MetaMathlibExt.ComplexityTheory.NP ∧
    ∀ L' : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L' ∈ MetaMathlibExt.ComplexityTheory.NP →
      Cslib.CookLevin.PolyManyOneRed L' L

/-- **Mahaney's theorem: sparse NP-complete sets imply P = NP.** Source: S. R. Mahaney,
"Sparse complete sets for NP: solution of a conjecture of Berman and Hartmanis", Journal
of Computer and System Sciences 25 (1982), 130-143. -/
public theorem_wanted mahaney :
    (∃ L : MetaMathlibExt.ComplexityTheory.DecisionProblem, Sparse L ∧ NPComplete L) →
      MetaMathlibExt.ComplexityTheory.P = MetaMathlibExt.ComplexityTheory.NP

end MetaMathlibExt.Complexity.KeyTheorems.Mahaney
