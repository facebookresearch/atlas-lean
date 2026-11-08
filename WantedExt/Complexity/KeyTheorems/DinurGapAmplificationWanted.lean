/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dinur's gap amplification: the combinatorial PCP theorem

Source:
I. Dinur, "The PCP theorem by gap amplification", Journal of the ACM 54 (2007), 12:1-12:44
(Proceedings of the Thirty-Eighth Annual ACM Symposium on Theory of Computing, STOC 2006,
241-250).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.DinurGapAmplification

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Dinur's gap amplification: the combinatorial PCP theorem

Dinur's proof of the PCP theorem proceeds by *gap amplification* for 2CSPs (binary
constraint satisfaction problems): a polynomial-time transformation that keeps the variable
set, blows up the number of constraints by a constant factor, and amplifies the
unsatisfiability gap by a constant factor `c > 0`. Iterating amplification (with alphabet
reduction) turns the trivial gap of 3SAT into a constant gap, giving the PCP theorem; this
file states the gap-amplification lemma itself, as a separate entry from the PCP theorem
file. A 2CSP instance is `(variable count, alphabet size, constraints)`, a constraint
being `(u, v, allowed pairs)`; its value under an assignment `Fin I.1 → Fin I.2.1` is
the fraction of satisfied constraints (`1` on the empty instance). Instances are
required to be well-formed: every constraint mentions variables below the variable
count and allowed pairs of labels below the alphabet size. Gap amplification must
genuinely amplify: the factor `c` is strictly greater than `1`, the amplified gap is
capped at a fixed constant `α < 1`, well-formedness is preserved, the alphabet grows
to at most `Σ ^ e` for a constant exponent `e` (graph powering replaces labels by
local views), and the degree of every variable grows by at most a constant factor `D`
(so the identity transformation, which has `c = 1`, is excluded). Alphabet
reduction is parameterized by the amplifier's own base alphabet `S0` and exponent
`e`: it accepts exactly the amplifier's output alphabet bound `S0 ^ e` (when
starting from base alphabet `S0`) and returns alphabet `S0`, with nondegenerate
bounds `2 ≤ S0` and `2 ≤ e` so `S0 ^ e > S0` and the reduction must genuinely
shrink the alphabet. The theorem shares one set of constants across both steps and
states the composed step explicitly: `Tred ∘ Tamp` maps base-alphabet instances to
base-alphabet instances with gap `δ ↦ min α' (c' * min α (c * δ))`.
-/

/-- A 2CSP instance: variable count, alphabet size, and the list of binary constraints. -/
abbrev CSPInstance := ℕ × ℕ × List (ℕ × ℕ × List (ℕ × ℕ))

/-- A 2CSP instance is well-formed: every constraint mentions variables below the
variable count, and every allowed pair has labels below the alphabet size. -/
def CSPWellFormed (I : CSPInstance) : Prop :=
  ∀ c ∈ I.2.2, c.1 < I.1 ∧ c.2.1 < I.1 ∧
    ∀ p ∈ c.2.2, p.1 < I.2.1 ∧ p.2 < I.2.1

/-- A constraint is satisfied by an assignment: its variable indices are in range
and the assigned label pair is allowed. -/
def cspConstraintSat (I : CSPInstance) (assign : Fin I.1 → Fin I.2.1)
    (c : ℕ × ℕ × List (ℕ × ℕ)) : Prop :=
  ∃ hu : c.1 < I.1, ∃ hv : c.2.1 < I.1,
    ((assign ⟨c.1, hu⟩).val, (assign ⟨c.2.1, hv⟩).val) ∈ c.2.2

open Classical in
/-- The value of a 2CSP instance under an assignment: the fraction of satisfied constraints. -/
noncomputable def cspVal (I : CSPInstance) (assign : Fin I.1 → Fin I.2.1) : ℚ :=
  if I.2.2 = [] then 1
  else ((I.2.2.filter (fun c => decide (cspConstraintSat I assign c))).length : ℚ) /
    (I.2.2.length : ℚ)

/-- The degree of a variable in a 2CSP instance: the number of constraints mentioning it. -/
def cspDegree (I : CSPInstance) (v : ℕ) : ℕ :=
  (I.2.2.filter (fun c => c.1 = v ∨ c.2.1 = v)).length

/-- Gap amplification with explicit constants `c α d D e`: a transformation keeping
the variables, preserving well-formedness, with constant constraint blowup and
constant-factor degree blowup, alphabet size at most `Sigma ^ e` for the exponent `e`
(the local-view alphabet of graph powering), preserving satisfiability and
amplifying every gap `δ` by a constant factor `c > 1`, capped at a fixed constant
`α < 1`. The constants are parameters (not existentially quantified inside) so
that the theorem below can share them with alphabet reduction. -/
def gapAmplification (c α : ℚ) (d D e : ℕ) (T : CSPInstance → CSPInstance) : Prop :=
  1 < c ∧ 0 < α ∧ α < 1 ∧ 1 ≤ d ∧ 1 ≤ D ∧
    ∀ I : CSPInstance, (T I).1 = I.1 ∧ (T I).2.1 ≤ I.2.1 ^ e ∧
      (CSPWellFormed I → CSPWellFormed (T I)) ∧
      (T I).2.2.length ≤ d * I.2.2.length ∧
      (∀ v, cspDegree (T I) v ≤ D * (cspDegree I v + 1)) ∧
      ((∃ assign, cspVal I assign = 1) → ∃ assign, cspVal (T I) assign = 1) ∧
      ∀ (δ : ℚ), 0 < δ → δ ≤ 1 →
        (∀ assign, cspVal I assign ≤ 1 - δ) →
          ∀ assign, cspVal (T I) assign ≤ 1 - min α (c * δ)

/-- Alphabet reduction with explicit constants, parameterized by the amplifier's
base alphabet `S0` and exponent `e`: a transformation applying to instances whose
alphabet is at most `S0 ^ e` (exactly the amplifier's output bound when starting
from base alphabet `S0`), reducing the alphabet back to `S0`, preserving
satisfiability and losing at most a constant factor `c' ≤ 1` in the gap (gap `δ`
becomes at least `min (c' * δ, α')`). The variable set may expand by a constant
factor: each old variable is replaced by at most `V` new variables (the reduction
adorns variables with auxiliary code symbols), so `(T I).1 ≤ V * (I.1 + 1)`, and the
constraint count grows by at most a constant factor. The nondegenerate bounds
`2 ≤ S0` and `2 ≤ e` are essential: with `S0 = 0` the premise would cover only
zero-alphabet instances and `T = id` would vacuously satisfy the statement, and
with `e = 1` the reduction would not need to shrink the alphabet at all; with
`2 ≤ S0` and `2 ≤ e` we have `S0 ^ e > S0`, so the reduction must genuinely shrink
the alphabet. The constants are parameters (not existentially quantified inside) so
that the theorem below shares `S0` and `e` with gap amplification. -/
def alphabetReduction (S0 e : ℕ) (c' α' : ℚ) (d' V : ℕ)
    (T : CSPInstance → CSPInstance) : Prop :=
  2 ≤ S0 ∧ 2 ≤ e ∧ 0 < c' ∧ c' ≤ 1 ∧ 0 < α' ∧ α' < 1 ∧ 1 ≤ d' ∧ 1 ≤ V ∧
    ∀ I : CSPInstance, I.2.1 ≤ S0 ^ e →
      (T I).1 ≤ V * (I.1 + 1) ∧ (T I).2.1 ≤ S0 ∧
      (CSPWellFormed I → CSPWellFormed (T I)) ∧
      (T I).2.2.length ≤ d' * I.2.2.length ∧
      ((∃ assign, cspVal I assign = 1) → ∃ assign, cspVal (T I) assign = 1) ∧
      ∀ (δ : ℚ), 0 < δ → δ ≤ 1 →
        (∀ assign, cspVal I assign ≤ 1 - δ) →
          ∀ assign, cspVal (T I) assign ≤ 1 - min α' (c' * δ)

/-- **Dinur's gap amplification: the combinatorial PCP theorem.** Source: I. Dinur, "The
PCP theorem by gap amplification", Journal of the ACM 54 (2007), 12:1-12:44 (Proceedings
of the Thirty-Eighth Annual ACM Symposium on Theory of Computing, STOC 2006, 241-250). -/
public theorem_wanted dinur_gap_amplification :
    ∃ (S0 e : ℕ) (c α c' α' : ℚ) (d D d' V : ℕ),
      2 ≤ S0 ∧ 2 ≤ e ∧ 1 < c ∧ 0 < α ∧ α < 1 ∧ 1 ≤ d ∧ 1 ≤ D ∧
      0 < c' ∧ c' ≤ 1 ∧ 0 < α' ∧ α' < 1 ∧ 1 ≤ d' ∧ 1 ≤ V ∧
      ∃ (Tamp Tred : CSPInstance → CSPInstance) (famp fred : List Bool → List Bool),
        IsPolyTime famp ∧ IsPolyTime fred ∧
        (∀ I : CSPInstance,
          MetaMathlibExt.BitstringEncoding.bitDecode (famp
            (MetaMathlibExt.BitstringEncoding.bitEncode I)) = some (Tamp I)) ∧
        (∀ I : CSPInstance,
          MetaMathlibExt.BitstringEncoding.bitDecode (fred
            (MetaMathlibExt.BitstringEncoding.bitEncode I)) = some (Tred I)) ∧
        gapAmplification c α d D e Tamp ∧
        alphabetReduction S0 e c' α' d' V Tred ∧
        ∀ I : CSPInstance, I.2.1 ≤ S0 →
          (Tred (Tamp I)).2.1 ≤ S0 ∧
          (CSPWellFormed I → CSPWellFormed (Tred (Tamp I))) ∧
          ((∃ assign, cspVal I assign = 1) → ∃ assign, cspVal (Tred (Tamp I)) assign = 1) ∧
          ∀ (δ : ℚ), 0 < δ → δ ≤ 1 →
            (∀ assign, cspVal I assign ≤ 1 - δ) →
              ∀ assign, cspVal (Tred (Tamp I)) assign ≤
                1 - min α' (c' * min α (c * δ))

end MetaMathlibExt.Complexity.KeyTheorems.DinurGapAmplification
