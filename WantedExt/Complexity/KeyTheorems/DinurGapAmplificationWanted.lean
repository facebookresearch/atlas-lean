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

/-- **2CSP instances.** A 2CSP instance is a triple $(n, \Sigma, C)$ of a natural number $n$ (the
number of variables), a natural number $\Sigma$ (the alphabet size) and a finite list $C$ of
constraints, where each constraint is a triple $(u, v, P)$ of natural numbers $u$ and $v$ (the
variables it mentions) and a finite list $P$ of pairs of natural numbers (the allowed label
pairs). -/
abbrev CSPInstance := ℕ × ℕ × List (ℕ × ℕ × List (ℕ × ℕ))

/-- **Well-formed 2CSP instances.** A 2CSP instance $(n, \Sigma, C)$ is well-formed when every
constraint $(u, v, P)$ in $C$ satisfies $u < n$ and $v < n$, and every allowed pair $(a, b)$ in
$P$ satisfies $a < \Sigma$ and $b < \Sigma$. -/
def CSPWellFormed (I : CSPInstance) : Prop :=
  ∀ c ∈ I.2.2, c.1 < I.1 ∧ c.2.1 < I.1 ∧
    ∀ p ∈ c.2.2, p.1 < I.2.1 ∧ p.2 < I.2.1

/-- **Satisfied constraint of a 2CSP instance.** Let $I = (n, \Sigma, C)$ be a 2CSP instance and
$\sigma$ an assignment of a label less than $\Sigma$ to each variable less than $n$. A constraint
$(u, v, P)$ is satisfied by $\sigma$ when $u < n$, $v < n$ and the pair $(\sigma(u), \sigma(v))$
belongs to $P$. -/
def cspConstraintSat (I : CSPInstance) (assign : Fin I.1 → Fin I.2.1)
    (c : ℕ × ℕ × List (ℕ × ℕ)) : Prop :=
  ∃ hu : c.1 < I.1, ∃ hv : c.2.1 < I.1,
    ((assign ⟨c.1, hu⟩).val, (assign ⟨c.2.1, hv⟩).val) ∈ c.2.2

open Classical in
/-- **Value of a 2CSP instance under an assignment.** Let $I = (n, \Sigma, C)$ be a 2CSP
instance and $\sigma$ an assignment of a label less than $\Sigma$ to each variable less than $n$.
The value of $I$ under $\sigma$ is the rational number $1$ if $C$ is empty, and otherwise the
number of entries of the list $C$ that are constraints satisfied by $\sigma$, divided by the
length of $C$. -/
noncomputable def cspVal (I : CSPInstance) (assign : Fin I.1 → Fin I.2.1) : ℚ :=
  if I.2.2 = [] then 1
  else ((I.2.2.filter (fun c => decide (cspConstraintSat I assign c))).length : ℚ) /
    (I.2.2.length : ℚ)

/-- **Degree of a variable in a 2CSP instance.** For a 2CSP instance $(n, \Sigma, C)$ and a
natural number $v$, the degree of $v$ is the number of entries $(u, w, P)$ of the list $C$ with
$u = v$ or $w = v$. -/
def cspDegree (I : CSPInstance) (v : ℕ) : ℕ :=
  (I.2.2.filter (fun c => c.1 = v ∨ c.2.1 = v)).length

/-- **Gap amplification with given constants.** Let $c, \alpha$ be rationals and $d, D, e$ natural
numbers. A map $T$ from 2CSP instances to 2CSP instances is a gap amplification with constants
$c, \alpha, d, D, e$ when $c > 1$, $0 < \alpha < 1$, $d \ge 1$, $D \ge 1$, and for every 2CSP
instance $I$ with $n$ variables, alphabet size $\Sigma$ and $m$ constraints: $T(I)$ has exactly $n$
variables, alphabet size at most $\Sigma^e$ and at most $d m$ constraints; if $I$ is well-formed
then so is $T(I)$; for every natural number $v$, if $v$ has degree $k$ in $I$, then $v$ has degree
at most $D(k + 1)$ in $T(I)$; if some assignment gives $I$ value $1$ then some assignment
gives $T(I)$ value $1$; and for every rational $\delta$ with $0 < \delta \le 1$, if every assignment
gives $I$ value at most $1 - \delta$, then every assignment gives $T(I)$ value at most
$1 - \min(\alpha, c\delta)$. -/
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

/-- **Alphabet reduction with given constants.** Let $S_0, e, d', V$ be natural numbers and
$c', \alpha'$ rationals. A map $T$ from 2CSP instances to 2CSP instances is an alphabet reduction
with constants $S_0, e, c', \alpha', d', V$ when $S_0 \ge 2$, $e \ge 2$, $0 < c' \le 1$,
$0 < \alpha' < 1$, $d' \ge 1$, $V \ge 1$, and for every 2CSP instance $I$ with $n$ variables,
alphabet size at most $S_0^e$ and $m$ constraints: $T(I)$ has at most $V(n + 1)$ variables,
alphabet size at most $S_0$ and at most $d' m$ constraints; if $I$ is well-formed then so is
$T(I)$; if some assignment gives $I$ value $1$ then some assignment gives $T(I)$ value $1$; and
for every rational $\delta$ with $0 < \delta \le 1$, if every assignment gives $I$ value at most
$1 - \delta$, then every assignment gives $T(I)$ value at most $1 - \min(\alpha', c'\delta)$.

The bounds $S_0 \ge 2$ and $e \ge 2$ give $S_0^e > S_0$, so the reduction must genuinely shrink
the alphabet. -/
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

/-- **Dinur's gap amplification and alphabet reduction.** There exist natural numbers
$S_0, e, d, D, d', V$ and rationals $c, \alpha, c', \alpha'$ with $S_0 \ge 2$, $e \ge 2$, $c > 1$,
$0 < \alpha < 1$, $d \ge 1$, $D \ge 1$, $0 < c' \le 1$, $0 < \alpha' < 1$, $d' \ge 1$ and $V \ge 1$,
and maps $A$ and $R$ from 2CSP instances to 2CSP instances, with the following properties.
Both maps are polynomial-time computable: for each $T \in \{A, R\}$ there is a polynomial-time
computable function $f$ from lists of booleans to lists of booleans such that, for every 2CSP
instance $I$, decoding $f$ applied to the bitstring encoding of $I$ succeeds and returns $T(I)$.
The map $A$ is a gap amplification with constants $c, \alpha, d, D, e$, and $R$ is an alphabet
reduction with constants $S_0, e, c', \alpha', d', V$. Finally, for every 2CSP instance $I$ with
alphabet size at most $S_0$, the instance $J = R(A(I))$ has alphabet size at most $S_0$; if $I$
is well-formed then so is $J$; if some assignment gives $I$ value $1$ then some assignment gives
$J$ value $1$; and for every rational $\delta$ with $0 < \delta \le 1$, if every assignment gives
$I$ value at most $1 - \delta$, then every assignment gives $J$ value at most
$1 - \min(\alpha', c' \min(\alpha, c\delta))$.

The constants $c$ and $c'$ are not tied together: the statement does not assert $c' c > 1$, so
the composed map $R \circ A$ need not enlarge the gap.

Source: I. Dinur, "The
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
