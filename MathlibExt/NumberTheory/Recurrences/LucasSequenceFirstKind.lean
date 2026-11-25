/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Basic

@[expose] public section

namespace MetaMathlibExt

/-!
# Lucas sequence of the first kind

Source-faithful recurrence predicate for the Lucas sequence of the first
kind with integer parameters.

Provenance:
- stable record: `jis_grounded_7e37bcd48e7477bda602ca6e`
- frozen source: `https://cs.uwaterloo.ca/journals/JIS/VOL13/Smyth/smyth2.tex`
- file SHA-256: `eb765815f14b18e047ccd51b0ed4ec17305d9410f60516b290425a6cd7a49d05`
- exact UTF-8 bytes 3175-3840, lines 114-122
- span SHA-256: `dce48c9908ba3e56bb82b2792cbb734d489dc1558763f1c1284855dc2de7ea4f`

The source fixes integers `P Q` and imposes `u 0 = 0`, `u 1 = 1`, and
`u (n + 2) = P * u (n + 1) - Q * u n` for every `n`. It discusses Binet
formulas separately, so this predicate records the recurrence directly.
-/

/--
**Lucas sequence of the first kind.** For integers $P$ and $Q$, a sequence of integers
$(u_n)_{n \ge 0}$ is the Lucas sequence of the first kind with parameters $P$ and $Q$ when
$u_0 = 0$, $u_1 = 1$, and $u_{n+2} = P u_{n+1} - Q u_n$ for every natural number $n$.

Source: stable record `jis_grounded_7e37bcd48e7477bda602ca6e`,
`https://cs.uwaterloo.ca/journals/JIS/VOL13/Smyth/smyth2.tex`,
lines 114-122.
-/
public def IsLucasSequenceFirstKind (P Q : ℤ) (u : ℕ → ℤ) : Prop :=
  u 0 = 0 ∧ u 1 = 1 ∧ ∀ n : ℕ, u (n + 2) = P * u (n + 1) - Q * u n

/-- **Lucas sequence of the first kind: value at zero.** If $(u_n)_{n \ge 0}$ is the Lucas sequence
of the first kind with integer parameters $P$ and $Q$, then $u_0 = 0$. -/
public theorem IsLucasSequenceFirstKind.initialZero {P Q : ℤ} {u : ℕ → ℤ}
    (h : IsLucasSequenceFirstKind P Q u) : u 0 = 0 :=
  h.1

/-- **Lucas sequence of the first kind: value at one.** If $(u_n)_{n \ge 0}$ is the Lucas sequence
of the first kind with integer parameters $P$ and $Q$, then $u_1 = 1$. -/
public theorem IsLucasSequenceFirstKind.initialOne {P Q : ℤ} {u : ℕ → ℤ}
    (h : IsLucasSequenceFirstKind P Q u) : u 1 = 1 :=
  h.2.1

/-- **Lucas sequence of the first kind: the recurrence.** If $(u_n)_{n \ge 0}$ is the Lucas
sequence of the first kind with integer parameters $P$ and $Q$, then
$u_{n+2} = P u_{n+1} - Q u_n$ for every natural number $n$. -/
public theorem IsLucasSequenceFirstKind.recurrenceStep {P Q : ℤ} {u : ℕ → ℤ}
    (h : IsLucasSequenceFirstKind P Q u) (n : ℕ) :
    u (n + 2) = P * u (n + 1) - Q * u n :=
  h.2.2 n

end MetaMathlibExt
