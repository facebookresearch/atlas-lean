/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The tight alternating knot constant: ropelength versus crossing number
-/
module

public import Mathlib.Data.EReal.Basic
public import MathlibExt.Topology.Knot.RegularProjection

@[expose] public section

open MathlibExt.Topology.Knot.Euclidean

namespace MathlibExt.Topology.Knot.TightAlternatingKnot

/-- **Admissible constants for the tight alternating knot inequality.**
A real number $c$ is admissible when $c \ge 0$ and, for every $n$ and
every oriented labeled link type with $n$ components that admits an
alternating diagram and whose crossing number is a natural number $k$,
the ropelength of the type is at least $c k$.

The restriction to finite crossing number excludes no such type: the
alternating representative is itself a regular projection, so every
link type admitting an alternating diagram has finite crossing
number. -/
def IsAdmissibleAlternating (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ (n : ℕ) (L : ParametrizedLink n),
    L.AdmitsAlternatingDiagram → ∀ k : ℕ,
      L.crossingNumber = (k : ℕ∞) →
        ENNReal.ofReal c * (k : ENNReal) ≤ L.ropelength

/-- **Tight alternating knot constant.** The tight alternating knot
constant $C_{22b} = b_0$ is the supremum, taken in the extended reals,
of the set of real numbers $c$ admissible for the tight alternating
knot inequality: those $c \ge 0$ such that every link type $K$ that
admits an alternating diagram and has finite crossing number
$\mathrm{Cr}(K)$ has ropelength $\mathrm{L}(K) \ge c\,\mathrm{Cr}(K)$.
The supremum is not assumed to be attained. -/
noncomputable def tightAlternatingKnotConstant : EReal :=
  sSup ((fun c : ℝ => (c : EReal)) '' {c : ℝ | IsAdmissibleAlternating c})

/-- **Zero is an admissible alternating constant.** The constant
$c = 0$ is admissible for the tight alternating knot inequality. -/
theorem isAdmissibleAlternating_zero : IsAdmissibleAlternating 0 := by
  refine ⟨le_rfl, fun _ _ _ _ _ => ?_⟩
  simp

/-- **Admissible alternating constants are downward closed among
nonnegative reals.** If a real number $c$ is admissible for the tight
alternating knot inequality and $c'$ is a real number with
$0 \le c' \le c$, then $c'$ is admissible as well. -/
theorem IsAdmissibleAlternating.of_le {c c' : ℝ}
    (hc : IsAdmissibleAlternating c) (h0 : 0 ≤ c') (h : c' ≤ c) :
    IsAdmissibleAlternating c' := by
  refine ⟨h0, fun n L hL k hk => ?_⟩
  calc
    ENNReal.ofReal c' * (k : ENNReal)
        ≤ ENNReal.ofReal c * (k : ENNReal) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal h) le_rfl
    _ ≤ L.ropelength := hc.2 n L hL k hk

/-- **Admissible constants are at most the tight alternating knot
constant.** Every real number $c$ that is admissible for the tight
alternating knot inequality is at most the tight alternating knot
constant. -/
theorem le_tightAlternatingKnotConstant {c : ℝ}
    (hc : IsAdmissibleAlternating c) :
    (c : EReal) ≤ tightAlternatingKnotConstant :=
  le_sSup ⟨c, hc, rfl⟩

/-- **The tight alternating knot constant is nonnegative.** The tight
alternating knot constant, an extended real number, is at least $0$. -/
theorem zero_le_tightAlternatingKnotConstant :
    (0 : EReal) ≤ tightAlternatingKnotConstant := by
  simpa using le_tightAlternatingKnotConstant isAdmissibleAlternating_zero

/-- **Upper bounds for the tight alternating knot constant.** For every
extended real number $b$, the tight alternating knot constant is at
most $b$ if and only if every real number $c$ that is admissible for
the tight alternating knot inequality satisfies $c \le b$. -/
theorem tightAlternatingKnotConstant_le_iff {b : EReal} :
    tightAlternatingKnotConstant ≤ b ↔
      ∀ c : ℝ, IsAdmissibleAlternating c → (c : EReal) ≤ b := by
  constructor
  · intro hb c hc
    exact (le_tightAlternatingKnotConstant hc).trans hb
  · intro hb
    apply sSup_le
    rintro x ⟨c, hc, rfl⟩
    exact hb c hc

/-- **Alternating link types have finite crossing number.** If an
oriented labeled link type with $n$ components admits an alternating
diagram, then its crossing number is finite: the alternating
representative is itself a regular projection. -/
theorem crossingNumber_lt_top_of_admitsAlternatingDiagram {n : ℕ}
    {L : ParametrizedLink n} (hL : L.AdmitsAlternatingDiagram) :
    L.crossingNumber < ⊤ := by
  obtain ⟨L', h', hreg, -⟩ := hL
  exact L.crossingNumber_lt_top_of_isotopic_of_isRegularProjection h' hreg

/-- **Alternating link types have a natural-number crossing number.**
If an oriented labeled link type with $n$ components admits an
alternating diagram, then its crossing number equals some natural
number $k$. -/
theorem exists_crossingNumber_eq_natCast_of_admitsAlternatingDiagram
    {n : ℕ} {L : ParametrizedLink n}
    (hL : L.AdmitsAlternatingDiagram) :
    ∃ k : ℕ, L.crossingNumber = (k : ℕ∞) := by
  have hlt := crossingNumber_lt_top_of_admitsAlternatingDiagram hL
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hlt.ne
  exact ⟨k, hk.symm⟩

end MathlibExt.Topology.Knot.TightAlternatingKnot
