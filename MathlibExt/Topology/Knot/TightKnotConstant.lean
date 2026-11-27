/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The tight knot constant: ropelength versus crossing number
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.EReal.Basic
public import MathlibExt.Topology.Knot.RegularProjection

@[expose] public section

open MathlibExt.Topology.Knot.Euclidean

namespace MathlibExt.Topology.Knot.TightKnot

/-- **Admissible constants for the tight-knot inequality.** A real number $c$ is admissible for
the tight-knot inequality when $c \ge 0$ and, for every $n \in \mathbb{N}$, every parametrized
link $L$ with $n$ components and every $k \in \mathbb{N}$ such that the crossing number of $L$
equals $k$, the ropelength of $L$ is at least $c \, k^{3/4}$, the inequality being read in
$[0, \infty]$. Here the crossing number and the ropelength of $L$ are those of its oriented
labeled ambient-isotopy type.

Link types of infinite crossing number, that is, types none of whose representatives admits a
regular projection, impose no constraint. -/
def IsAdmissible (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ (n : ℕ) (L : ParametrizedLink n) (k : ℕ),
    L.crossingNumber = (k : ℕ∞) →
      ENNReal.ofReal c * ENNReal.ofReal ((k : ℝ) ^ (3 / 4 : ℝ)) ≤
        L.ropelength

/-- **Tight knot constant.** The tight knot constant $C_{22a}$ is the supremum, taken in the
extended reals $[-\infty, \infty]$, of the set of real numbers $c$ that are admissible for the
tight-knot inequality $\mathrm{ropelength} \ge c \cdot (\text{crossing number})^{3/4}$ on link
types. The supremum is not assumed to be attained. -/
noncomputable def tightKnotConstant : EReal :=
  sSup ((fun c : ℝ => (c : EReal)) '' {c : ℝ | IsAdmissible c})

/-- **Zero is an admissible tight-knot constant.** The real number $0$ is admissible for the
tight-knot inequality between the ropelength and the crossing number of link types. -/
theorem isAdmissible_zero : IsAdmissible 0 := by
  refine ⟨le_rfl, fun _ _ _ _ => ?_⟩
  simp

/-- **Admissibility passes to smaller nonnegative constants.** If a real number $c$ is admissible
for the tight-knot inequality and $c'$ is a real number with $0 \le c' \le c$, then $c'$ is
admissible for the tight-knot inequality as well. -/
theorem IsAdmissible.of_le {c c' : ℝ} (hc : IsAdmissible c)
    (h0 : 0 ≤ c') (h : c' ≤ c) : IsAdmissible c' := by
  refine ⟨h0, fun n L k hk => ?_⟩
  calc
    ENNReal.ofReal c' * ENNReal.ofReal ((k : ℝ) ^ (3 / 4 : ℝ))
        ≤ ENNReal.ofReal c * ENNReal.ofReal ((k : ℝ) ^ (3 / 4 : ℝ)) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal h) le_rfl
    _ ≤ L.ropelength := hc.2 n L k hk

/-- **Admissible constants are bounded by the tight knot constant.** Let $C_{22a}$ be the tight
knot constant. Every real number $c$ that is admissible for the tight-knot inequality satisfies
$c \le C_{22a}$ in the extended reals. -/
theorem le_tightKnotConstant {c : ℝ} (hc : IsAdmissible c) :
    (c : EReal) ≤ tightKnotConstant :=
  le_sSup ⟨c, hc, rfl⟩

/-- **The tight knot constant is nonnegative.** The tight knot constant $C_{22a}$ satisfies
$0 \le C_{22a}$ in the extended reals. -/
theorem zero_le_tightKnotConstant : (0 : EReal) ≤ tightKnotConstant := by
  simpa using le_tightKnotConstant isAdmissible_zero

/-- **Upper bounds for the tight knot constant.** For every extended real number $b$, the tight
knot constant $C_{22a}$ satisfies $C_{22a} \le b$ if and only if every real number $c$ that is
admissible for the tight-knot inequality satisfies $c \le b$.

This is the characteristic rule for proving upper bounds on the tight knot constant without
unfolding its definition as a supremum. -/
theorem tightKnotConstant_le_iff {b : EReal} :
    tightKnotConstant ≤ b ↔
      ∀ c : ℝ, IsAdmissible c → (c : EReal) ≤ b := by
  constructor
  · intro hb c hc
    exact (le_tightKnotConstant hc).trans hb
  · intro hb
    apply sSup_le
    rintro x ⟨c, hc, rfl⟩
    exact hb c hc

end MathlibExt.Topology.Knot.TightKnot
