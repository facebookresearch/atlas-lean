/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Descent of rational power series along field extensions

A linear functional detecting a nonzero coefficient of the denominator descends
both polynomials and preserves their product identity with the base-field series.
-/

namespace MetaMathlibExt

/-- **Rationality of power series descends from field extensions.** Let $F$ be a field, let $G$ be
a field extension of $F$ (a field with an $F$-algebra structure), and let $A$ be a power series
over $F$. If there are polynomials $p$, $q$ over $G$ with $q \ne 0$ and $A q = p$, where $A$ is
viewed as a power series over $G$, then there are polynomials $P$, $Q$ over $F$ with $Q \ne 0$ and
$A Q = P$.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 1 (`jis-2024-24.1.3-thm-1`). -/
public theorem exists_polynomial_quotient_of_extension {F G : Type*} [Field F] [Field G]
    [Algebra F G] (A : PowerSeries F) (p q : Polynomial G) (hq : q ≠ 0)
    (h : PowerSeries.map (algebraMap F G) A * (q : PowerSeries G) = p) :
    ∃ P Q : Polynomial F, Q ≠ 0 ∧ A * (Q : PowerSeries F) = P := by
  have hlead : q.coeff q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero F hlead
  let descend (r : Polynomial G) : Polynomial F := AddMonoidAlgebra.map φ.toAddMonoidHom r
  have coeff_descend (r : Polynomial G) (n : ℕ) : (descend r).coeff n = φ (r.coeff n) := by
    simp [descend]
  refine ⟨descend p, descend q, ?_, ?_⟩
  · intro heq
    apply hφ
    rw [← coeff_descend, heq, Polynomial.coeff_zero]
  · apply PowerSeries.ext
    intro n
    -- The coefficients of `A` act by base-field scalar multiplication.
    simpa only [PowerSeries.coeff_mul, Polynomial.coeff_coe, PowerSeries.coeff_map,
      ← Algebra.smul_def, map_sum, map_smul, smul_eq_mul, coeff_descend] using
      congrArg (fun s : PowerSeries G ↦ φ (PowerSeries.coeff n s)) h

end MetaMathlibExt
