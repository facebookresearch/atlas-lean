/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Trace.Basic

import Mathlib.FieldTheory.Finite.Trace

/-!
# Trace zero in normal-basis coordinates

## References

- Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
  Journal of Integer Sequences 29 (2026), Article 26.4.6, pp. 1–31, §9.3, Theorem 30
  (the trace criterion for tuple representatives).
- Christophe Reutenauer, *Free Lie Algebras*, London Mathematical Society Monographs,
  New Series 7, Clarendon Press, 1993, §7.6.2 (the normal-basis coordinate map).
-/

namespace MetaMathlibExt

-- Finiteness of the extension is a hypothesis of the trace criterion, not data in its conclusion.
set_option linter.unusedFintypeInType false in
/-- **Zero-sum tuples correspond to trace-zero elements.** Let $K$ be a finite field that is an
algebra over a finite field $F$, let $q = |F|$ and $n = [K : F]$, and let $\beta \in K$ be such
that $\beta, \beta^q, \dots, \beta^{q^{n-1}}$ are linearly independent over $F$. Define
$\Phi : F^n \to K$ by $\Phi(a_0, \dots, a_{n-1}) = \sum_{i=0}^{n-1} a_i \beta^{q^i}$. Then for
every $a = (a_0, \dots, a_{n-1}) \in F^n$, we have $a_0 + a_1 + \dots + a_{n-1} = 0$ if and only if
the trace of $\Phi(a)$ from $K$ to $F$ is $0$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 30
(`jis-2026-26.4.6-thm-30`). -/
public theorem normalBasisMap_sum_eq_zero_iff_trace (F K : Type*)
    [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K] (n : ℕ)
    (hn : Module.finrank F K = n) (β : K)
    (hβ : LinearIndependent F (fun i : Fin n => β ^ (Fintype.card F ^ (i : ℕ))))
    (a : Fin n → F) :
    ∑ i, a i = 0 ↔ Algebra.trace F K (∑ i, a i • β ^ (Fintype.card F ^ (i : ℕ))) = 0 := by
  have htraceβ : Algebra.trace F K β ≠ 0 := by
    intro hzero
    have hsum := FiniteField.algebraMap_trace_eq_sum_pow F K β
    rw [hzero, map_zero, hn, Finset.sum_range, Nat.card_eq_fintype_card] at hsum
    have hone := (linearIndependent_iff'.mp hβ) Finset.univ (fun _ ↦ 1)
      (by simpa only [one_smul] using hsum.symm)
    have hnpos : 0 < n := hn ▸ Module.finrank_pos (R := F) (M := K)
    exact one_ne_zero (hone ⟨0, hnpos⟩ (Finset.mem_univ _))
  have htrace (i : Fin n) :
      Algebra.trace F K (β ^ (Fintype.card F ^ (i : ℕ))) = Algebra.trace F K β := by
    let σ := FiniteField.frobeniusAlgEquivOfAlgebraic F K
    have hpow : (σ ^ (i : ℕ)) β = β ^ (Fintype.card F ^ (i : ℕ)) := by
      rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    rw [← hpow, Algebra.trace_eq_of_algEquiv]
  simp only [map_sum, map_smul, htrace, smul_eq_mul]
  rw [← Finset.sum_mul, mul_eq_zero, or_iff_left htraceβ]

end MetaMathlibExt
