/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LiebAndoTrace
public import MathlibExt.LinearAlgebra.Matrix.TraceRpowConcave
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Lieb's concavity theorem for complex matrices, from Physlib

Lieb's joint concavity of `(A, B) ↦ tr (K* A^q K B^r)` for square complex matrices, transferred
from Physlib's operator version

## i. Overview

Lieb's concavity theorem (E. H. Lieb, *Convex trace functions and the Wigner–Yanase–Dyson
conjecture*, Adv. Math. 11 (1973), 267–288; E. A. Carlen, *Trace inequalities and quantum entropy:
an introductory course*, lecture-notes draft of May 3, 2009, Theorem 6.1) says that for
`q, r ≥ 0` with `q + r ≤ 1` the map `(A, B) ↦ tr (K* A^q K B^r)` is jointly concave on pairs of
positive-definite matrices. Physlib proves it for operators on a finite-dimensional complex Hilbert
space as `LiebAndoTrace.liebExtensionTrace_jointlyConcaveOn_pdSet`, for `q, r > 0`, square `K`, in
the form `tr (A^q K* B^p K)`. This file transfers it to complex matrices through the
`⋆`-algebra isomorphism `Matrix.toEuclideanCLM`, which commutes with the continuous functional
calculus and preserves traces and spectra, and adds the boundary cases `q = 0` and `r = 0` from
`MathlibExt.LinearAlgebra.Matrix.TraceRpowConcave`. Carlen states the theorem for rectangular
`K`; this file proves the square case only.

## ii. Key results

- `lieb_concavity_trace_rpow`: Lieb's joint concavity for square complex matrices.

## iii. Table of contents

- A. Transfer lemmas
- B. Lieb's concavity theorem

## iv. References

- E. H. Lieb, *Convex trace functions and the Wigner–Yanase–Dyson conjecture*, Adv. Math. 11
  (1973), 267–288.
- E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, lecture-notes
  draft of May 3, 2009 (published in Contemp. Math. 529, 2010), Theorem 6.1.

-/

@[expose] public section

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace PhyslibExt.QuantumInfo.LiebConcavity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## A. Transfer lemmas -/

/-- The `⋆`-algebra isomorphism between complex matrices and operators on Euclidean space. -/
local notation "Φ" => (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))

private lemma continuous_toEuclideanCLM : Continuous (Φ : Matrix n n ℂ → _) :=
  LinearMap.continuous_of_finiteDimensional
    (Φ : Matrix n n ℂ ≃⋆ₐ[ℂ] _).toAlgEquiv.toLinearEquiv.toLinearMap

private lemma spectrum_toEuclideanCLM (A : Matrix n n ℂ) : spectrum ℝ (Φ A) = spectrum ℝ A :=
  AlgEquiv.spectrum_eq ((Φ : Matrix n n ℂ ≃⋆ₐ[ℂ] _).toAlgEquiv.restrictScalars ℝ) A

private lemma mem_pdSet_toEuclideanCLM {A : Matrix n n ℂ} (hA : A.PosDef) :
    Φ A ∈ GeneralizedPerspectiveFunction.pdSet (ℋ := EuclideanSpace ℂ n) := by
  refine ⟨?_, ?_⟩
  · exact (IsSelfAdjoint.map Φ hA.isHermitian)
  · intro x hx
    rw [spectrum_toEuclideanCLM] at hx
    exact hA.isStrictlyPositive.spectrum_pos hx

private lemma toEuclideanCLM_cfc_rpow {A : Matrix n n ℂ} (hA : A.PosDef) (q : ℝ) :
    Φ (cfc (· ^ q : ℝ → ℝ) A) = (Φ A) ^ q := by
  have hpos : IsStrictlyPositive (Φ A) := by
    rw [StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R := ℝ) (Φ A)
      (IsSelfAdjoint.map Φ hA.isHermitian)]
    intro x hx
    rw [spectrum_toEuclideanCLM] at hx
    exact hA.isStrictlyPositive.spectrum_pos hx
  rw [CFC.rpow_eq_cfc_real hpos.nonneg]
  refine StarAlgHomClass.map_cfc Φ _ A ?_ continuous_toEuclideanCLM hA.isHermitian
    (IsSelfAdjoint.map Φ hA.isHermitian)
  intro x hx
  have hx0 : 0 < x := hA.isStrictlyPositive.spectrum_pos hx
  exact (Real.continuousAt_rpow_const x q (Or.inl hx0.ne')).continuousWithinAt

private lemma traceRe_toEuclideanCLM (M : Matrix n n ℂ) :
    LiebAndoTrace.traceRe (ℋ := EuclideanSpace ℂ n) (Φ M) = RCLike.re M.trace := by
  unfold LiebAndoTrace.traceRe
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun n ℂ).toBasis,
    LinearMap.toMatrix_toLin]
  rfl

omit [Fintype n] [DecidableEq n] in
/-- Positive-definite matrices form a convex set. -/
private lemma convex_posDef : Convex ℝ {A : Matrix n n ℂ | A.PosDef} := by
  intro A hA B hB a b ha hb hab
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_add] at hab
    simpa [hab] using hB
  · exact (hA.smul (by exact_mod_cast ha')).add_posSemidef
      (hB.posSemidef.smul (by exact_mod_cast hb))

/-- The real-scalar combination commutes with `Φ`. -/
private lemma toEuclideanCLM_combo (a b : ℝ) (X Y : Matrix n n ℂ) :
    Φ (a • X + b • Y) = a • Φ X + b • Φ Y := by
  change ((Φ : Matrix n n ℂ ≃⋆ₐ[ℂ] _).toAlgEquiv.restrictScalars ℝ) (a • X + b • Y) = _
  rw [map_add, map_smul, map_smul]
  rfl

/-- Physlib's trace functional, evaluated on the images of matrices. -/
private lemma liebExtensionTraceMap_toEuclideanCLM [Nontrivial (EuclideanSpace ℂ n)]
    (K : Matrix n n ℂ) {q r : ℝ} {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    LiebAndoTrace.liebExtensionTraceMap (ℋ := EuclideanSpace ℂ n) r q (Φ K) (Φ B) (Φ A) =
      RCLike.re (K.conjTranspose * cfc (· ^ q : ℝ → ℝ) A * K * cfc (· ^ r : ℝ → ℝ) B).trace := by
  unfold LiebAndoTrace.liebExtensionTraceMap
  rw [← toEuclideanCLM_cfc_rpow hB, ← toEuclideanCLM_cfc_rpow hA, ← map_star, ← map_mul, ← map_mul,
    ← map_mul, traceRe_toEuclideanCLM, Matrix.star_eq_conjTranspose]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [Matrix.mul_assoc]

/-! ## B. Lieb's concavity theorem -/

/-- **Lieb's concavity theorem, joint form.** For a square complex matrix `K` and reals
`q, r ≥ 0` with `q + r ≤ 1`, the map `(A, B) ↦ re tr (K* A^q K B^r)` is jointly concave on pairs of
positive-definite matrices, where `A^q = cfc (· ^ q) A` (E. A. Carlen, *Trace inequalities and
quantum entropy: an introductory course*, lecture-notes draft of May 3, 2009, Theorem 6.1, the case
of square `K`; E. H. Lieb, Adv. Math. 11 (1973), 267–288). The trace is real, being the squared
Hilbert–Schmidt norm of `A^{q/2} K B^{r/2}`. For `q, r > 0` the proof transfers Physlib's
`LiebAndoTrace.liebExtensionTrace_jointlyConcaveOn_pdSet` through `Matrix.toEuclideanCLM`; the
cases `q = 0` and `r = 0` are
`MathlibExt.LinearAlgebra.Matrix.TraceRpowConcave.lieb_concavity_trace_rpow_of_left_eq_zero` and
`lieb_concavity_trace_rpow_of_right_eq_zero`. -/
theorem lieb_concavity_trace_rpow (K : Matrix n n ℂ) {q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hqr : q + r ≤ 1) :
    ConcaveOn ℝ {p : Matrix n n ℂ × Matrix n n ℂ | p.1.PosDef ∧ p.2.PosDef}
      (fun p => RCLike.re
        (K.conjTranspose * cfc (· ^ q : ℝ → ℝ) p.1 * K * cfc (· ^ r : ℝ → ℝ) p.2).trace) := by
  rcases hq.eq_or_lt with rfl | hq'
  · exact MathlibExt.LinearAlgebra.Matrix.TraceRpowConcave.lieb_concavity_trace_rpow_of_left_eq_zero
      K hr (by linarith)
  rcases hr.eq_or_lt with rfl | hr'
  · exact
      MathlibExt.LinearAlgebra.Matrix.TraceRpowConcave.lieb_concavity_trace_rpow_of_right_eq_zero
      K hq (by linarith)
  have hconv : Convex ℝ {p : Matrix n n ℂ × Matrix n n ℂ | p.1.PosDef ∧ p.2.PosDef} := by
    intro x hx y hy a b ha hb hab
    exact ⟨convex_posDef hx.1 hy.1 ha hb hab, convex_posDef hx.2 hy.2 ha hb hab⟩
  rcases isEmpty_or_nonempty n with hn | hn
  · refine ⟨hconv, fun x _ y _ a b _ _ hab => ?_⟩
    simp [Matrix.trace, Finset.univ_eq_empty]
  have : Nontrivial (EuclideanSpace ℂ n) := inferInstance
  have hL := LiebAndoTrace.liebExtensionTrace_jointlyConcaveOn_pdSet (ℋ := EuclideanSpace ℂ n)
    (p := q) (q := r) hq' hr' (by linarith) (Φ K)
  refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
  have ha' : a = 1 - b := by linarith
  have key := hL (A₁ := Φ x.2) (A₂ := Φ y.2) (B₁ := Φ x.1) (B₂ := Φ y.1) (θ := b)
    (mem_pdSet_toEuclideanCLM hx.2) (mem_pdSet_toEuclideanCLM hy.2)
    (mem_pdSet_toEuclideanCLM hx.1) (mem_pdSet_toEuclideanCLM hy.1) hb (by linarith)
  have h1 : (a • x.1 + b • y.1).PosDef := convex_posDef hx.1 hy.1 ha hb hab
  have h2 : (a • x.2 + b • y.2).PosDef := convex_posDef hx.2 hy.2 ha hb hab
  rw [← ha', ← toEuclideanCLM_combo, ← toEuclideanCLM_combo,
    liebExtensionTraceMap_toEuclideanCLM K hx.1 hx.2,
    liebExtensionTraceMap_toEuclideanCLM K hy.1 hy.2,
    liebExtensionTraceMap_toEuclideanCLM K h1 h2] at key
  simpa only [smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] using key

end PhyslibExt.QuantumInfo.LiebConcavity
