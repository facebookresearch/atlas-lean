/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Etale.TraceForm

@[expose] public section

-- The product algebra `Fin 2 → ℚ` is étale, so its trace form is nondegenerate
-- (Theorem 5.20, forward direction via the iff).
example : (Algebra.traceForm ℚ (Fin 2 → ℚ)).Nondegenerate :=
  Algebra.traceForm_nondegenerate_iff_etale.mpr inferInstance

-- Conversely, nondegeneracy of the trace form forces étaleness.
example (h : (Algebra.traceForm ℚ (Fin 2 → ℚ)).Nondegenerate) :
    Algebra.Etale ℚ (Fin 2 → ℚ) :=
  Algebra.traceForm_nondegenerate_iff_etale.mp h

-- Every basis of the étale algebra `Fin 2 → ℚ` has nonzero discriminant
-- (Lemma 12.18, étale direction).
example (b : Module.Basis (Fin 2) ℚ (Fin 2 → ℚ)) :
    Algebra.discr ℚ b ≠ 0 :=
  Algebra.discr_ne_zero_of_etale b inferInstance

-- A nonzero discriminant for some basis forces the algebra to be étale
-- (Lemma 12.18, discriminant direction).
example (b : Module.Basis (Fin 2) ℚ (Fin 2 → ℚ)) (h : Algebra.discr ℚ b ≠ 0) :
    Algebra.Etale ℚ (Fin 2 → ℚ) :=
  Algebra.etale_of_discr_ne_zero b h

-- Nondegeneracy of the trace form forces the algebra to be reduced.
example : IsReduced (Fin 2 → ℚ) :=
  Algebra.isReduced_of_traceForm_nondegenerate
    (show (Algebra.traceForm ℚ (Fin 2 → ℚ)).Nondegenerate from
      Algebra.traceForm_nondegenerate_iff_etale.mpr inferInstance)

-- The trace on a finite product is the sum of the traces.
example : Algebra.trace ℚ (Fin 2 → ℚ) (fun _ => 1) = 2 := by
  rw [Algebra.trace_pi]
  simp

-- The trace form on a finite product is the sum of the trace forms.
example : Algebra.traceForm ℚ (Fin 2 → ℚ) (fun _ => 1) (fun _ => 1) = 2 := by
  rw [Algebra.traceForm_pi]
  simp [Algebra.traceForm_apply]
