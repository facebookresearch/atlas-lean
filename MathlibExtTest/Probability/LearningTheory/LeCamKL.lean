/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.LeCamKL

import MathlibExt.Probability.ProbabilityMassFunction.Uniform

instance : MeasurableSpace (Fin 2) := ⊤
instance : MeasurableSingletonClass (Fin 2) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Boundary check: the KL form of Le Cam's bound instantiates on
a two-point type. -/
example (p q : PMF (Fin 2)) (δ : Fin 2 → Bool)
    (hsupp : ∀ a, (q a) = 0 → (p a) = 0) :
    1 - Real.sqrt ((InformationTheory.klDiv p.toMeasure q.toMeasure).toReal / 2) ≤
      (∑ a ∈ Finset.univ.filter (fun a => δ a = true), (p a).toReal) +
        (∑ a ∈ Finset.univ.filter (fun a => δ a = false), (q a).toReal) :=
  lecam_kl p q δ hsupp

/-- Concrete check: for `p = q` a point mass, the KL divergence
is `0`, and the boundary atom `a = 1` has `q 1 = p 1 = 0`. -/
example :
    (InformationTheory.klDiv (PMF.pure (0 : Fin 2)).toMeasure
      (PMF.pure (0 : Fin 2)).toMeasure).toReal = 0 ∧
    (PMF.pure (0 : Fin 2)) (1 : Fin 2) = 0 := by
  refine ⟨?_, by simp [PMF.pure_apply]⟩
  rw [InformationTheory.toReal_klDiv_toMeasure (fun a h => h)]
  simp [PMF.pure_apply]

/-- Concrete check: point mass against uniform input has KL
divergence `log 2`, and Le Cam's bound then simplifies to
`1 - √(log 2 / 2) ≤ 1`. -/
example :
    (InformationTheory.klDiv (PMF.pure (0 : Fin 2)).toMeasure
      (PMF.uniformFintype (Fin 2)).toMeasure).toReal = Real.log 2 ∧
    1 - Real.sqrt (Real.log 2 / 2) ≤ 1 := by
  have hsupp : ∀ a, (PMF.uniformFintype (Fin 2)) a = 0 →
      (PMF.pure (0 : Fin 2)) a = 0 := by
    intro a h
    simp [PMF.uniformFintype_apply] at h
  have hkl : (InformationTheory.klDiv (PMF.pure (0 : Fin 2)).toMeasure
      (PMF.uniformFintype (Fin 2)).toMeasure).toReal = Real.log 2 := by
    rw [InformationTheory.toReal_klDiv_toMeasure hsupp]
    simp [Fin.sum_univ_two, PMF.pure_apply, PMF.uniformFintype_apply]
  refine ⟨hkl, ?_⟩
  have h := lecam_kl (PMF.pure (0 : Fin 2)) (PMF.uniformFintype (Fin 2))
    (fun _ => true) hsupp
  rw [hkl] at h
  have hsums : (∑ a ∈ Finset.univ.filter (fun a : Fin 2 => true = true),
      ((PMF.pure (0 : Fin 2)) a).toReal) +
      (∑ a ∈ Finset.univ.filter (fun a : Fin 2 => true = false),
        ((PMF.uniformFintype (Fin 2)) a).toReal) = 1 := by
    simp [Fin.sum_univ_two, PMF.pure_apply]
  rw [hsums] at h
  exact h
