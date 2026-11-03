/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovSemigroupProjective

import Mathlib.Data.Fin.VecNotation

/-!
# Compile checks for canonical Markov-semigroup laws

These checks pin the public construction used by the neutral Wright--Fisher
realization: finite laws are built from kernels, projectivity is proved, and
the resulting path measure is a genuine probability measure.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace MathlibExtTest.Probability.MarkovSemigroupProjective

#check MathlibExt.Probability.MarkovSemigroupProjective.finiteChainKernel
#check MathlibExt.Probability.MarkovSemigroupProjective.finiteLaw
#check MathlibExt.Probability.MarkovSemigroupProjective.isProjectiveMeasureFamily_finiteLaw
#check MathlibExt.Probability.MarkovSemigroupProjective.exists_projectiveLimit

#print axioms MathlibExt.Probability.MarkovSemigroupProjective.isProjectiveMeasureFamily_finiteLaw
#print axioms MathlibExt.Probability.MarkovSemigroupProjective.exists_projectiveLimit

section PublicSignatures

open MathlibExt.Probability.MarkovSemigroupProjective

variable {E : Type*} [MeasurableSpace E]

noncomputable example :
    (K : NNReal → Kernel E E) → (s : NNReal) →
      {n : ℕ} → (Fin n → NNReal) → Kernel E (Fin n → E) :=
  fun K s => finiteChainKernel K s

noncomputable example :
    (K : NNReal → Kernel E E) → E →
      (J : Finset NNReal) → Measure (J → E) :=
  finiteLaw

example (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (hKadd : ∀ s t, K (s + t) = K t ∘ₖ K s) (x : E) :
    IsProjectiveMeasureFamily (α := fun _ : NNReal => E)
      (finiteLaw K x) :=
  isProjectiveMeasureFamily_finiteLaw K hKadd x

variable [TopologicalSpace E] [PolishSpace E] [BorelSpace E]

example (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (hKadd : ∀ s t, K (s + t) = K t ∘ₖ K s) (x : E) :
    ∃ P : Measure (NNReal → E), IsProjectiveLimit P (finiteLaw K x) :=
  exists_projectiveLimit K hKadd x

end PublicSignatures

open MathlibExt.Probability.MarkovSemigroupProjective

private theorem map_zero_finiteChainLaw
    {E : Type*} [MeasurableSpace E]
    (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (x : E) (s t : NNReal) :
    (finiteChainLaw K x s (fun _ : Fin 1 => t)).map (fun z => z 0) =
      K (t - s) x := by
  rw [finiteChainLaw, finiteChainKernel]
  rw [Kernel.map_apply _
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 1 => E) 0).symm.measurable]
  rw [Measure.map_map (by fun_prop)
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin 1 => E) 0).symm.measurable]
  have hcomp :
      (fun z : Fin 1 → E => z 0) ∘
          (MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin 1 => E) 0).symm = Prod.fst := by
    funext z
    rfl
  rw [hcomp]
  change Kernel.fst
    (K (t - s) ⊗ₖ Kernel.prodMkLeft E
      (finiteChainKernel K t fun i => Fin.elim0 i)) x = _
  rw [Kernel.fst_compProd]

namespace IdentityKernel

open MathlibExt.Probability.MarkovSemigroupProjective

noncomputable def kernel (_ : NNReal) : Kernel ℝ ℝ := Kernel.id

instance kernel.instIsMarkovKernel (t : NNReal) :
    IsMarkovKernel (kernel t) := by
  unfold kernel
  infer_instance

theorem kernel_add (s t : NNReal) :
    kernel (s + t) = kernel t ∘ₖ kernel s := by
  simp [kernel]

example (t : NNReal) : IsMarkovKernel (kernel t) := by
  infer_instance

example (s : NNReal) {n : ℕ} (t : Fin n → NNReal) :
    IsMarkovKernel (finiteChainKernel kernel s t) := by
  infer_instance

example (x : ℝ) (J : Finset NNReal) :
    IsProbabilityMeasure (finiteLaw kernel x J) := by
  infer_instance

example (x : ℝ) :
    IsProbabilityMeasure (finiteLaw kernel x ∅) := by
  infer_instance

example : IsProbabilityMeasure
    (pathMeasure kernel kernel_add (0 : ℝ)) := by
  infer_instance

/-- The concrete one-point ordered law is its single transition marginal. -/
example (x : ℝ) (s t : NNReal) :
    (finiteChainLaw kernel x s ![t]).map (fun z => z 0) =
      kernel (t - s) x := by
  unfold finiteChainLaw
  rw [finiteChainKernel]
  rw [Kernel.map_apply _
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 1 => ℝ) 0).symm.measurable]
  rw [Measure.map_map (by fun_prop)
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin 1 => ℝ) 0).symm.measurable]
  have hcomp :
      (fun z : Fin 1 → ℝ => z 0) ∘
          (MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin 1 => ℝ) 0).symm = Prod.fst := by
    funext z
    rfl
  rw [hcomp]
  change Kernel.fst
    (kernel (t - s) ⊗ₖ Kernel.prodMkLeft ℝ
      (finiteChainKernel kernel t fun i => Fin.elim0 i)) x = _
  rw [Kernel.fst_compProd]

/-- A concrete path measure exists and has the proved ordered finite law. -/
example :
    (pathMeasure kernel kernel_add (0 : ℝ)).map
        (fun ω i => ω (({0, 1} : Finset NNReal).orderEmbOfFin rfl i)) =
      finiteChainLaw kernel (0 : ℝ) 0
        (({0, 1} : Finset NNReal).orderEmbOfFin rfl) :=
  map_ordered_pathMeasure kernel kernel_add (0 : ℝ) {0, 1}

end IdentityKernel

namespace TranslationKernel

open MathlibExt.Probability.MarkovSemigroupProjective

/-- Deterministic translation by elapsed time. -/
noncomputable def kernel (t : NNReal) : Kernel ℝ ℝ :=
  Kernel.deterministic (fun x => x + (t : ℝ)) (by fun_prop)

instance kernel.instIsMarkovKernel (t : NNReal) :
    IsMarkovKernel (kernel t) := by
  unfold kernel
  infer_instance

theorem kernel_add (s t : NNReal) :
    kernel (s + t) = kernel t ∘ₖ kernel s := by
  unfold kernel
  rw [Kernel.deterministic_comp_deterministic]
  apply Kernel.deterministic_congr
  funext x
  simp only [Function.comp_apply, NNReal.coe_add]
  ring

/-- The second requested coordinate uses both adjacent gaps: `1` then `2`. -/
example (x : ℝ) :
    (finiteChainLaw kernel x 0 ![(1 : NNReal), (3 : NNReal)]).map
        (fun z => z 1) = Measure.dirac (x + 3) := by
  let t : Fin 2 → NNReal := ![1, 3]
  have ht : StrictMono t := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    norm_num [t]
  have hdel := finiteChainKernel_map_eraseCoordinate
    kernel kernel_add t bot_le ht (0 : Fin 2)
  have hdelMeasure :
      (finiteChainLaw kernel x 0 t).map (eraseCoordinate (E := ℝ) 0) =
        finiteChainLaw kernel x 0 (fun i => t ((0 : Fin 2).succAbove i)) := by
    unfold finiteChainLaw
    rw [← Kernel.map_apply _ (measurable_eraseCoordinate (E := ℝ) 0)]
    exact congrArg (fun L : Kernel ℝ (Fin 1 → ℝ) => L x) hdel
  change (finiteChainLaw kernel x 0 t).map (fun z => z 1) = _
  calc
    (finiteChainLaw kernel x 0 t).map (fun z => z 1) =
        ((finiteChainLaw kernel x 0 t).map
          (eraseCoordinate (E := ℝ) 0)).map (fun z => z 0) := by
      rw [Measure.map_map (by fun_prop)
        (measurable_eraseCoordinate (E := ℝ) 0)]
      rfl
    _ = (finiteChainLaw kernel x 0
          (fun i => t ((0 : Fin 2).succAbove i))).map (fun z => z 0) := by
      rw [hdelMeasure]
    _ = kernel 3 x := by
      simpa [t] using map_zero_finiteChainLaw kernel x 0 3
    _ = Measure.dirac (x + 3) := by
      rw [kernel, Kernel.deterministic_apply]
      norm_num

end TranslationKernel

end MathlibExtTest.Probability.MarkovSemigroupProjective
