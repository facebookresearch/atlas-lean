/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.Basic
public import CSLibExt.MachineLearning.Sequence.ForwardBackward
public import CSLibExt.MachineLearning.Sequence.HiddenMarkovMeasure
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring

/-!
# Filtering and one-step prediction for normalized hidden Markov models

For a normalized hidden Markov model, `obsKernel` is the observation
kernel of a hidden path and `filterPosterior` is Mathlib's posterior
kernel for that path given the observed word. The predictive version
`prefixObsKernel` observes only the prefix of a one-step-longer hidden
path, and `predictivePosterior` is its posterior kernel.

The main theorem, `posterior_prediction_match`, assumes positive
evidence at the observed word. It identifies the forward-backward
smoothing weights with no future data with the filtering posterior
path masses, and one-step prediction with the predictive posterior
path masses. Zero initial, transition, and emission cells are allowed.
-/

@[expose] public section

namespace Cslib.MachineLearning.Sequence.HiddenMarkovFilter

open Cslib.MachineLearning.Sequence.HiddenMarkov
open Cslib.MachineLearning.Sequence.HiddenMarkovLaw
open Cslib.MachineLearning.Sequence.HiddenMarkovMeasure
open ProbabilityTheory
open MeasureTheory (IsProbabilityMeasure)

/-- The observation kernel of a normalized HMM at horizon `t`: a hidden path `z` of length
`t + 1` emits the observation word `x 0, …, x t` with law `obsPMF h hN t z`. -/
noncomputable def obsKernel {S O : Type*} [Fintype S] [Fintype O]
    [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace O]
    (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ) :
    Kernel (Fin (t + 1) → S) (Fin (t + 1) → O) :=
  Kernel.ofFunOfCountable fun z => (obsPMF h hN t z).toMeasure

instance {S O : Type*} [Fintype S] [Fintype O]
    [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace O]
    (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ) : IsMarkovKernel (obsKernel h hN t) :=
  ⟨fun z => by change IsProbabilityMeasure (obsPMF h hN t z).toMeasure; infer_instance⟩

/-- The observation kernel for one-step prediction: a hidden path of length `t + 2` emits only
the observed prefix `x 0, …, x t`; the unobserved emission at time `t + 1` is marginalized out
of `obsPMF h hN (t + 1) z`. -/
noncomputable def prefixObsKernel {S O : Type*} [Fintype S] [Fintype O]
    [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace O]
    (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ) :
    Kernel (Fin (t + 2) → S) (Fin (t + 1) → O) :=
  Kernel.ofFunOfCountable fun z => ((obsPMF h hN (t + 1) z).map Fin.init).toMeasure

instance {S O : Type*} [Fintype S] [Fintype O]
    [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace O]
    (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ) : IsMarkovKernel (prefixObsKernel h hN t) :=
  ⟨fun z => by
    change IsProbabilityMeasure ((obsPMF h hN (t + 1) z).map Fin.init).toMeasure
    infer_instance⟩

/-- The filtering posterior: Mathlib's posterior kernel of the hidden path of length `t + 1`
given the observations `x 0, …, x t`, under the path prior `pathPMF` and `obsKernel`. -/
noncomputable def filterPosterior {S O : Type*} [Fintype S] [Fintype O] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace O]
    (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ) :
    Kernel (Fin (t + 1) → O) (Fin (t + 1) → S) :=
  (obsKernel h hN t)†(pathPMF h hN t).toMeasure

/-- The one-step predictive posterior: Mathlib's posterior kernel of the hidden path of length
`t + 2` given only the observations `x 0, …, x t`. -/
noncomputable def predictivePosterior {S O : Type*} [Fintype S] [Fintype O] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace O]
    (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ) :
    Kernel (Fin (t + 1) → O) (Fin (t + 2) → S) :=
  (prefixObsKernel h hN t)†(pathPMF h hN (t + 1)).toMeasure

/-- One-step prediction: the filtering weights at time `t` (`smoothed` with no future data)
pushed through one transition, `∑ s, smoothed x g t 0 s * trans s s'`. -/
def prediction {S O K : Type*} [Fintype S] [Semifield K]
    (x : ℕ → O) (g : HMM S O K) (t : ℕ) (s' : S) : K :=
  ∑ s, smoothed x g t 0 s * g.trans s s'

/-- The path prior and `obsKernel` compose to the HMM joint law `jointPMF`. -/
theorem compProd_obsKernel {S O : Type*} [Fintype S] [Fintype O]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace O] [MeasurableSingletonClass O]
    (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ) :
    (pathPMF h hN t).toMeasure ⊗ₘ obsKernel h hN t = (jointPMF h hN t).toMeasure := by
  ext s hs
  rw [MeasureTheory.Measure.compProd_apply hs]
  rw [jointPMF, PMF.toMeasure_bind_apply _ _ _ hs]
  rw [MeasureTheory.lintegral_countable']
  congr 1
  ext z
  rw [PMF.toMeasure_map_apply _ _ _ measurable_prodMk_left hs]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z)]
  rw [mul_comm ((obsKernel h hN t) z _)]
  rfl

private theorem compProd_prodMk {α β : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] [MeasurableSpace β]
    (μ : MeasureTheory.Measure α) [MeasureTheory.SFinite μ]
    (κ : ProbabilityTheory.Kernel α β) [ProbabilityTheory.IsSFiniteKernel κ]
    (a : α) (t : Set β) (ht : MeasurableSet t) :
    (μ ⊗ₘ κ) ({a} ×ˢ t) = μ {a} * κ a t := by
  classical
  rw [MeasureTheory.Measure.compProd_apply ((MeasurableSet.singleton a).prod ht)]
  have hInt : (fun a' => κ a' (Prod.mk a' ⁻¹' ({a} ×ˢ t)))
      = fun a' => if a' = a then κ a t else 0 := by
    funext a'
    by_cases ha : a' = a
    · simp [ha]
    · have hEmpty : Prod.mk a' ⁻¹' ({a} ×ˢ t) = ∅ := by
        ext b
        simp [ha]
      rw [hEmpty]
      simp [ha]
  rw [hInt, MeasureTheory.lintegral_countable']
  rw [tsum_eq_single a (fun a' ha' => by simp [ha'])]
  have hIf : (if a = a then κ a t else 0) = κ a t := by simp
  rw [hIf]
  exact mul_comm _ _

theorem compProd_prefixObsKernel {S O : Type*} [Fintype S] [Fintype O]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace O] [MeasurableSingletonClass O]
    (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ) :
    (pathPMF h hN (t + 1)).toMeasure ⊗ₘ prefixObsKernel h hN t =
      ((jointPMF h hN (t + 1)).map fun zx => (zx.1, Fin.init zx.2)).toMeasure := by
  classical
  have hmap : ((jointPMF h hN (t + 1)).map fun zx => (zx.1, Fin.init zx.2)).toMeasure
      = MeasureTheory.Measure.map (fun zx => (zx.1, Fin.init zx.2))
        (jointPMF h hN (t + 1)).toMeasure :=
    (PMF.toMeasure_map _ _ (measurable_of_countable _)).symm
  rw [hmap, ← compProd_obsKernel h hN (t + 1), MeasureTheory.Measure.ext_iff_singleton]
  rintro ⟨z, x⟩
  have hLHS : ((pathPMF h hN (t + 1)).toMeasure ⊗ₘ prefixObsKernel h hN t) {(z, x)}
      = (pathPMF h hN (t + 1)).toMeasure {z}
        * ((obsPMF h hN (t + 1) z).map Fin.init).toMeasure {x} := by
    rw [← Set.singleton_prod_singleton,
      compProd_prodMk _ _ _ _ (MeasurableSet.singleton x)]
    rfl
  have hFinMeas : MeasurableSet
      ((Fin.init : (Fin (t + 1 + 1) → O) → (Fin (t + 1) → O)) ⁻¹' {x}) :=
    (measurable_of_countable _) (MeasurableSet.singleton x)
  have hRHS : MeasureTheory.Measure.map (fun zx => (zx.1, Fin.init zx.2))
        ((pathPMF h hN (t + 1)).toMeasure ⊗ₘ obsKernel h hN (t + 1)) {(z, x)}
      = (pathPMF h hN (t + 1)).toMeasure {z}
        * ((obsPMF h hN (t + 1) z).map Fin.init).toMeasure {x} := by
    rw [MeasureTheory.Measure.map_apply (measurable_of_countable _) (MeasurableSet.singleton _)]
    have hpre : (fun zx => (zx.1, (Fin.init : (Fin (t + 1 + 1) → O) → (Fin (t + 1) → O)) zx.2)) ⁻¹'
          {(z, x)}
        = {z} ×ˢ ((Fin.init : (Fin (t + 1 + 1) → O) → (Fin (t + 1) → O)) ⁻¹' {x}) := by
      ext ⟨z', x'⟩
      simp
    rw [hpre, compProd_prodMk _ _ _ _ hFinMeas]
    congr 1
    change (obsPMF h hN (t + 1) z).toMeasure (Fin.init ⁻¹' {x}) = _
    rw [← PMF.toMeasure_map _ _ (measurable_of_countable _),
      MeasureTheory.Measure.map_apply (measurable_of_countable _) (MeasurableSet.singleton _)]
  exact hLHS.trans hRHS.symm

private theorem init_snoc_eq {α : Type*} (t : ℕ) (w : Fin (t + 1) → α) (s' : α) :
    Fin.init (Fin.snoc (α := fun _ => α) w s') = w :=
  Fin.init_snoc _ _
private theorem snoc_last_eq {α : Type*} (t : ℕ) (w : Fin (t + 1) → α) (s' : α) :
    Fin.snoc (α := fun _ => α) w s' (Fin.last (t + 1)) = s' :=
  Fin.snoc_last _ _
private theorem snoc_init_self_eq {α : Type*} (t : ℕ) (z : Fin (t + 2) → α) :
    Fin.snoc (α := fun _ => α) (Fin.init z) (z (Fin.last (t + 1))) = z :=
  Fin.snoc_init_self _
private theorem map_init_apply {O : Type*} [Finite O] (t : ℕ)
    (q : PMF (Fin (t + 2) → O)) (x : Fin (t + 1) → O) :
    (PMF.map Fin.init q) x = ∑' o : O, q (Fin.snoc x o) := by
  classical
  haveI := Fintype.ofFinite O
  simp only [PMF.map_apply]
  rw [tsum_fintype, tsum_fintype]
  have hfilter : (∑ y : Fin (t + 2) → O, @ite ENNReal (x = Fin.init y)
        (Classical.propDecidable (x = Fin.init y)) (q y) 0) =
      ∑ y ∈ @Finset.filter (Fin (t + 2) → O) (fun y => x = Fin.init y)
        (fun y => Classical.propDecidable (x = Fin.init y)) Finset.univ, q y := by
    rw [Finset.sum_filter]
  rw [hfilter]
  have hbij : (∑ y ∈ @Finset.filter (Fin (t + 2) → O) (fun y => x = Fin.init y)
        (fun y => Classical.propDecidable (x = Fin.init y)) Finset.univ, q y) =
      ∑ o : O, q (Fin.snoc x o) := by
    refine Finset.sum_bij (fun y _ => y (Fin.last (t + 1))) ?_ ?_ ?_ ?_
    · intro y _
      exact Finset.mem_univ _
    · intro y1 hy1 y2 hy2 h
      have h' : y1 (Fin.last (t + 1)) = y2 (Fin.last (t + 1)) := h
      have m1 : Fin.init y1 = x :=
        ((@Finset.mem_filter _ (fun y : Fin (t + 2) → O => x = Fin.init y)
          (fun y => Classical.propDecidable (x = Fin.init y)) _ _).mp hy1).2.symm
      have m2 : Fin.init y2 = x :=
        ((@Finset.mem_filter _ (fun y : Fin (t + 2) → O => x = Fin.init y)
          (fun y => Classical.propDecidable (x = Fin.init y)) _ _).mp hy2).2.symm
      have e1 : Fin.snoc (Fin.init y1) (y1 (Fin.last (t + 1))) = y1 :=
        snoc_init_self_eq t y1
      have e2 : Fin.snoc (Fin.init y2) (y2 (Fin.last (t + 1))) = y2 :=
        snoc_init_self_eq t y2
      rw [← e1, ← e2, m1, m2, h']
    · intro o _
      refine ⟨Fin.snoc x o, (@Finset.mem_filter _ (fun y : Fin (t + 2) → O => x = Fin.init y)
        (fun y => Classical.propDecidable (x = Fin.init y)) _ _).mpr
        ⟨Finset.mem_univ _, (init_snoc_eq t x o).symm⟩, ?_⟩
      exact snoc_last_eq t x o
    · intro y hy
      show q y = q (Fin.snoc x (y (Fin.last (t + 1))))
      have m : Fin.init y = x :=
        ((@Finset.mem_filter _ (fun y : Fin (t + 2) → O => x = Fin.init y)
          (fun y => Classical.propDecidable (x = Fin.init y)) _ _).mp hy).2.symm
      have e : Fin.snoc (Fin.init y) (y (Fin.last (t + 1))) = y :=
        snoc_init_self_eq t y
      rw [← m, e]
  rw [hbij]
private theorem sum_snoc_eq {S : Type*} [Fintype S]
    (t : ℕ) (G : (Fin (t + 1) → S) → S → ℝ) :
    (∑ z : Fin (t + 2) → S, G (Fin.init z) (z (Fin.last (t + 1)))) =
      ∑ w : Fin (t + 1) → S, ∑ s' : S, G w s' := by
  have h1 : (∑ z : Fin (t + 2) → S, G (Fin.init z) (z (Fin.last (t + 1)))) =
      ∑ p : (Fin (t + 1) → S) × S, G p.1 p.2 := by
    refine Finset.sum_bij (fun z _ => ((Fin.init z), z (Fin.last (t + 1)))) ?_ ?_ ?_ ?_
    · intro z _
      exact Finset.mem_univ _
    · intro z1 _ z2 _ h
      have h1 : Fin.init z1 = Fin.init z2 := congrArg Prod.fst h
      have h2 : z1 (Fin.last (t + 1)) = z2 (Fin.last (t + 1)) := congrArg Prod.snd h
      have e1 : Fin.snoc (Fin.init z1) (z1 (Fin.last (t + 1))) = z1 :=
        snoc_init_self_eq t z1
      have e2 : Fin.snoc (Fin.init z2) (z2 (Fin.last (t + 1))) = z2 :=
        snoc_init_self_eq t z2
      rw [← e1, ← e2, h1, h2]
    · intro p _
      refine ⟨Fin.snoc (α := fun _ => S) p.1 p.2, Finset.mem_univ _, ?_⟩
      show (Fin.init (Fin.snoc (α := fun _ => S) p.1 p.2),
        (Fin.snoc (α := fun _ => S) p.1 p.2) (Fin.last (t + 1))) = p
      rw [init_snoc_eq t p.1 p.2, snoc_last_eq t p.1 p.2]
    · intro z _
      change G (Fin.init z) (z (Fin.last (t + 1))) = G (Fin.init z) (z (Fin.last (t + 1)))
      rfl
  rw [h1]
  exact Fintype.sum_prod_type (fun p => G p.1 p.2)
private theorem sum_filter_snoc_eq {S : Type*} [Fintype S] [DecidableEq S]
    (t : ℕ) (G : (Fin (t + 1) → S) → S → ℝ) (s' : S) :
    (∑ z ∈ Finset.univ.filter (fun z : Fin (t + 2) → S => z (Fin.last (t + 1)) = s'),
      G (Fin.init z) (z (Fin.last (t + 1)))) =
      ∑ w : Fin (t + 1) → S, G w s' := by
  refine Finset.sum_bij (fun z _ => Fin.init z) ?_ ?_ ?_ ?_
  · intro z _
    exact Finset.mem_univ _
  · intro z1 hz1 z2 hz2 h
    have h' : Fin.init z1 = Fin.init z2 := h
    have m1 : z1 (Fin.last (t + 1)) = s' := (Finset.mem_filter.mp hz1).2
    have m2 : z2 (Fin.last (t + 1)) = s' := (Finset.mem_filter.mp hz2).2
    have e1 : Fin.snoc (Fin.init z1) (z1 (Fin.last (t + 1))) = z1 :=
      snoc_init_self_eq t z1
    have e2 : Fin.snoc (Fin.init z2) (z2 (Fin.last (t + 1))) = z2 :=
      snoc_init_self_eq t z2
    rw [← e1, ← e2, h', m1, m2]
  · intro w _
    refine ⟨Fin.snoc w s', Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, snoc_last_eq t w s'⟩, ?_⟩
    exact init_snoc_eq t w s'
  · intro z hz
    have m : z (Fin.last (t + 1)) = s' := (Finset.mem_filter.mp hz).2
    change G (Fin.init z) (z (Fin.last (t + 1))) = G (Fin.init z) s'
    rw [m]
private theorem sum_fiberwise_eq {S : Type*} [Fintype S] [DecidableEq S]
    (t : ℕ) (F : (Fin (t + 1) → S) → S → ℝ) :
    (∑ s : S, ∑ w ∈ Finset.univ.filter (fun w : Fin (t + 1) → S => w (Fin.last t) = s), F w s) =
      ∑ w : Fin (t + 1) → S, F w (w (Fin.last t)) := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun w _ => by
    rw [Finset.sum_ite_eq]
    exact ite_eq_left (Finset.mem_univ _))

/-- The upstream path weight is nonnegative for normalized parameters. -/
private theorem pathWeight_nonneg {S O : Type*} [Fintype S] [Fintype O]
    (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ) (z : Fin (t + 1) → S) :
    0 ≤ pathWeight h t z := by
  simp only [pathWeight]
  exact mul_nonneg (hN.init_nonneg _)
    (Finset.prod_nonneg (fun i _ => hN.trans_nonneg _ _))

/-- The upstream observation weight is nonnegative for normalized parameters. -/
private theorem obsWeight_nonneg {S O : Type*} [Fintype S] [Fintype O]
    (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ) (z : Fin (t + 1) → S)
    (y : Fin (t + 1) → O) : 0 ≤ obsWeight h t z y := by
  simp only [obsWeight]
  exact Finset.prod_nonneg (fun i _ => hN.emit_nonneg _ _)

/-- `pathWeight` recurrence under `snoc`. -/
private theorem pathWeight_snoc {S O : Type*}
    (h : HMM S O ℝ) (t : ℕ) (z : Fin (t + 1) → S) (s : S) :
    pathWeight h (t + 1) (Fin.snoc z s) =
      pathWeight h t z * h.trans (z (Fin.last t)) s := by
  have hs : ∀ i : Fin t, (i.castSucc).succ = (i.succ).castSucc := fun _ => rfl
  have hl : (Fin.last t).succ = Fin.last (t + 1) := rfl
  have h0 : (Fin.snoc (α := fun _ => S) z s) 0 = z 0 := by simp
  simp only [pathWeight]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, h0, hs, hl]
  ring

/-- `obsWeight` recurrence under `snoc`. -/
private theorem obsWeight_snoc {S O : Type*}
    (h : HMM S O ℝ) (t : ℕ) (z : Fin (t + 1) → S) (y : Fin (t + 1) → O)
    (s : S) (o : O) :
    obsWeight h (t + 1) (Fin.snoc z s) (Fin.snoc y o) =
      obsWeight h t z y * h.emit s o := by
  simp only [obsWeight]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- `pathWeight` at `t + 1`, split at the prefix `Fin.init z`. -/
private theorem pathWeight_succ_init {S O : Type*}
    (h : HMM S O ℝ) (t : ℕ) (z : Fin (t + 2) → S) :
    pathWeight h (t + 1) z =
      pathWeight h t (Fin.init z) *
        h.trans (z (Fin.last t).castSucc) (z (Fin.last (t + 1))) := by
  have hz : z = Fin.snoc (Fin.init z) (z (Fin.last (t + 1))) :=
    (snoc_init_self_eq t z).symm
  have hlast : (Fin.init z) (Fin.last t) = z (Fin.last t).castSucc := rfl
  conv_lhs => rw [hz, pathWeight_snoc, hlast]

/-- The product of the path and observation weights is the path probability. -/
private theorem pathWeight_mul_obsWeight {S O : Type*} [Finite S] [Finite O]
    (h : HMM S O ℝ) (t : ℕ) (z : Fin (t + 1) → S) (y : Fin (t + 1) → O) :
    pathWeight h t z * obsWeight h t z y =
      pathProb h (extend t y) t z := by
  haveI := Fintype.ofFinite S
  haveI := Fintype.ofFinite O
  rw [← jointProb_factor h t z y]
  rfl

/-- **Filter and prediction correspondence.** At an observed word `x 0, …, x t` of positive
evidence, the forward-backward weights with no future data (`smoothed … t 0`) are the
posterior probabilities that the hidden state at time `t` is `s`, summed from the posterior
singleton masses of the paths, and `prediction` is the posterior probability that the hidden
state at time `t + 1` is `s'` given the same observations. Zero transition, emission and
initial weights are allowed. -/
theorem posterior_prediction_match {S O : Type*} [Fintype S] [Fintype O] [DecidableEq S]
    [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace O] [MeasurableSingletonClass O]
    (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ) (x : Fin (t + 1) → O)
    (hx : 0 < likelihood h (extend t x) t) :
    (∀ s : S, smoothed (extend t x) h t 0 s =
      ∑ z ∈ Finset.univ.filter (fun z : Fin (t + 1) → S => z (Fin.last t) = s),
        (filterPosterior h hN t x {z}).toReal) ∧
    (∀ s' : S, prediction (extend t x) h t s' =
      ∑ z ∈ Finset.univ.filter (fun z : Fin (t + 2) → S => z (Fin.last (t + 1)) = s'),
        (predictivePosterior h hN t x {z}).toReal) := by
  have key : ∀ z : Fin (t + 1) → S,
      (pathPMF h hN t).toMeasure {z} * obsKernel h hN t z {x} =
        ENNReal.ofReal (pathProb h (extend t x) t z) := by
    intro z
    have hμ : (pathPMF h hN t).toMeasure {z} = (pathPMF h hN t) z :=
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
    have hκ : obsKernel h hN t z {x} = (obsPMF h hN t z).toMeasure {x} := rfl
    have ho : (obsPMF h hN t z).toMeasure {x} = (obsPMF h hN t z) x :=
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
    rw [hμ, hκ, ho,
      pathPMF_apply h hN t z,
      obsPMF_apply h hN t z x,
      ← ENNReal.ofReal_mul (pathWeight_nonneg h hN t z),
      pathWeight_mul_obsWeight h t z x]
  have hD : (∑' z' : Fin (t + 1) → S,
        (pathPMF h hN t).toMeasure {z'} * obsKernel h hN t z' {x}) =
      ENNReal.ofReal (likelihood h (extend t x) t) := by
    rw [tsum_congr key, tsum_fintype,
      ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (fun z _ => HiddenMarkovLaw.pathProb_nonneg_extend S O h hN t x z)]
    simp only [likelihood]
  have hcomp : ((obsKernel h hN t) ∘ₘ (pathPMF h hN t).toMeasure) {x} =
      ENNReal.ofReal (likelihood h (extend t x) t) := by
    have h1 : ((obsKernel h hN t) ∘ₘ (pathPMF h hN t).toMeasure) {x} =
        ∫⁻ z, obsKernel h hN t z {x} ∂(pathPMF h hN t).toMeasure :=
      MeasureTheory.Measure.bind_apply (measurableSet_singleton x)
        (Kernel.aemeasurable (obsKernel h hN t))
    rw [h1, MeasureTheory.lintegral_countable']
    exact (tsum_congr fun z => mul_comm _ _).trans hD
  have hx' : ((obsKernel h hN t) ∘ₘ (pathPMF h hN t).toMeasure) {x} ≠ 0 := by
    rw [hcomp]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hx)
  have hpost : ∀ z : Fin (t + 1) → S,
      filterPosterior h hN t x {z} = ENNReal.ofReal (pathProb h (extend t x) t z) /
        ENNReal.ofReal (likelihood h (extend t x) t) := by
    intro z
    have h1 := Cslib.MachineLearning.Bayesian.posterior_apply_singleton
      (obsKernel h hN t) (pathPMF h hN t).toMeasure hx' z
    simp only [filterPosterior]
    rw [h1, key z, hD]
  have hpostR : ∀ z : Fin (t + 1) → S, (filterPosterior h hN t x {z}).toReal =
      pathProb h (extend t x) t z / likelihood h (extend t x) t := by
    intro z
    rw [hpost z]
    simp only [ENNReal.toReal_div,
      ENNReal.toReal_ofReal (HiddenMarkovLaw.pathProb_nonneg_extend S O h hN t x z),
      ENNReal.toReal_ofReal hx.le]
  have key2 : ∀ z : Fin (t + 2) → S,
      (pathPMF h hN (t + 1)).toMeasure {z} * prefixObsKernel h hN t z {x} =
        ENNReal.ofReal (pathProb h (extend t x) t (Fin.init z) *
          h.trans ((Fin.init z) (Fin.last t)) (z (Fin.last (t + 1)))) := by
    intro z
    have hμ : (pathPMF h hN (t + 1)).toMeasure {z} = (pathPMF h hN (t + 1)) z :=
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
    have hκ : prefixObsKernel h hN t z {x} =
        ((obsPMF h hN (t + 1) z).map Fin.init).toMeasure {x} := rfl
    have hmap : ((obsPMF h hN (t + 1) z).map Fin.init).toMeasure {x} =
        (obsPMF h hN (t + 1) z).map Fin.init x :=
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
    rw [hμ, hκ, hmap, map_init_apply t (obsPMF h hN (t + 1) z) x]
    have hQ : ∀ o : O, (obsPMF h hN (t + 1) z) (Fin.snoc x o) =
        ENNReal.ofReal (obsWeight h t (Fin.init z) x *
          h.emit (z (Fin.last (t + 1))) o) := by
      intro o
      rw [obsPMF_apply h hN (t + 1) z (Fin.snoc x o)]
      have hz : z = Fin.snoc (Fin.init z) (z (Fin.last (t + 1))) :=
        (snoc_init_self_eq t z).symm
      conv_lhs => rw [hz, obsWeight_snoc]
    rw [tsum_congr hQ, tsum_fintype,
      ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (fun o _ => mul_nonneg
        (obsWeight_nonneg h hN t (Fin.init z) x) (hN.emit_nonneg _ _))]
    rw [← Finset.mul_sum, hN.emit_sum (z (Fin.last (t + 1))), mul_one,
      pathPMF_apply h hN (t + 1) z]
    rw [← ENNReal.ofReal_mul (pathWeight_nonneg h hN (t + 1) z)]
    have hring : pathWeight h (t + 1) z *
          obsWeight h t (Fin.init z) x =
        (pathWeight h t (Fin.init z) *
            obsWeight h t (Fin.init z) x) *
          h.trans (z (Fin.last t).castSucc) (z (Fin.last (t + 1))) := by
      rw [pathWeight_succ_init]
      ring
    rw [hring, pathWeight_mul_obsWeight h t (Fin.init z) x]
    have hinit : Fin.init z (Fin.last t) = z (Fin.last t).castSucc := rfl
    rw [hinit]
  have hD' : (∑' z : Fin (t + 2) → S,
        (pathPMF h hN (t + 1)).toMeasure {z} * prefixObsKernel h hN t z {x}) =
      ENNReal.ofReal (likelihood h (extend t x) t) := by
    rw [tsum_congr key2, tsum_fintype,
      ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (fun z _ => mul_nonneg
        (HiddenMarkovLaw.pathProb_nonneg_extend S O h hN t x (Fin.init z))
        (hN.trans_nonneg _ _))]
    have hre : (∑ z : Fin (t + 2) → S, pathProb h (extend t x) t (Fin.init z) *
        h.trans ((Fin.init z) (Fin.last t)) (z (Fin.last (t + 1)))) =
        likelihood h (extend t x) t := by
      rw [sum_snoc_eq t
        (fun w s' => pathProb h (extend t x) t w * h.trans (w (Fin.last t)) s')]
      have hper : ∀ w : Fin (t + 1) → S,
          (∑ s' : S, pathProb h (extend t x) t w * h.trans (w (Fin.last t)) s') =
            pathProb h (extend t x) t w := by
        intro w
        rw [← Finset.mul_sum, hN.trans_sum (w (Fin.last t)), mul_one]
      have hcongr : (∑ w : Fin (t + 1) → S, ∑ s' : S,
          pathProb h (extend t x) t w * h.trans (w (Fin.last t)) s') =
          ∑ w : Fin (t + 1) → S, pathProb h (extend t x) t w :=
        Finset.sum_congr rfl (fun w _ => hper w)
      rw [hcongr]
      simp only [likelihood]
    rw [hre]
  have hcomp' : ((prefixObsKernel h hN t) ∘ₘ (pathPMF h hN (t + 1)).toMeasure) {x} =
      ENNReal.ofReal (likelihood h (extend t x) t) := by
    have h1 : ((prefixObsKernel h hN t) ∘ₘ (pathPMF h hN (t + 1)).toMeasure) {x} =
        ∫⁻ z, prefixObsKernel h hN t z {x} ∂(pathPMF h hN (t + 1)).toMeasure :=
      MeasureTheory.Measure.bind_apply (measurableSet_singleton x)
        (Kernel.aemeasurable (prefixObsKernel h hN t))
    rw [h1, MeasureTheory.lintegral_countable']
    exact (tsum_congr fun z => mul_comm _ _).trans hD'
  have hx'' : ((prefixObsKernel h hN t) ∘ₘ (pathPMF h hN (t + 1)).toMeasure) {x} ≠ 0 := by
    rw [hcomp']
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hx)
  have hpost2 : ∀ z : Fin (t + 2) → S,
      predictivePosterior h hN t x {z} =
        ENNReal.ofReal (pathProb h (extend t x) t (Fin.init z) *
          h.trans ((Fin.init z) (Fin.last t)) (z (Fin.last (t + 1)))) /
        ENNReal.ofReal (likelihood h (extend t x) t) := by
    intro z
    have h1 := Cslib.MachineLearning.Bayesian.posterior_apply_singleton
      (prefixObsKernel h hN t) (pathPMF h hN (t + 1)).toMeasure hx'' z
    simp only [predictivePosterior]
    rw [h1, key2 z, hD']
  have hpostR2 : ∀ z : Fin (t + 2) → S, (predictivePosterior h hN t x {z}).toReal =
      (pathProb h (extend t x) t (Fin.init z) *
        h.trans ((Fin.init z) (Fin.last t)) (z (Fin.last (t + 1)))) /
        likelihood h (extend t x) t := by
    intro z
    rw [hpost2 z]
    simp only [ENNReal.toReal_div,
      ENNReal.toReal_ofReal (mul_nonneg
        (HiddenMarkovLaw.pathProb_nonneg_extend S O h hN t x (Fin.init z))
        (hN.trans_nonneg _ _)),
      ENNReal.toReal_ofReal hx.le]
  constructor
  · intro s
    simp only [smoothed, backward, mul_one, add_zero]
    rw [forward_eq]
    have hrhs : (∑ z ∈ Finset.univ.filter
        (fun z : Fin (t + 1) → S => z (Fin.last t) = s),
        (filterPosterior h hN t x {z}).toReal) =
        (∑ z ∈ Finset.univ.filter (fun z : Fin (t + 1) → S => z (Fin.last t) = s),
          pathProb h (extend t x) t z) / likelihood h (extend t x) t := by
      trans ∑ z ∈ Finset.univ.filter (fun z : Fin (t + 1) → S => z (Fin.last t) = s),
        pathProb h (extend t x) t z / likelihood h (extend t x) t
      · exact Finset.sum_congr rfl (fun z _ => hpostR z)
      · exact (Finset.sum_div _ _ _).symm
    rw [hrhs, ← Finset.sum_filter]
  · intro s'
    simp only [prediction, smoothed, backward, mul_one, add_zero]
    have hpred : (∑ s : S, forward h (extend t x) t s / likelihood h (extend t x) t *
        h.trans s s') =
        (∑ w : Fin (t + 1) → S,
          pathProb h (extend t x) t w * h.trans (w (Fin.last t)) s') /
          likelihood h (extend t x) t := by
      trans ∑ s : S, (forward h (extend t x) t s * h.trans s s') /
        likelihood h (extend t x) t
      · exact Finset.sum_congr rfl (fun s _ => div_mul_eq_mul_div _ _ _)
      · rw [← Finset.sum_div]
        congr 1
        have h2 : ∀ s : S, forward h (extend t x) t s * h.trans s s' =
            ∑ w ∈ Finset.univ.filter (fun w : Fin (t + 1) → S => w (Fin.last t) = s),
              pathProb h (extend t x) t w * h.trans s s' := by
          intro s
          rw [forward_eq, Finset.sum_mul]
          trans ∑ w : Fin (t + 1) → S, (if w (Fin.last t) = s
            then pathProb h (extend t x) t w * h.trans s s' else 0)
          · exact Finset.sum_congr rfl (fun w _ => by
              by_cases hw : w (Fin.last t) = s <;> simp [hw])
          · rw [Finset.sum_filter]
        trans ∑ s : S, ∑ w ∈ Finset.univ.filter
          (fun w : Fin (t + 1) → S => w (Fin.last t) = s),
            pathProb h (extend t x) t w * h.trans s s'
        · exact Finset.sum_congr rfl (fun s _ => h2 s)
        · rw [sum_fiberwise_eq t
            (fun w s => pathProb h (extend t x) t w * h.trans s s')]
    have hpostsum : (∑ z ∈ Finset.univ.filter
        (fun z : Fin (t + 2) → S => z (Fin.last (t + 1)) = s'),
        (predictivePosterior h hN t x {z}).toReal) =
        (∑ z ∈ Finset.univ.filter (fun z : Fin (t + 2) → S => z (Fin.last (t + 1)) = s'),
          pathProb h (extend t x) t (Fin.init z) *
            h.trans ((Fin.init z) (Fin.last t)) (z (Fin.last (t + 1)))) /
          likelihood h (extend t x) t := by
      trans ∑ z ∈ Finset.univ.filter (fun z : Fin (t + 2) → S => z (Fin.last (t + 1)) = s'),
        (pathProb h (extend t x) t (Fin.init z) *
          h.trans ((Fin.init z) (Fin.last t)) (z (Fin.last (t + 1)))) /
          likelihood h (extend t x) t
      · exact Finset.sum_congr rfl (fun z _ => hpostR2 z)
      · exact (Finset.sum_div _ _ _).symm
    rw [hpred, hpostsum]
    congr 1
    exact (sum_filter_snoc_eq t
      (fun w s' => pathProb h (extend t x) t w * h.trans (w (Fin.last t)) s') s').symm
end Cslib.MachineLearning.Sequence.HiddenMarkovFilter
