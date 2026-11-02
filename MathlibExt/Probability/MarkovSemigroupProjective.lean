/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Probability.Kernel.Composition.KernelLemmas
public import MathlibExt.Probability.KolmogorovExtension

import Mathlib.Data.Fin.Pigeonhole

/-!
# Canonical laws from a Markov transition semigroup

This file constructs the finite-dimensional laws of a time-homogeneous
Markov process from genuine transition kernels.  Requested times are sorted,
the kernels over successive time gaps are iterated, and projectivity is
proved from the Chapman--Kolmogorov law.  Kolmogorov extension then gives a
probability measure on canonical path space.

No projective family or process-existence premise is supplied by a caller.

## Main results

* `finiteChainKernel` iterates kernels over ordered finite times.
* `isProjectiveMeasureFamily_finiteLaw` proves projectivity from
  Chapman--Kolmogorov.
* `pathMeasure` is the resulting canonical path-space probability measure.
* `map_ordered_pathMeasure` identifies every ordered finite-coordinate law.

## Relation to Mathlib

Mathlib's Ionescu--Tulcea construction provides trajectories indexed by
natural-number steps.  This module instead handles arbitrary finite subsets
of `NNReal`: it sorts each requested set, composes adjacent continuous-time
transition kernels, proves deletion/projectivity, and invokes the proved
Polish-space Kolmogorov extension in `MathlibExt`.

## Source

This is the canonical transition-function construction; see Kolmogorov
(1933) and Ethier--Kurtz (1986), Chapter 4, Section 4.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace MathlibExt.Probability.MarkovSemigroupProjective

noncomputable section

variable {E : Type*} [MeasurableSpace E]

/-- The law, as a kernel in its starting point, at finitely many ordered
times.  `s` is the time of the input state and `t` lists the requested
absolute times. -/
noncomputable def finiteChainKernel (K : NNReal → Kernel E E) (s : NNReal) :
    {n : ℕ} → (Fin n → NNReal) → Kernel E (Fin n → E)
  | 0, _ => Kernel.deterministic (fun _ i => Fin.elim0 i) (by fun_prop)
  | n + 1, t =>
      (K (t 0 - s) ⊗ₖ Kernel.prodMkLeft E
        (finiteChainKernel K (t 0) (fun i => t i.succ))).map
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm

instance finiteChainKernel.instIsMarkovKernel
    (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (s : NNReal) {n : ℕ} (t : Fin n → NNReal) :
    IsMarkovKernel (finiteChainKernel K s t) := by
  induction n generalizing s with
  | zero =>
      rw [finiteChainKernel]
      infer_instance
  | succ n ih =>
      rw [finiteChainKernel]
      let _ : IsMarkovKernel
          (finiteChainKernel K (t 0) (fun i => t i.succ)) :=
        ih (t 0) (fun i => t i.succ)
      exact Kernel.IsMarkovKernel.map _
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => E) 0).symm.measurable

/-- The ordered finite-dimensional law started from `x` at time `s`. -/
noncomputable def finiteChainLaw (K : NNReal → Kernel E E) (x : E)
    (s : NNReal) {n : ℕ} (t : Fin n → NNReal) : Measure (Fin n → E) :=
  finiteChainKernel K s t x

instance finiteChainLaw.instIsProbabilityMeasure
    (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)] (x : E)
    (s : NNReal) {n : ℕ} (t : Fin n → NNReal) :
    IsProbabilityMeasure (finiteChainLaw K x s t) := by
  unfold finiteChainLaw
  infer_instance

/-- Moving the starting time forward and then evolving to the first requested
time gives the same finite chain as evolving there directly. -/
theorem finiteChainKernel_comp (K : NNReal → Kernel E E)
    [∀ t, IsMarkovKernel (K t)]
    (hKadd : ∀ s t, K (s + t) = K t ∘ₖ K s)
    {s u : NNReal} (hsu : s ≤ u) {n : ℕ} (t : Fin n → NNReal)
    (hut : ∀ i, u ≤ t i) :
    finiteChainKernel K u t ∘ₖ K (u - s) = finiteChainKernel K s t := by
  cases n with
  | zero =>
      rw [finiteChainKernel, finiteChainKernel,
        Kernel.deterministic_comp_eq_map]
      apply Kernel.ext
      intro x
      rw [Kernel.map_apply _ (by fun_prop)]
      rw [Measure.map_const]
      rw [Kernel.deterministic_apply]
      simp
  | succ n =>
      rw [finiteChainKernel, finiteChainKernel, ← Kernel.map_comp]
      apply congrArg (fun L : Kernel E (E × (Fin n → E)) =>
        Kernel.map L (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => E) 0).symm)
      rw [Kernel.compProd_prodMkLeft_eq_comp,
        Kernel.compProd_prodMkLeft_eq_comp, Kernel.comp_assoc]
      congr 1
      rw [← hKadd]
      congr 1
      rw [add_comm, tsub_add_tsub_cancel (hut 0) hsu]

/-- Remove one coordinate from a finite vector. -/
def eraseCoordinate {n : ℕ} (j : Fin (n + 1)) :
    (Fin (n + 1) → E) → (Fin n → E) :=
  fun z i => z (j.succAbove i)

theorem measurable_eraseCoordinate {n : ℕ} (j : Fin (n + 1)) :
    Measurable (eraseCoordinate (E := E) j) := by
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply (j.succAbove i)

private theorem eraseCoordinate_zero_comp_cons {n : ℕ} :
    eraseCoordinate (E := E) (0 : Fin (n + 1)) ∘
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => E) 0).symm = Prod.snd := by
  funext z
  ext i
  rfl

private theorem eraseCoordinate_succ_comp_cons {n : ℕ} (j : Fin (n + 1)) :
    eraseCoordinate (E := E) j.succ ∘
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 2) => E) 0).symm =
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => E) 0).symm ∘
      Prod.map id (eraseCoordinate (E := E) j) := by
  funext z
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · simp only [Function.comp_apply, eraseCoordinate,
      Fin.succ_succAbove_succ]
    rfl

/-- Deleting the first requested time composes the initial transition with
the transition to the next requested time. -/
theorem finiteChainKernel_map_eraseCoordinate_zero
    (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (hKadd : ∀ s t, K (s + t) = K t ∘ₖ K s)
    {s : NNReal} {n : ℕ} (t : Fin (n + 1) → NNReal)
    (hst : s ≤ t 0) (ht : StrictMono t) :
    (finiteChainKernel K s t).map
        (eraseCoordinate (E := E) (0 : Fin (n + 1))) =
      finiteChainKernel K s (fun i => t i.succ) := by
  rw [finiteChainKernel, ← Kernel.map_comp_right _
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => E) 0).symm.measurable
    (measurable_eraseCoordinate (E := E) 0),
    eraseCoordinate_zero_comp_cons,
    ← Kernel.snd_eq, Kernel.snd_compProd_prodMkLeft]
  exact finiteChainKernel_comp K hKadd hst _ fun i =>
    (ht (by simp)).le

/-- Deleting one requested time from an ordered finite Markov chain composes
the two adjacent transition kernels. -/
theorem finiteChainKernel_map_eraseCoordinate
    (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (hKadd : ∀ s t, K (s + t) = K t ∘ₖ K s)
    {s : NNReal} {n : ℕ} (t : Fin (n + 1) → NNReal)
    (hst : s ≤ t 0) (ht : StrictMono t) (j : Fin (n + 1)) :
    (finiteChainKernel K s t).map (eraseCoordinate (E := E) j) =
      finiteChainKernel K s (fun i => t (j.succAbove i)) := by
  induction n generalizing s with
  | zero =>
      refine Fin.cases ?_ (fun i => Fin.elim0 i) j
      exact finiteChainKernel_map_eraseCoordinate_zero K hKadd t hst ht
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) j
      · exact finiteChainKernel_map_eraseCoordinate_zero K hKadd t hst ht
      · rw [finiteChainKernel, ← Kernel.map_comp_right _
          (MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 2) => E) 0).symm.measurable
          (measurable_eraseCoordinate (E := E) j.succ),
          eraseCoordinate_succ_comp_cons,
          Kernel.map_comp_right _
            (measurable_id.prodMap (measurable_eraseCoordinate (E := E) j))
            (MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => E) 0).symm.measurable,
          Kernel.compProd_prodMkLeft_eq_comp, Kernel.map_comp,
          ← Kernel.map_prod_map _ _ measurable_id
            (measurable_eraseCoordinate (E := E) j),
          Kernel.map_id]
        have htailStart : t 0 ≤ t (Fin.succ 0) :=
          (ht (by simp)).le
        have htailMono : StrictMono (fun i : Fin (n + 1) => t i.succ) :=
          ht.comp Fin.strictMono_succ
        rw [ih (fun i : Fin (n + 1) => t i.succ)
          htailStart htailMono j]
        rw [← Kernel.compProd_prodMkLeft_eq_comp]
        conv_rhs => rw [finiteChainKernel]
        simp only [Fin.succ_succAbove_zero,
          Fin.succ_succAbove_succ]

private theorem finiteChainKernel_map_empty
    (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    {s : NNReal} {n : ℕ} (t : Fin n → NNReal) :
    (finiteChainKernel K s t).map
        (fun (_ : Fin n → E) (i : Fin 0) => Fin.elim0 i) =
      finiteChainKernel K s (fun i : Fin 0 => Fin.elim0 i) := by
  rw [finiteChainKernel]
  apply Kernel.ext
  intro x
  rw [Kernel.map_apply _ (by fun_prop), Measure.map_const,
    Kernel.deterministic_apply]
  simp

/-- Restrict an ordered finite Markov law along any strictly increasing map
of coordinate sets. -/
theorem finiteChainKernel_map_strictMono
    (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (hKadd : ∀ s t, K (s + t) = K t ∘ₖ K s)
    {s : NNReal} {m n : ℕ} (t : Fin n → NNReal)
    (hst : ∀ i, s ≤ t i) (ht : StrictMono t)
    (e : Fin m → Fin n) (he : StrictMono e) :
    (finiteChainKernel K s t).map (fun z i => z (e i)) =
      finiteChainKernel K s (fun i => t (e i)) := by
  induction n using Nat.strong_induction_on generalizing m s with
  | h n ih =>
      cases m with
      | zero =>
          have hmap :
              (fun z : Fin n → E => fun i : Fin 0 => z (e i)) =
                (fun (_ : Fin n → E) (i : Fin 0) => Fin.elim0 i) := by
            funext z i
            exact Fin.elim0 i
          have htime :
              (fun i : Fin 0 => t (e i)) =
                (fun i : Fin 0 => Fin.elim0 i) := by
            funext i
            exact Fin.elim0 i
          rw [hmap, htime]
          exact finiteChainKernel_map_empty K t
      | succ m =>
          have hmn : m + 1 ≤ n := Fin.le_of_injective e he.injective
          rcases eq_or_lt_of_le hmn with hEq | hlt
          · subst n
            rw [he.eq_id]
            simp
          · have hnpos : 0 < n :=
              (Nat.zero_lt_succ m).trans_le hmn
            obtain ⟨N, rfl⟩ :=
              Nat.exists_eq_succ_of_ne_zero hnpos.ne'
            have hnot : ¬Function.Surjective e := by
              intro hsurj
              have hc := Fintype.card_le_of_surjective e hsurj
              simp only [Fintype.card_fin] at hc
              omega
            have hex : ∃ j, ∀ i, e i ≠ j := by
              simpa only [Function.Surjective, not_forall,
                not_exists, not_not] using hnot
            obtain ⟨j, hj⟩ := hex
            let e' : Fin (m + 1) → Fin N := fun i =>
              Classical.choose (Fin.exists_succAbove_eq (hj i))
            have he'_factor (i : Fin (m + 1)) :
                j.succAbove (e' i) = e i :=
              Classical.choose_spec (Fin.exists_succAbove_eq (hj i))
            have he' : StrictMono e' := by
              intro a b hab
              apply (Fin.succAboveOrderEmb j).lt_iff_lt.mp
              change j.succAbove (e' a) < j.succAbove (e' b)
              rw [he'_factor, he'_factor]
              exact he hab
            have he'_measurable :
                Measurable (fun z : Fin N → E => fun i => z (e' i)) := by
              apply Measurable.of_eval
              intro i
              exact measurable_pi_apply (e' i)
            calc
              (finiteChainKernel K s t).map (fun z i => z (e i)) =
                  ((finiteChainKernel K s t).map
                    (eraseCoordinate (E := E) j)).map
                    (fun z i => z (e' i)) := by
                rw [← Kernel.map_comp_right _
                  (measurable_eraseCoordinate (E := E) j)
                  he'_measurable]
                congr 1
                funext z i
                rw [Function.comp_apply, eraseCoordinate, he'_factor]
              _ = (finiteChainKernel K s
                    (fun i => t (j.succAbove i))).map
                    (fun z i => z (e' i)) := by
                rw [finiteChainKernel_map_eraseCoordinate K hKadd t
                  (hst 0) ht j]
              _ = finiteChainKernel K s
                    (fun i => t (j.succAbove (e' i))) := by
                exact ih N (by omega) _ (fun i => hst _)
                  (ht.comp (Fin.strictMono_succAbove j)) e' he'
              _ = finiteChainKernel K s (fun i => t (e i)) := by
                congr 1
                funext i
                rw [he'_factor]

/-- Measure form of `finiteChainKernel_map_strictMono`. -/
theorem finiteChainLaw_map_strictMono
    (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (hKadd : ∀ s t, K (s + t) = K t ∘ₖ K s)
    (x : E) {s : NNReal} {m n : ℕ} (t : Fin n → NNReal)
    (hst : ∀ i, s ≤ t i) (ht : StrictMono t)
    (e : Fin m → Fin n) (he : StrictMono e) :
    (finiteChainLaw K x s t).map (fun z i => z (e i)) =
      finiteChainLaw K x s (fun i => t (e i)) := by
  rw [finiteChainLaw, ← Kernel.map_apply _ (by fun_prop),
    finiteChainKernel_map_strictMono K hKadd t hst ht e he]
  rfl

/-- Reindex an ordered vector by the increasing enumeration of a finset. -/
noncomputable def orderMeasurableEquiv (J : Finset NNReal) :
    (Fin J.card → E) ≃ᵐ (J → E) where
  toFun y j := y ((J.orderIsoOfFin rfl).symm j)
  invFun y i := y (J.orderIsoOfFin rfl i)
  left_inv y := by
    ext i
    simp
  right_inv y := by
    ext j
    simp
  measurable_toFun := Measurable.of_eval fun _ => measurable_pi_apply _
  measurable_invFun := Measurable.of_eval fun _ => measurable_pi_apply _

/-- The increasing reindexing of the elements of `J` among those of a
larger finset `I`. -/
noncomputable def orderRestriction {I J : Finset NNReal} (hJI : J ⊆ I) :
    Fin J.card ↪o Fin I.card :=
  OrderEmbedding.ofStrictMono
    (fun j => (I.orderIsoOfFin rfl).symm
      ⟨J.orderEmbOfFin rfl j, hJI (J.orderEmbOfFin_mem rfl j)⟩)
    (fun _a _b hab => (I.orderIsoOfFin rfl).symm.strictMono
      ((J.orderEmbOfFin rfl).strictMono hab))

@[simp]
theorem orderEmbOfFin_orderRestriction {I J : Finset NNReal}
    (hJI : J ⊆ I) (j : Fin J.card) :
    I.orderEmbOfFin rfl (orderRestriction hJI j) =
      J.orderEmbOfFin rfl j := by
  change I.orderEmbOfFin rfl
    ((I.orderIsoOfFin rfl).symm
      ⟨J.orderEmbOfFin rfl j,
        hJI (J.orderEmbOfFin_mem rfl j)⟩) = _
  exact congrArg Subtype.val
    ((I.orderIsoOfFin rfl).apply_symm_apply _)

private theorem restrict_orderMeasurableEquiv {I J : Finset NNReal}
    (hJI : J ⊆ I) :
    Finset.restrict₂ (π := fun _ => E) hJI ∘ orderMeasurableEquiv I =
      orderMeasurableEquiv J ∘
        (fun z i => z (orderRestriction hJI i)) := by
  funext z j
  apply congrArg z
  apply (I.orderIsoOfFin rfl).injective
  rw [(I.orderIsoOfFin rfl).apply_symm_apply]
  apply Subtype.ext
  change (j : NNReal) =
    I.orderEmbOfFin rfl
      (orderRestriction hJI ((J.orderIsoOfFin rfl).symm j))
  rw [orderEmbOfFin_orderRestriction]
  exact (congrArg Subtype.val
    ((J.orderIsoOfFin rfl).apply_symm_apply j)).symm

/-- The canonical law at an arbitrary finite set of nonnegative times.

The generic construction does not assume `K 0 = Kernel.id`.  Consequently,
when zero is requested its marginal is `K 0 x`; callers that need a
deterministic initial value prove the identity law for their kernel. -/
noncomputable def finiteLaw (K : NNReal → Kernel E E) (x : E)
    (J : Finset NNReal) : Measure (J → E) :=
  (finiteChainLaw K x 0 (J.orderEmbOfFin rfl)).map
    (orderMeasurableEquiv J)

instance finiteLaw.instIsProbabilityMeasure
    (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (x : E) (J : Finset NNReal) : IsProbabilityMeasure (finiteLaw K x J) := by
  unfold finiteLaw
  infer_instance

/-- The finite laws obtained by sorting requested times form a projective
family; projectivity is a consequence of Chapman--Kolmogorov, not a premise. -/
theorem isProjectiveMeasureFamily_finiteLaw
    (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (hKadd : ∀ s t, K (s + t) = K t ∘ₖ K s) (x : E) :
    IsProjectiveMeasureFamily (α := fun _ : NNReal => E)
      (finiteLaw K x) := by
  intro I J hJI
  let e := orderRestriction hJI
  have he : StrictMono e := e.strictMono
  have heMeasurable :
      Measurable (fun z : Fin I.card → E => fun i => z (e i)) := by
    apply Measurable.of_eval
    intro i
    exact measurable_pi_apply (e i)
  have hchain :
      (finiteChainLaw K x 0 (I.orderEmbOfFin rfl)).map
          (fun z i => z (e i)) =
        finiteChainLaw K x 0 (J.orderEmbOfFin rfl) := by
    calc
      (finiteChainLaw K x 0 (I.orderEmbOfFin rfl)).map
          (fun z i => z (e i)) =
          finiteChainLaw K x 0
            (fun i => I.orderEmbOfFin rfl (e i)) :=
        finiteChainLaw_map_strictMono K hKadd x _
          (fun _ => bot_le) (I.orderEmbOfFin rfl).strictMono e he
      _ = finiteChainLaw K x 0 (J.orderEmbOfFin rfl) := by
        congr 1
        funext i
        exact orderEmbOfFin_orderRestriction hJI i
  calc
    finiteLaw K x J =
        (finiteChainLaw K x 0 (J.orderEmbOfFin rfl)).map
          (orderMeasurableEquiv J) := rfl
    _ = ((finiteChainLaw K x 0 (I.orderEmbOfFin rfl)).map
          (fun z i => z (e i))).map (orderMeasurableEquiv J) := by
        rw [hchain]
    _ = (finiteChainLaw K x 0 (I.orderEmbOfFin rfl)).map
          (orderMeasurableEquiv J ∘ fun z i => z (e i)) := by
        rw [Measure.map_map (orderMeasurableEquiv J).measurable
          heMeasurable]
    _ = (finiteChainLaw K x 0 (I.orderEmbOfFin rfl)).map
          (Finset.restrict₂ (π := fun _ => E) hJI ∘
            orderMeasurableEquiv I) := by
        rw [restrict_orderMeasurableEquiv hJI]
    _ = ((finiteChainLaw K x 0 (I.orderEmbOfFin rfl)).map
          (orderMeasurableEquiv I)).map
            (Finset.restrict₂ (π := fun _ => E) hJI) := by
        exact (Measure.map_map (Finset.measurable_restrict₂ hJI)
          (orderMeasurableEquiv I).measurable).symm
    _ = (finiteLaw K x I).map
          (Finset.restrict₂ (π := fun _ => E) hJI) := rfl

section Extension

variable [TopologicalSpace E] [PolishSpace E] [BorelSpace E]

/-- Kolmogorov extension applied to the proved finite Markov laws. -/
theorem exists_projectiveLimit
    (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (hKadd : ∀ s t, K (s + t) = K t ∘ₖ K s) (x : E) :
    ∃ P : Measure (NNReal → E),
      IsProjectiveLimit P (finiteLaw K x) := by
  exact
    MathlibExt.Probability.KolmogorovExtensionWanted.kolmogorov_extension
      (α := fun _ : NNReal => E) (finiteLaw K x)
      (isProjectiveMeasureFamily_finiteLaw K hKadd x)

/-- The canonical path-space measure selected from Kolmogorov extension.

As for `finiteLaw`, no identity-at-zero hypothesis is built into this generic
object: its time-zero marginal is `K 0 x` unless the caller proves
`K 0 = Kernel.id`. -/
noncomputable def pathMeasure
    (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (hKadd : ∀ s t, K (s + t) = K t ∘ₖ K s) (x : E) :
    Measure (NNReal → E) :=
  Classical.choose (exists_projectiveLimit K hKadd x)

/-- The canonical path measure has exactly the constructed finite laws. -/
theorem isProjectiveLimit_pathMeasure
    (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (hKadd : ∀ s t, K (s + t) = K t ∘ₖ K s) (x : E) :
    IsProjectiveLimit (pathMeasure K hKadd x) (finiteLaw K x) :=
  Classical.choose_spec (exists_projectiveLimit K hKadd x)

/-- The canonical path measure is a probability measure. -/
instance pathMeasure.instIsProbabilityMeasure
    (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (hKadd : ∀ s t, K (s + t) = K t ∘ₖ K s) (x : E) :
    IsProbabilityMeasure (pathMeasure K hKadd x) :=
  (isProjectiveLimit_pathMeasure K hKadd x).isProbabilityMeasure

/-- Every finite coordinate projection of the canonical path measure is its
explicit iterated-kernel law. -/
theorem map_restrict_pathMeasure
    (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (hKadd : ∀ s t, K (s + t) = K t ∘ₖ K s)
    (x : E) (J : Finset NNReal) :
    (pathMeasure K hKadd x).map J.restrict = finiteLaw K x J :=
  isProjectiveLimit_pathMeasure K hKadd x J

/-- The coordinates in increasing finset order have exactly the corresponding
iterated-kernel law. -/
theorem map_ordered_pathMeasure
    (K : NNReal → Kernel E E) [∀ t, IsMarkovKernel (K t)]
    (hKadd : ∀ s t, K (s + t) = K t ∘ₖ K s)
    (x : E) (J : Finset NNReal) :
    (pathMeasure K hKadd x).map
        (fun ω i => ω (J.orderEmbOfFin rfl i)) =
      finiteChainLaw K x 0 (J.orderEmbOfFin rfl) := by
  calc
    (pathMeasure K hKadd x).map
        (fun ω i => ω (J.orderEmbOfFin rfl i)) =
        ((pathMeasure K hKadd x).map J.restrict).map
          (orderMeasurableEquiv J).symm := by
      rw [Measure.map_map (orderMeasurableEquiv J).symm.measurable
        (Finset.measurable_restrict J)]
      rfl
    _ = (finiteLaw K x J).map (orderMeasurableEquiv J).symm := by
      rw [map_restrict_pathMeasure]
    _ = ((finiteChainLaw K x 0 (J.orderEmbOfFin rfl)).map
        (orderMeasurableEquiv J)).map (orderMeasurableEquiv J).symm := rfl
    _ = finiteChainLaw K x 0 (J.orderEmbOfFin rfl) :=
      MeasurableEquiv.map_symm_map (orderMeasurableEquiv J)

end Extension

end

end MathlibExt.Probability.MarkovSemigroupProjective
