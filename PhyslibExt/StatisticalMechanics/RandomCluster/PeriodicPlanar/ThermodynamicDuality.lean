/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TorusDuality
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CoherentLimit

/-!
# Duality of infinite-volume random-cluster measures

Planar duality passes from finite volume to the thermodynamic limit: if the dual finite-volume
measures are the images of the primal ones under the configuration duality, so are their weak
limits.

## i. Overview

An edge bijection `E ≃ F` induces the configuration duality `ω ↦ ω*`, `ω*(f) = ¬ω(f†)`, a
homeomorphism of configuration spaces. Weak convergence is preserved by continuous maps and weak
limits are unique, so a finite-volume exchange `μ*ₙ = μₙ ∘ (·*)⁻¹` passes to the limit. Applied to
buffered free and wired measures of a periodic graph and its dual, this gives
"free primal ↔ wired dual" and "wired primal ↔ free dual" in infinite volume.
Both headline results are conditional: they assume the finite-volume exchange `hfinite` for every
`n` (the buffered measures of the dual graph are exact images of the primal ones), besides
`0 < p, p* < 1` and `1 ≤ q, q*`.

## ii. Key results

- `weakLimit_dual_of_finite_exchange` : duality of finite-volume measures passes to weak limits.
- `PeriodicGraph.free_wired_bufferedInfiniteVolume_dual` : the wired dual infinite-volume measure
  is the image of the free primal one.
- `PeriodicGraph.wired_free_bufferedInfiniteVolume_dual` : the free dual infinite-volume measure is
  the image of the wired primal one.

## iii. Table of contents

- A. Configuration duality
- B. Duality of weak limits
- C. Buffered infinite-volume measures

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Section 6.1.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace StatMech
namespace FK
namespace PeriodicPlanar

variable {E F : Type*}

/-! ## A. Configuration duality -/

/-- The configuration duality induced by an edge bijection: a dual edge is open exactly when its
primal edge is closed. -/
def dualConfigEquiv (edgeDual : E ≃ F) : ConfigSpace E ≃ ConfigSpace F where
  toFun omega f := !(omega (edgeDual.symm f))
  invFun eta e := !(eta (edgeDual e))
  left_inv := by intro omega; funext e; simp
  right_inv := by intro eta; funext f; simp

@[simp] lemma dualConfigEquiv_apply (edgeDual : E ≃ F)
    (omega : ConfigSpace E) (f : F) :
    dualConfigEquiv edgeDual omega f = !(omega (edgeDual.symm f)) := rfl

@[simp] lemma dualConfigEquiv_symm_apply (edgeDual : E ≃ F)
    (eta : ConfigSpace F) (e : E) :
    (dualConfigEquiv edgeDual).symm eta e = !(eta (edgeDual e)) := rfl

lemma continuous_dualConfigEquiv (edgeDual : E ≃ F) :
    Continuous (dualConfigEquiv edgeDual) := by
  refine continuous_pi fun f => ?_
  exact (continuous_of_discreteTopology (f := fun b : Bool => !b)).comp
    (continuous_apply (edgeDual.symm f))

lemma continuous_dualConfigEquiv_symm (edgeDual : E ≃ F) :
    Continuous (dualConfigEquiv edgeDual).symm := by
  refine continuous_pi fun e => ?_
  exact (continuous_of_discreteTopology (f := fun b : Bool => !b)).comp
    (continuous_apply (edgeDual e))

/-- The configuration duality as a homeomorphism of configuration spaces. -/
def dualConfigHomeomorph (edgeDual : E ≃ F) : ConfigSpace E ≃ₜ ConfigSpace F where
  toEquiv := dualConfigEquiv edgeDual
  continuous_toFun := continuous_dualConfigEquiv edgeDual
  continuous_invFun := continuous_dualConfigEquiv_symm edgeDual

@[simp] lemma dualConfigEquiv_symm (edgeDual : E ≃ F) :
    dualConfigEquiv edgeDual.symm = (dualConfigEquiv edgeDual).symm := by
  ext eta e
  rfl

/-! ## B. Duality of weak limits -/

variable [Countable E] [Countable F]

/-- If the dual measures are the images of the primal ones under configuration duality, then so are
their weak limits. -/
lemma weakLimit_dual_of_finite_exchange
    (edgeDual : E ≃ F)
    (mu : ℕ → ProbabilityMeasure (ConfigSpace E))
    (muDual : ℕ → ProbabilityMeasure (ConfigSpace F))
    (nu : ProbabilityMeasure (ConfigSpace E))
    (nuDual : ProbabilityMeasure (ConfigSpace F))
    (hfinite : ∀ n, muDual n =
      (mu n).map (dualConfigEquiv edgeDual))
    (hmu : WeakConvergesTo mu nu)
    (hdual : WeakConvergesTo muDual nuDual) :
    nuDual = nu.map
      (dualConfigEquiv edgeDual) := by
  have hmapped : WeakConvergesTo
      (fun n => (mu n).map
        (dualConfigEquiv edgeDual))
      (nu.map (dualConfigEquiv edgeDual)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      mu nu hmu (continuous_dualConfigEquiv edgeDual)
  have hseq : (fun n => (mu n).map
      (dualConfigEquiv edgeDual)) = muDual := by
    funext n
    exact (hfinite n).symm
  rw [hseq] at hmapped
  exact tendsto_nhds_unique hdual hmapped

lemma weakLimit_dual_event
    (edgeDual : E ≃ F)
    (nu : ProbabilityMeasure (ConfigSpace E))
    (nuDual : ProbabilityMeasure (ConfigSpace F))
    (hdual : nuDual = nu.map
      (dualConfigEquiv edgeDual))
    {A : Set (ConfigSpace F)} (hA : MeasurableSet A) :
    (nuDual : Measure (ConfigSpace F)) A =
      (nu : Measure (ConfigSpace E)) ((dualConfigEquiv edgeDual) ⁻¹' A) := by
  rw [hdual, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (continuous_dualConfigEquiv edgeDual).measurable hA]

lemma weakLimit_dual_of_subsequence_exchange
    (edgeDual : E ≃ F)
    (mu : ℕ → ProbabilityMeasure (ConfigSpace E))
    (muDual : ℕ → ProbabilityMeasure (ConfigSpace F))
    (phi : ℕ → ℕ)
    (nu : ProbabilityMeasure (ConfigSpace E))
    (nuDual : ProbabilityMeasure (ConfigSpace F))
    (hfinite : ∀ n, muDual n =
      (mu n).map (dualConfigEquiv edgeDual))
    (hmu : WeakConvergesTo (fun n => mu (phi n)) nu)
    (hdual : WeakConvergesTo (fun n => muDual (phi n)) nuDual) :
    nuDual = nu.map
      (dualConfigEquiv edgeDual) := by
  apply weakLimit_dual_of_finite_exchange edgeDual
    (fun n => mu (phi n)) (fun n => muDual (phi n)) nu nuDual
  · exact fun n => hfinite (phi n)
  · exact hmu
  · exact hdual

lemma exists_common_weak_dual_limits
    (edgeDual : E ≃ F)
    (mu : ℕ → ProbabilityMeasure (ConfigSpace E))
    (muDual : ℕ → ProbabilityMeasure (ConfigSpace F))
    (hfinite : ∀ n, muDual n =
      (mu n).map (dualConfigEquiv edgeDual)) :
    ∃ (phi : ℕ → ℕ)
      (nu : ProbabilityMeasure (ConfigSpace E))
      (nuDual : ProbabilityMeasure (ConfigSpace F)),
      StrictMono phi ∧
      WeakConvergesTo (fun n => mu (phi n)) nu ∧
      WeakConvergesTo (fun n => muDual (phi n)) nuDual ∧
      nuDual = nu.map
        (dualConfigEquiv edgeDual) := by
  obtain ⟨nu, phi, hphi, hmu⟩ := CompactSpace.tendsto_subseq mu
  let nuDual := nu.map
    (dualConfigEquiv edgeDual)
  have hmapped : WeakConvergesTo
      (fun n => (mu (phi n)).map
        (dualConfigEquiv edgeDual))
      nuDual :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n => mu (phi n)) nu hmu (continuous_dualConfigEquiv edgeDual)
  have hseq : (fun n => (mu (phi n)).map
      (dualConfigEquiv edgeDual)) =
      (fun n => muDual (phi n)) := by
    funext n
    exact (hfinite (phi n)).symm
  rw [hseq] at hmapped
  exact ⟨phi, nu, nuDual, hphi, hmu, hmapped, rfl⟩

/-! ## C. Buffered infinite-volume measures -/

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]

/-- Conditional on the finite-volume exchange `hfinite` for every `n`, the buffered wired
infinite-volume measure of the dual graph is the image of the buffered free infinite-volume measure
of the primal graph. -/
theorem PeriodicGraph.free_wired_bufferedInfiniteVolume_dual
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W)
    (edgeDual : Sym2 V ≃ Sym2 W)
    {p pDual q qDual : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hpDual : 0 < pDual) (hpDual1 : pDual < 1) (hqDual : 1 ≤ qDual)
    (hfinite : ∀ n,
      Pdual.wiredBufferedMeasure n hpDual hpDual1 (zero_lt_one.trans_le hqDual) =
        (P.freeBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq)).map
          (dualConfigEquiv edgeDual)) :
    Pdual.wiredBufferedInfiniteVolume hpDual hpDual1
        (zero_lt_one.trans_le hqDual) =
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)).map
        (dualConfigEquiv edgeDual) := by
  exact weakLimit_dual_of_finite_exchange edgeDual
    (fun n => P.freeBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq))
    (fun n => Pdual.wiredBufferedMeasure n hpDual hpDual1
      (zero_lt_one.trans_le hqDual))
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq))
    (Pdual.wiredBufferedInfiniteVolume hpDual hpDual1
      (zero_lt_one.trans_le hqDual))
    hfinite
    (P.freeBufferedMeasure_weakConverges hp hp1 hq)
    (Pdual.wiredBufferedMeasure_weakConverges hpDual hpDual1 hqDual)

/-- Conditional on the finite-volume exchange `hfinite` for every `n`, the buffered free
infinite-volume measure of the dual graph is the image of the buffered wired infinite-volume measure
of the primal graph. -/
theorem PeriodicGraph.wired_free_bufferedInfiniteVolume_dual
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W)
    (edgeDual : Sym2 V ≃ Sym2 W)
    {p pDual q qDual : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hpDual : 0 < pDual) (hpDual1 : pDual < 1) (hqDual : 1 ≤ qDual)
    (hfinite : ∀ n,
      Pdual.freeBufferedMeasure n hpDual hpDual1 (zero_lt_one.trans_le hqDual) =
        (P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq)).map
          (dualConfigEquiv edgeDual)) :
    Pdual.freeBufferedInfiniteVolume hpDual hpDual1
        (zero_lt_one.trans_le hqDual) =
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)).map
        (dualConfigEquiv edgeDual) := by
  exact weakLimit_dual_of_finite_exchange edgeDual
    (fun n => P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq))
    (fun n => Pdual.freeBufferedMeasure n hpDual hpDual1
      (zero_lt_one.trans_le hqDual))
    (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq))
    (Pdual.freeBufferedInfiniteVolume hpDual hpDual1
      (zero_lt_one.trans_le hqDual))
    hfinite
    (P.wiredBufferedMeasure_weakConverges hp hp1 hq)
    (Pdual.freeBufferedMeasure_weakConverges hpDual hpDual1 hqDual)

end PeriodicPlanar
end FK
end StatMech
