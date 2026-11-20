/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














import Code.FK.DlrSandwich
import Code.FK.FKGeneralQConsumer
import Code.FK.IvProperties

open MeasureTheory Filter Set
open scoped BigOperators

namespace StatMech

namespace FK

open StatMech.Lattice



noncomputable def dlrBcEventMass {V : Type*} [Fintype V] [DecidableEq V]
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    (p q : ℝ) (A : Set (ConfigSpace (Sym2 V))) : ℝ :=
  ∑ omega, A.indicator (fun _ => (1 : ℝ)) omega * bcProb G C p q omega






noncomputable def IsFKDLR (d : ℕ) (p q : ℝ)
    (phi : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Prop := by
  classical
  exact ∀ n, ∃ weight : SimpleGraph (boxVerts d n) → ℝ,
      (∀ C, 0 ≤ weight C) ∧
      (∑ C, weight C = 1) ∧
      (∀ C, weight C ≠ 0 → C ≤ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d n)) ∧
      ∀ A : Set (ConfigSpace (Sym2 (boxVerts d n))),
        (phi : Measure _).real (boxRestrict d n ⁻¹' A) =
          ∑ C, weight C * dlrBcEventMass (boxGraph d n) C p q A



theorem dlr_box_mixture_sandwich
    {d n : ℕ} {p q : ℝ}
    {phi : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hDLR : IsFKDLR d p q phi)
    {A : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA : IsIncreasing A) :
    dlrBcEventMass (boxGraph d n) (⊥ : SimpleGraph (boxVerts d n)) p q A ≤
        (phi : Measure _).real (boxRestrict d n ⁻¹' A) ∧
      (phi : Measure _).real (boxRestrict d n ⁻¹' A) ≤
        dlrBcEventMass (boxGraph d n)
          (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d n)) p q A := by
  classical
  obtain ⟨weight, hweight, hsum, hsupp, hmix⟩ := hDLR n
  let freeMass := dlrBcEventMass (boxGraph d n)
    (⊥ : SimpleGraph (boxVerts d n)) p q A
  let wiredMass := dlrBcEventMass (boxGraph d n)
    (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d n)) p q A
  have hlowerComponent : ∀ C : SimpleGraph (boxVerts d n),
      freeMass ≤ dlrBcEventMass (boxGraph d n) C p q A := by
    intro C
    exact bcProb_free_le_bc (boxGraph d n) C hp hp1 hq hA
  have hlower : freeMass ≤
      ∑ C, weight C * dlrBcEventMass (boxGraph d n) C p q A := by
    calc
      freeMass = ∑ C, weight C * freeMass := by
        rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ C, weight C * dlrBcEventMass (boxGraph d n) C p q A := by
        apply Finset.sum_le_sum
        intro C _
        exact mul_le_mul_of_nonneg_left (hlowerComponent C) (hweight C)
  have hupper : (∑ C, weight C * dlrBcEventMass (boxGraph d n) C p q A) ≤
      wiredMass := by
    calc
      (∑ C, weight C * dlrBcEventMass (boxGraph d n) C p q A)
          ≤ ∑ C, weight C * wiredMass := by
            apply Finset.sum_le_sum
            intro C _
            by_cases hzero : weight C = 0
            · simp [hzero]
            · exact mul_le_mul_of_nonneg_left
                (bcProb_bc_le_wired (boxGraph d n) (boxBoundary d n) C
                  (hsupp C hzero) hp hp1 hq hA)
                (hweight C)
      _ = wiredMass := by rw [← Finset.sum_mul, hsum, one_mul]
  rw [hmix A]
  exact ⟨hlower, hupper⟩




theorem dlr_infinite_sandwich
    {d N : ℕ} {p q : ℝ}
    {phi : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hDLR : IsFKDLR d p q phi)
    {A : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hA : IsIncreasing A) :
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' A) ≤
        (phi : Measure _).real (boxRestrict d N ⁻¹' A) ∧
      (phi : Measure _).real (boxRestrict d N ⁻¹' A) ≤
        (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' A) := by
  classical
  have hfinite : ∀ m, N ≤ m →
      (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' A) ≤
        (phi : Measure _).real (boxRestrict d N ⁻¹' A) ∧
      (phi : Measure _).real (boxRestrict d N ⁻¹' A) ≤
        (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' A) := by
    intro m hNm
    let T : Set (ConfigSpace (Sym2 (boxVerts d m))) := boxRestrictLE d hNm ⁻¹' A
    have hT : IsIncreasing T := by
      intro omega omega' homega hmem
      exact hA (boxRestrictLE_monotone d hNm homega) hmem
    have hevent : boxRestrict d N ⁻¹' A = boxRestrict d m ⁻¹' T := by
      ext omega
      simp only [T, Set.mem_preimage, boxRestrictLE_boxRestrict]
    have hsand := dlr_box_mixture_sandwich hp hp1 hq hDLR hT
    have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
      (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
    have hfree :
        dlrBcEventMass (boxGraph d m) (⊥ : SimpleGraph (boxVerts d m)) p q T =
          (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
            (boxRestrict d m ⁻¹' T) := by
      rw [freeFiniteMeasure_real_boxRestrictEvent m hp hp1
        (zero_lt_one.trans_le hq) T hmeas]
      unfold dlrBcEventMass
      apply Finset.sum_congr rfl
      intro omega _
      rw [bcProb_bot_eq_fkProb]
    have hwired :
        dlrBcEventMass (boxGraph d m)
            (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d m)) p q T =
          (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
            (boxRestrict d m ⁻¹' T) := by
      rw [fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1
        (zero_lt_one.trans_le hq) T hmeas]
      unfold dlrBcEventMass
      apply Finset.sum_congr rfl
      intro omega _
      rw [bcProb_clique_eq_wiredFkProb]
    rw [hfree, hwired, ← hevent] at hsand
    exact hsand
  have heventually : ∀ᶠ m in atTop,
      (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' A) ≤
        (phi : Measure _).real (boxRestrict d N ⁻¹' A) ∧
      (phi : Measure _).real (boxRestrict d N ⁻¹' A) ≤
        (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' A) :=
    Filter.eventually_atTop.2 ⟨N, fun m hm => hfinite m hm⟩
  constructor
  · exact le_of_tendsto_of_tendsto
      (fkgq_free_infinite_measure N hp hp1 hq hA) tendsto_const_nhds
      (heventually.mono fun _ h => h.1)
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds
      (fkgq_wired_infinite_measure N hp hp1 hq hA)
      (heventually.mono fun _ h => h.2)

end FK

end StatMech
