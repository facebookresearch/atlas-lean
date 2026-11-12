/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Mathlib
import Code.FK.InfiniteVolume
import Code.FK.Limits
import Code.Foundations.MonotoneLimit
import Code.Foundations.Prokhorov

open MeasureTheory Filter Topology
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK





























theorem weakLimit_extremality_of_common_subseq (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {ν₀ ν₁ : ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))}
    {ψ : ℕ → ℕ}
    (h₀ : WeakConvergesTo
      (fun n => freeFiniteMeasure d (ψ n) hp hp1 (zero_lt_one.trans_le hq)) ν₀)
    (h₁ : WeakConvergesTo
      (fun n => wiredFiniteMeasure d (ψ n) hp hp1 (zero_lt_one.trans_le hq)) ν₁)
    {A : Set (ConfigSpace (Sym2 (Lattice.Site d)))}
    (hAclopen : IsClopen A) (hAinc : IsIncreasing A) :
    (ν₀ : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real A
      ≤ (ν₁ : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real A := by
  
  have ht₀ := h₀.tendsto_real_of_isClopen hAclopen
  have ht₁ := h₁.tendsto_real_of_isClopen hAclopen
  
  have hAmeas : MeasurableSet A := IsClopen.measurableSet_configSpace hAclopen
  have hdom : ∀ n,
      (freeFiniteMeasure d (ψ n) hp hp1 (zero_lt_one.trans_le hq)
          : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real A
        ≤ (wiredFiniteMeasure d (ψ n) hp hp1 (zero_lt_one.trans_le hq)
          : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real A :=
    fun n => freeFiniteMeasure_dominated d (ψ n) hp hp1 hq A hAmeas hAinc
  exact le_of_tendsto_of_tendsto ht₀ ht₁ (Filter.Eventually.of_forall hdom)






















theorem exists_common_subseq_weak_limits (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∃ (ψ : ℕ → ℕ) (ν₀ ν₁ : ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))),
      StrictMono ψ ∧
        WeakConvergesTo (fun n => freeFiniteMeasure d (ψ n) hp hp1 hq) ν₀ ∧
        WeakConvergesTo (fun n => wiredFiniteMeasure d (ψ n) hp hp1 hq) ν₁ := by
  obtain ⟨ν₀, φ, hφ, h₀⟩ :=
    prokhorov_seq_compact (fun n => freeFiniteMeasure d n hp hp1 hq)
  obtain ⟨ν₁, χ, hχ, h₁⟩ :=
    prokhorov_seq_compact (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
  exact ⟨φ ∘ χ, ν₀, ν₁, hφ.comp hχ, h₀.comp hχ.tendsto_atTop, h₁⟩























theorem exists_infiniteVolume_extremal (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    ∃ (ψ : ℕ → ℕ) (φ0 φ1 : ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))),
      StrictMono ψ ∧
        WeakConvergesTo
          (fun n => freeFiniteMeasure d (ψ n) hp hp1 (zero_lt_one.trans_le hq)) φ0 ∧
        WeakConvergesTo
          (fun n => wiredFiniteMeasure d (ψ n) hp hp1 (zero_lt_one.trans_le hq)) φ1 ∧
        ∀ A : Set (ConfigSpace (Sym2 (Lattice.Site d))),
          IsClopen A → IsIncreasing A →
            (φ0 : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real A
              ≤ (φ1 : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real A := by
  obtain ⟨ψ, ν₀, ν₁, hψ, h₀, h₁⟩ :=
    exists_common_subseq_weak_limits d hp hp1 (zero_lt_one.trans_le hq)
  refine ⟨ψ, ν₀, ν₁, hψ, h₀, h₁, ?_⟩
  intro A hAclopen hAinc
  exact weakLimit_extremality_of_common_subseq d hp hp1 hq h₀ h₁ hAclopen hAinc

end FK

end StatMech
