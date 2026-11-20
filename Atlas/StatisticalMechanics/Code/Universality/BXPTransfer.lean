/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib
import Code.Universality.Defs
import Code.Universality.STT
import Code.Universality.STTTransport

open MeasureTheory Set
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim











theorem boxCrossingProbabilities_nonempty
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) (n0 : ℕ) :
    (boxCrossingProbabilities μ ρ n0).Nonempty :=
  ⟨_, n0, 0, le_refl _, Or.inl rfl⟩



theorem boxCrossingProbabilities_bddBelow
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) (n0 : ℕ) :
    BddBelow (boxCrossingProbabilities μ ρ n0) := by
  refine ⟨0, ?_⟩
  rintro z ⟨n, τ, hn, rfl | rfl⟩ <;> exact measureReal_nonneg


theorem boxCrossingProbabilities_mem_Icc
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (ρ : ℝ) (n0 : ℕ) {x : ℝ} (hx : x ∈ boxCrossingProbabilities μ ρ n0) :
    x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨n, τ, hn, h⟩ := hx
  rcases h with rfl | rfl <;> exact ⟨measureReal_nonneg, measureReal_le_one⟩





theorem boxCrossingProbabilities_subset
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) {n0 n0' : ℕ} (h : n0 ≤ n0') :
    boxCrossingProbabilities μ ρ n0' ⊆ boxCrossingProbabilities μ ρ n0 := by
  rintro x ⟨n, τ, hn, hcase⟩
  exact ⟨n, τ, le_trans h hn, hcase⟩






theorem boxCrossingInf_mono
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) {n0 n0' : ℕ} (h : n0 ≤ n0') :
    boxCrossingInf μ ρ n0 ≤ boxCrossingInf μ ρ n0' := by
  unfold boxCrossingInf
  refine csInf_le_csInf (boxCrossingProbabilities_bddBelow μ ρ n0)
    (boxCrossingProbabilities_nonempty μ ρ n0') (boxCrossingProbabilities_subset μ ρ h)



















theorem bxp_transfer_core
    (μsrc μtgt : Measure (ConfigSpace (Sym2 (Site 2))))
    (ρsrc ρtgt : ℝ) (n0src n0tgt : ℕ) (hρ : 1 < ρsrc)
    (htgt : 0 < boxCrossingInf μtgt ρtgt n0tgt)
    (hcmp : ∀ x ∈ boxCrossingProbabilities μsrc ρsrc n0src,
        ∃ y ∈ boxCrossingProbabilities μtgt ρtgt n0tgt, y ≤ x) :
    BoxCrossingProperty μsrc ρsrc := by
  refine ⟨hρ, n0src, ?_⟩
  unfold boxCrossingInf at htgt ⊢
  have hSne := boxCrossingProbabilities_nonempty μsrc ρsrc n0src
  have hTbdd := boxCrossingProbabilities_bddBelow μtgt ρtgt n0tgt
  refine lt_of_lt_of_le htgt (le_csInf hSne ?_)
  intro x hx
  obtain ⟨y, hyT, hyx⟩ := hcmp x hx
  exact le_trans (csInf_le hTbdd hyT) hyx







































structure CrossingTransportData
    (μsq μtri : Measure (ConfigSpace (Sym2 (Site 2))))
    (ρsq ρtri : ℝ) : Prop where
  
  one_lt_ρsq : 1 < ρsq
  
  one_lt_ρtri : 1 < ρtri
  



  sqDominatedByTri : ∀ n0 : ℕ, ∀ x ∈ boxCrossingProbabilities μsq ρsq n0,
      ∃ y ∈ boxCrossingProbabilities μtri ρtri n0, y ≤ x
  


  triDominatedBySq : ∀ n0 : ℕ, ∀ x ∈ boxCrossingProbabilities μtri ρtri n0,
      ∃ y ∈ boxCrossingProbabilities μsq ρsq n0, y ≤ x











theorem bxp_square_of_triangular
    {μsq μtri : Measure (ConfigSpace (Sym2 (Site 2)))} {ρsq ρtri : ℝ}
    (hdata : CrossingTransportData μsq μtri ρsq ρtri)
    (htri : BoxCrossingProperty μtri ρtri) :
    BoxCrossingProperty μsq ρsq := by
  obtain ⟨_, n0, hpos⟩ := htri
  exact bxp_transfer_core μsq μtri ρsq ρtri n0 n0 hdata.one_lt_ρsq hpos
    (hdata.sqDominatedByTri n0)







theorem bxp_triangular_of_square
    {μsq μtri : Measure (ConfigSpace (Sym2 (Site 2)))} {ρsq ρtri : ℝ}
    (hdata : CrossingTransportData μsq μtri ρsq ρtri)
    (hsq : BoxCrossingProperty μsq ρsq) :
    BoxCrossingProperty μtri ρtri := by
  obtain ⟨_, n0, hpos⟩ := hsq
  exact bxp_transfer_core μtri μsq ρtri ρsq n0 n0 hdata.one_lt_ρtri hpos
    (hdata.triDominatedBySq n0)















theorem bxp_square_iff_triangular
    {μsq μtri : Measure (ConfigSpace (Sym2 (Site 2)))} {ρsq ρtri : ℝ}
    {p0 p1 p2 : ℝ} (hcrit : IsCriticalTri p0 p1 p2)
    (hdata : CrossingTransportData μsq μtri ρsq ρtri) :
    BoxCrossingProperty μsq ρsq ↔ BoxCrossingProperty μtri ρtri := by
  
  
  
  
  
  have _hconn := starTriangle_connectivity p0 p1 p2 hcrit
  exact ⟨bxp_triangular_of_square hdata, bxp_square_of_triangular hdata⟩

end Universality

end StatMech
