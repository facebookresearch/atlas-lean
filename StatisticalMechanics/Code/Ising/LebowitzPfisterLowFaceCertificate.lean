/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterLowFaceCertificateBlock0
import Code.Ising.LebowitzPfisterLowFaceCertificateBlock1
import Code.Ising.LebowitzPfisterLowFaceCertificateBlock2
import Code.Ising.LebowitzPfisterLowFaceCertificateBlock3
import Code.Ising.LebowitzPfisterLowFaceCertificateBlock4
import Code.Ising.LebowitzPfisterLowFaceCertificateBlock5
import Code.Ising.LebowitzPfisterLowFaceCertificateBlock6
import Code.Ising.LebowitzPfisterLowFaceCertificateBlock7
import Code.Ising.LebowitzPfisterLowFaceBoundsBlock0
import Code.Ising.LebowitzPfisterLowFaceBoundsBlock1
import Code.Ising.LebowitzPfisterLowFaceBoundsBlock2
import Code.Ising.LebowitzPfisterLowFaceBoundsBlock3
import Code.Ising.LebowitzPfisterLowFaceBoundsBlock4
import Code.Ising.LebowitzPfisterLowFaceBoundsBlock5
import Code.Ising.LebowitzPfisterLowFaceBoundsBlock6
import Code.Ising.LebowitzPfisterLowFaceBoundsBlock7









namespace StatMech.Ising.LowFaceCertificate

theorem radialBernCoeff_nonneg :
    ∀ (i j k : Fin 8) (a : Fin 13) (b : Fin 8) (c : Fin 4),
      0 <= radialBernCoeff i j k a b c := by
  intro i j k a b c
  have hi : radialCertificateAt i = true := by
    fin_cases i
    · exact radialCertificateAt_zero
    · exact radialCertificateAt_one
    · exact radialCertificateAt_two
    · exact radialCertificateAt_three
    · exact radialCertificateAt_four
    · exact radialCertificateAt_five
    · exact radialCertificateAt_six
    · exact radialCertificateAt_seven
  simp only [radialCertificateAt, radialCertificateAtIJ,
    radialCertificateFor, List.all_eq_true, List.mem_finRange,
    decide_eq_true_eq] at hi
  exact hi j trivial k trivial a trivial b trivial c trivial

theorem radializedCrossCoeff_bounds :
    ∀ (i j k : Fin 8) (t : TriTerm),
      t ∈ (radialize (crossCoeffPoly i j k)).terms ->
        t.ex <= 6 ∧ t.ey <= 6 ∧ t.ez <= 3 := by
  intro i
  fin_cases i
  · exact radializedCrossCoeff_bounds_at_zero
  · exact radializedCrossCoeff_bounds_at_one
  · exact radializedCrossCoeff_bounds_at_two
  · exact radializedCrossCoeff_bounds_at_three
  · exact radializedCrossCoeff_bounds_at_four
  · exact radializedCrossCoeff_bounds_at_five
  · exact radializedCrossCoeff_bounds_at_six
  · exact radializedCrossCoeff_bounds_at_seven

theorem crossCoeff_bounds :
    ∀ (i j k : Fin 8) (t : TriTerm),
      t ∈ (crossCoeffPoly i j k).terms ->
        3 <= t.ex + t.ey + t.ez ∧ t.ex + t.ey + t.ez <= 6 := by
  intro i
  fin_cases i
  · exact crossCoeff_bounds_at_zero
  · exact crossCoeff_bounds_at_one
  · exact crossCoeff_bounds_at_two
  · exact crossCoeff_bounds_at_three
  · exact crossCoeff_bounds_at_four
  · exact crossCoeff_bounds_at_five
  · exact crossCoeff_bounds_at_six
  · exact crossCoeff_bounds_at_seven

end StatMech.Ising.LowFaceCertificate
