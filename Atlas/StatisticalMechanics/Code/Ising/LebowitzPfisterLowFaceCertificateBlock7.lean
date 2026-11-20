/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterLowFaceCertificateCore

namespace StatMech.Ising.LowFaceCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_7_0 : radialCertificateAtIJ 7 0 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_7_1 : radialCertificateAtIJ 7 1 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_7_2 : radialCertificateAtIJ 7 2 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_7_3 : radialCertificateAtIJ 7 3 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_7_4 : radialCertificateAtIJ 7 4 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_7_5 : radialCertificateAtIJ 7 5 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_7_6 : radialCertificateAtIJ 7 6 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_7_7 : radialCertificateAtIJ 7 7 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

theorem radialCertificateAt_seven : radialCertificateAt 7 = true := by
  simp only [radialCertificateAt, List.all_eq_true, List.mem_finRange]
  intro j _
  fin_cases j
  · exact radialCertificateAtIJ_7_0
  · exact radialCertificateAtIJ_7_1
  · exact radialCertificateAtIJ_7_2
  · exact radialCertificateAtIJ_7_3
  · exact radialCertificateAtIJ_7_4
  · exact radialCertificateAtIJ_7_5
  · exact radialCertificateAtIJ_7_6
  · exact radialCertificateAtIJ_7_7

end StatMech.Ising.LowFaceCertificate
