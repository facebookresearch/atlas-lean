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
theorem radialCertificateAtIJ_6_0 : radialCertificateAtIJ 6 0 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_6_1 : radialCertificateAtIJ 6 1 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_6_2 : radialCertificateAtIJ 6 2 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_6_3 : radialCertificateAtIJ 6 3 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_6_4 : radialCertificateAtIJ 6 4 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_6_5 : radialCertificateAtIJ 6 5 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_6_6 : radialCertificateAtIJ 6 6 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_6_7 : radialCertificateAtIJ 6 7 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

theorem radialCertificateAt_six : radialCertificateAt 6 = true := by
  simp only [radialCertificateAt, List.all_eq_true, List.mem_finRange]
  intro j _
  fin_cases j
  · exact radialCertificateAtIJ_6_0
  · exact radialCertificateAtIJ_6_1
  · exact radialCertificateAtIJ_6_2
  · exact radialCertificateAtIJ_6_3
  · exact radialCertificateAtIJ_6_4
  · exact radialCertificateAtIJ_6_5
  · exact radialCertificateAtIJ_6_6
  · exact radialCertificateAtIJ_6_7

end StatMech.Ising.LowFaceCertificate
