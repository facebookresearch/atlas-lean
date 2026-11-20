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
theorem radialCertificateAtIJ_2_0 : radialCertificateAtIJ 2 0 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_2_1 : radialCertificateAtIJ 2 1 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_2_2 : radialCertificateAtIJ 2 2 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_2_3 : radialCertificateAtIJ 2 3 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_2_4 : radialCertificateAtIJ 2 4 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_2_5 : radialCertificateAtIJ 2 5 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_2_6 : radialCertificateAtIJ 2 6 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_2_7 : radialCertificateAtIJ 2 7 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

theorem radialCertificateAt_two : radialCertificateAt 2 = true := by
  simp only [radialCertificateAt, List.all_eq_true, List.mem_finRange]
  intro j _
  fin_cases j
  · exact radialCertificateAtIJ_2_0
  · exact radialCertificateAtIJ_2_1
  · exact radialCertificateAtIJ_2_2
  · exact radialCertificateAtIJ_2_3
  · exact radialCertificateAtIJ_2_4
  · exact radialCertificateAtIJ_2_5
  · exact radialCertificateAtIJ_2_6
  · exact radialCertificateAtIJ_2_7

end StatMech.Ising.LowFaceCertificate
