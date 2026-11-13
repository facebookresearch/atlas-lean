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
theorem radialCertificateAtIJ_1_0 : radialCertificateAtIJ 1 0 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_1_1 : radialCertificateAtIJ 1 1 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_1_2 : radialCertificateAtIJ 1 2 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_1_3 : radialCertificateAtIJ 1 3 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_1_4 : radialCertificateAtIJ 1 4 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_1_5 : radialCertificateAtIJ 1 5 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_1_6 : radialCertificateAtIJ 1 6 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_1_7 : radialCertificateAtIJ 1 7 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

theorem radialCertificateAt_one : radialCertificateAt 1 = true := by
  simp only [radialCertificateAt, List.all_eq_true, List.mem_finRange]
  intro j _
  fin_cases j
  · exact radialCertificateAtIJ_1_0
  · exact radialCertificateAtIJ_1_1
  · exact radialCertificateAtIJ_1_2
  · exact radialCertificateAtIJ_1_3
  · exact radialCertificateAtIJ_1_4
  · exact radialCertificateAtIJ_1_5
  · exact radialCertificateAtIJ_1_6
  · exact radialCertificateAtIJ_1_7

end StatMech.Ising.LowFaceCertificate
