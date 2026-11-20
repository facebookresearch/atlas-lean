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
theorem radialCertificateAtIJ_5_0 : radialCertificateAtIJ 5 0 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_5_1 : radialCertificateAtIJ 5 1 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_5_2 : radialCertificateAtIJ 5 2 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_5_3 : radialCertificateAtIJ 5 3 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_5_4 : radialCertificateAtIJ 5 4 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_5_5 : radialCertificateAtIJ 5 5 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_5_6 : radialCertificateAtIJ 5 6 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem radialCertificateAtIJ_5_7 : radialCertificateAtIJ 5 7 = true := by
  simp only [radialCertificateAtIJ, List.all_eq_true, List.mem_finRange]
  intro k _
  fin_cases k <;> decide

theorem radialCertificateAt_five : radialCertificateAt 5 = true := by
  simp only [radialCertificateAt, List.all_eq_true, List.mem_finRange]
  intro j _
  fin_cases j
  · exact radialCertificateAtIJ_5_0
  · exact radialCertificateAtIJ_5_1
  · exact radialCertificateAtIJ_5_2
  · exact radialCertificateAtIJ_5_3
  · exact radialCertificateAtIJ_5_4
  · exact radialCertificateAtIJ_5_5
  · exact radialCertificateAtIJ_5_6
  · exact radialCertificateAtIJ_5_7

end StatMech.Ising.LowFaceCertificate
