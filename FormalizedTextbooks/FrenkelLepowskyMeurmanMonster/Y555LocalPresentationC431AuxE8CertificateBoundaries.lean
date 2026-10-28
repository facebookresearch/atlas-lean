/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual boundaries of the bounded E8 certificates in the original C431 source group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChunks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8CertificateIndices

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- This finite check compares only the literal adjacent words inside each declared certificate.
/-- Every continuing chunk ends at the exact next chunk's initial word. -/
theorem y431AuxE8RewriteChunk_adjacent (i : Fin 1213)
    (h : y431AuxE8ChunkContinues i.castSucc = true) :
    (y431AuxE8RewriteChunk i.castSucc).2.1 = (y431AuxE8RewriteChunk i.succ).1 := by
  revert i h
  decide +kernel

/-- The final global chunk belonging to each exact normalization certificate. -/
def y431AuxE8CertificateEnd (c : Fin 574) : Fin 1214 :=
  ⟨y431AuxE8CertificateStart c + y431AuxE8CertificateLength c - 1, by
    have h := y431AuxE8Certificate_bounds c
    omega⟩

/-- Every boundary is the next chunk's initial word, except the final proved output word. -/
def y431AuxE8CertificateBoundary (c : Fin 574)
    (i : Fin (y431AuxE8CertificateLength c + 1)) : List (Fin 9) :=
  if h : i.val < y431AuxE8CertificateLength c then
    (y431AuxE8RewriteChunk (y431AuxE8CertificateRow c ⟨i.val, h⟩)).1
  else (y431AuxE8RewriteChunk (y431AuxE8CertificateEnd c)).2.1

/-- Each local chunk's finite moves, preserving the exact declared global ordering. -/
def y431AuxE8CertificateMoves (c : Fin 574)
    (i : Fin (y431AuxE8CertificateLength c)) : List Y431CoxeterMove :=
  (y431AuxE8RewriteChunk (y431AuxE8CertificateRow c i)).2.2

set_option maxRecDepth 100000 in
/-- Every move chain connects its two actual adjacent original-source boundaries. -/
theorem y431AuxE8CertificateBoundary_checked (c : Fin 574)
    (i : Fin (y431AuxE8CertificateLength c)) :
    y431CoxeterRun (y431AuxE8CertificateMoves c i)
      (y431AuxE8CertificateBoundary c i.castSucc) =
      some (y431AuxE8CertificateBoundary c i.succ) := by
  have hc := y431AuxE8RewriteChunk_checked (y431AuxE8CertificateRow c i)
  have hb := y431AuxE8Certificate_bounds c
  simp only [y431AuxE8CertificateMoves, y431AuxE8CertificateBoundary,
    Fin.val_castSucc, Fin.val_succ, dite_eq_left i.isLt]
  by_cases hs : i.val + 1 < y431AuxE8CertificateLength c
  · rw [dite_eq_left hs]
    have hj : y431AuxE8CertificateStart c + i.val < 1213 := by omega
    have hf := y431AuxE8Certificate_continues c i hs
    have ha := y431AuxE8RewriteChunk_adjacent
      (⟨y431AuxE8CertificateStart c + i.val, hj⟩ : Fin 1213) hf
    exact hc.trans (congrArg some ha)
  · rw [dite_eq_right hs]
    have he : y431AuxE8CertificateRow c i = y431AuxE8CertificateEnd c := by
      apply Fin.ext
      change y431AuxE8CertificateStart c + i.val =
        y431AuxE8CertificateStart c + y431AuxE8CertificateLength c - 1
      omega
    simpa only [he] using hc

set_option maxRecDepth 100000 in
/-- Each entire normalization certificate is an actual equality in the original C431 group. -/
theorem y431AuxE8Certificate_valid (c : Fin 574) :
    y431PositiveWord (y431AuxE8CertificateBoundary c 0) =
      y431PositiveWord
        (y431AuxE8CertificateBoundary c (Fin.last (y431AuxE8CertificateLength c))) :=
  y431CoxeterChain_valid (y431AuxE8CertificateBoundary c) (y431AuxE8CertificateMoves c)
    (y431AuxE8CertificateBoundary_checked c)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
