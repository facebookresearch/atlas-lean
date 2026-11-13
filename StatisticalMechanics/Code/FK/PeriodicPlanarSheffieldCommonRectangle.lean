/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FK.PeriodicPlanarSheffieldBoundaryEnlargement
import Code.FK.PeriodicPlanarSheffieldRectangleTranslation

open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

def commonRectLeftShift (M : Nat → Nat) (N : Nat) : Site 2 :=
  fun i => if i = 0 then -(M N : Int) else 0

def commonRectRightShift (M : Nat → Nat) (N : Nat) : Site 2 :=
  fun i => if i = 0 then (M N : Int) else 0

def commonRectBottomShift (M : Nat → Nat) (N : Nat) : Site 2 :=
  fun i => if i = 1 then -(M N : Int) else 0

def commonRectTopShift (M : Nat → Nat) (N : Nat) : Site 2 :=
  fun i => if i = 1 then (M N : Int) else 0





theorem PeriodicPlaneEmbedding.exists_commonSquare_fourBoundaryPlacements
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (buffer : Nat → Nat) (hbuffer : ∀ N, N ≤ buffer N) :
    ∃ (M : Nat → Nat)
      (baseL baseR baseB baseT : Nat → Site 2),
      (∀ N, P.shift (commonRectLeftShift M N) ''
          (P.shift (baseL N) '' (P.orbitBox (buffer N) : Set V)) ⊆
        E.rectVertices (-(M N : Real)) (M N : Real)
          (-(M N : Real)) (M N : Real)) ∧
      (∀ N, P.shift (commonRectRightShift M N) ''
          (P.shift (baseR N) '' (P.orbitBox (buffer N) : Set V)) ⊆
        E.rectVertices (-(M N : Real)) (M N : Real)
          (-(M N : Real)) (M N : Real)) ∧
      (∀ N, P.shift (commonRectBottomShift M N) ''
          (P.shift (baseB N) '' (P.orbitBox (buffer N) : Set V)) ⊆
        E.rectVertices (-(M N : Real)) (M N : Real)
          (-(M N : Real)) (M N : Real)) ∧
      (∀ N, P.shift (commonRectTopShift M N) ''
          (P.shift (baseT N) '' (P.orbitBox (buffer N) : Set V)) ⊆
        E.rectVertices (-(M N : Real)) (M N : Real)
          (-(M N : Real)) (M N : Real)) ∧
      Tendsto (fun N => mu.real
        (E.rectSideConnectionEvent (-(M N : Real)) (M N : Real)
          (-(M N : Real)) (M N : Real)
          (P.shift (commonRectLeftShift M N) ''
            (P.shift (baseL N) '' (P.orbitBox N : Set V)))
          (E.rectLeftBoundaryVertices (-(M N : Real)) (M N : Real)
            (-(M N : Real)) (M N : Real)))) atTop (nhds 1) ∧
      Tendsto (fun N => mu.real
        (E.rectSideConnectionEvent (-(M N : Real)) (M N : Real)
          (-(M N : Real)) (M N : Real)
          (P.shift (commonRectRightShift M N) ''
            (P.shift (baseR N) '' (P.orbitBox N : Set V)))
          (E.rectRightBoundaryVertices (-(M N : Real)) (M N : Real)
            (-(M N : Real)) (M N : Real)))) atTop (nhds 1) ∧
      Tendsto (fun N => mu.real
        (E.rectSideConnectionEvent (-(M N : Real)) (M N : Real)
          (-(M N : Real)) (M N : Real)
          (P.shift (commonRectBottomShift M N) ''
            (P.shift (baseB N) '' (P.orbitBox N : Set V)))
          (E.rectBottomBoundaryVertices (-(M N : Real)) (M N : Real)
            (-(M N : Real)) (M N : Real)))) atTop (nhds 1) ∧
      Tendsto (fun N => mu.real
        (E.rectSideConnectionEvent (-(M N : Real)) (M N : Real)
          (-(M N : Real)) (M N : Real)
          (P.shift (commonRectTopShift M N) ''
            (P.shift (baseT N) '' (P.orbitBox N : Set V)))
          (E.rectTopBoundaryVertices (-(M N : Real)) (M N : Real)
            (-(M N : Real)) (M N : Real)))) atTop (nhds 1) := by
  obtain ⟨baseL, radiusL, hleft⟩ :=
    E.exists_buffered_leftBoundaryPlacement_enlargeable
      mu hFKG hTI hunique buffer hbuffer 0
  obtain ⟨baseR, radiusR, hright⟩ :=
    E.exists_buffered_rightBoundaryPlacement_enlargeable
      mu hFKG hTI hunique buffer hbuffer 0
  obtain ⟨baseB, radiusB, hbottom⟩ :=
    E.exists_buffered_bottomBoundaryPlacement_enlargeable
      mu hFKG hTI hunique buffer hbuffer 0
  obtain ⟨baseT, radiusT, htop⟩ :=
    E.exists_buffered_topBoundaryPlacement_enlargeable
      mu hFKG hTI hunique buffer hbuffer 0
  let M : Nat → Nat := fun N =>
    max (max (radiusL N) (radiusR N)) (max (radiusB N) (radiusT N))
  have hL (N : Nat) : radiusL N ≤ M N := by simp [M]
  have hR (N : Nat) : radiusR N ≤ M N := by simp [M]
  have hB (N : Nat) : radiusB N ≤ M N := by simp [M]
  have hT (N : Nat) : radiusT N ≤ M N := by simp [M]
  have leftData := hleft
    (fun N => 2 * (M N : Real))
    (fun N => -(M N : Real)) (fun N => (M N : Real))
    (by
      intro N
      have h : (radiusL N : Real) ≤ M N := by
        exact_mod_cast hL N
      dsimp
      linarith)
    (by
      intro N
      have h : (radiusL N : Real) ≤ M N := by
        exact_mod_cast hL N
      dsimp
      linarith)
    (by intro N; change (radiusL N : Real) ≤ M N; exact_mod_cast hL N)
  have rightData := hright
    (fun N => -(2 * (M N : Real)))
    (fun N => -(M N : Real)) (fun N => (M N : Real))
    (by
      intro N
      have h : (radiusR N : Real) ≤ M N := by
        exact_mod_cast hR N
      dsimp
      linarith)
    (by
      intro N
      have h : (radiusR N : Real) ≤ M N := by
        exact_mod_cast hR N
      dsimp
      linarith)
    (by intro N; change (radiusR N : Real) ≤ M N; exact_mod_cast hR N)
  have bottomData := hbottom
    (fun N => -(M N : Real)) (fun N => (M N : Real))
    (fun N => 2 * (M N : Real))
    (by
      intro N
      have h : (radiusB N : Real) ≤ M N := by
        exact_mod_cast hB N
      dsimp
      linarith)
    (by intro N; change (radiusB N : Real) ≤ M N; exact_mod_cast hB N)
    (by
      intro N
      have h : (radiusB N : Real) ≤ M N := by
        exact_mod_cast hB N
      dsimp
      linarith)
  have topData := htop
    (fun N => -(M N : Real)) (fun N => (M N : Real))
    (fun N => -(2 * (M N : Real)))
    (by
      intro N
      have h : (radiusT N : Real) ≤ M N := by
        exact_mod_cast hT N
      dsimp
      linarith)
    (by intro N; change (radiusT N : Real) ≤ M N; exact_mod_cast hT N)
    (by
      intro N
      have h : (radiusT N : Real) ≤ M N := by
        exact_mod_cast hT N
      dsimp
      linarith)
  refine ⟨M, baseL, baseR, baseB, baseT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : y ∈ E.rectVertices 0 (2 * (M N : Real))
        (-(M N : Real)) (M N : Real) := by simpa using leftData.1 N hy
    have hmem := (E.shift_mem_rectVertices (commonRectLeftShift M N)
      0 (2 * M N) (-(M N : Real)) (M N : Real) y).2
        hy'
    convert hmem using 1 <;> simp [commonRectLeftShift] <;> ring_nf
  · intro N x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : y ∈ E.rectVertices (-(2 * (M N : Real))) 0
        (-(M N : Real)) (M N : Real) := by simpa using rightData.1 N hy
    have hmem := (E.shift_mem_rectVertices (commonRectRightShift M N)
      (-(2 * (M N : Real))) 0 (-(M N : Real)) (M N : Real) y).2
        hy'
    convert hmem using 1 <;> simp [commonRectRightShift] <;> ring_nf
  · intro N x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : y ∈ E.rectVertices (-(M N : Real)) (M N : Real)
        0 (2 * (M N : Real)) := by simpa using bottomData.1 N hy
    have hmem := (E.shift_mem_rectVertices (commonRectBottomShift M N)
      (-(M N : Real)) (M N : Real) 0 (2 * M N) y).2
        hy'
    convert hmem using 1 <;> simp [commonRectBottomShift] <;> ring_nf
  · intro N x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : y ∈ E.rectVertices (-(M N : Real)) (M N : Real)
        (-(2 * (M N : Real))) 0 := by simpa using topData.1 N hy
    have hmem := (E.shift_mem_rectVertices (commonRectTopShift M N)
      (-(M N : Real)) (M N : Real) (-(2 * (M N : Real))) 0 y).2
        hy'
    convert hmem using 1 <;> simp [commonRectTopShift] <;> ring_nf
  · apply leftData.2.congr'
    filter_upwards with N
    symm
    have h := E.rectLeftConnection_translate_measureReal_eq mu hTI
        (commonRectLeftShift M N) 0 (2 * M N)
          (-(M N : Real)) (M N : Real)
          (P.shift (baseL N) '' (P.orbitBox N : Set V))
    convert h using 1 <;> simp [commonRectLeftShift] <;> ring_nf
  · apply rightData.2.congr'
    filter_upwards with N
    symm
    have h := E.rectRightConnection_translate_measureReal_eq mu hTI
        (commonRectRightShift M N) (-(2 * (M N : Real))) 0
          (-(M N : Real)) (M N : Real)
          (P.shift (baseR N) '' (P.orbitBox N : Set V))
    convert h using 1 <;> simp [commonRectRightShift] <;> ring_nf
  · apply bottomData.2.congr'
    filter_upwards with N
    symm
    have h := E.rectBottomConnection_translate_measureReal_eq mu hTI
        (commonRectBottomShift M N) (-(M N : Real)) (M N : Real)
          0 (2 * M N)
          (P.shift (baseB N) '' (P.orbitBox N : Set V))
    convert h using 1 <;> simp [commonRectBottomShift] <;> ring_nf
  · apply topData.2.congr'
    filter_upwards with N
    symm
    have h := E.rectTopConnection_translate_measureReal_eq mu hTI
        (commonRectTopShift M N) (-(M N : Real)) (M N : Real)
          (-(2 * (M N : Real))) 0
          (P.shift (baseT N) '' (P.orbitBox N : Set V))
    convert h using 1 <;> simp [commonRectTopShift] <;> ring_nf

end StatMech.FK.PeriodicPlanar
