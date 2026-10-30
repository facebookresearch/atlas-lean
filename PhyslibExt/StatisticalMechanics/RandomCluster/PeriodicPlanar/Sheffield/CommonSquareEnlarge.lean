/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.ConnectorReadyCommonSquare

/-!
# Enlarging connector-ready common squares

Connector-ready common squares can be enlarged to any larger size, so a primal and a dual family
can be brought to the same square size.

## i. Overview

Given `E.ConnectorReadyCommonSquareData mu radius` with square sizes `M n` and any `M' n ≥ M n`,
each of the four sites is moved outward by `M' n - M n` along the axis normal to its side. The
buffered connectors still lie in the larger square `[-M' n, M' n]²`, and, by translation
invariance and monotonicity of side connections in the far sides of the rectangle, each box is
still connected to its own side with probability tending to `1`.

Applying this to a primal and a dual family with the common size `max (primal.M n) (dual.M n)`
gives two connector-ready families on one sequence of squares.

Headline fidelity. Both results are proved conditionally on translation invariance of the
measures (`hTI`, `hTIDual`) and on the given connector-ready data; nothing else is assumed.

## ii. Key results

- `PeriodicPlaneEmbedding.ConnectorReadyCommonSquareData.exists_enlarge` : enlarging a
  connector-ready family to any larger square size.
- `exists_commonHalfWidth_connectorReadyData` : primal and dual connector-ready families with
  the same square size.

## iii. Table of contents

- A. Enlarging one family
- B. A common size for primal and dual families

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. Enlarging one family -/

/-- A connector-ready common-square family for a translation invariant probability measure can be
enlarged to any larger square size `M' ≥ M`, keeping the connector radius. -/
theorem PeriodicPlaneEmbedding.ConnectorReadyCommonSquareData.exists_enlarge
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) {radius : Nat -> Nat}
    (data : E.ConnectorReadyCommonSquareData mu radius)
    (M' : Nat -> Nat) (hM : forall n, data.M n <= M' n) :
    exists enlarged : E.ConnectorReadyCommonSquareData mu radius,
      enlarged.M = M' := by
  let delta : Nat -> Nat := fun n => M' n - data.M n
  let zLeft : Nat -> Site 2 := fun n i =>
    if i = 0 then -(delta n : Int) else 0
  let zRight : Nat -> Site 2 := fun n i =>
    if i = 0 then (delta n : Int) else 0
  let zBottom : Nat -> Site 2 := fun n i =>
    if i = 1 then -(delta n : Int) else 0
  let zTop : Nat -> Site 2 := fun n i =>
    if i = 1 then (delta n : Int) else 0
  let baseLeft : Nat -> Site 2 := fun n => data.baseLeft n + zLeft n
  let baseRight : Nat -> Site 2 := fun n => data.baseRight n + zRight n
  let baseBottom : Nat -> Site 2 := fun n => data.baseBottom n + zBottom n
  let baseTop : Nat -> Site 2 := fun n => data.baseTop n + zTop n
  have hsum (n : Nat) : data.M n + delta n = M' n := by
    have hMn := hM n
    dsimp [delta]
    omega
  have hconnectorLeft (n : Nat) :
      P.shift (baseLeft n) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
        E.rectVertices (-(M' n : Real)) (M' n : Real)
          (-(M' n : Real)) (M' n : Real) := by
    rintro _ ⟨u, hu, rfl⟩
    have hold := data.connectorLeft n ⟨u, hu, rfl⟩
    rw [show baseLeft n = data.baseLeft n + zLeft n from rfl,
      P.shift_add]
    have hshift := (E.shift_mem_rectVertices (zLeft n)
      (-(data.M n : Real)) (data.M n : Real)
      (-(data.M n : Real)) (data.M n : Real)
      (P.shift (data.baseLeft n) u)).2 hold
    have hsumR : (data.M n : Real) + delta n = M' n := by
      exact_mod_cast hsum n
    have hcast : (data.M n : Real) <= M' n := by
      exact_mod_cast hM n
    refine E.rectVertices_mono ?_ ?_ ?_ ?_ hshift <;>
      simp only [Fin.isValue, one_ne_zero, ↓reduceIte, Int.cast_neg, Int.cast_natCast,
        Int.cast_zero, add_zero, le_add_neg_iff_add_le, neg_add_le_iff_le_add,
        add_neg_le_iff_le_add, neg_le_neg_iff, Nat.cast_le, zLeft] <;>
      first | exact_mod_cast hM n | linarith [hsumR, hcast]
  have hconnectorRight (n : Nat) :
      P.shift (baseRight n) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
        E.rectVertices (-(M' n : Real)) (M' n : Real)
          (-(M' n : Real)) (M' n : Real) := by
    rintro _ ⟨u, hu, rfl⟩
    have hold := data.connectorRight n ⟨u, hu, rfl⟩
    rw [show baseRight n = data.baseRight n + zRight n from rfl,
      P.shift_add]
    have hshift := (E.shift_mem_rectVertices (zRight n)
      (-(data.M n : Real)) (data.M n : Real)
      (-(data.M n : Real)) (data.M n : Real)
      (P.shift (data.baseRight n) u)).2 hold
    have hsumR : (data.M n : Real) + delta n = M' n := by
      exact_mod_cast hsum n
    have hcast : (data.M n : Real) <= M' n := by
      exact_mod_cast hM n
    refine E.rectVertices_mono ?_ ?_ ?_ ?_ hshift <;>
      simp only [Fin.isValue, one_ne_zero, ↓reduceIte, Int.cast_natCast, Int.cast_zero, add_zero,
        le_neg_add_iff_add_le, add_neg_le_iff_le_add, neg_le_neg_iff, Nat.cast_le, zRight] <;>
      first | exact_mod_cast hM n | linarith [hsumR, hcast]
  have hconnectorBottom (n : Nat) :
      P.shift (baseBottom n) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
        E.rectVertices (-(M' n : Real)) (M' n : Real)
          (-(M' n : Real)) (M' n : Real) := by
    rintro _ ⟨u, hu, rfl⟩
    have hold := data.connectorBottom n ⟨u, hu, rfl⟩
    rw [show baseBottom n = data.baseBottom n + zBottom n from rfl,
      P.shift_add]
    have hshift := (E.shift_mem_rectVertices (zBottom n)
      (-(data.M n : Real)) (data.M n : Real)
      (-(data.M n : Real)) (data.M n : Real)
      (P.shift (data.baseBottom n) u)).2 hold
    have hsumR : (data.M n : Real) + delta n = M' n := by
      exact_mod_cast hsum n
    have hcast : (data.M n : Real) <= M' n := by
      exact_mod_cast hM n
    refine E.rectVertices_mono ?_ ?_ ?_ ?_ hshift <;>
      simp only [Fin.isValue, zero_ne_one, ↓reduceIte, Int.cast_neg, Int.cast_natCast,
        Int.cast_zero, add_zero, le_add_neg_iff_add_le, neg_add_le_iff_le_add,
        add_neg_le_iff_le_add, neg_le_neg_iff, Nat.cast_le, zBottom] <;>
      first | exact_mod_cast hM n | linarith [hsumR, hcast]
  have hconnectorTop (n : Nat) :
      P.shift (baseTop n) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
        E.rectVertices (-(M' n : Real)) (M' n : Real)
          (-(M' n : Real)) (M' n : Real) := by
    rintro _ ⟨u, hu, rfl⟩
    have hold := data.connectorTop n ⟨u, hu, rfl⟩
    rw [show baseTop n = data.baseTop n + zTop n from rfl,
      P.shift_add]
    have hshift := (E.shift_mem_rectVertices (zTop n)
      (-(data.M n : Real)) (data.M n : Real)
      (-(data.M n : Real)) (data.M n : Real)
      (P.shift (data.baseTop n) u)).2 hold
    have hsumR : (data.M n : Real) + delta n = M' n := by
      exact_mod_cast hsum n
    have hcast : (data.M n : Real) <= M' n := by
      exact_mod_cast hM n
    refine E.rectVertices_mono ?_ ?_ ?_ ?_ hshift <;>
      simp only [Fin.isValue, zero_ne_one, ↓reduceIte, Int.cast_natCast, Int.cast_zero, add_zero,
        le_neg_add_iff_add_le, add_neg_le_iff_le_add, neg_le_neg_iff, Nat.cast_le, zTop] <;>
      first | exact_mod_cast hM n | linarith [hsumR, hcast]
  let left : Nat -> Real := fun n => mu.real
    (E.rectSideConnectionEvent (-(M' n : Real)) (M' n : Real)
      (-(M' n : Real)) (M' n : Real)
      (P.shift (baseLeft n) '' (P.orbitBox n : Set V))
      (E.rectLeftBoundaryVertices (-(M' n : Real)) (M' n : Real)
        (-(M' n : Real)) (M' n : Real)))
  have hleftLower (n : Nat) :
      mu.real (E.rectSideConnectionEvent
        (-(data.M n : Real)) (data.M n : Real)
        (-(data.M n : Real)) (data.M n : Real)
        (P.shift (data.baseLeft n) '' (P.orbitBox n : Set V))
        (E.rectLeftBoundaryVertices
          (-(data.M n : Real)) (data.M n : Real)
          (-(data.M n : Real)) (data.M n : Real))) <= left n := by
    have ht := E.rectLeftConnection_translate_measureReal_eq mu hTI
      (zLeft n) (-(data.M n : Real)) (data.M n : Real)
      (-(data.M n : Real)) (data.M n : Real)
      (P.shift (data.baseLeft n) '' (P.orbitBox n : Set V))
    have himage : P.shift (zLeft n) ''
        (P.shift (data.baseLeft n) '' (P.orbitBox n : Set V)) =
          P.shift (baseLeft n) '' (P.orbitBox n : Set V) := by
      rw [P.shift_image_shift]
    have hactive : -(data.M n : Real) + (zLeft n 0 : Int) =
        -(M' n : Real) := by
      have hsumR : (data.M n : Real) + delta n = M' n := by
        exact_mod_cast hsum n
      simp [zLeft]
      linarith
    rw [himage] at ht
    rw [← ht, hactive]
    have hcast : (data.M n : Real) <= M' n := by
      exact_mod_cast hM n
    exact measureReal_mono
      (E.rectLeftConnectionEvent_mono_otherBounds _
        (by simp [zLeft]; linarith [hcast])
        (by simpa [zLeft] using hcast)
        (by simpa [zLeft] using hcast))
  have hleftLimit : Tendsto left atTop (nhds 1) :=
    data.leftLimit.squeeze tendsto_const_nhds hleftLower
      (fun n => measureReal_le_one)
  
  let right : Nat -> Real := fun n => mu.real
    (E.rectSideConnectionEvent (-(M' n : Real)) (M' n : Real)
      (-(M' n : Real)) (M' n : Real)
      (P.shift (baseRight n) '' (P.orbitBox n : Set V))
      (E.rectRightBoundaryVertices (-(M' n : Real)) (M' n : Real)
        (-(M' n : Real)) (M' n : Real)))
  let bottom : Nat -> Real := fun n => mu.real
    (E.rectSideConnectionEvent (-(M' n : Real)) (M' n : Real)
      (-(M' n : Real)) (M' n : Real)
      (P.shift (baseBottom n) '' (P.orbitBox n : Set V))
      (E.rectBottomBoundaryVertices (-(M' n : Real)) (M' n : Real)
        (-(M' n : Real)) (M' n : Real)))
  let top : Nat -> Real := fun n => mu.real
    (E.rectSideConnectionEvent (-(M' n : Real)) (M' n : Real)
      (-(M' n : Real)) (M' n : Real)
      (P.shift (baseTop n) '' (P.orbitBox n : Set V))
      (E.rectTopBoundaryVertices (-(M' n : Real)) (M' n : Real)
        (-(M' n : Real)) (M' n : Real)))
  have hrightLower (n : Nat) :
      mu.real (E.rectSideConnectionEvent
        (-(data.M n : Real)) (data.M n : Real)
        (-(data.M n : Real)) (data.M n : Real)
        (P.shift (data.baseRight n) '' (P.orbitBox n : Set V))
        (E.rectRightBoundaryVertices
          (-(data.M n : Real)) (data.M n : Real)
          (-(data.M n : Real)) (data.M n : Real))) <= right n := by
    have ht := E.rectRightConnection_translate_measureReal_eq mu hTI
      (zRight n) (-(data.M n : Real)) (data.M n : Real)
      (-(data.M n : Real)) (data.M n : Real)
      (P.shift (data.baseRight n) '' (P.orbitBox n : Set V))
    have himage : P.shift (zRight n) ''
        (P.shift (data.baseRight n) '' (P.orbitBox n : Set V)) =
          P.shift (baseRight n) '' (P.orbitBox n : Set V) := by
      rw [P.shift_image_shift]
    have hactive : (data.M n : Real) + (zRight n 0 : Int) =
        (M' n : Real) := by
      have hsumR : (data.M n : Real) + delta n = M' n := by
        exact_mod_cast hsum n
      simp [zRight]
      linarith
    rw [himage] at ht
    rw [← ht, hactive]
    have hcast : (data.M n : Real) <= M' n := by
      exact_mod_cast hM n
    exact measureReal_mono
      (E.rectRightConnectionEvent_mono_otherBounds _
        (by simp [zRight]; linarith [hcast])
        (by simpa [zRight] using hcast)
        (by simpa [zRight] using hcast))
  have hbottomLower (n : Nat) :
      mu.real (E.rectSideConnectionEvent
        (-(data.M n : Real)) (data.M n : Real)
        (-(data.M n : Real)) (data.M n : Real)
        (P.shift (data.baseBottom n) '' (P.orbitBox n : Set V))
        (E.rectBottomBoundaryVertices
          (-(data.M n : Real)) (data.M n : Real)
          (-(data.M n : Real)) (data.M n : Real))) <= bottom n := by
    have ht := E.rectBottomConnection_translate_measureReal_eq mu hTI
      (zBottom n) (-(data.M n : Real)) (data.M n : Real)
      (-(data.M n : Real)) (data.M n : Real)
      (P.shift (data.baseBottom n) '' (P.orbitBox n : Set V))
    have himage : P.shift (zBottom n) ''
        (P.shift (data.baseBottom n) '' (P.orbitBox n : Set V)) =
          P.shift (baseBottom n) '' (P.orbitBox n : Set V) := by
      rw [P.shift_image_shift]
    have hactive : -(data.M n : Real) + (zBottom n 1 : Int) =
        -(M' n : Real) := by
      have hsumR : (data.M n : Real) + delta n = M' n := by
        exact_mod_cast hsum n
      simp [zBottom]
      linarith
    rw [himage] at ht
    rw [← ht, hactive]
    have hcast : (data.M n : Real) <= M' n := by
      exact_mod_cast hM n
    exact measureReal_mono
      (E.rectBottomConnectionEvent_mono_otherBounds _
        (by simpa [zBottom] using hcast)
        (by simpa [zBottom] using hcast)
        (by simp [zBottom]; linarith [hcast]))
  have htopLower (n : Nat) :
      mu.real (E.rectSideConnectionEvent
        (-(data.M n : Real)) (data.M n : Real)
        (-(data.M n : Real)) (data.M n : Real)
        (P.shift (data.baseTop n) '' (P.orbitBox n : Set V))
        (E.rectTopBoundaryVertices
          (-(data.M n : Real)) (data.M n : Real)
          (-(data.M n : Real)) (data.M n : Real))) <= top n := by
    have ht := E.rectTopConnection_translate_measureReal_eq mu hTI
      (zTop n) (-(data.M n : Real)) (data.M n : Real)
      (-(data.M n : Real)) (data.M n : Real)
      (P.shift (data.baseTop n) '' (P.orbitBox n : Set V))
    have himage : P.shift (zTop n) ''
        (P.shift (data.baseTop n) '' (P.orbitBox n : Set V)) =
          P.shift (baseTop n) '' (P.orbitBox n : Set V) := by
      rw [P.shift_image_shift]
    have hactive : (data.M n : Real) + (zTop n 1 : Int) =
        (M' n : Real) := by
      have hsumR : (data.M n : Real) + delta n = M' n := by
        exact_mod_cast hsum n
      simp [zTop]
      linarith
    rw [himage] at ht
    rw [← ht, hactive]
    have hcast : (data.M n : Real) <= M' n := by
      exact_mod_cast hM n
    exact measureReal_mono
      (E.rectTopConnectionEvent_mono_otherBounds _
        (by simpa [zTop] using hcast)
        (by simpa [zTop] using hcast)
        (by simp [zTop]; linarith [hcast]))
  have hrightLimit : Tendsto right atTop (nhds 1) :=
    data.rightLimit.squeeze tendsto_const_nhds hrightLower
      (fun n => measureReal_le_one)
  have hbottomLimit : Tendsto bottom atTop (nhds 1) :=
    data.bottomLimit.squeeze tendsto_const_nhds hbottomLower
      (fun n => measureReal_le_one)
  have htopLimit : Tendsto top atTop (nhds 1) :=
    data.topLimit.squeeze tendsto_const_nhds htopLower
      (fun n => measureReal_le_one)
  refine ⟨{
    M := M'
    baseLeft := baseLeft
    baseRight := baseRight
    baseBottom := baseBottom
    baseTop := baseTop
    connectorLeft := hconnectorLeft
    connectorRight := hconnectorRight
    connectorBottom := hconnectorBottom
    connectorTop := hconnectorTop
    leftLimit := hleftLimit
    rightLimit := hrightLimit
    bottomLimit := hbottomLimit
    topLimit := htopLimit }, rfl⟩

/-! ## B. A common size for primal and dual families -/

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

/-- Primal and dual connector-ready families, for translation invariant probability measures, can be
enlarged to the common square size `max (primal.M n) (dual.M n)`. -/
theorem exists_commonHalfWidth_connectorReadyData
    (E : PeriodicPlaneEmbedding P)
    (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))} [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {radius radiusDual : Nat -> Nat}
    (primal : E.ConnectorReadyCommonSquareData mu radius)
    (dual : Edual.ConnectorReadyCommonSquareData muDual radiusDual) :
    let commonM : Nat -> Nat := fun n => max (primal.M n) (dual.M n)
    exists primal' : E.ConnectorReadyCommonSquareData mu radius,
      exists dual' : Edual.ConnectorReadyCommonSquareData muDual radiusDual,
        primal'.M = commonM ∧ dual'.M = commonM := by
  let commonM : Nat -> Nat := fun n => max (primal.M n) (dual.M n)
  obtain ⟨primal', hp⟩ := primal.exists_enlarge E hTI commonM
    (fun n => Nat.le_max_left _ _)
  obtain ⟨dual', hd⟩ := dual.exists_enlarge Edual hTIDual commonM
    (fun n => Nat.le_max_right _ _)
  exact ⟨primal', dual', hp, hd⟩

end StatMech.FK.PeriodicPlanar
