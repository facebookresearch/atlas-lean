/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldVariablePadding










open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PairedMixedBoundaryScores

noncomputable def primalBottomSource
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    Finset V :=
  S.image (P.shift (data.base + preferenceGridSite
    ((0 : Fin (data.width + 1)), (0 : Fin (data.height + 1)))))

noncomputable def primalTopSource
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    Finset V :=
  S.image (P.shift (data.base + preferenceGridSite
    ((0 : Fin (data.width + 1)), Fin.last data.height)))

noncomputable def primalLeftSource
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    Finset V :=
  S.image (P.shift (data.base + preferenceGridSite
    ((0 : Fin (data.width + 1)), (0 : Fin (data.height + 1)))))

noncomputable def primalRightSource
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    Finset V :=
  S.image (P.shift (data.base + preferenceGridSite
    (Fin.last data.width, (0 : Fin (data.height + 1)))))

noncomputable def dualBottomSource
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    Finset W :=
  Sdual.image (Pdual.shift (data.baseDual + preferenceGridSite
    ((0 : Fin (data.widthDual + 1)), (0 : Fin (data.heightDual + 1)))))

noncomputable def dualTopSource
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    Finset W :=
  Sdual.image (Pdual.shift (data.baseDual + preferenceGridSite
    ((0 : Fin (data.widthDual + 1)), Fin.last data.heightDual)))

noncomputable def dualLeftSource
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    Finset W :=
  Sdual.image (Pdual.shift (data.baseDual + preferenceGridSite
    ((0 : Fin (data.widthDual + 1)), (0 : Fin (data.heightDual + 1)))))

noncomputable def dualRightSource
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    Finset W :=
  Sdual.image (Pdual.shift (data.baseDual + preferenceGridSite
    (Fin.last data.widthDual, (0 : Fin (data.heightDual + 1)))))

theorem primalBottomScore
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    p < mu.real (E.rectSideConnectionEvent
      data.wideLeft data.wideRight 0 data.shortTop
      (data.primalBottomSource : Set V)
      (E.rectBottomBoundaryVertices
        data.wideLeft data.wideRight 0 data.shortTop)) := by
  simpa [primalBottomSource] using
    data.primal_bottom (0 : Fin (data.width + 1))

theorem primalTopScore
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    p < mu.real (E.rectSideConnectionEvent
      data.wideLeft data.wideRight 0 data.shortTop
      (data.primalTopSource : Set V)
      (E.rectTopBoundaryVertices
        data.wideLeft data.wideRight 0 data.shortTop)) := by
  simpa [primalTopSource] using
    data.primal_top (0 : Fin (data.width + 1))

theorem primalLeftScore
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    p < mu.real (E.rectSideConnectionEvent
      0 data.narrowRight 0 data.tallTop
      (data.primalLeftSource : Set V)
      (E.rectLeftBoundaryVertices 0 data.narrowRight 0 data.tallTop)) := by
  simpa [primalLeftSource] using
    data.primal_left (0 : Fin (data.height + 1))

theorem primalRightScore
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    p < mu.real (E.rectSideConnectionEvent
      0 data.narrowRight 0 data.tallTop
      (data.primalRightSource : Set V)
      (E.rectRightBoundaryVertices 0 data.narrowRight 0 data.tallTop)) := by
  simpa [primalRightSource] using
    data.primal_right (0 : Fin (data.height + 1))

theorem dualBottomScore
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    pDual < muDual.real (Edual.rectSideConnectionEvent
      data.wideLeft data.wideRight 0 data.shortTop
      (data.dualBottomSource : Set W)
      (Edual.rectBottomBoundaryVertices
        data.wideLeft data.wideRight 0 data.shortTop)) := by
  simpa [dualBottomSource] using
    data.dual_bottom (0 : Fin (data.widthDual + 1))

theorem dualTopScore
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    pDual < muDual.real (Edual.rectSideConnectionEvent
      data.wideLeft data.wideRight 0 data.shortTop
      (data.dualTopSource : Set W)
      (Edual.rectTopBoundaryVertices
        data.wideLeft data.wideRight 0 data.shortTop)) := by
  simpa [dualTopSource] using
    data.dual_top (0 : Fin (data.widthDual + 1))

theorem dualLeftScore
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    pDual < muDual.real (Edual.rectSideConnectionEvent
      0 data.narrowRight 0 data.tallTop
      (data.dualLeftSource : Set W)
      (Edual.rectLeftBoundaryVertices 0 data.narrowRight 0 data.tallTop)) := by
  simpa [dualLeftSource] using
    data.dual_left (0 : Fin (data.heightDual + 1))

theorem dualRightScore
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    pDual < muDual.real (Edual.rectSideConnectionEvent
      0 data.narrowRight 0 data.tallTop
      (data.dualRightSource : Set W)
      (Edual.rectRightBoundaryVertices 0 data.narrowRight 0 data.tallTop)) := by
  simpa [dualRightSource] using
    data.dual_right (0 : Fin (data.heightDual + 1))

end PairedMixedBoundaryScores




structure ExactExtentPairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (S : Finset V) (Sdual : Finset W) (p pDual : Real)
    (extentX extentY : Nat) where
  data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual
  wideLeftInt : Int
  wideRightInt : Int
  narrowRight_eq : data.narrowRight = extentX
  shortTop_eq : data.shortTop = extentY
  tallTop_eq : data.tallTop = extentY
  wideLeft_eq : data.wideLeft = wideLeftInt
  wideRight_eq : data.wideRight = wideRightInt




theorem ExactExtentPairedMixedBoundaryScores.enlargeWideRight
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    [IsFiniteMeasure mu] [IsFiniteMeasure muDual]
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (newRight : Int) (hRight : raw.wideRightInt <= newRight) :
    Nonempty (ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY) := by
  let data := raw.data
  have hWide : data.wideRight <= (newRight : Real) := by
    rw [raw.wideRight_eq]
    exact_mod_cast hRight
  let enlarged : PairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual := {
    width := data.width
    height := data.height
    widthDual := data.widthDual
    heightDual := data.heightDual
    width_pos := data.width_pos
    height_pos := data.height_pos
    widthDual_pos := data.widthDual_pos
    heightDual_pos := data.heightDual_pos
    base := data.base
    baseDual := data.baseDual
    narrowRight := data.narrowRight
    shortTop := data.shortTop
    wideLeft := data.wideLeft
    wideRight := newRight
    tallTop := data.tallTop
    wideLeft_le := data.wideLeft_le
    narrowRight_le := data.narrowRight_le.trans hWide
    shortTop_le := data.shortTop_le
    primal_bottom := fun i => (data.primal_bottom i).trans_le
      (measureReal_mono (E.rectBottomConnectionEvent_mono_otherBounds _
        le_rfl hWide le_rfl))
    primal_top := fun i => (data.primal_top i).trans_le
      (measureReal_mono (E.rectTopConnectionEvent_mono_otherBounds _
        le_rfl hWide le_rfl))
    primal_left := data.primal_left
    primal_right := data.primal_right
    dual_bottom := fun i => (data.dual_bottom i).trans_le
      (measureReal_mono (Edual.rectBottomConnectionEvent_mono_otherBounds _
        le_rfl hWide le_rfl))
    dual_top := fun i => (data.dual_top i).trans_le
      (measureReal_mono (Edual.rectTopConnectionEvent_mono_otherBounds _
        le_rfl hWide le_rfl))
    dual_left := data.dual_left
    dual_right := data.dual_right }
  exact ⟨{
    data := enlarged
    wideLeftInt := raw.wideLeftInt
    wideRightInt := newRight
    narrowRight_eq := raw.narrowRight_eq
    shortTop_eq := raw.shortTop_eq
    tallTop_eq := raw.tallTop_eq
    wideLeft_eq := raw.wideLeft_eq
    wideRight_eq := rfl }⟩






theorem ExactExtentPairedMixedBoundaryScores.enlargeWide
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    [IsFiniteMeasure mu] [IsFiniteMeasure muDual]
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (newLeft newRight : Int)
    (hLeft : newLeft <= raw.wideLeftInt)
    (hRight : raw.wideRightInt <= newRight) :
    Nonempty (ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY) := by
  let data := raw.data
  have hWideLeft : (newLeft : Real) <= data.wideLeft := by
    rw [raw.wideLeft_eq]
    exact_mod_cast hLeft
  have hWideRight : data.wideRight <= (newRight : Real) := by
    rw [raw.wideRight_eq]
    exact_mod_cast hRight
  let enlarged : PairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual := {
    width := data.width
    height := data.height
    widthDual := data.widthDual
    heightDual := data.heightDual
    width_pos := data.width_pos
    height_pos := data.height_pos
    widthDual_pos := data.widthDual_pos
    heightDual_pos := data.heightDual_pos
    base := data.base
    baseDual := data.baseDual
    narrowRight := data.narrowRight
    shortTop := data.shortTop
    wideLeft := newLeft
    wideRight := newRight
    tallTop := data.tallTop
    wideLeft_le := hWideLeft.trans data.wideLeft_le
    narrowRight_le := data.narrowRight_le.trans hWideRight
    shortTop_le := data.shortTop_le
    primal_bottom := fun i => (data.primal_bottom i).trans_le
      (measureReal_mono (E.rectBottomConnectionEvent_mono_otherBounds _
        hWideLeft hWideRight le_rfl))
    primal_top := fun i => (data.primal_top i).trans_le
      (measureReal_mono (E.rectTopConnectionEvent_mono_otherBounds _
        hWideLeft hWideRight le_rfl))
    primal_left := data.primal_left
    primal_right := data.primal_right
    dual_bottom := fun i => (data.dual_bottom i).trans_le
      (measureReal_mono (Edual.rectBottomConnectionEvent_mono_otherBounds _
        hWideLeft hWideRight le_rfl))
    dual_top := fun i => (data.dual_top i).trans_le
      (measureReal_mono (Edual.rectTopConnectionEvent_mono_otherBounds _
        hWideLeft hWideRight le_rfl))
    dual_left := data.dual_left
    dual_right := data.dual_right }
  exact ⟨{
    data := enlarged
    wideLeftInt := newLeft
    wideRightInt := newRight
    narrowRight_eq := raw.narrowRight_eq
    shortTop_eq := raw.shortTop_eq
    tallTop_eq := raw.tallTop_eq
    wideLeft_eq := rfl
    wideRight_eq := rfl }⟩



theorem ExactExtentPairedMixedBoundaryScores.primalConnector_subset_narrow
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY radius : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (hleft : (E.connectorMarginRequirement radius : Int) <= raw.data.base 0)
    (hright : raw.data.base 0 + raw.data.width +
      E.connectorMarginRequirement radius <= extentX)
    (hbottom : (E.connectorMarginRequirement radius : Int) <= raw.data.base 1)
    (htop : raw.data.base 1 + raw.data.height +
      E.connectorMarginRequirement radius <= extentY) :
    forall v : PreferenceGridVertex raw.data.width raw.data.height,
      P.shift (raw.data.base + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆
        E.rectVertices 0 extentX 0 extentY := by
  intro v
  have hgrid := E.preferenceGrid_orbitBox_subset_translated_rect
    (P.bufferedRadius radius) (E.connectorMarginRequirement radius)
    raw.data.width raw.data.height raw.data.base
    (E.orbitBoxCoordinateBound_le_connectorMarginRequirement radius 0)
    (E.orbitBoxCoordinateBound_le_connectorMarginRequirement radius 1) v
  have hleftR : (E.connectorMarginRequirement radius : Real) <=
      raw.data.base 0 := by exact_mod_cast hleft
  have hrightR : (raw.data.base 0 : Real) + raw.data.width +
      E.connectorMarginRequirement radius <= extentX := by exact_mod_cast hright
  have hbottomR : (E.connectorMarginRequirement radius : Real) <=
      raw.data.base 1 := by exact_mod_cast hbottom
  have htopR : (raw.data.base 1 : Real) + raw.data.height +
      E.connectorMarginRequirement radius <= extentY := by exact_mod_cast htop
  have hmono : E.rectVertices
      (-(E.connectorMarginRequirement radius : Real) + raw.data.base 0)
      (E.connectorMarginRequirement radius + raw.data.width + raw.data.base 0)
      (-(E.connectorMarginRequirement radius : Real) + raw.data.base 1)
      (E.connectorMarginRequirement radius + raw.data.height + raw.data.base 1) ⊆
      E.rectVertices 0 extentX 0 extentY := by
    apply E.rectVertices_mono <;> push_cast <;> linarith
  simpa [add_comm] using hgrid.trans hmono


theorem ExactExtentPairedMixedBoundaryScores.dualConnector_subset_narrow
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY radius : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (hleft : (Edual.connectorMarginRequirement radius : Int) <=
      raw.data.baseDual 0)
    (hright : raw.data.baseDual 0 + raw.data.widthDual +
      Edual.connectorMarginRequirement radius <= extentX)
    (hbottom : (Edual.connectorMarginRequirement radius : Int) <=
      raw.data.baseDual 1)
    (htop : raw.data.baseDual 1 + raw.data.heightDual +
      Edual.connectorMarginRequirement radius <= extentY) :
    forall v : PreferenceGridVertex raw.data.widthDual raw.data.heightDual,
      Pdual.shift (raw.data.baseDual + preferenceGridSite v) ''
          (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) ⊆
        Edual.rectVertices 0 extentX 0 extentY := by
  intro v
  have hgrid := Edual.preferenceGrid_orbitBox_subset_translated_rect
    (Pdual.bufferedRadius radius) (Edual.connectorMarginRequirement radius)
    raw.data.widthDual raw.data.heightDual raw.data.baseDual
    (Edual.orbitBoxCoordinateBound_le_connectorMarginRequirement radius 0)
    (Edual.orbitBoxCoordinateBound_le_connectorMarginRequirement radius 1) v
  have hleftR : (Edual.connectorMarginRequirement radius : Real) <=
      raw.data.baseDual 0 := by exact_mod_cast hleft
  have hrightR : (raw.data.baseDual 0 : Real) + raw.data.widthDual +
      Edual.connectorMarginRequirement radius <= extentX := by
    exact_mod_cast hright
  have hbottomR : (Edual.connectorMarginRequirement radius : Real) <=
      raw.data.baseDual 1 := by exact_mod_cast hbottom
  have htopR : (raw.data.baseDual 1 : Real) + raw.data.heightDual +
      Edual.connectorMarginRequirement radius <= extentY := by
    exact_mod_cast htop
  have hmono : Edual.rectVertices
      (-(Edual.connectorMarginRequirement radius : Real) + raw.data.baseDual 0)
      (Edual.connectorMarginRequirement radius + raw.data.widthDual +
        raw.data.baseDual 0)
      (-(Edual.connectorMarginRequirement radius : Real) + raw.data.baseDual 1)
      (Edual.connectorMarginRequirement radius + raw.data.heightDual +
        raw.data.baseDual 1) ⊆ Edual.rectVertices 0 extentX 0 extentY := by
    apply Edual.rectVertices_mono <;> push_cast <;> linarith
  simpa [add_comm] using hgrid.trans hmono



theorem ExactExtentPairedMixedBoundaryScores.primalConnector_subset_wide
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY radius : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (hleft : (E.connectorMarginRequirement radius : Int) <= raw.data.base 0)
    (hright : raw.data.base 0 + raw.data.width +
      E.connectorMarginRequirement radius <= extentX)
    (hbottom : (E.connectorMarginRequirement radius : Int) <= raw.data.base 1)
    (htop : raw.data.base 1 + raw.data.height +
      E.connectorMarginRequirement radius <= extentY) :
    forall v : PreferenceGridVertex raw.data.width raw.data.height,
      P.shift (raw.data.base + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆
        E.rectVertices raw.data.wideLeft raw.data.wideRight
          0 raw.data.shortTop := by
  intro v
  apply (raw.primalConnector_subset_narrow hleft hright hbottom htop v).trans
  apply E.rectVertices_mono
  · exact raw.data.wideLeft_le
  · simpa [raw.narrowRight_eq] using raw.data.narrowRight_le
  · exact le_rfl
  · rw [raw.shortTop_eq]


theorem ExactExtentPairedMixedBoundaryScores.dualConnector_subset_wide
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY radius : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (hleft : (Edual.connectorMarginRequirement radius : Int) <=
      raw.data.baseDual 0)
    (hright : raw.data.baseDual 0 + raw.data.widthDual +
      Edual.connectorMarginRequirement radius <= extentX)
    (hbottom : (Edual.connectorMarginRequirement radius : Int) <=
      raw.data.baseDual 1)
    (htop : raw.data.baseDual 1 + raw.data.heightDual +
      Edual.connectorMarginRequirement radius <= extentY) :
    forall v : PreferenceGridVertex raw.data.widthDual raw.data.heightDual,
      Pdual.shift (raw.data.baseDual + preferenceGridSite v) ''
          (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) ⊆
        Edual.rectVertices raw.data.wideLeft raw.data.wideRight
          0 raw.data.shortTop := by
  intro v
  apply (raw.dualConnector_subset_narrow hleft hright hbottom htop v).trans
  apply Edual.rectVertices_mono
  · exact raw.data.wideLeft_le
  · simpa [raw.narrowRight_eq] using raw.data.narrowRight_le
  · exact le_rfl
  · rw [raw.shortTop_eq]



noncomputable def pairedWideLeftAtExtentX
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k extentX : Nat) : Int :=
  let h := schedule.horizontal k
  let v := schedule.vertical k
  let left : Site 2 := family.baseLeft + horizontalShift h
  let right : Site 2 := family.baseRight + horizontalShift (-(h : Int))
  let leftDual : Site 2 := familyDual.baseLeft + horizontalShift h
  let rightDual : Site 2 :=
    familyDual.baseRight + horizontalShift (-(h : Int))
  let width := boundaryGridWidth extentX left right
  let widthDual := boundaryGridWidth extentX leftDual rightDual
  let baseX := family.baseLeft 0 + h
  let baseXDual := familyDual.baseLeft 0 + h
  let aP := min 0 (min
    (baseX - family.baseBottom 0 - family.radiusBottom v)
    (baseX - family.baseTop 0 - family.radiusTop v))
  let aD := min 0 (min
    (baseXDual - familyDual.baseBottom 0 - familyDual.radiusBottom v)
    (baseXDual - familyDual.baseTop 0 - familyDual.radiusTop v))
  min aP aD


noncomputable def pairedWideRightAtExtentX
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k extentX : Nat) : Int :=
  let h := schedule.horizontal k
  let v := schedule.vertical k
  let left : Site 2 := family.baseLeft + horizontalShift h
  let right : Site 2 := family.baseRight + horizontalShift (-(h : Int))
  let leftDual : Site 2 := familyDual.baseLeft + horizontalShift h
  let rightDual : Site 2 :=
    familyDual.baseRight + horizontalShift (-(h : Int))
  let width := boundaryGridWidth extentX left right
  let widthDual := boundaryGridWidth extentX leftDual rightDual
  let baseX := family.baseLeft 0 + h
  let baseXDual := familyDual.baseLeft 0 + h
  let bP : Int := max (extentX : Int) (max
    (baseX + width - family.baseBottom 0 + family.radiusBottom v)
    (baseX + width - family.baseTop 0 + family.radiusTop v))
  let bD : Int := max (extentX : Int) (max
    (baseXDual + widthDual - familyDual.baseBottom 0 +
      familyDual.radiusBottom v)
    (baseXDual + widthDual - familyDual.baseTop 0 +
      familyDual.radiusTop v))
  max bP bD



structure AlignedExactExtentPairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (S : Finset V) (Sdual : Finset W) (p pDual : Real)
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k extentX extentY : Nat) where
  raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual extentX extentY
  primalBaseX_eq : raw.data.base 0 =
    family.baseLeft 0 + schedule.horizontal k
  primalEndX_eq : raw.data.base 0 + raw.data.width =
    extentX + family.baseRight 0 - schedule.horizontal k
  primalBaseY_eq : raw.data.base 1 =
    family.baseBottom 1 + schedule.vertical k
  primalEndY_eq : raw.data.base 1 + raw.data.height =
    extentY + family.baseTop 1 - schedule.vertical k
  dualBaseX_eq : raw.data.baseDual 0 =
    familyDual.baseLeft 0 + schedule.horizontal k
  dualEndX_eq : raw.data.baseDual 0 + raw.data.widthDual =
    extentX + familyDual.baseRight 0 - schedule.horizontal k
  dualBaseY_eq : raw.data.baseDual 1 =
    familyDual.baseBottom 1 + schedule.vertical k
  dualEndY_eq : raw.data.baseDual 1 + raw.data.heightDual =
    extentY + familyDual.baseTop 1 - schedule.vertical k
  wideLeft_formula : raw.wideLeftInt =
    pairedWideLeftAtExtentX E Edual family familyDual schedule k extentX
  wideRight_formula : raw.wideRightInt =
    pairedWideRightAtExtentX E Edual family familyDual schedule k extentX



structure PairedAlignedConnectorSlack
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (radius k : Nat) : Prop where
  primalLeft : (E.connectorMarginRequirement radius : Int) <=
    family.baseLeft 0 + schedule.horizontal k
  primalRight : family.baseRight 0 - schedule.horizontal k +
    E.connectorMarginRequirement radius <= 0
  primalBottom : (E.connectorMarginRequirement radius : Int) <=
    family.baseBottom 1 + schedule.vertical k
  primalTop : family.baseTop 1 - schedule.vertical k +
    E.connectorMarginRequirement radius <= 0
  dualLeft : (Edual.connectorMarginRequirement radius : Int) <=
    familyDual.baseLeft 0 + schedule.horizontal k
  dualRight : familyDual.baseRight 0 - schedule.horizontal k +
    Edual.connectorMarginRequirement radius <= 0
  dualBottom : (Edual.connectorMarginRequirement radius : Int) <=
    familyDual.baseBottom 1 + schedule.vertical k
  dualTop : familyDual.baseTop 1 - schedule.vertical k +
    Edual.connectorMarginRequirement radius <= 0



theorem exists_pairedAlignedConnectorSlack
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (radius : Nat) : exists k,
    PairedAlignedConnectorSlack E Edual family familyDual schedule radius k := by
  let ML : Int := E.connectorMarginRequirement radius
  let MD : Int := Edual.connectorMarginRequirement radius
  let h1 : Int := ML - family.baseLeft 0
  let h2 : Int := family.baseRight 0 + ML
  let h3 : Int := MD - familyDual.baseLeft 0
  let h4 : Int := familyDual.baseRight 0 + MD
  let v1 : Int := ML - family.baseBottom 1
  let v2 : Int := family.baseTop 1 + ML
  let v3 : Int := MD - familyDual.baseBottom 1
  let v4 : Int := familyDual.baseTop 1 + MD
  let horizontalTarget := h1.natAbs + h2.natAbs + h3.natAbs + h4.natAbs
  let verticalTarget := v1.natAbs + v2.natAbs + v3.natAbs + v4.natAbs
  have hHorizontal : ∀ᶠ eventuallyK in atTop,
      horizontalTarget <= schedule.horizontal eventuallyK :=
    schedule.horizontal_tendsto (eventually_ge_atTop horizontalTarget)
  have hVertical : ∀ᶠ eventuallyK in atTop,
      verticalTarget <= schedule.vertical eventuallyK :=
    schedule.vertical_tendsto (eventually_ge_atTop verticalTarget)
  obtain ⟨horizontalIndex, hHorizontalIndex⟩ :=
    eventually_atTop.1 hHorizontal
  obtain ⟨verticalIndex, hVerticalIndex⟩ :=
    eventually_atTop.1 hVertical
  let k := max horizontalIndex verticalIndex
  have hkH := hHorizontalIndex k (Nat.le_max_left _ _)
  have hkV := hVerticalIndex k (Nat.le_max_right _ _)
  have hh1 : h1 <= (schedule.horizontal k : Int) := by
    apply Int.le_natAbs.trans
    exact_mod_cast (show h1.natAbs <= schedule.horizontal k by
      apply (show h1.natAbs <= horizontalTarget by
        dsimp [horizontalTarget]; omega) |>.trans hkH)
  have hh2 : h2 <= (schedule.horizontal k : Int) := by
    apply Int.le_natAbs.trans
    exact_mod_cast (show h2.natAbs <= schedule.horizontal k by
      apply (show h2.natAbs <= horizontalTarget by
        dsimp [horizontalTarget]; omega) |>.trans hkH)
  have hh3 : h3 <= (schedule.horizontal k : Int) := by
    apply Int.le_natAbs.trans
    exact_mod_cast (show h3.natAbs <= schedule.horizontal k by
      apply (show h3.natAbs <= horizontalTarget by
        dsimp [horizontalTarget]; omega) |>.trans hkH)
  have hh4 : h4 <= (schedule.horizontal k : Int) := by
    apply Int.le_natAbs.trans
    exact_mod_cast (show h4.natAbs <= schedule.horizontal k by
      apply (show h4.natAbs <= horizontalTarget by
        dsimp [horizontalTarget]; omega) |>.trans hkH)
  have hv1 : v1 <= (schedule.vertical k : Int) := by
    apply Int.le_natAbs.trans
    exact_mod_cast (show v1.natAbs <= schedule.vertical k by
      apply (show v1.natAbs <= verticalTarget by
        dsimp [verticalTarget]; omega) |>.trans hkV)
  have hv2 : v2 <= (schedule.vertical k : Int) := by
    apply Int.le_natAbs.trans
    exact_mod_cast (show v2.natAbs <= schedule.vertical k by
      apply (show v2.natAbs <= verticalTarget by
        dsimp [verticalTarget]; omega) |>.trans hkV)
  have hv3 : v3 <= (schedule.vertical k : Int) := by
    apply Int.le_natAbs.trans
    exact_mod_cast (show v3.natAbs <= schedule.vertical k by
      apply (show v3.natAbs <= verticalTarget by
        dsimp [verticalTarget]; omega) |>.trans hkV)
  have hv4 : v4 <= (schedule.vertical k : Int) := by
    apply Int.le_natAbs.trans
    exact_mod_cast (show v4.natAbs <= schedule.vertical k by
      apply (show v4.natAbs <= verticalTarget by
        dsimp [verticalTarget]; omega) |>.trans hkV)
  refine ⟨k, ?_⟩
  constructor <;> dsimp only [h1, h2, h3, h4, v1, v2, v3, v4, ML, MD]
    at hh1 hh2 hh3 hh4 hv1 hv2 hv3 hv4 ⊢ <;> omega



theorem AlignedExactExtentPairedMixedBoundaryScores.primalConnector_subset_narrow
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k extentX extentY radius : Nat}
    (data : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (slack : PairedAlignedConnectorSlack E Edual family familyDual
      schedule radius k) :
    forall v : PreferenceGridVertex data.raw.data.width data.raw.data.height,
      P.shift (data.raw.data.base + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆
        E.rectVertices 0 extentX 0 extentY := by
  apply data.raw.primalConnector_subset_narrow
  · simpa [data.primalBaseX_eq] using slack.primalLeft
  · rw [data.primalEndX_eq]
    have := slack.primalRight
    omega
  · simpa [data.primalBaseY_eq] using slack.primalBottom
  · rw [data.primalEndY_eq]
    have := slack.primalTop
    omega


theorem AlignedExactExtentPairedMixedBoundaryScores.dualConnector_subset_narrow
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k extentX extentY radius : Nat}
    (data : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (slack : PairedAlignedConnectorSlack E Edual family familyDual
      schedule radius k) :
    forall v : PreferenceGridVertex
      data.raw.data.widthDual data.raw.data.heightDual,
      Pdual.shift (data.raw.data.baseDual + preferenceGridSite v) ''
          (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) ⊆
        Edual.rectVertices 0 extentX 0 extentY := by
  apply data.raw.dualConnector_subset_narrow
  · simpa [data.dualBaseX_eq] using slack.dualLeft
  · rw [data.dualEndX_eq]
    have := slack.dualRight
    omega
  · simpa [data.dualBaseY_eq] using slack.dualBottom
  · rw [data.dualEndY_eq]
    have := slack.dualTop
    omega



theorem AlignedExactExtentPairedMixedBoundaryScores.primalConnector_subset_wide
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k extentX extentY radius : Nat}
    (data : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (slack : PairedAlignedConnectorSlack E Edual family familyDual
      schedule radius k) :
    forall v : PreferenceGridVertex data.raw.data.width data.raw.data.height,
      P.shift (data.raw.data.base + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆
        E.rectVertices data.raw.data.wideLeft data.raw.data.wideRight
          0 data.raw.data.shortTop := by
  intro gridVertex
  apply (data.primalConnector_subset_narrow slack gridVertex).trans
  apply E.rectVertices_mono
  · exact data.raw.data.wideLeft_le
  · simpa [data.raw.narrowRight_eq] using data.raw.data.narrowRight_le
  · exact le_rfl
  · rw [data.raw.shortTop_eq]


theorem AlignedExactExtentPairedMixedBoundaryScores.dualConnector_subset_wide
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k extentX extentY radius : Nat}
    (data : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (slack : PairedAlignedConnectorSlack E Edual family familyDual
      schedule radius k) :
    forall v : PreferenceGridVertex
      data.raw.data.widthDual data.raw.data.heightDual,
      Pdual.shift (data.raw.data.baseDual + preferenceGridSite v) ''
          (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) ⊆
        Edual.rectVertices data.raw.data.wideLeft data.raw.data.wideRight
          0 data.raw.data.shortTop := by
  intro gridVertex
  apply (data.dualConnector_subset_narrow slack gridVertex).trans
  apply Edual.rectVertices_mono
  · exact data.raw.data.wideLeft_le
  · simpa [data.raw.narrowRight_eq] using data.raw.data.narrowRight_le
  · exact le_rfl
  · rw [data.raw.shortTop_eq]





theorem exists_alignedExactExtentPairedMixedBoundaryScores_atExtents
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k extentX extentY : Nat)
    (hposX : 0 < family.baseRight 0 - schedule.horizontal k + extentX -
      (family.baseLeft 0 + schedule.horizontal k))
    (hposXDual : 0 < familyDual.baseRight 0 - schedule.horizontal k +
      extentX - (familyDual.baseLeft 0 + schedule.horizontal k))
    (hposY : 0 < family.baseTop 1 - schedule.vertical k + extentY -
      (family.baseBottom 1 + schedule.vertical k))
    (hposYDual : 0 < familyDual.baseTop 1 - schedule.vertical k +
      extentY - (familyDual.baseBottom 1 + schedule.vertical k))
    (hleftP : family.radiusLeft (schedule.horizontal k) <= extentX)
    (hrightP : family.radiusRight (schedule.horizontal k) <= extentX)
    (hbottomP : family.radiusBottom (schedule.vertical k) <= extentY)
    (htopP : family.radiusTop (schedule.vertical k) <= extentY)
    (hleftD : familyDual.radiusLeft (schedule.horizontal k) <= extentX)
    (hrightD : familyDual.radiusRight (schedule.horizontal k) <= extentX)
    (hbottomD : familyDual.radiusBottom (schedule.vertical k) <= extentY)
    (htopD : familyDual.radiusTop (schedule.vertical k) <= extentY) :
    Nonempty (AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY) := by
  let h := schedule.horizontal k
  let v := schedule.vertical k
  let left : Site 2 := family.baseLeft + horizontalShift h
  let right : Site 2 := family.baseRight + horizontalShift (-(h : Int))
  let bottom : Site 2 := family.baseBottom + verticalShift v
  let top : Site 2 := family.baseTop + verticalShift (-(v : Int))
  let leftDual : Site 2 := familyDual.baseLeft + horizontalShift h
  let rightDual : Site 2 :=
    familyDual.baseRight + horizontalShift (-(h : Int))
  let bottomDual : Site 2 := familyDual.baseBottom + verticalShift v
  let topDual : Site 2 := familyDual.baseTop + verticalShift (-(v : Int))
  let width := boundaryGridWidth extentX left right
  let height := boundaryGridHeight extentY bottom top
  let widthDual := boundaryGridWidth extentX leftDual rightDual
  let heightDual := boundaryGridHeight extentY bottomDual topDual
  have hx0 : 0 < right 0 + (extentX : Int) - left 0 := by
    simpa [left, right, h] using hposX
  have hxDual0 : 0 < rightDual 0 + (extentX : Int) - leftDual 0 := by
    simpa [leftDual, rightDual, h] using hposXDual
  have hy0 : 0 < top 1 + (extentY : Int) - bottom 1 := by
    simpa [bottom, top, v] using hposY
  have hyDual0 : 0 < topDual 1 + (extentY : Int) - bottomDual 1 := by
    simpa [bottomDual, topDual, v] using hposYDual
  have hwidth : 0 < width := boundaryGridWidth_pos _ _ _ hx0
  have hheight : 0 < height := boundaryGridHeight_pos _ _ _ hy0
  have hwidthDual : 0 < widthDual :=
    boundaryGridWidth_pos _ _ _ hxDual0
  have hheightDual : 0 < heightDual :=
    boundaryGridHeight_pos _ _ _ hyDual0
  have hb : (family.baseLeft 0 + h + width -
      (family.baseRight 0 - h) : Int) = extentX := by
    have hnonneg : 0 <= right 0 + (extentX : Int) - left 0 := hx0.le
    have hwidthCast : (width : Int) = right 0 + extentX - left 0 := by
      dsimp only [width, boundaryGridWidth]
      rw [Int.toNat_of_nonneg hnonneg]
    rw [hwidthCast]
    simp [left, right]
    omega
  have hbDual : (familyDual.baseLeft 0 + h + widthDual -
      (familyDual.baseRight 0 - h) : Int) = extentX := by
    have hnonneg : 0 <= rightDual 0 + (extentX : Int) - leftDual 0 :=
      hxDual0.le
    have hwidthCast :
        (widthDual : Int) = rightDual 0 + extentX - leftDual 0 := by
      dsimp only [widthDual, boundaryGridWidth]
      rw [Int.toNat_of_nonneg hnonneg]
    rw [hwidthCast]
    simp [leftDual, rightDual]
    omega
  have hd : (family.baseBottom 1 + v + height -
      (family.baseTop 1 - v) : Int) = extentY := by
    have hnonneg : 0 <= top 1 + (extentY : Int) - bottom 1 := hy0.le
    have hheightCast : (height : Int) = top 1 + extentY - bottom 1 := by
      dsimp only [height, boundaryGridHeight]
      rw [Int.toNat_of_nonneg hnonneg]
    rw [hheightCast]
    simp [bottom, top]
    omega
  have hdDual : (familyDual.baseBottom 1 + v + heightDual -
      (familyDual.baseTop 1 - v) : Int) = extentY := by
    have hnonneg :
        0 <= topDual 1 + (extentY : Int) - bottomDual 1 := hyDual0.le
    have hheightCast :
        (heightDual : Int) = topDual 1 + extentY - bottomDual 1 := by
      dsimp only [heightDual, boundaryGridHeight]
      rw [Int.toNat_of_nonneg hnonneg]
    rw [hheightCast]
    simp [bottomDual, topDual]
    omega
  let base : Site 2 := fun i => if i = 0 then
    family.baseLeft 0 + h else family.baseBottom 1 + v
  let baseDual : Site 2 := fun i => if i = 0 then
    familyDual.baseLeft 0 + h else familyDual.baseBottom 1 + v
  let bottomLower : Int := base 0 - family.baseBottom 0 -
    family.radiusBottom v
  let topLower : Int := base 0 - family.baseTop 0 - family.radiusTop v
  let aP : Int := min 0 (min bottomLower topLower)
  let bottomUpper : Int := base 0 + width - family.baseBottom 0 +
    family.radiusBottom v
  let topUpper : Int := base 0 + width - family.baseTop 0 +
    family.radiusTop v
  let bP : Int := max extentX (max bottomUpper topUpper)
  let leftUpper : Int := base 1 + height - family.baseLeft 1 +
    family.radiusLeft h
  let rightUpper : Int := base 1 + height - family.baseRight 1 +
    family.radiusRight h
  let dP : Int := max extentY (max leftUpper rightUpper)
  let bottomLowerDual : Int := baseDual 0 - familyDual.baseBottom 0 -
    familyDual.radiusBottom v
  let topLowerDual : Int :=
    baseDual 0 - familyDual.baseTop 0 - familyDual.radiusTop v
  let aD : Int := min 0 (min bottomLowerDual topLowerDual)
  let bottomUpperDual : Int := baseDual 0 + widthDual -
    familyDual.baseBottom 0 + familyDual.radiusBottom v
  let topUpperDual : Int := baseDual 0 + widthDual -
    familyDual.baseTop 0 + familyDual.radiusTop v
  let bD : Int := max extentX (max bottomUpperDual topUpperDual)
  let leftUpperDual : Int := baseDual 1 + heightDual -
    familyDual.baseLeft 1 + familyDual.radiusLeft h
  let rightUpperDual : Int := baseDual 1 + heightDual -
    familyDual.baseRight 1 + familyDual.radiusRight h
  let dD : Int := max extentY (max leftUpperDual rightUpperDual)
  let a := min aP aD
  let b := max bP bD
  let d := max dP dD
  have hmixedP := family.mixedBoundaryScores E mu hTI h v width height
    (schedule.primal_left_bottom k) (schedule.primal_right_bottom k)
    (by simpa [base, hb, h] using (show (family.radiusLeft h : Int) <=
      extentX by exact_mod_cast hleftP))
    (by simpa [base, hb, h] using (show (family.radiusRight h : Int) <=
      extentX by exact_mod_cast hrightP))
    (by simpa [base, hd, v] using (show (family.radiusBottom v : Int) <=
      extentY by exact_mod_cast hbottomP))
    (by simpa [base, hd, v] using (show (family.radiusTop v : Int) <=
      extentY by exact_mod_cast htopP))
  have hmixedD := familyDual.mixedBoundaryScores Edual muDual hTIDual
    h v widthDual heightDual (schedule.dual_left_bottom k)
    (schedule.dual_right_bottom k)
    (by simpa [baseDual, hbDual, h] using
      (show (familyDual.radiusLeft h : Int) <= extentX by
        exact_mod_cast hleftD))
    (by simpa [baseDual, hbDual, h] using
      (show (familyDual.radiusRight h : Int) <= extentX by
        exact_mod_cast hrightD))
    (by simpa [baseDual, hdDual, v] using
      (show (familyDual.radiusBottom v : Int) <= extentY by
        exact_mod_cast hbottomD))
    (by simpa [baseDual, hdDual, v] using
      (show (familyDual.radiusTop v : Int) <= extentY by
        exact_mod_cast htopD))
  dsimp only at hmixedP hmixedD
  simp only [if_pos (rfl : (0 : Fin 2) = 0),
    if_neg (by decide : (1 : Fin 2) ≠ 0), if_true, if_false]
      at hmixedP hmixedD
  rw [hb, hd] at hmixedP
  rw [hbDual, hdDual] at hmixedD
  change (((aP : Real) <= 0 /\ (extentX : Real) <= bP /\
      (0 : Real) <= 0 /\ (extentY : Real) <= dP) /\ _) at hmixedP
  change (((aD : Real) <= 0 /\ (extentX : Real) <= bD /\
      (0 : Real) <= 0 /\ (extentY : Real) <= dD) /\ _) at hmixedD
  have hdP : dP = extentY := by
    have hleft := schedule.primal_left_top k
    have hright := schedule.primal_right_top k
    change (family.radiusLeft h : Int) + family.baseTop 1 <=
      family.baseLeft 1 + v at hleft
    change (family.radiusRight h : Int) + family.baseTop 1 <=
      family.baseRight 1 + v at hright
    have hbaseHeight : family.baseBottom 1 + (v : Int) + height =
        (extentY : Int) + family.baseTop 1 - v := by omega
    dsimp only [dP, leftUpper, rightUpper]
    simp only [base, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    rw [hbaseHeight]
    omega
  have hdD : dD = extentY := by
    have hleft := schedule.dual_left_top k
    have hright := schedule.dual_right_top k
    change (familyDual.radiusLeft h : Int) + familyDual.baseTop 1 <=
      familyDual.baseLeft 1 + v at hleft
    change (familyDual.radiusRight h : Int) + familyDual.baseTop 1 <=
      familyDual.baseRight 1 + v at hright
    have hbaseHeight : familyDual.baseBottom 1 + (v : Int) + heightDual =
        (extentY : Int) + familyDual.baseTop 1 - v := by omega
    dsimp only [dD, leftUpperDual, rightUpperDual]
    simp only [baseDual, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    rw [hbaseHeight]
    omega
  have hdCommon : d = extentY := by simp [d, hdP, hdD]
  let raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY := {
    data := {
    width := width
    height := height
    widthDual := widthDual
    heightDual := heightDual
    width_pos := hwidth
    height_pos := hheight
    widthDual_pos := hwidthDual
    heightDual_pos := hheightDual
    base := base
    baseDual := baseDual
    narrowRight := extentX
    shortTop := extentY
    wideLeft := a
    wideRight := b
    tallTop := d
    wideLeft_le := by
      exact (show (a : Real) <= (aP : Real) by
        exact_mod_cast min_le_left aP aD).trans hmixedP.1.1
    narrowRight_le := by
      exact hmixedP.1.2.1.trans (show (bP : Real) <= (b : Real) by
        exact_mod_cast le_max_left bP bD)
    shortTop_le := by
      exact hmixedP.1.2.2.2.trans (show (dP : Real) <= (d : Real) by
        exact_mod_cast le_max_left dP dD)
    primal_bottom := fun i => (hmixedP.2.1 i).trans_le (measureReal_mono
      (E.rectBottomConnectionEvent_mono_otherBounds _
        (by exact_mod_cast min_le_left aP aD)
        (by exact_mod_cast le_max_left bP bD) le_rfl))
    primal_top := fun i => (hmixedP.2.2.1 i).trans_le (measureReal_mono
      (E.rectTopConnectionEvent_mono_otherBounds _
        (by exact_mod_cast min_le_left aP aD)
        (by exact_mod_cast le_max_left bP bD) le_rfl))
    primal_left := fun j => (hmixedP.2.2.2.1 j).trans_le (measureReal_mono
      (E.rectLeftConnectionEvent_mono_otherBounds _ le_rfl le_rfl
        (by exact_mod_cast le_max_left dP dD)))
    primal_right := fun j => (hmixedP.2.2.2.2 j).trans_le (measureReal_mono
      (E.rectRightConnectionEvent_mono_otherBounds _ le_rfl le_rfl
        (by exact_mod_cast le_max_left dP dD)))
    dual_bottom := fun i => (hmixedD.2.1 i).trans_le (measureReal_mono
      (Edual.rectBottomConnectionEvent_mono_otherBounds _
        (by exact_mod_cast min_le_right aP aD)
        (by exact_mod_cast le_max_right bP bD) le_rfl))
    dual_top := fun i => (hmixedD.2.2.1 i).trans_le (measureReal_mono
      (Edual.rectTopConnectionEvent_mono_otherBounds _
        (by exact_mod_cast min_le_right aP aD)
        (by exact_mod_cast le_max_right bP bD) le_rfl))
    dual_left := fun j => (hmixedD.2.2.2.1 j).trans_le (measureReal_mono
      (Edual.rectLeftConnectionEvent_mono_otherBounds _ le_rfl le_rfl
        (by exact_mod_cast le_max_right dP dD)))
    dual_right := fun j => (hmixedD.2.2.2.2 j).trans_le (measureReal_mono
      (Edual.rectRightConnectionEvent_mono_otherBounds _ le_rfl le_rfl
        (by exact_mod_cast le_max_right dP dD))) }
    wideLeftInt := a
    wideRightInt := b
    narrowRight_eq := rfl
    shortTop_eq := rfl
    tallTop_eq := by
      change (d : Real) = (extentY : Real)
      exact_mod_cast hdCommon
    wideLeft_eq := rfl
    wideRight_eq := rfl }
  refine ⟨{
    raw := raw
    primalBaseX_eq := ?_
    primalEndX_eq := ?_
    primalBaseY_eq := ?_
    primalEndY_eq := ?_
    dualBaseX_eq := ?_
    dualEndX_eq := ?_
    dualBaseY_eq := ?_
    dualEndY_eq := ?_
    wideLeft_formula := ?_
    wideRight_formula := ?_ }⟩
  · simp [raw, base, h]
  · dsimp only [raw]
    simp only [base, if_pos (rfl : (0 : Fin 2) = 0)]
    omega
  · simp [raw, base, v]
  · dsimp only [raw]
    simp only [base, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    omega
  · simp [raw, baseDual, h]
  · dsimp only [raw]
    simp only [baseDual, if_pos (rfl : (0 : Fin 2) = 0)]
    omega
  · simp [raw, baseDual, v]
  · dsimp only [raw]
    simp only [baseDual, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    omega
  · simp [raw, pairedWideLeftAtExtentX, a, aP, aD, bottomLower,
      topLower, bottomLowerDual, topLowerDual, base, baseDual, h, v,
      left, right, leftDual, rightDual]
  · simp [raw, pairedWideRightAtExtentX, b, bP, bD, bottomUpper,
      topUpper, bottomUpperDual, topUpperDual, base, baseDual, h, v,
      left, right, leftDual, rightDual, width, widthDual]


theorem exists_pairedMixedBoundaryScores_atExtents
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k extentX extentY : Nat)
    (hposX : 0 < family.baseRight 0 - schedule.horizontal k + extentX -
      (family.baseLeft 0 + schedule.horizontal k))
    (hposXDual : 0 < familyDual.baseRight 0 - schedule.horizontal k +
      extentX - (familyDual.baseLeft 0 + schedule.horizontal k))
    (hposY : 0 < family.baseTop 1 - schedule.vertical k + extentY -
      (family.baseBottom 1 + schedule.vertical k))
    (hposYDual : 0 < familyDual.baseTop 1 - schedule.vertical k +
      extentY - (familyDual.baseBottom 1 + schedule.vertical k))
    (hleftP : family.radiusLeft (schedule.horizontal k) <= extentX)
    (hrightP : family.radiusRight (schedule.horizontal k) <= extentX)
    (hbottomP : family.radiusBottom (schedule.vertical k) <= extentY)
    (htopP : family.radiusTop (schedule.vertical k) <= extentY)
    (hleftD : familyDual.radiusLeft (schedule.horizontal k) <= extentX)
    (hrightD : familyDual.radiusRight (schedule.horizontal k) <= extentX)
    (hbottomD : familyDual.radiusBottom (schedule.vertical k) <= extentY)
    (htopD : familyDual.radiusTop (schedule.vertical k) <= extentY) :
    Nonempty (ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY) := by
  exact Nonempty.map AlignedExactExtentPairedMixedBoundaryScores.raw
    (exists_alignedExactExtentPairedMixedBoundaryScores_atExtents
      E Edual mu muDual hTI hTIDual family familyDual schedule k
      extentX extentY hposX hposXDual hposY hposYDual hleftP hrightP
      hbottomP htopP hleftD hrightD hbottomD htopD)





theorem exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k : Nat) :
    exists thresholdX thresholdY, forall {extentX extentY},
      thresholdX <= extentX -> thresholdY <= extentY ->
      Nonempty (AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
        S Sdual p pDual family familyDual schedule k extentX extentY) := by
  let h := schedule.horizontal k
  let v := schedule.vertical k
  let radiusX := max
    (max (family.radiusLeft h) (family.radiusRight h))
    (max (familyDual.radiusLeft h) (familyDual.radiusRight h))
  let radiusY := max
    (max (family.radiusBottom v) (family.radiusTop v))
    (max (familyDual.radiusBottom v) (familyDual.radiusTop v))
  let gapX : Int := family.baseLeft 0 + 2 * h - family.baseRight 0
  let gapXDual : Int :=
    familyDual.baseLeft 0 + 2 * h - familyDual.baseRight 0
  let gapY : Int := family.baseBottom 1 + 2 * v - family.baseTop 1
  let gapYDual : Int :=
    familyDual.baseBottom 1 + 2 * v - familyDual.baseTop 1
  let thresholdX := max radiusX
    (max (gapX.natAbs + 1) (gapXDual.natAbs + 1))
  let thresholdY := max radiusY
    (max (gapY.natAbs + 1) (gapYDual.natAbs + 1))
  refine ⟨thresholdX, thresholdY, ?_⟩
  intro extentX extentY hX hY
  have hradiusX : radiusX <= extentX :=
    (Nat.le_max_left _ _).trans hX
  have hradiusY : radiusY <= extentY :=
    (Nat.le_max_left _ _).trans hY
  have hgapX : gapX.natAbs + 1 <= extentX :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _) |>.trans hX
  have hgapXDual : gapXDual.natAbs + 1 <= extentX :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _) |>.trans hX
  have hgapY : gapY.natAbs + 1 <= extentY :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _) |>.trans hY
  have hgapYDual : gapYDual.natAbs + 1 <= extentY :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _) |>.trans hY
  have hposX : 0 < family.baseRight 0 - h + extentX -
      (family.baseLeft 0 + h) := by
    have hgap : gapX < (extentX : Int) := by
      have habs : gapX <= (gapX.natAbs : Int) := Int.le_natAbs
      have hcast : (gapX.natAbs + 1 : Int) <= extentX := by
        exact_mod_cast hgapX
      omega
    dsimp only [gapX] at hgap
    omega
  have hposXDual : 0 < familyDual.baseRight 0 - h + extentX -
      (familyDual.baseLeft 0 + h) := by
    have hgap : gapXDual < (extentX : Int) := by
      have habs : gapXDual <= (gapXDual.natAbs : Int) := Int.le_natAbs
      have hcast : (gapXDual.natAbs + 1 : Int) <= extentX := by
        exact_mod_cast hgapXDual
      omega
    dsimp only [gapXDual] at hgap
    omega
  have hposY : 0 < family.baseTop 1 - v + extentY -
      (family.baseBottom 1 + v) := by
    have hgap : gapY < (extentY : Int) := by
      have habs : gapY <= (gapY.natAbs : Int) := Int.le_natAbs
      have hcast : (gapY.natAbs + 1 : Int) <= extentY := by
        exact_mod_cast hgapY
      omega
    dsimp only [gapY] at hgap
    omega
  have hposYDual : 0 < familyDual.baseTop 1 - v + extentY -
      (familyDual.baseBottom 1 + v) := by
    have hgap : gapYDual < (extentY : Int) := by
      have habs : gapYDual <= (gapYDual.natAbs : Int) := Int.le_natAbs
      have hcast : (gapYDual.natAbs + 1 : Int) <= extentY := by
        exact_mod_cast hgapYDual
      omega
    dsimp only [gapYDual] at hgap
    omega
  exact exists_alignedExactExtentPairedMixedBoundaryScores_atExtents
    E Edual mu muDual
    hTI hTIDual family familyDual schedule k extentX extentY
    hposX hposXDual hposY hposYDual
    ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _) |>.trans hradiusX)
    ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _) |>.trans hradiusX)
    ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _) |>.trans hradiusY)
    ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _) |>.trans hradiusY)
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _) |>.trans hradiusX)
    ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _) |>.trans hradiusX)
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _) |>.trans hradiusY)
    ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _) |>.trans hradiusY)


theorem exists_exactExtentPairedMixedBoundaryScores_thresholds
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k : Nat) :
    exists thresholdX thresholdY, forall {extentX extentY},
      thresholdX <= extentX -> thresholdY <= extentY ->
      Nonempty (ExactExtentPairedMixedBoundaryScores E Edual mu muDual
        S Sdual p pDual extentX extentY) := by
  obtain ⟨thresholdX, thresholdY, hthreshold⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E Edual mu muDual hTI hTIDual family familyDual schedule k
  refine ⟨thresholdX, thresholdY, ?_⟩
  intro extentX extentY hX hY
  exact Nonempty.map AlignedExactExtentPairedMixedBoundaryScores.raw
    (hthreshold hX hY)



theorem ExactExtentPairedMixedBoundaryScores.extentX_le_wideSpan
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY) :
    (extentX : Int) <= raw.wideRightInt - raw.wideLeftInt := by
  have hleft : (raw.wideLeftInt : Real) <= 0 := by
    simpa [raw.wideLeft_eq] using raw.data.wideLeft_le
  have hright : (extentX : Real) <= raw.wideRightInt := by
    simpa [raw.narrowRight_eq, raw.wideRight_eq] using
      raw.data.narrowRight_le
  exact_mod_cast (show (extentX : Real) <=
    raw.wideRightInt - raw.wideLeftInt by linarith)




theorem ExactExtentPairedMixedBoundaryScores.dualVerticalMerge_translate_measureReal_le
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (hTI : Pdual.IsTranslationInvariant muDual)
    (z : Site 2) (a b c d : Real) (radius : Nat)
    (hbox : Pdual.shift z ''
        (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <=
      Edual.rectVertices a b c d) :
    muDual.real (Edual.rectanglePairMergeErrorUnion a b c d
        (raw.data.dualBottomSource.image (Pdual.shift z))
        (raw.data.dualTopSource.image (Pdual.shift z))) <=
      muDual.real (Pdual.pairMergeErrorUnion
        raw.data.dualBottomSource raw.data.dualTopSource radius) := by
  exact Edual.translated_rectanglePairMergeErrorUnion_measureReal_le
    muDual hTI z a b c d raw.data.dualBottomSource
      raw.data.dualTopSource radius hbox



theorem ExactExtentPairedMixedBoundaryScores.dualHorizontalMerge_translate_measureReal_le
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (hTI : Pdual.IsTranslationInvariant muDual)
    (z : Site 2) (a b c d : Real) (radius : Nat)
    (hbox : Pdual.shift z ''
        (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <=
      Edual.rectVertices a b c d) :
    muDual.real (Edual.rectanglePairMergeErrorUnion a b c d
        (raw.data.dualLeftSource.image (Pdual.shift z))
        (raw.data.dualRightSource.image (Pdual.shift z))) <=
      muDual.real (Pdual.pairMergeErrorUnion
        raw.data.dualLeftSource raw.data.dualRightSource radius) := by
  exact Edual.translated_rectanglePairMergeErrorUnion_measureReal_le
    muDual hTI z a b c d raw.data.dualLeftSource
      raw.data.dualRightSource radius hbox





theorem ExactExtentPairedMixedBoundaryScores.dualVerticalCrossing_ge_translate_inactive
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (hTI : Pdual.IsTranslationInvariant muDual)
    (z : Site 2) (a b : Real) (radius : Nat)
    (ha : a <= raw.data.wideLeft + (z 0 : Real))
    (hb : raw.data.wideRight + (z 0 : Real) <= b)
    (hbox : Pdual.shift z ''
        (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <=
      Edual.rectVertices a b (z 1 : Real)
        ((extentY : Real) + (z 1 : Real))) :
    muDual.real (Edual.rectSideConnectionEvent
        raw.data.wideLeft raw.data.wideRight 0 extentY
        (raw.data.dualBottomSource : Set W)
        (Edual.rectBottomBoundaryVertices
          raw.data.wideLeft raw.data.wideRight 0 extentY)) *
      muDual.real (Edual.rectSideConnectionEvent
        raw.data.wideLeft raw.data.wideRight 0 extentY
        (raw.data.dualTopSource : Set W)
        (Edual.rectTopBoundaryVertices
          raw.data.wideLeft raw.data.wideRight 0 extentY)) -
      muDual.real (Pdual.pairMergeErrorUnion
        raw.data.dualBottomSource raw.data.dualTopSource radius) <=
      muDual.real (Edual.verticalCrossingEvent a b (z 1 : Real)
        ((extentY : Real) + (z 1 : Real))) := by
  let bottom := raw.data.dualBottomSource.image (Pdual.shift z)
  let top := raw.data.dualTopSource.image (Pdual.shift z)
  have hcarried := Edual.verticalCrossing_ge_carriedComponents
    muDual hFKG a b (z 1 : Real) ((extentY : Real) + (z 1 : Real))
    bottom top
    (raw.data.wideLeft + (z 0 : Real))
    (raw.data.wideRight + (z 0 : Real))
    ((extentY : Real) + (z 1 : Real))
    (raw.data.wideLeft + (z 0 : Real))
    (raw.data.wideRight + (z 0 : Real)) (z 1 : Real)
    a b (z 1 : Real) ((extentY : Real) + (z 1 : Real))
    ha hb le_rfl ha hb le_rfl le_rfl le_rfl le_rfl le_rfl
  have hmerge := raw.dualVerticalMerge_translate_measureReal_le
    hTI z a b (z 1 : Real) ((extentY : Real) + (z 1 : Real))
      radius hbox
  have hbottom := Edual.rectBottomConnection_translate_measureReal_eq
    muDual hTI z raw.data.wideLeft raw.data.wideRight 0 extentY
      (raw.data.dualBottomSource : Set W)
  have htop := Edual.rectTopConnection_translate_measureReal_eq
    muDual hTI z raw.data.wideLeft raw.data.wideRight 0 extentY
      (raw.data.dualTopSource : Set W)
  have hbottom' := hbottom
  have htop' := htop
  simp only [zero_add] at hbottom' htop'
  simp only [bottom, top, Finset.coe_image] at hcarried
  rw [hbottom', htop'] at hcarried
  linarith




theorem ExactExtentPairedMixedBoundaryScores.dualHorizontalCrossing_ge_translate_inactive
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (hTI : Pdual.IsTranslationInvariant muDual)
    (z : Site 2) (c d : Real) (radius : Nat)
    (hc : c <= (z 1 : Real))
    (hd : (extentY : Real) + (z 1 : Real) <= d)
    (hbox : Pdual.shift z ''
        (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <=
      Edual.rectVertices (z 0 : Real)
        ((extentX : Real) + (z 0 : Real)) c d) :
    muDual.real (Edual.rectSideConnectionEvent 0 extentX 0 extentY
        (raw.data.dualLeftSource : Set W)
        (Edual.rectLeftBoundaryVertices 0 extentX 0 extentY)) *
      muDual.real (Edual.rectSideConnectionEvent 0 extentX 0 extentY
        (raw.data.dualRightSource : Set W)
        (Edual.rectRightBoundaryVertices 0 extentX 0 extentY)) -
      muDual.real (Pdual.pairMergeErrorUnion
        raw.data.dualLeftSource raw.data.dualRightSource radius) <=
      muDual.real (Edual.horizontalCrossingEvent
        (z 0 : Real) ((extentX : Real) + (z 0 : Real)) c d) := by
  let left := raw.data.dualLeftSource.image (Pdual.shift z)
  let right := raw.data.dualRightSource.image (Pdual.shift z)
  have hcarried := Edual.horizontalCrossing_ge_carriedComponents
    muDual hFKG (z 0 : Real) ((extentX : Real) + (z 0 : Real)) c d
    left right
    ((extentX : Real) + (z 0 : Real)) (z 1 : Real)
    ((extentY : Real) + (z 1 : Real)) (z 0 : Real) (z 1 : Real)
    ((extentY : Real) + (z 1 : Real))
    (z 0 : Real) ((extentX : Real) + (z 0 : Real)) c d
    le_rfl hc hd le_rfl hc hd le_rfl le_rfl le_rfl le_rfl
  have hmerge := raw.dualHorizontalMerge_translate_measureReal_le
    hTI z (z 0 : Real) ((extentX : Real) + (z 0 : Real)) c d
      radius hbox
  have hleft := Edual.rectLeftConnection_translate_measureReal_eq
    muDual hTI z 0 extentX 0 extentY
      (raw.data.dualLeftSource : Set W)
  have hright := Edual.rectRightConnection_translate_measureReal_eq
    muDual hTI z 0 extentX 0 extentY
      (raw.data.dualRightSource : Set W)
  have hleft' := hleft
  have hright' := hright
  simp only [zero_add] at hleft' hright'
  simp only [left, right, Finset.coe_image] at hcarried
  rw [hleft', hright'] at hcarried
  linarith





theorem dualVerticalCrossing_translate_inactive_tendsto_one
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG muDual) (hTI : Pdual.IsTranslationInvariant muDual)
    (S : Nat -> Finset V) (Sdual : Nat -> Finset W)
    (p pDual : Nat -> Real) (extentX extentY radius : Nat -> Nat)
    (raw : forall n, ExactExtentPairedMixedBoundaryScores
      E Edual mu muDual (S n) (Sdual n) (p n) (pDual n)
        (extentX n) (extentY n))
    (hpDual : Tendsto pDual atTop (nhds 1))
    (z : Nat -> Site 2) (a b : Nat -> Real)
    (ha : forall n,
      a n <= (raw n).data.wideLeft + (z n 0 : Real))
    (hb : forall n,
      (raw n).data.wideRight + (z n 0 : Real) <= b n)
    (hbox : forall n, Pdual.shift (z n) ''
        (Pdual.orbitBox (Pdual.bufferedRadius (radius n)) : Set W) <=
      Edual.rectVertices (a n) (b n) (z n 1 : Real)
        ((extentY n : Real) + (z n 1 : Real)))
    (hmerge : Tendsto (fun n => muDual.real
      (Pdual.pairMergeErrorUnion (raw n).data.dualBottomSource
        (raw n).data.dualTopSource (radius n))) atTop (nhds 0)) :
    Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent
      (a n) (b n) (z n 1 : Real)
        ((extentY n : Real) + (z n 1 : Real)))) atTop (nhds 1) := by
  let bottomScore : Nat -> Real := fun n => muDual.real
    (Edual.rectSideConnectionEvent
      (raw n).data.wideLeft (raw n).data.wideRight 0 (extentY n)
      ((raw n).data.dualBottomSource : Set W)
      (Edual.rectBottomBoundaryVertices
        (raw n).data.wideLeft (raw n).data.wideRight 0 (extentY n)))
  let topScore : Nat -> Real := fun n => muDual.real
    (Edual.rectSideConnectionEvent
      (raw n).data.wideLeft (raw n).data.wideRight 0 (extentY n)
      ((raw n).data.dualTopSource : Set W)
      (Edual.rectTopBoundaryVertices
        (raw n).data.wideLeft (raw n).data.wideRight 0 (extentY n)))
  have hbottom : Tendsto bottomScore atTop (nhds 1) :=
    hpDual.squeeze tendsto_const_nhds
      (fun n => by
        simpa [bottomScore, (raw n).shortTop_eq] using
          le_of_lt (raw n).data.dualBottomScore)
      (fun _ => measureReal_le_one)
  have htop : Tendsto topScore atTop (nhds 1) :=
    hpDual.squeeze tendsto_const_nhds
      (fun n => by
        simpa [topScore, (raw n).shortTop_eq] using
          le_of_lt (raw n).data.dualTopScore)
      (fun _ => measureReal_le_one)
  have hlower : Tendsto (fun n => bottomScore n * topScore n -
      muDual.real (Pdual.pairMergeErrorUnion
        (raw n).data.dualBottomSource (raw n).data.dualTopSource
          (radius n))) atTop (nhds 1) := by
    convert hbottom.mul htop |>.sub hmerge using 1 <;> norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlower tendsto_const_nhds
    (fun n => by
      simpa only [bottomScore, topScore] using
        (raw n).dualVerticalCrossing_ge_translate_inactive
          hFKG hTI (z n) (a n) (b n) (radius n)
            (ha n) (hb n) (hbox n))
    (fun _ => measureReal_le_one)



theorem dualHorizontalCrossing_translate_inactive_tendsto_one
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG muDual) (hTI : Pdual.IsTranslationInvariant muDual)
    (S : Nat -> Finset V) (Sdual : Nat -> Finset W)
    (p pDual : Nat -> Real) (extentX extentY radius : Nat -> Nat)
    (raw : forall n, ExactExtentPairedMixedBoundaryScores
      E Edual mu muDual (S n) (Sdual n) (p n) (pDual n)
        (extentX n) (extentY n))
    (hpDual : Tendsto pDual atTop (nhds 1))
    (z : Nat -> Site 2) (c d : Nat -> Real)
    (hc : forall n, c n <= (z n 1 : Real))
    (hd : forall n, (extentY n : Real) + (z n 1 : Real) <= d n)
    (hbox : forall n, Pdual.shift (z n) ''
        (Pdual.orbitBox (Pdual.bufferedRadius (radius n)) : Set W) <=
      Edual.rectVertices (z n 0 : Real)
        ((extentX n : Real) + (z n 0 : Real)) (c n) (d n))
    (hmerge : Tendsto (fun n => muDual.real
      (Pdual.pairMergeErrorUnion (raw n).data.dualLeftSource
        (raw n).data.dualRightSource (radius n))) atTop (nhds 0)) :
    Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent
      (z n 0 : Real) ((extentX n : Real) + (z n 0 : Real))
        (c n) (d n))) atTop (nhds 1) := by
  let leftScore : Nat -> Real := fun n => muDual.real
    (Edual.rectSideConnectionEvent 0 (extentX n) 0 (extentY n)
      ((raw n).data.dualLeftSource : Set W)
      (Edual.rectLeftBoundaryVertices 0 (extentX n) 0 (extentY n)))
  let rightScore : Nat -> Real := fun n => muDual.real
    (Edual.rectSideConnectionEvent 0 (extentX n) 0 (extentY n)
      ((raw n).data.dualRightSource : Set W)
      (Edual.rectRightBoundaryVertices 0 (extentX n) 0 (extentY n)))
  have hleft : Tendsto leftScore atTop (nhds 1) :=
    hpDual.squeeze tendsto_const_nhds
      (fun n => by
        simpa [leftScore, (raw n).narrowRight_eq,
          (raw n).tallTop_eq] using le_of_lt (raw n).data.dualLeftScore)
      (fun _ => measureReal_le_one)
  have hright : Tendsto rightScore atTop (nhds 1) :=
    hpDual.squeeze tendsto_const_nhds
      (fun n => by
        simpa [rightScore, (raw n).narrowRight_eq,
          (raw n).tallTop_eq] using le_of_lt (raw n).data.dualRightScore)
      (fun _ => measureReal_le_one)
  have hlower : Tendsto (fun n => leftScore n * rightScore n -
      muDual.real (Pdual.pairMergeErrorUnion
        (raw n).data.dualLeftSource (raw n).data.dualRightSource
          (radius n))) atTop (nhds 1) := by
    convert hleft.mul hright |>.sub hmerge using 1 <;> norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlower tendsto_const_nhds
    (fun n => by
      simpa only [leftScore, rightScore] using
        (raw n).dualHorizontalCrossing_ge_translate_inactive
          hFKG hTI (z n) (c n) (d n) (radius n)
            (hc n) (hd n) (hbox n))
    (fun _ => measureReal_le_one)


noncomputable def pairedWideSpanAtExtentX
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k extentX : Nat) : Int :=
  pairedWideRightAtExtentX E Edual family familyDual schedule k extentX -
    pairedWideLeftAtExtentX E Edual family familyDual schedule k extentX

theorem AlignedExactExtentPairedMixedBoundaryScores.wideSpan_formula
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k extentX extentY : Nat}
    (data : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY) :
    data.raw.wideRightInt - data.raw.wideLeftInt =
      pairedWideSpanAtExtentX E Edual family familyDual schedule k extentX := by
  rw [data.wideRight_formula, data.wideLeft_formula]
  rfl




theorem AlignedExactExtentPairedMixedBoundaryScores.dualLeftSource_transport
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k k' extentX extentY extentX' extentY' : Nat}
    (old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k' extentX' extentY') :
    new.raw.data.dualLeftSource =
      old.raw.data.dualLeftSource.image (Pdual.shift
        (horizontalShift ((schedule.horizontal k' : Int) -
          schedule.horizontal k) +
        verticalShift ((schedule.vertical k' : Int) -
          schedule.vertical k))) := by
  classical
  let delta : Int := (schedule.horizontal k' : Int) -
    schedule.horizontal k
  have hbase : new.raw.data.baseDual =
      old.raw.data.baseDual + horizontalShift delta +
        verticalShift ((schedule.vertical k' : Int) -
          schedule.vertical k) := by
    funext i
    fin_cases i
    · change new.raw.data.baseDual 0 =
        (old.raw.data.baseDual + horizontalShift delta +
          verticalShift ((schedule.vertical k' : Int) -
            schedule.vertical k)) 0
      rw [new.dualBaseX_eq]
      simp only [Pi.add_apply, horizontalShift, verticalShift, delta]
      rw [old.dualBaseX_eq]
      norm_num
    · change new.raw.data.baseDual 1 =
        (old.raw.data.baseDual + horizontalShift delta +
          verticalShift ((schedule.vertical k' : Int) -
            schedule.vertical k)) 1
      rw [new.dualBaseY_eq]
      simp only [Pi.add_apply, horizontalShift, verticalShift, delta]
      rw [old.dualBaseY_eq]
      norm_num
  simp only [PairedMixedBoundaryScores.dualLeftSource,
    Finset.image_image]
  apply Finset.image_congr
  intro u hu
  rw [hbase]
  simp only [Function.comp_apply]
  rw [<- Pdual.shift_add]
  apply congrArg (fun z => Pdual.shift z u)
  abel




theorem AlignedExactExtentPairedMixedBoundaryScores.dualRightSource_transport
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k k' extentX extentY extentX' extentY' : Nat}
    (old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k' extentX' extentY')
    (hExtentX : (extentX' : Int) = extentX +
      2 * ((schedule.horizontal k' : Int) - schedule.horizontal k)) :
    new.raw.data.dualRightSource =
      old.raw.data.dualRightSource.image (Pdual.shift
        (horizontalShift ((schedule.horizontal k' : Int) -
          schedule.horizontal k) +
        verticalShift ((schedule.vertical k' : Int) -
          schedule.vertical k))) := by
  classical
  let deltaH : Int := (schedule.horizontal k' : Int) -
    schedule.horizontal k
  let deltaV : Int := (schedule.vertical k' : Int) -
    schedule.vertical k
  have hsite : new.raw.data.baseDual + preferenceGridSite
        (Fin.last new.raw.data.widthDual,
          (0 : Fin (new.raw.data.heightDual + 1))) =
      old.raw.data.baseDual + preferenceGridSite
        (Fin.last old.raw.data.widthDual,
          (0 : Fin (old.raw.data.heightDual + 1))) +
        horizontalShift deltaH + verticalShift deltaV := by
    funext i
    fin_cases i
    · simp only [Pi.add_apply, preferenceGridSite,
        horizontalShift, verticalShift]
      norm_num
      rw [new.dualEndX_eq, old.dualEndX_eq]
      dsimp only [deltaH] at hExtentX ⊢
      omega
    · simp only [Pi.add_apply, preferenceGridSite,
        horizontalShift, verticalShift]
      norm_num
      rw [new.dualBaseY_eq, old.dualBaseY_eq]
      dsimp only [deltaV]
      omega
  simp only [PairedMixedBoundaryScores.dualRightSource,
    Finset.image_image]
  apply Finset.image_congr
  intro u hu
  rw [hsite]
  simp only [Function.comp_apply]
  rw [<- Pdual.shift_add]
  apply congrArg (fun z => Pdual.shift z u)
  abel



theorem AlignedExactExtentPairedMixedBoundaryScores.dualBottomSource_transport
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k k' extentX extentY extentX' extentY' : Nat}
    (old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k' extentX' extentY') :
    new.raw.data.dualBottomSource =
      old.raw.data.dualBottomSource.image (Pdual.shift
        (horizontalShift ((schedule.horizontal k' : Int) -
          schedule.horizontal k) +
        verticalShift ((schedule.vertical k' : Int) -
          schedule.vertical k))) := by
  simpa only [PairedMixedBoundaryScores.dualBottomSource,
    PairedMixedBoundaryScores.dualLeftSource] using
      old.dualLeftSource_transport new




theorem AlignedExactExtentPairedMixedBoundaryScores.dualTopSource_transport
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k k' extentX extentY extentX' extentY' : Nat}
    (old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k' extentX' extentY')
    (hExtentY : (extentY' : Int) = extentY +
      2 * ((schedule.vertical k' : Int) - schedule.vertical k)) :
    new.raw.data.dualTopSource =
      old.raw.data.dualTopSource.image (Pdual.shift
        (horizontalShift ((schedule.horizontal k' : Int) -
          schedule.horizontal k) +
        verticalShift ((schedule.vertical k' : Int) -
          schedule.vertical k))) := by
  classical
  let deltaH : Int := (schedule.horizontal k' : Int) -
    schedule.horizontal k
  let deltaV : Int := (schedule.vertical k' : Int) -
    schedule.vertical k
  have hsite : new.raw.data.baseDual + preferenceGridSite
        ((0 : Fin (new.raw.data.widthDual + 1)),
          Fin.last new.raw.data.heightDual) =
      old.raw.data.baseDual + preferenceGridSite
        ((0 : Fin (old.raw.data.widthDual + 1)),
          Fin.last old.raw.data.heightDual) +
        horizontalShift deltaH + verticalShift deltaV := by
    funext i
    fin_cases i
    · simp only [Pi.add_apply, preferenceGridSite,
        horizontalShift, verticalShift]
      norm_num
      rw [new.dualBaseX_eq, old.dualBaseX_eq]
      dsimp only [deltaH]
      omega
    · simp only [Pi.add_apply, preferenceGridSite,
        horizontalShift, verticalShift]
      norm_num
      rw [new.dualEndY_eq, old.dualEndY_eq]
      dsimp only [deltaV] at hExtentY ⊢
      omega
  simp only [PairedMixedBoundaryScores.dualTopSource,
    Finset.image_image]
  apply Finset.image_congr
  intro u hu
  rw [hsite]
  simp only [Function.comp_apply]
  rw [<- Pdual.shift_add]
  apply congrArg (fun z => Pdual.shift z u)
  abel





theorem AlignedExactExtentPairedMixedBoundaryScores.dualVerticalMerge_transport_measureReal_le
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    (hTI : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k k' extentX extentY extentX' extentY' radius : Nat}
    (old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k' extentX' extentY')
    (hExtentY : (extentY' : Int) = extentY +
      2 * ((schedule.vertical k' : Int) - schedule.vertical k))
    (hbox : Pdual.shift
      (horizontalShift ((schedule.horizontal k' : Int) -
          schedule.horizontal k) +
        verticalShift ((schedule.vertical k' : Int) -
          schedule.vertical k)) ''
        (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <=
      Edual.rectVertices new.raw.data.wideLeft
        new.raw.data.wideRight 0 extentY') :
    muDual.real (Edual.rectanglePairMergeErrorUnion
        new.raw.data.wideLeft new.raw.data.wideRight 0 extentY'
        new.raw.data.dualBottomSource new.raw.data.dualTopSource) <=
      muDual.real (Pdual.pairMergeErrorUnion
        old.raw.data.dualBottomSource old.raw.data.dualTopSource radius) := by
  let z : Site 2 :=
    horizontalShift ((schedule.horizontal k' : Int) -
        schedule.horizontal k) +
      verticalShift ((schedule.vertical k' : Int) - schedule.vertical k)
  have hbound := old.raw.dualVerticalMerge_translate_measureReal_le
    hTI z new.raw.data.wideLeft new.raw.data.wideRight 0 extentY'
      radius hbox
  rw [old.dualBottomSource_transport new,
    old.dualTopSource_transport new hExtentY]
  simpa only [z] using hbound



theorem AlignedExactExtentPairedMixedBoundaryScores.dualHorizontalMerge_transport_measureReal_le
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    (hTI : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k k' extentX extentY extentX' extentY' radius : Nat}
    (old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k' extentX' extentY')
    (hExtentX : (extentX' : Int) = extentX +
      2 * ((schedule.horizontal k' : Int) - schedule.horizontal k))
    (hbox : Pdual.shift
      (horizontalShift ((schedule.horizontal k' : Int) -
          schedule.horizontal k) +
        verticalShift ((schedule.vertical k' : Int) -
          schedule.vertical k)) ''
        (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <=
      Edual.rectVertices 0 extentX' 0 extentY') :
    muDual.real (Edual.rectanglePairMergeErrorUnion 0 extentX' 0 extentY'
        new.raw.data.dualLeftSource new.raw.data.dualRightSource) <=
      muDual.real (Pdual.pairMergeErrorUnion
        old.raw.data.dualLeftSource old.raw.data.dualRightSource radius) := by
  let z : Site 2 :=
    horizontalShift ((schedule.horizontal k' : Int) -
        schedule.horizontal k) +
      verticalShift ((schedule.vertical k' : Int) - schedule.vertical k)
  have hbound := old.raw.dualHorizontalMerge_translate_measureReal_le
    hTI z 0 extentX' 0 extentY' radius hbox
  rw [old.dualLeftSource_transport new,
    old.dualRightSource_transport new hExtentX]
  simpa only [z] using hbound



structure AlignedNormalRotatedInsetPairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (S : Finset V) (Sdual : Finset W) (p pDual : Real)
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding : Nat) where
  normalX : Nat
  rotatedX : Nat
  normalY : Nat
  rotatedY : Nat
  normal : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual family familyDual schedule k normalX normalY
  rotated : AlignedExactExtentPairedMixedBoundaryScores
    E.axisSwap Edual.axisSwap mu muDual S Sdual p pDual
    family.axisSwap familyDual.axisSwap schedule.axisSwap k rotatedX rotatedY
  normalSpan_eq : normal.raw.wideRightInt - normal.raw.wideLeftInt =
    rotatedY + 2 * padding
  rotatedSpan_eq : rotated.raw.wideRightInt - rotated.raw.wideLeftInt =
    normalY




theorem nonempty_alignedNormalRotatedInsetPairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding : Nat) :
    Nonempty (AlignedNormalRotatedInsetPairedMixedBoundaryScores
      E Edual mu muDual S Sdual p pDual family familyDual schedule k
      padding) := by
  obtain ⟨normalThresholdX, normalThresholdY, hnormal⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E Edual mu muDual hTI hTIDual family familyDual schedule k
  obtain ⟨rotatedThresholdX, rotatedThresholdY, hrotated⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E.axisSwap Edual.axisSwap mu muDual
      (P.axisSwap_isTranslationInvariant mu hTI)
      (Pdual.axisSwap_isTranslationInvariant muDual hTIDual)
      family.axisSwap familyDual.axisSwap schedule.axisSwap k
  let normalX := max normalThresholdX (rotatedThresholdY + 2 * padding)
  let rotatedX := max rotatedThresholdX normalThresholdY
  let normalProbe := Classical.choice
    (hnormal (Nat.le_max_left _ _) le_rfl :
      Nonempty (AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
        S Sdual p pDual family familyDual schedule k normalX
        normalThresholdY))
  let rotatedProbe := Classical.choice
    (hrotated (Nat.le_max_left _ _) le_rfl :
      Nonempty (AlignedExactExtentPairedMixedBoundaryScores
        E.axisSwap Edual.axisSwap mu muDual S Sdual p pDual
        family.axisSwap familyDual.axisSwap schedule.axisSwap k rotatedX
        rotatedThresholdY))
  let normalSpan := pairedWideSpanAtExtentX E Edual family familyDual
    schedule k normalX
  let rotatedSpan := pairedWideSpanAtExtentX E.axisSwap Edual.axisSwap
    family.axisSwap familyDual.axisSwap schedule.axisSwap k rotatedX
  have hnormalXSpan : (normalX : Int) <= normalSpan := by
    calc
      (normalX : Int) <= normalProbe.raw.wideRightInt -
          normalProbe.raw.wideLeftInt :=
        normalProbe.raw.extentX_le_wideSpan
      _ = normalSpan := by
        simpa only [normalSpan] using normalProbe.wideSpan_formula
  have hrotatedXSpan : (rotatedX : Int) <= rotatedSpan := by
    calc
      (rotatedX : Int) <= rotatedProbe.raw.wideRightInt -
          rotatedProbe.raw.wideLeftInt :=
        rotatedProbe.raw.extentX_le_wideSpan
      _ = rotatedSpan := by
        simpa only [rotatedSpan] using rotatedProbe.wideSpan_formula
  have hnormalSpanPadding : (2 * padding : Int) <= normalSpan := by
    have hX : rotatedThresholdY + 2 * padding <= normalX :=
      Nat.le_max_right _ _
    have hcast : (2 * padding : Int) <= (normalX : Int) := by
      exact_mod_cast (show 2 * padding <= normalX by omega)
    exact hcast.trans hnormalXSpan
  let rotatedY := (normalSpan - 2 * (padding : Int)).toNat
  let normalY := rotatedSpan.toNat
  have hrotatedThresholdY : rotatedThresholdY <= rotatedY := by
    have hX : rotatedThresholdY + 2 * padding <= normalX :=
      Nat.le_max_right _ _
    have hcastX : (rotatedThresholdY + 2 * padding : Int) <=
        (normalX : Int) := by
      exact_mod_cast hX
    have hcast : (rotatedThresholdY + 2 * padding : Int) <= normalSpan :=
      hcastX.trans hnormalXSpan
    have hnonneg : 0 <= normalSpan - 2 * (padding : Int) := by omega
    have hcastY : (rotatedThresholdY : Int) <= (rotatedY : Int) := by
      change (rotatedThresholdY : Int) <=
        ((normalSpan - 2 * (padding : Int)).toNat : Int)
      rw [Int.toNat_of_nonneg hnonneg]
      omega
    exact_mod_cast hcastY
  have hnormalThresholdY : normalThresholdY <= normalY := by
    have hX : normalThresholdY <= rotatedX := Nat.le_max_right _ _
    have hcastX : (normalThresholdY : Int) <= (rotatedX : Int) := by
      exact_mod_cast hX
    have hcast : (normalThresholdY : Int) <= rotatedSpan :=
      hcastX.trans hrotatedXSpan
    have hnonneg : 0 <= rotatedSpan := by
      exact (show (0 : Int) <= (rotatedX : Int) by omega).trans
        hrotatedXSpan
    have hcastY : (normalThresholdY : Int) <= (normalY : Int) := by
      change (normalThresholdY : Int) <= (rotatedSpan.toNat : Int)
      rw [Int.toNat_of_nonneg hnonneg]
      exact hcast
    exact_mod_cast hcastY
  let normal := Classical.choice
    (hnormal (Nat.le_max_left _ _) hnormalThresholdY :
      Nonempty (AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
        S Sdual p pDual family familyDual schedule k normalX normalY))
  let rotated := Classical.choice
    (hrotated (Nat.le_max_left _ _) hrotatedThresholdY :
      Nonempty (AlignedExactExtentPairedMixedBoundaryScores
        E.axisSwap Edual.axisSwap mu muDual S Sdual p pDual
        family.axisSwap familyDual.axisSwap schedule.axisSwap k rotatedX
        rotatedY))
  refine ⟨{
    normalX := normalX
    rotatedX := rotatedX
    normalY := normalY
    rotatedY := rotatedY
    normal := normal
    rotated := rotated
    normalSpan_eq := ?_
    rotatedSpan_eq := ?_ }⟩
  · rw [normal.wideSpan_formula]
    change normalSpan = (rotatedY : Int) + 2 * (padding : Int)
    have hnonneg : 0 <= normalSpan - 2 * (padding : Int) := by
      exact sub_nonneg.mpr hnormalSpanPadding
    change normalSpan =
      ((normalSpan - 2 * (padding : Int)).toNat : Int) +
        2 * (padding : Int)
    rw [Int.toNat_of_nonneg hnonneg]
    omega
  · rw [rotated.wideSpan_formula]
    change rotatedSpan = (normalY : Int)
    have hnonneg : 0 <= rotatedSpan := by
      exact (show (0 : Int) <= (rotatedX : Int) by omega).trans
        hrotatedXSpan
    change rotatedSpan = (rotatedSpan.toNat : Int)
    rw [Int.toNat_of_nonneg hnonneg]







structure AlignedNormalTwoRotatedEndpointPairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (S : Finset V) (Sdual : Finset W) (p pDual : Real)
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k : Nat) where
  normalX : Nat
  normalY : Nat
  rotatedHorizontalX : Nat
  rotatedHorizontalY : Nat
  normal : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual family familyDual schedule k normalX normalY
  rotatedVertical : AlignedExactExtentPairedMixedBoundaryScores
    E.axisSwap Edual.axisSwap mu muDual S Sdual p pDual
    family.axisSwap familyDual.axisSwap schedule.axisSwap k normalY normalX
  rotatedHorizontal : AlignedExactExtentPairedMixedBoundaryScores
    E.axisSwap Edual.axisSwap mu muDual S Sdual p pDual
    family.axisSwap familyDual.axisSwap schedule.axisSwap k
    rotatedHorizontalX rotatedHorizontalY
  normalSpan_eq : normal.raw.wideRightInt - normal.raw.wideLeftInt =
    rotatedHorizontalY
  rotatedHorizontalSpan_eq :
    rotatedHorizontal.raw.wideRightInt -
      rotatedHorizontal.raw.wideLeftInt = normalY




theorem nonempty_alignedNormalTwoRotatedEndpointPairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k : Nat) :
    Nonempty (AlignedNormalTwoRotatedEndpointPairedMixedBoundaryScores
      E Edual mu muDual S Sdual p pDual family familyDual schedule k) := by
  obtain ⟨normalThresholdX, normalThresholdY, hnormal⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E Edual mu muDual hTI hTIDual family familyDual schedule k
  obtain ⟨rotatedThresholdX, rotatedThresholdY, hrotated⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E.axisSwap Edual.axisSwap mu muDual
      (P.axisSwap_isTranslationInvariant mu hTI)
      (Pdual.axisSwap_isTranslationInvariant muDual hTIDual)
      family.axisSwap familyDual.axisSwap schedule.axisSwap k
  let normalX := max normalThresholdX rotatedThresholdY
  let rotatedHorizontalX := max rotatedThresholdX normalThresholdY
  let normalProbe := Classical.choice
    (hnormal (Nat.le_max_left _ _) le_rfl :
      Nonempty (AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
        S Sdual p pDual family familyDual schedule k normalX
        normalThresholdY))
  let rotatedProbe := Classical.choice
    (hrotated (Nat.le_max_left _ _) le_rfl :
      Nonempty (AlignedExactExtentPairedMixedBoundaryScores
        E.axisSwap Edual.axisSwap mu muDual S Sdual p pDual
        family.axisSwap familyDual.axisSwap schedule.axisSwap k
        rotatedHorizontalX rotatedThresholdY))
  let normalSpan := normalProbe.raw.wideRightInt -
    normalProbe.raw.wideLeftInt
  let rotatedHorizontalSpan := rotatedProbe.raw.wideRightInt -
    rotatedProbe.raw.wideLeftInt
  have hnormalSpan : 0 <= normalSpan := by
    exact (show (0 : Int) <= (normalX : Int) by omega).trans
      normalProbe.raw.extentX_le_wideSpan
  have hrotatedHorizontalSpan : 0 <= rotatedHorizontalSpan := by
    exact (show (0 : Int) <= (rotatedHorizontalX : Int) by omega).trans
      rotatedProbe.raw.extentX_le_wideSpan
  let normalY := rotatedHorizontalSpan.toNat
  let rotatedHorizontalY := normalSpan.toNat
  have hnormalThresholdY : normalThresholdY <= normalY := by
    have hX : normalThresholdY <= rotatedHorizontalX :=
      Nat.le_max_right _ _
    have hspan : (rotatedHorizontalX : Int) <=
        rotatedHorizontalSpan := by
      simpa only [rotatedHorizontalSpan] using
        rotatedProbe.raw.extentX_le_wideSpan
    have hXInt : (normalThresholdY : Int) <= rotatedHorizontalX := by
      exact_mod_cast hX
    rw [Int.le_toNat hrotatedHorizontalSpan]
    exact_mod_cast hXInt.trans hspan
  have hrotatedThresholdY : rotatedThresholdY <= rotatedHorizontalY := by
    have hX : rotatedThresholdY <= normalX := Nat.le_max_right _ _
    have hspan : (normalX : Int) <= normalSpan := by
      simpa only [normalSpan] using normalProbe.raw.extentX_le_wideSpan
    have hXInt : (rotatedThresholdY : Int) <= normalX := by
      exact_mod_cast hX
    rw [Int.le_toNat hnormalSpan]
    exact_mod_cast hXInt.trans hspan
  have hrotatedThresholdX : rotatedThresholdX <= normalY := by
    have hX : rotatedThresholdX <= rotatedHorizontalX :=
      Nat.le_max_left _ _
    have hspan : (rotatedHorizontalX : Int) <=
        rotatedHorizontalSpan := by
      simpa only [rotatedHorizontalSpan] using
        rotatedProbe.raw.extentX_le_wideSpan
    have hXInt : (rotatedThresholdX : Int) <= rotatedHorizontalX := by
      exact_mod_cast hX
    rw [Int.le_toNat hrotatedHorizontalSpan]
    exact_mod_cast hXInt.trans hspan
  let normal := Classical.choice
    (hnormal (extentX := normalX) (extentY := normalY)
      (Nat.le_max_left _ _) hnormalThresholdY)
  let rotatedVertical := Classical.choice
    (hrotated (extentX := normalY) (extentY := normalX)
      hrotatedThresholdX (Nat.le_max_right _ _))
  let rotatedHorizontal := Classical.choice
    (hrotated (extentX := rotatedHorizontalX)
      (extentY := rotatedHorizontalY)
      (Nat.le_max_left _ _) hrotatedThresholdY)
  refine ⟨{
    normalX := normalX
    normalY := normalY
    rotatedHorizontalX := rotatedHorizontalX
    rotatedHorizontalY := rotatedHorizontalY
    normal := normal
    rotatedVertical := rotatedVertical
    rotatedHorizontal := rotatedHorizontal
    normalSpan_eq := ?_
    rotatedHorizontalSpan_eq := ?_ }⟩
  · calc
      normal.raw.wideRightInt - normal.raw.wideLeftInt =
          pairedWideSpanAtExtentX E Edual family familyDual schedule k
            normalX := normal.wideSpan_formula
      _ = normalSpan := by
        symm
        simpa only [normalSpan] using normalProbe.wideSpan_formula
      _ = (rotatedHorizontalY : Int) := by
        rw [Int.toNat_of_nonneg hnormalSpan]
  · calc
      rotatedHorizontal.raw.wideRightInt -
          rotatedHorizontal.raw.wideLeftInt =
          pairedWideSpanAtExtentX E.axisSwap Edual.axisSwap
            family.axisSwap familyDual.axisSwap schedule.axisSwap k
            rotatedHorizontalX := rotatedHorizontal.wideSpan_formula
      _ = rotatedHorizontalSpan := by
        symm
        simpa only [rotatedHorizontalSpan] using
          rotatedProbe.wideSpan_formula
      _ = (normalY : Int) := by
        rw [Int.toNat_of_nonneg hrotatedHorizontalSpan]



theorem PeriodicPlaneEmbedding.horizontalCrossing_translate_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    (a b c d : Real) :
    mu.real (E.horizontalCrossingEvent a b c d) <=
      mu.real (E.horizontalCrossingEvent
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))) := by
  let A := E.horizontalCrossingEvent a b c d
  let translated := E.horizontalCrossingEvent
    (a + (z 0 : Real)) (b + (z 0 : Real))
    (c + (z 1 : Real)) (d + (z 1 : Real))
  have hsub : A <= P.translateEvent z translated := by
    intro omega homega
    change E.rectRestrict a b c d omega ∈
      E.finiteHorizontalCrossing a b c d at homega
    obtain ⟨x, y, hxLeft, hyRight, hxy⟩ := homega
    have hx' : P.shift z x.1 ∈ E.rectVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) :=
      (E.shift_mem_rectVertices z a b c d x.1).2 x.2
    have hy' : P.shift z y.1 ∈ E.rectVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) :=
      (E.shift_mem_rectVertices z a b c d y.1).2 y.2
    have hxBoundary := (E.shift_mem_rectLeftBoundaryVertices
      z a b c d x.1).2 ⟨x.2, hxLeft⟩
    have hyBoundary := (E.shift_mem_rectRightBoundaryVertices
      z a b c d y.1).2 ⟨y.2, hyRight⟩
    rw [E.openSub_rectRestrict_eq_induce] at hxy
    obtain ⟨path⟩ := hxy
    let ambientPath : (P.openSubgraph omega).Walk x.1 y.1 :=
      path.map (SimpleGraph.Embedding.induce
        (E.rectVertices a b c d)).toHom
    let translatedPath :=
      ambientPath.map (P.openSubgraphTranslateHom z omega)
    have htranslatedPath : ∀ v ∈ translatedPath.support,
        v ∈ E.rectVertices
          (a + (z 0 : Real)) (b + (z 0 : Real))
          (c + (z 1 : Real)) (d + (z 1 : Real)) := by
      intro v hv
      simp only [translatedPath, SimpleGraph.Walk.support_map,
        List.mem_map] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      change w ∈ (path.map (SimpleGraph.Embedding.induce
        (E.rectVertices a b c d)).toHom).support at hw
      rw [SimpleGraph.Walk.support_map] at hw
      obtain ⟨u, _hu, huw⟩ := List.mem_map.mp hw
      rw [← huw]
      exact (E.shift_mem_rectVertices z a b c d u.1).2 u.2
    change E.rectRestrict
      (a + (z 0 : Real)) (b + (z 0 : Real))
      (c + (z 1 : Real)) (d + (z 1 : Real))
      (P.configTranslate z omega) ∈ E.finiteHorizontalCrossing
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))
    refine ⟨⟨P.shift z x.1, hx'⟩, ⟨P.shift z y.1, hy'⟩,
      hxBoundary.2, hyBoundary.2, ?_⟩
    rw [E.openSub_rectRestrict_eq_induce]
    exact ⟨translatedPath.induce _ htranslatedPath⟩
  have hmeasure : mu.real A <=
      mu.real (P.translateEvent z translated) := measureReal_mono hsub
  change mu.real A <= mu.real translated
  calc
    mu.real A <= mu.real (P.translateEvent z translated) := hmeasure
    _ = mu.real translated := by
      unfold Measure.real
      rw [P.translateEvent_measure_eq mu hTI z
        (E.horizontalCrossingEvent_measurableSet _ _ _ _)]



theorem PeriodicPlaneEmbedding.verticalCrossing_translate_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    (a b c d : Real) :
    mu.real (E.verticalCrossingEvent a b c d) <=
      mu.real (E.verticalCrossingEvent
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))) := by
  let A := E.verticalCrossingEvent a b c d
  let translated := E.verticalCrossingEvent
    (a + (z 0 : Real)) (b + (z 0 : Real))
    (c + (z 1 : Real)) (d + (z 1 : Real))
  have hsub : A <= P.translateEvent z translated := by
    intro omega homega
    change E.rectRestrict a b c d omega ∈
      E.finiteVerticalCrossing a b c d at homega
    obtain ⟨x, y, hxBottom, hyTop, hxy⟩ := homega
    have hx' : P.shift z x.1 ∈ E.rectVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) :=
      (E.shift_mem_rectVertices z a b c d x.1).2 x.2
    have hy' : P.shift z y.1 ∈ E.rectVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) :=
      (E.shift_mem_rectVertices z a b c d y.1).2 y.2
    have hxBoundary := (E.shift_mem_rectBottomBoundaryVertices
      z a b c d x.1).2 ⟨x.2, hxBottom⟩
    have hyBoundary := (E.shift_mem_rectTopBoundaryVertices
      z a b c d y.1).2 ⟨y.2, hyTop⟩
    rw [E.openSub_rectRestrict_eq_induce] at hxy
    obtain ⟨path⟩ := hxy
    let ambientPath : (P.openSubgraph omega).Walk x.1 y.1 :=
      path.map (SimpleGraph.Embedding.induce
        (E.rectVertices a b c d)).toHom
    let translatedPath :=
      ambientPath.map (P.openSubgraphTranslateHom z omega)
    have htranslatedPath : ∀ v ∈ translatedPath.support,
        v ∈ E.rectVertices
          (a + (z 0 : Real)) (b + (z 0 : Real))
          (c + (z 1 : Real)) (d + (z 1 : Real)) := by
      intro v hv
      simp only [translatedPath, SimpleGraph.Walk.support_map,
        List.mem_map] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      change w ∈ (path.map (SimpleGraph.Embedding.induce
        (E.rectVertices a b c d)).toHom).support at hw
      rw [SimpleGraph.Walk.support_map] at hw
      obtain ⟨u, _hu, huw⟩ := List.mem_map.mp hw
      rw [← huw]
      exact (E.shift_mem_rectVertices z a b c d u.1).2 u.2
    change E.rectRestrict
      (a + (z 0 : Real)) (b + (z 0 : Real))
      (c + (z 1 : Real)) (d + (z 1 : Real))
      (P.configTranslate z omega) ∈ E.finiteVerticalCrossing
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))
    refine ⟨⟨P.shift z x.1, hx'⟩, ⟨P.shift z y.1, hy'⟩,
      hxBoundary.2, hyBoundary.2, ?_⟩
    rw [E.openSub_rectRestrict_eq_induce]
    exact ⟨translatedPath.induce _ htranslatedPath⟩
  have hmeasure : mu.real A <=
      mu.real (P.translateEvent z translated) := measureReal_mono hsub
  change mu.real A <= mu.real translated
  calc
    mu.real A <= mu.real (P.translateEvent z translated) := hmeasure
    _ = mu.real translated := by
      unfold Measure.real
      rw [P.translateEvent_measure_eq mu hTI z
        (E.verticalCrossingEvent_measurableSet _ _ _ _)]



theorem PeriodicPlaneEmbedding.horizontalCrossing_translate_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Nat -> Site 2) (a b c d : Nat -> Real)
    (hlimit : Tendsto (fun n => mu.real
      (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))
      atTop (nhds 1)) :
    Tendsto (fun n => mu.real (E.horizontalCrossingEvent
      (a n + (z n 0 : Real)) (b n + (z n 0 : Real))
      (c n + (z n 1 : Real)) (d n + (z n 1 : Real))))
      atTop (nhds 1) := by
  exact hlimit.squeeze tendsto_const_nhds
    (fun n => E.horizontalCrossing_translate_measureReal_le
      mu hTI (z n) (a n) (b n) (c n) (d n))
    (fun _ => measureReal_le_one)


theorem PeriodicPlaneEmbedding.verticalCrossing_translate_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Nat -> Site 2) (a b c d : Nat -> Real)
    (hlimit : Tendsto (fun n => mu.real
      (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
      atTop (nhds 1)) :
    Tendsto (fun n => mu.real (E.verticalCrossingEvent
      (a n + (z n 0 : Real)) (b n + (z n 0 : Real))
      (c n + (z n 1 : Real)) (d n + (z n 1 : Real))))
      atTop (nhds 1) := by
  exact hlimit.squeeze tendsto_const_nhds
    (fun n => E.verticalCrossing_translate_measureReal_le
      mu hTI (z n) (a n) (b n) (c n) (d n))
    (fun _ => measureReal_le_one)



theorem PeriodicPlaneEmbedding.crossingMax_independent_translate_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (zH zV : Nat -> Site 2)
    (aH bH cH dH aV bV cV dV : Nat -> Real)
    (hlimit : Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (aH n) (bH n) (cH n) (dH n)))
      (mu.real (E.verticalCrossingEvent
        (aV n) (bV n) (cV n) (dV n)))) atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (aH n + (zH n 0 : Real)) (bH n + (zH n 0 : Real))
        (cH n + (zH n 1 : Real)) (dH n + (zH n 1 : Real))))
      (mu.real (E.verticalCrossingEvent
        (aV n + (zV n 0 : Real)) (bV n + (zV n 0 : Real))
        (cV n + (zV n 1 : Real)) (dV n + (zV n 1 : Real)))))
      atTop (nhds 1) := by
  exact hlimit.squeeze tendsto_const_nhds
    (fun n => max_le_max
      (E.horizontalCrossing_translate_measureReal_le
        mu hTI (zH n) (aH n) (bH n) (cH n) (dH n))
      (E.verticalCrossing_translate_measureReal_le
        mu hTI (zV n) (aV n) (bV n) (cV n) (dV n)))
    (fun _ => max_le measureReal_le_one measureReal_le_one)




theorem exists_matched_commonSquareNormalBoundaryBandData_ge
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W))) [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {margin : Nat}
    {p pDual : Real}
    (primal : E.NormalBoundaryBandSeed mu S margin p)
    (dual : Edual.NormalBoundaryBandSeed muDual Sdual margin pDual)
    (lower : Nat) :
    exists M : Nat, lower <= M /\
      Nonempty (E.CommonSquareNormalBoundaryBandData
        mu S margin M p) /\
      Nonempty (Edual.CommonSquareNormalBoundaryBandData
        muDual Sdual margin M pDual) := by
  let M0 := commonPrimalDualBandHalfWidth
    primal.radiusLeft primal.radiusRight
    primal.radiusBottom primal.radiusTop
    dual.radiusLeft dual.radiusRight
    dual.radiusBottom dual.radiusTop
  let M := max M0 lower
  have hM0 : M0 <= M := Nat.le_max_left _ _
  have h := le_commonPrimalDualBandHalfWidth
    primal.radiusLeft primal.radiusRight
    primal.radiusBottom primal.radiusTop
    dual.radiusLeft dual.radiusRight
    dual.radiusBottom dual.radiusTop
  dsimp only at h
  refine ⟨M, Nat.le_max_right _ _, ?_, ?_⟩
  · exact Nonempty.intro <| primal.toCommonSquare E mu hTI M
      (h.1.trans hM0) (h.2.1.trans hM0)
      (h.2.2.1.trans hM0) (h.2.2.2.1.trans hM0)
  · exact Nonempty.intro <| dual.toCommonSquare Edual muDual hTIDual M
      (h.2.2.2.2.1.trans hM0) (h.2.2.2.2.2.1.trans hM0)
      (h.2.2.2.2.2.2.1.trans hM0) (h.2.2.2.2.2.2.2.trans hM0)




theorem PeriodicPlaneEmbedding.exists_commonSquareNormalBoundaryBands_outward
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (score : Nat -> Real) (margin M : Nat -> Nat)
    (data : forall n, E.CommonSquareNormalBoundaryBandData
      mu (P.orbitBox n) (margin n) (M n) (score n))
    (hscore : Tendsto score atTop (nhds 1))
    (_hscore_le : forall n, score n <= 1)
    (pad : Nat -> Int) (hpad : forall n, 0 <= pad n) :
    exists radius : Nat -> Nat, forall
      (width height : Nat -> Nat)
      (hwidth : forall n, 0 < width n)
      (hheight : forall n, 0 < height n),
      (forall n, E.orbitBoxCoordinateBound
        (P.bufferedRadius (radius n)) (0 : Fin 2) <= M n) ->
      (forall n, E.orbitBoxCoordinateBound
        (P.bufferedRadius (radius n)) (1 : Fin 2) <= M n) ->
      Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent
          (-(M n : Real)) (M n + width n : Real)
          (-(M n : Real) - pad n) (M n + height n + pad n : Real)))
        (mu.real (E.horizontalCrossingEvent
          (-(M n : Real) - pad n) (M n + width n + pad n : Real)
          (-(M n : Real)) (M n + height n : Real))))
        atTop (nhds 1) := by
  let zLeft : Nat -> Site 2 := fun n => (data n).zLeft
  let zRight : Nat -> Site 2 := fun n => (data n).zRight
  let zBottom : Nat -> Site 2 := fun n => (data n).zBottom
  let zTop : Nat -> Site 2 := fun n => (data n).zTop
  have hleftSubset (n : Nat) :
      ((P.orbitBox n).image (P.shift (zLeft n)) : Set V) <=
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real) := by
    simpa [zLeft] using ((data n).left (0 : Fin (margin n + 1))).1
  have hrightSubset (n : Nat) :
      ((P.orbitBox n).image (P.shift (zRight n)) : Set V) <=
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real) := by
    simpa [zRight] using ((data n).right (0 : Fin (margin n + 1))).1
  have hbottomSubset (n : Nat) :
      ((P.orbitBox n).image (P.shift (zBottom n)) : Set V) <=
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real) := by
    simpa [zBottom] using ((data n).bottom (0 : Fin (margin n + 1))).1
  have htopSubset (n : Nat) :
      ((P.orbitBox n).image (P.shift (zTop n)) : Set V) <=
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real) := by
    simpa [zTop] using ((data n).top (0 : Fin (margin n + 1))).1
  have hleftLower (n : Nat) : score n < mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zLeft n)) : Set V)
        (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))) := by
    simpa [zLeft] using ((data n).left (0 : Fin (margin n + 1))).2
  have hrightLower (n : Nat) : score n < mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zRight n)) : Set V)
        (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))) := by
    simpa [zRight] using ((data n).right (0 : Fin (margin n + 1))).2
  have hbottomLower (n : Nat) : score n < mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zBottom n)) : Set V)
        (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))) := by
    simpa [zBottom] using ((data n).bottom (0 : Fin (margin n + 1))).2
  have htopLower (n : Nat) : score n < mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zTop n)) : Set V)
        (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))) := by
    simpa [zTop] using ((data n).top (0 : Fin (margin n + 1))).2
  have hleftLimit := hscore.squeeze tendsto_const_nhds
    (fun n => le_of_lt (hleftLower n)) (fun _ => measureReal_le_one)
  have hrightLimit := hscore.squeeze tendsto_const_nhds
    (fun n => le_of_lt (hrightLower n)) (fun _ => measureReal_le_one)
  have hbottomLimit := hscore.squeeze tendsto_const_nhds
    (fun n => le_of_lt (hbottomLower n)) (fun _ => measureReal_le_one)
  have htopLimit := hscore.squeeze tendsto_const_nhds
    (fun n => le_of_lt (htopLower n)) (fun _ => measureReal_le_one)
  exact E.exists_fourShiftTemplate_outward_crossing_max_tendsto_one_of_coordinateBounds
    mu hFKG hTI hunique M zLeft zRight zBottom zTop
    hleftSubset hrightSubset hbottomSubset htopSubset
    hleftLimit hrightLimit hbottomLimit htopLimit pad hpad




theorem PeriodicPlaneEmbedding.exists_pointwise_commonSquareNormalBoundaryBands_outward
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (score : Nat -> Nat -> Real)
    (margin M : Nat -> Nat -> Nat)
    (data : forall k n, E.CommonSquareNormalBoundaryBandData
      mu (P.orbitBox n) (margin k n) (M k n) (score k n))
    (hscore : forall k, Tendsto (score k) atTop (nhds 1))
    (hscore_le : forall k n, score k n <= 1)
    (pad : Nat -> Nat -> Int) (hpad : forall k n, 0 <= pad k n)
    (width height : Nat -> Nat -> Nat)
    (hwidth : forall k n, 0 < width k n)
    (hheight : forall k n, 0 < height k n) :
    exists radius : Nat -> Nat -> Nat,
      (forall k n, E.orbitBoxCoordinateBound
        (P.bufferedRadius (radius k n)) (0 : Fin 2) <= M k n) ->
      (forall k n, E.orbitBoxCoordinateBound
        (P.bufferedRadius (radius k n)) (1 : Fin 2) <= M k n) ->
      forall k, Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent
          (-(M k n : Real)) (M k n + width k n : Real)
          (-(M k n : Real) - pad k n)
          (M k n + height k n + pad k n : Real)))
        (mu.real (E.horizontalCrossingEvent
          (-(M k n : Real) - pad k n)
          (M k n + width k n + pad k n : Real)
          (-(M k n : Real)) (M k n + height k n : Real))))
        atTop (nhds 1) := by
  have hexists (k : Nat) :=
    E.exists_commonSquareNormalBoundaryBands_outward mu hFKG hTI hunique
      (score k) (margin k) (M k) (data k) (hscore k) (hscore_le k)
      (pad k) (hpad k)
  let radius : Nat -> Nat -> Nat := fun k => Classical.choose (hexists k)
  have hcross (k : Nat) := Classical.choose_spec (hexists k)
  refine ⟨radius, ?_⟩
  intro hx hy k
  exact hcross k (width k) (height k) (hwidth k) (hheight k)
    (hx k) (hy k)



structure AlignedCrossNestedThreePairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (S : Finset V) (Sdual : Finset W) (p pDual : Real)
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding : Nat) where
  previousX : Nat
  previousY : Nat
  currentX : Nat
  currentY : Nat
  nextX : Nat
  nextY : Nat
  previous : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual family familyDual schedule k previousX previousY
  current : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual family familyDual schedule k currentX currentY
  next : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual family familyDual schedule k nextX nextY
  currentX_eq : (currentX : Int) = previous.raw.wideRightInt -
    previous.raw.wideLeftInt + 2 * padding
  nextX_eq : (nextX : Int) = current.raw.wideRightInt -
    current.raw.wideLeftInt + 2 * padding
  previousY_eq : previousY = currentY + 2 * padding
  currentY_eq : currentY = nextY + 2 * padding



theorem nonempty_alignedCrossNestedThreePairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding : Nat) :
    Nonempty (AlignedCrossNestedThreePairedMixedBoundaryScores
      E Edual mu muDual S Sdual p pDual family familyDual schedule k
      padding) := by
  obtain ⟨thresholdX, thresholdY, hthreshold⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E Edual mu muDual hTI hTIDual family familyDual schedule k
  let nextY := thresholdY
  let currentY := nextY + 2 * padding
  let previousY := currentY + 2 * padding
  let previousX := thresholdX
  let previous := Classical.choice
    (hthreshold (extentX := previousX) (extentY := previousY)
      (by simp [previousX]) (by dsimp [previousY, currentY, nextY]; omega))
  let previousSpan :=
    previous.raw.wideRightInt - previous.raw.wideLeftInt
  have hpreviousSpan : 0 <= previousSpan :=
    (show (0 : Int) <= previousX by omega).trans
      previous.raw.extentX_le_wideSpan
  let currentX := previousSpan.toNat + 2 * padding
  have hcurrentX : thresholdX <= currentX := by
    have hspan : previousX <= previousSpan.toNat := by
      rw [Int.le_toNat hpreviousSpan]
      exact previous.raw.extentX_le_wideSpan
    exact (show thresholdX = previousX by rfl) |>.trans_le
      (hspan.trans (Nat.le_add_right _ _))
  let current := Classical.choice
    (hthreshold (extentX := currentX) (extentY := currentY)
      hcurrentX (by simp [currentY, nextY]))
  let currentSpan := current.raw.wideRightInt - current.raw.wideLeftInt
  have hcurrentSpan : 0 <= currentSpan :=
    (show (0 : Int) <= currentX by omega).trans
      current.raw.extentX_le_wideSpan
  let nextX := currentSpan.toNat + 2 * padding
  have hnextX : thresholdX <= nextX := by
    have hspan : currentX <= currentSpan.toNat := by
      rw [Int.le_toNat hcurrentSpan]
      exact current.raw.extentX_le_wideSpan
    exact hcurrentX.trans (hspan.trans (Nat.le_add_right _ _))
  let next := Classical.choice
    (hthreshold (extentX := nextX) (extentY := nextY)
      hnextX (by simp [nextY]))
  refine ⟨{
    previousX := previousX
    previousY := previousY
    currentX := currentX
    currentY := currentY
    nextX := nextX
    nextY := nextY
    previous := previous
    current := current
    next := next
    currentX_eq := ?_
    nextX_eq := ?_
    previousY_eq := rfl
    currentY_eq := rfl }⟩
  · change ((previousSpan.toNat + 2 * padding : Nat) : Int) =
      previousSpan + 2 * (padding : Int)
    push_cast
    rw [Int.toNat_of_nonneg hpreviousSpan]
  · change ((currentSpan.toNat + 2 * padding : Nat) : Int) =
      currentSpan + 2 * (padding : Int)
    push_cast
    rw [Int.toNat_of_nonneg hcurrentSpan]




theorem exists_alignedCrossNestedThreePairedMixedBoundaryScores_ge
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding lowerX lowerY : Nat) :
    exists data : AlignedCrossNestedThreePairedMixedBoundaryScores
        E Edual mu muDual S Sdual p pDual family familyDual schedule k padding,
      lowerX <= data.currentX /\ lowerY <= data.currentY /\
      (lowerX : Int) <= data.current.raw.wideRightInt -
        data.current.raw.wideLeftInt := by
  obtain ⟨thresholdX, thresholdY, hthreshold⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E Edual mu muDual hTI hTIDual family familyDual schedule k
  let nextY := max thresholdY lowerY
  let currentY := nextY + 2 * padding
  let previousY := currentY + 2 * padding
  let previousX := max thresholdX lowerX
  let previous := Classical.choice
    (hthreshold (extentX := previousX) (extentY := previousY)
      (Nat.le_max_left _ _)
      (by dsimp [previousY, currentY, nextY]; omega))
  let previousSpan :=
    previous.raw.wideRightInt - previous.raw.wideLeftInt
  have hpreviousSpan : 0 <= previousSpan :=
    (show (0 : Int) <= previousX by omega).trans
      previous.raw.extentX_le_wideSpan
  let currentX := previousSpan.toNat + 2 * padding
  have hpreviousXSpan : previousX <= previousSpan.toNat := by
    rw [Int.le_toNat hpreviousSpan]
    exact previous.raw.extentX_le_wideSpan
  have hcurrentX : thresholdX <= currentX :=
    (Nat.le_max_left _ _).trans
      (hpreviousXSpan.trans (Nat.le_add_right _ _))
  let current := Classical.choice
    (hthreshold (extentX := currentX) (extentY := currentY)
      hcurrentX
      ((Nat.le_max_left _ _).trans (Nat.le_add_right _ _)))
  let currentSpan := current.raw.wideRightInt - current.raw.wideLeftInt
  have hcurrentSpan : 0 <= currentSpan :=
    (show (0 : Int) <= currentX by omega).trans
      current.raw.extentX_le_wideSpan
  let nextX := currentSpan.toNat + 2 * padding
  have hnextX : thresholdX <= nextX := by
    have hspan : currentX <= currentSpan.toNat := by
      rw [Int.le_toNat hcurrentSpan]
      exact current.raw.extentX_le_wideSpan
    exact hcurrentX.trans (hspan.trans (Nat.le_add_right _ _))
  let next := Classical.choice
    (hthreshold (extentX := nextX) (extentY := nextY)
      hnextX (Nat.le_max_left _ _))
  let data : AlignedCrossNestedThreePairedMixedBoundaryScores
      E Edual mu muDual S Sdual p pDual family familyDual schedule k
      padding := {
    previousX := previousX
    previousY := previousY
    currentX := currentX
    currentY := currentY
    nextX := nextX
    nextY := nextY
    previous := previous
    current := current
    next := next
    currentX_eq := by
      change ((previousSpan.toNat + 2 * padding : Nat) : Int) =
        previousSpan + 2 * (padding : Int)
      push_cast
      rw [Int.toNat_of_nonneg hpreviousSpan]
    nextX_eq := by
      change ((currentSpan.toNat + 2 * padding : Nat) : Int) =
        currentSpan + 2 * (padding : Int)
      push_cast
      rw [Int.toNat_of_nonneg hcurrentSpan]
    previousY_eq := rfl
    currentY_eq := rfl }
  refine ⟨data, ?_, ?_, ?_⟩
  · exact (Nat.le_max_right _ _).trans
      (hpreviousXSpan.trans (Nat.le_add_right _ _))
  · exact (Nat.le_max_right _ _).trans (Nat.le_add_right _ _)
  · have hlowerNat : lowerX <= currentX :=
      (Nat.le_max_right _ _).trans
        (hpreviousXSpan.trans (Nat.le_add_right _ _))
    have hlowerInt : (lowerX : Int) <= (currentX : Int) := by
      exact_mod_cast hlowerNat
    exact hlowerInt.trans current.raw.extentX_le_wideSpan




theorem nonempty_alignedRotatedCrossNestedThreePairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding : Nat) :
    Nonempty (AlignedCrossNestedThreePairedMixedBoundaryScores
      E.axisSwap Edual.axisSwap mu muDual S Sdual p pDual
      family.axisSwap familyDual.axisSwap schedule.axisSwap k padding) := by
  exact nonempty_alignedCrossNestedThreePairedMixedBoundaryScores
    E.axisSwap Edual.axisSwap mu muDual
    (P.axisSwap_isTranslationInvariant mu hTI)
    (Pdual.axisSwap_isTranslationInvariant muDual hTIDual)
    family.axisSwap familyDual.axisSwap schedule.axisSwap k padding



structure AlignedCrossNestedPairedSequence
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (p pDual : Nat -> Real)
    (family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n))
    (familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n))
    (padding : Nat) where
  radius : Nat -> Nat
  schedule : forall n, PairedAlignedMarginSchedule E Edual
    (family n) (familyDual n) (fun _ => 0) (fun _ => 0)
  index : Nat -> Nat
  slack : forall n, PairedAlignedConnectorSlack E Edual
    (family n) (familyDual n) (schedule n) (max (radius n) n) (index n)
  triple : forall n, AlignedCrossNestedThreePairedMixedBoundaryScores
    E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n) (p n) (pDual n)
    (family n) (familyDual n) (schedule n) (index n) padding



theorem exists_alignedCrossNestedPairedSequence_with_primalAdjacent
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu)
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (p pDual : Nat -> Real)
    (family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n))
    (familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n))
    (hp : Tendsto p atTop (nhds 1)) (hp_le : forall n, p n <= 1)
    (padding : Nat) :
    exists data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding,
      Tendsto (fun n => max
        (mu.real (E.horizontalCrossingEvent 0
          (data.triple n).currentX 0 (data.triple n).currentY))
        (mu.real (E.verticalCrossingEvent
          (data.triple n).current.raw.data.wideLeft
          (data.triple n).current.raw.data.wideRight 0
          (data.triple n).currentY))) atTop (nhds 1) := by
  let template : Nat -> Finset V := fun n => P.orbitBox n
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- hunique]
    exact measure_mono fun _ h => h.1
  have htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V)))
      atTop (nhds 1) := by
    simpa only [template, PeriodicGraph.setHitsInfinite,
      PeriodicGraph.orbitBoxHitsInfinite] using
      P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_mixedBoundaryScores_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit
  let schedule : forall n, PairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0) := fun n =>
    Classical.choice (exists_pairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0))
  have hslack (n : Nat) := exists_pairedAlignedConnectorSlack E Edual
    (family n) (familyDual n) (schedule n) (max (radius n) n)
  let index : Nat -> Nat := fun n => Classical.choose (hslack n)
  let slack : forall n, PairedAlignedConnectorSlack E Edual
      (family n) (familyDual n) (schedule n) (max (radius n) n)
      (index n) := fun n => Classical.choose_spec (hslack n)
  let triple : forall n, AlignedCrossNestedThreePairedMixedBoundaryScores
      E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n) (p n) (pDual n)
      (family n) (familyDual n) (schedule n) (index n) padding := fun n =>
    Classical.choice
      (nonempty_alignedCrossNestedThreePairedMixedBoundaryScores
        E Edual mu muDual hTI hTIDual (family n) (familyDual n)
        (schedule n) (index n) padding)
  let data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding := {
    radius := radius
    schedule := schedule
    index := index
    slack := slack
    triple := triple }
  refine ⟨data, ?_⟩
  apply hcross
      (fun n => (triple n).current.raw.data.width)
      (fun n => (triple n).current.raw.data.height)
      (fun n => (triple n).current.raw.data.width_pos)
      (fun n => (triple n).current.raw.data.height_pos)
      (fun n => (triple n).current.raw.data.base)
      (fun _ => 0) (fun n => (triple n).currentX)
      (fun _ => 0) (fun n => (triple n).currentY)
      (fun n => (triple n).current.raw.data.wideLeft)
      (fun n => (triple n).current.raw.data.wideRight)
      (fun _ => 0) (fun n => (triple n).currentY) p hp hp_le
  · intro n
    exact (triple n).current.raw.data.wideLeft_le
  · intro n
    simpa [(triple n).current.raw.narrowRight_eq] using
      (triple n).current.raw.data.narrowRight_le
  · intro n
    exact le_rfl
  · intro n
    exact le_rfl
  · intro n gridVertex vertex hvertex
    apply (triple n).current.primalConnector_subset_narrow
      (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := by
      simpa only [Finset.mem_coe, Finset.mem_image] using hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    exact (Nat.le_max_right (radius n) n).trans
      (P.id_le_bufferedRadius (max (radius n) n))
  · intro n gridVertex
    intro vertex hvertex
    apply (triple n).current.primalConnector_subset_narrow
      (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply P.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n gridVertex
    intro vertex hvertex
    rw [<- (triple n).current.raw.shortTop_eq]
    apply (triple n).current.primalConnector_subset_wide
      (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply P.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n i
    simpa [template, (triple n).current.raw.shortTop_eq] using
      le_of_lt ((triple n).current.raw.data.primal_bottom i)
  · intro n i
    simpa [template, (triple n).current.raw.shortTop_eq] using
      le_of_lt ((triple n).current.raw.data.primal_top i)
  · intro n j
    simpa [(triple n).current.raw.narrowRight_eq,
      (triple n).current.raw.tallTop_eq] using
      le_of_lt ((triple n).current.raw.data.primal_left j)
  · intro n j
    simpa [(triple n).current.raw.narrowRight_eq,
      (triple n).current.raw.tallTop_eq] using
      le_of_lt ((triple n).current.raw.data.primal_right j)



theorem exists_alignedCrossNestedPairedSequence_with_primalAdjacent_ge
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu)
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (p pDual : Nat -> Real)
    (family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n))
    (familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n))
    (hp : Tendsto p atTop (nhds 1)) (hp_le : forall n, p n <= 1)
    (padding : Nat) (lowerX lowerY : Nat -> Nat) :
    exists data : AlignedCrossNestedPairedSequence E Edual mu muDual
        p pDual family familyDual padding,
      (forall n, lowerX n <= (data.triple n).currentX) /\
      (forall n, lowerY n <= (data.triple n).currentY) /\
      (forall n, (lowerX n : Int) <=
        (data.triple n).current.raw.wideRightInt -
          (data.triple n).current.raw.wideLeftInt) /\
      Tendsto (fun n => max
        (mu.real (E.horizontalCrossingEvent 0
          (data.triple n).currentX 0 (data.triple n).currentY))
        (mu.real (E.verticalCrossingEvent
          (data.triple n).current.raw.data.wideLeft
          (data.triple n).current.raw.data.wideRight 0
          (data.triple n).currentY))) atTop (nhds 1) := by
  let template : Nat -> Finset V := fun n => P.orbitBox n
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- hunique]
    exact measure_mono fun _ h => h.1
  have htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V)))
      atTop (nhds 1) := by
    simpa only [template, PeriodicGraph.setHitsInfinite,
      PeriodicGraph.orbitBoxHitsInfinite] using
      P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_mixedBoundaryScores_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit
  let schedule : forall n, PairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0) := fun n =>
    Classical.choice (exists_pairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0))
  have hslack (n : Nat) := exists_pairedAlignedConnectorSlack E Edual
    (family n) (familyDual n) (schedule n) (max (radius n) n)
  let index : Nat -> Nat := fun n => Classical.choose (hslack n)
  let slack : forall n, PairedAlignedConnectorSlack E Edual
      (family n) (familyDual n) (schedule n) (max (radius n) n)
      (index n) := fun n => Classical.choose_spec (hslack n)
  have htriple (n : Nat) :=
    exists_alignedCrossNestedThreePairedMixedBoundaryScores_ge
      E Edual mu muDual hTI hTIDual (family n) (familyDual n)
      (schedule n) (index n) padding (lowerX n) (lowerY n)
  let triple : forall n, AlignedCrossNestedThreePairedMixedBoundaryScores
      E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n) (p n) (pDual n)
      (family n) (familyDual n) (schedule n) (index n) padding := fun n =>
    Classical.choose (htriple n)
  have htripleSpec (n : Nat) := Classical.choose_spec (htriple n)
  let data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding := {
    radius := radius
    schedule := schedule
    index := index
    slack := slack
    triple := triple }
  refine ⟨data, fun n => (htripleSpec n).1,
    fun n => (htripleSpec n).2.1,
    fun n => (htripleSpec n).2.2, ?_⟩
  apply hcross
      (fun n => (triple n).current.raw.data.width)
      (fun n => (triple n).current.raw.data.height)
      (fun n => (triple n).current.raw.data.width_pos)
      (fun n => (triple n).current.raw.data.height_pos)
      (fun n => (triple n).current.raw.data.base)
      (fun _ => 0) (fun n => (triple n).currentX)
      (fun _ => 0) (fun n => (triple n).currentY)
      (fun n => (triple n).current.raw.data.wideLeft)
      (fun n => (triple n).current.raw.data.wideRight)
      (fun _ => 0) (fun n => (triple n).currentY) p hp hp_le
  · intro n
    exact (triple n).current.raw.data.wideLeft_le
  · intro n
    simpa [(triple n).current.raw.narrowRight_eq] using
      (triple n).current.raw.data.narrowRight_le
  · intro n
    exact le_rfl
  · intro n
    exact le_rfl
  · intro n gridVertex vertex hvertex
    apply (triple n).current.primalConnector_subset_narrow
      (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := by
      simpa only [Finset.mem_coe, Finset.mem_image] using hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    exact (Nat.le_max_right (radius n) n).trans
      (P.id_le_bufferedRadius (max (radius n) n))
  · intro n gridVertex vertex hvertex
    apply (triple n).current.primalConnector_subset_narrow
      (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply P.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n gridVertex vertex hvertex
    rw [<- (triple n).current.raw.shortTop_eq]
    apply (triple n).current.primalConnector_subset_wide
      (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply P.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n i
    simpa [template, (triple n).current.raw.shortTop_eq] using
      le_of_lt ((triple n).current.raw.data.primal_bottom i)
  · intro n i
    simpa [template, (triple n).current.raw.shortTop_eq] using
      le_of_lt ((triple n).current.raw.data.primal_top i)
  · intro n j
    simpa [(triple n).current.raw.narrowRight_eq,
      (triple n).current.raw.tallTop_eq] using
      le_of_lt ((triple n).current.raw.data.primal_left j)
  · intro n j
    simpa [(triple n).current.raw.narrowRight_eq,
      (triple n).current.raw.tallTop_eq] using
      le_of_lt ((triple n).current.raw.data.primal_right j)

namespace AlignedCrossNestedPairedSequence

noncomputable def transitionA0
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (_data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding) (_n : Nat) : Real := 0

noncomputable def transitionB0
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding) (n : Nat) : Real :=
  (data.triple n).currentX

noncomputable def transitionC0
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (_data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding) (_n : Nat) : Real :=
  -(padding : Real)

noncomputable def transitionD0
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding) (n : Nat) : Real :=
  (data.triple n).currentY + padding

noncomputable def transitionA1
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding) (n : Nat) : Real :=
  (data.triple n).current.raw.data.wideLeft - padding

noncomputable def transitionB1
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding) (n : Nat) : Real :=
  (data.triple n).current.raw.data.wideRight + padding

noncomputable def transitionC1
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (_data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding) (_n : Nat) : Real := 0

noncomputable def transitionD1
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding) (n : Nat) : Real :=
  (data.triple n).currentY



theorem primalAdjacent_transitionCoordinates
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (hlimit : Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent 0
        (data.triple n).currentX 0 (data.triple n).currentY))
      (mu.real (E.verticalCrossingEvent
        (data.triple n).current.raw.data.wideLeft
        (data.triple n).current.raw.data.wideRight 0
        (data.triple n).currentY))) atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (data.transitionA0 n) (data.transitionB0 n)
        (data.transitionC0 n + padding)
        (data.transitionD0 n - padding)))
      (mu.real (E.verticalCrossingEvent
        (data.transitionA1 n + padding)
        (data.transitionB1 n - padding)
        (data.transitionC1 n) (data.transitionD1 n))))
      atTop (nhds 1) := by
  simpa [transitionA0, transitionB0, transitionC0, transitionD0,
    transitionA1, transitionB1, transitionC1, transitionD1] using hlimit



theorem primalAdjacent_translatedTransitionCoordinates
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (hTI : P.IsTranslationInvariant mu) (z0 z1 : Nat -> Site 2)
    (hlimit : Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent 0
        (data.triple n).currentX 0 (data.triple n).currentY))
      (mu.real (E.verticalCrossingEvent
        (data.triple n).current.raw.data.wideLeft
        (data.triple n).current.raw.data.wideRight 0
        (data.triple n).currentY))) atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (data.transitionA0 n + z0 n 0)
        (data.transitionB0 n + z0 n 0)
        (data.transitionC0 n + padding + z0 n 1)
        (data.transitionD0 n - padding + z0 n 1)))
      (mu.real (E.verticalCrossingEvent
        (data.transitionA1 n + padding + z1 n 0)
        (data.transitionB1 n - padding + z1 n 0)
        (data.transitionC1 n + z1 n 1)
        (data.transitionD1 n + z1 n 1)))) atTop (nhds 1) := by
  have hbase := data.primalAdjacent_transitionCoordinates hlimit
  simpa only [Int.cast_ofNat, add_assoc] using
    E.crossingMax_independent_translate_tendsto_one mu hTI z0 z1
      data.transitionA0 data.transitionB0
      (fun n => data.transitionC0 n + padding)
      (fun n => data.transitionD0 n - padding)
      (fun n => data.transitionA1 n + padding)
      (fun n => data.transitionB1 n - padding)
      data.transitionC1 data.transitionD1 hbase




theorem endpoint_transitionCoordinates_of_mergeLimits
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hp : Tendsto p atTop (nhds 1)) (hp_le : forall n, p n <= 1)
    (hmergeVertical : Tendsto (fun n => mu.real
      (E.rectanglePairMergeErrorUnion
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight 0
        (data.triple n).previousY
        (data.triple n).previous.raw.data.primalBottomSource
        (data.triple n).previous.raw.data.primalTopSource))
      atTop (nhds 0))
    (hmergeHorizontal : Tendsto (fun n => mu.real
      (E.rectanglePairMergeErrorUnion 0
        (data.triple n).nextX 0 (data.triple n).nextY
        (data.triple n).next.raw.data.primalLeftSource
        (data.triple n).next.raw.data.primalRightSource))
      atTop (nhds 0)) :
    Tendsto (fun n => mu.real (E.verticalCrossingEvent
      (data.transitionA0 n + padding)
      (data.transitionB0 n - padding)
      (data.transitionC0 n) (data.transitionD0 n)))
      atTop (nhds 1) /\
    Tendsto (fun n => mu.real (E.horizontalCrossingEvent
      (data.transitionA1 n) (data.transitionB1 n)
      (data.transitionC1 n + padding)
      (data.transitionD1 n - padding))) atTop (nhds 1) := by
  have hbottom : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight 0
        (data.triple n).previousY
        ((data.triple n).previous.raw.data.primalBottomSource : Set V)
        (E.rectBottomBoundaryVertices
          (data.triple n).previous.raw.data.wideLeft
          (data.triple n).previous.raw.data.wideRight 0
          (data.triple n).previousY))) atTop (nhds 1) := by
    exact hp.squeeze tendsto_const_nhds
      (fun n => by
        simpa [(data.triple n).previous.raw.shortTop_eq] using
          le_of_lt (data.triple n).previous.raw.data.primalBottomScore)
      (fun _ => measureReal_le_one)
  have htop : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight 0
        (data.triple n).previousY
        ((data.triple n).previous.raw.data.primalTopSource : Set V)
        (E.rectTopBoundaryVertices
          (data.triple n).previous.raw.data.wideLeft
          (data.triple n).previous.raw.data.wideRight 0
          (data.triple n).previousY))) atTop (nhds 1) := by
    exact hp.squeeze tendsto_const_nhds
      (fun n => by
        simpa [(data.triple n).previous.raw.shortTop_eq] using
          le_of_lt (data.triple n).previous.raw.data.primalTopScore)
      (fun _ => measureReal_le_one)
  have hleft : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent 0 (data.triple n).nextX 0
        (data.triple n).nextY
        ((data.triple n).next.raw.data.primalLeftSource : Set V)
        (E.rectLeftBoundaryVertices 0 (data.triple n).nextX 0
          (data.triple n).nextY))) atTop (nhds 1) := by
    exact hp.squeeze tendsto_const_nhds
      (fun n => by
        simpa [(data.triple n).next.raw.narrowRight_eq,
          (data.triple n).next.raw.tallTop_eq] using
          le_of_lt (data.triple n).next.raw.data.primalLeftScore)
      (fun _ => measureReal_le_one)
  have hright : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent 0 (data.triple n).nextX 0
        (data.triple n).nextY
        ((data.triple n).next.raw.data.primalRightSource : Set V)
        (E.rectRightBoundaryVertices 0 (data.triple n).nextX 0
          (data.triple n).nextY))) atTop (nhds 1) := by
    exact hp.squeeze tendsto_const_nhds
      (fun n => by
        simpa [(data.triple n).next.raw.narrowRight_eq,
          (data.triple n).next.raw.tallTop_eq] using
          le_of_lt (data.triple n).next.raw.data.primalRightScore)
      (fun _ => measureReal_le_one)
  have hvertical := E.verticalCrossing_tendsto_one_of_boundaryScores
    mu hFKG
    (fun n => (data.triple n).previous.raw.data.wideLeft)
    (fun n => (data.triple n).previous.raw.data.wideRight)
    (fun _ => 0) (fun n => (data.triple n).previousY)
    (fun n => (data.triple n).previous.raw.data.primalBottomSource)
    (fun n => (data.triple n).previous.raw.data.primalTopSource)
    hbottom htop hmergeVertical
  have hhorizontal := E.horizontalCrossing_tendsto_one_of_boundaryScores
    mu hFKG (fun _ => 0) (fun n => (data.triple n).nextX)
    (fun _ => 0) (fun n => (data.triple n).nextY)
    (fun n => (data.triple n).next.raw.data.primalLeftSource)
    (fun n => (data.triple n).next.raw.data.primalRightSource)
    hleft hright hmergeHorizontal
  let zVertical : Nat -> Site 2 := fun n => fun i =>
    if i = 0 then padding -
      (data.triple n).previous.raw.wideLeftInt else -(padding : Int)
  let zHorizontal : Nat -> Site 2 := fun n => fun i =>
    if i = 0 then
      (data.triple n).current.raw.wideLeftInt - padding
    else padding
  constructor
  · have htranslated := E.verticalCrossing_translate_tendsto_one
      mu hTI zVertical
      (fun n => (data.triple n).previous.raw.data.wideLeft)
      (fun n => (data.triple n).previous.raw.data.wideRight)
      (fun _ => 0) (fun n => (data.triple n).previousY) hvertical
    apply htranslated.congr'
    filter_upwards with n
    have hcurrentR : ((data.triple n).currentX : Real) =
        ((data.triple n).previous.raw.wideRightInt : Real) -
          (data.triple n).previous.raw.wideLeftInt + 2 * padding := by
      exact_mod_cast (data.triple n).currentX_eq
    have hpreviousYR : ((data.triple n).previousY : Real) =
        (data.triple n).currentY + 2 * padding := by
      exact_mod_cast (data.triple n).previousY_eq
    apply congrArg (fun event : Set (ConfigSpace (Sym2 V)) => mu.real event)
    congr 1
    all_goals
      simp only [transitionA0, transitionB0, transitionC0, transitionD0,
        zVertical, Pi.zero_apply, if_pos, if_neg]
    · rw [(data.triple n).previous.raw.wideLeft_eq]
      push_cast
      ring
    · rw [(data.triple n).previous.raw.wideRight_eq]
      push_cast
      linarith [hcurrentR]
    · push_cast
      ring
    · push_cast
      linarith [hpreviousYR]
  · have htranslated := E.horizontalCrossing_translate_tendsto_one
      mu hTI zHorizontal (fun _ => 0)
      (fun n => (data.triple n).nextX) (fun _ => 0)
      (fun n => (data.triple n).nextY) hhorizontal
    apply htranslated.congr'
    filter_upwards with n
    have hnextR : ((data.triple n).nextX : Real) =
        ((data.triple n).current.raw.wideRightInt : Real) -
          (data.triple n).current.raw.wideLeftInt + 2 * padding := by
      exact_mod_cast (data.triple n).nextX_eq
    have hcurrentYR : ((data.triple n).currentY : Real) =
        (data.triple n).nextY + 2 * padding := by
      exact_mod_cast (data.triple n).currentY_eq
    apply congrArg (fun event : Set (ConfigSpace (Sym2 V)) => mu.real event)
    congr 1
    all_goals
      simp only [transitionA1, transitionB1, transitionC1, transitionD1,
        zHorizontal, Pi.zero_apply, if_pos, if_neg]
    · rw [(data.triple n).current.raw.wideLeft_eq]
      push_cast
      ring
    · rw [(data.triple n).current.raw.wideRight_eq]
      push_cast
      linarith [hnextR]
    · push_cast
      linarith [hcurrentYR]






theorem dual_endpoint_transitionCoordinates_of_mergeLimits
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (hFKG : IsFKG muDual) (hTI : Pdual.IsTranslationInvariant muDual)
    (hp : Tendsto pDual atTop (nhds 1))
    (hp_le : forall n, pDual n <= 1)
    (hmergeVertical : Tendsto (fun n => muDual.real
      (Edual.rectanglePairMergeErrorUnion
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight 0
        (data.triple n).previousY
        (data.triple n).previous.raw.data.dualBottomSource
        (data.triple n).previous.raw.data.dualTopSource))
      atTop (nhds 0))
    (hmergeHorizontal : Tendsto (fun n => muDual.real
      (Edual.rectanglePairMergeErrorUnion 0
        (data.triple n).nextX 0 (data.triple n).nextY
        (data.triple n).next.raw.data.dualLeftSource
        (data.triple n).next.raw.data.dualRightSource))
      atTop (nhds 0)) :
    Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent
      (data.transitionA0 n + padding)
      (data.transitionB0 n - padding)
      (data.transitionC0 n) (data.transitionD0 n)))
      atTop (nhds 1) /\
    Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent
      (data.transitionA1 n) (data.transitionB1 n)
      (data.transitionC1 n + padding)
      (data.transitionD1 n - padding))) atTop (nhds 1) := by
  have hbottom : Tendsto (fun n => muDual.real
      (Edual.rectSideConnectionEvent
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight 0
        (data.triple n).previousY
        ((data.triple n).previous.raw.data.dualBottomSource : Set W)
        (Edual.rectBottomBoundaryVertices
          (data.triple n).previous.raw.data.wideLeft
          (data.triple n).previous.raw.data.wideRight 0
          (data.triple n).previousY))) atTop (nhds 1) := by
    exact hp.squeeze tendsto_const_nhds
      (fun n => by
        simpa [(data.triple n).previous.raw.shortTop_eq] using
          le_of_lt (data.triple n).previous.raw.data.dualBottomScore)
      (fun _ => measureReal_le_one)
  have htop : Tendsto (fun n => muDual.real
      (Edual.rectSideConnectionEvent
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight 0
        (data.triple n).previousY
        ((data.triple n).previous.raw.data.dualTopSource : Set W)
        (Edual.rectTopBoundaryVertices
          (data.triple n).previous.raw.data.wideLeft
          (data.triple n).previous.raw.data.wideRight 0
          (data.triple n).previousY))) atTop (nhds 1) := by
    exact hp.squeeze tendsto_const_nhds
      (fun n => by
        simpa [(data.triple n).previous.raw.shortTop_eq] using
          le_of_lt (data.triple n).previous.raw.data.dualTopScore)
      (fun _ => measureReal_le_one)
  have hleft : Tendsto (fun n => muDual.real
      (Edual.rectSideConnectionEvent 0 (data.triple n).nextX 0
        (data.triple n).nextY
        ((data.triple n).next.raw.data.dualLeftSource : Set W)
        (Edual.rectLeftBoundaryVertices 0 (data.triple n).nextX 0
          (data.triple n).nextY))) atTop (nhds 1) := by
    exact hp.squeeze tendsto_const_nhds
      (fun n => by
        simpa [(data.triple n).next.raw.narrowRight_eq,
          (data.triple n).next.raw.tallTop_eq] using
          le_of_lt (data.triple n).next.raw.data.dualLeftScore)
      (fun _ => measureReal_le_one)
  have hright : Tendsto (fun n => muDual.real
      (Edual.rectSideConnectionEvent 0 (data.triple n).nextX 0
        (data.triple n).nextY
        ((data.triple n).next.raw.data.dualRightSource : Set W)
        (Edual.rectRightBoundaryVertices 0 (data.triple n).nextX 0
          (data.triple n).nextY))) atTop (nhds 1) := by
    exact hp.squeeze tendsto_const_nhds
      (fun n => by
        simpa [(data.triple n).next.raw.narrowRight_eq,
          (data.triple n).next.raw.tallTop_eq] using
          le_of_lt (data.triple n).next.raw.data.dualRightScore)
      (fun _ => measureReal_le_one)
  have hvertical := Edual.verticalCrossing_tendsto_one_of_boundaryScores
    muDual hFKG
    (fun n => (data.triple n).previous.raw.data.wideLeft)
    (fun n => (data.triple n).previous.raw.data.wideRight)
    (fun _ => 0) (fun n => (data.triple n).previousY)
    (fun n => (data.triple n).previous.raw.data.dualBottomSource)
    (fun n => (data.triple n).previous.raw.data.dualTopSource)
    hbottom htop hmergeVertical
  have hhorizontal := Edual.horizontalCrossing_tendsto_one_of_boundaryScores
    muDual hFKG (fun _ => 0) (fun n => (data.triple n).nextX)
    (fun _ => 0) (fun n => (data.triple n).nextY)
    (fun n => (data.triple n).next.raw.data.dualLeftSource)
    (fun n => (data.triple n).next.raw.data.dualRightSource)
    hleft hright hmergeHorizontal
  let zVertical : Nat -> Site 2 := fun n => fun i =>
    if i = 0 then padding -
      (data.triple n).previous.raw.wideLeftInt else -(padding : Int)
  let zHorizontal : Nat -> Site 2 := fun n => fun i =>
    if i = 0 then
      (data.triple n).current.raw.wideLeftInt - padding
    else padding
  constructor
  · have htranslated := Edual.verticalCrossing_translate_tendsto_one
      muDual hTI zVertical
      (fun n => (data.triple n).previous.raw.data.wideLeft)
      (fun n => (data.triple n).previous.raw.data.wideRight)
      (fun _ => 0) (fun n => (data.triple n).previousY) hvertical
    apply htranslated.congr'
    filter_upwards with n
    have hcurrentR : ((data.triple n).currentX : Real) =
        ((data.triple n).previous.raw.wideRightInt : Real) -
          (data.triple n).previous.raw.wideLeftInt + 2 * padding := by
      exact_mod_cast (data.triple n).currentX_eq
    have hpreviousYR : ((data.triple n).previousY : Real) =
        (data.triple n).currentY + 2 * padding := by
      exact_mod_cast (data.triple n).previousY_eq
    apply congrArg (fun event : Set (ConfigSpace (Sym2 W)) =>
      muDual.real event)
    congr 1
    all_goals
      simp only [transitionA0, transitionB0, transitionC0, transitionD0,
        zVertical, Pi.zero_apply, if_pos, if_neg]
    · rw [(data.triple n).previous.raw.wideLeft_eq]
      push_cast
      ring
    · rw [(data.triple n).previous.raw.wideRight_eq]
      push_cast
      linarith [hcurrentR]
    · push_cast
      ring
    · push_cast
      linarith [hpreviousYR]
  · have htranslated := Edual.horizontalCrossing_translate_tendsto_one
      muDual hTI zHorizontal (fun _ => 0)
      (fun n => (data.triple n).nextX) (fun _ => 0)
      (fun n => (data.triple n).nextY) hhorizontal
    apply htranslated.congr'
    filter_upwards with n
    have hnextR : ((data.triple n).nextX : Real) =
        ((data.triple n).current.raw.wideRightInt : Real) -
          (data.triple n).current.raw.wideLeftInt + 2 * padding := by
      exact_mod_cast (data.triple n).nextX_eq
    have hcurrentYR : ((data.triple n).currentY : Real) =
        (data.triple n).nextY + 2 * padding := by
      exact_mod_cast (data.triple n).currentY_eq
    apply congrArg (fun event : Set (ConfigSpace (Sym2 W)) =>
      muDual.real event)
    congr 1
    all_goals
      simp only [transitionA1, transitionB1, transitionC1, transitionD1,
        zHorizontal, Pi.zero_apply, if_pos, if_neg]
    · rw [(data.triple n).current.raw.wideLeft_eq]
      push_cast
      ring
    · rw [(data.triple n).current.raw.wideRight_eq]
      push_cast
      linarith [hnextR]
    · push_cast
      linarith [hcurrentYR]




theorem exists_endpoint_transitionCoordinates_of_connectorContainment
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hp : Tendsto p atTop (nhds 1)) (hp_le : forall n, p n <= 1) :
    exists verticalRadius horizontalRadius : Nat -> Nat,
      (forall n, n <= verticalRadius n) /\
      (forall n, n <= horizontalRadius n) /\
      ((forall n,
        (P.orbitBox (P.bufferedRadius (verticalRadius n)) : Set V) <=
          E.rectVertices
            (data.triple n).previous.raw.data.wideLeft
            (data.triple n).previous.raw.data.wideRight 0
            (data.triple n).previousY) ->
       (forall n,
        (P.orbitBox (P.bufferedRadius (horizontalRadius n)) : Set V) <=
          E.rectVertices 0 (data.triple n).nextX 0
            (data.triple n).nextY) ->
       Tendsto (fun n => mu.real (E.verticalCrossingEvent
          (data.transitionA0 n + padding)
          (data.transitionB0 n - padding)
          (data.transitionC0 n) (data.transitionD0 n)))
          atTop (nhds 1) /\
       Tendsto (fun n => mu.real (E.horizontalCrossingEvent
          (data.transitionA1 n) (data.transitionB1 n)
          (data.transitionC1 n + padding)
          (data.transitionD1 n - padding))) atTop (nhds 1)) := by
  let bottom : Nat -> Finset V := fun n =>
    (data.triple n).previous.raw.data.primalBottomSource
  let top : Nat -> Fin 1 -> Finset V := fun n _ =>
    (data.triple n).previous.raw.data.primalTopSource
  let left : Nat -> Finset V := fun n =>
    (data.triple n).next.raw.data.primalLeftSource
  let right : Nat -> Fin 1 -> Finset V := fun n _ =>
    (data.triple n).next.raw.data.primalRightSource
  obtain ⟨verticalRadius, hverticalRadius, hverticalMerge⟩ :=
    E.exists_uniform_translatedTemplate_mergeError_tendsto_zero
      mu hTI hunique bottom top
  obtain ⟨horizontalRadius, hhorizontalRadius, hhorizontalMerge⟩ :=
    E.exists_uniform_translatedTemplate_mergeError_tendsto_zero
      mu hTI hunique left right
  refine ⟨verticalRadius, horizontalRadius, hverticalRadius,
    hhorizontalRadius, ?_⟩
  intro hverticalBox hhorizontalBox
  let z : Nat -> Site 2 := fun _ => 0
  let i : Nat -> Fin 1 := fun _ => 0
  have hshiftImage (s : Finset V) :
      s.image (P.shift (0 : Site 2)) = s := by
    ext v
    simp [P.shift_zero]
  have hmergeVertical := hverticalMerge z i
    (fun n => (data.triple n).previous.raw.data.wideLeft)
    (fun n => (data.triple n).previous.raw.data.wideRight)
    (fun _ => 0) (fun n => (data.triple n).previousY) (by
      intro n
      rw [show z n = 0 by rfl, P.shift_zero]
      intro v hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact hverticalBox n hu)
  have hmergeHorizontal := hhorizontalMerge z i
    (fun _ => 0) (fun n => (data.triple n).nextX)
    (fun _ => 0) (fun n => (data.triple n).nextY) (by
      intro n
      rw [show z n = 0 by rfl, P.shift_zero]
      intro v hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact hhorizontalBox n hu)
  apply data.endpoint_transitionCoordinates_of_mergeLimits
    hFKG hTI hp hp_le
  · simpa only [bottom, top, z, i, hshiftImage] using hmergeVertical
  · simpa only [left, right, z, i, hshiftImage] using hmergeHorizontal





theorem exists_dual_endpoint_transitionCoordinates_of_connectorContainment
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (hFKG : IsFKG muDual) (hTI : Pdual.IsTranslationInvariant muDual)
    (hunique : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (hp : Tendsto pDual atTop (nhds 1))
    (hp_le : forall n, pDual n <= 1) :
    exists verticalRadius horizontalRadius : Nat -> Nat,
      (forall n, n <= verticalRadius n) /\
      (forall n, n <= horizontalRadius n) /\
      ((forall n,
        (Pdual.orbitBox (Pdual.bufferedRadius (verticalRadius n)) : Set W) <=
          Edual.rectVertices
            (data.triple n).previous.raw.data.wideLeft
            (data.triple n).previous.raw.data.wideRight 0
            (data.triple n).previousY) ->
       (forall n,
        (Pdual.orbitBox
          (Pdual.bufferedRadius (horizontalRadius n)) : Set W) <=
          Edual.rectVertices 0 (data.triple n).nextX 0
            (data.triple n).nextY) ->
       Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent
          (data.transitionA0 n + padding)
          (data.transitionB0 n - padding)
          (data.transitionC0 n) (data.transitionD0 n)))
          atTop (nhds 1) /\
       Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent
          (data.transitionA1 n) (data.transitionB1 n)
          (data.transitionC1 n + padding)
          (data.transitionD1 n - padding))) atTop (nhds 1)) := by
  let bottom : Nat -> Finset W := fun n =>
    (data.triple n).previous.raw.data.dualBottomSource
  let top : Nat -> Fin 1 -> Finset W := fun n _ =>
    (data.triple n).previous.raw.data.dualTopSource
  let left : Nat -> Finset W := fun n =>
    (data.triple n).next.raw.data.dualLeftSource
  let right : Nat -> Fin 1 -> Finset W := fun n _ =>
    (data.triple n).next.raw.data.dualRightSource
  obtain ⟨verticalRadius, hverticalRadius, hverticalMerge⟩ :=
    Edual.exists_uniform_translatedTemplate_mergeError_tendsto_zero
      muDual hTI hunique bottom top
  obtain ⟨horizontalRadius, hhorizontalRadius, hhorizontalMerge⟩ :=
    Edual.exists_uniform_translatedTemplate_mergeError_tendsto_zero
      muDual hTI hunique left right
  refine ⟨verticalRadius, horizontalRadius, hverticalRadius,
    hhorizontalRadius, ?_⟩
  intro hverticalBox hhorizontalBox
  let z : Nat -> Site 2 := fun _ => 0
  let i : Nat -> Fin 1 := fun _ => 0
  have hshiftImage (s : Finset W) :
      s.image (Pdual.shift (0 : Site 2)) = s := by
    ext v
    simp [Pdual.shift_zero]
  have hmergeVertical := hverticalMerge z i
    (fun n => (data.triple n).previous.raw.data.wideLeft)
    (fun n => (data.triple n).previous.raw.data.wideRight)
    (fun _ => 0) (fun n => (data.triple n).previousY) (by
      intro n
      rw [show z n = 0 by rfl, Pdual.shift_zero]
      intro v hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact hverticalBox n hu)
  have hmergeHorizontal := hhorizontalMerge z i
    (fun _ => 0) (fun n => (data.triple n).nextX)
    (fun _ => 0) (fun n => (data.triple n).nextY) (by
      intro n
      rw [show z n = 0 by rfl, Pdual.shift_zero]
      intro v hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact hhorizontalBox n hu)
  apply data.dual_endpoint_transitionCoordinates_of_mergeLimits
    hFKG hTI hp hp_le
  · simpa only [bottom, top, z, i, hshiftImage] using hmergeVertical
  · simpa only [left, right, z, i, hshiftImage] using hmergeHorizontal



theorem transitionCoordinates_spans
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (B : Nat) (hpadding : 5 * B < padding) :
    (forall n, data.transitionA0 n + 5 * B <
      data.transitionB0 n - 5 * B) /\
    (forall n, data.transitionC0 n + 5 * B <
      data.transitionD0 n - 5 * B) /\
    (forall n, data.transitionA1 n + 5 * B <
      data.transitionB1 n - 5 * B) /\
    (forall n, data.transitionC1 n + 5 * B <
      data.transitionD1 n - 5 * B) := by
  have hpadR : (5 * B : Real) < padding := by exact_mod_cast hpadding
  constructor
  · intro n
    have hspan := (data.triple n).previous.raw.extentX_le_wideSpan
    have hcurrent := (data.triple n).currentX_eq
    have hnonneg : (0 : Int) <=
        (data.triple n).previous.raw.wideRightInt -
          (data.triple n).previous.raw.wideLeftInt := by
      exact (show (0 : Int) <= (data.triple n).previousX by omega).trans hspan
    have hsize : (10 * B : Nat) < (data.triple n).currentX := by
      have hcast : (2 * padding : Int) <= (data.triple n).currentX := by
        rw [hcurrent]
        omega
      have hnat : 2 * padding <= (data.triple n).currentX := by
        exact_mod_cast hcast
      omega
    change (0 : Real) + 5 * (B : Real) <
      ((data.triple n).currentX : Real) - 5 * (B : Real)
    have hsizeR : (10 * B : Real) < (data.triple n).currentX := by
      exact_mod_cast hsize
    linarith
  · constructor
    · intro n
      have hsize : (10 * B : Nat) < (data.triple n).currentY := by
        rw [(data.triple n).currentY_eq]
        omega
      simp only [transitionC0, transitionD0]
      have hsizeR : (10 * B : Real) < (data.triple n).currentY := by
        exact_mod_cast hsize
      linarith
    · constructor
      · intro n
        have hleft := (data.triple n).current.raw.data.wideLeft_le
        have hright := (data.triple n).current.raw.data.narrowRight_le
        have hzeroRight : (0 : Real) <=
            (data.triple n).current.raw.data.wideRight := by
          exact (show (0 : Real) <= (data.triple n).currentX by positivity).trans
            (by simpa [(data.triple n).current.raw.narrowRight_eq] using hright)
        simp only [transitionA1, transitionB1]
        linarith
      · intro n
        have hsize : (10 * B : Nat) < (data.triple n).currentY := by
          rw [(data.triple n).currentY_eq]
          omega
        change (0 : Real) + 5 * (B : Real) <
          ((data.triple n).currentY : Real) - 5 * (B : Real)
        have hsizeR : (10 * B : Real) < (data.triple n).currentY := by
          exact_mod_cast hsize
        linarith





theorem transitionCoordinates_spans_of_current_gt
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (B : Real)
    (hcurrentX : forall n, 10 * B < (data.triple n).currentX)
    (hcurrentY : forall n, 10 * B < (data.triple n).currentY) :
    (forall n, data.transitionA0 n + 5 * B <
      data.transitionB0 n - 5 * B) /\
    (forall n, data.transitionC0 n + 5 * B <
      data.transitionD0 n - 5 * B) /\
    (forall n, data.transitionA1 n + 5 * B <
      data.transitionB1 n - 5 * B) /\
    (forall n, data.transitionC1 n + 5 * B <
      data.transitionD1 n - 5 * B) := by
  constructor
  · intro n
    simp only [transitionA0, transitionB0]
    linarith [hcurrentX n]
  constructor
  · intro n
    simp only [transitionC0, transitionD0]
    have hpad : (0 : Real) <= padding := by positivity
    linarith [hcurrentY n]
  constructor
  · intro n
    have hspan := (data.triple n).current.raw.extentX_le_wideSpan
    have hspanR : ((data.triple n).currentX : Real) <=
        (data.triple n).current.raw.wideRightInt -
          (data.triple n).current.raw.wideLeftInt := by
      exact_mod_cast hspan
    simp only [transitionA1, transitionB1]
    rw [(data.triple n).current.raw.wideLeft_eq,
      (data.triple n).current.raw.wideRight_eq]
    push_cast
    have hpad : (0 : Real) <= padding := by positivity
    linarith [hcurrentX n]
  · intro n
    simp only [transitionC1, transitionD1]
    linarith [hcurrentY n]



theorem translatedTransitionCoordinates_spans
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (B : Nat) (hpadding : 5 * B < padding) (z0 z1 : Nat -> Site 2) :
    (forall n, data.transitionA0 n + z0 n 0 + 5 * B <
      data.transitionB0 n + z0 n 0 - 5 * B) /\
    (forall n, data.transitionC0 n + z0 n 1 + 5 * B <
      data.transitionD0 n + z0 n 1 - 5 * B) /\
    (forall n, data.transitionA1 n + z1 n 0 + 5 * B <
      data.transitionB1 n + z1 n 0 - 5 * B) /\
    (forall n, data.transitionC1 n + z1 n 1 + 5 * B <
      data.transitionD1 n + z1 n 1 - 5 * B) := by
  obtain ⟨hx0, hy0, hx1, hy1⟩ :=
    data.transitionCoordinates_spans B hpadding
  exact ⟨fun n => by linarith [hx0 n], fun n => by linarith [hy0 n],
    fun n => by linarith [hx1 n], fun n => by linarith [hy1 n]⟩

end AlignedCrossNestedPairedSequence





structure CrossNestedThreePairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (S : Finset V) (Sdual : Finset W) (p pDual : Real)
    (padding : Nat) where
  previousX : Nat
  previousY : Nat
  currentX : Nat
  currentY : Nat
  nextX : Nat
  nextY : Nat
  previous : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual previousX previousY
  current : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual currentX currentY
  next : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual nextX nextY
  currentX_eq : (currentX : Int) =
    previous.wideRightInt - previous.wideLeftInt + 2 * padding
  nextX_eq : (nextX : Int) =
    current.wideRightInt - current.wideLeftInt + 2 * padding
  previousY_eq : previousY = currentY + 2 * padding
  currentY_eq : currentY = nextY + 2 * padding



theorem nonempty_crossNestedThreePairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding : Nat) :
    Nonempty (CrossNestedThreePairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual padding) := by
  obtain ⟨thresholdX, thresholdY, hthreshold⟩ :=
    exists_exactExtentPairedMixedBoundaryScores_thresholds
      E Edual mu muDual hTI hTIDual family familyDual schedule k
  let nextY := thresholdY
  let currentY := nextY + 2 * padding
  let previousY := currentY + 2 * padding
  let previousX := thresholdX
  let previous := Classical.choice
    (hthreshold (extentX := previousX) (extentY := previousY)
      (by simp [previousX]) (by dsimp [previousY, currentY, nextY]; omega))
  let previousSpan := previous.wideRightInt - previous.wideLeftInt
  have hpreviousSpan : 0 <= previousSpan :=
    (show (0 : Int) <= previousX by omega).trans
      previous.extentX_le_wideSpan
  let currentX := previousSpan.toNat + 2 * padding
  have hcurrentX : thresholdX <= currentX := by
    have hspan : previousX <= previousSpan.toNat := by
      rw [Int.le_toNat hpreviousSpan]
      exact previous.extentX_le_wideSpan
    exact (show thresholdX = previousX by rfl) |>.trans_le
      (hspan.trans (Nat.le_add_right _ _))
  let current := Classical.choice
    (hthreshold (extentX := currentX) (extentY := currentY)
      hcurrentX (by simp [currentY, nextY]))
  let currentSpan := current.wideRightInt - current.wideLeftInt
  have hcurrentSpan : 0 <= currentSpan :=
    (show (0 : Int) <= currentX by omega).trans
      current.extentX_le_wideSpan
  let nextX := currentSpan.toNat + 2 * padding
  have hnextX : thresholdX <= nextX := by
    have hspan : currentX <= currentSpan.toNat := by
      rw [Int.le_toNat hcurrentSpan]
      exact current.extentX_le_wideSpan
    exact hcurrentX.trans (hspan.trans (Nat.le_add_right _ _))
  let next := Classical.choice
    (hthreshold (extentX := nextX) (extentY := nextY)
      hnextX (by simp [nextY]))
  refine ⟨{
    previousX := previousX
    previousY := previousY
    currentX := currentX
    currentY := currentY
    nextX := nextX
    nextY := nextY
    previous := previous
    current := current
    next := next
    currentX_eq := ?_
    nextX_eq := ?_
    previousY_eq := rfl
    currentY_eq := rfl }⟩
  · change ((previousSpan.toNat + 2 * padding : Nat) : Int) =
      previousSpan + 2 * (padding : Int)
    push_cast
    rw [Int.toNat_of_nonneg hpreviousSpan]
  · change ((currentSpan.toNat + 2 * padding : Nat) : Int) =
      currentSpan + 2 * (padding : Int)
    push_cast
    rw [Int.toNat_of_nonneg hcurrentSpan]



theorem exists_exactExtentPairedMixedBoundaryScores_ge
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k minimumX minimumY : Nat) :
    exists extentX extentY,
      minimumX <= extentX /\ minimumY <= extentY /\
      Nonempty (ExactExtentPairedMixedBoundaryScores E Edual mu muDual
        S Sdual p pDual extentX extentY) := by
  let h := schedule.horizontal k
  let v := schedule.vertical k
  let radiusX := max
    (max (family.radiusLeft h) (family.radiusRight h))
    (max (familyDual.radiusLeft h) (familyDual.radiusRight h))
  let radiusY := max
    (max (family.radiusBottom v) (family.radiusTop v))
    (max (familyDual.radiusBottom v) (familyDual.radiusTop v))
  obtain ⟨extentX, extentY, width, height, widthDual, heightDual,
      hminX, hminY, hwidth, hheight, hwidthDual, hheightDual,
      hb, hbDual, hd, hdDual⟩ :=
    exists_pairedMixedGridDimensions E Edual family familyDual h v
      (max minimumX radiusX) (max minimumY radiusY)
  have hminimumX : minimumX <= extentX :=
    (Nat.le_max_left _ _).trans hminX
  have hminimumY : minimumY <= extentY :=
    (Nat.le_max_left _ _).trans hminY
  have hleftP : family.radiusLeft h <= extentX :=
    (Nat.le_max_left _ _).trans (Nat.le_max_left _ _) |>.trans
      ((Nat.le_max_right _ _).trans hminX)
  have hrightP : family.radiusRight h <= extentX :=
    (Nat.le_max_right _ _).trans (Nat.le_max_left _ _) |>.trans
      ((Nat.le_max_right _ _).trans hminX)
  have hleftD : familyDual.radiusLeft h <= extentX :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _) |>.trans
      ((Nat.le_max_right _ _).trans hminX)
  have hrightD : familyDual.radiusRight h <= extentX :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _) |>.trans
      ((Nat.le_max_right _ _).trans hminX)
  have hbottomP : family.radiusBottom v <= extentY :=
    (Nat.le_max_left _ _).trans (Nat.le_max_left _ _) |>.trans
      ((Nat.le_max_right _ _).trans hminY)
  have htopP : family.radiusTop v <= extentY :=
    (Nat.le_max_right _ _).trans (Nat.le_max_left _ _) |>.trans
      ((Nat.le_max_right _ _).trans hminY)
  have hbottomD : familyDual.radiusBottom v <= extentY :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _) |>.trans
      ((Nat.le_max_right _ _).trans hminY)
  have htopD : familyDual.radiusTop v <= extentY :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _) |>.trans
      ((Nat.le_max_right _ _).trans hminY)
  have hposX : 0 < family.baseRight 0 - h + extentX -
      (family.baseLeft 0 + h) := by omega
  have hposXDual : 0 < familyDual.baseRight 0 - h + extentX -
      (familyDual.baseLeft 0 + h) := by omega
  have hposY : 0 < family.baseTop 1 - v + extentY -
      (family.baseBottom 1 + v) := by omega
  have hposYDual : 0 < familyDual.baseTop 1 - v + extentY -
      (familyDual.baseBottom 1 + v) := by omega
  refine ⟨extentX, extentY, hminimumX, hminimumY, ?_⟩
  exact exists_pairedMixedBoundaryScores_atExtents E Edual mu muDual
    hTI hTIDual family familyDual schedule k extentX extentY
    hposX hposXDual hposY hposYDual hleftP hrightP hbottomP htopP
    hleftD hrightD hbottomD htopD




theorem exists_pairedCommonBoundaryPairMergeRadius
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
    [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (bottom top left right : Finset V)
    (bottomDual topDual leftDual rightDual : Finset W)
    (cutoff : Nat) {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists radius, cutoff <= radius /\
      mu.real (P.pairMergeErrorUnion bottom top radius) < epsilon /\
      mu.real (P.pairMergeErrorUnion left right radius) < epsilon /\
      muDual.real
        (Pdual.pairMergeErrorUnion bottomDual topDual radius) < epsilon /\
      muDual.real
        (Pdual.pairMergeErrorUnion leftDual rightDual radius) < epsilon := by
  have hPV : ∀ᶠ radius in atTop,
      mu.real (P.pairMergeErrorUnion bottom top radius) < epsilon :=
    (tendsto_order.1
      (P.pairMergeErrorUnion_real_tendsto_zero
        mu hunique bottom top)).2 epsilon hepsilon
  have hPH : ∀ᶠ radius in atTop,
      mu.real (P.pairMergeErrorUnion left right radius) < epsilon :=
    (tendsto_order.1
      (P.pairMergeErrorUnion_real_tendsto_zero
        mu hunique left right)).2 epsilon hepsilon
  have hDV : ∀ᶠ radius in atTop,
      muDual.real
        (Pdual.pairMergeErrorUnion bottomDual topDual radius) < epsilon :=
    (tendsto_order.1
      (Pdual.pairMergeErrorUnion_real_tendsto_zero
        muDual huniqueDual bottomDual topDual)).2 epsilon hepsilon
  have hDH : ∀ᶠ radius in atTop,
      muDual.real
        (Pdual.pairMergeErrorUnion leftDual rightDual radius) < epsilon :=
    (tendsto_order.1
      (Pdual.pairMergeErrorUnion_real_tendsto_zero
        muDual huniqueDual leftDual rightDual)).2 epsilon hepsilon
  have hall := hPV.and (hPH.and (hDV.and hDH))
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 hall
  let radius := max cutoff threshold
  have hr := hthreshold radius (Nat.le_max_right _ _)
  exact ⟨radius, Nat.le_max_left _ _, hr.1, hr.2.1, hr.2.2.1,
    hr.2.2.2⟩


structure PairedAlignedMixedLevelStep
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (S : Nat -> Finset V) (Sdual : Nat -> Finset W)
    (p pDual : Nat -> Real)
    (family : forall m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (familyDual : forall m,
      Edual.NormalBoundaryBandFamily muDual (Sdual m) (pDual m))
    (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
    (previousScale previousConnector : Nat)
    (scoreEpsilon mergeEpsilon : Real) where
  scale : Nat
  scale_ge : previousScale <= scale
  primal_threshold_gt : 1 - scoreEpsilon < p scale
  dual_threshold_gt : 1 - scoreEpsilon < pDual scale
  schedule : PairedAlignedMarginSchedule E Edual
    (family scale) (familyDual scale)
    (verticalRequirement scale) (horizontalRequirement scale)
  mixed : PairedMixedBoundaryScores E Edual mu muDual
    (S scale) (Sdual scale) (p scale) (pDual scale)
  rotated : PairedMixedBoundaryScores E.axisSwap Edual.axisSwap mu muDual
    (S scale) (Sdual scale) (p scale) (pDual scale)
  nextConnector : Nat
  connector_mono : previousConnector <= nextConnector
  primalVerticalMerge : mu.real (P.pairMergeErrorUnion
    mixed.primalBottomSource mixed.primalTopSource nextConnector) <
      mergeEpsilon
  primalHorizontalMerge : mu.real (P.pairMergeErrorUnion
    mixed.primalLeftSource mixed.primalRightSource nextConnector) <
      mergeEpsilon
  dualVerticalMerge : muDual.real (Pdual.pairMergeErrorUnion
    mixed.dualBottomSource mixed.dualTopSource nextConnector) < mergeEpsilon
  dualHorizontalMerge : muDual.real (Pdual.pairMergeErrorUnion
    mixed.dualLeftSource mixed.dualRightSource nextConnector) < mergeEpsilon


theorem nonempty_pairedAlignedMixedLevelStep
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
    [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (S : Nat -> Finset V) (Sdual : Nat -> Finset W)
    (p pDual : Nat -> Real)
    (family : forall m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (familyDual : forall m,
      Edual.NormalBoundaryBandFamily muDual (Sdual m) (pDual m))
    (hp : Tendsto p atTop (nhds 1))
    (hpDual : Tendsto pDual atTop (nhds 1))
    (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
    (previousScale previousConnector : Nat)
    {scoreEpsilon mergeEpsilon : Real}
    (hscoreEpsilon : 0 < scoreEpsilon)
    (hmergeEpsilon : 0 < mergeEpsilon) :
    Nonempty (PairedAlignedMixedLevelStep E Edual mu muDual
      S Sdual p pDual family familyDual
      verticalRequirement horizontalRequirement previousScale
      previousConnector scoreEpsilon mergeEpsilon) := by
  have hpEventually : ∀ᶠ m in atTop,
      1 - scoreEpsilon < p m :=
    (tendsto_order.1 hp).1 (1 - scoreEpsilon) (by linarith)
  have hpDualEventually : ∀ᶠ m in atTop,
      1 - scoreEpsilon < pDual m :=
    (tendsto_order.1 hpDual).1 (1 - scoreEpsilon) (by linarith)
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 hpEventually
  obtain ⟨thresholdDual, hthresholdDual⟩ :=
    eventually_atTop.1 hpDualEventually
  let m := max previousScale (max threshold thresholdDual)
  have hm : previousScale <= m := Nat.le_max_left _ _
  have hpm : 1 - scoreEpsilon < p m :=
    hthreshold m ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  have hpmDual : 1 - scoreEpsilon < pDual m :=
    hthresholdDual m
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  let schedule := Classical.choice
    (exists_pairedAlignedMarginSchedule E Edual
      (family m) (familyDual m)
      (verticalRequirement m) (horizontalRequirement m))
  let mixed := Classical.choice
    (exists_pairedMixedBoundaryScores E Edual mu muDual hTI hTIDual
      (family m) (familyDual m) schedule 0)
  let rotated := Classical.choice
    (exists_pairedRotatedMixedBoundaryScores E Edual mu muDual hTI hTIDual
      (family m) (familyDual m) schedule 0)
  obtain ⟨nextConnector, hconnector, hPV, hPH, hDV, hDH⟩ :=
    exists_pairedCommonBoundaryPairMergeRadius P Pdual mu muDual
      hunique huniqueDual
      mixed.primalBottomSource mixed.primalTopSource
      mixed.primalLeftSource mixed.primalRightSource
      mixed.dualBottomSource mixed.dualTopSource
      mixed.dualLeftSource mixed.dualRightSource
      previousConnector hmergeEpsilon
  exact ⟨{
    scale := m
    scale_ge := hm
    primal_threshold_gt := hpm
    dual_threshold_gt := hpmDual
    schedule := schedule
    mixed := mixed
    rotated := rotated
    nextConnector := nextConnector
    connector_mono := hconnector
    primalVerticalMerge := hPV
    primalHorizontalMerge := hPH
    dualVerticalMerge := hDV
    dualHorizontalMerge := hDH }⟩


theorem exists_recursivePairedAlignedMixedLevelSteps
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
    [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (S : Nat -> Finset V) (Sdual : Nat -> Finset W)
    (p pDual : Nat -> Real)
    (family : forall m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (familyDual : forall m,
      Edual.NormalBoundaryBandFamily muDual (Sdual m) (pDual m))
    (hp : Tendsto p atTop (nhds 1))
    (hpDual : Tendsto pDual atTop (nhds 1))
    (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
    (scoreEpsilon mergeEpsilon : Nat -> Real)
    (hscoreEpsilon : forall n, 0 < scoreEpsilon n)
    (hmergeEpsilon : forall n, 0 < mergeEpsilon n) :
    exists state : Nat -> Nat × Nat,
      exists steps : forall n, PairedAlignedMixedLevelStep
        E Edual mu muDual S Sdual p pDual family familyDual
        verticalRequirement horizontalRequirement
        (state n).1 (state n).2 (scoreEpsilon n) (mergeEpsilon n),
      state 0 = (0, 0) /\
      forall n, state (n + 1) =
        ((steps n).scale + 1, (steps n).nextConnector) := by
  let chooseStep (n : Nat) (state : Nat × Nat) := Classical.choice
    (nonempty_pairedAlignedMixedLevelStep E Edual mu muDual hTI hTIDual
      hunique huniqueDual S Sdual p pDual family familyDual hp hpDual
      verticalRequirement horizontalRequirement state.1 state.2
      (hscoreEpsilon n) (hmergeEpsilon n))
  let state : Nat -> Nat × Nat := fun n =>
    Nat.rec (0, 0) (fun n previous =>
      let step := chooseStep n previous
      (step.scale + 1, step.nextConnector)) n
  let steps := fun n => chooseStep n (state n)
  refine ⟨state, steps, rfl, ?_⟩
  intro n
  simp only [state, steps]



theorem exists_recursivePairedAlignedMixedLevelSteps_with_limits
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
    [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (S : Nat -> Finset V) (Sdual : Nat -> Finset W)
    (p pDual : Nat -> Real)
    (family : forall m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (familyDual : forall m,
      Edual.NormalBoundaryBandFamily muDual (Sdual m) (pDual m))
    (hp : Tendsto p atTop (nhds 1)) (hp_le : forall m, p m <= 1)
    (hpDual : Tendsto pDual atTop (nhds 1))
    (hpDual_le : forall m, pDual m <= 1)
    (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat) :
    let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
    exists state : Nat -> Nat × Nat,
      exists steps : forall n, PairedAlignedMixedLevelStep
        E Edual mu muDual S Sdual p pDual family familyDual
        verticalRequirement horizontalRequirement
        (state n).1 (state n).2 (epsilon n) (epsilon n),
      state 0 = (0, 0) /\
      (forall n, state (n + 1) =
        ((steps n).scale + 1, (steps n).nextConnector)) /\
      Tendsto (fun n => (steps n).scale) atTop atTop /\
      Tendsto (fun n => p (steps n).scale) atTop (nhds 1) /\
      Tendsto (fun n => pDual (steps n).scale) atTop (nhds 1) /\
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion
        (steps n).mixed.primalBottomSource
        (steps n).mixed.primalTopSource (steps n).nextConnector))
        atTop (nhds 0) /\
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion
        (steps n).mixed.primalLeftSource
        (steps n).mixed.primalRightSource (steps n).nextConnector))
        atTop (nhds 0) /\
      Tendsto (fun n => muDual.real (Pdual.pairMergeErrorUnion
        (steps n).mixed.dualBottomSource
        (steps n).mixed.dualTopSource (steps n).nextConnector))
        atTop (nhds 0) /\
      Tendsto (fun n => muDual.real (Pdual.pairMergeErrorUnion
        (steps n).mixed.dualLeftSource
        (steps n).mixed.dualRightSource (steps n).nextConnector))
        atTop (nhds 0) := by
  dsimp only
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  obtain ⟨state, steps, hstate0, hstateSucc⟩ :=
    exists_recursivePairedAlignedMixedLevelSteps E Edual mu muDual
      hTI hTIDual hunique huniqueDual S Sdual p pDual family familyDual
      hp hpDual verticalRequirement horizontalRequirement
      epsilon epsilon hepsilon hepsilon
  have hstateCofinal : forall n, n <= (state n).1 := by
    intro n
    induction n with
    | zero => simp [hstate0]
    | succ n ih =>
        rw [hstateSucc n]
        exact Nat.succ_le_succ (ih.trans (steps n).scale_ge)
  have hscaleCofinal : forall n, n <= (steps n).scale := fun n =>
    (hstateCofinal n).trans (steps n).scale_ge
  have hscaleTop : Tendsto (fun n => (steps n).scale) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hscaleCofinal n)
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    simpa only [epsilon] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hlower : Tendsto (fun n => 1 - epsilon n) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilonZero
  have hpStep : Tendsto (fun n => p (steps n).scale)
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (steps n).primal_threshold_gt)
      (fun n => hp_le (steps n).scale)
  have hpDualStep : Tendsto (fun n => pDual (steps n).scale)
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (steps n).dual_threshold_gt)
      (fun n => hpDual_le (steps n).scale)
  have hPV := squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => le_of_lt (steps n).primalVerticalMerge) hepsilonZero
  have hPH := squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => le_of_lt (steps n).primalHorizontalMerge) hepsilonZero
  have hDV := squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => le_of_lt (steps n).dualVerticalMerge) hepsilonZero
  have hDH := squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => le_of_lt (steps n).dualHorizontalMerge) hepsilonZero
  exact ⟨state, steps, hstate0, hstateSucc, hscaleTop, hpStep, hpDualStep,
    hPV, hPH, hDV, hDH⟩





structure PeriodicPlanarDualPair.PointwiseRecursiveRectangleArrayCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  B : Real
  Bpos : 0 < B
  primalArcBound : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B
  dualArcBound : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B
  a : Nat -> Nat -> Real
  b : Nat -> Nat -> Real
  c : Nat -> Nat -> Real
  d : Nat -> Nat -> Real
  spanX : forall k n, a k n + 5 * B < b k n - 5 * B
  spanY : forall k n, c k n + 5 * B < d k n - 5 * B
  verticalStart : Tendsto (fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a 0 n + 4 * B) (b 0 n - 4 * B) (c 0 n) (d 0 n)))
    atTop (nhds 1)
  horizontalLevel : forall k, Tendsto (fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a (k + 1) n) (b (k + 1) n)
      (c (k + 1) n + 4 * B) (d (k + 1) n - 4 * B)))
    atTop (nhds 1)
  primalLevel : forall k, Tendsto (fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (a (k + 1) n + 4 * B) (b (k + 1) n - 4 * B)
      (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1)
  dualLevel : forall k, Tendsto (fun n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a k n + 4 * B) (b k n - 4 * B) (c k n) (d k n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B))))
    atTop (nhds 1)




theorem exists_cofinalIndex_five_uniform_tendsto_one_below_diagonal
    (f0 f1 f2 f3 f4 : Nat -> Nat -> Real)
    (hf0 : forall k, Tendsto (f0 k) atTop (nhds 1))
    (hf1 : forall k, Tendsto (f1 k) atTop (nhds 1))
    (hf2 : forall k, Tendsto (f2 k) atTop (nhds 1))
    (hf3 : forall k, Tendsto (f3 k) atTop (nhds 1))
    (hf4 : forall k, Tendsto (f4 k) atTop (nhds 1))
    (hle0 : forall k n, f0 k n <= 1)
    (hle1 : forall k n, f1 k n <= 1)
    (hle2 : forall k n, f2 k n <= 1)
    (hle3 : forall k n, f3 k n <= 1)
    (hle4 : forall k n, f4 k n <= 1) :
    exists index : Nat -> Nat,
      (forall n, n <= index n) /\
      forall k : Nat -> Nat, (forall n, k n < n + 1) ->
        Tendsto (fun n => f0 (k n) (index n)) atTop (nhds 1) /\
        Tendsto (fun n => f1 (k n) (index n)) atTop (nhds 1) /\
        Tendsto (fun n => f2 (k n) (index n)) atTop (nhds 1) /\
        Tendsto (fun n => f3 (k n) (index n)) atTop (nhds 1) /\
        Tendsto (fun n => f4 (k n) (index n)) atTop (nhds 1) := by
  let combined : Nat -> Nat -> Real := fun k n =>
    min (f0 k n) (min (f1 k n)
      (min (f2 k n) (min (f3 k n) (f4 k n))))
  have hcombined (k : Nat) : Tendsto (combined k) atTop (nhds 1) := by
    simpa only [combined, min_self] using
      (hf0 k).min ((hf1 k).min ((hf2 k).min ((hf3 k).min (hf4 k))))
  have hcombinedLe (k n : Nat) : combined k n <= 1 :=
    (min_le_left _ _).trans (hle0 k n)
  obtain ⟨index, hindex, huniform⟩ :=
    exists_cofinalIndex_uniform_tendsto_one_below_diagonal
      combined hcombined hcombinedLe
  refine ⟨index, hindex, ?_⟩
  intro k hk
  have hlimit := huniform k hk
  refine ⟨hlimit.squeeze tendsto_const_nhds
      (fun n => min_le_left _ _) (fun n => hle0 (k n) (index n)), ?_⟩
  refine ⟨hlimit.squeeze tendsto_const_nhds
      (fun n => (min_le_right _ _).trans (min_le_left _ _))
      (fun n => hle1 (k n) (index n)), ?_⟩
  refine ⟨hlimit.squeeze tendsto_const_nhds
      (fun n => (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
      (fun n => hle2 (k n) (index n)), ?_⟩
  refine ⟨hlimit.squeeze tendsto_const_nhds
      (fun n => (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
      (fun n => hle3 (k n) (index n)), ?_⟩
  exact hlimit.squeeze tendsto_const_nhds
    (fun n => (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))))
    (fun n => hle4 (k n) (index n))




theorem PeriodicPlanarDualPair.PointwiseRecursiveRectangleArrayCertificate.toRecursive
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (raw : D.PointwiseRecursiveRectangleArrayCertificate mu) :
    Nonempty (D.RecursiveRectangleArrayCertificate mu) := by
  let horizontal : Nat -> Nat -> Real := fun k n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (raw.a (k + 1) n) (raw.b (k + 1) n)
      (raw.c (k + 1) n + 4 * raw.B) (raw.d (k + 1) n - 4 * raw.B))
  let primal : Nat -> Nat -> Real := fun k n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (raw.a k n) (raw.b k n)
      (raw.c k n + 4 * raw.B) (raw.d k n - 4 * raw.B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (raw.a (k + 1) n + 4 * raw.B) (raw.b (k + 1) n - 4 * raw.B)
      (raw.c (k + 1) n) (raw.d (k + 1) n)))
  let dual : Nat -> Nat -> Real := fun k n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (raw.a k n + 4 * raw.B) (raw.b k n - 4 * raw.B)
        (raw.c k n) (raw.d k n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (raw.a k n) (raw.b k n)
        (raw.c k n + 4 * raw.B) (raw.d k n - 4 * raw.B)))
  let combined : Nat -> Nat -> Real := fun k n =>
    min (horizontal k n) (min (primal k n) (dual k n))
  have hhorizontal (k : Nat) : Tendsto (horizontal k) atTop (nhds 1) := by
    simpa only [horizontal] using raw.horizontalLevel k
  have hprimal (k : Nat) : Tendsto (primal k) atTop (nhds 1) := by
    simpa only [primal] using raw.primalLevel k
  have hdual (k : Nat) : Tendsto (dual k) atTop (nhds 1) := by
    simpa only [dual] using raw.dualLevel k
  have hcombined (k : Nat) : Tendsto (combined k) atTop (nhds 1) := by
    simpa only [combined, min_self] using
      (hhorizontal k).min ((hprimal k).min (hdual k))
  have hcombinedLe (k n : Nat) : combined k n <= 1 :=
    (min_le_left _ _).trans measureReal_le_one
  obtain ⟨index, hindex, huniform⟩ :=
    exists_cofinalIndex_uniform_tendsto_one_below_diagonal
      combined hcombined hcombinedLe
  have hindexTop : Tendsto index atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hindex n)
  let K : Nat -> Nat := fun n => n.pred
  let a : Nat -> Nat -> Real := fun n k => raw.a k (index n)
  let b : Nat -> Nat -> Real := fun n k => raw.b k (index n)
  let c : Nat -> Nat -> Real := fun n k => raw.c k (index n)
  let d : Nat -> Nat -> Real := fun n k => raw.d k (index n)
  have hcomponentLimit (k : Nat -> Nat) (hk : forall n, k n < n + 1) :
      Tendsto (fun n => combined (k n) (index n)) atTop (nhds 1) :=
    huniform k hk
  have hhorizontalOfCombined (k : Nat -> Nat)
      (hk : forall n, k n < n + 1) :
      Tendsto (fun n => horizontal (k n) (index n)) atTop (nhds 1) :=
    (hcomponentLimit k hk).squeeze tendsto_const_nhds
      (fun n => min_le_left _ _) (fun _ => measureReal_le_one)
  have hprimalOfCombined (k : Nat -> Nat)
      (hk : forall n, k n < n + 1) :
      Tendsto (fun n => primal (k n) (index n)) atTop (nhds 1) :=
    (hcomponentLimit k hk).squeeze tendsto_const_nhds
      (fun n => (min_le_right _ _).trans (min_le_left _ _))
      (fun _ => max_le measureReal_le_one measureReal_le_one)
  have hdualOfCombined (k : Nat -> Nat)
      (hk : forall n, k n < n + 1) :
      Tendsto (fun n => dual (k n) (index n)) atTop (nhds 1) :=
    (hcomponentLimit k hk).squeeze tendsto_const_nhds
      (fun n => (min_le_right _ _).trans (min_le_right _ _))
      (fun _ => max_le measureReal_le_one measureReal_le_one)
  refine ⟨{
    B := raw.B
    Bpos := raw.Bpos
    primalArcBound := raw.primalArcBound
    dualArcBound := raw.dualArcBound
    a := a
    b := b
    c := c
    d := d
    K := K
    spanX := fun n k => raw.spanX k (index n)
    spanY := fun n k => raw.spanY k (index n)
    verticalStart := raw.verticalStart.comp hindexTop
    horizontalEnd := ?_
    primalAdjacent := ?_
    dualLevels := ?_ }⟩
  · have hK : forall n, K n < n + 1 := by
      intro n
      exact (Nat.pred_le n).trans_lt (Nat.lt_succ_self n)
    have hlim := hhorizontalOfCombined K hK
    simpa only [horizontal, a, b, c, d] using hlim
  · intro k hk
    have hk' : forall n, k n < n + 1 := by
      intro n
      exact (hk n).trans_le (Nat.succ_le_succ (Nat.pred_le n))
    have hlim := hprimalOfCombined k hk'
    simpa only [primal, a, b, c, d] using hlim
  · intro k hk
    let k' : Nat -> Nat := fun n => if n = 0 then 0 else k n
    have hk' : forall n, k' n < n + 1 := by
      intro n
      by_cases hn : n = 0
      · simp [k', hn]
      · have hkn := hk n
        have hp : n.pred + 1 = n := by
          simpa only [Nat.succ_eq_add_one] using Nat.succ_pred hn
        dsimp only [K] at hkn
        rw [hp] at hkn
        simpa [k', hn] using Nat.lt_succ_of_le hkn
    have hlim := hdualOfCombined k' hk'
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    simpa [dual, a, b, c, d, k', hn0]



theorem PeriodicPlanarDualPair.PointwiseRecursiveRectangleArrayCertificate.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (raw : D.PointwiseRecursiveRectangleArrayCertificate mu) : False := by
  obtain ⟨bounded⟩ := raw.toRecursive D mu
  exact bounded.false D mu




theorem PeriodicPlanarDualPair.pointwiseRecursiveRectangleArray_false_of_normal_rotated_limits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a b c d : Nat -> Nat -> Real)
    (hspanX : forall k n, a k n + 5 * B < b k n - 5 * B)
    (hspanY : forall k n, c k n + 5 * B < d k n - 5 * B)
    (hverticalStart : Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (a 0 n + 4 * B) (b 0 n - 4 * B) (c 0 n) (d 0 n)))
      atTop (nhds 1))
    (hhorizontalLevel : forall k, Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (a (k + 1) n) (b (k + 1) n)
        (c (k + 1) n + 4 * B) (d (k + 1) n - 4 * B)))
      atTop (nhds 1))
    (hnormalAdjacent : forall k, Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a (k + 1) n + 4 * B) (b (k + 1) n - 4 * B)
        (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1))
    (hrotatedDualLevel : forall k, Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a k n + 4 * B) (b k n - 4 * B) (c k n) (d k n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B))))
      atTop (nhds 1)) : False := by
  exact PeriodicPlanarDualPair.PointwiseRecursiveRectangleArrayCertificate.false
    D mu {
      B := B
      Bpos := hBpos
      primalArcBound := hBp
      dualArcBound := hBd
      a := a
      b := b
      c := c
      d := d
      spanX := hspanX
      spanY := hspanY
      verticalStart := hverticalStart
      horizontalLevel := hhorizontalLevel
      primalLevel := hnormalAdjacent
      dualLevel := hrotatedDualLevel }




theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_normal_rotated_limits
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a b c d : Nat -> Nat -> Real)
    (hspanX : forall k n, a k n + 5 * B < b k n - 5 * B)
    (hspanY : forall k n, c k n + 5 * B < d k n - 5 * B)
    (hverticalStart :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      Tendsto (fun n => mu.real
        (D.primalEmbedding.verticalCrossingEvent
          (a 0 n + 4 * B) (b 0 n - 4 * B) (c 0 n) (d 0 n)))
        atTop (nhds 1))
    (hhorizontalLevel :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => mu.real
        (D.primalEmbedding.horizontalCrossingEvent
          (a (k + 1) n) (b (k + 1) n)
          (c (k + 1) n + 4 * B) (d (k + 1) n - 4 * B)))
        atTop (nhds 1))
    (hnormalAdjacent :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          (a (k + 1) n + 4 * B) (b (k + 1) n - 4 * B)
          (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1))
    (hrotatedDualLevel :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a k n + 4 * B) (b k n - 4 * B) (c k n) (d k n)))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B))))
        atTop (nhds 1)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only at hverticalStart hhorizontalLevel hnormalAdjacent
  dsimp only at hrotatedDualLevel
  dsimp only
  intro _hcommon
  exact D.pointwiseRecursiveRectangleArray_false_of_normal_rotated_limits
    _ B hBpos hBp hBd a b c d hspanX hspanY hverticalStart
    hhorizontalLevel hnormalAdjacent hrotatedDualLevel



theorem PeriodicPlanarDualPair.dualMeasure_crossingMax_tendsto_one
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (aV bV cV dV aH bH cH dH : Nat -> Real)
    (hlimit : Tendsto (fun n => max
      ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
        (aV n) (bV n) (cV n) (dV n)))
      ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
        (aH n) (bH n) (cH n) (dH n)))) atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (aV n) (bV n) (cV n) (dV n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (aH n) (bH n) (cH n) (dH n)))) atTop (nhds 1) := by
  apply hlimit.congr'
  filter_upwards [] with n
  rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _),
    D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]



theorem PeriodicPlanarDualPair.dualMeasure_twoLevel_outward_limits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Real)
    (xPad0 yPad0 xPad1 yPad1 : Nat -> Real)
    (hdual0 : Tendsto (fun n => max
      ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
        (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n)))
      ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
        (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n))))
      atTop (nhds 1))
    (hdual1 : Tendsto (fun n => max
      ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
        (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n)))
      ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
        (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n))))
      atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n))))
      atTop (nhds 1) /\
    Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n))))
      atTop (nhds 1) := by
  constructor
  · exact D.dualMeasure_crossingMax_tendsto_one mu
      (fun n => a0 n + xPad0 n) (fun n => b0 n - xPad0 n) c0 d0
      a0 b0 (fun n => c0 n + yPad0 n) (fun n => d0 n - yPad0 n)
      hdual0
  · exact D.dualMeasure_crossingMax_tendsto_one mu
      (fun n => a1 n + xPad1 n) (fun n => b1 n - xPad1 n) c1 d1
      a1 b1 (fun n => c1 n + yPad1 n) (fun n => d1 n - yPad1 n)
      hdual1




theorem PeriodicPlanarDualPair.variablePadTwoLevel_false_of_normal_rotated_limits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Real)
    (xPad0 yPad0 xPad1 yPad1 : Nat -> Real)
    (hxPad0 : forall n, 4 * B <= xPad0 n)
    (hyPad0 : forall n, 4 * B <= yPad0 n)
    (hxPad1 : forall n, 4 * B <= xPad1 n)
    (hyPad1 : forall n, 4 * B <= yPad1 n)
    (hspanX0 : forall n, a0 n + 5 * B < b0 n - 5 * B)
    (hspanY0 : forall n, c0 n + 5 * B < d0 n - 5 * B)
    (hspanX1 : forall n, a1 n + 5 * B < b1 n - 5 * B)
    (hspanY1 : forall n, c1 n + 5 * B < d1 n - 5 * B)
    (hverticalStart : Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n)))
      atTop (nhds 1))
    (hhorizontalEnd : Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n)))
      atTop (nhds 1))
    (hnormalAdjacent : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n))))
      atTop (nhds 1))
    (hrotatedDual0 : Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n))))
      atTop (nhds 1))
    (hrotatedDual1 : Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n))))
      atTop (nhds 1)) : False := by
  exact PeriodicPlanarDualPair.VariablePadTwoLevelRectangleArray.false
    D mu {
      Bpos := hBpos
      primalArcBound := hBp
      dualArcBound := hBd
      a0 := a0
      b0 := b0
      c0 := c0
      d0 := d0
      a1 := a1
      b1 := b1
      c1 := c1
      d1 := d1
      xPad0 := xPad0
      yPad0 := yPad0
      xPad1 := xPad1
      yPad1 := yPad1
      xPad0_ge := hxPad0
      yPad0_ge := hyPad0
      xPad1_ge := hxPad1
      yPad1_ge := hyPad1
      spanX0 := hspanX0
      spanY0 := hspanY0
      spanX1 := hspanX1
      spanY1 := hspanY1
      verticalStart := hverticalStart
      horizontalEnd := hhorizontalEnd
      primalAdjacent := hnormalAdjacent
      dualLevel0 := hrotatedDual0
      dualLevel1 := hrotatedDual1 }




theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_variablePad_normal_rotated_limits
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Real)
    (xPad0 yPad0 xPad1 yPad1 : Nat -> Real)
    (hxPad0 : forall n, 4 * B <= xPad0 n)
    (hyPad0 : forall n, 4 * B <= yPad0 n)
    (hxPad1 : forall n, 4 * B <= xPad1 n)
    (hyPad1 : forall n, 4 * B <= yPad1 n)
    (hspanX0 : forall n, a0 n + 5 * B < b0 n - 5 * B)
    (hspanY0 : forall n, c0 n + 5 * B < d0 n - 5 * B)
    (hspanX1 : forall n, a1 n + 5 * B < b1 n - 5 * B)
    (hspanY1 : forall n, c1 n + 5 * B < d1 n - 5 * B)
    (hverticalStart :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      Tendsto (fun n => mu.real
        (D.primalEmbedding.verticalCrossingEvent
          (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n)))
        atTop (nhds 1))
    (hhorizontalEnd :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      Tendsto (fun n => mu.real
        (D.primalEmbedding.horizontalCrossingEvent
          (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n)))
        atTop (nhds 1))
    (hnormalAdjacent :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      Tendsto (fun n => max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n))))
        atTop (nhds 1))
    (hrotatedDual0 :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      Tendsto (fun n => max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n)))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n))))
        atTop (nhds 1))
    (hrotatedDual1 :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      Tendsto (fun n => max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n)))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n))))
        atTop (nhds 1)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only at hverticalStart hhorizontalEnd hnormalAdjacent
  dsimp only at hrotatedDual0 hrotatedDual1
  dsimp only
  intro _hcommon
  exact D.variablePadTwoLevel_false_of_normal_rotated_limits _ B hBpos
    hBp hBd a0 b0 c0 d0 a1 b1 c1 d1 xPad0 yPad0 xPad1 yPad1
    hxPad0 hyPad0 hxPad1 hyPad1 hspanX0 hspanY0 hspanX1 hspanY1
    hverticalStart hhorizontalEnd hnormalAdjacent hrotatedDual0 hrotatedDual1





theorem PeriodicPlanarDualPair.variablePadTwoLevel_false_of_pointwise_limits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a b c d xPad yPad : Nat -> Nat -> Real)
    (hxPad : forall k n, 4 * B <= xPad k n)
    (hyPad : forall k n, 4 * B <= yPad k n)
    (hspanX : forall k n, a k n + 5 * B < b k n - 5 * B)
    (hspanY : forall k n, c k n + 5 * B < d k n - 5 * B)
    (hvertical : forall k, Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (a k n + xPad k n) (b k n - xPad k n) (c k n) (d k n)))
      atTop (nhds 1))
    (hhorizontal : forall k, Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (a (k + 1) n) (b (k + 1) n)
        (c (k + 1) n + yPad (k + 1) n)
        (d (k + 1) n - yPad (k + 1) n))) atTop (nhds 1))
    (hnormal : forall k, Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a k n) (b k n) (c k n + yPad k n) (d k n - yPad k n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a (k + 1) n + xPad (k + 1) n)
        (b (k + 1) n - xPad (k + 1) n)
        (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1))
    (hdual : forall k, Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a k n + xPad k n) (b k n - xPad k n) (c k n) (d k n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a k n) (b k n) (c k n + yPad k n) (d k n - yPad k n))))
      atTop (nhds 1)) : False := by
  let f0 : Nat -> Nat -> Real := fun k n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a k n + xPad k n) (b k n - xPad k n) (c k n) (d k n))
  let f1 : Nat -> Nat -> Real := fun k n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a (k + 1) n) (b (k + 1) n)
      (c (k + 1) n + yPad (k + 1) n)
      (d (k + 1) n - yPad (k + 1) n))
  let f2 : Nat -> Nat -> Real := fun k n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a k n) (b k n) (c k n + yPad k n) (d k n - yPad k n)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (a (k + 1) n + xPad (k + 1) n)
      (b (k + 1) n - xPad (k + 1) n)
      (c (k + 1) n) (d (k + 1) n)))
  let f3 : Nat -> Nat -> Real := fun k n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a k n + xPad k n) (b k n - xPad k n) (c k n) (d k n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a k n) (b k n) (c k n + yPad k n) (d k n - yPad k n)))
  let f4 : Nat -> Nat -> Real := fun k n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a (k + 1) n + xPad (k + 1) n)
        (b (k + 1) n - xPad (k + 1) n)
        (c (k + 1) n) (d (k + 1) n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a (k + 1) n) (b (k + 1) n)
        (c (k + 1) n + yPad (k + 1) n)
        (d (k + 1) n - yPad (k + 1) n)))
  have hf0 (k : Nat) : Tendsto (f0 k) atTop (nhds 1) := by
    simpa only [f0] using hvertical k
  have hf1 (k : Nat) : Tendsto (f1 k) atTop (nhds 1) := by
    simpa only [f1] using hhorizontal k
  have hf2 (k : Nat) : Tendsto (f2 k) atTop (nhds 1) := by
    simpa only [f2] using hnormal k
  have hf3 (k : Nat) : Tendsto (f3 k) atTop (nhds 1) := by
    simpa only [f3] using hdual k
  have hf4 (k : Nat) : Tendsto (f4 k) atTop (nhds 1) := by
    simpa only [f4] using hdual (k + 1)
  obtain ⟨index, _hindex, hall⟩ :=
    exists_cofinalIndex_five_uniform_tendsto_one_below_diagonal
      f0 f1 f2 f3 f4 hf0 hf1 hf2 hf3 hf4
      (fun _ _ => measureReal_le_one)
      (fun _ _ => measureReal_le_one)
      (fun _ _ => max_le measureReal_le_one measureReal_le_one)
      (fun _ _ => max_le measureReal_le_one measureReal_le_one)
      (fun _ _ => max_le measureReal_le_one measureReal_le_one)
  let level : Nat -> Nat := fun n => n
  have hlevel (n : Nat) : level n < n + 1 := Nat.lt_succ_self n
  obtain ⟨hv, hh, hn, hd0, hd1⟩ := hall level hlevel
  apply D.variablePadTwoLevel_false_of_normal_rotated_limits mu B hBpos
    hBp hBd
    (fun n => a (level n) (index n))
    (fun n => b (level n) (index n))
    (fun n => c (level n) (index n))
    (fun n => d (level n) (index n))
    (fun n => a (level n + 1) (index n))
    (fun n => b (level n + 1) (index n))
    (fun n => c (level n + 1) (index n))
    (fun n => d (level n + 1) (index n))
    (fun n => xPad (level n) (index n))
    (fun n => yPad (level n) (index n))
    (fun n => xPad (level n + 1) (index n))
    (fun n => yPad (level n + 1) (index n))
    (fun n => hxPad (level n) (index n))
    (fun n => hyPad (level n) (index n))
    (fun n => hxPad (level n + 1) (index n))
    (fun n => hyPad (level n + 1) (index n))
    (fun n => hspanX (level n) (index n))
    (fun n => hspanY (level n) (index n))
    (fun n => hspanX (level n + 1) (index n))
    (fun n => hspanY (level n + 1) (index n))
  · simpa only [f0] using hv
  · simpa only [f1] using hh
  · simpa only [f2] using hn
  · simpa only [f3] using hd0
  · simpa only [f4] using hd1





theorem PeriodicPlanarDualPair.variablePadTwoLevel_false_of_pointwise_transitions
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Nat -> Real)
    (xPad0 yPad0 xPad1 yPad1 : Nat -> Nat -> Real)
    (hxPad0 : forall k n, 4 * B <= xPad0 k n)
    (hyPad0 : forall k n, 4 * B <= yPad0 k n)
    (hxPad1 : forall k n, 4 * B <= xPad1 k n)
    (hyPad1 : forall k n, 4 * B <= yPad1 k n)
    (hspanX0 : forall k n, a0 k n + 5 * B < b0 k n - 5 * B)
    (hspanY0 : forall k n, c0 k n + 5 * B < d0 k n - 5 * B)
    (hspanX1 : forall k n, a1 k n + 5 * B < b1 k n - 5 * B)
    (hspanY1 : forall k n, c1 k n + 5 * B < d1 k n - 5 * B)
    (hvertical : forall k, Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (a0 k n + xPad0 k n) (b0 k n - xPad0 k n)
        (c0 k n) (d0 k n))) atTop (nhds 1))
    (hhorizontal : forall k, Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (a1 k n) (b1 k n)
        (c1 k n + yPad1 k n) (d1 k n - yPad1 k n)))
      atTop (nhds 1))
    (hnormal : forall k, Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a0 k n) (b0 k n)
        (c0 k n + yPad0 k n) (d0 k n - yPad0 k n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a1 k n + xPad1 k n) (b1 k n - xPad1 k n)
        (c1 k n) (d1 k n)))) atTop (nhds 1))
    (hdual0 : forall k, Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a0 k n + xPad0 k n) (b0 k n - xPad0 k n)
          (c0 k n) (d0 k n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a0 k n) (b0 k n)
          (c0 k n + yPad0 k n) (d0 k n - yPad0 k n))))
      atTop (nhds 1))
    (hdual1 : forall k, Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a1 k n + xPad1 k n) (b1 k n - xPad1 k n)
          (c1 k n) (d1 k n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a1 k n) (b1 k n)
          (c1 k n + yPad1 k n) (d1 k n - yPad1 k n))))
      atTop (nhds 1)) : False := by
  let f0 : Nat -> Nat -> Real := fun k n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a0 k n + xPad0 k n) (b0 k n - xPad0 k n) (c0 k n) (d0 k n))
  let f1 : Nat -> Nat -> Real := fun k n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a1 k n) (b1 k n)
      (c1 k n + yPad1 k n) (d1 k n - yPad1 k n))
  let f2 : Nat -> Nat -> Real := fun k n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a0 k n) (b0 k n)
      (c0 k n + yPad0 k n) (d0 k n - yPad0 k n)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (a1 k n + xPad1 k n) (b1 k n - xPad1 k n) (c1 k n) (d1 k n)))
  let f3 : Nat -> Nat -> Real := fun k n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a0 k n + xPad0 k n) (b0 k n - xPad0 k n) (c0 k n) (d0 k n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a0 k n) (b0 k n)
        (c0 k n + yPad0 k n) (d0 k n - yPad0 k n)))
  let f4 : Nat -> Nat -> Real := fun k n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a1 k n + xPad1 k n) (b1 k n - xPad1 k n) (c1 k n) (d1 k n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a1 k n) (b1 k n)
        (c1 k n + yPad1 k n) (d1 k n - yPad1 k n)))
  obtain ⟨index, _hindex, hall⟩ :=
    exists_cofinalIndex_five_uniform_tendsto_one_below_diagonal
      f0 f1 f2 f3 f4
      (fun k => by simpa only [f0] using hvertical k)
      (fun k => by simpa only [f1] using hhorizontal k)
      (fun k => by simpa only [f2] using hnormal k)
      (fun k => by simpa only [f3] using hdual0 k)
      (fun k => by simpa only [f4] using hdual1 k)
      (fun _ _ => measureReal_le_one)
      (fun _ _ => measureReal_le_one)
      (fun _ _ => max_le measureReal_le_one measureReal_le_one)
      (fun _ _ => max_le measureReal_le_one measureReal_le_one)
      (fun _ _ => max_le measureReal_le_one measureReal_le_one)
  let level : Nat -> Nat := fun n => n
  have hlevel (n : Nat) : level n < n + 1 := Nat.lt_succ_self n
  obtain ⟨hv, hh, hn, hd0, hd1⟩ := hall level hlevel
  apply D.variablePadTwoLevel_false_of_normal_rotated_limits mu B hBpos
    hBp hBd
    (fun n => a0 (level n) (index n))
    (fun n => b0 (level n) (index n))
    (fun n => c0 (level n) (index n))
    (fun n => d0 (level n) (index n))
    (fun n => a1 (level n) (index n))
    (fun n => b1 (level n) (index n))
    (fun n => c1 (level n) (index n))
    (fun n => d1 (level n) (index n))
    (fun n => xPad0 (level n) (index n))
    (fun n => yPad0 (level n) (index n))
    (fun n => xPad1 (level n) (index n))
    (fun n => yPad1 (level n) (index n))
    (fun n => hxPad0 (level n) (index n))
    (fun n => hyPad0 (level n) (index n))
    (fun n => hxPad1 (level n) (index n))
    (fun n => hyPad1 (level n) (index n))
    (fun n => hspanX0 (level n) (index n))
    (fun n => hspanY0 (level n) (index n))
    (fun n => hspanX1 (level n) (index n))
    (fun n => hspanY1 (level n) (index n))
  · simpa only [f0] using hv
  · simpa only [f1] using hh
  · simpa only [f2] using hn
  · simpa only [f3] using hd0
  · simpa only [f4] using hd1




theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_pointwise_transitions
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Nat -> Real)
    (xPad0 yPad0 xPad1 yPad1 : Nat -> Nat -> Real)
    (hxPad0 : forall k n, 4 * B <= xPad0 k n)
    (hyPad0 : forall k n, 4 * B <= yPad0 k n)
    (hxPad1 : forall k n, 4 * B <= xPad1 k n)
    (hyPad1 : forall k n, 4 * B <= yPad1 k n)
    (hspanX0 : forall k n, a0 k n + 5 * B < b0 k n - 5 * B)
    (hspanY0 : forall k n, c0 k n + 5 * B < d0 k n - 5 * B)
    (hspanX1 : forall k n, a1 k n + 5 * B < b1 k n - 5 * B)
    (hspanY1 : forall k n, c1 k n + 5 * B < d1 k n - 5 * B)
    (hvertical :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => mu.real
        (D.primalEmbedding.verticalCrossingEvent
          (a0 k n + xPad0 k n) (b0 k n - xPad0 k n)
          (c0 k n) (d0 k n))) atTop (nhds 1))
    (hhorizontal :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => mu.real
        (D.primalEmbedding.horizontalCrossingEvent
          (a1 k n) (b1 k n)
          (c1 k n + yPad1 k n) (d1 k n - yPad1 k n)))
        atTop (nhds 1))
    (hnormal :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          (a0 k n) (b0 k n)
          (c0 k n + yPad0 k n) (d0 k n - yPad0 k n)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          (a1 k n + xPad1 k n) (b1 k n - xPad1 k n)
          (c1 k n) (d1 k n)))) atTop (nhds 1))
    (hdual0 :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a0 k n + xPad0 k n) (b0 k n - xPad0 k n)
            (c0 k n) (d0 k n)))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            (a0 k n) (b0 k n)
            (c0 k n + yPad0 k n) (d0 k n - yPad0 k n))))
        atTop (nhds 1))
    (hdual1 :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a1 k n + xPad1 k n) (b1 k n - xPad1 k n)
            (c1 k n) (d1 k n)))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            (a1 k n) (b1 k n)
            (c1 k n + yPad1 k n) (d1 k n - yPad1 k n))))
        atTop (nhds 1)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only at hvertical hhorizontal hnormal hdual0 hdual1
  dsimp only
  intro _hcommon
  exact D.variablePadTwoLevel_false_of_pointwise_transitions _ B hBpos
    hBp hBd a0 b0 c0 d0 a1 b1 c1 d1 xPad0 yPad0 xPad1 yPad1
    hxPad0 hyPad0 hxPad1 hyPad1 hspanX0 hspanY0 hspanX1 hspanY1
    hvertical hhorizontal hnormal hdual0 hdual1




theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_pointwise_variablePad_limits
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a b c d xPad yPad : Nat -> Nat -> Real)
    (hxPad : forall k n, 4 * B <= xPad k n)
    (hyPad : forall k n, 4 * B <= yPad k n)
    (hspanX : forall k n, a k n + 5 * B < b k n - 5 * B)
    (hspanY : forall k n, c k n + 5 * B < d k n - 5 * B)
    (hvertical :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => mu.real
        (D.primalEmbedding.verticalCrossingEvent
          (a k n + xPad k n) (b k n - xPad k n) (c k n) (d k n)))
        atTop (nhds 1))
    (hhorizontal :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => mu.real
        (D.primalEmbedding.horizontalCrossingEvent
          (a (k + 1) n) (b (k + 1) n)
          (c (k + 1) n + yPad (k + 1) n)
          (d (k + 1) n - yPad (k + 1) n))) atTop (nhds 1))
    (hnormal :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          (a k n) (b k n) (c k n + yPad k n) (d k n - yPad k n)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          (a (k + 1) n + xPad (k + 1) n)
          (b (k + 1) n - xPad (k + 1) n)
          (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1))
    (hdual :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a k n + xPad k n) (b k n - xPad k n) (c k n) (d k n)))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            (a k n) (b k n) (c k n + yPad k n) (d k n - yPad k n))))
        atTop (nhds 1)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only at hvertical hhorizontal hnormal hdual
  dsimp only
  intro _hcommon
  exact D.variablePadTwoLevel_false_of_pointwise_limits _ B hBpos hBp hBd
    a b c d xPad yPad hxPad hyPad hspanX hspanY
    hvertical hhorizontal hnormal hdual




structure PeriodicPlanarDualPair.ComplementaryCrossNestedLimitCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  B : Real
  Bpos : 0 < B
  primalArcBound : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B
  dualArcBound : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B
  a0 : Nat -> Real
  b0 : Nat -> Real
  c0 : Nat -> Real
  d0 : Nat -> Real
  a1 : Nat -> Real
  b1 : Nat -> Real
  c1 : Nat -> Real
  d1 : Nat -> Real
  spanX0 : forall n, a0 n + 5 * B < b0 n - 5 * B
  spanY0 : forall n, c0 n + 5 * B < d0 n - 5 * B
  spanX1 : forall n, a1 n + 5 * B < b1 n - 5 * B
  spanY1 : forall n, c1 n + 5 * B < d1 n - 5 * B
  primalAdjacent : Tendsto (fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a0 n) (b0 n) (c0 n + 4 * B) (d0 n - 4 * B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (a1 n + 4 * B) (b1 n - 4 * B) (c1 n) (d1 n))))
    atTop (nhds 1)
  dualVertical0 : Tendsto (fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n)))
    atTop (nhds 1)
  dualHorizontal1 : Tendsto (fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a1 n) (b1 n) (c1 n + 4 * B) (d1 n - 4 * B)))
    atTop (nhds 1)



theorem PeriodicPlanarDualPair.ComplementaryCrossNestedLimitCertificate.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (data : D.ComplementaryCrossNestedLimitCertificate mu) : False := by
  let H0 : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (data.a0 n) (data.b0 n)
      (data.c0 n + 4 * data.B) (data.d0 n - 4 * data.B))
  let V1 : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (data.a1 n + 4 * data.B) (data.b1 n - 4 * data.B)
      (data.c1 n) (data.d1 n))
  let dualV0 : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (data.a0 n + 4 * data.B) (data.b0 n - 4 * data.B)
        (data.c0 n) (data.d0 n))
  let dualH1 : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (data.a1 n) (data.b1 n)
        (data.c1 n + 4 * data.B) (data.d1 n - 4 * data.B))
  have hH0sum (n : Nat) : H0 n + dualV0 n <= 1 := by
    exact D.matchedCrossing_measureReal_add_le_one mu data.Bpos
      data.primalArcBound data.dualArcBound (data.spanX0 n) (data.spanY0 n)
  have hV1sum (n : Nat) : V1 n + dualH1 n <= 1 := by
    exact D.matchedVerticalHorizontalCrossing_measureReal_add_le_one
      mu data.Bpos data.primalArcBound data.dualArcBound
      (data.spanX1 n) (data.spanY1 n)
  have hdualV0 : Tendsto dualV0 atTop (nhds 1) := by
    simpa only [dualV0] using data.dualVertical0
  have hdualH1 : Tendsto dualH1 atTop (nhds 1) := by
    simpa only [dualH1] using data.dualHorizontal1
  have hH0zero : Tendsto H0 atTop (nhds 0) := by
    have hupper (n : Nat) : H0 n <= 1 - dualV0 n := by
      linarith [hH0sum n]
    exact squeeze_zero (fun _ => measureReal_nonneg) hupper <| by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdualV0
  have hV1zero : Tendsto V1 atTop (nhds 0) := by
    have hupper (n : Nat) : V1 n <= 1 - dualH1 n := by
      linarith [hV1sum n]
    exact squeeze_zero (fun _ => measureReal_nonneg) hupper <| by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdualH1
  have hmaxZero : Tendsto (fun n => max (H0 n) (V1 n))
      atTop (nhds 0) := by
    simpa using hH0zero.max hV1zero
  have hmaxOne : Tendsto (fun n => max (H0 n) (V1 n))
      atTop (nhds 1) := by
    simpa only [H0, V1] using data.primalAdjacent
  have : (0 : Real) = 1 := tendsto_nhds_unique hmaxZero hmaxOne
  norm_num at this





theorem PeriodicPlanarDualPair.variablePadComplementaryCrossNested_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (a0 b0 c0 d0 a1 b1 c1 d1 pad : Nat -> Real)
    (hpad : forall n, 4 * B <= pad n)
    (hspanX0 : forall n, a0 n + 5 * B < b0 n - 5 * B)
    (hspanY0 : forall n, c0 n + 5 * B < d0 n - 5 * B)
    (hspanX1 : forall n, a1 n + 5 * B < b1 n - 5 * B)
    (hspanY1 : forall n, c1 n + 5 * B < d1 n - 5 * B)
    (hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a0 n) (b0 n) (c0 n + pad n) (d0 n - pad n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a1 n + pad n) (b1 n - pad n) (c1 n) (d1 n))))
      atTop (nhds 1))
    (hdualVertical0 : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a0 n + pad n) (b0 n - pad n) (c0 n) (d0 n)))
      atTop (nhds 1))
    (hdualHorizontal1 : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a1 n) (b1 n) (c1 n + pad n) (d1 n - pad n)))
      atTop (nhds 1)) : False := by
  let H0 : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a0 n) (b0 n) (c0 n + pad n) (d0 n - pad n))
  let V1 : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a1 n + pad n) (b1 n - pad n) (c1 n) (d1 n))
  let dualV0 : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a0 n + pad n) (b0 n - pad n) (c0 n) (d0 n))
  let dualH1 : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a1 n) (b1 n) (c1 n + pad n) (d1 n - pad n))
  have hH0sum (n : Nat) : H0 n + dualV0 n <= 1 := by
    exact D.matchedCrossing_measureReal_add_le_one_of_pads mu hBpos
      hBp hBd (hpad n) (hpad n) (hspanX0 n) (hspanY0 n)
  have hV1sum (n : Nat) : V1 n + dualH1 n <= 1 := by
    exact D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads
      mu hBpos hBp hBd (hpad n) (hpad n)
        (hspanX1 n) (hspanY1 n)
  have hH0zero : Tendsto H0 atTop (nhds 0) := by
    have hupper (n : Nat) : H0 n <= 1 - dualV0 n := by
      linarith [hH0sum n]
    exact squeeze_zero (fun _ => measureReal_nonneg) hupper <| by
      simpa [dualV0] using
        (tendsto_const_nhds (x := (1 : Real))).sub hdualVertical0
  have hV1zero : Tendsto V1 atTop (nhds 0) := by
    have hupper (n : Nat) : V1 n <= 1 - dualH1 n := by
      linarith [hV1sum n]
    exact squeeze_zero (fun _ => measureReal_nonneg) hupper <| by
      simpa [dualH1] using
        (tendsto_const_nhds (x := (1 : Real))).sub hdualHorizontal1
  have hmaxZero : Tendsto (fun n => max (H0 n) (V1 n))
      atTop (nhds 0) := by
    simpa using hH0zero.max hV1zero
  have hmaxOne : Tendsto (fun n => max (H0 n) (V1 n))
      atTop (nhds 1) := by
    simpa only [H0, V1] using hprimal
  have : (0 : Real) = 1 := tendsto_nhds_unique hmaxZero hmaxOne
  norm_num at this






theorem PeriodicPlanarDualPair.variablePadComplementaryEndpoints_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (vLeft vRight vBottom vTop : Nat -> Real)
    (hLeft hRight hBottom hTop pad : Nat -> Real)
    (hpad : forall n, 4 * B <= pad n)
    (hspanVX : forall n, vLeft n - pad n + 5 * B <
      vRight n + pad n - 5 * B)
    (hspanVY : forall n, vBottom n + 5 * B < vTop n - 5 * B)
    (hspanHX : forall n, hLeft n + 5 * B < hRight n - 5 * B)
    (hspanHY : forall n, hBottom n - pad n + 5 * B <
      hTop n + pad n - 5 * B)
    (hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (vLeft n - pad n) (vRight n + pad n)
        (vBottom n + pad n) (vTop n - pad n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (hLeft n + pad n) (hRight n - pad n)
        (hBottom n - pad n) (hTop n + pad n))))
      atTop (nhds 1))
    (hdualVertical : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (vLeft n) (vRight n) (vBottom n) (vTop n)))
      atTop (nhds 1))
    (hdualHorizontal : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (hLeft n) (hRight n) (hBottom n) (hTop n)))
      atTop (nhds 1)) : False := by
  apply D.variablePadComplementaryCrossNested_false mu B hBpos hBp hBd
    (fun n => vLeft n - pad n) (fun n => vRight n + pad n)
    vBottom vTop hLeft hRight
    (fun n => hBottom n - pad n) (fun n => hTop n + pad n) pad
    hpad hspanVX hspanVY hspanHX hspanHY
  · simpa only [sub_add_cancel, add_sub_cancel_right] using hprimal
  · simpa only [sub_add_cancel, add_sub_cancel_right] using hdualVertical
  · simpa only [sub_add_cancel, add_sub_cancel_right] using hdualHorizontal




theorem PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_eventSubsets
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (a b c d : Real)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B)
    (primalEvent : Set (ConfigSpace (Sym2 V)))
    (dualEvent : Set (ConfigSpace (Sym2 W)))
    (hprimal : primalEvent <=
      D.primalEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B))
    (hdual : dualEvent <=
      D.dualEmbedding.verticalCrossingEvent
        (a + 4 * B) (b - 4 * B) c d) :
    mu.real primalEvent +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' dualEvent) <= 1 := by
  have hbase := D.matchedCrossing_measureReal_add_le_one
    mu hBpos hBp hBd hab hcd
  have hp := measureReal_mono (h₂ := measure_ne_top mu _) hprimal
  have hdualPre :
      (dualConfigEquiv D.edgeDual) ⁻¹' dualEvent <=
        (dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a + 4 * B) (b - 4 * B) c d :=
    Set.preimage_mono hdual
  have hd := measureReal_mono (h₂ := measure_ne_top mu _)
    hdualPre
  linarith


theorem PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_eventSubsets
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (a b c d : Real)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B)
    (primalEvent : Set (ConfigSpace (Sym2 V)))
    (dualEvent : Set (ConfigSpace (Sym2 W)))
    (hprimal : primalEvent <=
      D.primalEmbedding.verticalCrossingEvent
        (a + 4 * B) (b - 4 * B) c d)
    (hdual : dualEvent <=
      D.dualEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B)) :
    mu.real primalEvent +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' dualEvent) <= 1 := by
  have hbase := D.matchedVerticalHorizontalCrossing_measureReal_add_le_one
    mu hBpos hBp hBd hab hcd
  have hp := measureReal_mono (h₂ := measure_ne_top mu _) hprimal
  have hdualPre :
      (dualConfigEquiv D.edgeDual) ⁻¹' dualEvent <=
        (dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            a b (c + 4 * B) (d - 4 * B) :=
    Set.preimage_mono hdual
  have hd := measureReal_mono (h₂ := measure_ne_top mu _)
    hdualPre
  linarith




theorem PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_innerVerticalStrip
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (a b c d vLeft vRight : Real)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B)
    (hleft : a + 4 * B <= vLeft)
    (hright : vRight <= b - 4 * B) :
    mu.real (D.primalEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B)) +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          vLeft vRight c d) <= 1 := by
  apply D.matchedCrossing_measureReal_add_le_one_of_eventSubsets
    mu B hBpos hBp hBd a b c d hab hcd
      (D.primalEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B))
      (D.dualEmbedding.verticalCrossingEvent vLeft vRight c d)
      (Set.Subset.rfl)
  exact D.dualEmbedding.verticalCrossingEvent_mono_horizontal
    hleft hright




theorem PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_innerHorizontalStrip
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (a b c d hBottom hTop : Real)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B)
    (hbottom : c + 4 * B <= hBottom)
    (htop : hTop <= d - 4 * B) :
    mu.real (D.primalEmbedding.verticalCrossingEvent
        (a + 4 * B) (b - 4 * B) c d) +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          a b hBottom hTop) <= 1 := by
  apply D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_eventSubsets
    mu B hBpos hBp hBd a b c d hab hcd
      (D.primalEmbedding.verticalCrossingEvent
        (a + 4 * B) (b - 4 * B) c d)
      (D.dualEmbedding.horizontalCrossingEvent a b hBottom hTop)
      (Set.Subset.rfl)
  exact D.dualEmbedding.horizontalCrossingEvent_mono_vertical
    hbottom htop




theorem PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_innerStrips
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (a b c d primalBottom primalTop dualLeft dualRight : Real)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B)
    (hprimalBottom : c + 4 * B <= primalBottom)
    (hprimalTop : primalTop <= d - 4 * B)
    (hdualLeft : a + 4 * B <= dualLeft)
    (hdualRight : dualRight <= b - 4 * B) :
    mu.real (D.primalEmbedding.horizontalCrossingEvent
        a b primalBottom primalTop) +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          dualLeft dualRight c d) <= 1 := by
  apply D.matchedCrossing_measureReal_add_le_one_of_eventSubsets
    mu B hBpos hBp hBd a b c d hab hcd
      (D.primalEmbedding.horizontalCrossingEvent
        a b primalBottom primalTop)
      (D.dualEmbedding.verticalCrossingEvent dualLeft dualRight c d)
  · exact D.primalEmbedding.horizontalCrossingEvent_mono_vertical
      hprimalBottom hprimalTop
  · exact D.dualEmbedding.verticalCrossingEvent_mono_horizontal
      hdualLeft hdualRight


theorem PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_innerStrips
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (a b c d primalLeft primalRight dualBottom dualTop : Real)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B)
    (hprimalLeft : a + 4 * B <= primalLeft)
    (hprimalRight : primalRight <= b - 4 * B)
    (hdualBottom : c + 4 * B <= dualBottom)
    (hdualTop : dualTop <= d - 4 * B) :
    mu.real (D.primalEmbedding.verticalCrossingEvent
        primalLeft primalRight c d) +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          a b dualBottom dualTop) <= 1 := by
  apply D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_eventSubsets
    mu B hBpos hBp hBd a b c d hab hcd
      (D.primalEmbedding.verticalCrossingEvent
        primalLeft primalRight c d)
      (D.dualEmbedding.horizontalCrossingEvent a b dualBottom dualTop)
  · exact D.primalEmbedding.verticalCrossingEvent_mono_horizontal
      hprimalLeft hprimalRight
  · exact D.dualEmbedding.horizontalCrossingEvent_mono_vertical
      hdualBottom hdualTop




theorem PeriodicPlanarDualPair.horizontalDualVerticalEndpoint_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy u - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy u - D.dualEmbedding.vertex x) i| <= B)
    (hLeft hRight hBottom hTop : Nat -> Real)
    (dualLeft dualRight dualBottom dualTop : Nat -> Real)
    (hspanHX : forall n, hLeft n + 5 * B < hRight n - 5 * B)
    (hspanDVY : forall n, dualBottom n + 5 * B < dualTop n - 5 * B)
    (hBottomFit : forall n, dualBottom n + 4 * B <= hBottom n)
    (hTopFit : forall n, hTop n <= dualTop n - 4 * B)
    (hLeftFit : forall n, hLeft n + 4 * B <= dualLeft n)
    (hRightFit : forall n, dualRight n <= hRight n - 4 * B)
    (hprimal : Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (hLeft n) (hRight n) (hBottom n) (hTop n))) atTop (nhds 1))
    (hdual : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (dualLeft n) (dualRight n) (dualBottom n) (dualTop n)))
      atTop (nhds 1)) : False := by
  let H : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (hLeft n) (hRight n) (hBottom n) (hTop n))
  let dualV : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (dualLeft n) (dualRight n) (dualBottom n) (dualTop n))
  have hsum (n : Nat) : H n + dualV n <= 1 :=
    D.matchedCrossing_measureReal_add_le_one_of_innerStrips
      mu B hBpos hBp hBd (hLeft n) (hRight n)
        (dualBottom n) (dualTop n) (hBottom n) (hTop n)
        (dualLeft n) (dualRight n) (hspanHX n) (hspanDVY n)
        (hBottomFit n) (hTopFit n) (hLeftFit n) (hRightFit n)
  have hdual' : Tendsto dualV atTop (nhds 1) := by
    simpa only [dualV] using hdual
  have hzero : Tendsto H atTop (nhds 0) := by
    have hupper : Tendsto (fun n => 1 - dualV n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdual'
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => by linarith [hsum n]) hupper
  have hone : Tendsto H atTop (nhds 1) := by
    simpa only [H] using hprimal
  have : (0 : Real) = 1 := tendsto_nhds_unique hzero hone
  norm_num at this



theorem PeriodicPlanarDualPair.verticalDualHorizontalEndpoint_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy u - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy u - D.dualEmbedding.vertex x) i| <= B)
    (vLeft vRight vBottom vTop : Nat -> Real)
    (dualLeft dualRight dualBottom dualTop : Nat -> Real)
    (hspanDHX : forall n, dualLeft n + 5 * B < dualRight n - 5 * B)
    (hspanVY : forall n, vBottom n + 5 * B < vTop n - 5 * B)
    (hLeftFit : forall n, dualLeft n + 4 * B <= vLeft n)
    (hRightFit : forall n, vRight n <= dualRight n - 4 * B)
    (hBottomFit : forall n, vBottom n + 4 * B <= dualBottom n)
    (hTopFit : forall n, dualTop n <= vTop n - 4 * B)
    (hprimal : Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (vLeft n) (vRight n) (vBottom n) (vTop n))) atTop (nhds 1))
    (hdual : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (dualLeft n) (dualRight n) (dualBottom n) (dualTop n)))
      atTop (nhds 1)) : False := by
  let Vcross : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (vLeft n) (vRight n) (vBottom n) (vTop n))
  let dualH : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (dualLeft n) (dualRight n) (dualBottom n) (dualTop n))
  have hsum (n : Nat) : Vcross n + dualH n <= 1 :=
    D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_innerStrips
      mu B hBpos hBp hBd (dualLeft n) (dualRight n)
        (vBottom n) (vTop n) (vLeft n) (vRight n)
        (dualBottom n) (dualTop n) (hspanDHX n) (hspanVY n)
        (hLeftFit n) (hRightFit n) (hBottomFit n) (hTopFit n)
  have hdual' : Tendsto dualH atTop (nhds 1) := by
    simpa only [dualH] using hdual
  have hzero : Tendsto Vcross atTop (nhds 0) := by
    have hupper : Tendsto (fun n => 1 - dualH n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdual'
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => by linarith [hsum n]) hupper
  have hone : Tendsto Vcross atTop (nhds 1) := by
    simpa only [Vcross] using hprimal
  have : (0 : Real) = 1 := tendsto_nhds_unique hzero hone
  norm_num at this




theorem PeriodicPlanarDualPair.asymmetricEndpointCoordinates_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Real)
    (vLeft vRight hBottom hTop : Nat -> Real)
    (hspanX0 : forall n, a0 n + 5 * B < b0 n - 5 * B)
    (hspanY0 : forall n, c0 n + 5 * B < d0 n - 5 * B)
    (hspanX1 : forall n, a1 n + 5 * B < b1 n - 5 * B)
    (hspanY1 : forall n, c1 n + 5 * B < d1 n - 5 * B)
    (hvLeft : forall n, a0 n + 4 * B <= vLeft n)
    (hvRight : forall n, vRight n <= b0 n - 4 * B)
    (hhBottom : forall n, c1 n + 4 * B <= hBottom n)
    (hhTop : forall n, hTop n <= d1 n - 4 * B)
    (hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a0 n) (b0 n) (c0 n + 4 * B) (d0 n - 4 * B)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a1 n + 4 * B) (b1 n - 4 * B) (c1 n) (d1 n))))
      atTop (nhds 1))
    (hdualV : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (vLeft n) (vRight n) (c0 n) (d0 n))) atTop (nhds 1))
    (hdualH : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a1 n) (b1 n) (hBottom n) (hTop n))) atTop (nhds 1)) : False := by
  let H : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a0 n) (b0 n) (c0 n + 4 * B) (d0 n - 4 * B))
  let V : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a1 n + 4 * B) (b1 n - 4 * B) (c1 n) (d1 n))
  let dualV : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (vLeft n) (vRight n) (c0 n) (d0 n))
  let dualH : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a1 n) (b1 n) (hBottom n) (hTop n))
  have hHdual (n : Nat) : H n + dualV n <= 1 := by
    exact D.matchedCrossing_measureReal_add_le_one_of_innerVerticalStrip
      mu B hBpos hBp hBd (a0 n) (b0 n) (c0 n) (d0 n)
        (vLeft n) (vRight n) (hspanX0 n) (hspanY0 n)
        (hvLeft n) (hvRight n)
  have hVdual (n : Nat) : V n + dualH n <= 1 := by
    exact D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_innerHorizontalStrip
      mu B hBpos hBp hBd (a1 n) (b1 n) (c1 n) (d1 n)
        (hBottom n) (hTop n) (hspanX1 n) (hspanY1 n)
        (hhBottom n) (hhTop n)
  have hdualV' : Tendsto dualV atTop (nhds 1) := by
    simpa only [dualV] using hdualV
  have hdualH' : Tendsto dualH atTop (nhds 1) := by
    simpa only [dualH] using hdualH
  have hHzero : Tendsto H atTop (nhds 0) := by
    have hupper : Tendsto (fun n => 1 - dualV n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdualV'
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => by linarith [hHdual n]) hupper
  have hVzero : Tendsto V atTop (nhds 0) := by
    have hupper : Tendsto (fun n => 1 - dualH n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdualH'
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => by linarith [hVdual n]) hupper
  have hzero : Tendsto (fun n => max (H n) (V n))
      atTop (nhds 0) := by
    simpa using hHzero.max hVzero
  have hone : Tendsto (fun n => max (H n) (V n))
      atTop (nhds 1) := by
    simpa only [H, V] using hprimal
  have : (0 : Real) = 1 := tendsto_nhds_unique hzero hone
  norm_num at this





theorem PeriodicPlanarDualPair.fullyAsymmetricEndpointCoordinates_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (hLeft hRight hBottom hTop : Nat -> Real)
    (vLeft vRight vBottom vTop : Nat -> Real)
    (dualVLeft dualVRight dualVBottom dualVTop : Nat -> Real)
    (dualHLeft dualHRight dualHBottom dualHTop : Nat -> Real)
    (hspanHX : forall n, hLeft n + 5 * B < hRight n - 5 * B)
    (hspanDVY : forall n,
      dualVBottom n + 5 * B < dualVTop n - 5 * B)
    (hspanDHX : forall n,
      dualHLeft n + 5 * B < dualHRight n - 5 * B)
    (hspanVY : forall n, vBottom n + 5 * B < vTop n - 5 * B)
    (hHBottom : forall n, dualVBottom n + 4 * B <= hBottom n)
    (hHTop : forall n, hTop n <= dualVTop n - 4 * B)
    (hDVLeft : forall n, hLeft n + 4 * B <= dualVLeft n)
    (hDVRight : forall n, dualVRight n <= hRight n - 4 * B)
    (hVLeft : forall n, dualHLeft n + 4 * B <= vLeft n)
    (hVRight : forall n, vRight n <= dualHRight n - 4 * B)
    (hDHBottom : forall n, vBottom n + 4 * B <= dualHBottom n)
    (hDHTop : forall n, dualHTop n <= vTop n - 4 * B)
    (hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (hLeft n) (hRight n) (hBottom n) (hTop n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (vLeft n) (vRight n) (vBottom n) (vTop n))))
      atTop (nhds 1))
    (hdualV : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (dualVLeft n) (dualVRight n)
          (dualVBottom n) (dualVTop n))) atTop (nhds 1))
    (hdualH : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (dualHLeft n) (dualHRight n)
          (dualHBottom n) (dualHTop n))) atTop (nhds 1)) : False := by
  let H : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (hLeft n) (hRight n) (hBottom n) (hTop n))
  let V : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (vLeft n) (vRight n) (vBottom n) (vTop n))
  let dualV : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (dualVLeft n) (dualVRight n) (dualVBottom n) (dualVTop n))
  let dualH : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (dualHLeft n) (dualHRight n) (dualHBottom n) (dualHTop n))
  have hHdual (n : Nat) : H n + dualV n <= 1 := by
    exact D.matchedCrossing_measureReal_add_le_one_of_innerStrips
      mu B hBpos hBp hBd (hLeft n) (hRight n)
      (dualVBottom n) (dualVTop n) (hBottom n) (hTop n)
      (dualVLeft n) (dualVRight n) (hspanHX n) (hspanDVY n)
      (hHBottom n) (hHTop n) (hDVLeft n) (hDVRight n)
  have hVdual (n : Nat) : V n + dualH n <= 1 := by
    exact D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_innerStrips
      mu B hBpos hBp hBd (dualHLeft n) (dualHRight n)
      (vBottom n) (vTop n) (vLeft n) (vRight n)
      (dualHBottom n) (dualHTop n) (hspanDHX n) (hspanVY n)
      (hVLeft n) (hVRight n) (hDHBottom n) (hDHTop n)
  have hHzero : Tendsto H atTop (nhds 0) := by
    have hdualV' : Tendsto dualV atTop (nhds 1) := by
      simpa only [dualV] using hdualV
    have hupper : Tendsto (fun n => 1 - dualV n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdualV'
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => by linarith [hHdual n]) hupper
  have hVzero : Tendsto V atTop (nhds 0) := by
    have hdualH' : Tendsto dualH atTop (nhds 1) := by
      simpa only [dualH] using hdualH
    have hupper : Tendsto (fun n => 1 - dualH n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdualH'
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => by linarith [hVdual n]) hupper
  have hzero : Tendsto (fun n => max (H n) (V n)) atTop (nhds 0) := by
    simpa using hHzero.max hVzero
  have hone : Tendsto (fun n => max (H n) (V n)) atTop (nhds 1) := by
    simpa only [H, V] using hprimal
  have : (0 : Real) = 1 := tendsto_nhds_unique hzero hone
  norm_num at this





def PeriodicPlaneEmbedding.CarriedCrossNestedArray.reframe
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (data : E.CarriedCrossNestedArray mu)
    (aWide bWide cTall dTall : Nat -> Real)
    (hwideLeft : forall n, aWide n <= data.a n)
    (hwideRight : forall n, data.b n <= bWide n)
    (htallBottom : forall n, cTall n <= data.c n)
    (htallTop : forall n, data.d n <= dTall n)
    (hverticalConnector : forall n,
      (P.orbitBox (P.bufferedRadius (data.verticalRadius n)) : Set V) <=
        E.rectVertices (aWide n) (bWide n) (data.c n) (data.d n))
    (hhorizontalConnector : forall n,
      (P.orbitBox (P.bufferedRadius (data.horizontalRadius n)) : Set V) <=
        E.rectVertices (data.a n) (data.b n) (cTall n) (dTall n)) :
    E.CarriedCrossNestedArray mu where
  a := data.a
  b := data.b
  c := data.c
  d := data.d
  aWide := aWide
  bWide := bWide
  cTall := cTall
  dTall := dTall
  bottom := data.bottom
  top := data.top
  left := data.left
  right := data.right
  verticalRadius := data.verticalRadius
  horizontalRadius := data.horizontalRadius
  wideLeft := hwideLeft
  wideRight := hwideRight
  tallBottom := htallBottom
  tallTop := htallTop
  verticalConnector := hverticalConnector
  horizontalConnector := hhorizontalConnector
  bottomLimit := data.bottomLimit
  topLimit := data.topLimit
  leftLimit := data.leftLimit
  rightLimit := data.rightLimit
  verticalMergeLimit := data.verticalMergeLimit
  horizontalMergeLimit := data.horizontalMergeLimit





noncomputable def PeriodicPlaneEmbedding.CarriedCrossNestedArray.reframeByCoordinateBounds
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (data : E.CarriedCrossNestedArray mu) :
    E.CarriedCrossNestedArray mu := by
  let xBound : Nat -> Real := fun n =>
    E.orbitBoxCoordinateBound
      (P.bufferedRadius (data.verticalRadius n)) 0
  let yBound : Nat -> Real := fun n =>
    E.orbitBoxCoordinateBound
      (P.bufferedRadius (data.horizontalRadius n)) 1
  apply data.reframe E mu
    (fun n => min (data.a n) (-xBound n))
    (fun n => max (data.b n) (xBound n))
    (fun n => min (data.c n) (-yBound n))
    (fun n => max (data.d n) (yBound n))
  · intro n
    exact min_le_left _ _
  · intro n
    exact le_max_left _ _
  · intro n
    exact min_le_left _ _
  · intro n
    exact le_max_left _ _
  · intro n v hv
    have hold := data.verticalConnector n hv
    have hx := E.abs_vertexCoord_le_orbitBoxCoordinateBound hv (0 : Fin 2)
    rw [abs_le] at hx
    exact ⟨(min_le_right (data.a n) (-xBound n)).trans hx.1,
      hx.2.trans (le_max_right (data.b n) (xBound n)),
      hold.2.2.1, hold.2.2.2⟩
  · intro n v hv
    have hold := data.horizontalConnector n hv
    have hy := E.abs_vertexCoord_le_orbitBoxCoordinateBound hv (1 : Fin 2)
    rw [abs_le] at hy
    exact ⟨hold.1, hold.2.1,
      (min_le_right (data.c n) (-yBound n)).trans hy.1,
      hy.2.trans (le_max_right (data.d n) (yBound n))⟩





theorem PeriodicPlanarDualPair.finiteStripArmArrays_dualCrossingLimits_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy u -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy u -
          D.dualEmbedding.vertex x) i| <= B)
    (hR hC hD : Nat -> Real) (hHeight : Nat -> Nat)
    (hLower hUpper : Nat -> Finset V)
    (vR vC vD : Nat -> Real) (vWidth : Nat -> Nat)
    (vLower vUpper : Nat -> Finset V)
    (dualVLeft dualVRight dualVBottom dualVTop : Nat -> Real)
    (dualHLeft dualHRight dualHBottom dualHTop : Nat -> Real)
    (hgapH : forall n, 3 * B < hD n - hC n)
    (hgapV : forall n, 3 * B < vD n - vC n)
    (hHorizontalArms : Tendsto (fun n => mu.real
      (D.primalEmbedding.axisSwap.finiteStripJoinedBoundaryArmEvent
        (hR n) (hC n) (hD n) (hHeight n) (hLower n) (hUpper n)))
      atTop (nhds 1))
    (hVerticalArms : Tendsto (fun n => mu.real
      (D.primalEmbedding.finiteStripJoinedBoundaryArmEvent
        (vR n) (vC n) (vD n) (vWidth n) (vLower n) (vUpper n)))
      atTop (nhds 1))
    (hspanHX : forall n,
      (2 * hC n + hD n) / 3 + 5 * B <
        (hC n + 2 * hD n) / 3 - 5 * B)
    (hspanDVY : forall n,
      dualVBottom n + 5 * B < dualVTop n - 5 * B)
    (hspanDHX : forall n,
      dualHLeft n + 5 * B < dualHRight n - 5 * B)
    (hspanVY : forall n,
      (2 * vC n + vD n) / 3 + 5 * B <
        (vC n + 2 * vD n) / 3 - 5 * B)
    (hHBottom : forall n, dualVBottom n + 4 * B <= hR n)
    (hHTop : forall n, hR n + hHeight n <= dualVTop n - 4 * B)
    (hDVLeft : forall n,
      (2 * hC n + hD n) / 3 + 4 * B <= dualVLeft n)
    (hDVRight : forall n,
      dualVRight n <= (hC n + 2 * hD n) / 3 - 4 * B)
    (hVLeft : forall n, dualHLeft n + 4 * B <= vR n)
    (hVRight : forall n, vR n + vWidth n <= dualHRight n - 4 * B)
    (hDHBottom : forall n,
      (2 * vC n + vD n) / 3 + 4 * B <= dualHBottom n)
    (hDHTop : forall n,
      dualHTop n <= (vC n + 2 * vD n) / 3 - 4 * B)
    (hdualV : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (dualVLeft n) (dualVRight n)
          (dualVBottom n) (dualVTop n))) atTop (nhds 1))
    (hdualH : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (dualHLeft n) (dualHRight n)
          (dualHBottom n) (dualHTop n))) atTop (nhds 1)) : False := by
  have hHorizontal :=
    D.primalEmbedding.horizontalCrossing_tendsto_one_of_axisSwap_finiteStripJoinedBoundaryArms
      mu B hBp hBpos.le hR hC hD hHeight hLower hUpper hgapH
        hHorizontalArms
  have hVertical :=
    D.primalEmbedding.verticalCrossing_tendsto_one_of_finiteStripJoinedBoundaryArms
      mu B hBp hBpos.le vR vC vD vWidth vLower vUpper hgapV
        hVerticalArms
  have hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        ((2 * hC n + hD n) / 3) ((hC n + 2 * hD n) / 3)
        (hR n) (hR n + hHeight n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (vR n) (vR n + vWidth n)
        ((2 * vC n + vD n) / 3) ((vC n + 2 * vD n) / 3))))
      atTop (nhds 1) := by
    simpa only [max_self] using hHorizontal.max hVertical
  exact D.fullyAsymmetricEndpointCoordinates_false mu B hBpos hBp hBd
    (fun n => (2 * hC n + hD n) / 3)
    (fun n => (hC n + 2 * hD n) / 3) hR
    (fun n => hR n + hHeight n) vR (fun n => vR n + vWidth n)
    (fun n => (2 * vC n + vD n) / 3)
    (fun n => (vC n + 2 * vD n) / 3)
    dualVLeft dualVRight dualVBottom dualVTop
    dualHLeft dualHRight dualHBottom dualHTop
    hspanHX hspanDVY hspanDHX hspanVY hHBottom hHTop
    hDVLeft hDVRight hVLeft hVRight hDHBottom hDHTop
    hprimal hdualV hdualH






theorem PeriodicPlanarDualPair.finiteStripArmArrays_carriedDual_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKGDual : IsFKG (D.dualMeasure mu))
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy u -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy u -
          D.dualEmbedding.vertex x) i| <= B)
    (hR hC hD : Nat -> Real) (hHeight : Nat -> Nat)
    (hLower hUpper : Nat -> Finset V)
    (vR vC vD : Nat -> Real) (vWidth : Nat -> Nat)
    (vLower vUpper : Nat -> Finset V)
    (hgapH : forall n, 3 * B < hD n - hC n)
    (hgapV : forall n, 3 * B < vD n - vC n)
    (hHorizontalArms : Tendsto (fun n => mu.real
      (D.primalEmbedding.axisSwap.finiteStripJoinedBoundaryArmEvent
        (hR n) (hC n) (hD n) (hHeight n) (hLower n) (hUpper n)))
      atTop (nhds 1))
    (hVerticalArms : Tendsto (fun n => mu.real
      (D.primalEmbedding.finiteStripJoinedBoundaryArmEvent
        (vR n) (vC n) (vD n) (vWidth n) (vLower n) (vUpper n)))
      atTop (nhds 1))
    (dual : D.dualEmbedding.CarriedCrossNestedArray (D.dualMeasure mu))
    (hspanHX : forall n,
      (2 * hC n + hD n) / 3 + 5 * B <
        (hC n + 2 * hD n) / 3 - 5 * B)
    (hspanDVY : forall n, dual.c n + 5 * B < dual.d n - 5 * B)
    (hspanDHX : forall n, dual.a n + 5 * B < dual.b n - 5 * B)
    (hspanVY : forall n,
      (2 * vC n + vD n) / 3 + 5 * B <
        (vC n + 2 * vD n) / 3 - 5 * B)
    (hHBottom : forall n, dual.c n + 4 * B <= hR n)
    (hHTop : forall n, hR n + hHeight n <= dual.d n - 4 * B)
    (hDVLeft : forall n,
      (2 * hC n + hD n) / 3 + 4 * B <= dual.aWide n)
    (hDVRight : forall n,
      dual.bWide n <= (hC n + 2 * hD n) / 3 - 4 * B)
    (hVLeft : forall n, dual.a n + 4 * B <= vR n)
    (hVRight : forall n, vR n + vWidth n <= dual.b n - 4 * B)
    (hDHBottom : forall n,
      (2 * vC n + vD n) / 3 + 4 * B <= dual.cTall n)
    (hDHTop : forall n,
      dual.dTall n <= (vC n + 2 * vD n) / 3 - 4 * B) : False := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  have hHorizontal :=
    D.primalEmbedding.horizontalCrossing_tendsto_one_of_axisSwap_finiteStripJoinedBoundaryArms
      mu B hBp hBpos.le hR hC hD hHeight hLower hUpper hgapH
        hHorizontalArms
  have hVertical :=
    D.primalEmbedding.verticalCrossing_tendsto_one_of_finiteStripJoinedBoundaryArms
      mu B hBp hBpos.le vR vC vD vWidth vLower vUpper hgapV
        hVerticalArms
  have hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        ((2 * hC n + hD n) / 3) ((hC n + 2 * hD n) / 3)
        (hR n) (hR n + hHeight n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (vR n) (vR n + vWidth n)
        ((2 * vC n + vD n) / 3) ((vC n + 2 * vD n) / 3))))
      atTop (nhds 1) := by
    simpa only [max_self] using hHorizontal.max hVertical
  have hdualV0 := dual.verticalCrossingLimit
    D.dualEmbedding (D.dualMeasure mu) hFKGDual
  have hdualH0 := dual.horizontalCrossingLimit
    D.dualEmbedding (D.dualMeasure mu) hFKGDual
  have hdualV : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (dual.aWide n) (dual.bWide n) (dual.c n) (dual.d n)))
      atTop (nhds 1) := by
    apply hdualV0.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)]
  have hdualH : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (dual.a n) (dual.b n) (dual.cTall n) (dual.dTall n)))
      atTop (nhds 1) := by
    apply hdualH0.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]
  exact D.fullyAsymmetricEndpointCoordinates_false mu B hBpos hBp hBd
    (fun n => (2 * hC n + hD n) / 3)
    (fun n => (hC n + 2 * hD n) / 3) hR
    (fun n => hR n + hHeight n) vR (fun n => vR n + vWidth n)
    (fun n => (2 * vC n + vD n) / 3)
    (fun n => (vC n + 2 * vD n) / 3)
    dual.aWide dual.bWide dual.c dual.d
    dual.a dual.b dual.cTall dual.dTall
    hspanHX hspanDVY hspanDHX hspanVY hHBottom hHTop
    hDVLeft hDVRight hVLeft hVRight hDHBottom hDHTop
    hprimal hdualV hdualH






theorem PeriodicPlanarDualPair.finiteStripArmArrays_reframedCarriedDual_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKGDual : IsFKG (D.dualMeasure mu))
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy u -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy u -
          D.dualEmbedding.vertex x) i| <= B)
    (hR hC hD : Nat -> Real) (hHeight : Nat -> Nat)
    (hLower hUpper : Nat -> Finset V)
    (vR vC vD : Nat -> Real) (vWidth : Nat -> Nat)
    (vLower vUpper : Nat -> Finset V)
    (hgapH : forall n, 3 * B < hD n - hC n)
    (hgapV : forall n, 3 * B < vD n - vC n)
    (hHorizontalArms : Tendsto (fun n => mu.real
      (D.primalEmbedding.axisSwap.finiteStripJoinedBoundaryArmEvent
        (hR n) (hC n) (hD n) (hHeight n) (hLower n) (hUpper n)))
      atTop (nhds 1))
    (hVerticalArms : Tendsto (fun n => mu.real
      (D.primalEmbedding.finiteStripJoinedBoundaryArmEvent
        (vR n) (vC n) (vD n) (vWidth n) (vLower n) (vUpper n)))
      atTop (nhds 1))
    (dual : D.dualEmbedding.CarriedCrossNestedArray (D.dualMeasure mu))
    (hspanHX : forall n,
      (2 * hC n + hD n) / 3 + 5 * B <
        (hC n + 2 * hD n) / 3 - 5 * B)
    (hspanDVY : forall n, dual.c n + 5 * B < dual.d n - 5 * B)
    (hspanDHX : forall n, dual.a n + 5 * B < dual.b n - 5 * B)
    (hspanVY : forall n,
      (2 * vC n + vD n) / 3 + 5 * B <
        (vC n + 2 * vD n) / 3 - 5 * B)
    (hHBottom : forall n, dual.c n + 4 * B <= hR n)
    (hHTop : forall n, hR n + hHeight n <= dual.d n - 4 * B)
    (hWideLeft : forall n,
      (2 * hC n + hD n) / 3 + 4 * B <=
        min (dual.a n) (-D.dualEmbedding.orbitBoxCoordinateBound
          (Pdual.bufferedRadius (dual.verticalRadius n)) 0))
    (hWideRight : forall n,
      max (dual.b n) (D.dualEmbedding.orbitBoxCoordinateBound
        (Pdual.bufferedRadius (dual.verticalRadius n)) 0) <=
          (hC n + 2 * hD n) / 3 - 4 * B)
    (hVLeft : forall n, dual.a n + 4 * B <= vR n)
    (hVRight : forall n, vR n + vWidth n <= dual.b n - 4 * B)
    (hTallBottom : forall n,
      (2 * vC n + vD n) / 3 + 4 * B <=
        min (dual.c n) (-D.dualEmbedding.orbitBoxCoordinateBound
          (Pdual.bufferedRadius (dual.horizontalRadius n)) 1))
    (hTallTop : forall n,
      max (dual.d n) (D.dualEmbedding.orbitBoxCoordinateBound
        (Pdual.bufferedRadius (dual.horizontalRadius n)) 1) <=
          (vC n + 2 * vD n) / 3 - 4 * B) : False := by
  let reframed := dual.reframeByCoordinateBounds
    D.dualEmbedding (D.dualMeasure mu)
  apply D.finiteStripArmArrays_carriedDual_false mu hFKGDual B hBpos
    hBp hBd hR hC hD hHeight hLower hUpper vR vC vD vWidth
    vLower vUpper hgapH hgapV hHorizontalArms hVerticalArms reframed
  · exact hspanHX
  · exact hspanDVY
  · exact hspanDHX
  · exact hspanVY
  · exact hHBottom
  · exact hHTop
  · exact hWideLeft
  · exact hWideRight
  · exact hVLeft
  · exact hVRight
  · exact hTallBottom
  · exact hTallTop






theorem PeriodicPlanarDualPair.carriedCrossNestedArrays_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hFKGDual : IsFKG (D.dualMeasure mu))
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (primal : D.primalEmbedding.CarriedCrossNestedArray mu)
    (dual : D.dualEmbedding.CarriedCrossNestedArray (D.dualMeasure mu))
    (hspanHX : forall n,
      primal.a n + 5 * B < primal.b n - 5 * B)
    (hspanDVY : forall n,
      dual.c n + 5 * B < dual.d n - 5 * B)
    (hspanDHX : forall n,
      dual.a n + 5 * B < dual.b n - 5 * B)
    (hspanVY : forall n,
      primal.c n + 5 * B < primal.d n - 5 * B)
    (hHBottom : forall n, dual.c n + 4 * B <= primal.cTall n)
    (hHTop : forall n, primal.dTall n <= dual.d n - 4 * B)
    (hDVLeft : forall n, primal.a n + 4 * B <= dual.aWide n)
    (hDVRight : forall n, dual.bWide n <= primal.b n - 4 * B)
    (hVLeft : forall n, dual.a n + 4 * B <= primal.aWide n)
    (hVRight : forall n, primal.bWide n <= dual.b n - 4 * B)
    (hDHBottom : forall n, primal.c n + 4 * B <= dual.cTall n)
    (hDHTop : forall n, dual.dTall n <= primal.d n - 4 * B) : False := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  have hprimal := primal.crossingMaxLimit D.primalEmbedding mu hFKG
  have hdualV0 := dual.verticalCrossingLimit
    D.dualEmbedding (D.dualMeasure mu) hFKGDual
  have hdualH0 := dual.horizontalCrossingLimit
    D.dualEmbedding (D.dualMeasure mu) hFKGDual
  have hdualV : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (dual.aWide n) (dual.bWide n) (dual.c n) (dual.d n)))
      atTop (nhds 1) := by
    apply hdualV0.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)]
  have hdualH : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (dual.a n) (dual.b n) (dual.cTall n) (dual.dTall n)))
      atTop (nhds 1) := by
    apply hdualH0.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]
  exact D.fullyAsymmetricEndpointCoordinates_false mu B hBpos hBp hBd
    primal.a primal.b primal.cTall primal.dTall
    primal.aWide primal.bWide primal.c primal.d
    dual.aWide dual.bWide dual.c dual.d
    dual.a dual.b dual.cTall dual.dTall
    hspanHX hspanDVY hspanDHX hspanVY
    hHBottom hHTop hDVLeft hDVRight hVLeft hVRight hDHBottom hDHTop
    hprimal hdualV hdualH



def PeriodicPlaneEmbedding.CarriedCrossNestedArray.tail
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (data : E.CarriedCrossNestedArray mu) :
    E.CarriedCrossNestedArray mu where
  a n := data.a (n + 1)
  b n := data.b (n + 1)
  c n := data.c (n + 1)
  d n := data.d (n + 1)
  aWide n := data.aWide (n + 1)
  bWide n := data.bWide (n + 1)
  cTall n := data.cTall (n + 1)
  dTall n := data.dTall (n + 1)
  bottom n := data.bottom (n + 1)
  top n := data.top (n + 1)
  left n := data.left (n + 1)
  right n := data.right (n + 1)
  verticalRadius n := data.verticalRadius (n + 1)
  horizontalRadius n := data.horizontalRadius (n + 1)
  wideLeft n := data.wideLeft (n + 1)
  wideRight n := data.wideRight (n + 1)
  tallBottom n := data.tallBottom (n + 1)
  tallTop n := data.tallTop (n + 1)
  verticalConnector n := data.verticalConnector (n + 1)
  horizontalConnector n := data.horizontalConnector (n + 1)
  bottomLimit := data.bottomLimit.comp (tendsto_add_atTop_nat 1)
  topLimit := data.topLimit.comp (tendsto_add_atTop_nat 1)
  leftLimit := data.leftLimit.comp (tendsto_add_atTop_nat 1)
  rightLimit := data.rightLimit.comp (tendsto_add_atTop_nat 1)
  verticalMergeLimit :=
    data.verticalMergeLimit.comp (tendsto_add_atTop_nat 1)
  horizontalMergeLimit :=
    data.horizontalMergeLimit.comp (tendsto_add_atTop_nat 1)




theorem PeriodicPlanarDualPair.carriedCrossNestedArrays_succ_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hFKGDual : IsFKG (D.dualMeasure mu))
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (primal : D.primalEmbedding.CarriedCrossNestedArray mu)
    (dual : D.dualEmbedding.CarriedCrossNestedArray (D.dualMeasure mu))
    (hspanHX : forall n,
      primal.a (n + 1) + 5 * B < primal.b (n + 1) - 5 * B)
    (hspanDVY : forall n,
      dual.c n + 5 * B < dual.d n - 5 * B)
    (hspanDHX : forall n,
      dual.a n + 5 * B < dual.b n - 5 * B)
    (hspanVY : forall n,
      primal.c (n + 1) + 5 * B < primal.d (n + 1) - 5 * B)
    (hHBottom : forall n, dual.c n + 4 * B <= primal.cTall (n + 1))
    (hHTop : forall n, primal.dTall (n + 1) <= dual.d n - 4 * B)
    (hDVLeft : forall n, primal.a (n + 1) + 4 * B <= dual.aWide n)
    (hDVRight : forall n, dual.bWide n <= primal.b (n + 1) - 4 * B)
    (hVLeft : forall n, dual.a n + 4 * B <= primal.aWide (n + 1))
    (hVRight : forall n, primal.bWide (n + 1) <= dual.b n - 4 * B)
    (hDHBottom : forall n, primal.c (n + 1) + 4 * B <= dual.cTall n)
    (hDHTop : forall n, dual.dTall n <= primal.d (n + 1) - 4 * B) : False := by
  exact D.carriedCrossNestedArrays_false mu hFKG hFKGDual B hBpos hBp hBd
    (primal.tail D.primalEmbedding mu) dual
    hspanHX hspanDVY hspanDHX hspanVY
    hHBottom hHTop hDVLeft hDVRight hVLeft hVRight hDHBottom hDHTop



theorem asymmetricComplementaryEndpointLimits_false
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (H V dualV dualH : Nat -> Real)
    (hH0 : forall n, 0 <= H n) (hV0 : forall n, 0 <= V n)
    (hHdual : forall n, H n + dualV n <= 1)
    (hVdual : forall n, V n + dualH n <= 1)
    (hprimal : Tendsto (fun n => max (H n) (V n)) atTop (nhds 1))
    (hdualV : Tendsto dualV atTop (nhds 1))
    (hdualH : Tendsto dualH atTop (nhds 1)) : False := by
  have hHzero : Tendsto H atTop (nhds 0) := by
    have hupper : Tendsto (fun n => 1 - dualV n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdualV
    apply squeeze_zero hH0 (fun n => ?_)
      hupper
    linarith [hHdual n]
  have hVzero : Tendsto V atTop (nhds 0) := by
    have hupper : Tendsto (fun n => 1 - dualH n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdualH
    apply squeeze_zero hV0 (fun n => ?_)
      hupper
    linarith [hVdual n]
  have hzero : Tendsto (fun n => max (H n) (V n))
      atTop (nhds 0) := by
    simpa using hHzero.max hVzero
  have : (0 : Real) = 1 := tendsto_nhds_unique hzero hprimal
  norm_num at this




theorem PeriodicPlanarDualPair.variablePadBranchAlignedComplementary_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (branch : Nat -> Bool) (a b c d xPad yPad : Nat -> Real)
    (hxPad : forall n, 4 * B <= xPad n)
    (hyPad : forall n, 4 * B <= yPad n)
    (hspanX : forall n, a n + 5 * B < b n - 5 * B)
    (hspanY : forall n, c n + 5 * B < d n - 5 * B)
    (hprimal : Tendsto (fun n => if branch n then
      mu.real (D.primalEmbedding.verticalCrossingEvent
        (a n + xPad n) (b n - xPad n) (c n) (d n))
    else
      mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a n) (b n) (c n + yPad n) (d n - yPad n)))
      atTop (nhds 1))
    (hdual : Tendsto (fun n => if branch n then
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a n) (b n) (c n + yPad n) (d n - yPad n))
    else
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a n + xPad n) (b n - xPad n) (c n) (d n)))
      atTop (nhds 1)) : False := by
  apply branchAlignedComplementaryLimits_false branch
    (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a n) (b n) (c n + yPad n) (d n - yPad n)))
    (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent
      (a n + xPad n) (b n - xPad n) (c n) (d n)))
    (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a n + xPad n) (b n - xPad n) (c n) (d n)))
    (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a n) (b n) (c n + yPad n) (d n - yPad n)))
  · intro n
    exact D.matchedCrossing_measureReal_add_le_one_of_pads mu hBpos
      hBp hBd (hxPad n) (hyPad n) (hspanX n) (hspanY n)
  · intro n
    exact D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads
      mu hBpos hBp hBd (hxPad n) (hyPad n)
        (hspanX n) (hspanY n)
  · exact hprimal
  · exact hdual






theorem PeriodicPlanarDualPair.outwardBranchAlignedComplementary_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (branch : Nat -> Bool) (a b c d xPad yPad : Nat -> Real)
    (vLeft vRight vBottom vTop : Nat -> Real)
    (hLeft hRight hBottom hTop : Nat -> Real)
    (hvLeft : forall n, vLeft n = a n + xPad n)
    (hvRight : forall n, vRight n = b n - xPad n)
    (hvBottom : forall n, vBottom n = c n)
    (hvTop : forall n, vTop n = d n)
    (hhLeft : forall n, hLeft n = a n)
    (hhRight : forall n, hRight n = b n)
    (hhBottom : forall n, hBottom n = c n + yPad n)
    (hhTop : forall n, hTop n = d n - yPad n)
    (hxPad : forall n, 4 * B <= xPad n)
    (hyPad : forall n, 4 * B <= yPad n)
    (hspanX : forall n, a n + 5 * B < b n - 5 * B)
    (hspanY : forall n, c n + 5 * B < d n - 5 * B)
    (hprimal : Tendsto (fun n => if branch n then
      mu.real (D.primalEmbedding.verticalCrossingEvent
        (vLeft n) (vRight n) (vBottom n) (vTop n))
    else
      mu.real (D.primalEmbedding.horizontalCrossingEvent
        (hLeft n) (hRight n) (hBottom n) (hTop n)))
      atTop (nhds 1))
    (hdual : Tendsto (fun n => if branch n then
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (hLeft n) (hRight n) (hBottom n) (hTop n))
    else
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (vLeft n) (vRight n) (vBottom n) (vTop n)))
      atTop (nhds 1)) : False := by
  apply D.variablePadBranchAlignedComplementary_false mu B hBpos hBp hBd
    branch a b c d xPad yPad hxPad hyPad hspanX hspanY
  · apply hprimal.congr'
    filter_upwards [] with n
    simp only [hvLeft n, hvRight n, hvBottom n, hvTop n,
      hhLeft n, hhRight n, hhBottom n, hhTop n]
  · apply hdual.congr'
    filter_upwards [] with n
    simp only [hvLeft n, hvRight n, hvBottom n, hvTop n,
      hhLeft n, hhRight n, hhBottom n, hhTop n]






theorem tendsto_max_one_fixedBranch_subsequence
    (H V : Nat -> Real)
    (hmax : Tendsto (fun n => max (H n) (V n)) atTop (nhds 1)) :
    (exists phi : Nat -> Nat, StrictMono phi /\
      (forall n, V (phi n) <= H (phi n)) /\
      Tendsto (fun n => H (phi n)) atTop (nhds 1)) \/
    (exists phi : Nat -> Nat, StrictMono phi /\
      (forall n, H (phi n) <= V (phi n)) /\
      Tendsto (fun n => V (phi n)) atTop (nhds 1)) := by
  let p : Nat -> Prop := fun n => V n <= H n
  by_cases hp : (setOf p).Infinite
  · left
    let phi : Nat -> Nat := Nat.nth p
    have hphi : StrictMono phi := Nat.nth_strictMono hp
    refine ⟨phi, hphi, ?_, ?_⟩
    · intro n
      exact Nat.nth_mem_of_infinite hp n
    · have hsub := hmax.comp hphi.tendsto_atTop
      apply hsub.congr'
      filter_upwards [] with n
      change max (H (phi n)) (V (phi n)) = H (phi n)
      rw [max_eq_left (Nat.nth_mem_of_infinite hp n)]
  · right
    have hpFinite : (setOf p).Finite := Set.not_infinite.mp hp
    have hnotp : (setOf fun n => ¬ p n).Infinite := by
      rw [<- Set.not_finite]
      intro hfinite
      rw [<- Set.compl_setOf p] at hfinite
      have huniv : (Set.univ : Set Nat).Finite := by
        have hunion := hpFinite.union hfinite
        simpa only [Set.union_compl_self] using hunion
      exact Set.infinite_univ huniv
    let phi : Nat -> Nat := Nat.nth (fun n => ¬ p n)
    have hphi : StrictMono phi := Nat.nth_strictMono hnotp
    refine ⟨phi, hphi, ?_, ?_⟩
    · intro n
      exact le_of_not_ge (Nat.nth_mem_of_infinite hnotp n)
    · have hsub := hmax.comp hphi.tendsto_atTop
      apply hsub.congr'
      filter_upwards [] with n
      change max (H (phi n)) (V (phi n)) = V (phi n)
      rw [max_eq_right (le_of_not_ge
        (Nat.nth_mem_of_infinite hnotp n))]






theorem AlignedCrossNestedPairedSequence.false_of_primalAdjacent_and_dualMergeLimits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {p pDual : Nat -> Real}
    {family : forall n, D.primalEmbedding.NormalBoundaryBandFamily
      mu (P.orbitBox n) (p n)}
    {familyDual : forall n, D.dualEmbedding.NormalBoundaryBandFamily
      (D.dualMeasure mu) (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence D.primalEmbedding
      D.dualEmbedding mu (D.dualMeasure mu)
        p pDual family familyDual padding)
    (hFKGDual : IsFKG (D.dualMeasure mu))
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
    (hpDual : Tendsto pDual atTop (nhds 1))
    (hpDual_le : forall n, pDual n <= 1)
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (hpadding : 4 * B <= (padding : Real))
    (hcurrentX : forall n, 10 * B < (data.triple n).currentX)
    (hcurrentY : forall n, 10 * B < (data.triple n).currentY)
    (hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent 0
        (data.triple n).currentX 0 (data.triple n).currentY))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (data.triple n).current.raw.data.wideLeft
        (data.triple n).current.raw.data.wideRight 0
        (data.triple n).currentY))) atTop (nhds 1))
    (hmergeVertical : Tendsto (fun n => (D.dualMeasure mu).real
      (D.dualEmbedding.rectanglePairMergeErrorUnion
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight 0
        (data.triple n).previousY
        (data.triple n).previous.raw.data.dualBottomSource
        (data.triple n).previous.raw.data.dualTopSource))
      atTop (nhds 0))
    (hmergeHorizontal : Tendsto (fun n => (D.dualMeasure mu).real
      (D.dualEmbedding.rectanglePairMergeErrorUnion 0
        (data.triple n).nextX 0 (data.triple n).nextY
        (data.triple n).next.raw.data.dualLeftSource
        (data.triple n).next.raw.data.dualRightSource))
      atTop (nhds 0)) : False := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  obtain ⟨hspanX0, hspanY0, hspanX1, hspanY1⟩ :=
    data.transitionCoordinates_spans_of_current_gt B hcurrentX hcurrentY
  have hprimal' := data.primalAdjacent_transitionCoordinates hprimal
  obtain ⟨hdualV, hdualH⟩ :=
    data.dual_endpoint_transitionCoordinates_of_mergeLimits
      hFKGDual hTIDual hpDual hpDual_le hmergeVertical hmergeHorizontal
  have hdualV' : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (data.transitionA0 n + padding)
          (data.transitionB0 n - padding)
          (data.transitionC0 n) (data.transitionD0 n)))
      atTop (nhds 1) := by
    apply hdualV.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)]
  have hdualH' : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (data.transitionA1 n) (data.transitionB1 n)
          (data.transitionC1 n + padding)
          (data.transitionD1 n - padding)))
      atTop (nhds 1) := by
    apply hdualH.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]
  apply D.variablePadComplementaryCrossNested_false mu B hBpos hBp hBd
    data.transitionA0 data.transitionB0
    data.transitionC0 data.transitionD0
    data.transitionA1 data.transitionB1
    data.transitionC1 data.transitionD1 (fun _ => (padding : Real))
    (fun _ => hpadding) hspanX0 hspanY0 hspanX1 hspanY1
  · simpa only using hprimal'
  · simpa only using hdualV'
  · simpa only using hdualH'







theorem AlignedCrossNestedPairedSequence.exists_mixedEndpointRadii_false_of_primalAdjacent
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {p pDual : Nat -> Real}
    {family : forall n, D.primalEmbedding.NormalBoundaryBandFamily
      mu (P.orbitBox n) (p n)}
    {familyDual : forall n, D.dualEmbedding.NormalBoundaryBandFamily
      (D.dualMeasure mu) (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence D.primalEmbedding
      D.dualEmbedding mu (D.dualMeasure mu)
        p pDual family familyDual padding)
    (hFKGDual : IsFKG (D.dualMeasure mu))
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
    (huniqueDual : (D.dualMeasure mu)
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (hpDual : Tendsto pDual atTop (nhds 1))
    (hpDual_le : forall n, pDual n <= 1)
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (hpadding : 4 * B <= (padding : Real))
    (hcurrentX : forall n, 10 * B < (data.triple n).currentX)
    (hcurrentY : forall n, 10 * B < (data.triple n).currentY)
    (hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent 0
        (data.triple n).currentX 0 (data.triple n).currentY))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (data.triple n).current.raw.data.wideLeft
        (data.triple n).current.raw.data.wideRight 0
        (data.triple n).currentY))) atTop (nhds 1)) :
    exists verticalRadius horizontalRadius : Nat -> Nat,
      (forall n, n <= verticalRadius n) /\
      (forall n, n <= horizontalRadius n) /\
      ((forall n,
        (Pdual.orbitBox
          (Pdual.bufferedRadius (verticalRadius n)) : Set W) <=
          D.dualEmbedding.rectVertices
            (data.triple n).previous.raw.data.wideLeft
            (data.triple n).previous.raw.data.wideRight 0
            (data.triple n).previousY) ->
       (forall n,
        (Pdual.orbitBox
          (Pdual.bufferedRadius (horizontalRadius n)) : Set W) <=
          D.dualEmbedding.rectVertices 0 (data.triple n).nextX 0
            (data.triple n).nextY) -> False) := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  obtain ⟨verticalRadius, horizontalRadius, hverticalRadius,
      hhorizontalRadius, hendpoints⟩ :=
    data.exists_dual_endpoint_transitionCoordinates_of_connectorContainment
      hFKGDual hTIDual huniqueDual hpDual hpDual_le
  refine ⟨verticalRadius, horizontalRadius, hverticalRadius,
    hhorizontalRadius, ?_⟩
  intro hverticalBox hhorizontalBox
  obtain ⟨hdualV, hdualH⟩ := hendpoints hverticalBox hhorizontalBox
  obtain ⟨hspanX0, hspanY0, hspanX1, hspanY1⟩ :=
    data.transitionCoordinates_spans_of_current_gt B hcurrentX hcurrentY
  have hprimal' := data.primalAdjacent_transitionCoordinates hprimal
  have hdualV' : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (data.transitionA0 n + padding)
          (data.transitionB0 n - padding)
          (data.transitionC0 n) (data.transitionD0 n)))
      atTop (nhds 1) := by
    apply hdualV.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)]
  have hdualH' : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (data.transitionA1 n) (data.transitionB1 n)
          (data.transitionC1 n + padding)
          (data.transitionD1 n - padding)))
      atTop (nhds 1) := by
    apply hdualH.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]
  apply D.variablePadComplementaryCrossNested_false mu B hBpos hBp hBd
    data.transitionA0 data.transitionB0
    data.transitionC0 data.transitionD0
    data.transitionA1 data.transitionB1
    data.transitionC1 data.transitionD1 (fun _ => (padding : Real))
    (fun _ => hpadding) hspanX0 hspanY0 hspanX1 hspanY1
  · simpa only using hprimal'
  · simpa only using hdualV'
  · simpa only using hdualH'





theorem PeriodicPlaneEmbedding.exists_deep_adjacentHeight_preference_crossing_branch
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (a b c d : Real) (t : Int) (ht : 0 <= t)
    {width height margin : Nat} (hwidth : 0 < width)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (source : PreferenceGridVertex width height -> Finset V)
    (bottom top left right : PreferenceGridVertex width height -> Real)
    (vertical horizontal : PreferenceGridVertex width height -> Bool)
    (hsource : forall x, (source x : Set V) <= E.rectVertices a b c d)
    (hbottomScore : forall x, bottom x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectBottomBoundaryVertices a b c d)))
    (htopScore : forall x, top x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectTopBoundaryVertices a b c d)))
    (hleftScore : forall x, left x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectLeftBoundaryVertices a b c d)))
    (hrightScore : forall x, right x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectRightBoundaryVertices a b c d)))
    (hverticalBottom : forall v, v.2.val <= margin -> vertical v = true)
    (hverticalTop : forall v, height <= v.2.val + margin ->
      vertical v = false)
    (hhorizontalLeft : forall v, v.1.val <= margin -> horizontal v = true)
    (hhorizontalRight : forall v, width <= v.1.val + margin ->
      horizontal v = false)
    (hVtrue : forall v, vertical v = true ->
      top v <= bottom v + epsilon)
    (hVfalse : forall v, vertical v = false ->
      bottom v <= top v + epsilon)
    (hHtrue : forall v, horizontal v = true ->
      right v <= left v + epsilon)
    (hHfalse : forall v, horizontal v = false ->
      left v <= right v + epsilon) :
    exists x xVertical xHorizontal : PreferenceGridVertex width height,
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) /\
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) /\
      margin <= x.1.val /\ x.1.val + margin < width /\
      margin <= x.2.val /\ x.2.val + margin < height /\
      ((1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
          bottom x + epsilon /\
        let U := (source xVertical).image (P.shift (verticalShift t))
        let Mtransfer := mu.real
          (E.rectanglePairMergeErrorUnion a b c d
            (source x) (source xVertical))
        let Mjoin := mu.real
          (E.rectanglePairMergeErrorUnion a b c (d + t) (source x) U)
        bottom x *
            (mu.real (P.setHitsInfinite (source xVertical : Set V)) *
              bottom x - Mtransfer - epsilon) - Mjoin <=
          mu.real (E.verticalCrossingEvent a b c (d + t))) \/
       (1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
          left x + epsilon /\
        left x *
            (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) *
              left x -
              mu.real (E.rectanglePairMergeErrorUnion a b c d
                (source x) (source xHorizontal)) - epsilon) -
            mu.real (E.rectanglePairMergeErrorUnion a b c d
              (source x) (source xHorizontal)) <=
          mu.real (E.horizontalCrossingEvent a b c d))) := by
  obtain ⟨x, xVertical, xHorizontal, hxV, hxH, hxVadj, hxVfalse,
      hxHadj, hxHfalse, hxLeft, hxRight, hxBottom, hxTop⟩ :=
    exists_deep_common_preference_grid_witness hwidth vertical horizontal
      hverticalBottom hverticalTop hhorizontalLeft hhorizontalRight
  have hBT := hVtrue x hxV
  have hLR := hHtrue x hxH
  rw [hbottomScore x, htopScore x] at hBT
  rw [hleftScore x, hrightScore x] at hLR
  have hpref := E.preference_max_bottom_left_add_epsilon_ge_fourthRoot
    mu hFKG a b c d (source x : Set V) epsilon hepsilon (hsource x)
      (by simpa [hbottomScore x, htopScore x] using hBT)
      (by simpa [hleftScore x, hrightScore x] using hLR)
  have hpref' :
      1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        max (bottom x) (left x) + epsilon := by
    simpa [hbottomScore x, hleftScore x] using hpref
  refine ⟨x, xVertical, xHorizontal, hxVadj, hxHadj,
    hxLeft, hxRight, hxBottom, hxTop, ?_⟩
  by_cases hLB : left x <= bottom x
  · left
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        bottom x + epsilon := by
      simpa [max_eq_left hLB] using hpref'
    have hOpp := hVfalse xVertical hxVfalse
    rw [hbottomScore xVertical, htopScore xVertical] at hOpp
    have htransfer :=
      E.adjacentHeightVerticalCrossing_ge_approxPreferredSide_transfer
        mu hFKG hTI a b c d t ht (source x) (source xVertical) epsilon
        (by simpa [hbottomScore xVertical, htopScore xVertical] using hOpp)
    rw [<- hbottomScore x] at htransfer
    exact ⟨hroot, htransfer⟩
  · right
    have hBL : bottom x <= left x := le_of_not_ge hLB
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        left x + epsilon := by
      simpa [max_eq_right hBL] using hpref'
    have hOpp := hHfalse xHorizontal hxHfalse
    rw [hleftScore xHorizontal, hrightScore xHorizontal] at hOpp
    have htransfer := E.horizontalCrossing_ge_approxPreferredSide_transfer
      mu hFKG a b c d (source x) (source xHorizontal) epsilon
      (by simpa [hleftScore xHorizontal, hrightScore xHorizontal] using hOpp)
    rw [<- hleftScore x] at htransfer
    exact ⟨hroot, htransfer⟩





theorem PeriodicPlaneEmbedding.translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (L R : Nat -> Finset V) (radius : Nat -> Nat)
    (z : Nat -> Site 2) (a b c d : Nat -> Real)
    (hbox : forall n,
      (P.shift (z n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n) (b n) (c n) (d n))
    (hmerge : Tendsto (fun n =>
      mu.real (P.pairMergeErrorUnion (L n) (R n) (radius n)))
        atTop (nhds 0)) :
    Tendsto (fun n => mu.real
      (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
        ((L n).image (P.shift (z n)))
        ((R n).image (P.shift (z n))))) atTop (nhds 0) := by
  exact squeeze_zero (fun _ => measureReal_nonneg) (fun n =>
    E.translated_rectanglePairMergeErrorUnion_measureReal_le
      mu hTI (z n) (a n) (b n) (c n) (d n)
        (L n) (R n) (radius n) (hbox n)) hmerge



def PeriodicPlaneEmbedding.UniformTemplateDeepGridAdjacentHeightCrossingRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (template : Nat -> Finset V) (step : Nat -> Int)
    (radius : Nat -> Nat) : Prop :=
  forall (width height margin : Nat -> Nat)
    (hwidth : forall n, 0 < width n)
    (base : Nat -> Site 2)
    (vertical horizontal : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Bool)
    (a b c d epsilon : Nat -> Real)
    (bottom top left right : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Real),
    Tendsto epsilon atTop (nhds 0) ->
    (forall n, 0 <= epsilon n) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V) <=
          E.rectVertices (a n) (b n) (c n) (d n)) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      margin n <= v.1.val -> v.1.val + margin n < width n ->
      margin n <= v.2.val -> v.2.val + margin n < height n ->
      (P.shift (base n + preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n) (b n) (c n) (d n)) ->
    (forall n v, bottom n v = mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n v, top n v = mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n v, left n v = mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n v, right n v = mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n v, v.2.val <= margin n -> vertical n v = true) ->
    (forall n v, height n <= v.2.val + margin n ->
      vertical n v = false) ->
    (forall n v, v.1.val <= margin n -> horizontal n v = true) ->
    (forall n v, width n <= v.1.val + margin n ->
      horizontal n v = false) ->
    (forall n v, vertical n v = true ->
      top n v <= bottom n v + epsilon n) ->
    (forall n v, vertical n v = false ->
      bottom n v <= top n v + epsilon n) ->
    (forall n v, horizontal n v = true ->
      right n v <= left n v + epsilon n) ->
    (forall n v, horizontal n v = false ->
      left n v <= right n v + epsilon n) ->
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (a n) (b n) (c n) (d n)))
      (mu.real (E.verticalCrossingEvent
        (a n) (b n) (c n) (d n + step n)))) atTop (nhds 1)

set_option linter.unusedVariables false in



theorem PeriodicPlaneEmbedding.uniformTemplateDeepGridAdjacentHeightCrossingRadius_of_pairMerge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (template : Nat -> Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (step : Nat -> Int) (hstep : forall n, 0 <= step n)
    (radius : Nat -> Nat)
    (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
        ((template n).image (P.shift
          (preferenceKingOffset (q n).2 +
            if (q n).1.val = 0 then 0 else verticalShift (step n))))
        (radius n))) atTop (nhds 0)) :
    E.UniformTemplateDeepGridAdjacentHeightCrossingRadius
      mu template step radius := by
  classical
  let neighbor : Nat -> (Fin 2 × (Fin 3 × Fin 3)) -> Finset V := fun n q =>
    (template n).image (P.shift (preferenceKingOffset q.2 +
      if q.1.val = 0 then 0 else verticalShift (step n)))
  intro width height margin hwidth base vertical horizontal
    a b c d epsilon bottom top left right hepsilon hepsilon0
    hsource hconnector hbottomScore htopScore hleftScore hrightScore
    hVbottom hVtop hHleft hHright hVtrue hVfalse hHtrue hHfalse
  have hwitness (n : Nat) :=
    E.exists_deep_adjacentHeight_preference_crossing_branch
      mu hFKG hTI (a n) (b n) (c n) (d n) (step n) (hstep n)
      (hwidth n) (epsilon n) (hepsilon0 n)
      (fun v => (template n).image
        (P.shift (base n + preferenceGridSite v)))
      (bottom n) (top n) (left n) (right n)
      (vertical n) (horizontal n) (hsource n)
      (hbottomScore n) (htopScore n) (hleftScore n) (hrightScore n)
      (hVbottom n) (hVtop n) (hHleft n) (hHright n)
      (hVtrue n) (hVfalse n) (hHtrue n) (hHfalse n)
  choose x xVertical xHorizontal hxVadj hxHadj hxLeft hxRight
    hxBottom hxTop hbranch using hwitness
  choose ijV hijV using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxVadj n)
  choose ijH hijH using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxHadj n)
  let source : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Finset V := fun n v =>
    (template n).image (P.shift (base n + preferenceGridSite v))
  let shiftedVerticalSource : Nat -> Finset V := fun n =>
    (source n (xVertical n)).image (P.shift (verticalShift (step n)))
  let z : Nat -> Site 2 := fun n => base n + preferenceGridSite (x n)
  have hzV (n : Nat) : z n + preferenceKingOffset (ijV n) =
      base n + preferenceGridSite (xVertical n) := by
    dsimp only [z]
    rw [hijV n]
    simp only [add_assoc]
  have hzH (n : Nat) : z n + preferenceKingOffset (ijH n) =
      base n + preferenceGridSite (xHorizontal n) := by
    dsimp only [z]
    rw [hijH n]
    simp only [add_assoc]
  have hneighbor0 (n : Nat) (ij : Fin 3 × Fin 3) :
      (neighbor n ((0 : Fin 2), ij)).image (P.shift (z n)) =
        (template n).image
          (P.shift (z n + preferenceKingOffset ij)) := by
    simp only [neighbor, Fin.isValue, Fin.val_zero, if_pos, add_zero,
      Finset.image_image]
    apply Finset.image_congr
    intro u hu
    simpa [add_comm] using
      (P.shift_add (preferenceKingOffset ij) (z n) u).symm
  have hneighbor1 (n : Nat) (ij : Fin 3 × Fin 3) :
      (neighbor n ((1 : Fin 2), ij)).image (P.shift (z n)) =
        ((template n).image
          (P.shift (z n + preferenceKingOffset ij))).image
            (P.shift (verticalShift (step n))) := by
    simp only [neighbor, Fin.isValue, Fin.val_one, one_ne_zero, if_false,
      Finset.image_image]
    apply Finset.image_congr
    intro u hu
    change P.shift (z n)
        (P.shift (preferenceKingOffset ij + verticalShift (step n)) u) =
      P.shift (verticalShift (step n))
        (P.shift (z n + preferenceKingOffset ij) u)
    rw [<- P.shift_add, <- P.shift_add]
    congr 2
    abel
  have hrectZ (n : Nat) :
      (P.shift (z n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n) (b n) (c n) (d n) := by
    exact hconnector n (x n) (hxLeft n) (hxRight n)
      (hxBottom n) (hxTop n)
  have hrectHull (n : Nat) :
      (P.shift (z n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n) (b n) (c n) (d n + step n) := by
    have hstepR : (0 : Real) <= step n := by exact_mod_cast hstep n
    exact (hrectZ n).trans
      (E.rectVertices_mono le_rfl le_rfl le_rfl (by linarith))
  have hMv00 :=
    E.translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge
      mu hTI template (fun n => neighbor n ((0 : Fin 2), ijV n))
      radius z a b c d hrectZ (by
        simpa only [neighbor] using
          hmerge (fun n => ((0 : Fin 2), ijV n)))
  have hMv10 :=
    E.translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge
      mu hTI template (fun n => neighbor n ((1 : Fin 2), ijV n))
      radius z a b c (fun n => d n + step n) hrectHull (by
        simpa only [neighbor] using
          hmerge (fun n => ((1 : Fin 2), ijV n)))
  have hMh0 :=
    E.translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge
      mu hTI template (fun n => neighbor n ((0 : Fin 2), ijH n))
      radius z a b c d hrectZ (by
        simpa only [neighbor] using
          hmerge (fun n => ((0 : Fin 2), ijH n)))
  let Mv0 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
      (source n (x n)) (source n (xVertical n)))
  let Mv1 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n + step n)
      (source n (x n)) (shiftedVerticalSource n))
  let Mv : Nat -> Real := fun n => Mv0 n + Mv1 n
  let Mh : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
      (source n (x n)) (source n (xHorizontal n)))
  have hMv0 : Tendsto Mv0 atTop (nhds 0) := by
    simpa only [Mv0, source, z, hneighbor0, hzV] using hMv00
  have hMv1 : Tendsto Mv1 atTop (nhds 0) := by
    simpa only [Mv1, source, shiftedVerticalSource, z, hneighbor1, hzV]
      using hMv10
  have hMv : Tendsto Mv atTop (nhds 0) := by
    simpa only [Mv, zero_add] using hMv0.add hMv1
  have hMh : Tendsto Mh atTop (nhds 0) := by
    simpa only [Mh, source, z, hneighbor0, hzH] using hMh0
  let verticalBranch : Nat -> Prop := fun n =>
    1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))) <=
          bottom n (x n) + epsilon n /\
      bottom n (x n) *
          (mu.real (P.setHitsInfinite
              (source n (xVertical n) : Set V)) * bottom n (x n) -
            Mv0 n - epsilon n) - Mv1 n <=
        mu.real (E.verticalCrossingEvent
          (a n) (b n) (c n) (d n + step n))
  let A : Nat -> Real := fun n =>
    if verticalBranch n then bottom n (x n) else left n (x n)
  let Hv : Nat -> Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xVertical n) : Set V))
  let Hh : Nat -> Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xHorizontal n) : Set V))
  let Cv : Nat -> Real := fun n => mu.real
    (E.verticalCrossingEvent (a n) (b n) (c n) (d n + step n))
  let Ch : Nat -> Real := fun n => mu.real
    (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))
  let root : Nat -> Real := fun n =>
    1 - Real.sqrt (Real.sqrt
      (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V))))
  have htranslatedHit (q : (n : Nat) ->
      PreferenceGridVertex (width n) (height n)) : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (source n (q n) : Set V)))
      atTop (nhds 1) := by
    apply htemplateHit.congr'
    filter_upwards with n
    have hset : ((source n (q n) : Finset V) : Set V) =
        P.shift (base n + preferenceGridSite (q n)) ''
          (template n : Set V) := by
      ext v
      simp [source]
    rw [hset, P.setHitsInfinite_translate_measureReal_eq mu hTI]
  have hroot : Tendsto root atTop (nhds 1) := by
    have hhit := htranslatedHit x
    have hmiss : Tendsto (fun n =>
        1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hhit
    simpa [root] using tendsto_const_nhds.sub hmiss.sqrt.sqrt
  have hHv : Tendsto Hv atTop (nhds 1) := by
    simpa [Hv] using htranslatedHit xVertical
  have hHh : Tendsto Hh atTop (nhds 1) := by
    simpa [Hh] using htranslatedHit xHorizontal
  have hrootA (n : Nat) : root n <= A n + epsilon n := by
    by_cases hv : verticalBranch n
    · simpa [A, root, hv] using hv.1
    · simpa [A, root, source, shiftedVerticalSource, Mv0, Mv1, hv] using
        ((hbranch n).resolve_left hv).1
  have hAupper (n : Nat) : A n <= 1 := by
    by_cases hv : verticalBranch n
    · simp only [A, if_pos hv]
      rw [hbottomScore n (x n)]
      exact measureReal_le_one
    · simp only [A, if_neg hv]
      rw [hleftScore n (x n)]
      exact measureReal_le_one
  have hcrossingBranch (n : Nat) :
      A n * (Hv n * A n - Mv n - epsilon n) - Mv n <= Cv n \/
      A n * (Hh n * A n - Mh n - epsilon n) - Mh n <= Ch n := by
    by_cases hv : verticalBranch n
    · left
      have hraw := hv.2
      have hA0 : 0 <= bottom n (x n) := by
        rw [hbottomScore]
        exact measureReal_nonneg
      have hM0 : 0 <= Mv0 n := measureReal_nonneg
      have hM1 : 0 <= Mv1 n := measureReal_nonneg
      simp only [A, if_pos hv, Hv, Cv, Mv] at ⊢
      nlinarith
    · right
      have hb := (hbranch n).resolve_left hv
      simpa [A, Hh, Ch, Mh, source, shiftedVerticalSource, Mv0, Mv1, hv]
        using hb.2
  simpa [Cv, Ch, max_comm] using
    crossing_max_tendsto_one_of_approxPreferredSide_root_branches
      root A Hv Hh Mv Mh epsilon Cv Ch hroot hrootA hAupper
      hHv hHh hMv hMh hepsilon hcrossingBranch
      (fun _ => measureReal_le_one) (fun _ => measureReal_le_one)





theorem PeriodicPlaneEmbedding.exists_uniformTemplate_deepGrid_adjacentHeight_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat -> Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (step : Nat -> Int) (hstep : forall n, 0 <= step n) :
    exists radius : Nat -> Nat,
      E.UniformTemplateDeepGridAdjacentHeightCrossingRadius
        mu template step radius := by
  let neighbor : Nat -> (Fin 2 × (Fin 3 × Fin 3)) -> Finset V := fun n q =>
    (template n).image (P.shift (preferenceKingOffset q.2 +
      if q.1.val = 0 then 0 else verticalShift (step n)))
  obtain ⟨radius, hradius⟩ :=
    P.exists_uniform_pairMergeRadius mu hunique template neighbor
  have hepsilon : Tendsto (fun n : Nat => (1 : Real) / (n + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hmerge (q : Nat -> Fin 2 × (Fin 3 × Fin 3)) :
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
        ((template n).image (P.shift
          (preferenceKingOffset (q n).2 +
            if (q n).1.val = 0 then 0 else verticalShift (step n))))
        (radius n))) atTop (nhds 0) := by
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => le_of_lt ((hradius n).2 (q n))) hepsilon
  exact ⟨radius,
    E.uniformTemplateDeepGridAdjacentHeightCrossingRadius_of_pairMerge
      mu hFKG hTI template htemplateHit step hstep radius hmerge⟩





theorem PeriodicPlaneEmbedding.exists_adjacentHeight_pairMergeRadius_at_error
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Finset V) (step : Int) (cutoff : Nat)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    exists radius : Nat, cutoff <= radius /\
      forall q : Fin 2 × (Fin 3 × Fin 3),
        mu.real (P.pairMergeErrorUnion template
          (template.image (P.shift (preferenceKingOffset q.2 +
            if q.1.val = 0 then 0 else verticalShift step))) radius) <
          epsilon := by
  let neighbor : Fin 2 × (Fin 3 × Fin 3) -> Finset V := fun q =>
    template.image (P.shift (preferenceKingOffset q.2 +
      if q.1.val = 0 then 0 else verticalShift step))
  have hsum : Tendsto (fun radius =>
      ∑ q : Fin 2 × (Fin 3 × Fin 3),
        mu.real (P.pairMergeErrorUnion template (neighbor q) radius))
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun q _ =>
      P.pairMergeErrorUnion_real_tendsto_zero
        mu hunique template (neighbor q))
  rw [Metric.tendsto_atTop] at hsum
  obtain ⟨threshold, hthreshold⟩ := hsum epsilon hepsilon
  let radius := max cutoff threshold
  have htotal : (∑ q : Fin 2 × (Fin 3 × Fin 3),
      mu.real (P.pairMergeErrorUnion template (neighbor q) radius)) <
      epsilon := by
    simpa [Real.dist_eq, abs_of_nonneg (Finset.sum_nonneg fun _ _ =>
      measureReal_nonneg)] using
      hthreshold radius (Nat.le_max_right cutoff threshold)
  refine ⟨radius, Nat.le_max_left _ _, ?_⟩
  intro q
  change mu.real
      (P.pairMergeErrorUnion template (neighbor q) radius) < epsilon
  exact (Finset.single_le_sum
    (f := fun i : Fin 2 × (Fin 3 × Fin 3) =>
      mu.real (P.pairMergeErrorUnion template (neighbor i) radius))
    (fun i (_ : i ∈ Finset.univ) => measureReal_nonneg)
    (Finset.mem_univ q)).trans_lt htotal





theorem exists_radiusFirst_adjacentEndpointRow
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (template : Finset V) (step : Int) (cutoff : Nat)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (B r y s : Real) (hB0 : 0 <= B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (t : Int) (ht : 3 * B < t)
    (minimumWidth minimumHeight : Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Int)
    (hhorizontalSpan : forall radius w,
      minimumWidth radius <= w ->
      3 * B < horizontalRight w - horizontalLeft w) :
    exists radius width height : Nat,
      cutoff <= radius /\
      minimumWidth radius <= width /\
      minimumHeight radius <= height /\
      (forall q : Fin 2 × (Fin 3 × Fin 3),
        mu.real (P.pairMergeErrorUnion template
          (template.image (P.shift (preferenceKingOffset q.2 +
            if q.1.val = 0 then 0 else verticalShift step))) radius) <
          epsilon) /\
      1 - epsilon < muDual.real (Edual.verticalCrossingEvent
        r (r + width) ((2 * s + (s + t)) / 3)
          ((s + 2 * (s + t)) / 3)) /\
      1 - epsilon < muDual.real (Edual.horizontalCrossingEvent
        (horizontalLeft width) (horizontalRight width)
        y (y + height)) := by
  obtain ⟨radius, hradius, hmerge⟩ :=
    E.exists_adjacentHeight_pairMergeRadius_at_error
      mu hunique template step cutoff epsilon hepsilon
  obtain ⟨width, hwidth, hvertical⟩ :=
    Edual.exists_verticalCrossing_measureReal_gt_of_unique
      muDual hFKGDual hTIDual huniqueDual r B s hB0 hB t ht
        (minimumWidth radius) hepsilon
  let horizontalS : Real := 2 * horizontalLeft width - horizontalRight width
  let horizontalT : Int :=
    3 * (horizontalRight width - horizontalLeft width)
  have hhorizontalT : 3 * B < horizontalT := by
    have hspan := hhorizontalSpan radius width hwidth
    rw [show (horizontalT : Real) =
        3 * ((horizontalRight width : Real) - horizontalLeft width) by
      simp only [horizontalT, Int.cast_mul, Int.cast_ofNat, Int.cast_sub]]
    nlinarith
  obtain ⟨height, hheight, hhorizontal⟩ :=
    Edual.exists_horizontalCrossing_measureReal_gt_of_unique
      muDual hFKGDual hTIDual huniqueDual y B horizontalS hB0 hB
        horizontalT hhorizontalT (minimumHeight radius) hepsilon
  refine ⟨radius, width, height, hradius, hwidth, hheight,
    hmerge, hvertical, ?_⟩
  convert hhorizontal using 1 <;>
    simp only [horizontalS, horizontalT, Int.cast_mul,
      Int.cast_ofNat, Int.cast_sub] <;> ring






theorem exists_radiusFirst_dependentGeometry_adjacentEndpointRow
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (template : Finset V) (step : Int) (cutoff : Nat)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (r y s : Nat -> Real) (t : Nat -> Int)
    (ht : forall radius, 3 * B < t radius)
    (minimumWidth minimumHeight : Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Nat -> Int)
    (hhorizontalSpan : forall radius w,
      minimumWidth radius <= w ->
      3 * B < horizontalRight radius w - horizontalLeft radius w) :
    exists radius width height : Nat,
      cutoff <= radius /\
      minimumWidth radius <= width /\
      minimumHeight radius <= height /\
      (forall q : Fin 2 × (Fin 3 × Fin 3),
        mu.real (P.pairMergeErrorUnion template
          (template.image (P.shift (preferenceKingOffset q.2 +
            if q.1.val = 0 then 0 else verticalShift step))) radius) <
          epsilon) /\
      1 - epsilon < muDual.real (Edual.verticalCrossingEvent
        (r radius) (r radius + width)
        ((2 * s radius + (s radius + t radius)) / 3)
        ((s radius + 2 * (s radius + t radius)) / 3)) /\
      1 - epsilon < muDual.real (Edual.horizontalCrossingEvent
        (horizontalLeft radius width) (horizontalRight radius width)
        (y radius) (y radius + height)) := by
  obtain ⟨radius, hradius, hmerge⟩ :=
    E.exists_adjacentHeight_pairMergeRadius_at_error
      mu hunique template step cutoff epsilon hepsilon
  obtain ⟨width, hwidth, hvertical⟩ :=
    Edual.exists_verticalCrossing_measureReal_gt_of_unique
      muDual hFKGDual hTIDual huniqueDual (r radius) B (s radius)
      hB0 hB (t radius) (ht radius) (minimumWidth radius) hepsilon
  let horizontalS : Real :=
    2 * horizontalLeft radius width - horizontalRight radius width
  let horizontalT : Int :=
    3 * (horizontalRight radius width - horizontalLeft radius width)
  have hhorizontalT : 3 * B < horizontalT := by
    have hspan := hhorizontalSpan radius width hwidth
    rw [show (horizontalT : Real) =
        3 * ((horizontalRight radius width : Real) -
          horizontalLeft radius width) by
      simp only [horizontalT, Int.cast_mul, Int.cast_ofNat, Int.cast_sub]]
    nlinarith
  obtain ⟨height, hheight, hhorizontal⟩ :=
    Edual.exists_horizontalCrossing_measureReal_gt_of_unique
      muDual hFKGDual hTIDual huniqueDual (y radius) B horizontalS
      hB0 hB horizontalT hhorizontalT (minimumHeight radius) hepsilon
  refine ⟨radius, width, height, hradius, hwidth, hheight,
    hmerge, hvertical, ?_⟩
  convert hhorizontal using 1 <;>
    simp only [horizontalS, horizontalT, Int.cast_mul,
      Int.cast_ofNat, Int.cast_sub] <;> ring




structure RadiusFirstAdjacentEndpointRow
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (template : Finset V) (step : Int) (cutoff : Nat)
    (epsilon B r y s : Real) (t : Int)
    (minimumWidth minimumHeight : Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Int) where
  radius : Nat
  width : Nat
  height : Nat
  cutoff_le_radius : cutoff <= radius
  minimumWidth_le : minimumWidth radius <= width
  minimumHeight_le : minimumHeight radius <= height
  merge_lt : forall q : Fin 2 × (Fin 3 × Fin 3),
    mu.real (P.pairMergeErrorUnion template
      (template.image (P.shift (preferenceKingOffset q.2 +
        if q.1.val = 0 then 0 else verticalShift step))) radius) < epsilon
  dualVertical_gt : 1 - epsilon < muDual.real
    (Edual.verticalCrossingEvent r (r + width)
      ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3))
  dualHorizontal_gt : 1 - epsilon < muDual.real
    (Edual.horizontalCrossingEvent
      (horizontalLeft width) (horizontalRight width) y (y + height))


theorem nonempty_radiusFirstAdjacentEndpointRow
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (template : Finset V) (step : Int) (cutoff : Nat)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (B r y s : Real) (hB0 : 0 <= B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (t : Int) (ht : 3 * B < t)
    (minimumWidth minimumHeight : Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Int)
    (hhorizontalSpan : forall radius w,
      minimumWidth radius <= w ->
      3 * B < horizontalRight w - horizontalLeft w) :
    Nonempty (RadiusFirstAdjacentEndpointRow E Edual mu muDual template
      step cutoff epsilon B r y s t minimumWidth minimumHeight
      horizontalLeft horizontalRight) := by
  obtain ⟨radius, width, height, hradius, hwidth, hheight,
      hmerge, hvertical, hhorizontal⟩ :=
    exists_radiusFirst_adjacentEndpointRow E Edual mu muDual hunique
      hFKGDual hTIDual huniqueDual template step cutoff epsilon hepsilon
      B r y s hB0 hB t ht minimumWidth minimumHeight
      horizontalLeft horizontalRight hhorizontalSpan
  exact ⟨{
    radius := radius
    width := width
    height := height
    cutoff_le_radius := hradius
    minimumWidth_le := hwidth
    minimumHeight_le := hheight
    merge_lt := hmerge
    dualVertical_gt := hvertical
    dualHorizontal_gt := hhorizontal }⟩






theorem exists_recursiveRadiusFirstAdjacentEndpointRows_with_limits
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (template : Nat -> Finset V) (initialStep : Int)
    (hinitialStep : 0 <= initialStep)
    (r y s : Nat -> Int -> Real) (t : Nat -> Int -> Int)
    (ht : forall n step, 3 * B < t n step)
    (minimumWidth minimumHeight : Nat -> Int -> Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Int -> Nat -> Int)
    (hhorizontalSpan : forall n step radius width,
      minimumWidth n step radius <= width ->
      3 * B < horizontalRight n step width -
        horizontalLeft n step width) :
    let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
    exists state : Nat -> Int × Nat,
      exists rows : forall n, RadiusFirstAdjacentEndpointRow E Edual mu
        muDual (template n) (state n).1 (state n).2 (epsilon n) B
        (r n (state n).1) (y n (state n).1) (s n (state n).1)
        (t n (state n).1) (minimumWidth n (state n).1)
        (minimumHeight n (state n).1) (horizontalLeft n (state n).1)
        (horizontalRight n (state n).1),
      state 0 = (initialStep, 0) /\
      (forall n, state (n + 1) =
        (((rows n).height : Int), (rows n).radius + 1)) /\
      (forall n, 0 <= (state n).1) /\
      Tendsto (fun n => (rows n).radius) atTop atTop /\
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
          ((template n).image (P.shift
            (preferenceKingOffset (q n).2 +
              if (q n).1.val = 0 then 0
              else verticalShift (state n).1))) (rows n).radius))
          atTop (nhds 0)) /\
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real
          (P.pairMergeErrorUnion (template (n + 1))
            ((template (n + 1)).image (P.shift
              (preferenceKingOffset (q (n + 1)).2 +
                if (q (n + 1)).1.val = 0 then 0
                else verticalShift (state (n + 1)).1)))
            (rows (n + 1)).radius)) atTop (nhds 0)) /\
      Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent
        (r n (state n).1) (r n (state n).1 + (rows n).width)
        ((2 * s n (state n).1 +
          (s n (state n).1 + t n (state n).1)) / 3)
        ((s n (state n).1 +
          2 * (s n (state n).1 + t n (state n).1)) / 3)))
        atTop (nhds 1) /\
      Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent
        (horizontalLeft n (state n).1 (rows n).width)
        (horizontalRight n (state n).1 (rows n).width)
        (y n (state n).1) (y n (state n).1 + (rows n).height)))
        atTop (nhds 1) := by
  dsimp only
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  let chooseRow (n : Nat) (state : Int × Nat) := Classical.choice
    (nonempty_radiusFirstAdjacentEndpointRow E Edual mu muDual hunique
      hFKGDual hTIDual huniqueDual (template n) state.1 state.2
      (epsilon n) (hepsilon n) B (r n state.1) (y n state.1)
      (s n state.1) hB0 hB (t n state.1) (ht n state.1)
      (minimumWidth n state.1) (minimumHeight n state.1)
      (horizontalLeft n state.1) (horizontalRight n state.1)
      (hhorizontalSpan n state.1))
  let state : Nat -> Int × Nat := fun n =>
    Nat.rec (initialStep, 0) (fun n previous =>
      let row := chooseRow n previous
      ((row.height : Int), row.radius + 1)) n
  let rows := fun n => chooseRow n (state n)
  have hstate0 : state 0 = (initialStep, 0) := rfl
  have hstateSucc (n : Nat) : state (n + 1) =
      (((rows n).height : Int), (rows n).radius + 1) := by
    simp only [state, rows]
  have hstepNonneg : forall n, 0 <= (state n).1 := by
    intro n
    cases n with
    | zero => simpa only [hstate0] using hinitialStep
    | succ n =>
        rw [hstateSucc n]
        exact Int.ofNat_zero_le _
  have hcutoffCofinal : forall n, n <= (state n).2 := by
    intro n
    induction n with
    | zero => simp only [hstate0, le_refl]
    | succ n ih =>
        rw [hstateSucc n]
        exact Nat.succ_le_succ (ih.trans (rows n).cutoff_le_radius)
  have hradiusCofinal : forall n, n <= (rows n).radius := fun n =>
    (hcutoffCofinal n).trans (rows n).cutoff_le_radius
  have hradiusTop : Tendsto (fun n => (rows n).radius) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hradiusCofinal n)
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    simpa only [epsilon] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hmerge (q : Nat -> Fin 2 × (Fin 3 × Fin 3)) :
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
        ((template n).image (P.shift
          (preferenceKingOffset (q n).2 +
            if (q n).1.val = 0 then 0
            else verticalShift (state n).1))) (rows n).radius))
        atTop (nhds 0) := by
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => le_of_lt ((rows n).merge_lt (q n))) hepsilonZero
  have hmergeShift (q : Nat -> Fin 2 × (Fin 3 × Fin 3)) :
      Tendsto (fun n => mu.real
        (P.pairMergeErrorUnion (template (n + 1))
          ((template (n + 1)).image (P.shift
            (preferenceKingOffset (q (n + 1)).2 +
              if (q (n + 1)).1.val = 0 then 0
              else verticalShift (state (n + 1)).1)))
          (rows (n + 1)).radius)) atTop (nhds 0) := by
    exact (hmerge q).comp (tendsto_add_atTop_nat 1)
  have hlower : Tendsto (fun n => 1 - epsilon n) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilonZero
  have hvertical : Tendsto (fun n => muDual.real
      (Edual.verticalCrossingEvent
        (r n (state n).1) (r n (state n).1 + (rows n).width)
        ((2 * s n (state n).1 +
          (s n (state n).1 + t n (state n).1)) / 3)
        ((s n (state n).1 +
          2 * (s n (state n).1 + t n (state n).1)) / 3)))
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (rows n).dualVertical_gt)
      (fun _ => measureReal_le_one)
  have hhorizontal : Tendsto (fun n => muDual.real
      (Edual.horizontalCrossingEvent
        (horizontalLeft n (state n).1 (rows n).width)
        (horizontalRight n (state n).1 (rows n).width)
        (y n (state n).1) (y n (state n).1 + (rows n).height)))
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (rows n).dualHorizontal_gt)
      (fun _ => measureReal_le_one)
  exact ⟨state, rows, hstate0, hstateSucc, hstepNonneg, hradiusTop,
    hmerge, hmergeShift, hvertical, hhorizontal⟩




def PeriodicPlaneEmbedding.UniformTemplateAdjacentBoundaryBandCrossingRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) (template : Nat -> Finset V)
    (step : Nat -> Int) (radius : Nat -> Nat) : Prop :=
  forall (width height margin : Nat -> Nat)
    (base : Nat -> Site 2) (a b c d p : Nat -> Real),
    (forall n, 2 * margin n < width n) ->
    (forall n, 2 * margin n < height n) ->
    (forall n, p n <= 1) -> Tendsto p atTop (nhds 1) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V) <=
          E.rectVertices (a n) (b n) (c n) (d n)) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      margin n <= v.1.val -> v.1.val + margin n < width n ->
      margin n <= v.2.val -> v.2.val + margin n < height n ->
      (P.shift (base n + preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n) (b n) (c n) (d n)) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      v.2.val <= margin n -> p n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      height n <= v.2.val + margin n -> p n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      v.1.val <= margin n -> p n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      width n <= v.1.val + margin n -> p n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))
      (mu.real (E.verticalCrossingEvent
        (a n) (b n) (c n) (d n + step n)))) atTop (nhds 1)




structure ExpandedEndpointPrimalBoundaryBandLevel
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (template : Nat -> Finset V) (radius : Nat -> Nat)
    (vLeft vRight vBottom vTop pad : Nat -> Real) where
  width : Nat -> Nat
  height : Nat -> Nat
  margin : Nat -> Nat
  base : Nat -> Site 2
  score : Nat -> Real
  width_separated : forall n, 2 * margin n < width n
  height_separated : forall n, 2 * margin n < height n
  score_le_one : forall n, score n <= 1
  score_tendsto : Tendsto score atTop (nhds 1)
  source_subset : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    ((template n).image
      (P.shift (base n + preferenceGridSite v)) : Set V) <=
        E.rectVertices (vLeft n - pad n) (vRight n + pad n)
          (vBottom n + pad n) (vTop n - pad n)
  connector_subset : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    margin n <= v.1.val -> v.1.val + margin n < width n ->
    margin n <= v.2.val -> v.2.val + margin n < height n ->
    (P.shift (base n + preferenceGridSite v) ''
      (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
        E.rectVertices (vLeft n - pad n) (vRight n + pad n)
          (vBottom n + pad n) (vTop n - pad n)
  bottom : forall n (v : PreferenceGridVertex (width n) (height n)),
    v.2.val <= margin n -> score n <= mu.real
      (E.rectSideConnectionEvent
        (vLeft n - pad n) (vRight n + pad n)
        (vBottom n + pad n) (vTop n - pad n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectBottomBoundaryVertices
          (vLeft n - pad n) (vRight n + pad n)
          (vBottom n + pad n) (vTop n - pad n)))
  top : forall n (v : PreferenceGridVertex (width n) (height n)),
    height n <= v.2.val + margin n -> score n <= mu.real
      (E.rectSideConnectionEvent
        (vLeft n - pad n) (vRight n + pad n)
        (vBottom n + pad n) (vTop n - pad n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectTopBoundaryVertices
          (vLeft n - pad n) (vRight n + pad n)
          (vBottom n + pad n) (vTop n - pad n)))
  left : forall n (v : PreferenceGridVertex (width n) (height n)),
    v.1.val <= margin n -> score n <= mu.real
      (E.rectSideConnectionEvent
        (vLeft n - pad n) (vRight n + pad n)
        (vBottom n + pad n) (vTop n - pad n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectLeftBoundaryVertices
          (vLeft n - pad n) (vRight n + pad n)
          (vBottom n + pad n) (vTop n - pad n)))
  right : forall n (v : PreferenceGridVertex (width n) (height n)),
    width n <= v.1.val + margin n -> score n <= mu.real
      (E.rectSideConnectionEvent
        (vLeft n - pad n) (vRight n + pad n)
        (vBottom n + pad n) (vTop n - pad n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectRightBoundaryVertices
          (vLeft n - pad n) (vRight n + pad n)
          (vBottom n + pad n) (vTop n - pad n)))



theorem ExpandedEndpointPrimalBoundaryBandLevel.primalAdjacent_limit
    {E : PeriodicPlaneEmbedding P}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {template : Nat -> Finset V} {radius : Nat -> Nat}
    {vLeft vRight vBottom vTop pad : Nat -> Real}
    {step : Nat -> Int}
    (level : ExpandedEndpointPrimalBoundaryBandLevel E mu template radius
      vLeft vRight vBottom vTop pad)
    (hcontinuation : E.UniformTemplateAdjacentBoundaryBandCrossingRadius
      mu template step radius) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (vLeft n - pad n) (vRight n + pad n)
        (vBottom n + pad n) (vTop n - pad n)))
      (mu.real (E.verticalCrossingEvent
        (vLeft n - pad n) (vRight n + pad n)
        (vBottom n + pad n) (vTop n - pad n + step n))))
      atTop (nhds 1) := by
  exact hcontinuation level.width level.height level.margin level.base
    (fun n => vLeft n - pad n) (fun n => vRight n + pad n)
    (fun n => vBottom n + pad n) (fun n => vTop n - pad n)
    level.score level.width_separated level.height_separated
    level.score_le_one level.score_tendsto level.source_subset
    level.connector_subset level.bottom level.top level.left level.right



theorem expandedEndpoint_spans_of_inner_gaps
    (B : Real) (hBpos : 0 < B)
    (vLeft vRight vBottom vTop : Nat -> Real)
    (hLeft hRight hBottom hTop pad : Nat -> Real)
    (hpad : forall n, 4 * B <= pad n)
    (hvWidth : forall n, 10 * B < vRight n - vLeft n)
    (hvHeight : forall n, 10 * B < vTop n - vBottom n)
    (hhWidth : forall n, 10 * B < hRight n - hLeft n)
    (hhHeight : forall n, 10 * B < hTop n - hBottom n) :
    (forall n, vLeft n - pad n + 5 * B <
      vRight n + pad n - 5 * B) /\
    (forall n, vBottom n + 5 * B < vTop n - 5 * B) /\
    (forall n, hLeft n + 5 * B < hRight n - 5 * B) /\
    (forall n, hBottom n - pad n + 5 * B <
      hTop n + pad n - 5 * B) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro n
  · nlinarith [hpad n, hvWidth n]
  · nlinarith [hvHeight n]
  · nlinarith [hhWidth n]
  · nlinarith [hpad n, hhHeight n]



theorem ExpandedEndpointPrimalBoundaryBandLevel.false_of_alignedEndpoints
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {template : Nat -> Finset V} {radius : Nat -> Nat}
    {vLeft vRight vBottom vTop pad : Nat -> Real}
    {hLeft hRight hBottom hTop : Nat -> Real}
    {step : Nat -> Int}
    (level : ExpandedEndpointPrimalBoundaryBandLevel D.primalEmbedding mu
      template radius vLeft vRight vBottom vTop pad)
    (hcontinuation :
      D.primalEmbedding.UniformTemplateAdjacentBoundaryBandCrossingRadius
        mu template step radius)
    (halignLeft : forall n, hLeft n + pad n = vLeft n - pad n)
    (halignRight : forall n, hRight n - pad n = vRight n + pad n)
    (halignBottom : forall n, hBottom n - pad n = vBottom n + pad n)
    (halignTop : forall n,
      hTop n + pad n = vTop n - pad n + step n)
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (hpad : forall n, 4 * B <= pad n)
    (hvWidth : forall n, 10 * B < vRight n - vLeft n)
    (hvHeight : forall n, 10 * B < vTop n - vBottom n)
    (hhWidth : forall n, 10 * B < hRight n - hLeft n)
    (hhHeight : forall n, 10 * B < hTop n - hBottom n)
    (hdualVertical : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (vLeft n) (vRight n) (vBottom n) (vTop n)))
      atTop (nhds 1))
    (hdualHorizontal : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (hLeft n) (hRight n) (hBottom n) (hTop n)))
      atTop (nhds 1)) : False := by
  have hprimal0 := level.primalAdjacent_limit hcontinuation
  have hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (vLeft n - pad n) (vRight n + pad n)
        (vBottom n + pad n) (vTop n - pad n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (hLeft n + pad n) (hRight n - pad n)
        (hBottom n - pad n) (hTop n + pad n))))
      atTop (nhds 1) := by
    apply hprimal0.congr'
    filter_upwards [] with n
    simp only [halignLeft n, halignRight n,
      halignBottom n, halignTop n]
  obtain ⟨hspanVX, hspanVY, hspanHX, hspanHY⟩ :=
    expandedEndpoint_spans_of_inner_gaps B hBpos
      vLeft vRight vBottom vTop hLeft hRight hBottom hTop pad hpad
      hvWidth hvHeight hhWidth hhHeight
  exact D.variablePadComplementaryEndpoints_false mu B hBpos hBp hBd
    vLeft vRight vBottom vTop hLeft hRight hBottom hTop pad hpad
    hspanVX hspanVY hspanHX hspanHY hprimal hdualVertical hdualHorizontal



theorem PeriodicPlaneEmbedding.uniformTemplateAdjacentBoundaryBandCrossingRadius_of_deepGrid
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (template : Nat -> Finset V) (step : Nat -> Int)
    (radius : Nat -> Nat)
    (hcross : E.UniformTemplateDeepGridAdjacentHeightCrossingRadius
      mu template step radius) :
    E.UniformTemplateAdjacentBoundaryBandCrossingRadius
      mu template step radius := by
  intro width height margin base a b c d p hwidthSep hheightSep hp hplim
    hsource hconnector hbottom htop hleft hright
  let epsilon : Nat -> Real := fun n => 1 - p n
  let bottom : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Real := fun n v =>
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  let top : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Real := fun n v =>
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))
  let left : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Real := fun n v =>
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  let right : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Real := fun n v =>
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))
  let vertical : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Bool := fun n v =>
    boundaryBandPreferenceColor (margin n) (height n) v.2.val
      (epsilon n) (bottom n v) (top n v)
  let horizontal : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Bool := fun n v =>
    boundaryBandPreferenceColor (margin n) (width n) v.1.val
      (epsilon n) (left n v) (right n v)
  have hepsilon : Tendsto epsilon atTop (nhds 0) := by
    simpa [epsilon] using
      (tendsto_const_nhds (x := (1 : Real))).sub hplim
  apply hcross width height margin
    (fun n => (Nat.zero_le (2 * margin n)).trans_lt (hwidthSep n))
    base vertical horizontal a b c d epsilon bottom top left right hepsilon
  · exact fun n => sub_nonneg.mpr (hp n)
  · exact hsource
  · exact hconnector
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_true_of_lower hv
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_false_of_upper (hheightSep n) hv
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_true_of_lower hv
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_false_of_upper (hwidthSep n) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_true_imp
      (sub_nonneg.mpr (hp n)) (hheightSep n) measureReal_le_one
      (fun h => hbottom n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_false_imp
      (sub_nonneg.mpr (hp n)) (hheightSep n) measureReal_le_one
      (fun h => htop n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_true_imp
      (sub_nonneg.mpr (hp n)) (hwidthSep n) measureReal_le_one
      (fun h => hleft n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_false_imp
      (sub_nonneg.mpr (hp n)) (hwidthSep n) measureReal_le_one
      (fun h => hright n v h) (le_refl _) hv



theorem PeriodicPlaneEmbedding.uniformTemplateAdjacentBoundaryBandCrossingRadius_of_pairMerge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (template : Nat -> Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (step : Nat -> Int) (hstep : forall n, 0 <= step n)
    (radius : Nat -> Nat)
    (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
        ((template n).image (P.shift
          (preferenceKingOffset (q n).2 +
            if (q n).1.val = 0 then 0 else verticalShift (step n))))
        (radius n))) atTop (nhds 0)) :
    E.UniformTemplateAdjacentBoundaryBandCrossingRadius
      mu template step radius := by
  apply E.uniformTemplateAdjacentBoundaryBandCrossingRadius_of_deepGrid
  exact E.uniformTemplateDeepGridAdjacentHeightCrossingRadius_of_pairMerge
    mu hFKG hTI template htemplateHit step hstep radius hmerge



theorem PeriodicPlaneEmbedding.exists_uniformTemplateAdjacentBoundaryBandCrossingRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat -> Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (step : Nat -> Int) (hstep : forall n, 0 <= step n) :
    exists radius, E.UniformTemplateAdjacentBoundaryBandCrossingRadius
      mu template step radius := by
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_deepGrid_adjacentHeight_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit step hstep
  exact ⟨radius,
    E.uniformTemplateAdjacentBoundaryBandCrossingRadius_of_deepGrid
      mu template step radius hcross⟩




theorem PeriodicPlaneEmbedding.exists_uniformTemplateAdjacentBoundaryBandCrossingRadius_with_pairMerge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat -> Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (step : Nat -> Int) (hstep : forall n, 0 <= step n) :
    exists radius : Nat -> Nat,
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
          ((template n).image (P.shift
            (preferenceKingOffset (q n).2 +
              if (q n).1.val = 0 then 0 else verticalShift (step n))))
          (radius n))) atTop (nhds 0)) /\
      E.UniformTemplateAdjacentBoundaryBandCrossingRadius
        mu template step radius := by
  let neighbor : Nat -> (Fin 2 × (Fin 3 × Fin 3)) -> Finset V :=
    fun n q => (template n).image (P.shift
      (preferenceKingOffset q.2 +
        if q.1.val = 0 then 0 else verticalShift (step n)))
  obtain ⟨radius, hradius⟩ :=
    P.exists_uniform_pairMergeRadius mu hunique template neighbor
  have hepsilon : Tendsto (fun n : Nat => (1 : Real) / (n + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hmerge (q : Nat -> Fin 2 × (Fin 3 × Fin 3)) :
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
        ((template n).image (P.shift
          (preferenceKingOffset (q n).2 +
            if (q n).1.val = 0 then 0 else verticalShift (step n))))
        (radius n))) atTop (nhds 0) := by
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => le_of_lt ((hradius n).2 (q n))) hepsilon
  exact ⟨radius, hmerge,
    E.uniformTemplateAdjacentBoundaryBandCrossingRadius_of_pairMerge
      mu hFKG hTI template htemplateHit step hstep radius hmerge⟩



def PeriodicPlaneEmbedding.UniformAdjacentBoundaryBandCrossingRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) (step : Nat -> Int)
    (radius : Nat -> Nat) : Prop :=
  E.UniformTemplateAdjacentBoundaryBandCrossingRadius mu
    (fun n => P.orbitBox n) step radius



theorem PeriodicPlaneEmbedding.exists_uniformAdjacentBoundaryBandRadius_with_cofinalConnectorSchedule
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (step : Nat -> Int) (hstep : forall n, 0 <= step n) :
    exists (radius : Nat -> Nat) (p : Nat -> Real)
      (family : forall m,
        E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)),
      E.UniformAdjacentBoundaryBandCrossingRadius mu step radius /\
      Tendsto p atTop (nhds 1) /\
      forall m, (family m).AlignedMarginSchedule E
        (fun _ => E.connectorMarginRequirement (radius m))
        (fun _ => E.connectorMarginRequirement (radius m)) := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- hunique]
    exact measure_mono fun _ h => h.1
  have hhit := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  obtain ⟨radius, hradius⟩ :=
    E.exists_uniformTemplateAdjacentBoundaryBandCrossingRadius
      mu hFKG hTI hunique (fun n => P.orbitBox n) hhit step hstep
  obtain ⟨p, family, hp, hschedule⟩ :=
    E.exists_cofinalNormalBoundaryBandFamilies_with_connectorSchedule
      mu hFKG hTI hunique radius
  exact ⟨radius, p, family, hradius, hp, hschedule⟩



def PeriodicPlaneEmbedding.UniformOutwardBoundaryCrossingRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) (pad : Nat -> Int)
    (radius : Nat -> Nat) : Prop :=
  forall (width height : Nat -> Nat)
    (hwidth : forall n, 0 < width n)
    (hheight : forall n, 0 < height n)
    (base : Nat -> Site 2) (a b c d p : Nat -> Real),
    Tendsto p atTop (nhds 1) -> (forall n, p n <= 1) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      ((P.orbitBox n).image
        (P.shift (base n + preferenceGridSite v)) : Set V) <=
          E.rectVertices (a n) (b n) (c n) (d n)) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      (P.shift (base n + preferenceGridSite v +
          verticalShift (-(pad n))) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n) (b n)
            (c n - pad n) (d n - pad n)) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      (P.shift (base n + preferenceGridSite v +
          verticalShift (-(pad n))) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n) (b n)
            (c n - pad n) (d n + pad n)) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      (P.shift (base n + preferenceGridSite v +
          horizontalShift (-(pad n))) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n - pad n) (b n - pad n) (c n) (d n)) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      (P.shift (base n + preferenceGridSite v +
          horizontalShift (-(pad n))) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n - pad n) (b n + pad n) (c n) (d n)) ->
    (forall n (i : Fin (width n + 1)), p n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image (P.shift (base n + preferenceGridSite
          (i, (0 : Fin (height n + 1))))) : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n (i : Fin (width n + 1)), p n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image (P.shift (base n + preferenceGridSite
          (i, Fin.last (height n)))) : Set V)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n (j : Fin (height n + 1)), p n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image (P.shift (base n + preferenceGridSite
          ((0 : Fin (width n + 1)), j))) : Set V)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n (j : Fin (height n + 1)), p n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image (P.shift (base n + preferenceGridSite
          (Fin.last (width n), j))) : Set V)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    Tendsto (fun n => max
      (mu.real (E.verticalCrossingEvent
        (a n) (b n) (c n - pad n) (d n + pad n)))
      (mu.real (E.horizontalCrossingEvent
        (a n - pad n) (b n + pad n) (c n) (d n))))
      atTop (nhds 1)


theorem PeriodicPlaneEmbedding.exists_uniformOutwardBoundaryCrossingRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (pad : Nat -> Int) (hpad : forall n, 0 <= pad n) :
    exists radius,
      E.UniformOutwardBoundaryCrossingRadius mu pad radius := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- hunique]
    exact measure_mono fun _ h => h.1
  have hhit := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_outwardBoundaryScores_crossing_max_tendsto_one
      mu hFKG hTI hunique (fun n => P.orbitBox n) hhit pad hpad
  exact ⟨radius, hcross⟩




structure PairedAdjacentBoundaryBandScheduleData
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W))) (step : Nat -> Int) where
  step_nonneg : forall n, 0 <= step n
  radius : Nat -> Nat
  radiusDual : Nat -> Nat
  score : Nat -> Real
  scoreDual : Nat -> Real
  family : forall m,
    E.NormalBoundaryBandFamily mu (P.orbitBox m) (score m)
  familyDual : forall m,
    Edual.NormalBoundaryBandFamily muDual
      (Pdual.orbitBox m) (scoreDual m)
  primalContinuation :
    E.UniformAdjacentBoundaryBandCrossingRadius mu step radius
  primalMerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
    Tendsto (fun n => mu.real (P.pairMergeErrorUnion (P.orbitBox n)
      ((P.orbitBox n).image (P.shift
        (preferenceKingOffset (q n).2 +
          if (q n).1.val = 0 then 0 else verticalShift (step n))))
      (radius n))) atTop (nhds 0)
  dualContinuation : Edual.UniformBoundaryBandCrossingRadius
    muDual radiusDual
  score_tendsto : Tendsto score atTop (nhds 1)
  score_le_one : forall m, score m <= 1
  scoreDual_tendsto : Tendsto scoreDual atTop (nhds 1)
  scoreDual_le_one : forall m, scoreDual m <= 1
  schedule : forall m, PairedAlignedMarginSchedule E Edual
    (family m) (familyDual m)
    (fun _ => max
      (E.connectorMarginRequirement (radius m))
      (Edual.connectorMarginRequirement (radiusDual m)))
    (fun _ => max
      (E.connectorMarginRequirement (radius m))
      (Edual.connectorMarginRequirement (radiusDual m)))



theorem exists_pairedAdjacentBoundaryBandScheduleData
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (step : Nat -> Int) (hstep : forall n, 0 <= step n) :
    Nonempty (PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step) := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- hunique]
    exact measure_mono fun _ h => h.1
  have hhit := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  obtain ⟨radius, hmerge, hprimal⟩ :=
    E.exists_uniformTemplateAdjacentBoundaryBandCrossingRadius_with_pairMerge
      mu hFKG hTI hunique (fun n => P.orbitBox n) hhit step hstep
  obtain ⟨radiusDual, hdual⟩ :=
    Edual.exists_uniformRadius_boundaryBandScores_crossing_max_tendsto_one
      muDual hFKGDual hTIDual huniqueDual
  obtain ⟨score, scoreDual, family, familyDual,
      hscore, hscore_le, hscoreDual, hscoreDual_le⟩ :=
    exists_pairedCofinalNormalBoundaryBandFamilies_bounded
      E Edual mu muDual hFKG hTI hunique
        hFKGDual hTIDual huniqueDual
  let requirement : Nat -> Nat := fun m => max
    (E.connectorMarginRequirement (radius m))
    (Edual.connectorMarginRequirement (radiusDual m))
  let schedule : forall m, PairedAlignedMarginSchedule E Edual
      (family m) (familyDual m) (fun _ => requirement m)
        (fun _ => requirement m) := fun m =>
    Classical.choice (exists_pairedAlignedMarginSchedule E Edual
      (family m) (familyDual m) (fun _ => requirement m)
        (fun _ => requirement m))
  refine ⟨{
    step_nonneg := hstep
    radius := radius
    radiusDual := radiusDual
    score := score
    scoreDual := scoreDual
    family := family
    familyDual := familyDual
    primalContinuation := ?_
    primalMerge := hmerge
    dualContinuation := ?_
    score_tendsto := hscore
    score_le_one := hscore_le
    scoreDual_tendsto := hscoreDual
    scoreDual_le_one := hscoreDual_le
    schedule := schedule }⟩
  · simpa [PeriodicPlaneEmbedding.UniformAdjacentBoundaryBandCrossingRadius]
      using hprimal
  · exact hdual





theorem PeriodicPlanarDualPair.exists_canonicalPairedAdjacentBoundaryBandScheduleData_of_common
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hcommon :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1)
    (step : Nat -> Int) (hstep : forall n, 0 <= step n) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    Nonempty (PairedAdjacentBoundaryBandScheduleData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) step) := by
  dsimp only
  letI : IsProbabilityMeasure
      (D.dualMeasure
        (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V)))) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  have hdata := D.freeBufferedInfiniteVolume_sheffieldData_of_common
    hp hp1 hq hcommon
  exact exists_pairedAdjacentBoundaryBandScheduleData
    D.primalEmbedding D.dualEmbedding _ _
      hdata.1 hdata.2.1 hdata.2.2.2.2.1
      hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.2 step hstep



structure PairedAdjacentOutwardScheduleData
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (step : Nat -> Int) (pad : Nat -> Int) where
  base : PairedAdjacentBoundaryBandScheduleData
    E Edual mu muDual step
  outwardRadiusDual : Nat -> Nat
  outwardContinuationDual :
    Edual.UniformOutwardBoundaryCrossingRadius
      muDual pad outwardRadiusDual
  schedule : forall m, PairedAlignedMarginSchedule E Edual
    (base.family m) (base.familyDual m)
    (fun _ => max
      (E.connectorMarginRequirement (base.radius m))
      (Edual.connectorMarginRequirement (outwardRadiusDual m)))
    (fun _ => max
      (E.connectorMarginRequirement (base.radius m))
      (Edual.connectorMarginRequirement (outwardRadiusDual m)))



theorem exists_pairedAdjacentOutwardScheduleData
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (step : Nat -> Int) (hstep : forall n, 0 <= step n)
    (pad : Nat -> Int) (hpad : forall n, 0 <= pad n) :
    Nonempty (PairedAdjacentOutwardScheduleData
      E Edual mu muDual step pad) := by
  let base := Classical.choice
    (exists_pairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual hFKG hTI hunique hFKGDual hTIDual huniqueDual
        step hstep)
  obtain ⟨outwardRadiusDual, houtward⟩ :=
    Edual.exists_uniformOutwardBoundaryCrossingRadius
      muDual hFKGDual hTIDual huniqueDual pad hpad
  let requirement : Nat -> Nat := fun m => max
    (E.connectorMarginRequirement (base.radius m))
    (Edual.connectorMarginRequirement (outwardRadiusDual m))
  let schedule : forall m, PairedAlignedMarginSchedule E Edual
      (base.family m) (base.familyDual m)
      (fun _ => requirement m) (fun _ => requirement m) := fun m =>
    Classical.choice (exists_pairedAlignedMarginSchedule E Edual
      (base.family m) (base.familyDual m)
      (fun _ => requirement m) (fun _ => requirement m))
  exact ⟨{
    base := base
    outwardRadiusDual := outwardRadiusDual
    outwardContinuationDual := houtward
    schedule := schedule }⟩




theorem PeriodicPlanarDualPair.exists_canonicalPairedAdjacentOutwardScheduleData_of_common
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hcommon :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1)
    (step : Nat -> Int) (hstep : forall n, 0 <= step n)
    (pad : Nat -> Int) (hpad : forall n, 0 <= pad n) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    Nonempty (PairedAdjacentOutwardScheduleData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) step pad) := by
  dsimp only
  letI : IsProbabilityMeasure
      (D.dualMeasure
        (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V)))) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  have hdata := D.freeBufferedInfiniteVolume_sheffieldData_of_common
    hp hp1 hq hcommon
  exact exists_pairedAdjacentOutwardScheduleData
    D.primalEmbedding D.dualEmbedding _ _
      hdata.1 hdata.2.1 hdata.2.2.2.2.1
      hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.2
      step hstep pad hpad



structure DualOutwardBoundaryBandLevel
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {step pad : Nat -> Int}
    (data : PairedAdjacentOutwardScheduleData
      E Edual mu muDual step pad) where
  a : Nat -> Real
  b : Nat -> Real
  c : Nat -> Real
  d : Nat -> Real
  width : Nat -> Nat
  height : Nat -> Nat
  base : Nat -> Site 2
  width_pos : forall n, 0 < width n
  height_pos : forall n, 0 < height n
  source_subset : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    ((Pdual.orbitBox n).image
      (Pdual.shift (base n + preferenceGridSite v)) : Set W) <=
        Edual.rectVertices (a n) (b n) (c n) (d n)
  connector_vertical_lower : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    (Pdual.shift (base n + preferenceGridSite v +
        verticalShift (-(pad n))) ''
      (Pdual.orbitBox (Pdual.bufferedRadius
        (data.outwardRadiusDual n)) : Set W)) <=
      Edual.rectVertices (a n) (b n)
        (c n - pad n) (d n - pad n)
  connector_vertical_outer : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    (Pdual.shift (base n + preferenceGridSite v +
        verticalShift (-(pad n))) ''
      (Pdual.orbitBox (Pdual.bufferedRadius
        (data.outwardRadiusDual n)) : Set W)) <=
      Edual.rectVertices (a n) (b n)
        (c n - pad n) (d n + pad n)
  connector_horizontal_lower : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    (Pdual.shift (base n + preferenceGridSite v +
        horizontalShift (-(pad n))) ''
      (Pdual.orbitBox (Pdual.bufferedRadius
        (data.outwardRadiusDual n)) : Set W)) <=
      Edual.rectVertices (a n - pad n) (b n - pad n) (c n) (d n)
  connector_horizontal_outer : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    (Pdual.shift (base n + preferenceGridSite v +
        horizontalShift (-(pad n))) ''
      (Pdual.orbitBox (Pdual.bufferedRadius
        (data.outwardRadiusDual n)) : Set W)) <=
      Edual.rectVertices (a n - pad n) (b n + pad n) (c n) (d n)
  bottom : forall n (i : Fin (width n + 1)),
    data.base.scoreDual n <= muDual.real
      (Edual.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((Pdual.orbitBox n).image
          (Pdual.shift (base n + preferenceGridSite
            (i, (0 : Fin (height n + 1))))) : Set W)
        (Edual.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  top : forall n (i : Fin (width n + 1)),
    data.base.scoreDual n <= muDual.real
      (Edual.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((Pdual.orbitBox n).image
          (Pdual.shift (base n + preferenceGridSite
            (i, Fin.last (height n)))) : Set W)
        (Edual.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))
  left : forall n (j : Fin (height n + 1)),
    data.base.scoreDual n <= muDual.real
      (Edual.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((Pdual.orbitBox n).image
          (Pdual.shift (base n + preferenceGridSite
            ((0 : Fin (width n + 1)), j))) : Set W)
        (Edual.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  right : forall n (j : Fin (height n + 1)),
    data.base.scoreDual n <= muDual.real
      (Edual.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((Pdual.orbitBox n).image
          (Pdual.shift (base n + preferenceGridSite
            (Fin.last (width n), j))) : Set W)
        (Edual.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))


theorem DualOutwardBoundaryBandLevel.crossing_limit
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {step pad : Nat -> Int}
    (data : PairedAdjacentOutwardScheduleData
      E Edual mu muDual step pad)
    (level : DualOutwardBoundaryBandLevel data) :
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        (level.a n) (level.b n)
        (level.c n - pad n) (level.d n + pad n)))
      (muDual.real (Edual.horizontalCrossingEvent
        (level.a n - pad n) (level.b n + pad n)
        (level.c n) (level.d n)))) atTop (nhds 1) := by
  exact data.outwardContinuationDual level.width level.height
    level.width_pos level.height_pos level.base
    level.a level.b level.c level.d data.base.scoreDual
    data.base.scoreDual_tendsto data.base.scoreDual_le_one
    level.source_subset level.connector_vertical_lower
    level.connector_vertical_outer level.connector_horizontal_lower
    level.connector_horizontal_outer level.bottom level.top
    level.left level.right



structure PairedBoundaryBandLevel
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {step : Nat -> Int}
    (data : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step) where
  a : Nat -> Real
  b : Nat -> Real
  c : Nat -> Real
  d : Nat -> Real
  width : Nat -> Nat
  height : Nat -> Nat
  margin : Nat -> Nat
  base : Nat -> Site 2
  widthDual : Nat -> Nat
  heightDual : Nat -> Nat
  marginDual : Nat -> Nat
  baseDual : Nat -> Site 2
  width_separated : forall n, 2 * margin n < width n
  height_separated : forall n, 2 * margin n < height n
  widthDual_separated : forall n, 2 * marginDual n < widthDual n
  heightDual_separated : forall n, 2 * marginDual n < heightDual n
  primal_source_subset : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    (((P.orbitBox n).image
      (P.shift (base n + preferenceGridSite v)) : Finset V) : Set V) <=
        E.rectVertices (a n) (b n) (c n) (d n)
  primal_connector_subset : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    margin n <= v.1.val -> v.1.val + margin n < width n ->
    margin n <= v.2.val -> v.2.val + margin n < height n ->
    (P.shift (base n + preferenceGridSite v) ''
      (P.orbitBox (P.bufferedRadius (data.radius n)) : Set V)) <=
        E.rectVertices (a n) (b n) (c n) (d n)
  primal_bottom : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    v.2.val <= margin n -> data.score n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  primal_top : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    height n <= v.2.val + margin n -> data.score n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))
  primal_left : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    v.1.val <= margin n -> data.score n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  primal_right : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    width n <= v.1.val + margin n -> data.score n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))
  dual_source_subset : forall n
      (v : PreferenceGridVertex (widthDual n) (heightDual n)),
    (((Pdual.orbitBox n).image
      (Pdual.shift (baseDual n + preferenceGridSite v)) : Finset W) :
        Set W) <= Edual.rectVertices (a n) (b n) (c n) (d n)
  dual_connector_subset : forall n
      (v : PreferenceGridVertex (widthDual n) (heightDual n)),
    marginDual n <= v.1.val ->
    v.1.val + marginDual n < widthDual n ->
    marginDual n <= v.2.val ->
    v.2.val + marginDual n < heightDual n ->
    (Pdual.shift (baseDual n + preferenceGridSite v) ''
      (Pdual.orbitBox
        (Pdual.bufferedRadius (data.radiusDual n)) : Set W)) <=
          Edual.rectVertices (a n) (b n) (c n) (d n)
  dual_bottom : forall n
      (v : PreferenceGridVertex (widthDual n) (heightDual n)),
    v.2.val <= marginDual n -> data.scoreDual n <= muDual.real
      (Edual.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((Pdual.orbitBox n).image
          (Pdual.shift (baseDual n + preferenceGridSite v)) : Set W)
        (Edual.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  dual_top : forall n
      (v : PreferenceGridVertex (widthDual n) (heightDual n)),
    heightDual n <= v.2.val + marginDual n ->
      data.scoreDual n <= muDual.real
      (Edual.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((Pdual.orbitBox n).image
          (Pdual.shift (baseDual n + preferenceGridSite v)) : Set W)
        (Edual.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))
  dual_left : forall n
      (v : PreferenceGridVertex (widthDual n) (heightDual n)),
    v.1.val <= marginDual n -> data.scoreDual n <= muDual.real
      (Edual.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((Pdual.orbitBox n).image
          (Pdual.shift (baseDual n + preferenceGridSite v)) : Set W)
        (Edual.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  dual_right : forall n
      (v : PreferenceGridVertex (widthDual n) (heightDual n)),
    widthDual n <= v.1.val + marginDual n ->
      data.scoreDual n <= muDual.real
      (Edual.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((Pdual.orbitBox n).image
          (Pdual.shift (baseDual n + preferenceGridSite v)) : Set W)
        (Edual.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))



theorem PairedBoundaryBandLevel.primalAdjacent_limit
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {step : Nat -> Int}
    (data : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step) (level : PairedBoundaryBandLevel data) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (level.a n) (level.b n) (level.c n) (level.d n)))
      (mu.real (E.verticalCrossingEvent
        (level.a n) (level.b n) (level.c n)
          (level.d n + step n)))) atTop (nhds 1) := by
  exact data.primalContinuation level.width level.height level.margin
    level.base level.a level.b level.c level.d data.score
    level.width_separated level.height_separated data.score_le_one
    data.score_tendsto level.primal_source_subset
    level.primal_connector_subset level.primal_bottom level.primal_top
    level.primal_left level.primal_right



theorem PairedBoundaryBandLevel.dual_limit
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {step : Nat -> Int}
    (data : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step) (level : PairedBoundaryBandLevel data) :
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        (level.a n) (level.b n) (level.c n) (level.d n)))
      (muDual.real (Edual.horizontalCrossingEvent
        (level.a n) (level.b n) (level.c n) (level.d n))))
      atTop (nhds 1) := by
  exact data.dualContinuation level.widthDual level.heightDual
    level.marginDual level.baseDual level.a level.b level.c level.d
    data.scoreDual level.widthDual_separated level.heightDual_separated
    data.scoreDual_le_one data.scoreDual_tendsto
    level.dual_source_subset level.dual_connector_subset
    level.dual_bottom level.dual_top level.dual_left level.dual_right



structure PairedAdjacentBoundaryBandTransition
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {step : Nat -> Int}
    (data : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step) where
  lower : PairedBoundaryBandLevel data
  upper : PairedBoundaryBandLevel data
  upper_a : upper.a = lower.a
  upper_b : upper.b = lower.b
  upper_c : upper.c = lower.c
  upper_d : upper.d = fun n => lower.d n + step n




theorem PairedAdjacentBoundaryBandTransition.local_limits
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {step : Nat -> Int}
    (data : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step)
    (transition : PairedAdjacentBoundaryBandTransition data) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)))
      (mu.real (E.verticalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n))))
      atTop (nhds 1) /\
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)))
      (muDual.real (Edual.horizontalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n))))
      atTop (nhds 1) /\
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n)))
      (muDual.real (Edual.horizontalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n))))
      atTop (nhds 1) := by
  refine ⟨?_, transition.lower.dual_limit data,
    transition.upper.dual_limit data⟩
  simpa only [transition.upper_a, transition.upper_b,
    transition.upper_c, transition.upper_d] using
      transition.lower.primalAdjacent_limit data




theorem PairedAdjacentBoundaryBandTransition.false_of_endpoints_and_matched
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual] {step : Nat -> Int}
    (data : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step)
    (transition : PairedAdjacentBoundaryBandTransition data)
    (hverticalStart : Tendsto (fun n => mu.real
      (E.verticalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)))
      atTop (nhds 1))
    (hhorizontalEnd : Tendsto (fun n => mu.real
      (E.horizontalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n)))
      atTop (nhds 1))
    (hmatchHorizontalLower : forall n,
      mu.real (E.horizontalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)) +
      muDual.real (Edual.verticalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)) <= 1)
    (hmatchVerticalLower : forall n,
      mu.real (E.verticalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)) +
      muDual.real (Edual.horizontalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)) <= 1)
    (hmatchHorizontalUpper : forall n,
      mu.real (E.horizontalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n)) +
      muDual.real (Edual.verticalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n)) <= 1)
    (hmatchVerticalUpper : forall n,
      mu.real (E.verticalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n)) +
      muDual.real (Edual.horizontalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n)) <= 1) : False := by
  let horizontal : Nat -> Nat -> Real := fun n k =>
    if k = 0 then mu.real (E.horizontalCrossingEvent
      (transition.lower.a n) (transition.lower.b n)
      (transition.lower.c n) (transition.lower.d n))
    else mu.real (E.horizontalCrossingEvent
      (transition.upper.a n) (transition.upper.b n)
      (transition.upper.c n) (transition.upper.d n))
  let vertical : Nat -> Nat -> Real := fun n k =>
    if k = 0 then mu.real (E.verticalCrossingEvent
      (transition.lower.a n) (transition.lower.b n)
      (transition.lower.c n) (transition.lower.d n))
    else mu.real (E.verticalCrossingEvent
      (transition.upper.a n) (transition.upper.b n)
      (transition.upper.c n) (transition.upper.d n))
  let dualVertical : Nat -> Nat -> Real := fun n k =>
    if k = 0 then muDual.real (Edual.verticalCrossingEvent
      (transition.lower.a n) (transition.lower.b n)
      (transition.lower.c n) (transition.lower.d n))
    else muDual.real (Edual.verticalCrossingEvent
      (transition.upper.a n) (transition.upper.b n)
      (transition.upper.c n) (transition.upper.d n))
  let dualHorizontal : Nat -> Nat -> Real := fun n k =>
    if k = 0 then muDual.real (Edual.horizontalCrossingEvent
      (transition.lower.a n) (transition.lower.b n)
      (transition.lower.c n) (transition.lower.d n))
    else muDual.real (Edual.horizontalCrossingEvent
      (transition.upper.a n) (transition.upper.b n)
      (transition.upper.c n) (transition.upper.d n))
  obtain ⟨hprimal, hdualLower, hdualUpper⟩ :=
    transition.local_limits data
  apply adjacent_height_array_contradiction_of_primal_dual_limits
    horizontal vertical dualVertical dualHorizontal (fun _ => 0)
    (fun n k => by
      by_cases hk : k = 0 <;> simp [horizontal, hk, measureReal_nonneg])
    (fun n k => by
      by_cases hk : k = 0 <;> simp [vertical, hk, measureReal_nonneg])
    (fun n k => by
      by_cases hk : k = 0 <;> simp [horizontal, hk, measureReal_le_one])
    (fun n k => by
      by_cases hk : k = 0 <;> simp [vertical, hk, measureReal_le_one])
  · simpa only [vertical, if_pos] using hverticalStart
  · simpa only [horizontal, Nat.zero_add, if_false, one_ne_zero] using
      hhorizontalEnd
  · intro n k
    by_cases hk : k = 0
    · simpa [horizontal, dualVertical, hk] using hmatchHorizontalLower n
    · simpa [horizontal, dualVertical, hk] using hmatchHorizontalUpper n
  · intro n k
    by_cases hk : k = 0
    · simpa [vertical, dualHorizontal, hk] using hmatchVerticalLower n
    · simpa [vertical, dualHorizontal, hk] using hmatchVerticalUpper n
  · intro k hk
    have hk0 : forall n, k n = 0 := by
      intro n
      have := hk n
      omega
    simpa only [horizontal, vertical, hk0, if_pos, Nat.zero_add,
      if_false, one_ne_zero] using hprimal
  · intro k
    let lower : Nat -> Real := fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)))
      (muDual.real (Edual.horizontalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)))
    let upper : Nat -> Real := fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n)))
      (muDual.real (Edual.horizontalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n)))
    have hlower : Tendsto lower atTop (nhds 1) := by
      simpa only [lower] using hdualLower
    have hupper : Tendsto upper atTop (nhds 1) := by
      simpa only [upper] using hdualUpper
    have hmin : Tendsto (fun n => min (lower n) (upper n))
        atTop (nhds 1) := by
      simpa only [min_self] using hlower.min hupper
    apply hmin.squeeze tendsto_const_nhds
    · intro n
      by_cases hk : k n = 0
      · simpa only [dualVertical, dualHorizontal, hk, if_pos, lower] using
          (min_le_left (lower n) (upper n))
      · simpa only [dualVertical, dualHorizontal, hk, if_neg, upper] using
          (min_le_right (lower n) (upper n))
    · intro n
      by_cases hk : k n = 0
      · simp only [dualVertical, dualHorizontal, hk, if_pos]
        exact max_le measureReal_le_one measureReal_le_one
      · simp only [dualVertical, dualHorizontal, hk, if_neg]
        exact max_le measureReal_le_one measureReal_le_one




structure PeriodicPlanarDualPair.PaddedPairedAdjacentTransition
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    {step pad : Nat -> Int}
    (data : PairedAdjacentOutwardScheduleData D.primalEmbedding
      D.dualEmbedding mu (D.dualMeasure mu) step pad) where
  primal : PairedAdjacentBoundaryBandTransition data.base
  dualLower : DualOutwardBoundaryBandLevel data
  dualUpper : DualOutwardBoundaryBandLevel data
  a0 : Nat -> Real
  b0 : Nat -> Real
  c0 : Nat -> Real
  d0 : Nat -> Real
  a1 : Nat -> Real
  b1 : Nat -> Real
  c1 : Nat -> Real
  d1 : Nat -> Real
  primalLower_a : primal.lower.a = a0
  primalLower_b : primal.lower.b = b0
  primalLower_c : primal.lower.c = fun n => c0 n + (pad n : Real)
  primalLower_d : primal.lower.d = fun n => d0 n - (pad n : Real)
  primalUpper_a : primal.upper.a = fun n => a1 n + (pad n : Real)
  primalUpper_b : primal.upper.b = fun n => b1 n - (pad n : Real)
  primalUpper_c : primal.upper.c = c1
  primalUpper_d : primal.upper.d = d1
  dualLower_a : dualLower.a = fun n => a0 n + (pad n : Real)
  dualLower_b : dualLower.b = fun n => b0 n - (pad n : Real)
  dualLower_c : dualLower.c = fun n => c0 n + (pad n : Real)
  dualLower_d : dualLower.d = fun n => d0 n - (pad n : Real)
  dualUpper_a : dualUpper.a = fun n => a1 n + (pad n : Real)
  dualUpper_b : dualUpper.b = fun n => b1 n - (pad n : Real)
  dualUpper_c : dualUpper.c = fun n => c1 n + (pad n : Real)
  dualUpper_d : dualUpper.d = fun n => d1 n - (pad n : Real)
  verticalStart : Tendsto (fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a0 n + pad n) (b0 n - pad n) (c0 n) (d0 n)))
    atTop (nhds 1)
  horizontalEnd : Tendsto (fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a1 n) (b1 n) (c1 n + pad n) (d1 n - pad n)))
    atTop (nhds 1)




theorem PeriodicPlanarDualPair.PaddedPairedAdjacentTransition.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {step pad : Nat -> Int}
    (data : PairedAdjacentOutwardScheduleData D.primalEmbedding
      D.dualEmbedding mu (D.dualMeasure mu) step pad)
    (transition : D.PaddedPairedAdjacentTransition mu data)
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (hpad : forall n, 4 * B <= (pad n : Real))
    (hspanX0 : forall n, transition.a0 n + 5 * B <
      transition.b0 n - 5 * B)
    (hspanY0 : forall n, transition.c0 n + 5 * B <
      transition.d0 n - 5 * B)
    (hspanX1 : forall n, transition.a1 n + 5 * B <
      transition.b1 n - 5 * B)
    (hspanY1 : forall n, transition.c1 n + 5 * B <
      transition.d1 n - 5 * B) : False := by
  let padReal : Nat -> Real := fun n => pad n
  have hprimal := (transition.primal.local_limits data.base).1
  have hprimal' : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (transition.a0 n) (transition.b0 n)
        (transition.c0 n + padReal n) (transition.d0 n - padReal n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (transition.a1 n + padReal n) (transition.b1 n - padReal n)
        (transition.c1 n) (transition.d1 n)))) atTop (nhds 1) := by
    simpa only [padReal, transition.primalLower_a,
      transition.primalLower_b, transition.primalLower_c,
      transition.primalLower_d, transition.primalUpper_a,
      transition.primalUpper_b, transition.primalUpper_c,
      transition.primalUpper_d] using hprimal
  have hdualLower := transition.dualLower.crossing_limit data
  have hdualLower' : Tendsto (fun n => max
      ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
        (transition.a0 n + padReal n) (transition.b0 n - padReal n)
        (transition.c0 n) (transition.d0 n)))
      ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
        (transition.a0 n) (transition.b0 n)
        (transition.c0 n + padReal n) (transition.d0 n - padReal n))))
      atTop (nhds 1) := by
    simpa only [padReal, transition.dualLower_a,
      transition.dualLower_b, transition.dualLower_c,
      transition.dualLower_d, add_sub_cancel_right, sub_add_cancel]
      using hdualLower
  have hdualUpper := transition.dualUpper.crossing_limit data
  have hdualUpper' : Tendsto (fun n => max
      ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
        (transition.a1 n + padReal n) (transition.b1 n - padReal n)
        (transition.c1 n) (transition.d1 n)))
      ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
        (transition.a1 n) (transition.b1 n)
        (transition.c1 n + padReal n) (transition.d1 n - padReal n))))
      atTop (nhds 1) := by
    simpa only [padReal, transition.dualUpper_a,
      transition.dualUpper_b, transition.dualUpper_c,
      transition.dualUpper_d, add_sub_cancel_right, sub_add_cancel]
      using hdualUpper
  obtain ⟨hdual0, hdual1⟩ := D.dualMeasure_twoLevel_outward_limits mu
    transition.a0 transition.b0 transition.c0 transition.d0
    transition.a1 transition.b1 transition.c1 transition.d1
    padReal padReal padReal padReal hdualLower' hdualUpper'
  apply D.variablePadTwoLevel_false_of_normal_rotated_limits mu B hBpos
    hBp hBd transition.a0 transition.b0 transition.c0 transition.d0
    transition.a1 transition.b1 transition.c1 transition.d1
    padReal padReal padReal padReal hpad hpad hpad hpad
    hspanX0 hspanY0 hspanX1 hspanY1
  · simpa only [padReal] using transition.verticalStart
  · simpa only [padReal] using transition.horizontalEnd
  · exact hprimal'
  · exact hdual0
  · exact hdual1





theorem PeriodicPlaneEmbedding.deepPreferenceGrid_orbitBox_subset_rect
    (E : PeriodicPlaneEmbedding P) (R M width height margin : Nat)
    (hx : E.orbitBoxCoordinateBound R (0 : Fin 2) <= M + margin)
    (hy : E.orbitBoxCoordinateBound R (1 : Fin 2) <= M + margin)
    (v : PreferenceGridVertex width height)
    (hvLeft : margin <= v.1.val)
    (hvRight : v.1.val + margin < width)
    (hvBottom : margin <= v.2.val)
    (hvTop : v.2.val + margin < height) :
    P.shift (preferenceGridSite v) '' (P.orbitBox R : Set V) <=
      E.rectVertices (-(M : Real)) (M + width : Real)
        (-(M : Real)) (M + height : Real) := by
  rintro _ ⟨u, hu, rfl⟩
  have hu0 := E.abs_vertexCoord_le_orbitBoxCoordinateBound hu (0 : Fin 2)
  have hu1 := E.abs_vertexCoord_le_orbitBoxCoordinateBound hu (1 : Fin 2)
  rw [abs_le] at hu0 hu1
  have hxR : E.orbitBoxCoordinateBound R (0 : Fin 2) <=
      (M + margin : Real) := by exact_mod_cast hx
  have hyR : E.orbitBoxCoordinateBound R (1 : Fin 2) <=
      (M + margin : Real) := by exact_mod_cast hy
  have hleftR : (margin : Real) <= v.1.val := by exact_mod_cast hvLeft
  have hrightR : (v.1.val : Real) + margin < width := by
    exact_mod_cast hvRight
  have hbottomR : (margin : Real) <= v.2.val := by
    exact_mod_cast hvBottom
  have htopR : (v.2.val : Real) + margin < height := by
    exact_mod_cast hvTop
  change (-(M : Real) <=
      E.vertexCoord (P.shift (preferenceGridSite v) u) 0 /\
    E.vertexCoord (P.shift (preferenceGridSite v) u) 0 <= M + width /\
    -(M : Real) <= E.vertexCoord (P.shift (preferenceGridSite v) u) 1 /\
    E.vertexCoord (P.shift (preferenceGridSite v) u) 1 <= M + height)
  simp only [E.vertexCoord_shift]
  simp only [preferenceGridSite, Pi.add_apply, Int.cast_natCast]
  constructor
  · linarith [hu0.1]
  constructor
  · linarith [hu0.2]
  constructor
  · linarith [hu1.1]
  · linarith [hu1.2]







theorem PeriodicPlaneEmbedding.exists_coupled_endpointCrossings_tendsto_one_of_unique
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r y B s : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (t : Int) (ht : 3 * B < t)
    (minimumWidth minimumHeight : Nat -> Nat)
    (hminimumWidth : forall n,
      3 * B < 3 * (minimumWidth n : Real)) :
    exists width height : Nat -> Nat,
      (forall n, minimumWidth n <= width n) /\
      (forall n, minimumHeight n <= height n) /\
      Tendsto (fun n => mu.real (E.verticalCrossingEvent
        r (r + width n)
        ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)))
        atTop (nhds 1) /\
      Tendsto (fun n => mu.real (E.horizontalCrossingEvent
        r (r + width n) y (y + height n))) atTop (nhds 1) := by
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  choose width hwidth hvertical using fun n =>
    E.exists_verticalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique r B s hB0 hB t ht (minimumWidth n)
        (hepsilon n)
  have hwidthB (n : Nat) : 3 * B < 3 * (width n : Real) := by
    exact (hminimumWidth n).trans_le (by
      gcongr
      exact_mod_cast hwidth n)
  let horizontalS : Nat -> Real := fun n => r - width n
  let horizontalT : Nat -> Int := fun n => 3 * (width n : Int)
  have hhorizontalT (n : Nat) : 3 * B < horizontalT n := by
    dsimp only [horizontalT]
    exact_mod_cast hwidthB n
  choose height hheight hhorizontal using fun n =>
    E.exists_horizontalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique y B (horizontalS n) hB0 hB
        (horizontalT n) (hhorizontalT n) (minimumHeight n) (hepsilon n)
  have hlower : Tendsto (fun n => 1 - epsilon n) atTop (nhds 1) := by
    have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
      simpa only [epsilon] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilonZero
  have hverticalLimit : Tendsto (fun n => mu.real
      (E.verticalCrossingEvent r (r + width n)
        ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)))
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (hvertical n)) (fun _ => measureReal_le_one)
  have hhorizontalLimit : Tendsto (fun n => mu.real
      (E.horizontalCrossingEvent r (r + width n) y (y + height n)))
      atTop (nhds 1) := by
    have hlowerHorizontal : forall n, 1 - epsilon n < mu.real
        (E.horizontalCrossingEvent r (r + width n) y (y + height n)) := by
      intro n
      convert hhorizontal n using 1 <;>
        simp only [horizontalS, horizontalT, Int.cast_mul,
          Int.cast_ofNat, Int.cast_natCast] <;> ring
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower tendsto_const_nhds (fun n => le_of_lt (hlowerHorizontal n))
        (fun _ => measureReal_le_one)
  exact ⟨width, height, hwidth, hheight,
    hverticalLimit, hhorizontalLimit⟩






theorem PeriodicPlaneEmbedding.exists_dependentSpan_endpointCrossings_tendsto_one_of_unique
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r y B s : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (t : Int) (ht : 3 * B < t)
    (minimumWidth minimumHeight : Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Nat -> Int)
    (hhorizontalSpan : forall n w, minimumWidth n <= w ->
      3 * B < horizontalRight n w - horizontalLeft n w) :
    exists width height : Nat -> Nat,
      (forall n, minimumWidth n <= width n) /\
      (forall n, minimumHeight n <= height n) /\
      Tendsto (fun n => mu.real (E.verticalCrossingEvent
        r (r + width n)
        ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)))
        atTop (nhds 1) /\
      Tendsto (fun n => mu.real (E.horizontalCrossingEvent
        (horizontalLeft n (width n)) (horizontalRight n (width n))
        y (y + height n))) atTop (nhds 1) := by
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  choose width hwidth hvertical using fun n =>
    E.exists_verticalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique r B s hB0 hB t ht (minimumWidth n)
        (hepsilon n)
  let horizontalS : Nat -> Real := fun n =>
    2 * horizontalLeft n (width n) - horizontalRight n (width n)
  let horizontalT : Nat -> Int := fun n =>
    3 * (horizontalRight n (width n) - horizontalLeft n (width n))
  have hhorizontalT (n : Nat) : 3 * B < horizontalT n := by
    have hspan := hhorizontalSpan n (width n) (hwidth n)
    rw [show (horizontalT n : Real) =
        3 * ((horizontalRight n (width n) : Real) -
          horizontalLeft n (width n)) by
      simp only [horizontalT, Int.cast_mul, Int.cast_ofNat, Int.cast_sub]]
    nlinarith
  choose height hheight hhorizontal using fun n =>
    E.exists_horizontalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique y B (horizontalS n) hB0 hB
        (horizontalT n) (hhorizontalT n) (minimumHeight n) (hepsilon n)
  have hlower : Tendsto (fun n => 1 - epsilon n) atTop (nhds 1) := by
    have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
      simpa only [epsilon] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilonZero
  have hverticalLimit : Tendsto (fun n => mu.real
      (E.verticalCrossingEvent r (r + width n)
        ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)))
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (hvertical n)) (fun _ => measureReal_le_one)
  have hhorizontalLimit : Tendsto (fun n => mu.real
      (E.horizontalCrossingEvent
        (horizontalLeft n (width n)) (horizontalRight n (width n))
        y (y + height n))) atTop (nhds 1) := by
    have hlowerHorizontal : forall n, 1 - epsilon n < mu.real
        (E.horizontalCrossingEvent
          (horizontalLeft n (width n)) (horizontalRight n (width n))
          y (y + height n)) := by
      intro n
      convert hhorizontal n using 1 <;>
        simp only [horizontalS, horizontalT, Int.cast_mul,
          Int.cast_ofNat, Int.cast_sub] <;> ring
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower tendsto_const_nhds (fun n => le_of_lt (hlowerHorizontal n))
        (fun _ => measureReal_le_one)
  exact ⟨width, height, hwidth, hheight,
    hverticalLimit, hhorizontalLimit⟩






theorem PeriodicPlaneEmbedding.exists_rowwise_dependentSpan_endpointCrossings_tendsto_one_of_unique
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (r y s : Nat -> Real) (t : Nat -> Int)
    (ht : forall n, 3 * B < t n)
    (epsilon : Nat -> Real) (hepsilon : forall n, 0 < epsilon n)
    (hepsilon_zero : Tendsto epsilon atTop (nhds 0))
    (minimumWidth minimumHeight : Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Nat -> Int)
    (hhorizontalSpan : forall n w, minimumWidth n <= w ->
      3 * B < horizontalRight n w - horizontalLeft n w) :
    exists width height : Nat -> Nat,
      (forall n, minimumWidth n <= width n) /\
      (forall n, minimumHeight n <= height n) /\
      Tendsto (fun n => mu.real (E.verticalCrossingEvent
        (r n) (r n + width n)
        ((2 * s n + (s n + t n)) / 3)
        ((s n + 2 * (s n + t n)) / 3))) atTop (nhds 1) /\
      Tendsto (fun n => mu.real (E.horizontalCrossingEvent
        (horizontalLeft n (width n)) (horizontalRight n (width n))
        (y n) (y n + height n))) atTop (nhds 1) := by
  choose width hwidth hvertical using fun n =>
    E.exists_verticalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique (r n) B (s n) hB0 hB (t n) (ht n)
        (minimumWidth n) (hepsilon n)
  let horizontalS : Nat -> Real := fun n =>
    2 * horizontalLeft n (width n) - horizontalRight n (width n)
  let horizontalT : Nat -> Int := fun n =>
    3 * (horizontalRight n (width n) - horizontalLeft n (width n))
  have hhorizontalT (n : Nat) : 3 * B < horizontalT n := by
    have hspan := hhorizontalSpan n (width n) (hwidth n)
    rw [show (horizontalT n : Real) =
        3 * ((horizontalRight n (width n) : Real) -
          horizontalLeft n (width n)) by
      simp only [horizontalT, Int.cast_mul, Int.cast_ofNat, Int.cast_sub]]
    nlinarith
  choose height hheight hhorizontal using fun n =>
    E.exists_horizontalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique (y n) B (horizontalS n) hB0 hB
        (horizontalT n) (hhorizontalT n) (minimumHeight n) (hepsilon n)
  have hlower : Tendsto (fun n => 1 - epsilon n) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilon_zero
  have hverticalLimit : Tendsto (fun n => mu.real
      (E.verticalCrossingEvent (r n) (r n + width n)
        ((2 * s n + (s n + t n)) / 3)
        ((s n + 2 * (s n + t n)) / 3))) atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (hvertical n)) (fun _ => measureReal_le_one)
  have hhorizontalLimit : Tendsto (fun n => mu.real
      (E.horizontalCrossingEvent
        (horizontalLeft n (width n)) (horizontalRight n (width n))
        (y n) (y n + height n))) atTop (nhds 1) := by
    have hlowerHorizontal : forall n, 1 - epsilon n < mu.real
        (E.horizontalCrossingEvent
          (horizontalLeft n (width n)) (horizontalRight n (width n))
          (y n) (y n + height n)) := by
      intro n
      convert hhorizontal n using 1 <;>
        simp only [horizontalS, horizontalT, Int.cast_mul,
          Int.cast_ofNat, Int.cast_sub] <;> ring
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower tendsto_const_nhds (fun n => le_of_lt (hlowerHorizontal n))
        (fun _ => measureReal_le_one)
  exact ⟨width, height, hwidth, hheight,
    hverticalLimit, hhorizontalLimit⟩





structure DependentRadiusFirstAdjacentEndpointRow
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (template : Finset V) (step : Int) (cutoff : Nat)
    (epsilon B : Real) (r y s : Nat -> Real) (t : Nat -> Int)
    (minimumWidth minimumHeight : Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Nat -> Int) where
  radius : Nat
  width : Nat
  height : Nat
  cutoff_le_radius : cutoff <= radius
  minimumWidth_le : minimumWidth radius <= width
  minimumHeight_le : minimumHeight radius <= height
  merge_lt : forall q : Fin 2 × (Fin 3 × Fin 3),
    mu.real (P.pairMergeErrorUnion template
      (template.image (P.shift (preferenceKingOffset q.2 +
        if q.1.val = 0 then 0 else verticalShift step))) radius) < epsilon
  dualVertical_gt : 1 - epsilon < muDual.real
    (Edual.verticalCrossingEvent (r radius) (r radius + width)
      ((2 * s radius + (s radius + t radius)) / 3)
      ((s radius + 2 * (s radius + t radius)) / 3))
  dualHorizontal_gt : 1 - epsilon < muDual.real
    (Edual.horizontalCrossingEvent
      (horizontalLeft radius width) (horizontalRight radius width)
      (y radius) (y radius + height))


theorem nonempty_dependentRadiusFirstAdjacentEndpointRow
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (template : Finset V) (step : Int) (cutoff : Nat)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (r y s : Nat -> Real) (t : Nat -> Int)
    (ht : forall radius, 3 * B < t radius)
    (minimumWidth minimumHeight : Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Nat -> Int)
    (hhorizontalSpan : forall radius width,
      minimumWidth radius <= width ->
      3 * B < horizontalRight radius width -
        horizontalLeft radius width) :
    Nonempty (DependentRadiusFirstAdjacentEndpointRow E Edual mu muDual
      template step cutoff epsilon B r y s t minimumWidth minimumHeight
      horizontalLeft horizontalRight) := by
  obtain ⟨radius, width, height, hradius, hwidth, hheight,
      hmerge, hvertical, hhorizontal⟩ :=
    exists_radiusFirst_dependentGeometry_adjacentEndpointRow
      E Edual mu muDual hunique hFKGDual hTIDual huniqueDual template
      step cutoff epsilon hepsilon B hB0 hB r y s t ht minimumWidth
      minimumHeight horizontalLeft horizontalRight hhorizontalSpan
  exact ⟨{
    radius := radius
    width := width
    height := height
    cutoff_le_radius := hradius
    minimumWidth_le := hwidth
    minimumHeight_le := hheight
    merge_lt := hmerge
    dualVertical_gt := hvertical
    dualHorizontal_gt := hhorizontal }⟩






theorem exists_recursiveDependentRadiusFirstAdjacentEndpointRows_with_limits
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (template : Nat -> Finset V) (initialStep : Int)
    (hinitialStep : 0 <= initialStep)
    (r y s : Nat -> Int -> Nat -> Real)
    (t : Nat -> Int -> Nat -> Int)
    (ht : forall n step radius, 3 * B < t n step radius)
    (minimumWidth minimumHeight : Nat -> Int -> Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Int -> Nat -> Nat -> Int)
    (hhorizontalSpan : forall n step radius width,
      minimumWidth n step radius <= width ->
      3 * B < horizontalRight n step radius width -
        horizontalLeft n step radius width) :
    let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
    exists state : Nat -> Int × Nat,
      exists rows : forall n, DependentRadiusFirstAdjacentEndpointRow
        E Edual mu muDual (template n) (state n).1 (state n).2
        (epsilon n) B (r n (state n).1) (y n (state n).1)
        (s n (state n).1) (t n (state n).1)
        (minimumWidth n (state n).1) (minimumHeight n (state n).1)
        (horizontalLeft n (state n).1) (horizontalRight n (state n).1),
      state 0 = (initialStep, 0) /\
      (forall n, state (n + 1) =
        (((rows n).height : Int), (rows n).radius + 1)) /\
      (forall n, 0 <= (state n).1) /\
      Tendsto (fun n => (rows n).radius) atTop atTop /\
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
          ((template n).image (P.shift
            (preferenceKingOffset (q n).2 +
              if (q n).1.val = 0 then 0
              else verticalShift (state n).1))) (rows n).radius))
          atTop (nhds 0)) /\
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real
          (P.pairMergeErrorUnion (template (n + 1))
            ((template (n + 1)).image (P.shift
              (preferenceKingOffset (q (n + 1)).2 +
                if (q (n + 1)).1.val = 0 then 0
                else verticalShift (state (n + 1)).1)))
            (rows (n + 1)).radius)) atTop (nhds 0)) /\
      Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent
        (r n (state n).1 (rows n).radius)
        (r n (state n).1 (rows n).radius + (rows n).width)
        ((2 * s n (state n).1 (rows n).radius +
          (s n (state n).1 (rows n).radius +
            t n (state n).1 (rows n).radius)) / 3)
        ((s n (state n).1 (rows n).radius +
          2 * (s n (state n).1 (rows n).radius +
            t n (state n).1 (rows n).radius)) / 3)))
        atTop (nhds 1) /\
      Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent
        (horizontalLeft n (state n).1 (rows n).radius (rows n).width)
        (horizontalRight n (state n).1 (rows n).radius (rows n).width)
        (y n (state n).1 (rows n).radius)
        (y n (state n).1 (rows n).radius + (rows n).height)))
        atTop (nhds 1) := by
  dsimp only
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  let chooseRow (n : Nat) (state : Int × Nat) := Classical.choice
    (nonempty_dependentRadiusFirstAdjacentEndpointRow
      E Edual mu muDual hunique hFKGDual hTIDual huniqueDual
      (template n) state.1 state.2 (epsilon n) (hepsilon n) B hB0 hB
      (r n state.1) (y n state.1) (s n state.1) (t n state.1)
      (ht n state.1) (minimumWidth n state.1)
      (minimumHeight n state.1) (horizontalLeft n state.1)
      (horizontalRight n state.1) (hhorizontalSpan n state.1))
  let state : Nat -> Int × Nat := fun n =>
    Nat.rec (initialStep, 0) (fun n previous =>
      let row := chooseRow n previous
      ((row.height : Int), row.radius + 1)) n
  let rows := fun n => chooseRow n (state n)
  have hstate0 : state 0 = (initialStep, 0) := rfl
  have hstateSucc (n : Nat) : state (n + 1) =
      (((rows n).height : Int), (rows n).radius + 1) := by
    simp only [state, rows]
  have hstepNonneg : forall n, 0 <= (state n).1 := by
    intro n
    cases n with
    | zero => simpa only [hstate0] using hinitialStep
    | succ n =>
        rw [hstateSucc n]
        exact Int.ofNat_zero_le _
  have hcutoffCofinal : forall n, n <= (state n).2 := by
    intro n
    induction n with
    | zero => simp only [hstate0, le_refl]
    | succ n ih =>
        rw [hstateSucc n]
        exact Nat.succ_le_succ (ih.trans (rows n).cutoff_le_radius)
  have hradiusCofinal : forall n, n <= (rows n).radius := fun n =>
    (hcutoffCofinal n).trans (rows n).cutoff_le_radius
  have hradiusTop : Tendsto (fun n => (rows n).radius) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hradiusCofinal n)
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    simpa only [epsilon] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hmerge (q : Nat -> Fin 2 × (Fin 3 × Fin 3)) :
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
        ((template n).image (P.shift
          (preferenceKingOffset (q n).2 +
            if (q n).1.val = 0 then 0
            else verticalShift (state n).1))) (rows n).radius))
        atTop (nhds 0) := by
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => le_of_lt ((rows n).merge_lt (q n))) hepsilonZero
  have hmergeShift (q : Nat -> Fin 2 × (Fin 3 × Fin 3)) :
      Tendsto (fun n => mu.real
        (P.pairMergeErrorUnion (template (n + 1))
          ((template (n + 1)).image (P.shift
            (preferenceKingOffset (q (n + 1)).2 +
              if (q (n + 1)).1.val = 0 then 0
              else verticalShift (state (n + 1)).1)))
          (rows (n + 1)).radius)) atTop (nhds 0) := by
    exact (hmerge q).comp (tendsto_add_atTop_nat 1)
  have hlower : Tendsto (fun n => 1 - epsilon n) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilonZero
  have hvertical : Tendsto (fun n => muDual.real
      (Edual.verticalCrossingEvent
        (r n (state n).1 (rows n).radius)
        (r n (state n).1 (rows n).radius + (rows n).width)
        ((2 * s n (state n).1 (rows n).radius +
          (s n (state n).1 (rows n).radius +
            t n (state n).1 (rows n).radius)) / 3)
        ((s n (state n).1 (rows n).radius +
          2 * (s n (state n).1 (rows n).radius +
            t n (state n).1 (rows n).radius)) / 3)))
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (rows n).dualVertical_gt)
      (fun _ => measureReal_le_one)
  have hhorizontal : Tendsto (fun n => muDual.real
      (Edual.horizontalCrossingEvent
        (horizontalLeft n (state n).1 (rows n).radius (rows n).width)
        (horizontalRight n (state n).1 (rows n).radius (rows n).width)
        (y n (state n).1 (rows n).radius)
        (y n (state n).1 (rows n).radius + (rows n).height)))
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (rows n).dualHorizontal_gt)
      (fun _ => measureReal_le_one)
  exact ⟨state, rows, hstate0, hstateSucc, hstepNonneg, hradiusTop,
    hmerge, hmergeShift, hvertical, hhorizontal⟩








theorem exists_carriedAsymmetricEndpointCoordinates_with_limits
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (B : Nat) (hBpos : 0 < B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (template : Nat -> Finset V) :
    let targetY : Nat -> Nat := fun n => 20 * B + n + 1
    exists radius width height : Nat -> Nat,
      Tendsto radius atTop atTop /\
      (forall n, 3 * B + 1 <= width n) /\
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real
          (P.pairMergeErrorUnion (template (n + 1))
            ((template (n + 1)).image (P.shift
              (preferenceKingOffset (q (n + 1)).2 +
                if (q (n + 1)).1.val = 0 then 0
                else verticalShift (height n))))
            (radius (n + 1)))) atTop (nhds 0)) /\
      Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent
        (4 * B) (4 * B + width n) (-4 * B)
          (targetY n + 4 * B))) atTop (nhds 1) /\
      Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent
        (-4 * B) (width n + 12 * B) (4 * B)
          (4 * B + height n))) atTop (nhds 1) /\
      (forall n, (0 : Real) + 5 * B < width n + 8 * B - 5 * B) /\
      (forall n, -(4 * B : Real) + 5 * B <
        targetY n + 4 * B - 5 * B) /\
      (forall n, -(4 * B : Real) + 5 * B <
        width n + 12 * B - 5 * B) /\
      (forall n, (0 : Real) + 5 * B <
        targetY n + height n - 5 * B) /\
      (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\
      (forall n, (4 * B : Real) + width n <=
        width n + 8 * B - 4 * B) /\
      (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\
      (forall n, (4 * B : Real) + height n <=
        targetY n + height n - 4 * B) := by
  dsimp only
  let targetY : Nat -> Nat := fun n => 20 * B + n + 1
  let r : Nat -> Int -> Nat -> Real := fun _ _ _ => 4 * B
  let y : Nat -> Int -> Nat -> Real := fun _ _ _ => 4 * B
  let s : Nat -> Int -> Nat -> Real := fun n _ _ =>
    -(targetY n : Real) - 12 * B
  let t : Nat -> Int -> Nat -> Int := fun n _ _ =>
    (3 * targetY n + 24 * B : Nat)
  let minimumWidth : Nat -> Int -> Nat -> Nat := fun _ _ _ => 3 * B + 1
  let minimumHeight : Nat -> Int -> Nat -> Nat := fun _ _ _ => 0
  let horizontalLeft : Nat -> Int -> Nat -> Nat -> Int := fun _ _ _ _ =>
    -(4 * (B : Int))
  let horizontalRight : Nat -> Int -> Nat -> Nat -> Int := fun _ _ _ w =>
    w + 12 * (B : Int)
  have ht (n : Nat) (step : Int) (radius : Nat) :
      3 * (B : Real) < t n step radius := by
    dsimp only [t, targetY]
    push_cast
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hn : (0 : Real) <= n := by positivity
    nlinarith
  have hhorizontalSpan (n : Nat) (step : Int) (radius width : Nat)
      (_hwidth : minimumWidth n step radius <= width) :
      3 * (B : Real) <
        horizontalRight n step radius width -
          horizontalLeft n step radius width := by
    dsimp only [horizontalRight, horizontalLeft]
    push_cast
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hw : (0 : Real) <= width := by positivity
    nlinarith
  obtain ⟨state, rows, _hstate0, hstateSucc, _hstepNonneg,
      hradius, _hmerge, hmergeShift, hvertical, hhorizontal⟩ :=
    exists_recursiveDependentRadiusFirstAdjacentEndpointRows_with_limits
      E Edual mu muDual hunique hFKGDual hTIDual huniqueDual
      (B : Real) (by positivity) hB template 0 (by omega)
      r y s t ht minimumWidth minimumHeight horizontalLeft horizontalRight
        hhorizontalSpan
  let radius : Nat -> Nat := fun n => (rows n).radius
  let width : Nat -> Nat := fun n => (rows n).width
  let height : Nat -> Nat := fun n => (rows n).height
  have hstateStep (n : Nat) : (state (n + 1)).1 = (height n : Int) := by
    rw [hstateSucc n]
  have hmergeCarried
      (q : Nat -> Fin 2 × (Fin 3 × Fin 3)) :
      Tendsto (fun n => mu.real
        (P.pairMergeErrorUnion (template (n + 1))
          ((template (n + 1)).image (P.shift
            (preferenceKingOffset (q (n + 1)).2 +
              if (q (n + 1)).1.val = 0 then 0
              else verticalShift (height n))))
          (radius (n + 1)))) atTop (nhds 0) := by
    apply (hmergeShift q).congr'
    filter_upwards [] with n
    simp only [hstateStep n, radius]
  have hvertical' : Tendsto (fun n => muDual.real
      (Edual.verticalCrossingEvent (4 * B) (4 * B + width n)
        (-4 * B) (targetY n + 4 * B))) atTop (nhds 1) := by
    apply hvertical.congr'
    filter_upwards [] with n
    congr 2 <;> dsimp only [r, s, t, targetY, width] <;> push_cast <;> ring
  have hhorizontal' : Tendsto (fun n => muDual.real
      (Edual.horizontalCrossingEvent (-4 * B) (width n + 12 * B)
        (4 * B) (4 * B + height n))) atTop (nhds 1) := by
    apply hhorizontal.congr'
    filter_upwards [] with n
    congr 2 <;>
      dsimp only [horizontalLeft, horizontalRight, y, width, height] <;>
      push_cast <;> ring
  have hwidthLower (n : Nat) : 3 * B + 1 <= width n :=
    (rows n).minimumWidth_le
  refine ⟨radius, width, height, hradius, hwidthLower, hmergeCarried,
    hvertical', hhorizontal', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have hw : (3 * B + 1 : Real) <= width n := by exact_mod_cast hwidthLower n
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    norm_num at hw ⊢
    linarith
  · intro n
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hn : (0 : Real) <= n := by positivity
    push_cast
    nlinarith
  · intro n
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hw : (0 : Real) <= width n := by positivity
    push_cast
    linarith
  · intro n
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hy : (10 * B : Real) < targetY n := by
      dsimp only [targetY]
      push_cast
      have hn : (0 : Real) <= n := by positivity
      nlinarith
    have hh : (0 : Real) <= height n := by positivity
    push_cast
    linarith
  · intro n
    norm_num
  · intro n
    have hBreal : (0 : Real) <= B := by positivity
    push_cast
    linarith
  · intro n
    norm_num
  · intro n
    have hy : (8 * B : Real) <= targetY n := by
      dsimp only [targetY]
      push_cast
      have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
      have hn : (0 : Real) <= n := by positivity
      nlinarith
    push_cast
    linarith





theorem PeriodicPlanarDualPair.exists_carriedAsymmetricEndpoints_false_of_primal_limit
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG (D.dualMeasure mu))
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
    (huniqueDual : (D.dualMeasure mu)
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (B : Nat) (hBpos : 0 < B)
    (hBp : forall {x z : V} (hxz : P.graph.Adj x z)
      (u) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxz u -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxz u -
          D.dualEmbedding.vertex x) i| <= B)
    (template : Nat -> Finset V) :
    let targetY : Nat -> Nat := fun n => 20 * B + n + 1
    exists radius width height : Nat -> Nat,
      Tendsto radius atTop atTop /\
      (forall n, 3 * B + 1 <= width n) /\
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real
          (P.pairMergeErrorUnion (template (n + 1))
            ((template (n + 1)).image (P.shift
              (preferenceKingOffset (q (n + 1)).2 +
                if (q (n + 1)).1.val = 0 then 0
                else verticalShift (height n))))
            (radius (n + 1)))) atTop (nhds 0)) /\
      (Tendsto (fun n => max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          0 (width n + 8 * B) 0 (targetY n)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          0 (width n + 8 * B) 0 (targetY n + height n))))
        atTop (nhds 1) -> False) := by
  dsimp only
  let targetY : Nat -> Nat := fun n => 20 * B + n + 1
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  obtain ⟨radius, width, height, hradius, hwidth, hmerge,
      hdualV0, hdualH0, hspanHX, hspanDVY, hspanDHX, hspanVY,
      hDVLeft, hDVRight, hDHBottom, hDHTop⟩ :=
    exists_carriedAsymmetricEndpointCoordinates_with_limits
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      hunique hFKGDual hTIDual huniqueDual B hBpos hBd template
  have hdualV : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (4 * B) (4 * B + width n) (-4 * B)
          (targetY n + 4 * B))) atTop (nhds 1) := by
    apply hdualV0.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)]
  have hdualH : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (-4 * B) (width n + 12 * B) (4 * B)
          (4 * B + height n))) atTop (nhds 1) := by
    apply hdualH0.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]
  have hspanDVY' : forall n,
      -(4 * B : Real) + 5 * B <
        (targetY n : Real) + 4 * B - 5 * B := by
    simpa only [targetY] using hspanDVY
  have hspanVY' : forall n,
      (0 : Real) + 5 * B <
        (targetY n : Real) + height n - 5 * B := by
    simpa only [targetY] using hspanVY
  have hDHTop' : forall n,
      (4 * B : Real) + height n <=
        (targetY n : Real) + height n - 4 * B := by
    simpa only [targetY] using hDHTop
  refine ⟨radius, width, height, hradius, hwidth, hmerge, ?_⟩
  intro hprimal
  exact D.fullyAsymmetricEndpointCoordinates_false mu (B : Real)
    (by exact_mod_cast hBpos) hBp hBd
    (fun _ => 0) (fun n => width n + 8 * B)
    (fun _ => 0) (fun n => (targetY n : Real))
    (fun _ => 0) (fun n => width n + 8 * B)
    (fun _ => 0) (fun n => (targetY n : Real) + height n)
    (fun _ => 4 * B) (fun n => 4 * B + width n)
    (fun _ => -4 * B) (fun n => targetY n + 4 * B)
    (fun _ => -4 * B) (fun n => width n + 12 * B)
    (fun _ => 4 * B) (fun n => 4 * B + height n)
    hspanHX (fun n => by nlinarith [hspanDVY' n])
    (fun n => by nlinarith [hspanDHX n]) hspanVY'
    (fun _ => by norm_num) (fun _ => by norm_num)
    hDVLeft hDVRight
    (fun _ => by norm_num) (fun _ => by apply le_of_eq; ring)
    hDHBottom hDHTop'
    hprimal hdualV hdualH





theorem PeriodicPlaneEmbedding.exists_uniformOrbitBoxMixedRadius_alignedExact_primalLimit
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (p pDual : Nat -> Real)
    (family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n))
    (familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual
        (Pdual.orbitBox n) (pDual n))
    (schedule : forall n, PairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0))
    (hp : Tendsto p atTop (nhds 1)) (hp_le : forall n, p n <= 1) :
    exists radius : Nat -> Nat,
      forall (k extentX extentY : Nat -> Nat)
        (data : forall n, AlignedExactExtentPairedMixedBoundaryScores
          E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
          (p n) (pDual n) (family n) (familyDual n) (schedule n)
          (k n) (extentX n) (extentY n)),
        (forall n, PairedAlignedConnectorSlack E Edual
          (family n) (familyDual n) (schedule n)
          (max (radius n) n) (k n)) ->
        Tendsto (fun n => max
          (mu.real (E.horizontalCrossingEvent
            0 (extentX n) 0 (extentY n)))
          (mu.real (E.verticalCrossingEvent
            (data n).raw.data.wideLeft (data n).raw.data.wideRight
            0 (extentY n)))) atTop (nhds 1) := by
  let template : Nat -> Finset V := fun n => P.orbitBox n
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- hunique]
    exact measure_mono fun _ h => h.1
  have htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V)))
      atTop (nhds 1) := by
    simpa only [template, PeriodicGraph.setHitsInfinite,
      PeriodicGraph.orbitBoxHitsInfinite] using
      P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_mixedBoundaryScores_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit
  refine ⟨radius, ?_⟩
  intro k extentX extentY data slack
  apply hcross
      (fun n => (data n).raw.data.width)
      (fun n => (data n).raw.data.height)
      (fun n => (data n).raw.data.width_pos)
      (fun n => (data n).raw.data.height_pos)
      (fun n => (data n).raw.data.base)
      (fun _ => 0) (fun n => (extentX n : Real))
      (fun _ => 0) (fun n => (extentY n : Real))
      (fun n => (data n).raw.data.wideLeft)
      (fun n => (data n).raw.data.wideRight)
      (fun _ => 0) (fun n => (extentY n : Real)) p hp hp_le
  · intro n
    exact (data n).raw.data.wideLeft_le
  · intro n
    simpa [(data n).raw.narrowRight_eq] using
      (data n).raw.data.narrowRight_le
  · intro n
    exact le_rfl
  · intro n
    exact le_rfl
  · intro n gridVertex vertex hvertex
    apply (data n).primalConnector_subset_narrow (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := by
      simpa only [template, Finset.mem_coe, Finset.mem_image] using hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    exact (Nat.le_max_right (radius n) n).trans
      (P.id_le_bufferedRadius (max (radius n) n))
  · intro n gridVertex vertex hvertex
    apply (data n).primalConnector_subset_narrow (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply P.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n gridVertex vertex hvertex
    rw [<- (data n).raw.shortTop_eq]
    apply (data n).primalConnector_subset_wide (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply P.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n i
    simpa [template, (data n).raw.shortTop_eq] using
      le_of_lt ((data n).raw.data.primal_bottom i)
  · intro n i
    simpa [template, (data n).raw.shortTop_eq] using
      le_of_lt ((data n).raw.data.primal_top i)
  · intro n j
    simpa [template, (data n).raw.narrowRight_eq,
      (data n).raw.tallTop_eq] using
      le_of_lt ((data n).raw.data.primal_left j)
  · intro n j
    simpa [template, (data n).raw.narrowRight_eq,
      (data n).raw.tallTop_eq] using
      le_of_lt ((data n).raw.data.primal_right j)

set_option maxHeartbeats 800000 in





theorem PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.primalAdjacent_limit_of_pairMerge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (S : Nat -> Finset V) (margin M width height radius : Nat -> Nat)
    (score : Nat -> Real)
    (data : forall n, E.CommonSquareNormalBoundaryBandData
      mu (S n) (margin n) (M n) (score n))
    (step : Nat -> Int) (hstep : forall n, 0 <= step n)
    (hwidth : forall n, 2 * margin n < width n)
    (hheight : forall n, 2 * margin n < height n)
    (hscore : Tendsto score atTop (nhds 1))
    (hscore_le : forall n, score n <= 1)
    (htemplateHit : Tendsto (fun n => mu.real
      (P.setHitsInfinite
        (P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight
          (data n).zBottom (data n).zTop : Set V))) atTop (nhds 1))
    (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion
        (P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight
          (data n).zBottom (data n).zTop)
        ((P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight
          (data n).zBottom (data n).zTop).image (P.shift
            (preferenceKingOffset (q n).2 +
              if (q n).1.val = 0 then 0 else verticalShift (step n))))
        (radius n))) atTop (nhds 0))
    (hconnector : forall n
      (v : PreferenceGridVertex (width n) (height n)),
      margin n <= v.1.val -> v.1.val + margin n < width n ->
      margin n <= v.2.val -> v.2.val + margin n < height n ->
      (P.shift (preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (-(M n : Real)) (M n + width n)
            (-(M n : Real)) (M n + height n)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (-(M n : Real)) (M n + width n)
        (-(M n : Real)) (M n + height n)))
      (mu.real (E.verticalCrossingEvent
        (-(M n : Real)) (M n + width n)
        (-(M n : Real)) (M n + height n + step n))))
      atTop (nhds 1) := by
  let template : Nat -> Finset V := fun n =>
    P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight
      (data n).zBottom (data n).zTop
  have hcontinuation :
      E.UniformTemplateAdjacentBoundaryBandCrossingRadius
        mu template step radius :=
    E.uniformTemplateAdjacentBoundaryBandCrossingRadius_of_pairMerge
      mu hFKG hTI template (by simpa only [template] using htemplateHit)
        step hstep radius (by simpa only [template] using hmerge)
  apply hcontinuation width height margin (fun _ => 0)
    (fun n => -(M n : Real)) (fun n => M n + width n)
    (fun n => -(M n : Real)) (fun n => M n + height n) score
    hwidth hheight hscore_le hscore
  · intro n v
    have hsource := E.fourShiftTemplate_preferenceGrid_subset_rect
      (M n) (width n) (height n) (S n)
      (data n).zLeft (data n).zRight (data n).zBottom (data n).zTop
      (by simpa [Finset.coe_image, horizontalShift] using
        ((data n).left (0 : Fin (margin n + 1))).1)
      (by simpa [Finset.coe_image, horizontalShift] using
        ((data n).right (0 : Fin (margin n + 1))).1)
      (by simpa [Finset.coe_image, verticalShift] using
        ((data n).bottom (0 : Fin (margin n + 1))).1)
      (by simpa [Finset.coe_image, verticalShift] using
        ((data n).top (0 : Fin (margin n + 1))).1) v
    simpa only [template, Pi.zero_apply, zero_add] using hsource
  · simpa only [Pi.zero_apply, zero_add] using hconnector
  · intro n v hv
    simpa only [template, Pi.zero_apply, zero_add] using
      le_of_lt ((data n).bottomBandScore E mu hTI (width n) (height n) v hv)
  · intro n v hv
    simpa only [template, Pi.zero_apply, zero_add] using
      le_of_lt ((data n).topBandScore E mu hTI (width n) (height n) v hv)
  · intro n v hv
    simpa only [template, Pi.zero_apply, zero_add] using
      le_of_lt ((data n).leftBandScore E mu hTI (width n) (height n) v hv)
  · intro n v hv
    simpa only [template, Pi.zero_apply, zero_add] using
      le_of_lt ((data n).rightBandScore E mu hTI (width n) (height n) v hv)




theorem PeriodicPlaneEmbedding.nonempty_carriedCrossNestedArray_of_alignedSharedLevelSteps
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (S : Nat -> Finset V) (score : Nat -> Real)
    (family : forall m, E.NormalBoundaryBandFamily mu (S m) (score m))
    (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
    (state : Nat -> Nat × Nat) (K : Nat -> Nat)
    (scoreEpsilon mergeEpsilon : Nat -> Real)
    (steps : forall n, E.AlignedSharedLevelStep mu S score family
      verticalRequirement horizontalRequirement
      (state n).1 (state n).2 (scoreEpsilon n) (mergeEpsilon n))
    (hscoreEpsilon : Tendsto scoreEpsilon atTop (nhds 0))
    (hmergeEpsilon : Tendsto mergeEpsilon atTop (nhds 0))
    (hextentK : forall n, (steps n).extent <= K n)
    (hverticalConnector : forall n,
      (P.orbitBox (P.bufferedRadius (steps n).nextConnector) : Set V) <=
        E.rectVertices (-(K n : Real)) (K n)
          (-(steps n).extent : Real) (steps n).extent)
    (hhorizontalConnector : forall n,
      (P.orbitBox (P.bufferedRadius (steps n).nextConnector) : Set V) <=
        E.rectVertices (-(steps n).extent : Real) (steps n).extent
          (-(K n : Real)) (K n)) :
    Nonempty (E.CarriedCrossNestedArray mu) := by
  have hlower : Tendsto (fun n => 1 - scoreEpsilon n)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hscoreEpsilon
  have hbottom : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent
        (-(steps n).extent : Real) (steps n).extent
        (-(steps n).extent : Real) (steps n).extent
        ((steps n).bottom : Set V)
        (E.rectBottomBoundaryVertices
          (-(steps n).extent : Real) (steps n).extent
          (-(steps n).extent : Real) (steps n).extent)))
      atTop (nhds 1) :=
    hlower.squeeze tendsto_const_nhds
      (fun n => le_of_lt ((steps n).threshold_gt.trans
        (steps n).bottomComponentScore))
      (fun _ => measureReal_le_one)
  have htop : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent
        (-(steps n).extent : Real) (steps n).extent
        (-(steps n).extent : Real) (steps n).extent
        ((steps n).top : Set V)
        (E.rectTopBoundaryVertices
          (-(steps n).extent : Real) (steps n).extent
          (-(steps n).extent : Real) (steps n).extent)))
      atTop (nhds 1) :=
    hlower.squeeze tendsto_const_nhds
      (fun n => le_of_lt ((steps n).threshold_gt.trans
        (steps n).topComponentScore))
      (fun _ => measureReal_le_one)
  have hleft : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent
        (-(steps n).extent : Real) (steps n).extent
        (-(steps n).extent : Real) (steps n).extent
        ((steps n).left : Set V)
        (E.rectLeftBoundaryVertices
          (-(steps n).extent : Real) (steps n).extent
          (-(steps n).extent : Real) (steps n).extent)))
      atTop (nhds 1) :=
    hlower.squeeze tendsto_const_nhds
      (fun n => le_of_lt ((steps n).threshold_gt.trans
        (steps n).leftComponentScore))
      (fun _ => measureReal_le_one)
  have hright : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent
        (-(steps n).extent : Real) (steps n).extent
        (-(steps n).extent : Real) (steps n).extent
        ((steps n).right : Set V)
        (E.rectRightBoundaryVertices
          (-(steps n).extent : Real) (steps n).extent
          (-(steps n).extent : Real) (steps n).extent)))
      atTop (nhds 1) :=
    hlower.squeeze tendsto_const_nhds
      (fun n => le_of_lt ((steps n).threshold_gt.trans
        (steps n).rightComponentScore))
      (fun _ => measureReal_le_one)
  have hverticalMerge : Tendsto (fun n => mu.real
      (P.pairMergeErrorUnion (steps n).bottom (steps n).top
        (steps n).nextConnector)) atTop (nhds 0) :=
    squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => le_of_lt (steps n).verticalMerge) hmergeEpsilon
  have hhorizontalMerge : Tendsto (fun n => mu.real
      (P.pairMergeErrorUnion (steps n).left (steps n).right
        (steps n).nextConnector)) atTop (nhds 0) :=
    squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => le_of_lt (steps n).horizontalMerge) hmergeEpsilon
  exact ⟨{
    a := fun n => -(steps n).extent
    b := fun n => (steps n).extent
    c := fun n => -(steps n).extent
    d := fun n => (steps n).extent
    aWide := fun n => -(K n : Real)
    bWide := fun n => K n
    cTall := fun n => -(K n : Real)
    dTall := fun n => K n
    bottom := fun n => (steps n).bottom
    top := fun n => (steps n).top
    left := fun n => (steps n).left
    right := fun n => (steps n).right
    verticalRadius := fun n => (steps n).nextConnector
    horizontalRadius := fun n => (steps n).nextConnector
    wideLeft := fun n => by
      exact neg_le_neg (by exact_mod_cast (hextentK n))
    wideRight := fun n => by exact_mod_cast (hextentK n)
    tallBottom := fun n => by
      exact neg_le_neg (by exact_mod_cast (hextentK n))
    tallTop := fun n => by exact_mod_cast (hextentK n)
    verticalConnector := hverticalConnector
    horizontalConnector := hhorizontalConnector
    bottomLimit := hbottom
    topLimit := htop
    leftLimit := hleft
    rightLimit := hright
    verticalMergeLimit := hverticalMerge
    horizontalMergeLimit := hhorizontalMerge }⟩

end StatMech.FK.PeriodicPlanar
