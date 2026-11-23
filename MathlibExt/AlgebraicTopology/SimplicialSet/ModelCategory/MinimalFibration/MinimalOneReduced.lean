/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.Existence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.PointedSimplexMinimality
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap
public import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.FundamentalGroupHurewiczIso

/-!
# One reduced minimal Kan cores

A connected minimal Kan complex over the point has one vertex.  If its first
homotopy group is trivial, every edge is literally the degenerate edge at
that vertex.  This file also transports connectedness and triviality of the
first homotopy group from a Kan complex to the carrier of any chosen minimal
subfibration using the strict inclusion-retraction equations.

The strong deformation retract supplied by `MinimalSubfibration` is retained
unchanged.  No homology or Hurewicz equivalence is constructed here.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial
open scoped Simplicial
open SSet.modelCategoryQuillen

universe u

namespace SSet

namespace MinimalFibration

/-- The chosen minimal subfibration of a Kan complex over the point. -/
noncomputable def chosenMinimalCore (X : SSet.{u}) [KanComplex X] :
    MinimalSubfibration (terminal.from X) :=
  (nonempty_minimalSubfibration (terminal.from X)).some

/-- The carrier of a minimal subfibration over the point is a Kan complex. -/
noncomputable instance MinimalSubfibration.carrierKanComplex
    {X : SSet.{u}} (M : MinimalSubfibration (terminal.from X)) :
    KanComplex (M.carrier : SSet.{u}) := by
  change Fibration (terminal.from (M.carrier : SSet.{u}))
  have h := M.isMinimalFibration.1
  rw [show M.carrier.ι ≫ terminal.from X =
      terminal.from (M.carrier : SSet.{u}) from terminal.hom_ext _ _] at h
  exact h

/-- Minimality of the carrier of a minimal subfibration over the point. -/
theorem MinimalSubfibration.carrier_isMinimal
    {X : SSet.{u}} (M : MinimalSubfibration (terminal.from X)) :
    IsMinimal (terminal.from (M.carrier : SSet.{u})) := by
  have heq : M.carrier.ι ≫ terminal.from X =
      terminal.from (M.carrier : SSet.{u}) := terminal.hom_ext _ _
  intro n a b hab hboundary hhom
  rw [← heq] at hab hhom
  exact M.isMinimalFibration.2 a b hab hboundary hhom

/-- A connected minimal Kan complex over the point has exactly one vertex. -/
theorem vertex_eq_of_isConnected_of_isMinimal
    (X : SSet.{u}) [KanComplex X] [X.IsConnected]
    (hmin : IsMinimal (terminal.from X)) (x y : X _⦋0⦌) : y = x := by
  let eIso := (SSet.nonempty_fundamentalGroupoid_iso_of_isConnected X x y).some
  obtain ⟨e, he⟩ := SSet.FundamentalGroupoid.homMk_surjective eIso.hom
  let px : X.PtSimplex 0 x := (SSet.PtSimplex.equiv₀ x).symm x
  let py : X.PtSimplex 0 x := (SSet.PtSimplex.equiv₀ x).symm y
  let e' : X.Edge ((SSet.PtSimplex.equiv₀ x) px)
      ((SSet.PtSimplex.equiv₀ x) py) := by
    simpa [px, py] using e
  let r : py.RelStruct₀ px :=
    (SSet.PtSimplex.RelStruct₀.equiv₀ (f := py) (g := px)).symm e'
  have hpy : py = px := hmin.ptSimplex_eq_of_relStruct₀ r
  simpa [px, py] using congrArg (SSet.PtSimplex.equiv₀ x) hpy

/-- Regard a based loop edge as a pointed one-simplex. -/
noncomputable def loopPtSimplex {X : SSet.{u}} {x : X _⦋0⦌}
    (e : X.Edge x x) : X.PtSimplex 1 x where
  map := SSet.yonedaEquiv.symm e.edge
  comm := by
    apply SSet.boundary.hom_ext
    intro i
    fin_cases i <;>
      simp [SSet.boundary.ι_ι_assoc,
        SSet.stdSimplex.δ_comp_yonedaEquiv_symm]

/-- In a connected minimal Kan complex with trivial first homotopy group,
every edge is the degenerate edge at the chosen vertex. -/
theorem edge_eq_sigmaZero_of_isConnected_of_isMinimal_of_piOne_subsingleton
    (X : SSet.{u}) [KanComplex X] [X.IsConnected]
    (hmin : IsMinimal (terminal.from X)) (x : X _⦋0⦌)
    [Subsingleton (SSet.KanComplex.π 1 X x)] (s : X _⦋1⦌) :
    s = X.σ 0 x := by
  have h0 : X.δ 0 s = x :=
    vertex_eq_of_isConnected_of_isMinimal X hmin x (X.δ 0 s)
  have h1 : X.δ 1 s = x :=
    vertex_eq_of_isConnected_of_isMinimal X hmin x (X.δ 1 s)
  let e : X.Edge x x := SSet.Edge.mk s h1 h0
  let p : X.PtSimplex 1 x := loopPtSimplex e
  have hp : SSet.KanComplex.π.mk p = 1 := Subsingleton.elim _ _
  let r : p.RelStruct₀ (.const : X.PtSimplex 1 x) :=
    (SSet.KanComplex.π.mk_eq_one_iff p).mp hp |>.some
  have hpr : p = (.const : X.PtSimplex 1 x) :=
    hmin.ptSimplex_eq_of_relStruct₀ r
  have hmap := congrArg RelativeMorphism.map hpr
  apply SSet.yonedaEquiv.symm.injective
  simpa [p, loopPtSimplex, e, SSet.σ_zero_eq_yonedaEquiv_const,
    SSet.yonedaEquiv_const] using hmap

/-- If every edge is the degenerate edge at `x`, every two-simplex has a
canonical pointed boundary at `x`. -/
noncomputable def ptTwoOfSimplexOfEdgesDegenerate
    {X : SSet.{u}} (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) (s : X _⦋2⦌) :
    X.PtSimplex 2 x where
  map := SSet.yonedaEquiv.symm s
  comm := by
    apply SSet.boundary.hom_ext
    intro i
    rw [SSet.boundary.ι_ι_assoc]
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    rw [hedge (X.δ i s)]
    rw [SSet.σ_zero_eq_yonedaEquiv_const, Equiv.symm_apply_apply]
    simp

@[simp]
theorem ptTwoOfSimplexOfEdgesDegenerate_map
    {X : SSet.{u}} (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) (s : X _⦋2⦌) :
    RelativeMorphism.map (ptTwoOfSimplexOfEdgesDegenerate x hedge s) =
      SSet.yonedaEquiv.symm s :=
  rfl

/-- Connectedness descends from the ambient simplicial set to the carrier of
a minimal subfibration through its strict retraction. -/
theorem MinimalSubfibration.carrier_isConnected
    {X : SSet.{u}} [X.IsConnected]
    (M : MinimalSubfibration (terminal.from X)) :
    (M.carrier : SSet.{u}).IsConnected := by
  rw [SSet.isConnected_iff]
  constructor
  · constructor
    intro c d
    obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective c
    obtain ⟨b, rfl⟩ := SSet.π₀.mk_surjective d
    have himage :
        SSet.mapπ₀ M.carrier.ι (SSet.π₀.mk a) =
          SSet.mapπ₀ M.carrier.ι (SSet.π₀.mk b) :=
      Subsingleton.elim _ _
    have hretract := congrArg (SSet.mapπ₀ M.sdr.r) himage
    simpa only [← SSet.mapπ₀_comp_apply, M.sdr.retract,
      SSet.mapπ₀_id_apply] using hretract
  · let x : X _⦋0⦌ := Classical.arbitrary _
    exact ⟨M.sdr.r.app _ x⟩

private theorem piMap_congr {X Y : SSet.{u}} {f g : X ⟶ Y}
    (hfg : f = g) {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (hf : f.app _ x = y) (hg : g.app _ x = y) (n : ℕ) :
    SSet.KanComplex.π.map f hf n = SSet.KanComplex.π.map g hg n := by
  cases hfg
  rfl

/-- Triviality of `π₁` at an included carrier vertex descends through the
strict inclusion-retraction equations. -/
theorem MinimalSubfibration.carrier_piOne_subsingleton
    {X : SSet.{u}} (M : MinimalSubfibration (terminal.from X))
    (mx : M.carrier _⦋0⦌)
    [Subsingleton (SSet.KanComplex.π 1 X (M.carrier.ι.app _ mx))] :
    Subsingleton (SSet.KanComplex.π 1 M.carrier mx) := by
  constructor
  intro p q
  have himage :
      SSet.KanComplex.π.map M.carrier.ι rfl 1 p =
        SSet.KanComplex.π.map M.carrier.ι rfl 1 q :=
    Subsingleton.elim _ _
  have hr : M.sdr.r.app _ (M.carrier.ι.app _ mx) = mx := by
    have h := congrArg (fun f => f.app _ mx) M.sdr.retract
    simpa using h
  have hretract := congrArg
    (SSet.KanComplex.π.map M.sdr.r hr 1) himage
  have hcomp : (M.carrier.ι ≫ M.sdr.r).app _ mx = mx := by
    have h := congrArg (fun f => f.app _ mx) M.sdr.retract
    simpa using h
  have hleft :
      SSet.KanComplex.π.map M.sdr.r hr 1
          (SSet.KanComplex.π.map M.carrier.ι rfl 1 p) = p := by
    rw [← SSet.KanComplex.π.map_comp_apply M.carrier.ι M.sdr.r
      rfl hr hcomp]
    exact (congrFun (piMap_congr M.sdr.retract hcomp rfl 1) p).trans
      (SSet.KanComplex.π.map_id_apply p)
  have hright :
      SSet.KanComplex.π.map M.sdr.r hr 1
          (SSet.KanComplex.π.map M.carrier.ι rfl 1 q) = q := by
    rw [← SSet.KanComplex.π.map_comp_apply M.carrier.ι M.sdr.r
      rfl hr hcomp]
    exact (congrFun (piMap_congr M.sdr.retract hcomp rfl 1) q).trans
      (SSet.KanComplex.π.map_id_apply q)
  exact hleft.symm.trans (hretract.trans hright)

/-- The carrier of a connected minimal subfibration has exactly one vertex. -/
theorem MinimalSubfibration.carrier_vertex_eq
    {X : SSet.{u}} [X.IsConnected]
    (M : MinimalSubfibration (terminal.from X))
    (mx my : M.carrier _⦋0⦌) : my = mx := by
  let _ : (M.carrier : SSet.{u}).IsConnected := M.carrier_isConnected
  exact vertex_eq_of_isConnected_of_isMinimal M.carrier
    M.carrier_isMinimal mx my

/-- If the ambient first homotopy group is trivial at the included carrier
vertex, every edge of the connected minimal carrier is degenerate. -/
theorem MinimalSubfibration.carrier_edge_eq_sigmaZero
    {X : SSet.{u}} [X.IsConnected]
    (M : MinimalSubfibration (terminal.from X))
    (mx : M.carrier _⦋0⦌)
    [Subsingleton (SSet.KanComplex.π 1 X (M.carrier.ι.app _ mx))]
    (s : M.carrier _⦋1⦌) :
    s = (M.carrier : SSet.{u}).σ 0 mx := by
  let _ : (M.carrier : SSet.{u}).IsConnected := M.carrier_isConnected
  let _ : Subsingleton (SSet.KanComplex.π 1 M.carrier mx) :=
    M.carrier_piOne_subsingleton mx
  exact edge_eq_sigmaZero_of_isConnected_of_isMinimal_of_piOne_subsingleton
    M.carrier M.carrier_isMinimal mx s

end MinimalFibration

end SSet
