/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Topology.Homotopy.VanKampenFullness
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.SigmaSubtypeFullness
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Tests for fullness from a two-set van Kampen cover

These tests use the public fullness API first with symbolic data and then with
an explicit cover of the real line.  The concrete path starts and ends in the
left open set, leaves it through the right open set, and is equipped with a
one-cell subordinate grid labeled by the right member of the cover.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Set Topology

universe u

namespace MathlibExtTest.Topology.Homotopy.VanKampenFullnessTests

open MathlibExt.Topology.Homotopy.VanKampenWanted

/-! ## Symbolic public clients -/

/-- The public grid lift elaborates from explicit fullness and essential
surjectivity witnesses, with the cover and endpoints inferred. -/
example {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hCover : U ∪ V = Set.univ)
    (hFull : (FundamentalGroupoid.map (inclusionInterRight U V)).Full)
    (hEssSurj : (FundamentalGroupoid.map (inclusionInterRight U V)).EssSurj)
    {a b : U} (p : Path a.1 b.1)
    (G : SubordinatePathGrid (twoSetOpenCover U V hU hV) p) :
    ∃ q : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b,
      (FundamentalGroupoid.map (inclusionSub U)).map q =
        Path.Homotopic.Quotient.mk p := by
  let _ : (FundamentalGroupoid.map (inclusionInterRight U V)).Full := hFull
  let _ : (FundamentalGroupoid.map (inclusionInterRight U V)).EssSurj := hEssSurj
  exact ⟨openCoverGridLift hU hV hCover p G,
    openCoverGridLift_map hU hV hCover p G⟩

/-- The final theorem can be consumed directly and returns the standard
`Functor.Full` structure expected by downstream instance inference. -/
example {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hCover : U ∪ V = Set.univ)
    (hFull : (FundamentalGroupoid.map (inclusionInterRight U V)).Full)
    (hEssSurj : (FundamentalGroupoid.map (inclusionInterRight U V)).EssSurj) :
    (FundamentalGroupoid.map (inclusionSub (X := X) U)).Full :=
  inclusionSub_full_of_interRight_full_essSurj hU hV hCover hFull hEssSurj

/-! ## A concrete right-cover excursion -/

private abbrev leftOpen : Set ℝ := Set.Iio 1

private abbrev rightOpen : Set ℝ := Set.univ

private theorem leftOpen_isOpen : IsOpen leftOpen := isOpen_Iio

private theorem rightOpen_isOpen : IsOpen rightOpen := isOpen_univ

private theorem realLine_cover : leftOpen ∪ rightOpen = Set.univ := by
  simp [rightOpen]

private def basepoint : leftOpen := ⟨1 / 2, by norm_num [leftOpen]⟩

/-- A loop based in the left member that reaches `2`, hence cannot be
contained in that member. -/
private def excursion : Path (basepoint : ℝ) (basepoint : ℝ) :=
  (Path.segment (1 / 2 : ℝ) 2).trans (Path.segment 2 (1 / 2 : ℝ))

/-- The explicit one-cell grid labels the whole excursion by the right open
set.  Its times are literally `0` and `1`. -/
private def excursionGrid :
    SubordinatePathGrid
      (twoSetOpenCover leftOpen rightOpen leftOpen_isOpen rightOpen_isOpen)
      excursion where
  extraCells := 0
  time i := unitInterval.uniformGrid 1 i
  time_strictMono := unitInterval.uniformGrid_strictMono 0
  time_zero := unitInterval.uniformGrid_zero 1
  time_last := unitInterval.uniformGrid_last 0
  label _ := true
  subordinate k := by
    simp [twoSetOpenCover, rightOpen]

/-- This grid takes the right-cover branch and its only cell really leaves
the left open set; the branch is not selected merely by a redundant label. -/
example : excursionGrid.label 0 = true ∧
    ¬ Set.range (excursionGrid.cell 0) ⊆ leftOpen := by
  constructor
  · rfl
  · intro hsubset
    have hzero : excursionGrid.time (0 : Fin 2) = 0 := by
      change unitInterval.uniformGrid 1 0 = 0
      exact unitInterval.uniformGrid_zero 1
    have hone : excursionGrid.time ((0 : Fin 1).succ) = 1 := by
      change unitInterval.uniformGrid 1 1 = 1
      exact unitInterval.uniformGrid_top (by norm_num) le_rfl
    have hcellRange : Set.range (excursionGrid.cell 0) =
        Set.range excursion := by
      change Set.range (excursion.subpath (excursionGrid.time (0 : Fin 2))
        (excursionGrid.time ((0 : Fin 1).succ))) = Set.range excursion
      rw [hzero, hone]
      simp
    have htwoExcursion : (2 : ℝ) ∈ Set.range excursion := by
      change (2 : ℝ) ∈ Set.range
        ((Path.segment (1 / 2 : ℝ) 2).trans
          (Path.segment 2 (1 / 2 : ℝ)))
      rw [Path.trans_range]
      exact Or.inl ⟨1, (Path.segment (1 / 2 : ℝ) 2).target⟩
    have htwo : (2 : ℝ) ∈ Set.range (excursionGrid.cell 0) := by
      rwa [hcellRange]
    have := hsubset htwo
    norm_num [leftOpen] at this

/-- The explicit grid has literal source and target normalization.  This is
the endpoint shape needed by `openCoverGridLift`, without caller-supplied
casts between the real endpoints and their subtype representatives. -/
example :
    excursionGrid.cell 0 0 = (basepoint : ℝ) ∧
      excursionGrid.cell 0 1 = (basepoint : ℝ) := by
  constructor
  · rw [excursionGrid.cell_source]
    change excursion (unitInterval.uniformGrid 1 0) = (basepoint : ℝ)
    rw [unitInterval.uniformGrid_zero]
    exact excursion.source
  · rw [excursionGrid.cell_target]
    change excursion (unitInterval.uniformGrid 1 1) = (basepoint : ℝ)
    rw [unitInterval.uniformGrid_top (by norm_num) le_rfl]
    exact excursion.target

/-! The following helper supplies an actual essential-surjectivity witness
for the concrete contractible cover.  It is deliberately stated for any
map from a nonempty space to a path-connected space. -/

private theorem mapEssSurjOfNonemptyPathConnected
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [Nonempty S] [PathConnectedSpace T] (f : C(S, T)) :
    (FundamentalGroupoid.map f).EssSurj where
  mem_essImage := by
    rintro ⟨t⟩
    let s : S := Classical.choice (inferInstance : Nonempty S)
    let p : Path (f s) t := PathConnectedSpace.somePath (f s) t
    exact ⟨FundamentalGroupoid.mk s,
      ⟨(CategoryTheory.Groupoid.isoEquivHom _ _).symm
        (Path.Homotopic.Quotient.mk p)⟩⟩

private theorem overlap_nonempty : (leftOpen ∩ rightOpen).Nonempty := by
  exact ⟨1 / 2, by norm_num [leftOpen, rightOpen]⟩

private theorem overlapContractible :
    ContractibleSpace ↑(leftOpen ∩ rightOpen) :=
  ((convex_Iio (1 : ℝ)).inter convex_univ).contractibleSpace overlap_nonempty

private theorem rightContractible :
    ContractibleSpace ↑rightOpen :=
  (convex_univ : Convex ℝ rightOpen).contractibleSpace (by
    exact ⟨0, Set.mem_univ 0⟩)

/-- For the concrete cover, the public lift maps exactly to the original
excursion class.  Both structural hypotheses are genuine consequences of
contractibility rather than assumed test parameters. -/
example :
    ∃ q : FundamentalGroupoid.mk basepoint ⟶ FundamentalGroupoid.mk basepoint,
      (FundamentalGroupoid.map (inclusionSub leftOpen)).map q =
        Path.Homotopic.Quotient.mk excursion := by
  let _ : ContractibleSpace ↑(leftOpen ∩ rightOpen) := overlapContractible
  let _ : ContractibleSpace ↑rightOpen := rightContractible
  let _ : (FundamentalGroupoid.map
      (inclusionInterRight leftOpen rightOpen)).Full :=
    FundamentalGroupoid.SigmaSubtype.mapFullOfPathConnectedSimplyConnected
      (inclusionInterRight leftOpen rightOpen)
  let _ : (FundamentalGroupoid.map
      (inclusionInterRight leftOpen rightOpen)).EssSurj :=
    mapEssSurjOfNonemptyPathConnected (inclusionInterRight leftOpen rightOpen)
  exact ⟨openCoverGridLift leftOpen_isOpen rightOpen_isOpen realLine_cover
      excursion excursionGrid,
    openCoverGridLift_map leftOpen_isOpen rightOpen_isOpen realLine_cover
      excursion excursionGrid⟩

/-- The final van Kampen fullness theorem applies to the same concrete cover
with inferred path-connectedness and simple connectedness instances. -/
example : (FundamentalGroupoid.map (inclusionSub leftOpen)).Full := by
  let _ : ContractibleSpace ↑(leftOpen ∩ rightOpen) := overlapContractible
  let _ : ContractibleSpace ↑rightOpen := rightContractible
  let hFull : (FundamentalGroupoid.map
      (inclusionInterRight leftOpen rightOpen)).Full :=
    FundamentalGroupoid.SigmaSubtype.mapFullOfPathConnectedSimplyConnected
      (inclusionInterRight leftOpen rightOpen)
  let hEssSurj : (FundamentalGroupoid.map
      (inclusionInterRight leftOpen rightOpen)).EssSurj :=
    mapEssSurjOfNonemptyPathConnected (inclusionInterRight leftOpen rightOpen)
  exact inclusionSub_full_of_interRight_full_essSurj leftOpen_isOpen
    rightOpen_isOpen realLine_cover hFull hEssSurj

end MathlibExtTest.Topology.Homotopy.VanKampenFullnessTests

end

end
