/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import MathlibExt.Topology.CWComplex.CharacteristicDiskMap
import Mathlib.Topology.Homeomorph.Lemmas
import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbedding
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Classical CW amalgams along matching closed cell embeddings

Construct the classical CW structure on the actual `TopCat` pushout. The
matching data preserve every coordinate of the original closed characteristic
disks. The cell indices retain all left cells and the unmatched right cells.

No Hausdorff, finiteness or countability hypothesis is added to the matching
span. The CW fields follow from the original structures, the matching laws,
and closedness of the two input maps.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace Topology.CWComplex.MatchedAmalgam

private def cwOpenHomeomorph {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set X) n) :
    Metric.ball (0 : Fin n → ℝ) 1 ≃ₜ
      Topology.CWComplex.openCell (C := (Set.univ : Set X)) n j := by
  let p := Topology.CWComplex.map (C := (Set.univ : Set X)) n j
  let e : p.source ≃ₜ p.target :=
    { toEquiv := p.toEquiv
      continuous_toFun := by
        have hc : ContinuousOn p p.source :=
          (Topology.CWComplex.continuousOn (C := (Set.univ : Set X)) n j).mono
            (by
              rw [Topology.CWComplex.source_eq (C := (Set.univ : Set X)) n j]
              exact Metric.ball_subset_closedBall)
        exact hc.domRestrict.subtype_mk (fun x => p.map_source x.property)
      continuous_invFun :=
        (Topology.CWComplex.continuousOn_symm (C := (Set.univ : Set X)) n j).domRestrict.subtype_mk
          (fun x => p.map_target x.property) }
  have hs : p.source = Metric.ball (0 : Fin n → ℝ) 1 :=
    Topology.CWComplex.source_eq (C := (Set.univ : Set X)) n j
  have ht : p.target = Topology.CWComplex.openCell (C := (Set.univ : Set X)) n j := by
    calc
      p.target = p '' p.source := p.image_source_eq_target.symm
      _ = p '' Metric.ball 0 1 := by rw [hs]
      _ = _ := rfl
  exact (Homeomorph.setCongr hs.symm).trans (e.trans (Homeomorph.setCongr ht))

private theorem cwOpenHomeomorph_whole {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set X) n)
    (x : Metric.ball (0 : Fin n → ℝ) 1) :
    (cwOpenHomeomorph n j x).val = Topology.CWComplex.map (C := (Set.univ : Set X)) n j x.val := rfl

/-- The characteristic map embeds the original open ball. -/
public theorem openCellMap_isEmbedding {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set X) n) :
    IsEmbedding (fun x : Metric.ball (0 : Fin n → ℝ) 1 =>
      Topology.CWComplex.map (C := (Set.univ : Set X)) n j x.val) :=
  IsEmbedding.subtypeVal.comp (cwOpenHomeomorph n j).isEmbedding

/-- A cell partial equivalence with the given full characteristic function. -/
@[expose]
public def cellPartialEquivOfEmbedding {Y : Type u} [TopologicalSpace Y] (n : ℕ)
    (c : (Fin n → ℝ) → Y)
    (he : IsEmbedding (fun x : Metric.ball (0 : Fin n → ℝ) 1 => c x.val)) :
    PartialEquiv (Fin n → ℝ) Y :=
  Set.InjOn.toPartialEquiv c (Metric.ball (0 : Fin n → ℝ) 1)
    (by
      intro x hx y hy hxy
      exact congrArg Subtype.val (he.injective
        (show (fun x : Metric.ball (0 : Fin n → ℝ) 1 => c x.val) ⟨x, hx⟩ =
          (fun x : Metric.ball (0 : Fin n → ℝ) 1 => c x.val) ⟨y, hy⟩ from hxy)))

/-- The constructed partial equivalence retains every coordinate value. -/
public theorem cellPartialEquivOfEmbedding_apply {Y : Type u} [TopologicalSpace Y] (n : ℕ)
    (c : (Fin n → ℝ) → Y)
    (he : IsEmbedding (fun x : Metric.ball (0 : Fin n → ℝ) 1 => c x.val)) (x : Fin n → ℝ) :
    cellPartialEquivOfEmbedding n c he x = c x := (rfl)

/-- Its source is the original open unit ball. -/
public theorem cellPartialEquivOfEmbedding_source {Y : Type u} [TopologicalSpace Y] (n : ℕ)
    (c : (Fin n → ℝ) → Y)
    (he : IsEmbedding (fun x : Metric.ball (0 : Fin n → ℝ) 1 => c x.val)) :
    (cellPartialEquivOfEmbedding n c he).source = Metric.ball (0 : Fin n → ℝ) 1 := (rfl)

/-- Its target is the original open-cell image. -/
public theorem cellPartialEquivOfEmbedding_target {Y : Type u} [TopologicalSpace Y] (n : ℕ)
    (c : (Fin n → ℝ) → Y)
    (he : IsEmbedding (fun x : Metric.ball (0 : Fin n → ℝ) 1 => c x.val)) :
    (cellPartialEquivOfEmbedding n c he).target =
      Set.range (fun x : Metric.ball (0 : Fin n → ℝ) 1 => c x.val) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, hxy⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, x.property, rfl⟩

/-- The inverse is continuous on the open-cell image. -/
public theorem cellPartialEquivOfEmbedding_continuousOn_symm {Y : Type u} [TopologicalSpace Y]
    (n : ℕ) (c : (Fin n → ℝ) → Y)
    (he : IsEmbedding (fun x : Metric.ball (0 : Fin n → ℝ) 1 => c x.val)) :
    ContinuousOn (cellPartialEquivOfEmbedding n c he).symm
        (cellPartialEquivOfEmbedding n c he).target := by
  let p := cellPartialEquivOfEmbedding n c he
  let e : Metric.ball (0 : Fin n → ℝ) 1 ≃ₜ p.target :=
    he.toHomeomorph.trans (Homeomorph.setCongr (cellPartialEquivOfEmbedding_target n c he).symm)
  have h : ∀ y : p.target, p.symm y.val = (e.symm y).val := by
    intro y
    let x := e.symm y
    have hpx : p x.val = y.val := by
      exact congrArg Subtype.val (e.apply_symm_apply y)
    rw [← hpx]
    exact p.left_inv x.property
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (p.target.domRestrict p.symm) =
      (fun y : p.target => (e.symm y).val) := funext h
  rw [heq]
  exact continuous_subtype_val.comp e.symm.continuous

private def embeddedCwCell {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [Topology.CWComplex (Set.univ : Set X)] (f : C(X, Y)) (hf : IsEmbedding f)
    (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set X) n) :
    PartialEquiv (Fin n → ℝ) Y :=
  cellPartialEquivOfEmbedding n
    (fun x => f (Topology.CWComplex.map (C := (Set.univ : Set X)) n j x))
    (hf.comp (openCellMap_isEmbedding n j))

private theorem embeddedCwCell_whole {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [Topology.CWComplex (Set.univ : Set X)] (f : C(X, Y)) (hf : IsEmbedding f)
    (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set X) n) (x : Fin n → ℝ) :
    embeddedCwCell f hf n j x = f (Topology.CWComplex.map (C := (Set.univ : Set X)) n j x) := rfl

private theorem embeddedCwCell_continuousOn {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set X)]
    (f : C(X, Y)) (hf : IsEmbedding f) (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set X) n) :
    ContinuousOn (embeddedCwCell f hf n j) (Metric.closedBall (0 : Fin n → ℝ) 1) :=
  f.continuous.comp_continuousOn (Topology.CWComplex.continuousOn (C := (Set.univ : Set X)) n j)


variable {C A B : TopCat.{u}}
variable [Topology.CWComplex (Set.univ : Set C)]
variable [Topology.CWComplex (Set.univ : Set A)]
variable [Topology.CWComplex (Set.univ : Set B)]

/-- Degree-preserving cell embeddings intertwining both entire closed disks. -/
public structure MatchingCharacteristicData (f : C ⟶ A) (g : C ⟶ B) where
  /-- Sends each `n`-cell `j` of `C` to the `n`-cell of `A` whose characteristic map, on the
  closed disk, is that of `j` followed by `f` (`leftLaw`). -/
  leftLabels : ∀ n, Topology.CWComplex.cell (Set.univ : Set C) n ↪
    Topology.CWComplex.cell (Set.univ : Set A) n
  /-- Sends each `n`-cell `j` of `C` to the `n`-cell of `B` whose characteristic map, on the
  closed disk, is that of `j` followed by `g` (`rightLaw`). -/
  rightLabels : ∀ n, Topology.CWComplex.cell (Set.univ : Set C) n ↪
    Topology.CWComplex.cell (Set.univ : Set B) n
  leftLaw : ∀ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set C) n)
    (x : Metric.closedBall (0 : Fin n → ℝ) 1),
    f (Topology.CWComplex.map (C := (Set.univ : Set C)) n j x.val) =
      Topology.CWComplex.map (C := (Set.univ : Set A)) n (leftLabels n j) x.val
  rightLaw : ∀ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set C) n)
    (x : Metric.closedBall (0 : Fin n → ℝ) 1),
    g (Topology.CWComplex.map (C := (Set.univ : Set C)) n j x.val) =
      Topology.CWComplex.map (C := (Set.univ : Set B)) n (rightLabels n j) x.val

/-- All left cells together with the right cells outside the matching image. -/
public abbrev Cell {f : C ⟶ A} {g : C ⟶ B} (d : MatchingCharacteristicData f g) (n : ℕ) :=
  Topology.CWComplex.cell (Set.univ : Set A) n ⊕
    {b : Topology.CWComplex.cell (Set.univ : Set B) n // b ∉ Set.range (d.rightLabels n)}

omit [Topology.CWComplex (Set.univ : Set C)] [Topology.CWComplex (Set.univ : Set A)]
  [Topology.CWComplex (Set.univ : Set B)] in
/-- The left pushout leg is closed when the right input map is closed. -/
public theorem inl_isClosedEmbedding (f : C ⟶ A) (g : C ⟶ B)
    (hg : IsClosedEmbedding g) : IsClosedEmbedding (pushout.inl f g) :=
  TopCat.isClosedEmbedding_of_isPushout (IsPushout.of_hasPushout f g).flip hg

omit [Topology.CWComplex (Set.univ : Set C)] [Topology.CWComplex (Set.univ : Set A)]
  [Topology.CWComplex (Set.univ : Set B)] in
/-- The right pushout leg is closed when the left input map is closed. -/
public theorem inr_isClosedEmbedding (f : C ⟶ A) (g : C ⟶ B)
    (hf : IsClosedEmbedding f) : IsClosedEmbedding (pushout.inr f g) :=
  TopCat.isClosedEmbedding_of_isPushout (IsPushout.of_hasPushout f g) hf

/-- The original left and right characteristic functions in the actual pushout. -/
public def cellMap {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (n : ℕ) : Cell d n → (Fin n → ℝ) →
        (pushout f g : TopCat.{u})
  | Sum.inl a, x => pushout.inl f g (Topology.CWComplex.map (C := (Set.univ : Set A)) n a x)
  | Sum.inr b, x => pushout.inr f g (Topology.CWComplex.map (C := (Set.univ : Set B)) n b.val x)

/-- The corresponding open-cell partial equivalences in the actual pushout. -/
public def cellPartialEquiv {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (n : ℕ) : Cell d n → PartialEquiv (Fin n → ℝ) ((pushout f g : TopCat.{u}))
  | Sum.inl a => embeddedCwCell (pushout.inl f g).hom
      (inl_isClosedEmbedding f g hg).isEmbedding n a
  | Sum.inr b => embeddedCwCell (pushout.inr f g).hom
      (inr_isClosedEmbedding f g hf).isEmbedding n b.val

/-- The partial equivalences retain the full characteristic functions. -/
public theorem cellPartialEquiv_apply {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (n : ℕ) (j : Cell d n) (x : Fin n → ℝ) :
    cellPartialEquiv d hf hg n j x = cellMap d n j x := by
  cases j <;> rfl

private theorem cellPartialEquiv_toFun {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (n : ℕ) (j : Cell d n) :
    (cellPartialEquiv d hf hg n j : (Fin n → ℝ) → (pushout f g : TopCat.{u})) =
      cellMap d n j := funext (cellPartialEquiv_apply d hf hg n j)

private theorem cellPartialEquiv_source {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (n : ℕ) (j : Cell d n) :
    (cellPartialEquiv d hf hg n j).source = Metric.ball (0 : Fin n → ℝ) 1 := by
  cases j <;> rfl

private theorem cellPartialEquiv_continuousOn {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (n : ℕ) (j : Cell d n) :
    ContinuousOn (cellPartialEquiv d hf hg n j) (Metric.closedBall (0 : Fin n → ℝ) 1) := by
  cases j with
  | inl a =>
      exact embeddedCwCell_continuousOn (pushout.inl f g).hom
        (inl_isClosedEmbedding f g hg).isEmbedding n a
  | inr b =>
      exact embeddedCwCell_continuousOn (pushout.inr f g).hom
        (inr_isClosedEmbedding f g hf).isEmbedding n b.val

private theorem cellPartialEquiv_continuousOn_symm {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (n : ℕ) (j : Cell d n) :
    ContinuousOn (cellPartialEquiv d hf hg n j).symm
      (cellPartialEquiv d hf hg n j).target := by
  cases j with
  | inl a =>
      exact cellPartialEquivOfEmbedding_continuousOn_symm n
        (fun x => pushout.inl f g (Topology.CWComplex.map (C := (Set.univ : Set A)) n a x))
        ((inl_isClosedEmbedding f g hg).isEmbedding.comp (openCellMap_isEmbedding n a))
  | inr b =>
      exact cellPartialEquivOfEmbedding_continuousOn_symm n
        (fun x => pushout.inr f g (Topology.CWComplex.map (C := (Set.univ : Set B)) n b.val x))
        ((inr_isClosedEmbedding f g hf).isEmbedding.comp (openCellMap_isEmbedding n b.val))

/-- Transfer each right cell to its actual cell in the pushout. -/
public def rightCellTransfer {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (n : ℕ)
    (b : Topology.CWComplex.cell (Set.univ : Set B) n) : Cell d n := by
  classical
  exact if hb : b ∈ Set.range (d.rightLabels n) then
    Sum.inl (d.leftLabels n (Classical.choose (Set.mem_range.mp hb)))
  else Sum.inr ⟨b, hb⟩

/-- Right-cell transfer preserves the entire original closed disk. -/
public theorem rightCellTransfer_closed_characteristic {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (n : ℕ)
    (b : Topology.CWComplex.cell (Set.univ : Set B) n)
    (x : Metric.closedBall (0 : Fin n → ℝ) 1) :
    pushout.inr f g (Topology.CWComplex.map (C := (Set.univ : Set B)) n b x.val) =
      cellMap d n (rightCellTransfer d n b) x.val := by
  classical
  by_cases hb : b ∈ Set.range (d.rightLabels n)
  · rw [rightCellTransfer, dite_eq_left hb]
    let c := Classical.choose (Set.mem_range.mp hb)
    have hc : d.rightLabels n c = b := Classical.choose_spec (Set.mem_range.mp hb)
    change pushout.inr f g (Topology.CWComplex.map (C := (Set.univ : Set B)) n b x.val) =
      pushout.inl f g (Topology.CWComplex.map (C := (Set.univ : Set A)) n (d.leftLabels n c) x.val)
    rw [← hc, ← d.rightLaw n c x]
    calc
      _ = pushout.inl f g (f (Topology.CWComplex.map (C := (Set.univ : Set C)) n c x.val)) :=
        (ConcreteCategory.congr_hom (pushout.condition (f := f) (g := g))
          (Topology.CWComplex.map (C := (Set.univ : Set C)) n c x.val)).symm
      _ = _ := congrArg (pushout.inl f g) (d.leftLaw n c x)
  · rw [rightCellTransfer, dite_eq_right hb]
    rfl

private theorem amalgamCell_mapsTo_finite_lower {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (n : ℕ) (j : Cell d n) :
    ∃ I : ∀ m, Finset (Cell d m),
      Set.MapsTo (cellMap d n j) (Metric.sphere (0 : Fin n → ℝ) 1)
        (⋃ (m < n) (b ∈ I m), cellMap d m b '' Metric.closedBall 0 1) := by
  classical
  cases j with
  | inl a =>
      obtain ⟨I, hI⟩ := Topology.CWComplex.mapsTo' (C := (Set.univ : Set A)) n a
      refine ⟨fun m => (I m).image Sum.inl, ?_⟩
      intro x hx
      have hmem := hI hx
      simp only [Set.mem_iUnion, Set.mem_image] at hmem ⊢
      rcases hmem with ⟨m, hm, b, hb, y, hy, hxy⟩
      refine ⟨m, hm, Sum.inl b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, y, hy, ?_⟩
      exact congrArg (pushout.inl f g) hxy
  | inr b =>
      obtain ⟨I, hI⟩ := Topology.CWComplex.mapsTo' (C := (Set.univ : Set B)) n b.val
      refine ⟨fun m => (I m).image (rightCellTransfer d m), ?_⟩
      intro x hx
      have hmem := hI hx
      simp only [Set.mem_iUnion, Set.mem_image] at hmem ⊢
      rcases hmem with ⟨m, hm, a, ha, y, hy, hxy⟩
      refine ⟨m, hm, rightCellTransfer d m a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, y, hy, ?_⟩
      exact (rightCellTransfer_closed_characteristic d m a ⟨y, hy⟩).symm.trans
        (congrArg (pushout.inr f g) hxy)

private theorem amalgamPartial_mapsTo_finite_lower {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (n : ℕ) (j : Cell d n) :
    ∃ I : ∀ m, Finset (Cell d m),
      Set.MapsTo (cellPartialEquiv d hf hg n j) (Metric.sphere (0 : Fin n → ℝ) 1)
        (⋃ (m < n) (b ∈ I m), cellPartialEquiv d hf hg m b '' Metric.closedBall 0 1) := by
  simpa only [cellPartialEquiv_toFun] using amalgamCell_mapsTo_finite_lower d n j

private theorem matchingRight_openImage {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set C) n) :
    g '' Topology.CWComplex.openCell (C := (Set.univ : Set C)) n j =
      Topology.CWComplex.openCell (C := (Set.univ : Set B)) n (d.rightLabels n j) := by
  ext z
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (d.rightLaw n j ⟨x, Metric.ball_subset_closedBall hx⟩).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Topology.CWComplex.map (C := (Set.univ : Set C)) n j x,
      ⟨x, hx, rfl⟩, d.rightLaw n j ⟨x, Metric.ball_subset_closedBall hx⟩⟩

/-- The right matching image, with its original degree-preserving labels. -/
@[expose]
public def matchingRightSubcomplex {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hg : IsClosedEmbedding g) :
    Topology.CWComplex.Subcomplex (Set.univ : Set B) where
  carrier := Set.range g
  I n := Set.range (d.rightLabels n)
  closed' := hg.isClosed_range
  union' := by
    rw [Set.empty_union]
    ext z
    constructor
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨n, hn⟩
      rcases Set.mem_iUnion.mp hn with ⟨j, hj⟩
      rcases j.property with ⟨k, hk⟩
      have h : z ∈ Topology.CWComplex.openCell
          (C := (Set.univ : Set B)) n (d.rightLabels n k) := by
        rw [hk]
        exact hj
      rw [← matchingRight_openImage d n k] at h
      rcases h with ⟨x, _, hx⟩
      exact ⟨x, hx⟩
    · rintro ⟨x, rfl⟩
      have hx : x ∈ ⋃ (n : ℕ)
          (j : Topology.CWComplex.cell (Set.univ : Set C) n),
              Topology.CWComplex.openCell (C := (Set.univ : Set C)) n j := by
        exact (Topology.CWComplex.iUnion_openCell_eq_complex
          (C := (Set.univ : Set C))).symm ▸ Set.mem_univ x
      rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
      rcases Set.mem_iUnion.mp hn with ⟨j, hj⟩
      have htarget : g x ∈ Topology.CWComplex.openCell
          (C := (Set.univ : Set B)) n (d.rightLabels n j) := by
        rw [← matchingRight_openImage d n j]
        exact ⟨x, hj, rfl⟩
      exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr
        ⟨⟨d.rightLabels n j, ⟨j, rfl⟩⟩, htarget⟩⟩

private theorem newRight_openCell_disjoint_range {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hg : IsClosedEmbedding g) (n : ℕ)
    (b : {b : Topology.CWComplex.cell (Set.univ : Set B) n // b ∉ Set.range (d.rightLabels n)}) :
    Disjoint (Topology.CWComplex.openCell (C := (Set.univ : Set B)) n b.val) (Set.range g) := by
  exact Topology.CWComplex.Subcomplex.disjoint_openCell_subcomplex_of_notMem
    (matchingRightSubcomplex d hg) b.property

private theorem newRightCell_disjoint_leftRange {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (n : ℕ)
    (b : {b : Topology.CWComplex.cell (Set.univ : Set B) n // b ∉ Set.range (d.rightLabels n)}) :
    Disjoint (cellMap d n (Sum.inr b) '' Metric.ball 0 1) (Set.range (pushout.inl f g)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, hzx⟩ ⟨y, hy⟩
  let v := Topology.CWComplex.map (C := (Set.univ : Set B)) n b.val x
  have hv : v ∈ Topology.CWComplex.openCell (C := (Set.univ : Set B)) n b.val := ⟨x, hx, rfl⟩
  have heq : pushout.inl f g y = pushout.inr f g v := hy.trans hzx.symm
  let ht := (IsPushout.of_hasPushout f g).map (forget TopCat)
  obtain ⟨c, _, hc⟩ :=
    (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit ht.isColimit hf.injective y v).mp heq
  exact (newRight_openCell_disjoint_range d hg n b).notMem_of_mem_left hv ⟨c, hc⟩

private theorem disjoint_image_of_injective {X Y : Type*} (f : X → Y) (hf : Function.Injective f)
    {S T : Set X} (h : Disjoint S T) : Disjoint (f '' S) (f '' T) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
  exact h.notMem_of_mem_left hx (by
    have hzx := hf (hzy.trans hxy.symm)
    rwa [hzx] at hz)

private theorem amalgamOpenCell_left_image {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (n : ℕ)
    (a : Topology.CWComplex.cell (Set.univ : Set A) n) :
    cellMap d n (Sum.inl a) '' Metric.ball 0 1 =
      (pushout.inl f g) '' Topology.CWComplex.openCell (C := (Set.univ : Set A)) n a := by
  change ((pushout.inl f g) ∘ Topology.CWComplex.map (C := (Set.univ : Set A)) n a) ''
      Metric.ball 0 1 =
    (pushout.inl f g) ''
      (Topology.CWComplex.map (C := (Set.univ : Set A)) n a '' Metric.ball 0 1)
  rw [Set.image_image]
  rfl

private theorem amalgamOpenCell_right_image {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (n : ℕ)
    (b : {b : Topology.CWComplex.cell (Set.univ : Set B) n // b ∉ Set.range (d.rightLabels n)}) :
    cellMap d n (Sum.inr b) '' Metric.ball 0 1 =
      (pushout.inr f g) '' Topology.CWComplex.openCell (C := (Set.univ : Set B)) n b.val := by
  change ((pushout.inr f g) ∘ Topology.CWComplex.map (C := (Set.univ : Set B)) n b.val) ''
      Metric.ball 0 1 =
    (pushout.inr f g) ''
      (Topology.CWComplex.map (C := (Set.univ : Set B)) n b.val '' Metric.ball 0 1)
  rw [Set.image_image]
  rfl

private theorem amalgamCell_pairwiseDisjoint {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    (Set.univ : Set (Σ n, Cell d n)).PairwiseDisjoint
      (fun j => cellMap d j.fst j.snd '' Metric.ball 0 1) := by
  rintro ⟨n, a⟩ _ ⟨m, b⟩ _ hne
  change Disjoint (cellMap d n a '' Metric.ball 0 1)
    (cellMap d m b '' Metric.ball 0 1)
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          have hAB : (⟨n, a⟩ : Σ k, Topology.CWComplex.cell (Set.univ : Set A) k) ≠ ⟨m, b⟩ := by
            intro h
            exact hne (congrArg
              (fun j : Σ k, Topology.CWComplex.cell (Set.univ : Set A) k =>
                (⟨j.fst, Sum.inl j.snd⟩ : Σ k, Cell d k)) h)
          rw [amalgamOpenCell_left_image, amalgamOpenCell_left_image]
          exact disjoint_image_of_injective _ (inl_isClosedEmbedding f g hg).injective
            (Topology.CWComplex.disjoint_openCell_of_ne hAB)
      | inr b =>
          exact (newRightCell_disjoint_leftRange d hf hg m b).symm.mono_left
            (by rintro z ⟨x, hx, h⟩; exact ⟨Topology.CWComplex.map n a x, h⟩)
  | inr a =>
      cases b with
      | inl b =>
          exact (newRightCell_disjoint_leftRange d hf hg n a).mono_right
            (by rintro z ⟨x, hx, h⟩; exact ⟨Topology.CWComplex.map m b x, h⟩)
      | inr b =>
          have hAB : (⟨n, a.val⟩ : Σ k, Topology.CWComplex.cell (Set.univ : Set B) k) ≠
              ⟨m, b.val⟩ := by
            intro h
            have hn : n = m := (Sigma.mk.inj_iff.mp h).1
            cases hn
            have hab : a = b := Subtype.ext (sigma_mk_injective h)
            subst b
            exact hne rfl
          rw [amalgamOpenCell_right_image, amalgamOpenCell_right_image]
          exact disjoint_image_of_injective _ (inr_isClosedEmbedding f g hf).injective
            (Topology.CWComplex.disjoint_openCell_of_ne hAB)

private theorem preimage_inter_image_injective {X Y : Type*} (f : X → Y) (hf : Function.Injective f)
    (S : Set Y) (K : Set X) : f ⁻¹' (S ∩ f '' K) = f ⁻¹' S ∩ K := by
  ext x
  constructor
  · rintro ⟨hx, y, hy, hyx⟩
    exact ⟨hx, by have h := hf hyx; rwa [h] at hy⟩
  · rintro ⟨hx, hxK⟩
    exact ⟨hx, x, hxK, rfl⟩

private theorem amalgamClosedCell_left_image {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (n : ℕ)
    (a : Topology.CWComplex.cell (Set.univ : Set A) n) :
    cellMap d n (Sum.inl a) '' Metric.closedBall 0 1 =
      (pushout.inl f g) '' Topology.CWComplex.closedCell (C := (Set.univ : Set A)) n a := by
  change ((pushout.inl f g) ∘ Topology.CWComplex.map (C := (Set.univ : Set A)) n a) ''
      Metric.closedBall 0 1 =
    (pushout.inl f g) ''
      (Topology.CWComplex.map (C := (Set.univ : Set A)) n a '' Metric.closedBall 0 1)
  rw [Set.image_image]
  rfl

private theorem amalgamClosedCell_right_transfer_image {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (n : ℕ)
    (b : Topology.CWComplex.cell (Set.univ : Set B) n) :
    cellMap d n (rightCellTransfer d n b) '' Metric.closedBall 0 1 =
      (pushout.inr f g) '' Topology.CWComplex.closedCell (C := (Set.univ : Set B)) n b := by
  ext z
  constructor
  · rintro ⟨x, hx, hzx⟩
    exact ⟨Topology.CWComplex.map (C := (Set.univ : Set B)) n b x, ⟨x, hx, rfl⟩,
      (rightCellTransfer_closed_characteristic d n b ⟨x, hx⟩).trans hzx⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, hzx⟩
    exact ⟨x, hx, (rightCellTransfer_closed_characteristic d n b ⟨x, hx⟩).symm.trans hzx⟩

private theorem amalgamCell_closed_of_intersections {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (S : Set ((pushout f g : TopCat.{u})))
    (hS : ∀ (n : ℕ) (j : Cell d n),
      IsClosed (S ∩ (cellMap d n j '' Metric.closedBall 0 1))) : IsClosed S := by
  have hA : IsClosed ((pushout.inl f g) ⁻¹' S) :=
    Topology.CWComplex.closed' (C := (Set.univ : Set A)) _ (Set.subset_univ _) (by
      intro n a
      have h := (hS n (Sum.inl a)).preimage (pushout.inl f g).hom.continuous
      rw [amalgamClosedCell_left_image, preimage_inter_image_injective _
        (inl_isClosedEmbedding f g hg).injective] at h
      exact h)
  have hB : IsClosed ((pushout.inr f g) ⁻¹' S) :=
    Topology.CWComplex.closed' (C := (Set.univ : Set B)) _ (Set.subset_univ _) (by
      intro n b
      have h := (hS n (rightCellTransfer d n b)).preimage (pushout.inr f g).hom.continuous
      rw [amalgamClosedCell_right_transfer_image, preimage_inter_image_injective _
        (inr_isClosedEmbedding f g hf).injective] at h
      exact h)
  let sq := IsPushout.of_hasPushout f g
  apply (TopCat.isClosed_iff_of_isColimit sq.cocone sq.isColimit S).mpr
  rintro (_ | _ | _)
  · change IsClosed (f ⁻¹' ((pushout.inl f g) ⁻¹' S))
    exact hA.preimage f.hom.continuous
  · exact hA
  · exact hB

private theorem amalgamCell_union {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) :
    (⋃ (n : ℕ) (j : Cell d n), cellMap d n j '' Metric.closedBall 0 1) = Set.univ := by
  ext z
  constructor
  · intro _
    exact Set.mem_univ z
  · intro _
    rcases Types.eq_or_eq_of_isPushout ((IsPushout.of_hasPushout f g).map (forget TopCat))
        z with hz | hz
    · rcases hz with ⟨a, rfl⟩
      have ha : a ∈ ⋃ (n : ℕ)
          (j : Topology.CWComplex.cell (Set.univ : Set A) n),
              Topology.CWComplex.map n j '' Metric.closedBall 0 1 := by
        rw [Topology.CWComplex.union']
        exact Set.mem_univ a
      simp only [Set.mem_iUnion, Set.mem_image] at ha ⊢
      rcases ha with ⟨n, j, x, hx, hxa⟩
      exact ⟨n, Sum.inl j, x, hx, congrArg (pushout.inl f g) hxa⟩
    · rcases hz with ⟨b, rfl⟩
      have hb : b ∈ ⋃ (n : ℕ)
          (j : Topology.CWComplex.cell (Set.univ : Set B) n),
              Topology.CWComplex.map n j '' Metric.closedBall 0 1 := by
        rw [Topology.CWComplex.union']
        exact Set.mem_univ b
      simp only [Set.mem_iUnion, Set.mem_image] at hb ⊢
      rcases hb with ⟨n, j, x, hx, hxb⟩
      exact ⟨n, rightCellTransfer d n j, x, hx,
        (rightCellTransfer_closed_characteristic d n j ⟨x, hx⟩).symm.trans
          (congrArg (pushout.inr f g) hxb)⟩

/-- The classical CW structure on the actual pushout of a matching closed span. -/
@[expose, instance_reducible]
public def classicalCWComplex {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) where
  cell := Cell d
  map := cellPartialEquiv d hf hg
  source_eq := by
    exact cellPartialEquiv_source d hf hg
  continuousOn := by
    exact cellPartialEquiv_continuousOn d hf hg
  continuousOn_symm := by
    exact cellPartialEquiv_continuousOn_symm d hf hg
  pairwiseDisjoint' := by
    simpa only [cellPartialEquiv_toFun] using amalgamCell_pairwiseDisjoint d hf hg
  mapsTo' := by
    exact amalgamPartial_mapsTo_finite_lower d hf hg
  closed' S _ hS := by
    exact amalgamCell_closed_of_intersections d hf hg S (by
      simpa only [cellPartialEquiv_toFun] using hS)
  union' := by
    simpa only [cellPartialEquiv_toFun] using amalgamCell_union d

/-- Every left characteristic coordinate is retained by the left pushout leg. -/
public theorem left_characteristic {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (n : ℕ) (a : Topology.CWComplex.cell (Set.univ : Set A) n) (x : Fin n → ℝ) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
        classicalCWComplex d hf hg
    Topology.CWComplex.map (C := (Set.univ : Set ((pushout f g : TopCat.{u})))) n (Sum.inl a) x =
      pushout.inl f g (Topology.CWComplex.map (C := (Set.univ : Set A)) n a x) := (rfl)

/-- Every unmatched-right characteristic coordinate is retained by the right leg. -/
public theorem newRight_characteristic {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (n : ℕ)
    (b : {b : Topology.CWComplex.cell (Set.univ : Set B) n // b ∉ Set.range (d.rightLabels n)})
    (x : Fin n → ℝ) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
        classicalCWComplex d hf hg
    Topology.CWComplex.map (C := (Set.univ : Set ((pushout f g : TopCat.{u})))) n (Sum.inr b) x =
      pushout.inr f g (Topology.CWComplex.map (C := (Set.univ : Set B)) n b.val x) := (rfl)


/-- Right-cell transfer is injective in every dimension. -/
public theorem rightCellTransfer_injective {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (m : ℕ) :
    Function.Injective (rightCellTransfer d m) := by
  classical
  intro b c hbc
  by_cases hb : b ∈ Set.range (d.rightLabels m)
  · by_cases hc : c ∈ Set.range (d.rightLabels m)
    · simp only [rightCellTransfer, dite_eq_left hb, dite_eq_left hc] at hbc
      have hk := (d.leftLabels m).injective (Sum.inl.inj hbc)
      exact (Classical.choose_spec hb).symm.trans
        ((congrArg (d.rightLabels m) hk).trans (Classical.choose_spec hc))
    · simp only [rightCellTransfer, dite_eq_left hb, dite_eq_right hc] at hbc
      cases hbc
  · by_cases hc : c ∈ Set.range (d.rightLabels m)
    · simp only [rightCellTransfer, dite_eq_right hb, dite_eq_left hc] at hbc
      cases hbc
    · simp only [rightCellTransfer, dite_eq_right hb, dite_eq_right hc] at hbc
      exact congrArg Subtype.val (Sum.inr.inj hbc)


/-- Swap the two sides of the same matching span. -/
public def MatchingCharacteristicData.flip {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) : MatchingCharacteristicData g f where
  leftLabels := d.rightLabels
  rightLabels := d.leftLabels
  leftLaw := d.rightLaw
  rightLaw := d.leftLaw

/-- The left matching image with its original labels. -/
public def matchingLeftSubcomplex {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) :
    Topology.CWComplex.Subcomplex (Set.univ : Set A) :=
  matchingRightSubcomplex d.flip hf

@[simp]
public theorem matchingRightSubcomplex_carrier {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hg : IsClosedEmbedding g) :
    (matchingRightSubcomplex d hg : Set B) = Set.range g := (rfl)

@[simp]
public theorem matchingRightSubcomplex_I {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hg : IsClosedEmbedding g) (n : ℕ) :
    (matchingRightSubcomplex d hg).I n = Set.range (d.rightLabels n) := (rfl)

@[simp]
public theorem matchingLeftSubcomplex_carrier {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) :
    (matchingLeftSubcomplex d hf : Set A) = Set.range f := (rfl)

@[simp]
public theorem matchingLeftSubcomplex_I {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (n : ℕ) :
    (matchingLeftSubcomplex d hf).I n = Set.range (d.leftLabels n) := (rfl)

/-- The degree-preserving left cell embedding in the constructed CW structure. -/
public def leftCellEmbedding {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (n : ℕ) :
    Topology.CWComplex.cell (Set.univ : Set A) n ↪ Cell d n :=
  Function.Embedding.inl

/-- The degree-preserving right cell embedding, including the matching cells. -/
public def rightCellEmbedding {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (n : ℕ) :
    Topology.CWComplex.cell (Set.univ : Set B) n ↪ Cell d n :=
  ⟨rightCellTransfer d n, rightCellTransfer_injective d n⟩

/-- Every right cell has its original characteristic map on the full closed disk. -/
public theorem right_characteristic {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (n : ℕ) (b : Topology.CWComplex.cell (Set.univ : Set B) n)
    (x : Metric.closedBall (0 : Fin n → ℝ) 1) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
        classicalCWComplex d hf hg
    Topology.CWComplex.map (C := (Set.univ : Set ((pushout f g : TopCat.{u})))) n
        (rightCellTransfer d n b) x.val =
      pushout.inr f g (Topology.CWComplex.map (C := (Set.univ : Set B)) n b x.val) := by
  let : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
      classicalCWComplex d hf hg
  change cellPartialEquiv d hf hg n (rightCellTransfer d n b) x.val = _
  exact (cellPartialEquiv_apply d hf hg n (rightCellTransfer d n b) x.val).trans
    (rightCellTransfer_closed_characteristic d n b x).symm

/-- The entire left characteristic disk commutes with the left pushout leg. -/
public theorem left_characteristicDiskMap {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (n : ℕ) (a : Topology.CWComplex.cell (Set.univ : Set A) n) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
        classicalCWComplex d hf hg
    characteristicDiskMap (X := (pushout f g : TopCat.{u})) n (Sum.inl a) =
      characteristicDiskMap (X := A) n a ≫ pushout.inl f g := by
  let : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
      classicalCWComplex d hf hg
  ext x
  simpa only [TopCat.comp_app, characteristicDiskMap_apply] using!
    left_characteristic d hf hg n a x.down.val

/-- The entire right characteristic disk commutes with the right pushout leg. -/
public theorem right_characteristicDiskMap {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (n : ℕ) (b : Topology.CWComplex.cell (Set.univ : Set B) n) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
        classicalCWComplex d hf hg
    characteristicDiskMap (X := (pushout f g : TopCat.{u})) n (rightCellTransfer d n b) =
      characteristicDiskMap (X := B) n b ≫ pushout.inr f g := by
  let : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
      classicalCWComplex d hf hg
  ext x
  simpa only [TopCat.comp_app, characteristicDiskMap_apply] using!
    right_characteristic d hf hg n b x.down

/-- The whole left summand is a CW subcomplex of the constructed pushout. -/
public def leftSubcomplex {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
        classicalCWComplex d hf hg
    Topology.CWComplex.Subcomplex (Set.univ : Set ((pushout f g : TopCat.{u}))) := by
  letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
      classicalCWComplex d hf hg
  let e : MatchingCharacteristicData (𝟙 A) (pushout.inl f g) :=
    { leftLabels := fun _ => Function.Embedding.refl _
      rightLabels := leftCellEmbedding d
      leftLaw := fun _ _ _ => rfl
      rightLaw := fun n j x => (left_characteristic d hf hg n j x.val).symm }
  exact matchingRightSubcomplex e (inl_isClosedEmbedding f g hg)

/-- The whole right summand is a CW subcomplex of the constructed pushout. -/
public def rightSubcomplex {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
        classicalCWComplex d hf hg
    Topology.CWComplex.Subcomplex (Set.univ : Set ((pushout f g : TopCat.{u}))) := by
  letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
      classicalCWComplex d hf hg
  let e : MatchingCharacteristicData (𝟙 B) (pushout.inr f g) :=
    { leftLabels := fun _ => Function.Embedding.refl _
      rightLabels := rightCellEmbedding d
      leftLaw := fun _ _ _ => rfl
      rightLaw := fun n j x => (right_characteristic d hf hg n j x).symm }
  exact matchingRightSubcomplex e (inr_isClosedEmbedding f g hf)

@[simp]
public theorem leftSubcomplex_carrier {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
        classicalCWComplex d hf hg
    (leftSubcomplex d hf hg : Set ((pushout f g : TopCat.{u}))) =
        Set.range (pushout.inl f g) := (rfl)

@[simp]
public theorem leftSubcomplex_I {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (n : ℕ) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
        classicalCWComplex d hf hg
    (leftSubcomplex d hf hg).I n = Set.range (leftCellEmbedding d n) := (rfl)

@[simp]
public theorem rightSubcomplex_carrier {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
        classicalCWComplex d hf hg
    (rightSubcomplex d hf hg : Set ((pushout f g : TopCat.{u}))) =
        Set.range (pushout.inr f g) := (rfl)

@[simp]
public theorem rightSubcomplex_I {f : C ⟶ A} {g : C ⟶ B}
    (d : MatchingCharacteristicData f g) (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (n : ℕ) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
        classicalCWComplex d hf hg
    (rightSubcomplex d hf hg).I n = Set.range (rightCellEmbedding d n) := (rfl)

end Topology.CWComplex.MatchedAmalgam
