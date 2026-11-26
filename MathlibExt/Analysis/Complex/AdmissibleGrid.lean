/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.Complex.RectilinearCycle
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.BoxIntegral.Partition.Additive
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Complex.Tietze

/-!
# Finite oriented grid contours

A grid index is a pair of integers. At positive scale `t`, its physical
vertex is `(v₀/t, v₁/t)` and each cell has side length `1/t`. A finite
filling is a positive scale and a finite set of selected cells, possibly
empty. Unrestricted vertex formulas use total real division, including
`x/0 = 0`; nondegenerate fillings and half-open boxes use positive scale.

Horizontal edges point right and vertical edges point up. Horizontal
boundary coefficients are the selected-cell indicator above minus that
below; vertical coefficients are the indicator on the left minus that
on the right. Internal edges cancel. The associated cycle is the sum of
counterclockwise cell boundaries. Its reduced trace is the finite union
of edges with nonzero coefficients. Integer-weighted edge integration
uses the stated complete complex normed target spaces and their norms.

Off the reduced trace, the analytic winding index equals the zero-or-one
multiplicity of the floor-based owner cell. Compact `K` contained in open
`G` admits a finite filling with reduced trace in `G \ K`, index one on
`K`, index zero outside `G`, and whole region in `G`. Empty `K` admits an
empty filling.

Two positive scales may be unrelated. A finite signed rectangular
overlay compares their cell multiplicities. If the closure of their
multiplicity-difference support and both reduced traces lie in `G \ K`,
then every complex-differentiable complete Banach-valued integrand on
`G \ K` has equal integrals over the two cycles.
-/

@[expose] public section


open Filter Set
open scoped Topology

/-- Integer coordinates of a square in a two-dimensional grid. -/
abbrev GridIndex := Fin 2 → ℤ

namespace GridIndex

/-- Move one grid step in coordinate `i`. -/
def succ (v : GridIndex) (i : Fin 2) : GridIndex :=
  Function.update v i (v i + 1)

/-- Move one grid step backwards in coordinate `i`. -/
def pred (v : GridIndex) (i : Fin 2) : GridIndex :=
  Function.update v i (v i - 1)

/-- A forward step increases its chosen integer coordinate by one.

```lean
theorem succ_apply_same (v : GridIndex) (i : Fin 2) : v.succ i i = v i + 1
``` -/
@[simp]
theorem succ_apply_same (v : GridIndex) (i : Fin 2) : v.succ i i = v i + 1 := by
  simp [succ]

/-- A backward step decreases its chosen integer coordinate by one.

```lean
theorem pred_apply_same (v : GridIndex) (i : Fin 2) : v.pred i i = v i - 1
``` -/
@[simp]
theorem pred_apply_same (v : GridIndex) (i : Fin 2) : v.pred i i = v i - 1 := by
  simp [pred]

/-- A forward step leaves every other integer coordinate unchanged.

```lean
theorem succ_apply_of_ne (v : GridIndex) {i j : Fin 2} (h : j ≠ i) :
    v.succ i j = v j
``` -/
@[simp]
theorem succ_apply_of_ne (v : GridIndex) {i j : Fin 2} (h : j ≠ i) :
    v.succ i j = v j := by
  simp [succ, h]

/-- A backward step leaves every other integer coordinate unchanged.

```lean
theorem pred_apply_of_ne (v : GridIndex) {i j : Fin 2} (h : j ≠ i) :
    v.pred i j = v j
``` -/
@[simp]
theorem pred_apply_of_ne (v : GridIndex) {i j : Fin 2} (h : j ≠ i) :
    v.pred i j = v j := by
  simp [pred, h]

/-- A backward step followed by the matching forward step returns the original index.

```lean
theorem pred_succ (v : GridIndex) (i : Fin 2) : (v.pred i).succ i = v
``` -/
@[simp]
theorem pred_succ (v : GridIndex) (i : Fin 2) : (v.pred i).succ i = v := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [succ_apply_of_ne, pred_apply_of_ne, h]

/-- A forward step followed by the matching backward step returns the original index.

```lean
theorem succ_pred (v : GridIndex) (i : Fin 2) : (v.succ i).pred i = v
``` -/
@[simp]
theorem succ_pred (v : GridIndex) (i : Fin 2) : (v.succ i).pred i = v := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [succ_apply_of_ne, pred_apply_of_ne, h]

/-- Equality after a forward step is equivalent to equality before its inverse backward step.

```lean
theorem succ_eq_iff_eq_pred (v w : GridIndex) (i : Fin 2) :
    v.succ i = w ↔ v = w.pred i
``` -/
theorem succ_eq_iff_eq_pred (v w : GridIndex) (i : Fin 2) :
    v.succ i = w ↔ v = w.pred i := by
  constructor
  · intro h
    simpa using congrArg (fun u : GridIndex ↦ u.pred i) h
  · rintro rfl
    exact pred_succ w i

/-- Equality after a backward step is equivalent to equality before its inverse forward step.

```lean
theorem pred_eq_iff_eq_succ (v w : GridIndex) (i : Fin 2) :
    v.pred i = w ↔ v = w.succ i
``` -/
theorem pred_eq_iff_eq_succ (v w : GridIndex) (i : Fin 2) :
    v.pred i = w ↔ v = w.succ i := by
  constructor
  · intro h
    simpa using congrArg (fun u : GridIndex ↦ u.succ i) h
  · rintro rfl
    exact succ_pred w i

end GridIndex

/-- A canonical oriented edge in a rectangular grid.  Horizontal edges point
right and vertical edges point upward. -/
inductive GridEdge where
  | horizontal (base : GridIndex)
  | vertical (base : GridIndex)
deriving DecidableEq

/-- A positive scale and a finite set of selected integer cells. Physical side length is the
reciprocal scale, and the finite set may be empty. -/
structure GridFilling where
  scale : ℝ
  scale_pos : 0 < scale
  cells : Finset GridIndex

/-- The complex vertex `(v 0/t,v 1/t)`, using total division with `x/0=0`. -/
noncomputable def gridPoint (t : ℝ) (v : GridIndex) : ℂ :=
  (((v 0 : ℤ) : ℝ) / t : ℂ) +
    (((v 1 : ℤ) : ℝ) / t : ℂ) * Complex.I

/-- The closed physical rectangle between successive scaled integer coordinates. -/
noncomputable def gridCell (t : ℝ) (v : GridIndex) : RectilinearRectangle where
  first := gridPoint t v
  second := gridPoint t (fun i => v i + 1)

/-- Grid indices whose closed physical cells meet `S`. -/
noncomputable def gridCellsMeeting (t : ℝ) (S : Set ℂ) : Set GridIndex :=
  {v | ((gridCell t v).carrier ∩ S).Nonempty}

/-- For positive scale, the corresponding nondegenerate half-open box in sign-reversed coordinates.
-/
noncomputable def gridCellBox (t : ℝ) (ht : 0 < t) (v : GridIndex) :
    BoxIntegral.Box (Fin 2) where
  lower i := -(((v i : ℝ) + 1) / t)
  upper i := -((v i : ℝ) / t)
  lower_lt_upper i := neg_lt_neg
    ((div_lt_div_iff_of_pos_right ht).2 (by norm_num))

/-- Convert a two-dimensional Mathlib box to the corresponding present
axis-parallel rectangle. -/
noncomputable def rectangleOfBox (I : BoxIntegral.Box (Fin 2)) : RectilinearRectangle :=
  RectilinearRectangle.ofBounds (-I.upper 0) (-I.lower 0) (-I.upper 1) (-I.lower 1)

/-- Open physical rectangle corresponding to a Mathlib half-open box. -/
noncomputable def rectangleOfBoxInterior (I : BoxIntegral.Box (Fin 2)) : Set ℂ :=
  Ioo (-I.upper 0) (-I.lower 0) ×ℂ
    Ioo (-I.upper 1) (-I.lower 1)

/-- The closure of the open rectangle associated with a nondegenerate box is its closed carrier.

```lean
theorem closure_rectangleOfBoxInterior (I : BoxIntegral.Box (Fin 2)) :
    closure (rectangleOfBoxInterior I) = (rectangleOfBox I).carrier
``` -/
theorem closure_rectangleOfBoxInterior (I : BoxIntegral.Box (Fin 2)) :
    closure (rectangleOfBoxInterior I) = (rectangleOfBox I).carrier := by
  have h₀ : -I.upper 0 < -I.lower 0 := neg_lt_neg (I.lower_lt_upper 0)
  have h₁ : -I.upper 1 < -I.lower 1 := neg_lt_neg (I.lower_lt_upper 1)
  rw [rectangleOfBoxInterior, Complex.closure_reProdIm,
    closure_Ioo h₀.ne, closure_Ioo h₁.ne]
  simp [rectangleOfBox, RectilinearRectangle.carrier, Complex.Rectangle, uIcc_of_le h₀.le,
    uIcc_of_le h₁.le]

/-- The associated closed rectangle determines a nondegenerate two-dimensional box uniquely.

```lean
theorem rectangleOfBox_injective : Function.Injective rectangleOfBox
``` -/
theorem rectangleOfBox_injective : Function.Injective rectangleOfBox := by
  intro I J h
  have hfirst := congrArg RectilinearRectangle.first h
  have hsecond := congrArg RectilinearRectangle.second h
  have hupper : I.upper = J.upper := by
    funext i
    fin_cases i
    · simpa [rectangleOfBox, RectilinearRectangle.ofBounds] using congrArg Complex.re hfirst
    · simpa [rectangleOfBox, RectilinearRectangle.ofBounds] using congrArg Complex.im hfirst
  have hlower : I.lower = J.lower := by
    funext i
    fin_cases i
    · simpa [rectangleOfBox, RectilinearRectangle.ofBounds] using congrArg Complex.re hsecond
    · simpa [rectangleOfBox, RectilinearRectangle.ofBounds] using congrArg Complex.im hsecond
  cases I
  cases J
  simp_all

/-- Embedding of nondegenerate boxes into the present rectangle type. -/
noncomputable def rectangleOfBoxEmbedding : BoxIntegral.Box (Fin 2) ↪ RectilinearRectangle where
  toFun := rectangleOfBox
  inj' := rectangleOfBox_injective

/-- The real coordinate pair `(-Re z,-Im z)` used for the half-open box convention. -/
noncomputable def complexBoxPoint (z : ℂ) : Fin 2 → ℝ :=
  fun i ↦ if i = 0 then -z.re else -z.im

/-- An open-rectangle point has its sign-reversed coordinate pair in the corresponding half-open
box.

```lean
theorem complexBoxPoint_mem_of_mem_rectangleOfBoxInterior
    (I : BoxIntegral.Box (Fin 2)) {z : ℂ}
    (hz : z ∈ rectangleOfBoxInterior I) : complexBoxPoint z ∈ I
``` -/
theorem complexBoxPoint_mem_of_mem_rectangleOfBoxInterior
    (I : BoxIntegral.Box (Fin 2)) {z : ℂ}
    (hz : z ∈ rectangleOfBoxInterior I) : complexBoxPoint z ∈ I := by
  intro i
  fin_cases i
  · change I.lower 0 < -z.re ∧ -z.re ≤ I.upper 0
    constructor <;> linarith [hz.1.1, hz.1.2]
  · change I.lower 1 < -z.im ∧ -z.im ≤ I.upper 1
    constructor <;> linarith [hz.2.1, hz.2.2]

/-- For positive `t`, membership of `-x` in `(-(n+1)/t,-n/t]` is equivalent to `floor(t*x)=n`.

```lean
theorem neg_mem_gridInterval_iff_floor {t : ℝ} (ht : 0 < t)
    (n : ℤ) (x : ℝ) :
    -x ∈ Ioc (-(((n : ℝ) + 1) / t)) (-((n : ℝ) / t)) ↔
      ⌊t * x⌋ = n
``` -/
theorem neg_mem_gridInterval_iff_floor {t : ℝ} (ht : 0 < t)
    (n : ℤ) (x : ℝ) :
    -x ∈ Ioc (-(((n : ℝ) + 1) / t)) (-((n : ℝ) / t)) ↔
      ⌊t * x⌋ = n := by
  rw [Int.floor_eq_iff]
  constructor
  · intro hx
    have hlow : (n : ℝ) / t ≤ x := by linarith [hx.2]
    have hupp : x < ((n : ℝ) + 1) / t := by linarith [hx.1]
    constructor
    · simpa [mul_comm] using (div_le_iff₀ ht).1 hlow
    · simpa [mul_comm] using (lt_div_iff₀ ht).1 hupp
  · intro hx
    have hlow : (n : ℝ) / t ≤ x := by
      exact (div_le_iff₀ ht).2 (by simpa [mul_comm] using hx.1)
    have hupp : x < ((n : ℝ) + 1) / t := by
      exact (lt_div_iff₀ ht).2 (by simpa [mul_comm] using hx.2)
    constructor <;> linarith

/-- Finite signed chains of nondegenerate two-dimensional boxes. -/
abbrev BoxOverlayChain := BoxIntegral.Box (Fin 2) →₀ ℤ

/-- Regard a signed box overlay as a rectilinear cycle by taking the boundary
of every box with its integer multiplicity. -/
noncomputable def BoxOverlayChain.toCycle (C : BoxOverlayChain) : RectilinearCycle :=
  Finsupp.mapDomain rectangleOfBoxEmbedding C

/-- Rectangle boundary integration is additive under a coordinate split when
the integrand is globally continuous.

```lean
theorem boundaryIntegral_rectangleOfBox_split {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) (hf : Continuous f) (I : BoxIntegral.Box (Fin 2))
    (i : Fin 2) (x : ℝ) (hx : x ∈ Ioo (I.lower i) (I.upper i)) :
    (I.splitLower i x).elim' 0
        (fun J ↦ (rectangleOfBox J).boundaryIntegral f) +
      (I.splitUpper i x).elim' 0
        (fun J ↦ (rectangleOfBox J).boundaryIntegral f) =
      (rectangleOfBox I).boundaryIntegral f
``` -/
theorem boundaryIntegral_rectangleOfBox_split {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) (hf : Continuous f) (I : BoxIntegral.Box (Fin 2))
    (i : Fin 2) (x : ℝ) (hx : x ∈ Ioo (I.lower i) (I.upper i)) :
    (I.splitLower i x).elim' 0
        (fun J ↦ (rectangleOfBox J).boundaryIntegral f) +
      (I.splitUpper i x).elim' 0
        (fun J ↦ (rectangleOfBox J).boundaryIntegral f) =
      (rectangleOfBox I).boundaryIntegral f := by
  fin_cases i
  · rw [BoxIntegral.Box.splitLower_def hx,
      BoxIntegral.Box.splitUpper_def hx]
    change
      (RectilinearRectangle.ofBounds
          (-x) (-I.lower 0) (-I.upper 1) (-I.lower 1)).boundaryIntegral f +
        (RectilinearRectangle.ofBounds
          (-I.upper 0) (-x) (-I.upper 1) (-I.lower 1)).boundaryIntegral f =
          (RectilinearRectangle.ofBounds (-I.upper 0) (-I.lower 0) (-I.upper 1)
            (-I.lower 1)).boundaryIntegral f
    simpa [add_comm] using
      (RectilinearRectangle.boundaryIntegral_ofBounds_vertical_concat f
        (-I.upper 0) (-x) (-I.lower 0) (-I.upper 1) (-I.lower 1)
        (hf.comp (by fun_prop)) (hf.comp (by fun_prop))).symm
  · rw [BoxIntegral.Box.splitLower_def hx,
      BoxIntegral.Box.splitUpper_def hx]
    change
      (RectilinearRectangle.ofBounds
          (-I.upper 0) (-I.lower 0) (-x) (-I.lower 1)).boundaryIntegral f +
        (RectilinearRectangle.ofBounds
          (-I.upper 0) (-I.lower 0) (-I.upper 1) (-x)).boundaryIntegral f =
          (RectilinearRectangle.ofBounds (-I.upper 0) (-I.lower 0) (-I.upper 1)
            (-I.lower 1)).boundaryIntegral f
    simpa [add_comm] using
      (RectilinearRectangle.boundaryIntegral_ofBounds_horizontal_concat f
        (-I.upper 0) (-I.lower 0) (-I.upper 1) (-x) (-I.lower 1)
        (hf.comp (by fun_prop)) (hf.comp (by fun_prop))).symm

/-- Globally continuous rectangle boundary integration, packaged as a
Mathlib box-additive map. -/
noncomputable def boundaryIntegralBoxAdditive {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) (hf : Continuous f) :
    BoxIntegral.BoxAdditiveMap (Fin 2) E ⊤ :=
  BoxIntegral.BoxAdditiveMap.ofMapSplitAdd
    (fun I ↦ (rectangleOfBox I).boundaryIntegral f) ⊤
    fun I _hI i x hx ↦ boundaryIntegral_rectangleOfBox_split f hf I i x hx

namespace GridFilling

/-- The physical complex point represented by a lattice vertex. -/
noncomputable def point (D : GridFilling) (v : GridIndex) : ℂ :=
  gridPoint D.scale v

/-- The real vertex coordinate is its first integer coordinate divided by the filling scale.

```lean
theorem point_re (D : GridFilling) (v : GridIndex) :
    (D.point v).re = (v 0 : ℝ) / D.scale
``` -/
@[simp]
theorem point_re (D : GridFilling) (v : GridIndex) :
    (D.point v).re = (v 0 : ℝ) / D.scale := by
  simp [point, gridPoint]

/-- The imaginary vertex coordinate is its second integer coordinate divided by the filling scale.

```lean
theorem point_im (D : GridFilling) (v : GridIndex) :
    (D.point v).im = (v 1 : ℝ) / D.scale
``` -/
@[simp]
theorem point_im (D : GridFilling) (v : GridIndex) :
    (D.point v).im = (v 1 : ℝ) / D.scale := by
  simp [point, gridPoint]

/-- The closed physical square at lattice index `v`. -/
noncomputable def cell (D : GridFilling) (v : GridIndex) : RectilinearRectangle :=
  gridCell D.scale v

/-- Mathlib box presentation of a physical cell. -/
noncomputable def cellBox (D : GridFilling) (v : GridIndex) :
    BoxIntegral.Box (Fin 2) :=
  gridCellBox D.scale D.scale_pos v

/-- The half-open presentation of a cell has exactly the same associated closed rectangle.

```lean
theorem rectangleOfBox_cellBox (D : GridFilling) (v : GridIndex) :
    rectangleOfBox (D.cellBox v) = D.cell v
``` -/
theorem rectangleOfBox_cellBox (D : GridFilling) (v : GridIndex) :
    rectangleOfBox (D.cellBox v) = D.cell v := by
  ext <;> simp [rectangleOfBox, cellBox, gridCellBox, cell, gridCell,
    gridPoint, RectilinearRectangle.ofBounds]

/-- A cell is the closed rectangle between its successive scaled integer coordinates.

```lean
theorem cell_eq_ofBounds (D : GridFilling) (v : GridIndex) :
    D.cell v = RectilinearRectangle.ofBounds
      ((v 0 : ℝ) / D.scale) (((v 0 : ℝ) + 1) / D.scale)
      ((v 1 : ℝ) / D.scale) (((v 1 : ℝ) + 1) / D.scale)
``` -/
theorem cell_eq_ofBounds (D : GridFilling) (v : GridIndex) :
    D.cell v = RectilinearRectangle.ofBounds
      ((v 0 : ℝ) / D.scale) (((v 0 : ℝ) + 1) / D.scale)
      ((v 1 : ℝ) / D.scale) (((v 1 : ℝ) + 1) / D.scale) := by
  ext <;> simp [cell, gridCell, gridPoint, RectilinearRectangle.ofBounds]

/-- Closed-cell membership is exactly the pair of stated closed coordinate-interval conditions.

```lean
theorem mem_cell_carrier_iff (D : GridFilling) (v : GridIndex) (z : ℂ) :
    z ∈ (D.cell v).carrier ↔
      z.re ∈ Icc ((v 0 : ℝ) / D.scale) (((v 0 : ℝ) + 1) / D.scale) ∧
        z.im ∈ Icc ((v 1 : ℝ) / D.scale) (((v 1 : ℝ) + 1) / D.scale)
``` -/
theorem mem_cell_carrier_iff (D : GridFilling) (v : GridIndex) (z : ℂ) :
    z ∈ (D.cell v).carrier ↔
      z.re ∈ Icc ((v 0 : ℝ) / D.scale) (((v 0 : ℝ) + 1) / D.scale) ∧
        z.im ∈ Icc ((v 1 : ℝ) / D.scale) (((v 1 : ℝ) + 1) / D.scale) := by
  have h₀ : (v 0 : ℝ) / D.scale ≤ ((v 0 : ℝ) + 1) / D.scale :=
    (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
  have h₁ : (v 1 : ℝ) / D.scale ≤ ((v 1 : ℝ) + 1) / D.scale :=
    (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
  simp [cell, gridCell, RectilinearRectangle.carrier, Complex.Rectangle, gridPoint,
    Complex.mem_reProdIm, uIcc_of_le h₀, uIcc_of_le h₁]

/-- Build a filling from a scale and a finite set of cell indices. -/
def ofCells (t : ℝ) (ht : 0 < t) (s : Finset GridIndex) : GridFilling where
  scale := t
  scale_pos := ht
  cells := s

/-- Indicator coefficient of a selected cell. -/
def cellCoeff (D : GridFilling) (v : GridIndex) : ℤ :=
  if v ∈ D.cells then 1 else 0

/-- The finite sum of counterclockwise boundaries of the selected physical cells. -/
noncomputable def toCycle (D : GridFilling) : RectilinearCycle :=
  ∑ v ∈ D.cells, RectilinearCycle.ofRectangle (D.cell v)

/-- In a complete complex normed target, the filling-cycle integral is the sum of its selected cell
boundary integrals.

```lean
theorem toCycle_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling) (f : ℂ → E) :
    D.toCycle.integral f = ∑ v ∈ D.cells, (D.cell v).boundaryIntegral f
``` -/
theorem toCycle_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling) (f : ℂ → E) :
    D.toCycle.integral f = ∑ v ∈ D.cells, (D.cell v).boundaryIntegral f := by
  change RectilinearCycle.integralAddHom f D.toCycle = _
  simp [toCycle]

/-- The filling-cycle analytic index is the sum of the selected cells' analytic indices.

```lean
theorem toCycle_index (D : GridFilling) (z : ℂ) :
    D.toCycle.index z =
      ∑ v ∈ D.cells, (RectilinearCycle.ofRectangle (D.cell v)).index z
``` -/
theorem toCycle_index (D : GridFilling) (z : ℂ) :
    D.toCycle.index z =
      ∑ v ∈ D.cells, (RectilinearCycle.ofRectangle (D.cell v)).index z := by
  change RectilinearCycle.indexAddHom z D.toCycle = _
  simp [toCycle]

/-- All cell-face coordinates of two fillings in one coordinate direction,
with `0` and `1` added to make the set nonempty and nontrivial. -/
noncomputable def commonCoordinates (D E : GridFilling) (i : Fin 2) : Finset ℝ :=
  {0, 1} ∪
    (D.cells.biUnion fun v ↦ {(D.cellBox v).lower i, (D.cellBox v).upper i}) ∪
      (E.cells.biUnion fun v ↦ {(E.cellBox v).lower i, (E.cellBox v).upper i})

/-- A nondegenerate box containing every selected cell of both fillings. -/
noncomputable def commonBoundingBox (D E : GridFilling) :
    BoxIntegral.Box (Fin 2) where
  lower i := (D.commonCoordinates E i).min' (by simp [commonCoordinates])
  upper i := (D.commonCoordinates E i).max' (by simp [commonCoordinates])
  lower_lt_upper i := lt_of_le_of_lt
    ((D.commonCoordinates E i).min'_le 0
      (by simp [commonCoordinates] : (0 : ℝ) ∈ D.commonCoordinates E i))
    (lt_of_lt_of_le zero_lt_one
      ((D.commonCoordinates E i).le_max' 1
        (by simp [commonCoordinates] : (1 : ℝ) ∈ D.commonCoordinates E i)))

/-- Different integer indices give different half-open cell boxes at a fixed positive scale.

```lean
theorem cellBox_injective (D : GridFilling) : Function.Injective D.cellBox
``` -/
theorem cellBox_injective (D : GridFilling) : Function.Injective D.cellBox := by
  intro v w h
  funext i
  have hi := congrArg (fun I : BoxIntegral.Box (Fin 2) ↦ I.lower i) h
  simp only [cellBox, gridCellBox] at hi
  apply_fun (fun x : ℝ ↦ x * D.scale) at hi
  simpa [D.scale_pos.ne'] using hi

/-- Distinct half-open grid cells are disjoint, with boundary faces assigned by the half-open
convention.

```lean
theorem disjoint_cellBox (D : GridFilling) {v w : GridIndex} (hvw : v ≠ w) :
    Disjoint (D.cellBox v : Set (Fin 2 → ℝ)) (D.cellBox w : Set (Fin 2 → ℝ))
``` -/
theorem disjoint_cellBox (D : GridFilling) {v w : GridIndex} (hvw : v ≠ w) :
    Disjoint (D.cellBox v : Set (Fin 2 → ℝ)) (D.cellBox w : Set (Fin 2 → ℝ)) := by
  rw [Set.disjoint_left]
  intro x hxv hxw
  have hcoord : ∃ i, v i ≠ w i := by
    by_contra h
    push Not at h
    exact hvw (funext h)
  rcases hcoord with ⟨i, hi⟩
  have hxvi := hxv i
  have hxwi := hxw i
  simp only [cellBox, gridCellBox, mem_Ioc] at hxvi hxwi
  rcases lt_or_gt_of_ne hi with hi | hi
  · have hstep : (v i : ℝ) + 1 ≤ (w i : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hi)
    have hscaled : -((w i : ℝ) / D.scale) ≤
        -(((v i : ℝ) + 1) / D.scale) := by
      exact neg_le_neg ((div_le_div_iff_of_pos_right D.scale_pos).2 hstep)
    exact (not_lt_of_ge (hxwi.2.trans hscaled)) hxvi.1
  · have hstep : (w i : ℝ) + 1 ≤ (v i : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hi)
    have hscaled : -((v i : ℝ) / D.scale) ≤
        -(((w i : ℝ) + 1) / D.scale) := by
      exact neg_le_neg ((div_le_div_iff_of_pos_right D.scale_pos).2 hstep)
    exact (not_lt_of_ge (hxvi.2.trans hscaled)) hxwi.1

/-- The selected grid cells as a finite set of pairwise-disjoint half-open
Mathlib boxes. -/
noncomputable def cellBoxes (D : GridFilling) : Finset (BoxIntegral.Box (Fin 2)) :=
  by
    classical
    exact D.cells.image D.cellBox

/-- The finite selected half-open cell boxes are pairwise disjoint.

```lean
theorem pairwiseDisjoint_cellBoxes (D : GridFilling) :
    Set.Pairwise (↑D.cellBoxes)
      (Function.onFun Disjoint fun I : BoxIntegral.Box (Fin 2) ↦
        (I : Set (Fin 2 → ℝ)))
``` -/
theorem pairwiseDisjoint_cellBoxes (D : GridFilling) :
    Set.Pairwise (↑D.cellBoxes)
      (Function.onFun Disjoint fun I : BoxIntegral.Box (Fin 2) ↦
        (I : Set (Fin 2 → ℝ))) := by
  classical
  intro I hI J hJ hIJ
  rw [Finset.mem_coe, cellBoxes, Finset.mem_image] at hI hJ
  rcases hI with ⟨v, hv, rfl⟩
  rcases hJ with ⟨w, hw, rfl⟩
  exact D.disjoint_cellBox fun hvw ↦ hIJ (congrArg D.cellBox hvw)

/-- Selected cells as a prepartition of any containing box. -/
noncomputable def cellsPrepartition (D : GridFilling)
    (B : BoxIntegral.Box (Fin 2)) (hB : ∀ v ∈ D.cells, D.cellBox v ≤ B) :
    BoxIntegral.Prepartition B where
  boxes := D.cellBoxes
  le_of_mem' I hI := by
    classical
    rw [cellBoxes, Finset.mem_image] at hI
    rcases hI with ⟨v, hv, rfl⟩
    exact hB v hv
  pairwiseDisjoint := D.pairwiseDisjoint_cellBoxes

/-- Each selected cell of the first filling lies in the nondegenerate common bounding box.

```lean
theorem cellBox_le_commonBoundingBox_left (D E : GridFilling)
    {v : GridIndex} (hv : v ∈ D.cells) : D.cellBox v ≤ D.commonBoundingBox E
``` -/
theorem cellBox_le_commonBoundingBox_left (D E : GridFilling)
    {v : GridIndex} (hv : v ∈ D.cells) : D.cellBox v ≤ D.commonBoundingBox E := by
  rw [BoxIntegral.Box.le_iff_bounds]
  constructor
  · intro i
    apply (D.commonCoordinates E i).min'_le _
    rw [commonCoordinates]
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨v, hv, by simp⟩))
  · intro i
    apply (D.commonCoordinates E i).le_max' _
    rw [commonCoordinates]
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨v, hv, by simp⟩))

/-- Each selected cell of the second filling lies in the nondegenerate common bounding box.

```lean
theorem cellBox_le_commonBoundingBox_right (D E : GridFilling)
    {v : GridIndex} (hv : v ∈ E.cells) : E.cellBox v ≤ D.commonBoundingBox E
``` -/
theorem cellBox_le_commonBoundingBox_right (D E : GridFilling)
    {v : GridIndex} (hv : v ∈ E.cells) : E.cellBox v ≤ D.commonBoundingBox E := by
  rw [BoxIntegral.Box.le_iff_bounds]
  constructor
  · intro i
    apply (D.commonCoordinates E i).min'_le _
    rw [commonCoordinates]
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨v, hv, by simp⟩)
  · intro i
    apply (D.commonCoordinates E i).le_max' _
    rw [commonCoordinates]
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨v, hv, by simp⟩)

/-- The cells of the left filling as a prepartition of the common bounding
box. -/
noncomputable def leftCellPrepartition (D E : GridFilling) :
    BoxIntegral.Prepartition (D.commonBoundingBox E) :=
  D.cellsPrepartition (D.commonBoundingBox E) fun _v hv ↦
    D.cellBox_le_commonBoundingBox_left E hv

/-- The cells of the right filling as a prepartition of the common bounding
box. -/
noncomputable def rightCellPrepartition (D E : GridFilling) :
    BoxIntegral.Prepartition (D.commonBoundingBox E) :=
  E.cellsPrepartition (D.commonBoundingBox E) fun _v hv ↦
    D.cellBox_le_commonBoundingBox_right E hv

/-- Finitely many coordinate cuts align both cell prepartitions as restrictions of one global split.

```lean
theorem exists_overlayHyperplanes (D E : GridFilling) :
    ∃ s : Finset (Fin 2 × ℝ),
      ∀ π ∈ ({D.leftCellPrepartition E, D.rightCellPrepartition E} :
          Set (BoxIntegral.Prepartition (D.commonBoundingBox E))),
        π ⊓ BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E) s =
          (BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E) s).filter
            fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ π.iUnion
``` -/
theorem exists_overlayHyperplanes (D E : GridFilling) :
    ∃ s : Finset (Fin 2 × ℝ),
      ∀ π ∈ ({D.leftCellPrepartition E, D.rightCellPrepartition E} :
          Set (BoxIntegral.Prepartition (D.commonBoundingBox E))),
        π ⊓ BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E) s =
          (BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E) s).filter
            fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ π.iUnion :=
  BoxIntegral.Prepartition.exists_splitMany_inf_eq_filter_of_finite
    {D.leftCellPrepartition E, D.rightCellPrepartition E}
    (Set.Finite.insert _ (Set.finite_singleton _))

/-- A chosen finite family of hyperplanes aligning the two cell
prepartitions. -/
noncomputable def overlayHyperplanes (D E : GridFilling) : Finset (Fin 2 × ℝ) :=
  Classical.choose (D.exists_overlayHyperplanes E)

/-- The chosen coordinate cuts satisfy the simultaneous alignment identities for both fillings.

```lean
theorem overlayHyperplanes_spec (D E : GridFilling) :
    ∀ π ∈ ({D.leftCellPrepartition E, D.rightCellPrepartition E} :
        Set (BoxIntegral.Prepartition (D.commonBoundingBox E))),
      π ⊓ BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
          (D.overlayHyperplanes E) =
        (BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
          (D.overlayHyperplanes E)).filter
            fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ π.iUnion
``` -/
theorem overlayHyperplanes_spec (D E : GridFilling) :
    ∀ π ∈ ({D.leftCellPrepartition E, D.rightCellPrepartition E} :
        Set (BoxIntegral.Prepartition (D.commonBoundingBox E))),
      π ⊓ BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
          (D.overlayHyperplanes E) =
        (BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
          (D.overlayHyperplanes E)).filter
            fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ π.iUnion :=
  Classical.choose_spec (D.exists_overlayHyperplanes E)

/-- A prepartition regarded as the unsigned box chain with coefficient one on
each of its boxes. -/
noncomputable def prepartitionToBoxOverlayChain
    {B : BoxIntegral.Box (Fin 2)} (π : BoxIntegral.Prepartition B) : BoxOverlayChain :=
  by
    classical
    exact ∑ I ∈ π.boxes, Finsupp.single I 1

/-- A member box has integer coefficient one in an unsigned prepartition chain.

```lean
theorem prepartitionToBoxOverlayChain_apply_of_mem
    {B : BoxIntegral.Box (Fin 2)} {π : BoxIntegral.Prepartition B}
    {I : BoxIntegral.Box (Fin 2)} (hI : I ∈ π) :
    prepartitionToBoxOverlayChain π I = 1
``` -/
theorem prepartitionToBoxOverlayChain_apply_of_mem
    {B : BoxIntegral.Box (Fin 2)} {π : BoxIntegral.Prepartition B}
    {I : BoxIntegral.Box (Fin 2)} (hI : I ∈ π) :
    prepartitionToBoxOverlayChain π I = 1 := by
  classical
  rw [prepartitionToBoxOverlayChain, Finset.sum_apply', Finset.sum_eq_single I]
  · simp
  · intro J hJ hJI
    change (Finsupp.single J (1 : ℤ) : BoxOverlayChain) I = 0
    exact Finsupp.single_eq_of_ne hJI.symm
  · exact fun h ↦ (h hI).elim

/-- A nonmember box has integer coefficient zero in an unsigned prepartition chain.

```lean
theorem prepartitionToBoxOverlayChain_apply_of_notMem
    {B : BoxIntegral.Box (Fin 2)} {π : BoxIntegral.Prepartition B}
    {I : BoxIntegral.Box (Fin 2)} (hI : I ∉ π) :
    prepartitionToBoxOverlayChain π I = 0
``` -/
theorem prepartitionToBoxOverlayChain_apply_of_notMem
    {B : BoxIntegral.Box (Fin 2)} {π : BoxIntegral.Prepartition B}
    {I : BoxIntegral.Box (Fin 2)} (hI : I ∉ π) :
    prepartitionToBoxOverlayChain π I = 0 := by
  classical
  rw [prepartitionToBoxOverlayChain]
  rw [Finset.sum_apply']
  apply Finset.sum_eq_zero
  intro J hJ
  simp only [Finsupp.single_apply]
  split
  · rename_i hJI
    exfalso
    exact hI (hJI ▸ hJ)
  · rfl

/-- Membership indicator of a finite box prepartition. -/
noncomputable def prepartitionIndicator
    {B : BoxIntegral.Box (Fin 2)} (π : BoxIntegral.Prepartition B)
    (I : BoxIntegral.Box (Fin 2)) : ℤ :=
  by
    classical
    exact if I ∈ π then 1 else 0

/-- The unsigned box-chain coefficient is exactly the prepartition membership indicator.

```lean
theorem prepartitionToBoxOverlayChain_apply
    {B : BoxIntegral.Box (Fin 2)} (π : BoxIntegral.Prepartition B)
    (I : BoxIntegral.Box (Fin 2)) :
    prepartitionToBoxOverlayChain π I = prepartitionIndicator π I
``` -/
theorem prepartitionToBoxOverlayChain_apply
    {B : BoxIntegral.Box (Fin 2)} (π : BoxIntegral.Prepartition B)
    (I : BoxIntegral.Box (Fin 2)) :
    prepartitionToBoxOverlayChain π I = prepartitionIndicator π I := by
  classical
  by_cases hI : I ∈ π
  · rw [prepartitionToBoxOverlayChain_apply_of_mem hI]
    simp [prepartitionIndicator, hI]
  · rw [prepartitionToBoxOverlayChain_apply_of_notMem hI]
    simp [prepartitionIndicator, hI]

/-- The global box partition on which both refined cell collections are
filters. -/
noncomputable def overlayPrepartition (D E : GridFilling) :
    BoxIntegral.Prepartition (D.commonBoundingBox E) :=
  BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
    (D.overlayHyperplanes E)

/-- Left cell prepartition after applying the chosen common split. -/
noncomputable def leftOverlayPrepartition (D E : GridFilling) :
    BoxIntegral.Prepartition (D.commonBoundingBox E) :=
  (D.leftCellPrepartition E).biUnion fun I ↦
    BoxIntegral.Prepartition.splitMany I (D.overlayHyperplanes E)

/-- Right cell prepartition after applying the chosen common split. -/
noncomputable def rightOverlayPrepartition (D E : GridFilling) :
    BoxIntegral.Prepartition (D.commonBoundingBox E) :=
  (D.rightCellPrepartition E).biUnion fun I ↦
    BoxIntegral.Prepartition.splitMany I (D.overlayHyperplanes E)

/-- The refined first filling is the global split restricted to its selected-cell union.

```lean
theorem leftOverlayPrepartition_eq_filter (D E : GridFilling) :
    D.leftOverlayPrepartition E =
      (BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
        (D.overlayHyperplanes E)).filter
          fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ (D.leftCellPrepartition E).iUnion
``` -/
theorem leftOverlayPrepartition_eq_filter (D E : GridFilling) :
    D.leftOverlayPrepartition E =
      (BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
        (D.overlayHyperplanes E)).filter
          fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ (D.leftCellPrepartition E).iUnion := by
  rw [leftOverlayPrepartition, ← BoxIntegral.Prepartition.inf_splitMany]
  exact D.overlayHyperplanes_spec E (D.leftCellPrepartition E) (by simp)

/-- The refined second filling is the global split restricted to its selected-cell union.

```lean
theorem rightOverlayPrepartition_eq_filter (D E : GridFilling) :
    D.rightOverlayPrepartition E =
      (BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
        (D.overlayHyperplanes E)).filter
          fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ (D.rightCellPrepartition E).iUnion
``` -/
theorem rightOverlayPrepartition_eq_filter (D E : GridFilling) :
    D.rightOverlayPrepartition E =
      (BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
        (D.overlayHyperplanes E)).filter
          fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ (D.rightCellPrepartition E).iUnion := by
  rw [rightOverlayPrepartition, ← BoxIntegral.Prepartition.inf_splitMany]
  exact D.overlayHyperplanes_spec E (D.rightCellPrepartition E) (by simp)

/-- The signed difference of the two refined finite box chains; boxes shared by both have zero
coefficient. -/
noncomputable def commonOverlay (D E : GridFilling) : BoxOverlayChain :=
  prepartitionToBoxOverlayChain (D.leftOverlayPrepartition E) -
    prepartitionToBoxOverlayChain (D.rightOverlayPrepartition E)

/-- The signed overlay coefficient is the first refined indicator minus the second.

```lean
theorem commonOverlay_apply (D E : GridFilling)
    (I : BoxIntegral.Box (Fin 2)) :
    D.commonOverlay E I =
      prepartitionIndicator (D.leftOverlayPrepartition E) I -
        prepartitionIndicator (D.rightOverlayPrepartition E) I
``` -/
theorem commonOverlay_apply (D E : GridFilling)
    (I : BoxIntegral.Box (Fin 2)) :
    D.commonOverlay E I =
      prepartitionIndicator (D.leftOverlayPrepartition E) I -
        prepartitionIndicator (D.rightOverlayPrepartition E) I := by
  classical
  rw [commonOverlay, Finsupp.sub_apply,
    prepartitionToBoxOverlayChain_apply,
    prepartitionToBoxOverlayChain_apply]

/-- Every box with nonzero signed overlay coefficient lies in the global overlay partition.

```lean
theorem mem_overlayPrepartition_of_mem_commonOverlay_support
    (D E : GridFilling) {I : BoxIntegral.Box (Fin 2)}
    (hI : I ∈ (D.commonOverlay E).support) :
    I ∈ D.overlayPrepartition E
``` -/
theorem mem_overlayPrepartition_of_mem_commonOverlay_support
    (D E : GridFilling) {I : BoxIntegral.Box (Fin 2)}
    (hI : I ∈ (D.commonOverlay E).support) :
    I ∈ D.overlayPrepartition E := by
  classical
  rw [Finsupp.mem_support_iff] at hI
  by_contra hglobal
  apply hI
  have hleft : I ∉ D.leftOverlayPrepartition E := by
    intro hleft
    rw [D.leftOverlayPrepartition_eq_filter E,
      BoxIntegral.Prepartition.mem_filter] at hleft
    exact hglobal hleft.1
  have hright : I ∉ D.rightOverlayPrepartition E := by
    intro hright
    rw [D.rightOverlayPrepartition_eq_filter E,
      BoxIntegral.Prepartition.mem_filter] at hright
    exact hglobal hright.1
  rw [commonOverlay, Finsupp.sub_apply,
    prepartitionToBoxOverlayChain_apply_of_notMem hleft,
    prepartitionToBoxOverlayChain_apply_of_notMem hright, sub_self]

/-- For aligned partitions, an overlay box lies wholly in the first union exactly when a given
point of that box lies there.

```lean
theorem overlayBox_subset_iUnion_iff_mem
    {B : BoxIntegral.Box (Fin 2)} (π ρ : BoxIntegral.Prepartition B)
    (halign : π ⊓ ρ = ρ.filter fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ π.iUnion)
    {I : BoxIntegral.Box (Fin 2)} (hI : I ∈ ρ) {x : Fin 2 → ℝ}
    (hx : x ∈ I) :
    (I : Set (Fin 2 → ℝ)) ⊆ π.iUnion ↔ x ∈ π.iUnion
``` -/
theorem overlayBox_subset_iUnion_iff_mem
    {B : BoxIntegral.Box (Fin 2)} (π ρ : BoxIntegral.Prepartition B)
    (halign : π ⊓ ρ = ρ.filter fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ π.iUnion)
    {I : BoxIntegral.Box (Fin 2)} (hI : I ∈ ρ) {x : Fin 2 → ℝ}
    (hx : x ∈ I) :
    (I : Set (Fin 2 → ℝ)) ⊆ π.iUnion ↔ x ∈ π.iUnion := by
  constructor
  · exact fun h ↦ h hx
  · intro hxπ
    have hxinf : x ∈ (π ⊓ ρ).iUnion := by
      rw [BoxIntegral.Prepartition.iUnion_inf]
      exact ⟨hxπ, ρ.subset_iUnion hI hx⟩
    rw [BoxIntegral.Prepartition.mem_iUnion] at hxinf
    rcases hxinf with ⟨J, hJ, hxJ⟩
    rw [halign, BoxIntegral.Prepartition.mem_filter] at hJ
    obtain rfl : J = I := ρ.eq_of_mem_of_mem hJ.1 hI hxJ hx
    exact hJ.2

/-- The cycle integral of a signed box chain is its finite integer-weighted sum of rectangle
boundary integrals.

```lean
theorem BoxOverlayChain.toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (C : BoxOverlayChain) (f : ℂ → E) :
    C.toCycle.integral f =
      C.sum fun I n ↦ n • (rectangleOfBox I).boundaryIntegral f
``` -/
theorem BoxOverlayChain.toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (C : BoxOverlayChain) (f : ℂ → E) :
    C.toCycle.integral f =
      C.sum fun I n ↦ n • (rectangleOfBox I).boundaryIntegral f := by
  unfold BoxOverlayChain.toCycle RectilinearCycle.integral
  rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp)
    (fun _ m n ↦ by simp [add_zsmul])]
  rfl

/-- Taking rectangle boundaries sends subtraction of signed box chains to subtraction of cycles.

```lean
theorem BoxOverlayChain.toCycle_sub (C D : BoxOverlayChain) :
    (C - D).toCycle = C.toCycle - D.toCycle
``` -/
theorem BoxOverlayChain.toCycle_sub (C D : BoxOverlayChain) :
    (C - D).toCycle = C.toCycle - D.toCycle := by
  simp [BoxOverlayChain.toCycle, Finsupp.mapDomain_sub]

/-- The additive map assigning a signed box chain its integer-weighted complete Banach-valued
boundary integral. -/
noncomputable def boxBoundaryIntegralAddHom {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) : BoxOverlayChain →+ E where
  toFun C := C.sum fun I n ↦ n • (rectangleOfBox I).boundaryIntegral f
  map_zero' := by simp
  map_add' C D := by
    apply Finsupp.sum_add_index'
    · intro I
      simp
    · intro I m n
      simp [add_zsmul]

/-- An unsigned prepartition cycle integrates to the finite sum of its boxes' boundary integrals.

```lean
theorem prepartitionToBoxOverlayChain_toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {B : BoxIntegral.Box (Fin 2)} (π : BoxIntegral.Prepartition B) (f : ℂ → E) :
    (prepartitionToBoxOverlayChain π).toCycle.integral f =
      ∑ I ∈ π.boxes, (rectangleOfBox I).boundaryIntegral f
``` -/
theorem prepartitionToBoxOverlayChain_toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {B : BoxIntegral.Box (Fin 2)} (π : BoxIntegral.Prepartition B) (f : ℂ → E) :
    (prepartitionToBoxOverlayChain π).toCycle.integral f =
      ∑ I ∈ π.boxes, (rectangleOfBox I).boundaryIntegral f := by
  classical
  rw [BoxOverlayChain.toCycle_integral]
  change boxBoundaryIntegralAddHom f (prepartitionToBoxOverlayChain π) = _
  simp [prepartitionToBoxOverlayChain, boxBoundaryIntegralAddHom]

/-- The box-presentation boundary sum equals the boundary sum indexed by the selected grid cells.

```lean
theorem sum_cellBoxes_boundaryIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → E) :
    ∑ I ∈ D.cellBoxes, (rectangleOfBox I).boundaryIntegral f =
      ∑ v ∈ D.cells, (D.cell v).boundaryIntegral f
``` -/
theorem sum_cellBoxes_boundaryIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → E) :
    ∑ I ∈ D.cellBoxes, (rectangleOfBox I).boundaryIntegral f =
      ∑ v ∈ D.cells, (D.cell v).boundaryIntegral f := by
  classical
  rw [cellBoxes, Finset.sum_image]
  · simp [rectangleOfBox_cellBox]
  · exact fun _ _ _ _ h ↦ D.cellBox_injective h

/-- Subdivision of the first filling preserves the contour integral of a globally continuous
complete Banach-valued integrand.

```lean
theorem leftOverlayPrepartition_toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D E₁ : GridFilling) (f : ℂ → E) (hf : Continuous f) :
    (prepartitionToBoxOverlayChain (D.leftOverlayPrepartition E₁)).toCycle.integral f =
      D.toCycle.integral f
``` -/
theorem leftOverlayPrepartition_toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D E₁ : GridFilling) (f : ℂ → E) (hf : Continuous f) :
    (prepartitionToBoxOverlayChain (D.leftOverlayPrepartition E₁)).toCycle.integral f =
      D.toCycle.integral f := by
  classical
  rw [prepartitionToBoxOverlayChain_toCycle_integral,
    leftOverlayPrepartition, BoxIntegral.Prepartition.biUnion_boxes,
    BoxIntegral.Prepartition.sum_biUnion_boxes]
  calc
    ∑ I ∈ (D.leftCellPrepartition E₁).boxes,
        ∑ J ∈ (BoxIntegral.Prepartition.splitMany I
          (D.overlayHyperplanes E₁)).boxes,
          (rectangleOfBox J).boundaryIntegral f =
        ∑ I ∈ (D.leftCellPrepartition E₁).boxes,
          (rectangleOfBox I).boundaryIntegral f := by
      apply Finset.sum_congr rfl
      intro I hI
      exact (boundaryIntegralBoxAdditive f hf).sum_partition_boxes (by simp)
        (BoxIntegral.Prepartition.isPartition_splitMany I (D.overlayHyperplanes E₁))
    _ = D.toCycle.integral f := by
      rw [leftCellPrepartition, cellsPrepartition, D.sum_cellBoxes_boundaryIntegral,
        ← D.toCycle_integral]

/-- Subdivision of the second filling preserves the contour integral of a globally continuous
complete Banach-valued integrand.

```lean
theorem rightOverlayPrepartition_toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D E₁ : GridFilling) (f : ℂ → E) (hf : Continuous f) :
    (prepartitionToBoxOverlayChain (D.rightOverlayPrepartition E₁)).toCycle.integral f =
      E₁.toCycle.integral f
``` -/
theorem rightOverlayPrepartition_toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D E₁ : GridFilling) (f : ℂ → E) (hf : Continuous f) :
    (prepartitionToBoxOverlayChain (D.rightOverlayPrepartition E₁)).toCycle.integral f =
      E₁.toCycle.integral f := by
  classical
  rw [prepartitionToBoxOverlayChain_toCycle_integral,
    rightOverlayPrepartition, BoxIntegral.Prepartition.biUnion_boxes,
    BoxIntegral.Prepartition.sum_biUnion_boxes]
  calc
    ∑ I ∈ (D.rightCellPrepartition E₁).boxes,
        ∑ J ∈ (BoxIntegral.Prepartition.splitMany I
          (D.overlayHyperplanes E₁)).boxes,
          (rectangleOfBox J).boundaryIntegral f =
        ∑ I ∈ (D.rightCellPrepartition E₁).boxes,
          (rectangleOfBox I).boundaryIntegral f := by
      apply Finset.sum_congr rfl
      intro I hI
      exact (boundaryIntegralBoxAdditive f hf).sum_partition_boxes (by simp)
        (BoxIntegral.Prepartition.isPartition_splitMany I (D.overlayHyperplanes E₁))
    _ = E₁.toCycle.integral f := by
      rw [rightCellPrepartition, cellsPrepartition,
        E₁.sum_cellBoxes_boundaryIntegral, ← E₁.toCycle_integral]

/-- For a globally continuous complete Banach-valued integrand, the signed overlay integral is the
difference of the filling integrals.

```lean
theorem commonOverlay_toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D E₁ : GridFilling) (f : ℂ → E) (hf : Continuous f) :
    (D.commonOverlay E₁).toCycle.integral f =
      D.toCycle.integral f - E₁.toCycle.integral f
``` -/
theorem commonOverlay_toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D E₁ : GridFilling) (f : ℂ → E) (hf : Continuous f) :
    (D.commonOverlay E₁).toCycle.integral f =
      D.toCycle.integral f - E₁.toCycle.integral f := by
  classical
  rw [commonOverlay, BoxOverlayChain.toCycle_sub,
    RectilinearCycle.integral_sub,
    D.leftOverlayPrepartition_toCycle_integral E₁ f hf,
    D.rightOverlayPrepartition_toCycle_integral E₁ f hf]

/-- A horizontal coefficient is the selected indicator above minus that below; a vertical
coefficient is the indicator on the left minus that on the right. -/
def boundaryCoeff (D : GridFilling) : GridEdge → ℤ
  | .horizontal v => D.cellCoeff v - D.cellCoeff (v.pred 1)
  | .vertical v => D.cellCoeff (v.pred 0) - D.cellCoeff v

/-- The four oriented grid edges contributed by one positively oriented
cell, before adjacent cells are cancelled. -/
noncomputable def cellBoundaryChain (v : GridIndex) : GridEdge →₀ ℤ :=
  Finsupp.single (.horizontal v) 1 -
    Finsupp.single (.horizontal (v.succ 1)) 1 +
      Finsupp.single (.vertical (v.succ 0)) 1 -
        Finsupp.single (.vertical v) 1

/-- The finitely supported oriented edge chain obtained by summing all cell
boundaries.  Its coefficients are exactly `boundaryCoeff`. -/
noncomputable def boundaryChain (D : GridFilling) : GridEdge →₀ ℤ :=
  ∑ v ∈ D.cells, cellBoundaryChain v

@[simp]
private theorem sum_horizontal_single (s : Finset GridIndex) (v : GridIndex) :
    ∑ x ∈ s, (Finsupp.single (GridEdge.horizontal x) (1 : ℤ))
      (GridEdge.horizontal v) =
      if v ∈ s then 1 else 0 := by
  classical
  split
  · rename_i hv
    rw [Finset.sum_eq_single v]
    · simp
    · intro x hx hne
      simp [hne]
    · exact fun h ↦ (h hv).elim
  · rename_i hv
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finsupp.single_apply]
    split
    · rename_i h
      exfalso
      exact hv (GridEdge.horizontal.inj h ▸ hx)
    · rfl

@[simp]
private theorem sum_vertical_single (s : Finset GridIndex) (v : GridIndex) :
    ∑ x ∈ s, (Finsupp.single (GridEdge.vertical x) (1 : ℤ))
      (GridEdge.vertical v) =
      if v ∈ s then 1 else 0 := by
  classical
  split
  · rename_i hv
    rw [Finset.sum_eq_single v]
    · simp
    · intro x hx hne
      simp [hne]
    · exact fun h ↦ (h hv).elim
  · rename_i hv
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finsupp.single_apply]
    split
    · rename_i h
      exfalso
      exact hv (GridEdge.vertical.inj h ▸ hx)
    · rfl

@[simp]
private theorem sum_horizontal_succ_single
    (s : Finset GridIndex) (v : GridIndex) (i : Fin 2) :
    ∑ x ∈ s, (Finsupp.single (GridEdge.horizontal (x.succ i)) (1 : ℤ))
      (GridEdge.horizontal v) =
      if v.pred i ∈ s then 1 else 0 := by
  classical
  by_cases hp : v.pred i ∈ s
  · have hrhs : (if v.pred i ∈ s then (1 : ℤ) else 0) = 1 := by simp [hp]
    rw [hrhs, Finset.sum_eq_single (v.pred i)]
    · simp
    · intro x hx hne
      simp only [Finsupp.single_apply]
      split
      · rename_i h
        exfalso
        apply hne
        exact (GridIndex.succ_eq_iff_eq_pred x v i).mp (GridEdge.horizontal.inj h)
      · rfl
    · exact fun h ↦ (h hp).elim
  · have hrhs : (if v.pred i ∈ s then (1 : ℤ) else 0) = 0 := by simp [hp]
    rw [hrhs]
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finsupp.single_apply]
    split
    · rename_i h
      exfalso
      apply hp
      rw [← (GridIndex.succ_eq_iff_eq_pred x v i).mp (GridEdge.horizontal.inj h)]
      exact hx
    · rfl

@[simp]
private theorem sum_vertical_succ_single
    (s : Finset GridIndex) (v : GridIndex) (i : Fin 2) :
    ∑ x ∈ s, (Finsupp.single (GridEdge.vertical (x.succ i)) (1 : ℤ))
      (GridEdge.vertical v) =
      if v.pred i ∈ s then 1 else 0 := by
  classical
  by_cases hp : v.pred i ∈ s
  · have hrhs : (if v.pred i ∈ s then (1 : ℤ) else 0) = 1 := by simp [hp]
    rw [hrhs, Finset.sum_eq_single (v.pred i)]
    · simp
    · intro x hx hne
      simp only [Finsupp.single_apply]
      split
      · rename_i h
        exfalso
        apply hne
        exact (GridIndex.succ_eq_iff_eq_pred x v i).mp (GridEdge.vertical.inj h)
      · rfl
    · exact fun h ↦ (h hp).elim
  · have hrhs : (if v.pred i ∈ s then (1 : ℤ) else 0) = 0 := by simp [hp]
    rw [hrhs]
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finsupp.single_apply]
    split
    · rename_i h
      exfalso
      apply hp
      rw [← (GridIndex.succ_eq_iff_eq_pred x v i).mp (GridEdge.vertical.inj h)]
      exact hx
    · rfl

/-- The summed boundary chain has the above-minus-below cell coefficient on each horizontal edge.

```lean
theorem boundaryChain_horizontal (D : GridFilling) (v : GridIndex) :
    D.boundaryChain (.horizontal v) = D.boundaryCoeff (.horizontal v)
``` -/
@[simp]
theorem boundaryChain_horizontal (D : GridFilling) (v : GridIndex) :
    D.boundaryChain (.horizontal v) = D.boundaryCoeff (.horizontal v) := by
  classical
  simp [boundaryChain, cellBoundaryChain, boundaryCoeff, cellCoeff]

/-- The summed boundary chain has the left-minus-right cell coefficient on each vertical edge.

```lean
theorem boundaryChain_vertical (D : GridFilling) (v : GridIndex) :
    D.boundaryChain (.vertical v) = D.boundaryCoeff (.vertical v)
``` -/
@[simp]
theorem boundaryChain_vertical (D : GridFilling) (v : GridIndex) :
    D.boundaryChain (.vertical v) = D.boundaryCoeff (.vertical v) := by
  classical
  simp [boundaryChain, cellBoundaryChain, boundaryCoeff, cellCoeff]

/-- A horizontal edge cancels exactly when its adjacent cell indicators agree.

```lean
theorem horizontal_boundaryCoeff_eq_zero_iff (D : GridFilling) (v : GridIndex) :
    D.boundaryCoeff (.horizontal v) = 0 ↔
      D.cellCoeff v = D.cellCoeff (v.pred 1)
``` -/
theorem horizontal_boundaryCoeff_eq_zero_iff (D : GridFilling) (v : GridIndex) :
    D.boundaryCoeff (.horizontal v) = 0 ↔
      D.cellCoeff v = D.cellCoeff (v.pred 1) := by
  simp [boundaryCoeff, sub_eq_zero]

/-- A vertical edge cancels exactly when its adjacent cell indicators agree.

```lean
theorem vertical_boundaryCoeff_eq_zero_iff (D : GridFilling) (v : GridIndex) :
    D.boundaryCoeff (.vertical v) = 0 ↔
      D.cellCoeff (v.pred 0) = D.cellCoeff v
``` -/
theorem vertical_boundaryCoeff_eq_zero_iff (D : GridFilling) (v : GridIndex) :
    D.boundaryCoeff (.vertical v) = 0 ↔
      D.cellCoeff (v.pred 0) = D.cellCoeff v := by
  simp [boundaryCoeff, sub_eq_zero]

/-- The four canonical edges contributed by one selected cell before
cancellation. -/
def cellEdges (v : GridIndex) : Finset GridEdge :=
  {.horizontal v, .horizontal (v.succ 1),
    .vertical v, .vertical (v.succ 0)}

/-- Finite reduced boundary: candidate cell edges filtered by nonzero net
coefficient. -/
def boundaryEdges (D : GridFilling) : Finset GridEdge :=
  (D.cells.biUnion cellEdges).filter fun e => D.boundaryCoeff e ≠ 0

/-- The reduced boundary edges are exactly those with nonzero net integer coefficient.

```lean
theorem mem_boundaryEdges_iff (D : GridFilling) (e : GridEdge) :
    e ∈ D.boundaryEdges ↔ D.boundaryCoeff e ≠ 0
``` -/
theorem mem_boundaryEdges_iff (D : GridFilling) (e : GridEdge) :
    e ∈ D.boundaryEdges ↔ D.boundaryCoeff e ≠ 0 := by
  rw [boundaryEdges, Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  cases e with
  | horizontal v =>
      by_cases hv : v ∈ D.cells
      · exact Finset.mem_biUnion.mpr ⟨v, hv, by simp [cellEdges]⟩
      · have hp : v.pred 1 ∈ D.cells := by
          by_contra hp
          apply h
          simp [boundaryCoeff, cellCoeff, hv, hp]
        exact Finset.mem_biUnion.mpr
          ⟨v.pred 1, hp, by simp [cellEdges]⟩
  | vertical v =>
      by_cases hv : v ∈ D.cells
      · exact Finset.mem_biUnion.mpr ⟨v, hv, by simp [cellEdges]⟩
      · have hp : v.pred 0 ∈ D.cells := by
          by_contra hp
          apply h
          simp [boundaryCoeff, cellCoeff, hv, hp]
        exact Finset.mem_biUnion.mpr
          ⟨v.pred 0, hp, by simp [cellEdges]⟩

/-- Every surviving boundary edge has coefficient one or negative one.

```lean
theorem boundaryCoeff_eq_one_or_neg_one_of_mem
    (D : GridFilling) {e : GridEdge} (he : e ∈ D.boundaryEdges) :
    D.boundaryCoeff e = 1 ∨ D.boundaryCoeff e = -1
``` -/
theorem boundaryCoeff_eq_one_or_neg_one_of_mem
    (D : GridFilling) {e : GridEdge} (he : e ∈ D.boundaryEdges) :
    D.boundaryCoeff e = 1 ∨ D.boundaryCoeff e = -1 := by
  rw [mem_boundaryEdges_iff] at he
  cases e with
  | horizontal v =>
      simp only [boundaryCoeff, cellCoeff] at he ⊢
      split_ifs at he ⊢ <;> omega
  | vertical v =>
      simp only [boundaryCoeff, cellCoeff] at he ⊢
      split_ifs at he ⊢ <;> omega

/-- The initial point of a canonical horizontal or vertical edge is its base grid vertex. -/
noncomputable def edgeStart (D : GridFilling) : GridEdge → ℂ
  | .horizontal v => D.point v
  | .vertical v => D.point v

/-- The endpoint is the next first-coordinate vertex for a horizontal edge and the next
second-coordinate vertex for a vertical edge. -/
noncomputable def edgeEnd (D : GridFilling) : GridEdge → ℂ
  | .horizontal v => D.point (v.succ 0)
  | .vertical v => D.point (v.succ 1)

/-- Geometric segment traced by a grid edge. -/
noncomputable def edgeTrace (D : GridFilling) (e : GridEdge) : Set ℂ :=
  segment ℝ (D.edgeStart e) (D.edgeEnd e)

set_option linter.flexible false in
/-- Each canonical edge of a cell lies in that cell's closed carrier.

```lean
theorem edgeTrace_subset_cell_carrier_of_mem_cellEdges
    (D : GridFilling) (v : GridIndex) {e : GridEdge} (he : e ∈ cellEdges v) :
    D.edgeTrace e ⊆ (D.cell v).carrier
``` -/
theorem edgeTrace_subset_cell_carrier_of_mem_cellEdges
    (D : GridFilling) (v : GridIndex) {e : GridEdge} (he : e ∈ cellEdges v) :
    D.edgeTrace e ⊆ (D.cell v).carrier := by
  classical
  simp only [cellEdges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with h | h | h | h <;> subst e <;> rw [edgeTrace] <;>
    apply (D.cell v).convex_carrier.segment_subset <;>
    rw [D.mem_cell_carrier_iff] <;>
    simp [edgeStart, edgeEnd, point, gridPoint, GridIndex.succ]
  all_goals
    constructor <;>
      exact (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)

/-- Each reduced boundary edge lies in at least one selected cell's closed carrier.

```lean
theorem exists_selected_cell_of_mem_boundaryEdges
    (D : GridFilling) {e : GridEdge} (he : e ∈ D.boundaryEdges) :
    ∃ v ∈ D.cells, D.edgeTrace e ⊆ (D.cell v).carrier
``` -/
theorem exists_selected_cell_of_mem_boundaryEdges
    (D : GridFilling) {e : GridEdge} (he : e ∈ D.boundaryEdges) :
    ∃ v ∈ D.cells, D.edgeTrace e ⊆ (D.cell v).carrier := by
  rw [boundaryEdges, Finset.mem_filter] at he
  rcases Finset.mem_biUnion.mp he.1 with ⟨v, hv, hev⟩
  exact ⟨v, hv, D.edgeTrace_subset_cell_carrier_of_mem_cellEdges v hev⟩

/-- A canonical edge trace is a compact complex line segment.

```lean
theorem isCompact_edgeTrace (D : GridFilling) (e : GridEdge) :
    IsCompact (D.edgeTrace e)
``` -/
theorem isCompact_edgeTrace (D : GridFilling) (e : GridEdge) :
    IsCompact (D.edgeTrace e) := by
  rw [edgeTrace, segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

/-- A canonical edge trace is closed in the complex plane.

```lean
theorem isClosed_edgeTrace (D : GridFilling) (e : GridEdge) :
    IsClosed (D.edgeTrace e)
``` -/
theorem isClosed_edgeTrace (D : GridFilling) (e : GridEdge) :
    IsClosed (D.edgeTrace e) := (D.isCompact_edgeTrace e).isClosed

/-- The complete stated horizontal coordinate interval belongs to the corresponding edge trace.

```lean
theorem horizontal_point_mem_edgeTrace (D : GridFilling) (v : GridIndex)
    {x : ℝ} (hx : x ∈ Icc ((v 0 : ℝ) / D.scale)
      (((v 0 : ℝ) + 1) / D.scale)) :
    (x : ℂ) + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I ∈
      D.edgeTrace (.horizontal v)
``` -/
theorem horizontal_point_mem_edgeTrace (D : GridFilling) (v : GridIndex)
    {x : ℝ} (hx : x ∈ Icc ((v 0 : ℝ) / D.scale)
      (((v 0 : ℝ) + 1) / D.scale)) :
    (x : ℂ) + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I ∈
      D.edgeTrace (.horizontal v) := by
  let t : ℝ := D.scale * x - (v 0 : ℝ)
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    have hlow := (div_le_iff₀ D.scale_pos).1 hx.1
    have hupp := (le_div_iff₀ D.scale_pos).1 hx.2
    dsimp [t]
    constructor <;> linarith
  rw [edgeTrace]
  have heq :
      (x : ℂ) + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I =
        AffineMap.lineMap (D.edgeStart (.horizontal v))
          (D.edgeEnd (.horizontal v)) t := by
    apply Complex.ext
    · simp [AffineMap.lineMap_apply_module', edgeStart, edgeEnd, point,
        gridPoint, GridIndex.succ, t]
      field_simp [D.scale_pos.ne']
      ring
    · simp [AffineMap.lineMap_apply_module', edgeStart, edgeEnd, point,
        gridPoint, GridIndex.succ, t]
  rw [heq]
  exact lineMap_mem_segment ℝ _ _ ht

/-- The complete stated vertical coordinate interval belongs to the corresponding edge trace.

```lean
theorem vertical_point_mem_edgeTrace (D : GridFilling) (v : GridIndex)
    {y : ℝ} (hy : y ∈ Icc ((v 1 : ℝ) / D.scale)
      (((v 1 : ℝ) + 1) / D.scale)) :
    ((v 0 : ℝ) / D.scale : ℂ) + (y : ℂ) * Complex.I ∈
      D.edgeTrace (.vertical v)
``` -/
theorem vertical_point_mem_edgeTrace (D : GridFilling) (v : GridIndex)
    {y : ℝ} (hy : y ∈ Icc ((v 1 : ℝ) / D.scale)
      (((v 1 : ℝ) + 1) / D.scale)) :
    ((v 0 : ℝ) / D.scale : ℂ) + (y : ℂ) * Complex.I ∈
      D.edgeTrace (.vertical v) := by
  let t : ℝ := D.scale * y - (v 1 : ℝ)
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    have hlow := (div_le_iff₀ D.scale_pos).1 hy.1
    have hupp := (le_div_iff₀ D.scale_pos).1 hy.2
    dsimp [t]
    constructor <;> linarith
  rw [edgeTrace]
  have heq :
      ((v 0 : ℝ) / D.scale : ℂ) + (y : ℂ) * Complex.I =
        AffineMap.lineMap (D.edgeStart (.vertical v))
          (D.edgeEnd (.vertical v)) t := by
    apply Complex.ext
    · simp [AffineMap.lineMap_apply_module', edgeStart, edgeEnd, point,
        gridPoint, GridIndex.succ, t]
    · simp [AffineMap.lineMap_apply_module', edgeStart, edgeEnd, point,
        gridPoint, GridIndex.succ, t]
      field_simp [D.scale_pos.ne']
      ring
  rw [heq]
  exact lineMap_mem_segment ℝ _ _ ht

/-- Banach-valued integral along one canonically oriented boundary edge. -/
noncomputable def edgeIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling)
    (e : GridEdge) (f : ℂ → E) : E :=
  match e with
  | .horizontal v =>
      ∫ x : ℝ in (v 0 : ℝ) / D.scale..((v 0 : ℝ) + 1) / D.scale,
        f (x + ((v 1 : ℝ) / D.scale) * Complex.I)
  | .vertical v =>
      Complex.I •
        ∫ y : ℝ in (v 1 : ℝ) / D.scale..((v 1 : ℝ) + 1) / D.scale,
          f (((v 0 : ℝ) / D.scale) + y * Complex.I)

/-- The boundary integral of one grid cell is the signed sum of its four
canonical grid-edge integrals.

```lean
theorem cell_boundaryIntegral_eq_edgeIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (v : GridIndex) (f : ℂ → E) :
    (D.cell v).boundaryIntegral f =
      D.edgeIntegral (.horizontal v) f -
        D.edgeIntegral (.horizontal (v.succ 1)) f +
          D.edgeIntegral (.vertical (v.succ 0)) f -
            D.edgeIntegral (.vertical v) f
``` -/
theorem cell_boundaryIntegral_eq_edgeIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (v : GridIndex) (f : ℂ → E) :
    (D.cell v).boundaryIntegral f =
      D.edgeIntegral (.horizontal v) f -
        D.edgeIntegral (.horizontal (v.succ 1)) f +
          D.edgeIntegral (.vertical (v.succ 0)) f -
            D.edgeIntegral (.vertical v) f := by
  simp [RectilinearRectangle.boundaryIntegral, edgeIntegral, cell, gridCell,
    gridPoint, GridIndex.succ]

/-- Integration of a finitely supported oriented grid-edge chain. -/
noncomputable def edgeIntegralAddHom {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling) (f : ℂ → E) :
    (GridEdge →₀ ℤ) →+ E where
  toFun c := c.sum fun e n ↦ n • D.edgeIntegral e f
  map_zero' := by simp
  map_add' c d := by
    apply Finsupp.sum_add_index'
    · intro e
      simp
    · intro e m n
      simp [add_zsmul]

/-- The additive edge-chain integral is the finite sum weighted by its integer edge coefficients.

```lean
theorem edgeIntegralAddHom_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling) (f : ℂ → E)
    (c : GridEdge →₀ ℤ) :
    D.edgeIntegralAddHom f c = c.sum fun e n ↦ n • D.edgeIntegral e f
``` -/
@[simp]
theorem edgeIntegralAddHom_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling) (f : ℂ → E)
    (c : GridEdge →₀ ℤ) :
    D.edgeIntegralAddHom f c = c.sum fun e n ↦ n • D.edgeIntegral e f := rfl

/-- Integrating a cell's four signed canonical edges gives its counterclockwise rectangle boundary
integral.

```lean
theorem edgeIntegralAddHom_cellBoundaryChain {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → E) (v : GridIndex) :
    D.edgeIntegralAddHom f (cellBoundaryChain v) =
      (D.cell v).boundaryIntegral f
``` -/
@[simp]
theorem edgeIntegralAddHom_cellBoundaryChain {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → E) (v : GridIndex) :
    D.edgeIntegralAddHom f (cellBoundaryChain v) =
      (D.cell v).boundaryIntegral f := by
  rw [cellBoundaryChain, map_sub, map_add, map_sub]
  simp [cell_boundaryIntegral_eq_edgeIntegral]

/-- The Cauchy-kernel integral along one grid edge varies continuously with
the pole away from that edge.

```lean
theorem continuousOn_edgeIntegral_cauchyKernel (D : GridFilling) (e : GridEdge) :
    ContinuousOn (fun z : ℂ ↦ D.edgeIntegral e (fun ξ ↦ (ξ - z)⁻¹))
      (D.edgeTrace e)ᶜ
``` -/
theorem continuousOn_edgeIntegral_cauchyKernel (D : GridFilling) (e : GridEdge) :
    ContinuousOn (fun z : ℂ ↦ D.edgeIntegral e (fun ξ ↦ (ξ - z)⁻¹))
      (D.edgeTrace e)ᶜ := by
  rw [continuousOn_iff_continuous_domRestrict]
  cases e with
  | horizontal v =>
      let a : ℝ := (v 0 : ℝ) / D.scale
      let b : ℝ := ((v 0 : ℝ) + 1) / D.scale
      have hab : a ≤ b := by
        dsimp [a, b]
        exact (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
      let q : ℝ → ℂ := fun x ↦
        (Set.projIcc a b hab x : ℝ) + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I
      have hqmem (x : ℝ) : q x ∈ D.edgeTrace (.horizontal v) := by
        apply D.horizontal_point_mem_edgeTrace v
        exact (Set.projIcc a b hab x).property
      have hjoint : Continuous (Function.uncurry fun
          (p : {p : ℂ // p ∈ (D.edgeTrace (.horizontal v))ᶜ})
            (x : ℝ) ↦ (q x - (p : ℂ))⁻¹) := by
        apply Continuous.inv₀ (by fun_prop)
        rintro ⟨p, x⟩ hzero
        apply p.property
        have hpq : q x = (p : ℂ) := sub_eq_zero.mp hzero
        simpa [hpq] using hqmem x
      have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := MeasureTheory.volume) hjoint a b
      change Continuous fun p : {p : ℂ // p ∈ (D.edgeTrace (.horizontal v))ᶜ} ↦
        ∫ x : ℝ in a..b,
          ((x : ℂ) + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I - (p : ℂ))⁻¹
      convert hcont using 1
      funext p
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc a b := by simpa [uIcc_of_le hab] using hx
      change
        ((x : ℂ) + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I - (p : ℂ))⁻¹ =
          (q x - (p : ℂ))⁻¹
      rw [show q x =
          (x : ℂ) + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I by
        simp [q, Set.projIcc_of_mem hab hx']]
  | vertical v =>
      let a : ℝ := (v 1 : ℝ) / D.scale
      let b : ℝ := ((v 1 : ℝ) + 1) / D.scale
      have hab : a ≤ b := by
        dsimp [a, b]
        exact (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
      let q : ℝ → ℂ := fun y ↦
        ((v 0 : ℝ) / D.scale : ℂ) + (Set.projIcc a b hab y : ℝ) * Complex.I
      have hqmem (y : ℝ) : q y ∈ D.edgeTrace (.vertical v) := by
        apply D.vertical_point_mem_edgeTrace v
        exact (Set.projIcc a b hab y).property
      have hjoint : Continuous (Function.uncurry fun
          (p : {p : ℂ // p ∈ (D.edgeTrace (.vertical v))ᶜ})
            (y : ℝ) ↦ (q y - (p : ℂ))⁻¹) := by
        apply Continuous.inv₀ (by fun_prop)
        rintro ⟨p, y⟩ hzero
        apply p.property
        have hpq : q y = (p : ℂ) := sub_eq_zero.mp hzero
        simpa [hpq] using hqmem y
      have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := MeasureTheory.volume) hjoint a b
      have hcont' : Continuous fun
          p : {p : ℂ // p ∈ (D.edgeTrace (.vertical v))ᶜ} ↦
          ∫ y : ℝ in a..b,
            (((v 0 : ℝ) / D.scale : ℂ) + (y : ℂ) * Complex.I - (p : ℂ))⁻¹ := by
        convert hcont using 1
        funext p
        apply intervalIntegral.integral_congr
        intro y hy
        have hy' : y ∈ Icc a b := by simpa [uIcc_of_le hab] using hy
        change
          (((v 0 : ℝ) / D.scale : ℂ) + (y : ℂ) * Complex.I - (p : ℂ))⁻¹ =
            (q y - (p : ℂ))⁻¹
        rw [show q y =
            ((v 0 : ℝ) / D.scale : ℂ) + (y : ℂ) * Complex.I by
          simp [q, Set.projIcc_of_mem hab hy']]
      exact hcont'.const_smul Complex.I

/-- Reduced geometric boundary after cancellation of internal edges. -/
noncomputable def reducedTrace (D : GridFilling) : Set ℂ :=
  ⋃ e ∈ D.boundaryEdges, D.edgeTrace e

/-- The reduced trace is closed as a finite union of closed edge segments.

```lean
theorem isClosed_reducedTrace (D : GridFilling) : IsClosed D.reducedTrace
``` -/
theorem isClosed_reducedTrace (D : GridFilling) : IsClosed D.reducedTrace := by
  apply isClosed_biUnion_finset
  intro e he
  exact D.isClosed_edgeTrace e

/-- Integral over the reduced boundary, with the signed net coefficient of
each surviving edge. -/
noncomputable def reducedIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling) (f : ℂ → E) : E :=
  ∑ e ∈ D.boundaryEdges, D.boundaryCoeff e • D.edgeIntegral e f

/-- Integrands agreeing on the reduced trace have equal complete Banach-valued reduced integrals.

```lean
theorem reducedIntegral_congr {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling)
    {f g : ℂ → E} (hfg : Set.EqOn f g D.reducedTrace) :
    D.reducedIntegral f = D.reducedIntegral g
``` -/
theorem reducedIntegral_congr {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling)
    {f g : ℂ → E} (hfg : Set.EqOn f g D.reducedTrace) :
    D.reducedIntegral f = D.reducedIntegral g := by
  unfold reducedIntegral
  apply Finset.sum_congr rfl
  intro e he
  have hedge : D.edgeIntegral e f = D.edgeIntegral e g := by
    cases e with
    | horizontal v =>
        simp only [edgeIntegral]
        apply intervalIntegral.integral_congr
        intro x hx
        apply hfg
        have hab : (v 0 : ℝ) / D.scale ≤ ((v 0 : ℝ) + 1) / D.scale :=
          (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
        exact mem_iUnion_of_mem (.horizontal v)
          (mem_iUnion_of_mem he (D.horizontal_point_mem_edgeTrace v (by
            simpa [uIcc_of_le hab] using hx)))
    | vertical v =>
        simp only [edgeIntegral]
        apply congrArg (fun q : E ↦ Complex.I • q)
        apply intervalIntegral.integral_congr
        intro y hy
        apply hfg
        have hab : (v 1 : ℝ) / D.scale ≤ ((v 1 : ℝ) + 1) / D.scale :=
          (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
        exact mem_iUnion_of_mem (.vertical v)
          (mem_iUnion_of_mem he (D.vertical_point_mem_edgeTrace v (by
            simpa [uIcc_of_le hab] using hy)))
  rw [hedge]

/-- A continuous complex-linear map commutes with an edge integral when the integrand is continuous
on that edge.

```lean
theorem edgeIntegral_comp_comm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (D : GridFilling) (e : GridEdge) (L : E →L[ℂ] F) (f : ℂ → E)
    (hf : ContinuousOn f (D.edgeTrace e)) :
    D.edgeIntegral e (fun z ↦ L (f z)) = L (D.edgeIntegral e f)
``` -/
theorem edgeIntegral_comp_comm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (D : GridFilling) (e : GridEdge) (L : E →L[ℂ] F) (f : ℂ → E)
    (hf : ContinuousOn f (D.edgeTrace e)) :
    D.edgeIntegral e (fun z ↦ L (f z)) = L (D.edgeIntegral e f) := by
  cases e with
  | horizontal v =>
      have hcont : ContinuousOn
          (fun x : ℝ ↦ f (x + ((v 1 : ℝ) / D.scale) * Complex.I))
          (uIcc ((v 0 : ℝ) / D.scale) (((v 0 : ℝ) + 1) / D.scale)) := by
        have hpath : Continuous
            (fun x : ℝ ↦ (x : ℂ) + ((v 1 : ℝ) / D.scale) * Complex.I) := by
          fun_prop
        apply hf.comp hpath.continuousOn
        intro x hx
        apply D.horizontal_point_mem_edgeTrace v
        have hab : (v 0 : ℝ) / D.scale ≤ ((v 0 : ℝ) + 1) / D.scale :=
          (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
        simpa [uIcc_of_le hab] using hx
      exact L.intervalIntegral_comp_comm hcont.intervalIntegrable
  | vertical v =>
      have hcont : ContinuousOn
          (fun y : ℝ ↦ f (((v 0 : ℝ) / D.scale) + y * Complex.I))
          (uIcc ((v 1 : ℝ) / D.scale) (((v 1 : ℝ) + 1) / D.scale)) := by
        have hpath : Continuous
            (fun y : ℝ ↦ ((v 0 : ℝ) / D.scale : ℂ) + y * Complex.I) := by
          fun_prop
        apply hf.comp hpath.continuousOn
        intro y hy
        apply D.vertical_point_mem_edgeTrace v
        have hab : (v 1 : ℝ) / D.scale ≤ ((v 1 : ℝ) + 1) / D.scale :=
          (div_le_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
        simpa [uIcc_of_le hab] using hy
      simp only [edgeIntegral, map_smul]
      rw [L.intervalIntegral_comp_comm hcont.intervalIntegrable]

/-- A continuous complex-linear map commutes with the reduced integral when the integrand is
continuous on a containing set.

```lean
theorem reducedIntegral_comp_comm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (D : GridFilling) (L : E →L[ℂ] F) (f : ℂ → E)
    {U : Set ℂ} (hD : D.reducedTrace ⊆ U) (hf : ContinuousOn f U) :
    D.reducedIntegral (fun z ↦ L (f z)) = L (D.reducedIntegral f)
``` -/
theorem reducedIntegral_comp_comm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (D : GridFilling) (L : E →L[ℂ] F) (f : ℂ → E)
    {U : Set ℂ} (hD : D.reducedTrace ⊆ U) (hf : ContinuousOn f U) :
    D.reducedIntegral (fun z ↦ L (f z)) = L (D.reducedIntegral f) := by
  unfold reducedIntegral
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [map_zsmul, D.edgeIntegral_comp_comm e L f]
  exact hf.mono fun z hz ↦ hD
    (mem_iUnion_of_mem e (mem_iUnion_of_mem he hz))

/-- The reduced boundary-edge set is exactly the support of the signed boundary chain.

```lean
theorem boundaryEdges_eq_boundaryChain_support (D : GridFilling) :
    D.boundaryEdges = D.boundaryChain.support
``` -/
theorem boundaryEdges_eq_boundaryChain_support (D : GridFilling) :
    D.boundaryEdges = D.boundaryChain.support := by
  ext e
  rw [mem_boundaryEdges_iff, Finsupp.mem_support_iff]
  cases e <;> simp

/-- The reduced integral is the additive edge-chain integral evaluated at the filling boundary
chain.

```lean
theorem reducedIntegral_eq_edgeIntegralAddHom {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → E) :
    D.reducedIntegral f = D.edgeIntegralAddHom f D.boundaryChain
``` -/
theorem reducedIntegral_eq_edgeIntegralAddHom {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → E) :
    D.reducedIntegral f = D.edgeIntegralAddHom f D.boundaryChain := by
  rw [reducedIntegral, edgeIntegralAddHom_apply,
    boundaryEdges_eq_boundaryChain_support]
  apply Finset.sum_congr rfl
  intro e he
  cases e <;> simp

/-- The reduced Cauchy-kernel integral is continuous in its pole off the reduced trace.

```lean
theorem continuousAt_reducedIntegral_cauchyKernel_of_not_mem_reducedTrace
    (D : GridFilling) {z : ℂ} (hz : z ∉ D.reducedTrace) :
    ContinuousAt (fun w : ℂ ↦ D.reducedIntegral (fun ξ ↦ (ξ - w)⁻¹)) z
``` -/
theorem continuousAt_reducedIntegral_cauchyKernel_of_not_mem_reducedTrace
    (D : GridFilling) {z : ℂ} (hz : z ∉ D.reducedTrace) :
    ContinuousAt (fun w : ℂ ↦ D.reducedIntegral (fun ξ ↦ (ξ - w)⁻¹)) z := by
  unfold reducedIntegral
  apply tendsto_finsetSum
  intro e he
  have hez : z ∈ (D.edgeTrace e)ᶜ := by
    intro hze
    apply hz
    exact mem_iUnion_of_mem e (mem_iUnion_of_mem he hze)
  have hedge : ContinuousAt
      (fun w : ℂ ↦ D.edgeIntegral e (fun ξ ↦ (ξ - w)⁻¹)) z :=
    ((D.continuousOn_edgeIntegral_cauchyKernel e) z hez).continuousAt
      ((D.isClosed_edgeTrace e).isOpen_compl.mem_nhds hez)
  exact (hedge.const_smul (D.boundaryCoeff e)).tendsto

/-- Algebraic discrete Stokes: summing the rectangle boundaries of all
selected cells gives exactly the integral over the reduced oriented edge
chain.

```lean
theorem toCycle_integral_eq_reducedIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → E) :
    D.toCycle.integral f = D.reducedIntegral f
``` -/
theorem toCycle_integral_eq_reducedIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → E) :
    D.toCycle.integral f = D.reducedIntegral f := by
  rw [toCycle_integral, reducedIntegral_eq_edgeIntegralAddHom]
  change (∑ v ∈ D.cells, (D.cell v).boundaryIntegral f) =
    D.edgeIntegralAddHom f (∑ v ∈ D.cells, cellBoundaryChain v)
  simp only [map_sum, edgeIntegralAddHom_cellBoundaryChain]

/-- The filling's analytic winding index is continuous off its reduced boundary.

```lean
theorem continuousAt_toCycle_index_of_not_mem_reducedTrace
    (D : GridFilling) {z : ℂ} (hz : z ∉ D.reducedTrace) :
    ContinuousAt (fun w : ℂ ↦ D.toCycle.index w) z
``` -/
theorem continuousAt_toCycle_index_of_not_mem_reducedTrace
    (D : GridFilling) {z : ℂ} (hz : z ∉ D.reducedTrace) :
    ContinuousAt (fun w : ℂ ↦ D.toCycle.index w) z := by
  have hred := D.continuousAt_reducedIntegral_cauchyKernel_of_not_mem_reducedTrace hz
  have heq : (fun w : ℂ ↦ D.toCycle.index w) = fun w ↦
      ((2 * Real.pi : ℂ) * Complex.I)⁻¹ *
        D.reducedIntegral (fun ξ ↦ (ξ - w)⁻¹) := by
    funext w
    rw [RectilinearCycle.index, D.toCycle_integral_eq_reducedIntegral]
  rw [heq]
  exact continuousAt_const.mul hred

/-- Closed region presented by the selected grid cells. -/
noncomputable def region (D : GridFilling) : Set ℂ :=
  ⋃ v ∈ D.cells, (D.cell v).carrier

/-- The selected-cell region is compact, including for an empty filling.

```lean
theorem isCompact_region (D : GridFilling) : IsCompact D.region
``` -/
theorem isCompact_region (D : GridFilling) : IsCompact D.region := by
  rw [region]
  apply D.cells.isCompact_biUnion
  intro v hv
  simpa [RectilinearRectangle.carrier, Complex.Rectangle] using
    (isCompact_uIcc.reProdIm isCompact_uIcc)

/-- The reduced trace lies in the selected closed-cell region.

```lean
theorem reducedTrace_subset_region (D : GridFilling) :
    D.reducedTrace ⊆ D.region
``` -/
theorem reducedTrace_subset_region (D : GridFilling) :
    D.reducedTrace ⊆ D.region := by
  intro z hz
  rw [reducedTrace] at hz
  rcases Set.mem_iUnion.mp hz with ⟨e, hz⟩
  rcases Set.mem_iUnion.mp hz with ⟨he, hze⟩
  obtain ⟨v, hv, hev⟩ := D.exists_selected_cell_of_mem_boundaryEdges he
  rw [region]
  exact Set.mem_iUnion_of_mem v (Set.mem_iUnion_of_mem hv (hev hze))

/-- Fine-grid selection rule: take every closed cell
meeting a prescribed thickening of `K`. -/
noncomputable def selectedCellSet (K : Set ℂ) (r t : ℝ) : Set GridIndex :=
  gridCellsMeeting t (Metric.cthickening r K)

/-- Open physical grid square at lattice index `v`. -/
noncomputable def cellInterior (D : GridFilling) (v : GridIndex) : Set ℂ :=
  Ioo ((v 0 : ℝ) / D.scale) (((v 0 : ℝ) + 1) / D.scale) ×ℂ
    Ioo ((v 1 : ℝ) / D.scale) (((v 1 : ℝ) + 1) / D.scale)

/-- Two integer coordinates determine a grid index. -/
def gridIndexEmbedding : GridIndex ↪ ℤ × ℤ where
  toFun v := (v 0, v 1)
  inj' := by
    intro v w h
    funext i
    fin_cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h

/-- At positive scale, only finitely many closed cells meet a bounded planar set.

```lean
theorem gridCellsMeeting_finite {S : Set ℂ} (hS : Bornology.IsBounded S)
    {t : ℝ} (ht : 0 < t) : (gridCellsMeeting t S).Finite
``` -/
theorem gridCellsMeeting_finite {S : Set ℂ} (hS : Bornology.IsBounded S)
    {t : ℝ} (ht : 0 < t) : (gridCellsMeeting t S).Finite := by
  obtain ⟨C, hSC⟩ := hS.subset_closedBall (0 : ℂ)
  have hC : ∀ z ∈ S, ‖z‖ ≤ C := by
    intro z hz
    simpa [Metric.mem_closedBall, dist_zero_right] using hSC hz
  let lo : ℤ := ⌊-t * C - 1⌋
  let hi : ℤ := ⌊t * C⌋
  let q : Finset (ℤ × ℤ) := Finset.Icc lo hi ×ˢ Finset.Icc lo hi
  have hpre : (gridIndexEmbedding ⁻¹' (q : Set (ℤ × ℤ))).Finite :=
    Set.Finite.preimage_embedding gridIndexEmbedding q.finite_toSet
  apply hpre.subset
  intro v hv
  rcases hv with ⟨z, hzcell, hzS⟩
  let D₀ : GridFilling := ofCells t ht ∅
  have hzcell' := (D₀.mem_cell_carrier_iff v z).1 hzcell
  have hzre : |z.re| ≤ C := (Complex.abs_re_le_norm z).trans (hC z hzS)
  have hzim : |z.im| ≤ C := (Complex.abs_im_le_norm z).trans (hC z hzS)
  have coord_bounds (i : Fin 2) (x : ℝ)
      (hx : x ∈ Icc ((v i : ℝ) / t) (((v i : ℝ) + 1) / t))
      (habs : |x| ≤ C) : v i ∈ Finset.Icc lo hi := by
    have hxlower : -C ≤ x := (neg_le_of_abs_le habs)
    have hxupper : x ≤ C := (le_of_abs_le habs)
    have hvupper_real : (v i : ℝ) ≤ t * C := by
      calc
        (v i : ℝ) ≤ t * x := by
          simpa [mul_comm] using (div_le_iff₀ ht).1 hx.1
        _ ≤ t * C := mul_le_mul_of_nonneg_left hxupper ht.le
    have hvlower_real : (-t * C - 1 : ℝ) ≤ (v i : ℝ) := by
      have htx : -t * C ≤ t * x := by
        nlinarith [mul_le_mul_of_nonneg_left hxlower ht.le]
      have hxu : t * x ≤ (v i : ℝ) + 1 := by
        simpa [mul_comm] using (le_div_iff₀ ht).1 hx.2
      linarith
    rw [Finset.mem_Icc]
    constructor
    · exact_mod_cast (Int.floor_le (-t * C - 1)).trans hvlower_real
    · exact Int.le_floor.mpr hvupper_real
  change (v 0, v 1) ∈ q
  rw [Finset.mem_product]
  exact ⟨coord_bounds 0 z.re hzcell'.1 hzre,
    coord_bounds 1 z.im hzcell'.2 hzim⟩

/-- At positive scale, the cells meeting a closed thickening of a compact planar set form a finite
set.

```lean
theorem selectedCellSet_finite (K : Set ℂ) (r : ℝ) {t : ℝ} (ht : 0 < t)
    (hK : IsCompact K) : (selectedCellSet K r t).Finite
``` -/
theorem selectedCellSet_finite (K : Set ℂ) (r : ℝ) {t : ℝ} (ht : 0 < t)
    (hK : IsCompact K) : (selectedCellSet K r t).Finite :=
  gridCellsMeeting_finite hK.cthickening.isBounded ht

/-- Finite filling consisting of every closed grid cell meeting a prescribed
closed thickening of `K`. -/
noncomputable def selectedFilling (K : Set ℂ) (r t : ℝ) (ht : 0 < t)
    (hK : IsCompact K) : GridFilling :=
  ofCells t ht (selectedCellSet_finite K r ht hK).toFinset

/-- Membership in the constructed filling is exactly the prescribed cell-thickening intersection
condition.

```lean
theorem mem_selectedFilling_cells (K : Set ℂ) (r : ℝ) {t : ℝ}
    (ht : 0 < t) (hK : IsCompact K) (v : GridIndex) :
    v ∈ (selectedFilling K r t ht hK).cells ↔ v ∈ selectedCellSet K r t
``` -/
@[simp]
theorem mem_selectedFilling_cells (K : Set ℂ) (r : ℝ) {t : ℝ}
    (ht : 0 < t) (hK : IsCompact K) (v : GridIndex) :
    v ∈ (selectedFilling K r t ht hK).cells ↔ v ∈ selectedCellSet K r t := by
  exact (selectedCellSet_finite K r ht hK).mem_toFinset

/-- Points in one closed cell have complex distance at most `2/D.scale`.

```lean
theorem dist_le_two_div_scale_of_mem_cell_carrier (D : GridFilling)
    (v : GridIndex) {z w : ℂ} (hz : z ∈ (D.cell v).carrier)
    (hw : w ∈ (D.cell v).carrier) : dist z w ≤ 2 / D.scale
``` -/
theorem dist_le_two_div_scale_of_mem_cell_carrier (D : GridFilling)
    (v : GridIndex) {z w : ℂ} (hz : z ∈ (D.cell v).carrier)
    (hw : w ∈ (D.cell v).carrier) : dist z w ≤ 2 / D.scale := by
  rw [D.mem_cell_carrier_iff] at hz hw
  have hwidth (i : Fin 2) :
      (((v i : ℝ) + 1) / D.scale) - (v i : ℝ) / D.scale = 1 / D.scale := by
    field_simp [D.scale_pos.ne']
    ring
  have hre : |z.re - w.re| ≤ 1 / D.scale := by
    rw [abs_le]
    constructor <;>
      linarith [hz.1.1, hz.1.2, hw.1.1, hw.1.2, hwidth 0]
  have him : |z.im - w.im| ≤ 1 / D.scale := by
    rw [abs_le]
    constructor <;>
      linarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2, hwidth 1]
  rw [dist_eq_norm]
  calc
    ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| :=
      Complex.norm_le_abs_re_add_abs_im (z - w)
    _ ≤ 1 / D.scale + 1 / D.scale := by simpa using add_le_add hre him
    _ = 2 / D.scale := by ring

/-- For nonnegative radius, each selected closed cell lies in the closed `(2/t+r)`-thickening of
the compact set.

```lean
theorem selectedFilling_cell_carrier_subset_cthickening
    (K : Set ℂ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) (hK : IsCompact K)
    {v : GridIndex} (hv : v ∈ (selectedFilling K r t ht hK).cells) :
    ((selectedFilling K r t ht hK).cell v).carrier ⊆
      Metric.cthickening (2 / t + r) K
``` -/
theorem selectedFilling_cell_carrier_subset_cthickening
    (K : Set ℂ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) (hK : IsCompact K)
    {v : GridIndex} (hv : v ∈ (selectedFilling K r t ht hK).cells) :
    ((selectedFilling K r t ht hK).cell v).carrier ⊆
      Metric.cthickening (2 / t + r) K := by
  rw [mem_selectedFilling_cells] at hv
  rcases hv with ⟨y, hycell, hyK⟩
  intro z hzcell
  apply Metric.cthickening_cthickening_subset (by positivity) hr K
  exact Metric.mem_cthickening_of_dist_le z y (2 / t)
    (Metric.cthickening r K) hyK
    ((selectedFilling K r t ht hK).dist_le_two_div_scale_of_mem_cell_carrier
      v hzcell hycell)

/-- For nonnegative radius, the full selected-cell region lies in the same closed
`(2/t+r)`-thickening.

```lean
theorem selectedFilling_region_subset_cthickening
    (K : Set ℂ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) (hK : IsCompact K) :
    (selectedFilling K r t ht hK).region ⊆ Metric.cthickening (2 / t + r) K
``` -/
theorem selectedFilling_region_subset_cthickening
    (K : Set ℂ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) (hK : IsCompact K) :
    (selectedFilling K r t ht hK).region ⊆ Metric.cthickening (2 / t + r) K := by
  intro z hz
  rw [region] at hz
  rcases Set.mem_iUnion.mp hz with ⟨v, hz⟩
  rcases Set.mem_iUnion.mp hz with ⟨hv, hzcell⟩
  exact selectedFilling_cell_carrier_subset_cthickening K hr ht hK hv hzcell

/-- For nonnegative radius, the reduced trace lies in the closed `(2/t+r)`-thickening.

```lean
theorem selectedFilling_reducedTrace_subset_cthickening
    (K : Set ℂ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) (hK : IsCompact K) :
    (selectedFilling K r t ht hK).reducedTrace ⊆
      Metric.cthickening (2 / t + r) K
``` -/
theorem selectedFilling_reducedTrace_subset_cthickening
    (K : Set ℂ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) (hK : IsCompact K) :
    (selectedFilling K r t ht hK).reducedTrace ⊆
      Metric.cthickening (2 / t + r) K := by
  intro z hz
  rw [reducedTrace] at hz
  rcases Set.mem_iUnion.mp hz with ⟨e, hz⟩
  rcases Set.mem_iUnion.mp hz with ⟨he, hze⟩
  rcases (selectedFilling K r t ht hK).exists_selected_cell_of_mem_boundaryEdges he with
    ⟨v, hv, hev⟩
  exact selectedFilling_cell_carrier_subset_cthickening K hr ht hK hv (hev hze)

/-- The selected filling's reduced trace is disjoint from the original compact set.

```lean
theorem selectedFilling_reducedTrace_disjoint
    (K : Set ℂ) {r t : ℝ} (ht : 0 < t) (hK : IsCompact K) :
    Disjoint (selectedFilling K r t ht hK).reducedTrace K
``` -/
theorem selectedFilling_reducedTrace_disjoint
    (K : Set ℂ) {r t : ℝ} (ht : 0 < t) (hK : IsCompact K) :
    Disjoint (selectedFilling K r t ht hK).reducedTrace K := by
  rw [Set.disjoint_left]
  intro z hztrace hzK
  let D := selectedFilling K r t ht hK
  rw [reducedTrace] at hztrace
  rcases Set.mem_iUnion.mp hztrace with ⟨e, hztrace⟩
  rcases Set.mem_iUnion.mp hztrace with ⟨he, hze⟩
  have selected_of_mem_carrier (v : GridIndex) (hzv : z ∈ (D.cell v).carrier) :
      v ∈ D.cells := by
    rw [mem_selectedFilling_cells]
    exact ⟨z, hzv, Metric.self_subset_cthickening K hzK⟩
  apply (D.mem_boundaryEdges_iff e).1 he
  cases e with
  | horizontal v =>
      have hzv : z ∈ (D.cell v).carrier :=
        D.edgeTrace_subset_cell_carrier_of_mem_cellEdges v (by simp [cellEdges]) hze
      have hzpred : z ∈ (D.cell (v.pred 1)).carrier :=
        D.edgeTrace_subset_cell_carrier_of_mem_cellEdges (v.pred 1)
          (by simp [cellEdges]) hze
      simp [boundaryCoeff, cellCoeff, selected_of_mem_carrier v hzv,
        selected_of_mem_carrier (v.pred 1) hzpred]
  | vertical v =>
      have hzv : z ∈ (D.cell v).carrier :=
        D.edgeTrace_subset_cell_carrier_of_mem_cellEdges v (by simp [cellEdges]) hze
      have hzpred : z ∈ (D.cell (v.pred 0)).carrier :=
        D.edgeTrace_subset_cell_carrier_of_mem_cellEdges (v.pred 0)
          (by simp [cellEdges]) hze
      simp [boundaryCoeff, cellCoeff, selected_of_mem_carrier v hzv,
        selected_of_mem_carrier (v.pred 0) hzpred]

/-- A cell's open interior lies in its closed carrier.

```lean
theorem cellInterior_subset_carrier (D : GridFilling) (v : GridIndex) :
    D.cellInterior v ⊆ (D.cell v).carrier
``` -/
theorem cellInterior_subset_carrier (D : GridFilling) (v : GridIndex) :
    D.cellInterior v ⊆ (D.cell v).carrier := by
  intro z hz
  rw [mem_cell_carrier_iff]
  exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩

/-- A counterclockwise cell boundary has analytic index one at an interior point.

```lean
theorem index_of_cell_eq_one_of_mem_cellInterior (D : GridFilling)
    (v : GridIndex) {z : ℂ} (hz : z ∈ D.cellInterior v) :
    (RectilinearCycle.ofRectangle (D.cell v)).index z = 1
``` -/
theorem index_of_cell_eq_one_of_mem_cellInterior (D : GridFilling)
    (v : GridIndex) {z : ℂ} (hz : z ∈ D.cellInterior v) :
    (RectilinearCycle.ofRectangle (D.cell v)).index z = 1 := by
  rw [RectilinearCycle.index_ofRectangle, D.cell_eq_ofBounds]
  rw [RectilinearRectangle.boundaryIntegral_ofBounds_inv_sub_eq_two_pi_mul_I
    hz.1.1 hz.1.2 hz.2.1 hz.2.2]
  have h : (2 * Real.pi : ℂ) * Complex.I ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
    · exact Complex.I_ne_zero
  exact inv_mul_cancel₀ h

/-- A point in one cell's open interior belongs to no other closed cell at the same scale.

```lean
theorem eq_of_mem_cellInterior_of_mem_cell_carrier (D : GridFilling)
    {u v : GridIndex} {z : ℂ} (hzv : z ∈ D.cellInterior v)
    (hzu : z ∈ (D.cell u).carrier) : u = v
``` -/
theorem eq_of_mem_cellInterior_of_mem_cell_carrier (D : GridFilling)
    {u v : GridIndex} {z : ℂ} (hzv : z ∈ D.cellInterior v)
    (hzu : z ∈ (D.cell u).carrier) : u = v := by
  rw [mem_cell_carrier_iff] at hzu
  funext i
  fin_cases i
  · have huv : u 0 < v 0 + 1 := by
      exact_mod_cast ((div_le_iff₀ D.scale_pos).1 hzu.1.1).trans_lt
        ((lt_div_iff₀ D.scale_pos).1 hzv.1.2)
    have hvu : v 0 < u 0 + 1 := by
      exact_mod_cast ((div_lt_iff₀ D.scale_pos).1 hzv.1.1).trans_le
        ((le_div_iff₀ D.scale_pos).1 hzu.1.2)
    exact le_antisymm (Int.lt_add_one_iff.mp huv) (Int.lt_add_one_iff.mp hvu)
  · have huv : u 1 < v 1 + 1 := by
      exact_mod_cast ((div_le_iff₀ D.scale_pos).1 hzu.2.1).trans_lt
        ((lt_div_iff₀ D.scale_pos).1 hzv.2.2)
    have hvu : v 1 < u 1 + 1 := by
      exact_mod_cast ((div_lt_iff₀ D.scale_pos).1 hzv.2.1).trans_le
        ((le_div_iff₀ D.scale_pos).1 hzu.2.2)
    exact le_antisymm (Int.lt_add_one_iff.mp huv) (Int.lt_add_one_iff.mp hvu)

/-- At an interior point of a grid cell, the filling-cycle index is that cell's selected indicator
coerced to a complex number.

```lean
theorem toCycle_index_eq_cellCoeff_of_mem_cellInterior (D : GridFilling)
    (v : GridIndex) {z : ℂ} (hz : z ∈ D.cellInterior v) :
    D.toCycle.index z = (D.cellCoeff v : ℂ)
``` -/
theorem toCycle_index_eq_cellCoeff_of_mem_cellInterior (D : GridFilling)
    (v : GridIndex) {z : ℂ} (hz : z ∈ D.cellInterior v) :
    D.toCycle.index z = (D.cellCoeff v : ℂ) := by
  rw [toCycle_index]
  by_cases hv : v ∈ D.cells
  · rw [Finset.sum_eq_single v]
    · rw [D.index_of_cell_eq_one_of_mem_cellInterior v hz]
      simp [cellCoeff, hv]
    · intro u hu huv
      apply RectilinearCycle.index_ofRectangle_eq_zero_of_not_mem_carrier
      intro hzu
      exact huv (D.eq_of_mem_cellInterior_of_mem_cell_carrier hz hzu)
    · exact fun h ↦ (h hv).elim
  · rw [Finset.sum_eq_zero]
    · simp [cellCoeff, hv]
    · intro u hu
      apply RectilinearCycle.index_ofRectangle_eq_zero_of_not_mem_carrier
      intro hzu
      exact hv (D.eq_of_mem_cellInterior_of_mem_cell_carrier hz hzu ▸ hu)

/-- The half-open grid cell canonically owning `z`, using floor in each
coordinate. -/
noncomputable def ownerIndex (D : GridFilling) (z : ℂ) : GridIndex :=
  fun i => if i = 0 then ⌊D.scale * z.re⌋ else ⌊D.scale * z.im⌋

/-- The sign-reversed coordinate pair lies in a half-open cell box exactly when that cell is the
floor-based owner.

```lean
theorem complexBoxPoint_mem_cellBox_iff (D : GridFilling)
    (v : GridIndex) (z : ℂ) :
    complexBoxPoint z ∈ D.cellBox v ↔ D.ownerIndex z = v
``` -/
theorem complexBoxPoint_mem_cellBox_iff (D : GridFilling)
    (v : GridIndex) (z : ℂ) :
    complexBoxPoint z ∈ D.cellBox v ↔ D.ownerIndex z = v := by
  constructor
  · intro hz
    funext i
    fin_cases i
    · simpa [complexBoxPoint, cellBox, gridCellBox, ownerIndex] using
        (neg_mem_gridInterval_iff_floor D.scale_pos (v 0) z.re).1 (hz 0)
    · simpa [complexBoxPoint, cellBox, gridCellBox, ownerIndex] using
        (neg_mem_gridInterval_iff_floor D.scale_pos (v 1) z.im).1 (hz 1)
  · intro hz i
    fin_cases i
    · apply (neg_mem_gridInterval_iff_floor D.scale_pos (v 0) z.re).2
      simpa [ownerIndex] using congrFun hz 0
    · apply (neg_mem_gridInterval_iff_floor D.scale_pos (v 1) z.im).2
      simpa [ownerIndex] using congrFun hz 1

/-- Every complex point lies in its floor-based owner cell's closed carrier.

```lean
theorem mem_owner_cell_carrier (D : GridFilling) (z : ℂ) :
    z ∈ (D.cell (D.ownerIndex z)).carrier
``` -/
theorem mem_owner_cell_carrier (D : GridFilling) (z : ℂ) :
    z ∈ (D.cell (D.ownerIndex z)).carrier := by
  rw [D.mem_cell_carrier_iff]
  constructor
  · constructor
    · apply (div_le_iff₀ D.scale_pos).2
      simpa [ownerIndex, mul_comm] using Int.floor_le (D.scale * z.re)
    · apply (le_div_iff₀ D.scale_pos).2
      simpa [ownerIndex, mul_comm] using (Int.lt_floor_add_one (D.scale * z.re)).le
  · constructor
    · apply (div_le_iff₀ D.scale_pos).2
      simpa [ownerIndex, mul_comm] using Int.floor_le (D.scale * z.im)
    · apply (le_div_iff₀ D.scale_pos).2
      simpa [ownerIndex, mul_comm] using (Int.lt_floor_add_one (D.scale * z.im)).le

/-- Every complex point lies in the closure of its owner cell's open interior.

```lean
theorem mem_closure_cellInterior_ownerIndex (D : GridFilling) (z : ℂ) :
    z ∈ closure (D.cellInterior (D.ownerIndex z))
``` -/
theorem mem_closure_cellInterior_ownerIndex (D : GridFilling) (z : ℂ) :
    z ∈ closure (D.cellInterior (D.ownerIndex z)) := by
  have h₀ : (D.ownerIndex z 0 : ℝ) / D.scale <
      ((D.ownerIndex z 0 : ℝ) + 1) / D.scale :=
    (div_lt_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
  have h₁ : (D.ownerIndex z 1 : ℝ) / D.scale <
      ((D.ownerIndex z 1 : ℝ) + 1) / D.scale :=
    (div_lt_div_iff_of_pos_right D.scale_pos).2 (by norm_num)
  rw [cellInterior, Complex.closure_reProdIm, closure_Ioo h₀.ne, closure_Ioo h₁.ne]
  constructor
  · constructor
    · apply (div_le_iff₀ D.scale_pos).2
      simpa [ownerIndex, mul_comm] using Int.floor_le (D.scale * z.re)
    · apply (le_div_iff₀ D.scale_pos).2
      simpa [ownerIndex, mul_comm] using (Int.lt_floor_add_one (D.scale * z.re)).le
  · constructor
    · apply (div_le_iff₀ D.scale_pos).2
      simpa [ownerIndex, mul_comm] using Int.floor_le (D.scale * z.im)
    · apply (le_div_iff₀ D.scale_pos).2
      simpa [ownerIndex, mul_comm] using (Int.lt_floor_add_one (D.scale * z.im)).le

/-- A point in a cell's open interior has that cell as its owner.

```lean
theorem ownerIndex_eq_of_mem_cellInterior (D : GridFilling) {v : GridIndex}
    {z : ℂ} (hz : z ∈ D.cellInterior v) : D.ownerIndex z = v
``` -/
theorem ownerIndex_eq_of_mem_cellInterior (D : GridFilling) {v : GridIndex}
    {z : ℂ} (hz : z ∈ D.cellInterior v) : D.ownerIndex z = v := by
  funext i
  fin_cases i
  · change ⌊D.scale * z.re⌋ = v 0
    apply Int.floor_eq_iff.mpr
    constructor
    · simpa [mul_comm] using ((div_lt_iff₀ D.scale_pos).1 hz.1.1).le
    · simpa [mul_comm] using (lt_div_iff₀ D.scale_pos).1 hz.1.2
  · change ⌊D.scale * z.im⌋ = v 1
    apply Int.floor_eq_iff.mpr
    constructor
    · simpa [mul_comm] using ((div_lt_iff₀ D.scale_pos).1 hz.2.1).le
    · simpa [mul_comm] using (lt_div_iff₀ D.scale_pos).1 hz.2.2

/-- Selected-cell multiplicity of the grid component containing `z`.

Away from the reduced boundary, adjacent cell indicators agree; hence this
floor-based representative is the same multiplicity on the whole component.
The discrete residue/Stokes theorem identifies its complex coercion with the
analytic winding index. -/
noncomputable def cellMultiplicity (D : GridFilling) (z : ℂ) : ℤ :=
  D.cellCoeff (D.ownerIndex z)

/-- Selected-cell multiplicity is zero outside the filling region.

```lean
theorem cellMultiplicity_eq_zero_of_not_mem_region
    (D : GridFilling) {z : ℂ} (hz : z ∉ D.region) :
    D.cellMultiplicity z = 0
``` -/
theorem cellMultiplicity_eq_zero_of_not_mem_region
    (D : GridFilling) {z : ℂ} (hz : z ∉ D.region) :
    D.cellMultiplicity z = 0 := by
  have howner : D.ownerIndex z ∉ D.cells := by
    intro hmem
    apply hz
    rw [region]
    exact Set.mem_iUnion_of_mem (D.ownerIndex z)
      (Set.mem_iUnion_of_mem hmem (D.mem_owner_cell_carrier z))
  simp [cellMultiplicity, cellCoeff, howner]

/-- Multiplicity is one exactly when the floor-based owner cell is selected.

```lean
theorem cellMultiplicity_eq_one_iff (D : GridFilling) (z : ℂ) :
    D.cellMultiplicity z = 1 ↔ D.ownerIndex z ∈ D.cells
``` -/
theorem cellMultiplicity_eq_one_iff (D : GridFilling) (z : ℂ) :
    D.cellMultiplicity z = 1 ↔ D.ownerIndex z ∈ D.cells := by
  simp [cellMultiplicity, cellCoeff]

/-- Selected-cell multiplicity is always zero or one.

```lean
theorem cellMultiplicity_eq_zero_or_one (D : GridFilling) (z : ℂ) :
    D.cellMultiplicity z = 0 ∨ D.cellMultiplicity z = 1
``` -/
theorem cellMultiplicity_eq_zero_or_one (D : GridFilling) (z : ℂ) :
    D.cellMultiplicity z = 0 ∨ D.cellMultiplicity z = 1 := by
  simp only [cellMultiplicity, cellCoeff]
  split_ifs <;> simp

/-- Every point of the compact set has multiplicity one in its selected filling.

```lean
theorem selectedFilling_cellMultiplicity_eq_one_of_mem
    (K : Set ℂ) {r t : ℝ} (ht : 0 < t) (hK : IsCompact K)
    {z : ℂ} (hz : z ∈ K) :
    (selectedFilling K r t ht hK).cellMultiplicity z = 1
``` -/
theorem selectedFilling_cellMultiplicity_eq_one_of_mem
    (K : Set ℂ) {r t : ℝ} (ht : 0 < t) (hK : IsCompact K)
    {z : ℂ} (hz : z ∈ K) :
    (selectedFilling K r t ht hK).cellMultiplicity z = 1 := by
  have hmem : (selectedFilling K r t ht hK).ownerIndex z ∈
      (selectedFilling K r t ht hK).cells := by
    rw [mem_selectedFilling_cells]
    exact ⟨z, (selectedFilling K r t ht hK).mem_owner_cell_carrier z,
      Metric.self_subset_cthickening K hz⟩
  simp [cellMultiplicity, cellCoeff, hmem]

/-- For nonnegative radius, multiplicity is zero outside the closed `(2/t+r)`-thickening.

```lean
theorem selectedFilling_cellMultiplicity_eq_zero_of_not_mem_cthickening
    (K : Set ℂ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) (hK : IsCompact K)
    {z : ℂ} (hz : z ∉ Metric.cthickening (2 / t + r) K) :
    (selectedFilling K r t ht hK).cellMultiplicity z = 0
``` -/
theorem selectedFilling_cellMultiplicity_eq_zero_of_not_mem_cthickening
    (K : Set ℂ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) (hK : IsCompact K)
    {z : ℂ} (hz : z ∉ Metric.cthickening (2 / t + r) K) :
    (selectedFilling K r t ht hK).cellMultiplicity z = 0 := by
  have hnot : (selectedFilling K r t ht hK).ownerIndex z ∉
      (selectedFilling K r t ht hK).cells := by
    intro hv
    apply hz
    exact selectedFilling_cell_carrier_subset_cthickening K hr ht hK hv
      ((selectedFilling K r t ht hK).mem_owner_cell_carrier z)
  simp [cellMultiplicity, cellCoeff, hnot]

/-- A point belongs to the selected half-open prepartition union exactly when its multiplicity is
one.

```lean
theorem complexBoxPoint_mem_cellsPrepartition_iUnion_iff
    (D : GridFilling) (B : BoxIntegral.Box (Fin 2))
    (hB : ∀ v ∈ D.cells, D.cellBox v ≤ B) (z : ℂ) :
    complexBoxPoint z ∈ (D.cellsPrepartition B hB).iUnion ↔
      D.cellMultiplicity z = 1
``` -/
theorem complexBoxPoint_mem_cellsPrepartition_iUnion_iff
    (D : GridFilling) (B : BoxIntegral.Box (Fin 2))
    (hB : ∀ v ∈ D.cells, D.cellBox v ≤ B) (z : ℂ) :
    complexBoxPoint z ∈ (D.cellsPrepartition B hB).iUnion ↔
      D.cellMultiplicity z = 1 := by
  classical
  rw [BoxIntegral.Prepartition.mem_iUnion]
  constructor
  · rintro ⟨I, hI, hzI⟩
    change I ∈ D.cellBoxes at hI
    rw [cellBoxes, Finset.mem_image] at hI
    rcases hI with ⟨v, hv, rfl⟩
    rw [D.cellMultiplicity_eq_one_iff]
    have howner := (D.complexBoxPoint_mem_cellBox_iff v z).1 hzI
    rwa [howner]
  · intro hz
    rw [D.cellMultiplicity_eq_one_iff] at hz
    refine ⟨D.cellBox (D.ownerIndex z), ?_, ?_⟩
    · change D.cellBox (D.ownerIndex z) ∈ D.cellBoxes
      rw [cellBoxes, Finset.mem_image]
      exact ⟨D.ownerIndex z, hz, rfl⟩
    · exact (D.complexBoxPoint_mem_cellBox_iff (D.ownerIndex z) z).2 rfl

/-- On an overlay box, first-filling multiplicity is one exactly when the whole box lies in the
first selected-cell union.

```lean
theorem cellMultiplicity_eq_one_iff_overlayBox_subset_left
    (D E : GridFilling) {I : BoxIntegral.Box (Fin 2)}
    (hI : I ∈ D.overlayPrepartition E) {z : ℂ}
    (hz : complexBoxPoint z ∈ I) :
    D.cellMultiplicity z = 1 ↔
      (I : Set (Fin 2 → ℝ)) ⊆ (D.leftCellPrepartition E).iUnion
``` -/
theorem cellMultiplicity_eq_one_iff_overlayBox_subset_left
    (D E : GridFilling) {I : BoxIntegral.Box (Fin 2)}
    (hI : I ∈ D.overlayPrepartition E) {z : ℂ}
    (hz : complexBoxPoint z ∈ I) :
    D.cellMultiplicity z = 1 ↔
      (I : Set (Fin 2 → ℝ)) ⊆ (D.leftCellPrepartition E).iUnion := by
  rw [← D.complexBoxPoint_mem_cellsPrepartition_iUnion_iff
    (D.commonBoundingBox E)
    (fun v hv ↦ D.cellBox_le_commonBoundingBox_left E hv) z]
  exact (overlayBox_subset_iUnion_iff_mem
    (D.leftCellPrepartition E) (D.overlayPrepartition E)
    (D.overlayHyperplanes_spec E (D.leftCellPrepartition E) (by simp)) hI hz).symm

/-- On an overlay box, second-filling multiplicity is one exactly when the whole box lies in the
second selected-cell union.

```lean
theorem cellMultiplicity_eq_one_iff_overlayBox_subset_right
    (D E : GridFilling) {I : BoxIntegral.Box (Fin 2)}
    (hI : I ∈ D.overlayPrepartition E) {z : ℂ}
    (hz : complexBoxPoint z ∈ I) :
    E.cellMultiplicity z = 1 ↔
      (I : Set (Fin 2 → ℝ)) ⊆ (D.rightCellPrepartition E).iUnion
``` -/
theorem cellMultiplicity_eq_one_iff_overlayBox_subset_right
    (D E : GridFilling) {I : BoxIntegral.Box (Fin 2)}
    (hI : I ∈ D.overlayPrepartition E) {z : ℂ}
    (hz : complexBoxPoint z ∈ I) :
    E.cellMultiplicity z = 1 ↔
      (I : Set (Fin 2 → ℝ)) ⊆ (D.rightCellPrepartition E).iUnion := by
  rw [← E.complexBoxPoint_mem_cellsPrepartition_iUnion_iff
    (D.commonBoundingBox E)
    (fun v hv ↦ D.cellBox_le_commonBoundingBox_right E hv) z]
  exact (overlayBox_subset_iUnion_iff_mem
    (D.rightCellPrepartition E) (D.overlayPrepartition E)
    (D.overlayHyperplanes_spec E (D.rightCellPrepartition E) (by simp)) hI hz).symm

/-- The coefficient of an overlay box is the first multiplicity minus the second at any point of
that box.

```lean
theorem commonOverlay_apply_eq_cellMultiplicity_sub
    (D E : GridFilling) {I : BoxIntegral.Box (Fin 2)}
    (hI : I ∈ D.overlayPrepartition E) {z : ℂ}
    (hz : complexBoxPoint z ∈ I) :
    D.commonOverlay E I = D.cellMultiplicity z - E.cellMultiplicity z
``` -/
theorem commonOverlay_apply_eq_cellMultiplicity_sub
    (D E : GridFilling) {I : BoxIntegral.Box (Fin 2)}
    (hI : I ∈ D.overlayPrepartition E) {z : ℂ}
    (hz : complexBoxPoint z ∈ I) :
    D.commonOverlay E I = D.cellMultiplicity z - E.cellMultiplicity z := by
  classical
  rw [D.commonOverlay_apply E I]
  have hd :
      prepartitionIndicator (D.leftOverlayPrepartition E) I =
        D.cellMultiplicity z := by
    by_cases hsub : (I : Set (Fin 2 → ℝ)) ⊆ (D.leftCellPrepartition E).iUnion
    · rw [(D.cellMultiplicity_eq_one_iff_overlayBox_subset_left E hI hz).2 hsub]
      have hmem : I ∈ D.leftOverlayPrepartition E := by
        rw [D.leftOverlayPrepartition_eq_filter E,
          BoxIntegral.Prepartition.mem_filter]
        exact ⟨hI, hsub⟩
      simp [prepartitionIndicator, hmem]
    · have hnot : I ∉ D.leftOverlayPrepartition E := by
        intro hmem
        rw [D.leftOverlayPrepartition_eq_filter E,
          BoxIntegral.Prepartition.mem_filter] at hmem
        exact hsub hmem.2
      have hindicator : prepartitionIndicator (D.leftOverlayPrepartition E) I = 0 := by
        simp [prepartitionIndicator, hnot]
      rw [hindicator]
      rcases D.cellMultiplicity_eq_zero_or_one z with hzero | hone
      · exact hzero.symm
      · exact (hsub ((D.cellMultiplicity_eq_one_iff_overlayBox_subset_left E hI hz).1 hone)).elim
  have he :
      prepartitionIndicator (D.rightOverlayPrepartition E) I =
        E.cellMultiplicity z := by
    by_cases hsub : (I : Set (Fin 2 → ℝ)) ⊆ (D.rightCellPrepartition E).iUnion
    · rw [(D.cellMultiplicity_eq_one_iff_overlayBox_subset_right E hI hz).2 hsub]
      have hmem : I ∈ D.rightOverlayPrepartition E := by
        rw [D.rightOverlayPrepartition_eq_filter E,
          BoxIntegral.Prepartition.mem_filter]
        exact ⟨hI, hsub⟩
      simp [prepartitionIndicator, hmem]
    · have hnot : I ∉ D.rightOverlayPrepartition E := by
        intro hmem
        rw [D.rightOverlayPrepartition_eq_filter E,
          BoxIntegral.Prepartition.mem_filter] at hmem
        exact hsub hmem.2
      have hindicator : prepartitionIndicator (D.rightOverlayPrepartition E) I = 0 := by
        simp [prepartitionIndicator, hnot]
      rw [hindicator]
      rcases E.cellMultiplicity_eq_zero_or_one z with hzero | hone
      · exact hzero.symm
      · exact (hsub ((D.cellMultiplicity_eq_one_iff_overlayBox_subset_right E hI hz).1 hone)).elim
  rw [hd, he]

/-- Center of a physical grid cell. -/
noncomputable def cellCenter (D : GridFilling) (v : GridIndex) : ℂ :=
  (((v 0 : ℤ) : ℝ) / D.scale + 1 / (2 * D.scale) : ℂ) +
    (((v 1 : ℤ) : ℝ) / D.scale + 1 / (2 * D.scale) : ℂ) * Complex.I

/-- For every point off the reduced trace, the analytic cycle index equals the complex coercion of
its floor-based selected-cell multiplicity. -/
def HasDiscreteResidueFormula (D : GridFilling) : Prop :=
  ∀ z ∉ D.reducedTrace, D.toCycle.index z = (D.cellMultiplicity z : ℂ)

/-- The analytic index of any finite grid filling equals its selected-cell multiplicity away from
the reduced boundary.

```lean
theorem hasDiscreteResidueFormula (D : GridFilling) :
    D.HasDiscreteResidueFormula
``` -/
theorem hasDiscreteResidueFormula (D : GridFilling) :
    D.HasDiscreteResidueFormula := by
  intro z hz
  let v : GridIndex := D.ownerIndex z
  have hcontinuous : ContinuousWithinAt (fun w : ℂ ↦ D.toCycle.index w)
      (D.cellInterior v) z :=
    (D.continuousAt_toCycle_index_of_not_mem_reducedTrace hz).continuousWithinAt
  apply hcontinuous.eq_const_of_mem_closure
    (by simpa [v] using D.mem_closure_cellInterior_ownerIndex z)
  intro w hw
  simpa [cellMultiplicity, v] using
    D.toCycle_index_eq_cellCoeff_of_mem_cellInterior v hw

/-- The analytic winding index is zero outside the selected-cell region.

```lean
theorem index_eq_zero_of_not_mem_region
    (D : GridFilling) {z : ℂ} (hz : z ∉ D.region) :
    D.toCycle.index z = 0
``` -/
theorem index_eq_zero_of_not_mem_region
    (D : GridFilling) {z : ℂ} (hz : z ∉ D.region) :
    D.toCycle.index z = 0 := by
  have hztrace : z ∉ D.reducedTrace := fun h =>
    hz (D.reducedTrace_subset_region h)
  rw [D.hasDiscreteResidueFormula z hztrace,
    D.cellMultiplicity_eq_zero_of_not_mem_region hz]
  simp

/-- Empty grid filling at an arbitrary positive scale. -/
def empty (t : ℝ) (ht : 0 < t) : GridFilling where
  scale := t
  scale_pos := ht
  cells := ∅

/-- An empty positive-scale filling has no selected cells.

```lean
theorem empty_cells (t : ℝ) (ht : 0 < t) : (empty t ht).cells = ∅
``` -/
@[simp]
theorem empty_cells (t : ℝ) (ht : 0 < t) : (empty t ht).cells = ∅ := rfl

/-- An empty positive-scale filling has the zero cycle.

```lean
theorem empty_toCycle (t : ℝ) (ht : 0 < t) :
    (empty t ht).toCycle = 0
``` -/
@[simp]
theorem empty_toCycle (t : ℝ) (ht : 0 < t) :
    (empty t ht).toCycle = 0 := by
  simp [toCycle]

/-- An empty positive-scale filling has no reduced boundary edges.

```lean
theorem empty_boundaryEdges (t : ℝ) (ht : 0 < t) :
    (empty t ht).boundaryEdges = ∅
``` -/
@[simp]
theorem empty_boundaryEdges (t : ℝ) (ht : 0 < t) :
    (empty t ht).boundaryEdges = ∅ := by
  simp [boundaryEdges]

/-- The reduced trace of an empty filling is empty.

```lean
theorem empty_reducedTrace (t : ℝ) (ht : 0 < t) :
    (empty t ht).reducedTrace = ∅
``` -/
@[simp]
theorem empty_reducedTrace (t : ℝ) (ht : 0 < t) :
    (empty t ht).reducedTrace = ∅ := by
  simp [reducedTrace]

/-- The region of an empty filling is empty.

```lean
theorem empty_region (t : ℝ) (ht : 0 < t) :
    (empty t ht).region = ∅
``` -/
@[simp]
theorem empty_region (t : ℝ) (ht : 0 < t) :
    (empty t ht).region = ∅ := by
  simp [region]

/-- Every complete Banach-valued reduced integral of an empty filling is zero.

```lean
theorem empty_reducedIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (t : ℝ) (ht : 0 < t) (f : ℂ → E) :
    (empty t ht).reducedIntegral f = 0
``` -/
@[simp]
theorem empty_reducedIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (t : ℝ) (ht : 0 < t) (f : ℂ → E) :
    (empty t ht).reducedIntegral f = 0 := by
  simp [reducedIntegral]

/-- The reduced trace is contained in `G \ K`, the analytic index is one on `K`, and the analytic
index is zero outside `G`. -/
def IsAdmissibleFor (D : GridFilling) (K G : Set ℂ) : Prop :=
  D.reducedTrace ⊆ G \ K ∧
    (∀ z ∈ K, D.toCycle.index z = 1) ∧
    ∀ z ∉ G, D.toCycle.index z = 0

/-- Admissibility persists when the ambient set is enlarged.

```lean
theorem IsAdmissibleFor.mono_right {D : GridFilling} {K G H : Set ℂ}
    (hD : D.IsAdmissibleFor K G) (hGH : G ⊆ H) : D.IsAdmissibleFor K H
``` -/
theorem IsAdmissibleFor.mono_right {D : GridFilling} {K G H : Set ℂ}
    (hD : D.IsAdmissibleFor K G) (hGH : G ⊆ H) : D.IsAdmissibleFor K H := by
  refine ⟨fun z hz ↦ ⟨hGH (hD.1 hz).1, (hD.1 hz).2⟩, hD.2.1, ?_⟩
  intro z hzH
  exact hD.2.2 z fun hzG ↦ hzH (hGH hzG)

/-- Admissibility for an index-one set implies admissibility for each subset of that set.

```lean
theorem IsAdmissibleFor.mono_left {D : GridFilling} {K L G : Set ℂ}
    (hD : D.IsAdmissibleFor L G) (hKL : K ⊆ L) :
    D.IsAdmissibleFor K G
``` -/
theorem IsAdmissibleFor.mono_left {D : GridFilling} {K L G : Set ℂ}
    (hD : D.IsAdmissibleFor L G) (hKL : K ⊆ L) :
    D.IsAdmissibleFor K G := by
  refine ⟨fun z hz => ⟨(hD.1 hz).1, fun hzK => (hD.1 hz).2 (hKL hzK)⟩,
    fun z hzK => hD.2.1 z (hKL hzK), hD.2.2⟩

/-- A compact set contained in an open planar set admits an admissible finite filling whose whole
cell region remains in the open set.

```lean
theorem exists_isAdmissibleFor_with_region_subset {K G : Set ℂ}
    (hK : IsCompact K) (hG : IsOpen G) (hKG : K ⊆ G) :
    ∃ D : GridFilling, D.IsAdmissibleFor K G ∧ D.region ⊆ G
``` -/
theorem exists_isAdmissibleFor_with_region_subset {K G : Set ℂ}
    (hK : IsCompact K) (hG : IsOpen G) (hKG : K ⊆ G) :
    ∃ D : GridFilling, D.IsAdmissibleFor K G ∧ D.region ⊆ G := by
  obtain ⟨δ, hδ, hδG⟩ := hK.exists_cthickening_subset_open hG hKG
  let r : ℝ := δ / 2
  let t : ℝ := 8 / δ
  have hr : 0 ≤ r := (half_pos hδ).le
  have ht : 0 < t := div_pos (by norm_num) hδ
  have houter : 2 / t + r ≤ δ := by
    dsimp [r, t]
    field_simp [hδ.ne']
    linarith
  let D : GridFilling := selectedFilling K r t ht hK
  have htraceOuter : D.reducedTrace ⊆ Metric.cthickening (2 / t + r) K := by
    simpa [D] using selectedFilling_reducedTrace_subset_cthickening K hr ht hK
  have houterG : Metric.cthickening (2 / t + r) K ⊆ G :=
    (Metric.cthickening_mono houter K).trans hδG
  have htraceG : D.reducedTrace ⊆ G := htraceOuter.trans houterG
  have htraceK : Disjoint D.reducedTrace K := by
    simpa [D] using selectedFilling_reducedTrace_disjoint K ht hK
  refine ⟨D, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro z hz
    exact ⟨htraceG hz, Set.disjoint_left.1 htraceK hz⟩
  · intro z hzK
    have hztrace : z ∉ D.reducedTrace := fun hz ↦
      Set.disjoint_left.1 htraceK hz hzK
    rw [D.hasDiscreteResidueFormula z hztrace]
    simpa [D] using selectedFilling_cellMultiplicity_eq_one_of_mem K ht hK hzK
  · intro z hzG
    have hztrace : z ∉ D.reducedTrace := fun hz ↦ hzG (htraceG hz)
    have hzouter : z ∉ Metric.cthickening (2 / t + r) K :=
      fun hz ↦ hzG (houterG hz)
    rw [D.hasDiscreteResidueFormula z hztrace]
    simpa [D] using
      selectedFilling_cellMultiplicity_eq_zero_of_not_mem_cthickening
        K hr ht hK hzouter
  · exact (selectedFilling_region_subset_cthickening K hr ht hK).trans houterG

/-- Every compact subset of an open planar set admits a finite positively oriented admissible grid
contour.

```lean
theorem exists_isAdmissibleFor {K G : Set ℂ} (hK : IsCompact K)
    (hG : IsOpen G) (hKG : K ⊆ G) : ∃ D : GridFilling, D.IsAdmissibleFor K G
``` -/
theorem exists_isAdmissibleFor {K G : Set ℂ} (hK : IsCompact K)
    (hG : IsOpen G) (hKG : K ⊆ G) : ∃ D : GridFilling, D.IsAdmissibleFor K G := by
  obtain ⟨D, hD, -⟩ := exists_isAdmissibleFor_with_region_subset hK hG hKG
  exact ⟨D, hD⟩

/-- Nested admissible grids for the classical multiplicativity argument.  The
outer grid has index one on the entire inner grid region and its reduced
trace is strictly outside that region.  By `IsAdmissibleFor.mono_left` it is
also admissible for the original compact set.

```lean
theorem exists_nested_isAdmissibleFor {K G : Set ℂ}
    (hK : IsCompact K) (hG : IsOpen G) (hKG : K ⊆ G) :
    ∃ D E : GridFilling,
      D.IsAdmissibleFor K G ∧ E.IsAdmissibleFor (K ∪ D.region) G
``` -/
theorem exists_nested_isAdmissibleFor {K G : Set ℂ}
    (hK : IsCompact K) (hG : IsOpen G) (hKG : K ⊆ G) :
    ∃ D E : GridFilling,
      D.IsAdmissibleFor K G ∧ E.IsAdmissibleFor (K ∪ D.region) G := by
  obtain ⟨D, hD, hDG⟩ :=
    exists_isAdmissibleFor_with_region_subset hK hG hKG
  have hcompact : IsCompact (K ∪ D.region) := hK.union D.isCompact_region
  have hsubset : K ∪ D.region ⊆ G := Set.union_subset hKG hDG
  obtain ⟨E, hE⟩ := exists_isAdmissibleFor hcompact hG hsubset
  exact ⟨D, E, hD, hE⟩

/-- Pointwise support of the signed cell-multiplicity difference of two grid
fillings.  Unlike the support of their free rectangle presentations, this set
is unchanged when either filling is subdivided without changing its region. -/
noncomputable def multiplicityDifferenceSupport (D E : GridFilling) : Set ℂ :=
  Function.support fun z ↦ D.cellMultiplicity z - E.cellMultiplicity z

/-- Membership in the difference support means exactly that the two cell multiplicities differ.

```lean
theorem mem_multiplicityDifferenceSupport_iff (D E : GridFilling) (z : ℂ) :
    z ∈ D.multiplicityDifferenceSupport E ↔
      D.cellMultiplicity z ≠ E.cellMultiplicity z
``` -/
theorem mem_multiplicityDifferenceSupport_iff (D E : GridFilling) (z : ℂ) :
    z ∈ D.multiplicityDifferenceSupport E ↔
      D.cellMultiplicity z ≠ E.cellMultiplicity z := by
  simp only [multiplicityDifferenceSupport, Function.mem_support]
  exact sub_ne_zero

/-- The multiplicity-difference support is symmetric in the two fillings.

```lean
theorem multiplicityDifferenceSupport_comm (D E : GridFilling) :
    D.multiplicityDifferenceSupport E = E.multiplicityDifferenceSupport D
``` -/
theorem multiplicityDifferenceSupport_comm (D E : GridFilling) :
    D.multiplicityDifferenceSupport E = E.multiplicityDifferenceSupport D := by
  ext z
  simp [mem_multiplicityDifferenceSupport_iff, ne_comm]

/-- Each closed rectangle with nonzero overlay coefficient lies in the closure of the
multiplicity-difference support.

```lean
theorem commonOverlay_rectangle_carrier_subset (D E : GridFilling)
    {I : BoxIntegral.Box (Fin 2)} (hI : I ∈ (D.commonOverlay E).support) :
    (rectangleOfBox I).carrier ⊆ closure (D.multiplicityDifferenceSupport E)
``` -/
theorem commonOverlay_rectangle_carrier_subset (D E : GridFilling)
    {I : BoxIntegral.Box (Fin 2)} (hI : I ∈ (D.commonOverlay E).support) :
    (rectangleOfBox I).carrier ⊆ closure (D.multiplicityDifferenceSupport E) := by
  rw [← closure_rectangleOfBoxInterior]
  apply closure_mono
  intro z hz
  rw [D.mem_multiplicityDifferenceSupport_iff E z]
  have hglobal := D.mem_overlayPrepartition_of_mem_commonOverlay_support E hI
  have hpoint := complexBoxPoint_mem_of_mem_rectangleOfBoxInterior I hz
  intro hmult
  apply Finsupp.mem_support_iff.mp hI
  rw [D.commonOverlay_apply_eq_cellMultiplicity_sub E hglobal hpoint,
    hmult, sub_self]

/-- The difference cycle is filled by signed rectangles with closed carriers in the closure of the
multiplicity-difference support.

```lean
theorem commonOverlay_fillingSupportedIn (D E : GridFilling) :
    (D.commonOverlay E).toCycle.FillingSupportedIn
      (closure (D.multiplicityDifferenceSupport E))
``` -/
theorem commonOverlay_fillingSupportedIn (D E : GridFilling) :
    (D.commonOverlay E).toCycle.FillingSupportedIn
      (closure (D.multiplicityDifferenceSupport E)) := by
  intro r hr
  rw [BoxOverlayChain.toCycle, Finsupp.support_mapDomain_embedding] at hr
  rcases Finset.mem_map.1 hr with ⟨I, hI, rfl⟩
  exact D.commonOverlay_rectangle_carrier_subset E hI

/-- The closure of the pointwise cell-multiplicity difference support is contained in `G \ K`. -/
def HaveCommonFillingAwayFrom (D E : GridFilling) (K G : Set ℂ) : Prop :=
  closure (D.multiplicityDifferenceSupport E) ⊆ G \ K

/-- Off both reduced traces, closure membership in the multiplicity-difference support implies
support membership.

```lean
theorem mem_multiplicityDifferenceSupport_of_mem_closure_of_not_mem_reducedTrace
    (D E : GridFilling) {z : ℂ}
    (hz : z ∈ closure (D.multiplicityDifferenceSupport E))
    (hzD : z ∉ D.reducedTrace) (hzE : z ∉ E.reducedTrace) :
    z ∈ D.multiplicityDifferenceSupport E
``` -/
theorem mem_multiplicityDifferenceSupport_of_mem_closure_of_not_mem_reducedTrace
    (D E : GridFilling) {z : ℂ}
    (hz : z ∈ closure (D.multiplicityDifferenceSupport E))
    (hzD : z ∉ D.reducedTrace) (hzE : z ∉ E.reducedTrace) :
    z ∈ D.multiplicityDifferenceSupport E := by
  rw [D.mem_multiplicityDifferenceSupport_iff E z]
  by_contra hmult
  have hdiffz : D.toCycle.index z - E.toCycle.index z = 0 := by
    rw [D.hasDiscreteResidueFormula z hzD, E.hasDiscreteResidueFormula z hzE,
      hmult, sub_self]
  have hcont : ContinuousAt (fun w ↦ D.toCycle.index w - E.toCycle.index w) z :=
    (D.continuousAt_toCycle_index_of_not_mem_reducedTrace hzD).sub
      (E.continuousAt_toCycle_index_of_not_mem_reducedTrace hzE)
  have hsmall : ∀ᶠ w in 𝓝 z,
      dist (D.toCycle.index w - E.toCycle.index w) 0 < 1 := by
    rw [ContinuousAt, hdiffz] at hcont
    filter_upwards [hcont (Metric.ball_mem_nhds 0 zero_lt_one)] with w hw
    change D.toCycle.index w - E.toCycle.index w ∈ Metric.ball 0 1 at hw
    exact Metric.mem_ball.mp hw
  have hnotD : ∀ᶠ w in 𝓝 z, w ∉ D.reducedTrace :=
    D.isClosed_reducedTrace.isOpen_compl.mem_nhds hzD
  have hnotE : ∀ᶠ w in 𝓝 z, w ∉ E.reducedTrace :=
    E.isClosed_reducedTrace.isOpen_compl.mem_nhds hzE
  have hfreq : ∃ᶠ w in 𝓝 z, w ∈ D.multiplicityDifferenceSupport E :=
    mem_closure_iff_frequently.1 hz
  rcases (hfreq.and_eventually (hsmall.and (hnotD.and hnotE))).exists with
    ⟨w, hwSupp, hwSmall, hwD, hwE⟩
  rw [D.hasDiscreteResidueFormula w hwD, E.hasDiscreteResidueFormula w hwE] at hwSmall
  have hwne := (D.mem_multiplicityDifferenceSupport_iff E w).1 hwSupp
  rcases D.cellMultiplicity_eq_zero_or_one w with hD₀ | hD₁ <;>
    rcases E.cellMultiplicity_eq_zero_or_one w with hE₀ | hE₁ <;>
    simp_all [dist_eq_norm]

/-- Only points of the two reduced traces can be added by closing the multiplicity-difference
support.

```lean
theorem closure_multiplicityDifferenceSupport_subset (D E : GridFilling) :
    closure (D.multiplicityDifferenceSupport E) ⊆
      (D.multiplicityDifferenceSupport E ∪ D.reducedTrace) ∪ E.reducedTrace
``` -/
theorem closure_multiplicityDifferenceSupport_subset (D E : GridFilling) :
    closure (D.multiplicityDifferenceSupport E) ⊆
      (D.multiplicityDifferenceSupport E ∪ D.reducedTrace) ∪ E.reducedTrace := by
  intro z hz
  by_cases hzD : z ∈ D.reducedTrace
  · exact Or.inl (Or.inr hzD)
  by_cases hzE : z ∈ E.reducedTrace
  · exact Or.inr hzE
  exact Or.inl (Or.inl
    (D.mem_multiplicityDifferenceSupport_of_mem_closure_of_not_mem_reducedTrace
      E hz hzD hzE))

/-- Any two admissible grid fillings have subdivision-invariant comparison
support inside the collar domain.

```lean
theorem haveCommonFillingAwayFrom_of_isAdmissibleFor
    {D E : GridFilling} {K G : Set ℂ}
    (hD : D.IsAdmissibleFor K G) (hE : E.IsAdmissibleFor K G) :
    D.HaveCommonFillingAwayFrom E K G
``` -/
theorem haveCommonFillingAwayFrom_of_isAdmissibleFor
    {D E : GridFilling} {K G : Set ℂ}
    (hD : D.IsAdmissibleFor K G) (hE : E.IsAdmissibleFor K G) :
    D.HaveCommonFillingAwayFrom E K G := by
  apply (D.closure_multiplicityDifferenceSupport_subset E).trans
  rintro z ((hz | hz) | hz)
  · rw [D.mem_multiplicityDifferenceSupport_iff E z] at hz
    constructor
    · by_contra hzG
      have hzDtrace : z ∉ D.reducedTrace := fun h ↦ hzG (hD.1 h).1
      have hzEtrace : z ∉ E.reducedTrace := fun h ↦ hzG (hE.1 h).1
      have hDz := D.hasDiscreteResidueFormula z hzDtrace
      have hEz := E.hasDiscreteResidueFormula z hzEtrace
      rw [hD.2.2 z hzG] at hDz
      rw [hE.2.2 z hzG] at hEz
      exact hz (by exact_mod_cast hDz.symm.trans hEz)
    · intro hzK
      have hzDtrace : z ∉ D.reducedTrace := fun h ↦ (hD.1 h).2 hzK
      have hzEtrace : z ∉ E.reducedTrace := fun h ↦ (hE.1 h).2 hzK
      have hDz := D.hasDiscreteResidueFormula z hzDtrace
      have hEz := E.hasDiscreteResidueFormula z hzEtrace
      rw [hD.2.1 z hzK] at hDz
      rw [hE.2.1 z hzK] at hEz
      exact hz (by exact_mod_cast hDz.symm.trans hEz)
  · exact hD.1 hz
  · exact hE.1 hz

/-- Closed set on which a scalar integrand must be retained while extending
it globally for the common-overlay argument. -/
noncomputable def comparisonCarrier (D E : GridFilling) : Set ℂ :=
  closure (D.multiplicityDifferenceSupport E) ∪
    D.reducedTrace ∪ E.reducedTrace

/-- The comparison carrier of two fillings is closed.

```lean
theorem isClosed_comparisonCarrier (D E : GridFilling) :
    IsClosed (D.comparisonCarrier E)
``` -/
theorem isClosed_comparisonCarrier (D E : GridFilling) :
    IsClosed (D.comparisonCarrier E) :=
  (isClosed_closure.union D.isClosed_reducedTrace).union E.isClosed_reducedTrace

/-- If both traces and their common-filling support lie in `G \ K`, so does the comparison carrier.

```lean
theorem comparisonCarrier_subset {D E : GridFilling} {K G : Set ℂ}
    (hD : D.reducedTrace ⊆ G \ K) (hE : E.reducedTrace ⊆ G \ K)
    (hDE : D.HaveCommonFillingAwayFrom E K G) :
    D.comparisonCarrier E ⊆ G \ K
``` -/
theorem comparisonCarrier_subset {D E : GridFilling} {K G : Set ℂ}
    (hD : D.reducedTrace ⊆ G \ K) (hE : E.reducedTrace ⊆ G \ K)
    (hDE : D.HaveCommonFillingAwayFrom E K G) :
    D.comparisonCarrier E ⊆ G \ K := by
  intro z hz
  change z ∈ (closure (D.multiplicityDifferenceSupport E) ∪
    D.reducedTrace) ∪ E.reducedTrace at hz
  rcases hz with ((hz | hz) | hz)
  · exact hDE hz
  · exact hD hz
  · exact hE hz

/-- A scalar function continuous on a containing set extends globally and agrees on the closed
comparison carrier.

```lean
theorem exists_continuous_extension_on_comparisonCarrier
    {D E : GridFilling} {U : Set ℂ} {f : ℂ → ℂ}
    (hf : ContinuousOn f U) (hsub : D.comparisonCarrier E ⊆ U) :
    ∃ g : ℂ → ℂ, Continuous g ∧ Set.EqOn g f (D.comparisonCarrier E)
``` -/
theorem exists_continuous_extension_on_comparisonCarrier
    {D E : GridFilling} {U : Set ℂ} {f : ℂ → ℂ}
    (hf : ContinuousOn f U) (hsub : D.comparisonCarrier E ⊆ U) :
    ∃ g : ℂ → ℂ, Continuous g ∧ Set.EqOn g f (D.comparisonCarrier E) := by
  let fc : C(D.comparisonCarrier E, ℂ) :=
    ⟨fun z ↦ f z, continuousOn_iff_continuous_domRestrict.mp (hf.mono hsub)⟩
  obtain ⟨g, hg⟩ := fc.exists_restrict_eq (D.isClosed_comparisonCarrier E)
  refine ⟨g, g.continuous, ?_⟩
  intro z hz
  have hgz := congrArg (fun F ↦ F ⟨z, hz⟩) hg
  exact hgz

/-- The scalar contour integrals agree under the common-filling condition and complex
differentiability on `G \ K`.

```lean
theorem integral_eq_of_haveCommonFillingAwayFrom_complex
    {D E : GridFilling} {K G : Set ℂ} {f : ℂ → ℂ}
    (hD : D.reducedTrace ⊆ G \ K) (hE : E.reducedTrace ⊆ G \ K)
    (hDE : D.HaveCommonFillingAwayFrom E K G)
    (hf : DifferentiableOn ℂ f (G \ K)) :
    D.toCycle.integral f = E.toCycle.integral f
``` -/
theorem integral_eq_of_haveCommonFillingAwayFrom_complex
    {D E : GridFilling} {K G : Set ℂ} {f : ℂ → ℂ}
    (hD : D.reducedTrace ⊆ G \ K) (hE : E.reducedTrace ⊆ G \ K)
    (hDE : D.HaveCommonFillingAwayFrom E K G)
    (hf : DifferentiableOn ℂ f (G \ K)) :
    D.toCycle.integral f = E.toCycle.integral f := by
  obtain ⟨g, hg, hgf⟩ := exists_continuous_extension_on_comparisonCarrier
    hf.continuousOn (comparisonCarrier_subset hD hE hDE)
  have hDf : D.toCycle.integral f = D.toCycle.integral g := by
    rw [D.toCycle_integral_eq_reducedIntegral,
      D.toCycle_integral_eq_reducedIntegral]
    apply D.reducedIntegral_congr
    exact fun z hz ↦ (hgf (Or.inl (Or.inr hz))).symm
  have hEf : E.toCycle.integral f = E.toCycle.integral g := by
    rw [E.toCycle_integral_eq_reducedIntegral,
      E.toCycle_integral_eq_reducedIntegral]
    apply E.reducedIntegral_congr
    exact fun z hz ↦ (hgf (Or.inr hz)).symm
  have hoverU : (D.commonOverlay E).toCycle.FillingSupportedIn (G \ K) :=
    fun r hr ↦ (D.commonOverlay_fillingSupportedIn E r hr).trans hDE
  have hoverC :
      (D.commonOverlay E).toCycle.FillingSupportedIn (D.comparisonCarrier E) :=
    fun r hr ↦ (D.commonOverlay_fillingSupportedIn E r hr).trans
      (subset_union_left.trans subset_union_left)
  have hoverZero : (D.commonOverlay E).toCycle.integral f = 0 :=
    RectilinearCycle.integral_eq_zero_of_fillingSupportedIn hoverU hf
  have hoverEq : (D.commonOverlay E).toCycle.integral g =
      (D.commonOverlay E).toCycle.integral f :=
    RectilinearCycle.integral_congr_of_fillingSupportedIn hoverC hgf
  have hdiff : D.toCycle.integral g - E.toCycle.integral g = 0 := by
    rw [← D.commonOverlay_toCycle_integral E g hg, hoverEq, hoverZero]
  exact hDf.trans ((sub_eq_zero.mp hdiff).trans hEf.symm)

/-- Finite-overlay/common-refinement theorem.  Multiplicity-difference
support inside `G \ K`, together with the two reduced traces there, implies
equality of Banach-valued contour integrals for every function complex
differentiable on `G \ K`.

```lean
theorem integral_eq_of_haveCommonFillingAwayFrom {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {D E : GridFilling} {K G : Set ℂ} {f : ℂ → F}
    (hD : D.reducedTrace ⊆ G \ K) (hE : E.reducedTrace ⊆ G \ K)
    (hDE : D.HaveCommonFillingAwayFrom E K G)
    (hf : DifferentiableOn ℂ f (G \ K)) :
    D.toCycle.integral f = E.toCycle.integral f
``` -/
theorem integral_eq_of_haveCommonFillingAwayFrom {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {D E : GridFilling} {K G : Set ℂ} {f : ℂ → F}
    (hD : D.reducedTrace ⊆ G \ K) (hE : E.reducedTrace ⊆ G \ K)
    (hDE : D.HaveCommonFillingAwayFrom E K G)
    (hf : DifferentiableOn ℂ f (G \ K)) :
    D.toCycle.integral f = E.toCycle.integral f := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro L
  let fL : ℂ → ℂ := fun z ↦ L (f z)
  have hfL : DifferentiableOn ℂ fL (G \ K) := by
    intro z hz
    exact L.differentiableAt.comp_differentiableWithinAt z (hf z hz)
  have hDL : L (D.toCycle.integral f) = D.toCycle.integral fL := by
    rw [D.toCycle_integral_eq_reducedIntegral,
      D.toCycle_integral_eq_reducedIntegral]
    exact (D.reducedIntegral_comp_comm L f hD hf.continuousOn).symm
  have hEL : L (E.toCycle.integral f) = E.toCycle.integral fL := by
    rw [E.toCycle_integral_eq_reducedIntegral,
      E.toCycle_integral_eq_reducedIntegral]
    exact (E.reducedIntegral_comp_comm L f hE hf.continuousOn).symm
  rw [hDL, hEL]
  exact integral_eq_of_haveCommonFillingAwayFrom_complex hD hE hDE hfL

/-- Admissible fillings for the same `K` and `G` have equal contour integrals of every complete
Banach-valued function complex differentiable on `G \ K`.

```lean
theorem integral_eq_of_isAdmissibleFor {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {D E : GridFilling} {K G : Set ℂ} {f : ℂ → F}
    (hD : D.IsAdmissibleFor K G) (hE : E.IsAdmissibleFor K G)
    (hf : DifferentiableOn ℂ f (G \ K)) :
    D.toCycle.integral f = E.toCycle.integral f
``` -/
theorem integral_eq_of_isAdmissibleFor {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {D E : GridFilling} {K G : Set ℂ} {f : ℂ → F}
    (hD : D.IsAdmissibleFor K G) (hE : E.IsAdmissibleFor K G)
    (hf : DifferentiableOn ℂ f (G \ K)) :
    D.toCycle.integral f = E.toCycle.integral f :=
  integral_eq_of_haveCommonFillingAwayFrom hD.1 hE.1
    (haveCommonFillingAwayFrom_of_isAdmissibleFor hD hE) hf

/-- The common-filling-away-from condition is symmetric in the two fillings.

```lean
theorem haveCommonFillingAwayFrom_comm (D E : GridFilling) (K G : Set ℂ) :
    D.HaveCommonFillingAwayFrom E K G ↔ E.HaveCommonFillingAwayFrom D K G
``` -/
theorem haveCommonFillingAwayFrom_comm (D E : GridFilling) (K G : Set ℂ) :
    D.HaveCommonFillingAwayFrom E K G ↔ E.HaveCommonFillingAwayFrom D K G := by
  rw [HaveCommonFillingAwayFrom, HaveCommonFillingAwayFrom,
    multiplicityDifferenceSupport_comm]

/-- A filling has the common-filling-away-from condition with itself for arbitrary sets.

```lean
theorem haveCommonFillingAwayFrom_self (D : GridFilling) (K G : Set ℂ) :
    D.HaveCommonFillingAwayFrom D K G
``` -/
theorem haveCommonFillingAwayFrom_self (D : GridFilling) (K G : Set ℂ) :
    D.HaveCommonFillingAwayFrom D K G := by
  simp [HaveCommonFillingAwayFrom, multiplicityDifferenceSupport]

/-- Under the common-filling condition, the multiplicities agree outside `G \ K`.

```lean
theorem cellMultiplicity_eq_of_haveCommonFillingAwayFrom
    {D E : GridFilling} {K G : Set ℂ} (hDE : D.HaveCommonFillingAwayFrom E K G)
    {z : ℂ} (hz : z ∉ G \ K) : D.cellMultiplicity z = E.cellMultiplicity z
``` -/
theorem cellMultiplicity_eq_of_haveCommonFillingAwayFrom
    {D E : GridFilling} {K G : Set ℂ} (hDE : D.HaveCommonFillingAwayFrom E K G)
    {z : ℂ} (hz : z ∉ G \ K) : D.cellMultiplicity z = E.cellMultiplicity z := by
  by_contra hne
  apply hz
  apply hDE
  exact subset_closure ((D.mem_multiplicityDifferenceSupport_iff E z).2 hne)

/-- Discrete-Stokes bridge supplied by the subdivision-invariant common
filling condition: the two analytic indices agree away from the comparison
region, whenever the point is off both reduced boundaries.

```lean
theorem index_eq_of_haveCommonFillingAwayFrom
    {D E : GridFilling} {K G : Set ℂ} (hDE : D.HaveCommonFillingAwayFrom E K G)
    {z : ℂ} (hz : z ∉ G \ K) (hzD : z ∉ D.reducedTrace)
    (hzE : z ∉ E.reducedTrace) : D.toCycle.index z = E.toCycle.index z
``` -/
theorem index_eq_of_haveCommonFillingAwayFrom
    {D E : GridFilling} {K G : Set ℂ} (hDE : D.HaveCommonFillingAwayFrom E K G)
    {z : ℂ} (hz : z ∉ G \ K) (hzD : z ∉ D.reducedTrace)
    (hzE : z ∉ E.reducedTrace) : D.toCycle.index z = E.toCycle.index z := by
  rw [D.hasDiscreteResidueFormula z hzD, E.hasDiscreteResidueFormula z hzE]
  exact_mod_cast cellMultiplicity_eq_of_haveCommonFillingAwayFrom hDE hz

/-- For admissible fillings, the trace hypotheses in the discrete-Stokes
bridge follow automatically outside `G \ K`.

```lean
theorem index_eq_of_haveCommonFillingAwayFrom_of_isAdmissibleFor
    {D E : GridFilling} {K G : Set ℂ} (hD : D.IsAdmissibleFor K G)
    (hE : E.IsAdmissibleFor K G) (hDE : D.HaveCommonFillingAwayFrom E K G)
    {z : ℂ} (hz : z ∉ G \ K) : D.toCycle.index z = E.toCycle.index z
``` -/
theorem index_eq_of_haveCommonFillingAwayFrom_of_isAdmissibleFor
    {D E : GridFilling} {K G : Set ℂ} (hD : D.IsAdmissibleFor K G)
    (hE : E.IsAdmissibleFor K G) (hDE : D.HaveCommonFillingAwayFrom E K G)
    {z : ℂ} (hz : z ∉ G \ K) : D.toCycle.index z = E.toCycle.index z := by
  apply index_eq_of_haveCommonFillingAwayFrom hDE hz
  · exact fun hzD ↦ hz (hD.1 hzD)
  · exact fun hzE ↦ hz (hE.1 hzE)

/-- The empty positive-scale filling is admissible for the empty index-one set inside any ambient
set.

```lean
theorem empty_isAdmissibleFor_empty (t : ℝ) (ht : 0 < t) (G : Set ℂ) :
    (empty t ht).IsAdmissibleFor ∅ G
``` -/
theorem empty_isAdmissibleFor_empty (t : ℝ) (ht : 0 < t) (G : Set ℂ) :
    (empty t ht).IsAdmissibleFor ∅ G := by
  simp [IsAdmissibleFor]

end GridFilling
