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

A grid index is a pair of integers. At positive scale `t`, its physical vertex is `(v₀/t, v₁/t)`
and each cell has side length `1/t`. A finite filling is a positive scale and a finite set of
selected cells, possibly empty. Unrestricted vertex formulas use total real division, including
`x/0 = 0`; nondegenerate fillings and half-open boxes use positive scale.

Horizontal edges point right and vertical edges point up. Horizontal boundary coefficients are
the selected-cell indicator above minus that below; vertical coefficients are the indicator on
the left minus that on the right. Internal edges cancel. The associated cycle is the sum of
counterclockwise cell boundaries. Its reduced trace is the finite union of edges with nonzero
coefficients. Integer-weighted edge integration uses the stated complete complex normed target
spaces and their norms.

Off the reduced trace, the analytic winding index equals the zero-or-one multiplicity of the
floor-based owner cell. Compact `K` contained in open `G` admits a finite filling with reduced
trace in `G \ K`, index one on `K`, index zero outside `G`, and whole region in `G`. Empty `K`
admits an empty filling.

Two positive scales may be unrelated. A finite signed rectangular overlay compares their cell
multiplicities. If the closure of their multiplicity-difference support and both reduced traces
lie in `G \ K`, then every complex-differentiable complete Banach-valued integrand on `G \ K`
has equal integrals over the two cycles.

## References

John B. Conway, *A Course in Functional Analysis*, second edition, Graduate Texts in Mathematics
96, Springer, 1990, Chapter VII §4, 4.4, p. 201, gives the admissible-contour step for
Riesz calculus. The construction here realizes that step with finite integer square grids,
compact-set thickenings, cancellation of oriented edges, and common rectangular refinements. Its
integration and comparison proofs use Mathlib's box-additive boundary integrals, rectangle
Cauchy–Goursat theory, Tietze extension, and separating continuous linear functionals. The scope
is finite rectilinear grids; no construction of arbitrary smooth, simple, disjoint, or
rectifiable contour families is asserted.
-/

@[expose] public section


open Filter Set
open scoped Topology

/-- **Integer indices for a planar square grid.** A grid index is a function `v:Fin 2→ℤ`,
written `(v₀,v₁)`. It records integer coordinates; no scale or selected-cell condition is
part of the index. -/
abbrev GridIndex := Fin 2 → ℤ

namespace GridIndex

/-- **Forward lattice step in one coordinate.** For `v:ℤ²` and `i∈Fin 2`, `succ_i(v)` has
coordinate `v_i+1` at `i` and agrees with `v` at the other coordinate. -/
def succ (v : GridIndex) (i : Fin 2) : GridIndex :=
  Function.update v i (v i + 1)

/-- **Backward lattice step in one coordinate.** For `v:ℤ²` and `i∈Fin 2`, `pred_i(v)` has
coordinate `v_i-1` at `i` and agrees with `v` elsewhere. -/
def pred (v : GridIndex) (i : Fin 2) : GridIndex :=
  Function.update v i (v i - 1)

/-- **Coordinate increment under a forward lattice step.** For `v:ℤ²` and `i∈Fin 2`,
`(succ_i(v))_i=v_i+1`. -/
@[simp]
theorem succ_apply_same (v : GridIndex) (i : Fin 2) : v.succ i i = v i + 1 := by
  simp [succ]

/-- **Coordinate decrement under a backward lattice step.** For `v:ℤ²` and `i∈Fin 2`,
`(pred_i(v))_i=v_i-1`. -/
@[simp]
theorem pred_apply_same (v : GridIndex) (i : Fin 2) : v.pred i i = v i - 1 := by
  simp [pred]

/-- **Other coordinates are fixed by a forward lattice step.** For `v:ℤ²` and distinct
`i,j∈Fin 2`, `(succ_i(v))_j=v_j`. -/
@[simp]
theorem succ_apply_of_ne (v : GridIndex) {i j : Fin 2} (h : j ≠ i) :
    v.succ i j = v j := by
  simp [succ, h]

/-- **Other coordinates are fixed by a backward lattice step.** For `v:ℤ²` and distinct
`i,j∈Fin 2`, `(pred_i(v))_j=v_j`. -/
@[simp]
theorem pred_apply_of_ne (v : GridIndex) {i j : Fin 2} (h : j ≠ i) :
    v.pred i j = v j := by
  simp [pred, h]

/-- **Forward step reverses a backward lattice step.** For `v:ℤ²` and `i∈Fin 2`,
`succ_i(pred_i(v))=v`. -/
@[simp]
theorem pred_succ (v : GridIndex) (i : Fin 2) : (v.pred i).succ i = v := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [succ_apply_of_ne, pred_apply_of_ne, h]

/-- **Backward step reverses a forward lattice step.** For `v:ℤ²` and `i∈Fin 2`,
`pred_i(succ_i(v))=v`. -/
@[simp]
theorem succ_pred (v : GridIndex) (i : Fin 2) : (v.succ i).pred i = v := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [succ_apply_of_ne, pred_apply_of_ne, h]

/-- **Forward lattice equality and its backward inverse.** For `v,w:ℤ²` and `i∈Fin 2`,
`succ_i(v)=w` if and only if `v=pred_i(w)`. -/
theorem succ_eq_iff_eq_pred (v w : GridIndex) (i : Fin 2) :
    v.succ i = w ↔ v = w.pred i := by
  constructor
  · intro h
    simpa using congrArg (fun u : GridIndex ↦ u.pred i) h
  · rintro rfl
    exact pred_succ w i

/-- **Backward lattice equality and its forward inverse.** For `v,w:ℤ²` and `i∈Fin 2`,
`pred_i(v)=w` if and only if `v=succ_i(w)`. -/
theorem pred_eq_iff_eq_succ (v w : GridIndex) (i : Fin 2) :
    v.pred i = w ↔ v = w.succ i := by
  constructor
  · intro h
    simpa using congrArg (fun u : GridIndex ↦ u.succ i) h
  · rintro rfl
    exact succ_pred w i

end GridIndex

/-- **Oriented horizontal and vertical lattice edges.** A grid edge consists of an integer
base point `v∈ℤ²` and either a horizontal or vertical direction. Horizontal edges point
right; vertical edges point up. Physical endpoints are obtained after choosing a scale. -/
inductive GridEdge where
  | horizontal (base : GridIndex)
  | vertical (base : GridIndex)
deriving DecidableEq

/-- **A finite positive-scale square-grid filling.** A filling consists of a real scale `t>0`
and a finite set `C⊆ℤ²` of selected cells. The cell side length is `1/t`; the selected set
may be empty. -/
structure GridFilling where
  scale : ℝ
  scale_pos : 0 < scale
  cells : Finset GridIndex

/-- **Physical vertex of a scaled integer grid.** For any real `t` and `v∈ℤ²`, `p_t(v)=v₀/t+i
v₁/t`. Division is total, so `p_0(v)=0`; this definition alone does not require a positive
scale. -/
noncomputable def gridPoint (t : ℝ) (v : GridIndex) : ℂ :=
  (((v 0 : ℤ) : ℝ) / t : ℂ) +
    (((v 1 : ℤ) : ℝ) / t : ℂ) * Complex.I

/-- **Closed cell between diagonal scaled grid vertices.** For `t∈ℝ` and `v∈ℤ²`, the cell is
the axis-parallel closed rectangle with diagonal endpoints `p_t(v)` and `p_t(v+(1,1))`,
where `p_t(v)=v₀/t+i v₁/t`. At `t=0` it is degenerate; for `t>0` it is a square of side
`1/t`. -/
noncomputable def gridCell (t : ℝ) (v : GridIndex) : RectilinearRectangle where
  first := gridPoint t v
  second := gridPoint t (fun i => v i + 1)

/-- **Lattice cells meeting a planar set.** For `t∈ℝ` and `S⊆ℂ`, the selected indices are
`{v∈ℤ² | carrier(gridCell t v)∩S≠∅}`. This set-valued definition requires neither
boundedness of `S` nor positivity of `t`. -/
noncomputable def gridCellsMeeting (t : ℝ) (S : Set ℂ) : Set GridIndex :=
  {v | ((gridCell t v).carrier ∩ S).Nonempty}

/-- **Half-open box for a positive-scale grid cell.** For `t>0` and `v∈ℤ²`, the box in
sign-reversed coordinates is the product of intervals `(-(v_i+1)/t,-v_i/t]`, `i=0,1`.
Positivity makes both intervals nondegenerate. -/
noncomputable def gridCellBox (t : ℝ) (ht : 0 < t) (v : GridIndex) :
    BoxIntegral.Box (Fin 2) where
  lower i := -(((v i : ℝ) + 1) / t)
  upper i := -((v i : ℝ) / t)
  lower_lt_upper i := neg_lt_neg
    ((div_lt_div_iff_of_pos_right ht).2 (by norm_num))

/-- **Closed complex rectangle associated with a real box.** Let `I=(l₀,u₀]×(l₁,u₁]` with
`l_i<u_i`. Its associated complex rectangle has real interval `[-u₀,-l₀]` and imaginary
interval `[-u₁,-l₁]`; both coordinates are sign-reversed. -/
noncomputable def rectangleOfBox (I : BoxIntegral.Box (Fin 2)) : RectilinearRectangle :=
  RectilinearRectangle.ofBounds (-I.upper 0) (-I.lower 0) (-I.upper 1) (-I.lower 1)

/-- **Open interior of the rectangle associated with a box.** For `I=(l₀,u₀]×(l₁,u₁]`,
`l_i<u_i`, this is `{z∈ℂ | -u₀<Re z<-l₀ and -u₁<Im z<-l₁}`. -/
noncomputable def rectangleOfBoxInterior (I : BoxIntegral.Box (Fin 2)) : Set ℂ :=
  Ioo (-I.upper 0) (-I.lower 0) ×ℂ
    Ioo (-I.upper 1) (-I.lower 1)

/-- **Closure of an open box rectangle.** For a nondegenerate real box `I=(l₀,u₀]×(l₁,u₁]`,
the closure of its sign-reversed open complex rectangle is the closed carrier
`[-u₀,-l₀]×[-u₁,-l₁]`. -/
theorem closure_rectangleOfBoxInterior (I : BoxIntegral.Box (Fin 2)) :
    closure (rectangleOfBoxInterior I) = (rectangleOfBox I).carrier := by
  have h₀ : -I.upper 0 < -I.lower 0 := neg_lt_neg (I.lower_lt_upper 0)
  have h₁ : -I.upper 1 < -I.lower 1 := neg_lt_neg (I.lower_lt_upper 1)
  rw [rectangleOfBoxInterior, Complex.closure_reProdIm,
    closure_Ioo h₀.ne, closure_Ioo h₁.ne]
  simp [rectangleOfBox, RectilinearRectangle.carrier, Complex.Rectangle, uIcc_of_le h₀.le,
    uIcc_of_le h₁.le]

/-- **The box-to-rectangle correspondence is injective.** For nondegenerate boxes `I,J⊆ℝ²`,
equality of their sign-reversed closed complex rectangles implies `I=J`. Both lower and
upper coordinate bounds are recovered from the diagonal endpoints. -/
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

/-- **Embedding of nondegenerate real boxes as complex rectangles.** The map sends
`I=(l₀,u₀]×(l₁,u₁]` to the closed complex rectangle `[-u₀,-l₀]×[-u₁,-l₁]`. It is
injective; it does not identify the half-open box with its closed carrier. -/
noncomputable def rectangleOfBoxEmbedding : BoxIntegral.Box (Fin 2) ↪ RectilinearRectangle where
  toFun := rectangleOfBox
  inj' := rectangleOfBox_injective

/-- **Sign-reversed real coordinates of a complex point.** For `z∈ℂ`, the associated vector in
`ℝ²` is `q(z)=(-Re z,-Im z)`. -/
noncomputable def complexBoxPoint (z : ℂ) : Fin 2 → ℝ :=
  fun i ↦ if i = 0 then -z.re else -z.im

/-- **Interior points give half-open box coordinates.** Let `I=(l₀,u₀]×(l₁,u₁]` with
`l_i<u_i`. If `z` lies in its sign-reversed open complex rectangle, then `q(z)=(-Re z,-Im
z)` belongs to `I`. -/
theorem complexBoxPoint_mem_of_mem_rectangleOfBoxInterior
    (I : BoxIntegral.Box (Fin 2)) {z : ℂ}
    (hz : z ∈ rectangleOfBoxInterior I) : complexBoxPoint z ∈ I := by
  intro i
  fin_cases i
  · change I.lower 0 < -z.re ∧ -z.re ≤ I.upper 0
    constructor <;> linarith [hz.1.1, hz.1.2]
  · change I.lower 1 < -z.im ∧ -z.im ≤ I.upper 1
    constructor <;> linarith [hz.2.1, hz.2.2]

/-- **Half-open grid intervals are characterized by the floor function.** For `t>0`, `n∈ℤ`,
and `x∈ℝ`, `-x∈(-(n+1)/t,-n/t]` if and only if `⌊t x⌋=n`. -/
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

/-- **Finite integer-weighted chains of real boxes.** A box chain is a finitely supported
function from nondegenerate two-dimensional real boxes to `ℤ`. Its coefficients may have
either sign. -/
abbrev BoxOverlayChain := BoxIntegral.Box (Fin 2) →₀ ℤ

/-- **Rectilinear cycle of a signed box chain.** For a finite box chain `C`, form `∑_I C(I) •
boundary(rectangleOfBox I)`, using the sign-reversed complex rectangle of each box.
Integer coefficients give the contour orientations. -/
noncomputable def BoxOverlayChain.toCycle (C : BoxOverlayChain) : RectilinearCycle :=
  Finsupp.mapDomain rectangleOfBoxEmbedding C

/-- **Boundary integral is additive under a coordinate cut.** Let `E` be a complete complex
normed vector space and `f:ℂ→E` globally continuous. For a nondegenerate real box `I`,
coordinate `i∈Fin 2`, and cut `l_i<x<u_i`, the boundary integral of its sign-reversed
complex rectangle equals the sum for the lower and upper subboxes. Their common edge
cancels. -/
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

/-- **Box-additive map of complex boundary integrals.** Let `E` be a complete complex normed
vector space and `f:ℂ→E` globally continuous. Assign each nondegenerate real box `I` the
counterclockwise boundary integral of `f` over its sign-reversed complex rectangle. This
assignment is additive under finite coordinate subdivision. -/
noncomputable def boundaryIntegralBoxAdditive {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) (hf : Continuous f) :
    BoxIntegral.BoxAdditiveMap (Fin 2) E ⊤ :=
  BoxIntegral.BoxAdditiveMap.ofMapSplitAdd
    (fun I ↦ (rectangleOfBox I).boundaryIntegral f) ⊤
    fun I _hI i x hx ↦ boundaryIntegral_rectangleOfBox_split f hf I i x hx

namespace GridFilling

/-- **Physical vertex for a finite grid filling.** For a filling `D` of scale `t>0` and
integer vertex `v∈ℤ²`, `D.point(v)=v₀/t+i v₁/t`. -/
noncomputable def point (D : GridFilling) (v : GridIndex) : ℂ :=
  gridPoint D.scale v

/-- **Real coordinate of a filling vertex.** For a filling `D` of scale `t>0` and `v∈ℤ²`,
`Re(D.point(v))=v₀/t`. -/
@[simp]
theorem point_re (D : GridFilling) (v : GridIndex) :
    (D.point v).re = (v 0 : ℝ) / D.scale := by
  simp [point, gridPoint]

/-- **Imaginary coordinate of a filling vertex.** For a filling `D` of scale `t>0` and `v∈ℤ²`,
`Im(D.point(v))=v₁/t`. -/
@[simp]
theorem point_im (D : GridFilling) (v : GridIndex) :
    (D.point v).im = (v 1 : ℝ) / D.scale := by
  simp [point, gridPoint]

/-- **Closed square at a filling-grid index.** For a filling `D` of scale `t>0` and any
`v∈ℤ²`, `D.cell(v)` has real interval `[v₀/t,(v₀+1)/t]` and imaginary interval
`[v₁/t,(v₁+1)/t]`. The index need not be selected in `D`. -/
noncomputable def cell (D : GridFilling) (v : GridIndex) : RectilinearRectangle :=
  gridCell D.scale v

/-- **Half-open real box of a filling-grid square.** For a filling `D` of scale `t>0` and
`v∈ℤ²`, `D.cellBox(v)=∏_{i=0,1}(-(v_i+1)/t,-v_i/t]` in sign-reversed coordinates. -/
noncomputable def cellBox (D : GridFilling) (v : GridIndex) :
    BoxIntegral.Box (Fin 2) :=
  gridCellBox D.scale D.scale_pos v

/-- **A cell box recovers the same closed grid square.** For a filling `D` of scale `t>0` and
`v∈ℤ²`, the sign-reversed complex rectangle associated with `D.cellBox(v)` is `D.cell(v)`. -/
theorem rectangleOfBox_cellBox (D : GridFilling) (v : GridIndex) :
    rectangleOfBox (D.cellBox v) = D.cell v := by
  ext <;> simp [rectangleOfBox, cellBox, gridCellBox, cell, gridCell,
    gridPoint, RectilinearRectangle.ofBounds]

/-- **Coordinate bounds of a positive-scale grid square.** For a filling `D` of scale `t>0`
and `v∈ℤ²`, `D.cell(v)` is the rectangle with real bounds `v₀/t,(v₀+1)/t` and imaginary
bounds `v₁/t,(v₁+1)/t`. -/
theorem cell_eq_ofBounds (D : GridFilling) (v : GridIndex) :
    D.cell v = RectilinearRectangle.ofBounds
      ((v 0 : ℝ) / D.scale) (((v 0 : ℝ) + 1) / D.scale)
      ((v 1 : ℝ) / D.scale) (((v 1 : ℝ) + 1) / D.scale) := by
  ext <;> simp [cell, gridCell, gridPoint, RectilinearRectangle.ofBounds]

/-- **Membership in a closed grid square.** For a filling `D` of scale `t>0`, `v∈ℤ²`, and
`z∈ℂ`, `z∈carrier(D.cell(v))` precisely when `v₀/t≤Re z≤(v₀+1)/t` and `v₁/t≤Im
z≤(v₁+1)/t`. -/
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

/-- **Filling determined by a scale and selected indices.** For `t>0` and a finite `C⊆ℤ²`,
form the grid filling with scale `t` and selected-cell set `C`. Its cells have side length
`1/t`, and `C` may be empty. -/
def ofCells (t : ℝ) (ht : 0 < t) (s : Finset GridIndex) : GridFilling where
  scale := t
  scale_pos := ht
  cells := s

/-- **Zero-or-one coefficient of a selected grid cell.** For a finite filling `D` and `v∈ℤ²`,
`c_D(v)=1` if `v` is selected in `D`, and `c_D(v)=0` otherwise. The coefficient is an
integer. -/
def cellCoeff (D : GridFilling) (v : GridIndex) : ℤ :=
  if v ∈ D.cells then 1 else 0

/-- **Counterclockwise boundary cycle of selected cells.** For a finite filling `D` of scale
`t>0`, its rectilinear cycle is `∑_{v∈D.cells} boundary(D.cell(v))`. Each closed square
has the counterclockwise orientation, and shared internal edges cancel. -/
noncomputable def toCycle (D : GridFilling) : RectilinearCycle :=
  ∑ v ∈ D.cells, RectilinearCycle.ofRectangle (D.cell v)

/-- **A filling integral is the sum of its cell-boundary integrals.** Let `E` be a complete
complex normed vector space, `D` a finite positive-scale filling, and `f:ℂ→E`. Then
`∮_{D.toCycle} f=∑_{v∈D.cells} ∮_{boundary(D.cell(v))} f`. No continuity premise is
required for this finite-sum identity. -/
theorem toCycle_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling) (f : ℂ → E) :
    D.toCycle.integral f = ∑ v ∈ D.cells, (D.cell v).boundaryIntegral f := by
  change RectilinearCycle.integralAddHom f D.toCycle = _
  simp [toCycle]

/-- **A filling winding index is the sum of cell indices.** For a finite positive-scale
filling `D` and any `z∈ℂ`, `index(D.toCycle,z)=∑_{v∈D.cells}
index(boundary(D.cell(v)),z)`, where each index is `(2πi)⁻¹∮(ζ-z)⁻¹ dζ`. The index uses
the total inverse, so the identity is stated at every `z`. -/
theorem toCycle_index (D : GridFilling) (z : ℂ) :
    D.toCycle.index z =
      ∑ v ∈ D.cells, (RectilinearCycle.ofRectangle (D.cell v)).index z := by
  change RectilinearCycle.indexAddHom z D.toCycle = _
  simp [toCycle]

/-- **Face coordinates for a common grid refinement.** Let `D,H` be finite grid fillings with
positive, possibly different, scales. For coordinate `i∈Fin 2`, form the finite set of all
lower and upper bounds of selected boxes from either filling, together with `0` and `1`.
The two extra coordinates ensure distinct extrema even when both fillings are empty. -/
noncomputable def commonCoordinates (D E : GridFilling) (i : Fin 2) : Finset ℝ :=
  {0, 1} ∪
    (D.cells.biUnion fun v ↦ {(D.cellBox v).lower i, (D.cellBox v).upper i}) ∪
      (E.cells.biUnion fun v ↦ {(E.cellBox v).lower i, (E.cellBox v).upper i})

/-- **A nondegenerate box containing two grid fillings.** Let `D,H` be finite grid fillings
with positive, possibly different, scales. In each coordinate, take the minimum and
maximum of their face-coordinate set, including `0` and `1`. The resulting half-open box
contains every selected cell box of both fillings and remains nondegenerate when both are
empty. -/
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

/-- **Distinct lattice indices give distinct cell boxes.** For a finite filling `D` of scale
`t>0`, the map `v∈ℤ²↦∏_{i=0,1}(-(v_i+1)/t,-v_i/t]` is injective. Positivity of `t` allows
recovery of both integer coordinates from the box bounds. -/
theorem cellBox_injective (D : GridFilling) : Function.Injective D.cellBox := by
  intro v w h
  funext i
  have hi := congrArg (fun I : BoxIntegral.Box (Fin 2) ↦ I.lower i) h
  simp only [cellBox, gridCellBox] at hi
  apply_fun (fun x : ℝ ↦ x * D.scale) at hi
  simpa [D.scale_pos.ne'] using hi

/-- **Distinct half-open grid cells are disjoint.** For a finite filling `D` of scale `t>0`
and distinct indices `v,w∈ℤ²`, the sign-reversed half-open boxes `D.cellBox(v)` and
`D.cellBox(w)` are disjoint as subsets of `ℝ²`. Shared faces of closed physical cells are
assigned to only one half-open box. -/
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

/-- **Finite collection of selected half-open cells.** For a finite positive-scale filling
`D`, take the image of its selected index set under `v↦D.cellBox(v)`. This finite box
family may be empty. -/
noncomputable def cellBoxes (D : GridFilling) : Finset (BoxIntegral.Box (Fin 2)) :=
  by
    classical
    exact D.cells.image D.cellBox

/-- **Selected half-open cells form a disjoint family.** For any finite positive-scale filling
`D`, distinct boxes in `D.cellBoxes` are disjoint as subsets of `ℝ²`. -/
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

/-- **Selected cells as a box prepartition.** Let `D` be a finite positive-scale filling and
`B` a nondegenerate real box containing every selected `D.cellBox(v)`. The selected boxes,
with their pairwise disjointness and containment in `B`, form a prepartition of `B`; they
need not cover `B`. -/
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

/-- **First-filling cells lie in the common bounding box.** Let `D,H` be finite grid fillings
with positive, possibly different, scales. For every index `v` selected in `D`,
`D.cellBox(v)⊆D.commonBoundingBox(H)` as half-open real boxes. -/
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

/-- **Second-filling cells lie in the common bounding box.** Let `D,H` be finite grid fillings
with positive, possibly different, scales. For every index `v` selected in `H`,
`H.cellBox(v)⊆D.commonBoundingBox(H)` as half-open real boxes. -/
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

/-- **First grid filling as a prepartition of a common box.** Let `D,H` be finite grid
fillings with positive, possibly different, scales. The boxes of `D` form a pairwise
disjoint finite prepartition of the common bounding box of `D,H`. Its union is the union
of selected first-filling half-open cells. -/
noncomputable def leftCellPrepartition (D E : GridFilling) :
    BoxIntegral.Prepartition (D.commonBoundingBox E) :=
  D.cellsPrepartition (D.commonBoundingBox E) fun _v hv ↦
    D.cellBox_le_commonBoundingBox_left E hv

/-- **Second grid filling as a prepartition of a common box.** Let `D,H` be finite grid
fillings with positive, possibly different, scales. The boxes of `H` form a pairwise
disjoint finite prepartition of the common bounding box of `D,H`. Its union is the union
of selected second-filling half-open cells. -/
noncomputable def rightCellPrepartition (D E : GridFilling) :
    BoxIntegral.Prepartition (D.commonBoundingBox E) :=
  E.cellsPrepartition (D.commonBoundingBox E) fun _v hv ↦
    D.cellBox_le_commonBoundingBox_right E hv

/-- **Finite coordinate cuts align two grid prepartitions.** Let `D,H` be finite grid fillings
with positive, possibly different, scales. There exists a finite set `s⊆Fin 2×ℝ` of
coordinate cuts such that, for each of their selected-cell prepartitions `π`, if
`ρ=splitMany(commonBox,s)`, then `π⊓ρ` is exactly the subfamily `{I∈ρ | I⊆union(π)}`. No
rational relation between the two scales is required. -/
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

/-- **Coordinate cuts chosen for two grid fillings.** Let `D,H` be finite grid fillings with
positive, possibly different, scales. Choose a finite family of real coordinate
hyperplanes that aligns both selected-cell prepartitions with one subdivision of their
common bounding box: each refined prepartition is the global subdivision restricted to its
own union. -/
noncomputable def overlayHyperplanes (D E : GridFilling) : Finset (Fin 2 × ℝ) :=
  Classical.choose (D.exists_overlayHyperplanes E)

/-- **The selected coordinate cuts give simultaneous alignment.** Let `D,H` be finite grid
fillings with positive, possibly different, scales. Let `ρ` be the subdivision of their
common bounding box by the chosen cuts. For either selected-cell prepartition `π`,
`π⊓ρ={I∈ρ | I⊆union(π)}`. Here intersection denotes common refinement and the right side
is a filtered box family. -/
theorem overlayHyperplanes_spec (D E : GridFilling) :
    ∀ π ∈ ({D.leftCellPrepartition E, D.rightCellPrepartition E} :
        Set (BoxIntegral.Prepartition (D.commonBoundingBox E))),
      π ⊓ BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
          (D.overlayHyperplanes E) =
        (BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
          (D.overlayHyperplanes E)).filter
            fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ π.iUnion :=
  Classical.choose_spec (D.exists_overlayHyperplanes E)

/-- **Integer chain of a finite box prepartition.** Let `B` be a nondegenerate half-open box
in `ℝ²` and `π` a finite prepartition of `B` into pairwise disjoint boxes. Assign
coefficient `1` to each box of `π` and `0` to every other box, obtaining a finite
integer-weighted box chain. -/
noncomputable def prepartitionToBoxOverlayChain
    {B : BoxIntegral.Box (Fin 2)} (π : BoxIntegral.Prepartition B) : BoxOverlayChain :=
  by
    classical
    exact ∑ I ∈ π.boxes, Finsupp.single I 1

/-- **A prepartition member has coefficient one.** Let `B` be a nondegenerate half-open box in
`ℝ²` and `π` a finite prepartition of `B` into pairwise disjoint boxes. If `I∈π`, its
coefficient in the associated integer box chain is `1`. -/
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

/-- **A box outside a prepartition has coefficient zero.** Let `B` be a nondegenerate
half-open box in `ℝ²` and `π` a finite prepartition of `B` into pairwise disjoint boxes.
If a nondegenerate box `I` does not belong to `π`, its coefficient in the associated
integer box chain is `0`. -/
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

/-- **Integer indicator of prepartition membership.** Let `B` be a nondegenerate half-open box
in `ℝ²` and `π` a finite prepartition of `B` into pairwise disjoint boxes. For a
nondegenerate box `I`, define `1_π(I)=1` when `I∈π` and `0` otherwise. -/
noncomputable def prepartitionIndicator
    {B : BoxIntegral.Box (Fin 2)} (π : BoxIntegral.Prepartition B)
    (I : BoxIntegral.Box (Fin 2)) : ℤ :=
  by
    classical
    exact if I ∈ π then 1 else 0

/-- **Box-chain coefficients equal the prepartition indicator.** Let `B` be a nondegenerate
half-open box in `ℝ²` and `π` a finite prepartition of `B` into pairwise disjoint boxes.
At every box `I`, the coefficient of the associated integer chain is `1_π(I)`, equal to
`1` or `0` according to membership in `π`. -/
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

/-- **Common finite subdivision for two grid fillings.** Let `D,H` be finite grid fillings
with positive, possibly different, scales. Subdivide their common bounding box using the
chosen aligning coordinate hyperplanes. Both refined selected-cell collections are
subfamilies of this global prepartition. -/
noncomputable def overlayPrepartition (D E : GridFilling) :
    BoxIntegral.Prepartition (D.commonBoundingBox E) :=
  BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
    (D.overlayHyperplanes E)

/-- **First-filling cells after common coordinate subdivision.** Let `D,H` be finite grid
fillings with positive, possibly different, scales. Subdivide each selected first-filling
box by the chosen common cuts and take the union of those finite subpartitions. This is
the refined first-filling prepartition inside the common bounding box. -/
noncomputable def leftOverlayPrepartition (D E : GridFilling) :
    BoxIntegral.Prepartition (D.commonBoundingBox E) :=
  (D.leftCellPrepartition E).biUnion fun I ↦
    BoxIntegral.Prepartition.splitMany I (D.overlayHyperplanes E)

/-- **Second-filling cells after common coordinate subdivision.** Let `D,H` be finite grid
fillings with positive, possibly different, scales. Subdivide each selected second-filling
box by the chosen common cuts and take their finite union. This is the refined
second-filling prepartition inside the common bounding box. -/
noncomputable def rightOverlayPrepartition (D E : GridFilling) :
    BoxIntegral.Prepartition (D.commonBoundingBox E) :=
  (D.rightCellPrepartition E).biUnion fun I ↦
    BoxIntegral.Prepartition.splitMany I (D.overlayHyperplanes E)

/-- **Refined first cells are a restriction of the global subdivision.** Let `D,H` be finite
grid fillings with positive, possibly different, scales. For the chosen global subdivision
`ρ`, the first refined family equals `{I∈ρ | I⊆union(firstCellPrepartition)}`. Thus no
overlay box crosses the first family's half-open union boundary. -/
theorem leftOverlayPrepartition_eq_filter (D E : GridFilling) :
    D.leftOverlayPrepartition E =
      (BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
        (D.overlayHyperplanes E)).filter
          fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ (D.leftCellPrepartition E).iUnion := by
  rw [leftOverlayPrepartition, ← BoxIntegral.Prepartition.inf_splitMany]
  exact D.overlayHyperplanes_spec E (D.leftCellPrepartition E) (by simp)

/-- **Refined second cells are a restriction of the global subdivision.** Let `D,H` be finite
grid fillings with positive, possibly different, scales. For the chosen global subdivision
`ρ`, the second refined family equals `{I∈ρ | I⊆union(secondCellPrepartition)}`. -/
theorem rightOverlayPrepartition_eq_filter (D E : GridFilling) :
    D.rightOverlayPrepartition E =
      (BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
        (D.overlayHyperplanes E)).filter
          fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ (D.rightCellPrepartition E).iUnion := by
  rw [rightOverlayPrepartition, ← BoxIntegral.Prepartition.inf_splitMany]
  exact D.overlayHyperplanes_spec E (D.rightCellPrepartition E) (by simp)

/-- **Signed box overlay of two grid fillings.** Let `D,H` be finite grid fillings with
positive, possibly different, scales. Subtract the integer chain of the refined
second-cell prepartition from that of the refined first-cell prepartition. A box shared by
both has coefficient zero; boxes belonging only to the first or second have coefficient
`1` or `-1`. -/
noncomputable def commonOverlay (D E : GridFilling) : BoxOverlayChain :=
  prepartitionToBoxOverlayChain (D.leftOverlayPrepartition E) -
    prepartitionToBoxOverlayChain (D.rightOverlayPrepartition E)

/-- **Signed overlay coefficients are differences of indicators.** Let `D,H` be finite grid
fillings with positive, possibly different, scales. For every real box `I`, the
common-overlay coefficient is `1_{leftOverlay}(I)-1_{rightOverlay}(I)`, with each
indicator taking integer values `0,1`. -/
theorem commonOverlay_apply (D E : GridFilling)
    (I : BoxIntegral.Box (Fin 2)) :
    D.commonOverlay E I =
      prepartitionIndicator (D.leftOverlayPrepartition E) I -
        prepartitionIndicator (D.rightOverlayPrepartition E) I := by
  classical
  rw [commonOverlay, Finsupp.sub_apply,
    prepartitionToBoxOverlayChain_apply,
    prepartitionToBoxOverlayChain_apply]

/-- **Every surviving signed box belongs to the global subdivision.** Let `D,H` be finite grid
fillings with positive, possibly different, scales. If the common-overlay coefficient at a
real box `I` is nonzero, then `I` belongs to the chosen global overlay prepartition. -/
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

/-- **Point membership detects an aligned overlay box.** Let `π,ρ` be finite prepartitions of
the same nondegenerate real box and suppose `π⊓ρ={J∈ρ | J⊆union(π)}`. For `I∈ρ` and `x∈I`,
`I⊆union(π)` if and only if `x∈union(π)`. This uses alignment, not a general assertion for
arbitrary intersecting boxes. -/
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

/-- **Integral of a signed box cycle.** Let `E` be a complete complex normed vector space. For
a finitely supported integer box chain `C` and `f:ℂ→E`, `∮_{C.toCycle} f=∑_I C(I) •
∮_{boundary(rectangleOfBox I)} f`. No continuity hypothesis is needed for this finite-sum
identity. -/
theorem BoxOverlayChain.toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (C : BoxOverlayChain) (f : ℂ → E) :
    C.toCycle.integral f =
      C.sum fun I n ↦ n • (rectangleOfBox I).boundaryIntegral f := by
  unfold BoxOverlayChain.toCycle RectilinearCycle.integral
  rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp)
    (fun _ m n ↦ by simp [add_zsmul])]
  rfl

/-- **Subtraction of signed box chains gives subtraction of cycles.** For finite integer box
chains `C,D`, `(C-D).toCycle=C.toCycle-D.toCycle`, where each cycle is the
integer-weighted sum of its boxes' counterclockwise rectangle boundaries. -/
theorem BoxOverlayChain.toCycle_sub (C D : BoxOverlayChain) :
    (C - D).toCycle = C.toCycle - D.toCycle := by
  simp [BoxOverlayChain.toCycle, Finsupp.mapDomain_sub]

/-- **Additive boundary-integral map on signed box chains.** Let `E` be a complete complex
normed vector space. For `f:ℂ→E`, send a finitely supported integer box chain `C` to `∑_I
C(I) • ∮_{boundary(rectangleOfBox I)} f`. This is an additive homomorphism from box chains
to `E`; no continuity premise is part of its definition. -/
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

/-- **Integral of an unsigned prepartition cycle.** Let `E` be a complete complex normed
vector space. Let `B` be a nondegenerate half-open box in `ℝ²` and `π` a finite
prepartition of `B` into pairwise disjoint boxes. For any `f:ℂ→E`, the contour integral of
the coefficient-one box chain is `∑_{I∈π.boxes} ∮_{boundary(rectangleOfBox I)} f`. No
regularity assumption on `f` is needed. -/
theorem prepartitionToBoxOverlayChain_toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {B : BoxIntegral.Box (Fin 2)} (π : BoxIntegral.Prepartition B) (f : ℂ → E) :
    (prepartitionToBoxOverlayChain π).toCycle.integral f =
      ∑ I ∈ π.boxes, (rectangleOfBox I).boundaryIntegral f := by
  classical
  rw [BoxOverlayChain.toCycle_integral]
  change boxBoundaryIntegralAddHom f (prepartitionToBoxOverlayChain π) = _
  simp [prepartitionToBoxOverlayChain, boxBoundaryIntegralAddHom]

/-- **Cell-index and cell-box sums have equal boundary integrals.** Let `E` be a complete
complex normed vector space. For a finite positive-scale filling `D` and `f:ℂ→E`,
`∑_{I∈D.cellBoxes} ∮_{boundary(rectangleOfBox I)} f=∑_{v∈D.cells} ∮_{boundary(D.cell(v))}
f`. Injectivity of the cell-box map prevents repetitions. -/
theorem sum_cellBoxes_boundaryIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → E) :
    ∑ I ∈ D.cellBoxes, (rectangleOfBox I).boundaryIntegral f =
      ∑ v ∈ D.cells, (D.cell v).boundaryIntegral f := by
  classical
  rw [cellBoxes, Finset.sum_image]
  · simp [rectangleOfBox_cellBox]
  · exact fun _ _ _ _ h ↦ D.cellBox_injective h

/-- **Refining the first grid preserves its contour integral.** Let `E` be a complete complex
normed vector space. Let `D,H` be finite grid fillings with positive, possibly different,
scales. If `f:ℂ→E` is globally continuous, the contour integral of the refined first box
chain equals `∮_{D.toCycle} f`. The internal edges introduced by subdivision cancel. -/
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

/-- **Refining the second grid preserves its contour integral.** Let `E` be a complete complex
normed vector space. Let `D,H` be finite grid fillings with positive, possibly different,
scales. If `f:ℂ→E` is globally continuous, the contour integral of the refined second box
chain equals `∮_{H.toCycle} f`. -/
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

/-- **Signed overlay integral is the difference of grid integrals.** Let `E` be a complete
complex normed vector space. Let `D,H` be finite grid fillings with positive, possibly
different, scales. For globally continuous `f:ℂ→E`, `∮_{commonOverlay(D,H).toCycle}
f=∮_{D.toCycle} f-∮_{H.toCycle} f`. This comparison allows unrelated positive scales and
empty fillings. -/
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

/-- **Signed coefficient of a grid boundary edge.** Let `D` be a finite grid filling of scale
`t>0`. Write `c_D(v)=1` for a selected integer cell `v∈ℤ²`, and `0` otherwise. For the
horizontal edge based at `v`, the coefficient is `c_D(v)-c_D(v-e₁)`; for the vertical edge
it is `c_D(v-e₀)-c_D(v)`. Here `e₀,e₁` are the two unit lattice steps. Thus the
coefficients are above-minus-below and left-minus-right. -/
def boundaryCoeff (D : GridFilling) : GridEdge → ℤ
  | .horizontal v => D.cellCoeff v - D.cellCoeff (v.pred 1)
  | .vertical v => D.cellCoeff (v.pred 0) - D.cellCoeff v

/-- **Four-edge chain of a counterclockwise grid square.** For `v∈ℤ²`, its oriented edge chain
is `h_v-h_{v+e₁}+v_{v+e₀}-v_v`, where `h_u` is the rightward horizontal edge and `v_u` the
upward vertical edge based at `u`. The integer coefficients give the bottom, top, right
and left orientations. -/
noncomputable def cellBoundaryChain (v : GridIndex) : GridEdge →₀ ℤ :=
  Finsupp.single (.horizontal v) 1 -
    Finsupp.single (.horizontal (v.succ 1)) 1 +
      Finsupp.single (.vertical (v.succ 0)) 1 -
        Finsupp.single (.vertical v) 1

/-- **Sum of oriented selected-cell edge chains.** Let `D` be a finite grid filling of scale
`t>0`. Sum the four-edge chain of each selected `v∈D.cells`. At a horizontal edge `h_v`
the coefficient is `c_D(v)-c_D(v-e₁)`, and at a vertical edge `v_v` it is
`c_D(v-e₀)-c_D(v)`, with `c_D` the selected-cell indicator. Internal edges cancel. -/
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

/-- **Horizontal coefficient in the summed cell-boundary chain.** Let `D` be a finite grid
filling of scale `t>0`. Write `c_D(v)=1` for a selected integer cell `v∈ℤ²`, and `0`
otherwise. At the rightward edge based at `v`, the summed chain coefficient is
`c_D(v)-c_D(v-e₁)`, the indicator above minus the indicator below. -/
@[simp]
theorem boundaryChain_horizontal (D : GridFilling) (v : GridIndex) :
    D.boundaryChain (.horizontal v) = D.boundaryCoeff (.horizontal v) := by
  classical
  simp [boundaryChain, cellBoundaryChain, boundaryCoeff, cellCoeff]

/-- **Vertical coefficient in the summed cell-boundary chain.** Let `D` be a finite grid
filling of scale `t>0`. Write `c_D(v)=1` for a selected integer cell `v∈ℤ²`, and `0`
otherwise. At the upward edge based at `v`, the summed chain coefficient is
`c_D(v-e₀)-c_D(v)`, the indicator on the left minus the indicator on the right. -/
@[simp]
theorem boundaryChain_vertical (D : GridFilling) (v : GridIndex) :
    D.boundaryChain (.vertical v) = D.boundaryCoeff (.vertical v) := by
  classical
  simp [boundaryChain, cellBoundaryChain, boundaryCoeff, cellCoeff]

/-- **Cancellation criterion for a horizontal grid edge.** Let `D` be a finite grid filling of
scale `t>0`. Write `c_D(v)=1` for a selected integer cell `v∈ℤ²`, and `0` otherwise. The
horizontal edge based at `v` has zero net boundary coefficient if and only if
`c_D(v)=c_D(v-e₁)`. It cancels when both adjacent cells are selected or neither is
selected. -/
theorem horizontal_boundaryCoeff_eq_zero_iff (D : GridFilling) (v : GridIndex) :
    D.boundaryCoeff (.horizontal v) = 0 ↔
      D.cellCoeff v = D.cellCoeff (v.pred 1) := by
  simp [boundaryCoeff, sub_eq_zero]

/-- **Cancellation criterion for a vertical grid edge.** Let `D` be a finite grid filling of
scale `t>0`. Write `c_D(v)=1` for a selected integer cell `v∈ℤ²`, and `0` otherwise. The
vertical edge based at `v` has zero net coefficient if and only if `c_D(v-e₀)=c_D(v)`, so
the left and right selection indicators agree. -/
theorem vertical_boundaryCoeff_eq_zero_iff (D : GridFilling) (v : GridIndex) :
    D.boundaryCoeff (.vertical v) = 0 ↔
      D.cellCoeff (v.pred 0) = D.cellCoeff v := by
  simp [boundaryCoeff, sub_eq_zero]

/-- **The four oriented edges adjacent to a grid cell.** For `v∈ℤ²`, take the horizontal edges
based at `v,v+e₁` and the vertical edges based at `v,v+e₀`. These are the four candidate
edges of the cell before signs and cancellation are applied. -/
def cellEdges (v : GridIndex) : Finset GridEdge :=
  {.horizontal v, .horizontal (v.succ 1),
    .vertical v, .vertical (v.succ 0)}

/-- **Surviving edges of a finite grid boundary.** Let `D` be a finite grid filling of scale
`t>0`. Take the finite union of the four edges of each selected cell and retain exactly
those with nonzero signed boundary coefficient. Horizontal coefficients are
above-minus-below and vertical coefficients left-minus-right. -/
def boundaryEdges (D : GridFilling) : Finset GridEdge :=
  (D.cells.biUnion cellEdges).filter fun e => D.boundaryCoeff e ≠ 0

/-- **Reduced-edge membership is equivalent to a nonzero coefficient.** Let `D` be a finite
grid filling of scale `t>0`. For any horizontal or vertical grid edge `e`,
`e∈D.boundaryEdges` if and only if `D.boundaryCoeff(e)≠0`. Every nonzero coefficient
therefore occurs among edges adjacent to selected cells. -/
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

/-- **Each surviving grid edge has unit signed weight.** Let `D` be a finite grid filling of
scale `t>0`. If `e∈D.boundaryEdges`, then its net integer boundary coefficient is `1` or
`-1`. This follows from taking differences of zero-or-one adjacent-cell indicators. -/
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

/-- **Initial complex point of an oriented grid edge.** Let `D` be a finite grid filling of
scale `t>0`. A horizontal or vertical edge based at `v∈ℤ²` begins at `v₀/t+i v₁/t`. -/
noncomputable def edgeStart (D : GridFilling) : GridEdge → ℂ
  | .horizontal v => D.point v
  | .vertical v => D.point v

/-- **Terminal complex point of an oriented grid edge.** Let `D` be a finite grid filling of
scale `t>0`. The horizontal edge based at `v` ends at `(v₀+1)/t+i v₁/t`, while the
vertical edge ends at `v₀/t+i(v₁+1)/t`. The orientations are rightward and upward. -/
noncomputable def edgeEnd (D : GridFilling) : GridEdge → ℂ
  | .horizontal v => D.point (v.succ 0)
  | .vertical v => D.point (v.succ 1)

/-- **Closed segment traced by an oriented grid edge.** Let `D` be a finite grid filling of
scale `t>0`. For a grid edge `e`, its trace is the real line segment joining its initial
and terminal complex points. Orientation affects integration, not this geometric set; its
length is `1/t`. -/
noncomputable def edgeTrace (D : GridFilling) (e : GridEdge) : Set ℂ :=
  segment ℝ (D.edgeStart e) (D.edgeEnd e)

set_option linter.flexible false in
/-- **Every edge of a grid cell lies in its closed square.** Let `D` be a finite grid filling
of scale `t>0`. If `e` is one of the four edges adjacent to the cell at `v∈ℤ²`, then
`D.edgeTrace(e)⊆carrier(D.cell(v))`. The cell need not be selected. -/
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

/-- **A surviving boundary edge belongs to a selected cell.** Let `D` be a finite grid filling
of scale `t>0`. For every `e∈D.boundaryEdges`, there is a selected index `v∈D.cells` such
that `D.edgeTrace(e)⊆carrier(D.cell(v))`. -/
theorem exists_selected_cell_of_mem_boundaryEdges
    (D : GridFilling) {e : GridEdge} (he : e ∈ D.boundaryEdges) :
    ∃ v ∈ D.cells, D.edgeTrace e ⊆ (D.cell v).carrier := by
  rw [boundaryEdges, Finset.mem_filter] at he
  rcases Finset.mem_biUnion.mp he.1 with ⟨v, hv, hev⟩
  exact ⟨v, hv, D.edgeTrace_subset_cell_carrier_of_mem_cellEdges v hev⟩

/-- **A grid-edge trace is compact.** Let `D` be a finite grid filling of scale `t>0`. For
every horizontal or vertical edge `e`, the real line segment between its complex endpoints
is compact in `ℂ`. -/
theorem isCompact_edgeTrace (D : GridFilling) (e : GridEdge) :
    IsCompact (D.edgeTrace e) := by
  rw [edgeTrace, segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

/-- **A grid-edge trace is closed.** Let `D` be a finite grid filling of scale `t>0`. For
every grid edge `e`, its closed real line segment is a closed subset of the complex plane. -/
theorem isClosed_edgeTrace (D : GridFilling) (e : GridEdge) :
    IsClosed (D.edgeTrace e) := (D.isCompact_edgeTrace e).isClosed

/-- **Every point of the horizontal edge interval lies on its trace.** Let `D` be a finite
grid filling of scale `t>0`. For an index `v∈ℤ²` and `v₀/t≤x≤(v₀+1)/t`, the point `x+i
v₁/t` lies on the trace of the horizontal edge based at `v`. -/
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

/-- **Every point of the vertical edge interval lies on its trace.** Let `D` be a finite grid
filling of scale `t>0`. For an index `v∈ℤ²` and `v₁/t≤y≤(v₁+1)/t`, the point `v₀/t+i y`
lies on the trace of the vertical edge based at `v`. -/
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

/-- **Banach-valued integral along an oriented grid edge.** Let `E` be a complete complex
normed vector space. Let `D` be a finite grid filling of scale `t>0`. For `f:ℂ→E`,
integrate `f(x+i v₁/t)` over `x∈[v₀/t,(v₀+1)/t]` on the horizontal edge at `v`. On the
vertical edge integrate `i • f(v₀/t+i y)` over `y∈[v₁/t,(v₁+1)/t]`. These are interval
integrals with the positive rightward and upward orientations. -/
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

/-- **A cell boundary integral is its signed four-edge sum.** Let `E` be a complete complex
normed vector space. Let `D` be a finite grid filling of scale `t>0`. For `f:ℂ→E` and any
cell index `v`, its counterclockwise boundary integral is
`I(h_v,f)-I(h_{v+e₁},f)+I(v_{v+e₀},f)-I(v_v,f)`, where `I(e,f)` is the positively oriented
grid-edge integral. No continuity premise is required for this identity. -/
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

/-- **Additive integral of an integer-weighted grid-edge chain.** Let `E` be a complete
complex normed vector space. Let `D` be a finite grid filling of scale `t>0`. For `f:ℂ→E`,
send a finite integer edge chain `c` to `∑_e c(e) • I_D(e,f)`, where `I_D(e,f)` is the
rightward or upward edge integral. This defines an additive homomorphism from edge chains
to `E`. -/
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

/-- **Value of the additive edge-chain integral.** Let `E` be a complete complex normed vector
space. Let `D` be a finite grid filling of scale `t>0`. For `f:ℂ→E` and a finitely
supported integer edge chain `c`, `D.edgeIntegralAddHom(f)(c)=∑_e c(e) •
D.edgeIntegral(e,f)`. No continuity premise is required. -/
@[simp]
theorem edgeIntegralAddHom_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling) (f : ℂ → E)
    (c : GridEdge →₀ ℤ) :
    D.edgeIntegralAddHom f c = c.sum fun e n ↦ n • D.edgeIntegral e f := rfl

/-- **Integrating one cell chain gives its rectangle boundary integral.** Let `E` be a
complete complex normed vector space. Let `D` be a finite grid filling of scale `t>0`. For
`f:ℂ→E` and `v∈ℤ²`, integration of the signed four-edge chain `h_v-h_{v+e₁}+v_{v+e₀}-v_v`
equals the counterclockwise boundary integral of `D.cell(v)`. -/
@[simp]
theorem edgeIntegralAddHom_cellBoundaryChain {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → E) (v : GridIndex) :
    D.edgeIntegralAddHom f (cellBoundaryChain v) =
      (D.cell v).boundaryIntegral f := by
  rw [cellBoundaryChain, map_sub, map_add, map_sub]
  simp [cell_boundaryIntegral_eq_edgeIntegral]

/-- **Cauchy edge integral is continuous away from its pole trace.** Let `D` be a finite grid
filling of scale `t>0`. For any grid edge `e`, `z↦∫_e(ξ-z)⁻¹ dξ` is continuous on
`ℂ∖D.edgeTrace(e)`. The inverse is total, but the continuity assertion excludes poles on
the integrated segment. -/
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

/-- **Geometric trace of the reduced grid boundary.** Let `D` be a finite grid filling of
scale `t>0`. The reduced trace is `T_D=⋃_{e∈D.boundaryEdges}D.edgeTrace(e)`, a finite
union of the surviving closed edge segments after internal-edge cancellation. It is empty
for an empty filling. -/
noncomputable def reducedTrace (D : GridFilling) : Set ℂ :=
  ⋃ e ∈ D.boundaryEdges, D.edgeTrace e

/-- **The reduced grid trace is closed.** Let `D` be a finite grid filling of scale `t>0`.
Write `T_D` for the reduced trace, the union of line segments belonging to edges with
nonzero boundary coefficient. Since the surviving edge family is finite and each segment
is closed, `T_D` is closed in `ℂ`. -/
theorem isClosed_reducedTrace (D : GridFilling) : IsClosed D.reducedTrace := by
  apply isClosed_biUnion_finset
  intro e he
  exact D.isClosed_edgeTrace e

/-- **Integral of the reduced signed grid boundary.** Let `E` be a complete complex normed
vector space. Let `D` be a finite grid filling of scale `t>0`. For `f:ℂ→E`, define
`D.reducedIntegral(f)=∑_{e∈D.boundaryEdges}D.boundaryCoeff(e) • D.edgeIntegral(e,f)`. The
surviving integer coefficients are `1` or `-1`; an empty filling has integral zero. -/
noncomputable def reducedIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling) (f : ℂ → E) : E :=
  ∑ e ∈ D.boundaryEdges, D.boundaryCoeff e • D.edgeIntegral e f

/-- **Reduced integrals depend only on values on surviving edges.** Let `E` be a complete
complex normed vector space. Let `D` be a finite grid filling of scale `t>0`. Write `T_D`
for the reduced trace, the union of line segments belonging to edges with nonzero boundary
coefficient. If `f,g:ℂ→E` agree at every point of `T_D`, then
`D.reducedIntegral(f)=D.reducedIntegral(g)`. No continuity premise is required. -/
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

/-- **Continuous linear maps commute with an edge integral.** Let `E,F` be complete complex
normed vector spaces, `D` a finite positive-scale filling, `e` a grid edge, and
`L:E→L[ℂ]F`. If `f:ℂ→E` is continuous on `D.edgeTrace(e)`, then `I_D(e,L∘f)=L(I_D(e,f))`. -/
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

/-- **Continuous linear maps commute with a reduced grid integral.** Let `E,F` be complete
complex normed vector spaces, `D` a finite positive-scale filling, and `L:E→L[ℂ]F`. If the
reduced trace lies in `U⊆ℂ` and `f:ℂ→E` is continuous on `U`, then
`D.reducedIntegral(L∘f)=L(D.reducedIntegral(f))`. -/
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

/-- **Surviving grid edges are the support of the boundary chain.** Let `D` be a finite grid
filling of scale `t>0`. The finite set `D.boundaryEdges` equals the support of the
finitely supported sum of all selected-cell four-edge chains. Both contain exactly the
edges with nonzero net integer coefficient. -/
theorem boundaryEdges_eq_boundaryChain_support (D : GridFilling) :
    D.boundaryEdges = D.boundaryChain.support := by
  ext e
  rw [mem_boundaryEdges_iff, Finsupp.mem_support_iff]
  cases e <;> simp

/-- **Reduced integration equals integration of the summed boundary chain.** Let `E` be a
complete complex normed vector space. Let `D` be a finite grid filling of scale `t>0`. For
any `f:ℂ→E`, `D.reducedIntegral(f)=D.edgeIntegralAddHom(f)(D.boundaryChain)`. The right
side integrates the sum of selected-cell signed edge chains; no continuity premise is
required. -/
theorem reducedIntegral_eq_edgeIntegralAddHom {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → E) :
    D.reducedIntegral f = D.edgeIntegralAddHom f D.boundaryChain := by
  rw [reducedIntegral, edgeIntegralAddHom_apply,
    boundaryEdges_eq_boundaryChain_support]
  apply Finset.sum_congr rfl
  intro e he
  cases e <;> simp

/-- **Reduced Cauchy integral is continuous off the grid trace.** Let `D` be a finite grid
filling of scale `t>0`. Write `T_D` for the reduced trace, the union of line segments
belonging to edges with nonzero boundary coefficient. If `z∉T_D`, then
`w↦D.reducedIntegral(ξ↦(ξ-w)⁻¹)` is continuous at `z`. -/
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

/-- **Discrete Stokes equality for a finite grid filling.** Let `E` be a complete complex
normed vector space. Let `D` be a finite grid filling of scale `t>0`. For every `f:ℂ→E`,
the sum of its counterclockwise selected-cell boundary integrals equals the reduced
signed-edge integral: `D.toCycle.integral(f)=D.reducedIntegral(f)`. Internal edges cancel,
without a continuity hypothesis on `f`. -/
theorem toCycle_integral_eq_reducedIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → E) :
    D.toCycle.integral f = D.reducedIntegral f := by
  rw [toCycle_integral, reducedIntegral_eq_edgeIntegralAddHom]
  change (∑ v ∈ D.cells, (D.cell v).boundaryIntegral f) =
    D.edgeIntegralAddHom f (∑ v ∈ D.cells, cellBoundaryChain v)
  simp only [map_sum, edgeIntegralAddHom_cellBoundaryChain]

/-- **Grid winding index is continuous off the reduced trace.** Let `D` be a finite grid
filling of scale `t>0`. Write `T_D` for the reduced trace, the union of line segments
belonging to edges with nonzero boundary coefficient. For `z∉T_D`, the analytic index
`w↦(2πi)⁻¹∮_{D.toCycle}(ξ-w)⁻¹ dξ` is continuous at `z`. -/
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

/-- **Closed region of the selected grid cells.** Let `D` be a finite grid filling of scale
`t>0`. The region is `R_D=⋃_{v∈D.cells}carrier(D.cell(v))`, the finite union of selected
closed squares. It may be empty and need not be connected. -/
noncomputable def region (D : GridFilling) : Set ℂ :=
  ⋃ v ∈ D.cells, (D.cell v).carrier

/-- **The selected-cell region is compact.** Let `D` be a finite grid filling of scale `t>0`.
The finite union `R_D=⋃_{v∈D.cells}carrier(D.cell(v))` is compact in the complex plane,
including the empty selected-cell case. -/
theorem isCompact_region (D : GridFilling) : IsCompact D.region := by
  rw [region]
  apply D.cells.isCompact_biUnion
  intro v hv
  simpa [RectilinearRectangle.carrier, Complex.Rectangle] using
    (isCompact_uIcc.reProdIm isCompact_uIcc)

/-- **The reduced boundary lies in the selected-cell region.** Let `D` be a finite grid
filling of scale `t>0`. Every point of the reduced trace
`⋃_{e∈D.boundaryEdges}D.edgeTrace(e)` belongs to the closed union
`⋃_{v∈D.cells}carrier(D.cell(v))`. -/
theorem reducedTrace_subset_region (D : GridFilling) :
    D.reducedTrace ⊆ D.region := by
  intro z hz
  rw [reducedTrace] at hz
  rcases Set.mem_iUnion.mp hz with ⟨e, hz⟩
  rcases Set.mem_iUnion.mp hz with ⟨he, hze⟩
  obtain ⟨v, hv, hev⟩ := D.exists_selected_cell_of_mem_boundaryEdges he
  rw [region]
  exact Set.mem_iUnion_of_mem v (Set.mem_iUnion_of_mem hv (hev hze))

/-- **Grid cells meeting a closed thickening of a planar set.** For `K⊆ℂ` and `r,t∈ℝ`, select
`{v∈ℤ² | carrier(gridCell t v)∩cthickening(r,K)≠∅}`. The set-valued definition makes no
compactness, nonnegative-radius, or positive-scale assumption; such hypotheses occur in
its finiteness and geometry lemmas. -/
noncomputable def selectedCellSet (K : Set ℂ) (r t : ℝ) : Set GridIndex :=
  gridCellsMeeting t (Metric.cthickening r K)

/-- **Open square inside a positive-scale grid cell.** Let `D` be a finite grid filling of
scale `t>0`. For `v∈ℤ²`, the interior is `{z | v₀/t<Re z<(v₀+1)/t and v₁/t<Im
z<(v₁+1)/t}`. The index need not be selected. -/
noncomputable def cellInterior (D : GridFilling) (v : GridIndex) : Set ℂ :=
  Ioo ((v 0 : ℝ) / D.scale) (((v 0 : ℝ) + 1) / D.scale) ×ℂ
    Ioo ((v 1 : ℝ) / D.scale) (((v 1 : ℝ) + 1) / D.scale)

/-- **Integer coordinate embedding of grid indices.** Send the grid index `v:Fin 2→ℤ` to the
pair `(v₀,v₁)∈ℤ×ℤ`. This map is injective because the two coordinates determine `v`. -/
def gridIndexEmbedding : GridIndex ↪ ℤ × ℤ where
  toFun v := (v 0, v 1)
  inj' := by
    intro v w h
    funext i
    fin_cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h

/-- **Only finitely many grid cells meet a bounded set.** For a bounded `S⊆ℂ` and `t>0`, the
set `{v∈ℤ² | carrier(gridCell t v)∩S≠∅}` is finite. Compactness of `S` is not required. -/
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

/-- **A compact set has finitely many thickening-selected cells.** If `K⊆ℂ` is compact, `t>0`,
and `r∈ℝ`, then the cells meeting `cthickening(r,K)` form a finite set. No
nonnegative-radius premise is required for finiteness. -/
theorem selectedCellSet_finite (K : Set ℂ) (r : ℝ) {t : ℝ} (ht : 0 < t)
    (hK : IsCompact K) : (selectedCellSet K r t).Finite :=
  gridCellsMeeting_finite hK.cthickening.isBounded ht

/-- **Finite filling selected by a compact-set thickening.** For compact `K⊆ℂ`, `t>0`, and
`r∈ℝ`, form the scale-`t` filling whose selected cells meet `cthickening(r,K)`. The
definition includes empty `K`; it does not assume `r≥0`. -/
noncomputable def selectedFilling (K : Set ℂ) (r t : ℝ) (ht : 0 < t)
    (hK : IsCompact K) : GridFilling :=
  ofCells t ht (selectedCellSet_finite K r ht hK).toFinset

/-- **Membership rule for the thickening-selected filling.** For compact `K⊆ℂ`, `t>0`, `r∈ℝ`,
and `v∈ℤ²`, the index `v` is selected precisely when its closed physical cell meets
`cthickening(r,K)`. This is the selection rule used to form the finite filling. -/
@[simp]
theorem mem_selectedFilling_cells (K : Set ℂ) (r : ℝ) {t : ℝ}
    (ht : 0 < t) (hK : IsCompact K) (v : GridIndex) :
    v ∈ (selectedFilling K r t ht hK).cells ↔ v ∈ selectedCellSet K r t := by
  exact (selectedCellSet_finite K r ht hK).mem_toFinset

/-- **Diameter bound for a closed grid square.** Let `D` be a finite grid filling of scale
`t>0`. If `z,w` lie in the same cell carrier at an index `v∈ℤ²`, then their complex
distance satisfies `dist(z,w)≤2/t`. This bound uses the sum of the two coordinate lengths
and does not require the cell to be selected. -/
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

/-- **A selected cell lies in an enlarged compact-set thickening.** Let `K⊆ℂ` be compact,
`t>0`, and let `D` consist of all scale-`t` closed cells meeting `cthickening(r,K)`. For
`r≥0`, every selected closed cell is contained in `cthickening(r+2/t,K)`. The `2/t` term
bounds the diameter of one physical cell. -/
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

/-- **The thickening-selected region stays within a controlled enlargement.** Let `K⊆ℂ` be
compact, `t>0`, and let `D` consist of all scale-`t` closed cells meeting
`cthickening(r,K)`. If `r≥0`, the union of its selected closed cell carriers is contained
in `cthickening(r+2/t,K)`. -/
theorem selectedFilling_region_subset_cthickening
    (K : Set ℂ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) (hK : IsCompact K) :
    (selectedFilling K r t ht hK).region ⊆ Metric.cthickening (2 / t + r) K := by
  intro z hz
  rw [region] at hz
  rcases Set.mem_iUnion.mp hz with ⟨v, hz⟩
  rcases Set.mem_iUnion.mp hz with ⟨hv, hzcell⟩
  exact selectedFilling_cell_carrier_subset_cthickening K hr ht hK hv hzcell

/-- **The selected reduced boundary lies in an enlarged thickening.** Let `K⊆ℂ` be compact,
`t>0`, and let `D` consist of all scale-`t` closed cells meeting `cthickening(r,K)`. If
`r≥0`, the reduced trace of `D` lies in `cthickening(r+2/t,K)` because every surviving
edge belongs to a selected cell. -/
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

/-- **The thickening-selected reduced boundary avoids the compact set.** Let `K⊆ℂ` be compact,
`t>0`, and let `D` consist of all scale-`t` closed cells meeting `cthickening(r,K)`. For
any real `r`, the reduced trace of `D` is disjoint from `K`. No nonnegative-radius premise
occurs in this assertion. -/
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

/-- **The open grid square lies in its closed cell.** Let `D` be a finite grid filling of
scale `t>0`. For every index `v∈ℤ²`, the square with strict coordinate bounds
`v_i/t<x_i<(v_i+1)/t` is contained in the closed carrier of `D.cell(v)`. -/
theorem cellInterior_subset_carrier (D : GridFilling) (v : GridIndex) :
    D.cellInterior v ⊆ (D.cell v).carrier := by
  intro z hz
  rw [mem_cell_carrier_iff]
  exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩

/-- **A counterclockwise grid square has index one in its interior.** Let `D` be a finite grid
filling of scale `t>0`. If `z∈D.cellInterior(v)`, then
`(2πi)⁻¹∮_{boundary(D.cell(v))}(ζ-z)⁻¹ dζ=1`. -/
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

/-- **An interior point determines its grid cell uniquely.** Let `D` be a finite grid filling
of scale `t>0`. If `z` lies in the open square at index `v` and in the closed cell at
index `u`, then `u=v`. The strict interior bounds exclude shared boundary faces. -/
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

/-- **Grid index equals cell selection at an interior point.** Let `D` be a finite grid
filling of scale `t>0`. For `z∈D.cellInterior(v)`, the analytic winding index of
`D.toCycle` is the complex coercion of `c_D(v)`, equal to `1` for a selected cell and `0`
otherwise. -/
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

/-- **Floor-based owner of a complex point in a grid.** Let `D` be a finite grid filling of
scale `t>0`. For `z∈ℂ`, define the integer owner index `o_D(z)=(⌊t Re z⌋,⌊t Im z⌋)`. It
determines the unique sign-reversed half-open cell box containing `(-Re z,-Im z)`. -/
noncomputable def ownerIndex (D : GridFilling) (z : ℂ) : GridIndex :=
  fun i => if i = 0 then ⌊D.scale * z.re⌋ else ⌊D.scale * z.im⌋

/-- **Half-open cell membership identifies the floor-based owner.** Let `D` be a finite grid
filling of scale `t>0`. For `v∈ℤ²` and `z∈ℂ`, `(-Re z,-Im z)∈D.cellBox(v)` if and only if
`o_D(z)=v`, where `o_D(z)=(⌊t Re z⌋,⌊t Im z⌋)`. -/
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

/-- **Every complex point lies in its owner cell carrier.** Let `D` be a finite grid filling
of scale `t>0`. For each `z∈ℂ`, the closed square at `o_D(z)=(⌊t Re z⌋,⌊t Im z⌋)` contains
`z`. The owner index need not be selected in `D`. -/
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

/-- **A point lies in the closure of its owner square interior.** Let `D` be a finite grid
filling of scale `t>0`. Every `z∈ℂ` belongs to the closure of `D.cellInterior(o_D(z))`,
where `o_D(z)=(⌊t Re z⌋,⌊t Im z⌋)`. Boundary points are included through closure. -/
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

/-- **Interior points have the corresponding grid owner.** Let `D` be a finite grid filling of
scale `t>0`. If `z` lies in the open cell at `v∈ℤ²`, then `(⌊t Re z⌋,⌊t Im z⌋)=v`. -/
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

/-- **Selected-cell multiplicity at a complex point.** For a filling `D` of scale `t>0`, write
`o_D(z)=(⌊t Re z⌋,⌊t Im z⌋)` and `m_D(z)=1` if this owner cell is selected, `0` otherwise.
This integer-valued function is the selected-cell indicator evaluated at the floor-based
owner. Away from the reduced boundary it is constant on each connected component, and its
complex coercion equals the analytic winding index. -/
noncomputable def cellMultiplicity (D : GridFilling) (z : ℂ) : ℤ :=
  D.cellCoeff (D.ownerIndex z)

/-- **Cell multiplicity vanishes outside the selected region.** For a filling `D` of scale
`t>0`, write `o_D(z)=(⌊t Re z⌋,⌊t Im z⌋)` and `m_D(z)=1` if this owner cell is selected,
`0` otherwise. If `z` does not belong to the union of selected closed cell carriers, then
`m_D(z)=0`. -/
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

/-- **Multiplicity one means the owner cell is selected.** For a filling `D` of scale `t>0`,
write `o_D(z)=(⌊t Re z⌋,⌊t Im z⌋)` and `m_D(z)=1` if this owner cell is selected, `0`
otherwise. For every `z∈ℂ`, `m_D(z)=1` if and only if `o_D(z)∈D.cells`. This equality
includes points on cell boundaries under the fixed half-open owner convention. -/
theorem cellMultiplicity_eq_one_iff (D : GridFilling) (z : ℂ) :
    D.cellMultiplicity z = 1 ↔ D.ownerIndex z ∈ D.cells := by
  simp [cellMultiplicity, cellCoeff]

/-- **Grid multiplicity takes only the values zero and one.** For a filling `D` of scale
`t>0`, write `o_D(z)=(⌊t Re z⌋,⌊t Im z⌋)` and `m_D(z)=1` if this owner cell is selected,
`0` otherwise. At every complex point `z`, `m_D(z)=0` or `m_D(z)=1`, since it is an
integer selection indicator. -/
theorem cellMultiplicity_eq_zero_or_one (D : GridFilling) (z : ℂ) :
    D.cellMultiplicity z = 0 ∨ D.cellMultiplicity z = 1 := by
  simp only [cellMultiplicity, cellCoeff]
  split_ifs <;> simp

/-- **Thickening-selected multiplicity is one on the compact set.** Let `K⊆ℂ` be compact,
`t>0`, and let `D` consist of all scale-`t` closed cells meeting `cthickening(r,K)`. For
any real `r` and every `z∈K`, the floor-based owner cell is selected, hence `m_D(z)=1`. -/
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

/-- **Selected multiplicity vanishes outside the enlarged thickening.** Let `K⊆ℂ` be compact,
`t>0`, and let `D` consist of all scale-`t` closed cells meeting `cthickening(r,K)`. If
`r≥0` and `z∉cthickening(r+2/t,K)`, then `m_D(z)=0`. -/
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

/-- **Selected half-open union is detected by multiplicity.** For a filling `D` of scale
`t>0`, write `o_D(z)=(⌊t Re z⌋,⌊t Im z⌋)` and `m_D(z)=1` if this owner cell is selected,
`0` otherwise. Let `B` be a nondegenerate real box containing all selected cell boxes, and
let `π` be their prepartition in `B`. Then `(-Re z,-Im z)∈union(π)` if and only if
`m_D(z)=1`. -/
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

/-- **First multiplicity detects containment of an overlay box.** Let `D,H` be finite
positive-scale fillings and `I` a box in their common overlay prepartition. If `(-Re z,-Im
z)∈I`, then the first multiplicity `m_D(z)` is one exactly when `I` is contained in the
union of the first selected-cell prepartition. Here `m_D` is the selected indicator at its
floor-based owner. -/
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

/-- **Second multiplicity detects containment of an overlay box.** Let `D,H` be finite
positive-scale fillings and `I` a box in their common overlay prepartition. If `(-Re z,-Im
z)∈I`, then the second multiplicity `m_H(z)` is one exactly when `I` is contained in the
union of the second selected-cell prepartition. Multiplicity is the selected indicator at
the floor-based owner. -/
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

/-- **A signed overlay coefficient is the pointwise multiplicity difference.** Let `D,H` be
finite positive-scale fillings and `I` a box in their common overlay prepartition. If
`(-Re z,-Im z)∈I`, then `commonOverlay(D,H)(I)=m_D(z)-m_H(z)`, where each multiplicity is
the integer selection indicator at the corresponding floor-based owner. -/
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

/-- **Center of a positive-scale grid square.** Let `D` be a finite grid filling of scale
`t>0`. For `v∈ℤ²`, the cell center is `(v₀+1/2)/t+i(v₁+1/2)/t`. It lies halfway between
the two coordinate bounds of the cell. -/
noncomputable def cellCenter (D : GridFilling) (v : GridIndex) : ℂ :=
  (((v 0 : ℤ) : ℝ) / D.scale + 1 / (2 * D.scale) : ℂ) +
    (((v 1 : ℤ) : ℝ) / D.scale + 1 / (2 * D.scale) : ℂ) * Complex.I

/-- **Discrete residue identity for a finite grid filling.** For a filling `D` of scale `t>0`,
write `o_D(z)=(⌊t Re z⌋,⌊t Im z⌋)` and `m_D(z)=1` if this owner cell is selected, `0`
otherwise. The predicate requires, for every `z` off the reduced trace,
`index(D.toCycle,z)=(m_D(z):ℂ)`, where the analytic index is `(2πi)⁻¹∮(ζ-z)⁻¹ dζ`. -/
def HasDiscreteResidueFormula (D : GridFilling) : Prop :=
  ∀ z ∉ D.reducedTrace, D.toCycle.index z = (D.cellMultiplicity z : ℂ)

/-- **Analytic grid index equals discrete cell multiplicity.** For a filling `D` of scale
`t>0`, write `o_D(z)=(⌊t Re z⌋,⌊t Im z⌋)` and `m_D(z)=1` if this owner cell is selected,
`0` otherwise. For every `z` off the reduced trace, `(2πi)⁻¹∮_{D.toCycle}(ζ-z)⁻¹
dζ=(m_D(z):ℂ)`. Internal-edge cancellation makes the owner convention agree with the
analytic index there. -/
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

/-- **Winding index vanishes outside the selected grid region.** Let `D` be a finite grid
filling of scale `t>0`. If `z` lies outside the union of selected closed cell carriers,
then `D.toCycle.index(z)=0`. Such a point is also off the reduced trace. -/
theorem index_eq_zero_of_not_mem_region
    (D : GridFilling) {z : ℂ} (hz : z ∉ D.region) :
    D.toCycle.index z = 0 := by
  have hztrace : z ∉ D.reducedTrace := fun h =>
    hz (D.reducedTrace_subset_region h)
  rw [D.hasDiscreteResidueFormula z hztrace,
    D.cellMultiplicity_eq_zero_of_not_mem_region hz]
  simp

/-- **Empty filling at a positive grid scale.** For any `t>0`, take the finite grid filling
with scale `t` and no selected integer cells. The scale remains positive although its
region, cycle and reduced boundary are empty. -/
def empty (t : ℝ) (ht : 0 < t) : GridFilling where
  scale := t
  scale_pos := ht
  cells := ∅

/-- **The empty filling has no selected indices.** For `t>0`, the selected-cell set of the
empty scale-`t` filling is `∅`. -/
@[simp]
theorem empty_cells (t : ℝ) (ht : 0 < t) : (empty t ht).cells = ∅ := rfl

/-- **The empty filling has zero rectilinear cycle.** For `t>0`, summing the counterclockwise
boundaries of the empty selected-cell set gives the zero rectilinear cycle. -/
@[simp]
theorem empty_toCycle (t : ℝ) (ht : 0 < t) :
    (empty t ht).toCycle = 0 := by
  simp [toCycle]

/-- **The empty filling has no surviving boundary edges.** For `t>0`, every boundary
coefficient of the empty filling is zero, so its reduced edge set is `∅`. -/
@[simp]
theorem empty_boundaryEdges (t : ℝ) (ht : 0 < t) :
    (empty t ht).boundaryEdges = ∅ := by
  simp [boundaryEdges]

/-- **The empty filling has empty reduced trace.** For `t>0`, the union of surviving edge
segments of the empty filling is `∅`. -/
@[simp]
theorem empty_reducedTrace (t : ℝ) (ht : 0 < t) :
    (empty t ht).reducedTrace = ∅ := by
  simp [reducedTrace]

/-- **The empty filling has empty closed region.** For `t>0`, the union of its selected closed
grid cell carriers is `∅`. -/
@[simp]
theorem empty_region (t : ℝ) (ht : 0 < t) :
    (empty t ht).region = ∅ := by
  simp [region]

/-- **Every reduced integral of the empty filling is zero.** Let `E` be a complete complex
normed vector space, `t>0`, and `f:ℂ→E`. The reduced signed-edge integral of `f` over the
empty scale-`t` filling is `0`, with no continuity premise. -/
@[simp]
theorem empty_reducedIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (t : ℝ) (ht : 0 < t) (f : ℂ → E) :
    (empty t ht).reducedIntegral f = 0 := by
  simp [reducedIntegral]

/-- **Admissibility of a finite grid contour around a set.** For a finite positive-scale
filling `D` and arbitrary `K,G⊆ℂ`, admissibility means exactly: the reduced trace lies in
`G∖K`; `D.toCycle.index(z)=1` for every `z∈K`; and `D.toCycle.index(z)=0` for every `z∉G`.
Filled-region containment in `G` is a separate condition. -/
def IsAdmissibleFor (D : GridFilling) (K G : Set ℂ) : Prop :=
  D.reducedTrace ⊆ G \ K ∧
    (∀ z ∈ K, D.toCycle.index z = 1) ∧
    ∀ z ∉ G, D.toCycle.index z = 0

/-- **Admissibility persists under enlargement of the ambient set.** Let `D` be a finite
positive-scale filling and `K,G,H⊆ℂ`. Admissibility for `K` in `G` means reduced trace in
`G∖K`, index one on `K`, and index zero outside `G`. If `D` is admissible for `K` in `G`
and `G⊆H`, then it is admissible for `K` in `H`. -/
theorem IsAdmissibleFor.mono_right {D : GridFilling} {K G H : Set ℂ}
    (hD : D.IsAdmissibleFor K G) (hGH : G ⊆ H) : D.IsAdmissibleFor K H := by
  refine ⟨fun z hz ↦ ⟨hGH (hD.1 hz).1, (hD.1 hz).2⟩, hD.2.1, ?_⟩
  intro z hzH
  exact hD.2.2 z fun hzG ↦ hzH (hGH hzG)

/-- **Admissibility persists for a smaller index-one set.** Let `D` be a finite positive-scale
filling and `K,L,G⊆ℂ` with `K⊆L`. Admissibility for `K` in `G` means reduced trace in
`G∖K`, index one on `K`, and index zero outside `G`. If `D` is admissible for `L` in `G`,
then it is admissible for `K` in `G`. -/
theorem IsAdmissibleFor.mono_left {D : GridFilling} {K L G : Set ℂ}
    (hD : D.IsAdmissibleFor L G) (hKL : K ⊆ L) :
    D.IsAdmissibleFor K G := by
  refine ⟨fun z hz => ⟨(hD.1 hz).1, fun hzK => (hD.1 hz).2 (hKL hzK)⟩,
    fun z hzK => hD.2.1 z (hKL hzK), hD.2.2⟩

/-- **A compact set has an admissible finite grid inside an open neighborhood.** If `K⊆ℂ` is
compact, `G⊆ℂ` is open, and `K⊆G`, there exists a positive-scale finite filling `D`
admissible for `K` in `G` whose entire selected closed-cell region lies in `G`.
Admissibility for `K` in `G` means reduced trace in `G∖K`, index one on `K`, and index
zero outside `G`. The empty compact set is allowed. -/
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

/-- **Existence of an admissible finite grid around a compact set.** For compact `K⊆ℂ`
contained in open `G⊆ℂ`, there exists a positive-scale finite filling `D` with reduced
trace in `G∖K`, cycle index one on `K`, and index zero outside `G`. This existence
statement includes empty `K`. -/
theorem exists_isAdmissibleFor {K G : Set ℂ} (hK : IsCompact K)
    (hG : IsOpen G) (hKG : K ⊆ G) : ∃ D : GridFilling, D.IsAdmissibleFor K G := by
  obtain ⟨D, hD, -⟩ := exists_isAdmissibleFor_with_region_subset hK hG hKG
  exact ⟨D, hD⟩

/-- **Nested admissible grids around a compact set and an inner region.** For compact `K⊆ℂ`
contained in open `G⊆ℂ`, there exist positive-scale finite fillings `D,H` such that `D` is
admissible for `K` in `G` and `H` is admissible for `K∪D.region` in `G`. Admissibility for
`K` in `G` means reduced trace in `G∖K`, index one on `K`, and index zero outside `G`.
Thus the outer reduced trace avoids the whole inner region and its index is one there. -/
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

/-- **Pointwise support of the difference of grid multiplicities.** Let `D,H` be finite grid
fillings with positive, possibly different, scales. Write `m_D(z),m_H(z)∈{0,1}` for the
selected-cell indicators at each filling's floor-based owner, and `S={z∈ℂ |
m_D(z)≠m_H(z)}`. The difference support is exactly `S`, the support of the integer
function `m_D-m_H`. It is defined from pointwise multiplicity, rather than from the formal
support of rectangle presentations. -/
noncomputable def multiplicityDifferenceSupport (D E : GridFilling) : Set ℂ :=
  Function.support fun z ↦ D.cellMultiplicity z - E.cellMultiplicity z

/-- **Difference-support membership means unequal grid multiplicities.** Let `D,H` be finite
grid fillings with positive, possibly different, scales. Write `m_D(z),m_H(z)∈{0,1}` for
the selected-cell indicators at each filling's floor-based owner, and `S={z∈ℂ |
m_D(z)≠m_H(z)}`. For every `z∈ℂ`, membership in the difference support is equivalent to
`m_D(z)≠m_H(z)`. -/
theorem mem_multiplicityDifferenceSupport_iff (D E : GridFilling) (z : ℂ) :
    z ∈ D.multiplicityDifferenceSupport E ↔
      D.cellMultiplicity z ≠ E.cellMultiplicity z := by
  simp only [multiplicityDifferenceSupport, Function.mem_support]
  exact sub_ne_zero

/-- **The multiplicity-difference support is symmetric.** Let `D,H` be finite grid fillings
with positive, possibly different, scales. Write `m_D(z),m_H(z)∈{0,1}` for the
selected-cell indicators at each filling's floor-based owner, and `S={z∈ℂ |
m_D(z)≠m_H(z)}`. Interchanging `D,H` negates the integer difference but leaves its
pointwise support unchanged: `S(D,H)=S(H,D)`. -/
theorem multiplicityDifferenceSupport_comm (D E : GridFilling) :
    D.multiplicityDifferenceSupport E = E.multiplicityDifferenceSupport D := by
  ext z
  simp [mem_multiplicityDifferenceSupport_iff, ne_comm]

/-- **Every surviving overlay rectangle lies in the closed difference support.** Let `D,H` be
finite grid fillings with positive, possibly different, scales. Write
`m_D(z),m_H(z)∈{0,1}` for the selected-cell indicators at each filling's floor-based
owner, and `S={z∈ℂ | m_D(z)≠m_H(z)}`. If a nondegenerate box `I` has nonzero coefficient
in the common signed overlay, the closed carrier of its sign-reversed complex rectangle is
contained in `closure(S)`. -/
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

/-- **The signed overlay gives a filling supported in the closed difference support.** Let
`D,H` be finite grid fillings with positive, possibly different, scales. Write
`m_D(z),m_H(z)∈{0,1}` for the selected-cell indicators at each filling's floor-based
owner, and `S={z∈ℂ | m_D(z)≠m_H(z)}`. Every rectangle with nonzero coefficient in the
common-overlay cycle has its closed complex carrier in `closure(S)`. Hence that
rectilinear cycle is filled by rectangles supported there. -/
theorem commonOverlay_fillingSupportedIn (D E : GridFilling) :
    (D.commonOverlay E).toCycle.FillingSupportedIn
      (closure (D.multiplicityDifferenceSupport E)) := by
  intro r hr
  rw [BoxOverlayChain.toCycle, Finsupp.support_mapDomain_embedding] at hr
  rcases Finset.mem_map.1 hr with ⟨I, hI, rfl⟩
  exact D.commonOverlay_rectangle_carrier_subset E hI

/-- **Common signed filling away from an excluded set.** Let `D,H` be finite grid fillings
with positive, possibly different, scales. Write `m_D(z),m_H(z)∈{0,1}` for the
selected-cell indicators at each filling's floor-based owner, and `S={z∈ℂ |
m_D(z)≠m_H(z)}`. For arbitrary `K,G⊆ℂ`, the predicate is exactly `closure(S)⊆G∖K`. It
controls the closed support of the multiplicity difference and imposes no separate trace
hypothesis. -/
def HaveCommonFillingAwayFrom (D E : GridFilling) (K G : Set ℂ) : Prop :=
  closure (D.multiplicityDifferenceSupport E) ⊆ G \ K

/-- **Off both grid traces the difference support is relatively closed.** Let `D,H` be finite
grid fillings with positive, possibly different, scales. Write `m_D(z),m_H(z)∈{0,1}` for
the selected-cell indicators at each filling's floor-based owner, and `S={z∈ℂ |
m_D(z)≠m_H(z)}`. If `z∈closure(S)` and `z` lies on neither reduced trace, then `z∈S`, so
`m_D(z)≠m_H(z)`. -/
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

/-- **Closing the difference support adds points only on grid traces.** Let `D,H` be finite
grid fillings with positive, possibly different, scales. Write `m_D(z),m_H(z)∈{0,1}` for
the selected-cell indicators at each filling's floor-based owner, and `S={z∈ℂ |
m_D(z)≠m_H(z)}`. Then `closure(S)⊆S∪trace(D)∪trace(H)`, where each trace is the union of
surviving signed-edge segments. -/
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

/-- **Admissible grids have comparison support in the punctured domain.** Let `D,H` be finite
grid fillings with positive, possibly different, scales. Write `m_D(z),m_H(z)∈{0,1}` for
the selected-cell indicators at each filling's floor-based owner, and `S={z∈ℂ |
m_D(z)≠m_H(z)}`. Admissibility for `K` in `G` means reduced trace in `G∖K`, index one on
`K`, and index zero outside `G`. If both fillings are admissible for the same `K` in `G`,
then `closure(S)⊆G∖K`. No compactness or openness premise is needed for this comparison
theorem. -/
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

/-- **Closed carrier for comparing two grid contour integrals.** Let `D,H` be finite grid
fillings with positive, possibly different, scales. Write `m_D(z),m_H(z)∈{0,1}` for the
selected-cell indicators at each filling's floor-based owner, and `S={z∈ℂ |
m_D(z)≠m_H(z)}`. Define the comparison carrier `C=closure(S)∪trace(D)∪trace(H)`. It
includes the closed signed-overlay support and both reduced contours on which an integrand
must be retained. -/
noncomputable def comparisonCarrier (D E : GridFilling) : Set ℂ :=
  closure (D.multiplicityDifferenceSupport E) ∪
    D.reducedTrace ∪ E.reducedTrace

/-- **The grid comparison carrier is closed.** Let `D,H` be finite grid fillings with
positive, possibly different, scales. Write `m_D(z),m_H(z)∈{0,1}` for the selected-cell
indicators at each filling's floor-based owner, and `S={z∈ℂ | m_D(z)≠m_H(z)}`. The set
`C=closure(S)∪trace(D)∪trace(H)` is closed in `ℂ`, since each reduced trace is a finite
union of closed segments. -/
theorem isClosed_comparisonCarrier (D E : GridFilling) :
    IsClosed (D.comparisonCarrier E) :=
  (isClosed_closure.union D.isClosed_reducedTrace).union E.isClosed_reducedTrace

/-- **The comparison carrier lies in the punctured domain under trace and filling
conditions.** Let `D,H` be finite grid fillings with positive, possibly different, scales.
Write `m_D(z),m_H(z)∈{0,1}` for the selected-cell indicators at each filling's floor-based
owner, and `S={z∈ℂ | m_D(z)≠m_H(z)}`. Let `K,G⊆ℂ`. If both reduced traces lie in `G∖K` and
`closure(S)⊆G∖K`, then `C=closure(S)∪trace(D)∪trace(H)` also lies in `G∖K`. -/
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

/-- **A scalar integrand extends continuously while retaining its comparison values.** Let
`D,H` be finite grid fillings with positive, possibly different, scales. Write
`m_D(z),m_H(z)∈{0,1}` for the selected-cell indicators at each filling's floor-based
owner, and `S={z∈ℂ | m_D(z)≠m_H(z)}`. Let `C=closure(S)∪trace(D)∪trace(H)`. If `C⊆U⊆ℂ` and
`f:ℂ→ℂ` is continuous on `U`, there exists globally continuous `g:ℂ→ℂ` with `g=f` on `C`.
No openness or boundedness premise on `U` is required. -/
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

/-- **Scalar grid integrals agree under a common signed filling.** Let `D,H` be finite grid
fillings with positive, possibly different, scales. Write `m_D(z),m_H(z)∈{0,1}` for the
selected-cell indicators at each filling's floor-based owner, and `S={z∈ℂ |
m_D(z)≠m_H(z)}`. For `K,G⊆ℂ`, assume both reduced traces lie in `G∖K` and
`closure(S)⊆G∖K`. If `f:ℂ→ℂ` is complex differentiable on `G∖K`, then `∮_{D.toCycle}
f=∮_{H.toCycle} f`. Openness and compactness are not additional hypotheses. -/
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

/-- **Banach-valued grid integrals agree under a common signed filling.** Let `F` be a
complete complex normed vector space. Let `D,H` be finite grid fillings with positive,
possibly different, scales. Write `m_D(z),m_H(z)∈{0,1}` for the selected-cell indicators
at each filling's floor-based owner, and `S={z∈ℂ | m_D(z)≠m_H(z)}`. For `K,G⊆ℂ`, assume
both reduced traces lie in `G∖K` and `closure(S)⊆G∖K`. If `f:ℂ→F` is complex
differentiable on `G∖K`, then `∮_{D.toCycle} f=∮_{H.toCycle} f`. The target need not be an
algebra. -/
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

/-- **Admissible grids give the same Banach-valued contour integral.** Let `F` be a complete
complex normed vector space and `D,H` finite positive-scale fillings. Admissibility for
`K` in `G` means reduced trace in `G∖K`, index one on `K`, and index zero outside `G`. If
both are admissible for the same `K,G⊆ℂ` and `f:ℂ→F` is complex differentiable on `G∖K`,
then `∮_{D.toCycle} f=∮_{H.toCycle} f`. No extra compactness or openness premise is
imposed. -/
theorem integral_eq_of_isAdmissibleFor {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {D E : GridFilling} {K G : Set ℂ} {f : ℂ → F}
    (hD : D.IsAdmissibleFor K G) (hE : E.IsAdmissibleFor K G)
    (hf : DifferentiableOn ℂ f (G \ K)) :
    D.toCycle.integral f = E.toCycle.integral f :=
  integral_eq_of_haveCommonFillingAwayFrom hD.1 hE.1
    (haveCommonFillingAwayFrom_of_isAdmissibleFor hD hE) hf

/-- **The common-filling-away-from condition is symmetric.** Let `D,H` be finite grid fillings
with positive, possibly different, scales. Write `m_D(z),m_H(z)∈{0,1}` for the
selected-cell indicators at each filling's floor-based owner, and `S={z∈ℂ |
m_D(z)≠m_H(z)}`. For arbitrary `K,G⊆ℂ`, `closure(S(D,H))⊆G∖K` if and only if
`closure(S(H,D))⊆G∖K`. -/
theorem haveCommonFillingAwayFrom_comm (D E : GridFilling) (K G : Set ℂ) :
    D.HaveCommonFillingAwayFrom E K G ↔ E.HaveCommonFillingAwayFrom D K G := by
  rw [HaveCommonFillingAwayFrom, HaveCommonFillingAwayFrom,
    multiplicityDifferenceSupport_comm]

/-- **A filling compares with itself away from every excluded set.** For a finite
positive-scale filling `D` and arbitrary `K,G⊆ℂ`, its multiplicity difference with itself
is zero. Thus its closed difference support is empty and lies in `G∖K`. -/
theorem haveCommonFillingAwayFrom_self (D : GridFilling) (K G : Set ℂ) :
    D.HaveCommonFillingAwayFrom D K G := by
  simp [HaveCommonFillingAwayFrom, multiplicityDifferenceSupport]

/-- **Common-filling support gives equal multiplicities outside the punctured domain.** Let
`D,H` be finite grid fillings with positive, possibly different, scales. Write
`m_D(z),m_H(z)∈{0,1}` for the selected-cell indicators at each filling's floor-based
owner, and `S={z∈ℂ | m_D(z)≠m_H(z)}`. If `closure(S)⊆G∖K` and `z∉G∖K`, then
`m_D(z)=m_H(z)`. No exclusion of the reduced traces is needed for this integer equality. -/
theorem cellMultiplicity_eq_of_haveCommonFillingAwayFrom
    {D E : GridFilling} {K G : Set ℂ} (hDE : D.HaveCommonFillingAwayFrom E K G)
    {z : ℂ} (hz : z ∉ G \ K) : D.cellMultiplicity z = E.cellMultiplicity z := by
  by_contra hne
  apply hz
  apply hDE
  exact subset_closure ((D.mem_multiplicityDifferenceSupport_iff E z).2 hne)

/-- **Common-filling support gives equal winding indices off both traces.** Let `D,H` be
finite grid fillings with positive, possibly different, scales. Write
`m_D(z),m_H(z)∈{0,1}` for the selected-cell indicators at each filling's floor-based
owner, and `S={z∈ℂ | m_D(z)≠m_H(z)}`. If `closure(S)⊆G∖K`, `z∉G∖K`, and `z` lies on
neither reduced trace, then `D.toCycle.index(z)=H.toCycle.index(z)`. The trace exclusions
allow the discrete residue formula to identify each index with its multiplicity. -/
theorem index_eq_of_haveCommonFillingAwayFrom
    {D E : GridFilling} {K G : Set ℂ} (hDE : D.HaveCommonFillingAwayFrom E K G)
    {z : ℂ} (hz : z ∉ G \ K) (hzD : z ∉ D.reducedTrace)
    (hzE : z ∉ E.reducedTrace) : D.toCycle.index z = E.toCycle.index z := by
  rw [D.hasDiscreteResidueFormula z hzD, E.hasDiscreteResidueFormula z hzE]
  exact_mod_cast cellMultiplicity_eq_of_haveCommonFillingAwayFrom hDE hz

/-- **Admissible common fillings have equal indices outside the punctured domain.** Let `D,H`
be finite grid fillings with positive, possibly different, scales. Write
`m_D(z),m_H(z)∈{0,1}` for the selected-cell indicators at each filling's floor-based
owner, and `S={z∈ℂ | m_D(z)≠m_H(z)}`. Admissibility for `K` in `G` means reduced trace in
`G∖K`, index one on `K`, and index zero outside `G`. If both fillings are admissible for
`K` in `G`, their common-filling-away-from condition holds, and `z∉G∖K`, then their
analytic winding indices at `z` are equal. Admissibility places both reduced traces inside
`G∖K`. -/
theorem index_eq_of_haveCommonFillingAwayFrom_of_isAdmissibleFor
    {D E : GridFilling} {K G : Set ℂ} (hD : D.IsAdmissibleFor K G)
    (hE : E.IsAdmissibleFor K G) (hDE : D.HaveCommonFillingAwayFrom E K G)
    {z : ℂ} (hz : z ∉ G \ K) : D.toCycle.index z = E.toCycle.index z := by
  apply index_eq_of_haveCommonFillingAwayFrom hDE hz
  · exact fun hzD ↦ hz (hD.1 hzD)
  · exact fun hzE ↦ hz (hE.1 hzE)

/-- **An empty grid is admissible for the empty set in every domain.** For any `t>0` and
`G⊆ℂ`, the empty scale-`t` filling has empty reduced trace and zero index everywhere. It
is therefore admissible for `K=∅` in `G`, with the index-one requirement vacuous. -/
theorem empty_isAdmissibleFor_empty (t : ℝ) (ht : 0 < t) (G : Set ℂ) :
    (empty t ht).IsAdmissibleFor ∅ G := by
  simp [IsAdmissibleFor]

end GridFilling
