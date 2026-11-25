/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Topology/HouseWithTwoRooms.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), problem `contractibleSpace_houseWithTwoRooms`, at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/contractibleSpace_houseWithTwoRooms.toml`, rev 1, submitter Junyan Xu, status
archived): the definition `HouseWithTwoRooms` and the statement of
`contractibleSpace_houseWithTwoRooms`, with the docstrings and comments they had in the former
wanted module `WantedExt/Topology/HouseWithTwoRoomsWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Junyan Xu
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: converted each
`@[eval_problem]` theorem into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, inlined any
`LeanEval` helper modules, and placed the declarations in the
`MathlibExt.Topology.HouseWithTwoRoomsWanted` namespace. Mathematical statements are unchanged.
Later change (ATLAS, 2026): the `theorem_wanted` was proved and the declarations moved from
`WantedExt/Topology/HouseWithTwoRoomsWanted.lean` to this `MathlibExt` module with unchanged
names, statements and docstrings, and the import of `Batteries.Util.ProofWanted` was dropped.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of
`contractibleSpace_houseWithTwoRooms`, the private definitions and lemmas it uses, the module
documentation and the linter options.
-/
module

public import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Bing's house with two rooms is contractible

Bing's house with two rooms is contractible.

We use the construction on p.4 of Allen Hatcher, *Algebraic Topology*.
The three coordinate axes are horizontal, diagonal and vertical towards
the east, northeast and north directions respectively, with the origin
located at the southwest corner.

The main result is `contractibleSpace_houseWithTwoRooms`: the subspace `HouseWithTwoRooms` of
`ℝ × ℝ × ℝ` is contractible.

## Proof outline

* The house lies in the box `[0,4] × [0,3] × [0,2]`, and it is a retract of this box: some map,
  continuous on the box, sends the box into the house and fixes every point of the house. The box
  is convex, hence contractible, and a retract `ρ ∘ ι = id` of a contractible space is
  contractible, since `id = ρ ∘ id ∘ ι` is then nullhomotopic.
* The retraction collapses the solid box onto the house through fourteen boxes with integer
  corners, which together cover the solid box. Each box `B` comes with a free face: its interior
  and the relative interior of that face meet neither the house nor the boxes collapsed after
  `B`, and its other five faces lie in the house and in the later boxes. The radial projection
  from a point beyond the free face retracts `B` onto these five faces; extended by the identity
  outside `B`, it maps the house, `B` and the later boxes continuously (by the pasting lemma for
  closed sets) onto the house and the later boxes. The composite of the fourteen steps is the
  retraction.
* The first seven boxes fill the lower room and the tube leading down to it from the hole in the
  top floor, starting with `[1,2] × [1,2] × [0,2]`, which is removed through that hole; the last
  seven fill the upper room and the tube leading up to it from the hole in the ground floor,
  starting with `[2,3] × [1,2] × [0,2]`.

## Implementation notes

Each box retraction is computed coordinate by coordinate: after the box is rescaled to
`[-1,1]³`, the radial projection from the point at distance `2` beyond the centre of the free
face multiplies the transverse coordinates by `4 / M` and moves the normal coordinate
accordingly, where `M` is the maximum of one quantity per coordinate. The quantity of a free
direction is at least `2` on the box, which keeps `M` away from `0`, so the same formula serves
for every orientation of the free face.

The conditions on the fourteen boxes and the cover of the solid box are checked by `decide` on
the integer data: a closed box misses the interior and the free face of another box as soon as
one coordinate separates them, and a face lies in a union of boxes with integer corners as soon
as each of its closed unit cells lies in one of the boxes. By hand, the house is identified
with a union of twenty-three rectangles.

The two declarations keep the full names they had in the former wanted module, so their
namespace repeats `Topology`; the `dupNamespace` linter is turned off for these two declarations
only.

## References

* Allen Hatcher, *Algebraic Topology*, p. 4: the construction of the house used here. This is the
  source cited by problem `contractibleSpace_houseWithTwoRooms` of the lean-eval benchmark
  (leanprover/lean-eval), from which the definition and the statement are taken.
-/

@[expose] public section

namespace MathlibExt.Topology.HouseWithTwoRoomsWanted
namespace Topology

open Set (Icc Ioo)

set_option linter.dupNamespace false in
/-- **Bing's house with two rooms.** Bing's house with two rooms, in the version drawn in
Hatcher's *Algebraic Topology*, is the subset $H$ of $\mathbb{R} \times \mathbb{R} \times
\mathbb{R}$ consisting of the points of $[0,4] \times [0,3] \times \{0,1,2\}$ that lie in none of
$(2,3) \times (1,2) \times \{0\}$, $(1,3) \times (1,2) \times \{1\}$ and
$(1,2) \times (1,2) \times \{2\}$ (three floors with holes), together with the inner walls
$\{1\} \times [1,2] \times [1,2]$, $\{2\} \times [1,3] \times [0,2]$,
$\{3\} \times [1,2] \times [0,1]$, $[1,2] \times \{1,2\} \times [1,2]$ and
$[2,3] \times \{1,2\} \times [0,1]$, and the outer walls $[0,4] \times \{0,3\} \times [0,2]$ and
$\{0,4\} \times [0,3] \times [0,2]$. -/
def HouseWithTwoRooms : Set (ℝ × ℝ × ℝ) :=
  (Icc 0 4 ×ˢ Icc 0 3 ×ˢ {0, 1, 2} \
    (Ioo 2 3 ×ˢ Ioo 1 2 ×ˢ {0} ∪ Ioo 1 3 ×ˢ Ioo 1 2 ×ˢ {1} ∪ Ioo 1 2 ×ˢ Ioo 1 2 ×ˢ {2})) ∪
  ({1} ×ˢ Icc 1 2 ×ˢ Icc 1 2 ∪ {2} ×ˢ Icc 1 3 ×ˢ Icc 0 2 ∪ {3} ×ˢ Icc 1 2 ×ˢ Icc 0 1 ∪
    Icc 1 2 ×ˢ {1, 2} ×ˢ Icc 1 2 ∪ Icc 2 3 ×ˢ {1, 2} ×ˢ Icc 0 1) ∪
  (Icc 0 4 ×ˢ {0, 3} ×ˢ Icc 0 2 ∪ {0, 4} ×ˢ Icc 0 3 ×ˢ Icc 0 2)

open Set

/-! ### One coordinate of a box retraction -/

/-- The kind of the interval cut out by a box in one coordinate direction, in its open part
(interior plus free faces): open for a direction without free face, and closed at the end of a
free face otherwise. -/
private inductive Kind
  /-- No free face in this direction. -/
  | ioo
  /-- A free face at the lower end. -/
  | ico
  /-- A free face at the upper end. -/
  | ioc

/-- The interval of kind `k` with endpoints `a` and `b`. -/
private def Kind.toSet : Kind → ℝ → ℝ → Set ℝ
  | .ioo, a, b => Ioo a b
  | .ico, a, b => Ico a b
  | .ioc, a, b => Ioc a b

/-- Whether a direction has no free face. -/
private def Kind.isIoo : Kind → Bool
  | .ioo => true
  | _ => false

/-- The contribution of a normalised coordinate `n ∈ [-1, 1]` to the denominator of the radial
projection: `4 |n|` for a direction without free face, and `3 ∓ n` (the distance to the centre
of projection, rescaled) in the free direction. -/
private def Kind.weight : Kind → ℝ → ℝ
  | .ioo, n => 4 * |n|
  | .ico, n => 3 + n
  | .ioc, n => 3 - n

/-- The normalised coordinate `n` after the radial projection with scaling factor `t`. -/
private def Kind.upd : Kind → ℝ → ℝ → ℝ
  | .ioo, t, n => t * n
  | .ico, t, n => t * (3 + n) - 3
  | .ioc, t, n => 3 - t * (3 - n)

private lemma Kind.continuous_weight (k : Kind) : Continuous fun n => k.weight n := by
  cases k <;> simp only [Kind.weight] <;> fun_prop

private lemma Kind.continuous_upd (k : Kind) : Continuous fun p : ℝ × ℝ => k.upd p.1 p.2 := by
  cases k <;> simp only [Kind.upd] <;> fun_prop

private lemma Kind.weight_le_four (k : Kind) {n : ℝ} (hn : n ∈ Icc (-1 : ℝ) 1) :
    k.weight n ≤ 4 := by
  obtain ⟨h1, h2⟩ := hn
  cases k <;> simp only [Kind.weight]
  · have := abs_le.mpr ⟨h1, h2⟩; linarith
  · linarith
  · linarith

private lemma Kind.two_le_weight {k : Kind} (hk : k.isIoo = false) {n : ℝ}
    (hn : n ∈ Icc (-1 : ℝ) 1) : 2 ≤ k.weight n := by
  obtain ⟨h1, h2⟩ := hn
  cases k
  · simp [Kind.isIoo] at hk
  · simp only [Kind.weight]; linarith
  · simp only [Kind.weight]; linarith

private lemma Kind.upd_mem {k : Kind} {n M : ℝ} (hn : n ∈ Icc (-1 : ℝ) 1) (hle : k.weight n ≤ M)
    (hM4 : M ≤ 4) (hM : 0 < M) : k.upd (4 / M) n ∈ Icc (-1 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := hn
  cases k <;> simp only [Kind.weight] at hle <;> simp only [Kind.upd, mem_Icc]
  · have habs : |4 / M * n| ≤ 1 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / M), div_mul_eq_mul_div,
        div_le_one hM]
      linarith
    exact abs_le.mp habs
  · rw [div_mul_eq_mul_div, le_sub_iff_add_le, sub_le_iff_le_add, le_div_iff₀ hM,
      div_le_iff₀ hM]
    constructor <;> linarith
  · rw [div_mul_eq_mul_div, le_sub_comm, sub_le_comm, le_div_iff₀ hM, div_le_iff₀ hM]
    constructor <;> linarith

private lemma Kind.upd_notMem {k : Kind} {n M : ℝ} (heq : k.weight n = M) (hM : 0 < M) :
    k.upd (4 / M) n ∉ k.toSet (-1) 1 := by
  cases k <;> simp only [Kind.weight] at heq <;> simp only [Kind.upd, Kind.toSet]
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy n 0 with hneg | hzero | hpos
    · rw [abs_of_neg hneg] at heq
      have : 4 / M * n = -1 := by rw [div_mul_eq_mul_div, div_eq_iff hM.ne']; linarith
      linarith
    · subst hzero; simp at heq; linarith
    · rw [abs_of_pos hpos] at heq
      have : 4 / M * n = 1 := by rw [div_mul_eq_mul_div, div_eq_iff hM.ne']; linarith
      linarith
  · rintro ⟨h1, h2⟩
    have : 4 / M * (3 + n) = 4 := by rw [heq, div_mul_cancel₀ _ hM.ne']
    linarith
  · rintro ⟨h1, h2⟩
    have : 4 / M * (3 - n) = 4 := by rw [heq, div_mul_cancel₀ _ hM.ne']
    linarith

private lemma Kind.weight_eq_four {k : Kind} {n : ℝ} (hn : n ∈ Icc (-1 : ℝ) 1)
    (hno : n ∉ k.toSet (-1) 1) : k.weight n = 4 := by
  obtain ⟨h1, h2⟩ := hn
  cases k <;>
    simp only [Kind.toSet, mem_Ioo, mem_Ico, mem_Ioc, not_and_or, not_lt, not_le] at hno <;>
    simp only [Kind.weight]
  · rcases hno with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  · rcases hno with h | h <;> linarith
  · rcases hno with h | h <;> linarith

private lemma Kind.upd_one (k : Kind) (n : ℝ) : k.upd 1 n = n := by
  cases k <;> simp only [Kind.upd] <;> ring

/-- The affine map sending `[a, b]` onto `[-1, 1]`. -/
private noncomputable def nrm (a b t : ℝ) : ℝ := (2 * t - a - b) / (b - a)

/-- The affine map sending `[-1, 1]` onto `[a, b]`, inverse to `nrm a b` when `a < b`. -/
private noncomputable def dnm (a b s : ℝ) : ℝ := (a + b) / 2 + (b - a) / 2 * s

private lemma dnm_nrm {a b : ℝ} (h : a < b) (t : ℝ) : dnm a b (nrm a b t) = t := by
  have : b - a ≠ 0 := (sub_pos.mpr h).ne'
  unfold dnm nrm; field_simp; ring

private lemma nrm_dnm {a b : ℝ} (h : a < b) (s : ℝ) : nrm a b (dnm a b s) = s := by
  have : b - a ≠ 0 := (sub_pos.mpr h).ne'
  unfold dnm nrm; field_simp; ring

private lemma continuous_nrm (a b : ℝ) : Continuous (nrm a b) := by unfold nrm; fun_prop

private lemma continuous_dnm (a b : ℝ) : Continuous (dnm a b) := by unfold dnm; fun_prop

private lemma nrm_mem_Icc_iff {a b : ℝ} (h : a < b) (t : ℝ) :
    nrm a b t ∈ Icc (-1 : ℝ) 1 ↔ t ∈ Icc a b := by
  have hba : 0 < b - a := sub_pos.mpr h
  simp only [nrm, mem_Icc, le_div_iff₀ hba, div_le_iff₀ hba]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

private lemma nrm_mem_toSet_iff {a b : ℝ} (h : a < b) (k : Kind) (t : ℝ) :
    nrm a b t ∈ k.toSet (-1) 1 ↔ t ∈ k.toSet a b := by
  have hba : 0 < b - a := sub_pos.mpr h
  cases k <;>
    simp only [Kind.toSet, nrm, mem_Ioo, mem_Ico, mem_Ioc, le_div_iff₀ hba, div_le_iff₀ hba,
      lt_div_iff₀ hba, div_lt_iff₀ hba] <;>
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The weight of a coordinate `q ∈ [a, b]`, computed in normalised form. -/
private noncomputable def weight1 (k : Kind) (a b q : ℝ) : ℝ := k.weight (nrm a b q)

/-- A coordinate `q ∈ [a, b]` after the radial projection with scaling factor `t`. -/
private noncomputable def retr1 (k : Kind) (a b t q : ℝ) : ℝ := dnm a b (k.upd t (nrm a b q))

private lemma continuous_weight1 (k : Kind) (a b : ℝ) : Continuous (weight1 k a b) :=
  k.continuous_weight.comp (continuous_nrm a b)

private lemma continuous_retr1 (k : Kind) (a b : ℝ) :
    Continuous fun p : ℝ × ℝ => retr1 k a b p.1 p.2 :=
  (continuous_dnm a b).comp <| k.continuous_upd.comp <|
    continuous_fst.prodMk ((continuous_nrm a b).comp continuous_snd)

private lemma weight1_le_four (k : Kind) {a b q : ℝ} (h : a < b) (hq : q ∈ Icc a b) :
    weight1 k a b q ≤ 4 :=
  k.weight_le_four ((nrm_mem_Icc_iff h q).mpr hq)

private lemma two_le_weight1 {k : Kind} (hk : k.isIoo = false) {a b q : ℝ} (h : a < b)
    (hq : q ∈ Icc a b) : 2 ≤ weight1 k a b q :=
  Kind.two_le_weight hk ((nrm_mem_Icc_iff h q).mpr hq)

private lemma retr1_mem {k : Kind} {a b q M : ℝ} (h : a < b) (hq : q ∈ Icc a b)
    (hle : weight1 k a b q ≤ M) (hM4 : M ≤ 4) (hM : 0 < M) :
    retr1 k a b (4 / M) q ∈ Icc a b := by
  rw [← nrm_mem_Icc_iff h, retr1, nrm_dnm h]
  exact Kind.upd_mem ((nrm_mem_Icc_iff h q).mpr hq) hle hM4 hM

private lemma retr1_notMem {k : Kind} {a b q M : ℝ} (h : a < b) (heq : weight1 k a b q = M)
    (hM : 0 < M) : retr1 k a b (4 / M) q ∉ k.toSet a b := by
  rw [← nrm_mem_toSet_iff h, retr1, nrm_dnm h]
  exact Kind.upd_notMem heq hM

private lemma weight1_eq_four {k : Kind} {a b q : ℝ} (h : a < b) (hq : q ∈ Icc a b)
    (hno : q ∉ k.toSet a b) : weight1 k a b q = 4 :=
  Kind.weight_eq_four ((nrm_mem_Icc_iff h q).mpr hq) (by rwa [nrm_mem_toSet_iff h])

private lemma retr1_one (k : Kind) {a b : ℝ} (h : a < b) (q : ℝ) : retr1 k a b 1 q = q := by
  rw [retr1, Kind.upd_one, dnm_nrm h]

/-! ### Boxes with natural-number corners -/

/-- A box `[x0, x1] × [y0, y1] × [z0, z1]` with natural-number corners, possibly degenerate. -/
private structure IBox where
  /-- The lower `x`-coordinate. -/
  x0 : ℕ
  /-- The upper `x`-coordinate. -/
  x1 : ℕ
  /-- The lower `y`-coordinate. -/
  y0 : ℕ
  /-- The upper `y`-coordinate. -/
  y1 : ℕ
  /-- The lower `z`-coordinate. -/
  z0 : ℕ
  /-- The upper `z`-coordinate. -/
  z1 : ℕ

/-- The points of a box. -/
private def IBox.toSet (b : IBox) : Set (ℝ × ℝ × ℝ) :=
  Icc (b.x0 : ℝ) b.x1 ×ˢ Icc (b.y0 : ℝ) b.y1 ×ˢ Icc (b.z0 : ℝ) b.z1

private lemma IBox.isClosed_toSet (b : IBox) : IsClosed b.toSet :=
  isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc)

/-- The union of a list of boxes. -/
private def boxesUnion : List IBox → Set (ℝ × ℝ × ℝ)
  | [] => ∅
  | b :: bs => b.toSet ∪ boxesUnion bs

private lemma isClosed_boxesUnion : ∀ bs : List IBox, IsClosed (boxesUnion bs)
  | [] => isClosed_empty
  | b :: bs => b.isClosed_toSet.union (isClosed_boxesUnion bs)

private lemma mem_boxesUnion {q : ℝ × ℝ × ℝ} :
    ∀ {bs : List IBox}, q ∈ boxesUnion bs ↔ ∃ b ∈ bs, q ∈ b.toSet
  | [] => by simp [boxesUnion]
  | b :: bs => by simp [boxesUnion, mem_boxesUnion]

private lemma boxesUnion_append (bs cs : List IBox) :
    boxesUnion (bs ++ cs) = boxesUnion bs ∪ boxesUnion cs := by
  ext q
  simp only [mem_union, mem_boxesUnion, List.mem_append]
  constructor
  · rintro ⟨b, hb | hb, hq⟩
    · exact Or.inl ⟨b, hb, hq⟩
    · exact Or.inr ⟨b, hb, hq⟩
  · rintro (⟨b, hb, hq⟩ | ⟨b, hb, hq⟩)
    · exact ⟨b, Or.inl hb, hq⟩
    · exact ⟨b, Or.inr hb, hq⟩

private lemma mem_boxesUnion_of {b : IBox} {bs : List IBox} (hb : b ∈ bs) {x y z : ℝ}
    (h1 : (b.x0 : ℝ) ≤ x) (h2 : x ≤ b.x1) (h3 : (b.y0 : ℝ) ≤ y) (h4 : y ≤ b.y1)
    (h5 : (b.z0 : ℝ) ≤ z) (h6 : z ≤ b.z1) : (x, y, z) ∈ boxesUnion bs :=
  mem_boxesUnion.mpr ⟨b, hb, ⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩

/-! ### Collapsing one box through its free faces -/

/-- A collapse step: a box together with the kind of each coordinate direction, which records
its free faces. -/
private structure Step where
  /-- The box removed by the step. -/
  box : IBox
  /-- The kind of the `x`-direction. -/
  kx : Kind
  /-- The kind of the `y`-direction. -/
  ky : Kind
  /-- The kind of the `z`-direction. -/
  kz : Kind

/-- The interior of the box together with the relative interiors of its free faces. -/
private def Step.core (s : Step) : Set (ℝ × ℝ × ℝ) :=
  s.kx.toSet s.box.x0 s.box.x1 ×ˢ s.ky.toSet s.box.y0 s.box.y1 ×ˢ s.kz.toSet s.box.z0 s.box.z1

/-- The denominator of the radial projection of a step. -/
private noncomputable def Step.gauge (s : Step) (q : ℝ × ℝ × ℝ) : ℝ :=
  max (weight1 s.kx s.box.x0 s.box.x1 q.1)
    (max (weight1 s.ky s.box.y0 s.box.y1 q.2.1) (weight1 s.kz s.box.z0 s.box.z1 q.2.2))

/-- The radial projection of a box onto its faces that are not free. -/
private noncomputable def Step.retr (s : Step) (q : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (retr1 s.kx s.box.x0 s.box.x1 (4 / s.gauge q) q.1,
    retr1 s.ky s.box.y0 s.box.y1 (4 / s.gauge q) q.2.1,
    retr1 s.kz s.box.z0 s.box.z1 (4 / s.gauge q) q.2.2)

/-- A step is nondegenerate if its box is a solid box with at least one free face. -/
private structure Step.Nondeg (s : Step) : Prop where
  hx : (s.box.x0 : ℝ) < s.box.x1
  hy : (s.box.y0 : ℝ) < s.box.y1
  hz : (s.box.z0 : ℝ) < s.box.z1
  hk : s.kx.isIoo = false ∨ s.ky.isIoo = false ∨ s.kz.isIoo = false

private lemma Step.continuous_gauge (s : Step) : Continuous s.gauge :=
  ((continuous_weight1 _ _ _).comp continuous_fst).max
    (((continuous_weight1 _ _ _).comp (continuous_fst.comp continuous_snd)).max
      ((continuous_weight1 _ _ _).comp (continuous_snd.comp continuous_snd)))

private lemma Step.gauge_le_four {s : Step} (hs : s.Nondeg) {q : ℝ × ℝ × ℝ}
    (hq : q ∈ s.box.toSet) : s.gauge q ≤ 4 :=
  max_le (weight1_le_four _ hs.hx hq.1)
    (max_le (weight1_le_four _ hs.hy hq.2.1) (weight1_le_four _ hs.hz hq.2.2))

private lemma Step.two_le_gauge {s : Step} (hs : s.Nondeg) {q : ℝ × ℝ × ℝ}
    (hq : q ∈ s.box.toSet) : 2 ≤ s.gauge q := by
  rcases hs.hk with h | h | h
  · exact le_max_of_le_left (two_le_weight1 h hs.hx hq.1)
  · exact le_max_of_le_right (le_max_of_le_left (two_le_weight1 h hs.hy hq.2.1))
  · exact le_max_of_le_right (le_max_of_le_right (two_le_weight1 h hs.hz hq.2.2))

private lemma Step.continuousOn_retr {s : Step} (hs : s.Nondeg) :
    ContinuousOn s.retr s.box.toSet := by
  have ht : ContinuousOn (fun q => 4 / s.gauge q) s.box.toSet :=
    continuousOn_const.div s.continuous_gauge.continuousOn fun _ hq =>
      (lt_of_lt_of_le two_pos (s.two_le_gauge hs hq)).ne'
  have key : ∀ (k : Kind) (a b : ℝ) (f : ℝ × ℝ × ℝ → ℝ), Continuous f →
      ContinuousOn (fun q => retr1 k a b (4 / s.gauge q) (f q)) s.box.toSet := by
    intro k a b f hf
    -- elaborating the composite first avoids a costly higher-order unification
    have h := (continuous_retr1 k a b).comp_continuousOn (ht.prodMk hf.continuousOn)
    exact h
  exact (key _ _ _ _ continuous_fst).prodMk
    ((key _ _ _ _ (continuous_fst.comp continuous_snd)).prodMk
      (key _ _ _ _ (continuous_snd.comp continuous_snd)))

private lemma Step.mapsTo_retr {s : Step} (hs : s.Nondeg) :
    MapsTo s.retr s.box.toSet (s.box.toSet \ s.core) := by
  intro q hq
  have hM : 0 < s.gauge q := lt_of_lt_of_le two_pos (s.two_le_gauge hs hq)
  have hM4 := s.gauge_le_four hs hq
  have h1 : weight1 s.kx s.box.x0 s.box.x1 q.1 ≤ s.gauge q := le_max_left _ _
  have h2 : weight1 s.ky s.box.y0 s.box.y1 q.2.1 ≤ s.gauge q :=
    le_max_of_le_right (le_max_left _ _)
  have h3 : weight1 s.kz s.box.z0 s.box.z1 q.2.2 ≤ s.gauge q :=
    le_max_of_le_right (le_max_right _ _)
  refine ⟨⟨retr1_mem hs.hx hq.1 h1 hM4 hM, retr1_mem hs.hy hq.2.1 h2 hM4 hM,
    retr1_mem hs.hz hq.2.2 h3 hM4 hM⟩, ?_⟩
  rintro ⟨hx, hy, hz⟩
  rcases max_choice (weight1 s.kx s.box.x0 s.box.x1 q.1)
    (max (weight1 s.ky s.box.y0 s.box.y1 q.2.1) (weight1 s.kz s.box.z0 s.box.z1 q.2.2))
    with he | he
  · exact retr1_notMem hs.hx he.symm hM hx
  · rcases max_choice (weight1 s.ky s.box.y0 s.box.y1 q.2.1)
      (weight1 s.kz s.box.z0 s.box.z1 q.2.2) with he' | he'
    · exact retr1_notMem hs.hy (he'.symm.trans he.symm) hM hy
    · exact retr1_notMem hs.hz (he'.symm.trans he.symm) hM hz

private lemma Step.retr_eq_self {s : Step} (hs : s.Nondeg) {q : ℝ × ℝ × ℝ}
    (hq : q ∈ s.box.toSet \ s.core) : s.retr q = q := by
  obtain ⟨hq, hno⟩ := hq
  have h4 : s.gauge q = 4 := by
    refine le_antisymm (s.gauge_le_four hs hq) ?_
    simp only [Step.core, mem_prod, not_and_or] at hno
    rcases hno with h | h | h
    · exact le_max_of_le_left (weight1_eq_four hs.hx hq.1 h).ge
    · exact le_max_of_le_right (le_max_of_le_left (weight1_eq_four hs.hy hq.2.1 h).ge)
    · exact le_max_of_le_right (le_max_of_le_right (weight1_eq_four hs.hz hq.2.2 h).ge)
  obtain ⟨x, y, z⟩ := q
  simp only [Step.retr, h4, div_self (four_ne_zero : (4 : ℝ) ≠ 0), retr1_one _ hs.hx,
    retr1_one _ hs.hy, retr1_one _ hs.hz]

/-- The radial projection of a step, extended by the identity outside its box. -/
private noncomputable def Step.extend (s : Step) (q : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  open Classical in if q ∈ s.box.toSet then s.retr q else q

private lemma Step.extend_eq_self {s : Step} (hs : s.Nondeg) {Y : Set (ℝ × ℝ × ℝ)}
    (hfree : ∀ q ∈ Y, q ∉ s.core) {q : ℝ × ℝ × ℝ} (hq : q ∈ Y) : s.extend q = q := by
  unfold Step.extend
  split_ifs with h
  · exact s.retr_eq_self hs ⟨h, hfree q hq⟩
  · rfl

/-- One collapse step retracts the union of its box and a closed set `Y` onto `Y`, when `Y`
misses the core of the box and contains its faces that are not free. -/
private lemma Step.retract {s : Step} (hs : s.Nondeg) {Y : Set (ℝ × ℝ × ℝ)} (hY : IsClosed Y)
    (hfree : ∀ q ∈ Y, q ∉ s.core) (hcov : s.box.toSet \ s.core ⊆ Y) :
    ContinuousOn s.extend (s.box.toSet ∪ Y) ∧ MapsTo s.extend (s.box.toSet ∪ Y) Y ∧
      ∀ q ∈ Y, s.extend q = q := by
  have hon : EqOn s.extend s.retr s.box.toSet := fun q hq => by simp [Step.extend, hq]
  refine ⟨ContinuousOn.union_of_isClosed ((s.continuousOn_retr hs).congr hon)
    (continuousOn_id.congr fun q hq => s.extend_eq_self hs hfree hq) s.box.isClosed_toSet hY,
    ?_, fun q hq => s.extend_eq_self hs hfree hq⟩
  rintro q (hq | hq)
  · rw [hon hq]; exact hcov (s.mapsTo_retr hs hq)
  · rw [s.extend_eq_self hs hfree hq]; exact hq

/-! ### Decidable conditions on the collapse data -/

/-- A sufficient condition, on natural numbers, for `[c, d]` to miss the interval of kind `k`
with endpoints `a` and `b`. -/
private def Kind.sep : Kind → ℕ → ℕ → ℕ → ℕ → Bool
  | .ioo, a, b, c, d => decide (d ≤ a) || decide (b ≤ c)
  | .ico, a, b, c, d => decide (d < a) || decide (b ≤ c)
  | .ioc, a, b, c, d => decide (d ≤ a) || decide (b < c)

private lemma Kind.sep_sound {k : Kind} {a b c d : ℕ} (h : k.sep a b c d = true) {t : ℝ}
    (ht : t ∈ Icc (c : ℝ) d) (hk : t ∈ k.toSet a b) : False := by
  obtain ⟨h1, h2⟩ := ht
  cases k <;> simp only [Kind.sep, Bool.or_eq_true, decide_eq_true_eq] at h <;>
    simp only [Kind.toSet, mem_Ioo, mem_Ico, mem_Ioc] at hk <;>
    rcases h with h | h
  · have : (d : ℝ) ≤ a := by exact_mod_cast h
    linarith [hk.1]
  · have : (b : ℝ) ≤ c := by exact_mod_cast h
    linarith [hk.2]
  · have : (d : ℝ) < a := by exact_mod_cast h
    linarith [hk.1]
  · have : (b : ℝ) ≤ c := by exact_mod_cast h
    linarith [hk.2]
  · have : (d : ℝ) ≤ a := by exact_mod_cast h
    linarith [hk.1]
  · have : (b : ℝ) < c := by exact_mod_cast h
    linarith [hk.2]

/-- A sufficient condition for a box to miss the core of a step: one coordinate separates
them. -/
private def Step.avoids (s : Step) (b : IBox) : Bool :=
  s.kx.sep s.box.x0 s.box.x1 b.x0 b.x1 || s.ky.sep s.box.y0 s.box.y1 b.y0 b.y1 ||
    s.kz.sep s.box.z0 s.box.z1 b.z0 b.z1

private lemma Step.avoids_sound {s : Step} {b : IBox} (h : s.avoids b = true) :
    ∀ q ∈ b.toSet, q ∉ s.core := by
  rintro ⟨x, y, z⟩ ⟨hx, hy, hz⟩ ⟨hx', hy', hz'⟩
  simp only [Step.avoids, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact Kind.sep_sound h hx hx'
  · exact Kind.sep_sound h hy hy'
  · exact Kind.sep_sound h hz hz'

/-- The closed unit intervals making up `[a, b]`, or `[a, a]` when `a = b`. -/
private def ivCells (a b : ℕ) : List (ℕ × ℕ) :=
  if a = b then [(a, a)] else (List.range (b - a)).map fun i => (a + i, a + i + 1)

private lemma ivCells_sound {a b : ℕ} {t : ℝ} (ht : t ∈ Icc (a : ℝ) b) :
    ∃ p ∈ ivCells a b, t ∈ Icc (p.1 : ℝ) p.2 := by
  obtain ⟨h1, h2⟩ := ht
  unfold ivCells
  split_ifs with hab
  · subst hab; exact ⟨(a, a), List.mem_singleton_self _, h1, h2⟩
  · have hab' : a < b := by
      have : a ≤ b := by exact_mod_cast h1.trans h2
      omega
    have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg a) h1
    have han : a ≤ ⌊t⌋₊ := Nat.le_floor h1
    by_cases hnb : ⌊t⌋₊ < b
    · refine ⟨(a + (⌊t⌋₊ - a), a + (⌊t⌋₊ - a) + 1),
        List.mem_map.mpr ⟨⌊t⌋₊ - a, List.mem_range.mpr (by omega), rfl⟩, ?_, ?_⟩
      · rw [show a + (⌊t⌋₊ - a) = ⌊t⌋₊ by omega]; exact Nat.floor_le ht0
      · rw [show a + (⌊t⌋₊ - a) + 1 = ⌊t⌋₊ + 1 by omega]; push_cast
        exact (Nat.lt_floor_add_one t).le
    · have htb : (b : ℝ) ≤ t :=
        le_trans (by exact_mod_cast (not_lt.mp hnb)) (Nat.floor_le ht0)
      refine ⟨(a + (b - 1 - a), a + (b - 1 - a) + 1),
        List.mem_map.mpr ⟨b - 1 - a, List.mem_range.mpr (by omega), rfl⟩, ?_, ?_⟩
      · rw [show a + (b - 1 - a) = b - 1 by omega, Nat.cast_sub (by omega)]; push_cast
        linarith
      · rw [show a + (b - 1 - a) + 1 = b by omega]; exact h2

/-- The closed unit cells making up a box. -/
private def IBox.cells (B : IBox) : List IBox :=
  (ivCells B.x0 B.x1).flatMap fun X => (ivCells B.y0 B.y1).flatMap fun Y =>
    (ivCells B.z0 B.z1).map fun Z => ⟨X.1, X.2, Y.1, Y.2, Z.1, Z.2⟩

private lemma IBox.cells_sound {B : IBox} {q : ℝ × ℝ × ℝ} (hq : q ∈ B.toSet) :
    ∃ c ∈ B.cells, q ∈ c.toSet := by
  obtain ⟨hx, hy, hz⟩ := hq
  obtain ⟨X, hX, hxX⟩ := ivCells_sound hx
  obtain ⟨Y, hY, hyY⟩ := ivCells_sound hy
  obtain ⟨Z, hZ, hzZ⟩ := ivCells_sound hz
  refine ⟨⟨X.1, X.2, Y.1, Y.2, Z.1, Z.2⟩, ?_, hxX, hyY, hzZ⟩
  simp only [IBox.cells, List.mem_flatMap, List.mem_map]
  exact ⟨X, hX, Y, hY, Z, hZ, rfl⟩

/-- Whether the box `c` lies in the box `b`. -/
private def IBox.sub (c b : IBox) : Bool :=
  decide (b.x0 ≤ c.x0) && decide (c.x1 ≤ b.x1) && decide (b.y0 ≤ c.y0) &&
    decide (c.y1 ≤ b.y1) && decide (b.z0 ≤ c.z0) && decide (c.z1 ≤ b.z1)

private lemma IBox.sub_sound {c b : IBox} (h : c.sub b = true) : c.toSet ⊆ b.toSet := by
  simp only [IBox.sub, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  rintro ⟨x, y, z⟩ ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, ⟨hz1, hz2⟩⟩
  exact ⟨⟨le_trans (by exact_mod_cast h1) hx1, le_trans hx2 (by exact_mod_cast h2)⟩,
    ⟨le_trans (by exact_mod_cast h3) hy1, le_trans hy2 (by exact_mod_cast h4)⟩,
    ⟨le_trans (by exact_mod_cast h5) hz1, le_trans hz2 (by exact_mod_cast h6)⟩⟩

private lemma boxesUnion_subset {bs : List IBox} {B : IBox}
    (h : bs.all (fun b => b.sub B) = true) : boxesUnion bs ⊆ B.toSet := by
  intro q hq
  obtain ⟨b, hb, hqb⟩ := mem_boxesUnion.mp hq
  exact IBox.sub_sound (List.all_eq_true.mp h b hb) hqb

/-- A sufficient condition for a box to lie in a union of boxes: each of its closed unit cells
lies in one of them. -/
private def covered (B : IBox) (P : List IBox) : Bool :=
  B.cells.all fun c => P.any fun b => c.sub b

private lemma covered_sound {B : IBox} {P : List IBox} (h : covered B P = true) :
    B.toSet ⊆ boxesUnion P := by
  intro q hq
  obtain ⟨c, hc, hqc⟩ := IBox.cells_sound hq
  simp only [covered, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨b, hb, hcb⟩ := h c hc
  exact mem_boxesUnion.mpr ⟨b, hb, IBox.sub_sound hcb hqc⟩

/-- The endpoints of `[a, b]` that do not bound a free face, as degenerate intervals. -/
private def Kind.faces : Kind → ℕ → ℕ → List (ℕ × ℕ)
  | .ioo, a, b => [(a, a), (b, b)]
  | .ico, _, b => [(b, b)]
  | .ioc, a, _ => [(a, a)]

private lemma Kind.faces_sound {k : Kind} {a b : ℕ} {t : ℝ} (ht : t ∈ Icc (a : ℝ) b)
    (hno : t ∉ k.toSet a b) : ∃ p ∈ k.faces a b, t ∈ Icc (p.1 : ℝ) p.2 := by
  obtain ⟨h1, h2⟩ := ht
  cases k <;>
    simp only [Kind.toSet, mem_Ioo, mem_Ico, mem_Ioc, not_and_or, not_lt, not_le] at hno <;>
    rcases hno with h | h
  · exact ⟨(a, a), by simp [Kind.faces], h1, h⟩
  · exact ⟨(b, b), by simp [Kind.faces], h, h2⟩
  · exact absurd h1 (not_le.mpr h)
  · exact ⟨(b, b), by simp [Kind.faces], h, h2⟩
  · exact ⟨(a, a), by simp [Kind.faces], h1, h⟩
  · exact absurd h2 (not_le.mpr h)

/-- The faces of the box of a step that are not free. -/
private def Step.faces (s : Step) : List IBox :=
  ((s.kx.faces s.box.x0 s.box.x1).map fun p =>
      ⟨p.1, p.2, s.box.y0, s.box.y1, s.box.z0, s.box.z1⟩) ++
    ((s.ky.faces s.box.y0 s.box.y1).map fun p =>
      ⟨s.box.x0, s.box.x1, p.1, p.2, s.box.z0, s.box.z1⟩) ++
    ((s.kz.faces s.box.z0 s.box.z1).map fun p =>
      ⟨s.box.x0, s.box.x1, s.box.y0, s.box.y1, p.1, p.2⟩)

private lemma Step.faces_sound {s : Step} {q : ℝ × ℝ × ℝ} (hq : q ∈ s.box.toSet)
    (hno : q ∉ s.core) : ∃ F ∈ s.faces, q ∈ F.toSet := by
  obtain ⟨x, y, z⟩ := q
  obtain ⟨hx, hy, hz⟩ := hq
  simp only [Step.core, mem_prod, not_and_or] at hno
  rcases hno with h | h | h
  · obtain ⟨p, hp, hxp⟩ := Kind.faces_sound hx h
    exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hp)),
      hxp, hy, hz⟩
  · obtain ⟨p, hp, hyp⟩ := Kind.faces_sound hy h
    exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hp)),
      hx, hyp, hz⟩
  · obtain ⟨p, hp, hzp⟩ := Kind.faces_sound hz h
    exact ⟨_, List.mem_append_right _ (List.mem_map_of_mem hp), hx, hy, hzp⟩

/-- Boolean form of `Step.Nondeg`. -/
private def Step.nondegB (s : Step) : Bool :=
  decide (s.box.x0 < s.box.x1) && decide (s.box.y0 < s.box.y1) &&
    decide (s.box.z0 < s.box.z1) && !(s.kx.isIoo && s.ky.isIoo && s.kz.isIoo)

private lemma Step.nondeg_of_nondegB {s : Step} (h : s.nondegB = true) : s.Nondeg := by
  simp only [Step.nondegB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff] at h
  obtain ⟨⟨⟨hx, hy⟩, hz⟩, hk⟩ := h
  exact ⟨by exact_mod_cast hx, by exact_mod_cast hy, by exact_mod_cast hz, by tauto⟩

/-- The conditions for collapsing the box of a step when the boxes `P` remain. -/
private def Step.ok (s : Step) (P : List IBox) : Bool :=
  s.nondegB && P.all s.avoids && s.faces.all fun F => covered F P

private lemma Step.ok_sound {s : Step} {P : List IBox} (h : s.ok P = true) :
    s.Nondeg ∧ (∀ q ∈ boxesUnion P, q ∉ s.core) ∧ s.box.toSet \ s.core ⊆ boxesUnion P := by
  simp only [Step.ok, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hnd, hfree⟩, hcov⟩ := h
  refine ⟨Step.nondeg_of_nondegB hnd, fun q hq => ?_, fun q ⟨hq, hno⟩ => ?_⟩
  · obtain ⟨b, hb, hqb⟩ := mem_boxesUnion.mp hq
    exact Step.avoids_sound (hfree b hb) q hqb
  · obtain ⟨F, hF, hqF⟩ := Step.faces_sound hq hno
    exact covered_sound (hcov F hF) hqF

/-- The conditions for collapsing the boxes of a list of steps, in order, onto the union of the
boxes `R`. -/
private def valid : List Step → List IBox → Bool
  | [], _ => true
  | s :: ss, R => s.ok (ss.map Step.box ++ R) && valid ss R

/-- Valid collapse data give a retraction of the union of all the boxes onto the union of the
boxes `R`. -/
private theorem exists_retraction : ∀ (ss : List Step) (R : List IBox), valid ss R = true →
    ∃ r : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ, ContinuousOn r (boxesUnion (ss.map Step.box ++ R)) ∧
      MapsTo r (boxesUnion (ss.map Step.box ++ R)) (boxesUnion R) ∧
      ∀ q ∈ boxesUnion R, r q = q
  | [], R, _ => ⟨id, continuousOn_id, fun _ hq => hq, fun _ _ => rfl⟩
  | s :: ss, R, h => by
    simp only [valid, Bool.and_eq_true] at h
    obtain ⟨hs, hss⟩ := h
    obtain ⟨r, hrc, hrm, hrf⟩ := exists_retraction ss R hss
    obtain ⟨hnd, hfree, hcov⟩ := Step.ok_sound hs
    obtain ⟨hgc, hgm, hgf⟩ := Step.retract hnd (isClosed_boxesUnion _) hfree hcov
    refine ⟨r ∘ s.extend, hrc.comp hgc hgm, hrm.comp hgm, fun q hq => ?_⟩
    have hqY : q ∈ boxesUnion (ss.map Step.box ++ R) := by
      rw [boxesUnion_append]; exact Or.inr hq
    simp only [Function.comp, hgf q hqY, hrf q hq]

/-- A retract of a convex set is contractible. -/
private theorem contractibleSpace_of_retraction {S H : Set (ℝ × ℝ × ℝ)} (hS : Convex ℝ S)
    (hHS : H ⊆ S) (hH : H.Nonempty) {r : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ} (hrc : ContinuousOn r S)
    (hrm : MapsTo r S H) (hrf : ∀ q ∈ H, r q = q) : ContractibleSpace H := by
  have : ContractibleSpace S := hS.contractibleSpace (hH.mono hHS)
  let i : C(H, S) := ⟨Set.inclusion hHS, continuous_inclusion hHS⟩
  let ρ : C(S, H) := ⟨hrm.restrict r S H, hrc.mapsToRestrict hrm⟩
  have hρi : ρ.comp ((ContinuousMap.id S).comp i) = ContinuousMap.id H :=
    ContinuousMap.ext fun x => Subtype.ext (hrf x x.2)
  rw [contractible_iff_id_nullhomotopic, ← hρi]
  exact ((id_nullhomotopic S).comp_left i).comp_right ρ

/-! ### The house as a union of rectangles, and its collapse data -/

/-- The house as a union of twenty-three rectangles: the three floors (four rectangles around
each hole), the inner walls and the outer walls. -/
private def houseRects : List IBox :=
  [⟨0, 2, 0, 3, 0, 0⟩, ⟨3, 4, 0, 3, 0, 0⟩, ⟨2, 3, 0, 1, 0, 0⟩, ⟨2, 3, 2, 3, 0, 0⟩,
    ⟨0, 1, 0, 3, 1, 1⟩, ⟨3, 4, 0, 3, 1, 1⟩, ⟨1, 3, 0, 1, 1, 1⟩, ⟨1, 3, 2, 3, 1, 1⟩,
    ⟨0, 1, 0, 3, 2, 2⟩, ⟨2, 4, 0, 3, 2, 2⟩, ⟨1, 2, 0, 1, 2, 2⟩, ⟨1, 2, 2, 3, 2, 2⟩,
    ⟨1, 1, 1, 2, 1, 2⟩, ⟨2, 2, 1, 3, 0, 2⟩, ⟨3, 3, 1, 2, 0, 1⟩, ⟨1, 2, 1, 1, 1, 2⟩,
    ⟨1, 2, 2, 2, 1, 2⟩, ⟨2, 3, 1, 1, 0, 1⟩, ⟨2, 3, 2, 2, 0, 1⟩,
    ⟨0, 4, 0, 0, 0, 2⟩, ⟨0, 4, 3, 3, 0, 2⟩, ⟨0, 0, 0, 3, 0, 2⟩, ⟨4, 4, 0, 3, 0, 2⟩]

/-- The fourteen collapse steps: first the lower room, entered through the hole in the top
floor, then the upper room, entered through the hole in the ground floor. -/
private def houseSteps : List Step :=
  [⟨⟨1, 2, 1, 2, 0, 2⟩, .ioo, .ioo, .ioc⟩, ⟨⟨0, 1, 1, 2, 0, 1⟩, .ioc, .ioo, .ioo⟩,
    ⟨⟨0, 2, 0, 1, 0, 1⟩, .ioo, .ioc, .ioo⟩, ⟨⟨2, 4, 0, 1, 0, 1⟩, .ico, .ioo, .ioo⟩,
    ⟨⟨3, 4, 1, 3, 0, 1⟩, .ioo, .ico, .ioo⟩, ⟨⟨2, 3, 2, 3, 0, 1⟩, .ioc, .ioo, .ioo⟩,
    ⟨⟨0, 2, 2, 3, 0, 1⟩, .ioo, .ico, .ioo⟩, ⟨⟨2, 3, 1, 2, 0, 2⟩, .ioo, .ioo, .ico⟩,
    ⟨⟨3, 4, 1, 2, 1, 2⟩, .ico, .ioo, .ioo⟩, ⟨⟨2, 4, 0, 1, 1, 2⟩, .ioo, .ioc, .ioo⟩,
    ⟨⟨0, 2, 0, 1, 1, 2⟩, .ioc, .ioo, .ioo⟩, ⟨⟨0, 1, 1, 3, 1, 2⟩, .ioo, .ico, .ioo⟩,
    ⟨⟨1, 2, 2, 3, 1, 2⟩, .ico, .ioo, .ioo⟩, ⟨⟨2, 4, 2, 3, 1, 2⟩, .ioo, .ico, .ioo⟩]

/-- The solid box `[0,4] × [0,3] × [0,2]` containing the house. -/
private def houseBox : IBox := ⟨0, 4, 0, 3, 0, 2⟩

private lemma valid_houseSteps : valid houseSteps houseRects = true := by decide +kernel

private lemma covered_houseBox :
    covered houseBox (houseSteps.map Step.box ++ houseRects) = true := by
  decide +kernel

private lemma houseRects_sub_houseBox : houseRects.all (fun b => b.sub houseBox) = true := by
  decide +kernel

private lemma mem_house_iff {x y z : ℝ} : (x, y, z) ∈ HouseWithTwoRooms ↔
    (((0 ≤ x ∧ x ≤ 4) ∧ (0 ≤ y ∧ y ≤ 3) ∧ (z = 0 ∨ z = 1 ∨ z = 2)) ∧
        ¬(((2 < x ∧ x < 3) ∧ (1 < y ∧ y < 2) ∧ z = 0 ∨
            (1 < x ∧ x < 3) ∧ (1 < y ∧ y < 2) ∧ z = 1) ∨
          (1 < x ∧ x < 2) ∧ (1 < y ∧ y < 2) ∧ z = 2) ∨
      (((x = 1 ∧ (1 ≤ y ∧ y ≤ 2) ∧ 1 ≤ z ∧ z ≤ 2 ∨ x = 2 ∧ (1 ≤ y ∧ y ≤ 3) ∧ 0 ≤ z ∧ z ≤ 2) ∨
            x = 3 ∧ (1 ≤ y ∧ y ≤ 2) ∧ 0 ≤ z ∧ z ≤ 1) ∨
          (1 ≤ x ∧ x ≤ 2) ∧ (y = 1 ∨ y = 2) ∧ 1 ≤ z ∧ z ≤ 2) ∨
        (2 ≤ x ∧ x ≤ 3) ∧ (y = 1 ∨ y = 2) ∧ 0 ≤ z ∧ z ≤ 1) ∨
      (0 ≤ x ∧ x ≤ 4) ∧ (y = 0 ∨ y = 3) ∧ 0 ≤ z ∧ z ≤ 2 ∨
        (x = 0 ∨ x = 4) ∧ (0 ≤ y ∧ y ≤ 3) ∧ 0 ≤ z ∧ z ≤ 2 := by
  simp only [HouseWithTwoRooms, mem_union, mem_sdiff, mem_prod, mem_Icc, mem_Ioo, mem_insert_iff,
    mem_singleton_iff]

private lemma house_subset : HouseWithTwoRooms ⊆ boxesUnion houseRects := by
  rintro ⟨x, y, z⟩ hq
  rw [mem_house_iff] at hq
  rcases hq with (⟨⟨⟨hx0, hx4⟩, ⟨hy0, hy3⟩, hz⟩, hnh⟩ |
      ((((⟨rfl, ⟨hy1, hy2⟩, hz1, hz2⟩ | ⟨rfl, ⟨hy1, hy2⟩, hz1, hz2⟩) |
        ⟨rfl, ⟨hy1, hy2⟩, hz1, hz2⟩) | ⟨⟨hx1, hx2⟩, hy, hz1, hz2⟩) | ⟨⟨hx1, hx2⟩, hy, hz1, hz2⟩)) |
    ⟨⟨hx1, hx2⟩, hy, hz1, hz2⟩ | ⟨hx, ⟨hy1, hy2⟩, hz1, hz2⟩
  · rcases hz with rfl | rfl | rfl
    · have key : ¬(2 < x ∧ x < 3 ∧ 1 < y ∧ y < 2) := fun ⟨a, b, c, d⟩ =>
        hnh (Or.inl (Or.inl ⟨⟨a, b⟩, ⟨c, d⟩, rfl⟩))
      rcases le_or_gt x 2 with h1 | h1
      · refine mem_boxesUnion_of (b := ⟨0, 2, 0, 3, 0, 0⟩) (by simp [houseRects])
          ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
      rcases le_or_gt 3 x with h2 | h2
      · refine mem_boxesUnion_of (b := ⟨3, 4, 0, 3, 0, 0⟩) (by simp [houseRects])
          ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
      rcases le_or_gt y 1 with h3 | h3
      · refine mem_boxesUnion_of (b := ⟨2, 3, 0, 1, 0, 0⟩) (by simp [houseRects])
          ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
      have h4 : 2 ≤ y := not_lt.mp fun h4 => key ⟨h1, h2, h3, h4⟩
      refine mem_boxesUnion_of (b := ⟨2, 3, 2, 3, 0, 0⟩) (by simp [houseRects])
        ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
    · have key : ¬(1 < x ∧ x < 3 ∧ 1 < y ∧ y < 2) := fun ⟨a, b, c, d⟩ =>
        hnh (Or.inl (Or.inr ⟨⟨a, b⟩, ⟨c, d⟩, rfl⟩))
      rcases le_or_gt x 1 with h1 | h1
      · refine mem_boxesUnion_of (b := ⟨0, 1, 0, 3, 1, 1⟩) (by simp [houseRects])
          ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
      rcases le_or_gt 3 x with h2 | h2
      · refine mem_boxesUnion_of (b := ⟨3, 4, 0, 3, 1, 1⟩) (by simp [houseRects])
          ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
      rcases le_or_gt y 1 with h3 | h3
      · refine mem_boxesUnion_of (b := ⟨1, 3, 0, 1, 1, 1⟩) (by simp [houseRects])
          ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
      have h4 : 2 ≤ y := not_lt.mp fun h4 => key ⟨h1, h2, h3, h4⟩
      refine mem_boxesUnion_of (b := ⟨1, 3, 2, 3, 1, 1⟩) (by simp [houseRects])
        ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
    · have key : ¬(1 < x ∧ x < 2 ∧ 1 < y ∧ y < 2) := fun ⟨a, b, c, d⟩ =>
        hnh (Or.inr ⟨⟨a, b⟩, ⟨c, d⟩, rfl⟩)
      rcases le_or_gt x 1 with h1 | h1
      · refine mem_boxesUnion_of (b := ⟨0, 1, 0, 3, 2, 2⟩) (by simp [houseRects])
          ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
      rcases le_or_gt 2 x with h2 | h2
      · refine mem_boxesUnion_of (b := ⟨2, 4, 0, 3, 2, 2⟩) (by simp [houseRects])
          ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
      rcases le_or_gt y 1 with h3 | h3
      · refine mem_boxesUnion_of (b := ⟨1, 2, 0, 1, 2, 2⟩) (by simp [houseRects])
          ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
      have h4 : 2 ≤ y := not_lt.mp fun h4 => key ⟨h1, h2, h3, h4⟩
      refine mem_boxesUnion_of (b := ⟨1, 2, 2, 3, 2, 2⟩) (by simp [houseRects])
        ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
  · refine mem_boxesUnion_of (b := ⟨1, 1, 1, 2, 1, 2⟩) (by simp [houseRects])
      ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
  · refine mem_boxesUnion_of (b := ⟨2, 2, 1, 3, 0, 2⟩) (by simp [houseRects])
      ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
  · refine mem_boxesUnion_of (b := ⟨3, 3, 1, 2, 0, 1⟩) (by simp [houseRects])
      ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
  · rcases hy with rfl | rfl
    · refine mem_boxesUnion_of (b := ⟨1, 2, 1, 1, 1, 2⟩) (by simp [houseRects])
        ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
    · refine mem_boxesUnion_of (b := ⟨1, 2, 2, 2, 1, 2⟩) (by simp [houseRects])
        ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
  · rcases hy with rfl | rfl
    · refine mem_boxesUnion_of (b := ⟨2, 3, 1, 1, 0, 1⟩) (by simp [houseRects])
        ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
    · refine mem_boxesUnion_of (b := ⟨2, 3, 2, 2, 0, 1⟩) (by simp [houseRects])
        ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
  · rcases hy with rfl | rfl
    · refine mem_boxesUnion_of (b := ⟨0, 4, 0, 0, 0, 2⟩) (by simp [houseRects])
        ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
    · refine mem_boxesUnion_of (b := ⟨0, 4, 3, 3, 0, 2⟩) (by simp [houseRects])
        ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
  · rcases hx with rfl | rfl
    · refine mem_boxesUnion_of (b := ⟨0, 0, 0, 3, 0, 2⟩) (by simp [houseRects])
        ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith
    · refine mem_boxesUnion_of (b := ⟨4, 4, 0, 3, 0, 2⟩) (by simp [houseRects])
        ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num <;> linarith

private lemma mem_house_floor0 {x y : ℝ} (hx0 : 0 ≤ x) (hx4 : x ≤ 4) (hy0 : 0 ≤ y) (hy3 : y ≤ 3)
    (h : ¬(2 < x ∧ x < 3 ∧ 1 < y ∧ y < 2)) : (x, y, (0 : ℝ)) ∈ HouseWithTwoRooms := by
  refine mem_house_iff.2 (Or.inl (Or.inl ⟨⟨⟨hx0, hx4⟩, ⟨hy0, hy3⟩, Or.inl rfl⟩, ?_⟩))
  rintro ((⟨⟨a, b⟩, ⟨c, d⟩, -⟩ | ⟨-, -, e⟩) | ⟨-, -, e⟩)
  · exact h ⟨a, b, c, d⟩
  · norm_num at e
  · norm_num at e

private lemma mem_house_floor1 {x y : ℝ} (hx0 : 0 ≤ x) (hx4 : x ≤ 4) (hy0 : 0 ≤ y) (hy3 : y ≤ 3)
    (h : ¬(1 < x ∧ x < 3 ∧ 1 < y ∧ y < 2)) : (x, y, (1 : ℝ)) ∈ HouseWithTwoRooms := by
  refine mem_house_iff.2 (Or.inl (Or.inl ⟨⟨⟨hx0, hx4⟩, ⟨hy0, hy3⟩, Or.inr (Or.inl rfl)⟩, ?_⟩))
  rintro ((⟨-, -, e⟩ | ⟨⟨a, b⟩, ⟨c, d⟩, -⟩) | ⟨-, -, e⟩)
  · norm_num at e
  · exact h ⟨a, b, c, d⟩
  · norm_num at e

private lemma mem_house_floor2 {x y : ℝ} (hx0 : 0 ≤ x) (hx4 : x ≤ 4) (hy0 : 0 ≤ y) (hy3 : y ≤ 3)
    (h : ¬(1 < x ∧ x < 2 ∧ 1 < y ∧ y < 2)) : (x, y, (2 : ℝ)) ∈ HouseWithTwoRooms := by
  refine mem_house_iff.2 (Or.inl (Or.inl ⟨⟨⟨hx0, hx4⟩, ⟨hy0, hy3⟩, Or.inr (Or.inr rfl)⟩, ?_⟩))
  rintro ((⟨-, -, e⟩ | ⟨-, -, e⟩) | ⟨⟨a, b⟩, ⟨c, d⟩, -⟩)
  · norm_num at e
  · norm_num at e
  · exact h ⟨a, b, c, d⟩

private lemma subset_house : boxesUnion houseRects ⊆ HouseWithTwoRooms := by
  rintro ⟨x, y, z⟩ hq
  obtain ⟨b, hb, hqb⟩ := mem_boxesUnion.mp hq
  simp only [houseRects, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩ := hqb <;>
  norm_num at h1 h2 h3 h4 h5 h6
  · obtain rfl : z = 0 := le_antisymm h6 h5
    exact mem_house_floor0 h1 (by linarith) h3 h4 fun ⟨a, _⟩ => by linarith
  · obtain rfl : z = 0 := le_antisymm h6 h5
    exact mem_house_floor0 (by linarith) h2 h3 h4 fun ⟨_, a, _⟩ => by linarith
  · obtain rfl : z = 0 := le_antisymm h6 h5
    exact mem_house_floor0 (by linarith) (by linarith) h3 (by linarith)
      fun ⟨_, _, a, _⟩ => by linarith
  · obtain rfl : z = 0 := le_antisymm h6 h5
    exact mem_house_floor0 (by linarith) (by linarith) (by linarith) h4
      fun ⟨_, _, _, a⟩ => by linarith
  · obtain rfl : z = 1 := le_antisymm h6 h5
    exact mem_house_floor1 h1 (by linarith) h3 h4 fun ⟨a, _⟩ => by linarith
  · obtain rfl : z = 1 := le_antisymm h6 h5
    exact mem_house_floor1 (by linarith) h2 h3 h4 fun ⟨_, a, _⟩ => by linarith
  · obtain rfl : z = 1 := le_antisymm h6 h5
    exact mem_house_floor1 (by linarith) (by linarith) h3 (by linarith)
      fun ⟨_, _, a, _⟩ => by linarith
  · obtain rfl : z = 1 := le_antisymm h6 h5
    exact mem_house_floor1 (by linarith) (by linarith) (by linarith) h4
      fun ⟨_, _, _, a⟩ => by linarith
  · obtain rfl : z = 2 := le_antisymm h6 h5
    exact mem_house_floor2 h1 (by linarith) h3 h4 fun ⟨a, _⟩ => by linarith
  · obtain rfl : z = 2 := le_antisymm h6 h5
    exact mem_house_floor2 (by linarith) h2 h3 h4 fun ⟨_, a, _⟩ => by linarith
  · obtain rfl : z = 2 := le_antisymm h6 h5
    exact mem_house_floor2 (by linarith) (by linarith) h3 (by linarith)
      fun ⟨_, _, a, _⟩ => by linarith
  · obtain rfl : z = 2 := le_antisymm h6 h5
    exact mem_house_floor2 (by linarith) (by linarith) (by linarith) h4
      fun ⟨_, _, _, a⟩ => by linarith
  · obtain rfl : x = 1 := le_antisymm h2 h1
    exact mem_house_iff.2
      (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl ⟨rfl, ⟨h3, h4⟩, h5, h6⟩))))))
  · obtain rfl : x = 2 := le_antisymm h2 h1
    exact mem_house_iff.2
      (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨rfl, ⟨h3, h4⟩, h5, h6⟩))))))
  · obtain rfl : x = 3 := le_antisymm h2 h1
    exact mem_house_iff.2 (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr ⟨rfl, ⟨h3, h4⟩, h5, h6⟩)))))
  · obtain rfl : y = 1 := le_antisymm h4 h3
    exact mem_house_iff.2 (Or.inl (Or.inr (Or.inl (Or.inr ⟨⟨h1, h2⟩, Or.inl rfl, h5, h6⟩))))
  · obtain rfl : y = 2 := le_antisymm h4 h3
    exact mem_house_iff.2 (Or.inl (Or.inr (Or.inl (Or.inr ⟨⟨h1, h2⟩, Or.inr rfl, h5, h6⟩))))
  · obtain rfl : y = 1 := le_antisymm h4 h3
    exact mem_house_iff.2 (Or.inl (Or.inr (Or.inr ⟨⟨h1, h2⟩, Or.inl rfl, h5, h6⟩)))
  · obtain rfl : y = 2 := le_antisymm h4 h3
    exact mem_house_iff.2 (Or.inl (Or.inr (Or.inr ⟨⟨h1, h2⟩, Or.inr rfl, h5, h6⟩)))
  · obtain rfl : y = 0 := le_antisymm h4 h3
    exact mem_house_iff.2 (Or.inr (Or.inl ⟨⟨h1, h2⟩, Or.inl rfl, h5, h6⟩))
  · obtain rfl : y = 3 := le_antisymm h4 h3
    exact mem_house_iff.2 (Or.inr (Or.inl ⟨⟨h1, h2⟩, Or.inr rfl, h5, h6⟩))
  · obtain rfl : x = 0 := le_antisymm h2 h1
    exact mem_house_iff.2 (Or.inr (Or.inr ⟨Or.inl rfl, ⟨h3, h4⟩, h5, h6⟩))
  · obtain rfl : x = 4 := le_antisymm h2 h1
    exact mem_house_iff.2 (Or.inr (Or.inr ⟨Or.inr rfl, ⟨h3, h4⟩, h5, h6⟩))

private lemma house_eq : HouseWithTwoRooms = boxesUnion houseRects :=
  Subset.antisymm house_subset subset_house

set_option linter.dupNamespace false in
/-- **Bing's house with two rooms is contractible.** Bing's house with two rooms, regarded as a
subspace of $\mathbb{R} \times \mathbb{R} \times \mathbb{R}$, is contractible.

Source: Allen Hatcher, *Algebraic Topology*. Via leanprover/lean-eval@38361be, problem
`contractibleSpace_houseWithTwoRooms`. -/
theorem contractibleSpace_houseWithTwoRooms : ContractibleSpace HouseWithTwoRooms := by
  obtain ⟨r, hrc, hrm, hrf⟩ := exists_retraction houseSteps houseRects valid_houseSteps
  have hbox := covered_sound covered_houseBox
  rw [← house_eq] at hrm hrf
  refine contractibleSpace_of_retraction (S := houseBox.toSet)
    ((convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _)))
    (house_eq ▸ boxesUnion_subset houseRects_sub_houseBox) ⟨(0, 0, 0), ?_⟩ (hrc.mono hbox)
    (hrm.mono_left hbox) hrf
  rw [house_eq]
  exact mem_boxesUnion_of (b := ⟨0, 2, 0, 3, 0, 0⟩) (by simp [houseRects]) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Topology

end MathlibExt.Topology.HouseWithTwoRoomsWanted
