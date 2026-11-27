/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.Triangulated.GrothendieckGroup
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Data.Fintype.BigOperators

/-!
# General stability contracts on actual triangulated categories

The class map is the actual triangulated K0 quotient. Numerical data are
a chosen homomorphism to the concrete lattice Z^r, followed by an additive
complex central charge. A slicing concerns actual objects, shifts, Hom
and distinguished triangles. HN data are finite actual triangle towers.
This chosen realization is part of the stability datum; it is not asserted
to be a canonical Euler-numerical quotient of an arbitrary variety.

Local finiteness is expressed by stabilization of strict subobject chains in
the phase window, whose admissible maps are witnessed by actual triangles.
For a slicing and windows of width less than one, this is the strict
exact-window formulation of Bridgeland's Lemma 4.3. The formal quasi-abelian
window structure and its comparison are separate proof work; no provider
for them is asserted here.

These are definitions of stability data. They assert no existence on an
arbitrary triangulated category or variety.

Sources: Bridgeland, *Stability conditions on triangulated categories*,
https://arxiv.org/abs/math/0212237, Definition 3.3, Lemma 4.3 and
Definitions 5.1/5.7; Kontsevich--Soibelman,
https://arxiv.org/abs/0811.2435, Section 1, numerical support property.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.BridgelandStability

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Pretriangulated
open MathlibExt.CategoryTheory.TriangulatedGrothendieck
open scoped ZeroObject

universe u v

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- An actual object-property candidate for a real-indexed slicing. -/
abbrev SliceFamily := ℝ → ObjectProperty C

/-- The general HN tower; no heart, quiver or variety is chosen. -/
structure HNFiltration (P : SliceFamily C) (E : C) where
  length : ℕ
  stages : Fin (length + 1) → C
  pieces : Fin length → C
  phases : Fin length → ℝ
  start : IsZero (stages 0)
  finish : stages (Fin.last length) ≅ E
  arrow : ∀ i : Fin length, stages i.castSucc ⟶ stages i.succ
  toPiece : ∀ i : Fin length, stages i.succ ⟶ pieces i
  boundary : ∀ i : Fin length, pieces i ⟶ (stages i.castSucc)⟦(1 : ℤ)⟧
  distinguished : ∀ i : Fin length,
    Triangle.mk (arrow i) (toPiece i) (boundary i) ∈ distTriang C
  semistable : ∀ i : Fin length, P (phases i) (pieces i)
  nonzero : ∀ i : Fin length, ¬ IsZero (pieces i)
  decreasing : StrictAnti phases

/-- A nonzero object cannot be represented by an empty HN tower. -/
theorem HNFiltration.length_pos {P : SliceFamily C} {E : C}
    (F : HNFiltration C P E) (hE : ¬ IsZero E) : 0 < F.length := by
  apply Nat.pos_of_ne_zero
  intro hlength
  have hindex : Fin.last F.length = (0 : Fin (F.length + 1)) :=
    Fin.ext (by simpa using hlength)
  have hz : IsZero (F.stages (Fin.last F.length)) := by
    rw [hindex]
    exact F.start
  exact hE (IsZero.of_iso hz F.finish.symm)

/-- The slicing axioms, on the actual category and its actual maps. -/
structure SlicingLaws (P : SliceFamily C) : Prop where
  zero : ∀ phi : ℝ, P phi (0 : C)
  isomorphic : ∀ phi (E F : C), Nonempty (E ≅ F) → P phi E → P phi F
  extensions : ∀ phi (T : Triangle C), T ∈ distTriang C →
    P phi T.obj₁ → P phi T.obj₃ → P phi T.obj₂
  shift : ∀ phi (E : C), P phi E ↔ P (phi + 1) (E⟦(1 : ℤ)⟧)
  hom_vanishing : ∀ phi psi, psi < phi → ∀ E F : C,
    P phi E → P psi F → Subsingleton (E ⟶ F)
  harderNarasimhan : ∀ E : C, Nonempty (HNFiltration C P E)

/-- A slicing is a candidate equipped with its actual axioms. -/
structure Slicing where
  family : SliceFamily C
  laws : SlicingLaws C family

/-- Actual extension-window membership, via a distinguished-triangle HN tower. -/
def InPhaseWindow (P : SliceFamily C) (a b : ℝ) (E : C) : Prop :=
  ∃ F : HNFiltration C P E, ∀ i, a < F.phases i ∧ F.phases i < b

/-- The strict admissible-mono formulation in a phase window, through
an actual distinguished triangle with third object in that window. -/
def WindowAdmissible {A B : C} (W : ObjectProperty C) (f : A ⟶ B) : Prop :=
  W A ∧ W B ∧ ∃ Q : C, W Q ∧ ∃ (g : B ⟶ Q) (h : Q ⟶ A⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang C

/-- A chain of actual strict window subobjects of the fixed object E. -/
structure WindowSubobjectChain (W : ObjectProperty C) (E : C) (length : ℕ) where
  objects : Fin (length + 1) → C
  member : ∀ i, W (objects i)
  inclusion : ∀ i, objects i ⟶ E
  admissible_inclusion : ∀ i, WindowAdmissible C W (inclusion i)
  arrow : ∀ i : Fin length, objects i.castSucc ⟶ objects i.succ
  compatible : ∀ i : Fin length, arrow i ≫ inclusion i.succ = inclusion i.castSucc
  admissible_arrow : ∀ i : Fin length, WindowAdmissible C W (arrow i)
  strict : ∀ i : Fin length, ¬ IsIso (arrow i)

/-- An optional quantitative bound on actual finite chains inside a fixed object. -/
def WindowChainLengthBound (W : ObjectProperty C) : Prop :=
  ∀ E : C, W E → ∃ N : ℕ, ∀ length : ℕ,
    Nonempty (WindowSubobjectChain C W E length) → length ≤ N

/-- No infinite ascending chain of actual strict window subobjects of E. -/
def WindowNoetherian (W : ObjectProperty C) : Prop :=
  ∀ E : C, W E → ∀ (A : ℕ → C) (inc : ∀ n, A n ⟶ E)
    (f : ∀ n, A n ⟶ A (n + 1)),
    (∀ n, W (A n)) →
    (∀ n, WindowAdmissible C W (inc n)) →
    (∀ n, f n ≫ inc (n + 1) = inc n) →
    (∀ n, WindowAdmissible C W (f n)) →
    (∀ n, ¬ IsIso (f n)) → False

/-- No infinite descending chain of actual strict window subobjects of E. -/
def WindowArtinian (W : ObjectProperty C) : Prop :=
  ∀ E : C, W E → ∀ (A : ℕ → C) (inc : ∀ n, A n ⟶ E)
    (f : ∀ n, A (n + 1) ⟶ A n),
    (∀ n, W (A n)) →
    (∀ n, WindowAdmissible C W (inc n)) →
    (∀ n, f n ≫ inc n = inc (n + 1)) →
    (∀ n, WindowAdmissible C W (f n)) →
    (∀ n, ¬ IsIso (f n)) → False

/-- Actual strict finite length means both ascending and descending chain conditions. -/
def WindowFiniteLength (W : ObjectProperty C) : Prop :=
  WindowNoetherian C W ∧ WindowArtinian C W

/-- The actual small-window local-finiteness contract. -/
def LocallyFinite (P : SliceFamily C) : Prop :=
  ∃ e : ℝ, 0 < e ∧ 2 * e < 1 ∧ ∀ phi : ℝ,
    WindowFiniteLength C (InPhaseWindow C P (phi - e) (phi + e))

/-- A chosen numerical realization of actual K0 in a concrete finite-rank lattice. -/
structure NumericalCharge (rank : ℕ) where
  classMap : K0 C →+ (Fin rank → ℤ)
  charge : (Fin rank → ℤ) →+ ℂ

variable {C}

/-- The actual numerical class of E, obtained from its canonical K0 class. -/
def NumericalCharge.ofObject {rank : ℕ} (N : NumericalCharge C rank) (E : C) :
    Fin rank → ℤ := N.classMap (classOf C E)

/-- The actual central charge of that class. -/
def NumericalCharge.objectCharge {rank : ℕ} (N : NumericalCharge C rank) (E : C) : ℂ :=
  N.charge (N.ofObject E)

/-- The fixed l1 norm on the actual integer lattice. -/
def latticeNorm {rank : ℕ} (v : Fin rank → ℤ) : ℝ := ∑ i, |(v i : ℝ)|

/-- The general locally finite Bridgeland stability datum with charge on
actual K0. It need not factor through a finite-rank numerical realization. -/
structure StabilityCondition (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] where
  charge : K0 C →+ ℂ
  slicing : Slicing C
  phase_charge : ∀ phi (E : C), slicing.family phi E → ¬ IsZero E →
    ∃ r : ℝ, 0 < r ∧ charge (classOf C E) =
      (r : ℂ) * Complex.exp ((phi * Real.pi : ℝ) * Complex.I)
  locallyFinite : LocallyFinite C slicing.family

/-- A zero-charge placeholder cannot supply a stability condition on a
nonzero actual category: positive phases and the actual HN pieces rule it out. -/
theorem StabilityCondition.isZero_of_charge_zero [IsTriangulated C]
    (s : StabilityCondition C) (hzero : s.charge = 0) (E : C) : IsZero E := by
  by_contra hE
  obtain ⟨F⟩ := s.slicing.laws.harderNarasimhan E
  let i : Fin F.length := ⟨0, HNFiltration.length_pos C F hE⟩
  obtain ⟨r, hr, hcharge⟩ := s.phase_charge (F.phases i) (F.pieces i)
    (F.semistable i) (F.nonzero i)
  rw [hzero, AddMonoidHom.zero_apply] at hcharge
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr))
    (Complex.exp_ne_zero _) hcharge.symm

/-- All stability data and support/local-finiteness laws, with no existence assertion. -/
structure NumericalStabilityCondition (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] (rank : ℕ) where
  numerical : NumericalCharge C rank
  slicing : Slicing C
  phase_charge : ∀ phi (E : C), slicing.family phi E → ¬ IsZero E →
    ∃ r : ℝ, 0 < r ∧ numerical.objectCharge E =
      (r : ℂ) * Complex.exp ((phi * Real.pi : ℝ) * Complex.I)
  locallyFinite : LocallyFinite C slicing.family
  supportConstant : ℝ
  supportPositive : 0 < supportConstant
  support : ∀ phi (E : C), slicing.family phi E →
    latticeNorm (numerical.ofObject E) ≤ supportConstant * ‖numerical.objectCharge E‖

/-- A numerical support datum forgets to the general actual stability datum. -/
def NumericalStabilityCondition.toStabilityCondition [IsTriangulated C] {rank : ℕ}
    (s : NumericalStabilityCondition C rank) : StabilityCondition C where
  charge := s.numerical.charge.comp s.numerical.classMap
  slicing := s.slicing
  phase_charge := s.phase_charge
  locallyFinite := s.locallyFinite

/-- Numerical classes are normalized on actual distinguished triangles. -/
theorem NumericalCharge.ofObject_triangle {rank : ℕ} (N : NumericalCharge C rank)
    {T : Triangle C} (hT : T ∈ distTriang C) :
    N.ofObject T.obj₂ = N.ofObject T.obj₁ + N.ofObject T.obj₃ := by
  simp only [NumericalCharge.ofObject, classOf_triangle hT, map_add]

/-- The actual charge has the same distinguished-triangle additivity. -/
theorem NumericalCharge.objectCharge_triangle {rank : ℕ} (N : NumericalCharge C rank)
    {T : Triangle C} (hT : T ∈ distTriang C) :
    N.objectCharge T.obj₂ = N.objectCharge T.obj₁ + N.objectCharge T.obj₃ := by
  simp only [NumericalCharge.objectCharge, N.ofObject_triangle hT, map_add]

/-- Chosen numerical realizations preserve actual object isomorphisms. -/
theorem NumericalCharge.ofObject_iso {rank : ℕ} (N : NumericalCharge C rank)
    {E F : C} (e : E ≅ F) : N.ofObject E = N.ofObject F :=
  congrArg N.classMap (classOf_iso e)

/-- Their actual complex charges preserve those isomorphisms. -/
theorem NumericalCharge.objectCharge_iso {rank : ℕ} (N : NumericalCharge C rank)
    {E F : C} (e : E ≅ F) : N.objectCharge E = N.objectCharge F :=
  congrArg N.charge (N.ofObject_iso e)

/-- The numerical class of a genuine shift has the genuine negative sign. -/
theorem NumericalCharge.ofObject_shift_one {rank : ℕ} (N : NumericalCharge C rank)
    (E : C) : N.ofObject (E⟦(1 : ℤ)⟧) = -N.ofObject E := by
  simp only [NumericalCharge.ofObject, classOf_shift_one, map_neg]

/-- Charge sign agrees with the phase shift by one. -/
theorem NumericalCharge.objectCharge_shift_one {rank : ℕ} (N : NumericalCharge C rank)
    (E : C) : N.objectCharge (E⟦(1 : ℤ)⟧) = -N.objectCharge E := by
  simp only [NumericalCharge.objectCharge, N.ofObject_shift_one E, map_neg]

end MathlibExt.CategoryTheory.BridgelandStability
