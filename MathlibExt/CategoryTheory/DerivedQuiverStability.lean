/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.CategoryTheory.Triangulated.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import MathlibExt.CategoryTheory.Triangulated.BridgelandStability

/-!
# A concrete bounded derived quiver slicing and numerical support packet

Representations are actual functors from the path category of the quiver
to finitely generated vector spaces. The candidate slicing is fixed by
actual derived cohomology, actual subobjects and the argument of a vertex
central charge. The numerical class is the actual alternating Euler sum
of those finite-dimensional cohomology spaces. HN data are finite towers
of actual distinguished triangles with strictly decreasing phases.

Sources: Bridgeland, *Stability conditions on triangulated categories*,
https://arxiv.org/abs/math/0212237, Proposition2.4, Proposition5.3 and
Example5.5. The support inequality uses the concrete vertex-dimension
lattice, as in the support-property formulation of Kontsevich--Soibelman,
https://arxiv.org/abs/0811.2435, Section1. No full moduli/wall-crossing or
geometric K3-surface stability interface is claimed by this finite-quiver
packet. Generic Euler/K0 comparison is already covered mathematical
support and is not re-requested here.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DerivedQuiverStability

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard

variable (k V : Type) [Field k] [Quiver V] [Fintype V]

/-- Actual finite-dimensional quiver representations. -/
abbrev Representations := Paths V ⥤ FGModuleCat.{0} k

abbrev D := DerivedCategory (Representations k V)

/-- Actual standard cohomology representations. -/
abbrev cohomology (K : D k V) (n : ℤ) : Representations k V :=
  (DerivedCategory.homologyFunctor (Representations k V) n).obj K

/-- Boundedness is finite support of the actual nonzero cohomology objects. -/
def Bounded (K : D k V) : Prop := {n : ℤ | ¬ IsZero (cohomology k V K n)}.Finite

/-- The actual vertex dimension vector of a heart object. -/
def dimensionVector (M : Representations k V) (v : V) : ℤ :=
  Module.finrank k (M.obj ((Paths.of V).obj v))

/-- The actual additive central charge on the concrete numerical lattice. -/
def centralCharge (z : V → ℂ) : (V → ℤ) →+ ℂ where
  toFun d := ∑ v : V, (d v : ℂ) * z v
  map_zero' := by simp
  map_add' d e := by simp [add_mul, Finset.sum_add_distrib]

/-- Vertex charges in the upper half-plane. Their central charge is a stability function
on the finite-length heart of finite-dimensional representations: it sends every nonzero
representation to the upper half-plane (Bridgeland, Definition 2.1 and Example 5.5). -/
structure VertexCharges where
  /-- The charge of each vertex. -/
  charge : V → ℂ
  /-- Every vertex charge has positive imaginary part. -/
  im_pos : ∀ v, 0 < (charge v).im

variable {V} in
/-- The charge of a representation: the central charge of its dimension vector. -/
abbrev heartCharge (Z : VertexCharges V) (M : Representations k V) : ℂ :=
  centralCharge V Z.charge (dimensionVector k V M)

variable {V} in
/-- The phase `arg Z(M) / π` of a representation. For a nonzero representation `Z(M)`
lies in the upper half-plane, so its phase lies in `(0, 1)`; the phase is only used for
nonzero representations. -/
def heartPhase (Z : VertexCharges V) (M : Representations k V) : ℝ :=
  (heartCharge k Z M).arg / Real.pi

variable {V} in
/-- Semistability tests every actual nonzero subrepresentation by its charge phase. -/
def HeartSemistable (Z : VertexCharges V) (M : Representations k V) : Prop :=
  ¬ IsZero M ∧ ∀ (A : Representations k V) (i : A ⟶ M), Mono i → ¬ IsZero A →
    heartPhase k Z A ≤ heartPhase k Z M

/-- The bounded objects of the derived category. -/
abbrev BoundedDerivedQuiver := (show ObjectProperty (D k V) from Bounded k V).FullSubcategory

/-- The numerical class of a bounded object: at each vertex `v`, the alternating sum
`∑ₙ (-1)ⁿ dim H^n(K)_v` of the dimensions of its cohomology at `v`. Boundedness makes the
sum finite, so this is the Euler characteristic; it is not defined on unbounded objects. -/
def numericalClass (K : D k V) (_hK : Bounded k V K) (v : V) : ℤ :=
  GradedObject.eulerChar (ComplexShape.up ℤ) (fun n ↦
    (forget₂ (FGModuleCat.{0} k) (ModuleCat.{0} k)).obj
      ((cohomology k V K n).obj ((Paths.of V).obj v)))

/-- The central charge of a bounded object, evaluated on its numerical class. -/
abbrev derivedCharge (z : V → ℂ) (K : D k V) (hK : Bounded k V K) : ℂ :=
  centralCharge V z (numericalClass k V K hK)

/-- The l¹ norm of the numerical class of a bounded object. -/
def numericalNorm (K : D k V) (hK : Bounded k V K) : ℝ :=
  ∑ v : V, (|numericalClass k V K hK v| : ℤ)

variable {V} in
/-- A shift by m raises phase by m: H^n(K) has phase phi+n. -/
def slicing (Z : VertexCharges V) (phi : ℝ) : ObjectProperty (D k V) := fun K ↦
  Bounded k V K ∧ ∀ n : ℤ, ¬ IsZero (cohomology k V K n) →
    HeartSemistable k Z (cohomology k V K n) ∧
      heartPhase k Z (cohomology k V K n) - (n : ℝ) = phi

variable {V} in
/-- An actual distinguished-triangle HN tower, with literal stages and nonzero pieces. -/
abbrev HNFiltration (Z : VertexCharges V) (K : D k V) :=
  MathlibExt.CategoryTheory.BridgelandStability.HNFiltration (D k V) (slicing k Z) K

variable {V} in
/-- The actual extension window of slicing objects, via a finite triangle tower. -/
abbrev InPhaseWindow (Z : VertexCharges V) (a b : ℝ) (K : D k V) : Prop :=
  MathlibExt.CategoryTheory.BridgelandStability.InPhaseWindow (D k V) (slicing k Z) a b K

variable {V} in
/-- The requested laws concern only the fixed candidate slicing and computed charge. -/
structure SlicingLaws (Z : VertexCharges V) : Prop where
  zero : ∀ phi : ℝ, slicing k Z phi (0 : D k V)
  isomorphic : ∀ (phi : ℝ) (K L : D k V), Nonempty (K ≅ L) →
    slicing k Z phi K → slicing k Z phi L
  extensions : ∀ (phi : ℝ) (T : _root_.CategoryTheory.Pretriangulated.Triangle (D k V)),
    T ∈ distTriang (D k V) → slicing k Z phi T.obj₁ → slicing k Z phi T.obj₃ →
      slicing k Z phi T.obj₂
  phase_charge : ∀ (phi : ℝ) (K : D k V) (hK : slicing k Z phi K), ¬ IsZero K →
    ∃ m : ℝ, 0 < m ∧ derivedCharge k V Z.charge K hK.1 =
      (m : ℂ) * Complex.exp ((phi * Real.pi : ℝ) * Complex.I)
  shift : ∀ (phi : ℝ) (K : D k V),
    slicing k Z phi K ↔ slicing k Z (phi + 1) (K⟦(1 : ℤ)⟧)
  hom_vanishing : ∀ (phi psi : ℝ), psi < phi →
    ∀ (K L : D k V), slicing k Z phi K → slicing k Z psi L → Subsingleton (K ⟶ L)
  harderNarasimhan : ∀ K : D k V, Bounded k V K → Nonempty (HNFiltration k Z K)
  support : ∃ C : ℝ, 0 < C ∧ ∀ (phi : ℝ) (K : D k V) (hK : slicing k Z phi K),
    C * numericalNorm k V K hK.1 ≤ ‖derivedCharge k V Z.charge K hK.1‖
  local_window : ∃ e : ℝ, 0 < e ∧ ∀ phi : ℝ, ∃ n : ℤ,
    ∀ K : D k V, InPhaseWindow k Z (phi - e) (phi + e) K →
      ∀ j : ℤ, j ≠ n → IsZero (cohomology k V K j)

end MathlibExt.CategoryTheory.DerivedQuiverStability
