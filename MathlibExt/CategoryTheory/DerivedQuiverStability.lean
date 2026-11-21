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

abbrev heartCharge (z : V → ℂ) (M : Representations k V) : ℂ :=
  centralCharge V z (dimensionVector k V M)

def heartPhase (z : V → ℂ) (M : Representations k V) : ℝ :=
  (heartCharge k V z M).arg / Real.pi

/-- Semistability tests every actual nonzero subrepresentation by its charge phase. -/
def HeartSemistable (z : V → ℂ) (M : Representations k V) : Prop :=
  ¬ IsZero M ∧ ∀ (A : Representations k V) (i : A ⟶ M), Mono i → ¬ IsZero A →
    heartPhase k V z A ≤ heartPhase k V z M

/-- The literal alternating Euler class of actual cohomology at each vertex. -/
def numericalClass (K : D k V) (v : V) : ℤ :=
  GradedObject.eulerChar (ComplexShape.up ℤ) (fun n ↦
    (forget₂ (FGModuleCat.{0} k) (ModuleCat.{0} k)).obj
      ((cohomology k V K n).obj ((Paths.of V).obj v)))

abbrev derivedCharge (z : V → ℂ) (K : D k V) : ℂ :=
  centralCharge V z (numericalClass k V K)

/-- A concrete l1 norm on the actual vertex Euler class. -/
def numericalNorm (K : D k V) : ℝ := ∑ v : V, (|numericalClass k V K v| : ℤ)

/-- A shift by m raises phase by m: H^n(K) has phase phi+n. -/
def slicing (z : V → ℂ) (phi : ℝ) : ObjectProperty (D k V) := fun K ↦
  Bounded k V K ∧ ∀ n : ℤ, ¬ IsZero (cohomology k V K n) →
    HeartSemistable k V z (cohomology k V K n) ∧
      heartPhase k V z (cohomology k V K n) - (n : ℝ) = phi

/-- An actual distinguished-triangle HN tower, with literal stages and nonzero pieces. -/
abbrev HNFiltration (z : V → ℂ) (K : D k V) :=
  MathlibExt.CategoryTheory.BridgelandStability.HNFiltration (D k V) (slicing k V z) K

/-- The actual extension window of slicing objects, via a finite triangle tower. -/
def InPhaseWindow (z : V → ℂ) (a b : ℝ) (K : D k V) : Prop :=
  ∃ F : HNFiltration k V z K, ∀ i, a < F.phases i ∧ F.phases i < b

/-- The requested laws concern only the fixed candidate slicing and computed charge. -/
structure SlicingLaws (z : V → ℂ) : Prop where
  zero : ∀ phi : ℝ, slicing k V z phi (0 : D k V)
  isomorphic : ∀ (phi : ℝ) (K L : D k V), Nonempty (K ≅ L) →
    slicing k V z phi K → slicing k V z phi L
  extensions : ∀ (phi : ℝ) (T : _root_.CategoryTheory.Pretriangulated.Triangle (D k V)),
    T ∈ distTriang (D k V) → slicing k V z phi T.obj₁ → slicing k V z phi T.obj₃ →
      slicing k V z phi T.obj₂
  phase_charge : ∀ (phi : ℝ) (K : D k V), slicing k V z phi K → ¬ IsZero K →
    ∃ m : ℝ, 0 < m ∧ derivedCharge k V z K =
      (m : ℂ) * Complex.exp ((phi * Real.pi : ℝ) * Complex.I)
  shift : ∀ (phi : ℝ) (K : D k V),
    slicing k V z phi K ↔ slicing k V z (phi + 1) (K⟦(1 : ℤ)⟧)
  hom_vanishing : ∀ (phi psi : ℝ), psi < phi →
    ∀ (K L : D k V), slicing k V z phi K → slicing k V z psi L → Subsingleton (K ⟶ L)
  harderNarasimhan : ∀ K : D k V, Bounded k V K → Nonempty (HNFiltration k V z K)
  support : ∃ C : ℝ, 0 < C ∧ ∀ (phi : ℝ) (K : D k V), slicing k V z phi K →
    C * numericalNorm k V K ≤ ‖derivedCharge k V z K‖
  local_window : ∃ e : ℝ, 0 < e ∧ ∀ phi : ℝ, ∃ n : ℤ,
    ∀ K : D k V, InPhaseWindow k V z (phi - e) (phi + e) K →
      ∀ j : ℤ, j ≠ n → IsZero (cohomology k V K j)

end MathlibExt.CategoryTheory.DerivedQuiverStability
