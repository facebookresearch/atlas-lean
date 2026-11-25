/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Topology.Instances.Complex
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Actual complex flags as Hermitian projection matrices

The topology is the actual Euclidean subspace topology on a finite tuple of
complex matrices. Nested Hermitian idempotents and their integer traces
specify the flag. The associated subspaces are literal linear-map ranges;
their dimensions and inclusions are proved using Mathlib's completed
projection/trace theorem. No general rank--trace lemma is requested here.

The explicit standard flag in dimension three supplies a concrete geometric
point for the Bott--Samelson and point-class normalizations.

Reference: Fulton, *Young Tableaux*, Chapters 9--10, the complex full flag
manifold. Mathlib's `LinearMap.IsProj.trace` is reused directly.
-/

@[expose] public noncomputable section

namespace MathlibExt.LinearAlgebra.HermitianFlags

open _root_.CategoryTheory

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

structure IsFlagProjectors {n : ℕ} (p : Fin (n + 1) → Mat n) : Prop where
  zero : p 0 = 0
  top : p (Fin.last n) = 1
  hermitian : ∀ i, (p i).conjTranspose = p i
  idempotent : ∀ i, p i * p i = p i
  trace : ∀ i, (p i).trace = (i.val : ℂ)
  nested : ∀ i j, p i * p j = p (min i j)

abbrev Flag (n : ℕ) := {p : Fin (n + 1) → Mat n // IsFlagProjectors p}
abbrev flagSpace (n : ℕ) : TopCat.{0} := TopCat.of (Flag n)

def subspace {n : ℕ} (F : Flag n) (i : Fin (n + 1)) := LinearMap.range (F.val i).toLin'

theorem subspace_rank {n : ℕ} (F : Flag n) (i : Fin (n + 1)) :
    Module.finrank ℂ (subspace F i) = i.val := by
  have he : IsIdempotentElem (F.val i).toLin' :=
    IsIdempotentElem.map (F.property.idempotent i)
      (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n))
  have h := LinearMap.IsProj.trace (LinearMap.IsIdempotentElem.isProj_range _ he)
  rw [Matrix.trace_toLin'_eq, F.property.trace] at h
  exact Nat.cast_injective h.symm

theorem subspace_mono {n : ℕ} (F : Flag n) {i j : Fin (n + 1)} (hij : i ≤ j) :
    subspace F i ≤ subspace F j := by
  rintro x ⟨y, rfl⟩
  refine ⟨(F.val i).toLin' y, ?_⟩
  change ((F.val j).toLin' ∘ₗ (F.val i).toLin') y = (F.val i).toLin' y
  rw [← Matrix.toLin'_mul, F.property.nested, min_eq_right hij]

/-- Coordinate line and coordinate plane of the standard flag in C³. -/
def standardMatrices : Fin 4 → Mat 3 :=
  ![0, Matrix.diagonal ![1, 0, 0], Matrix.diagonal ![1, 1, 0], 1]

def standardFlag : Flag 3 := ⟨standardMatrices, {
  zero := rfl
  top := rfl
  hermitian := by
    intro i
    ext j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [standardMatrices]
  idempotent := by
    intro i
    ext j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [standardMatrices, Matrix.mul_apply, Fin.sum_univ_three]
  trace := by
    intro i
    fin_cases i <;> norm_num [standardMatrices, Matrix.trace, Fin.sum_univ_three]
  nested := by
    intro i j
    ext k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [standardMatrices, Matrix.mul_apply, Fin.sum_univ_three]
}⟩

end MathlibExt.LinearAlgebra.HermitianFlags
