/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.AffineTangent
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

/-! Tests for affine Zariski closures, tangent spaces and addition images. -/

open MvPolynomial MathlibExt.AlgebraicGeometry.AffineTangent
open scoped Pointwise

variable {k σ : Type*} [Field k]

/-! ### Zariski closure -/

-- Membership in the closure: every polynomial vanishing on the set vanishes at the point.
example (S : Set (σ → k)) (x : σ → k) :
    x ∈ zariskiClosure S ↔ ∀ f : MvPolynomial σ k, (∀ y ∈ S, eval y f = 0) → eval x f = 0 :=
  mem_zariskiClosure_iff

-- The closure contains the set, and the closure of the empty set is empty.
example (S : Set (σ → k)) : S ⊆ zariskiClosure S := subset_zariskiClosure S

example : zariskiClosure (∅ : Set (σ → k)) = ∅ := by simp

-- The closure is the smallest zero locus containing the set.
example (S : Set (σ → k)) (I : Ideal (MvPolynomial σ k)) (h : S ⊆ zeroLocus k I) :
    zariskiClosure S ⊆ zeroLocus k I :=
  zariskiClosure_subset_zeroLocus h

-- Zero loci are closed, so closure is idempotent.
example (I : Ideal (MvPolynomial σ k)) : zariskiClosure (zeroLocus k I) = zeroLocus k I :=
  zariskiClosure_zeroLocus I

example (S : Set (σ → k)) : zariskiClosure (zariskiClosure S) = zariskiClosure S :=
  zariskiClosure_zariskiClosure S

-- A point outside a coordinate hyperplane is not in the closure of a set inside it.
example (S : Set (σ → k)) (i : σ) (hS : ∀ y ∈ S, y i = 0) (x : σ → k) (hx : x i ≠ 0) :
    x ∉ zariskiClosure S := fun h =>
  hx (by simpa using mem_zariskiClosure_iff.mp h (X i) (fun y hy => by simpa using hS y hy))

/-! ### Addition images -/

example (X Y : Set (σ → k)) (p q : σ → k) (hp : p ∈ X) (hq : q ∈ Y) :
    p + q ∈ additionImageClosure X Y :=
  add_subset_additionImageClosure X Y (Set.add_mem_add hp hq)

-- Adding the origin does not change a set, so its addition image is its closure.
example (Y : Set (σ → k)) : additionImageClosure 0 Y = zariskiClosure Y := by
  rw [additionImageClosure, zero_add]

-- The addition image of empty sets is empty.
example (Y : Set (σ → k)) : additionImageClosure ∅ Y = ∅ := by
  simp [additionImageClosure]

/-! ### Differentials and tangent spaces -/

section Tangent

variable [Fintype σ]

-- The differential of a coordinate is the coordinate projection; constants have differential 0.
example (i : σ) (p v : σ → k) : differential (X i : MvPolynomial σ k) p v = v i := by simp

example (a : k) (p v : σ → k) : differential (C a : MvPolynomial σ k) p v = 0 := by simp

-- The Leibniz rule on a product of coordinates.
example (i j : σ) (p v : σ → k) :
    differential (X i * X j : MvPolynomial σ k) p v = p i * v j + p j * v i := by
  simp [differential_mul]

-- Scheme-theoretic tangent space of a coordinate hyperplane at one of its points.
example (i : σ) (p : σ → k) (hp : p i = 0) (v : σ → k) :
    v ∈ tangentIdeal (Ideal.span {(X i : MvPolynomial σ k)}) p ↔ v i = 0 := by
  rw [tangentIdeal_span (by simpa using hp)]
  simp

-- The tangent space of a reduced point is zero.
example (p : σ → k) : tangentSet {p} p = ⊥ := by
  refine eq_bot_iff.mpr fun v hv => ?_
  rw [Submodule.mem_bot]
  funext i
  have h := mem_tangentSet_iff.mp hv (X i - C (p i)) (by simp)
  rw [differential_sub] at h
  simpa using h

-- The empty set has the unit vanishing ideal, whose tangent space is zero at every point.
example (p : σ → k) : tangentSet (∅ : Set (σ → k)) p = ⊥ := by
  refine eq_bot_iff.mpr fun v hv => ?_
  rw [Submodule.mem_bot]
  funext i
  simpa using mem_tangentSet_iff.mp hv (X i) (by simp)

-- Off the zero locus, the tangent space of an ideal can be smaller than the kernel of its
-- generator's differential: `f = X ^ 2 - 1` has `df₀(1) = 0`, but `X * f ∈ (f)` has
-- `d(X * f)₀(1) = -1`.
example : differential (X () ^ 2 - 1 : MvPolynomial Unit k) 0 (fun _ => 1) = 0 ∧
    (fun _ => (1 : k)) ∉ tangentIdeal (Ideal.span {(X () ^ 2 - 1 : MvPolynomial Unit k)}) 0 := by
  refine ⟨by simp [differential_sub, pow_two, differential_mul], fun h => ?_⟩
  have hmem : (X () * (X () ^ 2 - 1) : MvPolynomial Unit k) ∈ Ideal.span {X () ^ 2 - 1} :=
    Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have := mem_tangentIdeal_iff.mp h _ hmem
  simp [differential_mul, differential_sub, pow_two] at this

-- `tangentSet` only sees the `k`-points: over `𝔽₂` the polynomial `X ^ 2 - X` vanishes on the
-- whole line, so the tangent space of its `𝔽₂`-points is zero, while the line itself, cut out by
-- the zero ideal, has the full tangent space.
example : tangentSet (Set.univ : Set (Unit → ZMod 2)) 0 = ⊥ ∧
    tangentIdeal (⊥ : Ideal (MvPolynomial Unit (ZMod 2))) 0 = ⊤ := by
  refine ⟨eq_bot_iff.mpr fun v hv => ?_, eq_top_iff.mpr fun v _ => ?_⟩
  · have hvan : ∀ y : Unit → ZMod 2, eval y (X () ^ 2 - X () : MvPolynomial Unit (ZMod 2)) = 0 :=
      fun y => by
        have : ∀ a : ZMod 2, a ^ 2 - a = 0 := by decide
        simpa using this (y ())
    have h := mem_tangentSet_iff.mp hv (X () ^ 2 - X ()) fun y _ => hvan y
    rw [Submodule.mem_bot]
    funext u
    simpa [differential_sub, pow_two, differential_mul] using h
  · exact mem_tangentIdeal_iff.mpr fun f hf => by simp [(Ideal.mem_bot).mp hf]

end Tangent

/-! ### Compatibility with the `Fin n` tangent-space API -/

example {n : ℕ} (f : MvPolynomial (Fin n) k) (p : Fin n → k) :
    differential f p = totalDerivativeAtLin f p :=
  differential_eq_totalDerivativeAtLin f p

example {n : ℕ} (I : Ideal (MvPolynomial (Fin n) k)) (p : Fin n → k) :
    tangentIdeal I p = tangentSpaceIdeal I p :=
  tangentIdeal_eq_tangentSpaceIdeal I p

example {n : ℕ} (S : Set (Fin n → k)) (p v : Fin n → k) :
    v ∈ tangentSet S p ↔ ∀ f ∈ vanishingIdeal k S, totalDerivativeAt f p v = 0 := by
  rw [tangentSet, tangentIdeal_eq_tangentSpaceIdeal, mem_tangentSpaceIdeal]
