/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GroupZeroCotangentModels
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.Ring

/-!
# Integral p-power roots and their actual dlog cotangent classes

The coefficient ring of mu_(p^n) is the literal quotient
R[T]/(T^(p^n)-1), retaining nilpotents and the original integral R.
The origin of dlog is the class of T-1 at the actual augmentation.
Based root units in any original augmented algebra map additively to
that algebra's I/I² by u |-> [u-1].

When a unit is the coordinate of an actual Cartier character of a
finite affine group scheme, this is precisely its pulled-back dlog.
The generic Tate-to-character and formal-cotangent inverse-limit
comparisons remain separate geometric maps. Nothing here inverts p
before forming the finite zero-section cotangents.

References: Scholze--Weinstein, arXiv:1211.6357v2, Hodge--Tate sequence
in Section 1; Fargues, *La filtration de Harder--Narasimhan des schémas
en groupes finis et plats*, the integral Hodge--Tate morphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IntegralRootDlogModels

open _root_.CategoryTheory
open GroupZeroCotangentModels

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]

/-- The original p-power equation, as an ideal of the full polynomial ring. -/
def rootIdeal (n : ℕ) : Ideal (Polynomial R) :=
  Ideal.span {Polynomial.X ^ (p ^ n) - 1}

/-- The full integral coordinate ring of mu_(p^n). -/
abbrev RootRing (n : ℕ) := Polynomial R ⧸ rootIdeal p R n

/-- Its actual torus coordinate, including its nilpotent information. -/
def rootCoordinate (n : ℕ) : RootRing p R n :=
  Ideal.Quotient.mk (rootIdeal p R n) Polynomial.X

omit [Fact p.Prime] in
/-- The coordinate satisfies the original equation in the unreduced quotient ring. -/
theorem root_coordinate_power (n : ℕ) : rootCoordinate p R n ^ (p ^ n) = 1 := by
  have h : Ideal.Quotient.mk (rootIdeal p R n) (Polynomial.X ^ (p ^ n) - 1) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton _)
  simpa only [map_sub, map_pow, map_one, sub_eq_zero, rootCoordinate] using h

/-- The coordinate is an actual unit, using p^n>0 over every coefficient ring. -/
def rootUnit (n : ℕ) : (RootRing p R n)ˣ where
  val := rootCoordinate p R n
  inv := rootCoordinate p R n ^ (p ^ n - 1)
  val_inv := by
    have hn : p ^ n - 1 + 1 = p ^ n := Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n (Fact.out : p.Prime).ne_zero))
    rw [mul_comm, ← pow_succ, hn, root_coordinate_power]
  inv_val := by
    have hn : p ^ n - 1 + 1 = p ^ n := Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n (Fact.out : p.Prime).ne_zero))
    rw [← pow_succ, hn, root_coordinate_power]

/-- The actual identity evaluation T |-> 1 on this quotient. -/
def rootAugmentation (n : ℕ) : RootRing p R n →ₐ[R] R :=
  Ideal.Quotient.liftₐ (rootIdeal p R n) (Polynomial.aeval (1 : R)) (by
    have h : rootIdeal p R n ≤ RingHom.ker (Polynomial.aeval (1 : R)).toRingHom := by
      apply Ideal.span_le.mpr
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      simp
    exact fun a ha ↦ h ha)

/-- The coefficient algebra and its exact identity augmentation. -/
def rootAlgebra (n : ℕ) : AugmentedAlgebra R where
  ring := CommAlgCat.of R (RootRing p R n)
  augmentation := rootAugmentation p R n

/-- The original T-1 element in the actual augmentation ideal. -/
def rootOrigin (n : ℕ) : (rootAlgebra p R n).ideal R := by
  let a : (rootAlgebra p R n).ring := rootCoordinate p R n
  refine ⟨a - 1, ?_⟩
  change rootAugmentation p R n (rootCoordinate p R n - (1 : RootRing p R n)) = 0
  simp [rootAugmentation, rootCoordinate]

/-- The integral dlog generator is the literal T-1 cotangent class. -/
def rootDlog (n : ℕ) : (rootAlgebra p R n).cotangent R :=
  ((rootAlgebra p R n).ideal R).toCotangent (rootOrigin p R n)

variable (A : AugmentedAlgebra R)

/-- Actual p-power root units based at the original identity section. -/
def basedRoots (n : ℕ) : Subgroup A.ringˣ where
  carrier := {u | u ^ (p ^ n) = 1 ∧ A.augmentation (u : A.ring) = 1}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    constructor
    · rw [mul_pow, hu.1, hv.1, one_mul]
    · change A.augmentation ((u : A.ring) * (v : A.ring)) = 1
      rw [map_mul, hu.2, hv.2, one_mul]
  inv_mem' {u} hu := by
    constructor
    · rw [inv_pow, hu.1, inv_one]
    · have h : Units.map A.augmentation.toMonoidHom u = 1 := Units.ext hu.2
      change ((Units.map A.augmentation.toMonoidHom u⁻¹ : Rˣ) : R) = 1
      rw [map_inv, h, inv_one]
      rfl

/-- A based unit has its exact u-1 element in the original augmentation ideal. -/
def basedOrigin (n : ℕ) (u : basedRoots p R A n) : A.ideal R :=
  ⟨((u : A.ringˣ) : A.ring) - 1, by
    change A.augmentation (((u : A.ringˣ) : A.ring) - 1) = 0
    rw [map_sub, u.property.2, map_one, sub_self]⟩

/-- Actual integral dlog is additive on the original based p-power root units. -/
def basedDlog (n : ℕ) : Additive (basedRoots p R A n) →+ A.cotangent R where
  toFun u := (A.ideal R).toCotangent (basedOrigin p R A n u.toMul)
  map_zero' := by
    apply ((A.ideal R).toCotangent_eq_zero _).mpr
    change (1 : A.ring) - 1 ∈ (A.ideal R) ^ 2
    simp
  map_add' u v := by
    rw [← map_add]
    apply (A.ideal R).toCotangent_eq.mpr
    have he : ((basedOrigin p R A n (u.toMul * v.toMul) -
        (basedOrigin p R A n u.toMul + basedOrigin p R A n v.toMul) : A.ideal R) : A.ring) =
        (((u.toMul : A.ringˣ) : A.ring) - 1) *
          (((v.toMul : A.ringˣ) : A.ring) - 1) := by
      change (((u.toMul : A.ringˣ) : A.ring) * ((v.toMul : A.ringˣ) : A.ring) - 1 -
        ((((u.toMul : A.ringˣ) : A.ring) - 1) +
          (((v.toMul : A.ringˣ) : A.ring) - 1))) = _
      ring
    change ((basedOrigin p R A n (u.toMul * v.toMul) -
      (basedOrigin p R A n u.toMul + basedOrigin p R A n v.toMul) : A.ideal R) :
        A.ring) ∈ (A.ideal R) ^ 2
    rw [he, pow_two]
    exact Ideal.mul_mem_mul (basedOrigin p R A n u.toMul).property
      (basedOrigin p R A n v.toMul).property

/-- Pull back the original T-1 dlog generator along a genuine augmented coefficient map. -/
def dlogPullback (n : ℕ) (f : AugmentedMap R (rootAlgebra p R n) A) :
    A.cotangent R := f.cotangent R (rootDlog p R n)

end MathlibExt.AlgebraicGeometry.IntegralRootDlogModels
