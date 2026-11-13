/-
Copyright 2026 Anthropic, PBC.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib, copyright its respective authors,
released under the Apache License, Version 2.0. No individual authors are
identified for this source file in the upstream ATTRIBUTION.md.
-/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
The source fixture below is adapted from lines 13–159 of
`P2M/Sol/S_fermatLastTheoremFive.lean`, anthropics/fermats-last-theorem,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache-2.0).
The representation and operation bodies are preserved. Scoped registrations
are made ordinary in the test namespace; F157's redundant final `try ring`
is removed because the pinned simplifier already closes that proof.
The source type is not replaced by an alias for QuadraticAlgebra.
Production never imports this fixture.
-/
module

public import MathlibExt.NumberTheory.QuadraticForms.GoldenOrderEquiv

@[expose] public section

namespace GoldenOrderSource

-- BEGIN LITERAL SOURCE FIXTURE
@[ext]
structure Zphi where

  re : ℤ

  im : ℤ
  deriving DecidableEq, Repr

namespace Zphi

instance : Zero Zphi := ⟨⟨0, 0⟩⟩
instance : One Zphi := ⟨⟨1, 0⟩⟩
instance : Inhabited Zphi := ⟨0⟩

@[simp] theorem re_zero : (0 : Zphi).re = 0 := rfl
@[simp] theorem im_zero : (0 : Zphi).im = 0 := rfl
@[simp] theorem re_one : (1 : Zphi).re = 1 := rfl
@[simp] theorem im_one : (1 : Zphi).im = 0 := rfl

def phi : Zphi := ⟨0, 1⟩

@[simp] theorem re_phi : phi.re = 0 := rfl
@[simp] theorem im_phi : phi.im = 1 := rfl

instance : Add Zphi := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

@[simp] theorem add_def (x y x' y' : ℤ) :
    (⟨x, y⟩ + ⟨x', y'⟩ : Zphi) = ⟨x + x', y + y'⟩ := rfl
@[simp] theorem re_add (z w : Zphi) : (z + w).re = z.re + w.re := rfl
@[simp] theorem im_add (z w : Zphi) : (z + w).im = z.im + w.im := rfl

instance : Neg Zphi := ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp] theorem re_neg (z : Zphi) : (-z).re = -z.re := rfl
@[simp] theorem im_neg (z : Zphi) : (-z).im = -z.im := rfl

instance : Mul Zphi :=
  ⟨fun z w => ⟨z.re * w.re + z.im * w.im, z.re * w.im + z.im * w.re + z.im * w.im⟩⟩

@[simp] theorem re_mul (z w : Zphi) :
    (z * w).re = z.re * w.re + z.im * w.im := rfl
@[simp] theorem im_mul (z w : Zphi) :
    (z * w).im = z.re * w.im + z.im * w.re + z.im * w.im := rfl

instance addCommGroup : AddCommGroup Zphi := by
  refine
  { sub := fun a b => a + -b
    nsmul := @nsmulRec Zphi ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec Zphi ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec Zphi ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ } <;>
  intros <;> ext <;> simp [add_comm, add_left_comm]

@[simp] theorem re_sub (z w : Zphi) : (z - w).re = z.re - w.re := rfl
@[simp] theorem im_sub (z w : Zphi) : (z - w).im = z.im - w.im := rfl

def ofInt (n : ℤ) : Zphi := ⟨n, 0⟩

instance addGroupWithOne : AddGroupWithOne Zphi :=
  { Zphi.addCommGroup with
    natCast := fun n => ofInt n
    intCast := ofInt }

instance commRing : CommRing Zphi := by
  refine
  { Zphi.addGroupWithOne with
    npow := @npowRec Zphi ⟨1⟩ ⟨(· * ·)⟩
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;> ext <;> simp <;> ring

@[simp] theorem re_natCast (n : ℕ) : (n : Zphi).re = n := rfl
@[simp] theorem im_natCast (n : ℕ) : (n : Zphi).im = 0 := rfl
@[simp] theorem re_intCast (n : ℤ) : (n : Zphi).re = n := by cases n <;> rfl
@[simp] theorem im_intCast (n : ℤ) : (n : Zphi).im = 0 := by cases n <;> rfl
@[simp] theorem re_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Zphi).re = OfNat.ofNat n := rfl
@[simp] theorem im_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Zphi).im = 0 := rfl

theorem intCast_val (n : ℤ) : (n : Zphi) = ⟨n, 0⟩ := by ext <;> simp

instance : CharZero Zphi where
  cast_injective _ _ h := by simpa [Zphi.ext_iff] using h

instance nontrivial : Nontrivial Zphi :=
  ⟨⟨0, 1, fun h => by simpa using congrArg re h⟩⟩

def sqrt5 : Zphi := ⟨-1, 2⟩

@[simp] theorem re_sqrt5 : sqrt5.re = -1 := rfl
@[simp] theorem im_sqrt5 : sqrt5.im = 2 := rfl

theorem sqrt5_eq : sqrt5 = 2 * phi - 1 := by ext <;> simp

@[simp] theorem sqrt5_sq : sqrt5 * sqrt5 = 5 := by ext <;> simp

@[simp] theorem phi_sq : phi * phi = phi + 1 := by ext <;> simp

def conj : Zphi →+* Zphi where
  toFun z := ⟨z.re + z.im, -z.im⟩
  map_zero' := by ext <;> simp
  map_add' _ _ := by ext <;> simp <;> ring
  map_one' := by ext <;> simp
  map_mul' _ _ := by ext <;> simp <;> ring

@[simp] theorem conj_mk (a b : ℤ) : conj ⟨a, b⟩ = ⟨a + b, -b⟩ := rfl
@[simp] theorem re_conj (z : Zphi) : (conj z).re = z.re + z.im := rfl
@[simp] theorem im_conj (z : Zphi) : (conj z).im = -z.im := rfl

@[simp] theorem conj_conj (z : Zphi) : conj (conj z) = z := by ext <;> simp

@[simp] theorem conj_intCast (n : ℤ) : conj (n : Zphi) = n := by ext <;> simp

theorem conj_phi : conj phi = 1 - phi := by ext <;> simp

theorem conj_sqrt5 : conj sqrt5 = -sqrt5 := by ext <;> simp

def norm (z : Zphi) : ℤ := z.re * z.re + z.re * z.im - z.im * z.im

@[simp] theorem norm_mk (a b : ℤ) : norm ⟨a, b⟩ = a * a + a * b - b * b := rfl

theorem mul_conj (z : Zphi) : z * conj z = (norm z : Zphi) := by
  ext <;> (simp [norm]; try ring)

@[simp] theorem norm_zero : norm 0 = 0 := by simp [norm]
@[simp] theorem norm_one : norm 1 = 1 := by simp [norm]
@[simp] theorem norm_intCast (n : ℤ) : norm (n : Zphi) = n * n := by simp [norm]
@[simp] theorem norm_phi : norm phi = -1 := by simp [norm]
@[simp] theorem norm_sqrt5 : norm sqrt5 = -5 := by simp [norm]

theorem norm_mul (z w : Zphi) : norm (z * w) = norm z * norm w := by
  simp [norm] ; ring

theorem norm_neg (z : Zphi) : norm (-z) = norm z := by simp [norm]

theorem norm_conj (z : Zphi) : norm (conj z) = norm z := by simp [norm] ; ring

-- END LITERAL SOURCE FIXTURE

/-- A proved coordinate-preserving ring equivalence, not a carrier alias. -/
def coordinateEquiv : Zphi ≃+* QuadraticAlgebra ℤ 1 1 where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp

@[simp]
theorem coordinateEquiv_phi : coordinateEquiv phi = QuadraticAlgebra.omega := rfl

@[simp]
theorem coordinateEquiv_conj (z : Zphi) :
    coordinateEquiv (conj z) = star (coordinateEquiv z) := by
  ext <;> simp [coordinateEquiv]

@[simp]
theorem coordinateEquiv_norm (z : Zphi) :
    QuadraticAlgebra.norm (coordinateEquiv z) = norm z := by
  simp [QuadraticAlgebra.norm_def, coordinateEquiv, norm]

/-- Exact F623–677 source statement, via the two representation bridges. -/
theorem exists_phi_pow_of_isUnit (z : Zphi) (hz : IsUnit z) :
    ∃ n : ℕ, z = phi ^ n ∨ z = -(phi ^ n) ∨ z * phi ^ n = 1 ∨ z * phi ^ n = -1 := by
  obtain ⟨n, h | h | h | h⟩ := QuadraticAlgebra.exists_omega_pow_of_isUnit
    (coordinateEquiv z) (hz.map coordinateEquiv)
  · exact ⟨n, Or.inl (coordinateEquiv.injective (by simpa using h))⟩
  · exact ⟨n, Or.inr (Or.inl (coordinateEquiv.injective (by simpa using h)))⟩
  · exact ⟨n, Or.inr (Or.inr (Or.inl
      (coordinateEquiv.injective (by simpa using h))))⟩
  · exact ⟨n, Or.inr (Or.inr (Or.inr
      (coordinateEquiv.injective (by simpa using h))))⟩

end Zphi
end GoldenOrderSource
