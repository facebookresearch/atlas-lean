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

public import MathlibExt.LinearAlgebra.Matrix.ZeroExtension.Trace
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Data.Matrix.Basic

/-!
# Finite-matrix zero extensions as commutator Lie maps

Let k be a commutative ring and A a possibly noncommutative k-algebra. For m≤n, upper-left zero
extension sends an m×m matrix to an n×n matrix with the same entries in the initial block and
zero elsewhere. It is k-linear, multiplicative and injective, hence preserves the commutator
bracket [X,Y]=XY−YX. These Lie maps preserve equal-size identities and compose along m≤n≤p,
including size zero.

An algebra morphism A→B acts entrywise on matrix Lie algebras and commutes with every zero
extension. Over k itself, trace preservation restricts zero extension to sl_m(k)→sl_n(k), where
sl_m(k) is the Lie algebra of trace-zero m×m matrices. Entrywise application of k→A gives
sl_m(k)→Mat_m(A), compatible with size extension and coefficient morphisms. The scalar map is
the specified algebra map on entries. Ring and coefficient-algebra universes are independent.
-/

@[expose] public section

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w

namespace Matrix

variable (k : Type u) [CommRing k]
variable (A : Type v) [Ring A] [Algebra k A]

/-- Let k be a commutative ring in universe u and A a possibly noncommutative ring and k-algebra in
an independent universe v. For m,n∈ℕ with m≤n, this k-linear Lie map Mat_m(A)→Mat_n(A) is
upper-left zero extension. Its (i,j) entry is the input entry when i,j<m and zero otherwise. It
preserves [X,Y]=XY−YX by multiplicativity and additivity, is injective, and is defined also for
m=0. -/
def zeroExtendLieHom {m n : ℕ} (h : m ≤ n) :
    Matrix (Fin m) (Fin m) A →ₗ⁅k⁆ Matrix (Fin n) (Fin n) A where
  toLinearMap := zeroExtendLinear (k := k) (A := A) h
  map_lie' := by
    intro B C
    change zeroExtend h (B * C - C * B) =
      zeroExtend h B * zeroExtend h C - zeroExtend h C * zeroExtend h B
    have hs := map_sub (zeroExtendAlgHom (k := k) (A := A) h) (B * C) (C * B)
    simpa only [zeroExtendAlgHom_apply, zeroExtend_mul] using hs

@[simp]
theorem zeroExtendLieHom_apply {m n : ℕ} (h : m ≤ n) (B : Matrix (Fin m) (Fin m) A) :
    zeroExtendLieHom k A h B = zeroExtend h B := rfl

theorem zeroExtendLieHom_apply_entry {m n : ℕ} (h : m ≤ n)
    (B : Matrix (Fin m) (Fin m) A) (i j : Fin n) :
    zeroExtendLieHom k A h B i j = if hi : i.val < m then
      if hj : j.val < m then B ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0 else 0 := rfl

theorem zeroExtendLieHom_injective {m n : ℕ} (h : m ≤ n) :
    Function.Injective (zeroExtendLieHom k A h) := zeroExtend_injective h

@[simp]
theorem zeroExtendLieHom_id (m : ℕ) :
    zeroExtendLieHom k A (le_rfl : m ≤ m) = LieHom.id := by
  apply LieHom.ext
  intro B
  exact zeroExtend_self B

theorem zeroExtendLieHom_comp {m n p : ℕ} (h : m ≤ n) (h' : n ≤ p) :
    (zeroExtendLieHom k A h').comp (zeroExtendLieHom k A h) =
      zeroExtendLieHom k A (h.trans h') := by
  apply LieHom.ext
  intro B
  exact zeroExtend_comp h h' B

variable {B : Type w} [Ring B] [Algebra k B]

/-- Let k be a commutative ring in universe u and A a possibly noncommutative ring and k-algebra in
an independent universe v. Let B be another ring and k-algebra in an independent universe w. For
a k-algebra morphism f:A→B and m∈ℕ, this k-linear Lie map Mat_m(A)→Mat_m(B) sends each entry
X_{ij} to f(X_{ij}). It preserves matrix products and therefore the commutator bracket, with the
same finite matrix index on both sides. -/
def coefficientLieHom (f : A →ₐ[k] B) (m : ℕ) :
    Matrix (Fin m) (Fin m) A →ₗ⁅k⁆ Matrix (Fin m) (Fin m) B :=
  (f.mapMatrix (m := Fin m)).toLieHom

@[simp]
theorem coefficientLieHom_apply_entry (f : A →ₐ[k] B) (m : ℕ)
    (C : Matrix (Fin m) (Fin m) A) (i j : Fin m) :
    coefficientLieHom k A f m C i j = f (C i j) := rfl

/-- Let k be a commutative ring in universe u and A a possibly noncommutative ring and k-algebra in
an independent universe v. Let B be another ring and k-algebra in an independent universe w. For
f:A→B a k-algebra morphism, m≤n and X∈Mat_m(A), the entrywise matrix map f_n satisfies
f_n(Z_{m,n}X)=Z_{m,n}(f_mX), where Z_{m,n} is upper-left zero extension. The equality includes
all entries outside the initial block, which are zero on both sides. -/
theorem coefficientLieHom_zeroExtend (f : A →ₐ[k] B) {m n : ℕ} (h : m ≤ n)
    (C : Matrix (Fin m) (Fin m) A) :
    coefficientLieHom k A f n (zeroExtend h C) =
      zeroExtend h (coefficientLieHom k A f m C) := by
  ext i j
  by_cases hi : i.val < m <;> by_cases hj : j.val < m <;>
    simp only [coefficientLieHom_apply_entry, zeroExtend_apply, hi, hj, ↓reduceDIte, map_zero]

/-- Let k be a commutative ring in universe u and A a possibly noncommutative ring and k-algebra in
an independent universe v. Let B be another ring and k-algebra in an independent universe w. For
a k-algebra morphism f:A→B and m≤n, let f_m,f_n be its entrywise matrix Lie maps and Z_A,Z_B the
zero-extension Lie maps over A and B. The Lie-map equality is f_n∘Z_A=Z_B∘f_m from Mat_m(A) to
Mat_n(B). -/
theorem coefficientLieHom_zeroExtend_comp (f : A →ₐ[k] B) {m n : ℕ} (h : m ≤ n) :
    (coefficientLieHom k A f n).comp (zeroExtendLieHom k A h) =
      (zeroExtendLieHom k B h).comp (coefficientLieHom k A f m) := by
  apply LieHom.ext
  intro C
  exact coefficientLieHom_zeroExtend k A f h C

/-- Let k be a commutative ring and m∈ℕ. The scalar special-linear Lie algebra sl_m(k) is the
submodule of m×m matrices over k with trace zero, equipped with the commutator bracket
[X,Y]=XY−YX. Its carrier is the trace-zero matrix Lie subalgebra, with no field or
characteristic restriction. -/
abbrev ScalarSpecialLinear (m : ℕ) := ↥(LieAlgebra.SpecialLinear.sl (Fin m) k)

/-- Let k be a commutative ring in universe u and A a possibly noncommutative ring and k-algebra in
an independent universe v. For m∈ℕ, this k-linear Lie map sl_m(k)→Mat_m(A) first includes a
trace-zero scalar matrix into Mat_m(k), then applies the algebra map k→A entrywise. Its (i,j)
entry on s∈sl_m(k) is algebraMap(k,A)(s_{ij}). The target is the full matrix Lie algebra over A. -/
def scalarLieHom (m : ℕ) : ScalarSpecialLinear k m →ₗ⁅k⁆ Matrix (Fin m) (Fin m) A :=
  (coefficientLieHom k k (Algebra.ofId k A) m).comp
    (LieAlgebra.SpecialLinear.sl (Fin m) k).incl

@[simp]
theorem scalarLieHom_apply_entry (m : ℕ) (s : ScalarSpecialLinear k m) (i j : Fin m) :
    scalarLieHom k A m s i j = algebraMap k A (s.val i j) := rfl

/-- Let k be a commutative ring and m,n∈ℕ with m≤n. Upper-left zero extension defines this k-linear
Lie map sl_m(k)→sl_n(k). It sends a trace-zero matrix s to its zero extension and preserves
trace because the additional diagonal entries are zero. The commutator bracket is preserved by
the matrix zero-extension Lie map. -/
def scalarZeroExtendLieHom {m n : ℕ} (h : m ≤ n) :
    ScalarSpecialLinear k m →ₗ⁅k⁆ ScalarSpecialLinear k n where
  toFun s := ⟨zeroExtend h s.val, by
    change Matrix.trace (zeroExtend h s.val) = 0
    rw [zeroExtend_trace]
    exact s.property⟩
  map_add' s t := by
    apply Subtype.ext
    exact (zeroExtendLinear (k := k) (A := k) h).map_add s.val t.val
  map_smul' r s := by
    apply Subtype.ext
    exact (zeroExtendLinear (k := k) (A := k) h).map_smul r s.val
  map_lie' := by
    intro s t
    apply Subtype.ext
    exact (zeroExtendLieHom k k h).map_lie s.val t.val

@[simp]
theorem scalarZeroExtendLieHom_coe {m n : ℕ} (h : m ≤ n) (s : ScalarSpecialLinear k m) :
    (scalarZeroExtendLieHom k h s).val = zeroExtend h s.val := rfl

/-- Let k be a commutative ring in universe u and A a possibly noncommutative ring and k-algebra in
an independent universe v. For m≤n, let s_m:sl_m(k)→Mat_m(A) and s_n be the entrywise scalar
maps, Z_A:Mat_m(A)→Mat_n(A) the matrix zero extension and Z_k:sl_m(k)→sl_n(k) its trace-zero
restriction. Then Z_A∘s_m=s_n∘Z_k as k-linear Lie maps from sl_m(k) to Mat_n(A). -/
theorem scalarLieHom_zeroExtend {m n : ℕ} (h : m ≤ n) :
    (zeroExtendLieHom k A h).comp (scalarLieHom k A m) =
      (scalarLieHom k A n).comp (scalarZeroExtendLieHom k h) := by
  apply LieHom.ext
  intro s
  ext i j
  by_cases hi : i.val < m <;> by_cases hj : j.val < m <;>
    simp only [LieHom.comp_apply, zeroExtendLieHom_apply, scalarLieHom_apply_entry,
      scalarZeroExtendLieHom_coe, zeroExtend_apply, hi, hj, ↓reduceDIte, map_zero]

/-- Let k be a commutative ring in universe u and A a possibly noncommutative ring and k-algebra in
an independent universe v. Let B be another ring and k-algebra in an independent universe w. For
a k-algebra morphism f:A→B and m∈ℕ, let f_m:Mat_m(A)→Mat_m(B) be its entrywise Lie map and
s_A,s_B the scalar maps from sl_m(k). Then f_m∘s_A=s_B, because f carries the algebra map k→A to
the algebra map k→B. -/
theorem scalarLieHom_coefficient (f : A →ₐ[k] B) (m : ℕ) :
    (coefficientLieHom k A f m).comp (scalarLieHom k A m) = scalarLieHom k B m := by
  apply LieHom.ext
  intro s
  ext i j
  simp only [LieHom.comp_apply, coefficientLieHom_apply_entry, scalarLieHom_apply_entry,
    AlgHom.commutes]

end Matrix
