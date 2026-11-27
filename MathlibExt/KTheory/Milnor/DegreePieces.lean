/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Milnor.Grading
public import MathlibExt.KTheory.Milnor.Symbols
public import MathlibExt.KTheory.Milnor.K2

/-!
# Degree pieces of the Milnor K-ring

`TensorRing.degree F n` is the `n`-th power of the image of
`ι : Additive Fˣ → TensorRing F`, and `MilnorKRing.degree F n`
is its image under the quotient `mk : TensorRing → MilnorKRing`.
Both families carry genuine `GradedAlgebra` instances introduced in
`Grading.lean`: `TensorRing.degree` via `TensorAlgebra.gradedAlgebra` and
`MilnorKRing.degree` via `TwoSidedIdeal.gradedAlgebraQuotientGrade` over the
homogeneous Steinberg ideal. In particular `1 ∈ degree 0` and
`degree m * degree n ⊆ degree (m+n)` are structural graded facts, not merely
image-defined. This file records those facts with direct generic
graded-instance proofs, and that Steinberg symbols lie in the expected degrees.

## Main definitions

* `TensorRing.one_mem_degree_zero`, `MilnorKRing.one_mem_degree_zero`:
  `1 ∈ degree F 0`, from `SetLike.GradedOne`.
* `TensorRing.mul_mem_degree`, `MilnorKRing.mul_mem_degree`,
  `MilnorKRing.mk_mul_mem_degree`: degree additivity for products,
  `degree m * degree n ⊆ degree (m+n)`, from `SetLike.GradedMul` and the
  quotient grade/map API.
* `MilnorKRing.degreeZeroUnitRep`: the element `1` viewed in `degree F 0`,
  the structural degree-zero unit.
* `MilnorKRing.symbolList_mem_degree`,
  `MilnorKRing.symbolList_singleton_mem_degree`,
  `MilnorKRing.k2Symbol_mem_degree_two`: symbols live in degree `len` / `1` / `2`.
* `MilnorKRing.mul`, `MilnorKRing.mulLeft`, `MilnorKRing.mulRight`,
  `MilnorKRing.mulHom`: restricted multiplication on degree subtypes,
  as the structural graded multiplication and as `ℤ`-linear maps.
* `MilnorKRing.mul_degreeZeroUnitRep_right/left`,
  `MilnorKRing.mul_assoc_rep`: unit and associativity at the representative
  level, modulo `degreeCastEquiv` for the `0 + n` and `(m+n)+p` index
  equalities.

## Implementation notes

`MilnorKRing.degree F n = (TensorRing.degree F n).map mkLinear` is
definitionally `TwoSidedIdeal.quotientGrade`. By `Grading.lean` it carries a
`GradedAlgebra (degree F)` instance, so `one_mem_degree_zero` and
`mul_mem_degree` are direct applications of `SetLike.GradedOne.one_mem` /
`SetLike.GradedMul.mul_mem`. `mk_mul_mem_degree` uses the graded product on
`TensorRing.degree` together with `Submodule.mem_map` and `map_mul`. Restricted
multiplication `mul` is the structural graded multiplication. Left unitality
needs `degreeCastEquiv F (Nat.zero_add n)` to align `0 + n = n`.
-/

@[expose] public section

open TensorAlgebra
open scoped TensorAlgebra

namespace MilnorK

variable (F : Type*) [Field F]

namespace TensorRing

/-- `1` lies in degree zero of the tensor ring, as the structural
graded unit from `TensorAlgebra.gradedAlgebra`. -/
theorem one_mem_degree_zero : (1 : TensorRing F) ∈ TensorRing.degree F 0 :=
  SetLike.one_mem_graded _

/-- Product of tensor degree elements lies in degree sum, as the structural
graded multiplication from `TensorAlgebra.gradedAlgebra`. -/
theorem mul_mem_degree {m n : ℕ} {a b : TensorRing F}
    (ha : a ∈ TensorRing.degree F m) (hb : b ∈ TensorRing.degree F n) :
    a * b ∈ TensorRing.degree F (m + n) :=
  SetLike.mul_mem_graded ha hb

end TensorRing

namespace MilnorKRing

/-- The quotient image of a product of tensor elements in degrees `m` and `n`
belongs to degree `m+n`. Uses the structural graded product on
`TensorRing.degree` and the quotient grade/map API `degree = map mkLinear`. -/
theorem mk_mul_mem_degree {m n : ℕ} {a b : TensorRing F}
    (ha : a ∈ TensorRing.degree F m) (hb : b ∈ TensorRing.degree F n) :
    mk F a * mk F b ∈ degree F (m + n) := by
  have hmul : a * b ∈ TensorRing.degree F (m + n) :=
    SetLike.mul_mem_graded ha hb
  have hmap : mkLinear F (a * b) ∈ degree F (m + n) :=
    Submodule.mem_map_of_mem hmul
  have hmk : mk F (a * b) ∈ degree F (m + n) := by
    rwa [mkLinear_apply] at hmap
  have heq : mk F (a * b) = mk F a * mk F b := map_mul (mk F) a b
  rwa [heq] at hmk

/-- Degree pieces are closed under multiplication:
if `x ∈ degree m` and `y ∈ degree n` then `x*y ∈ degree (m+n)`.
Directly the structural `GradedMul` from `GradedAlgebra (degree F)` introduced
in `Grading.lean` via `gradedAlgebraQuotientGrade`. -/
theorem mul_mem_degree {m n : ℕ} {x y : MilnorKRing F}
    (hx : x ∈ degree F m) (hy : y ∈ degree F n) :
    x * y ∈ degree F (m + n) :=
  SetLike.mul_mem_graded hx hy

/-- `1` belongs to degree zero of the Milnor K-ring, as the structural graded
unit from `GradedAlgebra (degree F)` in `Grading.lean`. -/
theorem one_mem_degree_zero : (1 : MilnorKRing F) ∈ degree F 0 :=
  SetLike.one_mem_graded _

/-- The element `1` regarded as lying in `degree F 0`, i.e. the canonical
structural degree-zero unit from `GradedAlgebra (degree F)`. -/
def degreeZeroUnitRep : degree F 0 :=
  ⟨1, one_mem_degree_zero F⟩

/-- The underlying ring element of `degreeZeroUnitRep` is `1`. -/
theorem degreeZeroUnitRep_coe : (degreeZeroUnitRep F : MilnorKRing F) = 1 :=
  rfl

/-- `symbolList` belongs to degree given by list length, using the structural
grading `GradedAlgebra (degree F)`. -/
theorem symbolList_mem_degree (xs : List Fˣ) :
    symbolList F xs ∈ degree F xs.length := by
  induction xs with
  | nil =>
    simp only [symbolList_nil, List.length]
    exact one_mem_degree_zero F
  | cons hd tl ih =>
    have h1 : symbol F hd ∈ degree F 1 := symbol_mem_degree_one F hd
    have hmul : symbol F hd * symbolList F tl ∈ degree F (1 + tl.length) :=
      mul_mem_degree (F := F) h1 ih
    have h_eq : 1 + tl.length = (hd :: tl).length := by
      simp [Nat.add_comm]
    have hmem : symbol F hd * symbolList F tl ∈ degree F (hd :: tl).length :=
      h_eq ▸ hmul
    exact hmem

/-- Singleton symbol list in degree one. -/
theorem symbolList_singleton_mem_degree (a : Fˣ) :
    symbolList F [a] ∈ degree F 1 := by
  have h := symbolList_mem_degree F [a]
  simpa using h

/-- Product of two symbols in degree two, via structural graded multiplication. -/
theorem k2Symbol_mem_degree_two (a b : Fˣ) :
    k2Symbol (F := F) a b ∈ degree F 2 := by
  have h1 : symbol F a ∈ degree F 1 := symbol_mem_degree_one F a
  have h2 : symbol F b ∈ degree F 1 := symbol_mem_degree_one F b
  have h := mul_mem_degree (F := F) h1 h2
  simpa [k2Symbol_def] using h

/-- Restricted multiplication `degree F m × degree F n → degree F (m+n)`:
structural graded multiplication `degree m * degree n ⊆ degree (m+n)` from
`GradedAlgebra (degree F)` in `Grading.lean`. -/
def mul {m n : ℕ} (x : degree F m) (y : degree F n) :
    degree F (m + n) :=
  ⟨x.1 * y.1, mul_mem_degree (F := F) x.2 y.2⟩

/-- The coercion of `mul x y` to `MilnorKRing F` equals the product `x.1 * y.1` of
the underlying ring elements. -/
@[simp]
theorem mul_coe {m n : ℕ} (x : degree F m) (y : degree F n) :
    (mul F x y : MilnorKRing F) = x.1 * y.1 :=
  rfl

/-- Left multiplication by a fixed degree `m` element as a `ℤ`-linear map
on degree `n`. -/
def mulLeft {m n : ℕ} (x : degree F m) : degree F n →ₗ[ℤ] degree F (m + n) where
  toFun y := mul F x y
  map_add' y₁ y₂ := by
    apply Subtype.ext
    simp [mul, mul_add]
  map_smul' c y := by
    apply Subtype.ext
    simp only [mul, Submodule.coe_smul]
    exact Algebra.mul_smul_comm (R := ℤ) (A := MilnorKRing F) _ _ _

/-- Right multiplication by a fixed degree `n` element as a `ℤ`-linear map
on degree `m`. -/
def mulRight {m n : ℕ} (y : degree F n) : degree F m →ₗ[ℤ] degree F (m + n) where
  toFun x := mul F x y
  map_add' x₁ x₂ := by
    apply Subtype.ext
    simp [mul, add_mul]
  map_smul' c x := by
    apply Subtype.ext
    simp only [mul, Submodule.coe_smul]
    exact Algebra.smul_mul_assoc (R := ℤ) (A := MilnorKRing F) _ _ _

/-- Bilinear restricted multiplication as a curried linear map:
`degree m →ₗ degree n →ₗ degree (m+n)`. -/
def mulHom (m n : ℕ) : degree F m →ₗ[ℤ] degree F n →ₗ[ℤ] degree F (m + n) where
  toFun x := mulLeft F x
  map_add' x₁ x₂ := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    simp [mulLeft, mul, add_mul]
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    simp only [mulLeft, mul, Submodule.coe_smul]
    exact Algebra.smul_mul_assoc (R := ℤ) (A := MilnorKRing F) _ _ _

section IntegralLaws

/-- Right unit at representative level. -/
theorem mul_degreeZeroUnitRep_right {n : ℕ} (x : degree F n) :
    (mul (F := F) x (degreeZeroUnitRep F)) = x := by
  apply Subtype.ext
  change x.1 * (degreeZeroUnitRep F).1 = x.1
  simp [degreeZeroUnitRep]

/-- Left unitality up to `degreeCastEquiv`: multiplying by `degreeZeroUnitRep`
on the left and then casting `0 + n = n` returns the original degree element. -/
theorem mul_degreeZeroUnitRep_left_cast {n : ℕ} (y : degree F n) :
    degreeCastEquiv F (Nat.zero_add n)
        (mul (F := F) (degreeZeroUnitRep F) y) = y := by
  apply Subtype.ext
  calc (degreeCastEquiv F (Nat.zero_add n)
          (mul (F := F) (degreeZeroUnitRep F) y)).1
      = (mul (F := F) (degreeZeroUnitRep F) y).1 :=
        degreeCastEquiv_val (F := F) (Nat.zero_add n)
          (mul (F := F) (degreeZeroUnitRep F) y)
    _ = (degreeZeroUnitRep F).1 * y.1 := rfl
    _ = 1 * y.1 := rfl
    _ = y.1 := one_mul _

/-- Value-level left unitality: the underlying ring element of
`mul degreeZeroUnitRep y` is `y.1`, i.e. `1 * y = y` in `MilnorKRing F`. -/
theorem mul_degreeZeroUnitRep_left_val {n : ℕ} (y : degree F n) :
    (mul (F := F) (degreeZeroUnitRep F) y : MilnorKRing F) =
      (y : MilnorKRing F) := by
  change (degreeZeroUnitRep F).1 * y.1 = y.1
  simp [degreeZeroUnitRep]

/-- Associativity at representative level. -/
theorem mul_assoc_rep {m n p : ℕ} (x : degree F m) (y : degree F n) (z : degree F p)
    (h : (m + n) + p = m + (n + p) := Nat.add_assoc m n p) :
    degreeCastEquiv F h
        (mul (F := F)
          (mul (F := F) x y) z) =
      mul (F := F) x
        (mul (F := F) y z) := by
  apply Subtype.ext
  calc (degreeCastEquiv F h
          (mul (F := F)
            (mul (F := F) x y) z)).1
      = (mul (F := F)
            (mul (F := F) x y) z).1 :=
        degreeCastEquiv_val (F := F) h
          (mul (F := F)
            (mul (F := F) x y) z)
    _ = (x.1 * y.1) * z.1 := rfl
    _ = x.1 * (y.1 * z.1) := mul_assoc _ _ _
    _ = (mul (F := F) x
            (mul (F := F) y z)).1 := rfl

end IntegralLaws

end MilnorKRing

end MilnorK
