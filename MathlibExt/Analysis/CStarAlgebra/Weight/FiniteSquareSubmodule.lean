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

public import MathlibExt.Analysis.CStarAlgebra.Weight.FiniteStarDomain
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Tactic.Abel

/-!
# The actual finite-square linear domain and original two-square star algebra

A global extended positive weight determines the literal set of x for which
its value on x*x is finite. Additivity, finite positive homogeneity and
C-star positivity make that same set a complex submodule and a left ideal.
The left multiplication maps below have their original algebra values.

The two-square-finite set likewise supplies an actual complex submodule
and a nonunital star subalgebra. These are algebraic prerequisites for the
weight GNS domain and its algebraic core. Only the original ambient norm is
inherited here; no weight inner product, weight norm, completion, normal
representation or modular operator is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped NNReal ENNReal

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- Positive additivity makes the actual global weight monotone on the original positive cone. -/
theorem Weight.value_mono (φ : Weight A) (a b : PositiveElement A) (hab : (a : A) ≤ (b : A)) :
    φ.value a ≤ φ.value b := by
  let d : PositiveElement A := ⟨(b : A) - (a : A), sub_nonneg.mpr hab⟩
  have hsum : positiveAdd a d = b := by
    apply Subtype.ext
    change (a : A) + ((b : A) - (a : A)) = (b : A)
    abel
  calc
    φ.value a ≤ φ.value a + φ.value d := le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ φ.value d from zero_le)
    _ = φ.value b := by rw [← φ.add_value, hsum]

/-- A positive minorant of an actual finite-positive element has finite weight. -/
theorem Weight.finite_of_le (φ : Weight A) (a b : PositiveElement A)
    (hab : (a : A) ≤ (b : A)) (hb : φ.value b < ⊤) : φ.value a < ⊤ :=
  lt_of_le_of_lt (φ.value_mono a b hab) hb

/-- Finite nonnegative-real scaling preserves an actual finite-positive weight value. -/
theorem Weight.finite_positiveSmul (φ : Weight A) (r : ℝ≥0) (a : PositiveElement A)
    (ha : φ.value a < ⊤) : φ.value (positiveSmul r a) < ⊤ := by
  rw [φ.smul_value]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top ha

/-- Complex scaling of the original square is finite positive scaling by the scalar norm square. -/
theorem leftSquare_smul (c : ℂ) (x : A) :
    leftSquare (c • x) = positiveSmul ⟨‖c‖ ^ 2, sq_nonneg ‖c‖⟩ (leftSquare x) := by
  apply Subtype.ext
  change star (c • x) * (c • x) = (‖c‖ ^ 2 : ℝ) • (star x * x)
  rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.star_def, RCLike.conj_mul]
  change (RCLike.ofReal ‖c‖ : ℂ) ^ 2 • (star x * x) = (‖c‖ ^ 2 : ℝ) • (star x * x)
  calc
    (RCLike.ofReal ‖c‖ : ℂ) ^ 2 • (star x * x) =
        (RCLike.ofReal (‖c‖ ^ 2) : ℂ) • (star x * x) :=
      congrArg (fun z : ℂ => z • (star x * x)) (RCLike.ofReal_pow (K := ℂ) ‖c‖ 2).symm
    _ = (‖c‖ ^ 2 : ℝ) • (star x * x) :=
      (RCLike.real_smul_eq_coe_smul (K := ℂ) (‖c‖ ^ 2) (star x * x)).symm

/-- The original finite-square domain is closed under addition, by the positive square bound. -/
theorem Weight.add_mem_finiteSquareDomain (φ : Weight A) (x y : A)
    (hx : x ∈ φ.finiteSquareDomain) (hy : y ∈ φ.finiteSquareDomain) :
    x + y ∈ φ.finiteSquareDomain := by
  let s := positiveAdd (leftSquare x) (leftSquare y)
  have hidentity :
      ((star x * x + star y * y) + (star x * x + star y * y)) -
        star (x + y) * (x + y) = star (x - y) * (x - y) := by
    simp only [star_add, star_sub, add_mul, mul_add, sub_mul, mul_sub]
    abel
  have hbound : (leftSquare (x + y) : A) ≤ (positiveAdd s s : A) := by
    apply sub_nonneg.mp
    change 0 ≤ ((star x * x + star y * y) + (star x * x + star y * y)) -
      star (x + y) * (x + y)
    rw [hidentity]
    exact star_mul_self_nonneg (x - y)
  have hs : φ.value s < ⊤ := (φ.finite_add_iff (leftSquare x) (leftSquare y)).2 ⟨hx, hy⟩
  exact φ.finite_of_le (leftSquare (x + y)) (positiveAdd s s) hbound
    ((φ.finite_add_iff s s).2 ⟨hs, hs⟩)

/-- The original finite-square domain is closed under every complex scalar. -/
theorem Weight.smul_mem_finiteSquareDomain (φ : Weight A) (c : ℂ) (x : A)
    (hx : x ∈ φ.finiteSquareDomain) : c • x ∈ φ.finiteSquareDomain := by
  change φ.value (leftSquare (c • x)) < ⊤
  rw [leftSquare_smul]
  exact φ.finite_positiveSmul ⟨‖c‖ ^ 2, sq_nonneg ‖c‖⟩ (leftSquare x) hx

/-- Original left multiplication has the genuine C-star positive square estimate. -/
theorem leftSquare_mul_le (a x : A) :
    (leftSquare (a * x) : A) ≤
      (positiveSmul ⟨‖a‖ ^ 2, sq_nonneg ‖a‖⟩ (leftSquare x) : A) := by
  change star (a * x) * (a * x) ≤ (‖a‖ ^ 2 : ℝ) • (star x * x)
  rw [star_mul, ← mul_assoc, mul_assoc _ (star a), sq,
    ← CStarRing.norm_star_mul_self (x := a)]
  exact CStarAlgebra.star_left_conjugate_le_norm_smul x (star a * a)
    (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg a))

/-- The global weight retains the actual bound needed by the later weight-norm left action. -/
theorem Weight.value_leftSquare_mul_le (φ : Weight A) (a x : A) :
    φ.value (leftSquare (a * x)) ≤
      ENNReal.ofNNReal (NNReal.mk (‖a‖ ^ 2) (sq_nonneg ‖a‖)) * φ.value (leftSquare x) := by
  calc
    φ.value (leftSquare (a * x)) ≤
        φ.value (positiveSmul (NNReal.mk (‖a‖ ^ 2) (sq_nonneg ‖a‖)) (leftSquare x)) :=
      φ.value_mono _ _ (leftSquare_mul_le a x)
    _ = ENNReal.ofNNReal (NNReal.mk (‖a‖ ^ 2) (sq_nonneg ‖a‖)) * φ.value (leftSquare x) :=
      φ.smul_value (NNReal.mk (‖a‖ ^ 2) (sq_nonneg ‖a‖)) (leftSquare x)

/-- Every original left multiplier preserves the literal finite-square domain. -/
theorem Weight.mul_mem_finiteSquareDomain (φ : Weight A) (a x : A)
    (hx : x ∈ φ.finiteSquareDomain) : a * x ∈ φ.finiteSquareDomain := by
  change φ.value (leftSquare (a * x)) < ⊤
  exact lt_of_le_of_lt (φ.value_leftSquare_mul_le a x)
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hx)

/-- The original finite-square set with its proved complex submodule structure. -/
def Weight.finiteSquareSubmodule (φ : Weight A) : Submodule ℂ A where
  carrier := φ.finiteSquareDomain
  zero_mem' := φ.zero_mem_finiteSquareDomain
  add_mem' := by
    intro x y hx hy
    exact φ.add_mem_finiteSquareDomain x y hx hy
  smul_mem' := by
    intro c x hx
    exact φ.smul_mem_finiteSquareDomain c x hx

/-- The actual linear domain has exactly the original finite-square carrier. -/
@[simp]
theorem Weight.coe_finiteSquareSubmodule (φ : Weight A) :
    (φ.finiteSquareSubmodule : Set A) = φ.finiteSquareDomain :=
  rfl

/-- Left multiplication on the actual finite-square complex module. -/
def Weight.finiteSquareLeftMul (φ : Weight A) (a : A) :
    φ.finiteSquareSubmodule →ₗ[ℂ] φ.finiteSquareSubmodule where
  toFun x := ⟨a * (x : A), φ.mul_mem_finiteSquareDomain a (x : A) x.property⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    change a * ((x : A) + (y : A)) = a * (x : A) + a * (y : A)
    exact mul_add a (x : A) (y : A)
  map_smul' := by
    intro c x
    apply Subtype.ext
    change a * (c • (x : A)) = c • (a * (x : A))
    exact mul_smul_comm c a (x : A)

/-- The actual linear left action retains every original multiplication value. -/
@[simp]
theorem Weight.finiteSquareLeftMul_apply (φ : Weight A) (a : A) (x : φ.finiteSquareSubmodule) :
    (φ.finiteSquareLeftMul a x : A) = a * (x : A) :=
  rfl

/-- The original two-square core is exactly the finite domain intersected with its star preimage. -/
theorem Weight.mem_finiteStarSquareDomain_iff (φ : Weight A) (x : A) :
    x ∈ φ.finiteStarSquareDomain ↔ x ∈ φ.finiteSquareDomain ∧ star x ∈ φ.finiteSquareDomain := by
  change φ.value (leftSquare x) < ⊤ ∧ φ.value (rightSquare x) < ⊤ ↔
    φ.value (leftSquare x) < ⊤ ∧ φ.value (leftSquare (star x)) < ⊤
  rw [leftSquare_star]

/-- The exact two-square-finite core as a complex submodule of the original algebra. -/
def Weight.finiteStarSquareSubmodule (φ : Weight A) : Submodule ℂ A where
  carrier := φ.finiteStarSquareDomain
  zero_mem' := by
    apply (φ.mem_finiteStarSquareDomain_iff 0).2
    rw [star_zero]
    exact ⟨φ.zero_mem_finiteSquareDomain, φ.zero_mem_finiteSquareDomain⟩
  add_mem' := by
    intro x y hx hy
    obtain ⟨hx, hxStar⟩ := (φ.mem_finiteStarSquareDomain_iff x).1 hx
    obtain ⟨hy, hyStar⟩ := (φ.mem_finiteStarSquareDomain_iff y).1 hy
    apply (φ.mem_finiteStarSquareDomain_iff (x + y)).2
    refine ⟨φ.add_mem_finiteSquareDomain x y hx hy, ?_⟩
    rw [star_add]
    exact φ.add_mem_finiteSquareDomain (star x) (star y) hxStar hyStar
  smul_mem' := by
    intro c x hx
    obtain ⟨hx, hxStar⟩ := (φ.mem_finiteStarSquareDomain_iff x).1 hx
    apply (φ.mem_finiteStarSquareDomain_iff (c • x)).2
    refine ⟨φ.smul_mem_finiteSquareDomain c x hx, ?_⟩
    rw [star_smul]
    exact φ.smul_mem_finiteSquareDomain (star c) (star x) hxStar

/-- The actual core module retains exactly the original two-square-finite set. -/
@[simp]
theorem Weight.coe_finiteStarSquareSubmodule (φ : Weight A) :
    (φ.finiteStarSquareSubmodule : Set A) = φ.finiteStarSquareDomain :=
  rfl

/-- Original multiplication preserves the actual two-square-finite core. -/
theorem Weight.mul_mem_finiteStarSquareDomain (φ : Weight A) (x y : A)
    (hx : x ∈ φ.finiteStarSquareDomain) (hy : y ∈ φ.finiteStarSquareDomain) :
    x * y ∈ φ.finiteStarSquareDomain := by
  have hxStar := ((φ.mem_finiteStarSquareDomain_iff x).1 hx).2
  have hyLeft := ((φ.mem_finiteStarSquareDomain_iff y).1 hy).1
  apply (φ.mem_finiteStarSquareDomain_iff (x * y)).2
  refine ⟨φ.mul_mem_finiteSquareDomain x y hyLeft, ?_⟩
  rw [star_mul]
  exact φ.mul_mem_finiteSquareDomain (star y) (star x) hxStar

/-- The genuine algebraic core under original complex operations, product and star. -/
def Weight.finiteStarSquareSubalgebra (φ : Weight A) : NonUnitalStarSubalgebra ℂ A where
  carrier := φ.finiteStarSquareDomain
  zero_mem' := φ.finiteStarSquareSubmodule.zero_mem
  add_mem' := by
    intro x y hx hy
    exact φ.finiteStarSquareSubmodule.add_mem hx hy
  smul_mem' := by
    intro c x hx
    exact φ.finiteStarSquareSubmodule.smul_mem c hx
  mul_mem' := by
    intro x y hx hy
    exact φ.mul_mem_finiteStarSquareDomain x y hx hy
  star_mem' := by
    intro x hx
    exact (φ.finiteStarSquareDomain_star_iff x).2 hx

/-- The actual nonunital star algebra has exactly the original finite-star-square carrier. -/
@[simp]
theorem Weight.coe_finiteStarSquareSubalgebra (φ : Weight A) :
    (φ.finiteStarSquareSubalgebra : Set A) = φ.finiteStarSquareDomain :=
  rfl

end

end CStarAlgebra.ScalarWeight
