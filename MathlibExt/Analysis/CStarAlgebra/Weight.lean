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

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Algebra.Order.Nonneg.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Global scalar weights on the original nonunital C-star algebra

An extended positive weight on a nonunital C-star algebra has positive
additivity and nonnegative-real homogeneity. Its finite square domain is
`{x : phi (star x * x) < infinity}`. Norm semicontinuity, norm density and
the trace-square law are separate properties.

Every positive-domain type below uses the stock canonical spectral order.
All topologies and norms are inherited from the given algebra A. No local
AF algebra, K0 map, bounded functional or alternate carrier is stored.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped NNReal ENNReal

namespace CStarAlgebra
namespace ScalarWeight

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- **Positive cone of a nonunital C*-algebra.** Let `A` be a nonunital complex C*-algebra with its
canonical spectral order. Its positive cone consists of elements `a ∈ A` satisfying `0 ≤ a`. -/
abbrev PositiveElement (A : Type u) [NonUnitalCStarAlgebra A] := Nonneg A

/-- **Zero in the positive cone.** Let `A` be a nonunital complex C*-algebra with its canonical spectral
order. The zero element is an element of the positive cone of `A`. -/
def positiveZero (A : Type u) [NonUnitalCStarAlgebra A] : PositiveElement A :=
  ⟨0, le_rfl⟩

/-- **Addition in the positive cone.** Let `A` be a nonunital complex C*-algebra with its canonical
spectral order. For positive elements `a,b ∈ A`, their sum `a+b` is positive. -/
def positiveAdd (a b : PositiveElement A) : PositiveElement A :=
  ⟨(a : A) + (b : A), add_nonneg a.property b.property⟩

/-- **Nonnegative scalar action on the positive cone.** Let `A` be a nonunital complex C*-algebra with
its canonical spectral order. For a finite nonnegative real scalar `r` and a positive element `a ∈
A`, the element `r a` is positive. -/
noncomputable def positiveSmul (r : ℝ≥0) (a : PositiveElement A) : PositiveElement A :=
  ⟨(r : ℝ) • (a : A), smul_nonneg r.property a.property⟩

/-- **Positive adjoint square.** Let `A` be a nonunital complex C*-algebra with its canonical spectral
order. For every `x ∈ A`, the product `x* x` is an element of its positive cone. -/
def leftSquare (x : A) : PositiveElement A :=
  ⟨star x * x, star_mul_self_nonneg x⟩

/-- **Positive reversed adjoint square.** Let `A` be a nonunital complex C*-algebra with its canonical
spectral order. For every `x ∈ A`, the product `x x*` is an element of its positive cone. -/
def rightSquare (x : A) : PositiveElement A :=
  ⟨x * star x, by simpa only [star_star] using star_mul_self_nonneg (star x)⟩

/-- **Extended positive weight.** Let `A` be a nonunital complex C*-algebra with its canonical spectral
order. A weight is a map `φ : A₊ → [0,∞]` that vanishes at zero, is additive on positive elements,
and satisfies `φ(r a) = r φ(a)` for every finite nonnegative real scalar `r`. Infinite weight values
are allowed. -/
structure Weight (A : Type u) [NonUnitalCStarAlgebra A] where
  /-- The global extended nonnegative value on each actual positive element. -/
  value : PositiveElement A → ℝ≥0∞
  zero_value : value (positiveZero A) = 0
  add_value : ∀ a b, value (positiveAdd a b) = value a + value b
  smul_value : ∀ (r : ℝ≥0) a, value (positiveSmul r a) = (r : ℝ≥0∞) * value a

/-- **Extensionality of positive weights.** Let `A` be a nonunital complex C*-algebra with its canonical
spectral order. Two extended positive weights on `A` are equal if their values agree at every
positive element. -/
@[ext]
theorem Weight.ext_value {φ ψ : Weight A} (h : ∀ a : PositiveElement A, φ.value a = ψ.value a) :
    φ = ψ := by
  rcases φ with ⟨f, hf0, hfadd, hfsmul⟩
  rcases ψ with ⟨g, hg0, hgadd, hgsmul⟩
  have hfg : f = g := funext h
  cases hfg
  rfl

/-- **Zero positive weight.** Let `A` be a nonunital complex C*-algebra with its canonical spectral
order. The map assigning value zero to every positive element is an extended positive weight on `A`. -/
def zeroWeight (A : Type u) [NonUnitalCStarAlgebra A] : Weight A where
  value := fun _ => 0
  zero_value := rfl
  add_value := by intro a b; exact (zero_add 0).symm
  smul_value := by intro r a; exact (mul_zero (r : ℝ≥0∞)).symm

/-- **Finite positive domain of a weight.** Let `A` be a nonunital complex C*-algebra with its canonical
spectral order. For a weight `φ`, its finite positive domain is the set of positive `a ∈ A` for
which `φ(a) < ∞`. -/
def Weight.finitePositiveElements (phi : Weight A) : Set A :=
  {a | ∃ ha : (0 : A) ≤ a, phi.value ⟨a, ha⟩ < ⊤}

/-- **Finite square domain of a weight.** Let `A` be a nonunital complex C*-algebra with its canonical
spectral order. For a weight `φ`, its finite square domain is `{x ∈ A : φ(x* x) < ∞}`. -/
def Weight.finiteSquareDomain (phi : Weight A) : Set A :=
  {x | phi.value (leftSquare x) < ⊤}

/-- **Finite integration span of a weight.** Let `A` be a nonunital complex C*-algebra with its
canonical spectral order. For a weight `φ`, the finite integration domain is the complex-linear span
in `A` of its positive elements of finite weight. -/
def Weight.finiteIntegrationDomain (phi : Weight A) : Submodule ℂ A :=
  Submodule.span ℂ phi.finitePositiveElements

/-- **Tracial square law for a weight.** Let `A` be a nonunital complex C*-algebra with its canonical
spectral order. A weight `φ` is tracial when `φ(x* x) = φ(x x*)` for every `x ∈ A`. -/
def Weight.IsTracial (phi : Weight A) : Prop :=
  ∀ x : A, phi.value (leftSquare x) = phi.value (rightSquare x)

/-- **Tracial positive weight.** Let `A` be a nonunital complex C*-algebra with its canonical spectral
order. This is an extended positive weight `φ` on `A` satisfying `φ(x* x) = φ(x x*)` for every `x ∈
A`. -/
abbrev TracialWeight (A : Type u) [NonUnitalCStarAlgebra A] :=
  {phi : Weight A // phi.IsTracial}

/-- **Norm lower semicontinuity of a weight.** Let `A` be a nonunital complex C*-algebra with its
canonical spectral order. A weight `φ` is norm lower semicontinuous when its value function on `A₊`,
with the inherited norm topology, is lower semicontinuous. -/
def Weight.IsNormLowerSemicontinuous (phi : Weight A) : Prop :=
  LowerSemicontinuous phi.value

/-- **Norm-densely-defined weight.** Let `A` be a nonunital complex C*-algebra with its canonical
spectral order. A weight `φ` is norm densely defined when its finite square domain `{x : φ(x* x) <
∞}` is norm-dense in `A`. -/
def Weight.IsNormDenselyDefined (phi : Weight A) : Prop :=
  Dense phi.finiteSquareDomain

/-- **Norm density of a finite integration domain.** Let `A` be a nonunital complex C*-algebra with its
canonical spectral order. A weight has this property when the complex-linear span of its finite
positive elements is norm-dense in `A`. -/
def Weight.HasNormDenseIntegrationDomain (phi : Weight A) : Prop :=
  Dense (phi.finiteIntegrationDomain : Set A)

/-- **Finite weight of a positive sum.** Let `A` be a nonunital complex C*-algebra with its canonical
spectral order. For a weight `φ` and positive `a,b ∈ A`, `φ(a+b) < ∞` exactly when both `φ(a) < ∞`
and `φ(b) < ∞`. -/
theorem Weight.finite_add_iff (phi : Weight A) (a b : PositiveElement A) :
    phi.value (positiveAdd a b) < ⊤ ↔ phi.value a < ⊤ ∧ phi.value b < ⊤ := by
  rw [phi.add_value]
  exact ENNReal.add_lt_top

/-- **Zero lies in every finite square domain.** Let `A` be a nonunital complex C*-algebra with its
canonical spectral order. For every weight `φ`, the zero element belongs to `{x : φ(x* x) < ∞}`. -/
theorem Weight.zero_mem_finiteSquareDomain (phi : Weight A) :
    (0 : A) ∈ phi.finiteSquareDomain := by
  have hzero : leftSquare (0 : A) = positiveZero A := by
    apply Subtype.ext
    simp only [leftSquare, positiveZero, star_zero, zero_mul]
  change phi.value (leftSquare (0 : A)) < ⊤
  rw [hzero, phi.zero_value]
  exact ENNReal.zero_lt_top

/-- **Star exchanges the adjoint squares.** Let `A` be a nonunital complex C*-algebra with its canonical
spectral order. For `x ∈ A`, the positive square `(x*)* x*` equals `x x*`. -/
theorem leftSquare_star (x : A) : leftSquare (star x) = rightSquare x := by
  apply Subtype.ext
  simp only [leftSquare, rightSquare, star_star]

/-- **Star invariance of a tracial finite square domain.** Let `A` be a nonunital complex C*-algebra
with its canonical spectral order. For a tracial weight `φ` and `x ∈ A`, `x*` belongs to the finite
square domain exactly when `x` does. -/
theorem Weight.finiteSquareDomain_star_iff (phi : Weight A) (hphi : phi.IsTracial)
    (x : A) : star x ∈ phi.finiteSquareDomain ↔ x ∈ phi.finiteSquareDomain := by
  change phi.value (leftSquare (star x)) < ⊤ ↔ phi.value (leftSquare x) < ⊤
  rw [leftSquare_star, ← hphi x]

/-- **Closed sublevels of a lower semicontinuous weight.** Let `A` be a nonunital complex C*-algebra
with its canonical spectral order. A weight `φ` is norm lower semicontinuous exactly when `{a ∈ A₊ :
φ(a) ≤ r}` is closed in the positive cone for every `r ∈ [0,∞]`. -/
theorem Weight.normLowerSemicontinuous_iff (phi : Weight A) :
    phi.IsNormLowerSemicontinuous ↔ ∀ r : ℝ≥0∞,
      IsClosed {a : PositiveElement A | phi.value a ≤ r} :=
  lowerSemicontinuous_iff_isClosed_preimage

/-- **Value of the zero weight.** Let `A` be a nonunital complex C*-algebra with its canonical spectral
order. The zero weight takes the extended real value zero at every positive `a ∈ A`. -/
theorem zeroWeight_value (a : PositiveElement A) : (zeroWeight A).value a = 0 := rfl

/-- **Square domain of the zero weight.** Let `A` be a nonunital complex C*-algebra with its canonical
spectral order. Every element of `A` belongs to the finite square domain of the zero weight. -/
theorem zeroWeight_finiteSquareDomain : (zeroWeight A).finiteSquareDomain = Set.univ := by
  ext x
  simp [Weight.finiteSquareDomain, zeroWeight, ENNReal.zero_lt_top]

/-- **The zero weight is tracial.** Let `A` be a nonunital complex C*-algebra with its canonical
spectral order. The zero weight satisfies equality of its values at `x* x` and `x x*` for every `x ∈
A`. -/
theorem zeroWeight_isTracial : (zeroWeight A).IsTracial := by
  intro x
  rfl

/-- **Lower semicontinuity of the zero weight.** Let `A` be a nonunital complex C*-algebra with its
canonical spectral order. The zero weight is lower semicontinuous on the positive cone in its
inherited norm topology. -/
theorem zeroWeight_isNormLowerSemicontinuous :
    (zeroWeight A).IsNormLowerSemicontinuous :=
  lowerSemicontinuous_const

/-- **Dense definition of the zero weight.** Let `A` be a nonunital complex C*-algebra with its
canonical spectral order. The finite square domain of the zero weight is norm-dense in `A`, since it
is all of `A`. -/
theorem zeroWeight_isNormDenselyDefined : (zeroWeight A).IsNormDenselyDefined := by
  rw [Weight.IsNormDenselyDefined, zeroWeight_finiteSquareDomain]
  exact dense_univ

end ScalarWeight
end CStarAlgebra
