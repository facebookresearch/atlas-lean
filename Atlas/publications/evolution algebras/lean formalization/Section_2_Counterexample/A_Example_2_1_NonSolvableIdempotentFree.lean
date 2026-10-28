/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Group.Idempotent
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.StdBasis
import Section_1_Introduction.A_EvolutionAlgebra
import Section_1_Introduction.B_Conjecture_1_1_SolvableIffIdempotentFree
import Section_2_Preliminaries.A_Preliminaries

/-!
# Example 2.1: a non-solvable idempotent-free algebra

The three-dimensional complex evolution algebra `𝓔₀` disproving the original
García-Martínez / Pérez-Rodríguez conjecture (paper, `exm`).

The original conjecture states that a complex evolution algebra is solvable
if and only if it admits no nonzero idempotents. `𝓔₀` is neither solvable
nor does it have nonzero idempotents, so the conjecture is false.

The algebra data and all its structures are established below. The two key
facts are proved as `not_solvable` and `no_nonzero_idempotent`, so
`conjecture_false` holds without further assumptions.

## Main definitions

* `EvolutionAlgebras.Conjecture`: the original conjecture, as a `Prop`.
* `EvolutionAlgebras.Counterexample`: the carrier of `𝓔₀` (coordinate triples).

## Main results

* `Counterexample.not_solvable`, `Counterexample.no_nonzero_idempotent`:
  the two key facts about `𝓔₀` (nonsolvability, no nonzero idempotents).
* `EvolutionAlgebras.conjecture_false`: the original conjecture is false,
  with no further assumptions.
-/

namespace EvolutionAlgebras

/-- **Paper Example 2.1.** The carrier of the counterexample `𝓔₀`: coordinate triples. Addition,
negation and scalar action are pointwise; multiplication is the
evolution-algebra product from `structMat` (see `mul_apply`). All instances
below are proved. -/
structure Counterexample where
  toFun : Fin 3 → ℂ

namespace Counterexample

/-- Structure matrix of `𝓔₀` w.r.t. the natural basis (paper Example 2.1,
    `exm`):
rows `[-2 0 2; 0 1 -1; 0 -1 1]`. Determines the multiplication below and
every coordinate computation. -/
def structMat : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-2, 0, 2; 0, 1, -1; 0, -1, 1]

/-- **Helper.** Pointwise operations on the carrier `Counterexample` (paper Example 2.1):
addition, negation, and scalar action act coordinate by coordinate. -/
instance zeroInst : Zero Counterexample := ⟨⟨0⟩⟩

instance addInst : Add Counterexample := ⟨fun x y => ⟨x.toFun + y.toFun⟩⟩

instance negInst : Neg Counterexample := ⟨fun x => ⟨-x.toFun⟩⟩

instance smulInst : SMul ℂ Counterexample := ⟨fun c x => ⟨c • x.toFun⟩⟩

/-- Evolution-algebra multiplication from the structure matrix:
`(x * y) j = x₀y₀A₀ⱼ + x₁y₁A₁ⱼ + x₂y₂A₂ⱼ`. In particular `eᵢ * eⱼ = 0`
for `i ≠ j` and `eᵢ * eᵢ` is row `i` of `structMat`. -/
instance mulInst : Mul Counterexample :=
  ⟨fun x y => ⟨fun j => x.toFun 0 * y.toFun 0 * structMat 0 j +
    x.toFun 1 * y.toFun 1 * structMat 1 j +
    x.toFun 2 * y.toFun 2 * structMat 2 j⟩⟩

/-- Helper result: computation rules for the operations (each holds by `rfl`), for rewriting
in coordinate proofs. -/
@[simp] theorem mul_apply (x y : Counterexample) :
    x * y = ⟨fun j => x.toFun 0 * y.toFun 0 * structMat 0 j +
      x.toFun 1 * y.toFun 1 * structMat 1 j +
      x.toFun 2 * y.toFun 2 * structMat 2 j⟩ := rfl

@[simp] theorem add_apply (x y : Counterexample) :
    x + y = ⟨x.toFun + y.toFun⟩ := rfl

@[simp] theorem zero_def : (0 : Counterexample) = ⟨0⟩ := rfl

@[simp] theorem smul_def (c : ℂ) (x : Counterexample) :
    c • x = ⟨c • x.toFun⟩ := rfl

/-- Helper result: projecting a constructor gives back the coordinate function (holds by
`rfl`). -/
@[simp] theorem toFun_mk (f : Fin 3 → ℂ) :
    (⟨f⟩ : Counterexample).toFun = f := rfl

/-- `r₁ = e₁ * e₁ = -2e₁ + 2e₃` (paper Example 2.1, `exm`). One of the two
generators of the stable term of the derived series. -/
def r1 : Counterexample := ⟨![-2, 0, 2]⟩

/-- `r₂ = e₂ * e₂ = e₂ - e₃` (paper Example 2.1, `exm`). The second generator
of the stable term; it is nonzero, so the stable term is nonzero. -/
def r2 : Counterexample := ⟨![0, 1, -1]⟩

/-- `r₃ = e₃ * e₃ = -e₂ + e₃` (paper Example 2.1, `exm`). Since `r₃ = -r₂`,
every product expands in terms of `r₁` and `r₂` alone. -/
def r3 : Counterexample := ⟨![0, -1, 1]⟩

/-- Helper result: pointwise additive structure. -/
instance : AddCommMonoid Counterexample where
  nsmul := fun n x => ⟨n • x.toFun⟩
  nsmul_zero := by
    intro x
    cases x with | mk f
    change (⟨(0 : ℕ) • f⟩ : Counterexample) = ⟨0⟩
    simp only [Counterexample.mk.injEq]
    simp
  nsmul_succ := by
    intro n x
    cases x with | mk f
    change (⟨(n + 1 : ℕ) • f⟩ : Counterexample) = ⟨((n : ℕ) • f) + f⟩
    simp only [Counterexample.mk.injEq]
    funext j
    rw [add_smul, one_smul]
  add_assoc := by
    intro a b c
    cases a with | mk f
    cases b with | mk g
    cases c with | mk h
    change (⟨(f + g) + h⟩ : Counterexample) = ⟨f + (g + h)⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.add_apply]
    ring
  zero_add := by
    intro a
    cases a with | mk f
    change (⟨(0 : Fin 3 → ℂ) + f⟩ : Counterexample) = ⟨f⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.add_apply, Pi.zero_apply]
    ring
  add_zero := by
    intro a
    cases a with | mk f
    change (⟨f + (0 : Fin 3 → ℂ)⟩ : Counterexample) = ⟨f⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.add_apply, Pi.zero_apply]
    ring
  add_comm := by
    intro a b
    cases a with | mk f
    cases b with | mk g
    change (⟨f + g⟩ : Counterexample) = ⟨g + f⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.add_apply]
    ring

/-- Helper result: distributivity of the evolution product over pointwise addition,
checked coordinate by coordinate. -/
instance distribInst : Distrib Counterexample where
  left_distrib := by
    intro a b c
    cases a with | mk f
    cases b with | mk g
    cases c with | mk h
    simp only [mul_apply, add_apply, Counterexample.mk.injEq]
    funext j
    simp only [Pi.add_apply]
    ring
  right_distrib := by
    intro a b c
    cases a with | mk f
    cases b with | mk g
    cases c with | mk h
    simp only [mul_apply, add_apply, Counterexample.mk.injEq]
    funext j
    simp only [Pi.add_apply]
    ring

/-- Helper result: zero annihilates the evolution product. -/
instance mulZeroInst : MulZeroClass Counterexample where
  zero_mul := by
    intro a
    cases a with | mk f
    change (⟨fun j => (0 : Fin 3 → ℂ) 0 * f 0 * structMat 0 j +
      (0 : Fin 3 → ℂ) 1 * f 1 * structMat 1 j +
      (0 : Fin 3 → ℂ) 2 * f 2 * structMat 2 j⟩ : Counterexample) = ⟨0⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.zero_apply]
    ring
  mul_zero := by
    intro a
    cases a with | mk f
    change (⟨fun j => f 0 * (0 : Fin 3 → ℂ) 0 * structMat 0 j +
      f 1 * (0 : Fin 3 → ℂ) 1 * structMat 1 j +
      f 2 * (0 : Fin 3 → ℂ) 2 * structMat 2 j⟩ : Counterexample) = ⟨0⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.zero_apply]
    ring

/-- Helper result: pointwise `ℂ`-module structure. -/
instance : Module ℂ Counterexample where
  one_smul := by
    intro a
    cases a with | mk f
    change (⟨(1 : ℂ) • f⟩ : Counterexample) = ⟨f⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.smul_apply]
    simp
  mul_smul := by
    intro c d a
    cases a with | mk f
    change (⟨(c * d : ℂ) • f⟩ : Counterexample) = ⟨c • (d • f)⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.smul_apply]
    ring
  smul_add := by
    intro c a b
    cases a with | mk f
    cases b with | mk g
    change (⟨c • (f + g)⟩ : Counterexample) = ⟨(c • f) + (c • g)⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.smul_apply, Pi.add_apply]
    ring
  smul_zero := by
    intro c
    change (⟨c • (0 : Fin 3 → ℂ)⟩ : Counterexample) = ⟨0⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.smul_apply, Pi.zero_apply]
    simp
  add_smul := by
    intro c d a
    cases a with | mk f
    change (⟨((c + d : ℂ)) • f⟩ : Counterexample) = ⟨(c • f) + (d • f)⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.smul_apply, Pi.add_apply]
    ring
  zero_smul := by
    intro a
    cases a with | mk f
    simp only [smul_def, zero_def, Counterexample.mk.injEq]
    funext j
    simp only [Pi.smul_apply, Pi.zero_apply]
    simp

/-- Helper result: the semiring structure, assembled from the additive and multiplicative
structures above. -/
instance : NonUnitalNonAssocSemiring Counterexample where
  toAddCommMonoid := inferInstance
  toMul := inferInstance
  left_distrib := distribInst.left_distrib
  right_distrib := distribInst.right_distrib
  zero_mul := mulZeroInst.zero_mul
  mul_zero := mulZeroInst.mul_zero

/-- Helper result: pointwise subtraction. -/
instance subInst : Sub Counterexample := ⟨fun x y => ⟨x.toFun - y.toFun⟩⟩

/-- Helper result: pointwise `ℤ`-scalar action. -/
instance zsmulInst : SMul ℤ Counterexample := ⟨fun n x => ⟨n • x.toFun⟩⟩

/-- Helper result: pointwise subtraction and integer-scalar structure. -/
instance : SubNegMonoid Counterexample where
  toAddMonoid := inferInstance
  toNeg := inferInstance
  toSub := inferInstance
  toZSMul := inferInstance
  sub_eq_add_neg := by
    intro a b
    cases a with | mk f
    cases b with | mk g
    change (⟨f - g⟩ : Counterexample) = ⟨f + -g⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
    exact sub_eq_add_neg _ _
  zsmul_zero' := by
    intro a
    cases a with | mk f
    change (⟨(0 : ℤ) • f⟩ : Counterexample) = ⟨0⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.smul_apply, Pi.zero_apply]
    rw [show (0 : ℤ) = 1 - 1 from (sub_self 1).symm, sub_smul, one_smul,
      sub_self]
  zsmul_succ' := by
    intro n a
    cases a with | mk f
    change (⟨((n.succ : ℕ) : ℤ) • f⟩ : Counterexample) = ⟨((n : ℤ) • f) + f⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.smul_apply, Pi.add_apply]
    rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  zsmul_neg' := by
    intro n a
    cases a with | mk f
    change (⟨(Int.negSucc n) • f⟩ : Counterexample) = ⟨-(((n.succ : ℕ) : ℤ) • f)⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.smul_apply, Pi.neg_apply]
    rw [Int.negSucc_eq, neg_smul, Nat.succ_eq_add_one, Nat.cast_add,
      Nat.cast_one]

/-- Helper result: pointwise additive group structure. -/
instance : AddGroup Counterexample where
  toSubNegMonoid := inferInstance
  neg_add_cancel := by
    intro a
    cases a with | mk f
    change (⟨-f + f⟩ : Counterexample) = ⟨0⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
    exact neg_add_cancel _

/-- Helper result: pointwise additive commutative group structure (only commutativity
is new; the rest is inherited from the structures above). -/
instance : AddCommGroup Counterexample where
  toAddGroup := inferInstance
  add_comm := by
    intro a b
    cases a with | mk f
    cases b with | mk g
    change (⟨f + g⟩ : Counterexample) = ⟨g + f⟩
    simp only [Counterexample.mk.injEq]
    funext j
    simp only [Pi.add_apply]
    ring

/-- Helper result: the (non-unital, non-associative) ring structure, assembled from the
additive group and multiplicative structures above. -/
instance : NonUnitalNonAssocRing Counterexample where
  toAddCommGroup := inferInstance
  toMul := inferInstance
  left_distrib := distribInst.left_distrib
  right_distrib := distribInst.right_distrib
  zero_mul := mulZeroInst.zero_mul
  mul_zero := mulZeroInst.mul_zero

/-- Helper result: the scalar action of `Counterexample` on itself coincides with `*`. -/
@[simp] theorem smul_toMul (x y : Counterexample) : x • y = x * y := rfl

/-- Helper result: scalar action passes through the evolution product on the left:
`(c • x) * y = c • (x * y)`, checked coordinate by coordinate. -/
instance : IsScalarTower ℂ Counterexample Counterexample where
  smul_assoc := by
    intro c x y
    cases x with | mk f
    cases y with | mk g
    simp only [smul_toMul, mul_apply, smul_def, Counterexample.mk.injEq]
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Helper result: scalar action passes through the evolution product on the right:
`c • (x * y) = x * (c • y)`, checked coordinate by coordinate. -/
instance : SMulCommClass ℂ Counterexample Counterexample where
  smul_comm := by
    intro c x y
    cases x with | mk f
    cases y with | mk g
    simp only [smul_toMul, mul_apply, smul_def, Counterexample.mk.injEq]
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Helper result: the algebra bundle, assembled from the module and scalar-compatibility
structures above. -/
instance : NonUnitalNonAssocAlgebra ℂ Counterexample where
  toModule := inferInstance
  toIsScalarTower := inferInstance
  toSMulCommClass := inferInstance

/-- Helper result: coordinate functions as a linear equivalence. Transports the standard
basis (`Pi.basisFun`) onto `Counterexample` to prove the `EvolutionAlgebra`
instance below. -/
def toFunEquiv : (Fin 3 → ℂ) ≃ₗ[ℂ] Counterexample where
  toFun := Counterexample.mk
  map_add' := by intro f g; rfl
  map_smul' := by intro c f; rfl
  invFun := Counterexample.toFun
  left_inv := by intro f; rfl
  right_inv := by intro x; cases x with | mk f; rfl

/-- Helper result: the equivalence acts as the constructor on functions. -/
@[simp] theorem toFunEquiv_apply (f : Fin 3 → ℂ) : toFunEquiv f = ⟨f⟩ := rfl

/-- Helper result: the standard basis is a natural basis (paper Example 2.1: `𝓔₀` is an
evolution algebra): distinct basis vectors multiply to zero since their
coordinate supports are disjoint. -/
instance : EvolutionAlgebra ℂ Counterexample :=
  ⟨3, (Pi.basisFun ℂ (Fin 3)).map toFunEquiv, fun i j hij => by
    -- Each rewriting rule is applied once per basis vector (`i` and `j`).
    rw [Module.Basis.map_apply, Module.Basis.map_apply,
      Pi.basisFun_apply, Pi.basisFun_apply,
      toFunEquiv_apply, toFunEquiv_apply, mul_apply, zero_def]
    simp only [Counterexample.mk.injEq]
    funext m
    have key : ∀ k : Fin 3,
        Pi.single (M := fun _ => ℂ) i 1 k * Pi.single (M := fun _ => ℂ) j 1 k
          = 0 := by
      intro k
      by_cases h : i = k
      · subst h
        have h2 : j ≠ i := Ne.symm hij
        simp [h2]
      · simp [h]
    simp only [key, zero_mul, add_zero, Pi.zero_apply]⟩

/-- `r₁ * r₁ = 4r₁ - 4r₂`: coordinate computation (paper Example 2.1). Used
to express `r₁` through products below. -/
theorem r1_mul_r1 : r1 * r1 = (4 : ℂ) • r1 + ((-4 : ℂ)) • r2 := by
  unfold r1 r2
  simp only [mul_apply, smul_def, add_apply, Counterexample.mk.injEq]
  funext j
  fin_cases j <;> simp [structMat, smul_eq_mul] <;> ring

/-- `r₁ * r₂ = 2r₂`: coordinate computation. Used to express `r₁` and `r₂`
through products below. -/
theorem r1_mul_r2 : r1 * r2 = (2 : ℂ) • r2 := by
  unfold r1 r2
  simp only [mul_apply, smul_def, Counterexample.mk.injEq]
  funext j
  fin_cases j <;> simp [structMat, smul_eq_mul]

/-- `r₁` as a combination of products: `r₁ = ¼(r₁r₁) + ½(r₁r₂)`. Shows `r₁`
lies in the square of the algebra, and in the square of `span{r₁, r₂}`. -/
theorem r1_combo : r1 = (1 / 4 : ℂ) • (r1 * r1) + (1 / 2 : ℂ) • (r1 * r2) := by
  unfold r1 r2
  simp only [mul_apply, smul_def, add_apply, Counterexample.mk.injEq]
  funext j
  fin_cases j <;> simp [structMat, smul_eq_mul] <;> ring

/-- `r₂ = ½(r₁r₂)`. Shows `r₂` lies in the square of the algebra, and in
the square of `span{r₁, r₂}`. -/
theorem r2_combo : r2 = (1 / 2 : ℂ) • (r1 * r2) := by
  unfold r1 r2
  simp only [mul_apply, smul_def, Counterexample.mk.injEq]
  funext j
  fin_cases j <;> simp [structMat, smul_eq_mul]

/-- Expansion of the evolution product: every `x * y` is a combination of
`r₁` and `r₂` (this uses `structMat` row 2 = −row 1, i.e. `r₃ = -r₂`).
The key computation for nonsolvability: every square lands in
`span{r₁, r₂}`. -/
theorem evoMul_expand (x y : Counterexample) :
    x * y = (x.toFun 0 * y.toFun 0) • r1 +
      (x.toFun 1 * y.toFun 1 - x.toFun 2 * y.toFun 2) • r2 := by
  cases x with | mk f
  cases y with | mk g
  have hrow : ∀ j, structMat 2 j = -structMat 1 j := by
    intro j
    fin_cases j <;> simp [structMat]
  have hr1 : ∀ j, r1.toFun j = structMat 0 j := by
    intro j
    fin_cases j <;> rfl
  have hr2 : ∀ j, r2.toFun j = structMat 1 j := by
    intro j
    fin_cases j <;> rfl
  simp only [mul_apply, smul_def, add_apply, Counterexample.mk.injEq]
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, hr1, hr2, hrow]
  ring

/-- `r₂ ≠ 0` (witness: the second coordinate is `1`). Hence the stable
term `span{r₁, r₂}` is nonzero. -/
theorem r2_ne_zero : r2 ≠ 0 := by
  intro h
  have h2 : (![0, 1, -1] : Fin 3 → ℂ) = 0 := congrArg Counterexample.toFun h
  have h3 := congrFun h2 1
  simp at h3

/-- Paper Example 2.1 (`𝓔₀⁽²⁾`): the square of the whole algebra is
`span{r₁, r₂}`. Together with `sq_span` below, this says the derived series
stabilizes at `span{r₁, r₂}`. -/
theorem sq_top :
    square ℂ Counterexample ⊤ = Submodule.span ℂ {r1, r2} := by
  apply le_antisymm
  · unfold square
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨x, -, y, -, rfl⟩ := hz
    rw [evoMul_expand]
    apply Submodule.add_mem <;> apply Submodule.smul_mem
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  · rw [Submodule.span_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    obtain rfl | rfl := hv
    · rw [r1_combo]
      apply Submodule.add_mem <;> apply Submodule.smul_mem
      · unfold square
        exact Submodule.subset_span ⟨r1, Submodule.mem_top, r1,
          Submodule.mem_top, rfl⟩
      · unfold square
        exact Submodule.subset_span ⟨r1, Submodule.mem_top, r2,
          Submodule.mem_top, rfl⟩
    · rw [r2_combo]
      apply Submodule.smul_mem
      unfold square
      exact Submodule.subset_span ⟨r1, Submodule.mem_top, r2,
        Submodule.mem_top, rfl⟩

/-- Stabilization (paper Example 2.1: `𝓔₀⁽ᵏ⁾ = 𝓔₀⁽²⁾` for `k ≥ 2`): squaring
`span{r₁, r₂}` fixes it. -/
theorem sq_span :
    square ℂ Counterexample (Submodule.span ℂ {r1, r2}) =
      Submodule.span ℂ {r1, r2} := by
  have hmem1 : r1 ∈ Submodule.span ℂ ({r1, r2} : Set Counterexample) :=
    Submodule.subset_span (by simp)
  have hmem2 : r2 ∈ Submodule.span ℂ ({r1, r2} : Set Counterexample) :=
    Submodule.subset_span (by simp)
  apply le_antisymm
  · unfold square
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    rw [evoMul_expand]
    apply Submodule.add_mem <;> apply Submodule.smul_mem
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  · rw [Submodule.span_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    obtain rfl | rfl := hv
    · have hmem : (1 / 4 : ℂ) • (r1 * r1) + (1 / 2 : ℂ) • (r1 * r2) ∈
          square ℂ Counterexample (Submodule.span ℂ {r1, r2}) := by
        apply Submodule.add_mem <;> apply Submodule.smul_mem
        · unfold square
          exact Submodule.subset_span ⟨r1, hmem1, r1, hmem1, rfl⟩
        · unfold square
          exact Submodule.subset_span ⟨r1, hmem1, r2, hmem2, rfl⟩
      rw [← r1_combo] at hmem
      exact hmem
    · have hmem : (1 / 2 : ℂ) • (r1 * r2) ∈
          square ℂ Counterexample (Submodule.span ℂ {r1, r2}) := by
        apply Submodule.smul_mem
        unfold square
        exact Submodule.subset_span ⟨r1, hmem1, r2, hmem2, rfl⟩
      rw [← r2_combo] at hmem
      exact hmem

/-- Every derived term from the second on is `span{r₁, r₂}` (paper: the
    series
stabilizes at `𝓔₀⁽²⁾`). Since this subspace is nonzero, `𝓔₀` is not solvable. -/
theorem stab : ∀ k, derivedSeries ℂ Counterexample (k + 1) =
    Submodule.span ℂ {r1, r2} := by
  intro k
  induction k with
  | zero =>
    rw [derivedSeries_succ ℂ Counterexample, derivedSeries_zero ℂ Counterexample]
    exact sq_top
  | succ k ih =>
    rw [derivedSeries_succ ℂ Counterexample, ih]
    exact sq_span

/-- `span{r₁, r₂}` is nonzero (it contains `r₂ ≠ 0`). Hence every derived
term of `𝓔₀` is nonzero. -/
theorem span_ne_bot : Submodule.span ℂ {r1, r2} ≠ ⊥ := by
  intro h
  have hmem : r2 ∈ (⊥ : Submodule ℂ Counterexample) := by
    rw [← h]
    exact Submodule.subset_span (by simp)
  rw [Submodule.mem_bot] at hmem
  exact r2_ne_zero hmem

/-- `𝓔₀` is not solvable: every derived term is nonzero (`⊤` at step zero,
`span{r₁, r₂} ≠ ⊥` after). Paper Example 2.1, first half of the disproof. -/
theorem not_solvable : ¬ IsSolvable ℂ Counterexample := by
  intro h
  obtain ⟨k, hk⟩ := h.solvable
  cases k with
  | zero =>
    rw [derivedSeries_zero ℂ Counterexample] at hk
    have hmem : r2 ∈ (⊥ : Submodule ℂ Counterexample) := by
      rw [← hk]
      exact Submodule.mem_top
    rw [Submodule.mem_bot] at hmem
    exact r2_ne_zero hmem
  | succ k =>
    rw [stab k] at hk
    exact span_ne_bot hk

/-- No nonzero idempotents in `𝓔₀`: `x * x = x` forces every coordinate to
`0`. With `(a, b, c)` the coordinates, the idempotent equation gives
`-2a² = a`, `b² - c² = b`, `2a² - b² + c² = c`; hence `a ∈ {0, -½}`. If
`a = 0` then `(b - c)(b + c) = b` with `b + c = 0` gives `b = c = 0`; if
`a = -½` then `b + c = ½` against `(b - c) / 2 = b`. Paper Example 2.1,
second half of the disproof (the coordinate system has only the trivial
solution). -/
theorem no_nonzero_idempotent :
    ¬ ∃ x : Counterexample, IsIdempotentElem x ∧ x ≠ 0 := by
  intro h'
  obtain ⟨x, hx, hne⟩ := h'
  have hxx : x * x = x := hx
  cases x with | mk f
  have e0 := congrFun (congrArg Counterexample.toFun hxx) 0
  have e1 := congrFun (congrArg Counterexample.toFun hxx) 1
  have e2 := congrFun (congrArg Counterexample.toFun hxx) 2
  simp only [mul_apply, toFun_mk] at e0 e1 e2
  have e00 : structMat 0 0 = (-2 : ℂ) := rfl
  have e01 : structMat 0 1 = (0 : ℂ) := rfl
  have e02 : structMat 0 2 = (2 : ℂ) := rfl
  have e10 : structMat 1 0 = (0 : ℂ) := rfl
  have e11 : structMat 1 1 = (1 : ℂ) := rfl
  have e12 : structMat 1 2 = (-1 : ℂ) := rfl
  have e20 : structMat 2 0 = (0 : ℂ) := rfl
  have e21 : structMat 2 1 = (-1 : ℂ) := rfl
  have e22 : structMat 2 2 = (1 : ℂ) := rfl
  rw [e00, e10, e20] at e0
  rw [e01, e11, e21] at e1
  rw [e02, e12, e22] at e2
  have e0s := e0.symm
  have hfac : f 0 * (2 * f 0 + 1) = 0 := by linear_combination e0s
  obtain ha | ha1 := mul_eq_zero.mp hfac
  · rw [ha] at e2
    have e1s := e1.symm
    have e2s := e2.symm
    have hbc : f 1 + f 2 = 0 := by linear_combination e1s + e2s
    have hfac2 : (f 1 - f 2) * (f 1 + f 2) = f 1 := by linear_combination e1
    rw [hbc] at hfac2
    rw [mul_zero] at hfac2
    have hb : f 1 = 0 := hfac2.symm
    have hc : f 2 = 0 := by
      rw [hb] at hbc
      simpa using hbc
    have hf0 : f = 0 := by
      funext j
      fin_cases j <;> simp [ha, hb, hc]
    apply hne
    rw [hf0]
    exact zero_def.symm
  · have ha2 : f 0 = -1 / 2 := by linear_combination ha1 / 2
    rw [ha2] at e2
    have e1s := e1.symm
    have e2s := e2.symm
    have hsum : f 1 + f 2 = 1 / 2 := by linear_combination e1s + e2s
    have hfac2 : (f 1 - f 2) * (f 1 + f 2) = f 1 := by linear_combination e1
    rw [hsum] at hfac2
    have hcontra : (-1 / 2 : ℂ) = 0 := by linear_combination 2 * hfac2 + hsum
    norm_num at hcontra

end Counterexample

/- Both key facts about `𝓔₀` are now proved (`Counterexample.not_solvable`,
`Counterexample.no_nonzero_idempotent`), so the disproof below needs no
further assumptions. -/

/-- **Paper Conjecture 1.1.** The original conjecture (paper Conjecture 1.1, `theconjecture`) is
    false,
witnessed by `𝓔₀`: it is not solvable yet admits no nonzero idempotents, so the
two sides of the claimed `↔` differ. Combines `not_solvable` with
`no_nonzero_idempotent`. -/
theorem conjecture_false : ¬ Conjecture := fun h =>
  Counterexample.not_solvable ((h Counterexample).mpr Counterexample.no_nonzero_idempotent)

end EvolutionAlgebras
