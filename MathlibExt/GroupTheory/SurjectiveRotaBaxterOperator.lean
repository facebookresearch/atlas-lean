/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Fintype.Basic

/-!
# A surjective non-injective Rota–Baxter operator (Kourovka Notebook Problem 20.125)

A Rota–Baxter operator (of weight `1`) on a group `G` is a map `B : G → G` such that
`B g * B h = B (g * B g * h * (B g)⁻¹)` for all `g h : G`. Problem 20.125 of the Kourovka
Notebook (V. G. Bardakov) asks whether there exist a non-abelian group `G` and a Rota–Baxter
operator on `G` that is surjective but not injective. The answer is yes: following van Doorn,
Judin, Monticone and Morrison (arXiv:2607.17477, Theorem 5.1), on `G = S₃ × ℤ^ℕ` the map
`B (σ, f) = (σ⁻¹, s f)`, where `s f n = f (n + 1)` is the left shift, is such an operator.

The verification is componentwise:

* inversion is a Rota–Baxter operator on every group, since both sides of the identity equal
  `g⁻¹ * h⁻¹ = (h * g)⁻¹`;
* on a commutative group, `g * B g * h * (B g)⁻¹ = g * h`, so the Rota–Baxter identity says that
  `B` is multiplicative; in particular the left shift, an endomorphism of `ℤ^ℕ`, is a Rota–Baxter
  operator;
* a product of Rota–Baxter operators is a Rota–Baxter operator on the product group.

Inversion is bijective and the left shift is surjective but not injective (it forgets `f 0`), so
`B` is surjective but not injective; `G` is not abelian because `S₃` is not.

## Main definitions

* `IsRotaBaxterOperator`: the Rota–Baxter identity of weight `1` for a map `B : G → G`.
* `surjectiveNonInjectiveRotaBaxterOperatorExists`: the statement of Kourovka Problem 20.125.
* `leftShift`: the left shift on `ℤ^ℕ`, written multiplicatively.
* `rotaBaxterExample`: the operator `(σ, f) ↦ (σ⁻¹, s f)` on `S₃ × ℤ^ℕ`.

## Main results

* `isRotaBaxterOperator_inv`: inversion is a Rota–Baxter operator.
* `isRotaBaxterOperator_iff_map_mul`, `isRotaBaxterOperator_monoidHom`: on a commutative group,
  the Rota–Baxter operators are the multiplicative maps; every endomorphism is one.
* `IsRotaBaxterOperator.prodMap`: products of Rota–Baxter operators.
* `surjectiveNonInjectiveRotaBaxterOperatorExists_holds`: the statement holds.

## Implementation notes

The definitions and the statement keep the full names they had in the former wanted module, so
the namespace still reads `SurjectiveRotaBaxterOperatorKourovka20Problem125Wanted`.

The group `S₃` is `Equiv.Perm (Fin 3)`. Mathlib's `ℕ → ℤ` is an additive group, so `ℤ^ℕ` enters
the multiplicative group `G` as `Multiplicative (ℕ → ℤ)`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.SurjectiveRotaBaxterOperatorKourovka20Problem125Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.125 (V. G. Bardakov). UnsolvedMath
record UM-00701783 (`KOU-20.125`), dataset ulamai/UnsolvedMath v1.8.0.

A Rota-Baxter operator (of weight `1`) satisfies `B(g) B(h) = B(g B(g) h B(g)⁻¹)`, the definition of
Guo-Lang-Sheng and Bardakov-Gubarev used in the resolving preprints.
-/

/-- **Rota–Baxter operators on groups.** A Rota–Baxter operator (of weight $1$) on a group $G$ is
a map $B \colon G \to G$ such that $B(g)\,B(h) = B\bigl(g\,B(g)\,h\,B(g)^{-1}\bigr)$ for all
$g, h \in G$. -/
def IsRotaBaxterOperator {G : Type} [Group G] (B : G → G) : Prop :=
  ∀ g h : G, B g * B h = B (g * B g * h * (B g)⁻¹)

/-- **Kourovka Problem 20.125 (surjective non-injective Rota–Baxter operators).** The statement,
asked by V. G. Bardakov, that there exist a non-abelian group $G$ and a Rota–Baxter operator $B$ on
$G$ such that $B$ is surjective but not injective. -/
def surjectiveNonInjectiveRotaBaxterOperatorExists : Prop :=
  ∃ (G : Type) (_ : Group G), (∃ x y : G, x * y ≠ y * x) ∧
    ∃ B : G → G, IsRotaBaxterOperator B ∧ Function.Surjective B ∧ ¬ Function.Injective B

/-! ### Examples and products of Rota–Baxter operators -/

/-- Inversion is a Rota–Baxter operator on every group: both sides of the identity equal
`g⁻¹ * h⁻¹ = (h * g)⁻¹`. -/
theorem isRotaBaxterOperator_inv {G : Type} [Group G] :
    IsRotaBaxterOperator fun g : G => g⁻¹ := by
  intro g h
  simp

/-- On a commutative group, `g * B g * h * (B g)⁻¹ = g * h`, so a map is a Rota–Baxter operator if
and only if it is multiplicative. -/
theorem isRotaBaxterOperator_iff_map_mul {G : Type} [CommGroup G] {B : G → G} :
    IsRotaBaxterOperator B ↔ ∀ g h : G, B g * B h = B (g * h) :=
  forall₂_congr fun g h => by rw [mul_right_comm (g * B g), mul_inv_cancel_right]

/-- Every endomorphism of a commutative group is a Rota–Baxter operator. -/
theorem isRotaBaxterOperator_monoidHom {G : Type} [CommGroup G] (f : G →* G) :
    IsRotaBaxterOperator f :=
  isRotaBaxterOperator_iff_map_mul.2 fun g h => (map_mul f g h).symm

/-- If `B` and `C` are Rota–Baxter operators on `G` and `H`, then `(g, h) ↦ (B g, C h)` is a
Rota–Baxter operator on `G × H`. -/
theorem IsRotaBaxterOperator.prodMap {G H : Type} [Group G] [Group H] {B : G → G} {C : H → H}
    (hB : IsRotaBaxterOperator B) (hC : IsRotaBaxterOperator C) :
    IsRotaBaxterOperator (Prod.map B C) :=
  fun g h => Prod.ext (hB g.1 h.1) (hC g.2 h.2)

/-! ### The left shift on `ℤ^ℕ` -/

/-- **The left shift on `ℤ^ℕ`.** The endomorphism $s(f)(n) = f(n + 1)$ of the additive group
$\mathbb{Z}^{\mathbb{N}}$ of functions $\mathbb{N} \to \mathbb{Z}$, written multiplicatively on
`Multiplicative (ℕ → ℤ)`. -/
def leftShift : Multiplicative (ℕ → ℤ) →* Multiplicative (ℕ → ℤ) where
  toFun f := Multiplicative.ofAdd fun n => f.toAdd (n + 1)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The `n`th term of the shift of `f` is the `(n + 1)`st term of `f`. -/
@[simp]
theorem toAdd_leftShift_apply (f : Multiplicative (ℕ → ℤ)) (n : ℕ) :
    (leftShift f).toAdd n = f.toAdd (n + 1) :=
  rfl

/-- The left shift is surjective: `f` is the shift of the sequence `0, f 0, f 1, …`. -/
theorem leftShift_surjective : Function.Surjective leftShift := fun f =>
  ⟨Multiplicative.ofAdd fun n => Nat.casesOn n 0 f.toAdd, rfl⟩

/-- The left shift is not injective: the sequence `1, 0, 0, …` and the zero sequence have the same
shift. -/
theorem leftShift_not_injective : ¬ Function.Injective leftShift := by
  intro h
  have h₁ : leftShift (Multiplicative.ofAdd fun n => if n = 0 then 1 else 0) = leftShift 1 :=
    congrArg Multiplicative.ofAdd (funext fun n => by simp)
  simpa using congrFun (congrArg Multiplicative.toAdd (h h₁)) 0

/-! ### The operator of van Doorn, Judin, Monticone and Morrison -/

/-- **A surjective non-injective Rota–Baxter operator on `S₃ × ℤ^ℕ`.** The map
$B(\sigma, f) = (\sigma^{-1}, s(f))$ on $S_3 \times \mathbb{Z}^{\mathbb{N}}$, where $S_3$ is
`Equiv.Perm (Fin 3)`, $\mathbb{Z}^{\mathbb{N}}$ is written multiplicatively and $s$ is the left
shift `leftShift`. -/
def rotaBaxterExample :
    Equiv.Perm (Fin 3) × Multiplicative (ℕ → ℤ) → Equiv.Perm (Fin 3) × Multiplicative (ℕ → ℤ) :=
  Prod.map (fun σ => σ⁻¹) leftShift

/-- `(σ, f) ↦ (σ⁻¹, s f)` is a Rota–Baxter operator on `S₃ × ℤ^ℕ`. -/
theorem isRotaBaxterOperator_rotaBaxterExample : IsRotaBaxterOperator rotaBaxterExample :=
  isRotaBaxterOperator_inv.prodMap (isRotaBaxterOperator_monoidHom leftShift)

/-- `(σ, f) ↦ (σ⁻¹, s f)` is surjective. -/
theorem rotaBaxterExample_surjective : Function.Surjective rotaBaxterExample :=
  inv_surjective.prodMap leftShift_surjective

/-- `(σ, f) ↦ (σ⁻¹, s f)` is not injective. -/
theorem rotaBaxterExample_not_injective : ¬ Function.Injective rotaBaxterExample := fun h =>
  leftShift_not_injective (Prod.map_injective.1 h).2

/-- The transpositions `(0 1)` and `(1 2)` do not commute, so `S₃` is not abelian. -/
private theorem swap_mul_swap_ne_swap_mul_swap :
    Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 ≠ Equiv.swap 1 2 * Equiv.swap 0 1 := by
  decide

/--
**A surjective, non-injective Rota–Baxter operator on a non-abelian group.** There exist a
non-abelian group $G$ and a Rota–Baxter operator $B$ on $G$ that is surjective but not injective.

For example, van Doorn, Judin, Monticone and Morrison take $G = S_3 \times \mathbb{Z}^{\mathbb{N}}$
and $B(\sigma, f) = (\sigma^{-1}, s(f))$, where $s$ is the left shift.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem
20.125 (V. G. Bardakov); resolution: P. Monticone, Kourovka Notebook Problem 20.125, solution note,
23 March 2026; W. van Doorn, E. Judin, P. Monticone and D. Morrison, On some problems from the
Kourovka Notebook, preprint, arXiv:2607.17477 (2026), van Doorn-Judin-Monticone-Morrison, Theorem
5.1: G = S3 × Z^N with B(σ, f) = (σ⁻¹, s(f)), s the left shift; the Kourovka Notebook (21st issue)
marks 20.125 solved (AI solution confirmed by V. G. Bardakov), https://arxiv.org/abs/2607.17477.
-/
theorem surjectiveNonInjectiveRotaBaxterOperatorExists_holds :
    surjectiveNonInjectiveRotaBaxterOperatorExists :=
  ⟨Equiv.Perm (Fin 3) × Multiplicative (ℕ → ℤ), inferInstance,
    ⟨(Equiv.swap 0 1, 1), (Equiv.swap 1 2, 1), fun h =>
      swap_mul_swap_ne_swap_mul_swap (congrArg Prod.fst h)⟩,
    rotaBaxterExample, isRotaBaxterOperator_rotaBaxterExample, rotaBaxterExample_surjective,
    rotaBaxterExample_not_injective⟩

end MathlibExt.GroupTheory.SurjectiveRotaBaxterOperatorKourovka20Problem125Wanted
