/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetDeformationRetract

@[expose] public section

/-!
# Minimal fibrations – basic definitions

This module provides the pure simplicial-set foundation for the minimal-fibration lane.

* Goerss–Jardine, *Simplicial Homotopy Theory*, Chapter I §10, Definitions 10.2 and the
  minimality criterion around Proposition 10.4.
* Hovey, *Model Categories*, §3.5.

We work with a map `p : X ⟶ S` of simplicial sets.  An `n`-simplex `x : X _⦋n⦌`
is identified with a map `Δ[n] ⟶ X` via `SSet.yonedaEquiv.symm`.  Two `n`-simplices
with the same image in `S` and the same restriction to `∂Δ[n]` are *fiberwise
homotopic relative to the boundary* when there exists `H : Δ[n] ⊗ Δ[1] ⟶ X`
stationary on `boundary n` (in the sense of the existing `SSet.HomotopyRel`)
and lying over the constant base simplex: `H ≫ p = fst ≫ (Δ[n] → S)`.

`FiberwiseHomotopic` is the existence proposition.  `IsMinimal` says that
fiberwise homotopic simplices over the same base with the same boundary are equal;
`IsMinimalFibration` adds the `Fibration` requirement.  No equivalence-relation
structure, minimal subfibration construction, Zorn argument, factorization, or
isomorphism theorem is proved here, to keep the module independent of
`KanComplex.W`, SSet weak equivalences, `TopCat`, realization, and the final
model-category instance.

## Nonclaims

* Does not prove `FiberwiseHomotopic` is an equivalence relation.
* Does not construct a minimal subfibration or prove factorization.
* Does not prove a trivial-fibration or isomorphism theorem.
-/

open CategoryTheory Simplicial SSet HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen

namespace SSet
namespace MinimalFibration

universe u

variable {X S : SSet.{u}}

/-- Fiberwise homotopy between `n`-simplices `x y : X _⦋n⦌` over `p : X ⟶ S`,
relative to `boundary n`.

* `x` and `y` are represented by `yonedaEquiv.symm` as maps `Δ[n] ⟶ X`.
* `homotopyRel` is a homotopy `H : HomotopyRel f g (boundary n)` stationary on
  `∂Δ[n]` in the sense of `SSet.HomotopyRel`.
* `over` requires `H` to lie over the constant base simplex: `H.h ≫ p` is the
  projection to `Δ[n]` followed by the base map `f ≫ p`.
  Consequently `f ≫ p = g ≫ p`. -/
structure FiberwiseHomotopy {n : ℕ} (p : X ⟶ S) (x y : X _⦋n⦌) where
  homotopyRel : HomotopyRel (yonedaEquiv.symm x) (yonedaEquiv.symm y) (boundary n)
  over : homotopyRel.h ≫ p = fst _ _ ≫ (yonedaEquiv.symm x ≫ p)

namespace FiberwiseHomotopy

variable {p : X ⟶ S} {n : ℕ} {x y : X _⦋n⦌}

/-- Underlying map `Δ[n] ⊗ Δ[1] ⟶ X`. -/
abbrev h (H : FiberwiseHomotopy (n := n) p x y) : Δ[n] ⊗ Δ[1] ⟶ X :=
  H.homotopyRel.h

@[reassoc (attr := simp)]
lemma h₀ (H : FiberwiseHomotopy (n := n) p x y) :
    SSet.ι₀ ≫ H.h = yonedaEquiv.symm x :=
  H.homotopyRel.h₀

@[reassoc (attr := simp)]
lemma h₁ (H : FiberwiseHomotopy (n := n) p x y) :
    SSet.ι₁ ≫ H.h = yonedaEquiv.symm y :=
  H.homotopyRel.h₁

lemma stationary (H : FiberwiseHomotopy (n := n) p x y) {m : SimplexCategoryᵒᵖ}
    (a : (Δ[n] : SSet.{u}).obj m) (ha : a ∈ (boundary n).obj m)
    (t : (Δ[1] : SSet.{u}).obj m) :
    H.h.app m ⟨a, t⟩ = (yonedaEquiv.symm x).app m a :=
  H.homotopyRel.stationary a ha t

/-- The two `n`-simplices have the same image in the base `S`. -/
lemma base_eq (H : FiberwiseHomotopy (n := n) p x y) :
    yonedaEquiv.symm x ≫ p = yonedaEquiv.symm y ≫ p := by
  have hy : yonedaEquiv.symm y ≫ p = yonedaEquiv.symm x ≫ p := by
    calc yonedaEquiv.symm y ≫ p
        = (SSet.ι₁ ≫ H.h) ≫ p := by
          rw [H.h₁]
      _ = SSet.ι₁ ≫ (H.h ≫ p) := by
          simp only [Category.assoc]
      _ = SSet.ι₁ ≫ (fst _ _ ≫ (yonedaEquiv.symm x ≫ p)) := by
          rw [H.over]
      _ = yonedaEquiv.symm x ≫ p := by
          simp
  exact hy.symm

lemma base_app_eq (H : FiberwiseHomotopy (n := n) p x y) :
    p.app _ x = p.app _ y := by
  have h := H.base_eq
  rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp] at h
  exact yonedaEquiv.symm.injective h

end FiberwiseHomotopy

/-- Proposition that two `n`-simplices over `p : X ⟶ S` are fiberwise homotopic
relative to `boundary n` over the constant base. -/
def FiberwiseHomotopic {n : ℕ} (p : X ⟶ S) (x y : X _⦋n⦌) : Prop :=
  Nonempty (FiberwiseHomotopy (n := n) p x y)

/-- A map `p : X ⟶ S` is minimal when simplices with the same base image,
same boundary, and fiberwise homotopic relative to the boundary over the
constant base are equal.  This is Goerss–Jardine I.10 Definition 10.2 and the
criterion around Proposition 10.4; cf. Hovey §3.5.  Intended for `Fibration p`. -/
def IsMinimal (p : X ⟶ S) : Prop :=
  ∀ {n : ℕ} (x y : X _⦋n⦌),
    p.app _ x = p.app _ y →
    (boundary n).ι ≫ yonedaEquiv.symm x =
      (boundary n).ι ≫ yonedaEquiv.symm y →
    FiberwiseHomotopic p x y → x = y

/-- A fibration `p : X ⟶ S` is a minimal fibration when it is a Kan fibration
(`Fibration p`) and `IsMinimal p` holds. -/
def IsMinimalFibration (p : X ⟶ S) : Prop :=
  Fibration p ∧ IsMinimal p

lemma isMinimalFibration_iff {p : X ⟶ S} :
    IsMinimalFibration p ↔ Fibration p ∧ IsMinimal p :=
  Iff.rfl

end MinimalFibration
end SSet
