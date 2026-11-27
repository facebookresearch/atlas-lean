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
# Minimal fibrations and relative fiberwise simplex homotopy

For p:X→S and n-simplices x,y of X, a fiberwise homotopy is a map H:Δ[n]×Δ[1]→X with endpoints x
and y, stationary on ∂Δ[n]×Δ[1], and with H≫p=pr₁≫p(x). Thus the base n-simplex is fixed in the
interval direction and the endpoint base images and boundary restrictions agree.

The corresponding existence relation defines minimality: simplices with the same base and
boundary that are fiberwise homotopic must be equal. A minimal fibration is a map with this
property and Kan horn lifting. All simplicial sets may lie in any universe u.

References: Goerss–Jardine, Simplicial Homotopy Theory, Chapter I, Section 10, Definition 10.2 and Proposition 10.4; Hovey, Model Categories, Section 3.5.
-/

open CategoryTheory Simplicial SSet HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen

namespace SSet
namespace MinimalFibration

universe u

variable {X S : SSet.{u}}

/-- Let p:X→S be a map of simplicial sets, and x,y n-simplices of X. Represent them by maps
x̄,ȳ:Δ[n]→X. A fiberwise homotopy H has cylinder Δ[n]×Δ[1]→X, stationary on ∂Δ[n], and
satisfies H≫p=pr₁≫(x̄≫p). Its endpoint restrictions are x̄ at vertex zero and ȳ at vertex one.
The projection to S is independent of the interval parameter. -/
structure FiberwiseHomotopy {n : ℕ} (p : X ⟶ S) (x y : X _⦋n⦌) where
  /-- Let p:X→S be a map of simplicial sets, and x,y n-simplices of X. Represent them by maps
x̄,ȳ:Δ[n]→X. This component is the homotopy between x̄ and ȳ stationary on the whole
boundary cylinder ∂Δ[n]×Δ[1]. -/
  homotopyRel : HomotopyRel (yonedaEquiv.symm x) (yonedaEquiv.symm y) (boundary n)
  /-- Let p:X→S be a map of simplicial sets, and x,y n-simplices of X. Represent them by maps
x̄,ȳ:Δ[n]→X. A fiberwise homotopy H has cylinder Δ[n]×Δ[1]→X, stationary on ∂Δ[n], and
satisfies H≫p=pr₁≫(x̄≫p). The over-base equation identifies the cylinder projection with the
fixed base n-simplex p(x), throughout the interval. -/
  over : homotopyRel.h ≫ p = fst _ _ ≫ (yonedaEquiv.symm x ≫ p)

namespace FiberwiseHomotopy

variable {p : X ⟶ S} {n : ℕ} {x y : X _⦋n⦌}

/-- Let p:X→S be a map of simplicial sets, and x,y n-simplices of X. Represent them by maps
x̄,ȳ:Δ[n]→X. A fiberwise homotopy H has cylinder Δ[n]×Δ[1]→X, stationary on ∂Δ[n], and
satisfies H≫p=pr₁≫(x̄≫p). Forgetting the relative and over-base conditions gives its underlying
cylinder map Δ[n]×Δ[1]→X. -/
abbrev h (H : FiberwiseHomotopy (n := n) p x y) : Δ[n] ⊗ Δ[1] ⟶ X :=
  H.homotopyRel.h

/-- Let p:X→S be a map of simplicial sets, and x,y n-simplices of X. Represent them by maps
x̄,ȳ:Δ[n]→X. A fiberwise homotopy H has cylinder Δ[n]×Δ[1]→X, stationary on ∂Δ[n], and
satisfies H≫p=pr₁≫(x̄≫p). Restriction along the endpoint-zero inclusion Δ[n]→Δ[n]×Δ[1] is x̄. -/
@[reassoc (attr := simp)]
lemma h₀ (H : FiberwiseHomotopy (n := n) p x y) :
    SSet.ι₀ ≫ H.h = yonedaEquiv.symm x :=
  H.homotopyRel.h₀

/-- Let p:X→S be a map of simplicial sets, and x,y n-simplices of X. Represent them by maps
x̄,ȳ:Δ[n]→X. A fiberwise homotopy H has cylinder Δ[n]×Δ[1]→X, stationary on ∂Δ[n], and
satisfies H≫p=pr₁≫(x̄≫p). Restriction along the endpoint-one inclusion Δ[n]→Δ[n]×Δ[1] is ȳ. -/
@[reassoc (attr := simp)]
lemma h₁ (H : FiberwiseHomotopy (n := n) p x y) :
    SSet.ι₁ ≫ H.h = yonedaEquiv.symm y :=
  H.homotopyRel.h₁

/-- Let p:X→S be a map of simplicial sets, and x,y n-simplices of X. Represent them by maps
x̄,ȳ:Δ[n]→X. A fiberwise homotopy H has cylinder Δ[n]×Δ[1]→X, stationary on ∂Δ[n], and
satisfies H≫p=pr₁≫(x̄≫p). In every simplicial degree m, for a boundary simplex a and interval
simplex t, H(a,t)=x̄(a). -/
lemma stationary (H : FiberwiseHomotopy (n := n) p x y) {m : SimplexCategoryᵒᵖ}
    (a : (Δ[n] : SSet.{u}).obj m) (ha : a ∈ (boundary n).obj m)
    (t : (Δ[1] : SSet.{u}).obj m) :
    H.h.app m ⟨a, t⟩ = (yonedaEquiv.symm x).app m a :=
  H.homotopyRel.stationary a ha t

/-- Let p:X→S be a map of simplicial sets, and x,y n-simplices of X. Represent them by maps
x̄,ȳ:Δ[n]→X. A fiberwise homotopy H has cylinder Δ[n]×Δ[1]→X, stationary on ∂Δ[n], and
satisfies H≫p=pr₁≫(x̄≫p). Its endpoint maps have the same projection: x̄≫p=ȳ≫p as maps Δ[n]→S. -/
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

/-- Let p:X→S be a map of simplicial sets, and x,y n-simplices of X. Represent them by maps
x̄,ȳ:Δ[n]→X. A fiberwise homotopy H has cylinder Δ[n]×Δ[1]→X, stationary on ∂Δ[n], and
satisfies H≫p=pr₁≫(x̄≫p). The base n-simplex values satisfy pₙ(x)=pₙ(y). -/
lemma base_app_eq (H : FiberwiseHomotopy (n := n) p x y) :
    p.app _ x = p.app _ y := by
  have h := H.base_eq
  rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp] at h
  exact yonedaEquiv.symm.injective h

end FiberwiseHomotopy

/-- Let p:X→S be a map of simplicial sets, and x,y n-simplices of X. Represent them by maps
x̄,ȳ:Δ[n]→X. The relation asserts the existence of a homotopy of x̄,ȳ stationary on ∂Δ[n] and
projecting to p(x) independently of the interval parameter. -/
def FiberwiseHomotopic {n : ℕ} (p : X ⟶ S) (x y : X _⦋n⦌) : Prop :=
  Nonempty (FiberwiseHomotopy (n := n) p x y)

/-- A simplicial map p:X→S is minimal when, in every degree n, simplices x,y with the same base
image and boundary restriction are equal whenever they admit a fiberwise homotopy relative to
∂Δ[n]. -/
def IsMinimal (p : X ⟶ S) : Prop :=
  ∀ {n : ℕ} (x y : X _⦋n⦌),
    p.app _ x = p.app _ y →
    (boundary n).ι ≫ yonedaEquiv.symm x =
      (boundary n).ι ≫ yonedaEquiv.symm y →
    FiberwiseHomotopic p x y → x = y

/-- A map p:X→S of simplicial sets is a minimal fibration when it has the Kan horn-lifting property
and is minimal: fiberwise homotopic simplices with the same base and boundary are equal. -/
def IsMinimalFibration (p : X ⟶ S) : Prop :=
  Fibration p ∧ IsMinimal p

/-- For a simplicial map p:X→S, being a minimal fibration is equivalent to being a Kan fibration and
satisfying the simplex-level minimality predicate. -/
lemma isMinimalFibration_iff {p : X ⟶ S} :
    IsMinimalFibration p ↔ Fibration p ∧ IsMinimal p :=
  Iff.rfl

end MinimalFibration
end SSet
