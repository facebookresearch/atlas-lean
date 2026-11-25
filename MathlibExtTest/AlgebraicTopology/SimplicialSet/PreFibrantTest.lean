/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.PreFibrant

/-!
# Tests for pre-fibrant simplicial sets

Consumer checks for the public declarations of
`MathlibExt/AlgebraicTopology/SimplicialSet/PreFibrant.lean`:
constant simplices and Stevenson's `s₀ⁿ(v)` recursion, the `0`-th
face of a horn map (`d₀f`), the predicate `SSet.IsPreFibrant`
(Stevenson Definition 3.1) and its two filling properties, the
examples (quasicategories, Kan complexes, nerves, standard
simplices, joins of standard simplices, full subcomplexes), closure
under isomorphism and under inner fibrations (Remark 3.4), and the
inner-anodyne replacement into a quasicategory (hence into a
pre-fibrant simplicial set).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.PreFibrantTest

variable {S T X : SSet.{u}}

/-! ### Constant simplices -/

example (n : ℕ) (v : S _⦋0⦌) : S _⦋n⦌ := SSet.constSimplex S n v

/-- `s₀⁰(v) = v`. -/
example (v : S _⦋0⦌) : SSet.constSimplex S 0 v = v :=
  SSet.constSimplex_zero v

/-- `s₀ⁿ⁺¹(v) = s₀(s₀ⁿ(v))`. -/
example (n : ℕ) (v : S _⦋0⦌) :
    SSet.constSimplex S (n + 1) v =
      S.σ (0 : Fin (n + 1)) (SSet.constSimplex S n v) :=
  SSet.constSimplex_succ n v

/-- The constant map at `v` classifies the constant simplex at `v`. -/
example (n : ℕ) (v : S _⦋0⦌) :
    SSet.yonedaEquiv (SSet.const v : Δ[n] ⟶ S) = SSet.constSimplex S n v :=
  SSet.yonedaEquiv_const_eq n v

example (n : ℕ) (v : S _⦋0⦌) :
    SSet.IsConstantSimplex (SSet.constSimplex S n v) :=
  SSet.isConstantSimplex_constSimplex n v

/-- Constancy is preserved by simplicial maps. -/
example {n : ℕ} {x : S _⦋n⦌} (hx : SSet.IsConstantSimplex x) (p : S ⟶ T) :
    SSet.IsConstantSimplex (p.app _ x) :=
  hx.map p

/-- A standard simplex maps constantly if and only if its classified
simplex is constant. -/
example {n : ℕ} (f : Δ[n] ⟶ S) :
    SSet.IsConstantSimplex (SSet.yonedaEquiv f) ↔
      ∃ v : S _⦋0⦌, f = SSet.const v :=
  SSet.isConstantSimplex_yonedaEquiv_iff f

/-! ### The `0`-th face of a horn map -/

example {n : ℕ} {i : Fin (n + 3)} (f : (Λ[n + 2, i] : SSet.{u}) ⟶ S)
    (h : (0 : Fin (n + 3)) ≠ i) : S _⦋n + 1⦌ :=
  SSet.hornFaceZero f h

example {n : ℕ} {i : Fin (n + 3)} (f : (Λ[n + 2, i] : SSet.{u}) ⟶ S)
    (h : (0 : Fin (n + 3)) ≠ i) (p : S ⟶ T) :
    SSet.hornFaceZero (f ≫ p) h = p.app _ (SSet.hornFaceZero f h) :=
  SSet.hornFaceZero_comp f h p

/-- `d₀f` is the simplex classified by restricting along the face
inclusion opposite vertex `0`. -/
example {n : ℕ} {i : Fin (n + 3)} (f : (Λ[n + 2, i] : SSet.{u}) ⟶ S)
    (h : (0 : Fin (n + 3)) ≠ i) :
    SSet.hornFaceZero f h = SSet.yonedaEquiv (SSet.horn.ι i 0 h ≫ f) :=
  SSet.hornFaceZero_eq_yonedaEquiv f h

/-! ### The pre-fibrant filling properties -/

section Filling

variable [SSet.IsPreFibrant S]

/-- Definition 3.1(i): every `Λ[2, 1]`-horn fills. -/
example (σ₀ : (Λ[2, (1 : Fin 3)] : SSet.{u}) ⟶ S) :
    ∃ σ : Δ[2] ⟶ S, σ₀ = Λ[2, (1 : Fin 3)].ι ≫ σ :=
  SSet.IsPreFibrant.hornFillingTwo σ₀

/-- Definition 3.1(ii): every inner horn with constant `0`-th face
fills. -/
example {n : ℕ} {i : Fin (n + 3)} (σ₀ : (Λ[n + 2, i] : SSet.{u}) ⟶ S)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2))
    (hconst : SSet.IsConstantSimplex (SSet.hornFaceZero σ₀ (ne_of_lt h0))) :
    ∃ σ : Δ[n + 2] ⟶ S, σ₀ = Λ[n + 2, i].ι ≫ σ :=
  SSet.IsPreFibrant.hornFillingConst σ₀ h0 hn hconst

/-- The constant-face hypothesis holds for horns factoring through
a constant map: the `0`-th face of `Λ.ι ≫ const v` is the constant
simplex at `v`. -/
example {n : ℕ} {i : Fin (n + 3)} (h : (0 : Fin (n + 3)) ≠ i)
    (v : S _⦋0⦌) :
    SSet.IsConstantSimplex
      (SSet.hornFaceZero (Λ[n + 2, i].ι ≫ SSet.const v) h) := by
  rw [SSet.hornFaceZero_comp]
  exact SSet.isConstantSimplex_constSimplex _ v

end Filling

/-! ### Examples -/

/-- Stevenson, Example 3.2: every quasicategory is pre-fibrant. -/
example [SSet.Quasicategory S] : SSet.IsPreFibrant S := inferInstance

/-- Every Kan complex is pre-fibrant (through quasicategories). -/
example [SSet.KanComplex S] : SSet.IsPreFibrant S := inferInstance

/-- The nerve of a category is pre-fibrant. -/
example {C : Type u} [Category.{u} C] :
    SSet.IsPreFibrant (CategoryTheory.nerve C) := inferInstance

example : SSet.IsPreFibrant (CategoryTheory.nerve (Fin 2)) := inferInstance

/-- Standard simplices are quasicategories, hence pre-fibrant. -/
example (n : ℕ) : SSet.Quasicategory (Δ[n] : SSet.{u}) := inferInstance

example (n : ℕ) : SSet.IsPreFibrant (Δ[n] : SSet.{u}) := inferInstance

example : SSet.IsPreFibrant (Δ[0] : SSet.{u}) := inferInstance

example : SSet.IsPreFibrant (Δ[2] : SSet.{u}) := inferInstance

/-- Joins of standard simplices are pre-fibrant. -/
example (m n : ℕ) : SSet.IsPreFibrant ((Δ[m] : SSet.{u}) ⋆ Δ[n]) :=
  inferInstance

example : SSet.IsPreFibrant ((Δ[1] : SSet.{u}) ⋆ Δ[2]) := inferInstance

/-! ### Closure properties -/

/-- Pre-fibrancy transfers along isomorphisms. -/
example {A B : SSet.{u}} (e : A ≅ B) [SSet.IsPreFibrant B] :
    SSet.IsPreFibrant A :=
  SSet.isPreFibrant_of_iso e

/-- Explicitly: `Δ[n]` is pre-fibrant because it is isomorphic to a
nerve. -/
example (n : ℕ) : SSet.IsPreFibrant (Δ[n] : SSet.{u}) :=
  SSet.isPreFibrant_of_iso (SSet.stdSimplex.isoNerve n)

/-- Stevenson, Remark 3.4: the domain of an inner fibration into a
pre-fibrant simplicial set is pre-fibrant. -/
example (p : X ⟶ S) [SSet.InnerFibration p] [SSet.IsPreFibrant S] :
    SSet.IsPreFibrant X :=
  SSet.isPreFibrant_of_innerFibration p

/-- Full subcomplexes of pre-fibrant simplicial sets are
pre-fibrant (Remark 3.4, second part). -/
example (V : Set (X _⦋0⦌)) [SSet.IsPreFibrant X] :
    SSet.IsPreFibrant (SSet.Subcomplex.full V : SSet.{u}) :=
  inferInstance

example (V : Set ((Δ[3] : SSet.{u}) _⦋0⦌)) :
    SSet.IsPreFibrant (SSet.Subcomplex.full V : SSet.{u}) :=
  inferInstance

/-! ### Replacement -/

example : SSet.{u} := SSet.preFibrantReplacement X

example : X ⟶ SSet.preFibrantReplacement X :=
  SSet.toPreFibrantReplacement X

/-- The replacement map is inner anodyne. -/
example : SSet.innerAnodyneExtensions (SSet.toPreFibrantReplacement X) :=
  SSet.innerAnodyneExtensions_toPreFibrantReplacement X

/-- The replacement is a quasicategory, hence pre-fibrant. -/
example : SSet.Quasicategory (SSet.preFibrantReplacement X) := inferInstance

example : SSet.IsPreFibrant (SSet.preFibrantReplacement X) := inferInstance

/-- The factorization data: inner anodyne followed by inner
fibration, composing to the terminal map. -/
example : SSet.innerHornInclusions.rlp.llp
    (SSet.preFibrantReplacementData X).i :=
  (SSet.preFibrantReplacementData X).hi

example : SSet.InnerFibration (SSet.preFibrantReplacementData X).p :=
  inferInstance

example : (SSet.preFibrantReplacementData X).i ≫
    (SSet.preFibrantReplacementData X).p = terminal.from X :=
  (SSet.preFibrantReplacementData X).fac

/-- Existence form: an inner anodyne map to a pre-fibrant target. -/
example : ∃ (T : SSet.{u}) (f : X ⟶ T),
    SSet.innerAnodyneExtensions f ∧ SSet.IsPreFibrant T :=
  SSet.exists_innerAnodyneExtensions_and_isPreFibrant X

/-- Existence form: an inner anodyne map to a quasicategory (the
target actually constructed). -/
example : ∃ (T : SSet.{u}) (f : X ⟶ T),
    SSet.innerAnodyneExtensions f ∧ SSet.Quasicategory T :=
  SSet.exists_innerAnodyneExtensions_and_quasicategory X

/-- The replacement can be used as a pre-fibrant horn filler. -/
example (σ₀ : (Λ[2, (1 : Fin 3)] : SSet.{u}) ⟶
    SSet.preFibrantReplacement X) :
    ∃ σ : Δ[2] ⟶ SSet.preFibrantReplacement X,
      σ₀ = Λ[2, (1 : Fin 3)].ι ≫ σ :=
  SSet.IsPreFibrant.hornFillingTwo σ₀

/-- Inner horn inclusions themselves are inner anodyne, as a
consistency check on the replacement class. -/
example {n : ℕ} {i : Fin (n + 1)} (h0 : 0 < i) (hn : i < Fin.last n) :
    SSet.innerAnodyneExtensions Λ[n, i].ι :=
  SSet.innerAnodyneExtensions.horn_ι h0 hn

end MathlibExtTest.AlgebraicTopology.SimplicialSet.PreFibrantTest

end
