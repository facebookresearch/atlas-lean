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

public import MathlibExt.Analysis.CStarAlgebra.Category.Basic
public import MathlibExt.Analysis.CStarAlgebra.C0DirectSum

/-!
# Actual heterogeneous C-star c0 sums in the C-star category

The carrier is the closed subalgebra of the bounded dependent product whose
norm levels have finite support. The category object, coordinate inclusions,
projections and family maps retain the existing carrier and formulas.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open CategoryTheory

namespace NonUnitalCStarAlgCat

universe u

/-- **Carrier of a heterogeneous c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its `c₀` sum consists of sections `aᵢ ∈ Aᵢ` for which `{i : ‖aᵢ‖ ≥ ε}` is finite for
every `ε > 0`, equipped with the supremum norm and coordinatewise operations. This is that closed
nonunital star-subalgebra carrier. -/
abbrev c0SumCarrier {I : Type u} (A : I → NonUnitalCStarAlgCat.{u}) :=
  CStarC0Sum (fun i => A i)

/-- **Categorical c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex C*-algebras, its `c₀`
sum consists of sections `aᵢ ∈ Aᵢ` for which `{i : ‖aᵢ‖ ≥ ε}` is finite for every `ε > 0`, equipped
with the supremum norm and coordinatewise operations. The sum is a nonunital complex C*-algebra and
hence an object of the nonunital C*-algebra category. An empty index set gives the zero algebra. -/
def c0SumObj {I : Type u} (A : I → NonUnitalCStarAlgCat.{u}) :
    NonUnitalCStarAlgCat.{u} :=
  NonUnitalCStarAlgCat.of (c0SumCarrier A)

/-- **Coordinate inclusion into a c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its `c₀` sum consists of sections `aᵢ ∈ Aᵢ` for which `{i : ‖aᵢ‖ ≥ ε}` is finite for
every `ε > 0`, equipped with the supremum norm and coordinatewise operations. For `i ∈ I`, the star
homomorphism `Aᵢ → ⨁₀ Aᵢ` puts its input at coordinate `i` and zero at every other coordinate. -/
def c0SumInclusion {I : Type u} (A : I → NonUnitalCStarAlgCat.{u}) (i : I) :
    A i ⟶ c0SumObj A := by
  classical
  exact CStarC0Sum.single (fun j => A j) i

/-- **Coordinate projection from a c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its `c₀` sum consists of sections `aᵢ ∈ Aᵢ` for which `{i : ‖aᵢ‖ ≥ ε}` is finite for
every `ε > 0`, equipped with the supremum norm and coordinatewise operations. For `i ∈ I`,
coordinate evaluation is a nonunital star homomorphism `⨁₀ Aᵢ → Aᵢ`. -/
def c0SumProjection {I : Type u} (A : I → NonUnitalCStarAlgCat.{u}) (i : I) :
    c0SumObj A ⟶ A i :=
  CStarC0Sum.eval (fun j => A j) i

/-- **Coordinatewise map on c₀ sums.** For families `(Aᵢ)ᵢ∈I` and `(Bᵢ)ᵢ∈I` of nonunital complex
C*-algebras and nonunital star homomorphisms `fᵢ : Aᵢ → Bᵢ`, both c₀ sums have the supremum norm.
The family defines a nonunital star homomorphism between their c₀ sums, sending `(aᵢ)` to
`(fᵢ(aᵢ))`. -/
def c0SumMap {I : Type u} {A B : I → NonUnitalCStarAlgCat.{u}}
    (f : ∀ i, A i ⟶ B i) : c0SumObj A ⟶ c0SumObj B :=
  CStarC0Sum.map (fun i => A i) (fun i => B i) f

/-- **Coordinates of a c₀ inclusion.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its `c₀` sum consists of sections `aᵢ ∈ Aᵢ` for which `{i : ‖aᵢ‖ ≥ ε}` is finite for
every `ε > 0`, equipped with the supremum norm and coordinatewise operations. The `j` coordinate of
the inclusion of `a ∈ Aᵢ` is the dependent single-coordinate section: `a` at `i`, zero elsewhere. -/
theorem c0SumInclusion_apply {I : Type u} (A : I → NonUnitalCStarAlgCat.{u})
    (i : I) (a : A i) (j : I) :
    c0SumProjection A j (c0SumInclusion A i a) = (by
      classical
      let x : ∀ k, A k := Pi.single i a
      exact x j) := by
  classical
  rfl

/-- **Projection retracts a c₀ inclusion.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its `c₀` sum consists of sections `aᵢ ∈ Aᵢ` for which `{i : ‖aᵢ‖ ≥ ε}` is finite for
every `ε > 0`, equipped with the supremum norm and coordinatewise operations. Projecting the
inclusion of `a ∈ Aᵢ` onto coordinate `i` returns `a`. -/
@[simp]
theorem c0SumInclusion_apply_self {I : Type u}
    (A : I → NonUnitalCStarAlgCat.{u}) (i : I) (a : A i) :
    c0SumProjection A i (c0SumInclusion A i a) = a := by
  classical
  exact CStarC0Sum.single_apply_self (fun j => A j) i a

/-- **Other coordinates of a c₀ inclusion.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its `c₀` sum consists of sections `aᵢ ∈ Aᵢ` for which `{i : ‖aᵢ‖ ≥ ε}` is finite for
every `ε > 0`, equipped with the supremum norm and coordinatewise operations. For `j ≠ i`,
projecting the inclusion of `a ∈ Aᵢ` onto coordinate `j` gives zero. -/
@[simp]
theorem c0SumInclusion_apply_ne {I : Type u}
    (A : I → NonUnitalCStarAlgCat.{u}) (i : I) (a : A i)
    {j : I} (hji : j ≠ i) : c0SumProjection A j (c0SumInclusion A i a) = 0 := by
  classical
  exact CStarC0Sum.single_apply_ne (fun k => A k) i a hji

/-- **Evaluation of a c₀ projection.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its `c₀` sum consists of sections `aᵢ ∈ Aᵢ` for which `{i : ‖aᵢ‖ ≥ ε}` is finite for
every `ε > 0`, equipped with the supremum norm and coordinatewise operations. For a section `a` in
the c₀ sum, its projection to `Aᵢ` is `aᵢ`. -/
@[simp]
theorem c0SumProjection_apply {I : Type u}
    (A : I → NonUnitalCStarAlgCat.{u}) (i : I) (a : c0SumCarrier A) :
    c0SumProjection A i a = a i := rfl

/-- **Coordinates of a c₀ sum map.** For families `(Aᵢ)ᵢ∈I` and `(Bᵢ)ᵢ∈I` of nonunital complex
C*-algebras and nonunital star homomorphisms `fᵢ : Aᵢ → Bᵢ`, both c₀ sums have the supremum norm.
The `i` coordinate of the image of a section `a` is `fᵢ(aᵢ)`. -/
@[simp]
theorem c0SumMap_apply {I : Type u} {A B : I → NonUnitalCStarAlgCat.{u}}
    (f : ∀ i, A i ⟶ B i) (a : c0SumObj A) (i : I) :
    c0SumProjection B i (c0SumMap f a) = f i (c0SumProjection A i a) := rfl

/-- **Categorical retraction of a c₀ inclusion.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its `c₀` sum consists of sections `aᵢ ∈ Aᵢ` for which `{i : ‖aᵢ‖ ≥ ε}` is finite for
every `ε > 0`, equipped with the supremum norm and coordinatewise operations. The inclusion `Aᵢ → ⨁₀
Aᵢ` followed by projection to `Aᵢ` is the identity morphism. -/
@[simp]
theorem c0SumInclusion_projection {I : Type u}
    (A : I → NonUnitalCStarAlgCat.{u}) (i : I) :
    c0SumInclusion A i ≫ c0SumProjection A i = 𝟙 (A i) := by
  ext a
  exact c0SumInclusion_apply_self A i a

/-- **Isometric c₀ coordinate inclusion.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its `c₀` sum consists of sections `aᵢ ∈ Aᵢ` for which `{i : ‖aᵢ‖ ≥ ε}` is finite for
every `ε > 0`, equipped with the supremum norm and coordinatewise operations. For `a ∈ Aᵢ`, the norm
of its inclusion into the c₀ sum is `‖a‖`. -/
@[simp]
theorem norm_c0SumInclusion {I : Type u}
    (A : I → NonUnitalCStarAlgCat.{u}) (i : I) (a : A i) :
    ‖c0SumInclusion A i a‖ = ‖a‖ := by
  classical
  exact CStarC0Sum.norm_single (fun j => A j) i a

end NonUnitalCStarAlgCat
