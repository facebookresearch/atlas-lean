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

public import MathlibExt.Analysis.CStarAlgebra.Grading
public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.ZeroAtInftyFlip
public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.ZeroAtInftyOpen

import Mathlib.Tactic.FinCases

/-!
# Coefficientwise gradings of zero-at-infinity functions

The grading is computed on Mathlib's existing `C₀(X, A)` carrier by
postcomposing with the coefficient grading generator. Its norm, completeness,
star and scalar actions remain the stock structures. The domain is an arbitrary
topological space: no local compactness, separation or nonemptiness is needed.

Evaluation, coefficient postcomposition and cocompact precomposition retain
their existing nonunital star-algebra homomorphisms. No ambient grading instance
or source-specific cone carrier is introduced.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped CStarAlgebra ZeroAtInfty

namespace CStarGrading

universe uX uY uZ uA uB uC

section Grading

variable (X : Type uX) [TopologicalSpace X]
variable {A : Type uA} [NonUnitalCStarAlgebra A] (γ : CStarGrading A)

/-- **Coefficientwise grading of functions vanishing at infinity.** Let `X` be any topological space and
`A` a nonunital complex C*-algebra with grading `γ` and generator `σ`. The C*-algebra `C₀(X,A)`
consists of continuous functions vanishing along the cocompact filter, with supremum norm. Applying
`γ(n)` to every function value defines a `ℤ/2ℤ` grading on `C₀(X,A)`. -/
def zeroAtInfty : CStarGrading C₀(X, A) :=
  ofInvolution
    (ZeroAtInftyContinuousMap.postcompStarAlgEquiv X γ.generatorAut)
    (by
      intro f
      apply ZeroAtInftyContinuousMap.ext
      intro x
      change γ.generatorAut (γ.generatorAut (f x)) = f x
      exact γ.generator_involutive (f x))

/-- **Generator on the vanishing-function algebra.** Let `X` be any topological space and `A` a
nonunital complex C*-algebra with grading `γ` and generator `σ`. The C*-algebra `C₀(X,A)` consists
of continuous functions vanishing along the cocompact filter, with supremum norm. The degree-one
automorphism is postcomposition `f ↦ σ ∘ f`. -/
@[simp]
theorem zeroAtInfty_generatorAut :
    (zeroAtInfty X γ).generatorAut =
      ZeroAtInftyContinuousMap.postcompStarAlgEquiv X γ.generatorAut :=
  ofInvolution_generatorAut _ _

/-- **Values of the vanishing-function grading generator.** Let `X` be any topological space and `A` a
nonunital complex C*-algebra with grading `γ` and generator `σ`. The C*-algebra `C₀(X,A)` consists
of continuous functions vanishing along the cocompact filter, with supremum norm. For `f ∈ C₀(X,A)`
and `x ∈ X`, the grading generator has value `σ(f(x))`. -/
@[simp]
theorem zeroAtInfty_generator_apply (f : C₀(X, A)) (x : X) :
    (zeroAtInfty X γ).generatorAut f x = γ.generatorAut (f x) := by
  rw [zeroAtInfty_generatorAut]
  rfl

/-- **Degree action on vanishing-function values.** Let `X` be any topological space and `A` a nonunital
complex C*-algebra with grading `γ` and generator `σ`. The C*-algebra `C₀(X,A)` consists of
continuous functions vanishing along the cocompact filter, with supremum norm. For every degree `n`,
function `f`, and point `x`, the induced action has value `γ(n)(f(x))`. -/
theorem zeroAtInfty_aut_apply (n : ZMod 2) (f : C₀(X, A)) (x : X) :
    PointNormCStarAddAction.aut (zeroAtInfty X γ) n f x =
      PointNormCStarAddAction.aut γ n (f x) := by
  fin_cases n
  · change (zeroAtInfty X γ) (0 : ZMod 2) f x = γ (0 : ZMod 2) (f x)
    simp only [PointNormCStarAddAction.apply_zero]
  · change (zeroAtInfty X γ).generatorAut f x = γ.generatorAut (f x)
    exact zeroAtInfty_generator_apply X γ f x

/-- **Homogeneous vanishing functions.** Let `X` be any topological space and `A` a nonunital complex
C*-algebra with grading `γ` and generator `σ`. The C*-algebra `C₀(X,A)` consists of continuous
functions vanishing along the cocompact filter, with supremum norm. A function in `C₀(X,A)` has
degree `n` exactly when its value at every point belongs to the degree-`n` part of `A`. -/
theorem mem_zeroAtInfty_part_iff (n : ZMod 2) (f : C₀(X, A)) :
    f ∈ (zeroAtInfty X γ).part n ↔ ∀ x, f x ∈ γ.part n := by
  rw [(zeroAtInfty X γ).mem_part_iff_generator]
  constructor
  · intro h x
    apply (γ.mem_part_iff_generator n (f x)).2
    have hx := congrArg (fun g : C₀(X, A) => g x) h
    simpa only [zeroAtInfty_generator_apply,
      ZeroAtInftyContinuousMap.smul_apply] using hx
  · intro h
    apply ZeroAtInftyContinuousMap.ext
    intro x
    have hx := (γ.mem_part_iff_generator n (f x)).1 (h x)
    simpa only [zeroAtInfty_generator_apply,
      ZeroAtInftyContinuousMap.smul_apply] using hx

/-- **Even projection of a vanishing function.** Let `X` be any topological space and `A` a nonunital
complex C*-algebra with grading `γ` and generator `σ`. The C*-algebra `C₀(X,A)` consists of
continuous functions vanishing along the cocompact filter, with supremum norm. At each `x ∈ X`, the
even projection of `f` is the even projection of `f(x)` in `A`. -/
@[simp]
theorem zeroAtInfty_evenProjection_apply (f : C₀(X, A)) (x : X) :
    (zeroAtInfty X γ).evenProjection f x = γ.evenProjection (f x) := by
  simp only [evenProjection_apply, ZeroAtInftyContinuousMap.smul_apply,
    ZeroAtInftyContinuousMap.add_apply, zeroAtInfty_generator_apply]

/-- **Odd projection of a vanishing function.** Let `X` be any topological space and `A` a nonunital
complex C*-algebra with grading `γ` and generator `σ`. The C*-algebra `C₀(X,A)` consists of
continuous functions vanishing along the cocompact filter, with supremum norm. At each `x ∈ X`, the
odd projection of `f` is the odd projection of `f(x)` in `A`. -/
@[simp]
theorem zeroAtInfty_oddProjection_apply (f : C₀(X, A)) (x : X) :
    (zeroAtInfty X γ).oddProjection f x = γ.oddProjection (f x) := by
  simp only [oddProjection_apply, ZeroAtInftyContinuousMap.smul_apply,
    ZeroAtInftyContinuousMap.sub_apply, zeroAtInfty_generator_apply]

/-- **Graded evaluation of vanishing functions.** Let `X` be any topological space and `A` a nonunital
complex C*-algebra with grading `γ` and generator `σ`. The C*-algebra `C₀(X,A)` consists of
continuous functions vanishing along the cocompact filter, with supremum norm. Evaluation at a point
`x ∈ X` is an equivariant nonunital star homomorphism `C₀(X,A) → A`. -/
def zeroAtInftyEval (x : X) : Hom (zeroAtInfty X γ) γ where
  toNonUnitalStarAlgHom := ZeroAtInftyContinuousMap.evalAt x
  equivariant' := by
    intro n f
    change PointNormCStarAddAction.aut (zeroAtInfty X γ) n.toAdd f x =
      PointNormCStarAddAction.aut γ n.toAdd (f x)
    exact zeroAtInfty_aut_apply X γ n.toAdd f x

/-- **Value of a graded evaluation map.** Let `X` be any topological space and `A` a nonunital complex
C*-algebra with grading `γ` and generator `σ`. The C*-algebra `C₀(X,A)` consists of continuous
functions vanishing along the cocompact filter, with supremum norm. For `f ∈ C₀(X,A)`, the graded
evaluation at `x` is `f(x)`. -/
@[simp]
theorem zeroAtInftyEval_apply (x : X) (f : C₀(X, A)) :
    zeroAtInftyEval X γ x f = f x := rfl

/-- **Underlying map of graded vanishing-function evaluation.** Let `X` be any topological space and `A`
a nonunital complex C*-algebra with grading `γ` and generator `σ`. The C*-algebra `C₀(X,A)` consists
of continuous functions vanishing along the cocompact filter, with supremum norm. Forgetting
equivariance leaves the point-evaluation nonunital star homomorphism `C₀(X,A) → A`. -/
@[simp]
theorem zeroAtInftyEval_toNonUnitalStarAlgHom (x : X) :
    (zeroAtInftyEval X γ x).toNonUnitalStarAlgHom =
      ZeroAtInftyContinuousMap.evalAt x := rfl

end Grading

section Postcomposition

variable (X : Type uX) [TopologicalSpace X]
variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]
variable {γA : CStarGrading A} {γB : CStarGrading B} {γC : CStarGrading C}

/-- **Graded coefficient postcomposition.** Let `X` be a topological space, let `A,B` be graded
nonunital complex C*-algebras, and let `φ : A → B` be an equivariant nonunital star homomorphism.
Their vanishing-function algebras carry coefficientwise gradings and supremum norms. Postcomposition
`f ↦ φ ∘ f` is an equivariant nonunital star homomorphism `C₀(X,A) → C₀(X,B)`. -/
def zeroAtInftyPostcomp (φ : Hom γA γB) :
    Hom (zeroAtInfty X γA) (zeroAtInfty X γB) where
  toNonUnitalStarAlgHom :=
    ZeroAtInftyContinuousMap.nonUnitalStarAlgHom_postcomp φ.toNonUnitalStarAlgHom
  equivariant' := by
    intro n f
    apply ZeroAtInftyContinuousMap.ext
    intro x
    change φ (PointNormCStarAddAction.aut (zeroAtInfty X γA) n.toAdd f x) =
      PointNormCStarAddAction.aut (zeroAtInfty X γB) n.toAdd
        (ZeroAtInftyContinuousMap.nonUnitalStarAlgHom_postcomp
          φ.toNonUnitalStarAlgHom f) x
    rw [zeroAtInfty_aut_apply, zeroAtInfty_aut_apply]
    exact Hom.equivariant φ n.toAdd (f x)

/-- **Evaluation of graded coefficient postcomposition.** Let `X` be a topological space, let `A,B` be
graded nonunital complex C*-algebras, and let `φ : A → B` be an equivariant nonunital star
homomorphism. Their vanishing-function algebras carry coefficientwise gradings and supremum norms.
At every `x ∈ X`, the postcomposed function has value `φ(f(x))`. -/
@[simp]
theorem zeroAtInftyPostcomp_apply (φ : Hom γA γB) (f : C₀(X, A)) (x : X) :
    zeroAtInftyPostcomp X φ f x = φ (f x) := rfl

/-- **Underlying map of graded coefficient postcomposition.** Let `X` be a topological space, let `A,B`
be graded nonunital complex C*-algebras, and let `φ : A → B` be an equivariant nonunital star
homomorphism. Their vanishing-function algebras carry coefficientwise gradings and supremum norms.
Forgetting equivariance leaves the pointwise nonunital star homomorphism induced by `φ` on vanishing
functions. -/
@[simp]
theorem zeroAtInftyPostcomp_toNonUnitalStarAlgHom (φ : Hom γA γB) :
    (zeroAtInftyPostcomp X φ).toNonUnitalStarAlgHom =
      ZeroAtInftyContinuousMap.nonUnitalStarAlgHom_postcomp
        φ.toNonUnitalStarAlgHom := rfl

/-- **Identity coefficient postcomposition.** Let `X` be any topological space and `A` a nonunital
complex C*-algebra with grading `γ` and generator `σ`. The C*-algebra `C₀(X,A)` consists of
continuous functions vanishing along the cocompact filter, with supremum norm. Postcomposition with
the identity graded star homomorphism of `A` gives the identity graded homomorphism of `C₀(X,A)`. -/
@[simp]
theorem zeroAtInftyPostcomp_id (γ : CStarGrading A) :
    zeroAtInftyPostcomp X (Hom.id γ) = Hom.id (zeroAtInfty X γ) := by
  apply PointNormCStarAction.Hom.ext
  intro f
  apply ZeroAtInftyContinuousMap.ext
  intro x
  rfl

/-- **Composition of graded coefficient postcomposition.** For a topological space `X`, graded nonunital
complex C*-algebras `A,B,C`, and equivariant star homomorphisms `φ : A → B`, `ψ : B → C`,
postcomposition by `ψ ∘ φ` on vanishing functions equals postcomposition by `φ` followed by
postcomposition by `ψ`. -/
theorem zeroAtInftyPostcomp_comp (ψ : Hom γB γC) (φ : Hom γA γB) :
    zeroAtInftyPostcomp X (Hom.comp ψ φ) =
      Hom.comp (zeroAtInftyPostcomp X ψ) (zeroAtInftyPostcomp X φ) := by
  apply PointNormCStarAction.Hom.ext
  intro f
  apply ZeroAtInftyContinuousMap.ext
  intro x
  rfl

/-- **Evaluation commutes with graded postcomposition.** Let `X` be a topological space, let `A,B` be
graded nonunital complex C*-algebras, and let `φ : A → B` be an equivariant nonunital star
homomorphism. Their vanishing-function algebras carry coefficientwise gradings and supremum norms.
Postcomposition by `φ` followed by evaluation at `x` equals evaluation at `x` followed by `φ`. -/
theorem zeroAtInftyEval_postcomp (φ : Hom γA γB) (x : X) :
    Hom.comp (zeroAtInftyEval X γB x) (zeroAtInftyPostcomp X φ) =
      Hom.comp φ (zeroAtInftyEval X γA x) := by
  apply PointNormCStarAction.Hom.ext
  intro f
  rfl

end Postcomposition

section Precomposition

variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (γ : CStarGrading A)

/-- **Graded cocompact precomposition.** Let `X,Y` be topological spaces, `A` a graded nonunital complex
C*-algebra, and `g : X → Y` a continuous cocompact map, meaning that it maps the cocompact filter of
`X` toward that of `Y`. Precomposition `f ↦ f ∘ g` is an equivariant nonunital star homomorphism
`C₀(Y,A) → C₀(X,A)` for the coefficientwise gradings. -/
def zeroAtInftyPrecomp (g : CocompactMap X Y) :
    Hom (zeroAtInfty Y γ) (zeroAtInfty X γ) where
  toNonUnitalStarAlgHom := ZeroAtInftyContinuousMap.compNonUnitalStarAlgHom g
  equivariant' := by
    intro n f
    apply ZeroAtInftyContinuousMap.ext
    intro x
    change PointNormCStarAddAction.aut (zeroAtInfty Y γ) n.toAdd f (g x) =
      PointNormCStarAddAction.aut (zeroAtInfty X γ) n.toAdd
        (ZeroAtInftyContinuousMap.compNonUnitalStarAlgHom g f) x
    rw [zeroAtInfty_aut_apply, zeroAtInfty_aut_apply]
    rfl

/-- **Value of graded cocompact precomposition.** Let `X,Y` be topological spaces, `A` a graded
nonunital complex C*-algebra, and `g : X → Y` a continuous cocompact map, meaning that it maps the
cocompact filter of `X` toward that of `Y`. For `f ∈ C₀(Y,A)` and `x ∈ X`, the precomposed function
has value `f(g(x))`. -/
@[simp]
theorem zeroAtInftyPrecomp_apply (g : CocompactMap X Y) (f : C₀(Y, A)) (x : X) :
    zeroAtInftyPrecomp γ g f x = f (g x) := rfl

/-- **Underlying map of graded cocompact precomposition.** Let `X,Y` be topological spaces, `A` a graded
nonunital complex C*-algebra, and `g : X → Y` a continuous cocompact map, meaning that it maps the
cocompact filter of `X` toward that of `Y`. Forgetting equivariance leaves the nonunital star
homomorphism `f ↦ f ∘ g` on vanishing functions. -/
@[simp]
theorem zeroAtInftyPrecomp_toNonUnitalStarAlgHom (g : CocompactMap X Y) :
    (zeroAtInftyPrecomp γ g).toNonUnitalStarAlgHom =
      ZeroAtInftyContinuousMap.compNonUnitalStarAlgHom g := rfl

/-- **Identity cocompact precomposition.** For any topological space `X` and graded nonunital complex
C*-algebra `A`, precomposition with the identity map of `X` gives the identity graded star
homomorphism of `C₀(X,A)`. -/
@[simp]
theorem zeroAtInftyPrecomp_id :
    zeroAtInftyPrecomp γ (CocompactMap.id X) = Hom.id (zeroAtInfty X γ) := by
  apply PointNormCStarAction.Hom.ext
  intro f
  apply ZeroAtInftyContinuousMap.ext
  intro x
  rfl

/-- **Contravariant composition of cocompact maps.** For topological spaces `X,Y,Z`, a graded nonunital
complex C*-algebra `A`, and continuous cocompact maps `h : X → Y`, `g : Y → Z`, precomposition along
`g ∘ h` on `C₀(Z,A)` equals precomposition along `g` followed by precomposition along `h`. -/
theorem zeroAtInftyPrecomp_comp (g : CocompactMap Y Z) (h : CocompactMap X Y) :
    zeroAtInftyPrecomp γ (g.comp h) =
      Hom.comp (zeroAtInftyPrecomp γ h) (zeroAtInftyPrecomp γ g) := by
  apply PointNormCStarAction.Hom.ext
  intro f
  apply ZeroAtInftyContinuousMap.ext
  intro x
  rfl

/-- **Evaluation commutes with graded precomposition.** Let `X,Y` be topological spaces, `A` a graded
nonunital complex C*-algebra, and `g : X → Y` a continuous cocompact map, meaning that it maps the
cocompact filter of `X` toward that of `Y`. Precomposition along `g` followed by evaluation at `x`
equals evaluation of the original function at `g(x)`. -/
theorem zeroAtInftyEval_precomp (g : CocompactMap X Y) (x : X) :
    Hom.comp (zeroAtInftyEval X γ x) (zeroAtInftyPrecomp γ g) =
      zeroAtInftyEval Y γ (g x) := by
  apply PointNormCStarAction.Hom.ext
  intro f
  rfl

end Precomposition

section Interchange

variable {X : Type uX} {Y : Type uY}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {γA : CStarGrading A} {γB : CStarGrading B}

/-- **Coefficient postcomposition commutes with cocompact precomposition.** For topological spaces
`X,Y`, graded nonunital complex C*-algebras `A,B`, an equivariant nonunital star homomorphism `φ : A
→ B`, and a continuous cocompact map `g : X → Y`, the two graded homomorphisms taking `f ∈ C₀(Y,A)`
to `φ ∘ f ∘ g ∈ C₀(X,B)` agree, regardless of composition order. -/
theorem zeroAtInftyPostcomp_precomp (φ : Hom γA γB) (g : CocompactMap X Y) :
    Hom.comp (zeroAtInftyPostcomp X φ) (zeroAtInftyPrecomp γA g) =
      Hom.comp (zeroAtInftyPrecomp γB g) (zeroAtInftyPostcomp Y φ) := by
  apply PointNormCStarAction.Hom.ext
  intro f
  apply ZeroAtInftyContinuousMap.ext
  intro x
  rfl

end Interchange

end CStarGrading
