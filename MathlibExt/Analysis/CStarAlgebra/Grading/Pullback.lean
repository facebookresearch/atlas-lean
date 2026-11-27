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

public import MathlibExt.Analysis.CStarAlgebra.Pullback
public import MathlibExt.Analysis.CStarAlgebra.Grading.Constructions

/-!
# Computed gradings of nonunital C-star pullbacks

The pullback of genuine graded homomorphisms is the existing closed equalizer
inside the product algebra. Its grading is the restriction of the existing
coordinatewise product grading. No new carrier, norm, C-star instance or
supplied output grading is introduced.

The coordinate homomorphisms and universal lift retain their original
ungraded maps. The only new invariance proof is the cospan equation transported
by the actual coefficient grading generators.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped CStarAlgebra

namespace CStarGrading

universe uA uB uC uX

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]
variable {γA : CStarGrading A} {γB : CStarGrading B} {γC : CStarGrading C}
variable (φ : Hom γA γC) (ψ : Hom γB γC)

/-- **Invariance of a graded pullback.** Let `A,B,C` be graded nonunital complex C*-algebras with
actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital star homomorphisms.
Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product C*-norm. The
product grading generator sends every pair in `P` to another pair in `P`. -/
theorem pullback_generator_invariant (p : A × B)
    (hp : p ∈ NonUnitalCStarPullback.Pullback
      φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom) :
    (prod γA γB).generatorAut p ∈ NonUnitalCStarPullback.Pullback
      φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom := by
  change φ p.1 = ψ p.2 at hp
  rw [NonUnitalCStarPullback.mem_pullback, prod_generatorAut, prodGenerator_apply]
  change φ (γA.generatorAut p.1) = ψ (γB.generatorAut p.2)
  calc
    φ (γA.generatorAut p.1) = γC.generatorAut (φ p.1) :=
      Hom.equivariant φ 1 p.1
    _ = γC.generatorAut (ψ p.2) := congrArg γC.generatorAut hp
    _ = ψ (γB.generatorAut p.2) := (Hom.equivariant ψ 1 p.2).symm

/-- **Grading of a C*-pullback.** Let `A,B,C` be graded nonunital complex C*-algebras with actions
`γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital star homomorphisms. Their
closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product C*-norm. The
coordinatewise action of `γ_A,γ_B` restricts to a `ℤ/2ℤ` grading of `P`. -/
def pullback : CStarGrading
    (NonUnitalCStarPullback.Pullback φ.toNonUnitalStarAlgHom
      ψ.toNonUnitalStarAlgHom) := by
  let _ : IsClosed (NonUnitalCStarPullback.Pullback
      φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom : Set (A × B)) :=
    NonUnitalCStarPullback.isClosed_pullback _ _
  exact restrictSubalgebra (prod γA γB)
    (NonUnitalCStarPullback.Pullback φ.toNonUnitalStarAlgHom
      ψ.toNonUnitalStarAlgHom) (pullback_generator_invariant φ ψ)

/-- **First projection of a graded pullback.** Let `A,B,C` be graded nonunital complex C*-algebras with
actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital star homomorphisms.
Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product C*-norm. The first
projection `P → A` is an equivariant nonunital complex star homomorphism. -/
def pullbackFst : Hom (pullback φ ψ) γA := by
  let _ : IsClosed (NonUnitalCStarPullback.Pullback
      φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom : Set (A × B)) :=
    NonUnitalCStarPullback.isClosed_pullback _ _
  exact Hom.comp (prodFst γA γB)
    (restrictSubalgebraInclusion (prod γA γB)
      (NonUnitalCStarPullback.Pullback φ.toNonUnitalStarAlgHom
        ψ.toNonUnitalStarAlgHom) (pullback_generator_invariant φ ψ))

/-- **Second projection of a graded pullback.** Let `A,B,C` be graded nonunital complex C*-algebras with
actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital star homomorphisms.
Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product C*-norm. The second
projection `P → B` is an equivariant nonunital complex star homomorphism. -/
def pullbackSnd : Hom (pullback φ ψ) γB := by
  let _ : IsClosed (NonUnitalCStarPullback.Pullback
      φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom : Set (A × B)) :=
    NonUnitalCStarPullback.isClosed_pullback _ _
  exact Hom.comp (prodSnd γA γB)
    (restrictSubalgebraInclusion (prod γA γB)
      (NonUnitalCStarPullback.Pullback φ.toNonUnitalStarAlgHom
        ψ.toNonUnitalStarAlgHom) (pullback_generator_invariant φ ψ))

/-- **First coordinate of a graded pullback projection.** Let `A,B,C` be graded nonunital complex
C*-algebras with actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital
star homomorphisms. Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product
C*-norm. For `(a,b) ∈ P`, the first graded projection evaluates to `a`. -/
@[simp]
theorem pullbackFst_apply
    (p : NonUnitalCStarPullback.Pullback φ.toNonUnitalStarAlgHom
      ψ.toNonUnitalStarAlgHom) : pullbackFst φ ψ p = p.1.1 := rfl

/-- **Second coordinate of a graded pullback projection.** Let `A,B,C` be graded nonunital complex
C*-algebras with actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital
star homomorphisms. Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product
C*-norm. For `(a,b) ∈ P`, the second graded projection evaluates to `b`. -/
@[simp]
theorem pullbackSnd_apply
    (p : NonUnitalCStarPullback.Pullback φ.toNonUnitalStarAlgHom
      ψ.toNonUnitalStarAlgHom) : pullbackSnd φ ψ p = p.1.2 := rfl

/-- **Underlying first pullback projection.** Let `A,B,C` be graded nonunital complex C*-algebras with
actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital star homomorphisms.
Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product C*-norm. Forgetting
grading equivariance gives the first-coordinate star homomorphism of the ungraded pullback. -/
@[simp]
theorem pullbackFst_toNonUnitalStarAlgHom :
    (pullbackFst φ ψ).toNonUnitalStarAlgHom =
      NonUnitalCStarPullback.fstHom φ.toNonUnitalStarAlgHom
        ψ.toNonUnitalStarAlgHom := rfl

/-- **Underlying second pullback projection.** Let `A,B,C` be graded nonunital complex C*-algebras with
actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital star homomorphisms.
Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product C*-norm. Forgetting
grading equivariance gives the second-coordinate star homomorphism of the ungraded pullback. -/
@[simp]
theorem pullbackSnd_toNonUnitalStarAlgHom :
    (pullbackSnd φ ψ).toNonUnitalStarAlgHom =
      NonUnitalCStarPullback.sndHom φ.toNonUnitalStarAlgHom
        ψ.toNonUnitalStarAlgHom := rfl

/-- **Coordinates of each pullback grading degree.** Let `A,B,C` be graded nonunital complex C*-algebras
with actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital star
homomorphisms. Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product
C*-norm. For every `n ∈ ℤ/2ℤ`, the grading sends `(a,b) ∈ P` to `(γ_A(n)a,γ_B(n)b)`. -/
theorem pullback_aut_coe (n : ZMod 2)
    (p : NonUnitalCStarPullback.Pullback φ.toNonUnitalStarAlgHom
      ψ.toNonUnitalStarAlgHom) :
    ((PointNormCStarAddAction.aut (pullback φ ψ) n p :
        NonUnitalCStarPullback.Pullback φ.toNonUnitalStarAlgHom
          ψ.toNonUnitalStarAlgHom) : A × B) =
      (PointNormCStarAddAction.aut γA n p.1.1,
        PointNormCStarAddAction.aut γB n p.1.2) := by
  apply Prod.ext
  · simpa only [pullbackFst_apply] using Hom.equivariant (pullbackFst φ ψ) n p
  · simpa only [pullbackSnd_apply] using Hom.equivariant (pullbackSnd φ ψ) n p

/-- **Coordinates of the pullback generator.** Let `A,B,C` be graded nonunital complex C*-algebras with
actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital star homomorphisms.
Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product C*-norm. The
degree-one generator of `P` is the pair of degree-one generators of `A` and `B`. -/
@[simp]
theorem pullback_generator_coe
    (p : NonUnitalCStarPullback.Pullback φ.toNonUnitalStarAlgHom
      ψ.toNonUnitalStarAlgHom) :
    (((pullback φ ψ).generatorAut p :
        NonUnitalCStarPullback.Pullback φ.toNonUnitalStarAlgHom
          ψ.toNonUnitalStarAlgHom) : A × B) =
      (γA.generatorAut p.1.1, γB.generatorAut p.1.2) :=
  pullback_aut_coe φ ψ 1 p

/-- **Homogeneous parts of a pullback.** Let `A,B,C` be graded nonunital complex C*-algebras with
actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital star homomorphisms.
Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product C*-norm. A pair
`(a,b) ∈ P` has degree `n` exactly when both `a` and `b` have degree `n` in their respective
algebras. -/
theorem mem_pullback_part_iff (n : ZMod 2)
    (p : NonUnitalCStarPullback.Pullback φ.toNonUnitalStarAlgHom
      ψ.toNonUnitalStarAlgHom) :
    p ∈ (pullback φ ψ).part n ↔ p.1.1 ∈ γA.part n ∧ p.1.2 ∈ γB.part n := by
  let _ : IsClosed (NonUnitalCStarPullback.Pullback
      φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom : Set (A × B)) :=
    NonUnitalCStarPullback.isClosed_pullback _ _
  exact (mem_restrictSubalgebra_part_iff (prod γA γB)
    (NonUnitalCStarPullback.Pullback φ.toNonUnitalStarAlgHom
      ψ.toNonUnitalStarAlgHom) (pullback_generator_invariant φ ψ) n p).trans
    (mem_prod_part_iff γA γB n (p : A × B))

/-- **Compatibility of graded pullback projections.** Let `A,B,C` be graded nonunital complex
C*-algebras with actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital
star homomorphisms. Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product
C*-norm. The first graded projection followed by `φ` equals the second followed by `ψ`. -/
theorem pullback_condition :
    Hom.comp φ (pullbackFst φ ψ) = Hom.comp ψ (pullbackSnd φ ψ) := by
  apply PointNormCStarAction.Hom.ext
  intro p
  exact NonUnitalCStarPullback.condition φ.toNonUnitalStarAlgHom
    ψ.toNonUnitalStarAlgHom p

section UniversalProperty

variable {X : Type uX} [NonUnitalCStarAlgebra X] {γX : CStarGrading X}

/-- **Universal graded pullback lift.** Let `A,B,C` be graded nonunital complex C*-algebras with actions
`γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital star homomorphisms. Their
closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product C*-norm. Let `X` be
another graded nonunital complex C*-algebra and let `u : X → A`, `v : X → B` be equivariant
nonunital star homomorphisms with `φ ∘ u = ψ ∘ v`. The map `x ↦ (u(x),v(x))` is an equivariant
nonunital star homomorphism `X → P`. -/
def pullbackLift (u : Hom γX γA) (v : Hom γX γB)
    (h : φ.toNonUnitalStarAlgHom.comp u.toNonUnitalStarAlgHom =
      ψ.toNonUnitalStarAlgHom.comp v.toNonUnitalStarAlgHom) :
    Hom γX (pullback φ ψ) where
  toNonUnitalStarAlgHom := NonUnitalCStarPullback.lift
    φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom
    u.toNonUnitalStarAlgHom v.toNonUnitalStarAlgHom h
  equivariant' := by
    intro n x
    apply Subtype.ext
    change (u (PointNormCStarAddAction.aut γX n.toAdd x),
        v (PointNormCStarAddAction.aut γX n.toAdd x)) =
      ((PointNormCStarAddAction.aut (pullback φ ψ) n.toAdd
          (NonUnitalCStarPullback.lift φ.toNonUnitalStarAlgHom
            ψ.toNonUnitalStarAlgHom u.toNonUnitalStarAlgHom
            v.toNonUnitalStarAlgHom h x) :
          NonUnitalCStarPullback.Pullback φ.toNonUnitalStarAlgHom
            ψ.toNonUnitalStarAlgHom) : A × B)
    rw [pullback_aut_coe]
    exact Prod.ext (Hom.equivariant u n.toAdd x) (Hom.equivariant v n.toAdd x)

/-- **Ungraded homomorphism of a graded pullback lift.** Let `A,B,C` be graded nonunital complex
C*-algebras with actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital
star homomorphisms. Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product
C*-norm. Let `X` be another graded nonunital complex C*-algebra and let `u : X → A`, `v : X → B` be
equivariant nonunital star homomorphisms with `φ ∘ u = ψ ∘ v`. Forgetting equivariance gives the
usual universal star homomorphism `x ↦ (u(x),v(x))` into the ungraded pullback. -/
@[simp]
theorem pullbackLift_toNonUnitalStarAlgHom (u : Hom γX γA) (v : Hom γX γB)
    (h : φ.toNonUnitalStarAlgHom.comp u.toNonUnitalStarAlgHom =
      ψ.toNonUnitalStarAlgHom.comp v.toNonUnitalStarAlgHom) :
    (pullbackLift φ ψ u v h).toNonUnitalStarAlgHom =
      NonUnitalCStarPullback.lift φ.toNonUnitalStarAlgHom
        ψ.toNonUnitalStarAlgHom u.toNonUnitalStarAlgHom
        v.toNonUnitalStarAlgHom h := rfl

/-- **Coordinate values of a graded pullback lift.** Let `A,B,C` be graded nonunital complex C*-algebras
with actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital star
homomorphisms. Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product
C*-norm. Let `X` be another graded nonunital complex C*-algebra and let `u : X → A`, `v : X → B` be
equivariant nonunital star homomorphisms with `φ ∘ u = ψ ∘ v`. At every `x ∈ X`, the lift has
ambient pair `(u(x),v(x))`. -/
@[simp]
theorem pullbackLift_coe_apply (u : Hom γX γA) (v : Hom γX γB)
    (h : φ.toNonUnitalStarAlgHom.comp u.toNonUnitalStarAlgHom =
      ψ.toNonUnitalStarAlgHom.comp v.toNonUnitalStarAlgHom) (x : X) :
    ((pullbackLift φ ψ u v h x :
        NonUnitalCStarPullback.Pullback φ.toNonUnitalStarAlgHom
          ψ.toNonUnitalStarAlgHom) : A × B) = (u x, v x) := rfl

/-- **First projection of the graded lift.** Let `A,B,C` be graded nonunital complex C*-algebras with
actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital star homomorphisms.
Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product C*-norm. Let `X` be
another graded nonunital complex C*-algebra and let `u : X → A`, `v : X → B` be equivariant
nonunital star homomorphisms with `φ ∘ u = ψ ∘ v`. The lift followed by the first graded projection
equals `u`. -/
@[simp]
theorem pullbackFst_comp_lift (u : Hom γX γA) (v : Hom γX γB)
    (h : φ.toNonUnitalStarAlgHom.comp u.toNonUnitalStarAlgHom =
      ψ.toNonUnitalStarAlgHom.comp v.toNonUnitalStarAlgHom) :
    Hom.comp (pullbackFst φ ψ) (pullbackLift φ ψ u v h) = u := by
  apply PointNormCStarAction.Hom.ext
  intro x
  rfl

/-- **Second projection of the graded lift.** Let `A,B,C` be graded nonunital complex C*-algebras with
actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital star homomorphisms.
Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product C*-norm. Let `X` be
another graded nonunital complex C*-algebra and let `u : X → A`, `v : X → B` be equivariant
nonunital star homomorphisms with `φ ∘ u = ψ ∘ v`. The lift followed by the second graded projection
equals `v`. -/
@[simp]
theorem pullbackSnd_comp_lift (u : Hom γX γA) (v : Hom γX γB)
    (h : φ.toNonUnitalStarAlgHom.comp u.toNonUnitalStarAlgHom =
      ψ.toNonUnitalStarAlgHom.comp v.toNonUnitalStarAlgHom) :
    Hom.comp (pullbackSnd φ ψ) (pullbackLift φ ψ u v h) = v := by
  apply PointNormCStarAction.Hom.ext
  intro x
  rfl

/-- **Extensionality of graded pullback homomorphisms.** Let `A,B,C` be graded nonunital complex
C*-algebras with actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital
star homomorphisms. Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product
C*-norm. For another graded nonunital complex C*-algebra `X`, two equivariant star homomorphisms `X
→ P` are equal if both their coordinate projections agree. -/
theorem pullback_hom_ext (k l : Hom γX (pullback φ ψ))
    (hfst : Hom.comp (pullbackFst φ ψ) k = Hom.comp (pullbackFst φ ψ) l)
    (hsnd : Hom.comp (pullbackSnd φ ψ) k = Hom.comp (pullbackSnd φ ψ) l) : k = l := by
  have hraw := NonUnitalCStarPullback.hom_ext φ.toNonUnitalStarAlgHom
    ψ.toNonUnitalStarAlgHom k.toNonUnitalStarAlgHom l.toNonUnitalStarAlgHom
    (congrArg (fun θ : Hom γX γA => θ.toNonUnitalStarAlgHom) hfst)
    (congrArg (fun θ : Hom γX γB => θ.toNonUnitalStarAlgHom) hsnd)
  exact PointNormCStarAction.Hom.ext (fun x => DFunLike.congr_fun hraw x)

/-- **Uniqueness of a graded pullback lift.** Let `A,B,C` be graded nonunital complex C*-algebras with
actions `γ_A,γ_B,γ_C`, and let `φ : A → C`, `ψ : B → C` be equivariant nonunital star homomorphisms.
Their closed pullback is `P = {(a,b) : φ(a) = ψ(b)}`, with the inherited product C*-norm. Let `X` be
another graded nonunital complex C*-algebra and let `u : X → A`, `v : X → B` be equivariant
nonunital star homomorphisms with `φ ∘ u = ψ ∘ v`. Any equivariant star homomorphism `X → P` whose
projections are `u` and `v` equals the universal lift. -/
theorem pullbackLift_unique (u : Hom γX γA) (v : Hom γX γB)
    (h : φ.toNonUnitalStarAlgHom.comp u.toNonUnitalStarAlgHom =
      ψ.toNonUnitalStarAlgHom.comp v.toNonUnitalStarAlgHom)
    (k : Hom γX (pullback φ ψ))
    (hfst : Hom.comp (pullbackFst φ ψ) k = u)
    (hsnd : Hom.comp (pullbackSnd φ ψ) k = v) : k = pullbackLift φ ψ u v h := by
  have hraw := NonUnitalCStarPullback.lift_unique φ.toNonUnitalStarAlgHom
    ψ.toNonUnitalStarAlgHom u.toNonUnitalStarAlgHom v.toNonUnitalStarAlgHom
    h k.toNonUnitalStarAlgHom
    (congrArg (fun θ : Hom γX γA => θ.toNonUnitalStarAlgHom) hfst)
    (congrArg (fun θ : Hom γX γB => θ.toNonUnitalStarAlgHom) hsnd)
  exact PointNormCStarAction.Hom.ext (fun x => DFunLike.congr_fun hraw x)

end UniversalProperty

end CStarGrading
