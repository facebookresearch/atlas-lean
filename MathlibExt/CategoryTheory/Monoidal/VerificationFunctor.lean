/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.MonRelCat
public import MathlibExt.CategoryTheory.Monoidal.TracedFunctor

/-!
# Abstract verification-functor rules

A functor to preorders and monotone relations interprets a Hoare triple as
membership in the image relation. Composition gives an intermediate assertion;
tensor gives two component triples; preservation of trace gives an invariant.
All three decompositions are equivalences, supplying the semantic ingredients
for both soundness and relative completeness of a diagram proof system.

The strong monoidal comparison maps remain explicit. In particular, assertions
on a tensor object are not assumed to be definitionally pairs, and the assertion
orders need not be antisymmetric. No assertion syntax or termination claim is
part of this construction.

Source: Arthan, Martin, Mathiesen and Oliva, *A General Framework for Sound and
Complete Floyd-Hoare Logics*, Definitions 3.1–3.2 and Theorem 3.4,
https://arxiv.org/abs/0807.1016.
-/

@[expose] public section
namespace CategoryTheory.VerificationFunctor
open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] (F : C ⥤ MonRelCat.{w})

/-- The image relation interprets a Hoare triple between assertions. -/
def Triple {X Y : C} (f : X ⟶ Y) (P : F.obj X) (Q : F.obj Y) : Prop :=
  (P, Q) ∈ (F.map f).rel

/-- Consequence strengthens the input assertion and weakens the output. -/
theorem Triple.consequence {X Y : C} {f : X ⟶ Y} {P P' : F.obj X} {Q Q' : F.obj Y}
    (h : Triple F f P Q) (hP : P' ≤ P) (hQ : Q ≤ Q') : Triple F f P' Q' :=
  (F.map f).closed hP hQ h

/-- Identity verification is assertion entailment, not assertion equality. -/
@[simp] theorem triple_id_iff {X : C} (P Q : F.obj X) :
    Triple F (𝟙 X) P Q ↔ P ≤ Q := by simp [Triple]

/-- Sequential verification is equivalent to an intermediate assertion. -/
theorem triple_comp_iff {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : F.obj X) (R : F.obj Z) :
    Triple F (f ≫ g) P R ↔ ∃ Q, Triple F f P Q ∧ Triple F g Q R := by
  simp only [Triple, F.map_comp]
  rfl

/-- The sequential Hoare rule. -/
theorem Triple.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    {P : F.obj X} {Q : F.obj Y} {R : F.obj Z}
    (hf : Triple F f P Q) (hg : Triple F g Q R) : Triple F (f ≫ g) P R :=
  (triple_comp_iff F f g P R).mpr ⟨Q, hf, hg⟩

section Monoidal
variable [MonoidalCategory C] [F.Monoidal]

/-- Verify a tensor-typed morphism using pairs of assertions, transported by
the strong monoidal comparison maps. -/
def TensorTriple {X Y U V : C} (f : X ⊗ U ⟶ Y ⊗ V)
    (P : F.obj X × F.obj U) (Q : F.obj Y × F.obj V) : Prop :=
  (P, Q) ∈ (μ F X U ≫ F.map f ≫ δ F Y V).rel

/-- Comparison-adjusted triples expose their actual input and output assertions. -/
theorem tensorTriple_iff {X Y U V : C} (f : X ⊗ U ⟶ Y ⊗ V)
    (P : F.obj X × F.obj U) (Q : F.obj Y × F.obj V) :
    TensorTriple F f P Q ↔ ∃ P' Q',
      (P, P') ∈ (μ F X U).rel ∧ Triple F f P' Q' ∧ (Q', Q) ∈ (δ F Y V).rel := by
  change (∃ P', (P, P') ∈ (μ F X U).rel ∧
    ∃ Q', Triple F f P' Q' ∧ (Q', Q) ∈ (δ F Y V).rel) ↔ _
  constructor
  · rintro ⟨P', hP, Q', hf, hQ⟩
    exact ⟨P', Q', hP, hf, hQ⟩
  · rintro ⟨P', Q', hP, hf, hQ⟩
    exact ⟨P', hP, Q', hf, hQ⟩

/-- Tensor verification on arbitrary assertions decomposes through the comparisons. -/
theorem triple_tensor_iff {X Y U V : C} (f : X ⟶ Y) (g : U ⟶ V)
    (P : F.obj (X ⊗ U)) (Q : F.obj (Y ⊗ V)) :
    Triple F (f ⊗ₘ g) P Q ↔ ∃ p u q v,
      (P, (p, u)) ∈ (δ F X U).rel ∧ Triple F f p q ∧ Triple F g u v ∧
        ((q, v), Q) ∈ (μ F Y V).rel := by
  rw [Triple, Functor.Monoidal.map_tensor]
  change (∃ pu, (P, pu) ∈ (δ F X U).rel ∧
    ∃ qv, (Triple F f pu.1 qv.1 ∧ Triple F g pu.2 qv.2) ∧
      (qv, Q) ∈ (μ F Y V).rel) ↔ _
  constructor
  · rintro ⟨⟨p, u⟩, hP, ⟨q, v⟩, ⟨hf, hg⟩, hQ⟩
    exact ⟨p, u, q, v, hP, hf, hg, hQ⟩
  · rintro ⟨p, u, q, v, hP, hf, hg, hQ⟩
    exact ⟨(p, u), hP, (q, v), ⟨hf, hg⟩, hQ⟩

/-- On comparison-adjusted assertions, the parallel rule is exactly conjunction. -/
theorem tensorTriple_tensor_iff {X Y U V : C} (f : X ⟶ Y) (g : U ⟶ V)
    (p : F.obj X) (u : F.obj U) (q : F.obj Y) (v : F.obj V) :
    TensorTriple F (f ⊗ₘ g) (p, u) (q, v) ↔ Triple F f p q ∧ Triple F g u v := by
  unfold TensorTriple
  rw [Functor.Monoidal.map_tensor]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc,
    Functor.Monoidal.μ_δ, Category.comp_id]
  rfl

variable [SymmetricCategory C] {T : SymmetricTrace C}

/-- Trace preservation gives both the invariant rule and existence of a sufficient invariant. -/
theorem triple_trace_iff (hF : T.Preserves MonRelCat.symmetricTrace F)
    {X Y U : C} (f : X ⊗ U ⟶ Y ⊗ U) (P : F.obj X) (Q : F.obj Y) :
    Triple F (T.trace f) P Q ↔ ∃ I : F.obj U, TensorTriple F f (P, I) (Q, I) := by
  rw [Triple, hF f]
  rfl

end Monoidal
end CategoryTheory.VerificationFunctor
