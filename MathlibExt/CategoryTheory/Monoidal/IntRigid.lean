/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.IntCompact
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Int recovers symmetric rigid categories

For a symmetric right-rigid source, every formal pair is isomorphic to an
embedded object. The canonical embedding is therefore an equivalence.
Moreover, any supplied symmetric trace equals the canonical rigid trace.

These are the compact-target consequences of Joyal, Street and Verity,
Traced monoidal categories (1996), Propositions 3.1, 5.1 and 5.2,
https://doi.org/10.1017/S0305004100074338, in the symmetric specialization.
The general extension and its universal uniqueness are separate statements.
-/

@[expose] public section
universe v u
namespace CategoryTheory
open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open scoped MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [RightRigidCategory C]

namespace IntConstruction
variable (T : SymmetricTrace C)

/-- For a right rigid source category `C`, the formal negative object `(𝟙_ C, U)` is isomorphic
to `J(Uᘁ)`, the embedding `J = embedding T` of the right dual of `U`. -/
def negativeIso (U : C) :
    (⟨𝟙_ C, U⟩ : IntConstruction T) ≅ (embedding T).obj (Uᘁ) :=
  rightDualIso (positivePairing T U) (ExactPairing.map (embedding T) U (Uᘁ))

/-- For a right rigid source category `C`, every Int object `X` is isomorphic to the embedded
representative `J(X.positive ⊗ X.negativeᘁ)`, where `J = embedding T`: the composite of
`decomposition`, `negativeIso` on the negative factor, and the tensor comparison of `J`. -/
def representativeIso (X : IntConstruction T) :
    X ≅ (embedding T).obj (X.positive ⊗ X.negativeᘁ) :=
  decomposition T X ≪≫
    (Iso.refl ((embedding T).obj X.positive) ⊗ᵢ negativeIso T X.negative) ≪≫
      μIso (embedding T) X.positive (X.negativeᘁ)

/-- The canonical Int embedding is essentially surjective for a right-rigid source. -/
instance embeddingEssSurj : (embedding T).EssSurj where
  mem_essImage X := ⟨X.positive ⊗ X.negativeᘁ, ⟨(representativeIso T X).symm⟩⟩

/-- The fully faithful embedding is an equivalence for a right-rigid source. -/
instance embeddingIsEquivalence : (embedding T).IsEquivalence where

/-- Int adds no new objects up to equivalence to a symmetric right-rigid category. -/
noncomputable abbrev rigidEquivalence : C ≌ IntConstruction T :=
  (embedding T).asEquivalence

/-- For a right rigid source category `C`, the inverse of `rigidEquivalence T` sends `X` to an
object isomorphic to `X.positive ⊗ X.negativeᘁ`, the object whose embedding
`J(X.positive ⊗ X.negativeᘁ)` represents `X` in `representativeIso`. -/
noncomputable def rigidInverseObjIso (X : IntConstruction T) :
    (rigidEquivalence T).inverse.obj X ≅ X.positive ⊗ X.negativeᘁ :=
  (rigidEquivalence T).inverse.mapIso (representativeIso T X) ≪≫
    ((rigidEquivalence T).unitIso.app _).symm

/-- The forward equivalence retains the embedding's strong braided structure. -/
noncomputable instance rigidFunctorBraided : (rigidEquivalence T).functor.Braided :=
  inferInstanceAs ((embedding T).Braided)

/-- The inverse to the Int embedding is strong monoidal. -/
noncomputable instance rigidInverseMonoidal : (rigidEquivalence T).inverse.Monoidal :=
  (rigidEquivalence T).inverseMonoidal

/-- Unit and counit of the chosen equivalence are monoidal. -/
noncomputable instance rigidEquivalenceIsMonoidal : (rigidEquivalence T).IsMonoidal :=
  inferInstanceAs ((embedding T).asEquivalence.toAdjunction.IsMonoidal)

set_option backward.defeqAttrib.useBackward true in
/-- The inverse equivalence preserves symmetry as well as tensor products. -/
noncomputable instance rigidInverseBraided : (rigidEquivalence T).inverse.Braided where
  braided X Y := by
    let e := rigidEquivalence T
    let : NatTrans.IsMonoidal e.counitIso.hom :=
      inferInstanceAs (NatTrans.IsMonoidal (rigidEquivalence T).counit)
    let : NatTrans.IsMonoidal e.counitIso.symm.hom :=
      inferInstanceAs (NatTrans.IsMonoidal e.counitIso.inv)
    let : (e.inverse ⋙ e.functor).LaxBraided :=
      Functor.LaxBraided.ofNatIso e.counitIso.symm
    apply e.functor.map_injective
    apply (cancel_epi (μ e.functor (e.inverse.obj X) (e.inverse.obj Y))).1
    have h := Functor.LaxBraided.braided (F := e.inverse ⋙ e.functor) X Y
    change (μ e.functor _ _ ≫ e.functor.map (μ e.inverse X Y)) ≫
      e.functor.map (e.inverse.map (β_ X Y).hom) =
        (β_ _ _).hom ≫ μ e.functor _ _ ≫ e.functor.map (μ e.inverse Y X) at h
    simp only [Functor.map_comp, Category.assoc] at h ⊢
    rw [← Functor.LaxBraided.braided_assoc] at h
    exact h

/-- The inverse equivalence preserves the canonical trace. -/
theorem rigidInverse_preserves_trace :
    (symmetricTraceOfRigid (IntConstruction T)).Preserves (symmetricTraceOfRigid C)
      (rigidEquivalence T).inverse :=
  SymmetricTrace.preserves_of_rigid _

end IntConstruction

namespace SymmetricTrace

/-- A supplied symmetric trace on a right-rigid category is its canonical trace. -/
theorem trace_eq_of_rigid (T : SymmetricTrace C) {X Y U : C} (f : X ⊗ U ⟶ Y ⊗ U) :
    T.trace f = (symmetricTraceOfRigid C).trace f := by
  apply (IntConstruction.embedding T).map_injective
  exact (IntConstruction.embedding_preserves_trace T f).trans
    (preserves_of_rigid (IntConstruction.embedding T) f).symm

/-- Symmetric trace is unique once every object has a right dual. -/
instance subsingleton_of_rigid : Subsingleton (SymmetricTrace C) where
  allEq T S := by
    have h : @T.trace = @S.trace := by
      funext X Y U f
      exact (trace_eq_of_rigid T f).trans (trace_eq_of_rigid S f).symm
    cases T
    cases S
    cases h
    rfl

end SymmetricTrace
end CategoryTheory
