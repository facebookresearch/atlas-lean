/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.SystemF.Model

/-!
# Binary beta-invariant relations

The only law on an admissible relation is invariance under the existing
full-beta conversion, independently on both sides. Neither typing nor
parametricity is a field. Arrow relations test every related pair of inputs;
universal relations quantify every index of their declared family in Prop.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.SystemF

/-- **Beta-invariant binary relations on the term model.**
A binary relation on the term model, invariant under beta conversion. -/
structure Rel where
  /-- The actual binary predicate. -/
  holds : Model → Model → Prop
  /-- Conversion may replace either argument independently. -/
  congr : ∀ {f f' g g'}, BetaEq f f' → BetaEq g g' →
    (holds f g ↔ holds f' g')

namespace Rel

/-- **Extensionality of beta-invariant relations.**
Admissible relations are determined by their binary predicates. -/
@[ext] theorem ext {R S : Rel}
    (h : ∀ f g, R.holds f g ↔ S.holds f g) : R = S := by
  cases R
  cases S
  congr 1
  funext f g
  exact propext (h f g)

/-- **Function-space relation of beta-invariant relations.**
Related functions send every related input pair to related outputs. -/
def arrow (A B : Rel) : Rel where
  holds f g := ∀ x y, A.holds x y → B.holds (Model.app f x) (Model.app g y)
  congr hff' hgg' := ⟨
    fun h x y hxy => (B.congr (hff'.appFun x) (hgg'.appFun y)).mp (h x y hxy),
    fun h x y hxy => (B.congr (hff'.appFun x) (hgg'.appFun y)).mpr (h x y hxy)⟩

universe u

/-- **Universal quantification over a family of relations.**
Universal relatedness, over any index sort, uses impredicative Prop. -/
def universal {ι : Sort u} (family : ι → Rel) : Rel where
  holds f g := ∀ i, (family i).holds f g
  congr hff' hgg' := ⟨
    fun h i => ((family i).congr hff' hgg').mp (h i),
    fun h i => ((family i).congr hff' hgg').mpr (h i)⟩

/-- **Empty beta-invariant relation.**
The empty relation is admissible and prevents vacuous universality. -/
def empty : Rel where
  holds _ _ := False
  congr _ _ := Iff.rfl

/-- **Total beta-invariant relation.** The total binary relation is admissible. -/
def total : Rel where
  holds _ _ := True
  congr _ _ := Iff.rfl

/-- **Relation of two terms beta-equal to a fixed term.**
Both arguments belong to the fixed beta-conversion class of `x`. -/
def betaClass (x : Model) : Rel where
  holds f g := BetaEq f x ∧ BetaEq g x
  congr hff' hgg' := ⟨
    fun h => ⟨hff'.symm.trans h.1, hgg'.symm.trans h.2⟩,
    fun h => ⟨hff'.trans h.1, hgg'.trans h.2⟩⟩

end Rel

end Cslib.Languages.LambdaCalculus.SystemF
