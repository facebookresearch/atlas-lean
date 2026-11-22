/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.Combinatorial
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalIndexQuillenComparisons

/-!
# Ordinary injective models from the original combinatorial coefficient

Combinatoriality supplies an existential witness for the coefficient rank and
its two original generating families. `coefficientData` selects that source
witness. It contains coefficient data only: the model on the functor category,
its compact diagrams, its generators and its factorizations are constructed by
the existing original injective factory.

For an essentially small original category the native small-model equivalence
supplies the index input. All coefficient and index object/Hom universes remain
independent of the working universe. The returned carrier is the original
`D ⥤ C`, and the model is literally `originalSmithModelCategory` for the selected
source witness. Both factor records below retain their native middle functors
and transformations; reclassification changes membership proofs only.

The model construction and projective-to-injective identity comparison follow
*Higher Topos Theory*, Proposition A.2.8.2 and Remark A.2.8.5, author version
of April 9, 2017, printed pages 830 and 832 (PDF pages 848 and 850).
Essentially small index transport and independence of source choices are
project-derived consequences of the actual class identities.
-/

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

namespace HomotopicalAlgebra.FunctorInjective.SourceConstruction

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

variable (C : Type uC) [Category.{vC} C] [ModelCategory C]

/-- A selected witness of the original coefficient's combinatoriality.
No functor-category structure or conclusion is included in these source data. -/
structure CoefficientData where
  /-- The rank of the original coefficient generation and presentability witness. -/
  cardinal : Cardinal.{w}
  /-- Regularity belongs to that same original witness. -/
  [regular : Fact cardinal.IsRegular]
  /-- The native ordinal iteration uses the bottom of that same witness. -/
  [bottom : OrderBot cardinal.ord.ToType]
  /-- Actual local presentability of the coefficient at the selected rank. -/
  [locallyPresentable : IsCardinalLocallyPresentable C cardinal]
  /-- Both actual coefficient families and their original right-class identities. -/
  generation : CofibrantGenerationData C cardinal

/-- Select actual coefficient generation from the existing existential
combinatorial hypothesis. No rank or desired functor model is supplied. -/
def coefficientData [IsCombinatorialModelCategory.{w} C] : CoefficientData.{w} C := by
  apply Classical.choice
  obtain ⟨kappa, hRegular, hBottom, hPresentable, ⟨d⟩⟩ :=
    IsCombinatorialModelCategory.exists_cardinal (C := C)
  let : Fact kappa.IsRegular := hRegular
  let : OrderBot kappa.ord.ToType := hBottom
  let : IsCardinalLocallyPresentable C kappa := hPresentable
  exact ⟨
    { cardinal := kappa
      regular := hRegular
      bottom := hBottom
      locallyPresentable := hPresentable
      generation := d }⟩

namespace CoefficientData

variable {C} (c : CoefficientData.{w} C)
  {D : Type uD} [Category.{vD} D] (s : Functor.EssentialIndexData.{w} D C)

local instance coefficientRegular : Fact c.cardinal.IsRegular := c.regular
/-- The selected coefficient witness supplies its actual native ordinal bottom. -/
local instance coefficientBottom : OrderBot c.cardinal.ord.ToType := c.bottom
local instance coefficientPresentable : IsCardinalLocallyPresentable C c.cardinal :=
  c.locallyPresentable

/-- Native essential smallness supplies the full original small-index equivalence.
Coefficient Hom smallness follows from actual coefficient local presentability. -/
def essentialIndex [EssentiallySmall.{w} D] : Functor.EssentialIndexData.{w} D C := by
  letI : IsLocallyPresentable.{w} C := ⟨c.cardinal, c.regular, c.locallyPresentable⟩
  letI : LocallySmall.{w} C := inferInstance
  exact Functor.EssentialIndexData.ofEssentiallySmall

/-- Construct the model on the unchanged original carrier using the selected
coefficient source and the full original index equivalence. -/
@[instance_reducible]
def modelCategory : ModelCategory (D ⥤ C) :=
  originalSmithModelCategory c.generation c.cardinal s

/-- The returned dictionary is the exact original Smith construction. -/
theorem modelCategory_eq_original :
    c.modelCategory s = originalSmithModelCategory c.generation c.cardinal s := rfl

/-- The same original source constructs the common rank and both actual families. -/
def generationAndFactors :
    OriginalInjectiveGenerationAndFactorsData c.generation c.cardinal s :=
  originalInjectiveGenerationAndFactors c.generation c.cardinal s

/-- The common-rank generation makes this exact model combinatorial. -/
theorem isCombinatorial :
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    IsCombinatorialModelCategory.{w} (D ⥤ C) :=
  originalInjectiveModel_isCombinatorial c.generation c.cardinal s

/-- Every model predicate concerns the original whole natural transformation. -/
theorem fiveClasses :
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    weakEquivalences (D ⥤ C) = (weakEquivalences C).functorCategory D ∧
      cofibrations (D ⥤ C) = (cofibrations C).functorCategory D ∧
      trivialCofibrations (D ⥤ C) = (trivialCofibrations C).functorCategory D ∧
      fibrations (D ⥤ C) = ((trivialCofibrations C).functorCategory D).rlp ∧
      trivialFibrations (D ⥤ C) = ((cofibrations C).functorCategory D).rlp :=
  originalInjectiveModel_fiveClasses c.generation c.cardinal s

/-- The first native common-rank factorization, stated in the original
objectwise and whole-lifting classes independently of a target model instance. -/
def cofibrantFactorizationData :
    FunctorialFactorizationData ((cofibrations C).functorCategory D)
      (((cofibrations C).functorCategory D).rlp) := by
  letI : ModelCategory (D ⥤ C) := c.modelCategory s
  let g := c.generationAndFactors s
  letI : Fact g.cardinal.IsRegular := g.regular
  letI : OrderBot g.cardinal.ord.ToType := g.bottom
  exact g.generationData.cofibrantFactorizationData.ofLE
    (by rw [originalInjectiveModel_cofibrations c.generation c.cardinal s])
    (by rw [originalInjectiveModel_trivialFibrations c.generation c.cardinal s])

/-- The second native common-rank factorization uses the actual produced
Smith family and the full original trivial-cofibration lifting class. -/
def fibrantFactorizationData :
    FunctorialFactorizationData ((trivialCofibrations C).functorCategory D)
      (((trivialCofibrations C).functorCategory D).rlp) := by
  letI : ModelCategory (D ⥤ C) := c.modelCategory s
  let g := c.generationAndFactors s
  letI : Fact g.cardinal.IsRegular := g.regular
  letI : OrderBot g.cardinal.ord.ToType := g.bottom
  exact g.generationData.fibrantFactorizationData.ofLE
    (by rw [originalInjectiveModel_trivialCofibrations c.generation c.cardinal s])
    (by rw [originalInjectiveModel_fibrations c.generation c.cardinal s])

/-- Reclassification retains all three first-factor fields, including every
original Arrow map in its middle functor. The dependent transformation fields
are recorded by heterogeneous equality alongside the equality of whole middle functors. -/
theorem cofibrantFactorizationData_nativeFields :
    let g := c.generationAndFactors s
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    letI : Fact g.cardinal.IsRegular := g.regular
    letI : OrderBot g.cardinal.ord.ToType := g.bottom
    (c.cofibrantFactorizationData s).Z = g.generationData.cofibrantFactorizationData.Z ∧
      HEq (c.cofibrantFactorizationData s).i g.generationData.cofibrantFactorizationData.i ∧
      HEq (c.cofibrantFactorizationData s).p g.generationData.cofibrantFactorizationData.p := by
  exact ⟨rfl, HEq.rfl, HEq.rfl⟩

/-- Reclassification retains the actual second-factor fields at that same
constructed rank and for every original Arrow, using heterogeneous equality
for its dependent transformation fields. -/
theorem fibrantFactorizationData_nativeFields :
    let g := c.generationAndFactors s
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    letI : Fact g.cardinal.IsRegular := g.regular
    letI : OrderBot g.cardinal.ord.ToType := g.bottom
    (c.fibrantFactorizationData s).Z = g.generationData.fibrantFactorizationData.Z ∧
      HEq (c.fibrantFactorizationData s).i g.generationData.fibrantFactorizationData.i ∧
      HEq (c.fibrantFactorizationData s).p g.generationData.fibrantFactorizationData.p := by
  exact ⟨rfl, HEq.rfl, HEq.rfl⟩

/-- Every first right factor is weak on every original index object. -/
theorem cofibrantFactorizationData_right_weak (f : Arrow (D ⥤ C)) :
    (weakEquivalences C).functorCategory D ((c.cofibrantFactorizationData s).p.app f) := by
  let : ModelCategory (D ⥤ C) := c.modelCategory s
  have h : trivialFibrations (D ⥤ C) ((c.cofibrantFactorizationData s).p.app f) := by
    rw [originalInjectiveModel_trivialFibrations c.generation c.cardinal s]
    exact (c.cofibrantFactorizationData s).hp f
  rw [← originalSmithModel_weakEquivalences c.generation c.cardinal s]
  exact h.2

/-- Every second left factor is weak on every original index object. -/
theorem fibrantFactorizationData_left_weak (f : Arrow (D ⥤ C)) :
    (weakEquivalences C).functorCategory D ((c.fibrantFactorizationData s).i.app f) :=
  fun a => ((c.fibrantFactorizationData s).hi f a).2

/-- The existing projective factory uses the same selected coefficient source. -/
@[instance_reducible]
def projectiveModelCategory : ModelCategory (D ⥤ C) :=
  originalProjectiveModelCategory c.generation s

/-- The literal identity is a Quillen equivalence between the two actually
constructed models; neither target model is supplied. -/
theorem projectiveToInjective_isQuillenEquivalence :
    @Adjunction.IsQuillenEquivalence (D ⥤ C) _ (D ⥤ C) _
      (c.projectiveModelCategory s) (c.modelCategory s)
      (𝟭 (D ⥤ C)) (𝟭 (D ⥤ C)) (Adjunction.id (C := D ⥤ C)) :=
  originalProjectiveToInjective_isQuillenEquivalence c.generation c.cardinal s

end CoefficientData

variable {C} [IsCombinatorialModelCategory.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]

/-- The complete selected index for the original essentially small category. -/
def essentialIndex : Functor.EssentialIndexData.{w} D C :=
  (coefficientData C).essentialIndex

/-- Construct the original injective model from conventional combinatorial
coefficient and essential-smallness hypotheses, with no chosen rank input. -/
@[instance_reducible]
def modelCategory : ModelCategory (D ⥤ C) :=
  (coefficientData C).modelCategory (essentialIndex (D := D) (C := C))

/-- The existence entry uses the same original Smith model and source witness. -/
theorem modelCategory_eq_original :
    let c := coefficientData C
    letI : Fact c.cardinal.IsRegular := c.regular
    letI : OrderBot c.cardinal.ord.ToType := c.bottom
    letI : IsCardinalLocallyPresentable C c.cardinal := c.locallyPresentable
    modelCategory (D := D) (C := C) =
      originalSmithModelCategory c.generation c.cardinal (essentialIndex (D := D) (C := C)) :=
  rfl

/-- Combinatoriality is an output for the constructed original model. -/
theorem isCombinatorial :
    letI : ModelCategory (D ⥤ C) := modelCategory (D := D) (C := C)
    IsCombinatorialModelCategory.{w} (D ⥤ C) :=
  (coefficientData C).isCombinatorial (essentialIndex (D := D) (C := C))

/-- The conventional existence entry retains all five original model classes. -/
theorem fiveClasses :
    letI : ModelCategory (D ⥤ C) := modelCategory (D := D) (C := C)
    weakEquivalences (D ⥤ C) = (weakEquivalences C).functorCategory D ∧
      cofibrations (D ⥤ C) = (cofibrations C).functorCategory D ∧
      trivialCofibrations (D ⥤ C) = (trivialCofibrations C).functorCategory D ∧
      fibrations (D ⥤ C) = ((trivialCofibrations C).functorCategory D).rlp ∧
      trivialFibrations (D ⥤ C) = ((cofibrations C).functorCategory D).rlp :=
  (coefficientData C).fiveClasses (essentialIndex (D := D) (C := C))

/-- The existence entry returns the actual first native factor record. -/
def cofibrantFactorizationData :
    FunctorialFactorizationData ((cofibrations C).functorCategory D)
      (((cofibrations C).functorCategory D).rlp) :=
  (coefficientData C).cofibrantFactorizationData (essentialIndex (D := D) (C := C))

/-- The existence entry returns the actual second native factor record. -/
def fibrantFactorizationData :
    FunctorialFactorizationData ((trivialCofibrations C).functorCategory D)
      (((trivialCofibrations C).functorCategory D).rlp) :=
  (coefficientData C).fibrantFactorizationData (essentialIndex (D := D) (C := C))

/-- Conventional source hypotheses produce a combinatorial injective model
and its full original class identities on the unchanged carrier. -/
theorem existsModelCategory :
    ∃ M : ModelCategory (D ⥤ C),
      letI : ModelCategory (D ⥤ C) := M
      IsCombinatorialModelCategory.{w} (D ⥤ C) ∧
        weakEquivalences (D ⥤ C) = (weakEquivalences C).functorCategory D ∧
        cofibrations (D ⥤ C) = (cofibrations C).functorCategory D ∧
        trivialCofibrations (D ⥤ C) = (trivialCofibrations C).functorCategory D ∧
        fibrations (D ⥤ C) = ((trivialCofibrations C).functorCategory D).rlp ∧
        trivialFibrations (D ⥤ C) = ((cofibrations C).functorCategory D).rlp :=
  ⟨modelCategory (D := D) (C := C), isCombinatorial (D := D) (C := C),
    fiveClasses (D := D) (C := C)⟩

end HomotopicalAlgebra.FunctorInjective.SourceConstruction
