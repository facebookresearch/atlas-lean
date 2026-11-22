/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalWeakSolutionSet
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalFibrancy
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.Presentable
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRecognition
import MathlibExt.AlgebraicTopology.ModelCategory.Combinatorial
import MathlibExt.AlgebraicTopology.ModelCategory.Proper

/-!
# The original small-family localized model

All six Smith inputs are proved from the original site and family. One actual
package retains the new model, its global classes and both weak factorization
systems, the literal first family and actual Smith second family, one common
generation cardinal and the native functorial factors at that cardinal.
The original local-fibrant predicates continue to use the fixed base model.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]

/-- Every field is an output constructed internally for the original family.
The model-indexed fields all refer to this SAME model; no model or recognition
packet is a premise of the original-family constructor below. -/
structure OriginalLocalSmithData (S : I → Arrow (SimplicialPresheaf.{u} D)) where
  /-- All six actual Smith proofs, with the literal stored base first family. -/
  recognition : SmithRecognitionInput.{u} (C := SimplicialPresheaf.{u} D)
    (data D).I (originalLocalEquivalences S)
  /-- Smith's actual second family and the two native weak factorization systems. -/
  smith : SmithModelStructureData.{u} (C := SimplicialPresheaf.{u} D)
    (data D).I (originalLocalEquivalences S)
  /-- The new model on the unchanged original presheaf category. -/
  model : ModelCategory (SimplicialPresheaf.{u} D)
  /-- All original monomorphisms are cofibrations in this model. -/
  cofibrations_eq : model.categoryWithCofibrations.cofibrations =
    monomorphisms (SimplicialPresheaf.{u} D)
  /-- The new weak class is literally the original all-target local weak class. -/
  weakEquivalences_eq : model.categoryWithWeakEquivalences.weakEquivalences =
    originalLocalEquivalences S
  /-- Fibrations are the GLOBAL right lifting class against monic local weak maps. -/
  fibrations_eq : model.categoryWithFibrations.fibrations =
    (localTrivialMonomorphisms S).rlp
  /-- The unchanged GLOBAL trivial-fibration class. -/
  trivialFibrations_eq :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := model
    trivialFibrations (SimplicialPresheaf.{u} D) =
      (monomorphisms (SimplicialPresheaf.{u} D)).rlp
  /-- The GLOBAL trivial-cofibration class is exactly monic local weakness. -/
  trivialCofibrations_eq :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := model
    trivialCofibrations (SimplicialPresheaf.{u} D) = localTrivialMonomorphisms S
  /-- The first GLOBAL weak factorization system, on every original arrow. -/
  cofibration_wfs : IsWeakFactorizationSystem
    (monomorphisms (SimplicialPresheaf.{u} D))
    (monomorphisms (SimplicialPresheaf.{u} D)).rlp
  /-- The second GLOBAL weak factorization system, on every original arrow. -/
  trivialCofibration_wfs : IsWeakFactorizationSystem
    (localTrivialMonomorphisms S) (localTrivialMonomorphisms S).rlp
  /-- One common generation cardinal, distinct from any asserted replacement choice. -/
  θ : Cardinal.{u}
  /-- Actual regularity of the SAME generation cardinal. -/
  regular : Fact θ.IsRegular
  /-- The actual bottom of that cardinal's native ordinal type. -/
  bottom : OrderBot θ.ord.ToType
  /-- Original local presentability at that SAME generation cardinal. -/
  locallyPresentable :
    letI : Fact θ.IsRegular := regular
    IsCardinalLocallyPresentable (SimplicialPresheaf.{u} D) θ
  /-- The literal first family has all native SOA capabilities at the SAME cardinal. -/
  I_eligible :
    letI : Fact θ.IsRegular := regular
    letI : OrderBot θ.ord.ToType := bottom
    (data D).I.IsCardinalForSmallObjectArgument θ
  /-- Smith's actual second family has those capabilities at the SAME cardinal. -/
  J_eligible :
    letI : Fact θ.IsRegular := regular
    letI : OrderBot θ.ord.ToType := bottom
    smith.J.IsCardinalForSmallObjectArgument θ
  /-- Native generation data for this SAME new model and cardinal. -/
  generation :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := model
    letI : Fact θ.IsRegular := regular
    letI : OrderBot θ.ord.ToType := bottom
    CofibrantGenerationData (SimplicialPresheaf.{u} D) θ
  /-- The standard first-family projection retains the literal stored I0. -/
  generation_I : generation.I = (data D).I
  /-- The standard second-family projection retains the ACTUAL Smith family. -/
  generation_J : generation.J = smith.J
  /-- The unconditional original terminal criterion, with no localized-model premise. -/
  terminal_iff : ∀ Z : SimplicialPresheaf.{u} D,
    (localTrivialMonomorphisms S).rlp (terminal.from Z) ↔ isOriginalLocalFibrant S Z
  /-- Fibrant objects in this SAME new model are exactly the original local objects. -/
  isFibrant_iff :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := model
    ∀ Z : SimplicialPresheaf.{u} D, IsFibrant Z ↔ isOriginalLocalFibrant S Z
  /-- Original local weakness agrees with objectwise weakness at new-model fibrant endpoints. -/
  localWhitehead :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := model
    ∀ {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B),
      IsFibrant A → IsFibrant B →
      (originalLocalEquivalences S f ↔ SimplicialPresheaf.objectwiseKanWeakEquivalences D f)
  /-- Every original object is cofibrant in this SAME new model. -/
  all_cofibrant :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := model
    ∀ Z : SimplicialPresheaf.{u} D, IsCofibrant Z
  /-- Actual combinatoriality witnessed using the stored cardinal and generation data. -/
  combinatorial :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := model
    IsCombinatorialModelCategory.{u} (SimplicialPresheaf.{u} D)
  /-- Full left properness of this SAME new model, not the base model. -/
  leftProper :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := model
    IsLeftProper (SimplicialPresheaf.{u} D)

namespace OriginalLocalSmithData

variable {S : I → Arrow (SimplicialPresheaf.{u} D)}

omit [Small.{u} I] in
/-- The actual first-family native factors are COMPUTED at the recorded theta. -/
def cofibrationFactorization (d : OriginalLocalSmithData S) : FunctorialFactorizationData
    (monomorphisms (SimplicialPresheaf.{u} D))
    (monomorphisms (SimplicialPresheaf.{u} D)).rlp := by
  letI : Fact d.θ.IsRegular := d.regular
  letI : OrderBot d.θ.ord.ToType := d.bottom
  letI : (data D).I.IsCardinalForSmallObjectArgument d.θ := d.I_eligible
  letI : LocallySmall.{u} (SimplicialPresheaf.{u} D) := d.I_eligible.locallySmall
  exact (SmallObject.functorialFactorizationData (data D).I d.θ).ofLE
    (data D).I_left.le (data D).I_right.le

omit [Small.{u} I] in
/-- The entire first factorization is the literal native construction at stored theta. -/
theorem cofibrationFactorization_native (d : OriginalLocalSmithData S) :
    letI : Fact d.θ.IsRegular := d.regular
    letI : OrderBot d.θ.ord.ToType := d.bottom
    letI : (data D).I.IsCardinalForSmallObjectArgument d.θ := d.I_eligible
    letI : LocallySmall.{u} (SimplicialPresheaf.{u} D) := d.I_eligible.locallySmall
    d.cofibrationFactorization = (SmallObject.functorialFactorizationData (data D).I d.θ).ofLE
      (data D).I_left.le (data D).I_right.le := rfl

omit [Small.{u} I] in
/-- ACTUAL Smith J and the SAME theta compute the entire second factorization. -/
def trivialCofibrationFactorization (d : OriginalLocalSmithData S) :
    FunctorialFactorizationData
      (localTrivialMonomorphisms S) (localTrivialMonomorphisms S).rlp := by
  letI : Fact d.θ.IsRegular := d.regular
  letI : OrderBot d.θ.ord.ToType := d.bottom
  letI : d.smith.J.IsCardinalForSmallObjectArgument d.θ := d.J_eligible
  letI : LocallySmall.{u} (SimplicialPresheaf.{u} D) := d.J_eligible.locallySmall
  exact (SmallObject.functorialFactorizationData d.smith.J d.θ).ofLE
    (d.smith.trivialCofibrations_eq.trans
      (congrArg (fun P : MorphismProperty (SimplicialPresheaf.{u} D) =>
        P ⊓ originalLocalEquivalences S) (data D).I_left)).le
    (d.smith.fibrations_eq.trans
      (congrArg MorphismProperty.rlp
        (congrArg (fun P : MorphismProperty (SimplicialPresheaf.{u} D) =>
          P ⊓ originalLocalEquivalences S) (data D).I_left))).le

omit [Small.{u} I] in
/-- The second factorization is definitionally the SAME native J/theta value. -/
theorem trivialCofibrationFactorization_native (d : OriginalLocalSmithData S) :
    letI : Fact d.θ.IsRegular := d.regular
    letI : OrderBot d.θ.ord.ToType := d.bottom
    letI : d.smith.J.IsCardinalForSmallObjectArgument d.θ := d.J_eligible
    letI : LocallySmall.{u} (SimplicialPresheaf.{u} D) := d.J_eligible.locallySmall
    d.trivialCofibrationFactorization =
      (SmallObject.functorialFactorizationData d.smith.J d.θ).ofLE
        (d.smith.trivialCofibrations_eq.trans
          (congrArg (fun P : MorphismProperty (SimplicialPresheaf.{u} D) =>
            P ⊓ originalLocalEquivalences S) (data D).I_left)).le
        (d.smith.fibrations_eq.trans
          (congrArg MorphismProperty.rlp
            (congrArg (fun P : MorphismProperty (SimplicialPresheaf.{u} D) =>
              P ⊓ originalLocalEquivalences S) (data D).I_left))).le := rfl

end OriginalLocalSmithData

/-- The six Smith conditions are constructed from the original site and S. -/
private theorem originalSmithInput (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    SmithRecognitionInput.{u} (C := SimplicialPresheaf.{u} D)
      (data D).I (originalLocalEquivalences S) := by
  let q := data D
  let : ModelCategory (SimplicialPresheaf.{u} D) := q.model
  refine
    { weak_two_out_of_three := originalLocalEquivalences_hasTwoOutOfThreeProperty S
      weak_retracts := originalLocalEquivalences_isStableUnderRetracts S
      trivial_fibrations_weak := ?_
      trivial_cofibrations_cobase := ?_
      trivial_cofibrations_transfinite := ?_
      solution_set := ?_ }
  · intro A B f hf
    have htf : trivialFibrations (SimplicialPresheaf.{u} D) f := by
      rw [q.trivialFibrations_eq, ← q.I_right]
      exact hf
    exact weakEquivalences_le_originalLocalEquivalences S f htf.2
  · have hleft : (data D).I.rlp.llp = monomorphisms (SimplicialPresheaf.{u} D) :=
      (data D).I_left
    rw [hleft]
    exact localTrivialMonomorphisms_isStableUnderCobaseChange S
  · have hleft : (data D).I.rlp.llp = monomorphisms (SimplicialPresheaf.{u} D) :=
      (data D).I_left
    rw [hleft]
    exact localTrivialMonomorphisms_isStableUnderTransfiniteComposition S
  · intro A B f _hf
    exact originalLocalWeakArrowInclusion_solutionSetCondition S (Arrow.mk f)

/-- Construct the entire new model package without a model, Smith or HFC input. -/
private theorem existsOriginalLocalSmithData
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    Nonempty (OriginalLocalSmithData S) := by
  let q := data D
  let : LocallySmall.{u} (SimplicialPresheaf.{u} D) := SimplicialPresheaf.locallySmall
  let : IsLocallyPresentable.{u} (SimplicialPresheaf.{u} D) :=
    SimplicialPresheaf.isLocallyPresentable
  let : q.I.HasSmallObjectArgument.{u} := q.I_smallObject
  have hIleft : q.I.rlp.llp = monomorphisms (SimplicialPresheaf.{u} D) := q.I_left
  have hIright : q.I.rlp = (monomorphisms (SimplicialPresheaf.{u} D)).rlp := q.I_right
  let h := originalSmithInput S
  obtain ⟨s⟩ := smithRecognition q.I (originalLocalEquivalences S) h
  let : s.J.HasSmallObjectArgument.{u} := s.J_smallObject
  let : HasFiniteLimits (SimplicialPresheaf.{u} D) := inferInstance
  let : HasFiniteColimits (SimplicialPresheaf.{u} D) := inferInstance
  have hJleft : s.J.rlp.llp = localTrivialMonomorphisms S := by
    rw [s.trivialCofibrations_eq, hIleft]
    rfl
  have hJright : s.J.rlp = (localTrivialMonomorphisms S).rlp := by
    rw [s.fibrations_eq, hIleft]
    rfl
  let M : ModelCategory (SimplicialPresheaf.{u} D) := by
    let : CategoryWithCofibrations (SimplicialPresheaf.{u} D) :=
      ⟨monomorphisms (SimplicialPresheaf.{u} D)⟩
    let : CategoryWithWeakEquivalences (SimplicialPresheaf.{u} D) :=
      ⟨originalLocalEquivalences S⟩
    let : CategoryWithFibrations (SimplicialPresheaf.{u} D) :=
      ⟨(localTrivialMonomorphisms S).rlp⟩
    exact s.modelCategory h.weak_two_out_of_three (by
      change monomorphisms (SimplicialPresheaf.{u} D) = q.I.rlp.llp
      exact hIleft.symm) (by
      change (localTrivialMonomorphisms S).rlp = s.J.rlp
      exact hJright.symm) rfl
  let : ModelCategory (SimplicialPresheaf.{u} D) := M
  have hTC : trivialCofibrations (SimplicialPresheaf.{u} D) =
      localTrivialMonomorphisms S := rfl
  have hTF : trivialFibrations (SimplicialPresheaf.{u} D) =
      (monomorphisms (SimplicialPresheaf.{u} D)).rlp := by
    change (localTrivialMonomorphisms S).rlp ⊓ originalLocalEquivalences S = _
    rw [← hJright, s.trivialFibrations_eq, hIright]
  have hCWFS : IsWeakFactorizationSystem
      (monomorphisms (SimplicialPresheaf.{u} D))
      (monomorphisms (SimplicialPresheaf.{u} D)).rlp := by
    have hc := s.cofibration_wfs
    rw [hIleft, hIright] at hc
    exact hc
  have hTWFS : IsWeakFactorizationSystem
      (localTrivialMonomorphisms S) (localTrivialMonomorphisms S).rlp := by
    have ht := s.trivialCofibration_wfs
    rw [hJleft, hJright] at ht
    exact ht
  obtain ⟨θ, hθ, hbot, hLP, hIθ, hJθ⟩ := exists_common_generation_cardinal q.I s.J
  let : Fact θ.IsRegular := hθ
  let : OrderBot θ.ord.ToType := hbot
  let : q.I.IsCardinalForSmallObjectArgument θ := hIθ
  let : s.J.IsCardinalForSmallObjectArgument θ := hJθ
  let cg : CofibrantGenerationData (SimplicialPresheaf.{u} D) θ :=
    { I := q.I
      J := s.J
      I_smallObject := hIθ
      J_smallObject := hJθ
      I_rlp := q.I_right.trans hTF.symm
      J_rlp := hJright }
  have hfibrant (Z : SimplicialPresheaf.{u} D) :
      IsFibrant Z ↔ isOriginalLocalFibrant S Z := by
    rw [isFibrant_iff, fibration_iff]
    change (localTrivialMonomorphisms S).rlp (terminal.from Z) ↔ _
    exact localTrivialMonomorphisms_terminal_iff S Z
  have hwhitehead {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
      (hA : IsFibrant A) (hB : IsFibrant B) :
      originalLocalEquivalences S f ↔ SimplicialPresheaf.objectwiseKanWeakEquivalences D f :=
    originalLocalEquivalence_iff_objectwiseWeak_of_localFibrant S f
      ((hfibrant A).mp hA) ((hfibrant B).mp hB)
  have hcofibrant (Z : SimplicialPresheaf.{u} D) : IsCofibrant Z := by
    rw [isCofibrant_iff, cofibration_iff]
    change monomorphisms (SimplicialPresheaf.{u} D) (initial.to Z)
    let : ModelCategory (SimplicialPresheaf.{u} D) := q.model
    have hz := q.all_cofibrant Z
    rw [isCofibrant_iff, cofibration_iff] at hz
    change q.model.categoryWithCofibrations.cofibrations (initial.to Z) at hz
    rw [q.cofibrations_eq] at hz
    exact hz
  have hcombinatorial : IsCombinatorialModelCategory.{u} (SimplicialPresheaf.{u} D) :=
    { exists_cardinal := ⟨θ, hθ, hbot, hLP, ⟨cg⟩⟩ }
  have hproper : IsLeftProper (SimplicialPresheaf.{u} D) :=
    isLeftProper_of_all_objects_cofibrant hcofibrant
  exact ⟨{
    recognition := h
    smith := s
    model := M
    cofibrations_eq := rfl
    weakEquivalences_eq := rfl
    fibrations_eq := rfl
    trivialFibrations_eq := hTF
    trivialCofibrations_eq := hTC
    cofibration_wfs := hCWFS
    trivialCofibration_wfs := hTWFS
    θ := θ
    regular := hθ
    bottom := hbot
    locallyPresentable := hLP
    I_eligible := hIθ
    J_eligible := hJθ
    generation := cg
    generation_I := rfl
    generation_J := rfl
    terminal_iff := localTrivialMonomorphisms_terminal_iff S
    isFibrant_iff := hfibrant
    localWhitehead := hwhitehead
    all_cofibrant := hcofibrant
    combinatorial := hcombinatorial
    leftProper := hproper }⟩

/-- Select ONE internally constructed full original-S model package. -/
def originalLocalSmithData (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    OriginalLocalSmithData S := (existsOriginalLocalSmithData S).some

/-- The full original-family model existence theorem, using that SAME package. -/
theorem exists_originalLocalSmithModel (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    Nonempty (OriginalLocalSmithData S) := ⟨originalLocalSmithData S⟩

/-- Opt-in actual localized model, projected from the SAME constructed data value. -/
@[instance_reducible]
def originalLocalSmithModel (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model

end SimplicialPresheaf.InjectiveKan
