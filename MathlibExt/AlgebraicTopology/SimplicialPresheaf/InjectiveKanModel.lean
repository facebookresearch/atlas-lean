/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.MonomorphismGenerators
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.Presentable
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveWeakClosure
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.KanWeakArrowInterpolation
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRecognition
import MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# The injective Kan–Quillen model on the original simplicial presheaves

On the original category `Dᵒᵖ ⥤ SSet`, cofibrations are all natural
monomorphisms, weak equivalences are the original objectwise realization
weak equivalences, and fibrations are the global right orthogonal to their
intersection. The model is constructed from the actual original
monomorphism generators and bounded weak-arrow interpolation, through the
native six-field Smith recognition theorem.

One complete data choice records the literal first family and Smith's second
family at one common regular cardinal for local presentability and standard
cofibrant generation. Both native functorial factorizations retain their
original maps. The named model is opt-in; no presheaf model or generation
result is a construction input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen

namespace SimplicialPresheaf.InjectiveKan

variable (D : Type w) [Category.{v} D]

/-- The original global mono class intersected with the original weak class. -/
def trivialMonomorphisms : MorphismProperty (SimplicialPresheaf.{u} D) :=
  monomorphisms (SimplicialPresheaf.{u} D) ⊓ objectwiseKanWeakEquivalences D

/-- The actual global RLP; objectwise scalar fibrancy is not substituted here. -/
def injectiveFibrations : MorphismProperty (SimplicialPresheaf.{u} D) :=
  (trivialMonomorphisms D).rlp

section SmallSites

variable [Small.{u} D] [LocallySmall.{u} D]

private theorem smithInput
    (I : MorphismProperty (SimplicialPresheaf.{u} D))
    (hleft : I.rlp.llp = monomorphisms (SimplicialPresheaf.{u} D))
    (hright : I.rlp = (monomorphisms (SimplicialPresheaf.{u} D)).rlp) :
    SmithRecognitionInput.{u} (C := SimplicialPresheaf.{u} D)
      I (objectwiseKanWeakEquivalences D) := by
  refine
    { weak_two_out_of_three := inferInstance
      weak_retracts := inferInstance
      trivial_fibrations_weak := ?_
      trivial_cofibrations_cobase := ?_
      trivial_cofibrations_transfinite := ?_
      solution_set := ?_ }
  · rw [hright]
    exact globalMonos_rlp_le_objectwiseKanWeakEquivalences D
  · rw [hleft]
    infer_instance
  · rw [hleft]
    infer_instance
  · intro A B i _hi
    obtain ⟨γ, J, F, incoming, hF, hfactor⟩ :=
      SimplicialPresheaf.objectwiseKanWeakArrowInterpolation (D := D) (Arrow.mk i)
    let X : J → (objectwiseKanWeakEquivalences D).arrowObjectProperty.FullSubcategory :=
      fun j => ⟨F j, (hF j).1⟩
    refine ⟨J, X, incoming, ?_⟩
    intro Y t
    obtain ⟨j, outgoing, s, e, hs, houtgoing, hwhole, hleftLeg, hrightLeg⟩ :=
      hfactor Y.obj Y.property t
    refine ⟨j, ObjectProperty.homMk outgoing, ?_⟩
    exact hwhole

end SmallSites

/-- The complete original-site model and generation data, with one literal
first family, actual Smith second family and common generation cardinal. -/
structure Data where
  /-- Index of the literal first-family original representatives. -/
  index : Type u
  /-- The actual original arrows from the monomorphism generator theorem. -/
  F : index → Arrow (SimplicialPresheaf.{u} D)
  I_smallObject : (ofHoms (fun k => (F k).hom)).HasSmallObjectArgument.{u}
  I_left : (ofHoms (fun k => (F k).hom)).rlp.llp =
    monomorphisms (SimplicialPresheaf.{u} D)
  I_right : (ofHoms (fun k => (F k).hom)).rlp =
    (monomorphisms (SimplicialPresheaf.{u} D)).rlp
  /-- Native recognition data with the actual second family for this same first family. -/
  smith : SmithModelStructureData.{u} (C := SimplicialPresheaf.{u} D)
    (ofHoms (fun k => (F k).hom)) (objectwiseKanWeakEquivalences D)
  /-- The actual model on the original carrier with the class dictionaries below. -/
  model : ModelCategory (SimplicialPresheaf.{u} D)
  cofibrations_eq : model.categoryWithCofibrations.cofibrations =
    monomorphisms (SimplicialPresheaf.{u} D)
  weakEquivalences_eq : model.categoryWithWeakEquivalences.weakEquivalences =
    objectwiseKanWeakEquivalences D
  fibrations_eq : model.categoryWithFibrations.fibrations = injectiveFibrations D
  /-- Common cardinal for local presentability and both native generating families. -/
  κ : Cardinal.{u}
  regular : Fact κ.IsRegular
  /-- Actual least stage of the common cardinal's native ordinal type. -/
  bottom : OrderBot κ.ord.ToType
  locallyPresentable :
    letI : Fact κ.IsRegular := regular
    IsCardinalLocallyPresentable (SimplicialPresheaf.{u} D) κ
  I_eligible :
    letI : Fact κ.IsRegular := regular
    letI : OrderBot κ.ord.ToType := bottom
    (ofHoms (fun k => (F k).hom)).IsCardinalForSmallObjectArgument κ
  J_eligible :
    letI : Fact κ.IsRegular := regular
    letI : OrderBot κ.ord.ToType := bottom
    smith.J.IsCardinalForSmallObjectArgument κ

namespace Data

variable {D} (q : Data.{u} D)

/-- The first family is literally G1's represented original arrows. -/
def I : MorphismProperty (SimplicialPresheaf.{u} D) :=
  ofHoms (fun k => (q.F k).hom)

theorem J_rlp_eq : q.smith.J.rlp = injectiveFibrations D := by
  rw [q.smith.fibrations_eq, q.I_left]
  rfl

theorem J_left_eq : q.smith.J.rlp.llp = trivialMonomorphisms D := by
  rw [q.smith.trivialCofibrations_eq, q.I_left]
  rfl

theorem cofibration_wfs (q : Data.{u} D) : IsWeakFactorizationSystem
    (monomorphisms (SimplicialPresheaf.{u} D))
    (monomorphisms (SimplicialPresheaf.{u} D)).rlp := by
  have h := q.smith.cofibration_wfs
  rw [q.I_left, q.I_right] at h
  exact h

theorem trivialCofibration_wfs (q : Data.{u} D) : IsWeakFactorizationSystem
    (trivialMonomorphisms.{u} D) (injectiveFibrations D) := by
  rw [← q.J_left_eq, ← q.J_rlp_eq]
  exact q.smith.trivialCofibration_wfs

theorem trivialCofibrations_eq :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := q.model
    trivialCofibrations (SimplicialPresheaf.{u} D) = trivialMonomorphisms D := by
  let : ModelCategory (SimplicialPresheaf.{u} D) := q.model
  change q.model.categoryWithCofibrations.cofibrations ⊓
    q.model.categoryWithWeakEquivalences.weakEquivalences = trivialMonomorphisms D
  rw [q.cofibrations_eq, q.weakEquivalences_eq]
  rfl

theorem trivialFibrations_eq :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := q.model
    trivialFibrations (SimplicialPresheaf.{u} D) =
      (monomorphisms (SimplicialPresheaf.{u} D)).rlp := by
  let : ModelCategory (SimplicialPresheaf.{u} D) := q.model
  change q.model.categoryWithFibrations.fibrations ⊓
    q.model.categoryWithWeakEquivalences.weakEquivalences = _
  rw [q.fibrations_eq, q.weakEquivalences_eq, ← q.J_rlp_eq,
    q.smith.trivialFibrations_eq, q.I_right]

/-- Native standard data uses the same model, literal families and common κ. -/
def generation :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := q.model
    letI : Fact q.κ.IsRegular := q.regular
    letI : OrderBot q.κ.ord.ToType := q.bottom
    CofibrantGenerationData (SimplicialPresheaf.{u} D) q.κ := by
  letI : ModelCategory (SimplicialPresheaf.{u} D) := q.model
  letI : Fact q.κ.IsRegular := q.regular
  letI : OrderBot q.κ.ord.ToType := q.bottom
  exact
    { I := q.I
      J := q.smith.J
      I_smallObject := q.I_eligible
      J_smallObject := q.J_eligible
      I_rlp := q.I_right.trans q.trivialFibrations_eq.symm
      J_rlp := q.J_rlp_eq.trans q.fibrations_eq.symm }

/-- The native first-family factorization at the common cardinal, preserving
all original objects and maps when identifying its two classes. -/
def cofibrationFactorization : FunctorialFactorizationData
    (monomorphisms (SimplicialPresheaf.{u} D))
    (monomorphisms (SimplicialPresheaf.{u} D)).rlp := by
  letI : Fact q.κ.IsRegular := q.regular
  letI : OrderBot q.κ.ord.ToType := q.bottom
  letI : q.I.IsCardinalForSmallObjectArgument q.κ := q.I_eligible
  letI : LocallySmall.{u} (SimplicialPresheaf.{u} D) := q.I_eligible.locallySmall
  exact (SmallObject.functorialFactorizationData q.I q.κ).ofLE
    q.I_left.le q.I_right.le

/-- The native Smith-family factorization at that same common cardinal. -/
def trivialCofibrationFactorization : FunctorialFactorizationData
    (trivialMonomorphisms.{u} D) (injectiveFibrations D) := by
  letI : Fact q.κ.IsRegular := q.regular
  letI : OrderBot q.κ.ord.ToType := q.bottom
  letI : q.smith.J.IsCardinalForSmallObjectArgument q.κ := q.J_eligible
  letI : LocallySmall.{u} (SimplicialPresheaf.{u} D) := q.J_eligible.locallySmall
  exact (SmallObject.functorialFactorizationData q.smith.J q.κ).ofLE
    q.J_left_eq.le q.J_rlp_eq.le

theorem all_cofibrant :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := q.model
    ∀ X : SimplicialPresheaf.{u} D, IsCofibrant X := by
  let : ModelCategory (SimplicialPresheaf.{u} D) := q.model
  intro X
  rw [isCofibrant_iff, cofibration_iff]
  change q.model.categoryWithCofibrations.cofibrations (initial.to X)
  rw [q.cofibrations_eq]
  apply (NatTrans.mono_iff_mono_app (initial.to X)).mpr
  intro d
  let ev := (evaluation Dᵒᵖ SSet.{u}).obj d
  have hinit : IsInitial (ev.obj (⊥_ SimplicialPresheaf.{u} D)) :=
    initialIsInitial.isInitialObj ev (⊥_ SimplicialPresheaf.{u} D)
  let e : ev.obj (⊥_ SimplicialPresheaf.{u} D) ≅ ⊥_ SSet.{u} :=
    hinit.uniqueUpToIso initialIsInitial
  have heq : (initial.to X).app d = e.hom ≫ initial.to (X.obj d) :=
    hinit.hom_ext _ _
  rw [heq]
  infer_instance

end Data

section SmallSites

variable [Small.{u} D] [LocallySmall.{u} D]

/-- All data is constructed from the original site alone. No endpoint,
generating-family, weak-accessibility, Smith, WFS or model input is supplied. -/
private theorem exists_data : Nonempty (Data.{u} D) := by
  let : LocallySmall.{u} (SimplicialPresheaf.{u} D) := SimplicialPresheaf.locallySmall
  let : IsLocallyPresentable.{u} (SimplicialPresheaf.{u} D) :=
    SimplicialPresheaf.isLocallyPresentable
  obtain ⟨K, F, κ₀, hκ₀, hbot₀, hG1⟩ :=
    SimplicialPresheaf.exists_monomorphism_generators (D := D)
  let : Fact κ₀.IsRegular := hκ₀
  let : OrderBot κ₀.ord.ToType := hbot₀
  obtain ⟨hbound, hF, hcover, hEndpoints, hSmall, hIκ₀, hSOA,
    hleft, hright, hWFS, hFF⟩ := hG1
  let I := ofHoms (fun k => (F k).hom)
  let : I.HasSmallObjectArgument.{u} := hSOA
  let hSmith := smithInput D I hleft hright
  obtain ⟨s⟩ := smithRecognition I (objectwiseKanWeakEquivalences D) hSmith
  let : s.J.HasSmallObjectArgument.{u} := s.J_smallObject
  let : HasFiniteLimits (SimplicialPresheaf.{u} D) := inferInstance
  let : HasFiniteColimits (SimplicialPresheaf.{u} D) := inferInstance
  let : CategoryWithCofibrations (SimplicialPresheaf.{u} D) :=
    ⟨monomorphisms (SimplicialPresheaf.{u} D)⟩
  let : CategoryWithWeakEquivalences (SimplicialPresheaf.{u} D) :=
    ⟨objectwiseKanWeakEquivalences D⟩
  let : CategoryWithFibrations (SimplicialPresheaf.{u} D) :=
    ⟨injectiveFibrations D⟩
  let M : ModelCategory (SimplicialPresheaf.{u} D) :=
    s.modelCategory (by infer_instance) (by
      change monomorphisms (SimplicialPresheaf.{u} D) = I.rlp.llp
      exact hleft.symm) (by
      change injectiveFibrations D = s.J.rlp
      rw [s.fibrations_eq, hleft]
      rfl) rfl
  obtain ⟨κ, hκ, hbot, hLP, hIκ, hJκ⟩ := exists_common_generation_cardinal I s.J
  exact ⟨{
    index := K
    F := F
    I_smallObject := hSOA
    I_left := hleft
    I_right := hright
    smith := s
    model := M
    cofibrations_eq := rfl
    weakEquivalences_eq := rfl
    fibrations_eq := rfl
    κ := κ
    regular := hκ
    bottom := hbot
    locallyPresentable := hLP
    I_eligible := hIκ
    J_eligible := hJκ }⟩

/-- Select one full package for the original site. Every named accessor and
the full existence theorem below use this same choice. -/
def data : Data.{u} D := (exists_data D).some

/-- The full original native-type contract, obtained from one constructed package. -/
theorem exists_injectiveKanModel :
    let C := SimplicialPresheaf.{u} D
    let W := objectwiseKanWeakEquivalences.{u} D
    let Monos := monomorphisms C
    let T := trivialMonomorphisms.{u} D
    let Fib := injectiveFibrations.{u} D
    ∃ (K : Type u) (F : K → Arrow C),
      let I := ofHoms (fun k => (F k).hom)
      ∃ (s : SmithModelStructureData.{u} (C := C) I W) (M : ModelCategory C),
        letI : ModelCategory C := M
        ∃ (κ : Cardinal.{u}) (hκ : Fact κ.IsRegular)
          (hbot : OrderBot κ.ord.ToType),
          letI : Fact κ.IsRegular := hκ
          letI : OrderBot κ.ord.ToType := hbot
          ∃ cg : CofibrantGenerationData C κ,
            M.categoryWithCofibrations.cofibrations = Monos ∧
            M.categoryWithWeakEquivalences.weakEquivalences = W ∧
            M.categoryWithFibrations.fibrations = Fib ∧
            trivialCofibrations C = T ∧
            trivialFibrations C = Monos.rlp ∧
            I.rlp = Monos.rlp ∧
            s.J.rlp = Fib ∧ s.J.rlp.llp = T ∧ s.J.rlp ⊓ W = I.rlp ∧
            IsWeakFactorizationSystem Monos Monos.rlp ∧
            IsWeakFactorizationSystem T Fib ∧
            Nonempty (FunctorialFactorizationData Monos Monos.rlp) ∧
            Nonempty (FunctorialFactorizationData T Fib) ∧
            I.IsSmall.{u} ∧ s.J.IsSmall.{u} ∧
            I.HasSmallObjectArgument.{u} ∧ s.J.HasSmallObjectArgument.{u} ∧
            IsCardinalLocallyPresentable C κ ∧
            I.IsCardinalForSmallObjectArgument κ ∧
            s.J.IsCardinalForSmallObjectArgument κ ∧
            cg.I = I ∧ cg.J = s.J ∧ ∀ X : C, IsCofibrant X := by
  let q := data D
  let : ModelCategory (SimplicialPresheaf.{u} D) := q.model
  let : Fact q.κ.IsRegular := q.regular
  let : OrderBot q.κ.ord.ToType := q.bottom
  refine ⟨q.index, q.F, q.smith, q.model, q.κ, q.regular, q.bottom,
    q.generation, q.cofibrations_eq, q.weakEquivalences_eq, q.fibrations_eq,
    q.trivialCofibrations_eq, q.trivialFibrations_eq, q.I_right,
    q.J_rlp_eq, q.J_left_eq, q.smith.trivialFibrations_eq,
    q.cofibration_wfs, q.trivialCofibration_wfs,
    ⟨q.cofibrationFactorization⟩, ⟨q.trivialCofibrationFactorization⟩,
    q.I_eligible.isSmall, q.J_eligible.isSmall,
    q.I_smallObject, q.smith.J_smallObject, q.locallyPresentable,
    q.I_eligible, q.J_eligible, rfl, rfl, q.all_cofibrant⟩

/-- Opt-in named actual model on the original presheaf carrier. -/
@[instance_reducible]
def modelCategory : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model

end SmallSites

end SimplicialPresheaf.InjectiveKan
