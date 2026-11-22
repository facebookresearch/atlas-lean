/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OperatorStabilizationK
public import MathlibExt.AlgebraicTopology.ModelCategory.EvaluationTransfer
public import MathlibExt.CategoryTheory.Operad.FinBijCard
public import Mathlib.Data.PNat.Basic

/-!
# Positive one-step native symmetric stabilization sources

The free horn indices and the one-step stabilization labels are both positive.
The additional arrows are the original scalar-boundary pushout products with
the original native mapping-cylinder source. All source bounds use the actual
continuous closed diagram and the original realized-generator cardinal.

The positive native level model and its generation data are derived here.
The one-step K bank uses the original unit/S¹ lambda arrows and retains their
actual positive free endpoints. Its raw right class and terminal Omega tests
are proved. The full Hovey zeta family at both generating-I coefficient
endpoints, its derived locality and a positive stable model remain separate
results. No result for arbitrary Day coefficients or the distinct nested A8
module category is asserted here.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.MorphismProperty CategoryTheory.EnrichedFunctorCat
open CategoryTheory.BraidedCategory
open Topology
open scoped CGWH.modelCategory MonoidalClosed Cardinal Simplicial

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
namespace NativePositiveK

private instance originalCardinalRegular : Fact realizedGeneratorCardinal.{v}.IsRegular :=
  ⟨isRegular_realizedGeneratorCardinal⟩

variable {I P L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (index : P → I) (s : NativeStabilizationFamily.{u, v} I L)

/-- Restrict the original free-object labels, keeping the original full free maps. -/
def levelGenerators (K : MorphismProperty PointedCGWH.{u, v}) :
    MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  adjointFamilyGenerators (fun a : P => Free.functor (index a)) K

/-- Tests at exactly the retained original operator objects. -/
def levelProperty (K : MorphismProperty PointedCGWH.{u, v}) :
    MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  EvaluationTransfer.evaluationProperty (fun a : P => evaluation (index a)) K

/-- The retained free boundaries; positivity is supplied by the actual index map. -/
abbrev levelI := levelGenerators index PointedCGWH.realizedBoundaryInclusions.{u, v}

/-- The retained free horns, with the same restriction as the free boundaries. -/
abbrev levelJ := levelGenerators index PointedCGWH.realizedHornInclusions.{u, v}

/-- Both summands are literal: restricted free horns and retained original extra maps. -/
def generators : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  levelJ index ⊔ NativeK.additionalGenerators s

/-- The full retained property is evaluated at every retained index and nowhere else. -/
theorem levelProperty_iff (K : MorphismProperty PointedCGWH.{u, v})
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    levelProperty index K f ↔ ∀ a : P, K (component f (index a)) :=
  EvaluationTransfer.evaluationProperty_iff _ _ f

/-- The original free/evaluation adjunction computes the entire restricted right class. -/
theorem levelGenerators_rlp_eq (K : MorphismProperty PointedCGWH.{u, v}) :
    (levelGenerators index K).rlp = levelProperty index K.rlp :=
  EvaluationTransfer.evaluatedGenerators_rlp_eq
    (fun a : P => Free.functor (index a))
    (fun a : P => evaluation (index a)) (fun a => Free.adjunction (index a)) K

/-- Restriction preserves each complete original free arrow. -/
theorem levelGenerators_le_ordinary (K : MorphismProperty PointedCGWH.{u, v}) :
    levelGenerators index K ≤ HomotopicalAlgebra.EnrichedProjective.generators (A := I) K := by
  intro X Y f hf
  obtain ⟨q, hq⟩ := (adjointFamilyGenerators_iff _ _ f).mp hf
  exact (adjointFamilyGenerators_iff _ _ f).mpr ⟨⟨index q.1, q.2⟩, hq⟩

/-- The native horn dictionary gives precisely the retained level fibration tests. -/
theorem levelJ_rlp_eq : (levelJ index).rlp =
    levelProperty index (fibrations PointedCGWH.{u, v}) := by
  rw [levelJ, levelGenerators_rlp_eq]
  exact congrArg (levelProperty index)
    (show PointedCGWH.realizedHornInclusions.{u, v}.rlp =
      fibrations PointedCGWH.{u, v} from PointedCGWH.cofibrantGenerationData.J_rlp)

/-- The native boundary dictionary gives precisely the retained trivial fibration tests. -/
theorem levelI_rlp_eq : (levelI index).rlp =
    levelProperty index (trivialFibrations PointedCGWH.{u, v}) := by
  rw [levelI, levelGenerators_rlp_eq]
  exact congrArg (levelProperty index)
    (show PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp =
      trivialFibrations PointedCGWH.{u, v} from PointedCGWH.cofibrantGenerationData.I_rlp)

/-- Both original generator summands remain separate membership alternatives. -/
theorem generators_iff {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    generators index s f ↔ levelJ index f ∨ NativeK.additionalGenerators s f :=
  MorphismProperty.sup_iff _ _ _

/-- Every retained original cylinder/boundary arrow belongs to this same bank. -/
theorem generatorMap_mem (l : L) (m : ℕ) :
    generators index s (NativeK.generatorMap s l m) :=
  (generators_iff index s _).mpr (Or.inr (NativeK.generatorMap_mem s l m))

/-- Both restrictions give a subfamily of the full original native bank. -/
theorem generators_le_ordinary : generators index s ≤ NativeK.generators s :=
  sup_le_sup (levelGenerators_le_ordinary index _) le_rfl

/-- Full right lifting retains the restricted horn tests and every original full corner. -/
theorem lifting_iff {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (p : X ⟶ Y) :
    (generators index s).rlp p ↔
      (∀ a : P, fibrations PointedCGWH.{u, v} (component p (index a))) ∧
        ∀ l : L, trivialFibrations PointedCGWH.{u, v}
          (PointedCGWH.NativeMappingCorner.square (NativeK.cylinderSource s l) p).π := by
  constructor
  · intro hp
    refine ⟨?_, fun l => (NativeK.boundary_lifting_iff _).mp (fun m => ?_)⟩
    · have hJ : (levelJ index).rlp p :=
        fun _ _ i hi => hp i ((generators_iff index s _).mpr (Or.inl hi))
      rw [levelJ_rlp_eq] at hJ
      exact (levelProperty_iff index _ p).mp hJ
    · exact (NativeK.generatorMap_lifting_iff s l m p).mp
        (hp _ (generatorMap_mem index s l m))
  · rintro ⟨hLevel, hCorner⟩ A C i hi
    rcases (generators_iff index s i).mp hi with hJ | hExtra
    · have hp : (levelJ index).rlp p := by
        rw [levelJ_rlp_eq]
        exact (levelProperty_iff index _ p).mpr hLevel
      exact hp i hJ
    · obtain ⟨⟨l, m⟩⟩ := hExtra
      exact (NativeK.generatorMap_lifting_iff s l m p).mpr
        ((NativeK.boundary_lifting_iff _).mpr (hCorner l) m)

section OriginalCardinal

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The actual restricted bank still consists of original native projective cofibrations. -/
theorem generators_le_cofibrations : generators index s ≤
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  (generators_le_ordinary index s).trans (NativeK.generators_le_cofibrations s)

/-- Every retained cell transition is closed at every original operator evaluation. -/
theorem cellTransition_closedEmbedding
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) => (generators index s).homFamily) f)
    {a b : realizedGeneratorCardinal.{v}.ord.ToType} (φ : a ⟶ b) (i : I) :
    IsClosedEmbedding (ConcreteCategory.hom (component (c.F.map φ) i).right) := by
  let _ : (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)).IsStableUnderCoproducts.{v} :=
    IsStableUnderCoproducts.of_llp_eq _ _ (trivialFibrations_llp _)
  let _ : (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)).IsStableUnderTransfiniteComposition.{v} := by
    rw [← trivialFibrations_llp]
    infer_instance
  let _ : PreservesWellOrderContinuousOfShape realizedGeneratorCardinal.{v}.ord.ToType
      (𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I)) :=
    ⟨fun _ _ => by infer_instance⟩
  have hC : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) (c.F.map φ) :=
    c.map_map_mem_of_le (𝟭 _) (generators index s) (cofibrations _)
      (generators_le_cofibrations index s) φ
  exact NativeK.cofibration_component_closedEmbedding _ hC i

/-- Source Hom for both restricted summands uses the caller's exact original closed chain. -/
theorem generatorsSource_preservesClosedColimit
    {A C : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : A ⟶ C)
    (hf : generators index s f)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ i : I, ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (component (E.map φ) i).right)) :
    PreservesColimit E (coyoneda.obj (Opposite.op A)) :=
  NativeK.generatorsSource_preservesClosedColimit s f
    (generators_le_ordinary index s f hf) E hE

/-- Literal additional-generator targets retain the original cylinder tensor and Hom theorem. -/
theorem generatorTarget_preservesClosedColimit (l : L) (m : ℕ)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ i : I, ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (component (E.map φ) i).right)) :
    PreservesColimit E
      (coyoneda.obj (Opposite.op (CategoryTheory.Arrow.mk (NativeK.generatorMap s l m)).right)) :=
  NativeK.generatorTarget_preservesClosedColimit s l m E hE

/-- Smallness is inherited by the actual subset, rather than by replacing its arrows. -/
theorem generators_isSmall : (generators index s).IsSmall.{v} := by
  let _ : (NativeK.generators s).IsSmall.{v} := NativeK.generators_isSmall s
  let j : (generators index s).toSet → (NativeK.generators s).toSet :=
    fun f => ⟨f.1, generators_le_ordinary index s f.1.hom f.2⟩
  have hj : Function.Injective j := by
    intro f g h
    apply Subtype.ext
    exact congrArg (fun x : (NativeK.generators s).toSet => x.val) h
  exact ⟨small_of_injective hj⟩

/-- All six eligibility fields are derived at the original cardinal and caller bottom. -/
theorem generators_isCardinalForSmallObjectArgument :
    (generators index s).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} := by
  let d := NativeK.generators_isCardinalForSmallObjectArgument s
  refine { isSmall := generators_isSmall index s
           locallySmall := d.locallySmall
           hasPushouts := d.hasPushouts
           hasCoproducts := d.hasCoproducts
           hasIterationOfShape := d.hasIterationOfShape
           preservesColimit := ?_ }
  intro A C X Y i hi f c
  let _ : c.F.IsWellOrderContinuous :=
    c.toTransfiniteCompositionOfShape.isWellOrderContinuous
  exact generatorsSource_preservesClosedColimit index s i hi c.F
    (fun a _ _ φ => cellTransition_closedEmbedding index s f c φ a)

attribute [local instance] generators_isCardinalForSmallObjectArgument

/-- The retained bank uses the original small-object algorithm at the same native cardinal. -/
def factorizationData :
    FunctorialFactorizationData (generators index s).rlp.llp (generators index s).rlp :=
  SmallObject.functorialFactorizationData (generators index s) realizedGeneratorCardinal.{v}

/-- Every actual intermediate object and both natural maps are the original SOA functions. -/
theorem factorizationData_fields :
    let original := SmallObject.functorialFactorizationData
      (generators index s) realizedGeneratorCardinal.{v}
    (factorizationData index s).Z = original.Z ∧
      (factorizationData index s).i = original.i ∧
      (factorizationData index s).p = original.p := ⟨rfl, rfl, rfl⟩

/-- Every whole caller Arrow preserves the same original intermediate object. -/
theorem factorizationData_Z_obj
    (f : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (factorizationData index s).Z.obj f =
      SmallObject.obj (generators index s) realizedGeneratorCardinal.{v} f.hom := rfl

/-- The complete middle functor retains the original map on every Arrow square. -/
theorem factorizationData_Z_map
    {f g : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (φ : f ⟶ g) :
    (factorizationData index s).Z.map φ =
      SmallObject.objMap (generators index s) realizedGeneratorCardinal.{v} φ := rfl

/-- The full original small-object injection is retained. -/
theorem factorizationData_i_app
    (f : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (factorizationData index s).i.app f =
      SmallObject.ιObj (generators index s) realizedGeneratorCardinal.{v} f.hom := rfl

/-- The full original small-object projection is retained. -/
theorem factorizationData_p_app
    (f : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (factorizationData index s).p.app f =
      SmallObject.πObj (generators index s) realizedGeneratorCardinal.{v} f.hom := rfl

/-- Both original factors compose to exactly the same full caller Arrow. -/
theorem factorizationData_fac
    (f : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (factorizationData index s).i.app f ≫ (factorizationData index s).p.app f = f.hom :=
  (factorizationData index s).fac_app

/-- The generated WFS is obtained from the same produced small-object data. -/
theorem weakFactorizationSystem :
    IsWeakFactorizationSystem (generators index s).rlp.llp (generators index s).rlp := by
  let _ : HasFunctorialFactorization (generators index s).rlp.llp (generators index s).rlp :=
    ⟨⟨factorizationData index s⟩⟩
  exact IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp => hi p hp)

/-- Terminal lifting tests the actual retained adjoints, without any removed free-object tests. -/
theorem lifting_toZero_iff_isOmega (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (generators index s).rlp (Diagrams.toZero E) ↔ NativeK.IsOmega s E := by
  rw [lifting_iff]
  have hLevel : ∀ a : P, fibrations PointedCGWH.{u, v}
      (component (Diagrams.toZero E) (index a)) := by
    have hE : fibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) (Diagrams.toZero E) := by
      let _ : IsFibrant E := HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant E
      exact (HomotopicalAlgebra.fibration_iff _).mp
        ((isFibrant_iff_of_isTerminal (Diagrams.toZero E) Diagrams.zeroDiagramIsTerminal).mp
          inferInstance)
    rw [HomotopicalAlgebra.EnrichedProjective.Native.fibrations_eq] at hE
    exact fun a => (EvaluationTransfer.evaluationProperty_iff _ _ _).mp hE (index a)
  rw [and_iff_right hLevel]
  exact ⟨fun h l => (NativeK.zeroCorner_trivialFibration_iff s l E).mp (h l),
    fun h l => (NativeK.zeroCorner_trivialFibration_iff s l E).mpr (h l)⟩


/-- Both endpoints of every literal retained free boundary preserve the same supplied chain. -/
theorem boundaryFreeEndpoints_preservesClosedColimit (a : P) (m : ℕ)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ i : I, ∀ ⦃x y⦄ (φ : x ⟶ y),
      IsClosedEmbedding (ConcreteCategory.hom (component (E.map φ) i).right)) :
    PreservesColimit E (coyoneda.obj (Opposite.op
      (CategoryTheory.Arrow.mk ((Free.functor (index a)).map (NativeK.boundaryMap m))).left)) ∧
    PreservesColimit E (coyoneda.obj (Opposite.op
      (CategoryTheory.Arrow.mk ((Free.functor (index a)).map (NativeK.boundaryMap m))).right)) :=
  ⟨PointedCGWH.EnrichedSource.free_preservesClosedColimit (index a)
      (CategoryTheory.Arrow.mk (NativeK.boundaryMap m)).left (NativeK.boundary_source_mk_le m) E hE,
    PointedCGWH.EnrichedSource.free_preservesClosedColimit (index a)
      (CategoryTheory.Arrow.mk (NativeK.boundaryMap m)).right (NativeK.boundary_target_mk_le m) E hE⟩

/-- Both literal retained free-horn endpoints keep their actual finite horn/simplex bounds. -/
theorem hornFreeEndpoints_preservesClosedColimit (a : P) (m : ℕ) (j : Fin (m + 2))
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ i : I, ∀ ⦃x y⦄ (φ : x ⟶ y),
      IsClosedEmbedding (ConcreteCategory.hom (component (E.map φ) i).right)) :
    let h := (Under.costar CGWH.point.{u, v}).map (CGWH.realizedHornInclusion.{v, u} m j)
    PreservesColimit E (coyoneda.obj (Opposite.op
      (CategoryTheory.Arrow.mk ((Free.functor (index a)).map h)).left)) ∧
    PreservesColimit E (coyoneda.obj (Opposite.op
      (CategoryTheory.Arrow.mk ((Free.functor (index a)).map h)).right)) :=
  ⟨PointedCGWH.EnrichedSource.free_preservesClosedColimit (index a) _
      (NativeK.finiteCostarOfFinite_mk_le (SSet.horn.{v} (m + 1) j)) E hE,
    PointedCGWH.EnrichedSource.free_preservesClosedColimit (index a) _
      (NativeK.finiteCostarOfFinite_mk_le (Δ[m + 1] : SSet.{v})) E hE⟩

/-- The horn summand's arbitrary targets retain their original finite-simplex Hom fact. -/
theorem levelJTarget_preservesClosedColimit
    {A C : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : A ⟶ C) (hf : levelJ index f)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ i : I, ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (component (E.map φ) i).right)) :
    PreservesColimit E (coyoneda.obj (Opposite.op C)) := by
  obtain ⟨⟨a, ⟨⟨T, U, g⟩, hj⟩⟩, hq⟩ := (adjointFamilyGenerators_iff _ _ f).mp hf
  have hT : #↥U.right ≤ Cardinal.continuum := by
    change (CGWH.realizedHornInclusions.{u, v}.strictMap (Under.costar CGWH.point)) g at hj
    cases hj with
    | @map A C g hg =>
      unfold CGWH.realizedHornInclusions at hg
      rw [MorphismProperty.iSup_iff] at hg
      obtain ⟨m, ⟨j⟩⟩ := hg
      exact NativeK.finiteCostarOfFinite_mk_le (Δ[m + 1] : SSet.{v})
  let _ : PreservesColimit E
      (coyoneda.obj (Opposite.op (Free.object (index a) U))) :=
    PointedCGWH.EnrichedSource.free_preservesClosedColimit (index a) U hT E hE
  let e : C ≅ Free.object (index a) U :=
    CategoryTheory.Arrow.rightFunc.mapIso (eqToIso hq)
  exact preservesColimit_of_natIso E (coyoneda.mapIso e.op)

/-- Both codomain summands are proved on the same original continuous closed diagram. -/
theorem generatorsTarget_preservesClosedColimit
    {A C : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : A ⟶ C)
    (hf : generators index s f)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ i : I, ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (component (E.map φ) i).right)) :
    PreservesColimit E (coyoneda.obj (Opposite.op C)) := by
  rcases (generators_iff index s f).mp hf with hJ | hExtra
  · exact levelJTarget_preservesClosedColimit index f hJ E hE
  · obtain ⟨⟨l, m⟩⟩ := hExtra
    exact NativeK.generatorTarget_preservesClosedColimit s l m E hE

/-- Source and target Hom preserve the caller's actual supplied colimit cocone and its legs. -/
def generatorsEndpointsIsColimit
    {A C : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : A ⟶ C)
    (hf : generators index s f)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ i : I, ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (component (E.map φ) i).right))
    (c : Cocone E) (hc : IsColimit c) :
    IsColimit ((coyoneda.obj (Opposite.op A)).mapCocone c) ×
      IsColimit ((coyoneda.obj (Opposite.op C)).mapCocone c) := by
  let _ := generatorsSource_preservesClosedColimit index s f hf E hE
  let _ := generatorsTarget_preservesClosedColimit index s f hf E hE
  exact ⟨isColimitOfPreserves _ hc, isColimitOfPreserves _ hc⟩

private theorem retainedLevelEligible (Q : MorphismProperty PointedCGWH.{u, v})
    (d : (HomotopicalAlgebra.EnrichedProjective.generators (A := I) Q).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v}) :
    (levelGenerators index Q).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} := by
  let _ : (HomotopicalAlgebra.EnrichedProjective.generators (A := I) Q).IsSmall.{v} := d.isSmall
  let j : (levelGenerators index Q).toSet →
      (HomotopicalAlgebra.EnrichedProjective.generators (A := I) Q).toSet :=
    fun f => ⟨f.1, levelGenerators_le_ordinary index Q f.1.hom f.2⟩
  have hj : Function.Injective j := by
    intro f g h
    apply Subtype.ext
    exact congrArg
      (fun x : (HomotopicalAlgebra.EnrichedProjective.generators (A := I) Q).toSet => x.val) h
  let _ : PreservesWellOrderContinuousOfShape realizedGeneratorCardinal.{v}.ord.ToType
      (𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I)) :=
    ⟨fun _ _ => by infer_instance⟩
  refine { isSmall := ⟨small_of_injective hj⟩
           locallySmall := d.locallySmall
           hasPushouts := d.hasPushouts
           hasCoproducts := d.hasCoproducts
           hasIterationOfShape := d.hasIterationOfShape
           preservesColimit := ?_ }
  intro A C X Y i hi f c
  exact d.preservesColimit i (levelGenerators_le_ordinary index Q i hi) f
    (c.mapOfLE (𝟭 _) (levelGenerators index Q)
      (HomotopicalAlgebra.EnrichedProjective.generators (A := I) Q)
      (levelGenerators_le_ordinary index Q))

/-- The positive boundary family derives all six original eligibility fields, at the same κ. -/
theorem levelI_isCardinalForSmallObjectArgument :
    (levelI index).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
  retainedLevelEligible index PointedCGWH.realizedBoundaryInclusions
    (HomotopicalAlgebra.EnrichedProjective.Native.generatorsI_isCardinalForSmallObjectArgument (A := I))

/-- The positive horn family derives all six original eligibility fields, at the same κ. -/
theorem levelJ_isCardinalForSmallObjectArgument :
    (levelJ index).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
  retainedLevelEligible index PointedCGWH.realizedHornInclusions
    (HomotopicalAlgebra.EnrichedProjective.Native.generatorsJ_isCardinalForSmallObjectArgument (A := I))

/-- Positive J-left weakness follows from the original ordinary J-left source theorem. -/
theorem levelJ_left_weak : (levelJ index).rlp.llp ≤
    levelProperty index (weakEquivalences PointedCGWH.{u, v}) := by
  intro X Y f hf
  have ho : NativeK.levelJ (I := I).rlp.llp f :=
    antitone_llp (antitone_rlp (levelGenerators_le_ordinary index _)) f hf
  rw [← HomotopicalAlgebra.EnrichedProjective.Native.trivialCofibrations_eq] at ho
  have hw := ho.2
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq] at hw
  exact (levelProperty_iff index _ f).mpr
    (fun a => (EvaluationTransfer.evaluationProperty_iff _ _ _).mp hw (index a))

omit B in
theorem baseRightIntersection :
    PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp =
      PointedCGWH.realizedHornInclusions.{u, v}.rlp ⊓ weakEquivalences PointedCGWH.{u, v} := by
  have hI : PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp =
      trivialFibrations PointedCGWH.{u, v} := PointedCGWH.cofibrantGenerationData.I_rlp
  have hJ : PointedCGWH.realizedHornInclusions.{u, v}.rlp =
      fibrations PointedCGWH.{u, v} := PointedCGWH.cofibrantGenerationData.J_rlp
  rw [hI, hJ]
  rfl

theorem levelI_hasSmallObjectArgument : (levelI index).HasSmallObjectArgument.{v} :=
  ⟨realizedGeneratorCardinal.{v}, inferInstance, B, levelI_isCardinalForSmallObjectArgument index⟩

theorem levelJ_hasSmallObjectArgument : (levelJ index).HasSmallObjectArgument.{v} :=
  ⟨realizedGeneratorCardinal.{v}, inferInstance, B, levelJ_isCardinalForSmallObjectArgument index⟩

attribute [local instance] levelI_hasSmallObjectArgument levelJ_hasSmallObjectArgument

/-- The native retained level model is produced by the original evaluation transfer. -/
@[instance_reducible]
def levelModel : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := by
  let _ : (adjointFamilyGenerators (fun a : P => Free.functor (index a))
      PointedCGWH.realizedBoundaryInclusions.{u, v}).HasSmallObjectArgument.{v} :=
    levelI_hasSmallObjectArgument index
  let _ : (adjointFamilyGenerators (fun a : P => Free.functor (index a))
      PointedCGWH.realizedHornInclusions.{u, v}).HasSmallObjectArgument.{v} :=
    levelJ_hasSmallObjectArgument index
  exact EvaluationTransfer.evaluationProjectiveModelCategory
    (fun a : P => Free.functor (index a))
    (fun a : P => evaluation (index a)) (fun a => Free.adjunction (index a))
    PointedCGWH.realizedBoundaryInclusions PointedCGWH.realizedHornInclusions
    (weakEquivalences PointedCGWH.{u, v}) baseRightIntersection (levelJ_left_weak index)

/-- The produced model retains the literal positive weak class and generating cofibrations. -/
theorem levelModel_weak_cofibrations :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) =
      levelProperty index (weakEquivalences PointedCGWH.{u, v}) ∧
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) = (levelI index).rlp.llp :=
  ⟨rfl, rfl⟩

/-- The produced model's fibrations test precisely the retained original indices. -/
theorem levelModel_fibrations :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
    fibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) =
      levelProperty index (fibrations PointedCGWH.{u, v}) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
  change (levelJ index).rlp = _
  exact levelJ_rlp_eq index

/-- The produced positive level model has no additional fibrancy requirement at removed indices. -/
theorem levelModel_allObjectsFibrant (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
    IsFibrant E := by
  have hOrd : fibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) (Diagrams.toZero E) := by
    let _ : IsFibrant E := HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant E
    exact (HomotopicalAlgebra.fibration_iff _).mp
      ((isFibrant_iff_of_isTerminal (Diagrams.toZero E) Diagrams.zeroDiagramIsTerminal).mp
        inferInstance)
  rw [HomotopicalAlgebra.EnrichedProjective.Native.fibrations_eq] at hOrd
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
  apply (isFibrant_iff_of_isTerminal (Diagrams.toZero E) Diagrams.zeroDiagramIsTerminal).mpr
  apply (HomotopicalAlgebra.fibration_iff _).mpr
  rw [levelModel_fibrations]
  exact (levelProperty_iff index _ _).mpr
    (fun a => (EvaluationTransfer.evaluationProperty_iff _ _ _).mp hOrd (index a))

/-- Terminal K-locality also has the produced retained level-model fibrancy dictionary. -/
theorem lifting_toZero_iff_fibrantOmega (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (generators index s).rlp (Diagrams.toZero E) ↔
      (let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
       IsFibrant E) ∧ NativeK.IsOmega s E := by
  rw [and_iff_right (levelModel_allObjectsFibrant index E)]
  exact lifting_toZero_iff_isOmega index s E



/-- Both full Arrow naturality squares retain the same original factorization maps. -/
theorem factorizationData_naturality
    {f g : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (φ : f ⟶ g) :
    (factorizationData index s).i.app f ≫ (factorizationData index s).Z.map φ =
      φ.left ≫ (factorizationData index s).i.app g ∧
    (factorizationData index s).Z.map φ ≫ (factorizationData index s).p.app g =
      (factorizationData index s).p.app f ≫ φ.right :=
  ⟨((factorizationData index s).i.naturality φ).symm,
    (factorizationData index s).p.naturality φ⟩

/-- The produced original right factor satisfies precisely the retained full RLP tests. -/
theorem factorizationData_p_tests
    (f : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (∀ a : P, fibrations PointedCGWH.{u, v}
      (component ((factorizationData index s).p.app f) (index a))) ∧
      ∀ l : L, trivialFibrations PointedCGWH.{u, v}
        (PointedCGWH.NativeMappingCorner.square (NativeK.cylinderSource s l)
          ((factorizationData index s).p.app f)).π :=
  (lifting_iff index s _).mp ((factorizationData index s).hp f)

/-- Both retained level algorithms are the original fixed-cardinal small-object construction. -/
def levelIFactorizationData :
    FunctorialFactorizationData (levelI index).rlp.llp (levelI index).rlp := by
  let _ := levelI_isCardinalForSmallObjectArgument index
  exact SmallObject.functorialFactorizationData (levelI index) realizedGeneratorCardinal.{v}

/-- The retained horn algorithm uses the same fixed cardinal and caller bottom. -/
def levelJFactorizationData :
    FunctorialFactorizationData (levelJ index).rlp.llp (levelJ index).rlp := by
  let _ := levelJ_isCardinalForSmallObjectArgument index
  exact SmallObject.functorialFactorizationData (levelJ index) realizedGeneratorCardinal.{v}

/-- Both level factorization records retain their full original object, map, injection and projection functions. -/
theorem levelFactorizationData_fields
    (f : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I))
    {g h : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (φ : g ⟶ h) :
    let _ := levelI_isCardinalForSmallObjectArgument index
    let _ := levelJ_isCardinalForSmallObjectArgument index
    (levelIFactorizationData index).Z.obj f =
      SmallObject.obj (levelI index) realizedGeneratorCardinal.{v} f.hom ∧
    (levelJFactorizationData index).Z.obj f =
      SmallObject.obj (levelJ index) realizedGeneratorCardinal.{v} f.hom ∧
    (levelIFactorizationData index).Z.map φ =
      SmallObject.objMap (levelI index) realizedGeneratorCardinal.{v} φ ∧
    (levelJFactorizationData index).Z.map φ =
      SmallObject.objMap (levelJ index) realizedGeneratorCardinal.{v} φ ∧
    (levelIFactorizationData index).i.app f =
      SmallObject.ιObj (levelI index) realizedGeneratorCardinal.{v} f.hom ∧
    (levelIFactorizationData index).p.app f =
      SmallObject.πObj (levelI index) realizedGeneratorCardinal.{v} f.hom ∧
    (levelJFactorizationData index).i.app f =
      SmallObject.ιObj (levelJ index) realizedGeneratorCardinal.{v} f.hom ∧
    (levelJFactorizationData index).p.app f =
      SmallObject.πObj (levelJ index) realizedGeneratorCardinal.{v} f.hom :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩



/-- Trivial fibrations of the produced model are the original retained boundary-right class. -/
theorem levelModel_trivialFibrations :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
    trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) =
      levelProperty index (trivialFibrations PointedCGWH.{u, v}) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
  change (levelJ index).rlp ⊓ levelProperty index (weakEquivalences PointedCGWH.{u, v}) = _
  rw [levelJ_rlp_eq]
  exact (EvaluationTransfer.evaluationProperty_inf (fun a : P => evaluation (index a))
    (fibrations PointedCGWH.{u, v}) (weakEquivalences PointedCGWH.{u, v})).symm

/-- Trivial cofibrations are generated by exactly the retained horn family. -/
theorem levelModel_trivialCofibrations :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
    trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) = (levelJ index).rlp.llp := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
  exact (fibrations_llp (EnrichedFunctorCat PointedCGWH.{u, v} I)).symm

/-- The same actual positive native model carries literal I/J generation data at the original κ. -/
def levelGenerationData :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
    CofibrantGenerationData (EnrichedFunctorCat PointedCGWH.{u, v} I) realizedGeneratorCardinal.{v} := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
  refine { I := levelI index
           J := levelJ index
           I_smallObject := levelI_isCardinalForSmallObjectArgument index
           J_smallObject := levelJ_isCardinalForSmallObjectArgument index
           I_rlp := ?_
           J_rlp := rfl }
  rw [levelI_rlp_eq, levelModel_trivialFibrations]

/-- Both complete original generator properties are unchanged in the returned generation record. -/
theorem levelGenerationData_fields :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
    (levelGenerationData index).I = levelI index ∧
      (levelGenerationData index).J = levelJ index := ⟨rfl, rfl⟩



/-- Each retained original free/evaluation adjunction is Quillen for the produced retained model. -/
theorem freeAtEvaluation_isQuillenAdjunction (a : P) :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
    (Free.adjunction (V := PointedCGWH.{u, v}) (index a)).IsQuillenAdjunction := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
  apply CategoryTheory.Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y f hf
    rw [levelModel_fibrations] at hf
    exact (levelProperty_iff index _ _).mp hf a
  · intro X Y f hf
    rw [levelModel_trivialFibrations] at hf
    exact (levelProperty_iff index _ _).mp hf a

/-- A genuinely cofibrant coefficient gives a positive free cofibrant object at a retained index. -/
theorem freeCoefficient_cofibrant (a : P) (T : PointedCGWH.{u, v}) [IsCofibrant T] :
    let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
    IsCofibrant (Free.object (index a) T) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := levelModel index
  let _ : (Free.adjunction (V := PointedCGWH.{u, v}) (index a)).IsQuillenAdjunction :=
    freeAtEvaluation_isQuillenAdjunction index a
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := Free.adjunction (V := PointedCGWH.{u, v}) (index a)) inferInstance


end OriginalCardinal

end NativePositiveK

namespace ActualPositive

open CategoryTheory.Operad.SmallFinBijGroupoid

/-- The actual original free-object index, restricted to strictly positive cardinalities. -/
def index (n : ℕ+) : PointedCGWH.SymmetricOperatorIndex.{u, v} :=
  PointedCGWH.symmetricOperatorObj (card n)

/-- The original one-step labels, restricted independently to n > 0. -/
def oneStepFamily : NativeStabilizationFamily.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v} ℕ+ where
  source n := Actual.symmetricFamily.source (card n, card 1)
  target n := Actual.symmetricFamily.target (card n, card 1)
  coefficient n := Actual.symmetricFamily.coefficient (card n, card 1)
  inclusion n := Actual.symmetricFamily.inclusion (card n, card 1)
  coefficient_cofibrant n := Actual.symmetricFamily.coefficient_cofibrant (card n, card 1)
  coefficient_bound n := Actual.symmetricFamily.coefficient_bound (card n, card 1)

/-- Literal positive free boundaries on the original native symmetric carrier. -/
abbrev levelI := NativePositiveK.levelI index.{u, v}

/-- Literal positive free horns on that same original carrier. -/
abbrev levelJ := NativePositiveK.levelJ index.{u, v}

/-- The genuine positive one-step bank restricts both original summands. -/
abbrev K := NativePositiveK.generators index.{u, v} oneStepFamily.{u, v}

/-- Each source is the retained n-th object; each target is the original n tensor 1 object. -/
theorem oneStepFamily_objects (n : ℕ+) :
    oneStepFamily.{u, v}.source n = PointedCGWH.symmetricOperatorObj (card n) ∧
      oneStepFamily.target n = PointedCGWH.symmetricOperatorObj (card n ⊗ card 1) :=
  ⟨rfl, rfl⟩

/-- The coefficient is the actual native ordered one-sphere and its original block-braid inclusion. -/
theorem oneStepFamily_coefficient_inclusion (n : ℕ+) :
    oneStepFamily.{u, v}.coefficient n = PointedCGWH.sphereSequence.functor.obj (card 1) ∧
      oneStepFamily.inclusion n =
        PointedCGWH.SymmetricModulePresentation.operatorGenerator (card 1) (card n)
          (card n ⊗ card 1) (β_ (card 1) (card n)).hom := ⟨rfl, rfl⟩

/-- The same original free stabilization map is retained, with its original degree and braid. -/
theorem stabilization_original (n : ℕ+) :
    NativeK.stabilization oneStepFamily.{u, v} n =
      NativeK.stabilization Actual.symmetricFamily (card n, card 1) := rfl

/-- Both positive restrictions are visible in the full right-class formula. -/
theorem lifting_iff {X Y : Actual.SymmetricCarrier.{u, v}} (p : X ⟶ Y) :
    K.rlp p ↔
      (∀ n : ℕ, 0 < n → fibrations PointedCGWH.{u, v}
        (component p (PointedCGWH.symmetricOperatorObj (card n)))) ∧
      ∀ n : ℕ+, trivialFibrations PointedCGWH.{u, v}
        (PointedCGWH.NativeMappingCorner.square (NativeK.cylinderSource oneStepFamily n) p).π := by
  rw [NativePositiveK.lifting_iff]
  exact ⟨fun h => ⟨fun n hn => h.1 ⟨n, hn⟩, h.2⟩,
    fun h => ⟨fun n => h.1 n n.2, h.2⟩⟩


/-- The actual one-step coefficient remains the original ordered circle smash power. -/
theorem oneStepFamily_coefficient (n : ℕ+) :
    oneStepFamily.{u, v}.coefficient n =
      MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} 1 := rfl

/-- Both original native degrees are positive, and the target retains the original block sum. -/
theorem oneStep_degrees (n : ℕ+) :
    0 < (card (n : ℕ)).of.len ∧
      (card (n : ℕ) ⊗ card 1).of.len = (n : ℕ) + 1 := ⟨n.2, rfl⟩

/-- All three original mapping-cylinder functions are retained literally. -/
theorem cylinder_original (n : ℕ+) :
    NativeK.cylinder oneStepFamily.{u, v} n =
      NativeK.cylinder Actual.symmetricFamily.{u, v} (card n, card 1) ∧
    CategoryTheory.Arrow.mk (NativeK.cylinderSource oneStepFamily.{u, v} n) =
      CategoryTheory.Arrow.mk (NativeK.cylinderSource Actual.symmetricFamily.{u, v} (card n, card 1)) ∧
    CategoryTheory.Arrow.mk (NativeK.cylinderRetraction oneStepFamily.{u, v} n) =
      CategoryTheory.Arrow.mk (NativeK.cylinderRetraction Actual.symmetricFamily.{u, v} (card n, card 1)) := by
  have h := congrArg CategoryTheory.Arrow.mk (stabilization_original.{u, v} n)
  exact ⟨congrArg PointedCGWH.EnrichedIntervalMappingCylinder.object h,
    congrArg (fun f : CategoryTheory.Arrow Actual.SymmetricCarrier.{u, v} =>
      CategoryTheory.Arrow.mk (PointedCGWH.EnrichedIntervalMappingCylinder.source f)) h,
    congrArg (fun f : CategoryTheory.Arrow Actual.SymmetricCarrier.{u, v} =>
      CategoryTheory.Arrow.mk (PointedCGWH.EnrichedIntervalMappingCylinder.retraction f)) h⟩

/-- The full original scalar-boundary pushout square and its full output arrow are retained. -/
theorem generator_original (n : ℕ+) (m : ℕ) :
    (⟨CategoryTheory.Arrow.mk (NativeK.stabilization oneStepFamily.{u, v} n),
        NativeK.generatorSquare oneStepFamily.{u, v} n m⟩ :
      Σ f : CategoryTheory.Arrow Actual.SymmetricCarrier.{u, v},
        WeightedEndVariance.tensorBifunctor.PushoutObjObj (NativeK.boundaryMap m)
          (PointedCGWH.EnrichedIntervalMappingCylinder.source f)) =
      ⟨CategoryTheory.Arrow.mk (NativeK.stabilization Actual.symmetricFamily.{u, v} (card n, card 1)),
        NativeK.generatorSquare Actual.symmetricFamily.{u, v} (card n, card 1) m⟩ ∧
    CategoryTheory.Arrow.mk (NativeK.generatorMap oneStepFamily.{u, v} n m) =
      CategoryTheory.Arrow.mk (NativeK.generatorMap Actual.symmetricFamily.{u, v} (card n, card 1) m) := by
  have h := congrArg CategoryTheory.Arrow.mk (stabilization_original.{u, v} n)
  exact ⟨congrArg (fun f : CategoryTheory.Arrow Actual.SymmetricCarrier.{u, v} =>
      (⟨f, Functor.PushoutObjObj.ofHasPushout WeightedEndVariance.tensorBifunctor
          (NativeK.boundaryMap m) (PointedCGWH.EnrichedIntervalMappingCylinder.source f)⟩ :
        Σ g : CategoryTheory.Arrow Actual.SymmetricCarrier.{u, v},
          WeightedEndVariance.tensorBifunctor.PushoutObjObj (NativeK.boundaryMap m)
            (PointedCGWH.EnrichedIntervalMappingCylinder.source g))) h,
    congrArg (fun f : CategoryTheory.Arrow Actual.SymmetricCarrier.{u, v} =>
      CategoryTheory.Arrow.mk (Functor.PushoutObjObj.ofHasPushout
        WeightedEndVariance.tensorBifunctor (NativeK.boundaryMap m)
        (PointedCGWH.EnrichedIntervalMappingCylinder.source f)).ι) h⟩

/-- The original operator adjoint is retained as an entire morphism. -/
theorem adjoint_original (n : ℕ+) (X : Actual.SymmetricCarrier.{u, v}) :
    NativeK.adjoint oneStepFamily n X =
      NativeK.adjoint Actual.symmetricFamily (card n, card 1) X := rfl

/-- Positive Omega tests use the actual original one-step adjoints at n > 0. -/
def IsOmega (X : Actual.SymmetricCarrier.{u, v}) : Prop :=
  ∀ n : ℕ, 0 < n → weakEquivalences PointedCGWH.{u, v}
    (NativeK.adjoint Actual.symmetricFamily (card n, card 1) X)

/-- The retained family condition is exactly the positive original operator condition. -/
theorem isOmega_iff (X : Actual.SymmetricCarrier.{u, v}) :
    NativeK.IsOmega oneStepFamily X ↔ IsOmega X :=
  ⟨fun h n hn => h ⟨n, hn⟩, fun h n => h n n.2⟩

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The positive native level model is constructed from its actual I/J source proofs. -/
abbrev levelModel := NativePositiveK.levelModel index.{u, v}

/-- The actual positive native model keeps its literal I/J generation record at κ. -/
abbrev generationData := NativePositiveK.levelGenerationData index.{u, v}

/-- Terminal RLP is precisely the actual positive one-step Omega class. -/
theorem K_local_iff_isOmega (X : Actual.SymmetricCarrier.{u, v}) :
    K.rlp (Diagrams.toZero X) ↔ IsOmega X :=
  (NativePositiveK.lifting_toZero_iff_isOmega index oneStepFamily X).trans (isOmega_iff X)

/-- All positive K source eligibility fields are produced at the original native cardinal. -/
theorem K_isCardinalForSmallObjectArgument :
    K.{u, v}.IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
  NativePositiveK.generators_isCardinalForSmallObjectArgument index oneStepFamily

/-- The actual positive algorithm keeps all original Arrow inputs and both small-object factors. -/
abbrev factorizationData := NativePositiveK.factorizationData index.{u, v} oneStepFamily.{u, v}

/-- The actual original one-step free source and free target are cofibrant in the positive level model. -/
theorem stabilization_cofibrant_endpoints (n : ℕ+) :
    let _ : ModelCategory Actual.SymmetricCarrier.{u, v} := levelModel
    IsCofibrant (CategoryTheory.Arrow.mk (NativeK.stabilization oneStepFamily.{u, v} n)).left ∧
      IsCofibrant (CategoryTheory.Arrow.mk (NativeK.stabilization oneStepFamily.{u, v} n)).right := by
  let _ : ModelCategory Actual.SymmetricCarrier.{u, v} := levelModel
  constructor
  · let _ : IsCofibrant (oneStepFamily.{u, v}.coefficient n) := oneStepFamily.coefficient_cofibrant n
    change IsCofibrant (Free.object (index ⟨(n : ℕ) + 1, Nat.zero_lt_succ (n : ℕ)⟩)
      (oneStepFamily.coefficient n))
    exact NativePositiveK.freeCoefficient_cofibrant index _ _
  · let _ : IsCofibrant (𝟙_ PointedCGWH.{u, v}) := PointedCGWH.modelCategory.smashUnit_isCofibrant
    exact NativePositiveK.freeCoefficient_cofibrant index n _


end ActualPositive
end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
