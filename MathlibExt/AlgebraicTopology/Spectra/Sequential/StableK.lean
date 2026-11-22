/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StabilizationCylinder
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationK
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StabilizationMappingNormalization
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSphereOne
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeIntervalBoundaryModel
import MathlibExt.Topology.Category.PointedCGWH.NativeMappingCorner

/-!
# The literal correlated native stable K family

The additional generators are the actual scalar pushout-products of each
original pointed boundary with each original stabilization mapping-cylinder
source. The original native level free-J family is retained as the other
summand. The entire family consists of original native cofibrations.
Full Arrow lifting against each member is the genuine coefficient lifting
against its original mapping pullback corner. No K/SOA/locality dictionary
or desired acyclicity is supplied.

## Source and native generating-family convention

The primary reference is Mandell, May, Schwede and Shipley, *Model Categories
of Diagram Spectra*, author version of December 30, 1999:
https://www.math.uchicago.edu/~may/PAPERS/mmssLMSDec30.pdf.
Definition 9.3 (printed p. 29) constructs K using the generating families of
Definition 6.2 (printed p. 19), based disk boundaries and disk cylinders.
The project uses its fixed freely pointed realized simplicial boundaries
and horns as the native I and J. The correlated scalar/cylinder construction
here follows Definition 9.3 with those project families. References to
"original" or "literal" below concern these fixed native maps, labels,
cardinal and factorization choices. Comparison with the printed generating
families and their chosen factorizations is a separate mathematical result.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open CategoryTheory.EnrichedFunctorCat.ScalarLeibniz
open PointedCGWH.EnrichedFunctorMapping
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.SequentialSpectrum.StableK

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private abbrev familyIndex :=
  CategoryTheory.Spectra.Sequential.Index PointedCGWH.sphereOne.{u, v}

private abbrev familyDegree (n : ℕ) :=
  CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne.{u, v} n

private abbrev familySuccessorIso (n : ℕ) :=
  CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso
    PointedCGWH.sphereOne.{u, v} n

/-- The one shared native sequential family retains the original sphere and successor inclusion. -/
def stabilizationFamily : NativeStabilizationFamily.{u, v} familyIndex ℕ where
  source n := familyDegree n
  target n := familyDegree (n + 1)
  coefficient _ := PointedCGWH.sphereOne
  inclusion n := (familySuccessorIso n).inv
  coefficient_cofibrant _ := PointedCGWH.modelCategory.sphereOne_isCofibrant
  coefficient_bound _ := PointedCGWH.CoefficientCardinal.sphereOne_mk_le

/-- Equality is proved through the original whole Free adjunct, without choosing another map. -/
theorem stabilizationFamily_stabilization_eq_unitStabilizationMap (n : ℕ) :
    NativeK.stabilization.{u, v} stabilizationFamily n =
      unitStabilizationMap PointedCGWH.sphereOne.{u, v} n := by
  apply ((freeAtEvaluationAdjunction PointedCGWH.sphereOne (n + 1)).homEquiv
    PointedCGWH.sphereOne
    ((freeAt PointedCGWH.sphereOne n).obj (𝟙_ PointedCGWH.{u, v}))).injective
  change (Free.adjunction (familyDegree (n + 1))).homEquiv
    PointedCGWH.sphereOne
    (Free.object (familyDegree n) (𝟙_ PointedCGWH.{u, v}))
      (CurrentFree.stabilization (familyDegree n)
        (familyDegree (n + 1)) PointedCGWH.sphereOne
          (familySuccessorIso n).inv) = _
  rw [CurrentFree.stabilization_adjunct]
  exact (unitStabilizationMap_homEquiv_normalized PointedCGWH.sphereOne n).symm

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits

/-- The original full freely pointed finite boundary coefficient arrow. -/
abbrev boundaryMap (m : ℕ) :=
  (Under.costar CGWH.point.{u, v}).map (CGWH.realizedBoundaryInclusion.{v, u} m)

/-- The actual chosen two-variable pushout square, with original coefficient and λ-cylinder maps. -/
def generatorSquare (n m : ℕ) :
    ScalarLeibniz.tensorBifunctor.PushoutObjObj (boundaryMap.{u, v} m)
      (stabilizationCylinderSource.{u, v} n) :=
  pushoutSquare (boundaryMap m) (stabilizationCylinderSource n)

/-- The literal correlated extra generator map of the original stable construction. -/
abbrev generatorMap (n m : ℕ) := (generatorSquare.{u, v} n m).ι

/-- Both ℕ labels remain correlated in the actual original scalar generator family. -/
def additionalGenerators : MorphismProperty PointedCGWH.SequentialSpectrum.{u, v} :=
  MorphismProperty.ofHoms (fun nm : ℕ × ℕ => generatorMap nm.1 nm.2)

/-- The complete original actual native free-J family, with its original base coefficients. -/
abbrev levelJ : MorphismProperty PointedCGWH.SequentialSpectrum.{u, v} :=
  HomotopicalAlgebra.EnrichedProjective.generators
    (A := CategoryTheory.Spectra.Sequential.Index PointedCGWH.sphereOne)
    PointedCGWH.realizedHornInclusions

omit B in
/-- Every original n,m generator Arrow is the same complete shared family value. -/
theorem stabilizationFamily_generatorArrow_eq (n m : ℕ) :
    Arrow.mk (NativeK.generatorMap.{u, v} stabilizationFamily n m) =
      Arrow.mk (generatorMap.{u, v} n m) := by
  have h : Arrow.mk (NativeK.stabilization.{u, v} stabilizationFamily n) =
      Arrow.mk (unitStabilizationMap PointedCGWH.sphereOne.{u, v} n) :=
    congrArg Arrow.mk (stabilizationFamily_stabilization_eq_unitStabilizationMap n)
  exact congrArg
    (fun f : Arrow PointedCGWH.SequentialSpectrum.{u, v} =>
      Arrow.mk ((Functor.PushoutObjObj.ofHasPushout
        (WeightedEndVariance.tensorBifunctor
          (V := PointedCGWH.{u, v}) (I := familyIndex))
        (NativeK.boundaryMap m) (EnrichedIntervalMappingCylinder.source f)).ι)) h

omit B in
/-- The shared extra class retains the whole original pair-indexed generator function. -/
theorem stabilizationFamily_additionalGenerators_eq :
    NativeK.additionalGenerators.{u, v} stabilizationFamily = additionalGenerators.{u, v} := by
  ext X Y f
  rw [NativeK.additionalGenerators, additionalGenerators]
  simp only [MorphismProperty.ofHoms_iff]
  constructor
  · rintro ⟨nm, h⟩
    exact ⟨nm, h.trans (stabilizationFamily_generatorArrow_eq nm.1 nm.2)⟩
  · rintro ⟨nm, h⟩
    exact ⟨nm, h.trans (stabilizationFamily_generatorArrow_eq nm.1 nm.2).symm⟩

/-- The K-class name aliases the one shared native family, with its original full summands. -/
abbrev generators : MorphismProperty PointedCGWH.SequentialSpectrum.{u, v} :=
  NativeK.generators stabilizationFamily

omit B in
/-- The whole shared K class is the literal original free-J and correlated additional class. -/
theorem generators_eq_original : generators.{u, v} = levelJ ⊔ additionalGenerators := by
  rw [generators, NativeK.generators, stabilizationFamily_additionalGenerators_eq]

omit B in
/-- Membership keeps the original two full summands, without replacing their source arrows. -/
theorem generators_iff {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    generators f ↔ levelJ f ∨ additionalGenerators f := by
  rw [generators_eq_original]
  exact MorphismProperty.sup_iff _ _ _

omit B in
/-- The exact original n,m map belongs to the original correlated family. -/
theorem generatorMap_mem (n m : ℕ) : additionalGenerators.{u, v} (generatorMap n m) := ⟨(n, m)⟩

omit B in
/-- The original level-J family is retained literally in K. -/
theorem levelJ_le_generators : levelJ.{u, v} ≤ generators := by
  rw [generators_eq_original]
  exact le_sup_left

/-- Each original coefficient boundary and λ-cylinder source gives
a native projective cofibration. -/
theorem generatorMap_cofibration (n m : ℕ) :
    cofibrations PointedCGWH.SequentialSpectrum.{u, v} (generatorMap n m) :=
  HomotopicalAlgebra.EnrichedProjective.Native.ScalarCompatibility.scalarPushoutProduct_cofibration
    (boundaryMap m) (stabilizationCylinderSource n)
    (IntervalCoefficient.originalBoundary_cofibration m)
    ((HomotopicalAlgebra.cofibration_iff _).mp (stabilizationCylinderSource_cofibration n))
    (generatorSquare n m)

/-- The actual original free-J double orthogonal is the native trivial-cofibration class. -/
theorem levelJ_left_eq : levelJ.{u, v}.rlp.llp =
    trivialCofibrations PointedCGWH.SequentialSpectrum.{u, v} :=
  (HomotopicalAlgebra.EnrichedProjective.Native.trivialCofibrations_eq
    (A := CategoryTheory.Spectra.Sequential.Index PointedCGWH.sphereOne)).symm

/-- The actual original free-J right class is native level fibrations. -/
theorem levelJ_right_eq : levelJ.{u, v}.rlp =
    fibrations PointedCGWH.SequentialSpectrum.{u, v} := rfl

/-- The whole original K family consists of actual original native cofibrations. -/
theorem generators_le_cofibrations : generators.{u, v} ≤
    cofibrations PointedCGWH.SequentialSpectrum.{u, v} := by
  intro X Y f hf
  rcases (generators_iff f).mp hf with hJ | hExtra
  · have h := levelJ.{u, v}.le_llp_rlp f hJ
    rw [levelJ_left_eq] at h
    exact h.1
  · obtain ⟨⟨n, m⟩⟩ := hExtra
    exact generatorMap_cofibration n m

omit B in
/-- Whole original K-generator lifting is the genuine mapping-corner coefficient lifting. -/
theorem generatorMap_lifting_iff (n m : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y) :
    HasLiftingProperty (generatorMap n m) p ↔ HasLiftingProperty (boundaryMap m)
      (PointedCGWH.NativeMappingCorner.square (stabilizationCylinderSource n) p).π :=
  PointedCGWH.NativeMappingCorner.lifting_iff (generatorSquare n m)
    (PointedCGWH.NativeMappingCorner.square (stabilizationCylinderSource n) p)

omit B in
private theorem originalBoundary_right_eq :
    PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp =
      trivialFibrations PointedCGWH.{u, v} := PointedCGWH.cofibrantGenerationData.I_rlp

omit B in
/-- The original pointed boundary family detects precisely
its original native trivial fibrations. -/
theorem boundary_lifting_iff {X Y : PointedCGWH.{u, v}} (p : X ⟶ Y) :
    (∀ m : ℕ, HasLiftingProperty (boundaryMap m) p) ↔
      trivialFibrations PointedCGWH.{u, v} p := by
  constructor
  · intro h
    have hp : PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp p := by
      intro A C i hi
      change (CGWH.realizedBoundaryInclusions.{u, v}.strictMap (Under.costar CGWH.point)) i at hi
      cases hi with
      | @map A C i hi =>
        obtain ⟨m⟩ := hi
        exact h m
    rwa [originalBoundary_right_eq] at hp
  · intro h m
    have hp : PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp p := by
      rwa [originalBoundary_right_eq]
    apply hp
    change (CGWH.realizedBoundaryInclusions.{u, v}.strictMap (Under.costar CGWH.point))
      (boundaryMap m)
    exact .map (CGWH.boundary_mem_realizedBoundaryInclusions m)

/-- Both directions of K lifting retain level fibrations
and every actual original mapping corner. -/
theorem lifting_iff {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y) :
    generators.rlp p ↔ fibrations PointedCGWH.SequentialSpectrum.{u, v} p ∧
      ∀ n : ℕ, trivialFibrations PointedCGWH.{u, v}
        (PointedCGWH.NativeMappingCorner.square (stabilizationCylinderSource n) p).π := by
  constructor
  · intro h
    refine ⟨?_, fun n => (boundary_lifting_iff _).mp (fun m => ?_)⟩
    · have hp : levelJ.{u, v}.rlp p := by
        intro A C i hi
        exact h i (levelJ_le_generators _ hi)
      rwa [levelJ_right_eq] at hp
    · exact (generatorMap_lifting_iff n m p).mp
        (h _ ((generators_iff _).mpr (Or.inr (generatorMap_mem n m))))
  · rintro ⟨hLevel, hCorners⟩
    intro A C i hi
    rcases (generators_iff i).mp hi with hJ | hExtra
    · have hp : levelJ.{u, v}.rlp p := by rwa [levelJ_right_eq]
      exact hp i hJ
    · obtain ⟨⟨n, m⟩⟩ := hExtra
      exact (generatorMap_lifting_iff n m p).mpr ((boundary_lifting_iff _).mpr (hCorners n) m)

end PointedCGWH.SequentialSpectrum.StableK
