/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.ChosenFiberTransport
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.DiagonalFiberSequence
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.IntegerColimitNormalization
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalFiberNullity
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableGeneratorClasses

/-!
# Original orthogonal chosen fibers and every original integer degree

The unchanged orthogonal chosen cone supplies the full original sequential
chosen cone under enriched restriction. The actual ordered loop, cube and
singular comparisons give the original group connecting maps on every
starting level and positive index. Their original quotient maps are exact
at the base, chosen fiber and total spectrum.

The complete original integer normalization retains all changing levels,
degrees and offset maps. The resulting original group sequence is exact
in every integer degree. The all integer nullity consequence below states
its actual integer map hypothesis explicitly; it does not identify that
hypothesis with arbitrary source Omega tests.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.ChosenFiberTests

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
  OrthogonalIntegerHomotopy
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry
open PointedCGWH.Spectra.Orthogonal.ChosenFiberTransport
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- All original starting levels and homotopy indices retain their actual
orthogonal component groups and transition maps. -/
def diagonalFunctor (m k : ℕ) : OrthogonalCarrier.{u, v} ⥤ (ℕ ⥤ GrpCat.{v}) :=
  underlyingSequential ⋙ diagonalDiagramFunctor m k

/-- The positive homotopy degree and original orthogonal dimension are unchanged. -/
theorem diagonalFunctor_obj_stage (m k : ℕ) (X : OrthogonalCarrier.{u, v}) (n : ℕ) :
    ((diagonalFunctor m k).obj X).obj n =
      (PointedCGWH.piNPositiveFunctor (k + n)).obj
        (X.toEnrichedFunctor.obj
          (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex (m + n))) :=
  rfl

/-- Every actual stage map is the group image of the full original
orthogonal component of the same input Arrow. -/
theorem diagonalFunctor_map_stage (m k : ℕ) {X Y : OrthogonalCarrier.{u, v}}
    (f : X ⟶ Y) (n : ℕ) :
    ((diagonalFunctor m k).map f).app n =
      (PointedCGWH.piNPositiveFunctor (k + n)).map
        (component f (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex (m + n))) :=
  congrArg ((PointedCGWH.piNPositiveFunctor (k + n)).map) (underlying_map f (m + n))

/-- Each original starting pair uses the same actual filtered group quotient. -/
def diagonalPiFunctor (m k : ℕ) : OrthogonalCarrier.{u, v} ⥤ GrpCat.{v} :=
  underlyingSequential ⋙ diagonalColimitFunctor m k

/-- Every full original Arrow retains its actual map of diagonal group quotients. -/
theorem diagonalPiFunctor_map (m k : ℕ) {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    (diagonalPiFunctor m k).map f =
      GrpCat.FilteredColimits.colimitMap ((diagonalFunctor m k).map f) := rfl

/-- The actual orthogonal degree pair retains its full original integer degree. -/
theorem diagonal_degree (m k n : ℕ) :
    ((k + n + 1 : ℕ) : ℤ) - ((m + n : ℕ) : ℤ) = integerDegree m k := by
  simp only [integerDegree]
  omega

/-- Every finite original offset keeps the same original integer degree. -/
theorem diagonal_offset_degree (m k r : ℕ) :
    integerDegree (m + r) (k + r) = integerDegree m k := by
  simp only [integerDegree]
  omega

/-- Both complete native quotient comparison maps are the original
normalization of the actual starting pair. -/
def integerComparisonNatIso (m k : ℕ) :
    diagonalPiFunctor.{u, v} m k ≅ integerPiFunctor (integerDegree m k) :=
  Functor.isoWhiskerLeft underlyingSequential (integerColimitNatIso m k)

/-- Every whole original Arrow commutes with the complete forward
normalization function in its actual integer degree. -/
theorem integerComparison_hom_naturality (m k : ℕ)
    {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    (diagonalPiFunctor m k).map f ≫ (integerComparisonNatIso m k).hom.app Y =
      (integerComparisonNatIso m k).hom.app X ≫ (integerPiFunctor (integerDegree m k)).map f :=
  (integerComparisonNatIso m k).hom.naturality f

/-- Every whole original Arrow keeps the complete inverse normalization function. -/
theorem integerComparison_inv_naturality (m k : ℕ)
    {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    (integerPiFunctor (integerDegree m k)).map f ≫ (integerComparisonNatIso m k).inv.app Y =
      (integerComparisonNatIso m k).inv.app X ≫ (diagonalPiFunctor m k).map f :=
  (integerComparisonNatIso m k).inv.naturality f

/-- The entire original native group Arrow is identified with its exact
integer group Arrow by both original normalization endpoints. -/
def integerComparisonArrowIso (m k : ℕ)
    {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    Arrow.mk ((diagonalPiFunctor m k).map f) ≅
      Arrow.mk ((integerPiFunctor (integerDegree m k)).map f) :=
  Arrow.isoMk ((integerComparisonNatIso m k).app X) ((integerComparisonNatIso m k).app Y)
    (integerComparison_hom_naturality m k f).symm

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- Original K-rightness supplies every actual component Serre fibration
of the same original continuous orthogonal Arrow. -/
theorem originalLevelFibrations {X Y : OrthogonalCarrier.{u, v}} (p : X ⟶ Y)
    (hp : (NativeK.generators orthogonalFamily).rlp p) :
    ∀ n : ℕ, fibrations PointedCGWH.{u, v}
      (PointedCGWH.SequentialSpectrum.levelMap (underlyingSequential.map p) n) := by
  have h := NativeK.right_le_fibrations orthogonalFamily p hp
  rw [HomotopicalAlgebra.EnrichedProjective.Native.fibrations_eq] at h
  have he := (EvaluationTransfer.evaluationProperty_iff _ _ p).mp h
  intro n
  rw [underlying_map]
  exact he (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n)

variable {X Y : OrthogonalCarrier.{u, v}} (p : X ⟶ Y)
  (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c)
  (hp : (NativeK.generators orthogonalFamily).rlp p)

/-- The full original orthogonal connecting map is the original ordered
loop and cube connecting map on the caller's unchanged restricted cone. -/
def diagonalConnecting (m k : ℕ) :
    (diagonalPiFunctor m (k + 1)).obj Y ⟶ (diagonalPiFunctor m k).obj c.pt :=
  PointedCGWH.SequentialSpectrum.StableHomotopy.DiagonalFiberSequence.diagonalConnectingMap
    (underlyingSequential.map p) (underlyingChosenCone p c)
    (underlyingChosenConeIsLimit p c hc) (originalLevelFibrations p hp) m k

include hc hp in
/-- Every original group quotient is exact at the actual total spectrum. -/
theorem diagonal_exact_at_total (m k : ℕ) :
    Function.MulExact ((diagonalPiFunctor m k).map c.fst).hom
      ((diagonalPiFunctor m k).map p).hom :=
  PointedCGWH.SequentialSpectrum.StableHomotopy.DiagonalFiberSequence.diagonal_exact_at_total
    (underlyingSequential.map p) (underlyingChosenCone p c)
    (underlyingChosenConeIsLimit p c hc) (originalLevelFibrations p hp) m k

/-- The original connecting group function is exact at the same original chosen fiber. -/
theorem diagonal_exact_at_fiber (m k : ℕ) :
    Function.MulExact (diagonalConnecting p c hc hp m k).hom
      ((diagonalPiFunctor m k).map c.fst).hom :=
  PointedCGWH.SequentialSpectrum.StableHomotopy.DiagonalFiberSequence.diagonal_exact_at_fiber
    (underlyingSequential.map p) (underlyingChosenCone p c)
    (underlyingChosenConeIsLimit p c hc) (originalLevelFibrations p hp) m k

/-- The same next-degree projection and chosen connecting function are
exact at the original base group quotient. -/
theorem diagonal_exact_at_base (m k : ℕ) :
    Function.MulExact ((diagonalPiFunctor m (k + 1)).map p).hom
      (diagonalConnecting p c hc hp m k).hom :=
  PointedCGWH.SequentialSpectrum.StableHomotopy.DiagonalFiberSequence.diagonal_exact_at_base
    (underlyingSequential.map p) (underlyingChosenCone p c)
    (underlyingChosenConeIsLimit p c hc) (originalLevelFibrations p hp) m k

omit B in
/-- Every original all integer map hypothesis tests the complete
diagonal quotient map at every original starting pair. -/
theorem diagonalMap_isIso_of_integerPiStar (hf : integerPiStarEquivalences p) (m k : ℕ) :
    IsIso ((diagonalPiFunctor m k).map p) :=
  ((MorphismProperty.isomorphisms GrpCat.{v}).arrow_mk_iso_iff
    (integerComparisonArrowIso m k p)).mpr ((integerPiStarEquivalences_iff p).mp hf _)

omit B in
private theorem null_middle_of_exact
    {G₀ G₁ G₂ G₃ G₄ : Type*}
    [Monoid G₀] [Monoid G₁] [Monoid G₂] [Monoid G₃] [Monoid G₄]
    (a : G₀ →* G₁) (d : G₁ →* G₂) (i : G₂ →* G₃) (b : G₃ →* G₄)
    (hBase : Function.MulExact a d) (hFiber : Function.MulExact d i)
    (hTotal : Function.MulExact i b) (ha : Function.Surjective a)
    (hb : Function.Injective b) (x : G₂) : x = 1 := by
  have hi : i x = 1 := hb ((hTotal.apply_apply_eq_one x).trans b.map_one.symm)
  obtain ⟨y, hy⟩ := (hFiber x).mp hi
  obtain ⟨z, hz⟩ := ha y
  exact hy.symm.trans ((congrArg d hz).symm.trans (hBase.apply_apply_eq_one z))

include hc hp in
/-- All original integer classes of the caller's actual chosen fiber are
the identity when the original full K-right Arrow is an integer equivalence. -/
theorem chosenFiber_integerPi_eq_one (hf : integerPiStarEquivalences p)
    (q : ℤ) (x : (integerPiFunctor q).obj c.pt) : x = 1 := by
  let m := integerTailLevel q
  let k := integerTailPositiveIndex q
  let a := (diagonalPiFunctor m (k + 1)).map p
  let d := diagonalConnecting p c hc hp m k
  let i := (diagonalPiFunctor m k).map c.fst
  let b := (diagonalPiFunctor m k).map p
  let _ : IsIso a := diagonalMap_isIso_of_integerPiStar p hf m (k + 1)
  let _ : IsIso b := diagonalMap_isIso_of_integerPiStar p hf m k
  exact null_middle_of_exact a.hom d.hom i.hom b.hom
    (diagonal_exact_at_base p c hc hp m k) (diagonal_exact_at_fiber p c hc hp m k)
    (diagonal_exact_at_total p c hc hp m k)
    (ConcreteCategory.bijective_of_isIso a).2 (ConcreteCategory.bijective_of_isIso b).1 x

omit B in
/-- The original continuous orthogonal zero has trivial groups in every
original integer degree, through its actual full zero comparison. -/
theorem zero_integerPi_subsingleton (q : ℤ) :
    Subsingleton ((integerPiFunctor.{u, v} q).obj Diagrams.zeroDiagram) := by
  let _ : Subsingleton ((integerStablePiFunctor.{u, v} q).obj Diagrams.zeroDiagram) :=
    NativeK.OriginalFiberNullity.sequentialZero_integerPi_subsingleton q
  let e := (integerStablePiFunctor q).mapIso underlyingZeroIso
  exact (ConcreteCategory.bijective_of_isIso e.hom).1.subsingleton

include hc hp in
/-- The same original chosen collapse is invertible on every original
integer group; the source and target are unchanged. -/
theorem chosenCollapse_integerPiStar (hf : integerPiStarEquivalences p) :
    integerPiStarEquivalences c.snd := by
  apply (integerPiStarEquivalences_iff c.snd).mpr
  intro q
  let _ : Subsingleton ((integerPiFunctor q).obj c.pt) := ⟨fun x y =>
    (chosenFiber_integerPi_eq_one p c hc hp hf q x).trans
      (chosenFiber_integerPi_eq_one p c hc hp hf q y).symm⟩
  let _ := zero_integerPi_subsingleton.{u, v} q
  exact (ConcreteCategory.isIso_iff_bijective ((integerPiFunctor q).map c.snd)).mpr
    (Function.bijective_of_subsingleton' _)

include hc hp in
/-- The original chosen fiber is Omega from the full original paired K
family, at every original source and added degree. -/
theorem chosenFiber_isOmega : NativeK.IsOmega orthogonalFamily c.pt :=
  (NativeK.chosenFiber_right_local_omega orthogonalFamily p hp c hc).2.2

include hc hp in
/-- This consequence uses only the proved integer detector on the
chosen Omega fiber and the original zero, with its full native source labels. -/
theorem chosenCollapse_omegaTests_of_integerPiStar (hf : integerPiStarEquivalences p) :
    NativeK.omegaTests orthogonalFamily c.snd := by
  let Z : OrthogonalCarrier.{u, v} := Diagrams.zeroDiagram
  let _ : IsIso (Diagrams.toZero Z) :=
    Diagrams.zeroDiagram_isZero.isIso Diagrams.zeroDiagram_isZero (Diagrams.toZero Z)
  have hZero : NativeK.IsOmega orthogonalFamily Z :=
    (NativeK.lifting_toZero_iff_isOmega orthogonalFamily Z).mp
      (MorphismProperty.rlp_of_isIso _ _)
  have hLevel : weakEquivalences OrthogonalCarrier.{u, v} c.snd :=
    (integerPiStar_iff_levelWeak_of_isOmega c.snd (chosenFiber_isOmega p c hc hp) hZero).mp
      (chosenCollapse_integerPiStar p c hc hp hf)
  exact NativeK.levelWeak_le_omegaTests orthogonalFamily c.snd hLevel

include c hc hp in
/-- The exact integer hypothesis yields every original component level
trivial fibration through the original one-sphere normalized corner. -/
theorem levelTrivialFibration_of_integerPiStar (hf : integerPiStarEquivalences p) :
    trivialFibrations OrthogonalCarrier.{u, v} p ∧
      ∀ a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v},
        trivialFibrations PointedCGWH.{u, v} (component p a) :=
  PointedCGWH.Spectra.NativeStable.orthogonal_chosenFiber_levelTrivialFibration
    p hp c hc (chosenCollapse_omegaTests_of_integerPiStar p c hc hp hf)

end PointedCGWH.Spectra.Orthogonal.ChosenFiberTests
