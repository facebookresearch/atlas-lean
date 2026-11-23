/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.HSpaceRelativeTotal
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import MathlibExt.Algebra.Homology.FirstQuadrantLowestRow
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeCoefficientTransitions
public import MathlibExt.CategoryTheory.CategoryHomology.InvertingCoefficientCoinvariants
public import MathlibExt.CategoryTheory.CategoryHomology.CoefficientCokernelHomologyAction
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexPulledCoverHomologyCocone
public import MathlibExt.Topology.Homotopy.HSpacePulledRelativeDeckHomology
public import MathlibExt.RepresentationTheory.CoinvariantsReflection
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# The actual original H-space relative lowest-row step

The coefficient diagram is the cokernel of the original simplex pullback
chain map for the internally computed inclusion. Its signed total is the
same original relative total whose acyclicity was derived from ordinary
integral homology of the arbitrary original continuous map.

Actual previous-degree coefficient zeros kill the lower spectral rows.
The existing second-page comparison and lowest-row theorem therefore kill
the actual next zero-column category-homology group. This is the input to
the remaining derived nilpotent-deck/coinvariants detection; it does not
assume or claim the still-required cover homology comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology
open scoped Simplicial SSet.modelCategoryQuillen

universe u

public section

namespace TopCat.HSpaceCommonUnitFibration

local instance : HasCoproducts.{u} (ChainComplex AddCommGrpCat.{u} ℕ) := fun I =>
  let : Small.{u} (Discrete I) := small_self (Discrete I)
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  HomologicalComplex.instHasColimitsOfShape

/-- The actual relative chain diagram of the original map and chosen model factorization. -/
def originalRelativeChainDiagram {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SSet.SimplexIndex (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))) ⥤
      ChainComplex AddCommGrpCat.{u} ℕ :=
  cokernel (Functor.whiskerRight
    (SSet.simplexPullbackDiagramMap (relativeInclusion f) (relativeInclusion_projection f))
    ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})))

/-- Ordinary Hiso and actual lower relative coefficient zeros force the next
actual zero-column category-homology group to vanish. -/
theorem originalRelativeCoefficientHomologyZero_isZero_of_lower_coefficients
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f))
    (q : ℕ)
    (hBelow : ∀ k : ℕ, k < q → ∀ s,
      IsZero (((originalRelativeChainDiagram f).obj s).homology k)) :
    IsZero (homologyWithCoefficients
      (originalRelativeChainDiagram f ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) q) 0) := by
  let D := originalRelativeChainDiagram f
  let K := coefficientChainBicomplex D
  have hTotal : (K.total (ComplexShape.down ℕ)).Acyclic := by
    change (originalRelativeCoefficientTotal f).Acyclic
    exact originalRelativeCoefficientTotal_acyclic_of_integralHomology_isIso f h
  have hRows : ∀ k : ℕ, k < q → ∀ a : ℕ,
      IsZero (((HomologicalComplex₂.horizontalFirstQuadrantSpectralSequence K).page 2 (by decide)).X
        (a, k)) := by
    intro k hk a
    let Hk := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) k
    let M := D ⋙ Hk
    have hM : IsZero M := Functor.isZero M (hBelow k hk)
    have hBar : IsZero (coefficientBarComplex M) :=
      (alternatingCoefficientBarFunctor
        (J := SSet.SimplexIndex
          (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))))
        (A := AddCommGrpCat.{u})).map_isZero hM
    have hVertical : IsZero (K.verticalHomologyComplex k) :=
      IsZero.of_iso hBar (coefficientChainVerticalHomologyIso D k)
    have hHomology : IsZero ((K.verticalHomologyComplex k).homology a) :=
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) a).map_isZero
        hVertical
    exact IsZero.of_iso hHomology
      (HomologicalComplex₂.horizontalSecondPageVerticalHorizontalHomologyIso K a k)
  have hPage : IsZero (((coefficientChainSpectralSequence D).page 2).X (0, q)) :=
    HomologicalComplex₂.isZero_horizontalSecondPage_zeroColumn_of_total_acyclic_of_lower_rows
      K q hTotal hRows
  exact IsZero.of_iso hPage (coefficientChainSecondPageIso D 0 q).symm

/-- The actual initial relative zero-column group vanishes with no lower-row premise. -/
theorem originalRelativeCoefficientHomologyZero_zero_isZero
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f)) :
    IsZero (homologyWithCoefficients
      (originalRelativeChainDiagram f ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) 0) 0) :=
  originalRelativeCoefficientHomologyZero_isZero_of_lower_coefficients f h 0
    (fun k hk => False.elim (Nat.not_lt_zero k hk))

end TopCat.HSpaceCommonUnitFibration

namespace TopCat.HSpaceCommonUnitFibration

/-- The original relative coefficient functor inverts every actual simplex arrow,
by the two computed common-base fibrations and actual relative quotient. -/
theorem originalRelativeHomologyCoefficients_map_isIso
    {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    {s t : SSet.SimplexIndex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)))} (a : s ⟶ t) :
    IsIso (((originalRelativeChainDiagram f) ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n).map a) := by
  let : HomotopicalAlgebra.Fibration (unitProjection X) := unitProjection_isFibration X
  let : HomotopicalAlgebra.Fibration (relativeProjection f) := relativeProjection_fibration f
  let : Mono (relativeInclusion f) := relativeInclusion_mono f
  exact SSet.relativeSimplexHomologyCoefficientTransition_isIso
    (relativeInclusion f) (relativeInclusion_projection f)
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) n a

/-- The actual relative root representation uses the derived transition inversions. -/
def originalRelativeRootAction {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    (i : SSet.SimplexIndex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)))) :
    Representation ℤ (End ((SSet.categoryNerveUnit
      (SSet.SimplexIndex (CategoryTheory.nerve
        (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))))).obj i))
      (((originalRelativeChainDiagram f).obj i).homology n) := by
  let M := originalRelativeChainDiagram f ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n
  let : ∀ {s t} (a : s ⟶ t), IsIso (M.map a) :=
    fun a => originalRelativeHomologyCoefficients_map_isIso f n a
  exact invertingCoefficientRootAction M i

private theorem originalRelativeBase_isConnected (X : TopCat.{u}) [PathConnectedSpace X] :
    (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))).IsConnected := by
  let : (TopCat.toSSet.obj X).IsConnected := inferInstance
  let : CategoryTheory.IsConnected (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) :=
    SSet.fundamentalGroupoid_category_isConnected _
  exact CategoryTheory.nerve_isConnected_of_category_isConnected

/-- The actual next root-action coinvariants vanish from ordinary Hiso and
actual lower relative coefficients. The action and comparison are computed. -/
theorem originalRelativeRootCoinvariants_subsingleton_of_lower_coefficients
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f))
    (q : ℕ) (i : SSet.SimplexIndex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))))
    (hBelow : ∀ k : ℕ, k < q → ∀ s,
      IsZero (((originalRelativeChainDiagram f).obj s).homology k)) :
    Subsingleton (Representation.Coinvariants (originalRelativeRootAction f q i)) := by
  let B := CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))
  let J := SSet.SimplexIndex B
  let M := originalRelativeChainDiagram f ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) q
  let : ∀ {s t : J} (a : s ⟶ t), IsIso (M.map a) :=
    fun a => originalRelativeHomologyCoefficients_map_isIso f q a
  let : B.IsConnected := originalRelativeBase_isConnected X
  let : (CategoryTheory.nerve J).IsConnected := SSet.simplexIndexNerve_isConnected B
  let : Small.{u} J := small_self J
  let : HasColimitsOfShape J AddCommGrpCat.{u} := AddCommGrpCat.hasColimitsOfShape (J := J)
  let : HasColimit M := inferInstance
  change Subsingleton (Representation.Coinvariants (invertingCoefficientRootAction M i))
  exact invertingCoefficientCoinvariants_subsingleton_of_homologyZero_isZero M i
    (originalRelativeCoefficientHomologyZero_isZero_of_lower_coefficients f h q hBelow)

private abbrev originalSourceChains (X : TopCat.{u}) :
    SSet.SimplexIndex (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))) ⥤
      ChainComplex AddCommGrpCat.{u} ℕ :=
  SSet.simplexPullbackDiagram (unitProjection X) ⋙
    (SSet.chainComplexFunctor AddCommGrpCat.{u}).obj
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})

private abbrev originalTargetChains {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SSet.SimplexIndex (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))) ⥤
      ChainComplex AddCommGrpCat.{u} ℕ :=
  SSet.simplexPullbackDiagram (relativeProjection f) ⋙
    (SSet.chainComplexFunctor AddCommGrpCat.{u}).obj
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})

private abbrev originalCoefficientArrow {X Y : TopCat.{u}} (f : X ⟶ Y) :
    originalSourceChains X ⟶ originalTargetChains f :=
  Functor.whiskerRight
    (SSet.simplexPullbackDiagramMap (relativeInclusion f) (relativeInclusion_projection f))
    ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))

private theorem originalCoefficientArrow_mono {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Mono (originalCoefficientArrow f) := by
  let : Mono (relativeInclusion f) := relativeInclusion_mono f
  exact SSet.relativeSimplexChainArrow_mono (relativeInclusion f)
    (relativeInclusion_projection f)
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})

private theorem originalSourceGroupoid_isConnected (X : TopCat.{u}) [PathConnectedSpace X] :
    CategoryTheory.IsConnected (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) := by
  let : (TopCat.toSSet.obj X).IsConnected := inferInstance
  exact SSet.fundamentalGroupoid_category_isConnected (TopCat.toSSet.obj X)

private theorem originalSourceCoefficients_map_isIso
    (X : TopCat.{u}) (n : ℕ)
    {s t : SSet.SimplexIndex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)))} (a : s ⟶ t) :
    IsIso ((originalSourceChains X ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n).map a) := by
  let : HomotopicalAlgebra.Fibration (unitProjection X) := unitProjection_isFibration X
  exact SSet.simplexFibrationHomologyCoefficients_map_isIso
    (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) (unitProjection X)
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) n a

private theorem originalTargetCoefficients_map_isIso
    {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    {s t : SSet.SimplexIndex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)))} (a : s ⟶ t) :
    IsIso ((originalTargetChains f ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n).map a) := by
  let : HomotopicalAlgebra.Fibration (relativeProjection f) := relativeProjection_fibration f
  exact SSet.simplexFibrationHomologyCoefficients_map_isIso
    (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) (relativeProjection f)
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) n a

private theorem originalSourceRootAction_isTrivial
    (X : TopCat.{u}) [HSpace X] [PathConnectedSpace X] (n : ℕ)
    (i : SSet.SimplexIndex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))))
    [∀ {s t} (a : s ⟶ t), IsIso ((originalSourceChains X ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n).map a)] :
    Representation.IsTrivial (invertingCoefficientRootAction
      (originalSourceChains X ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n) i) := by
  let G := SSet.FundamentalGroupoid (TopCat.toSSet.obj X)
  let R : AddCommGrpCat.{u} := AlgebraicTopology.singularIntegralCoefficients
  let b := (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (Opposite.op ⦋0⦌)
    (TopCat.toSSetObj₀Equiv.symm (HSpace.e : X))
  let : CategoryTheory.IsConnected G := originalSourceGroupoid_isConnected X
  let : HomotopicalAlgebra.Fibration (unitProjection X) := unitProjection_isFibration X
  let : ∀ {s t : SSet.SimplexIndex (CategoryTheory.nerve G)} (a : s ⟶ t),
      IsIso ((SSet.simplexFibrationHomologyCoefficients G (unitProjection X) R n).map a) :=
    fun a => SSet.simplexFibrationHomologyCoefficients_map_isIso
      G (unitProjection X) R n a
  have hDeck (g : End (SSet.FundamentalGroupoid.mk b)) :
      SSet.homologyMap (SSet.KanComplex.nativeCoverBaseChangeDeckMap (unitProjection X) b g)
        R n = 𝟙 _ := by
    have h := TopCat.HSpaceHomotopyAction.unitPulledCoverBaseDeckMap_homologyMap_eq_id
      X (HSpace.e : X) g R n
    rw [SSet.KanComplex.unitPulledCoverBaseDeckMap_eq] at h
    rw [unitProjection_eq]
    exact h
  change Representation.IsTrivial (invertingCoefficientRootAction
    (SSet.simplexFibrationHomologyCoefficients G (unitProjection X) R n) i)
  exact SSet.simplexFibrationRootAction_isTrivial G (unitProjection X) b R n hDeck i

private theorem originalTargetRootAction_isTrivial
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h1 : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f)) (n : ℕ)
    (i : SSet.SimplexIndex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))))
    [∀ {s t} (a : s ⟶ t), IsIso ((originalTargetChains f ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n).map a)] :
    Representation.IsTrivial (invertingCoefficientRootAction
      (originalTargetChains f ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n) i) := by
  let G := SSet.FundamentalGroupoid (TopCat.toSSet.obj X)
  let R : AddCommGrpCat.{u} := AlgebraicTopology.singularIntegralCoefficients
  let b := (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (Opposite.op ⦋0⦌)
    (TopCat.toSSetObj₀Equiv.symm (HSpace.e : X))
  let : CategoryTheory.IsConnected G := originalSourceGroupoid_isConnected X
  let : HomotopicalAlgebra.Fibration (relativeProjection f) := relativeProjection_fibration f
  let : ∀ {s t : SSet.SimplexIndex (CategoryTheory.nerve G)} (a : s ⟶ t),
      IsIso ((SSet.simplexFibrationHomologyCoefficients G (relativeProjection f) R n).map a) :=
    fun a => SSet.simplexFibrationHomologyCoefficients_map_isIso
      G (relativeProjection f) R n a
  have hDeck (g : End (SSet.FundamentalGroupoid.mk b)) :
      SSet.homologyMap (SSet.KanComplex.nativeCoverBaseChangeDeckMap (relativeProjection f) b g)
        R n = 𝟙 _ := relativeIntermediatePulledDeck_homologyMap_eq_id f h1 (HSpace.e : X) g R n
  change Representation.IsTrivial (invertingCoefficientRootAction
    (SSet.simplexFibrationHomologyCoefficients G (relativeProjection f) R n) i)
  exact SSet.simplexFibrationRootAction_isTrivial G (relativeProjection f) b R n hDeck i

/-- The ACTUAL relative root action has a length-two augmentation bound,
derived from the original LES and the two original H-space unit traces. -/
theorem originalRelativeRootAction_ker_le_invariants
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h1 : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f))
    (q : ℕ) (i : SSet.SimplexIndex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)))) :
    Representation.Coinvariants.ker (originalRelativeRootAction f q i) ≤
      (originalRelativeRootAction f q i).invariants := by
  let A := originalSourceChains X
  let B := originalTargetChains f
  let α : A ⟶ B := originalCoefficientArrow f
  let : Mono α := originalCoefficientArrow_mono f
  cases q with
  | zero =>
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) 0
    let : ∀ {s t} (a : s ⟶ t), IsIso ((B ⋙ H).map a) :=
      fun a => originalTargetCoefficients_map_isIso f 0 a
    let : ∀ {s t} (a : s ⟶ t), IsIso ((cokernel α ⋙ H).map a) :=
      fun a => originalRelativeHomologyCoefficients_map_isIso f 0 a
    let sigma := invertingCoefficientRootAction (B ⋙ H) i
    let rho := invertingCoefficientRootAction (cokernel α ⋙ H) i
    let m := coefficientCokernelProjectionRootMap α 0 i
    let : Representation.IsTrivial sigma := originalTargetRootAction_isTrivial f h1 0 i
    have hm : Function.Surjective m := coefficientCokernelProjectionRootMap_zero_surjective α i
    change Representation.Coinvariants.ker rho ≤ rho.invariants
    have hFixed (g : End ((SSet.categoryNerveUnit (SSet.SimplexIndex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))))).obj i))
        (v : ((cokernel α).obj i).homology 0) : rho g v = v := by
      obtain ⟨a, ha⟩ := hm v
      exact (congrArg (rho g) ha.symm).trans
        ((Representation.IntertwiningMap.isIntertwining sigma rho m g a).symm.trans
          ((congrArg m (sigma.isTrivial_apply g a)).trans ha))
    intro v _
    exact (Representation.mem_invariants rho v).mpr (fun g => hFixed g v)
  | succ n =>
    let Hn := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n
    let Hq := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) (n + 1)
    let : ∀ {s t} (a : s ⟶ t), IsIso ((A ⋙ Hn).map a) :=
      fun a => originalSourceCoefficients_map_isIso X n a
    let : ∀ {s t} (a : s ⟶ t), IsIso ((B ⋙ Hq).map a) :=
      fun a => originalTargetCoefficients_map_isIso f (n + 1) a
    let : ∀ {s t} (a : s ⟶ t), IsIso ((cokernel α ⋙ Hq).map a) :=
      fun a => originalRelativeHomologyCoefficients_map_isIso f (n + 1) a
    let sigma := invertingCoefficientRootAction (B ⋙ Hq) i
    let rho := invertingCoefficientRootAction (cokernel α ⋙ Hq) i
    let tau := invertingCoefficientRootAction (A ⋙ Hn) i
    let : Representation.IsTrivial sigma :=
      originalTargetRootAction_isTrivial f h1 (n + 1) i
    let : Representation.IsTrivial tau := originalSourceRootAction_isTrivial X n i
    change Representation.Coinvariants.ker rho ≤ rho.invariants
    exact Representation.Coinvariants.ker_le_invariants_of_exact sigma rho tau
      (coefficientCokernelProjectionRootMap α (n + 1) i)
      (coefficientCokernelBoundaryRootMap α n i) (coefficientCokernelRootMaps_exact α n i)

/-- BOTH augmentation differences act trivially on every actual relative class:
this is the computed I²=0 relation, with no nilpotence witness. -/
theorem originalRelativeRootAction_augmentationDifference_fixed
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h1 : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f))
    (q : ℕ) (i : SSet.SimplexIndex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))))
    (g h : End ((SSet.categoryNerveUnit (SSet.SimplexIndex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))))).obj i))
    (v : ((originalRelativeChainDiagram f).obj i).homology q) :
    originalRelativeRootAction f q i g (originalRelativeRootAction f q i h v - v) =
      originalRelativeRootAction f q i h v - v := by
  let rho := originalRelativeRootAction f q i
  have hMem : rho h v - v ∈ Representation.Coinvariants.ker rho :=
    Submodule.subset_span ⟨⟨h, v⟩, rfl⟩
  exact (Representation.mem_invariants rho (rho h v - v)).mp
    ((originalRelativeRootAction_ker_le_invariants f h1 q i) hMem) g

/-- Ordinary integral Hiso of the arbitrary original H-space map kills EVERY
actual relative homology coefficient, by the original lowest-row induction. -/
theorem originalRelativeHomologyCoefficients_isZero_of_integralHomology_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f))
    (q : ℕ) (i : SSet.SimplexIndex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)))) :
    IsZero (((originalRelativeChainDiagram f).obj i).homology q) := by
  have hAll : ∀ q : ℕ, ∀ i : SSet.SimplexIndex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))),
      IsZero (((originalRelativeChainDiagram f).obj i).homology q) := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro i
      have hBelow : ∀ k : ℕ, k < q → ∀ s,
          IsZero (((originalRelativeChainDiagram f).obj s).homology k) :=
        fun k hk s => ih k hk s
      let rho := originalRelativeRootAction f q i
      let : Subsingleton (Representation.Coinvariants rho) :=
        originalRelativeRootCoinvariants_subsingleton_of_lower_coefficients f h q i hBelow
      let : Subsingleton (((originalRelativeChainDiagram f).obj i).homology q) :=
        Representation.Coinvariants.subsingleton_of_ker_le_invariants rho
          (originalRelativeRootAction_ker_le_invariants f (h 1) q i)
      exact AddCommGrpCat.isZero_of_subsingleton _
  exact hAll q i

end TopCat.HSpaceCommonUnitFibration

namespace TopCat.HSpaceCommonUnitFibration

private theorem originalRelativeChainDiagram_eq_computation {X Y : TopCat.{u}} (f : X ⟶ Y) :
    originalRelativeChainDiagram f = cokernel (Functor.whiskerRight
      (SSet.simplexPullbackDiagramMap (relativeInclusion f) (relativeInclusion_projection f))
      ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))) := by
  rfl

/-- The original relative diagram is its literal original functor-category cokernel. -/
theorem originalRelativeChainDiagram_eq {X Y : TopCat.{u}} (f : X ⟶ Y) :
    originalRelativeChainDiagram f = cokernel (Functor.whiskerRight
      (SSet.simplexPullbackDiagramMap (relativeInclusion f) (relativeInclusion_projection f))
      ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))) :=
  originalRelativeChainDiagram_eq_computation f

end TopCat.HSpaceCommonUnitFibration
