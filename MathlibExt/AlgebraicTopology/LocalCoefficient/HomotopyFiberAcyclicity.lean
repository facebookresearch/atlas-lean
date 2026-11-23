/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.InvertingCoefficientCoinvariants
public import MathlibExt.AlgebraicTopology.LocalCoefficient.WeakEquivalence

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MappingPathFiber

import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractiblePoint
import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexContraction
import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexResolutionAugmentationWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceAddCommGrpChains
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceChains
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanSpectralSequence
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanVerticalCoefficientBarNaturality
public import MathlibExt.AlgebraicTopology.SingularHomology.Integral
public import MathlibExt.AlgebraicTopology.PlusConstruction.Basic
import MathlibExt.Algebra.Homology.FirstQuadrantCollapse
import MathlibExt.Algebra.Homology.FirstQuadrantEdge
import MathlibExt.Algebra.Homology.FirstQuadrantSpectralComparison
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.CommSq
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.Logic.Small.Defs
public import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.Algebra.Homology.SpectralSequence.Basic
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomotopyInvariance
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidRealizationWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NerveUnit
import MathlibExt.CategoryTheory.CategoryHomology.Constant
import MathlibExt.CategoryTheory.CategoryHomology.InitialGenerator
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Endomorphism
import MathlibExt.AlgebraicTopology.LocalCoefficient.RegularModuleBasis
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseHomology
import MathlibExt.AlgebraicTopology.SimplicialSet.ChangeOfCategory
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanHomotopyPullback
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathHomotopyFiber
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPRealizationWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCertificates
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverBaseChangePathFiber
import MathlibExt.Algebra.Homology.Functor
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import MathlibExt.Algebra.Homology.FirstQuadrantSecondPageNaturality
import MathlibExt.Algebra.Homology.FirstQuadrantStablePageGradedNaturality
import MathlibExt.Algebra.Homology.FirstQuadrantHomologyFilteredObjectFunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanDiagonalTotalNaturality
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetFiberEdge
import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakPiZero
import MathlibExt.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Adjunction.Basic
import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetFunctoriality
import MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarBaseFunctoriality
import MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarChangeOfCategory
import MathlibExt.AlgebraicTopology.SimplicialObject.DataIso
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Connected.Clopen
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopConnectingHomotopy
import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyGroupCommutativity
import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.FundamentalGroupHurewiczIso
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.GroupTheory.Abelianization.Defs
import MathlibExt.AlgebraicTopology.LocalCoefficient.IntegralConsequence
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.WeakHomotopySingularHomology
import MathlibExt.Topology.Homotopy.TopCat.HurewiczOne
public import MathlibExt.Topology.CWComplex.BasedWhiteheadUniverseLift
public import MathlibExt.Topology.CWComplex.UnbasedWhitehead

/-!
# Homotopy-fiber acyclicity and integral local coefficients

Integral homology isomorphisms with every target local coefficient system
give actual terminal homology isomorphisms and canonical reduced acyclicity
of every ending-path fiber. The terminal-homology condition also gives the
same original pullback-chain quasi-isomorphisms, without flatness assumptions.

For a nonempty source and a connected target of genuine classical CW type,
an actual source point and target paths make every ending fiber nonempty.
In this original CW setting, canonical reduced acyclicity of all fibers is
equivalent to local-coefficient homology equivalence. The target CW model may
have an independent universe, and no Hausdorff assumption is placed on the
original target. The terminal-homology companion retains unrestricted sources.

The private construction uses the original regular-cover and mapping-path
maps, the actual simplex-pullback Bousfield--Kan augmentation, spectral page
and finite-filtration comparisons, and the same integral path-representation
and stalk tensors. The public conclusions keep the original maps and full
ending fibers. The recognition theorems additionally use the ACTUAL
fundamental-group maps to derive weakness on all components. With genuine
independently sized unbased CW models, they construct a homotopy equivalence
whose forward map is the literal original map, and both inverse homotopies.
The based relative companion is additional. No plus construction is asserted.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra AlgebraicTopology
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace ActualKanFibrationHomologyCoefficients

-- These are the existing canonical colimit choices, installed locally to
-- avoid re-solving a forall-index coproduct problem at every occurrence.
local instance (I : Type u) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance (I : Type u) : HasColimitsOfShape (Discrete I) (ModuleCat.{u} ℤ) :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

local instance : HasCoproducts.{u} (ModuleCat.{u} ℤ) :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
      AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
    ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

attribute [local instance] TopCat.toSSet_obj_kanComplex

private abbrev integralCoefficients : AddCommGrpCat.{u} :=
  singularIntegralCoefficients

/-- The point projection is weak using the existing finite-ordinal nerve. -/
private theorem standardSimplexToPoint_weak (A : SimplexCategory) :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj A : SSet.{u})) := by
  obtain ⟨n⟩ := A
  let C : Type u := ULift.{u} (Fin (n + 1))
  let z : C := ULift.up (Fin.last n)
  have hz : IsTerminal z :=
    IsTerminal.ofUniqueHom
      (fun a : C => homOfLE (show a.down ≤ Fin.last n from Fin.le_last a.down))
      (fun _ _ => Subsingleton.elim _ _)
  have hn : SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from (CategoryTheory.nerve C : SSet.{u})) :=
    NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_isTerminal hz
  let e : (Δ[n] : SSet.{u}) ≅ CategoryTheory.nerve C :=
    SSet.stdSimplex.isoNerve.{u} n
  have hcomp : e.hom ≫ SSet.stdSimplex.isTerminalObj₀.from (CategoryTheory.nerve C) =
      SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hpre := MorphismProperty.RespectsIso.precomp
    SSet.realizationWeakEquivalences e.hom
      (SSet.stdSimplex.isTerminalObj₀.from (CategoryTheory.nerve C)) hn
  exact hcomp ▸ hpre

/-- Every standard-simplex map is weak, without a desired weak-map input. -/
private theorem standardSimplexMap_weak {A B : SimplexCategory}
    (a : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ SSet.stdSimplex.obj B) :
    SSet.realizationWeakEquivalences a := by
  let qm := SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj A)
  let qn := SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj B)
  have hfac : a ≫ qn = qm := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hcomp : SSet.realizationWeakEquivalences (a ≫ qn) :=
    hfac.symm ▸ standardSimplexToPoint_weak A
  exact SSet.realizationWeakEquivalences.of_postcomp a qn
    (standardSimplexToPoint_weak B) hcomp

/-- The transition square is the actual pullback square over the simplex map. -/
private theorem simplexTransition_isPullback {E B : SSet.{u}} (p : E ⟶ B)
    {s t : SSet.SimplexIndex B} (a : s ⟶ t) :
    IsPullback ((SSet.simplexPullbackDiagram p).map a)
      (pullback.snd p s.hom) (pullback.snd p t.hom) (SSet.stdSimplex.map a.left) := by
  have hout : IsPullback
      ((SSet.simplexPullbackDiagram p).map a ≫ pullback.fst p t.hom)
      (pullback.snd p s.hom) p (SSet.stdSimplex.map a.left ≫ t.hom) := by
    rw [SSet.simplexPullbackDiagram_map_fst, CostructuredArrow.w a]
    exact IsPullback.of_hasPullback p s.hom
  exact hout.of_right (SSet.simplexPullbackDiagram_map_snd p a)
    (IsPullback.of_hasPullback p t.hom)

/-- Right properness derives every actual Kan-fibration simplex transition. -/
private theorem simplexTransition_weak {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    {s t : SSet.SimplexIndex B} (a : s ⟶ t) :
    SSet.realizationWeakEquivalences ((SSet.simplexPullbackDiagram p).map a) := by
  let theta : (SSet.stdSimplex.obj s.left : SSet.{u}) ⟶ SSet.stdSimplex.obj t.left :=
    SSet.stdSimplex.map a.left
  have hWeak : WeakEquivalence theta :=
    (weakEquivalence_iff theta).mpr (standardSimplexMap_weak theta)
  have hFib : Fibration (pullback.snd p t.hom) :=
    SSet.fibration_of_isPullback (IsPullback.of_hasPullback p t.hom).flip
  have hw : WeakEquivalence ((SSet.simplexPullbackDiagram p).map a) :=
    @IsRightProper.weakEquivalence_of_isPullback SSet.{u} _ _ _ _
      _ _ _ _ (pullback.snd p s.hom) ((SSet.simplexPullbackDiagram p).map a)
      theta (pullback.snd p t.hom) (simplexTransition_isPullback p a).flip hFib hWeak
  exact (weakEquivalence_iff _).mp hw

/-- Homology uses the existing weak-equivalence chain theorem. -/
private theorem homologyMap_isIso_of_weak {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : SSet.realizationWeakEquivalences f) (R : AddCommGrpCat.{u}) (n : ℕ) :
    IsIso (SSet.homologyMap f R n) := by
  let : QuasiIso (SSet.chainComplexMap f R) := hf.quasiIso_chainComplexMap_addCommGrp R
  change IsIso (HomologicalComplex.homologyMap (SSet.chainComplexMap f R) n)
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance

/-- The coefficient functor is the actual simplex-fiber homology functor. -/
private noncomputable def fiberHomologyCoefficients {E B : SSet.{u}}
    (p : E ⟶ B) (n : ℕ) : SSet.SimplexIndex B ⥤ AddCommGrpCat.{u} :=
  SSet.simplexPullbackDiagram p ⋙ SSet.homologyFunctor integralCoefficients.{u} n

/-- Its actual transitions are isomorphisms, derived from the given fibration. -/
private theorem fiberHomologyCoefficients_map_isIso {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] (n : ℕ) {s t : SSet.SimplexIndex B} (a : s ⟶ t) :
    IsIso ((fiberHomologyCoefficients p n).map a) :=
  homologyMap_isIso_of_weak (simplexTransition_weak p a) integralCoefficients.{u} n

/-- The actual original projection gives the map to the identity-base diagram. -/
private noncomputable def projectionDiagramMap {E B : SSet.{u}} (p : E ⟶ B) :
    SSet.simplexPullbackDiagram p ⟶ SSet.simplexPullbackDiagram (𝟙 B) :=
  SSet.simplexPullbackDiagramMap p (Category.comp_id p)

/-- Its homology coefficient map is computed from that same projection. -/
private noncomputable def projectionCoefficientMap {E B : SSet.{u}}
    (p : E ⟶ B) (n : ℕ) :
    fiberHomologyCoefficients p n ⟶ fiberHomologyCoefficients (𝟙 B) n :=
  CategoryTheory.Functor.whiskerRight (projectionDiagramMap p) (SSet.homologyFunctor
    integralCoefficients.{u} n)

/-- The projection still has the whole original standard-simplex coordinate. -/
private theorem projectionCoefficientMap_comp_base {E B : SSet.{u}}
    (p : E ⟶ B) (n : ℕ) (s : SSet.SimplexIndex B) :
    (projectionCoefficientMap p n).app s ≫
        SSet.homologyMap (pullback.snd (𝟙 B) s.hom) integralCoefficients n =
      SSet.homologyMap (pullback.snd p s.hom) integralCoefficients n := by
  let H : SSet.{u} ⥤ AddCommGrpCat.{u} :=
    SSet.homologyFunctor (C := AddCommGrpCat.{u}) integralCoefficients.{u} n
  have hs : (projectionDiagramMap p).app s ≫ pullback.snd (𝟙 B) s.hom =
      pullback.snd p s.hom :=
    SSet.simplexPullbackDiagramMap_app_snd p (Category.comp_id p) s
  exact (H.map_comp _ _).symm.trans (congrArg H.map hs)

/-- The canonical identity-base object has its actual weak point projection. -/
private theorem baseDiagramPoint_weak (B : SSet.{u}) (s : SSet.SimplexIndex B) :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from
        ((SSet.simplexPullbackDiagram (𝟙 B)).obj s)) := by
  obtain ⟨A, a, rfl⟩ := CostructuredArrow.mk_surjective s
  obtain ⟨n⟩ := A
  let k : pullback (𝟙 B) a ⟶ (Δ[n] : SSet.{u}) := pullback.snd (𝟙 B) a
  let q := SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u})
  let : IsIso k := inferInstance
  have hk : SSet.realizationWeakEquivalences k :=
    SSet.realizationWeakEquivalences.of_isIso k
  have hcomp : k ≫ q = SSet.stdSimplex.isTerminalObj₀.from (pullback (𝟙 B) a) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact hcomp ▸ SSet.realizationWeakEquivalences.comp_mem _ _ hk
    (standardSimplexToPoint_weak ⦋n⦌)

/-- No desired coefficient trivialization is supplied for the identity base. -/
private noncomputable def basePointCoefficientIso (B : SSet.{u}) (n : ℕ) :
    fiberHomologyCoefficients (𝟙 B) n ≅
      (Functor.const (SSet.SimplexIndex B)).obj
        ((Δ[0] : SSet.{u}).homology integralCoefficients n) := by
  let H : SSet.{u} ⥤ AddCommGrpCat.{u} :=
    SSet.homologyFunctor (C := AddCommGrpCat.{u}) integralCoefficients.{u} n
  refine NatIso.ofComponents (fun s => ?_) ?_
  · let q : (SSet.simplexPullbackDiagram (𝟙 B)).obj s ⟶ (Δ[0] : SSet.{u}) :=
      SSet.stdSimplex.isTerminalObj₀.from ((SSet.simplexPullbackDiagram (𝟙 B)).obj s)
    let g : (fiberHomologyCoefficients (𝟙 B) n).obj s ⟶
        ((Δ[0] : SSet.{u}).homology integralCoefficients.{u} n) :=
      SSet.homologyMap q integralCoefficients.{u} n
    have hg : IsIso g :=
      homologyMap_isIso_of_weak (baseDiagramPoint_weak B s) integralCoefficients.{u} n
    exact @asIso _ _ _ _ g hg
  · intro s t a
    let qs : (SSet.simplexPullbackDiagram (𝟙 B)).obj s ⟶ (Δ[0] : SSet.{u}) :=
      SSet.stdSimplex.isTerminalObj₀.from ((SSet.simplexPullbackDiagram (𝟙 B)).obj s)
    let qt : (SSet.simplexPullbackDiagram (𝟙 B)).obj t ⟶ (Δ[0] : SSet.{u}) :=
      SSet.stdSimplex.isTerminalObj₀.from ((SSet.simplexPullbackDiagram (𝟙 B)).obj t)
    have h : (SSet.simplexPullbackDiagram (𝟙 B)).map a ≫ qt = qs :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    change H.map ((SSet.simplexPullbackDiagram (𝟙 B)).map a) ≫ H.map qt = H.map qs ≫ 𝟙 _
    exact (H.map_comp _ _).symm.trans
      ((congrArg H.map h).trans (Category.comp_id _).symm)

private theorem point_isConnected : (Δ[0] : SSet.{u}).IsConnected := by
  apply (SSet.isConnected_iff (X := (Δ[0] : SSet.{u}))).mpr
  constructor
  · constructor
    intro a b
    obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective a
    obtain ⟨y, rfl⟩ := SSet.π₀.mk_surjective b
    apply congrArg SSet.π₀.mk
    apply SSet.stdSimplex.obj₀Equiv.injective
    exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
  · exact ⟨SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)⟩

/-- The identity-base row zero is the actual integral constant coefficient. -/
private noncomputable def baseZeroCoefficientIso (B : SSet.{u}) :
    fiberHomologyCoefficients (𝟙 B) 0 ≅
      (Functor.const (SSet.SimplexIndex B)).obj integralCoefficients := by
  letI : (Δ[0] : SSet.{u}).IsConnected := point_isConnected
  exact basePointCoefficientIso B 0 ≪≫
    (CategoryTheory.Functor.const (SSet.SimplexIndex B)).mapIso
      (asIso ((Δ[0] : SSet.{u}).homology₀ε integralCoefficients.{u}))

/-- The row-zero map is the actual projection, followed by its computed base coordinate. -/
private noncomputable def rowZeroProjection {E B : SSet.{u}} (p : E ⟶ B) :
    fiberHomologyCoefficients p 0 ⟶
      (Functor.const (SSet.SimplexIndex B)).obj integralCoefficients :=
  projectionCoefficientMap p 0 ≫ (baseZeroCoefficientIso B).hom


/-- The computed identity-base row uses the exact point augmentation. -/
private theorem baseZeroCoefficientIso_hom_app (B : SSet.{u}) (s : SSet.SimplexIndex B) :
    (baseZeroCoefficientIso B).hom.app s =
      SSet.homologyMap
          (SSet.stdSimplex.isTerminalObj₀.from
            ((SSet.simplexPullbackDiagram (𝟙 B)).obj s)) integralCoefficients 0 ≫
        (Δ[0] : SSet.{u}).homology₀ε integralCoefficients := by
  let R : AddCommGrpCat.{u} := integralCoefficients.{u}
  let ε : (Δ[0] : SSet.{u}).homology R 0 ⟶ R := (Δ[0] : SSet.{u}).homology₀ε R
  have hp : (basePointCoefficientIso B 0).hom.app s =
      SSet.homologyMap (SSet.stdSimplex.isTerminalObj₀.from
        ((SSet.simplexPullbackDiagram (𝟙 B)).obj s)) R 0 := by
    dsimp only [basePointCoefficientIso]
    rfl
  change (basePointCoefficientIso B 0).hom.app s ≫ ε =
    SSet.homologyMap (SSet.stdSimplex.isTerminalObj₀.from
      ((SSet.simplexPullbackDiagram (𝟙 B)).obj s)) R 0 ≫ ε
  exact congrArg (fun f => f ≫ ε) hp

/-- Every row-zero component is the original actual point projection. -/
private theorem rowZeroProjection_app {E B : SSet.{u}}
    (p : E ⟶ B) (s : SSet.SimplexIndex B) :
    (rowZeroProjection p).app s =
      SSet.homologyMap
          (SSet.stdSimplex.isTerminalObj₀.from
            ((SSet.simplexPullbackDiagram p).obj s)) integralCoefficients 0 ≫
        (Δ[0] : SSet.{u}).homology₀ε integralCoefficients := by
  let H : SSet.{u} ⥤ AddCommGrpCat.{u} :=
    SSet.homologyFunctor (C := AddCommGrpCat.{u}) integralCoefficients.{u} 0
  let a := (projectionDiagramMap p).app s
  let qs := SSet.stdSimplex.isTerminalObj₀.from
      ((SSet.simplexPullbackDiagram p).obj s)
  let qt := SSet.stdSimplex.isTerminalObj₀.from
      ((SSet.simplexPullbackDiagram (𝟙 B)).obj s)
  let e : H.obj (Δ[0] : SSet.{u}) ⟶ integralCoefficients.{u} :=
    (Δ[0] : SSet.{u}).homology₀ε integralCoefficients.{u}
  have hcomp : a ≫ qt = qs := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hbase : (baseZeroCoefficientIso B).hom.app s = H.map qt ≫ e :=
    baseZeroCoefficientIso_hom_app B s
  change H.map a ≫ (baseZeroCoefficientIso B).hom.app s = H.map qs ≫ e
  exact (congrArg (fun k => H.map a ≫ k) hbase).trans
    ((Category.assoc (H.map a) (H.map qt) e).symm.trans
      ((congrArg (fun q => q ≫ e) (H.map_comp a qt).symm).trans
        (congrArg (fun q => H.map q ≫ e) hcomp)))

/-- The row-zero E2 coefficient projection is built from the same actual map. -/
private noncomputable def rowZeroSecondPageProjection {E B : SSet.{u}}
    (p : E ⟶ B) (n : ℕ) :
    ((SSet.bkHomologySpectralSequence integralCoefficients
        (SSet.simplexPullbackDiagram p)).page 2).X (n, 0) ⟶
      CategoryTheory.CategoryHomology.homologyWithCoefficients
        ((Functor.const (SSet.SimplexIndex B)).obj integralCoefficients) n :=
  (SSet.bkSecondPageCoefficientHomologyIso integralCoefficients.{u}
      (SSet.simplexPullbackDiagram p) n 0).hom ≫
    (CategoryTheory.CategoryHomology.homologyWithCoefficientsFunctor
      (C := SSet.SimplexIndex B) (A := AddCommGrpCat.{u}) n).map (rowZeroProjection p)

/-- The original projection also calibrates the whole total homology map. -/
private theorem resolutionHomology_projection {E B : SSet.{u}}
    (p : E ⟶ B) (n : ℕ) :
    SSet.homologyMap (SSet.simplexResolutionMap p (Category.comp_id p))
        integralCoefficients n ≫
      SSet.homologyMap (SSet.simplexResolutionAugmentation (𝟙 B)) integralCoefficients n =
    SSet.homologyMap (SSet.simplexResolutionAugmentation p) integralCoefficients n ≫
      SSet.homologyMap p integralCoefficients n := by
  let H : SSet.{u} ⥤ AddCommGrpCat.{u} :=
    SSet.homologyFunctor (C := AddCommGrpCat.{u}) integralCoefficients.{u} n
  change H.map (SSet.simplexResolutionMap p (Category.comp_id p)) ≫
      H.map (SSet.simplexResolutionAugmentation (𝟙 B)) =
    H.map (SSet.simplexResolutionAugmentation p) ≫ H.map p
  exact (H.map_comp _ _).symm.trans
    ((congrArg H.map (SSet.simplexResolutionAugmentation_naturality p (Category.comp_id p))).trans
      (H.map_comp _ _))

/-- The resolution's homology isomorphism is induced by its same actual augmentation. -/
private noncomputable def resolutionHomologyIso {E B : SSet.{u}}
    (p : E ⟶ B) (n : ℕ) :
    (SSet.simplexResolution p).homology integralCoefficients n ≅
      E.homology integralCoefficients n := by
  letI : IsIso (SSet.homologyMap (SSet.simplexResolutionAugmentation p) integralCoefficients.{u} n)
    :=
    homologyMap_isIso_of_weak
      (SSet.simplexResolutionAugmentation_mem_realizationWeakEquivalences p)
      integralCoefficients.{u} n
  exact asIso (SSet.homologyMap (SSet.simplexResolutionAugmentation p) integralCoefficients.{u} n)


/-- The strict fiber is connected by the actual exact sequence at π₀. -/
private theorem pointedStrictFiber_isConnected (S : SSet.FibrationSequence.{u})
    [S.E.IsConnected]
    (hπ : Subsingleton (SSet.KanComplex.π 1 S.B S.b)) :
    S.fiber.IsConnected := by
  let : Subsingleton (SSet.KanComplex.π 1 S.B S.b) := hπ
  let : Subsingleton (SSet.KanComplex.π 0 S.E S.e) :=
    (SSet.KanComplex.π₀EquivπZero S.e).subsingleton_congr.mp inferInstance
  have hunit : S.connectingMap (n := 0)
      (1 : SSet.KanComplex.π 1 S.B S.b) = 1 := by
    let q : SSet.KanComplex.π 1 S.E S.e := 1
    have hq : SSet.KanComplex.π.map S.p S.hb 1 q = 1 :=
      Subsingleton.elim _ _
    exact (congrArg (S.connectingMap (n := 0)) hq).symm.trans
      (S.connectingMap_map_eq_one q)
  have hzero : ∀ q : SSet.KanComplex.π 0 S.fiber S.fiberPoint, q = 1 := by
    intro q
    have hq : SSet.KanComplex.π.map S.fiberIncl rfl 0 q = 1 := by
      change SSet.KanComplex.π.map S.fiberIncl
        (show S.fiberIncl.app (Opposite.op ⦋0⦌) S.fiberPoint = S.e from rfl) 0 q =
          (1 : SSet.KanComplex.π 0 S.E S.e)
      exact Subsingleton.elim _ _
    obtain ⟨r, hr⟩ := S.exactness_at_fiber q hq
    exact hr.symm.trans
      ((congrArg (S.connectingMap (n := 0)) (Subsingleton.elim r 1)).trans hunit)
  let : Subsingleton (SSet.KanComplex.π 0 S.fiber S.fiberPoint) :=
    ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  apply (SSet.isConnected_iff (X := S.fiber)).mpr
  exact ⟨(SSet.KanComplex.π₀EquivπZero S.fiberPoint).subsingleton_congr.mpr
      inferInstance, ⟨S.fiberPoint⟩⟩

/-- A Kan connected base supplies an edge between the specified actual vertices. -/
private theorem connectedBase_edge {B : SSet.{u}} [SSet.KanComplex B]
    [B.IsConnected] (b₀ b₁ : B _⦋0⦌) : Nonempty (B.Edge b₀ b₁) := by
  have h : SSet.π₀.mk b₀ = SSet.π₀.mk b₁ := Subsingleton.elim _ _
  rw [SSet.π₀.mk_eq_mk_iff] at h
  induction h with
  | rel _ _ h => exact h
  | refl => exact ⟨SSet.Edge.id _⟩
  | symm _ _ _ ih => exact ⟨ih.some.inv⟩
  | trans _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.some.comp ih₂.some⟩

/-- A nonempty original subcomplex contains an actual vertex. -/
private theorem nonemptySubcomplex_vertex {X : SSet.{u}} (A : X.Subcomplex)
    (hA : A ≠ ⊥) : ∃ x : X _⦋0⦌, x ∈ A.obj (Opposite.op ⦋0⦌) := by
  by_contra hnone
  push Not at hnone
  have hle : A ≤ ⊥ := by
    intro n x hx
    have hzero : X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op x ∈
        A.obj (Opposite.op ⦋0⦌) := A.map _ hx
    exact (hnone _ hzero).elim
  exact hA (le_antisymm hle bot_le)

/-- The given fibration lifts an arbitrary base vertex from a computed source vertex. -/
private theorem strictFiber_exists_point {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [E.IsConnected] [SSet.KanComplex B] [B.IsConnected]
    (b : B _⦋0⦌) : ∃ e : E _⦋0⦌, p.app (Opposite.op ⦋0⦌) e = b := by
  let e₀ : E _⦋0⦌ := Classical.arbitrary _
  let b₀ : B _⦋0⦌ := p.app (Opposite.op ⦋0⦌) e₀
  have hsource : SSet.Subcomplex.fiber p b₀ ≠ ⊥ := by
    intro h
    have he : e₀ ∈ (SSet.Subcomplex.fiber p b₀).obj (Opposite.op ⦋0⦌) :=
      (SSet.Subcomplex.mem_fiber_obj_zero_iff p b₀).mpr rfl
    rw [h] at he
    change e₀ ∈ (∅ : Set (E _⦋0⦌)) at he
    exact he
  obtain ⟨edge⟩ := connectedBase_edge b₀ b
  have htarget : SSet.Subcomplex.fiber p b ≠ ⊥ :=
    (SSet.Subcomplex.fiber_neq_bot_iff_of_edge p edge).mp hsource
  obtain ⟨e, he⟩ := nonemptySubcomplex_vertex (SSet.Subcomplex.fiber p b) htarget
  exact ⟨e, (SSet.Subcomplex.mem_fiber_obj_zero_iff p b).mp he⟩

/-- Every actual strict fiber is connected over a one-connected Kan base. -/
private theorem strictFiber_isConnected {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [E.IsConnected] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b))
    (b : B _⦋0⦌) : (SSet.Subcomplex.fiber p b : SSet.{u}).IsConnected := by
  obtain ⟨e, he⟩ := strictFiber_exists_point p b
  let S : SSet.FibrationSequence.{u} :=
    { E := E
      B := B
      p := p
      fibration_p := inferInstance
      fibrant_B := inferInstance
      e := e
      b := b
      hb := he }
  exact pointedStrictFiber_isConnected S (hπ b)

/-- A weak realization map transports connectedness using its original component map. -/
private theorem isConnected_of_weak {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : SSet.realizationWeakEquivalences f) [X.IsConnected] : Y.IsConnected := by
  apply (SSet.isConnected_iff (X := Y)).mpr
  constructor
  · constructor
    intro a b
    obtain ⟨a₀, rfl⟩ := hf.bijective_mapπ₀.2 a
    obtain ⟨b₀, rfl⟩ := hf.bijective_mapπ₀.2 b
    exact congrArg (SSet.mapπ₀ f) (Subsingleton.elim a₀ b₀)
  · exact ⟨f.app (Opposite.op ⦋0⦌) (Classical.arbitrary _)⟩

/-- The first vertex remains an actual object of the original simplex category. -/
private def firstVertexSimplex {B : SSet.{u}} (s : SSet.SimplexIndex B) :
    SSet.SimplexIndex B :=
  CostructuredArrow.mk
    (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ s.left 0) ≫ s.hom)

/-- Its inclusion is the literal original standard-simplex vertex map. -/
private def firstVertexInclusion {B : SSet.{u}} (s : SSet.SimplexIndex B) :
    firstVertexSimplex s ⟶ s :=
  CostructuredArrow.homMk (SimplexCategory.const ⦋0⦌ s.left 0) rfl

private def firstVertexBasePoint {B : SSet.{u}} (s : SSet.SimplexIndex B) : B _⦋0⦌ :=
  SSet.yonedaEquiv (firstVertexSimplex s).hom

private theorem firstVertexSimplex_hom {B : SSet.{u}} (s : SSet.SimplexIndex B) :
    (firstVertexSimplex s).hom = SSet.const (X := (Δ[0] : SSet.{u}))
      (firstVertexBasePoint s) := by
  change (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ s.left 0) ≫ s.hom :
      (Δ[0] : SSet.{u}) ⟶ B) = SSet.const (X := (Δ[0] : SSet.{u})) (firstVertexBasePoint s)
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_const]
  rfl

/-- The first vertex pullback is the same original strict fiber, by the pullback UP. -/
private noncomputable def firstVertexStrictFiberIso {E B : SSet.{u}}
    (p : E ⟶ B) (s : SSet.SimplexIndex B) :
    (SSet.Subcomplex.fiber p (firstVertexBasePoint s) : SSet.{u}) ≅
      (SSet.simplexPullbackDiagram p).obj (firstVertexSimplex s) := by
  change (SSet.Subcomplex.fiber p (firstVertexBasePoint s) : SSet.{u}) ≅
    pullback p (firstVertexSimplex s).hom
  rw [firstVertexSimplex_hom]
  exact (SSet.Subcomplex.fiber_isPullback p (firstVertexBasePoint s)).isoPullback

/-- Every original simplex pullback is connected, using its derived weak vertex transition. -/
private theorem simplexPullback_isConnected {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [E.IsConnected] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b))
    (s : SSet.SimplexIndex B) : ((SSet.simplexPullbackDiagram p).obj s).IsConnected := by
  let : (SSet.Subcomplex.fiber p (firstVertexBasePoint s) : SSet.{u}).IsConnected :=
    strictFiber_isConnected p hπ (firstVertexBasePoint s)
  let : ((SSet.simplexPullbackDiagram p).obj (firstVertexSimplex s)).IsConnected :=
    isConnected_of_weak
      (SSet.realizationWeakEquivalences.of_isIso (firstVertexStrictFiberIso p s).hom)
  exact isConnected_of_weak (simplexTransition_weak p (firstVertexInclusion s))

/-- The computed row-zero component is the stock homology augmentation of the actual object. -/
private theorem rowZeroProjection_app_eq_augmentation {E B : SSet.{u}}
    (p : E ⟶ B) (s : SSet.SimplexIndex B) :
    (rowZeroProjection p).app s =
      ((SSet.simplexPullbackDiagram p).obj s).homology₀ε integralCoefficients := by
  rw [rowZeroProjection_app]
  exact SSet.homologyMap_comp_homology₀ε _ integralCoefficients.{u}

/-- The actual row-zero component is invertible; no edge-calibration witness is supplied. -/
private theorem rowZeroProjection_app_isIso {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [E.IsConnected] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b))
    (s : SSet.SimplexIndex B) : IsIso ((rowZeroProjection p).app s) := by
  let K : SSet.{u} := (SSet.simplexPullbackDiagram p).obj s
  let R : AddCommGrpCat.{u} := integralCoefficients.{u}
  let : K.IsConnected := simplexPullback_isConnected p hπ s
  have hε : IsIso (K.homology₀ε R) := inferInstance
  have h : (rowZeroProjection p).app s = K.homology₀ε R :=
    rowZeroProjection_app_eq_augmentation p s
  exact Eq.mp (congrArg (fun f : K.homology R 0 ⟶ R => IsIso f) h.symm) hε

/-- The entire row-zero coefficient isomorphism is computed from the original projection. -/
private noncomputable def rowZeroCoefficientIso {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [E.IsConnected] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b)) :
    fiberHomologyCoefficients p 0 ≅
      (Functor.const (SSet.SimplexIndex B)).obj integralCoefficients := by
  letI : ∀ s, IsIso ((rowZeroProjection p).app s) :=
    fun s => rowZeroProjection_app_isIso p hπ s
  letI : IsIso (rowZeroProjection p) := NatIso.isIso_of_isIso_app _
  exact asIso (rowZeroProjection p)

/-- The coefficient-induced second-page row-zero map is invertible. Its spectral
page-map identification is a separate proof obligation, not an assumption. -/
private theorem rowZeroSecondPageProjection_isIso {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [E.IsConnected] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b)) (n : ℕ) :
    IsIso (rowZeroSecondPageProjection p n) := by
  let H : (SSet.SimplexIndex B ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
    CategoryTheory.CategoryHomology.homologyWithCoefficientsFunctor
      (C := SSet.SimplexIndex B) (A := AddCommGrpCat.{u}) n
  let e := SSet.bkSecondPageCoefficientHomologyIso integralCoefficients.{u}
    (SSet.simplexPullbackDiagram p) n 0 ≪≫ H.mapIso (rowZeroCoefficientIso p hπ)
  have he : e.hom = rowZeroSecondPageProjection p n := by
    change (SSet.bkSecondPageCoefficientHomologyIso integralCoefficients.{u}
        (SSet.simplexPullbackDiagram p) n 0).hom ≫
        H.map (rowZeroCoefficientIso p hπ).hom =
      (SSet.bkSecondPageCoefficientHomologyIso integralCoefficients.{u}
        (SSet.simplexPullbackDiagram p) n 0).hom ≫ H.map (rowZeroProjection p)
    rfl
  exact Eq.mp (congrArg (fun f => IsIso f) he) e.isIso_hom

/-- The existing alternating-to-normalized homology comparison is natural,
using its actual P-infinity retraction and not an added comparison witness. -/
private theorem coefficientBarNormalization_naturality
    {J : Type u} [Category.{0} J] {M N : J ⥤ AddCommGrpCat.{u}}
    (α : M ⟶ N) (n : ℕ) :
    HomologicalComplex.homologyMap
          ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map
            (CategoryTheory.CategoryHomology.coefficientBarSimplicialMap α)) n ≫
        ((AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
          (Y := CategoryTheory.CategoryHomology.coefficientBarSimplicial N)).toHomologyIso n).inv =
      ((AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
          (Y := CategoryTheory.CategoryHomology.coefficientBarSimplicial M)).toHomologyIso n).inv ≫
        (CategoryTheory.CategoryHomology.homologyWithCoefficientsFunctor
          (C := J) (A := AddCommGrpCat.{u}) n).map α := by
  let f := CategoryTheory.CategoryHomology.coefficientBarSimplicialMap α
  change HomologicalComplex.homologyMap
      ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map f) n ≫
      HomologicalComplex.homologyMap
        (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex
          (CategoryTheory.CategoryHomology.coefficientBarSimplicial N)) n =
    HomologicalComplex.homologyMap
        (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex
          (CategoryTheory.CategoryHomology.coefficientBarSimplicial M)) n ≫
      HomologicalComplex.homologyMap
        ((AlgebraicTopology.normalizedMooreComplex AddCommGrpCat.{u}).map f) n
  exact HomologicalComplex.homologyMap_square
    (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_naturality f) n

/-- The entire existing BK second-page coefficient comparison is natural for
its actual fixed spectral-page map, not merely for a newly defined coefficient map. -/
private theorem bkSecondPageCoefficientHomologyIso_naturality
    {J : Type u} [Category.{0} J] {D E : J ⥤ SSet.{u}}
    (α : D ⟶ E) (p q : ℕ) :
    HomologicalComplex₂.horizontalSecondPageMapOfBicomplex
          ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients).map α) p q ≫
        (SSet.bkSecondPageCoefficientHomologyIso integralCoefficients E p q).hom =
      (SSet.bkSecondPageCoefficientHomologyIso integralCoefficients D p q).hom ≫
        (CategoryTheory.CategoryHomology.homologyWithCoefficientsFunctor
          (C := J) (A := AddCommGrpCat.{u}) p).map
          (Functor.whiskerRight α (SSet.homologyFunctor integralCoefficients q)) := by
  let K := SSet.bkAlternatingBicomplex AddCommGrpCat.{u} integralCoefficients.{u} D
  let L := SSet.bkAlternatingBicomplex AddCommGrpCat.{u} integralCoefficients.{u} E
  let f : K ⟶ L :=
    (SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients.{u}).map α
  let β := CategoryTheory.Functor.whiskerRight α (SSet.homologyFunctor integralCoefficients.{u} q)
  let aD := (HomologicalComplex₂.horizontalSecondPageVerticalHorizontalHomologyIso K p q).hom
  let aE := (HomologicalComplex₂.horizontalSecondPageVerticalHorizontalHomologyIso L p q).hom
  let bD := HomologicalComplex.homologyMap
    (SSet.bkVerticalHomologyCoefficientBarComplexIso integralCoefficients.{u} D q).hom p
  let bE := HomologicalComplex.homologyMap
    (SSet.bkVerticalHomologyCoefficientBarComplexIso integralCoefficients.{u} E q).hom p
  let cD := ((AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
    (Y := CategoryTheory.CategoryHomology.coefficientBarSimplicial
      (D ⋙ SSet.homologyFunctor integralCoefficients.{u} q))).toHomologyIso p).inv
  let cE := ((AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
    (Y := CategoryTheory.CategoryHomology.coefficientBarSimplicial
      (E ⋙ SSet.homologyFunctor integralCoefficients.{u} q))).toHomologyIso p).inv
  let v := HomologicalComplex.homologyMap
    (HomologicalComplex₂.verticalHomologyComplexMap f q) p
  let b := HomologicalComplex.homologyMap
    ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (CategoryTheory.CategoryHomology.coefficientBarSimplicialMap β)) p
  let h := (CategoryTheory.CategoryHomology.homologyWithCoefficientsFunctor
    (C := J) (A := AddCommGrpCat.{u}) p).map β
  have hfirst : HomologicalComplex₂.horizontalSecondPageMapOfBicomplex f p q ≫ aE = aD ≫ v :=
    HomologicalComplex₂.horizontalSecondPageVerticalHorizontalHomologyIso_hom_naturality f p q
  have hbar : v ≫ bE = bD ≫ b := by
    have h := SSet.bkVerticalHomologyCoefficientBarComplexIso_hom_naturality
      integralCoefficients.{u} α q
    change HomologicalComplex₂.verticalHomologyComplexMap f q ≫
      (SSet.bkVerticalHomologyCoefficientBarComplexIso integralCoefficients.{u} E q).hom =
      (SSet.bkVerticalHomologyCoefficientBarComplexIso integralCoefficients.{u} D q).hom ≫
        (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map
          (CategoryTheory.CategoryHomology.coefficientBarSimplicialMap β) at h
    exact HomologicalComplex.homologyMap_square h p
  have hnorm : b ≫ cE = cD ≫ h := coefficientBarNormalization_naturality β p
  have sqA : CommSq (HomologicalComplex₂.horizontalSecondPageMapOfBicomplex f p q)
      aD aE v := ⟨hfirst⟩
  have sqB : CommSq v bD bE b := ⟨hbar⟩
  have sqC : CommSq b cD cE h := ⟨hnorm⟩
  have hs := (sqA.vert_comp (sqB.vert_comp sqC)).w
  change HomologicalComplex₂.horizontalSecondPageMapOfBicomplex f p q ≫
      (aE ≫ (bE ≫ cE)) = (aD ≫ (bD ≫ cD)) ≫ h
  exact hs

/-- The actual page-two projection equals the computed row-zero coefficient map. -/
private theorem actualSecondPageProjection_rowZero {E B : SSet.{u}}
    (p : E ⟶ B) (n : ℕ) :
    HomologicalComplex₂.horizontalSecondPageMapOfBicomplex
          ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients).map
            (projectionDiagramMap p)) n 0 ≫
        (SSet.bkSecondPageCoefficientHomologyIso integralCoefficients
          (SSet.simplexPullbackDiagram (𝟙 B)) n 0).hom ≫
        (CategoryTheory.CategoryHomology.homologyWithCoefficientsFunctor
          (C := SSet.SimplexIndex B) (A := AddCommGrpCat.{u}) n).map
          (baseZeroCoefficientIso B).hom =
      rowZeroSecondPageProjection p n := by
  let H : (SSet.SimplexIndex B ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
    CategoryTheory.CategoryHomology.homologyWithCoefficientsFunctor
      (C := SSet.SimplexIndex B) (A := AddCommGrpCat.{u}) n
  let φ := HomologicalComplex₂.horizontalSecondPageMapOfBicomplex
    ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients.{u}).map
      (projectionDiagramMap p)) n 0
  let a := (SSet.bkSecondPageCoefficientHomologyIso integralCoefficients.{u}
    (SSet.simplexPullbackDiagram (𝟙 B)) n 0).hom
  let b := (SSet.bkSecondPageCoefficientHomologyIso integralCoefficients.{u}
    (SSet.simplexPullbackDiagram p) n 0).hom
  let β := projectionCoefficientMap p 0
  let η := (baseZeroCoefficientIso B).hom
  have hnat : φ ≫ a = b ≫ H.map β :=
    bkSecondPageCoefficientHomologyIso_naturality (projectionDiagramMap p) n 0
  have hm : H.map β ≫ H.map η = H.map (β ≫ η) := (H.map_comp β η).symm
  change φ ≫ (a ≫ H.map η) = b ≫ H.map (β ≫ η)
  exact (Category.assoc φ a (H.map η)).symm.trans
    ((congrArg (fun t => t ≫ H.map η) hnat).trans
      ((Category.assoc b (H.map β) (H.map η)).trans
        (congrArg (fun t => b ≫ t) hm)))

/-- The original fixed second-page projection on row zero is invertible. -/
private theorem actualSecondPageProjection_rowZero_isIso {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [E.IsConnected] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b)) (n : ℕ) :
    IsIso (HomologicalComplex₂.horizontalSecondPageMapOfBicomplex
      ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients).map
        (projectionDiagramMap p)) n 0) := by
  let H : (SSet.SimplexIndex B ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
    CategoryTheory.CategoryHomology.homologyWithCoefficientsFunctor
      (C := SSet.SimplexIndex B) (A := AddCommGrpCat.{u}) n
  let φ := HomologicalComplex₂.horizontalSecondPageMapOfBicomplex
    ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients.{u}).map
      (projectionDiagramMap p)) n 0
  let e := SSet.bkSecondPageCoefficientHomologyIso integralCoefficients.{u}
    (SSet.simplexPullbackDiagram (𝟙 B)) n 0 ≪≫ H.mapIso (baseZeroCoefficientIso B)
  let : IsIso e.hom := e.isIso_hom
  have he : φ ≫ e.hom = rowZeroSecondPageProjection p n :=
    actualSecondPageProjection_rowZero p n
  have hrow : IsIso (rowZeroSecondPageProjection p n) := rowZeroSecondPageProjection_isIso p hπ n
  let : IsIso (φ ≫ e.hom) :=
    Eq.mp (congrArg (fun f => IsIso f) he.symm) hrow
  exact (isIso_comp_right_iff φ e.hom).mp inferInstance

/-- BK total homology is identified with the same actual source by its existing
Alexander--Whitney comparison and actual augmentation. -/
private noncomputable def originalTotalHomologyIso {E B : SSet.{u}}
    (p : E ⟶ B) (n : ℕ) :
    (SSet.bkAlternatingTotalComplex AddCommGrpCat.{u} integralCoefficients
      (SSet.simplexPullbackDiagram p)).homology n ≅ E.homology integralCoefficients n :=
  (SSet.bkDiagonalTotalHomologyIso integralCoefficients.{u}
      (SSet.simplexPullbackDiagram p) n).symm ≪≫
    (HomologicalComplex.homologyMapIso
      (SSet.bkCarrierChainIso AddCommGrpCat.{u} integralCoefficients.{u}
        (SSet.simplexPullbackDiagram p)) n).symm ≪≫
    resolutionHomologyIso p n

/-- The actual total-bicomplex map is the original map on homology under those fixed coordinates. -/
private theorem originalTotalHomology_projection {E B : SSet.{u}}
    (p : E ⟶ B) (n : ℕ) :
    HomologicalComplex.homologyMap
          ((SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{u} integralCoefficients).map
            (projectionDiagramMap p)) n ≫
        (originalTotalHomologyIso (𝟙 B) n).hom =
      (originalTotalHomologyIso p n).hom ≫ SSet.homologyMap p integralCoefficients n := by
  let D := SSet.simplexPullbackDiagram p
  let E := SSet.simplexPullbackDiagram (𝟙 B)
  let α := projectionDiagramMap p
  let aD := SSet.bkDiagonalTotalHomologyIso integralCoefficients.{u} D n
  let aE := SSet.bkDiagonalTotalHomologyIso integralCoefficients.{u} E n
  let bD := HomologicalComplex.homologyMapIso
    (SSet.bkCarrierChainIso AddCommGrpCat.{u} integralCoefficients.{u} D) n
  let bE := HomologicalComplex.homologyMapIso
    (SSet.bkCarrierChainIso AddCommGrpCat.{u} integralCoefficients.{u} E) n
  let rD := (resolutionHomologyIso p n).hom
  let rE := (resolutionHomologyIso (𝟙 B) n).hom
  let f := HomologicalComplex.homologyMap
    ((SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{u} integralCoefficients.{u}).map α) n
  let c := HomologicalComplex.homologyMap
    ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map
      ((SSet.coproductLinearizationFunctor AddCommGrpCat.{u} integralCoefficients.{u}).map
        (SSet.bkHocolimMap α))) n
  let h := SSet.homologyMap (SSet.simplexResolutionMap p (Category.comp_id p))
    integralCoefficients.{u} n
  have haw : c ≫ aE.hom = aD.hom ≫ f :=
    SSet.bkDiagonalTotalHomologyIso_naturality integralCoefficients.{u} α n
  have hcarrier : h ≫ bE.hom = bD.hom ≫ c := by
    have hchain : SSet.chainComplexMap
          (SSet.simplexResolutionMap p (Category.comp_id p)) integralCoefficients.{u} ≫
        (SSet.bkCarrierChainIso AddCommGrpCat.{u} integralCoefficients.{u} E).hom =
      (SSet.bkCarrierChainIso AddCommGrpCat.{u} integralCoefficients.{u} D).hom ≫
        (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map
          ((SSet.coproductLinearizationFunctor AddCommGrpCat.{u} integralCoefficients.{u}).map
            (SSet.bkHocolimMap α)) :=
      SSet.bkCarrierChainIso_naturality AddCommGrpCat.{u} integralCoefficients.{u} α
    exact HomologicalComplex.homologyMap_square hchain n
  have hr : h ≫ rE = rD ≫ SSet.homologyMap p integralCoefficients.{u} n :=
    resolutionHomology_projection p n
  have sqA : CommSq c aD.hom aE.hom f := ⟨haw⟩
  have sqB : CommSq h bD.hom bE.hom c := ⟨hcarrier⟩
  have sqR : CommSq h rD rE (SSet.homologyMap p integralCoefficients.{u} n) := ⟨hr⟩
  have hs := (sqA.vert_inv.vert_comp (sqB.vert_inv.vert_comp sqR)).w
  change f ≫ (aE.inv ≫ (bE.inv ≫ rE)) =
    (aD.inv ≫ (bD.inv ≫ rD)) ≫ SSet.homologyMap p integralCoefficients.{u} n
  exact hs

/-- Surjectivity/injectivity of the actual original homology map is retained
by the fixed total coordinates; no unrelated abutment isomorphism is supplied. -/
private theorem originalTotalHomology_projection_isIso {E B : SSet.{u}}
    (p : E ⟶ B) (n : ℕ) [IsIso (SSet.homologyMap p integralCoefficients n)] :
    IsIso (HomologicalComplex.homologyMap
      ((SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{u} integralCoefficients).map
        (projectionDiagramMap p)) n) := by
  let f := HomologicalComplex.homologyMap
    ((SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{u} integralCoefficients.{u}).map
      (projectionDiagramMap p)) n
  let e := (originalTotalHomologyIso (𝟙 B) n).hom
  let : IsIso (f ≫ e) := by
    dsimp only [f, e]
    rw [originalTotalHomology_projection]
    infer_instance
  exact (isIso_comp_right_iff f e).mp inferInstance

/-- The stable page map retains the canonical associated-graded filtration coordinate. -/
private theorem stablePageProjection_graded {E B : SSet.{u}}
    (p : E ⟶ B) (a b : ℕ) :
    HomologicalComplex₂.horizontalStablePageMapOfBicomplex
          ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients).map
            (projectionDiagramMap p)) a b ≫
        (HomologicalComplex₂.horizontalStablePageGradedIsoAtIndex
          (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} integralCoefficients
            (SSet.simplexPullbackDiagram (𝟙 B))) a b).hom =
      (HomologicalComplex₂.horizontalStablePageGradedIsoAtIndex
          (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} integralCoefficients
            (SSet.simplexPullbackDiagram p)) a b).hom ≫
        HomologicalComplex₂.horizontalTotalHomologyGradedPieceMapOfBicomplex
          ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients).map
            (projectionDiagramMap p)) a b :=
  HomologicalComplex₂.horizontalStablePageGradedIsoAtIndex_naturality _ a b

/-- Positive homology of each identity-base simplex object vanishes using
its computed point isomorphism and the stock dimension bound for Δ[0]. -/
private theorem basePositiveCoefficient_obj_isZero (B : SSet.{u})
    (q : ℕ) (hq : 1 ≤ q) (s : SSet.SimplexIndex B) :
    IsZero ((fiberHomologyCoefficients (𝟙 B) q).obj s) := by
  have hp : IsZero ((Δ[0] : SSet.{u}).homology integralCoefficients.{u} q) :=
    SSet.isZero_homology_of_hasDimensionLT (Δ[0] : SSet.{u}) integralCoefficients.{u} q 1 hq
  exact IsZero.of_iso hp ((basePointCoefficientIso B q).app s)

/-- A pointwise-zero coefficient system has zero category homology in every
degree by the existing bar coproduct universal property and normalization. -/
private theorem categoryHomology_isZero_of_coefficients_zero
    {J : Type u} [Category.{0} J] (M : J ⥤ AddCommGrpCat.{u})
    (hM : ∀ j : J, IsZero (M.obj j)) (n : ℕ) :
    IsZero (CategoryTheory.CategoryHomology.homologyWithCoefficients M n) := by
  let K := CategoryTheory.CategoryHomology.coefficientBarComplex M
  have hx : IsZero (K.X n) := by
    change IsZero ((CategoryTheory.CategoryHomology.coefficientBarSimplicial M).obj
      (Opposite.op ⦋n⦌))
    rw [CategoryTheory.CategoryHomology.coefficientBarSimplicial_obj]
    change IsZero (∐ CategoryTheory.CategoryHomology.coefficientBarFamily M n)
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Sigma.hom_ext
    intro chain
    exact (hM chain.left).eq_of_src _ _
  have hh : IsZero (K.homology n) :=
    (HomologicalComplex.ExactAt.of_isZero hx).isZero_homology
  exact IsZero.of_iso hh
    ((AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := CategoryTheory.CategoryHomology.coefficientBarSimplicial M)).toHomologyIso n)

/-- Every positive row of the actual identity-base second page is zero.
This does not assume that the nerve of the simplex category is contractible. -/
private theorem basePositiveSecondPage_isZero (B : SSet.{u})
    (p q : ℕ) (hq : 1 ≤ q) :
    IsZero (((SSet.bkHomologySpectralSequence integralCoefficients
      (SSet.simplexPullbackDiagram (𝟙 B))).page 2).X (p, q)) := by
  have hzero : IsZero (CategoryTheory.CategoryHomology.homologyWithCoefficients
      (fiberHomologyCoefficients (𝟙 B) q) p) :=
    categoryHomology_isZero_of_coefficients_zero _
      (basePositiveCoefficient_obj_isZero B q hq) p
  exact IsZero.of_iso hzero
    (SSet.bkSecondPageCoefficientHomologyIso integralCoefficients.{u}
      (SSet.simplexPullbackDiagram (𝟙 B)) p q)

/-- The integral coefficient object is actually nonzero, at its literal integer unit. -/
private theorem integral_identity_ne_zero :
    (𝟙 (integralCoefficients : AddCommGrpCat.{u})) ≠ 0 := by
  intro h
  have h₁ := congrArg
    (fun k : integralCoefficients.{u} ⟶ integralCoefficients.{u} => k (ULift.up (1 : ℤ))) h
  have h₂ : (1 : ℤ) = 0 := congrArg ULift.down h₁
  exact one_ne_zero h₂

/-- An invertible integral augmentation forces connectedness of the SAME
simplicial set. No connected component or nonempty model is supplied. -/
private theorem isConnected_of_integral_augmentation_isIso (X : SSet.{u})
    [IsIso (X.homology₀ε integralCoefficients)] : X.IsConnected := by
  let R : AddCommGrpCat.{u} := integralCoefficients.{u}
  let : IsIso (X.homology₀ε R) := by
    change IsIso (X.homology₀ε integralCoefficients.{u})
    infer_instance
  let e : X.homology R 0 ≅ (∐ fun _ : SSet.π₀ X => R) := X.homology₀Iso R
  have hpre : Subsingleton (SSet.π₀ X) := by
    classical
    constructor
    intro a b
    by_contra hab
    let ja : R ⟶ X.homology R 0 := Sigma.ι (fun _ : SSet.π₀ X => R) a ≫ e.inv
    let jb : R ⟶ X.homology R 0 := Sigma.ι (fun _ : SSet.π₀ X => R) b ≫ e.inv
    have hja : ja ≫ X.homology₀ε R = 𝟙 R := by
      change (Sigma.ι (fun _ : SSet.π₀ X => R) a ≫ e.inv) ≫
        (e.hom ≫ Sigma.desc (fun _ : SSet.π₀ X => 𝟙 R)) = 𝟙 R
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Sigma.ι_comp_desc]
    have hjb : jb ≫ X.homology₀ε R = 𝟙 R := by
      change (Sigma.ι (fun _ : SSet.π₀ X => R) b ≫ e.inv) ≫
        (e.hom ≫ Sigma.desc (fun _ : SSet.π₀ X => 𝟙 R)) = 𝟙 R
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Sigma.ι_comp_desc]
    have hj : ja = jb := (cancel_mono (X.homology₀ε R)).mp (hja.trans hjb.symm)
    have hi : Sigma.ι (fun _ : SSet.π₀ X => R) a =
        Sigma.ι (fun _ : SSet.π₀ X => R) b := (cancel_mono e.inv).mp hj
    let d : (∐ fun _ : SSet.π₀ X => R) ⟶ R :=
      Sigma.desc (fun c => if c = a then 𝟙 R else 0)
    have hid : (𝟙 R) = 0 := by
      calc
        (𝟙 R) = Sigma.ι (fun _ : SSet.π₀ X => R) a ≫ d := by
          simp only [d, Sigma.ι_comp_desc]; exact (ite_eq_left True.intro).symm
        _ = Sigma.ι (fun _ : SSet.π₀ X => R) b ≫ d := congrArg (fun k => k ≫ d) hi
        _ = 0 := by simp only [d, Sigma.ι_comp_desc, ite_eq_right (Ne.symm hab)]
    exact integral_identity_ne_zero hid
  have hn : X.Nonempty := by
    by_contra hnone
    let : IsEmpty (X _⦋0⦌) := ⟨fun x => hnone ⟨x⟩⟩
    let : IsEmpty (SSet.π₀ X) := ⟨fun c => by
      obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective c
      exact isEmptyElim x⟩
    have hz : IsZero (∐ fun _ : SSet.π₀ X => R) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply Sigma.hom_ext
      intro c
      exact isEmptyElim c
    have hX : IsZero (X.homology R 0) := IsZero.of_iso hz e
    have hR : IsZero R := IsZero.of_iso hX (asIso (X.homology₀ε R)).symm
    exact integral_identity_ne_zero (hR.eq_of_src _ _)
  exact (SSet.isConnected_iff (X := X)).mpr ⟨hpre, hn⟩

/-- Integral H₀ isomorphy to a connected target derives connectedness of the
actual source; it is not a new outer premise on the original space. -/
private theorem isConnected_of_integral_homology_zero_isIso
    {X B : SSet.{u}} (f : X ⟶ B) [B.IsConnected]
    [IsIso (SSet.homologyMap f integralCoefficients 0)] : X.IsConnected := by
  have h := SSet.homologyMap_comp_homology₀ε f integralCoefficients.{u}
  let : IsIso (X.homology₀ε integralCoefficients.{u}) := by
    rw [← h]
    infer_instance
  exact isConnected_of_integral_augmentation_isIso X

private abbrev integerModuleCoefficients : ModuleCat.{u} ℤ :=
  ModuleCat.of ℤ (ULift.{u} ℤ)

private abbrev integerModuleForget : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}

/-- The actual ℤ-module/additive-group equivalence supplies the coefficient
homology coordinate, by the stock chain and exact-functor homology comparisons. -/
private noncomputable def integerModuleHomologyIso (X : SSet.{u}) (n : ℕ) :
    integerModuleForget.obj (X.homology integerModuleCoefficients n) ≅
      X.homology integralCoefficients n := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := integerModuleForget.{u}
  let Z : ModuleCat.{u} ℤ := integerModuleCoefficients.{u}
  let K : ChainComplex (ModuleCat.{u} ℤ) ℕ := X.chainComplex Z
  let e : ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) ≅
      X.chainComplex integralCoefficients.{u} :=
    (SSet.mapChainComplexFunctorIso.{u} U Z).app X
  exact ((HomologicalComplex.mapHomologyFunctorIso n U).app K).symm ≪≫
    HomologicalComplex.homologyMapIso e n

/-- Both stock coordinate squares retain the original simplicial map. -/
private theorem integerModuleHomologyIso_naturality {X Y : SSet.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    integerModuleForget.map (SSet.homologyMap f integerModuleCoefficients n) ≫
        (integerModuleHomologyIso Y n).hom =
      (integerModuleHomologyIso X n).hom ≫ SSet.homologyMap f integralCoefficients n := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := integerModuleForget.{u}
  let Z : ModuleCat.{u} ℤ := integerModuleCoefficients.{u}
  let K : ChainComplex (ModuleCat.{u} ℤ) ℕ := X.chainComplex Z
  let L : ChainComplex (ModuleCat.{u} ℤ) ℕ := Y.chainComplex Z
  let c : K ⟶ L := SSet.chainComplexMap f Z
  let CX : ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) ≅
      X.chainComplex integralCoefficients.{u} :=
    (SSet.mapChainComplexFunctorIso.{u} U Z).app X
  let CY : ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj L) ≅
      Y.chainComplex integralCoefficients.{u} :=
    (SSet.mapChainComplexFunctorIso.{u} U Z).app Y
  let eK := (HomologicalComplex.mapHomologyFunctorIso n U).app K
  let eL := (HomologicalComplex.mapHomologyFunctorIso n U).app L
  let bK := HomologicalComplex.homologyMapIso CX n
  let bL := HomologicalComplex.homologyMapIso CY n
  let m := HomologicalComplex.homologyMap
    ((U.mapHomologicalComplex (ComplexShape.down ℕ)).map c) n
  let h := U.map (SSet.homologyMap f Z n)
  let g := SSet.homologyMap f integralCoefficients.{u} n
  have hF : CommSq m eK.hom eL.hom h :=
    ⟨(HomologicalComplex.mapHomologyFunctorIso n U).hom.naturality c⟩
  have hFinv : CommSq h eK.symm.hom eL.symm.hom m :=
    CommSq.vert_inv (g := eK) (h := eL) hF
  have hChain : (U.mapHomologicalComplex (ComplexShape.down ℕ)).map c ≫ CY.hom =
      CX.hom ≫ SSet.chainComplexMap f integralCoefficients.{u} :=
    (SSet.mapChainComplexFunctorIso.{u} U Z).hom.naturality f
  have hC : CommSq m bK.hom bL.hom g := ⟨HomologicalComplex.homologyMap_square hChain n⟩
  have hc : h ≫ (eL.inv ≫ bL.hom) = (eK.inv ≫ bK.hom) ≫ g :=
    (CommSq.vert_comp hFinv hC).w
  simpa only [integerModuleHomologyIso, Iso.trans_hom, Iso.symm_hom,
    U, Z, K, L, CX, CY, c, eK, eL, bK, bL, h, g] using! hc

/-- The same simplicial homology map is invertible after the genuine ℤ-module
comparison; no tensor-flatness or supplied equivalence is used. -/
private theorem integerModule_homologyMap_isIso {X Y : SSet.{u}}
    (f : X ⟶ Y) (n : ℕ) [IsIso (SSet.homologyMap f integerModuleCoefficients n)] :
    IsIso (SSet.homologyMap f integralCoefficients n) := by
  let eX := (integerModuleHomologyIso X n).hom
  let eY := (integerModuleHomologyIso Y n).hom
  let : IsIso (eX ≫ SSet.homologyMap f integralCoefficients.{u} n) := by
    rw [← integerModuleHomologyIso_naturality]
    infer_instance
  exact (isIso_comp_left_iff eX (SSet.homologyMap f integralCoefficients.{u} n)).mp inferInstance

private abbrev originalRegularBase (Y : TopCat.{u}) (y : Y) : SSet.{u} :=
  SSet.KanComplex.nativeCover (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y)

private noncomputable abbrev originalRegularTotal {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) : SSet.{u} :=
  pullback (TopCat.toSSet.map f)
    (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
      (TopCat.toSSetObj₀Equiv.symm y))

private noncomputable def originalRegularProjection {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) : originalRegularTotal f y ⟶ originalRegularBase Y y :=
  pullback.snd (TopCat.toSSet.map f)
    (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
      (TopCat.toSSetObj₀Equiv.symm y))

/-- The existing regular-cover homology square converts the actual all-target-
local-system hypothesis to the same full original cover projection. -/
private theorem originalRegularProjection_module_homology_isIso {X Y : TopCat.{u}}
    (f : X ⟶ Y) (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (y : Y) (n : ℕ) : IsIso (SSet.homologyMap
      (originalRegularProjection f y) integerModuleCoefficients n) := by
  let L : TopCat.LocalSystem ℤ Y :=
    CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)
  let h : TopCat.localCoefficientHomology (L.pullback f) n ⟶
      TopCat.localCoefficientHomology L n :=
    TopCat.localCoefficientPullbackHomologyMap f L n
  let eS : TopCat.localCoefficientHomology (L.pullback f) n ≅
      (originalRegularTotal f y).homology integerModuleCoefficients.{u} n :=
    HomologicalComplex.homologyMapIso
      (TopCat.originalTopRegularPullbackCoverChainIso f y) n
  let eT : TopCat.localCoefficientHomology L n ≅
      (originalRegularBase Y y).homology integerModuleCoefficients.{u} n :=
    HomologicalComplex.homologyMapIso (TopCat.originalTopRegularCoverChainIso Y y) n
  let g : (originalRegularTotal f y).homology integerModuleCoefficients.{u} n ⟶
      (originalRegularBase Y y).homology integerModuleCoefficients.{u} n :=
    SSet.homologyMap (originalRegularProjection f y) integerModuleCoefficients.{u} n
  let : IsIso h := hf L n
  have hs : h ≫ eT.hom = eS.hom ≫ g := by
    have hchain : TopCat.localCoefficientPullbackChainMap f L ≫
        (TopCat.originalTopRegularCoverChainIso Y y).hom =
      (TopCat.originalTopRegularPullbackCoverChainIso f y).hom ≫
        SSet.chainComplexMap (originalRegularProjection f y) integerModuleCoefficients.{u} :=
      TopCat.originalTopRegularCoverChainMap_square f y
    exact HomologicalComplex.homologyMap_square hchain n
  let : IsIso (eS.hom ≫ g) := by
    rw [← hs]
    infer_instance
  exact (isIso_comp_left_iff eS.hom g).mp inferInstance

/-- The actual regular projection has all integral homology isomorphisms. -/
private theorem originalRegularProjection_homology_isIso {X Y : TopCat.{u}}
    (f : X ⟶ Y) (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (y : Y) (n : ℕ) : IsIso (SSet.homologyMap
      (originalRegularProjection f y) integralCoefficients n) := by
  let : IsIso (SSet.homologyMap (originalRegularProjection f y) integerModuleCoefficients.{u} n) :=
    originalRegularProjection_module_homology_isIso f hf y n
  exact integerModule_homologyMap_isIso (originalRegularProjection f y) n

/-- The actual regular base is connected and has trivial native π₁ at every vertex. -/
private theorem originalRegularBase_one_connected (Y : TopCat.{u}) (y : Y) :
    letI : SSet.KanComplex (originalRegularBase Y y) :=
      SSet.KanComplex.nativeCover_kanComplex (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y)
    (originalRegularBase Y y).IsConnected ∧
      ∀ b : (originalRegularBase Y y) _⦋0⦌,
        Subsingleton (SSet.KanComplex.π 1 (originalRegularBase Y y) b) :=
  SSet.KanComplex.nativeCover_isConnected_and_piOne_subsingleton
    (X := TopCat.toSSet.obj Y) (x := TopCat.toSSetObj₀Equiv.symm y)

/-- Connectedness of the actual pulled cover is derived from the regular H₀
map. No connectedness of the original space is introduced. -/
private theorem originalRegularTotal_isConnected {X Y : TopCat.{u}}
    (f : X ⟶ Y) (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (y : Y) : (originalRegularTotal f y).IsConnected := by
  let : (originalRegularBase Y y).IsConnected := (originalRegularBase_one_connected Y y).1
  let : IsIso (SSet.homologyMap (originalRegularProjection f y) integralCoefficients.{u} 0) :=
    originalRegularProjection_homology_isIso f hf y 0
  exact isConnected_of_integral_homology_zero_isIso (originalRegularProjection f y)

/-- The fixed mapping-path section is weak using the already-proved Kan
mapping-path theorem. An arbitrary original map is not assumed a fibration. -/
private theorem mappingPathSection_weak {X B : SSet.{u}} (f : X ⟶ B)
    [SSet.KanComplex X] [SSet.KanComplex B] :
    SSet.realizationWeakEquivalences (SSet.mappingPathSection f) :=
  (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mp
    (SSet.KanComplex.W.of_mappingPathSection f)

/-- The mapping-path target retains the actual original homology map. -/
private theorem mappingPathTarget_homology_isIso {X B : SSet.{u}} (f : X ⟶ B)
    [SSet.KanComplex X] [SSet.KanComplex B] (n : ℕ)
    [IsIso (SSet.homologyMap f integralCoefficients n)] :
    IsIso (SSet.homologyMap (SSet.mappingPathTarget f) integralCoefficients n) := by
  let s := SSet.homologyMap (SSet.mappingPathSection f) integralCoefficients.{u} n
  let p := SSet.homologyMap (SSet.mappingPathTarget f) integralCoefficients.{u} n
  let : IsIso s := homologyMap_isIso_of_weak (mappingPathSection_weak f) integralCoefficients.{u} n
  have hs : s ≫ p = SSet.homologyMap f integralCoefficients.{u} n :=
    ((SSet.homologyFunctor integralCoefficients.{u} n).map_comp _ _).symm.trans
      ((SSet.homologyFunctor integralCoefficients.{u} n).congr_map
        (SSet.mappingPathSection_comp_target f))
  let : IsIso (s ≫ p) := by rw [hs]; infer_instance
  exact (isIso_comp_left_iff s p).mp inferInstance

private noncomputable def originalRegularKanProjection {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) :
    SSet.mappingPathSpace (originalRegularProjection f y) ⟶ originalRegularBase Y y :=
  SSet.mappingPathTarget (originalRegularProjection f y)

/-- The original regular reduction now has a DERIVED Kan fibration. -/
private theorem originalRegularKanProjection_fibration {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) : Fibration (originalRegularKanProjection f y) := by
  let : Fibration (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
    (TopCat.toSSetObj₀Equiv.symm y)) := SSet.KanComplex.nativeCoverProjection_fibration _ _
  let : SSet.KanComplex (TopCat.toSSet.obj X) := TopCat.toSSet_obj_kanComplex X
  let : SSet.KanComplex (originalRegularTotal f y) := by
    let a : originalRegularTotal f y ⟶ TopCat.toSSet.obj X :=
      pullback.fst (TopCat.toSSet.map f)
        (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
          (TopCat.toSSetObj₀Equiv.symm y))
    let : Fibration a :=
      SSet.fibration_of_isPullback
        (IsPullback.of_hasPullback (TopCat.toSSet.map f)
          (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
            (TopCat.toSSetObj₀Equiv.symm y)))
    exact HomotopicalAlgebra.isFibrant_of_fibration a
  let : SSet.KanComplex (originalRegularBase Y y) :=
    SSet.KanComplex.nativeCover_kanComplex (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y)
  change Fibration (SSet.mappingPathTarget (originalRegularProjection f y))
  infer_instance

/-- The SAME actual target fibration has all integral homology maps invertible. -/
private theorem originalRegularKanProjection_homology_isIso {X Y : TopCat.{u}}
    (f : X ⟶ Y) (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (y : Y) (n : ℕ) : IsIso (SSet.homologyMap
      (originalRegularKanProjection f y) integralCoefficients n) := by
  let : Fibration (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
    (TopCat.toSSetObj₀Equiv.symm y)) := SSet.KanComplex.nativeCoverProjection_fibration _ _
  let : SSet.KanComplex (TopCat.toSSet.obj X) := TopCat.toSSet_obj_kanComplex X
  let : SSet.KanComplex (originalRegularTotal f y) := by
    let a : originalRegularTotal f y ⟶ TopCat.toSSet.obj X :=
      pullback.fst (TopCat.toSSet.map f)
        (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
          (TopCat.toSSetObj₀Equiv.symm y))
    let : Fibration a :=
      SSet.fibration_of_isPullback
        (IsPullback.of_hasPullback (TopCat.toSSet.map f)
          (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
            (TopCat.toSSetObj₀Equiv.symm y)))
    exact HomotopicalAlgebra.isFibrant_of_fibration a
  let : SSet.KanComplex (originalRegularBase Y y) :=
    SSet.KanComplex.nativeCover_kanComplex (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y)
  let : IsIso (SSet.homologyMap (originalRegularProjection f y) integralCoefficients.{u} n) :=
    originalRegularProjection_homology_isIso f hf y n
  change IsIso (SSet.homologyMap (SSet.mappingPathTarget (originalRegularProjection f y))
    integralCoefficients.{u} n)
  exact mappingPathTarget_homology_isIso (originalRegularProjection f y) n

/-- The computed actual Kan fibration has a connected source by the derived
cover H₀ comparison and fixed weak mapping-path section. -/
private theorem originalRegularKanTotal_isConnected {X Y : TopCat.{u}}
    (f : X ⟶ Y) (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (y : Y) : (SSet.mappingPathSpace (originalRegularProjection f y)).IsConnected := by
  let : Fibration (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
    (TopCat.toSSetObj₀Equiv.symm y)) := SSet.KanComplex.nativeCoverProjection_fibration _ _
  let : SSet.KanComplex (TopCat.toSSet.obj X) := TopCat.toSSet_obj_kanComplex X
  let : SSet.KanComplex (originalRegularTotal f y) := by
    let a : originalRegularTotal f y ⟶ TopCat.toSSet.obj X :=
      pullback.fst (TopCat.toSSet.map f)
        (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
          (TopCat.toSSetObj₀Equiv.symm y))
    let : Fibration a :=
      SSet.fibration_of_isPullback
        (IsPullback.of_hasPullback (TopCat.toSSet.map f)
          (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
            (TopCat.toSSetObj₀Equiv.symm y)))
    exact HomotopicalAlgebra.isFibrant_of_fibration a
  let : SSet.KanComplex (originalRegularBase Y y) :=
    SSet.KanComplex.nativeCover_kanComplex (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y)
  let : (originalRegularTotal f y).IsConnected := originalRegularTotal_isConnected f hf y
  exact isConnected_of_weak (mappingPathSection_weak (originalRegularProjection f y))

/-- The actual row-zero spectral edge needed for the full criterion is derived
from ONLY the original map and its actual all-target-local-system hypothesis. -/
private theorem originalRegular_actual_rowZero_isIso {X Y : TopCat.{u}}
    (f : X ⟶ Y) (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (y : Y) (n : ℕ) :
    IsIso (HomologicalComplex₂.horizontalSecondPageMapOfBicomplex
      ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients).map
        (projectionDiagramMap (originalRegularKanProjection f y))) n 0) := by
  let : Fibration (originalRegularKanProjection f y) := originalRegularKanProjection_fibration f y
  let : (SSet.mappingPathSpace (originalRegularProjection f y)).IsConnected :=
    originalRegularKanTotal_isConnected f hf y
  let : SSet.KanComplex (originalRegularBase Y y) :=
    SSet.KanComplex.nativeCover_kanComplex (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y)
  let : (originalRegularBase Y y).IsConnected := (originalRegularBase_one_connected Y y).1
  exact actualSecondPageProjection_rowZero_isIso
    (originalRegularKanProjection f y) (originalRegularBase_one_connected Y y).2 n

private noncomputable abbrev originalRegularVertex (Y : TopCat.{u}) (y : Y) :
    (originalRegularBase Y y) _⦋0⦌ :=
  SSet.KanComplex.nativeCoverIdentityPoint (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y)

/-- The derived strict-fiber coordinate maps to the SAME complete original
ending-path fiber, through the existing actual native-cover comparison. -/
private noncomputable def originalEndingFiberComparison {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) :
    SSet.toTop.obj
        (SSet.Subcomplex.fiber (originalRegularKanProjection f y) (originalRegularVertex Y y) :
          SSet.{u}) ⟶ TopCat.homotopyFiber f y :=
  SSet.toTop.map
      (SSet.pathHomotopyFiberStrictMappingPathIso (originalRegularProjection f y) (originalRegularVertex Y
        y)).inv ≫
    SSet.KanComplex.nativeCoverOriginalTopPathFiberComparison f y
      (TopCat.toSSetObj₀Equiv.symm y) (originalRegularVertex Y y)
      (SSet.KanComplex.nativeCoverProjection_identityPoint
        (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y))

/-- Its weakness is derived from the computed carrier Iso and the existing
actual original-fiber comparison, with no desired fiber-model witness. -/
private theorem originalEndingFiberComparison_weak {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) :
    TopCat.weakHomotopyEquivalences (originalEndingFiberComparison f y) := by
  let a := TopCat.toSSetObj₀Equiv.symm y
  let v := originalRegularVertex Y y
  let e := SSet.pathHomotopyFiberStrictMappingPathIso (originalRegularProjection f y) v
  have hi : TopCat.weakHomotopyEquivalences (SSet.toTop.map e.inv) :=
    TopCat.weakHomotopyEquivalences.of_isIso _
  have hv := SSet.KanComplex.nativeCoverProjection_identityPoint (TopCat.toSSet.obj Y) a
  have hc := SSet.KanComplex.nativeCoverOriginalTopPathFiberComparison_mem_weakHomotopyEquivalences
    f y a v hv
  exact TopCat.weakHomotopyEquivalences.comp_mem _ _ hi hc

/-- Component equality gives an actual fundamental-groupoid morphism even
when the simplicial set is not Kan. -/
private theorem groupoidHom_of_component_eq {X : SSet.{u}} {x y : X _⦋0⦌}
    (h : SSet.π₀.mk x = SSet.π₀.mk y) :
    Nonempty (SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk y) := by
  rw [SSet.π₀.mk_eq_mk_iff] at h
  induction h with
  | rel _ _ h => exact ⟨SSet.FundamentalGroupoid.homMk h.some⟩
  | refl => exact ⟨𝟙 _⟩
  | symm _ _ _ ih => exact ⟨inv ih.some⟩
  | trans _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.some ≫ ih₂.some⟩

private theorem isConnected_source_of_weak {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : SSet.realizationWeakEquivalences f) [Y.IsConnected] : X.IsConnected := by
  apply (SSet.isConnected_iff (X := X)).mpr
  constructor
  · exact ⟨fun a b => hf.bijective_mapπ₀.1 (Subsingleton.elim _ _)⟩
  · have hn : Nonempty (SSet.π₀ X) := by
      obtain ⟨a, _⟩ := hf.bijective_mapπ₀.2 (Classical.arbitrary (SSet.π₀ Y))
      exact ⟨a⟩
    exact (SSet.π₀.nonempty_iff X).mp hn

/-- The existing native π₁/endomorphism dictionary makes the fundamental
groupoid of a one-connected Kan base thin, without identifying End with Hom. -/
private theorem oneConnectedGroupoid_homs_subsingleton (B : SSet.{u}) [SSet.KanComplex B]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b)) :
    ∀ x y : SSet.FundamentalGroupoid B, Subsingleton (x ⟶ y) := by
  have hend : ∀ x : SSet.FundamentalGroupoid B, Subsingleton (End x) := by
    intro x
    obtain ⟨b, rfl⟩ := SSet.FundamentalGroupoid.mk_surjective x
    exact (SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd b).toEquiv.subsingleton_congr.mp
      (hπ b)
  intro x y
  have hx : Subsingleton (x ⟶ x) := (End.homEquiv (X := x)).subsingleton_congr.mp (hend x)
  constructor
  intro f g
  exact (cancel_mono (inv g)).mp (@Subsingleton.elim _ hx (f ≫ inv g) (g ≫ inv g))

private theorem weakGroupoid_homs_subsingleton_source {X Y : SSet.{u}}
    {f : X ⟶ Y} (hf : SSet.realizationWeakEquivalences f)
    (hy : ∀ x y : SSet.FundamentalGroupoid Y, Subsingleton (x ⟶ y)) :
    ∀ x y : SSet.FundamentalGroupoid X, Subsingleton (x ⟶ y) := by
  let F := SSet.mapFundamentalGroupoid f
  let : F.IsEquivalence := hf.isEquivalence_mapFundamentalGroupoid
  intro x y
  exact ⟨fun a b => F.map_injective
    (@Subsingleton.elim _ (hy (F.obj x) (F.obj y)) (F.map a) (F.map b))⟩

private theorem weakGroupoid_homs_subsingleton_target {X Y : SSet.{u}}
    {f : X ⟶ Y} (hf : SSet.realizationWeakEquivalences f)
    (hx : ∀ x y : SSet.FundamentalGroupoid X, Subsingleton (x ⟶ y)) :
    ∀ x y : SSet.FundamentalGroupoid Y, Subsingleton (x ⟶ y) := by
  let F := SSet.mapFundamentalGroupoid f
  let : F.IsEquivalence := hf.isEquivalence_mapFundamentalGroupoid
  let G := F.asEquivalence.inverse
  intro x y
  exact ⟨fun a b => G.map_injective
    (@Subsingleton.elim _ (hx (G.obj x) (G.obj y)) (G.map a) (G.map b))⟩

/-- The identity-base simplex diagram has its computed point projection. -/
private noncomputable def baseDiagramToPoint (B : SSet.{u}) :
    SSet.simplexPullbackDiagram (𝟙 B) ⟶ SSet.bkPointDiagram (SSet.SimplexIndex B) where
  app s := SSet.stdSimplex.isTerminalObj₀.from ((SSet.simplexPullbackDiagram (𝟙 B)).obj s)
  naturality s t a := by
    change (SSet.simplexPullbackDiagram (𝟙 B)).map a ≫
      SSet.stdSimplex.isTerminalObj₀.from ((SSet.simplexPullbackDiagram (𝟙 B)).obj t) =
      SSet.stdSimplex.isTerminalObj₀.from ((SSet.simplexPullbackDiagram (𝟙 B)).obj s) ≫ 𝟙 _
    rw [Category.comp_id]
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The same actual identity-base resolution maps to the simplex-category nerve. -/
private noncomputable def baseResolutionToSimplexNerve (B : SSet.{u}) :
    SSet.simplexResolution (𝟙 B) ⟶ CategoryTheory.nerve (SSet.SimplexIndex B) :=
  SSet.bkHocolimMap (baseDiagramToPoint B) ≫ (SSet.bkPointIsoNerve (SSet.SimplexIndex B)).hom

private theorem baseResolutionToSimplexNerve_weak (B : SSet.{u}) :
    SSet.realizationWeakEquivalences (baseResolutionToSimplexNerve B) := by
  have h := SSet.bkHocolimMap_mem_realizationWeakEquivalences (baseDiagramToPoint B)
    (baseDiagramPoint_weak B)
  have he := SSet.realizationWeakEquivalences.of_isIso
    (SSet.bkPointIsoNerve (SSet.SimplexIndex B)).hom
  exact SSet.realizationWeakEquivalences.comp_mem _ _ h he

/-- The simplex nerve is connected by the ACTUAL two weak resolution legs. -/
private theorem simplexNerve_isConnected (B : SSet.{u}) [B.IsConnected] :
    (CategoryTheory.nerve (SSet.SimplexIndex B)).IsConnected := by
  let : (SSet.simplexResolution (𝟙 B)).IsConnected := isConnected_source_of_weak
    (SSet.simplexResolutionAugmentation_mem_realizationWeakEquivalences (𝟙 B))
  exact isConnected_of_weak (baseResolutionToSimplexNerve_weak B)

/-- Only π₁ of the simplex nerve is trivialized; the original base's higher
homology remains present in category homology. -/
private theorem simplexNerveGroupoid_homs_subsingleton (B : SSet.{u}) [SSet.KanComplex B]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b)) :
    ∀ x y : SSet.FundamentalGroupoid (CategoryTheory.nerve (SSet.SimplexIndex B)),
      Subsingleton (x ⟶ y) :=
  weakGroupoid_homs_subsingleton_target (baseResolutionToSimplexNerve_weak B)
    (weakGroupoid_homs_subsingleton_source
      (SSet.simplexResolutionAugmentation_mem_realizationWeakEquivalences (𝟙 B))
      (oneConnectedGroupoid_homs_subsingleton B hπ))

/-- Morphism-inverting coefficients descend through the existing universal
fundamental groupoid. The target may be in a larger object universe. -/
private noncomputable def coefficientGroupoidFunctor
    {J : Type u} [Category.{0} J] (M : J ⥤ AddCommGrpCat.{u})
    [∀ {x y : J} (f : x ⟶ y), IsIso (M.map f)] :
    SSet.FundamentalGroupoid (CategoryTheory.nerve J) ⥤ Core AddCommGrpCat.{u} :=
  CategoryTheory.CategoryHomology.invertingCoefficientCore M

private noncomputable abbrev coefficientGroupoidExtension
    {J : Type u} [Category.{0} J] (M : J ⥤ AddCommGrpCat.{u})
    [∀ {x y : J} (f : x ⟶ y), IsIso (M.map f)] :
    SSet.FundamentalGroupoid (CategoryTheory.nerve J) ⥤ AddCommGrpCat.{u} :=
  CategoryTheory.CategoryHomology.invertingCoefficientExtension M

/-- Restricting that computed extension recovers the original coefficient
functor, with literal identity object coordinates. -/
private noncomputable def coefficientGroupoidRestrictionIso
    {J : Type u} [Category.{0} J] (M : J ⥤ AddCommGrpCat.{u})
    [∀ {x y : J} (f : x ⟶ y), IsIso (M.map f)] :
    SSet.categoryNerveUnit J ⋙ coefficientGroupoidExtension M ≅ M :=
  CategoryTheory.CategoryHomology.invertingCoefficientRestrictionIso M

private noncomputable def nerveCoefficientPath
    {J : Type u} [Category.{0} J] [(CategoryTheory.nerve J).IsConnected] (i j : J) :
    (SSet.categoryNerveUnit J).obj i ⟶ (SSet.categoryNerveUnit J).obj j := by
  let xi : (CategoryTheory.nerve J : SSet.{u}) _⦋0⦌ := CategoryTheory.nerveEquiv.symm i
  let xj : (CategoryTheory.nerve J : SSet.{u}) _⦋0⦌ := CategoryTheory.nerveEquiv.symm j
  change SSet.FundamentalGroupoid.mk xi ⟶ SSet.FundamentalGroupoid.mk xj
  have h : SSet.π₀.mk (X := (CategoryTheory.nerve J : SSet.{u})) xi =
      SSet.π₀.mk (X := (CategoryTheory.nerve J : SSet.{u})) xj := Subsingleton.elim _ _
  exact (groupoidHom_of_component_eq (X := (CategoryTheory.nerve J : SSet.{u})) h).some

private theorem nerveCoefficientPath_self
    {J : Type u} [Category.{0} J] [(CategoryTheory.nerve J).IsConnected]
    (hthin : ∀ x y : SSet.FundamentalGroupoid (CategoryTheory.nerve J), Subsingleton (x ⟶ y))
    (i : J) : nerveCoefficientPath i i = 𝟙 ((SSet.categoryNerveUnit J).obj i) :=
  @Subsingleton.elim _ (hthin _ _) _ _

/-- On a thin connected fundamental groupoid, the actual descent makes the
original coefficient system constant, with a computed path coordinate. -/
private noncomputable def constantIsoOfCoefficientGroupoid
    {J : Type u} [Category.{0} J] [(CategoryTheory.nerve J).IsConnected]
    (M : J ⥤ AddCommGrpCat.{u}) [∀ {x y : J} (f : x ⟶ y), IsIso (M.map f)]
    (hthin : ∀ x y : SSet.FundamentalGroupoid (CategoryTheory.nerve J), Subsingleton (x ⟶ y))
    (i : J) : (Functor.const J).obj (M.obj i) ≅ M := by
  let F := coefficientGroupoidExtension M
  let U := SSet.categoryNerveUnit J
  let e := coefficientGroupoidRestrictionIso M
  let c : (CategoryTheory.Functor.const J).obj ((U ⋙ F).obj i) ≅ U ⋙ F :=
    NatIso.ofComponents (fun j => asIso (F.map (nerveCoefficientPath i j))) (by
      intro j k f
      change 𝟙 _ ≫ F.map (nerveCoefficientPath i k) =
        F.map (nerveCoefficientPath i j) ≫ F.map (U.map f)
      rw [Category.id_comp, ← F.map_comp]
      exact congrArg F.map
        (@Subsingleton.elim _ (hthin (U.obj i) (U.obj k))
          (nerveCoefficientPath i k) (nerveCoefficientPath i j ≫ U.map f)))
  exact (CategoryTheory.Functor.const J).mapIso (e.app i).symm ≪≫ c ≪≫ e

/-- The chosen-object coordinate is the literal identity, derived from
thinness rather than supplied as a calibration premise. -/
private theorem constantIsoOfCoefficientGroupoid_app_self
    {J : Type u} [Category.{0} J] [(CategoryTheory.nerve J).IsConnected]
    (M : J ⥤ AddCommGrpCat.{u}) [∀ {x y : J} (f : x ⟶ y), IsIso (M.map f)]
    (hthin : ∀ x y : SSet.FundamentalGroupoid (CategoryTheory.nerve J), Subsingleton (x ⟶ y))
    (i : J) : (constantIsoOfCoefficientGroupoid M hthin i).app i = Iso.refl (M.obj i) := by
  let F := coefficientGroupoidExtension M
  let U := SSet.categoryNerveUnit J
  let e : (U ⋙ F).obj i ≅ M.obj i := (coefficientGroupoidRestrictionIso M).app i
  have hm : F.map (nerveCoefficientPath i i) = 𝟙 (F.obj (U.obj i)) :=
    (congrArg F.map (nerveCoefficientPath_self hthin i)).trans (F.map_id (U.obj i))
  apply Iso.ext
  change e.inv ≫ (F.map (nerveCoefficientPath i i) ≫ e.hom) = 𝟙 (M.obj i)
  exact (congrArg (fun h => e.inv ≫ (h ≫ e.hom)) hm).trans
    ((congrArg (fun h => e.inv ≫ h) (Category.id_comp e.hom)).trans e.inv_hom_id)

private def actualFiberSimplex {B : SSet.{u}} (b : B _⦋0⦌) : SSet.SimplexIndex B :=
  CostructuredArrow.mk (SSet.const (X := (Δ[0] : SSet.{u})) b)

private noncomputable def actualFiberPullbackIso {E B : SSet.{u}}
    (p : E ⟶ B) (b : B _⦋0⦌) :
    (SSet.Subcomplex.fiber p b : SSet.{u}) ≅
      (SSet.simplexPullbackDiagram p).obj (actualFiberSimplex b) :=
  (SSet.Subcomplex.fiber_isPullback p b).isoPullback

/-- The actual fibration coefficients are constant by their DERIVED
morphism inversion and the original one-connected base's simplex nerve. -/
private noncomputable def actualFiberCoefficientConstIso {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b))
    (b : B _⦋0⦌) (q : ℕ) :
    (Functor.const (SSet.SimplexIndex B)).obj
        ((fiberHomologyCoefficients p q).obj (actualFiberSimplex b)) ≅
      fiberHomologyCoefficients p q := by
  letI : (CategoryTheory.nerve (SSet.SimplexIndex B)).IsConnected := simplexNerve_isConnected B
  letI : ∀ {s t : SSet.SimplexIndex B} (a : s ⟶ t),
      IsIso ((fiberHomologyCoefficients p q).map a) :=
    fun {s t} a => fiberHomologyCoefficients_map_isIso p q a
  exact constantIsoOfCoefficientGroupoid (fiberHomologyCoefficients p q)
    (simplexNerveGroupoid_homs_subsingleton B hπ) (actualFiberSimplex b)

private theorem actualFiberCoefficientConstIso_app_self {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b))
    (b : B _⦋0⦌) (q : ℕ) :
    (actualFiberCoefficientConstIso p hπ b q).app (actualFiberSimplex b) =
      Iso.refl ((fiberHomologyCoefficients p q).obj (actualFiberSimplex b)) := by
  let : (CategoryTheory.nerve (SSet.SimplexIndex B)).IsConnected := simplexNerve_isConnected B
  let : ∀ {s t : SSet.SimplexIndex B} (a : s ⟶ t),
      IsIso ((fiberHomologyCoefficients p q).map a) :=
    fun {s t} a => fiberHomologyCoefficients_map_isIso p q a
  exact constantIsoOfCoefficientGroupoid_app_self (fiberHomologyCoefficients p q)
    (simplexNerveGroupoid_homs_subsingleton B hπ) (actualFiberSimplex b)

/-- The existing constant bar/nerve comparison carries the ACTUAL degree-zero
summand to the corresponding literal nerve vertex. -/
private theorem constantCoefficientBar_inclusion_coordinate
    {J : Type u} [Category.{0} J] (R : AddCommGrpCat.{u}) (i : J) :
    CategoryTheory.CategoryHomology.coefficientBarι ((Functor.const J).obj R)
        (ComposableArrows.mk₀ i) ≫
      (CategoryTheory.CategoryHomology.constantCoefficientBarComplexIso J AddCommGrpCat.{u} R).hom.f
        0 =
        (CategoryTheory.nerve J).ιChainComplex (ComposableArrows.mk₀ i) := by
  let τ := (sigmaConst : AddCommGrpCat.{u} ⥤ (Type u ⥤ AddCommGrpCat.{u})).obj R
  have hs : (CategoryTheory.CategoryHomology.constantCoefficientBarSimplicialIso
      J AddCommGrpCat.{u} R).hom.app (Opposite.op ⦋0⦌) = 𝟙 _ := by
    let e := SimplicialObject.Data.toSimplicialObject_mapObjIso τ (CategoryTheory.nerveData J)
    let d := CategoryTheory.nerveDataSimplicialIso J
    have he : e.inv.app (Opposite.op ⦋0⦌) = 𝟙 _ :=
      SimplicialObject.Data.toSimplicialObject_mapObjIso_inv_app_mk τ
        (CategoryTheory.nerveData J) 0
    have hd : d.hom.app (Opposite.op ⦋0⦌) = 𝟙 _ :=
      CategoryTheory.nerveDataSimplicialIso_hom_app (C := J) 0
    have ht : τ.map (d.hom.app (Opposite.op ⦋0⦌)) = 𝟙 _ :=
      (congrArg τ.map hd).trans (τ.map_id _)
    change e.inv.app (Opposite.op ⦋0⦌) ≫ τ.map (d.hom.app (Opposite.op ⦋0⦌)) = 𝟙 _
    exact (congrArg (fun h => e.inv.app (Opposite.op ⦋0⦌) ≫ h) ht).trans
      ((Category.comp_id _).trans he)
  change CategoryTheory.CategoryHomology.coefficientBarι ((CategoryTheory.Functor.const J).obj R)
      (ComposableArrows.mk₀ i) ≫
      ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map
        (CategoryTheory.CategoryHomology.constantCoefficientBarSimplicialIso
          J AddCommGrpCat.{u} R).hom).f 0 = _
  erw [AlgebraicTopology.alternatingFaceMapComplex_map_f, hs, Category.comp_id]
  rfl

/-- The canonical constant coefficient class maps to the identity under the
ACTUAL nerve augmentation, without an initial-category assumption. -/
private theorem constantCoefficientClass_augmentation
    {J : Type u} [Category.{0} J] (R : AddCommGrpCat.{u}) (i : J) :
    CategoryTheory.CategoryHomology.coefficientHomologyClass ((Functor.const J).obj R) i ≫
        (CategoryTheory.CategoryHomology.homologyWithConstantCoefficientsIso
          J AddCommGrpCat.{u} R 0).hom ≫
        (CategoryTheory.nerve J).homology₀ε R = 𝟙 R := by
  let M : J ⥤ AddCommGrpCat.{u} := (CategoryTheory.Functor.const J).obj R
  let K := CategoryTheory.CategoryHomology.coefficientBarComplex M
  let L := (CategoryTheory.nerve J).chainComplex R
  let e := CategoryTheory.CategoryHomology.coefficientHomologyZeroComparison M
  let c := CategoryTheory.CategoryHomology.constantCoefficientBarComplexIso J AddCommGrpCat.{u} R
  let ι : R ⟶ K.X 0 := CategoryTheory.CategoryHomology.coefficientBarι M (ComposableArrows.mk₀ i)
  let ιN : R ⟶ L.X 0 := (CategoryTheory.nerve J).ιChainComplex (ComposableArrows.mk₀ i)
  let ε : L.homology 0 ⟶ R := (CategoryTheory.nerve J).homology₀ε R
  have hc : (CategoryTheory.CategoryHomology.homologyWithConstantCoefficientsIso
      J AddCommGrpCat.{u} R 0).hom = e.hom ≫ HomologicalComplex.homologyMap c.hom 0 := rfl
  have hp : ChainComplex.homologyZeroClass K ≫ HomologicalComplex.homologyMap c.hom 0 =
      c.hom.f 0 ≫ ChainComplex.homologyZeroClass L :=
    ChainComplex.homologyZeroClass_naturality c.hom
  have hι : ι ≫ c.hom.f 0 = ιN := constantCoefficientBar_inclusion_coordinate R i
  have hclass : ιN ≫ ChainComplex.homologyZeroClass L =
      L.liftCycles ιN 0 (by simp) (by simp) ≫ L.homologyπ 0 :=
    CategoryTheory.CategoryHomology.comp_homologyZeroProjection_eq_class L ιN
  change (ι ≫ ChainComplex.homologyZeroClass K ≫ e.inv) ≫
    (CategoryTheory.CategoryHomology.homologyWithConstantCoefficientsIso
      J AddCommGrpCat.{u} R 0).hom ≫ ε = 𝟙 R
  rw [hc]
  calc
    (ι ≫ ChainComplex.homologyZeroClass K ≫ e.inv) ≫
        (e.hom ≫ HomologicalComplex.homologyMap c.hom 0) ≫ ε =
      ι ≫ ChainComplex.homologyZeroClass K ≫ HomologicalComplex.homologyMap c.hom 0 ≫ ε := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = ι ≫ (ChainComplex.homologyZeroClass K ≫ HomologicalComplex.homologyMap c.hom 0) ≫ ε := by
      simp only [Category.assoc]
    _ = ι ≫ (c.hom.f 0 ≫ ChainComplex.homologyZeroClass L) ≫ ε := by rw [hp]
    _ = (ι ≫ c.hom.f 0) ≫ ChainComplex.homologyZeroClass L ≫ ε := by simp only [Category.assoc]
    _ = ιN ≫ ChainComplex.homologyZeroClass L ≫ ε := by rw [hι]
    _ = (L.liftCycles ιN 0 (by simp) (by simp) ≫ L.homologyπ 0) ≫ ε :=
      congrArg (fun k => k ≫ ε) hclass
    _ = 𝟙 R := by
      simpa only [ιN, L, ε, Category.assoc] using
        SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
          (X := CategoryTheory.nerve J) (R := R) (ComposableArrows.mk₀ i)

private noncomputable def coefficientHomologyZeroIsoOfGroupoid
    {J : Type u} [Category.{0} J] [(CategoryTheory.nerve J).IsConnected]
    (M : J ⥤ AddCommGrpCat.{u}) [∀ {x y : J} (f : x ⟶ y), IsIso (M.map f)]
    (hthin : ∀ x y : SSet.FundamentalGroupoid (CategoryTheory.nerve J), Subsingleton (x ⟶ y))
    (i : J) : CategoryTheory.CategoryHomology.homologyWithCoefficients M 0 ≅ M.obj i :=
  (CategoryTheory.CategoryHomology.homologyWithCoefficientsFunctor
      (C := J) (A := AddCommGrpCat.{u}) 0).mapIso
        (constantIsoOfCoefficientGroupoid M hthin i).symm ≪≫
    CategoryTheory.CategoryHomology.homologyWithConstantCoefficientsIso
      J AddCommGrpCat.{u} (M.obj i) 0 ≪≫
    asIso ((CategoryTheory.nerve J).homology₀ε (M.obj i))

/-- The chosen fiber coefficient class has a DERIVED identity coordinate in
category H₀, rather than an assumed edge calibration. -/
private theorem coefficientHomologyZeroIsoOfGroupoid_class
    {J : Type u} [Category.{0} J] [(CategoryTheory.nerve J).IsConnected]
    (M : J ⥤ AddCommGrpCat.{u}) [∀ {x y : J} (f : x ⟶ y), IsIso (M.map f)]
    (hthin : ∀ x y : SSet.FundamentalGroupoid (CategoryTheory.nerve J), Subsingleton (x ⟶ y))
    (i : J) : CategoryTheory.CategoryHomology.coefficientHomologyClass M i ≫
        (coefficientHomologyZeroIsoOfGroupoid M hthin i).hom = 𝟙 (M.obj i) := by
  let ψ := constantIsoOfCoefficientGroupoid M hthin i
  let H : (J ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
    CategoryTheory.CategoryHomology.homologyWithCoefficientsFunctor
      (C := J) (A := AddCommGrpCat.{u}) 0
  let c := (CategoryTheory.CategoryHomology.homologyWithConstantCoefficientsIso
    J AddCommGrpCat.{u} (M.obj i) 0).hom
  let ε := (CategoryTheory.nerve J).homology₀ε (M.obj i)
  let qM := CategoryTheory.CategoryHomology.coefficientHomologyClass M i
  let qC := CategoryTheory.CategoryHomology.coefficientHomologyClass
    ((CategoryTheory.Functor.const J).obj (M.obj i)) i
  have hn : qM ≫ H.map ψ.inv = ψ.inv.app i ≫ qC :=
    CategoryTheory.CategoryHomology.coefficientHomologyClass_naturality ψ.inv i
  have hi : ψ.inv.app i = 𝟙 (M.obj i) := by
    exact congrArg (fun e => e.inv) (constantIsoOfCoefficientGroupoid_app_self M hthin i)
  have hc : qC ≫ (c ≫ ε) = 𝟙 (M.obj i) :=
    constantCoefficientClass_augmentation (M.obj i) i
  change qM ≫ (H.map ψ.inv ≫ (c ≫ ε)) = 𝟙 (M.obj i)
  exact (Category.assoc qM (H.map ψ.inv) (c ≫ ε)).symm.trans
    ((congrArg (fun h => h ≫ (c ≫ ε)) hn).trans
      ((congrArg (fun h => (h ≫ qC) ≫ (c ≫ ε)) hi).trans
        ((congrArg (fun h => h ≫ (c ≫ ε)) (Category.id_comp qC)).trans hc)))

/-- Category H₀ of the actual fiber coefficient system is the homology of
the SAME strict fiber at the specified original base vertex. -/
private noncomputable def actualFiberCoefficientHomologyZeroIso {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b))
    (b : B _⦋0⦌) (q : ℕ) :
    CategoryTheory.CategoryHomology.homologyWithCoefficients (fiberHomologyCoefficients p q) 0 ≅
      (SSet.Subcomplex.fiber p b : SSet.{u}).homology integralCoefficients q := by
  letI : (CategoryTheory.nerve (SSet.SimplexIndex B)).IsConnected := simplexNerve_isConnected B
  letI : ∀ {s t : SSet.SimplexIndex B} (a : s ⟶ t),
      IsIso ((fiberHomologyCoefficients p q).map a) :=
    fun {s t} a => fiberHomologyCoefficients_map_isIso p q a
  exact coefficientHomologyZeroIsoOfGroupoid (fiberHomologyCoefficients p q)
      (simplexNerveGroupoid_homs_subsingleton B hπ) (actualFiberSimplex b) ≪≫
    ((SSet.homologyFunctor (C := AddCommGrpCat.{u}) integralCoefficients.{u} q).mapIso
      (actualFiberPullbackIso p b)).symm

/-- The specified actual fiber inclusion class is carried by the actual
pullback inverse in EVERY degree; this is not inferred from an abstract bijection. -/
private theorem actualFiberCoefficientHomologyZeroIso_class {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b))
    (b : B _⦋0⦌) (q : ℕ) :
    CategoryTheory.CategoryHomology.coefficientHomologyClass
          (fiberHomologyCoefficients p q) (actualFiberSimplex b) ≫
        (actualFiberCoefficientHomologyZeroIso p hπ b q).hom =
      SSet.homologyMap (actualFiberPullbackIso p b).inv integralCoefficients q := by
  let : (CategoryTheory.nerve (SSet.SimplexIndex B)).IsConnected := simplexNerve_isConnected B
  let : ∀ {s t : SSet.SimplexIndex B} (a : s ⟶ t),
      IsIso ((fiberHomologyCoefficients p q).map a) :=
    fun {s t} a => fiberHomologyCoefficients_map_isIso p q a
  let M : SSet.SimplexIndex B ⥤ AddCommGrpCat.{u} := fiberHomologyCoefficients p q
  let e := coefficientHomologyZeroIsoOfGroupoid M
    (simplexNerveGroupoid_homs_subsingleton B hπ) (actualFiberSimplex b)
  let c := CategoryTheory.CategoryHomology.coefficientHomologyClass M (actualFiberSimplex b)
  let g := SSet.homologyMap (actualFiberPullbackIso p b).inv integralCoefficients.{u} q
  have hc : c ≫ e.hom = 𝟙 (M.obj (actualFiberSimplex b)) :=
    coefficientHomologyZeroIsoOfGroupoid_class M
      (simplexNerveGroupoid_homs_subsingleton B hπ) (actualFiberSimplex b)
  change c ≫ (e.hom ≫ g) = g
  exact (Category.assoc c e.hom g).symm.trans
    ((congrArg (fun h => h ≫ g) hc).trans (Category.id_comp g))

/-- The actual zero-column second-page term is the SAME chosen fiber homology. -/
private noncomputable def actualZeroColumnFiberHomologyIso {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b))
    (b : B _⦋0⦌) (q : ℕ) :
    ((SSet.bkHomologySpectralSequence integralCoefficients
      (SSet.simplexPullbackDiagram p)).page 2).X (0, q) ≅
        (SSet.Subcomplex.fiber p b : SSet.{u}).homology integralCoefficients q :=
  SSet.bkSecondPageCoefficientHomologyIso integralCoefficients.{u}
      (SSet.simplexPullbackDiagram p) 0 q ≪≫
    actualFiberCoefficientHomologyZeroIso p hπ b q

/-- The same chosen fiber class is calibrated on the actual zero-column
page through the existing second-page inverse and actual pullback map. -/
private theorem actualZeroColumnFiberHomologyIso_class {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b))
    (b : B _⦋0⦌) (q : ℕ) :
    CategoryTheory.CategoryHomology.coefficientHomologyClass
          (fiberHomologyCoefficients p q) (actualFiberSimplex b) ≫
        (SSet.bkSecondPageCoefficientHomologyIso integralCoefficients
          (SSet.simplexPullbackDiagram p) 0 q).inv ≫
        (actualZeroColumnFiberHomologyIso p hπ b q).hom =
      SSet.homologyMap (actualFiberPullbackIso p b).inv integralCoefficients q := by
  let e : ((SSet.bkHomologySpectralSequence integralCoefficients.{u}
      (SSet.simplexPullbackDiagram p)).page 2).X (0, q) ≅
      CategoryTheory.CategoryHomology.homologyWithCoefficients
        (fiberHomologyCoefficients p q) 0 :=
    SSet.bkSecondPageCoefficientHomologyIso integralCoefficients.{u}
      (SSet.simplexPullbackDiagram p) 0 q
  let c := CategoryTheory.CategoryHomology.coefficientHomologyClass
    (fiberHomologyCoefficients p q) (actualFiberSimplex b)
  let g := actualFiberCoefficientHomologyZeroIso p hπ b q
  change c ≫ (e.inv ≫ (e.hom ≫ g.hom)) =
    SSet.homologyMap (actualFiberPullbackIso p b).inv integralCoefficients.{u} q
  exact (congrArg (fun h => c ≫ h) (Iso.inv_hom_id_assoc e g.hom)).trans
    (actualFiberCoefficientHomologyZeroIso_class p hπ b q)

/-- Vanishing of a chosen actual fiber homology group transports to each
actual simplex coefficient by the COMPUTED constant coefficient Iso. -/
private theorem actualFiberCoefficient_obj_isZero {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b))
    (b : B _⦋0⦌) (q : ℕ)
    (hz : IsZero ((SSet.Subcomplex.fiber p b : SSet.{u}).homology integralCoefficients q))
    (s : SSet.SimplexIndex B) : IsZero ((fiberHomologyCoefficients p q).obj s) := by
  have hbase : IsZero ((fiberHomologyCoefficients p q).obj (actualFiberSimplex b)) :=
    IsZero.of_iso hz ((SSet.homologyFunctor (C := AddCommGrpCat.{u}) integralCoefficients.{u}
      q).mapIso (actualFiberPullbackIso p b)).symm
  exact IsZero.of_iso hbase ((actualFiberCoefficientConstIso p hπ b q).app s).symm

/-- Every horizontal position of a vanished fiber row is zero. The only
vanishing input is a previous-degree induction hypothesis on that SAME fiber. -/
private theorem actualSecondPage_isZero_of_fiberHomology_isZero {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b))
    (b : B _⦋0⦌) (q : ℕ)
    (hz : IsZero ((SSet.Subcomplex.fiber p b : SSet.{u}).homology integralCoefficients q))
    (a : ℕ) : IsZero (((SSet.bkHomologySpectralSequence integralCoefficients
      (SSet.simplexPullbackDiagram p)).page 2).X (a, q)) := by
  have hc : IsZero (CategoryTheory.CategoryHomology.homologyWithCoefficients
      (fiberHomologyCoefficients p q) a) :=
    categoryHomology_isZero_of_coefficients_zero _
      (actualFiberCoefficient_obj_isZero p hπ b q hz) a
  exact IsZero.of_iso hc
    (SSet.bkSecondPageCoefficientHomologyIso integralCoefficients.{u}
      (SSet.simplexPullbackDiagram p) a q)

/-- The original regular/mapping-path reduction has the complete chosen-
fiber zero-column identification without an extra model or point input. -/
private noncomputable def originalZeroColumnFiberHomologyIso {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) (q : ℕ) :
    ((SSet.bkHomologySpectralSequence integralCoefficients
      (SSet.simplexPullbackDiagram (originalRegularKanProjection f y))).page 2).X (0, q) ≅
      (SSet.Subcomplex.fiber (originalRegularKanProjection f y) (originalRegularVertex Y y) :
        SSet.{u}).homology integralCoefficients q := by
  letI : Fibration (originalRegularKanProjection f y) := originalRegularKanProjection_fibration f y
  letI : SSet.KanComplex (originalRegularBase Y y) :=
    SSet.KanComplex.nativeCover_kanComplex (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y)
  letI : (originalRegularBase Y y).IsConnected := (originalRegularBase_one_connected Y y).1
  exact actualZeroColumnFiberHomologyIso (originalRegularKanProjection f y)
    (originalRegularBase_one_connected Y y).2 (originalRegularVertex Y y) q

/-- The same projection satisfies every native page-successor square by
specializing the existing general theorem. -/
private theorem actualProjection_page_successor {E B : SSet.{u}} (p : E ⟶ B)
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : 1 ≤ r) (a b : ℕ) :
    HomologicalComplex.homologyMap
          (HomologicalComplex₂.horizontalPageMapOfBicomplex
            ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients).map
              (projectionDiagramMap p)) r hr) (a, b) ≫
        ((SSet.bkHomologySpectralSequence integralCoefficients
          (SSet.simplexPullbackDiagram (𝟙 B))).iso r r' (a, b) hrr' hr).hom =
      ((SSet.bkHomologySpectralSequence integralCoefficients
          (SSet.simplexPullbackDiagram p)).iso r r' (a, b) hrr' hr).hom ≫
        (HomologicalComplex₂.horizontalPageMapOfBicomplex
          ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients).map
            (projectionDiagramMap p)) r' (by omega)).f (a, b) :=
  HomologicalComplex₂.horizontalPageMapOfBicomplex_successor _ r r' hrr' hr a b

/-- The original map's fixed regular/mapping-path projection inherits that
whole arbitrary-page square without a supplied compatible family. -/
private theorem originalProjection_page_successor {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) (r r' : ℤ) (hrr' : r + 1 = r') (hr : 1 ≤ r) (a b : ℕ) :
    HomologicalComplex.homologyMap
          (HomologicalComplex₂.horizontalPageMapOfBicomplex
            ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients).map
              (projectionDiagramMap (originalRegularKanProjection f y))) r hr) (a, b) ≫
        ((SSet.bkHomologySpectralSequence integralCoefficients
          (SSet.simplexPullbackDiagram (𝟙 (originalRegularBase Y y)))).iso
            r r' (a, b) hrr' hr).hom =
      ((SSet.bkHomologySpectralSequence integralCoefficients
          (SSet.simplexPullbackDiagram (originalRegularKanProjection f y))).iso
            r r' (a, b) hrr' hr).hom ≫
        (HomologicalComplex₂.horizontalPageMapOfBicomplex
          ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients).map
            (projectionDiagramMap (originalRegularKanProjection f y))) r' (by omega)).f (a, b) :=
  actualProjection_page_successor (originalRegularKanProjection f y) r r' hrr' hr a b

/-- The projection defines a genuine morphism of the existing native
spectral sequences, with every compatibility square derived by675. -/
private noncomputable def actualProjectionSpectralSequenceMap {E B : SSet.{u}}
    (p : E ⟶ B) :
    SSet.bkHomologySpectralSequence integralCoefficients (SSet.simplexPullbackDiagram p) ⟶
      SSet.bkHomologySpectralSequence integralCoefficients (SSet.simplexPullbackDiagram (𝟙 B)) where
  hom r hr := HomologicalComplex₂.horizontalPageMapOfBicomplex
    ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients.{u}).map
      (projectionDiagramMap p)) r hr
  comm r r' pq hrr' hr := by
    obtain ⟨a, b⟩ := pq
    exact actualProjection_page_successor p r r' hrr' hr a b

private theorem firstQuadrant_zeroColumn_noOutgoing (r : ℤ) (hr : 1 ≤ r) (n : ℕ) :
    ∀ k : ℕ × ℕ, ¬ (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).Rel (0, n) k := by
  intro k h
  have hf : (0 : ℤ) + (-r) = (k.1 : ℤ) := h.1
  omega

private theorem firstQuadrant_zeroRow_noIncoming (r : ℤ) (hr : 2 ≤ r) (n : ℕ) :
    ∀ i : ℕ × ℕ, ¬ (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).Rel i (n, 0) := by
  intro i h
  have hs : (i.2 : ℤ) + (r - 1) = 0 := h.2
  omega

/-- The actual row-zero page map remains monic at every successor page.
The proof uses the native no-incoming shape and the actual page morphism. -/
private theorem actualProjection_rowZero_mono_add_two {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [E.IsConnected] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b)) (a m : ℕ) :
    Mono (((actualProjectionSpectralSequenceMap p).hom ((m : ℤ) + 2)).f (a, 0)) := by
  let S := SSet.bkHomologySpectralSequence integralCoefficients.{u} (SSet.simplexPullbackDiagram p)
  let T := SSet.bkHomologySpectralSequence integralCoefficients.{u} (SSet.simplexPullbackDiagram (𝟙
    B))
  let φ := actualProjectionSpectralSequenceMap p
  induction m with
  | zero =>
      change Mono (HomologicalComplex₂.horizontalSecondPageMapOfBicomplex
        ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients.{u}).map
          (projectionDiagramMap p)) a 0)
      let : IsIso (HomologicalComplex₂.horizontalSecondPageMapOfBicomplex
        ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients.{u}).map
          (projectionDiagramMap p)) a 0) := actualSecondPageProjection_rowZero_isIso p hπ a
      infer_instance
  | succ m ih =>
      let r : ℤ := (m : ℤ) + 2
      let r' : ℤ := ((m + 1 : ℕ) : ℤ) + 2
      have hrr' : r + 1 = r' := by dsimp only [r, r']; omega
      have hr2 : 2 ≤ r := by omega
      have hr : 1 ≤ r := by omega
      have hr' : 1 ≤ r' := by omega
      let : Mono ((φ.hom r hr).f (a, 0)) := ih
      let h := HomologicalComplex.homologyMap (φ.hom r hr) (a, 0)
      let : Mono h := HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
        (φ.hom r hr) (a, 0) (firstQuadrant_zeroRow_noIncoming r hr2 a)
      let eS := S.iso r r' (a, 0) hrr' hr
      let eT := T.iso r r' (a, 0) hrr' hr
      let g := (φ.hom r' hr').f (a, 0)
      have hc : h ≫ eT.hom = eS.hom ≫ g := φ.comm r r' (a, 0) hrr' hr
      let : Mono (eS.hom ≫ g) := by rw [← hc]; infer_instance
      have hm : Mono (eS.inv ≫ (eS.hom ≫ g)) := inferInstance
      simpa only [Iso.inv_hom_id_assoc] using hm

private theorem actualProjection_rowZero_mono {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [E.IsConnected] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b))
    (a : ℕ) (r : ℤ) (hr : 2 ≤ r) : Mono (((actualProjectionSpectralSequenceMap p).hom r).f (a, 0))
      := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, r = (m : ℤ) + 2 := by
    let m := (r - 2).toNat
    refine ⟨m, ?_⟩
    dsimp only [m]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  subst r
  exact actualProjection_rowZero_mono_add_two p hπ a m

/-- A monic term map and an epic homology map force the differential out of
that source term to vanish when the target term is isolated. All assumptions
are structural facts that will be DERIVED for the sole actual transgression. -/
private theorem differential_eq_zero_of_homologyMap_epi
    {C : Type u} [Category C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} (f : K ⟶ L) (j : ι)
    (hinL : L.d (c.prev j) j = 0)
    (houtL : L.d j (c.next j) = 0) [Mono (f.f j)]
    [Epi (HomologicalComplex.homologyMap f j)] : K.d j (c.next j) = 0 := by
  let : IsIso (L.homologyπ j) := L.isIso_homologyπ (c.prev j) j rfl hinL
  let : IsIso (L.iCycles j) := L.isIso_iCycles j (c.next j) rfl houtL
  let m := HomologicalComplex.cyclesMap f j
  let : Epi (m ≫ L.homologyπ j) := by
    dsimp only [m]
    rw [← HomologicalComplex.homologyπ_naturality f j]
    infer_instance
  let : Epi m := (epi_comp_iff_of_isIso m (L.homologyπ j)).mp inferInstance
  let : Epi (K.iCycles j ≫ f.f j) := by
    rw [← HomologicalComplex.cyclesMap_i f j]
    change Epi (m ≫ L.iCycles j)
    infer_instance
  let : Epi (f.f j) := epi_of_epi (K.iCycles j) (f.f j)
  let : IsIso (f.f j) := isIso_of_mono_of_epi _
  let : Epi (K.iCycles j) := (epi_comp_iff_of_isIso (K.iCycles j) (f.f j)).mp inferInstance
  apply (cancel_epi (K.iCycles j)).mp
  rw [HomologicalComplex.iCycles_d, comp_zero]

/-- A source term with no outgoing shape has zero actual outgoing differential. -/
private theorem actualZeroColumn_outgoing_zero {E B : SSet.{u}} (p : E ⟶ B)
    (r : ℤ) (hr : 1 ≤ r) (n : ℕ) (k : ℕ × ℕ) :
    ((SSet.bkHomologySpectralSequence integralCoefficients
      (SSet.simplexPullbackDiagram p)).page r hr).d (0, n) k = 0 :=
  HomologicalComplex.shape _ _ _ (firstQuadrant_zeroColumn_noOutgoing r hr n k)

private theorem actualZeroRow_incoming_zero {E B : SSet.{u}} (p : E ⟶ B)
    (r : ℤ) (hr : 2 ≤ r) (n : ℕ) (i : ℕ × ℕ) :
    ((SSet.bkHomologySpectralSequence integralCoefficients
      (SSet.simplexPullbackDiagram p)).page r (by omega)).d i (n, 0) = 0 :=
  HomologicalComplex.shape _ _ _ (firstQuadrant_zeroRow_noIncoming r hr n i)

/-- A vanished actual second-page term stays zero at every later page by
the EXISTING first-quadrant collapse theorem. -/
private theorem actualPage_isZero_of_secondPage {E B : SSet.{u}}
    (p : E ⟶ B) (a b : ℕ) (r : ℤ) (hr : 2 ≤ r)
    (hz : IsZero (((SSet.bkHomologySpectralSequence integralCoefficients
      (SSet.simplexPullbackDiagram p)).page 2).X (a, b))) :
    IsZero (((SSet.bkHomologySpectralSequence integralCoefficients
      (SSet.simplexPullbackDiagram p)).page r (by omega)).X (a, b)) := by
  let m := (r - 2).toNat
  have hre : r = (m : ℤ) + 2 := by
    dsimp only [m]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have h := HomologicalComplex₂.isZero_horizontalPage_add_two_of_isZero_secondPage
    (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} integralCoefficients.{u}
      (SSet.simplexPullbackDiagram p)) a b m hz
  exact IsZero.of_iso h
    (CategoryTheory.SpectralSequence.pageXIsoOfEq
      (SSet.bkHomologySpectralSequence integralCoefficients.{u} (SSet.simplexPullbackDiagram p))
      (a, b) r ((m : ℤ) + 2) hre (by omega))

/-- Before page n+1, every incoming differential to the actual (0,n)
term comes from a previous positive fiber row, hence is zero. -/
private theorem actualZeroColumn_incoming_zero_before_first {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b)) (b : B _⦋0⦌) (n : ℕ)
    (hbelow : ∀ q : ℕ, 1 ≤ q → q < n →
      IsZero ((SSet.Subcomplex.fiber p b : SSet.{u}).homology integralCoefficients q))
    (r : ℤ) (hr : 2 ≤ r) (hsmall : r ≤ (n : ℤ)) (i : ℕ × ℕ) :
    ((SSet.bkHomologySpectralSequence integralCoefficients
      (SSet.simplexPullbackDiagram p)).page r (by omega)).d i (0, n) = 0 := by
  let P := (SSet.bkHomologySpectralSequence integralCoefficients.{u}
    (SSet.simplexPullbackDiagram p)).page r
  let c := ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩
  by_cases hrel : c.Rel i (0, n)
  · have hs : (i.2 : ℤ) + (r - 1) = (n : ℤ) := hrel.2
    have hq : 1 ≤ i.2 := by omega
    have hqn : i.2 < n := by omega
    have hz : IsZero (((SSet.bkHomologySpectralSequence integralCoefficients.{u}
        (SSet.simplexPullbackDiagram p)).page 2).X (i.1, i.2)) :=
      actualSecondPage_isZero_of_fiberHomology_isZero p hπ b i.2 (hbelow i.2 hq hqn) i.1
    have hpage : IsZero (P.X i) := actualPage_isZero_of_secondPage p i.1 i.2 r hr hz
    exact hpage.eq_of_src _ _
  · exact P.shape i (0, n) hrel

private noncomputable def actualZeroColumn_pageSuccIso {E B : SSet.{u}}
    (p : E ⟶ B) (r : ℤ) (hr : 2 ≤ r) (n : ℕ)
    (hin : ((SSet.bkHomologySpectralSequence integralCoefficients
      (SSet.simplexPullbackDiagram p)).page r (by omega)).d
        ((ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).prev (0, n)) (0, n) = 0) :
    ((SSet.bkHomologySpectralSequence integralCoefficients
      (SSet.simplexPullbackDiagram p)).page r (by omega)).X (0, n) ≅
    ((SSet.bkHomologySpectralSequence integralCoefficients
      (SSet.simplexPullbackDiagram p)).page (r + 1) (by omega)).X (0, n) := by
  let S := SSet.bkHomologySpectralSequence integralCoefficients.{u} (SSet.simplexPullbackDiagram p)
  let P := S.page r
  let c := ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩
  let k := c.next (0, n)
  have hout : P.d (0, n) k = 0 := actualZeroColumn_outgoing_zero p r (by omega) n k
  exact (P.iCyclesIso (0, n) k rfl hout).symm ≪≫
    P.isoHomologyπ (c.prev (0, n)) (0, n) rfl hin ≪≫
      S.iso r (r + 1) (0, n) rfl (by omega)

/-- The actual zero-column term is unchanged up to the sole transgression
page, using only derived previous-row zeros and the original native successors. -/
private noncomputable def actualZeroColumn_beforeTransgressionIso {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b)) (b : B _⦋0⦌) (n : ℕ)
    (hbelow : ∀ q : ℕ, 1 ≤ q → q < n →
      IsZero ((SSet.Subcomplex.fiber p b : SSet.{u}).homology integralCoefficients q))
    (m : ℕ) (hm : m + 1 ≤ n) :
    ((SSet.bkHomologySpectralSequence integralCoefficients
      (SSet.simplexPullbackDiagram p)).page 2).X (0, n) ≅
    ((SSet.bkHomologySpectralSequence integralCoefficients
      (SSet.simplexPullbackDiagram p)).page ((m : ℤ) + 2)).X (0, n) := by
  revert hm
  induction m with
  | zero => intro hm; exact Iso.refl _
  | succ m ih =>
      intro hm
      let r : ℤ := (m : ℤ) + 2
      have hr : 2 ≤ r := by dsimp only [r]; omega
      have hsmall : r ≤ (n : ℤ) := by dsimp only [r]; omega
      let i := (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).prev (0, n)
      have hin := actualZeroColumn_incoming_zero_before_first p hπ b n hbelow r hr hsmall i
      let e := actualZeroColumn_pageSuccIso p r hr n hin
      let eindex := CategoryTheory.SpectralSequence.pageXIsoOfEq
        (SSet.bkHomologySpectralSequence integralCoefficients.{u} (SSet.simplexPullbackDiagram p))
        (0, n) (r + 1) ((((m + 1 : ℕ) : ℤ)) + 2)
        (by dsimp only [r]; push_cast; omega) (by omega)
      exact ih (by omega) ≪≫ e ≪≫ eindex

/-- The actual cokernel functor sends a square with epic right side to an
epic map, by the existing cokernel descent instance. -/
private theorem actualCokernelMap_epi_of_right_epi {C : Type u} [Category C] [Abelian C]
    {f g : Arrow C} (h : f ⟶ g) [Epi h.right] : Epi ((Limits.coker C).map h) := by
  change Epi (cokernel.desc f.hom (h.right ≫ cokernel.π g.hom)
    (by simp [← Arrow.w_assoc h]))
  infer_instance

/-- The source filtration stage is zero when its actual monic total map
factors through a zero target stage. -/
private theorem sourceStage_isZero_of_mono_total {C : Type u} [Category C] [HasZeroMorphisms C]
    {A B H K : C} (i : A ⟶ H) [Mono i] (f : H ⟶ K) [Mono f]
    (s : A ⟶ B) (j : B ⟶ K) (hB : IsZero B) (hcomm : i ≫ f = s ≫ j) : IsZero A := by
  have hs : s = 0 := hB.eq_of_tgt _ _
  have hif : i ≫ f = 0 := hcomm.trans (by rw [hs, zero_comp])
  have hi : i = 0 := (cancel_mono f).mp (by simpa only [zero_comp] using hif)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_mono i).mp
  simpa only [Category.id_comp, zero_comp] using hi

/-- In positive total degree, the actual identity-base lowest filtration
stage is zero by its positive-row vanishing and EXISTING convergence. -/
private theorem baseFiniteFiltrationZeroStage_isZero (B : SSet.{u}) (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((HomologicalComplex₂.horizontalFiniteTotalHomologyFiltration
      (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} integralCoefficients
        (SSet.simplexPullbackDiagram (𝟙 B))) n).obj 0) := by
  let L := SSet.bkAlternatingBicomplex AddCommGrpCat.{u} integralCoefficients.{u}
    (SSet.simplexPullbackDiagram (𝟙 B))
  have hg : IsZero (HomologicalComplex₂.horizontalTotalHomologyGradedPiece L 0 n) :=
    HomologicalComplex₂.isZero_horizontalTotalHomologyGradedPiece_of_secondPage L 0 n
      (basePositiveSecondPage_isZero B 0 n hn)
  have hc : IsZero ((HomologicalComplex₂.horizontalTotalHomologyFiltration L n).obj
      ((0 : ℤ) : EInt)) :=
    IsZero.of_iso hg (HomologicalComplex₂.horizontalTotalHomologyGradedPieceZeroIsoFiltrationZero L
      n).symm
  exact IsZero.of_iso hc
    ((HomologicalComplex₂.horizontalCompleteFiniteHomologyFiltrationDiagramIso L n).app 0).symm

/-- Injectivity of the SAME actual original homology map makes the source's
lowest positive-degree filtration stage zero via the actual image-map square. -/
private theorem actualFiniteFiltrationZeroStage_isZero {E B : SSet.{u}}
    (p : E ⟶ B) (n : ℕ) (hn : 1 ≤ n)
    [IsIso (SSet.homologyMap p integralCoefficients n)] :
    IsZero ((HomologicalComplex₂.horizontalFiniteTotalHomologyFiltration
      (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} integralCoefficients
        (SSet.simplexPullbackDiagram p)) n).obj 0) := by
  let K := SSet.bkAlternatingBicomplex AddCommGrpCat.{u} integralCoefficients.{u}
    (SSet.simplexPullbackDiagram p)
  let L := SSet.bkAlternatingBicomplex AddCommGrpCat.{u} integralCoefficients.{u}
    (SSet.simplexPullbackDiagram (𝟙 B))
  let f : K ⟶ L := (SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u}
    integralCoefficients.{u}).map
    (projectionDiagramMap p)
  let i := (HomologicalComplex₂.horizontalFiniteTotalHomologyFiltration K n).ι.app 0
  let j := (HomologicalComplex₂.horizontalFiniteTotalHomologyFiltration L n).ι.app 0
  let a := ((HomologicalComplex₂.horizontalFiniteTotalHomologyFiltrationDiagramFunctor n).map f).app
    0
  let t := HomologicalComplex.homologyMap (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) n
  let : Mono i := by
    dsimp only [i]
    rw [HomologicalComplex₂.horizontalFiniteTotalHomologyFiltration_ι_app]
    exact (Image.monoFactorisation
      (HomologicalComplex.homologyMap (K.horizontalFilteredTotalComplexToTotal 0) n)).m_mono
  let : IsIso t := originalTotalHomology_projection_isIso p n
  have hc : a ≫ j = i ≫ t :=
    HomologicalComplex₂.horizontalFiniteTotalHomologyFiltrationDiagramFunctor_map_app_ι n f 0
  exact sourceStage_isZero_of_mono_total i t a j (baseFiniteFiltrationZeroStage_isZero B n hn)
    hc.symm

/-- The actual source stable zero-column term vanishes in positive degree,
using its actual lowest image stage and the canonical stable/graded Iso. -/
private theorem actualStableZeroColumn_isZero {E B : SSet.{u}} (p : E ⟶ B)
    (n : ℕ) (hn : 1 ≤ n) [IsIso (SSet.homologyMap p integralCoefficients n)] :
    IsZero (((SSet.bkHomologySpectralSequence integralCoefficients
      (SSet.simplexPullbackDiagram p)).page
        (HomologicalComplex₂.horizontalStablePageIndex 0 n)).X (0, n)) := by
  let K := SSet.bkAlternatingBicomplex AddCommGrpCat.{u} integralCoefficients.{u}
    (SSet.simplexPullbackDiagram p)
  have hf : IsZero ((HomologicalComplex₂.horizontalFiniteTotalHomologyFiltration K n).obj 0) :=
    actualFiniteFiltrationZeroStage_isZero p n hn
  have hc : IsZero ((HomologicalComplex₂.horizontalTotalHomologyFiltration K n).obj ((0 : ℤ) :
    EInt)) :=
    IsZero.of_iso hf ((HomologicalComplex₂.horizontalCompleteFiniteHomologyFiltrationDiagramIso K
      n).app 0)
  have hg : IsZero (HomologicalComplex₂.horizontalTotalHomologyGradedPiece K 0 n) :=
    IsZero.of_iso hc (HomologicalComplex₂.horizontalTotalHomologyGradedPieceZeroIsoFiltrationZero K
      n)
  exact IsZero.of_iso hg (HomologicalComplex₂.horizontalStablePageGradedIsoAtIndex K 0 n)

/-- Actual total-homology epimorphy reaches the top graded piece via the
EXISTING inclusion square, exhaustive stage and cokernel functor. -/
private theorem actualTopGradedProjection_epi {E B : SSet.{u}} (p : E ⟶ B) (a : ℕ)
    [IsIso (SSet.homologyMap p integralCoefficients a)] :
    Epi (HomologicalComplex₂.horizontalTotalHomologyGradedPieceMapOfBicomplex
      ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients).map
        (projectionDiagramMap p)) a 0) := by
  let K := SSet.bkAlternatingBicomplex AddCommGrpCat.{u} integralCoefficients.{u}
    (SSet.simplexPullbackDiagram p)
  let L := SSet.bkAlternatingBicomplex AddCommGrpCat.{u} integralCoefficients.{u}
    (SSet.simplexPullbackDiagram (𝟙 B))
  let f : K ⟶ L := (SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u}
    integralCoefficients.{u}).map
    (projectionDiagramMap p)
  let v := HomologicalComplex₂.horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f a 0
  let i := (HomologicalComplex₂.horizontalTotalHomologyFiltration K a).ι.app ((a : ℤ) : EInt)
  let j := (HomologicalComplex₂.horizontalTotalHomologyFiltration L a).ι.app ((a : ℤ) : EInt)
  let t := HomologicalComplex.homologyMap (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) a
  let : IsIso i := HomologicalComplex₂.horizontalTotalHomologyFiltration_exhaustive K a
  let : IsIso j := HomologicalComplex₂.horizontalTotalHomologyFiltration_exhaustive L a
  let : IsIso t := originalTotalHomology_projection_isIso p a
  have hc : v ≫ j = i ≫ t := by
    simpa only [Nat.add_zero] using
      HomologicalComplex₂.horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_ι f a 0
  let : Epi (v ≫ j) := by rw [hc]; infer_instance
  let : Epi v := (epi_comp_iff_of_isIso v j).mp inferInstance
  let h := HomologicalComplex₂.horizontalTotalHomologyFiltrationStepSquareOfBicomplex f a 0
  let : Epi h.right := by change Epi v; infer_instance
  change Epi ((Limits.coker AddCommGrpCat.{u}).map h)
  exact actualCokernelMap_epi_of_right_epi h

/-- The canonical stable-page/graded square makes the SAME actual native
top-page map epic; its native-page equality is an existing theorem. -/
private theorem actualStableTopProjection_epi {E B : SSet.{u}} (p : E ⟶ B) (a : ℕ)
    [IsIso (SSet.homologyMap p integralCoefficients a)] :
    Epi (((actualProjectionSpectralSequenceMap p).hom
      (HomologicalComplex₂.horizontalStablePageIndex a 0)).f (a, 0)) := by
  let K := SSet.bkAlternatingBicomplex AddCommGrpCat.{u} integralCoefficients.{u}
    (SSet.simplexPullbackDiagram p)
  let L := SSet.bkAlternatingBicomplex AddCommGrpCat.{u} integralCoefficients.{u}
    (SSet.simplexPullbackDiagram (𝟙 B))
  let f : K ⟶ L := (SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u}
    integralCoefficients.{u}).map
    (projectionDiagramMap p)
  let g := HomologicalComplex₂.horizontalTotalHomologyGradedPieceMapOfBicomplex f a 0
  let φ := HomologicalComplex₂.horizontalStablePageMapOfBicomplex f a 0
  let eK := HomologicalComplex₂.horizontalStablePageGradedIsoAtIndex K a 0
  let eL := HomologicalComplex₂.horizontalStablePageGradedIsoAtIndex L a 0
  let : Epi g := actualTopGradedProjection_epi p a
  have hc : φ ≫ eL.hom = eK.hom ≫ g := stablePageProjection_graded p a 0
  let : Epi (φ ≫ eL.hom) := by rw [hc]; infer_instance
  let : Epi φ := (epi_comp_iff_of_isIso φ eL.hom).mp inferInstance
  change Epi ((HomologicalComplex₂.horizontalPageMapOfBicomplex f
    (HomologicalComplex₂.horizontalStablePageIndex a 0)
    (HomologicalComplex₂.horizontalStablePageIndex_one_le a 0)).f (a, 0))
  rw [← HomologicalComplex₂.horizontalStablePageMapOfBicomplex_eq_pageMap f a 0]
  exact inferInstance

/-- The sole possible row-zero transgression into (0,n) vanishes, by the
ACTUAL top-graded epi and ACTUAL native successor square. -/
private theorem actualTransgression_eq_zero {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [E.IsConnected] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b))
    (n : ℕ) (hn : 1 ≤ n) [IsIso (SSet.homologyMap p integralCoefficients (n + 1))] :
    ((SSet.bkHomologySpectralSequence integralCoefficients
      (SSet.simplexPullbackDiagram p)).page ((n : ℤ) + 1) (by omega)).d (n + 1, 0) (0, n) = 0 := by
  let S := SSet.bkHomologySpectralSequence integralCoefficients.{u} (SSet.simplexPullbackDiagram p)
  let T := SSet.bkHomologySpectralSequence integralCoefficients.{u} (SSet.simplexPullbackDiagram (𝟙
    B))
  let φ := actualProjectionSpectralSequenceMap p
  let r : ℤ := (n : ℤ) + 1
  let r' := HomologicalComplex₂.horizontalStablePageIndex (n + 1) 0
  let j : ℕ × ℕ := (n + 1, 0)
  let k : ℕ × ℕ := (0, n)
  let c := ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩
  have hr : 2 ≤ r := by dsimp only [r]; omega
  have hrr' : r + 1 = r' := by
    dsimp only [r, r', HomologicalComplex₂.horizontalStablePageIndex]
    push_cast
    omega
  let f := φ.hom r (by omega)
  let h := HomologicalComplex.homologyMap f j
  let g := (φ.hom r').f j
  let eS := S.iso r r' j hrr' (by omega)
  let eT := T.iso r r' j hrr' (by omega)
  let : Mono (f.f j) := actualProjection_rowZero_mono p hπ (n + 1) r hr
  let : Epi g := actualStableTopProjection_epi p (n + 1)
  have hc : h ≫ eT.hom = eS.hom ≫ g := φ.comm r r' j hrr' (by omega)
  let : Epi (h ≫ eT.hom) := by rw [hc]; infer_instance
  let : Epi h := (epi_comp_iff_of_isIso h eT.hom).mp inferInstance
  have hrel : c.Rel j k := by
    change ((n + 1 : ℕ) : ℤ) + (-r) = (0 : ℤ) ∧ (0 : ℤ) + (r - 1) = n
    dsimp only [r]
    push_cast
    omega
  have hnext : c.next j = k := c.next_eq' hrel
  have hinT : (T.page r).d (c.prev j) j = 0 :=
    actualZeroRow_incoming_zero (𝟙 B) r hr (n + 1) (c.prev j)
  have hzT : IsZero ((T.page r).X k) :=
    actualPage_isZero_of_secondPage (𝟙 B) 0 n r hr (basePositiveSecondPage_isZero B 0 n hn)
  have houtT : (T.page r).d j (c.next j) = 0 := by
    rw [hnext]
    exact hzT.eq_of_tgt _ _
  have hd := differential_eq_zero_of_homologyMap_epi f j hinT houtT
  rw [hnext] at hd
  exact hd

/-- A positive fiber row is zero once previous positive rows are zero.
Every transgression and filtration condition is derived above from the
SAME original homology map; no desired acyclicity is supplied. -/
private theorem actualPositiveFiberRow_isZero {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [E.IsConnected] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b))
    (b : B _⦋0⦌) (n : ℕ) (hn : 1 ≤ n)
    (hbelow : ∀ q : ℕ, 1 ≤ q → q < n →
      IsZero ((SSet.Subcomplex.fiber p b : SSet.{u}).homology integralCoefficients q))
    [IsIso (SSet.homologyMap p integralCoefficients n)]
    [IsIso (SSet.homologyMap p integralCoefficients (n + 1))] :
    IsZero ((SSet.Subcomplex.fiber p b : SSet.{u}).homology integralCoefficients n) := by
  let S := SSet.bkHomologySpectralSequence integralCoefficients.{u} (SSet.simplexPullbackDiagram p)
  let r : ℤ := (n : ℤ) + 1
  let k : ℕ × ℕ := (0, n)
  let j : ℕ × ℕ := (n + 1, 0)
  let c := ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩
  let m := n - 1
  have hm : m + 1 ≤ n := by dsimp only [m]; omega
  let e0 := actualZeroColumn_beforeTransgressionIso p hπ b n hbelow m hm
  let er := CategoryTheory.SpectralSequence.pageXIsoOfEq S k ((m : ℤ) + 2) r
    (by dsimp only [m, r]; omega) (by omega)
  have hrel : c.Rel j k := by
    change ((n + 1 : ℕ) : ℤ) + (-r) = (0 : ℤ) ∧ (0 : ℤ) + (r - 1) = n
    dsimp only [r]
    push_cast
    omega
  have hprev : c.prev k = j := c.prev_eq' hrel
  have hin : (S.page r).d (c.prev k) k = 0 := by
    rw [hprev]
    exact actualTransgression_eq_zero p hπ n hn
  let e1 := actualZeroColumn_pageSuccIso p r (by dsimp only [r]; omega) n hin
  let ei := CategoryTheory.SpectralSequence.pageXIsoOfEq S k (r + 1)
    (HomologicalComplex₂.horizontalStablePageIndex 0 n)
    (by dsimp only [r, HomologicalComplex₂.horizontalStablePageIndex]; omega) (by omega)
  have hlate : IsZero ((S.page (HomologicalComplex₂.horizontalStablePageIndex 0 n)).X k) :=
    actualStableZeroColumn_isZero p n hn
  have hsecond : IsZero ((S.page 2).X k) := IsZero.of_iso hlate (e0 ≪≫ er ≪≫ e1 ≪≫ ei)
  exact IsZero.of_iso hsecond (actualZeroColumnFiberHomologyIso p hπ b n).symm

/-- Strong induction proves every positive homology group of the SAME
actual strict fiber vanishes from original all-degree homology isomorphisms. -/
private theorem actualKanFiber_positiveHomology_isZero {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [E.IsConnected] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b)) (b : B _⦋0⦌)
    (hhom : ∀ n : ℕ, IsIso (SSet.homologyMap p integralCoefficients n)) :
    ∀ n : ℕ, 1 ≤ n →
      IsZero ((SSet.Subcomplex.fiber p b : SSet.{u}).homology integralCoefficients n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      let : IsIso (SSet.homologyMap p integralCoefficients.{u} n) := hhom n
      let : IsIso (SSet.homologyMap p integralCoefficients.{u} (n + 1)) := hhom (n + 1)
      exact actualPositiveFiberRow_isZero p hπ b n hn (fun q hq hqn => ih q hqn hq)

private theorem originalIntegralHomology_isZero_of_weak {X Y : TopCat.{u}}
    (f : X ⟶ Y) (hf : TopCat.weakHomotopyEquivalences f) (n : ℕ)
    (hz : IsZero (AlgebraicTopology.singularIntegralHomology n X)) :
    IsZero (AlgebraicTopology.singularIntegralHomology n Y) := by
  let : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f) :=
    hf.isIso_singularHomologyFunctor_map singularIntegralCoefficients.{u} n
  exact IsZero.of_iso hz (asIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f)).symm

private theorem originalIntegralAugmentation_isIso_of_weak {X Y : TopCat.{u}}
    (f : X ⟶ Y) (hf : TopCat.weakHomotopyEquivalences f)
    [IsIso ((TopCat.toSSet.obj X).homology₀ε integralCoefficients)] :
    IsIso ((TopCat.toSSet.obj Y).homology₀ε integralCoefficients) := by
  let h := SSet.homologyMap (TopCat.toSSet.map f) integralCoefficients.{u} 0
  let : IsIso h := hf.isIso_singularHomologyFunctor_map singularIntegralCoefficients.{u} 0
  have hn : h ≫ (TopCat.toSSet.obj Y).homology₀ε integralCoefficients.{u} =
      (TopCat.toSSet.obj X).homology₀ε integralCoefficients.{u} :=
    SSet.homologyMap_comp_homology₀ε (TopCat.toSSet.map f) integralCoefficients.{u}
  let : IsIso (h ≫ (TopCat.toSSet.obj Y).homology₀ε integralCoefficients.{u}) := by
    rw [hn]
    infer_instance
  exact (isIso_comp_left_iff h ((TopCat.toSSet.obj Y).homology₀ε integralCoefficients.{u})).mp
    inferInstance

private theorem realizedIntegralHomology_isZero_of_simplicial {X : SSet.{u}}
    (n : ℕ) (hz : IsZero (X.homology integralCoefficients n)) :
    IsZero (AlgebraicTopology.singularIntegralHomology n (SSet.toTop.obj X)) := by
  let i := sSetTopAdj.unit.app X
  let : IsIso (SSet.homologyMap i integralCoefficients.{u} n) :=
    homologyMap_isIso_of_weak (SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences X)
      integralCoefficients.{u} n
  exact IsZero.of_iso hz (asIso (SSet.homologyMap i integralCoefficients.{u} n)).symm

private theorem realizedIntegralAugmentation_isIso_of_simplicial {X : SSet.{u}}
    [IsIso (X.homology₀ε integralCoefficients)] :
    IsIso ((TopCat.toSSet.obj (SSet.toTop.obj X)).homology₀ε integralCoefficients) := by
  let i := sSetTopAdj.unit.app X
  let h := SSet.homologyMap i integralCoefficients.{u} 0
  let : IsIso h := homologyMap_isIso_of_weak
    (SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences X) integralCoefficients.{u} 0
  have hn : h ≫ (TopCat.toSSet.obj (SSet.toTop.obj X)).homology₀ε integralCoefficients.{u} =
      X.homology₀ε integralCoefficients.{u} := SSet.homologyMap_comp_homology₀ε i
        integralCoefficients.{u}
  let : IsIso (h ≫ (TopCat.toSSet.obj (SSet.toTop.obj X)).homology₀ε integralCoefficients.{u})
    := by
    rw [hn]
    infer_instance
  exact (isIso_comp_left_iff h
    ((TopCat.toSSet.obj (SSet.toTop.obj X)).homology₀ε integralCoefficients.{u})).mp inferInstance

/-- The singular object of the ACTUAL terminal TopCat is the standard point,
by preservation of terminal objects under the existing right adjoint. -/
private noncomputable def singularTerminalPointIso :
    TopCat.toSSet.obj (⊤_ TopCat.{u}) ≅ (Δ[0] : SSet.{u}) :=
  (IsTerminal.isTerminalObj TopCat.toSSet (⊤_ TopCat.{u}) terminalIsTerminal).uniqueUpToIso
    SSet.stdSimplex.isTerminalObj₀

private theorem singularTerminal_isConnected : (TopCat.toSSet.obj (⊤_ TopCat.{u})).IsConnected := by
  let : (Δ[0] : SSet.{u}).IsConnected := point_isConnected
  exact isConnected_source_of_weak
    (SSet.realizationWeakEquivalences.of_isIso singularTerminalPointIso.hom)

private theorem singularTerminal_positiveHomology_isZero (n : ℕ) (hn : 1 ≤ n) :
    IsZero (AlgebraicTopology.singularIntegralHomology n (⊤_ TopCat.{u})) := by
  have hz : IsZero ((Δ[0] : SSet.{u}).homology integralCoefficients.{u} n) :=
    SSet.isZero_homology_of_hasDimensionLT (Δ[0] : SSet.{u}) integralCoefficients.{u} n 1 hn
  exact IsZero.of_iso hz ((SSet.homologyFunctor integralCoefficients.{u} n).mapIso
    singularTerminalPointIso)

/-- Positive-group vanishing and the computed H₀ augmentation recover
isomorphy of the SAME actual terminal homology map, in every degree. This is
only the final dictionary; the original fiber's group data must be DERIVED. -/
private theorem actualTerminalHomologyMap_isIso_of_derived_groups (X : TopCat.{u})
    (hpos : ∀ n : ℕ, 1 ≤ n → IsZero (AlgebraicTopology.singularIntegralHomology n X))
    [IsIso ((TopCat.toSSet.obj X).homology₀ε integralCoefficients)] (n : ℕ) :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map (terminal.from X)) := by
  cases n with
  | zero =>
      let : (TopCat.toSSet.obj (⊤_ TopCat.{u})).IsConnected := singularTerminal_isConnected
      let h := SSet.homologyMap (TopCat.toSSet.map (terminal.from X)) integralCoefficients.{u} 0
      let e := (TopCat.toSSet.obj (⊤_ TopCat.{u})).homology₀ε integralCoefficients.{u}
      have hn : h ≫ e = (TopCat.toSSet.obj X).homology₀ε integralCoefficients.{u} :=
        SSet.homologyMap_comp_homology₀ε (TopCat.toSSet.map (terminal.from X))
          integralCoefficients.{u}
      let : IsIso (h ≫ e) := by rw [hn]; infer_instance
      exact (isIso_comp_right_iff h e).mp inferInstance
  | succ n =>
      exact (hpos (n + 1) (by omega)).isIso
        (singularTerminal_positiveHomology_isZero (n + 1) (by omega)) _

/-- The original all-target-local-system hypothesis makes every positive
integral homology group of the SAME full ending-path homotopy fiber zero. -/
private theorem originalEndingFiber_positiveHomology_isZero {X Y : TopCat.{u}}
    (f : X ⟶ Y) (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (y : Y) (n : ℕ) (hn : 1 ≤ n) :
    IsZero (AlgebraicTopology.singularIntegralHomology n (TopCat.homotopyFiber f y)) := by
  let p := originalRegularKanProjection f y
  let b := originalRegularVertex Y y
  let F : SSet.{u} := SSet.Subcomplex.fiber p b
  let : Fibration p := originalRegularKanProjection_fibration f y
  let : (SSet.mappingPathSpace (originalRegularProjection f y)).IsConnected :=
    originalRegularKanTotal_isConnected f hf y
  let : SSet.KanComplex (originalRegularBase Y y) :=
    SSet.KanComplex.nativeCover_kanComplex (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y)
  let : (originalRegularBase Y y).IsConnected := (originalRegularBase_one_connected Y y).1
  have hF : IsZero (F.homology integralCoefficients.{u} n) :=
    actualKanFiber_positiveHomology_isZero p (originalRegularBase_one_connected Y y).2 b
      (originalRegularKanProjection_homology_isIso f hf y) n hn
  have hr : IsZero (AlgebraicTopology.singularIntegralHomology n (SSet.toTop.obj F)) :=
    realizedIntegralHomology_isZero_of_simplicial n hF
  exact originalIntegralHomology_isZero_of_weak
    (originalEndingFiberComparison f y) (originalEndingFiberComparison_weak f y) n hr

/-- The computed strict-fiber connectedness and both original weak
coordinates preserve the full ending fiber's actual H₀ augmentation. -/
private theorem originalEndingFiber_augmentation_isIso {X Y : TopCat.{u}}
    (f : X ⟶ Y) (hf : TopCat.IsLocalCoefficientHomologyEquivalence f) (y : Y) :
    IsIso ((TopCat.toSSet.obj (TopCat.homotopyFiber f y)).homology₀ε integralCoefficients) := by
  let p := originalRegularKanProjection f y
  let b := originalRegularVertex Y y
  let F : SSet.{u} := SSet.Subcomplex.fiber p b
  let : Fibration p := originalRegularKanProjection_fibration f y
  let : (SSet.mappingPathSpace (originalRegularProjection f y)).IsConnected :=
    originalRegularKanTotal_isConnected f hf y
  let : SSet.KanComplex (originalRegularBase Y y) :=
    SSet.KanComplex.nativeCover_kanComplex (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y)
  let : (originalRegularBase Y y).IsConnected := (originalRegularBase_one_connected Y y).1
  let : F.IsConnected := strictFiber_isConnected p (originalRegularBase_one_connected Y y).2 b
  let : IsIso (F.homology₀ε integralCoefficients.{u}) := inferInstance
  let : IsIso ((TopCat.toSSet.obj (SSet.toTop.obj F)).homology₀ε integralCoefficients.{u}) :=
    realizedIntegralAugmentation_isIso_of_simplicial (X := F)
  exact originalIntegralAugmentation_isIso_of_weak
    (originalEndingFiberComparison f y) (originalEndingFiberComparison_weak f y)

/-- The actual terminal map of EVERY full original ending-path fiber is an
integral homology isomorphism in EVERY degree. No model or acyclicity
witness, original T2/CW/connectedness, flatness or component restriction is supplied. -/
private theorem originalEndingFiber_terminalHomology_isIso {X Y : TopCat.{u}}
    (f : X ⟶ Y) (hf : TopCat.IsLocalCoefficientHomologyEquivalence f) (y : Y) (n : ℕ) :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y))) := by
  let : IsIso ((TopCat.toSSet.obj (TopCat.homotopyFiber f y)).homology₀ε integralCoefficients.{u})
    :=
    originalEndingFiber_augmentation_isIso f hf y
  exact actualTerminalHomologyMap_isIso_of_derived_groups (TopCat.homotopyFiber f y)
    (originalEndingFiber_positiveHomology_isZero f hf y) n

/-- The actual all-local H₀ comparison already derives the structural source
condition. This private bridge therefore needs no additional π₁-surjectivity
premise and returns the SAME original ending-fiber terminal map. -/
private theorem originalAcyclicFiberCriterion {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f) (y : Y) (n : ℕ) :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y))) :=
  originalEndingFiber_terminalHomology_isIso f hf y n








end ActualKanFibrationHomologyCoefficients

end


noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra AlgebraicTopology
open scoped Simplicial SSet.modelCategoryQuillen
universe u
namespace ActualKanFibrationHomologyCoefficients

-- These are the existing canonical colimit choices, installed locally to
-- avoid re-solving a forall-index coproduct problem at every occurrence.
local instance (I : Type u) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance (I : Type u) : HasColimitsOfShape (Discrete I) (ModuleCat.{u} ℤ) :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

local instance : HasCoproducts.{u} (ModuleCat.{u} ℤ) :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
      AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
    ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

attribute [local instance] TopCat.toSSet_obj_kanComplex

/-- The native successor squares propagate the ACTUAL second-page
component isomorphisms. This conditional helper is used only after its
second-page hypothesis is derived from the actual fiber rows below. -/
private theorem actualProjection_allPages_isIso_add_two {E B : SSet.{u}}
    (p : E ⟶ B)
    (h₂ : ∀ pq : ℕ × ℕ, IsIso (((actualProjectionSpectralSequenceMap p).hom 2).f pq))
    (m : ℕ) (pq : ℕ × ℕ) :
    IsIso (((actualProjectionSpectralSequenceMap p).hom ((m : ℤ) + 2)).f pq) := by
  let S := SSet.bkHomologySpectralSequence integralCoefficients (SSet.simplexPullbackDiagram p)
  let T := SSet.bkHomologySpectralSequence integralCoefficients (SSet.simplexPullbackDiagram (𝟙 B))
  let φ := actualProjectionSpectralSequenceMap p
  revert pq
  induction m with
  | zero =>
      intro pq
      change IsIso (((actualProjectionSpectralSequenceMap p).hom 2).f pq)
      exact h₂ pq
  | succ m ih =>
      intro pq
      let r : ℤ := (m : ℤ) + 2
      let r' : ℤ := ((m + 1 : ℕ) : ℤ) + 2
      have hrr' : r + 1 = r' := by dsimp only [r, r']; omega
      let : ∀ i : ℕ × ℕ, IsIso ((φ.hom r).f i) := ih
      let : IsIso (φ.hom r) := HomologicalComplex.Hom.isIso_of_components _
      let h := HomologicalComplex.homologyMap (φ.hom r) pq
      let eS := S.iso r r' pq hrr' (by dsimp only [r]; omega)
      let eT := T.iso r r' pq hrr' (by dsimp only [r]; omega)
      let g := (φ.hom r').f pq
      have hc : h ≫ eT.hom = eS.hom ≫ g := φ.comm r r' pq hrr' (by dsimp only [r]; omega)
      let : IsIso (eS.hom ≫ g) := by
        rw [← hc]
        infer_instance
      exact (isIso_comp_left_iff eS.hom g).mp inferInstance

private theorem actualProjection_allPages_isIso {E B : SSet.{u}} (p : E ⟶ B)
    (h₂ : ∀ pq : ℕ × ℕ, IsIso (((actualProjectionSpectralSequenceMap p).hom 2).f pq))
    (r : ℤ) (hr : 2 ≤ r) (pq : ℕ × ℕ) :
    IsIso (((actualProjectionSpectralSequenceMap p).hom r (by omega)).f pq) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, r = (m : ℤ) + 2 := by
    let m := (r - 2).toNat
    refine ⟨m, ?_⟩
    dsimp only [m]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  subst r
  exact actualProjection_allPages_isIso_add_two p h₂ m pq

/-- For the actual fibration over the simply connected base, all component
maps on the second page are derived from the SAME actual fiber homology
zeros. Row zero retains the existing actual augmentation comparison. -/
private theorem actualProjection_secondPage_isIso_of_fiberRowsZero {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [E.IsConnected] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b)) (b : B _⦋0⦌)
    (hF : ∀ q : ℕ, 1 ≤ q →
      IsZero ((SSet.Subcomplex.fiber p b : SSet.{u}).homology integralCoefficients q))
    (pq : ℕ × ℕ) :
    IsIso (((actualProjectionSpectralSequenceMap p).hom 2).f pq) := by
  obtain ⟨a, q⟩ := pq
  cases q with
  | zero =>
      change IsIso (HomologicalComplex₂.horizontalSecondPageMapOfBicomplex
        ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients).map
          (projectionDiagramMap p)) a 0)
      exact actualSecondPageProjection_rowZero_isIso p hπ a
  | succ q =>
      have hS : IsZero (((SSet.bkHomologySpectralSequence integralCoefficients
          (SSet.simplexPullbackDiagram p)).page 2).X (a, q + 1)) :=
        actualSecondPage_isZero_of_fiberHomology_isZero p hπ b (q + 1) (hF (q + 1) (by omega)) a
      have hT : IsZero (((SSet.bkHomologySpectralSequence integralCoefficients
          (SSet.simplexPullbackDiagram (𝟙 B))).page 2).X (a, q + 1)) :=
        basePositiveSecondPage_isZero B a (q + 1) (by omega)
      exact hS.isIso hT _

/-- Bounded convergence and the existing native stable-page map equality
derive the ACTUAL total quasi-isomorphism; no edge/abutment Iso is an input. -/
private theorem actualProjection_total_quasiIso_of_fiberRowsZero {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [E.IsConnected] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b)) (b : B _⦋0⦌)
    (hF : ∀ q : ℕ, 1 ≤ q →
      IsZero ((SSet.Subcomplex.fiber p b : SSet.{u}).homology integralCoefficients q)) :
    QuasiIso (HomologicalComplex₂.total.map
      ((SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients).map
        (projectionDiagramMap p)) (ComplexShape.down ℕ)) := by
  let f := (SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients).map
    (projectionDiagramMap p)
  have h₂ := actualProjection_secondPage_isIso_of_fiberRowsZero p hπ b hF
  apply HomologicalComplex₂.quasiIso_totalMap_of_isIso_horizontalStablePageMap_firstQuadrant f
  intro a q
  rw [HomologicalComplex₂.horizontalStablePageMapOfBicomplex_eq_pageMap]
  change IsIso (((actualProjectionSpectralSequenceMap p).hom
    (HomologicalComplex₂.horizontalStablePageIndex a q)).f (a, q))
  exact actualProjection_allPages_isIso p h₂
    (HomologicalComplex₂.horizontalStablePageIndex a q)
    (by dsimp only [HomologicalComplex₂.horizontalStablePageIndex]; omega) (a, q)

/-- The SAME original integral homology map is recovered from actual
total quasi-isomorphy and the already calibrated source/target coordinates. -/
private theorem actualKanProjection_integralHomology_isIso_of_fiberRowsZero {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [E.IsConnected] [SSet.KanComplex B] [B.IsConnected]
    (hπ : ∀ b : B _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 B b)) (b : B _⦋0⦌)
    (hF : ∀ q : ℕ, 1 ≤ q →
      IsZero ((SSet.Subcomplex.fiber p b : SSet.{u}).homology integralCoefficients q))
    (n : ℕ) : IsIso (SSet.homologyMap p integralCoefficients n) := by
  let f := (SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} integralCoefficients).map
    (projectionDiagramMap p)
  let : QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) :=
    actualProjection_total_quasiIso_of_fiberRowsZero p hπ b hF
  let : IsIso (HomologicalComplex.homologyMap
      ((SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{u} integralCoefficients).map
        (projectionDiagramMap p)) n) := by
    change IsIso (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) n)
    infer_instance
  have hc := originalTotalHomology_projection p n
  let : IsIso ((originalTotalHomologyIso p n).hom ≫
      SSet.homologyMap p integralCoefficients n) :=
    hc ▸ (inferInstance : IsIso (HomologicalComplex.homologyMap
      ((SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{u} integralCoefficients).map
        (projectionDiagramMap p)) n ≫ (originalTotalHomologyIso (𝟙 B) n).hom))
  exact (isIso_comp_left_iff (originalTotalHomologyIso p n).hom
    (SSet.homologyMap p integralCoefficients n)).mp inferInstance

/-- Connected base and connected actual strict fiber derive connectedness
of the total space through the existing pointed π₀ exact segment. -/
private theorem pointedTotal_isConnected_of_fiber (S : SSet.FibrationSequence.{u})
    [S.B.IsConnected] [S.fiber.IsConnected] : S.E.IsConnected := by
  let : Subsingleton (SSet.KanComplex.π 0 S.B S.b) :=
    (SSet.KanComplex.π₀EquivπZero S.b).subsingleton_congr.mp inferInstance
  let : Subsingleton (SSet.KanComplex.π 0 S.fiber S.fiberPoint) :=
    (SSet.KanComplex.π₀EquivπZero S.fiberPoint).subsingleton_congr.mp inferInstance
  have hE : Subsingleton (SSet.KanComplex.π 0 S.E S.e) := by
    constructor
    intro a b
    obtain ⟨r, hr⟩ := S.exactness_at_E a (Subsingleton.elim _ _)
    obtain ⟨s, hs⟩ := S.exactness_at_E b (Subsingleton.elim _ _)
    exact hr.symm.trans
      ((congrArg (SSet.KanComplex.π.map S.fiberIncl rfl 0)
        (Subsingleton.elim r s)).trans hs)
  apply (SSet.isConnected_iff (X := S.E)).mpr
  exact ⟨(SSet.KanComplex.π₀EquivπZero S.e).subsingleton_congr.mpr hE, ⟨S.e⟩⟩

private theorem total_isConnected_of_connectedStrictFiber {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [SSet.KanComplex B] [B.IsConnected]
    (b : B _⦋0⦌) [(SSet.Subcomplex.fiber p b : SSet.{u}).IsConnected] :
    E.IsConnected := by
  let z : (SSet.Subcomplex.fiber p b : SSet.{u}) _⦋0⦌ := Classical.arbitrary _
  let S : SSet.FibrationSequence.{u} :=
    { E := E
      B := B
      p := p
      fibration_p := inferInstance
      fibrant_B := inferInstance
      e := z.1
      b := b
      hb := (SSet.Subcomplex.mem_fiber_obj_zero_iff p b).mp z.2 }
  exact pointedTotal_isConnected_of_fiber S

/-- The original integral terminal H₀ map fixes the original augmentation,
using the SAME naturality square and actual terminal object. -/
private theorem originalEndingFiber_augmentation_isIso_of_terminal {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y)
    (h₀ : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 0).map
      (terminal.from (TopCat.homotopyFiber f y)))) :
    IsIso ((TopCat.toSSet.obj (TopCat.homotopyFiber f y)).homology₀ε integralCoefficients) := by
  let t := terminal.from (TopCat.homotopyFiber f y)
  let : IsIso (SSet.homologyMap (TopCat.toSSet.map t) integralCoefficients 0) := h₀
  let : (TopCat.toSSet.obj (⊤_ TopCat.{u})).IsConnected := singularTerminal_isConnected
  have hn : SSet.homologyMap (TopCat.toSSet.map t) integralCoefficients 0 ≫
      (TopCat.toSSet.obj (⊤_ TopCat.{u})).homology₀ε integralCoefficients =
    (TopCat.toSSet.obj (TopCat.homotopyFiber f y)).homology₀ε integralCoefficients :=
    SSet.homologyMap_comp_homology₀ε (TopCat.toSSet.map t) integralCoefficients
  have hi : IsIso (SSet.homologyMap (TopCat.toSSet.map t) integralCoefficients 0 ≫
      (TopCat.toSSet.obj (⊤_ TopCat.{u})).homology₀ε integralCoefficients) := inferInstance
  exact hn ▸ hi

/-- The computed strict fiber is connected from original terminal H₀
acyclicity. Neither its connectedness nor a model is supplied. -/
private theorem originalRegularStrictFiber_isConnected_of_terminal {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y)
    (h₀ : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 0).map
      (terminal.from (TopCat.homotopyFiber f y)))) :
    (SSet.Subcomplex.fiber (originalRegularKanProjection f y)
      (originalRegularVertex Y y) : SSet.{u}).IsConnected := by
  let F : SSet.{u} := SSet.Subcomplex.fiber (originalRegularKanProjection f y)
    (originalRegularVertex Y y)
  let c := originalEndingFiberComparison f y
  let i := sSetTopAdj.unit.app F
  let : IsIso ((TopCat.toSSet.obj (TopCat.homotopyFiber f y)).homology₀ε integralCoefficients) :=
    originalEndingFiber_augmentation_isIso_of_terminal f y h₀
  let : IsIso (SSet.homologyMap (TopCat.toSSet.map c) integralCoefficients 0) :=
    (originalEndingFiberComparison_weak f y).isIso_singularHomologyFunctor_map
      singularIntegralCoefficients.{u} 0
  let : IsIso (SSet.homologyMap i integralCoefficients 0) :=
    homologyMap_isIso_of_weak (SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences F)
      integralCoefficients 0
  have hc : SSet.homologyMap (TopCat.toSSet.map c) integralCoefficients 0 ≫
      (TopCat.toSSet.obj (TopCat.homotopyFiber f y)).homology₀ε integralCoefficients =
    (TopCat.toSSet.obj (SSet.toTop.obj F)).homology₀ε integralCoefficients :=
    SSet.homologyMap_comp_homology₀ε (TopCat.toSSet.map c) integralCoefficients
  let : IsIso ((TopCat.toSSet.obj (SSet.toTop.obj F)).homology₀ε integralCoefficients) :=
    hc ▸ (inferInstance : IsIso (SSet.homologyMap (TopCat.toSSet.map c) integralCoefficients 0 ≫
      (TopCat.toSSet.obj (TopCat.homotopyFiber f y)).homology₀ε integralCoefficients))
  have hi : SSet.homologyMap i integralCoefficients 0 ≫
      (TopCat.toSSet.obj (SSet.toTop.obj F)).homology₀ε integralCoefficients =
    F.homology₀ε integralCoefficients :=
    SSet.homologyMap_comp_homology₀ε i integralCoefficients
  let : IsIso (F.homology₀ε integralCoefficients) :=
    hi ▸ (inferInstance : IsIso (SSet.homologyMap i integralCoefficients 0 ≫
      (TopCat.toSSet.obj (SSet.toTop.obj F)).homology₀ε integralCoefficients))
  exact isConnected_of_integral_augmentation_isIso F

/-- The chosen actual strict-fiber groups vanish by the SAME original
ending-fiber map and realization/singular unit, in every positive degree. -/
private theorem originalRegularStrictFiber_positive_isZero_of_terminal {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y))))
    (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((SSet.Subcomplex.fiber (originalRegularKanProjection f y)
      (originalRegularVertex Y y) : SSet.{u}).homology integralCoefficients n) := by
  let F : SSet.{u} := SSet.Subcomplex.fiber (originalRegularKanProjection f y)
    (originalRegularVertex Y y)
  let t := (AlgebraicTopology.singularIntegralHomologyFunctor n).map
    (terminal.from (TopCat.homotopyFiber f y))
  let c := (AlgebraicTopology.singularIntegralHomologyFunctor n).map
    (originalEndingFiberComparison f y)
  let i := SSet.homologyMap (sSetTopAdj.unit.app F) integralCoefficients n
  let : IsIso t := h n
  let : IsIso c := (originalEndingFiberComparison_weak f y).isIso_singularHomologyFunctor_map
    singularIntegralCoefficients.{u} n
  let : IsIso i := by
    change IsIso (SSet.homologyMap (sSetTopAdj.unit.app F) integralCoefficients n)
    exact homologyMap_isIso_of_weak
      (SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences F) integralCoefficients n
  have hE : IsZero (AlgebraicTopology.singularIntegralHomology n (TopCat.homotopyFiber f y)) :=
    IsZero.of_iso (singularTerminal_positiveHomology_isZero n hn) (asIso t)
  have hR : IsZero (AlgebraicTopology.singularIntegralHomology n (SSet.toTop.obj F)) :=
    IsZero.of_iso hE (asIso c)
  let eI : F.homology integralCoefficients n ≅
      (TopCat.toSSet.obj (SSet.toTop.obj F)).homology integralCoefficients n := by
    letI : IsIso (SSet.homologyMap (sSetTopAdj.unit.app F) integralCoefficients n) :=
      homologyMap_isIso_of_weak
        (SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences F) integralCoefficients n
    exact asIso (SSet.homologyMap (sSetTopAdj.unit.app F) integralCoefficients n)
  exact IsZero.of_iso hR eI

/-- Original ending-fiber H₀ acyclicity derives the connectedness of the
SAME computed target-fibration source. -/
private theorem originalRegularKanSource_isConnected_of_terminal {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y)
    (h₀ : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 0).map
      (terminal.from (TopCat.homotopyFiber f y)))) :
    (SSet.mappingPathSpace (originalRegularProjection f y)).IsConnected := by
  let p := originalRegularKanProjection f y
  let b := originalRegularVertex Y y
  let : Fibration p := originalRegularKanProjection_fibration f y
  let : SSet.KanComplex (originalRegularBase Y y) :=
    SSet.KanComplex.nativeCover_kanComplex (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y)
  let : (originalRegularBase Y y).IsConnected := (originalRegularBase_one_connected Y y).1
  let : (SSet.Subcomplex.fiber p b : SSet.{u}).IsConnected :=
    originalRegularStrictFiber_isConnected_of_terminal f y h₀
  exact total_isConnected_of_connectedStrictFiber p b

/-- Original ending-fiber acyclicity DERIVES every structural hypothesis
of the SAME regular-cover target-fibration scalar comparison. -/
private theorem originalRegularKanProjection_integral_isIso_of_terminal {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y))))
    (n : ℕ) : IsIso (SSet.homologyMap (originalRegularKanProjection f y) integralCoefficients n)
      := by
  let p := originalRegularKanProjection f y
  let b := originalRegularVertex Y y
  let : Fibration p := originalRegularKanProjection_fibration f y
  let : SSet.KanComplex (originalRegularBase Y y) :=
    SSet.KanComplex.nativeCover_kanComplex (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y)
  let : (originalRegularBase Y y).IsConnected := (originalRegularBase_one_connected Y y).1
  let : (SSet.mappingPathSpace (originalRegularProjection f y)).IsConnected :=
    originalRegularKanSource_isConnected_of_terminal f y (h 0)
  exact actualKanProjection_integralHomology_isIso_of_fiberRowsZero
    p (originalRegularBase_one_connected Y y).2 b
    (originalRegularStrictFiber_positive_isZero_of_terminal f y h) n

/-- The original pulled-cover projection retains its actual integral map
after cancellation of the fixed weak mapping-path section. -/
private theorem originalRegularProjection_integral_isIso_of_terminal {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y))))
    (n : ℕ) : IsIso (SSet.homologyMap (originalRegularProjection f y) integralCoefficients n) := by
  let : Fibration (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
    (TopCat.toSSetObj₀Equiv.symm y)) := SSet.KanComplex.nativeCoverProjection_fibration _ _
  let : SSet.KanComplex (originalRegularTotal f y) := inferInstance
  let : SSet.KanComplex (originalRegularBase Y y) :=
    SSet.KanComplex.nativeCover_kanComplex (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y)
  let q := originalRegularProjection f y
  let s := SSet.homologyMap (SSet.mappingPathSection q) integralCoefficients n
  let p := SSet.homologyMap (SSet.mappingPathTarget q) integralCoefficients n
  let : IsIso s := by
    change IsIso (SSet.homologyMap (SSet.mappingPathSection q) integralCoefficients n)
    exact homologyMap_isIso_of_weak (mappingPathSection_weak q) integralCoefficients n
  let : IsIso p := originalRegularKanProjection_integral_isIso_of_terminal f y h n
  have hs : s ≫ p = SSet.homologyMap q integralCoefficients n :=
    ((SSet.homologyFunctor integralCoefficients n).map_comp _ _).symm.trans
      ((SSet.homologyFunctor integralCoefficients n).congr_map
        (SSet.mappingPathSection_comp_target q))
  exact hs ▸ (inferInstance : IsIso (s ≫ p))



end ActualKanFibrationHomologyCoefficients
end

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology
open ActualOriginalMapCalibration
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace ActualKanFibrationHomologyCoefficients

-- These are the existing canonical colimit choices, installed locally to
-- avoid re-solving a forall-index coproduct problem at every occurrence.
local instance (I : Type u) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance (I : Type u) : HasColimitsOfShape (Discrete I) (ModuleCat.{u} ℤ) :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

local instance : HasCoproducts.{u} (ModuleCat.{u} ℤ) :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
      AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
    ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)


attribute [local instance] TopCat.toSSet_obj_kanComplex

/-- The SAME original regular projection has actual integral-module homology
isomorphisms. The exact module/additive-group dictionary is reflected back,
not replaced by an assumed coefficient quasi-isomorphism. -/
private theorem originalRegularProjection_module_isIso_of_terminal {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y)))) (n : ℕ) :
    IsIso (SSet.homologyMap (originalRegularProjection f y)
      integerModuleCoefficients n) := by
  let q := originalRegularProjection f y
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := integerModuleForget.{u}
  let g := SSet.homologyMap q integerModuleCoefficients.{u} n
  let a := SSet.homologyMap q integralCoefficients.{u} n
  let eS := integerModuleHomologyIso (originalRegularTotal f y) n
  let eT := integerModuleHomologyIso (originalRegularBase Y y) n
  let : IsIso a := originalRegularProjection_integral_isIso_of_terminal f y h n
  have hs : U.map g ≫ eT.hom = eS.hom ≫ a :=
    integerModuleHomologyIso_naturality q n
  have hi : IsIso (U.map g ≫ eT.hom) :=
    hs.symm ▸ (inferInstance : IsIso (eS.hom ≫ a))
  let : IsIso (U.map g) :=
    (isIso_comp_right_iff (U.map g) eT.hom).mp hi
  exact isIso_of_reflects_iso g U

/-- Ending-fiber acyclicity derives quasi-isomorphy of the literal original
regular local-system pullback map through its already proved cover square. -/
private theorem originalRegularCoefficientMap_quasiIso_of_terminal {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y)))) :
    QuasiIso (SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map f)
      (CategoryTheory.regularPathModuleCoefficientFunctor
        (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)))) := by
  let sf := TopCat.toSSet.map f
  let b := TopCat.toSSetObj₀Equiv.symm y
  let L : SSet.LocalSystem ℤ (TopCat.toSSet.obj Y) :=
    CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk b)
  let m := SSet.localCoefficientPullbackChainMap sf L
  let q := originalRegularProjection f y
  let c := SSet.chainComplexMap q integerModuleCoefficients.{u}
  let eS := SSet.KanComplex.regularLocalCoefficientPullbackCoverChainIso sf b
  let eT := SSet.KanComplex.originalNativeRegularCoefficientCoverChainIso
    (TopCat.toSSet.obj Y) b
  have hc : QuasiIso c := by
    apply (quasiIso_iff c).mpr
    intro n
    exact (quasiIsoAt_iff_isIso_homologyMap c n).mpr
      (originalRegularProjection_module_isIso_of_terminal f y h n)
  have hs : m ≫ eT.hom = eS.hom ≫ c :=
    SSet.KanComplex.originalRegularPullbackChainMap_cover_square sf b
  let e : Arrow.mk m ≅ Arrow.mk c := Arrow.isoMk eS eT hs.symm
  exact (quasiIso_iff_of_arrow_mk_iso m c e).mpr hc

/-- Path-connectedness gives actual original ordinary paths. The public
singular path equivalence then gives paths in the SAME singular fundamental
groupoid, with no original simplicial connectedness or Kan witness input. -/
private theorem originalSingularRegularPaths (Y : TopCat.{u}) [PathConnectedSpace Y]
    (y : Y) (z : SSet.FundamentalGroupoid (TopCat.toSSet.obj Y)) :
    Nonempty (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y) ⟶ z) := by
  let t := (TopCat.singularFundamentalGroupoidFunctor Y).obj z
  let p : _root_.FundamentalGroupoid.mk y ⟶ t :=
    _root_.Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath y t.as)
  exact ⟨(TopCat.singularRegularPathEquiv Y y z).symm p⟩

/-- Every ORIGINAL integral target local system is covered by the computed
path representation and stalk tensor comparison. The regular comparison and
all construction paths are derived from the SAME original ending fiber. -/
private theorem originalEveryLocalSystemChainMap_quasiIso_of_terminal
    {X Y : TopCat.{u}} [PathConnectedSpace Y] (f : X ⟶ Y) (y : Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y))))
    (L : TopCat.LocalSystem ℤ Y) :
    QuasiIso (TopCat.localCoefficientPullbackChainMap f L) := by
  let sf := TopCat.toSSet.map f
  let b := TopCat.toSSetObj₀Equiv.symm y
  let M : SSet.LocalSystem ℤ (TopCat.toSSet.obj Y) := L.toSingular
  have hr : QuasiIso (SSet.localCoefficientPullbackChainMap sf
      (CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk b))) :=
    originalRegularCoefficientMap_quasiIso_of_terminal f y h
  have hM : QuasiIso (SSet.localCoefficientPullbackChainMap sf M) :=
    originalAllCoefficientPullback_quasiIso_of_regular sf b
      (originalSingularRegularPaths Y y) hr M
  let e := (SSet.localCoefficientChainComplexFunctor (R := ℤ)
    (X := TopCat.toSSet.obj X)).mapIso (TopCat.LocalSystem.singularPullbackIso f L).symm
  let g := SSet.localCoefficientChainMap (TopCat.LocalSystem.singularPullbackIso f L).inv
  have he : e.hom = g :=
    SSet.localCoefficientChainComplexFunctor_map _
  let : IsIso g := he ▸ (inferInstance : IsIso e.hom)
  let : QuasiIso (SSet.localCoefficientPullbackChainMap sf M) := hM
  change QuasiIso (g ≫ SSet.localCoefficientPullbackChainMap sf M)
  infer_instance

/-- EVERY degree and EVERY original target system is an isomorphism on the
SAME public topological local-coefficient homology map. -/
private theorem originalEveryLocalSystemHomology_isIso_of_terminal
    {X Y : TopCat.{u}} [PathConnectedSpace Y] (f : X ⟶ Y) (y : Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y))))
    (L : TopCat.LocalSystem ℤ Y) (n : ℕ) :
    IsIso (TopCat.localCoefficientPullbackHomologyMap f L n) := by
  let : QuasiIso (TopCat.localCoefficientPullbackChainMap f L) :=
    originalEveryLocalSystemChainMap_quasiIso_of_terminal f y h L
  exact (quasiIsoAt_iff_isIso_homologyMap
    (TopCat.localCoefficientPullbackChainMap f L) n).mp inferInstance

/-- The original all-local-coefficient condition is DERIVED from the same
ending-fiber terminal map. A chosen point only instantiates the actual fiber;
no coefficient comparison, edge map, model or acyclicity is supplied. -/
private theorem originalAllLocalCoefficientEquivalence_of_terminal
    {X Y : TopCat.{u}} [PathConnectedSpace Y] (f : X ⟶ Y) (y : Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y)))) :
    TopCat.IsLocalCoefficientHomologyEquivalence f :=
  fun L n => originalEveryLocalSystemHomology_isIso_of_terminal f y h L n

/-- Both directions refer to the SAME full ending-path homotopy fiber and
actual integral terminal maps, and to EVERY original integral target system.
This stronger path-connected-target theorem is used by the connected-CW-type
adapter; it does not claim that connected arbitrary spaces are path connected. -/
private theorem originalEndingFiber_allLocalCoefficient_iff
    {X Y : TopCat.{u}} [PathConnectedSpace Y] (f : X ⟶ Y) :
    (∀ y : Y, ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y)))) ↔
        TopCat.IsLocalCoefficientHomologyEquivalence f := by
  constructor
  · intro h
    let y : Y := Classical.arbitrary Y
    exact originalAllLocalCoefficientEquivalence_of_terminal f y (h y)
  · intro h y n
    exact originalEndingFiber_terminalHomology_isIso f h y n

end ActualKanFibrationHomologyCoefficients

end


noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u v

namespace ActualKanFibrationHomologyCoefficients

open scoped ContinuousMap

-- These are the existing canonical colimit choices, installed locally to
-- avoid re-solving a forall-index coproduct problem at every occurrence.
local instance (I : Type u) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance (I : Type u) : HasColimitsOfShape (Discrete I) (ModuleCat.{u} ℤ) :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

local instance : HasCoproducts.{u} (ModuleCat.{u} ℤ) :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
      AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
    ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)


/-- Full original connected-CW-type acyclicity/local-coefficient iff. The
CW-type datum is precisely the original mathematical qualifier; it is NOT a
model for the ending fiber or a desired comparison/homology witness. The
source space is unrestricted, so the original connected-CW-type source is
included without adding any further hypothesis. -/
private theorem originalConnectedCWType_allLocalCoefficient_iff
    {X Y : TopCat.{u}} [ConnectedSpace Y]
    {C : TopCat.{v}} [T2Space C] [Topology.CWComplex (Set.univ : Set C)]
    (e : C ≃ₕ Y) (f : X ⟶ Y) :
    (∀ y : Y, ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y)))) ↔
        TopCat.IsLocalCoefficientHomologyEquivalence f := by
  let : PathConnectedSpace Y :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType e
  exact originalEndingFiber_allLocalCoefficient_iff f


/-- The original CW-type qualifier may be supplied existentially, with an
independent model universe. No chosen model or inverse for f is an extra input. -/
private theorem originalConnectedCWType_allLocalCoefficient_iff_exists
    {X Y : TopCat.{u}} [ConnectedSpace Y]
    (hCW : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Y))
    (f : X ⟶ Y) :
    (∀ y : Y, ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y)))) ↔
        TopCat.IsLocalCoefficientHomologyEquivalence f := by
  obtain ⟨C, hT, hC, ⟨e⟩⟩ := hCW
  let : T2Space C := hT
  let : Topology.CWComplex (Set.univ : Set C) := hC
  exact originalConnectedCWType_allLocalCoefficient_iff e f

end ActualKanFibrationHomologyCoefficients

end

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open ActualOriginalMapCalibration
open scoped Simplicial

universe u v

namespace ActualOriginalMapCalibration

-- Prefer the existing structural module on tensors and linear maps over
-- the competing canonical integer action; all remain the SAME ℤ-modules.
attribute [local instance 1001] TensorProduct.instModule LinearMap.module


-- These are the existing canonical colimit choices, installed locally to
-- avoid re-solving a forall-index coproduct problem at every occurrence.
local instance (I : Type u) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance (I : Type u) : HasColimitsOfShape (Discrete I) (ModuleCat.{u} ℤ) :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

local instance : HasCoproducts.{u} (ModuleCat.{u} ℤ) :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
      AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
    ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

local instance (Γ : Type u) [Group Γ] (I : Type u) :
    HasColimitsOfShape (Discrete I) (Rep.{u} ℤ Γ) := inferInstance

local instance (Γ : Type u) [Group Γ] : HasCoproducts.{u} (Rep.{u} ℤ Γ) :=
  fun _I => inferInstance



end ActualOriginalMapCalibration

namespace ActualKanFibrationHomologyCoefficients

open scoped ContinuousMap

-- These are the existing canonical colimit choices, installed locally to
-- avoid re-solving a forall-index coproduct problem at every occurrence.
local instance (I : Type u) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance (I : Type u) : HasColimitsOfShape (Discrete I) (ModuleCat.{u} ℤ) :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

local instance : HasCoproducts.{u} (ModuleCat.{u} ℤ) :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
      AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
    ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)



end ActualKanFibrationHomologyCoefficients

end

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ContinuousMap

universe u v

namespace TopCat

/-- Every original ending-path fiber has its actual integral terminal homology map invertible when
  the original map is a local-coefficient homology equivalence. -/
public theorem homotopyFiber_terminalHomology_isIso_of_localCoefficientHomologyEquivalence
    {X Y : TopCat.{u}}
    (f : X ⟶ Y) (hf : TopCat.IsLocalCoefficientHomologyEquivalence f) (y : Y) (n : ℕ) :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y))) := by
  exact _root_.ActualKanFibrationHomologyCoefficients.originalEndingFiber_terminalHomology_isIso f
    hf y n

/-- The actual original pullback chain map is a quasi-isomorphism for every integral target local
  system, from the actual ending-fiber terminal maps. No flatness is required. -/
public theorem localCoefficientPullbackChainMap_quasiIso_of_homotopyFiber
    {X Y : TopCat.{u}} [PathConnectedSpace Y] (f : X ⟶ Y) (y : Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y))))
    (L : TopCat.LocalSystem ℤ Y) :
    QuasiIso (TopCat.localCoefficientPullbackChainMap f L) := by
  exact
    _root_.ActualKanFibrationHomologyCoefficients.originalEveryLocalSystemChainMap_quasiIso_of_terminal
    f y h L

/-- The integral homology-to-a-point condition on every actual ending fiber is equivalent
  to local-coefficient homology equivalence for a connected CW-type target. The original source
  is unrestricted; the canonical reduced-acyclicity criterion appears below with nonemptiness. -/
public theorem homotopyFiber_terminalHomology_iff_localCoefficientHomologyEquivalence
    {X Y : TopCat.{u}} [ConnectedSpace Y]
    (hCW : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Y))
    (f : X ⟶ Y) :
    (∀ y : Y, ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y)))) ↔
        TopCat.IsLocalCoefficientHomologyEquivalence f := by
  exact
    _root_.ActualKanFibrationHomologyCoefficients.originalConnectedCWType_allLocalCoefficient_iff_exists
    hCW f

-- Install the same canonical same-level coproducts used by the accepted proof.
local instance (I : Type u) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

private theorem canonicalTerminal_contractible :
    ContractibleSpace (⊤_ TopCat.{u}) := by
  exact (TopCat.homeoOfIso (TopCat.terminalIsoPUnit.{u})).contractibleSpace

private theorem canonicalAcyclicSpace_of_terminalHomology
    (X : TopCat.{u})
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from X))) : TopCat.IsAcyclicSpace X := by
  let : ContractibleSpace (⊤_ TopCat.{u}) := canonicalTerminal_contractible
  intro n
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
    AlgebraicTopology.singularIntegralHomologyFunctor n
  let t : X ⟶ (⊤_ TopCat.{u}) := terminal.from X
  let : IsIso (H.map t) := h n
  let e : AlgebraicTopology.reducedSingularHomology AddCommGrpCat.{u}
      AlgebraicTopology.singularIntegralCoefficients n X ≅ kernel (H.map t) :=
    AlgebraicTopology.reducedSingularHomologyKernelIsoOfContractibleTarget
      AddCommGrpCat.{u} AlgebraicTopology.singularIntegralCoefficients n t
  have hK : IsZero (kernel (H.map t)) :=
    (CategoryTheory.Preadditive.mono_iff_isZero_kernel (H.map t)).mp inferInstance
  exact hK.of_iso e

/-- For a nonempty space, the canonical reduced-homology predicate is
equivalent to isomorphy of its ACTUAL terminal homology maps. The point of the
space supplies the section; no connectedness or model is assumed. -/
public theorem isAcyclicSpace_iff_terminalHomology_isIso
    (X : TopCat.{u}) [Nonempty X] :
    TopCat.IsAcyclicSpace X ↔
      ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
        (terminal.from X)) := by
  let : ContractibleSpace (⊤_ TopCat.{u}) := canonicalTerminal_contractible
  constructor
  · intro h n
    let H : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
      AlgebraicTopology.singularIntegralHomologyFunctor n
    let t : X ⟶ (⊤_ TopCat.{u}) := terminal.from X
    let e : AlgebraicTopology.reducedSingularHomology AddCommGrpCat.{u}
        AlgebraicTopology.singularIntegralCoefficients n X ≅ kernel (H.map t) :=
      AlgebraicTopology.reducedSingularHomologyKernelIsoOfContractibleTarget
        AddCommGrpCat.{u} AlgebraicTopology.singularIntegralCoefficients n t
    have hK : IsZero (kernel (H.map t)) := (h n).of_iso e.symm
    let : Mono (H.map t) := CategoryTheory.Preadditive.mono_of_isZero_kernel (H.map t) hK
    let x : X := Classical.choice (inferInstance : Nonempty X)
    let s : (⊤_ TopCat.{u}) ⟶ X := TopCat.const x
    let st : SplitEpi t :=
      { section_ := s
        id := terminalIsTerminal.hom_ext _ _ }
    let : IsSplitEpi (H.map t) := IsSplitEpi.mk' (st.map H)
    exact isIso_of_mono_of_isSplitEpi (H.map t)
  · exact canonicalAcyclicSpace_of_terminalHomology X

/-- Every local-coefficient homology equivalence is canonically acyclic at
each original target point, including the repository's empty-space convention. -/
public theorem isAcyclicMapAt_of_localCoefficientHomologyEquivalence
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f) (y : Y) :
    TopCat.IsAcyclicMapAt f y := by
  exact canonicalAcyclicSpace_of_terminalHomology (TopCat.homotopyFiber f y)
    (fun n => homotopyFiber_terminalHomology_isIso_of_localCoefficientHomologyEquivalence
      f hf y n)

private theorem canonicalHomotopyFiber_nonempty
    {X Y : TopCat.{u}} [Nonempty X] [PathConnectedSpace Y]
    (f : X ⟶ Y) (y : Y) : Nonempty (TopCat.homotopyFiber f y) := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let p : Path (f x) y := PathConnectedSpace.somePath (f x) y
  let γ : TopCat.pathObject Y :=
    p.toContinuousMap.comp
      ⟨TopCat.I.homeomorph.{u}, (TopCat.I.homeomorph.{u}).continuous⟩
  have h₀ : γ (0 : TopCat.I.{u}) = f x := by
    change p (TopCat.I.homeomorph.{u} 0) = f x
    have ht : TopCat.I.homeomorph.{u} (0 : TopCat.I.{u}) = (0 : unitInterval) := by simp
    rw [ht]
    exact p.source
  have h₁ : γ (1 : TopCat.I.{u}) = y := by
    change p (TopCat.I.homeomorph.{u} 1) = y
    have ht : TopCat.I.homeomorph.{u} (1 : TopCat.I.{u}) = (1 : unitInterval) := by simp
    rw [ht]
    exact p.target
  let P : TopCat.{u} := TopCat.of PUnit
  let a : P ⟶ X := TopCat.const x
  let c : P ⟶ Y := TopCat.const y
  let k : P ⟶ TopCat.pathObject Y := TopCat.const γ
  let l : P ⟶ X ⨯ P := Limits.prod.lift a (𝟙 P)
  have ha : a ≫ f = k ≫ TopCat.pathEvalZero Y := by
    apply TopCat.ext
    intro z
    exact h₀.symm
  have hc : c = k ≫ TopCat.pathEvalOne Y := by
    apply TopCat.ext
    intro z
    exact h₁.symm
  have hw : l ≫ Limits.prod.map f c = k ≫ TopCat.pathEndpoints Y := by
    apply Limits.prod.hom_ext
    · simpa only [l, TopCat.pathEndpoints, Category.assoc, Limits.prod.map_fst,
        Limits.prod.lift_fst, Limits.prod.lift_fst_assoc] using ha
    · simpa only [l, TopCat.pathEndpoints, Category.assoc, Limits.prod.map_snd,
        Limits.prod.lift_snd, Limits.prod.lift_snd_assoc, Category.id_comp] using hc
  let z : P ⟶ TopCat.homotopyFiber f y := pullback.lift l k hw
  exact ⟨z PUnit.unit⟩

/-- The canonical acyclicity criterion in the original connected CW-type
setting. Nonemptiness comes from the original source and target paths, and the
conclusion uses `IsAcyclicMapAt` on the SAME complete ending fibers. -/
public theorem homotopyFiber_acyclic_iff_localCoefficientHomologyEquivalence
    {X Y : TopCat.{u}} [Nonempty X] [ConnectedSpace Y]
    (hCW : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Y))
    (f : X ⟶ Y) :
    (∀ y : Y, TopCat.IsAcyclicMapAt f y) ↔
      TopCat.IsLocalCoefficientHomologyEquivalence f := by
  have hT := homotopyFiber_terminalHomology_iff_localCoefficientHomologyEquivalence hCW f
  obtain ⟨C, hTC, hC, ⟨e⟩⟩ := hCW
  let : T2Space C := hTC
  let : Topology.CWComplex (Set.univ : Set C) := hC
  let : PathConnectedSpace Y :=
    _root_.Topology.CWComplex.pathConnectedSpace_of_connected_CWType e
  constructor
  · intro h
    apply hT.mp
    intro y n
    let : Nonempty (TopCat.homotopyFiber f y) := canonicalHomotopyFiber_nonempty f y
    exact ((isAcyclicSpace_iff_terminalHomology_isIso (TopCat.homotopyFiber f y)).mp (h y)) n
  · intro hf y
    exact isAcyclicMapAt_of_localCoefficientHomologyEquivalence f hf y

end TopCat

end


/-!
## The actual regular-cover premise

The following bridge starts from the literal regular pullback projection's
integral homology maps. The existing fiber calculation then gives
the actual ending-fiber terminal maps, without an all-local-system or fiber
acyclicity premise. Applications must prove the regular-cover premise from
their original relative chain maps and connecting morphisms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra AlgebraicTopology
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace ActualKanFibrationHomologyCoefficients

local instance (I : Type u) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

attribute [local instance] TopCat.toSSet_obj_kanComplex

/-- The accepted fiber calculation uses only the actual regular homology maps;
its H₀ map derives the source connectedness needed by that calculation. -/
private theorem originalEndingFiber_terminalHomology_isIso_of_regularProjection
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
    (hReg : ∀ n : ℕ, IsIso (SSet.homologyMap
      (originalRegularProjection f y) integralCoefficients n)) (n : ℕ) :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y))) := by
  let : Fibration (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
      (TopCat.toSSetObj₀Equiv.symm y)) := SSet.KanComplex.nativeCoverProjection_fibration _ _
  let : SSet.KanComplex (originalRegularTotal f y) := by
    let a : originalRegularTotal f y ⟶ TopCat.toSSet.obj X :=
      pullback.fst (TopCat.toSSet.map f)
        (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
          (TopCat.toSSetObj₀Equiv.symm y))
    let : Fibration a := SSet.fibration_of_isPullback
      (IsPullback.of_hasPullback (TopCat.toSSet.map f)
        (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
          (TopCat.toSSetObj₀Equiv.symm y)))
    exact HomotopicalAlgebra.isFibrant_of_fibration a
  let : SSet.KanComplex (originalRegularBase Y y) :=
    SSet.KanComplex.nativeCover_kanComplex (TopCat.toSSet.obj Y)
      (TopCat.toSSetObj₀Equiv.symm y)
  let : (originalRegularBase Y y).IsConnected := (originalRegularBase_one_connected Y y).1
  let : IsIso (SSet.homologyMap (originalRegularProjection f y) integralCoefficients.{u} 0) :=
    hReg 0
  let : (originalRegularTotal f y).IsConnected :=
    isConnected_of_integral_homology_zero_isIso (originalRegularProjection f y)
  let : (SSet.mappingPathSpace (originalRegularProjection f y)).IsConnected :=
    isConnected_of_weak (mappingPathSection_weak (originalRegularProjection f y))
  let p := originalRegularKanProjection f y
  let b := originalRegularVertex Y y
  let F : SSet.{u} := SSet.Subcomplex.fiber p b
  let : Fibration p := originalRegularKanProjection_fibration f y
  have hpHom (k : ℕ) : IsIso (SSet.homologyMap p integralCoefficients.{u} k) := by
    let : IsIso (SSet.homologyMap (originalRegularProjection f y) integralCoefficients.{u} k) :=
      hReg k
    change IsIso (SSet.homologyMap (SSet.mappingPathTarget (originalRegularProjection f y))
      integralCoefficients.{u} k)
    exact mappingPathTarget_homology_isIso (originalRegularProjection f y) k
  let : F.IsConnected := strictFiber_isConnected p (originalRegularBase_one_connected Y y).2 b
  let : IsIso (F.homology₀ε integralCoefficients.{u}) := inferInstance
  let : IsIso ((TopCat.toSSet.obj (SSet.toTop.obj F)).homology₀ε integralCoefficients.{u}) :=
    realizedIntegralAugmentation_isIso_of_simplicial (X := F)
  let : IsIso ((TopCat.toSSet.obj (TopCat.homotopyFiber f y)).homology₀ε integralCoefficients.{u}) :=
    originalIntegralAugmentation_isIso_of_weak
      (originalEndingFiberComparison f y) (originalEndingFiberComparison_weak f y)
  have hPos (k : ℕ) (hk : 1 ≤ k) :
      IsZero (AlgebraicTopology.singularIntegralHomology k (TopCat.homotopyFiber f y)) := by
    have hF : IsZero (F.homology integralCoefficients.{u} k) :=
      actualKanFiber_positiveHomology_isZero p (originalRegularBase_one_connected Y y).2 b
        hpHom k hk
    have hReal : IsZero (AlgebraicTopology.singularIntegralHomology k (SSet.toTop.obj F)) :=
      realizedIntegralHomology_isZero_of_simplicial k hF
    exact originalIntegralHomology_isZero_of_weak
      (originalEndingFiberComparison f y) (originalEndingFiberComparison_weak f y) k hReal
  exact actualTerminalHomologyMap_isIso_of_derived_groups (TopCat.homotopyFiber f y) hPos n

end ActualKanFibrationHomologyCoefficients

namespace TopCat

attribute [local instance] TopCat.toSSet_obj_kanComplex

/-- Integral homology isomorphisms of the actual pulled regular cover give all
the actual terminal homology isomorphisms of the original ending-path fiber.
No connectedness, CW, original fibration or fiber-model input is required. -/
public theorem homotopyFiber_terminalHomology_isIso_of_regularCoverHomology
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
    (hReg : ∀ n : ℕ, IsIso (SSet.homologyMap
      (pullback.snd (TopCat.toSSet.map f)
        (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
          (TopCat.toSSetObj₀Equiv.symm y)))
      AlgebraicTopology.singularIntegralCoefficients.{u} n)) (n : ℕ) :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y))) := by
  exact _root_.ActualKanFibrationHomologyCoefficients.originalEndingFiber_terminalHomology_isIso_of_regularProjection
    f y hReg n

/-- At a path-connected original target, one actual regular-cover comparison
implies homology equivalence with every integral target local system. The
accepted actual stalk-tensor and chain-map comparison supplies this implication. -/
public theorem localCoefficientHomologyEquivalence_of_regularCoverHomology
    {X Y : TopCat.{u}} [PathConnectedSpace Y] (f : X ⟶ Y) (y : Y)
    (hReg : ∀ n : ℕ, IsIso (SSet.homologyMap
      (pullback.snd (TopCat.toSSet.map f)
        (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
          (TopCat.toSSetObj₀Equiv.symm y)))
      AlgebraicTopology.singularIntegralCoefficients.{u} n)) :
    TopCat.IsLocalCoefficientHomologyEquivalence f := by
  exact _root_.ActualKanFibrationHomologyCoefficients.originalAllLocalCoefficientEquivalence_of_terminal
    f y (fun n => homotopyFiber_terminalHomology_isIso_of_regularCoverHomology f y hReg n)

end TopCat

end


/-!
## Integral Kan and original acyclic-map recognition

The following results give integral Kan loop and original-map recognition
using the existing fiber and local-coefficient calculations. The public
interfaces retain the original maps and required hypotheses.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra AlgebraicTopology
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace ActualKanFibrationHomologyCoefficients

-- The existing accepted canonical coproduct choices are local to this reopened scope.
local instance (I : Type u) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance (I : Type u) : HasColimitsOfShape (Discrete I) (ModuleCat.{u} ℤ) :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

local instance : HasCoproducts.{u} (ModuleCat.{u} ℤ) :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
      AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
    ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)


/-- Commutativity is transported through the EXISTING actual multiplicative
connecting shift. It is not a supplied loop-space structure. -/
private theorem actualLoop_piOne_mul_comm
    (K : SSet.{u}) [SSet.KanComplex K] (v : K _⦋0⦌)
    (a b : SSet.KanComplex.π 1 (SSet.loopSpace K v)
      (SSet.LoopShiftOriginalGeometry.originalLoopPoint K v)) : a * b = b * a := by
  let F : SSet.{u} := SSet.loopSpace K v
  let z : F _⦋0⦌ := SSet.LoopShiftOriginalGeometry.originalLoopPoint K v
  let : SSet.KanComplex F := SSet.loopSpace_kanComplex K v
  let e : SSet.KanComplex.π 2 K v ≃* SSet.KanComplex.π 1 F z :=
    SSet.loopConnectingMulEquiv 0 K v
  apply e.symm.injective
  rw [e.symm.map_mul, e.symm.map_mul]
  exact SSet.KanComplex.π.mul_comm_two v (e.symm a) (e.symm b)

/-- First Hurewicz kills an ACTUAL commuting native pi-one group when its
integral H1 vanishes. The commuting operations are the existing group operations. -/
private theorem nativePiOne_subsingleton_of_comm_and_H1_zero
    (K : SSet.{u}) [SSet.KanComplex K] [K.IsConnected] (v : K _⦋0⦌)
    (hc : ∀ a b : SSet.KanComplex.π 1 K v, a * b = b * a)
    (hH : IsZero (K.homology integralCoefficients 1)) :
    Subsingleton (SSet.KanComplex.π 1 K v) := by
  let G := SSet.KanComplex.π 1 K v
  let : CommGroup G := { (inferInstance : Group G) with mul_comm := hc }
  let eN := SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd v
  let eH := SSet.fundamentalGroupAbelianizationHomologyOneIso K v
  have hz : IsZero (AddCommGrpCat.of
      (Additive (Abelianization (End (SSet.FundamentalGroupoid.mk v))))) :=
    IsZero.of_iso hH eH
  let : Subsingleton (Additive (Abelianization
      (End (SSet.FundamentalGroupoid.mk v)))) := AddCommGrpCat.subsingleton_of_isZero hz
  let e : G ≃* Abelianization (End (SSet.FundamentalGroupoid.mk v)) :=
    (Abelianization.equivOfComm (H := G)).trans eN.abelianizationCongr
  constructor
  intro a b
  apply e.injective
  exact congrArg Additive.toMul
    (Subsingleton.elim (Additive.ofMul (e a)) (Additive.ofMul (e b)))

/-- A single actual basepoint suffices on a connected Kan object, by the
original groupoid paths and endomorphism comparisons. -/
private theorem nativePiOne_subsingleton_all_vertices
    (K : SSet.{u}) [SSet.KanComplex K] [K.IsConnected] (v : K _⦋0⦌)
    (hv : Subsingleton (SSet.KanComplex.π 1 K v)) :
    ∀ w : K _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 K w) := by
  have hE : Subsingleton (End (SSet.FundamentalGroupoid.mk v)) :=
    (SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd v).toEquiv.subsingleton_congr.mp hv
  intro w
  let a := (connectedBase_edge v w).some
  let c := asIso (SSet.FundamentalGroupoid.homMk a)
  let e : End (SSet.FundamentalGroupoid.mk v) ≃ End (SSet.FundamentalGroupoid.mk w) :=
    (End.homEquiv (X := SSet.FundamentalGroupoid.mk v)).trans
      ((Iso.homCongr c c).trans (End.homEquiv (X := SSet.FundamentalGroupoid.mk w)).symm)
  have hW : Subsingleton (End (SSet.FundamentalGroupoid.mk w)) :=
    e.subsingleton_congr.mp hE
  exact (SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd w).toEquiv.subsingleton_congr.mpr hW

end ActualKanFibrationHomologyCoefficients

end

/- The existing based-path fibration supplies this continuation;
   no raw-loop CW-type witness is assumed. -/
noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra AlgebraicTopology
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace ActualKanFibrationHomologyCoefficients

-- The existing accepted canonical coproduct choices are local to this reopened scope.
local instance (I : Type u) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance (I : Type u) : HasColimitsOfShape (Discrete I) (ModuleCat.{u} ℤ) :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

local instance : HasCoproducts.{u} (ModuleCat.{u} ℤ) :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
      AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
    ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)


private theorem standardPoint_kan : SSet.KanComplex (Δ[0] : SSet.{u}) := by
  rw [SSet.KanComplex.iff]
  intro n i f hf
  exact ⟨SSet.stdSimplex.isTerminalObj₀.from _,
    fun j hj => SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩

/-- An actual contraction supplies both original maps and homotopies for
weakness of the SAME point projection. Applied only to the public based-path
contraction below, not to a supplied loop-acyclicity witness. -/
private theorem terminalWeak_of_actualContraction (E : SSet.{u}) [SSet.KanComplex E]
    (e : E _⦋0⦌) (H : SSet.Homotopy (SSet.const e) (𝟙 E)) :
    SSet.KanComplex.W (SSet.stdSimplex.isTerminalObj₀.from E) := by
  let : SSet.KanComplex (Δ[0] : SSet.{u}) := standardPoint_kan
  let q := SSet.stdSimplex.isTerminalObj₀.from E
  let s : (Δ[0] : SSet.{u}) ⟶ E := SSet.const e
  apply SSet.KanComplex.W.of_homotopy q s
  · have he : q ≫ s = SSet.const e := by simp only [s, SSet.comp_const]
    exact he.symm ▸ H
  · have he : s ≫ q = 𝟙 (Δ[0] : SSet.{u}) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [he]
    change SSet.RelativeMorphism.Homotopy
      (SSet.RelativeMorphism.botEquiv.symm _) (SSet.RelativeMorphism.botEquiv.symm _)
    exact SSet.RelativeMorphism.Homotopy.refl _

/-- Every group and the vertex of the EXISTING total space give its
connectedness, with no independent model or path-space replacement. -/
private theorem existingLoop_total_connected (K : SSet.{u}) [SSet.KanComplex K]
    (v : K _⦋0⦌) : (SSet.loopFibrationSequence K v).E.IsConnected := by
  let S := SSet.loopFibrationSequence K v
  let : Subsingleton (SSet.KanComplex.π 0 S.E S.e) :=
    SSet.subsingleton_pi_basedPath K v 0
  apply (SSet.isConnected_iff (X := S.E)).mpr
  exact ⟨(SSet.KanComplex.π₀EquivπZero S.e).subsingleton_congr.mpr inferInstance, ⟨S.e⟩⟩

/-- The SAME based-path projection has integral homology Isos, using its
actual contraction and the original terminal-map hypothesis on K. -/
private theorem existingLoop_projection_integral_isIso
    (K : SSet.{u}) [SSet.KanComplex K] (v : K _⦋0⦌)
    (h : ∀ n : ℕ, IsIso (SSet.homologyMap
      (SSet.stdSimplex.isTerminalObj₀.from K) integralCoefficients n)) (n : ℕ) :
    IsIso (SSet.homologyMap (SSet.loopFibrationSequence K v).p integralCoefficients n) := by
  let : SSet.KanComplex (Δ[0] : SSet.{u}) := standardPoint_kan
  let S : SSet.FibrationSequence.{u} := SSet.loopFibrationSequence K v
  let : SSet.KanComplex S.B := (inferInstance : SSet.KanComplex K)
  let tK : K ⟶ (Δ[0] : SSet.{u}) := SSet.stdSimplex.isTerminalObj₀.from K
  let tE : S.E ⟶ (Δ[0] : SSet.{u}) := SSet.stdSimplex.isTerminalObj₀.from S.E
  let H : SSet.{u} ⥤ AddCommGrpCat.{u} := SSet.homologyFunctor integralCoefficients.{u} n
  have hK : IsIso (H.map tK) := by
    change IsIso (SSet.homologyMap (SSet.stdSimplex.isTerminalObj₀.from K)
      integralCoefficients.{u} n)
    exact h n
  let : IsIso (H.map tK) := hK
  have hw : SSet.KanComplex.W tE :=
    terminalWeak_of_actualContraction S.E S.e (SSet.basedPathContraction K v)
  let : IsIso (H.map tE) := by
    change IsIso (SSet.homologyMap tE integralCoefficients.{u} n)
    exact homologyMap_isIso_of_weak
      ((SSet.KanComplex.W_iff_realizationWeakEquivalence tE).mp hw) integralCoefficients.{u} n
  have hp : S.p ≫ tK = tE := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hs : H.map S.p ≫ H.map tK = H.map tE :=
    (H.map_comp S.p tK).symm.trans (H.congr_map hp)
  have hi : IsIso (H.map S.p ≫ H.map tK) := hs.symm ▸ (inferInstance : IsIso (H.map tE))
  exact (@isIso_comp_right_iff _ _ _ _ _ (H.map S.p) (H.map tK) hK).mp hi

/-- Exactness at degree zero derives connectedness of the SAME strict loop
fiber of the existing sequence. -/
private theorem existingLoop_connected (K : SSet.{u}) [SSet.KanComplex K]
    (v : K _⦋0⦌) (hπ : Subsingleton (SSet.KanComplex.π 1 K v)) :
    (SSet.loopSpace K v).IsConnected := by
  let S := SSet.loopFibrationSequence K v
  let : S.E.IsConnected := existingLoop_total_connected K v
  exact pointedStrictFiber_isConnected S hπ

/-- The full existing first-nonzero-row comparison derives positive integral
homology vanishing of the ACTUAL strict loop fiber. -/
private theorem existingLoop_positive_integral_isZero
    (K : SSet.{u}) [SSet.KanComplex K] [K.IsConnected] (v : K _⦋0⦌)
    (hπ : ∀ b : K _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 K b))
    (h : ∀ n : ℕ, IsIso (SSet.homologyMap
      (SSet.stdSimplex.isTerminalObj₀.from K) integralCoefficients n)) :
    ∀ n : ℕ, 1 ≤ n → IsZero ((SSet.loopSpace K v).homology integralCoefficients n) := by
  let S : SSet.FibrationSequence.{u} := SSet.loopFibrationSequence K v
  let : SSet.KanComplex S.B := (inferInstance : SSet.KanComplex K)
  let : S.B.IsConnected := (inferInstance : K.IsConnected)
  let : Fibration S.p := S.fibration_p
  let : S.E.IsConnected := existingLoop_total_connected K v
  exact actualKanFiber_positiveHomology_isZero S.p hπ v
    (existingLoop_projection_integral_isIso K v h)

/-- Degree zero is the actual augmentation of the SAME derived connected
loop fiber; all its terminal homology maps are then Isos. -/
private theorem existingLoop_terminal_integral_isIso
    (K : SSet.{u}) [SSet.KanComplex K] [K.IsConnected] (v : K _⦋0⦌)
    (hπ : ∀ b : K _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 K b))
    (h : ∀ n : ℕ, IsIso (SSet.homologyMap
      (SSet.stdSimplex.isTerminalObj₀.from K) integralCoefficients n)) (n : ℕ) :
    IsIso (SSet.homologyMap (SSet.stdSimplex.isTerminalObj₀.from (SSet.loopSpace K v))
      integralCoefficients n) := by
  let F := SSet.loopSpace K v
  let : F.IsConnected := existingLoop_connected K v (hπ v)
  cases n with
  | zero =>
      let : (Δ[0] : SSet.{u}).IsConnected := point_isConnected
      let t := SSet.stdSimplex.isTerminalObj₀.from F
      let f := SSet.homologyMap t integralCoefficients.{u} 0
      let e := (Δ[0] : SSet.{u}).homology₀ε integralCoefficients.{u}
      have he : f ≫ e = F.homology₀ε integralCoefficients.{u} :=
        SSet.homologyMap_comp_homology₀ε t integralCoefficients.{u}
      let : IsIso (f ≫ e) :=
        he.symm ▸ (inferInstance : IsIso (F.homology₀ε integralCoefficients.{u}))
      exact (isIso_comp_right_iff f e).mp inferInstance
  | succ n =>
      exact (existingLoop_positive_integral_isZero K v hπ h (n + 1) (by omega)).isIso
        (SSet.isZero_homology_of_hasDimensionLT (Δ[0] : SSet.{u})
          integralCoefficients.{u} (n + 1) 1 (by omega)) _

/-- H1=0 kills the actual commuting loop pi-one group, then original
basepoint transport gives the result at every loop vertex. -/
private theorem existingLoop_piOne_subsingleton_all
    (K : SSet.{u}) [SSet.KanComplex K] [K.IsConnected] (v : K _⦋0⦌)
    (hπ : ∀ b : K _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 K b))
    (h : ∀ n : ℕ, IsIso (SSet.homologyMap
      (SSet.stdSimplex.isTerminalObj₀.from K) integralCoefficients n)) :
    ∀ w : (SSet.loopSpace K v) _⦋0⦌,
      Subsingleton (SSet.KanComplex.π 1 (SSet.loopSpace K v) w) := by
  let F := SSet.loopSpace K v
  let z := SSet.LoopShiftOriginalGeometry.originalLoopPoint K v
  let : F.IsConnected := existingLoop_connected K v (hπ v)
  have h1 : Subsingleton (SSet.KanComplex.π 1 F z) :=
    nativePiOne_subsingleton_of_comm_and_H1_zero F z
      (actualLoop_piOne_mul_comm K v)
      (existingLoop_positive_integral_isZero K v hπ h 1 (by omega))
  exact nativePiOne_subsingleton_all_vertices F z h1

/-- Induction uses only actual Kan loop fibers, their derived homology, first
Hurewicz and the EXISTING multiplicative connecting shifts. -/
private theorem simplyConnected_integralAcyclic_positive_pi (n : ℕ) :
    ∀ (K : SSet.{u}) [SSet.KanComplex K] [K.IsConnected],
      (∀ b : K _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 K b)) →
      (∀ k : ℕ, IsIso (SSet.homologyMap
        (SSet.stdSimplex.isTerminalObj₀.from K) integralCoefficients k)) →
      ∀ v : K _⦋0⦌, Subsingleton (SSet.KanComplex.π (n + 1) K v) := by
  induction n with
  | zero =>
      intro K hKan hConn hπ h v
      exact hπ v
  | succ n ih =>
      intro K hKan hConn hπ h v
      let F : SSet.{u} := SSet.loopSpace K v
      let z : F _⦋0⦌ := SSet.LoopShiftOriginalGeometry.originalLoopPoint K v
      let : SSet.KanComplex F := SSet.loopSpace_kanComplex K v
      let : F.IsConnected := existingLoop_connected K v (hπ v)
      let : Subsingleton (SSet.KanComplex.π (n + 1) F z) :=
        ih F (existingLoop_piOne_subsingleton_all K v hπ h)
          (existingLoop_terminal_integral_isIso K v hπ h) z
      let e : SSet.KanComplex.π (n + 2) K v ≃* SSet.KanComplex.π (n + 1) F z :=
        SSet.loopConnectingMulEquiv n K v
      exact e.toEquiv.subsingleton_congr.mpr inferInstance

private theorem standardPoint_pi_subsingleton (n : ℕ)
    (z : (Δ[0] : SSet.{u}) _⦋0⦌) :
    Subsingleton (SSet.KanComplex.π n (Δ[0] : SSet.{u}) z) := by
  let : SSet.KanComplex (Δ[0] : SSet.{u}) := standardPoint_kan
  constructor
  intro a b
  obtain ⟨p, rfl⟩ := SSet.KanComplex.π.mk_surjective a
  obtain ⟨q, rfl⟩ := SSet.KanComplex.π.mk_surjective b
  have hpq : p = q := SSet.RelativeMorphism.ext (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
  exact congrArg SSet.KanComplex.π.mk hpq

/-- The SAME actual terminal map is weak: its component map and every
positive pointed homotopy map are derived bijections. -/
private theorem simplyConnected_integralAcyclic_terminal_weak
    (K : SSet.{u}) [SSet.KanComplex K] [K.IsConnected]
    (hπ : ∀ b : K _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 K b))
    (h : ∀ n : ℕ, IsIso (SSet.homologyMap
      (SSet.stdSimplex.isTerminalObj₀.from K) integralCoefficients n)) :
    SSet.KanComplex.W (SSet.stdSimplex.isTerminalObj₀.from K) := by
  let : SSet.KanComplex (Δ[0] : SSet.{u}) := standardPoint_kan
  let : (Δ[0] : SSet.{u}).IsConnected := point_isConnected
  let t := SSet.stdSimplex.isTerminalObj₀.from K
  rw [SSet.KanComplex.W_iff]
  constructor
  · constructor
    · intro a b hab
      exact Subsingleton.elim _ _
    · intro q
      let v : K _⦋0⦌ := Classical.arbitrary _
      exact ⟨SSet.π₀.mk v, Subsingleton.elim _ _⟩
  · intro n v
    let : Subsingleton (SSet.KanComplex.π (n + 1) K v) :=
      simplyConnected_integralAcyclic_positive_pi n K hπ h v
    let : Subsingleton (SSet.KanComplex.π (n + 1) (Δ[0] : SSet.{u}) (t.app _ v)) :=
      standardPoint_pi_subsingleton (n + 1) (t.app _ v)
    constructor
    · intro a b hab
      exact Subsingleton.elim _ _
    · intro q
      exact ⟨1, Subsingleton.elim _ _⟩


/-- The derived weak map is the SAME original realization point projection. -/
private theorem simplyConnected_integralAcyclic_terminal_realizationWeak
    (K : SSet.{u}) [SSet.KanComplex K] [K.IsConnected]
    (hπ : ∀ b : K _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 K b))
    (h : ∀ n : ℕ, IsIso (SSet.homologyMap
      (SSet.stdSimplex.isTerminalObj₀.from K) integralCoefficients n)) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from K) := by
  let : SSet.KanComplex (Δ[0] : SSet.{u}) := standardPoint_kan
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mp
    (simplyConnected_integralAcyclic_terminal_weak K hπ h)

end ActualKanFibrationHomologyCoefficients

end


noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra AlgebraicTopology
open scoped Simplicial SSet.modelCategoryQuillen

universe u v w

namespace ActualKanFibrationHomologyCoefficients

local instance (I : Type u) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance (I : Type u) : HasColimitsOfShape (Discrete I) (ModuleCat.{u} ℤ) :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

local instance : HasCoproducts.{u} (ModuleCat.{u} ℤ) :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
      AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
    ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

/-- The stock H₀ naturality square detects every actual component. The proof
uses its coproduct generators, so it applies without connectedness assumptions. -/
private theorem integral_homologyZero_isIso_mapπZero_bijective
    {X Y : SSet.{u}} (f : X ⟶ Y)
    [IsIso (SSet.homologyMap f integralCoefficients 0)] :
    Function.Bijective (SSet.mapπ₀ f) := by
  classical
  let R : AddCommGrpCat.{u} := integralCoefficients.{u}
  let p := SSet.mapπ₀ f
  let k : (∐ fun _ : SSet.π₀ X => R) ⟶ (∐ fun _ : SSet.π₀ Y => R) :=
    (sigmaConst.obj R).map (SSet.π₀Functor.map f)
  have hnat : SSet.homologyMap f R 0 ≫ (Y.homology₀Iso R).hom =
      (X.homology₀Iso R).hom ≫ k :=
    SSet.homologyMap_comp_homology₀Iso_hom f R
  have hk : IsIso k := by
    have hi : IsIso ((X.homology₀Iso R).hom ≫ k) :=
      hnat ▸ (inferInstance : IsIso
        (SSet.homologyMap f R 0 ≫ (Y.homology₀Iso R).hom))
    exact (isIso_comp_left_iff (X.homology₀Iso R).hom k).mp hi
  let : IsIso k := hk
  have hkMap : k = Sigma.map' p (fun _ => 𝟙 R) := rfl
  have hι (a : SSet.π₀ X) :
      Sigma.ι (fun _ : SSet.π₀ X => R) a ≫ k =
        Sigma.ι (fun _ : SSet.π₀ Y => R) (p a) := by
    rw [hkMap]
    simp only [Sigma.ι_comp_map', Category.id_comp]
  constructor
  · intro a b hab
    have hj : Sigma.ι (fun _ : SSet.π₀ X => R) a =
        Sigma.ι (fun _ : SSet.π₀ X => R) b :=
      (cancel_mono k).mp ((hι a).trans ((congrArg
        (Sigma.ι (fun _ : SSet.π₀ Y => R)) hab).trans (hι b).symm))
    by_contra hne
    let d : (∐ fun _ : SSet.π₀ X => R) ⟶ R :=
      Sigma.desc (fun c => if c = a then 𝟙 R else 0)
    have hz : (𝟙 R) = 0 := by
      calc
        (𝟙 R) = Sigma.ι (fun _ : SSet.π₀ X => R) a ≫ d := by
          simp [d]
        _ = Sigma.ι (fun _ : SSet.π₀ X => R) b ≫ d := congrArg (fun t => t ≫ d) hj
        _ = 0 := by simp only [d, Sigma.ι_comp_desc, ite_eq_right (Ne.symm hne)]
    exact integral_identity_ne_zero hz
  · intro b
    by_contra hb
    have hnone : ∀ a : SSet.π₀ X, p a ≠ b := by
      intro a ha
      exact hb ⟨a, ha⟩
    let d : (∐ fun _ : SSet.π₀ Y => R) ⟶ R :=
      Sigma.desc (fun c => if c = b then 𝟙 R else 0)
    have hkd : k ≫ d = 0 := by
      apply Sigma.hom_ext
      intro a
      rw [← Category.assoc, hι]
      simp only [d, Sigma.ι_comp_desc, ite_eq_right (hnone a), comp_zero]
    have hd : d = 0 := (cancel_epi k).mp (hkd.trans
      (show k ≫ (0 : (∐ fun _ : SSet.π₀ Y => R) ⟶ R) = 0 by simp).symm)
    have hz : (𝟙 R) = 0 := by
      calc
        (𝟙 R) = Sigma.ι (fun _ : SSet.π₀ Y => R) b ≫ d := by
          simp [d]
        _ = 0 := by rw [hd, comp_zero]
    exact integral_identity_ne_zero hz

/-- Injectivity of the original π₁ projection makes its actual δ₂ surjective.
The existing multiplicative law and π₂ commutativity then make fiber π₁ commute. -/
private theorem strictFiber_piOne_mul_comm_of_piMap_injective
    (S : SSet.FibrationSequence.{u})
    (hp : Function.Injective (SSet.KanComplex.π.map S.p S.hb 1))
    (a b : SSet.KanComplex.π 1 S.fiber S.fiberPoint) : a * b = b * a := by
  have hs : Function.Surjective (S.connectingMap 1) := by
    intro q
    apply S.exactness_at_fiber q
    apply hp
    exact (S.map_p_comp_fiberIncl_eq_one q).trans
      (SSet.KanComplex.π.map_one S.p S.hb 1).symm
  obtain ⟨r, hr⟩ := hs a
  obtain ⟨s, hsb⟩ := hs b
  rw [← hr, ← hsb, ← S.connectingMap_mul 0, ← S.connectingMap_mul 0]
  exact congrArg (S.connectingMap 1) (SSet.KanComplex.π.mul_comm_two S.b r s)

/-- H₀ fixes connectedness of this SAME fiber; H₁ and its now-proved
commutativity kill its fundamental group at every vertex. -/
private theorem strictFiber_piOne_subsingleton_of_integral_terminal
    (S : SSet.FibrationSequence.{u})
    (hp : Function.Injective (SSet.KanComplex.π.map S.p S.hb 1))
    (hF : ∀ n : ℕ, IsIso (SSet.homologyMap
      (SSet.stdSimplex.isTerminalObj₀.from S.fiber) integralCoefficients n)) :
    ∀ z : S.fiber _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 S.fiber z) := by
  let : (Δ[0] : SSet.{u}).IsConnected := point_isConnected
  let : IsIso (SSet.homologyMap (SSet.stdSimplex.isTerminalObj₀.from S.fiber)
    integralCoefficients.{u} 0) := hF 0
  let : S.fiber.IsConnected := isConnected_of_integral_homology_zero_isIso
    (SSet.stdSimplex.isTerminalObj₀.from S.fiber)
  let : IsIso (SSet.homologyMap (SSet.stdSimplex.isTerminalObj₀.from S.fiber)
    integralCoefficients.{u} 1) := hF 1
  have hz : IsZero (S.fiber.homology integralCoefficients.{u} 1) :=
    IsZero.of_iso
      (SSet.isZero_homology_of_hasDimensionLT (Δ[0] : SSet.{u}) integralCoefficients.{u} 1 1 (by omega))
      (asIso (SSet.homologyMap (SSet.stdSimplex.isTerminalObj₀.from S.fiber)
        integralCoefficients.{u} 1))
  have h1 : Subsingleton (SSet.KanComplex.π 1 S.fiber S.fiberPoint) :=
    nativePiOne_subsingleton_of_comm_and_H1_zero S.fiber S.fiberPoint
      (strictFiber_piOne_mul_comm_of_piMap_injective S hp) hz
  exact nativePiOne_subsingleton_all_vertices S.fiber S.fiberPoint h1

/-- The native constant class equals the unit of the same canonical group.
The public constant-simplex multiplication and group cancellation prove the
identity without unfolding or replacing the group structure. -/
private theorem native_piGroup_unit_eq
    (K : SSet.{u}) [SSet.KanComplex K] (x : K _⦋0⦌) (n : ℕ) :
    @One.one (SSet.KanComplex.π (n + 1) K x)
      (SSet.KanComplex.π.instOne (n := n + 1) (X := K) (x := x)) =
    @One.one (SSet.KanComplex.π (n + 1) K x)
      (SSet.KanComplex.π.group (n := n) (X := K) (x := x)).toMulOneClass.toMulOne.toOne := by
  let c : SSet.KanComplex.π (n + 1) K x :=
    SSet.KanComplex.π.mk (SSet.RelativeMorphism.const : K.PtSimplex (n + 1) x)
  have hNative : @One.one (SSet.KanComplex.π (n + 1) K x)
      (SSet.KanComplex.π.instOne (n := n + 1) (X := K) (x := x)) = c := rfl
  have hcc : c * c = c :=
    (SSet.PtSimplex.MulStruct.oneMul
      (SSet.RelativeMorphism.const : K.PtSimplex (n + 1) x) (Fin.last n)).mul_eq
  have hGroup : c = @One.one (SSet.KanComplex.π (n + 1) K x)
      (SSet.KanComplex.π.group (n := n) (X := K) (x := x)).toMulOneClass.toMulOne.toOne :=
    mul_right_cancel (hcc.trans (one_mul c).symm)
  exact hNative.trans hGroup

/-- Exactness and the accepted actual loop induction derive all positive
homotopy bijections of the original projection. -/
private theorem strictFibration_positive_piMap_bijective
    (S : SSet.FibrationSequence.{u})
    (hp : Function.Injective (SSet.KanComplex.π.map S.p S.hb 1))
    (hF : ∀ n : ℕ, IsIso (SSet.homologyMap
      (SSet.stdSimplex.isTerminalObj₀.from S.fiber) integralCoefficients n)) (n : ℕ) :
    Function.Bijective (SSet.KanComplex.π.map S.p S.hb (n + 1)) := by
  let : (Δ[0] : SSet.{u}).IsConnected := point_isConnected
  let : IsIso (SSet.homologyMap (SSet.stdSimplex.isTerminalObj₀.from S.fiber)
    integralCoefficients.{u} 0) := hF 0
  let : S.fiber.IsConnected := isConnected_of_integral_homology_zero_isIso
    (SSet.stdSimplex.isTerminalObj₀.from S.fiber)
  have hπ := strictFiber_piOne_subsingleton_of_integral_terminal S hp hF
  let : Subsingleton (SSet.KanComplex.π (n + 1) S.fiber S.fiberPoint) :=
    simplyConnected_integralAcyclic_positive_pi n S.fiber hπ hF S.fiberPoint
  have hzero : Subsingleton (SSet.KanComplex.π n S.fiber S.fiberPoint) := by
    cases n with
    | zero => exact (SSet.KanComplex.π₀EquivπZero S.fiberPoint).subsingleton_congr.mp inferInstance
    | succ n => exact simplyConnected_integralAcyclic_positive_pi n S.fiber hπ hF S.fiberPoint
  constructor
  · intro a b hab
    let P : SSet.KanComplex.π (n + 1) S.E S.e →*
        SSet.KanComplex.π (n + 1) S.B S.b :=
      MonoidHom.ofClass (SSet.KanComplex.π.mapHom S.p S.hb n)
    have hP (z : SSet.KanComplex.π (n + 1) S.E S.e) :
        P z = SSet.KanComplex.π.map S.p S.hb (n + 1) z := by
      change SSet.KanComplex.π.mapHom S.p S.hb n z = _
      exact SSet.KanComplex.π.mapHom_apply S.p S.hb n z
    have habP : P a = P b := (hP a).trans (hab.trans (hP b).symm)
    have hE := native_piGroup_unit_eq S.E S.e n
    have hB := native_piGroup_unit_eq S.B S.b n
    have hqGroup : P (a⁻¹ * b) = @One.one (SSet.KanComplex.π (n + 1) S.B S.b)
        (SSet.KanComplex.π.group (n := n) (X := S.B) (x := S.b)).toMulOneClass.toMulOne.toOne := by
      have hm : P (a⁻¹ * b) * P b = P b := by
        rw [P.map_mul, P.map_inv, habP, mul_assoc]
        exact inv_mul_cancel_left (P b) (P b)
      exact mul_right_cancel (hm.trans (one_mul (P b)).symm)
    have hq : SSet.KanComplex.π.map S.p S.hb (n + 1) (a⁻¹ * b) =
        @One.one (SSet.KanComplex.π (n + 1) S.B S.b)
          (SSet.KanComplex.π.instOne (n := n + 1) (X := S.B) (x := S.b)) :=
      (hP (a⁻¹ * b)).symm.trans (hqGroup.trans hB.symm)
    obtain ⟨r, hr⟩ := S.exactness_at_E (a⁻¹ * b) hq
    have hr1 : r = @One.one (SSet.KanComplex.π (n + 1) S.fiber S.fiberPoint)
        (SSet.KanComplex.π.instOne (n := n + 1) (X := S.fiber) (x := S.fiberPoint)) :=
      Subsingleton.elim _ _
    have he : a⁻¹ * b = @One.one (SSet.KanComplex.π (n + 1) S.E S.e)
        (SSet.KanComplex.π.instOne (n := n + 1) (X := S.E) (x := S.e)) := hr.symm.trans
      ((congrArg (SSet.KanComplex.π.map S.fiberIncl rfl (n + 1)) hr1).trans
        (SSet.KanComplex.π.map_one S.fiberIncl rfl (n + 1)))
    exact inv_mul_eq_one.mp (he.trans hE)
  · intro q
    exact S.exactness_at_B q (@Subsingleton.elim _ hzero _ _)

/-- Public native/ordinary group comparisons calibrate the ACTUAL map at every
singular vertex. Their opposite-multiplication convention is retained. -/
private theorem original_singular_piOne_bijective
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hπ : ∀ x : X, Function.Bijective
      (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x) :
        FundamentalGroup X x → FundamentalGroup Y (f x))) :
    ∀ a : (TopCat.toSSet.obj X) _⦋0⦌,
      Function.Bijective (SSet.KanComplex.π.map (TopCat.toSSet.map f) rfl 1 (x := a)) := by
  let : SSet.KanComplex (TopCat.toSSet.obj X) := TopCat.toSSet_obj_kanComplex X
  let : SSet.KanComplex (TopCat.toSSet.obj Y) := TopCat.toSSet_obj_kanComplex Y
  intro a
  obtain ⟨x, rfl⟩ := (TopCat.toSSetObj₀Equiv (X := X)).symm.surjective a
  let q := TopCat.toSSet.map f
  let a := TopCat.toSSetObj₀Equiv.symm x
  let b := q.app (Opposite.op ⦋0⦌) a
  let c := TopCat.singularMappedVertexIso f x
  let nx := SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd a
  let ny := SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd b
  let ox := TopCat.singularFundamentalGroupoidEndMulEquiv X x
  let oy := TopCat.singularFundamentalGroupoidEndMulEquiv Y (f x)
  let ec : End ((SSet.mapFundamentalGroupoid q).obj (SSet.FundamentalGroupoid.mk a)) ≃
      End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm (f x))) :=
    End.homEquiv.trans ((Iso.homCongr c c).trans End.homEquiv.symm)
  let ex := nx.toEquiv.trans ox.toEquiv
  let ey := ny.toEquiv.trans (ec.trans oy.toEquiv)
  have hc (z : End (SSet.FundamentalGroupoid.mk a)) :
      ec ((SSet.mapFundamentalGroupoid q).mapEnd (SSet.FundamentalGroupoid.mk a) z) =
        SSet.basedFundamentalGroupHom q a
          (TopCat.toSSetObj₀Equiv.symm (f x)) c z := by
    rw [SSet.basedFundamentalGroupHom_apply]
    rfl
  have hn (z : SSet.KanComplex.π 1 (TopCat.toSSet.obj X) a) :
      ey (SSet.KanComplex.π.map q rfl 1 z) =
        FundamentalGroup.mapOfEq f.hom rfl (ex z) := by
    have hn := SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_naturality q a z
    have ho : oy.symm (FundamentalGroup.mapOfEq f.hom rfl (ox (nx z))) =
        SSet.basedFundamentalGroupHom q a
          (TopCat.toSSetObj₀Equiv.symm (f x)) c (ox.symm (ox (nx z))) :=
      TopCat.singularEnd_inverse_naturality f x (ox (nx z))
    rw [ox.symm_apply_apply] at ho
    have hx : ex z = ox (nx z) := rfl
    calc
      ey (SSet.KanComplex.π.map q rfl 1 z) =
          oy (ec (ny (SSet.KanComplex.π.map q rfl 1 z))) := rfl
      _ = oy (ec ((SSet.mapFundamentalGroupoid q).mapEnd
          (SSet.FundamentalGroupoid.mk a) (nx z))) := congrArg (fun t => oy (ec t)) hn
      _ = oy (SSet.basedFundamentalGroupHom q a
          (TopCat.toSSetObj₀Equiv.symm (f x)) c (nx z)) := congrArg oy (hc (nx z))
      _ = FundamentalGroup.mapOfEq f.hom rfl (ex z) := by
        apply oy.symm.injective
        rw [oy.symm_apply_apply]
        exact ho.symm.trans
          (congrArg (fun t => oy.symm (FundamentalGroup.mapOfEq f.hom rfl t)) hx.symm)
  constructor
  · intro z z' hz
    apply ex.injective
    apply (hπ x).1
    exact (hn z).symm.trans ((congrArg ey hz).trans (hn z'))
  · intro z
    obtain ⟨t, ht⟩ := (hπ x).2 (ey z)
    refine ⟨ex.symm t, ey.injective ?_⟩
    rw [hn, ex.apply_symm_apply, ht]

/-- This computed comparison uses the original ending-path coordinates,
not a supplied CW model of the fiber. -/
private noncomputable def originalDirectStrictEndingFiberComparison
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y) :
    SSet.toTop.obj (SSet.Subcomplex.fiber
      (SSet.mappingPathTarget (TopCat.toSSet.map f))
      (TopCat.toSSetObj₀Equiv.symm y) : SSet.{u}) ⟶ TopCat.homotopyFiber f y :=
  SSet.toTop.map
      (SSet.pathHomotopyFiberStrictMappingPathIso (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm y)).inv ≫
    SSet.originalSingularPathFiberRealizationComparison f y

private theorem originalDirectStrictEndingFiberComparison_weak
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y) :
    TopCat.weakHomotopyEquivalences (originalDirectStrictEndingFiberComparison f y) := by
  have hi : TopCat.weakHomotopyEquivalences (SSet.toTop.map
      (SSet.pathHomotopyFiberStrictMappingPathIso (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm y)).inv) :=
    TopCat.weakHomotopyEquivalences.of_isIso _
  exact TopCat.weakHomotopyEquivalences.comp_mem _ _ hi
    (SSet.originalSingularPathFiberRealizationComparison_mem_weakHomotopyEquivalences f y)

/-- The SAME literal point projection is invertible when its connectedness
and positive groups have been derived; no Kan/CW/model premise is needed here. -/
private theorem integral_terminal_isIso_of_derived_groups
    (K : SSet.{u}) [K.IsConnected]
    (h : ∀ n : ℕ, 1 ≤ n → IsZero (K.homology integralCoefficients n)) (n : ℕ) :
    IsIso (SSet.homologyMap (SSet.stdSimplex.isTerminalObj₀.from K) integralCoefficients n) := by
  cases n with
  | zero =>
    let : (Δ[0] : SSet.{u}).IsConnected := point_isConnected
    let t := SSet.stdSimplex.isTerminalObj₀.from K
    let m := SSet.homologyMap t integralCoefficients.{u} 0
    let e := (Δ[0] : SSet.{u}).homology₀ε integralCoefficients.{u}
    have he : m ≫ e = K.homology₀ε integralCoefficients.{u} :=
      SSet.homologyMap_comp_homology₀ε t integralCoefficients.{u}
    have hi : IsIso (m ≫ e) :=
      he.symm ▸ (inferInstance : IsIso (K.homology₀ε integralCoefficients.{u}))
    exact (isIso_comp_right_iff m e).mp hi
  | succ n =>
    exact (h (n + 1) (by omega)).isIso
      (SSet.isZero_homology_of_hasDimensionLT (Δ[0] : SSet.{u})
        integralCoefficients.{u} (n + 1) 1 (by omega)) _

/-- Actual comparison and unit-map naturality transfer the original ending
fiber acyclicity to its SAME strict mapping-path coordinate. -/
private theorem originalDirectStrictFiber_terminal_integral_isIso
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f) (y : Y) :
    ∀ n : ℕ, IsIso (SSet.homologyMap
      (SSet.stdSimplex.isTerminalObj₀.from (SSet.Subcomplex.fiber
        (SSet.mappingPathTarget (TopCat.toSSet.map f))
        (TopCat.toSSetObj₀Equiv.symm y) : SSet.{u})) integralCoefficients n) := by
  let F : SSet.{u} := SSet.Subcomplex.fiber
    (SSet.mappingPathTarget (TopCat.toSSet.map f)) (TopCat.toSSetObj₀Equiv.symm y)
  let J := TopCat.homotopyFiber f y
  let c : SSet.toTop.obj F ⟶ J := originalDirectStrictEndingFiberComparison f y
  let i : F ⟶ TopCat.toSSet.obj (SSet.toTop.obj F) := sSetTopAdj.unit.app F
  have hc : TopCat.weakHomotopyEquivalences c :=
    originalDirectStrictEndingFiberComparison_weak f y
  have ht := originalAcyclicFiberCriterion f hf y
  let : IsIso ((TopCat.toSSet.obj J).homology₀ε integralCoefficients.{u}) :=
    originalEndingFiber_augmentation_isIso_of_terminal f y (ht 0)
  let : IsIso (SSet.homologyMap (TopCat.toSSet.map c) integralCoefficients.{u} 0) :=
    hc.isIso_singularHomologyFunctor_map singularIntegralCoefficients.{u} 0
  let : IsIso ((TopCat.toSSet.obj (SSet.toTop.obj F)).homology₀ε integralCoefficients.{u}) := by
    rw [← SSet.homologyMap_comp_homology₀ε (TopCat.toSSet.map c) integralCoefficients.{u}]
    infer_instance
  let : IsIso (SSet.homologyMap i integralCoefficients.{u} 0) :=
    homologyMap_isIso_of_weak (SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences F)
      integralCoefficients.{u} 0
  let : IsIso (F.homology₀ε integralCoefficients.{u}) := by
    rw [← SSet.homologyMap_comp_homology₀ε i integralCoefficients.{u}]
    infer_instance
  let : F.IsConnected := isConnected_of_integral_augmentation_isIso F
  apply integral_terminal_isIso_of_derived_groups F
  intro n hn
  let : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map (terminal.from J)) := ht n
  have hJ : IsZero (AlgebraicTopology.singularIntegralHomology n J) :=
    IsZero.of_iso (singularTerminal_positiveHomology_isZero n hn)
      (asIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map (terminal.from J)))
  let mC := (AlgebraicTopology.singularIntegralHomologyFunctor n).map c
  let : IsIso mC := hc.isIso_singularHomologyFunctor_map singularIntegralCoefficients.{u} n
  have hR : IsZero (AlgebraicTopology.singularIntegralHomology n (SSet.toTop.obj F)) :=
    IsZero.of_iso hJ (asIso mC)
  let eI : F.homology integralCoefficients.{u} n ≅
      (TopCat.toSSet.obj (SSet.toTop.obj F)).homology integralCoefficients.{u} n := by
    letI : IsIso (SSet.homologyMap (sSetTopAdj.unit.app F) integralCoefficients.{u} n) :=
      homologyMap_isIso_of_weak
        (SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences F) integralCoefficients.{u} n
    exact asIso (SSet.homologyMap (sSetTopAdj.unit.app F) integralCoefficients.{u} n)
  exact IsZero.of_iso hR eI

/-- Every singular vertex is the actual vertex of an original point, so the
previous acyclicity statement covers ALL strict fibers, not a selected component. -/
private theorem originalDirectStrictFiber_terminal_integral_isIso_all
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f) :
    ∀ b : (TopCat.toSSet.obj Y) _⦋0⦌, ∀ n : ℕ,
      IsIso (SSet.homologyMap (SSet.stdSimplex.isTerminalObj₀.from
        (SSet.Subcomplex.fiber (SSet.mappingPathTarget (TopCat.toSSet.map f)) b : SSet.{u}))
        integralCoefficients n) := by
  intro b
  obtain ⟨y, rfl⟩ := (TopCat.toSSetObj₀Equiv (X := Y)).symm.surjective b
  exact originalDirectStrictFiber_terminal_integral_isIso f hf y

/-- All local-coefficient equivalences and the ACTUAL π₁ maps imply weakness
of the SAME original map on ALL components. CW type is not an input here. -/
private theorem original_allLocalCoefficient_piOneIso_mem_weakHomotopyEquivalences
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (hπ : ∀ x : X, Function.Bijective
      (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x) :
        FundamentalGroup X x → FundamentalGroup Y (f x))) :
    TopCat.weakHomotopyEquivalences f := by
  let A := TopCat.toSSet.obj X
  let B := TopCat.toSSet.obj Y
  let q : A ⟶ B := TopCat.toSSet.map f
  let : SSet.KanComplex A := TopCat.toSSet_obj_kanComplex X
  let : SSet.KanComplex B := TopCat.toSSet_obj_kanComplex Y
  let : IsIso (SSet.homologyMap q integralCoefficients.{u} 0) :=
    by
      change IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 0).map f)
      exact hf.isIntegral 0
  have hq₁ := original_singular_piOne_bijective f hπ
  apply (TopCat.mem_weakHomotopyEquivalences_iff f).mpr
  apply (SSet.KanComplex.W_iff q).mpr
  refine ⟨integral_homologyZero_isIso_mapπZero_bijective q, ?_⟩
  intro n a
  let M : SSet.{u} := SSet.mappingPathSpace (f := q)
  let s : A ⟶ M := SSet.mappingPathSection q
  let p : M ⟶ B := SSet.mappingPathTarget q
  have hs : SSet.KanComplex.W s := SSet.KanComplex.W.of_mappingPathSection q
  let : SSet.KanComplex M := hs.kanComplex_target
  let : Fibration p := inferInstance
  let e : M _⦋0⦌ := s.app (Opposite.op ⦋0⦌) a
  let b : B _⦋0⦌ := q.app (Opposite.op ⦋0⦌) a
  have hb : p.app (Opposite.op ⦋0⦌) e = b :=
    congrArg (fun t : A ⟶ B => t.app (Opposite.op ⦋0⦌) a)
      (SSet.mappingPathSection_comp_target q)
  let S : SSet.FibrationSequence.{u} :=
    { E := M
      B := B
      p := p
      fibration_p := inferInstance
      fibrant_B := inferInstance
      e := e
      b := b
      hb := hb }
  have hcomp (k : ℕ) (z : SSet.KanComplex.π k A a) :
      SSet.KanComplex.π.map p hb k (SSet.KanComplex.π.map s rfl k z) =
        SSet.KanComplex.π.map q rfl k z := by
    have hsq : (s ≫ p).app (Opposite.op ⦋0⦌) a = b := hb
    exact (SSet.KanComplex.π.map_comp_apply s p rfl hb hsq z).symm.trans
      (congrFun (SSet.KanComplex.π.map_congr
        (SSet.mappingPathSection_comp_target q) hsq rfl k) z)
  have hp₁ : Function.Injective (SSet.KanComplex.π.map S.p S.hb 1) := by
    change Function.Injective (SSet.KanComplex.π.map p hb 1)
    intro z z' hz
    obtain ⟨t, ht⟩ := (hs.bijective_piMap 1 a).2 z
    obtain ⟨t', ht'⟩ := (hs.bijective_piMap 1 a).2 z'
    have hq : SSet.KanComplex.π.map q rfl 1 t =
        SSet.KanComplex.π.map q rfl 1 t' := by
      calc
        SSet.KanComplex.π.map q rfl 1 t =
            SSet.KanComplex.π.map p hb 1 (SSet.KanComplex.π.map s rfl 1 t) :=
          (hcomp 1 t).symm
        _ = SSet.KanComplex.π.map p hb 1 z := congrArg (SSet.KanComplex.π.map p hb 1) ht
        _ = SSet.KanComplex.π.map p hb 1 z' := hz
        _ = SSet.KanComplex.π.map p hb 1 (SSet.KanComplex.π.map s rfl 1 t') :=
          congrArg (SSet.KanComplex.π.map p hb 1) ht'.symm
        _ = SSet.KanComplex.π.map q rfl 1 t' := hcomp 1 t'
    have htt := (hq₁ a).1 hq
    exact ht.symm.trans ((congrArg (SSet.KanComplex.π.map s rfl 1) htt).trans ht')
  have hF : ∀ k : ℕ, IsIso (SSet.homologyMap
      (SSet.stdSimplex.isTerminalObj₀.from S.fiber) integralCoefficients k) :=
    originalDirectStrictFiber_terminal_integral_isIso_all f hf b
  have hp := strictFibration_positive_piMap_bijective S hp₁ hF n
  have hbij : Function.Bijective
      (SSet.KanComplex.π.map p hb (n + 1) ∘ SSet.KanComplex.π.map s rfl (n + 1)) :=
    hp.comp (hs.bijective_piMap (n + 1) a)
  have heq : SSet.KanComplex.π.map q rfl (n + 1) =
      SSet.KanComplex.π.map p hb (n + 1) ∘ SSet.KanComplex.π.map s rfl (n + 1) := by
    funext z
    exact (hcomp (n + 1) z).symm
  rw [heq]
  exact hbij

/-- Genuine independently sized BASED CW models upgrade the DERIVED weak
original map to an actual inverse and BOTH point-relative inverse families.
This companion does not identify unbased CW type with stronger based data. -/
private theorem original_basedCWType_allLocalCoefficient_piOneIso_inverse
    (X Y : TopCat.{u}) (CX : TopCat.{v}) (CY : TopCat.{w})
    [T2Space CX] [T2Space CY]
    [Topology.CWComplex (Set.univ : Set CX)] [Topology.CWComplex (Set.univ : Set CY)]
    (x : X) (y : Y) (cx : CX) (cy : CY)
    (jx : Topology.CWComplex.cell (Set.univ : Set CX) 0)
    (jy : Topology.CWComplex.cell (Set.univ : Set CY) 0)
    (hjx : Topology.CWComplex.map 0 jx ![] = cx)
    (hjy : Topology.CWComplex.map 0 jy ![] = cy)
    (rx : C(X, CX)) (sx : C(CX, X)) (ry : C(Y, CY)) (sy : C(CY, Y))
    (hrx : rx x = cx) (hsx : sx cx = x) (hry : ry y = cy) (hsy : sy cy = y)
    (LX : ContinuousMap.HomotopyRel (sx.comp rx) (ContinuousMap.id X) {x})
    (RX : ContinuousMap.HomotopyRel (rx.comp sx) (ContinuousMap.id CX) {cx})
    (LY : ContinuousMap.HomotopyRel (sy.comp ry) (ContinuousMap.id Y) {y})
    (RY : ContinuousMap.HomotopyRel (ry.comp sy) (ContinuousMap.id CY) {cy})
    (f : X ⟶ Y) (hxy : f x = y)
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (hπ : ∀ z : X, Function.Bijective
      (FundamentalGroup.mapOfEq f.hom (rfl : f.hom z = f z) :
        FundamentalGroup X z → FundamentalGroup Y (f z))) :
    ∃ g : Y ⟶ X, g y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (f ≫ g).hom (TopCat.Hom.hom (𝟙 X)) {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (g ≫ f).hom (TopCat.Hom.hom (𝟙 Y)) {y}) := by
  exact Topology.CWComplex.basedCWTypeWhiteheadIndependentModels
    X Y CX CY x y cx cy jx jy hjx hjy rx sx ry sy hrx hsx hry hsy LX RX LY RY f hxy
      (original_allLocalCoefficient_piOneIso_mem_weakHomotopyEquivalences f hf hπ)

/-- The unrestricted all-local-coefficient unbased CW-type companion: the genuine models have
independent universes; no point calibration, fiber model or inverse for `f`
is an input. The returned equivalence keeps the literal original forward map. -/
private theorem original_allLocalCoefficient_CWType_piOneIso_homotopyEquiv
    {X Y : TopCat.{u}}
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C X))
    (hCWY : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C Y))
    (f : X ⟶ Y) (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (hπ : ∀ x : X, Function.Bijective
      (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x) :
        FundamentalGroup X x → FundamentalGroup Y (f x))) :
    ∃ e : ContinuousMap.HomotopyEquiv X Y, e.toFun = f.hom := by
  obtain ⟨CX, hTX, hCX, ⟨ex⟩⟩ := hCWX
  obtain ⟨CY, hTY, hCY, ⟨ey⟩⟩ := hCWY
  let : T2Space CX := hTX
  let : T2Space CY := hTY
  let : Topology.CWComplex (Set.univ : Set CX) := hCX
  let : Topology.CWComplex (Set.univ : Set CY) := hCY
  exact Topology.CWComplex.unbasedCWTypeWhiteheadIndependentModels CX CY ex ey f
    (original_allLocalCoefficient_piOneIso_mem_weakHomotopyEquivalences f hf hπ)

/-- Both ordinary inverse homotopies concern the SAME original map and spaces,
not just the existence of an abstract homotopy type. -/
private theorem original_allLocalCoefficient_CWType_piOneIso_actual_inverse
    {X Y : TopCat.{u}}
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C X))
    (hCWY : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C Y))
    (f : X ⟶ Y) (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (hπ : ∀ x : X, Function.Bijective
      (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x) :
        FundamentalGroup X x → FundamentalGroup Y (f x))) :
    ∃ g : Y ⟶ X, Nonempty (TopCat.Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (TopCat.Homotopy (g ≫ f) (𝟙 Y)) := by
  obtain ⟨e, he⟩ := original_allLocalCoefficient_CWType_piOneIso_homotopyEquiv hCWX hCWY f hf hπ
  let g : Y ⟶ X := TopCat.ofHom e.invFun
  refine ⟨g, ?_, ?_⟩
  · have hg : (TopCat.Hom.hom g : C(Y, X)) = e.invFun := TopCat.hom_ofHom e.invFun
    have hfg : (TopCat.Hom.hom (f ≫ g) : C(X, X)) = e.invFun.comp e.toFun :=
      (TopCat.hom_comp f g).trans (congrArg₂ ContinuousMap.comp hg he.symm)
    let H : ContinuousMap.Homotopy (e.invFun.comp e.toFun) (ContinuousMap.id X) :=
      e.left_inv.some
    exact ⟨H.cast hfg.symm (TopCat.hom_id (X := X)).symm⟩
  · have hg : (TopCat.Hom.hom g : C(Y, X)) = e.invFun := TopCat.hom_ofHom e.invFun
    have hgf : (TopCat.Hom.hom (g ≫ f) : C(Y, Y)) = e.toFun.comp e.invFun :=
      (TopCat.hom_comp g f).trans (congrArg₂ ContinuousMap.comp he.symm hg)
    let H : ContinuousMap.Homotopy (e.toFun.comp e.invFun) (ContinuousMap.id Y) :=
      e.right_inv.some
    exact ⟨H.cast hgf.symm (TopCat.hom_id (X := Y)).symm⟩

/-- Canonical reduced acyclicity is used in the original nonempty-source,
connected-CW-target context. The verified canonical criterion supplies the
terminal-homology information internally; every original component and
basepoint is included in the actual weak-equivalence conclusion. -/
private theorem original_canonical_acyclic_piOneIso_mem_weakHomotopyEquivalences
    {X Y : TopCat.{u}} [Nonempty X] [ConnectedSpace Y]
    (hCWY : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C Y))
    (f : X ⟶ Y) (hA : ∀ y : Y, TopCat.IsAcyclicMapAt f y)
    (hπ : ∀ x : X, Function.Bijective
      (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x) :
        FundamentalGroup X x → FundamentalGroup Y (f x))) :
    TopCat.weakHomotopyEquivalences f := by
  have hf : TopCat.IsLocalCoefficientHomologyEquivalence f :=
    (TopCat.homotopyFiber_acyclic_iff_localCoefficientHomologyEquivalence hCWY f).mp hA
  exact original_allLocalCoefficient_piOneIso_mem_weakHomotopyEquivalences f hf hπ

/-- The original canonical-acyclic CW recognition theorem retains genuine
UNBASED independently sized models and returns a homotopy equivalence whose
literal forward map is the original f. No desired inverse, fiber model or
based calibration is supplied. -/
private theorem original_canonical_acyclic_CWType_piOneIso_homotopyEquiv
    {X Y : TopCat.{u}} [Nonempty X] [ConnectedSpace Y]
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C X))
    (hCWY : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C Y))
    (f : X ⟶ Y) (hA : ∀ y : Y, TopCat.IsAcyclicMapAt f y)
    (hπ : ∀ x : X, Function.Bijective
      (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x) :
        FundamentalGroup X x → FundamentalGroup Y (f x))) :
    ∃ e : ContinuousMap.HomotopyEquiv X Y, e.toFun = f.hom := by
  obtain ⟨CX, hTX, hCX, ⟨ex⟩⟩ := hCWX
  obtain ⟨CY, hTY, hCY, ⟨ey⟩⟩ := hCWY
  let : T2Space CX := hTX
  let : T2Space CY := hTY
  let : Topology.CWComplex (Set.univ : Set CX) := hCX
  let : Topology.CWComplex (Set.univ : Set CY) := hCY
  have hTarget : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C Y) :=
    ⟨CY, hTY, hCY, ⟨ey⟩⟩
  exact Topology.CWComplex.unbasedCWTypeWhiteheadIndependentModels CX CY ex ey f
    (original_canonical_acyclic_piOneIso_mem_weakHomotopyEquivalences hTarget f hA hπ)

/-- Both canonical-recognition inverse families concern the original f and
the original topologies. The CW qualifiers are genuinely unbased. -/
private theorem original_canonical_acyclic_CWType_piOneIso_actual_inverse
    {X Y : TopCat.{u}} [Nonempty X] [ConnectedSpace Y]
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C X))
    (hCWY : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C Y))
    (f : X ⟶ Y) (hA : ∀ y : Y, TopCat.IsAcyclicMapAt f y)
    (hπ : ∀ x : X, Function.Bijective
      (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x) :
        FundamentalGroup X x → FundamentalGroup Y (f x))) :
    ∃ g : Y ⟶ X, Nonempty (TopCat.Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (TopCat.Homotopy (g ≫ f) (𝟙 Y)) := by
  obtain ⟨e, he⟩ := original_canonical_acyclic_CWType_piOneIso_homotopyEquiv
    hCWX hCWY f hA hπ
  let g : Y ⟶ X := TopCat.ofHom e.invFun
  refine ⟨g, ?_, ?_⟩
  · have hg : (TopCat.Hom.hom g : C(Y, X)) = e.invFun := TopCat.hom_ofHom e.invFun
    have hfg : (TopCat.Hom.hom (f ≫ g) : C(X, X)) = e.invFun.comp e.toFun :=
      (TopCat.hom_comp f g).trans (congrArg₂ ContinuousMap.comp hg he.symm)
    let H : ContinuousMap.Homotopy (e.invFun.comp e.toFun) (ContinuousMap.id X) :=
      e.left_inv.some
    exact ⟨H.cast hfg.symm (TopCat.hom_id (X := X)).symm⟩
  · have hg : (TopCat.Hom.hom g : C(Y, X)) = e.invFun := TopCat.hom_ofHom e.invFun
    have hgf : (TopCat.Hom.hom (g ≫ f) : C(Y, Y)) = e.toFun.comp e.invFun :=
      (TopCat.hom_comp g f).trans (congrArg₂ ContinuousMap.comp he.symm hg)
    let H : ContinuousMap.Homotopy (e.toFun.comp e.invFun) (ContinuousMap.id Y) :=
      e.right_inv.some
    exact ⟨H.cast hgf.symm (TopCat.hom_id (X := Y)).symm⟩

end ActualKanFibrationHomologyCoefficients

end

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology
open scoped Simplicial ContinuousMap

universe u v w

local instance (I : Type u) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

namespace SSet.KanComplex

/-- The actual terminal map of a connected Kan complex is weak when its actual integral terminal homology maps are isomorphisms and π₁ is trivial at every vertex. -/
public theorem terminalMap_weak_of_integralHomology_isIso
    (K : SSet.{u}) [SSet.KanComplex K] [K.IsConnected]
    (hπ : ∀ b : K _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 K b))
    (h : ∀ n : ℕ, IsIso (SSet.homologyMap
      (SSet.stdSimplex.isTerminalObj₀.from K) AlgebraicTopology.singularIntegralCoefficients.{u} n)) :
    SSet.KanComplex.W (SSet.stdSimplex.isTerminalObj₀.from K) := by
  exact _root_.ActualKanFibrationHomologyCoefficients.simplyConnected_integralAcyclic_terminal_weak
    (K := K) (hπ := hπ) (h := h)

/-- The same actual terminal map is a realization weak equivalence, from integral acyclicity and simple connectedness of the original Kan complex. -/
public theorem terminalMap_realizationWeak_of_integralHomology_isIso
    (K : SSet.{u}) [SSet.KanComplex K] [K.IsConnected]
    (hπ : ∀ b : K _⦋0⦌, Subsingleton (SSet.KanComplex.π 1 K b))
    (h : ∀ n : ℕ, IsIso (SSet.homologyMap
      (SSet.stdSimplex.isTerminalObj₀.from K) AlgebraicTopology.singularIntegralCoefficients.{u} n)) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from K) := by
  exact _root_.ActualKanFibrationHomologyCoefficients.simplyConnected_integralAcyclic_terminal_realizationWeak
    (K := K) (hπ := hπ) (h := h)

end SSet.KanComplex

namespace TopCat

/-- All integral target local systems and the actual π₁ maps determine weakness of the SAME original map on all components; no CW hypothesis is required. -/
public theorem allLocalCoefficient_piOneIso_mem_weakHomotopyEquivalences
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (hπ : ∀ x : X, Function.Bijective
      (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x) :
        FundamentalGroup X x → FundamentalGroup Y (f x))) :
    TopCat.weakHomotopyEquivalences f := by
  exact _root_.ActualKanFibrationHomologyCoefficients.original_allLocalCoefficient_piOneIso_mem_weakHomotopyEquivalences
    (X := X) (Y := Y) (f := f) (hf := hf) (hπ := hπ)

/-- For genuine independently sized unbased CW models, the original all-local-coefficient and π₁ comparisons give a homotopy equivalence with forward map EXACTLY f. -/
public theorem allLocalCoefficient_CWType_piOneIso_homotopyEquiv
    {X Y : TopCat.{u}}
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C X))
    (hCWY : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C Y))
    (f : X ⟶ Y) (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (hπ : ∀ x : X, Function.Bijective
      (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x) :
        FundamentalGroup X x → FundamentalGroup Y (f x))) :
    ∃ e : ContinuousMap.HomotopyEquiv X Y, e.toFun = f.hom := by
  exact _root_.ActualKanFibrationHomologyCoefficients.original_allLocalCoefficient_CWType_piOneIso_homotopyEquiv
    (X := X) (Y := Y) (hCWX := hCWX) (hCWY := hCWY) (f := f) (hf := hf) (hπ := hπ)

/-- The same original all-local-coefficient comparison constructs a continuous inverse and BOTH ordinary inverse homotopies. -/
public theorem allLocalCoefficient_CWType_piOneIso_actual_inverse
    {X Y : TopCat.{u}}
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C X))
    (hCWY : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C Y))
    (f : X ⟶ Y) (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (hπ : ∀ x : X, Function.Bijective
      (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x) :
        FundamentalGroup X x → FundamentalGroup Y (f x))) :
    ∃ g : Y ⟶ X, Nonempty (TopCat.Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (TopCat.Homotopy (g ≫ f) (𝟙 Y)) := by
  exact _root_.ActualKanFibrationHomologyCoefficients.original_allLocalCoefficient_CWType_piOneIso_actual_inverse
    (X := X) (Y := Y) (hCWX := hCWX) (hCWY := hCWY) (f := f) (hf := hf) (hπ := hπ)

/-- The additional based companion retains the given genuine based CW models, literal points and BOTH singleton-relative inverse homotopies; weakness of f is derived first. -/
public theorem basedCWType_allLocalCoefficient_piOneIso_inverse
    (X Y : TopCat.{u}) (CX : TopCat.{v}) (CY : TopCat.{w})
    [T2Space CX] [T2Space CY]
    [Topology.CWComplex (Set.univ : Set CX)] [Topology.CWComplex (Set.univ : Set CY)]
    (x : X) (y : Y) (cx : CX) (cy : CY)
    (jx : Topology.CWComplex.cell (Set.univ : Set CX) 0)
    (jy : Topology.CWComplex.cell (Set.univ : Set CY) 0)
    (hjx : Topology.CWComplex.map 0 jx ![] = cx)
    (hjy : Topology.CWComplex.map 0 jy ![] = cy)
    (rx : C(X, CX)) (sx : C(CX, X)) (ry : C(Y, CY)) (sy : C(CY, Y))
    (hrx : rx x = cx) (hsx : sx cx = x) (hry : ry y = cy) (hsy : sy cy = y)
    (LX : ContinuousMap.HomotopyRel (sx.comp rx) (ContinuousMap.id X) {x})
    (RX : ContinuousMap.HomotopyRel (rx.comp sx) (ContinuousMap.id CX) {cx})
    (LY : ContinuousMap.HomotopyRel (sy.comp ry) (ContinuousMap.id Y) {y})
    (RY : ContinuousMap.HomotopyRel (ry.comp sy) (ContinuousMap.id CY) {cy})
    (f : X ⟶ Y) (hxy : f x = y)
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (hπ : ∀ z : X, Function.Bijective
      (FundamentalGroup.mapOfEq f.hom (rfl : f.hom z = f z) :
        FundamentalGroup X z → FundamentalGroup Y (f z))) :
    ∃ g : Y ⟶ X, g y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (f ≫ g).hom (TopCat.Hom.hom (𝟙 X)) {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (g ≫ f).hom (TopCat.Hom.hom (𝟙 Y)) {y}) := by
  exact _root_.ActualKanFibrationHomologyCoefficients.original_basedCWType_allLocalCoefficient_piOneIso_inverse
    (X := X) (Y := Y) (CX := CX) (CY := CY) (x := x) (y := y) (cx := cx) (cy := cy) (jx := jx) (jy := jy) (hjx := hjx) (hjy := hjy) (rx := rx) (sx := sx) (ry := ry) (sy := sy) (hrx := hrx) (hsx := hsx) (hry := hry) (hsy := hsy) (LX := LX) (RX := RX) (LY := LY) (RY := RY) (f := f) (hxy := hxy) (hf := hf) (hπ := hπ)

/-- Canonical reduced acyclicity of the actual ending fibers and the actual π₁ maps give weakness on all components in the original nonempty-source, connected-CW-type target setting. -/
public theorem canonical_acyclic_piOneIso_mem_weakHomotopyEquivalences
    {X Y : TopCat.{u}} [Nonempty X] [ConnectedSpace Y]
    (hCWY : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C Y))
    (f : X ⟶ Y) (hA : ∀ y : Y, TopCat.IsAcyclicMapAt f y)
    (hπ : ∀ x : X, Function.Bijective
      (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x) :
        FundamentalGroup X x → FundamentalGroup Y (f x))) :
    TopCat.weakHomotopyEquivalences f := by
  exact _root_.ActualKanFibrationHomologyCoefficients.original_canonical_acyclic_piOneIso_mem_weakHomotopyEquivalences
    (X := X) (Y := Y) (hCWY := hCWY) (f := f) (hA := hA) (hπ := hπ)

/-- The original canonical acyclic map between genuine independently sized unbased CW-type spaces has a homotopy equivalence whose forward map is EXACTLY f. -/
public theorem canonical_acyclic_CWType_piOneIso_homotopyEquiv
    {X Y : TopCat.{u}} [Nonempty X] [ConnectedSpace Y]
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C X))
    (hCWY : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C Y))
    (f : X ⟶ Y) (hA : ∀ y : Y, TopCat.IsAcyclicMapAt f y)
    (hπ : ∀ x : X, Function.Bijective
      (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x) :
        FundamentalGroup X x → FundamentalGroup Y (f x))) :
    ∃ e : ContinuousMap.HomotopyEquiv X Y, e.toFun = f.hom := by
  exact _root_.ActualKanFibrationHomologyCoefficients.original_canonical_acyclic_CWType_piOneIso_homotopyEquiv
    (X := X) (Y := Y) (hCWX := hCWX) (hCWY := hCWY) (f := f) (hA := hA) (hπ := hπ)

/-- The canonical acyclic original map has a constructed continuous inverse and BOTH ordinary inverse homotopies. Its original nonempty and connected-CW scope is retained. -/
public theorem canonical_acyclic_CWType_piOneIso_actual_inverse
    {X Y : TopCat.{u}} [Nonempty X] [ConnectedSpace Y]
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C X))
    (hCWY : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (ContinuousMap.HomotopyEquiv C Y))
    (f : X ⟶ Y) (hA : ∀ y : Y, TopCat.IsAcyclicMapAt f y)
    (hπ : ∀ x : X, Function.Bijective
      (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x) :
        FundamentalGroup X x → FundamentalGroup Y (f x))) :
    ∃ g : Y ⟶ X, Nonempty (TopCat.Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (TopCat.Homotopy (g ≫ f) (𝟙 Y)) := by
  exact _root_.ActualKanFibrationHomologyCoefficients.original_canonical_acyclic_CWType_piOneIso_actual_inverse
    (X := X) (Y := Y) (hCWX := hCWX) (hCWY := hCWY) (f := f) (hA := hA) (hπ := hπ)

end TopCat

end
