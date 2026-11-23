/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.LocalCoefficient.HomotopyFiberAcyclicity
import Mathlib.Data.ZMod.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Logic.Small.Defs

/-! Direct canonical reduced-acyclicity, nonemptiness, terminal-map and nonflat contracts. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ContinuousMap

universe u v

#check @TopCat.homotopyFiber_terminalHomology_isIso_of_localCoefficientHomologyEquivalence
#print axioms TopCat.homotopyFiber_terminalHomology_isIso_of_localCoefficientHomologyEquivalence
#check @TopCat.localCoefficientPullbackChainMap_quasiIso_of_homotopyFiber
#print axioms TopCat.localCoefficientPullbackChainMap_quasiIso_of_homotopyFiber
#check @TopCat.homotopyFiber_terminalHomology_iff_localCoefficientHomologyEquivalence
#print axioms TopCat.homotopyFiber_terminalHomology_iff_localCoefficientHomologyEquivalence

-- All original points and degrees, with no CW or replacement-fiber input.
example {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f) (y : Y) (n : ℕ) :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y))) :=
  TopCat.homotopyFiber_terminalHomology_isIso_of_localCoefficientHomologyEquivalence f hf y n

-- The entire actual chain map with an arbitrary original target local system.
example {X Y : TopCat.{u}} [PathConnectedSpace Y] (f : X ⟶ Y) (y : Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y)))) (L : TopCat.LocalSystem ℤ Y) :
    QuasiIso (TopCat.localCoefficientPullbackChainMap f L) :=
  TopCat.localCoefficientPullbackChainMap_quasiIso_of_homotopyFiber f y h L

-- A genuine independently sized CW-type model, not an inverse for f.
example {X Y : TopCat.{u}} [ConnectedSpace Y]
    {C : TopCat.{v}} [T2Space C] [Topology.CWComplex (Set.univ : Set C)]
    (e : C ≃ₕ Y) (f : X ⟶ Y) :
    (∀ y : Y, ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y)))) ↔
        TopCat.IsLocalCoefficientHomologyEquivalence f :=
  TopCat.homotopyFiber_terminalHomology_iff_localCoefficientHomologyEquivalence
    ⟨C, inferInstance, inferInstance, ⟨e⟩⟩ f

-- Nonflat integer-mod-two stalks are part of the original every-system conclusion.
example {X Y : TopCat.{u}} [ConnectedSpace Y]
    (hCW : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Y))
    (f : X ⟶ Y)
    (h : ∀ y : Y, ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y)))) (n : ℕ) :
    IsIso (TopCat.localCoefficientPullbackHomologyMap f
      ((CategoryTheory.Functor.const (_root_.FundamentalGroupoid Y)).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))) n) := by
  exact
    ((TopCat.homotopyFiber_terminalHomology_iff_localCoefficientHomologyEquivalence hCW f).mp h) _ n

#check @TopCat.isAcyclicSpace_iff_terminalHomology_isIso
#print axioms TopCat.isAcyclicSpace_iff_terminalHomology_isIso
#check @TopCat.isAcyclicMapAt_of_localCoefficientHomologyEquivalence
#print axioms TopCat.isAcyclicMapAt_of_localCoefficientHomologyEquivalence
#check @TopCat.homotopyFiber_acyclic_iff_localCoefficientHomologyEquivalence
#print axioms TopCat.homotopyFiber_acyclic_iff_localCoefficientHomologyEquivalence

-- Canonical reduced acyclicity of a real nonempty space yields every actual terminal map.
example (X : TopCat.{u}) [Nonempty X] (h : TopCat.IsAcyclicSpace X) (n : ℕ) :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map (terminal.from X)) :=
  ((TopCat.isAcyclicSpace_iff_terminalHomology_isIso X).mp h) n

-- The unrestricted forward theorem now states the actual canonical predicate.
example {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f) (y : Y) :
    TopCat.IsAcyclicMapAt f y :=
  TopCat.isAcyclicMapAt_of_localCoefficientHomologyEquivalence f hf y

-- The original connected-source CW context supplies Nonempty without a fiber witness.
example {X Y : TopCat.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    (hCW : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Y))
    (f : X ⟶ Y) (hf : TopCat.IsLocalCoefficientHomologyEquivalence f) :
    ∀ y : Y, TopCat.IsAcyclicMapAt f y :=
  (TopCat.homotopyFiber_acyclic_iff_localCoefficientHomologyEquivalence hCW f).mpr hf

-- Canonical acyclicity, with the real source nonemptiness, includes nonflat Z/2 stalks.
example {X Y : TopCat.{u}} [Nonempty X] [ConnectedSpace Y]
    (hCW : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Y))
    (f : X ⟶ Y) (h : ∀ y : Y, TopCat.IsAcyclicMapAt f y) (n : ℕ) :
    IsIso (TopCat.localCoefficientPullbackHomologyMap f
      ((CategoryTheory.Functor.const (_root_.FundamentalGroupoid Y)).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))) n) := by
  exact ((TopCat.homotopyFiber_acyclic_iff_localCoefficientHomologyEquivalence hCW f).mp h) _ n

local instance (I : Type u) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

private theorem empty_integral_homology_isZero (X : TopCat.{u}) [IsEmpty X] (n : ℕ) :
    IsZero (AlgebraicTopology.singularIntegralHomology n X) := by
  let K := TopCat.toSSet.obj X
  have hnone : ¬ K.Nonempty := by
    rintro ⟨x⟩
    exact isEmptyElim (TopCat.toSSetObj₀Equiv x)
  let : K.HasDimensionLT 0 := K.notNonempty_iff_hasDimensionLT_zero.mp hnone
  exact SSet.isZero_homology_of_hasDimensionLT K
    AlgebraicTopology.singularIntegralCoefficients n 0 (Nat.zero_le n)

private theorem empty_canonical_acyclic (X : TopCat.{u}) [IsEmpty X] :
    TopCat.IsAcyclicSpace X := by
  intro n
  let R : AddCommGrpCat.{u} := AlgebraicTopology.singularIntegralCoefficients
  let a := (AlgebraicTopology.singularHomologyAugmentation AddCommGrpCat.{u} R n).app X
  have hH : IsZero (AlgebraicTopology.singularIntegralHomology n X) :=
    empty_integral_homology_isZero X n
  have hK : IsZero (kernel a) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (cancel_mono (kernel.ι a)).mp
    simp only [Category.id_comp, zero_comp]
    exact hH.eq_of_tgt _ _
  exact hK.of_iso (AlgebraicTopology.reducedSingularHomologyObjIso AddCommGrpCat.{u} R n X)

private theorem empty_terminal_H0_not_isIso (X : TopCat.{u}) [IsEmpty X] :
    ¬ IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 0).map (terminal.from X)) := by
  intro h
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := AlgebraicTopology.singularIntegralHomologyFunctor 0
  let R : AddCommGrpCat.{u} := AlgebraicTopology.singularIntegralCoefficients
  let : IsIso (H.map (terminal.from X)) := h
  have hX : IsZero (H.obj X) := empty_integral_homology_isZero X 0
  have hT : IsZero (H.obj (⊤_ TopCat.{u})) :=
    hX.of_iso (asIso (H.map (terminal.from X))).symm
  let e : (⊤_ TopCat.{u}) ≅ (TopCat.of PUnit : TopCat.{u}) :=
    TopCat.terminalIsoPUnit.{u}
  have hP : IsZero (H.obj (TopCat.of PUnit : TopCat.{u})) :=
    hT.of_iso (H.mapIso e).symm
  let eR := AlgebraicTopology.singularHomologyPUnitZeroIso AddCommGrpCat.{u} R
  have hR : IsZero R := hP.of_iso eR.symm
  have hid : (𝟙 R) = (0 : R ⟶ R) := hR.eq_of_src _ _
  have hv := ConcreteCategory.congr_hom hid (ULift.up (1 : ℤ))
  have h10 : (1 : ℤ) = 0 := congrArg ULift.down hv
  exact one_ne_zero h10

-- Empty has canonical reduced acyclicity, but its actual H0 terminal map is not an Iso.
theorem client_empty_canonical_and_H0_negative :
    TopCat.IsAcyclicSpace (TopCat.of Empty : TopCat.{0}) ∧
      ¬ IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 0).map
        (terminal.from (TopCat.of Empty : TopCat.{0}))) := by
  exact ⟨empty_canonical_acyclic _, empty_terminal_H0_not_isIso _⟩

-- The original adverse map is Empty→PUnit, with its SAME actual ending fibers.
theorem client_empty_to_point_canonical_not_local_equivalence :
    (∀ y : PUnit, TopCat.IsAcyclicMapAt
      (TopCat.const PUnit.unit : (TopCat.of Empty : TopCat.{0}) ⟶ TopCat.of PUnit) y) ∧
      ¬ TopCat.IsLocalCoefficientHomologyEquivalence
        (TopCat.const PUnit.unit : (TopCat.of Empty : TopCat.{0}) ⟶ TopCat.of PUnit) := by
  let f : (TopCat.of Empty : TopCat.{0}) ⟶ TopCat.of PUnit := TopCat.const PUnit.unit
  constructor
  · intro y
    let : IsEmpty (TopCat.homotopyFiber f y) :=
      ⟨fun z => isEmptyElim (TopCat.homotopyFiberToTotal f y z)⟩
    exact empty_canonical_acyclic _
  · intro hf
    let : IsEmpty (TopCat.homotopyFiber f PUnit.unit) :=
      ⟨fun z => isEmptyElim (TopCat.homotopyFiberToTotal f PUnit.unit z)⟩
    exact empty_terminal_H0_not_isIso _
      (TopCat.homotopyFiber_terminalHomology_isIso_of_localCoefficientHomologyEquivalence
        f hf PUnit.unit 0)

end
