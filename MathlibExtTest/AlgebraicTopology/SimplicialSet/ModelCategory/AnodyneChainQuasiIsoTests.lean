/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AnodyneChainQuasiIso
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Data.Matrix.Mul

/-!
# Chain quasi-isomorphisms of anodyne extensions

These owner tests exercise the normalized and unnormalized public theorems
on all one- and two-dimensional horns, a mixed coproduct, a nontrivial
pushout, a Nat-shaped transfinite composition, retract transport, and
identity maps of empty and disconnected simplicial sets.  Coefficients
include the zero module and the regular module over a noncommutative matrix
ring.

The tests assert only the two public anodyne-to-chain conclusions.  In
particular, they make no converse, realization, TopCat, reduced, relative,
or cofiber claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex MorphismProperty
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
namespace AnodyneChainQuasiIsoTests

section PublicContract

variable {R : Type u} [Ring R] (A : ModuleCat.{u} R)
  {X Y : SSet.{u}} {f : X ⟶ Y}

example (hf : SSet.anodyneExtensions f) :
    QuasiIso (SSet.normalizedChainComplexMap f A) :=
  SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap A hf

example (hf : SSet.anodyneExtensions f) :
    QuasiIso (SSet.chainComplexMap f A) :=
  SSet.anodyneExtensions.quasiIso_chainComplexMap A hf

end PublicContract

section LiteralHorns

variable {R : Type u} [Ring R] (A : ModuleCat.{u} R)

/-- The left one-horn catches the degree-one missing-face orientation. -/
example :
    QuasiIso
      (SSet.normalizedChainComplexMap
        (SSet.horn (n := 1) (0 : Fin 2)).ι A) :=
  SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap A
    (SSet.anodyneExtensions.horn_ι (0 : Fin 2))

/-- The right one-horn catches the opposite degree-one orientation. -/
example :
    QuasiIso
      (SSet.normalizedChainComplexMap
        (SSet.horn (n := 1) (1 : Fin 2)).ι A) :=
  SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap A
    (SSet.anodyneExtensions.horn_ι (1 : Fin 2))

/-- The first two-horn tests the positive end of the signed boundary. -/
example :
    QuasiIso
      (SSet.normalizedChainComplexMap
        (SSet.horn (n := 2) (0 : Fin 3)).ι A) :=
  SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap A
    (SSet.anodyneExtensions.horn_ι (0 : Fin 3))

/-- The middle two-horn tests the negative missing-face sign. -/
example :
    QuasiIso
      (SSet.normalizedChainComplexMap
        (SSet.horn (n := 2) (1 : Fin 3)).ι A) :=
  SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap A
    (SSet.anodyneExtensions.horn_ι (1 : Fin 3))

/-- The last two-horn tests the other positive missing-face sign. -/
example :
    QuasiIso
      (SSet.normalizedChainComplexMap
        (SSet.horn (n := 2) (2 : Fin 3)).ι A) :=
  SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap A
    (SSet.anodyneExtensions.horn_ι (2 : Fin 3))

/-- The unnormalized adapter is exercised on the sign-sensitive middle horn. -/
example :
    QuasiIso
      (SSet.chainComplexMap
        (SSet.horn (n := 2) (1 : Fin 3)).ι A) :=
  SSet.anodyneExtensions.quasiIso_chainComplexMap A
    (SSet.anodyneExtensions.horn_ι (1 : Fin 3))

end LiteralHorns

section MixedCoproduct

private abbrev mixedHornSource (b : Bool) : SSet.{u} :=
  if b then SSet.horn (n := 2) (1 : Fin 3)
  else SSet.horn (n := 1) (0 : Fin 2)

private abbrev mixedHornTarget (b : Bool) : SSet.{u} :=
  if b then Δ[2] else Δ[1]

private def mixedHornMap (b : Bool) :
    mixedHornSource.{u} b ⟶ mixedHornTarget.{u} b := by
  cases b with
  | false => exact (SSet.horn (n := 1) (0 : Fin 2)).ι
  | true => exact (SSet.horn (n := 2) (1 : Fin 3)).ι

private noncomputable abbrev mixedHornCoproduct :
    (∐ mixedHornSource.{u}) ⟶ ∐ mixedHornTarget.{u} :=
  Limits.Sigma.map mixedHornMap

private theorem mixedHornCoproduct_anodyne :
    SSet.anodyneExtensions mixedHornCoproduct.{u} := by
  apply MorphismProperty.colimMap
  rintro ⟨b⟩
  cases b with
  | false => exact SSet.anodyneExtensions.horn_ι (0 : Fin 2)
  | true => exact SSet.anodyneExtensions.horn_ι (1 : Fin 3)

variable {R : Type u} [Ring R] (A : ModuleCat.{u} R)

example :
    QuasiIso
      (SSet.normalizedChainComplexMap mixedHornCoproduct.{u} A) :=
  SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap A
    mixedHornCoproduct_anodyne

end MixedCoproduct

section NontrivialPushout

private abbrev pushoutHorn : SSet.{0} :=
  SSet.horn (n := 1) (0 : Fin 2)

private abbrev pushoutHornInclusion :
    pushoutHorn ⟶ (Δ[1] : SSet.{0}) :=
  (SSet.horn (n := 1) (0 : Fin 2)).ι

private noncomputable def collapsePushoutHorn :
    pushoutHorn ⟶ (Δ[0] : SSet.{0}) :=
  SSet.stdSimplex.isTerminalObj₀.from pushoutHorn

/-- This is the new leg after attaching a one-simplex to a point along one
endpoint.  Its source and target differ, so this is not an identity-pushout
test. -/
private noncomputable def pushedHorn :
    (Δ[0] : SSet.{0}) ⟶
      pushout pushoutHornInclusion collapsePushoutHorn :=
  pushout.inr pushoutHornInclusion collapsePushoutHorn

private theorem pushedHorn_anodyne :
    SSet.anodyneExtensions pushedHorn := by
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (P := SSet.anodyneExtensions)
    (IsPushout.of_hasPushout pushoutHornInclusion collapsePushoutHorn).flip
    (SSet.anodyneExtensions.horn_ι (0 : Fin 2))

variable {R : Type} [Ring R] (A : ModuleCat.{0} R)

example :
    QuasiIso (SSet.normalizedChainComplexMap pushedHorn A) :=
  SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap A
    pushedHorn_anodyne

end NontrivialPushout

section ClosureConstructors

private abbrev towerHorn : SSet.{0} :=
  SSet.horn (n := 1) (0 : Fin 2)

private abbrev towerCell : SSet.{0} := Δ[1]

private abbrev towerHornInclusion : towerHorn ⟶ towerCell :=
  (SSet.horn (n := 1) (0 : Fin 2)).ι

private structure HornTowerStageData where
  carrier : SSet.{0}
  attach : towerHorn ⟶ carrier

private def hornTowerBase : HornTowerStageData where
  carrier := towerHorn
  attach := 𝟙 _

private noncomputable def hornTowerNext
    (P : HornTowerStageData) : HornTowerStageData where
  carrier := pushout towerHornInclusion P.attach
  attach := towerHornInclusion ≫ pushout.inl towerHornInclusion P.attach

private noncomputable def hornTowerData : ℕ → HornTowerStageData
  | 0 => hornTowerBase
  | n + 1 => hornTowerNext (hornTowerData n)

private noncomputable abbrev hornTowerStage (n : ℕ) : SSet.{0} :=
  (hornTowerData n).carrier

private noncomputable abbrev hornTowerAttach (n : ℕ) :
    towerHorn ⟶ hornTowerStage n :=
  (hornTowerData n).attach

/-- Every successor stage is the actual pushout obtained by attaching one
new one-simplex along the fixed left horn. -/
private theorem hornTowerStage_succ (n : ℕ) :
    hornTowerStage (n + 1) =
      pushout towerHornInclusion (hornTowerAttach n) :=
  rfl

private noncomputable def hornTowerStep (n : ℕ) :
    hornTowerStage n ⟶ hornTowerStage (n + 1) := by
  change (hornTowerData n).carrier ⟶
    (hornTowerNext (hornTowerData n)).carrier
  exact pushout.inr towerHornInclusion (hornTowerData n).attach

/-- The successor map is literally the new leg of the horn-attachment
pushout, not an identity or a finite tower reindexed by `ℕ`. -/
private theorem hornTowerStep_isPushout (n : ℕ) :
    IsPushout (hornTowerAttach n) towerHornInclusion
      (hornTowerStep n)
      (pushout.inl towerHornInclusion (hornTowerAttach n)) := by
  exact (IsPushout.of_hasPushout
    towerHornInclusion (hornTowerAttach n)).flip

private theorem hornTowerStep_anodyne (n : ℕ) :
    SSet.anodyneExtensions (hornTowerStep n) :=
  MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (P := SSet.anodyneExtensions) (hornTowerStep_isPushout n)
    (SSet.anodyneExtensions.horn_ι (0 : Fin 2))

private noncomputable def hornTowerFunctor : ℕ ⥤ SSet.{0} :=
  Functor.ofSequence hornTowerStep

private noncomputable def hornTowerInclusion :
    hornTowerFunctor.obj 0 ⟶ colimit hornTowerFunctor :=
  colimit.ι hornTowerFunctor 0

private noncomputable def hornTowerTransfiniteComposition :
    SSet.anodyneExtensions.TransfiniteCompositionOfShape ℕ
      hornTowerInclusion where
  F := hornTowerFunctor
  isoBot := Iso.refl _
  incl := (colimit.cocone hornTowerFunctor).ι
  isColimit := colimit.isColimit _
  fac := by
    change 𝟙 _ ≫ colimit.ι hornTowerFunctor 0 =
      colimit.ι hornTowerFunctor 0
    exact Category.id_comp _
  map_mem n _ := by
    change SSet.anodyneExtensions
      ((Functor.ofSequence hornTowerStep).map
        (homOfLE (Nat.le_add_right n 1)))
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact hornTowerStep_anodyne n

/-- This client reaches the public theorem through a concrete, unbounded
Nat tower with one genuine horn attachment at every successor. -/
example {R : Type} [Ring R] (A : ModuleCat.{0} R) :
    QuasiIso
      (SSet.normalizedChainComplexMap hornTowerInclusion A) := by
  have hf : SSet.anodyneExtensions hornTowerInclusion := by
    apply MorphismProperty.transfiniteCompositionsOfShape_le
      (W := SSet.anodyneExtensions) (J := ℕ)
    exact hornTowerTransfiniteComposition.mem
  exact SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap A hf

variable {R : Type u} [Ring R] (A : ModuleCat.{u} R)
  {X Y Z W : SSet.{u}} {f : X ⟶ Y} {g : Z ⟶ W}

/-- Retract transport is exercised on the actual arrow-category retract
witness, before invoking the public chain theorem. -/
example (h : RetractArrow f g) (hg : SSet.anodyneExtensions g) :
    QuasiIso (SSet.normalizedChainComplexMap f A) := by
  have hf : SSet.anodyneExtensions f :=
    MorphismProperty.of_retract h hg
  exact SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap A hf

end ClosureConstructors

section EmptyAndDisconnected

private abbrev emptySSet : SSet.{u} :=
  (⊥ : (Δ[0] : SSet.{u}).Subcomplex)

private abbrev twoPointSSet : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{u} (Fin 2))

variable {R : Type u} [Ring R] (A : ModuleCat.{u} R)

example :
    QuasiIso
      (SSet.normalizedChainComplexMap (𝟙 emptySSet.{u}) A) :=
  SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap A
    (SSet.anodyneExtensions.of_isIso (𝟙 emptySSet.{u}))

example :
    QuasiIso (SSet.chainComplexMap (𝟙 twoPointSSet.{u}) A) :=
  SSet.anodyneExtensions.quasiIso_chainComplexMap A
    (SSet.anodyneExtensions.of_isIso (𝟙 twoPointSSet.{u}))

end EmptyAndDisconnected

section CoefficientGates

variable {R : Type u} [Ring R]

/-- Zero coefficients are supported, but this direction still consumes an
anodyne premise and states no converse. -/
example :
    QuasiIso
      (SSet.normalizedChainComplexMap
        (SSet.horn (n := 2) (1 : Fin 3)).ι
        (⊥_ (ModuleCat.{u} R))) :=
  SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap
    (⊥_ (ModuleCat.{u} R))
    (SSet.anodyneExtensions.horn_ι (1 : Fin 3))

private abbrev MatrixRing := Matrix (Fin 2) (Fin 2) ℤ

/-- The coefficient ring is concretely noncommutative. -/
example : True := by
  fail_if_success let _ : CommRing MatrixRing := inferInstance
  trivial

/-- The regular left module over a noncommutative matrix ring prevents an
accidental `CommRing` assumption in either public theorem. -/
example :
    QuasiIso
      (SSet.normalizedChainComplexMap
        (SSet.horn (n := 2) (1 : Fin 3)).ι
        (ModuleCat.of MatrixRing MatrixRing)) :=
  SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap
    (ModuleCat.of MatrixRing MatrixRing)
    (SSet.anodyneExtensions.horn_ι (1 : Fin 3))

end CoefficientGates

section ExplicitUniverses

example {R : Type 1} [Ring R] (A : ModuleCat.{1} R)
    {X Y : SSet.{1}} {f : X ⟶ Y} (hf : SSet.anodyneExtensions f) :
    QuasiIso (SSet.normalizedChainComplexMap f A) :=
  SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap A hf

example {R : Type} [Ring R] (A : ModuleCat.{0} R)
    {X Y : SSet.{0}} {f : X ⟶ Y} (hf : SSet.anodyneExtensions f) :
    QuasiIso (SSet.normalizedChainComplexMap f A) :=
  SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap A hf

example {R : Type 1} [Ring R] (A : ModuleCat.{1} R)
    {X Y : SSet.{1}} {f : X ⟶ Y} (hf : SSet.anodyneExtensions f) :
    QuasiIso (SSet.chainComplexMap f A) :=
  SSet.anodyneExtensions.quasiIso_chainComplexMap A hf

example {R : Type} [Ring R] (A : ModuleCat.{0} R)
    {X Y : SSet.{0}} {f : X ⟶ Y} (hf : SSet.anodyneExtensions f) :
    QuasiIso (SSet.chainComplexMap f A) :=
  SSet.anodyneExtensions.quasiIso_chainComplexMap A hf

end ExplicitUniverses

section NegativePremiseAndScopeGates

example {R : Type u} [Ring R] (_A : ModuleCat.{u} R)
    {X Y : SSet.{u}} (_f : X ⟶ Y) : True := by
  fail_if_success
    have _h : QuasiIso (SSet.normalizedChainComplexMap _f _A) :=
      SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap _A
        (by infer_instance)
  trivial

/-- error: Unknown constant
`SSet.anodyneExtensions.of_quasiIso_normalizedChainComplexMap` -/
#guard_msgs (error, substring := true) in
#check SSet.anodyneExtensions.of_quasiIso_normalizedChainComplexMap

/-- error: Unknown constant
`SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap_generic` -/
#guard_msgs (error, substring := true) in
#check SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap_generic

end NegativePremiseAndScopeGates

#print axioms SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap
#print axioms SSet.anodyneExtensions.quasiIso_chainComplexMap

end AnodyneChainQuasiIsoTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
