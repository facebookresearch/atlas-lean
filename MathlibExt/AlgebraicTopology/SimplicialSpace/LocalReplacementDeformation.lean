/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerOneSimplexCylinder
import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalReplacementPreservation

/-!
# Stationary deformation for the canonical local replacement

The same canonical terminal iteration sends every original monic Rezk weak map
to a Reedy trivial cofibration between complete Segal spaces.  The literal
inner one-simplex cylinder therefore supplies a strict retraction and a
homotopy from the identity to the retract composite, stationary on the whole
source cylinder.
-/

set_option autoImplicit false
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MorphismProperty

namespace SimplicialSpace

/-- Every object produced by the exact canonical terminal iteration is a
complete Segal space for the same eligible cardinal and auxiliary family. -/
theorem canonical_localReplacement_completeSegalSpaces
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    (X : SimplicialSpace.{u}) :
    completeSegalSpaces
      ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj X) := by
  let t := terminal.fromNatTrans SimplicialSpace.{u}
  let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
  let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
  have hQ : r.Z = SmallObject.terminalIteration LocalGenerators.J.{u} κ :=
    SmallObject.canonical_terminal_middle_eq_terminalIteration
      LocalGenerators.J.{u} κ
  rw [← hQ]
  apply (LocalGenerators.terminal_rlp_iff_completeSegalSpaces (r.Z.obj X)).1
  have hp : r.p.app X = terminal.from (r.Z.obj X) :=
    terminalIsTerminal.hom_ext _ _
  rw [← hp]
  exact r.hp X

/-- The exact canonical terminal iteration sends an original monic Rezk weak
map to a trivial cofibration in the named Reedy model. -/
theorem canonical_localReplacement_map_trivialCofibration
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    {X Y : SimplicialSpace.{u}} (i : X ⟶ Y) [Mono i]
    (hi : rezkWeakEquivalences i) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    trivialCofibrations SimplicialSpace.{u}
      ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map i) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let Q := SmallObject.terminalIteration LocalGenerators.J.{u} κ
  let t := terminal.fromNatTrans SimplicialSpace.{u}
  let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
  let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
  have hQ : r.Z = Q :=
    SmallObject.canonical_terminal_middle_eq_terminalIteration
      LocalGenerators.J.{u} κ
  have hMono : Q.PreservesMonomorphisms := by
    have h : r.Z.PreservesMonomorphisms :=
      canonical_localReplacement_preservesMonomorphisms κ
    rw [hQ] at h
    exact h
  let _ : Q.PreservesMonomorphisms := hMono
  let _ : Mono (Q.map i) := inferInstance
  have hWeak : WeakEquivalence (Q.map i) := by
    have h := (canonical_localReplacement_weak_detection κ i).1 hi
    rw [hQ] at h
    exact h
  exact ⟨
    (HomotopicalAlgebra.cofibration_iff (Q.map i)).1
      ((ReedyModel.cofibration_iff (Q.map i)).2 inferInstance),
    (HomotopicalAlgebra.weakEquivalence_iff (Q.map i)).1 hWeak⟩

/-- The same canonical Q-map has a strict retraction and an actual inner
one-simplex homotopy from the identity to the retract composite, stationary on
the whole original QX cylinder. -/
theorem canonical_localReplacement_strongDeformation
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    {X Y : SimplicialSpace.{u}} (i : X ⟶ Y) [Mono i]
    (hi : rezkWeakEquivalences i) :
    Nonempty (innerOneSimplexPrecylinder.StrongDeformationData
      ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map i)) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let Q := SmallObject.terminalIteration LocalGenerators.J.{u} κ
  exact ReedyModel.nonempty_innerStrongDeformationData_of_trivialCofibration
    (Q.map i) (canonical_localReplacement_map_trivialCofibration κ i hi)
      (canonical_localReplacement_completeSegalSpaces κ X).1
      (canonical_localReplacement_completeSegalSpaces κ Y).1

end SimplicialSpace
