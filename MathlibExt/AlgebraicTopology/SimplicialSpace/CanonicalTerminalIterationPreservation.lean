/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalReplacementPreservation

/-!
# Preservation and weak detection for the literal canonical terminal iteration

The canonical factorization middle is already identified with the literal
terminal-iteration functor.  These wrappers expose pullback, monomorphism and
cardinal-accessibility preservation directly on that functor, so downstream
arguments do not repeatedly reconstruct and rewrite the factorization data.
The same exact rewrite also exposes weak detection directly on the literal
terminal-iteration map.
-/

set_option autoImplicit false
noncomputable section

universe u

open Cardinal CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SimplicialSpace

/-- The literal canonical terminal iteration preserves pullbacks. -/
theorem canonical_terminalIteration_preservesPullbacks
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ] :
    PreservesLimitsOfShape WalkingCospan
      (SmallObject.terminalIteration LocalGenerators.J.{u} κ) := by
  let t := terminal.fromNatTrans SimplicialSpace.{u}
  let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
  let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
  have h : PreservesLimitsOfShape WalkingCospan r.Z :=
    canonical_localReplacement_preservesPullbacks κ
  rw [SmallObject.canonical_terminal_middle_eq_terminalIteration
    LocalGenerators.J.{u} κ] at h
  exact h

/-- The literal canonical terminal iteration preserves monomorphisms. -/
theorem canonical_terminalIteration_preservesMonomorphisms
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ] :
    (SmallObject.terminalIteration LocalGenerators.J.{u} κ).PreservesMonomorphisms := by
  let t := terminal.fromNatTrans SimplicialSpace.{u}
  let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
  let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
  have h : r.Z.PreservesMonomorphisms :=
    canonical_localReplacement_preservesMonomorphisms κ
  rw [SmallObject.canonical_terminal_middle_eq_terminalIteration
    LocalGenerators.J.{u} κ] at h
  exact h

/-- At every externally supplied regular common endpoint-presentability
cardinal, the literal canonical terminal iteration is accessible. -/
theorem canonical_terminalIteration_isCardinalAccessible
    (κ μ : Cardinal.{u})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    [Fact μ.IsRegular]
    [∀ i : LocalGenerators.J.{u}.toSet,
      IsCardinalPresentable.{u} i.1.left μ]
    [∀ i : LocalGenerators.J.{u}.toSet,
      IsCardinalPresentable.{u} i.1.right μ] :
    (SmallObject.terminalIteration LocalGenerators.J.{u} κ).IsCardinalAccessible μ := by
  let t := terminal.fromNatTrans SimplicialSpace.{u}
  let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
  let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
  have h : r.Z.IsCardinalAccessible μ :=
    canonical_localReplacement_isCardinalAccessible κ μ
  rw [SmallObject.canonical_terminal_middle_eq_terminalIteration
    LocalGenerators.J.{u} κ] at h
  exact h

/-- The literal canonical terminal iteration detects the original Rezk weak
class through the named Reedy weak equivalences. -/
theorem canonical_terminalIteration_weak_detection
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    rezkWeakEquivalences f ↔
      WeakEquivalence
        ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map f) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let t := terminal.fromNatTrans SimplicialSpace.{u}
  let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
  let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
  have h : rezkWeakEquivalences f ↔ WeakEquivalence (r.Z.map f) := by
    simpa only using canonical_localReplacement_weak_detection κ f
  have hEq : r.Z =
      SmallObject.terminalIteration LocalGenerators.J.{u} κ :=
    SmallObject.canonical_terminal_middle_eq_terminalIteration
      LocalGenerators.J.{u} κ
  rw [hEq] at h
  exact h

end SimplicialSpace
