/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.AuxiliaryGeneratorProperties
import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalReplacement
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalIterationCardinalColimits
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalIterationPullbacks
import MathlibExt.AlgebraicTopology.SimplicialSpace.Presentable
import MathlibExt.CategoryTheory.SmallObject.EndpointProfile
import MathlibExt.CategoryTheory.SmallObject.TerminalIteration

/-!
# Preservation by the canonical local replacement

Fix the literal auxiliary family and an eligible regular cardinal `κ`. The
canonical functor-category small-object factorization of the terminal natural
transformation has middle functor `Qκ`. This file identifies that whole functor
with the terminal restriction of the same native `κ`-iteration, retains its
two native factors and right-unit normalization, and transfers pullbacks,
monomorphisms, and cardinal-filtered colimits to that exact `Qκ`.

No replacement, family, or factorization is reselected.
-/

set_option autoImplicit false
noncomputable section

universe u

open Cardinal CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty

namespace SimplicialSpace

/-- The exact canonical local-replacement middle at `κ` preserves pullbacks.
Monicity of the literal auxiliary generators is derived from their proved
monic-and-weak membership. -/
theorem canonical_localReplacement_preservesPullbacks
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ] :
    let t := terminal.fromNatTrans SimplicialSpace.{u}
    let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
    let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
    PreservesLimitsOfShape WalkingCospan r.Z := by
  dsimp only
  let t := terminal.fromNatTrans SimplicialSpace.{u}
  let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
  let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
  let _ : ∀ i : LocalGenerators.J.{u}.toSet,
      Mono (LocalGenerators.J.{u}.homFamily i) := fun i =>
    (LocalGenerators.le_monomorphisms_inf_rezkWeakEquivalences _ i.2).1
  let _ : PreservesLimitsOfShape WalkingCospan
      (SmallObject.iteration LocalGenerators.J.{u} κ) :=
    originalIteration_preservesPullbacks LocalGenerators.J.{u} κ
  rw [SmallObject.canonical_terminal_middle_eq_terminalIteration
    LocalGenerators.J.{u} κ]
  exact SmallObject.terminalIteration_preservesLimitsOfShape
    LocalGenerators.J.{u} κ WalkingCospan

/-- The exact canonical local-replacement middle at `κ` preserves
monomorphisms as a consequence of its pullback preservation. -/
theorem canonical_localReplacement_preservesMonomorphisms
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ] :
    let t := terminal.fromNatTrans SimplicialSpace.{u}
    let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
    let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
    r.Z.PreservesMonomorphisms := by
  dsimp only
  let t := terminal.fromNatTrans SimplicialSpace.{u}
  let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
  let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
  let _ : PreservesLimitsOfShape WalkingCospan r.Z :=
    canonical_localReplacement_preservesPullbacks κ
  infer_instance

/-- For any externally supplied regular `μ` presenting both endpoints of the
literal auxiliary generators, the exact canonical local-replacement middle at
`κ` is `μ`-accessible. This parameterized form lets later cardinal
envelopes enlarge `μ` without changing `κ` or `Qκ`. -/
theorem canonical_localReplacement_isCardinalAccessible
    (κ μ : Cardinal.{u})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    [Fact μ.IsRegular]
    [∀ i : LocalGenerators.J.{u}.toSet,
      IsCardinalPresentable.{u} i.1.left μ]
    [∀ i : LocalGenerators.J.{u}.toSet,
      IsCardinalPresentable.{u} i.1.right μ] :
    let t := terminal.fromNatTrans SimplicialSpace.{u}
    let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
    let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
    r.Z.IsCardinalAccessible μ := by
  dsimp only
  let t := terminal.fromNatTrans SimplicialSpace.{u}
  let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
  let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
  let _ : IsLocallyPresentable.{u} SimplicialSpace.{u} :=
    SimplicialSpace.isLocallyPresentable
  let _ : HasCardinalFilteredColimits.{u} SimplicialSpace.{u} μ :=
    { hasColimitsOfShape := fun _ _ _ => by infer_instance }
  let _ : ∀ i : LocalGenerators.J.{u}.toSet,
      Mono (LocalGenerators.J.{u}.homFamily i) := fun i =>
    (LocalGenerators.le_monomorphisms_inf_rezkWeakEquivalences _ i.2).1
  let _ : (SmallObject.iteration LocalGenerators.J.{u} κ).IsCardinalAccessible μ :=
    originalIteration_isCardinalAccessible LocalGenerators.J.{u} κ μ
  rw [SmallObject.canonical_terminal_middle_eq_terminalIteration
    LocalGenerators.J.{u} κ]
  exact SmallObject.terminalIteration_isCardinalAccessible
    LocalGenerators.J.{u} κ μ

/-- The exact canonical local replacement at an eligible `κ` preserves
pullbacks, monomorphisms, and filtered colimits at one common regular endpoint
presentability cardinal `μ > ℵ₀`. The result retains the whole middle functor,
both native factors, their factorization, and the inverse-right-unit
normalization. -/
theorem canonical_localReplacement_preservation
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ] :
    let t := terminal.fromNatTrans SimplicialSpace.{u}
    let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
    let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
    ∃ (μ : Cardinal.{u}) (hμ : Fact μ.IsRegular),
      letI : Fact μ.IsRegular := hμ
      ℵ₀ < μ ∧
        (∀ i : LocalGenerators.J.{u}.toSet,
          IsCardinalPresentable.{u} i.1.left μ ∧
            IsCardinalPresentable.{u} i.1.right μ) ∧
        r.Z = SmallObject.terminalIteration LocalGenerators.J.{u} κ ∧
        (∀ X : SimplicialSpace.{u},
          r.i.app X =
              SmallObject.ιObj LocalGenerators.J.{u} κ (terminal.from X) ∧
            r.p.app X =
              SmallObject.πObj LocalGenerators.J.{u} κ (terminal.from X) ∧
            r.i.app X ≫ r.p.app X = terminal.from X ∧
            r.p.app X ≫
                ((SmallObject.ιIteration LocalGenerators.J.{u} κ).app
                  ((terminal.arrowFunctor SimplicialSpace.{u}).obj X)).right =
              ((SmallObject.iteration LocalGenerators.J.{u} κ).obj
                ((terminal.arrowFunctor SimplicialSpace.{u}).obj X)).hom) ∧
        PreservesLimitsOfShape WalkingCospan r.Z ∧
        r.Z.PreservesMonomorphisms ∧
        r.Z.IsCardinalAccessible μ := by
  dsimp only
  let t := terminal.fromNatTrans SimplicialSpace.{u}
  let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
  let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
  let _ : IsLocallyPresentable.{u} SimplicialSpace.{u} :=
    SimplicialSpace.isLocallyPresentable
  obtain ⟨μ, hμ, hωμ, _hfixed, hends⟩ :=
    SmallObject.original_endpoints_have_common_presentability_cardinal
      LocalGenerators.J.{u} κ PUnit
  let _ : Fact μ.IsRegular := hμ
  let _ : ∀ i : LocalGenerators.J.{u}.toSet,
      IsCardinalPresentable.{u} i.1.left μ := fun i => (hends i).1
  let _ : ∀ i : LocalGenerators.J.{u}.toSet,
      IsCardinalPresentable.{u} i.1.right μ := fun i => (hends i).2
  have hEq : r.Z =
      SmallObject.terminalIteration LocalGenerators.J.{u} κ :=
    SmallObject.canonical_terminal_middle_eq_terminalIteration
      LocalGenerators.J.{u} κ
  have hFactors :
      ∀ X : SimplicialSpace.{u},
        r.i.app X =
            SmallObject.ιObj LocalGenerators.J.{u} κ (terminal.from X) ∧
          r.p.app X =
            SmallObject.πObj LocalGenerators.J.{u} κ (terminal.from X) ∧
          r.i.app X ≫ r.p.app X = terminal.from X ∧
          r.p.app X ≫
              ((SmallObject.ιIteration LocalGenerators.J.{u} κ).app
                ((terminal.arrowFunctor SimplicialSpace.{u}).obj X)).right =
            ((SmallObject.iteration LocalGenerators.J.{u} κ).obj
              ((terminal.arrowFunctor SimplicialSpace.{u}).obj X)).hom := by
    intro X
    refine ⟨SmallObject.canonical_terminal_middle_unit_app
      LocalGenerators.J.{u} κ X,
      SmallObject.canonical_terminal_middle_factor_app
        LocalGenerators.J.{u} κ X, ?_, ?_⟩
    · simpa only [NatTrans.comp_app, t, terminal.fromNatTrans_app] using
        congr_app r.fac X
    · exact SmallObject.canonical_terminal_middle_factor_app_ιIteration_right
        LocalGenerators.J.{u} κ X
  have hPullbacks :
      PreservesLimitsOfShape WalkingCospan r.Z :=
    canonical_localReplacement_preservesPullbacks κ
  have hMonomorphisms :
      r.Z.PreservesMonomorphisms :=
    canonical_localReplacement_preservesMonomorphisms κ
  have hAccessible :
      r.Z.IsCardinalAccessible μ :=
    canonical_localReplacement_isCardinalAccessible κ μ
  refine ⟨μ, hμ, hωμ, hends, hEq, hFactors, ?_, ?_, ?_⟩
  · exact hPullbacks
  · exact hMonomorphisms
  · exact hAccessible

end SimplicialSpace
