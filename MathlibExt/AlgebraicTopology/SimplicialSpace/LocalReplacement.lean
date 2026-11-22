/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalGenerationCardinal
import MathlibExt.CategoryTheory.NatTrans.TerminalArrow
import MathlibExt.AlgebraicTopology.SimplicialSpace.AuxiliaryGeneratorProperties
import MathlibExt.AlgebraicTopology.SimplicialSpace.TerminalLocality
import MathlibExt.AlgebraicTopology.SimplicialSpace.WeakCobaseChange
import MathlibExt.AlgebraicTopology.SimplicialSpace.WeakCoproducts
import MathlibExt.AlgebraicTopology.SimplicialSpace.WeakTransfiniteComposition
import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalWhitehead

/-!
# Functorial local-object replacement

One working-universe regular cardinal controls the full literal auxiliary family.
The returned native small-object and functor-category factorization data keep
that same cardinal and the original terminal natural transformation. Their
middle functor, unit and terminal right factor preserve every original map.
The unit is monic and Rezk weak against every same-universe complete Segal space;
the middle objects are complete Segal spaces.

Source: Rezk, *A model for the homotopy theory of homotopy theory*, Proposition 9.1
and Section 12. The canonical data and cellular-class identity use the native
Mathlib small-object and functorial-factorization APIs.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra
namespace SimplicialSpace

private abbrev replacementMonoWeak : MorphismProperty SimplicialSpace.{u} :=
  monomorphisms SimplicialSpace.{u} ⊓ rezkWeakEquivalences.{u}

private theorem auxiliaryLeft_le_replacementMonoWeak (κ : Cardinal.{u})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ] :
    LocalGenerators.J.{u}.rlp.llp ≤ replacementMonoWeak.{u} := by
  -- Use the actual proved same-universe closure classes, without caller premises.
  let _ : replacementMonoWeak.{u}.IsStableUnderCoproducts.{u} :=
    monomorphisms_inf_rezkWeakEquivalences_isStableUnderCoproducts
  let _ : replacementMonoWeak.{u}.IsStableUnderTransfiniteComposition.{u} :=
    monomorphisms_inf_rezkWeakEquivalences_isStableUnderTransfiniteComposition
  let _ : replacementMonoWeak.{u}.IsStableUnderCobaseChange :=
    monomorphisms_inf_rezkWeakEquivalences_isStableUnderCobaseChange
  let _ : replacementMonoWeak.{u}.IsStableUnderRetracts := inferInstance
  rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument' LocalGenerators.J.{u} κ]
  rw [retracts_le_iff]
  have hCells : (coproducts.{u} LocalGenerators.J.{u}).pushouts ≤
      replacementMonoWeak.{u} :=
    pushouts_le_iff.mpr
      (coproducts_le_iff.mpr LocalGenerators.le_monomorphisms_inf_rezkWeakEquivalences)
  exact le_trans
    ((transfiniteCompositionsOfShape_monotone (J := κ.ord.ToType)) hCells)
    (replacementMonoWeak.{u}.transfiniteCompositionsOfShape_le κ.ord.ToType)

/-- The actual native auxiliary SOA, evaluated once on the original terminal transformation. -/
theorem exists_functorial_localReplacement :
    let t := terminal.fromNatTrans SimplicialSpace.{u}
    ∃ (κ : Cardinal.{u}) (hκ : Fact κ.IsRegular) (hbot : OrderBot κ.ord.ToType),
      letI : Fact κ.IsRegular := hκ
      letI : OrderBot κ.ord.ToType := hbot
      IsCardinalLocallyPresentable SimplicialSpace.{u} κ ∧
        ∃ (hJ : LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ),
          letI : LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ := hJ
          ∃ (d : FunctorialFactorizationData
                LocalGenerators.J.{u}.rlp.llp LocalGenerators.J.{u}.rlp)
            (r : MapFactorizationData
                (LocalGenerators.J.{u}.rlp.llp.functorCategory SimplicialSpace.{u})
                (LocalGenerators.J.{u}.rlp.functorCategory SimplicialSpace.{u}) t),
            d = SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ ∧
            r = (d.functorCategory SimplicialSpace.{u}).factorizationData t ∧
            ∀ X : SimplicialSpace.{u},
              Mono (r.i.app X) ∧ rezkWeakEquivalences (r.i.app X) ∧
                completeSegalSpaces (r.Z.obj X) := by
  dsimp only
  obtain ⟨κ, hκ, hbot, hC, _, _, hJ⟩ := LocalGenerators.exists_common_smallness_cardinal
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hbot
  let _ : LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ := hJ
  let t := terminal.fromNatTrans SimplicialSpace.{u}
  let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
  let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
  refine ⟨κ, hκ, hbot, hC, hJ, d, r, rfl, rfl, ?_⟩
  intro X
  have hUnit : replacementMonoWeak.{u} (r.i.app X) :=
    auxiliaryLeft_le_replacementMonoWeak κ (r.i.app X) (r.hi X)
  refine ⟨hUnit.1, hUnit.2, ?_⟩
  apply (LocalGenerators.terminal_rlp_iff_completeSegalSpaces (r.Z.obj X)).1
  have hterminal : r.p.app X = terminal.from (r.Z.obj X) :=
    terminalIsTerminal.hom_ext _ _
  rw [← hterminal]
  exact r.hp X

/-- The actual canonical auxiliary SOA detects the original weak class through
its same middle functor and the existing named Reedy weak class. -/
theorem canonical_localReplacement_weak_detection (κ : Cardinal.{u})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    let t := terminal.fromNatTrans SimplicialSpace.{u}
    let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
    let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    rezkWeakEquivalences f ↔ WeakEquivalence (r.Z.map f) := by
  dsimp only
  let t := terminal.fromNatTrans SimplicialSpace.{u}
  let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
  let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  have hUnit (A : SimplicialSpace.{u}) : rezkWeakEquivalences (r.i.app A) :=
    (auxiliaryLeft_le_replacementMonoWeak κ (r.i.app A) (r.hi A)).2
  have hCSS (A : SimplicialSpace.{u}) : completeSegalSpaces (r.Z.obj A) := by
    apply (LocalGenerators.terminal_rlp_iff_completeSegalSpaces (r.Z.obj A)).1
    have hTerminal : r.p.app A = terminal.from (r.Z.obj A) :=
      terminalIsTerminal.hom_ext _ _
    rw [← hTerminal]
    exact r.hp A
  have hNat : f ≫ r.i.app Y = r.i.app X ≫ r.Z.map f := r.i.naturality f
  have hWeak : rezkWeakEquivalences f ↔ rezkWeakEquivalences (r.Z.map f) := by
    calc
      rezkWeakEquivalences f ↔ rezkWeakEquivalences (f ≫ r.i.app Y) :=
        (rezkWeakEquivalences.postcomp_iff f (r.i.app Y) (hUnit Y)).symm
      _ ↔ rezkWeakEquivalences (r.i.app X ≫ r.Z.map f) := by rw [hNat]
      _ ↔ rezkWeakEquivalences (r.Z.map f) :=
        rezkWeakEquivalences.precomp_iff (r.i.app X) (r.Z.map f) (hUnit X)
  constructor
  · intro hf
    exact (rezkWeak_iff_reedyWeak_of_completeSegalSpaces
      (r.Z.map f) (hCSS X) (hCSS Y)).1 (hWeak.1 hf)
  · intro hf
    have hQ : rezkWeakEquivalences (r.Z.map f) :=
      reedyWeak_le_rezkWeak (r.Z.map f)
        ((HomotopicalAlgebra.weakEquivalence_iff _).1 hf)
    exact hWeak.2 hQ

end SimplicialSpace
