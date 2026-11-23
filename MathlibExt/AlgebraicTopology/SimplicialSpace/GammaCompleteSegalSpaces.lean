/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.GammaMapping
import MathlibExt.AlgebraicTopology.Quasicategory.CoreFibration
import MathlibExt.AlgebraicTopology.Quasicategory.CoreTrivialFibration
import MathlibExt.AlgebraicTopology.Quasicategory.EquivalenceLiftingIsofibration
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.FunctionRestriction
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.PrismSkeletal
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.ShuffleFilling
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalSpaces
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyGenerators
import MathlibExt.AlgebraicTopology.SimplicialSpace.BoundaryMatching
import MathlibExt.AlgebraicTopology.SimplicialSpace.SpineInnerAnodyne
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CoherentIsoEndpoint

/-!
# The canonical Gamma diagram is a complete Segal space

Use the actual canonical Gamma mapping comparison, native core restriction
fibrations, the original matching maps, all spines in degrees at least two
and the full coherent walking-isomorphism endpoint. No mapping callback or
Gamma fibrancy/model premise is required. Original-unit weakness is separate.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open CategoryTheory.MorphismProperty MonoidalClosed
open scoped Simplicial SimplicialSpace.Inner SSet.modelCategoryQuillen

universe u

namespace SSet.Rezk

private abbrev gamma (Q : SSet.{u}) : SimplicialSpace.{u} :=
  SimplicialSpace.ofSimplicialObject.obj (gammaDiagram.obj Q)

private abbrev discrete (A : SSet.{u}) : SimplicialSpace.{u} :=
  SimplicialSpace.ofSimplicialObject.obj (simplicialSpaceDiscrete.obj A)


private lemma coreRestriction_fibration {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (Q : SSet.{u}) [SSet.Quasicategory Q] :
    HomotopicalAlgebra.Fibration (SSet.core.map ((pre i).app Q)) := by
  let : SSet.InnerFibration ((pre i).app Q) := SSet.innerFibration_pre_app_of_mono i Q
  let : SSet.HasStrictEquivalenceLifting ((pre i).app Q) :=
    (SSet.isIsofibration_hoFunctor_map_iff_hasStrictEquivalenceLifting _).mp
      (SSet.hoFunctor_pre_isIsofibration_of_mono_of_shuffleCell i Q
        (fun n => SSet.shuffleHornZeroCellExtension_of_quasicategory n Q)
        (fun n => SSet.shuffleHornTwoCellExtension_of_quasicategory n Q))
  exact SSet.fibration_core_map_of_hasStrictEquivalenceLifting _

private lemma coreRestriction_mem_rlp_monomorphisms {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : SSet.categoricalEquivalences i) (Q : SSet.{u}) [SSet.Quasicategory Q] :
    (monomorphisms SSet.{u}).rlp (SSet.core.map ((pre i).app Q)) := by
  have hp := SSet.categoricalFibrations_and_categoricalEquivalences_pre_app_of_mono i hi Q
  have hI : SSet.modelCategoryQuillen.I.rlp ((pre i).app Q) :=
    (SSet.categoricalFibrations_and_categoricalEquivalences_iff _).mp hp
  have hMono : (monomorphisms SSet.{u}).rlp ((pre i).app Q) := by
    rw [SSet.rlp_monomorphisms]
    exact hI
  exact SSet.core_map_mem_rlp_monomorphisms hMono

private lemma realizationWeak_of_rlp_monomorphisms {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : (monomorphisms SSet.{u}).rlp p) : SSet.realizationWeakEquivalences p := by
  let : HomotopicalAlgebra.Fibration p :=
    (SSet.modelCategoryQuillen.fibration_iff _).mpr
      ((antitone_rlp SSet.modelCategoryQuillen.J_le_monomorphisms) _ hp)
  apply (SSet.modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration p).mp
  rw [← SSet.rlp_monomorphisms]
  exact hp

private lemma coreRestriction_realizationWeak {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : SSet.categoricalEquivalences i) (Q : SSet.{u}) [SSet.Quasicategory Q] :
    SSet.realizationWeakEquivalences (SSet.core.map ((pre i).app Q)) :=
  realizationWeak_of_rlp_monomorphisms (coreRestriction_mem_rlp_monomorphisms i hi Q)


/-- The actual inner mapping object out of the discrete embedding. -/
private abbrev gammaInnerMap (Q A : SSet.{u}) : SSet.{u} :=
  (SimplicialSpace.innerHomFunctor.obj (op (discrete A))).obj (gamma Q)

/-- Precomposition retains the original discrete map in every degree. -/
private abbrev gammaPrecomp (Q : SSet.{u}) {A B : SSet.{u}} (i : A ⟶ B) :
    gammaInnerMap Q B ⟶ gammaInnerMap Q A :=
  (SimplicialSpace.innerHomFunctor.map
    (SimplicialSpace.ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map i)).op).app
      (gamma Q)

section

variable (Q : SSet.{u}) [SSet.Quasicategory Q]

/-- The entire original source-restriction square is retained. -/
private def gammaPrecompArrowIso {A B : SSet.{u}} (i : A ⟶ B) :
    Arrow.mk (gammaPrecomp Q i) ≅ Arrow.mk (SSet.core.map ((pre i).app Q)) :=
  Arrow.isoMk (gammaMappingIso B Q) (gammaMappingIso A Q) (gammaMappingIso_naturality_source i).symm

private lemma gammaPrecomp_mem_J_rlp {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    SSet.modelCategoryQuillen.J.rlp (gammaPrecomp Q i) := by
  have hp : SSet.modelCategoryQuillen.J.rlp (SSet.core.map ((pre i).app Q)) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp (coreRestriction_fibration i Q)
  exact ((SSet.modelCategoryQuillen.J.rlp).arrow_mk_iso_iff
    (gammaPrecompArrowIso Q i)).mpr hp

private lemma gammaPrecomp_realizationWeak {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : SSet.categoricalEquivalences i) :
    SSet.realizationWeakEquivalences (gammaPrecomp Q i) := by
  have hp := coreRestriction_realizationWeak i hi Q
  exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
    (gammaPrecompArrowIso Q i)).mpr hp

private lemma innerHom_preservesTerminal (X : SimplicialSpace.{u}) :
    PreservesLimitsOfShape (Discrete PEmpty.{1})
      (SimplicialSpace.innerHomFunctor.obj (op X)) := by
  let : (SimplicialSpace.innerHomFunctor.obj (op X)).IsRightAdjoint :=
    ⟨_, ⟨SimplicialSpace.innerTensorHomAdjunction₂.adj X⟩⟩
  infer_instance

/-- Native Reedy fibrancy uses every original outer boundary and inner horn. -/
private lemma gamma_reedyFibrant :
    let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
    IsFibrant (gamma Q) := by
  let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  rw [HomotopicalAlgebra.isFibrant_iff, HomotopicalAlgebra.fibration_iff,
    ← SimplicialSpace.ReedyGeneratingFamilies.J_rlp_eq_fibrations]
  intro X Y i hi
  change MorphismProperty.ofHoms
    (fun h : SimplicialSpace.ReedyGeneratingFamilies.HornIndex =>
      (SimplicialSpace.ReedyGeneratingFamilies.hornFamily h).hom) i at hi
  cases hi with
  | mk h =>
    let m := h.1
    let n := h.2.1
    let j := h.2.2
    let : NeZero n.1 := ⟨by omega⟩
    let _ := innerHom_preservesTerminal (discrete (SSet.boundary.{u} m : SSet.{u}))
    let _ := innerHom_preservesTerminal (discrete (Δ[m] : SSet.{u}))
    let q := Functor.PullbackObjObj.ofIsTerminal SimplicialSpace.innerHomFunctor
      (SimplicialSpace.ReedyGeneratingFamilies.outerBoundaryMap m)
      (terminal.from (gamma Q)) terminalIsTerminal
    have hp : HasLiftingProperty (SSet.horn.{u} n.1 j).ι q.π := by
      change HasLiftingProperty (SSet.horn.{u} n.1 j).ι
        (gammaPrecomp Q (SSet.boundary.{u} m).ι)
      exact gammaPrecomp_mem_J_rlp Q _ _
        (SSet.modelCategoryQuillen.horn_ι_mem_J n.1 j)
    exact (SimplicialSpace.innerTensorHomAdjunction₂.hasLiftingProperty_iff
      (SimplicialSpace.ReedyGeneratingFamilies.hornPushout m n j) q).mpr hp

/-- The two original boundary/Yoneda comparison maps retain the matching arrow. -/
private def gammaMatchingArrowIso (n : ℕ) :
    Arrow.mk (SimplicialObject.matchingMap (gamma Q).diagram n) ≅
      Arrow.mk (SSet.core.map ((pre (SSet.boundary.{u} n).ι).app Q)) := by
  let e : Arrow.mk (gammaPrecomp Q (SSet.boundary.{u} n).ι) ≅
      Arrow.mk (SimplicialObject.matchingMap (gamma Q).diagram n) :=
    Arrow.isoMk (SSet.Rezk.pointwiseYonedaIso n (gamma Q).diagram)
      ((SimplicialSpace.boundaryMatchingIso n).app (gamma Q))
      (SimplicialSpace.boundaryMatchingIso_boundary n (gamma Q)).symm
  exact e.symm ≪≫ gammaPrecompArrowIso Q _

private lemma gamma_matching_fibration (n : ℕ) :
    HomotopicalAlgebra.Fibration (SimplicialObject.matchingMap (gamma Q).diagram n) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  have h : SSet.modelCategoryQuillen.J.rlp
      (SSet.core.map ((pre (SSet.boundary.{u} n).ι).app Q)) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp (coreRestriction_fibration _ Q)
  exact ((SSet.modelCategoryQuillen.J.rlp).arrow_mk_iso_iff
    (gammaMatchingArrowIso Q n)).mpr h

omit [SSet.Quasicategory Q] in
/-- Every original proper-face projection is unchanged by the native boundary comparison. -/
private lemma gamma_boundary_projections (n : ℕ) (a : SimplicialObject.matchingIndex n) :
    ((SimplicialSpace.boundaryMatchingIso n).app (gamma Q)).hom ≫
      SimplicialObject.matchingπ (gamma Q).diagram n a =
      (SimplicialSpace.innerHomFunctor.map (SimplicialSpace.boundaryFaceMap a).op).app
        (gamma Q) ≫
      (SSet.Rezk.pointwiseYonedaIso a.obj.right.unop.len (gamma Q).diagram).hom :=
  SimplicialSpace.boundaryMatchingIso_app_π n (gamma Q) a

omit [SSet.Quasicategory Q] in
private lemma gamma_fullE_section :
    gammaPrecomp Q SSet.coherentIso.toDeltaZero ≫
      gammaPrecomp Q SSet.coherentIso.endpointInclusion =
        𝟙 (gammaInnerMap Q (Δ[0] : SSet.{u})) := by
  dsimp only [gammaPrecomp]
  rw [← NatTrans.comp_app, ← SimplicialSpace.innerHomFunctor.map_comp, ← op_comp,
    ← SimplicialSpace.ofSimplicialObject.map_comp, ← SSet.simplicialSpaceDiscrete.map_comp,
    SSet.coherentIso.endpointInclusion_comp_toDeltaZero]
  simp only [SSet.simplicialSpaceDiscrete.map_id, SimplicialSpace.ofSimplicialObject.map_id,
    op_id, SimplicialSpace.innerHomFunctor.map_id, NatTrans.id_app]

private lemma gamma_fullE_projection_realizationWeak :
    SSet.realizationWeakEquivalences (gammaPrecomp Q SSet.coherentIso.toDeltaZero) := by
  let : Mono SSet.coherentIso.endpointInclusion :=
    SSet.stdSimplex.isTerminalObj₀.mono_from _
  have hi := gammaPrecomp_realizationWeak Q SSet.coherentIso.endpointInclusion
    SSet.categoricalEquivalences.coherentIso_endpointInclusion
  apply SSet.realizationWeakEquivalences.of_postcomp _ _ hi
  rw [gamma_fullE_section Q]
  exact SSet.realizationWeakEquivalences.id_mem _

/-- The existing core/function Gamma diagram is a complete Segal space. -/
theorem gammaDiagram_completeSegalSpaces :
    SimplicialSpace.completeSegalSpaces
      (SimplicialSpace.ofSimplicialObject.obj (gammaDiagram.obj Q)) := by
  let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  constructor
  · exact gamma_reedyFibrant Q
  · intro a
    cases a with
    | inl n =>
      have hi := SSet.Rezk.monomorphisms_inf_categoricalEquivalences_spineSubcomplex_ι
        n.1 n.2
      exact gammaPrecomp_realizationWeak Q (SSet.Rezk.spineSubcomplex n.1).ι hi.2
    | inr p =>
      let : Mono SSet.coherentIso.endpointInclusion :=
        SSet.stdSimplex.isTerminalObj₀.mono_from _
      exact gammaPrecomp_realizationWeak Q SSet.coherentIso.endpointInclusion
        SSet.categoricalEquivalences.coherentIso_endpointInclusion

end

end SSet.Rezk
