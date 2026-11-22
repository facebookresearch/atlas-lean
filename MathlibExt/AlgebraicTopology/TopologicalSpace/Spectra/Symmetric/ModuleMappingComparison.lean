/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.EnrichedRightMappingCategory
public import MathlibExt.CategoryTheory.Enriched.EnrichedHomTransport
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.RightModuleMapping
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.RightModuleEnrichment
public import MathlibExt.Topology.Category.PointedCGWH.Separator

/-!
# Enriched mapping objects for symmetric sphere modules

Identifies compatible module morphisms with the product/equalizer mapping object. The
enriched-category comparison retains identities, composition, parameter maps and every operator
component of the module presentation.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.SymmetricModuleMappingComparison

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  sphereSequenceMonObj sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction

/-- The symmetric right sphere modules in the mapping object comparison. -/
abbrev Carrier := SymmetricRightModulePresentation.RightSphereModule.{u, v}

/-- All original full J Hom actions and complete actual right coefficient actions. -/
abbrev actualData : Enriched.EnrichedRightMappingCategory.Data
    (V := PointedCGWH.{u, v}) (I := SymmetricOperatorIndex.{u, v})
      (A := Operad.SmallFinBijGroupoid) Carrier.{u, v} where
  diagram M :=
    ((SymmetricRightModulePresentation.rightModuleToOperator.{u, v}).obj M).toEnrichedFunctor
  coefficient := sphereSequence.{u, v}.functor.obj
  rightIndex n a :=
    symmetricOperatorObj.{u, v} ((show Operad.SmallFinBijGroupoid from n.asIndex) ⊗ a)
  right M n a :=
    SymmetricRightModulePresentation.pairAction M (show Operad.SmallFinBijGroupoid from n.asIndex) a

private theorem pointedSmallLimits : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} := by
  let _ : HasLimitsOfSize.{v, v} CGWH.{u, v} := CGWH.limits.instHasLimitsOfSize
  let _ : HasLimitsOfSize.{v, v} PointedCGWH.{u, v} := by
    change HasLimitsOfSize.{v, v} (Under CGWH.point.{u, v})
    infer_instance
  exact hasLimitsOfSizeShrink.{0, 0} PointedCGWH.{u, v}

instance fullObjectProducts : ∀ M N : Carrier.{u, v},
    HasProduct (Enriched.EnrichedRightMappingCategory.system actualData M N).objects :=
  fun M N => by
    let _ : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} := pointedSmallLimits
    infer_instance

instance fullRelationProducts : ∀ M N : Carrier.{u, v},
    HasProduct (Enriched.EnrichedRightMappingCategory.system actualData M N).relations :=
  fun M N => by
    let _ : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} := pointedSmallLimits
    infer_instance

instance fullEqualizers : ∀ M N : Carrier.{u, v}, HasEqualizer
    (Enriched.ProductRelationMapping.leftMap
      (Enriched.EnrichedRightMappingCategory.system actualData M N))
    (Enriched.ProductRelationMapping.rightMap
      (Enriched.EnrichedRightMappingCategory.system actualData M N)) :=
  fun M N => by
    let _ : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} := pointedSmallLimits
    infer_instance

/-- The original native J tagging retains the entire original degree. -/
theorem index_eta (n : SymmetricOperatorIndex.{u, v}) :
    symmetricOperatorObj.{u, v} (show Operad.SmallFinBijGroupoid from n.asIndex) = n := by
  cases n
  rfl

/-- The whole full-Hom functor map retains the entire original module component. -/
theorem forward_component {M N : Carrier.{u, v}} (f : M ⟶ N)
    (n : SymmetricOperatorIndex.{u, v}) :
    EnrichedFunctorCat.component (SymmetricRightModulePresentation.rightModuleToOperator.map f) n =
      f.hom.natTrans.app (show Operad.SmallFinBijGroupoid from n.asIndex) := by
  cases n
  exact SymmetricRightModulePresentation.rightModuleToOperator_component f _

private def forwardFullyFaithful :
    SymmetricRightModulePresentation.rightModuleToOperator.{u, v}.FullyFaithful := by
  change
    SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor.FullyFaithful
  exact SymmetricRightModulePresentation.rightModuleOperatorEquivalence.fullyFaithfulFunctor

/-- Every whole original module morphism gives the full J-compatible transformation. -/
def toFullCompatible {M N : Carrier.{u, v}} (f : M ⟶ N) :
    Enriched.EnrichedRightActionMapping.CompatibleHom
      (Enriched.EnrichedRightMappingCategory.mappingData actualData M N) :=
  ⟨SymmetricRightModulePresentation.rightModuleToOperator.map f, fun n a => by
    change SymmetricRightModulePresentation.pairAction M
        (show Operad.SmallFinBijGroupoid from n.asIndex) a ≫
      EnrichedFunctorCat.component (SymmetricRightModulePresentation.rightModuleToOperator.map f)
        (actualData.rightIndex n a) =
      (EnrichedFunctorCat.component
        (SymmetricRightModulePresentation.rightModuleToOperator.map f) n ▷
        sphereSequence.{u, v}.functor.obj a) ≫
          SymmetricRightModulePresentation.pairAction N
            (show Operad.SmallFinBijGroupoid from n.asIndex) a
    rw [forward_component, forward_component]
    exact SymmetricRightModuleMapping.pairAction_map f _ a⟩

/-- Every full original compatible transformation recovers the actual module morphism. -/
@[no_expose]
def ofFullCompatible {M N : Carrier.{u, v}}
    (f : Enriched.EnrichedRightActionMapping.CompatibleHom
      (Enriched.EnrichedRightMappingCategory.mappingData actualData M N)) : M ⟶ N :=
  (forwardFullyFaithful).preimage f.val

/-- Whole original module morphisms are recovered. -/
theorem of_toFullCompatible {M N : Carrier.{u, v}} (f : M ⟶ N) :
    ofFullCompatible (toFullCompatible f) = f := by
  change (forwardFullyFaithful).preimage
    (SymmetricRightModulePresentation.rightModuleToOperator.map f) = f
  exact (forwardFullyFaithful).preimage_map f

/-- Whole full-Hom compatible transformations are recovered. -/
theorem to_ofFullCompatible {M N : Carrier.{u, v}}
    (f : Enriched.EnrichedRightActionMapping.CompatibleHom
      (Enriched.EnrichedRightMappingCategory.mappingData actualData M N)) :
    toFullCompatible (ofFullCompatible f) = f := by
  apply Subtype.ext
  change SymmetricRightModulePresentation.rightModuleToOperator.map
    ((forwardFullyFaithful).preimage f.val) = f.val
  exact (forwardFullyFaithful).map_preimage f.val

/-- The actual full source morphism correspondence has both complete original inverses. -/
def fullCompatibleHomEquiv (M N : Carrier.{u, v}) : (M ⟶ N) ≃
    Enriched.EnrichedRightActionMapping.CompatibleHom
      (Enriched.EnrichedRightMappingCategory.mappingData actualData M N) where
  toFun := toFullCompatible
  invFun := ofFullCompatible
  left_inv := of_toFullCompatible
  right_inv := to_ofFullCompatible

/-- The full enriched relation presentation uses its actual original mapping object. -/
abbrev fullHom (M N : Carrier.{u, v}) :=
  Enriched.EnrichedRightMappingCategory.Hom actualData M N

/-- The projection from the full mapping object to the component internal Hom. -/
abbrev fullπ (M N : Carrier.{u, v}) (n : SymmetricOperatorIndex.{u, v}) :=
  Enriched.EnrichedRightMappingCategory.π actualData M N n

/-- Actual module morphisms are precisely all unit-points of the full source mapping object. -/
@[no_expose]
def fullHomEquiv (M N : Carrier.{u, v}) : (M ⟶ N) ≃
    (𝟙_ PointedCGWH.{u, v} ⟶ fullHom M N) :=
  (fullCompatibleHomEquiv M N).trans
    (Enriched.EnrichedRightMappingCategory.compatibleHomEquiv actualData M N)

/-- Every entire original component is retained in the full mapping representation. -/
theorem fullHomEquiv_π {M N : Carrier.{u, v}} (f : M ⟶ N)
    (n : SymmetricOperatorIndex.{u, v}) :
    fullHomEquiv M N f ≫ fullπ M N n =
      eHomEquiv PointedCGWH.{u, v}
        (f.hom.natTrans.app (show Operad.SmallFinBijGroupoid from n.asIndex)) :=
  (Enriched.EnrichedRightMappingCategory.compatibleHomEquiv_π actualData M N
    (toFullCompatible f) n).trans
      (congrArg (eHomEquiv PointedCGWH.{u, v}) (forward_component f n))

private theorem originalPoint_π (M N : Carrier.{u, v})
    (p : 𝟙_ PointedCGWH.{u, v} ⟶ SymmetricRightModuleMapping.Hom M N)
    (i : Operad.SmallFinBijGroupoid) :
    p ≫ SymmetricRightModuleMapping.π M N i = eHomEquiv PointedCGWH.{u, v}
      (((SymmetricRightModuleMapping.homEquiv M N).symm p).hom.natTrans.app i) :=
  (congrArg (fun z => z ≫ SymmetricRightModuleMapping.π M N i)
    ((SymmetricRightModuleMapping.homEquiv M N).apply_symm_apply p)).symm.trans
      (SymmetricRightModuleMapping.homEquiv_π
        ((SymmetricRightModuleMapping.homEquiv M N).symm p) i)

private theorem fullPoint_π (M N : Carrier.{u, v})
    (p : 𝟙_ PointedCGWH.{u, v} ⟶ fullHom M N) (i : Operad.SmallFinBijGroupoid) :
    p ≫ fullπ M N (symmetricOperatorObj i) = eHomEquiv PointedCGWH.{u, v}
      (((fullHomEquiv M N).symm p).hom.natTrans.app i) :=
  (congrArg (fun z => z ≫ fullπ M N (symmetricOperatorObj i))
    ((fullHomEquiv M N).apply_symm_apply p)).symm.trans
      (fullHomEquiv_π ((fullHomEquiv M N).symm p) (symmetricOperatorObj i))

/-- Every complete original parameter projection satisfies all full source J relations. -/
def toFullFamily (M N : Carrier.{u, v}) :
    Enriched.EnrichedRightActionMapping.Family
      (Enriched.EnrichedRightMappingCategory.mappingData actualData M N)
      (SymmetricRightModuleMapping.Hom M N) where
  app n := SymmetricRightModuleMapping.π M N
    (show Operad.SmallFinBijGroupoid from n.asIndex)
  condition r := by
    apply isSeparator_tensorUnit.def
    intro p
    let f := (SymmetricRightModuleMapping.homEquiv M N).symm p
    let q := Enriched.EnrichedRightActionMapping.compatibleToFamily
      (Enriched.EnrichedRightMappingCategory.mappingData actualData M N) (toFullCompatible f)
    have apps : ∀ n : SymmetricOperatorIndex.{u, v},
        p ≫ SymmetricRightModuleMapping.π M N
          (show Operad.SmallFinBijGroupoid from n.asIndex) = q.app n := by
      intro n
      exact (originalPoint_π M N p _).trans
        (congrArg (eHomEquiv PointedCGWH.{u, v}) (forward_component f n)).symm
    let s := Enriched.EnrichedRightMappingCategory.system actualData M N
    let qL := SymmetricRightModuleMapping.π M N
      (show Operad.SmallFinBijGroupoid from (s.leftIndex r).asIndex)
    let qR := SymmetricRightModuleMapping.π M N
      (show Operad.SmallFinBijGroupoid from (s.rightIndex r).asIndex)
    change p ≫ (qL ≫ s.leftComponent r) = p ≫ (qR ≫ s.rightComponent r)
    exact (Category.assoc p qL (s.leftComponent r)).symm.trans
      ((congrArg (fun z => z ≫ s.leftComponent r) (apps (s.leftIndex r))).trans
        ((q.condition r).trans
          ((congrArg (fun z => z ≫ s.rightComponent r) (apps (s.rightIndex r))).symm.trans
            (Category.assoc p qR (s.rightComponent r)))))

/-- Every full source parameter projection satisfies both entire original module relations. -/
def toOriginalFamily (M N : Carrier.{u, v}) :
    Enriched.RightActionMapping.CompatibleFamily (SymmetricRightModuleMapping.mappingData M N)
      (fullHom M N) where
  app i := fullπ M N (symmetricOperatorObj i)
  condition r := by
    apply isSeparator_tensorUnit.def
    intro p
    let f := (fullHomEquiv M N).symm p
    let q := Enriched.RightActionMapping.compatibleToFamily
      (SymmetricRightModuleMapping.mappingData M N) (SymmetricRightModuleMapping.toCompatibleHom f)
    have apps : (fun i => p ≫ fullπ M N (symmetricOperatorObj i)) = q.app :=
      funext (fun i => fullPoint_π M N p i)
    let d := SymmetricRightModuleMapping.mappingData M N
    let a := fun i => fullπ M N (symmetricOperatorObj i)
    change p ≫ Enriched.RightActionMapping.familyLeft d a r =
      p ≫ Enriched.RightActionMapping.familyRight d a r
    exact (Enriched.RightActionMapping.familyLeft_precomp d p a r).symm.trans
      ((congrArg (fun z => Enriched.RightActionMapping.familyLeft d z r) apps).trans
        ((q.condition r).trans
          ((congrArg (fun z => Enriched.RightActionMapping.familyRight d z r) apps).symm.trans
            (Enriched.RightActionMapping.familyRight_precomp d p a r))))

/-- The complete continuous comparison lifts the actual original parameter family. -/
@[no_expose]
def toFull (M N : Carrier.{u, v}) : SymmetricRightModuleMapping.Hom M N ⟶ fullHom M N :=
  (Enriched.EnrichedRightMappingCategory.parameterEquiv actualData M N
    (SymmetricRightModuleMapping.Hom M N)).symm (toFullFamily M N)

/-- The complete continuous inverse lifts both actual original module relation families. -/
@[no_expose]
def toOriginal (M N : Carrier.{u, v}) : fullHom M N ⟶ SymmetricRightModuleMapping.Hom M N :=
  (SymmetricRightModuleMapping.parameterEquiv M N (fullHom M N)).symm (toOriginalFamily M N)

/-- Every complete original degree projection is retained by the full continuous comparison. -/
@[reassoc]
theorem toFull_π (M N : Carrier.{u, v}) (n : SymmetricOperatorIndex.{u, v}) :
    toFull M N ≫ fullπ M N n = SymmetricRightModuleMapping.π M N
      (show Operad.SmallFinBijGroupoid from n.asIndex) :=
  Enriched.EnrichedRightMappingCategory.parameterEquiv_symm_π actualData M N
    (SymmetricRightModuleMapping.Hom M N) (toFullFamily M N) n

/-- Every entire inverse projection is the original actual source mapping projection. -/
@[reassoc]
theorem toOriginal_π (M N : Carrier.{u, v}) (i : Operad.SmallFinBijGroupoid) :
    toOriginal M N ≫ SymmetricRightModuleMapping.π M N i =
      fullπ M N (symmetricOperatorObj i) := by
  let e := SymmetricRightModuleMapping.parameterEquiv M N (fullHom M N)
  exact (SymmetricRightModuleMapping.parameterEquiv_app M N (fullHom M N)
    (e.symm (toOriginalFamily M N)) i).symm.trans
      (congrArg (fun q => q.app i) (e.apply_symm_apply (toOriginalFamily M N)))

private theorem original_hom_ext {M N : Carrier.{u, v}} {P : PointedCGWH.{u, v}}
    {f g : P ⟶ SymmetricRightModuleMapping.Hom M N}
    (h : ∀ i, f ≫ SymmetricRightModuleMapping.π M N i =
      g ≫ SymmetricRightModuleMapping.π M N i) : f = g := by
  apply (SymmetricRightModuleMapping.parameterEquiv M N P).injective
  apply Enriched.RightActionMapping.CompatibleFamily.ext
  funext i
  exact (SymmetricRightModuleMapping.parameterEquiv_app M N P f i).trans
    ((h i).trans (SymmetricRightModuleMapping.parameterEquiv_app M N P g i).symm)

/-- The whole original native module mapping morphism is recovered. -/
theorem toFull_toOriginal (M N : Carrier.{u, v}) : toFull M N ≫ toOriginal M N = 𝟙 _ := by
  apply original_hom_ext
  intro i
  let p := toFull M N
  let q := toOriginal M N
  let r := SymmetricRightModuleMapping.π M N i
  have h : (p ≫ q) ≫ r = r := (Category.assoc p q r).trans
    ((congrArg (fun z => p ≫ z) (toOriginal_π M N i)).trans
      (toFull_π M N (symmetricOperatorObj i)))
  exact h.trans (Category.id_comp r).symm

/-- The whole full native source mapping morphism is recovered. -/
theorem toOriginal_toFull (M N : Carrier.{u, v}) : toOriginal M N ≫ toFull M N = 𝟙 _ := by
  apply Enriched.EnrichedRightMappingCategory.hom_ext actualData
  intro n
  cases n with
  | mk n =>
    let i : Operad.SmallFinBijGroupoid := n
    let p := toOriginal M N
    let q := toFull M N
    let r := fullπ M N (symmetricOperatorObj i)
    have h : (p ≫ q) ≫ r = r := (Category.assoc p q r).trans
      ((congrArg (fun z => p ≫ z) (toFull_π M N (symmetricOperatorObj i))).trans
        (toOriginal_π M N i))
    exact h.trans (Category.id_comp r).symm

/-- The actual original module mapping space and full enriched source mapping space
are isomorphic. -/
@[no_expose]
def homIso (M N : Carrier.{u, v}) : SymmetricRightModuleMapping.Hom M N ≅ fullHom M N where
  hom := toFull M N
  inv := toOriginal M N
  hom_inv_id := toFull_toOriginal M N
  inv_hom_id := toOriginal_toFull M N

/-- The actual original module identity is its original complete mapping-space unit point. -/
@[no_expose]
def originalIdentity (M : Carrier.{u, v}) :
    𝟙_ PointedCGWH.{u, v} ⟶ SymmetricRightModuleMapping.Hom M M :=
  SymmetricRightModuleMapping.homEquiv M M (𝟙 M)

/-- Actual composition on the literal original mapping objects uses their exact identity-value
comparison with the already independently derived original relation equalizer composition. -/
@[no_expose]
def originalComposition (M N P : Carrier.{u, v}) :
    SymmetricRightModuleMapping.Hom M N ⊗ SymmetricRightModuleMapping.Hom N P ⟶
      SymmetricRightModuleMapping.Hom M P :=
  ((SymmetricRightModuleEnrichment.mappingHomIso M N).hom ⊗ₘ
    (SymmetricRightModuleEnrichment.mappingHomIso N P).hom) ≫
      Enriched.RightActionMappingCategory.composition
        SymmetricRightModuleEnrichment.actualData M N P ≫
          (SymmetricRightModuleEnrichment.mappingHomIso M P).inv

/-- Every whole original identity projection is the actual internal-Hom identity. -/
theorem originalIdentity_π (M : Carrier.{u, v}) (i : Operad.SmallFinBijGroupoid) :
    originalIdentity M ≫ SymmetricRightModuleMapping.π M M i =
      eId PointedCGWH.{u, v} (M.X.functor.obj i) :=
  (SymmetricRightModuleMapping.homEquiv_π (𝟙 M) i).trans
    (eHomEquiv_id PointedCGWH.{u, v} (M.X.functor.obj i))

/-- Actual original R-linear composition retains both whole internal-Hom component factors. -/
@[reassoc]
theorem originalComposition_π (M N P : Carrier.{u, v}) (i : Operad.SmallFinBijGroupoid) :
    originalComposition M N P ≫ SymmetricRightModuleMapping.π M P i =
      (SymmetricRightModuleMapping.π M N i ⊗ₘ SymmetricRightModuleMapping.π N P i) ≫
        eComp PointedCGWH.{u, v} (M.X.functor.obj i) (N.X.functor.obj i) (P.X.functor.obj i) := by
  let f := (SymmetricRightModuleEnrichment.mappingHomIso M N).hom ⊗ₘ
    (SymmetricRightModuleEnrichment.mappingHomIso N P).hom
  let g := Enriched.RightActionMappingCategory.composition
    SymmetricRightModuleEnrichment.actualData M N P
  let h := (SymmetricRightModuleEnrichment.mappingHomIso M P).inv
  let r := SymmetricRightModuleMapping.π M P i
  let q := Enriched.RightActionMappingCategory.π SymmetricRightModuleEnrichment.actualData M P i
  let t := Enriched.RightActionMappingCategory.π SymmetricRightModuleEnrichment.actualData M N i ⊗ₘ
    Enriched.RightActionMappingCategory.π SymmetricRightModuleEnrichment.actualData N P i
  let c := eComp PointedCGWH.{u, v} (M.X.functor.obj i) (N.X.functor.obj i) (P.X.functor.obj i)
  let s := SymmetricRightModuleMapping.π M N i ⊗ₘ SymmetricRightModuleMapping.π N P i
  have hh : h ≫ r = q := SymmetricRightModuleEnrichment.mappingHomIso_inv_π M P i
  have hg : g ≫ q = t ≫ c := Enriched.RightActionMappingCategory.composition_π
    SymmetricRightModuleEnrichment.actualData M N P i
  have hf : f ≫ t = s :=
    (tensorHom_comp_tensorHom
      (SymmetricRightModuleEnrichment.mappingHomIso M N).hom
      (SymmetricRightModuleEnrichment.mappingHomIso N P).hom
      (Enriched.RightActionMappingCategory.π SymmetricRightModuleEnrichment.actualData M N i)
      (Enriched.RightActionMappingCategory.π SymmetricRightModuleEnrichment.actualData N P i)).trans
        (congrArg₂ (fun x y => x ⊗ₘ y)
          (SymmetricRightModuleEnrichment.mappingHomIso_hom_π M N i)
          (SymmetricRightModuleEnrichment.mappingHomIso_hom_π N P i))
  change (f ≫ g ≫ h) ≫ r = s ≫ c
  calc
    _ = f ≫ g ≫ (h ≫ r) := by simp only [Category.assoc]
    _ = f ≫ g ≫ q := congrArg (fun z => f ≫ g ≫ z) hh
    _ = f ≫ (t ≫ c) := congrArg (fun z => f ≫ z) hg
    _ = (f ≫ t) ≫ c := (Category.assoc f t c).symm
    _ = _ := congrArg (fun z => z ≫ c) hf

/-- The whole continuous Hom comparison preserves the actual original module identity. -/
theorem homIso_identity (M : Carrier.{u, v}) : originalIdentity M ≫ (homIso M M).hom =
    Enriched.EnrichedRightMappingCategory.identity actualData M := by
  apply Enriched.EnrichedRightMappingCategory.hom_ext actualData
  intro n
  let i : Operad.SmallFinBijGroupoid := n.asIndex
  have h : (originalIdentity M ≫ toFull M M) ≫ fullπ M M n =
      eId PointedCGWH.{u, v} (M.X.functor.obj i) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => originalIdentity M ≫ z) (toFull_π M M n)).trans
        (originalIdentity_π M i))
  exact h.trans (Enriched.EnrichedRightMappingCategory.identity_π actualData M n).symm

/-- The whole continuous comparison preserves actual R-linear composition
on both full Hom objects. -/
theorem homIso_composition (M N P : Carrier.{u, v}) :
    originalComposition M N P ≫ (homIso M P).hom =
      ((homIso M N).hom ⊗ₘ (homIso N P).hom) ≫
        Enriched.EnrichedRightMappingCategory.composition actualData M N P := by
  apply Enriched.EnrichedRightMappingCategory.hom_ext actualData
  intro n
  let i : Operad.SmallFinBijGroupoid := n.asIndex
  let c := eComp PointedCGWH.{u, v} (M.X.functor.obj i) (N.X.functor.obj i) (P.X.functor.obj i)
  let s := SymmetricRightModuleMapping.π M N i ⊗ₘ SymmetricRightModuleMapping.π N P i
  have hl : (originalComposition M N P ≫ toFull M P) ≫ fullπ M P n = s ≫ c :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => originalComposition M N P ≫ z) (toFull_π M P n)).trans
        (originalComposition_π M N P i))
  let f := toFull M N ⊗ₘ toFull N P
  let g := Enriched.EnrichedRightMappingCategory.composition actualData M N P
  let q := fullπ M N n ⊗ₘ fullπ N P n
  have hg : g ≫ fullπ M P n = q ≫ c :=
    Enriched.EnrichedRightMappingCategory.composition_π actualData M N P n
  have hf : f ≫ q = s :=
    (tensorHom_comp_tensorHom (toFull M N) (toFull N P) (fullπ M N n) (fullπ N P n)).trans
      (congrArg₂ (fun x y => x ⊗ₘ y) (toFull_π M N n) (toFull_π N P n))
  have hr : (f ≫ g) ≫ fullπ M P n = s ≫ c :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => f ≫ z) hg).trans
        ((Category.assoc f q c).symm.trans (congrArg (fun z => z ≫ c) hf)))
  exact hl.trans hr.symm

/-- The original literal module Hom objects carry all full enriched category laws. -/
@[instance_reducible]
def literalEnrichedCategory : EnrichedCategory PointedCGWH.{u, v} Carrier.{u, v} := by
  let _ : EnrichedCategory PointedCGWH.{u, v} Carrier.{u, v} :=
    Enriched.EnrichedRightMappingCategory.enrichedCategory actualData
  exact EnrichedHomTransport.enrichedCategoryOnOriginalObjects
    SymmetricRightModuleMapping.Hom (fun M N => (homIso M N).symm)

/-- The enriched identity with the original right module mapping object. -/
@[no_expose]
def literalIdentity (M : Carrier.{u, v}) :
    𝟙_ PointedCGWH.{u, v} ⟶ SymmetricRightModuleMapping.Hom M M :=
  @eId PointedCGWH.{u, v} _ _ Carrier.{u, v} literalEnrichedCategory M

/-- The enriched composition on the original right module mapping objects. -/
@[no_expose]
def literalComposition (M N P : Carrier.{u, v}) :
    SymmetricRightModuleMapping.Hom M N ⊗ SymmetricRightModuleMapping.Hom N P ⟶
      SymmetricRightModuleMapping.Hom M P :=
  @eComp PointedCGWH.{u, v} _ _ Carrier.{u, v} literalEnrichedCategory M N P

/-- The full literal identity is the original actual module mapping point. -/
theorem literalIdentity_eq (M : Carrier.{u, v}) : literalIdentity M = originalIdentity M := by
  let q := homIso M M
  let i := originalIdentity M
  let j := Enriched.EnrichedRightMappingCategory.identity actualData M
  have h : i ≫ q.hom = j := homIso_identity M
  have hInv := congrArg (fun z => z ≫ q.inv) h
  have hCancel : (i ≫ q.hom) ≫ q.inv = i :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => i ≫ z) q.hom_inv_id).trans (Category.comp_id _))
  change j ≫ q.inv = i
  exact hInv.symm.trans hCancel

/-- The full literal composition is the actual original R-linear mapping composition. -/
theorem literalComposition_eq (M N P : Carrier.{u, v}) :
    literalComposition M N P = originalComposition M N P := by
  let q := homIso M P
  let f := (homIso M N).hom ⊗ₘ (homIso N P).hom
  let g := Enriched.EnrichedRightMappingCategory.composition actualData M N P
  let c := originalComposition M N P
  have h : c ≫ q.hom = f ≫ g := homIso_composition M N P
  have hInv := congrArg (fun z => z ≫ q.inv) h
  have hCancel : (c ≫ q.hom) ≫ q.inv = c :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => c ≫ z) q.hom_inv_id).trans (Category.comp_id _))
  change f ≫ g ≫ q.inv = c
  exact (Category.assoc f g q.inv).symm.trans (hInv.symm.trans hCancel)

/-- Original module morphism composition is the actual original mapping-space composition. -/
theorem originalHomEquiv_composition {M N P : Carrier.{u, v}} (f : M ⟶ N) (g : N ⟶ P) :
    SymmetricRightModuleMapping.homEquiv M P (f ≫ g) = (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
      (SymmetricRightModuleMapping.homEquiv M N f ⊗ₘ SymmetricRightModuleMapping.homEquiv N P g) ≫
        originalComposition M N P := by
  apply original_hom_ext
  intro i
  simp only [Category.assoc, originalComposition_π, tensorHom_comp_tensorHom_assoc,
    SymmetricRightModuleMapping.homEquiv_π]
  exact eHomEquiv_comp PointedCGWH.{u, v} (f.hom.natTrans.app i) (g.hom.natTrans.app i)

/-- The actual ordinary right module category is genuinely enriched by its literal original Hom. -/
@[instance_reducible]
def literalEnrichedOrdinaryCategory :
    EnrichedOrdinaryCategory PointedCGWH.{u, v} Carrier.{u, v} where
  toEnrichedCategory := literalEnrichedCategory
  homEquiv := SymmetricRightModuleMapping.homEquiv _ _
  homEquiv_id M := by
    change originalIdentity M = literalIdentity M
    exact (literalIdentity_eq M).symm
  homEquiv_comp f g := by
    change SymmetricRightModuleMapping.homEquiv _ _ (f ≫ g) =
      (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
        (SymmetricRightModuleMapping.homEquiv _ _ f ⊗ₘ SymmetricRightModuleMapping.homEquiv _ _ g) ≫
          literalComposition _ _ _
    rw [literalComposition_eq]
    exact originalHomEquiv_composition f g

/-- Every complete forward comparison component is the exact original mapping projection. -/
@[reassoc]
theorem homIso_hom_π (M N : Carrier.{u, v}) (n : SymmetricOperatorIndex.{u, v}) :
    (homIso M N).hom ≫ fullπ M N n = SymmetricRightModuleMapping.π M N
      (show Operad.SmallFinBijGroupoid from n.asIndex) := toFull_π M N n

/-- Every complete inverse comparison component is the exact original source projection. -/
@[reassoc]
theorem homIso_inv_π (M N : Carrier.{u, v}) (i : Operad.SmallFinBijGroupoid) :
    (homIso M N).inv ≫ SymmetricRightModuleMapping.π M N i =
      fullπ M N (symmetricOperatorObj i) := toOriginal_π M N i

/-- The selected literal module enrichment has the whole original mapping Hom object. -/
theorem literalHom_eq (M N : Carrier.{u, v}) :
    @EnrichedCategory.Hom PointedCGWH.{u, v} _ _ Carrier.{u, v}
      literalEnrichedCategory M N = SymmetricRightModuleMapping.Hom M N := by rfl

/-- The actual selected enriched identity is the whole original module mapping point. -/
theorem literalEnrichedCategory_identity (M : Carrier.{u, v}) :
    @eId PointedCGWH.{u, v} _ _ Carrier.{u, v} literalEnrichedCategory M =
      originalIdentity M := literalIdentity_eq M

/-- The actual selected enriched composition is the whole original R-linear mapping operation. -/
theorem literalEnrichedCategory_composition (M N P : Carrier.{u, v}) :
    @eComp PointedCGWH.{u, v} _ _ Carrier.{u, v} literalEnrichedCategory M N P =
      originalComposition M N P := literalComposition_eq M N P

/-- The selected ordinary enrichment retains exactly the complete original literal enrichment. -/
theorem literalEnrichedOrdinaryCategory_enrichment :
    literalEnrichedOrdinaryCategory.{u, v}.toEnrichedCategory = literalEnrichedCategory.{u, v} :=
  by rfl

end PointedCGWH.SymmetricModuleMappingComparison
