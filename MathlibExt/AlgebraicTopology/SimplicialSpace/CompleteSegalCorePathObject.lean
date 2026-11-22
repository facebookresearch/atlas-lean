/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.FiniteCompletenessHorelComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalHomotopyCategory
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ComponentUnionWeakRestriction
import Mathlib.AlgebraicTopology.ModelCategory.PathObject

/-!
# Intrinsic complete-Segal core-path objects and equivalence fibres

The original equivalence subcomplex, endpoint, mapping fibre, intrinsic
object quotient and original natural maps construct the native scalar path
object at complete Segal targets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.SegalHomotopy

/-- The actual source-first endpoint of the original equivalence subcomplex. -/
def coreEndpoint (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (equivalenceSubcomplex W hW : SSet.{u}) ⟶
      (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) :=
  prod.lift (equivalenceSource W hW) (equivalenceTarget W hW)

/-- Global Reedy fibrancy and the actual component inclusion give the endpoint fibration. -/
theorem coreEndpoint_fibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    Fibration (coreEndpoint W hW) := by
  have hfac : coreEndpoint W hW =
      (equivalenceSubcomplex W hW).ι ≫ mappingEndpoint W := by
    apply prod.hom_ext <;>
      simp [coreEndpoint, equivalenceSource, equivalenceTarget]
  let : Fibration (equivalenceSubcomplex W hW).ι := by
    change Fibration (SSet.componentUnion (W.diagram _⦋1⦌)
      (equivalenceComponents W hW)).ι
    exact SSet.componentUnionInclusionKanFibration _ _
  let : Fibration (mappingEndpoint W) :=
    ReedyModel.mappingEndpoint_fibration W hW.1
  rw [hfac]
  infer_instance

/-- The true original endpoint fibre over the prescribed original vertex pair. -/
abbrev equivalenceFibre (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  pullback (coreEndpoint W hW) (mappingPointPair W x y)

/-- The actual whole core-to-mapping-fibre comparison, retaining both projections. -/
def equivalenceFibreToMappingFibre (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    equivalenceFibre W hW x y ⟶ mappingFibre W x y :=
  pullback.lift
    (pullback.fst (coreEndpoint W hW) (mappingPointPair W x y) ≫
      (equivalenceSubcomplex W hW).ι)
    (pullback.snd (coreEndpoint W hW) (mappingPointPair W x y)) (by
      have hfac : coreEndpoint W hW =
          (equivalenceSubcomplex W hW).ι ≫ mappingEndpoint W := by
        apply prod.hom_ext <;>
          simp [coreEndpoint, equivalenceSource, equivalenceTarget]
      simpa only [Category.assoc, ← hfac] using
        (pullback.condition (f := coreEndpoint W hW) (g := mappingPointPair W x y)))

/-- The whole original square is a pullback and the actual core fibre is Kan. -/
theorem equivalenceFibre_preimageIsPullback
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    IsPullback (pullback.fst (coreEndpoint W hW) (mappingPointPair W x y))
      (equivalenceFibreToMappingFibre W hW x y)
      (equivalenceSubcomplex W hW).ι (mappingFibre.fst W x y) ∧
      SSet.KanComplex (equivalenceFibre W hW x y) := by
  let : (fibrations SSet.{u}).RespectsIso := by
    rw [SSet.modelCategoryQuillen.fibrations_eq]
    exact MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ g hg => by
      let : IsIso g := hg
      exact MorphismProperty.rlp_of_isIso SSet.modelCategoryQuillen.J g
  have hfac : coreEndpoint W hW =
      (equivalenceSubcomplex W hW).ι ≫ mappingEndpoint W := by
    apply prod.hom_ext <;>
      simp [coreEndpoint, equivalenceSource, equivalenceTarget]
  have hsnd : equivalenceFibreToMappingFibre W hW x y ≫ mappingFibre.snd W x y =
      pullback.snd (coreEndpoint W hW) (mappingPointPair W x y) := by
    exact pullback.lift_snd _ _ _
  have hfst : equivalenceFibreToMappingFibre W hW x y ≫ mappingFibre.fst W x y =
      pullback.fst (coreEndpoint W hW) (mappingPointPair W x y) ≫
        (equivalenceSubcomplex W hW).ι := by
    exact pullback.lift_fst _ _ _
  have whole : IsPullback
      (pullback.fst (coreEndpoint W hW) (mappingPointPair W x y))
      (equivalenceFibreToMappingFibre W hW x y ≫ mappingFibre.snd W x y)
      ((equivalenceSubcomplex W hW).ι ≫ mappingEndpoint W) (mappingPointPair W x y) := by
    rw [hsnd, ← hfac]
    exact IsPullback.of_hasPullback _ _
  have sq := whole.of_bot hfst.symm (ReedyModel.mappingFibre_isPullback W x y)
  let : Fibration (coreEndpoint W hW) := coreEndpoint_fibration W hW
  let : Fibration (pullback.snd (coreEndpoint W hW) (mappingPointPair W x y)) := by
    rw [HomotopicalAlgebra.fibration_iff]
    exact (fibrations SSet.{u}).of_isPullback (IsPullback.of_hasPullback _ _)
      ((HomotopicalAlgebra.fibration_iff _).mp (coreEndpoint_fibration W hW))
  let : IsFibrant (Δ[0] : SSet.{u}) :=
    (isFibrant_iff_of_isTerminal (𝟙 (Δ[0] : SSet.{u}))
      SSet.stdSimplex.isTerminalObj₀).mpr (by infer_instance)
  exact ⟨sq, isFibrant_of_fibration
    (pullback.snd (coreEndpoint W hW) (mappingPointPair W x y))⟩

/-- The exact original component-preimage is compared with the same core fibre. -/
def equivalenceFibrePreimageIso (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    equivalenceFibre W hW x y ≅
      (SSet.componentUnion (mappingFibre W x y)
        ((SSet.mapπ₀ (mappingFibre.fst W x y)) ⁻¹' equivalenceComponents W hW) : SSet.{u}) := by
  have hCore := (equivalenceFibre_preimageIsPullback W hW x y).1
  have hPre : IsPullback
      (SSet.componentUnionPreimageMap (mappingFibre.fst W x y) (equivalenceComponents W hW))
      (SSet.componentUnion (mappingFibre W x y)
        ((SSet.mapπ₀ (mappingFibre.fst W x y)) ⁻¹' equivalenceComponents W hW)).ι
      (equivalenceSubcomplex W hW).ι (mappingFibre.fst W x y) := by
    simpa only [equivalenceSubcomplex, SSet.componentUnion] using
      (SSet.componentUnionPreimageMap_isPullback
        (mappingFibre.fst W x y) (equivalenceComponents W hW)).flip
  exact hCore.isoIsPullback _ _ hPre

/-- Both inverse directions retain every original projection and intrinsic vertex class. -/
theorem equivalenceFibrePreimageIso_laws (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    let U := SSet.componentUnion (mappingFibre W x y)
      ((SSet.mapπ₀ (mappingFibre.fst W x y)) ⁻¹' equivalenceComponents W hW)
    let e := equivalenceFibrePreimageIso W hW x y
    e.hom ≫ U.ι = equivalenceFibreToMappingFibre W hW x y ∧
      e.hom ≫ SSet.componentUnionPreimageMap (mappingFibre.fst W x y)
        (equivalenceComponents W hW) =
        pullback.fst (coreEndpoint W hW) (mappingPointPair W x y) ∧
      e.inv ≫ pullback.fst (coreEndpoint W hW) (mappingPointPair W x y) =
        SSet.componentUnionPreimageMap (mappingFibre.fst W x y)
          (equivalenceComponents W hW) ∧
      e.inv ≫ pullback.snd (coreEndpoint W hW) (mappingPointPair W x y) =
        U.ι ≫ mappingFibre.snd W x y ∧
      (∀ a : (mappingFibre W x y) _⦋0⦌,
        a ∈ U.obj (op ⦋0⦌) ↔
          IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨y⟩) (SSet.π₀.mk a)) := by
  let U := SSet.componentUnion (mappingFibre W x y)
    ((SSet.mapπ₀ (mappingFibre.fst W x y)) ⁻¹' equivalenceComponents W hW)
  let e := equivalenceFibrePreimageIso W hW x y
  have hCore := (equivalenceFibre_preimageIsPullback W hW x y).1
  have hPre : IsPullback
      (SSet.componentUnionPreimageMap (mappingFibre.fst W x y) (equivalenceComponents W hW))
      U.ι (equivalenceSubcomplex W hW).ι (mappingFibre.fst W x y) := by
    simpa only [U, equivalenceSubcomplex, SSet.componentUnion] using
      (SSet.componentUnionPreimageMap_isPullback
        (mappingFibre.fst W x y) (equivalenceComponents W hW)).flip
  have he1 : e.hom ≫ U.ι = equivalenceFibreToMappingFibre W hW x y := by
    exact IsPullback.isoIsPullback_hom_snd _ _ hCore hPre
  have he2 : e.hom ≫ SSet.componentUnionPreimageMap (mappingFibre.fst W x y)
      (equivalenceComponents W hW) =
        pullback.fst (coreEndpoint W hW) (mappingPointPair W x y) := by
    exact IsPullback.isoIsPullback_hom_fst _ _ hCore hPre
  have hi1 : e.inv ≫ pullback.fst (coreEndpoint W hW) (mappingPointPair W x y) =
      SSet.componentUnionPreimageMap (mappingFibre.fst W x y) (equivalenceComponents W hW) := by
    exact IsPullback.isoIsPullback_inv_fst _ _ hCore hPre
  have hi2 : e.inv ≫ pullback.snd (coreEndpoint W hW) (mappingPointPair W x y) =
      U.ι ≫ mappingFibre.snd W x y := by
    have hs : equivalenceFibreToMappingFibre W hW x y ≫ mappingFibre.snd W x y =
        pullback.snd (coreEndpoint W hW) (mappingPointPair W x y) := by
      exact pullback.lift_snd _ _ _
    rw [← hs, ← Category.assoc]
    exact congrArg (fun q => q ≫ mappingFibre.snd W x y)
      (IsPullback.isoIsPullback_inv_snd _ _ hCore hPre)
  refine ⟨he1, he2, hi1, hi2, ?_⟩
  intro a
  rw [SSet.componentUnion_preimage]
  change (mappingFibre.fst W x y).app (op ⦋0⦌) a ∈
      (equivalenceSubcomplex W hW).obj (op ⦋0⦌) ↔ _
  rw [mem_equivalenceSubcomplex_zero]
  exact isEquivalenceEdge_iff_of_fibre W hW _ a rfl

/-- The canonical core-fibre map keeps the prescribed target vertices and all original maps. -/
def equivalenceFibreMap {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (V.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y') :
    equivalenceFibre W hW x y ⟶ equivalenceFibre V hV x' y' :=
  pullback.map (coreEndpoint W hW) (mappingPointPair W x y)
    (coreEndpoint V hV) (mappingPointPair V x' y')
    (equivalenceMap f hW hV) (𝟙 _)
    (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)))
    (by
      apply prod.hom_ext
      · simpa only [coreEndpoint, Category.assoc, prod.lift_fst, prod.map_fst,
          prod.lift_fst_assoc] using (equivalenceSource_naturality f hW hV).symm
      · simpa only [coreEndpoint, Category.assoc, prod.lift_snd, prod.map_snd,
          prod.lift_snd_assoc] using (equivalenceTarget_naturality f hW hV).symm)
    (by rw [mappingPointPair_naturality, hx, hy, Category.id_comp])

/-- Both projections, the original MF comparison and every inner operator commute. -/
theorem equivalenceFibreMap_laws {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (V.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y') :
    let m := equivalenceFibreMap f hW hV hx hy
    let UW := SSet.componentUnion (mappingFibre W x y)
      ((SSet.mapπ₀ (mappingFibre.fst W x y)) ⁻¹' equivalenceComponents W hW)
    let UV := SSet.componentUnion (mappingFibre V x' y')
      ((SSet.mapπ₀ (mappingFibre.fst V x' y')) ⁻¹' equivalenceComponents V hV)
    let eW := equivalenceFibrePreimageIso W hW x y
    let eV := equivalenceFibrePreimageIso V hV x' y'
    let um := eW.inv ≫ m ≫ eV.hom
    m ≫ pullback.fst (coreEndpoint V hV) (mappingPointPair V x' y') =
        pullback.fst (coreEndpoint W hW) (mappingPointPair W x y) ≫ equivalenceMap f hW hV ∧
      m ≫ pullback.snd (coreEndpoint V hV) (mappingPointPair V x' y') =
        pullback.snd (coreEndpoint W hW) (mappingPointPair W x y) ∧
      m ≫ equivalenceFibreToMappingFibre V hV x' y' =
        equivalenceFibreToMappingFibre W hW x y ≫ mappingFibre.map f hx hy ∧
      (∀ {n n' : SimplexCategoryᵒᵖ} (a : n ⟶ n'),
        (equivalenceFibre W hW x y).map a ≫ m.app n' =
          m.app n ≫ (equivalenceFibre V hV x' y').map a) ∧
      eW.hom ≫ um = m ≫ eV.hom ∧
      um ≫ UV.ι = UW.ι ≫ mappingFibre.map f hx hy ∧
      um ≫ SSet.componentUnionPreimageMap (mappingFibre.fst V x' y')
        (equivalenceComponents V hV) =
        SSet.componentUnionPreimageMap (mappingFibre.fst W x y)
          (equivalenceComponents W hW) ≫ equivalenceMap f hW hV := by
  let m := equivalenceFibreMap f hW hV hx hy
  have h1 : m ≫ pullback.fst (coreEndpoint V hV) (mappingPointPair V x' y') =
      pullback.fst (coreEndpoint W hW) (mappingPointPair W x y) ≫ equivalenceMap f hW hV := by
    simp [m, equivalenceFibreMap]
  have h2 : m ≫ pullback.snd (coreEndpoint V hV) (mappingPointPair V x' y') =
      pullback.snd (coreEndpoint W hW) (mappingPointPair W x y) := by
    simp [m, equivalenceFibreMap]
  have cfW : equivalenceFibreToMappingFibre W hW x y ≫ mappingFibre.fst W x y =
      pullback.fst (coreEndpoint W hW) (mappingPointPair W x y) ≫
        (equivalenceSubcomplex W hW).ι := pullback.lift_fst _ _ _
  have cfV : equivalenceFibreToMappingFibre V hV x' y' ≫ mappingFibre.fst V x' y' =
      pullback.fst (coreEndpoint V hV) (mappingPointPair V x' y') ≫
        (equivalenceSubcomplex V hV).ι := pullback.lift_fst _ _ _
  have csW : equivalenceFibreToMappingFibre W hW x y ≫ mappingFibre.snd W x y =
      pullback.snd (coreEndpoint W hW) (mappingPointPair W x y) := pullback.lift_snd _ _ _
  have csV : equivalenceFibreToMappingFibre V hV x' y' ≫ mappingFibre.snd V x' y' =
      pullback.snd (coreEndpoint V hV) (mappingPointPair V x' y') := pullback.lift_snd _ _ _
  have h3 : m ≫ equivalenceFibreToMappingFibre V hV x' y' =
      equivalenceFibreToMappingFibre W hW x y ≫ mappingFibre.map f hx hy := by
    apply pullback.hom_ext
    · change (m ≫ equivalenceFibreToMappingFibre V hV x' y') ≫
        mappingFibre.fst V x' y' =
        (equivalenceFibreToMappingFibre W hW x y ≫ mappingFibre.map f hx hy) ≫
          mappingFibre.fst V x' y'
      simp only [Category.assoc, cfV, mappingFibre.map_fst]
      rw [← Category.assoc, h1, Category.assoc, equivalenceMap_ι,
        ← Category.assoc, ← cfW]
      exact Category.assoc _ _ _
    · change (m ≫ equivalenceFibreToMappingFibre V hV x' y') ≫
        mappingFibre.snd V x' y' =
        (equivalenceFibreToMappingFibre W hW x y ≫ mappingFibre.map f hx hy) ≫
          mappingFibre.snd V x' y'
      simp only [Category.assoc, csV, csW, mappingFibre.map_snd]
      exact h2
  let eW := equivalenceFibrePreimageIso W hW x y
  let eV := equivalenceFibrePreimageIso V hV x' y'
  have w := equivalenceFibrePreimageIso_laws W hW x y
  have v := equivalenceFibrePreimageIso_laws V hV x' y'
  refine ⟨h1, h2, h3, fun a => m.naturality a, ?_, ?_, ?_⟩
  · exact Iso.hom_inv_id_assoc eW _
  · calc
      (eW.inv ≫ m ≫ eV.hom) ≫ _ = eW.inv ≫ m ≫ (eV.hom ≫ _) := by
        exact (Category.assoc _ _ _).trans
          (congrArg (fun q => eW.inv ≫ q) (Category.assoc _ _ _))
      _ = eW.inv ≫ m ≫ equivalenceFibreToMappingFibre V hV x' y' :=
        congrArg (fun q => eW.inv ≫ m ≫ q) v.1
      _ = eW.inv ≫ (equivalenceFibreToMappingFibre W hW x y ≫ mappingFibre.map f hx hy) :=
        congrArg (fun q => eW.inv ≫ q) h3
      _ = (eW.inv ≫ equivalenceFibreToMappingFibre W hW x y) ≫ mappingFibre.map f hx hy :=
        (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun q => q ≫ mappingFibre.map f hx hy)
        ((Iso.inv_comp_eq eW).mpr w.1.symm)
  · calc
      (eW.inv ≫ m ≫ eV.hom) ≫ _ = eW.inv ≫ m ≫ (eV.hom ≫ _) := by
        exact (Category.assoc _ _ _).trans
          (congrArg (fun q => eW.inv ≫ q) (Category.assoc _ _ _))
      _ = eW.inv ≫ m ≫ pullback.fst (coreEndpoint V hV) (mappingPointPair V x' y') :=
        congrArg (fun q => eW.inv ≫ m ≫ q) v.2.1
      _ = eW.inv ≫ (pullback.fst (coreEndpoint W hW) (mappingPointPair W x y) ≫
          equivalenceMap f hW hV) := congrArg (fun q => eW.inv ≫ q) h1
      _ = (eW.inv ≫ pullback.fst (coreEndpoint W hW) (mappingPointPair W x y)) ≫
          equivalenceMap f hW hV := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun q => q ≫ equivalenceMap f hW hV) w.2.2.1

end SimplicialSpace.SegalHomotopy

namespace SimplicialSpace

/-- The actual equivalence subcomplex gives the complete target's native scalar path object. -/
def completeSegalCorePathObject (W : SimplicialSpace.{u}) (hC : completeSegalSpaces W) :
    PathObject (W.diagram _⦋0⦌) := by
  let hF := (FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete W).mp hC
  let hS : segalSpaces W := hF.1
  have hi : SSet.realizationWeakEquivalences (SegalHomotopy.equivalenceIdentity W hS) :=
    (FiniteCompletenessHorel.completeness_tests_iff W hS).2.2.2.mp hF.2
  exact
    { P := (SegalHomotopy.equivalenceSubcomplex W hS : SSet.{u})
      ι := SegalHomotopy.equivalenceIdentity W hS
      p₀ := SegalHomotopy.equivalenceSource W hS
      p₁ := SegalHomotopy.equivalenceTarget W hS
      ι_p₀ := by
        simp only [SegalHomotopy.equivalenceSource, ← Category.assoc,
          SegalHomotopy.equivalenceIdentity_ι]
        simpa using (W.diagram.δ_comp_σ_succ (i := (0 : Fin 1)))
      ι_p₁ := by
        simp only [SegalHomotopy.equivalenceTarget, ← Category.assoc,
          SegalHomotopy.equivalenceIdentity_ι]
        simpa using (W.diagram.δ_comp_σ_self (i := (0 : Fin 1)))
      weakEquivalence_ι := by
        rw [HomotopicalAlgebra.weakEquivalence_iff]
        exact hi }

/-- Very-good structure and all original identity/source/target naturalities are constructed. -/
theorem completeSegalCorePathObject_laws (W : SimplicialSpace.{u})
    (hC : completeSegalSpaces W) :
    let P := completeSegalCorePathObject W hC
    P.IsVeryGood ∧ P.ι ≫ P.p₀ = 𝟙 _ ∧ P.ι ≫ P.p₁ = 𝟙 _ ∧
      (∀ (V : SimplicialSpace.{u}) (hV : completeSegalSpaces V) (f : W ⟶ V),
        let hS := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete W).mp hC).1
        let hT := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete V).mp hV).1
        let m := SegalHomotopy.equivalenceMap f hS hT
        P.ι ≫ m = f.hom.app (op ⦋0⦌) ≫ (completeSegalCorePathObject V hV).ι ∧
          m ≫ (completeSegalCorePathObject V hV).p₀ = P.p₀ ≫ f.hom.app (op ⦋0⦌) ∧
          m ≫ (completeSegalCorePathObject V hV).p₁ = P.p₁ ≫ f.hom.app (op ⦋0⦌)) := by
  let P := completeSegalCorePathObject W hC
  let hS := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete W).mp hC).1
  have hgood : P.IsGood :=
    { fibration_p := SegalHomotopy.coreEndpoint_fibration W hS }
  let : IsSplitMono P.ι := ⟨⟨P.p₀, P.ι_p₀⟩⟩
  let : Mono P.ι := inferInstance
  have hcof : Cofibration P.ι := by
    rw [HomotopicalAlgebra.cofibration_iff]
    exact (show Mono P.ι from inferInstance)
  refine ⟨{ fibration_p := hgood.fibration_p, cofibration_ι := hcof }, P.ι_p₀, P.ι_p₁, ?_⟩
  intro V hV f
  exact ⟨SegalHomotopy.equivalenceIdentity_naturality f _ _,
    SegalHomotopy.equivalenceSource_naturality f _ _,
    SegalHomotopy.equivalenceTarget_naturality f _ _⟩

/-- The SAME intrinsic object-component map is bijective at actual complete endpoints. -/
theorem completeSegalObjectComponentClass_bijective
    (W : SimplicialSpace.{u}) (hC : completeSegalSpaces W) :
    let hS := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete W).mp hC).1
    Function.Bijective (SegalHomotopy.objectComponentClass W hS) := by
  let P := completeSegalCorePathObject W hC
  let hS := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete W).mp hC).1
  have hi : SSet.realizationWeakEquivalences P.ι := by
    exact (HomotopicalAlgebra.weakEquivalence_iff _).mp P.weakEquivalence_ι
  have hbij := SSet.realizationWeakEquivalences.bijective_mapπ₀ hi
  have hs : SSet.mapπ₀ P.p₀ = SSet.mapπ₀ P.p₁ := by
    funext c
    obtain ⟨a, rfl⟩ := hbij.2 c
    have h0 := congrArg (fun f => SSet.mapπ₀ f a) P.ι_p₀
    have h1 := congrArg (fun f => SSet.mapπ₀ f a) P.ι_p₁
    simpa only [SSet.mapπ₀_comp_apply, SSet.mapπ₀_id_apply] using h0.trans h1.symm
  let c₀ : Cofork (↾(SSet.mapπ₀ P.p₀)) (↾(SSet.mapπ₀ P.p₁)) :=
    Cofork.ofπ (𝟙 _) (by
      ext c
      exact congrFun hs c)
  let hc₀ : IsColimit c₀ := Cofork.IsColimit.mk _
    (fun s => s.π) (fun s => by simp [c₀])
    (fun s m hm => by simpa [c₀] using hm)
  let hc₁ := SegalHomotopy.isColimitObjectComponentCofork W hS
  let e := IsColimit.coconePointUniqueUpToIso hc₀ hc₁
  have he : e.hom = ↾(SegalHomotopy.objectComponentClass W hS) := by
    have h := IsColimit.comp_coconePointUniqueUpToIso_hom hc₀ hc₁ WalkingParallelPair.one
    change (𝟙 _) ≫ e.hom = ↾(SegalHomotopy.objectComponentClass W hS) at h
    exact (Category.id_comp _).symm.trans h
  have hb : Function.Bijective e.hom := (CategoryTheory.isIso_iff_bijective e.hom).mp inferInstance
  rw [he] at hb
  exact hb

end SimplicialSpace
