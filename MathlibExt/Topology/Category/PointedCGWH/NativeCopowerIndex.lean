/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.BasedDiscreteMonoidal
public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# The based-discrete copower index

An ordinary category determines a PointedCGWH-enriched index with based-discrete Hom spaces.
Its identity and composition maps agree with ordinary identities and composition on each
generator. The ordinary restriction functor sends an index arrow to its specified generator
in the enriched Hom object.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w uI

open CategoryTheory CategoryTheory.MonoidalCategory

namespace PointedCGWH

section OriginalIndex

variable (I : Type uI) [Category.{w} I]

private abbrev originalTypeEnrichment : EnrichedCategory (Type w) I :=
  enrichedCategoryTypeOfCategory I

/-- The native copower enrichment is a separate wrapper around the original index category. -/
def CopowerIndex :=
  letI : EnrichedCategory (Type w) I := enrichedCategoryTypeOfCategory I
  letI : basedDiscreteFunctor.{u, v, w}.LaxMonoidal :=
    basedDiscreteMonoidal.{u, v, w}.toLaxMonoidal
  TransportEnrichment basedDiscreteFunctor.{u, v, w} I

/-- The wrapper carries the actual transported native Hom-object enrichment. -/
instance copowerIndexEnrichedCategory :
    EnrichedCategory PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I) := by
  letI : EnrichedCategory (Type w) I := enrichedCategoryTypeOfCategory I
  letI : basedDiscreteFunctor.{u, v, w}.LaxMonoidal :=
    basedDiscreteMonoidal.{u, v, w}.toLaxMonoidal
  change EnrichedCategory PointedCGWH.{u, max v w}
    (TransportEnrichment basedDiscreteFunctor.{u, v, w} I)
  infer_instance

/-- Place an original object in the separate enriched wrapper. -/
def copowerIndexObj (i : I) : CopowerIndex.{u, v, w} I :=
  i

/-- The genuine enriched Hom object is the original based-discrete arrow copower. -/
theorem copowerIndex_hom (i j : I) :
    (copowerIndexObj.{u, v, w} I i ⟶[PointedCGWH.{u, max v w}]
      copowerIndexObj.{u, v, w} I j) = basedDiscreteObj.{u, v, w} (i ⟶ j) := rfl

/-- Identity uses the literal original identity-arrow injection. -/
theorem copowerIndex_id (i : I) :
    eId PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I i) =
      basedDiscreteIncl.{u, v, w} (i ⟶ i) (𝟙 i) := by
  change basedDiscreteUnitIso.{u, v, w}.hom ≫
    basedDiscreteFunctor.{u, v, w}.map (↾fun _ : PUnit.{w + 1} => 𝟙 i) = _
  exact basedDiscreteIncl_naturality.{u, v, w} (fun _ : PUnit.{w + 1} => 𝟙 i)
    PUnit.unit

/-- Enriched composition keeps the original tensorator followed by original arrow composition. -/
theorem copowerIndex_comp (i j k : I) :
    eComp PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I i)
        (copowerIndexObj.{u, v, w} I j) (copowerIndexObj.{u, v, w} I k) =
      basedDiscreteTensorProductHom.{u, v, w} (i ⟶ j) (j ⟶ k) ≫
        basedDiscreteFunctor.{u, v, w}.map (↾fun p : (i ⟶ j) × (j ⟶ k) => p.1 ≫ p.2) :=
  rfl

/-- The complete original-arrow pair generator composes to the original composite injection. -/
theorem copowerIndex_comp_generator {i j k : I} (f : i ⟶ j) (g : j ⟶ k) :
    basedDiscretePairIncl.{u, v, w} (i ⟶ j) (j ⟶ k) f g ≫
        eComp PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I i)
          (copowerIndexObj.{u, v, w} I j) (copowerIndexObj.{u, v, w} I k) =
      basedDiscreteIncl.{u, v, w} (i ⟶ k) (f ≫ g) := by
  let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
  let E : Type w := i ⟶ j
  let F : Type w := j ⟶ k
  let T : PointedCGWH.{u, max v w} :=
    basedDiscreteObj.{u, v, w} E ⊗ basedDiscreteObj.{u, v, w} F
  let P : PointedCGWH.{u, max v w} := basedDiscreteObj.{u, v, w} (E × F)
  let H : PointedCGWH.{u, max v w} := basedDiscreteObj.{u, v, w} (i ⟶ k)
  let p : U ⟶ T := basedDiscretePairIncl.{u, v, w} E F f g
  let t : T ⟶ P := basedDiscreteTensorProductHom.{u, v, w} E F
  let m : P ⟶ H :=
    basedDiscreteFunctor.{u, v, w}.map (↾fun q : E × F => q.1 ≫ q.2)
  let c : T ⟶ H :=
    eComp PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I i)
      (copowerIndexObj.{u, v, w} I j) (copowerIndexObj.{u, v, w} I k)
  let pair : U ⟶ P := basedDiscreteIncl.{u, v, w} (E × F) (f, g)
  let composite : U ⟶ H := basedDiscreteIncl.{u, v, w} (i ⟶ k) (f ≫ g)
  have hc : c = t ≫ m := copowerIndex_comp.{u, v, w} I i j k
  have ht : p ≫ t = pair := basedDiscreteTensorProductHom_pair.{u, v, w} E F f g
  have hm : pair ≫ m = composite :=
    basedDiscreteIncl_naturality.{u, v, w} (fun q : E × F => q.1 ≫ q.2) (f, g)
  change p ≫ c = composite
  exact (congrArg (fun q : T ⟶ H => p ≫ q) hc).trans
    ((Category.assoc p t m).symm.trans
      ((congrArg (fun q : U ⟶ P => q ≫ m) ht).trans hm))

/-- The associated ordinary category has genuine native unit-points as arrows. -/
def CopowerUnderlying :=
  ForgetEnrichment PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I)

/-- Keep the associated ordinary dictionary on its distinct wrapper. -/
instance copowerUnderlyingCategory : Category (CopowerUnderlying.{u, v, w} I) := by
  change Category
    (ForgetEnrichment PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I))
  infer_instance

/-- Original arrows restrict by their literal native unit-copower injections. -/
def copowerRestriction : I ⥤ CopowerUnderlying.{u, v, w} I where
  obj i := ForgetEnrichment.of PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I i)
  map {i j} f := ForgetEnrichment.homOf PointedCGWH.{u, max v w}
    (show 𝟙_ PointedCGWH.{u, max v w} ⟶
      copowerIndexObj.{u, v, w} I i ⟶[PointedCGWH.{u, max v w}]
        copowerIndexObj.{u, v, w} I j from basedDiscreteIncl.{u, v, w} (i ⟶ j) f)
  map_id i := by
    rw [← copowerIndex_id]
    exact ForgetEnrichment.homOf_eId PointedCGWH.{u, max v w} _
  map_comp {i j k} f g := by
    let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
    let i' : CopowerIndex.{u, v, w} I := copowerIndexObj.{u, v, w} I i
    let j' : CopowerIndex.{u, v, w} I := copowerIndexObj.{u, v, w} I j
    let k' : CopowerIndex.{u, v, w} I := copowerIndexObj.{u, v, w} I k
    let fi : U ⟶ i' ⟶[PointedCGWH.{u, max v w}] j' :=
      basedDiscreteIncl.{u, v, w} (i ⟶ j) f
    let gi : U ⟶ j' ⟶[PointedCGWH.{u, max v w}] k' :=
      basedDiscreteIncl.{u, v, w} (j ⟶ k) g
    let hi : U ⟶ i' ⟶[PointedCGWH.{u, max v w}] k' :=
      basedDiscreteIncl.{u, v, w} (i ⟶ k) (f ≫ g)
    let ci : U ⟶ i' ⟶[PointedCGWH.{u, max v w}] k' :=
      (λ_ U).inv ≫ (fi ⊗ₘ gi) ≫ eComp PointedCGWH.{u, max v w} i' j' k'
    have hGenerator : ci = hi := copowerIndex_comp_generator.{u, v, w} I f g
    have hCompose : ForgetEnrichment.homOf PointedCGWH.{u, max v w} ci =
        ForgetEnrichment.homOf PointedCGWH.{u, max v w} fi ≫
          ForgetEnrichment.homOf PointedCGWH.{u, max v w} gi :=
      ForgetEnrichment.homOf_comp PointedCGWH.{u, max v w} fi gi
    change ForgetEnrichment.homOf PointedCGWH.{u, max v w} hi =
      ForgetEnrichment.homOf PointedCGWH.{u, max v w} fi ≫
        ForgetEnrichment.homOf PointedCGWH.{u, max v w} gi
    exact (congrArg (fun q : U ⟶ i' ⟶[PointedCGWH.{u, max v w}] k' =>
      ForgetEnrichment.homOf PointedCGWH.{u, max v w} q) hGenerator).symm.trans hCompose

/-- Restriction keeps the actual unit-shaped native Hom injection. -/
theorem copowerRestriction_map {i j : I} (f : i ⟶ j) :
    ForgetEnrichment.homTo PointedCGWH.{u, max v w}
      ((copowerRestriction.{u, v, w} I).map f) =
      basedDiscreteIncl.{u, v, w} (i ⟶ j) f := rfl

end OriginalIndex

end PointedCGWH
