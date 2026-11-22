/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereFunctor
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorCategory
public import MathlibExt.Topology.Category.CGWH.Colimits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Native orthogonal operator index

The coefficient is the original representation sphere functor. All native
small-shape colimits and tensor preservation are derived from existing native
providers. This module makes no source module, Thom topology, spectrum model,
or stable localization claim.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.Spectra

attribute [local instance] OrthogonalIndex.enrichedCategory

/-- The original bare index objects tagged by the actual sphere coefficient. -/
abbrev OrthogonalOperatorIndex : Type :=
  letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  Enriched.SphereOperator.OperatorIndex
    OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}

/-- The native enrichment is definitionally the proved generic operator enrichment. -/
instance orthogonalOperatorEnrichedCategory :
    EnrichedCategory PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v} := by
  letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  exact Enriched.SphereOperator.operatorEnrichedCategory
    OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}

namespace OrthogonalOperatorIndex

/-- View an original dimension as a tagged operator object. -/
def ofIndex (n : OrthogonalIndex) : OrthogonalOperatorIndex.{u, v} := by
  letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  exact ⟨n⟩

/-- The full native coend Hom. -/
abbrev hom (n k : OrthogonalIndex) : PointedCGWH.{u, v} :=
  ofIndex.{u, v} n ⟶[PointedCGWH.{u, v}] ofIndex.{u, v} k

/-- The coend weight is the actual full Hom out of the coefficient-first sum. -/
abbrev weight (n k : OrthogonalIndex) :=
  letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  Enriched.SphereOperator.weight OrthogonalIndex.enrichedMonoidalData.{u, v} n k

/-- Native Hom is precisely the original weighted coend. -/
theorem hom_eq_weightedCoend (n k : OrthogonalIndex) :
    hom.{u, v} n k =
      Enriched.weightedCoend (weight.{u, v} n k) orthogonalSphereFunctor.{u, v} := rfl

/-- The full Hom/coefficient generator, retaining every native isometry parameter. -/
def ι (n k a : OrthogonalIndex) :
    OrthogonalIndex.hom.{u, v} (a + n) k ⊗
      PointedCGWH.orthogonalSphere.{u, v} a ⟶ hom.{u, v} n k := by
  letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  exact Enriched.weightedCoend.ι (weight.{u, v} n k)
    orthogonalSphereFunctor.{u, v} a

/-- The full native relation uses the original one-point sphere action. -/
theorem balance (n k a b : OrthogonalIndex) :
    (α_ ((weight.{u, v} n k).obj (Opposite.op b))
      (OrthogonalIndex.hom.{u, v} a b)
      (PointedCGWH.orthogonalSphere.{u, v} a)).inv ≫
      (MonoidalClosed.uncurry
        ((weight.{u, v} n k).map (Opposite.op b) (Opposite.op a)) ⊗ₘ
          𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) ≫
      ι.{u, v} n k a =
    (weight.{u, v} n k).obj (Opposite.op b) ◁
      PointedCGWH.orthogonalSphereAction.{u, v} a b ≫ ι.{u, v} n k b := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  let _ : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  let W := weight.{u, v} n k
  let H := OrthogonalIndex.hom.{u, v} a b
  let S := PointedCGWH.orthogonalSphere.{u, v} a
  let T := PointedCGWH.orthogonalSphere.{u, v} b
  let f : H ⟶ (ihom S).obj T := orthogonalSphereFunctor.{u, v}.map a b
  let action := PointedCGWH.orthogonalSphereAction.{u, v} a b
  have hUncurry : MonoidalClosed.uncurry f = (β_ S H).hom ≫ action :=
    orthogonalSphereFunctor_uncurry a b
  have hAction : (β_ H S).hom ≫ MonoidalClosed.uncurry f = action := by
    rw [hUncurry, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have hBalance :
      (α_ (W.obj (Opposite.op b)) H S).inv ≫
        (MonoidalClosed.uncurry (W.map (Opposite.op b) (Opposite.op a)) ⊗ₘ 𝟙 S) ≫
        Enriched.weightedCoend.ι W orthogonalSphereFunctor.{u, v} a =
      W.obj (Opposite.op b) ◁
        ((β_ H S).hom ≫ MonoidalClosed.uncurry f) ≫
        Enriched.weightedCoend.ι W orthogonalSphereFunctor.{u, v} b :=
    Enriched.weightedCoend.condition W orthogonalSphereFunctor.{u, v} a b
  rw [hAction] at hBalance
  exact hBalance

/-- The identity remains the original unit coend generator. -/
theorem id_eq (n : OrthogonalIndex) :
    eId PointedCGWH.{u, v} (ofIndex.{u, v} n) =
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
      OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
    Enriched.SphereOperator.identityGenerator
      OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} n := rfl

/-- Composition is the original descent through both full coends. -/
theorem comp_eq (n k l : OrthogonalIndex) :
    eComp PointedCGWH.{u, v} (ofIndex.{u, v} n) (ofIndex.{u, v} k)
      (ofIndex.{u, v} l) =
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
      OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
    Enriched.SphereOperator.composition
      OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} n k l := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  let _ : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  exact Enriched.SphereOperator.operatorIndex_comp
    OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}
    (ofIndex.{u, v} n) (ofIndex.{u, v} k) (ofIndex.{u, v} l)

/-- The entire pair of native generators keeps the positive coefficient crossing
and late-first multiplication of the original operator construction. -/
theorem composition_generator (n k l a b : OrthogonalIndex) :
    (ι.{u, v} n k a ⊗ₘ ι.{u, v} k l b) ≫
      eComp PointedCGWH.{u, v} (ofIndex.{u, v} n) (ofIndex.{u, v} k)
        (ofIndex.{u, v} l) =
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
      OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
    Enriched.SphereOperator.compositionGenerator
      OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}
      n k l a b := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  let _ : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  rw [comp_eq]
  exact Enriched.SphereOperator.composition_generator
    OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}
    n k l a b

/-- Both full unit laws are inherited from the proved coend construction. -/
theorem id_comp (n k : OrthogonalIndex) :
    (λ_ (hom.{u, v} n k)).inv ≫
      eId PointedCGWH.{u, v} (ofIndex.{u, v} n) ▷ hom.{u, v} n k ≫
      eComp PointedCGWH.{u, v} (ofIndex.{u, v} n) (ofIndex.{u, v} n)
        (ofIndex.{u, v} k) = 𝟙 (hom.{u, v} n k) :=
  e_id_comp PointedCGWH.{u, v} _ _

/-- Full native coend composition preserves the original right unit at every dimension. -/
theorem comp_id (n k : OrthogonalIndex) :
    (ρ_ (hom.{u, v} n k)).inv ≫
      hom.{u, v} n k ◁ eId PointedCGWH.{u, v} (ofIndex.{u, v} k) ≫
      eComp PointedCGWH.{u, v} (ofIndex.{u, v} n) (ofIndex.{u, v} k)
        (ofIndex.{u, v} k) = 𝟙 (hom.{u, v} n k) :=
  e_comp_id PointedCGWH.{u, v} _ _

/-- Associativity holds on all three native coends with the original bracketing. -/
theorem assoc (n k l m : OrthogonalIndex) :
    (α_ (hom.{u, v} n k) (hom.{u, v} k l) (hom.{u, v} l m)).inv ≫
      eComp PointedCGWH.{u, v} (ofIndex.{u, v} n) (ofIndex.{u, v} k)
        (ofIndex.{u, v} l) ▷ hom.{u, v} l m ≫
      eComp PointedCGWH.{u, v} (ofIndex.{u, v} n) (ofIndex.{u, v} l)
        (ofIndex.{u, v} m) =
    hom.{u, v} n k ◁
      eComp PointedCGWH.{u, v} (ofIndex.{u, v} k) (ofIndex.{u, v} l)
        (ofIndex.{u, v} m) ≫
      eComp PointedCGWH.{u, v} (ofIndex.{u, v} n) (ofIndex.{u, v} k)
        (ofIndex.{u, v} m) :=
  e_assoc PointedCGWH.{u, v} _ _ _ _

/-- Delta inserts the original sphere unit into the complete bare native Hom. -/
def delta (n k : OrthogonalIndex) :
    OrthogonalIndex.hom.{u, v} n k ⟶ hom.{u, v} n k := by
  letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  exact (ρ_ (OrthogonalIndex.hom.{u, v} n k)).inv ≫
    (eHomWhiskerRight PointedCGWH.{u, v} (λ_ n).hom k ⊗ₘ
      orthogonalSphereMonoidalData.{u, v}.epsilon) ≫
    Enriched.weightedCoend.ι (weight.{u, v} n k)
      orthogonalSphereFunctor.{u, v} (𝟙_ OrthogonalIndex)

/-- Delta preserves the original enriched identity on the full native Hom. -/
theorem delta_id (n : OrthogonalIndex) :
    (@eId PointedCGWH.{u, v} _ _ OrthogonalIndex
      OrthogonalIndex.enrichedCategory.{u, v} n) ≫ delta.{u, v} n n =
      eId PointedCGWH.{u, v} (ofIndex.{u, v} n) := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  let _ : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  let H : PointedCGWH.{u, v} := n ⟶[PointedCGWH.{u, v}] n
  let K : PointedCGWH.{u, v} := (𝟙_ OrthogonalIndex ⊗ n) ⟶[PointedCGWH.{u, v}] n
  let Z : PointedCGWH.{u, v} := orthogonalSphereFunctor.{u, v}.obj (𝟙_ OrthogonalIndex)
  let p : H ⟶ K := eHomWhiskerRight PointedCGWH.{u, v} (λ_ n).hom n
  let e : 𝟙_ PointedCGWH.{u, v} ⟶ Z := orthogonalSphereMonoidalData.{u, v}.epsilon
  let j : K ⊗ Z ⟶ hom.{u, v} n n :=
    Enriched.weightedCoend.ι (weight.{u, v} n n)
      orthogonalSphereFunctor.{u, v} (𝟙_ OrthogonalIndex)
  have hp : eId PointedCGWH.{u, v} n ≫ p =
      eHomEquiv PointedCGWH.{u, v} (λ_ n).hom :=
    eId_comp_eHomWhiskerRight PointedCGWH.{u, v} OrthogonalIndex (λ_ n).hom
  have ht :
      (eId PointedCGWH.{u, v} n ⊗ₘ 𝟙 (𝟙_ PointedCGWH.{u, v})) ≫ (p ⊗ₘ e) =
      (eId PointedCGWH.{u, v} n ≫ p) ⊗ₘ e := by
    simpa only [Category.id_comp] using tensorHom_comp_tensorHom
      (eId PointedCGWH.{u, v} n) (𝟙 (𝟙_ PointedCGWH.{u, v})) p e
  change eId PointedCGWH.{u, v} n ≫ (ρ_ H).inv ≫ (p ⊗ₘ e) ≫ j =
    (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
      (eHomEquiv PointedCGWH.{u, v} (λ_ n).hom ⊗ₘ e) ≫ j
  rw [rightUnitor_inv_naturality_assoc, ← tensorHom_id]
  rw [← Category.assoc (eId PointedCGWH.{u, v} n ⊗ₘ
    𝟙 (𝟙_ PointedCGWH.{u, v})) (p ⊗ₘ e) j, ht, hp, unitors_inv_equal]

/-- The original right inclusion requires the actual native block swap because
the original operator weight is coefficient first. -/
def nu (n a : OrthogonalIndex) :
    PointedCGWH.orthogonalSphere.{u, v} a ⟶ hom.{u, v} n (n + a) := by
  letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  letI : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
  exact (λ_ (PointedCGWH.orthogonalSphere.{u, v} a)).inv ≫
    (eHomEquiv PointedCGWH.{u, v} (β_ a n).hom ⊗ₘ
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) ≫ ι.{u, v} n (n + a) a

end OrthogonalOperatorIndex


end CategoryTheory.Spectra
