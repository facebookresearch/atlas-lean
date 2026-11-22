/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceCompositionCompatibility
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceUnitCompatibility

/-!
# The actual reverse enriched functor from original orthogonal source laws

The original source unit and associative equations assemble the original
coend map fields into a genuine functor on the original operator category.
Every value and entire Hom map is retained. Restricting an original operator
functor and selecting its original sphere action reconstructs that complete
functor, including its map function.

## Primary source and formalized scope

The source is Mandell, May, Schwede and Shipley, *Model categories of diagram
spectra*, the supplied December 30, 1999 preprint: Construction 2.1 and
Theorem 2.2 on printed/PDF page 9, with the proof in Section 23 on
printed/PDF page 63. The published paper is in *Proceedings of the London
Mathematical Society* (3) 82 (2001), 441–512. The reverse construction on
page 63 descends the original index and right coefficient actions to the
operator Hom colimit; here the coefficient is the representation sphere.

`reverseFunctor` takes an unbundled original continuous enriched I-space
`X`, a sphere transformation `t`, and its explicit unit `hu` and
associativity `ha` equations. It proves the complete object and Hom fields
form a functor on the existing native continuous coend operator index.
The accompanying morphism construction takes an actual source morphism
and its sphere-preservation equation. All index actions, coefficient
profiles, maps and independent native universes are retained.

The bundled right-module/category equivalence of Theorem 2.2, the
identification with the MMSS Thom Hom topology, and model-category
comparisons are separate unfinished targets. The downstream reconstruction
endofunctor and its natural isomorphism to native identity use the actual
existing restriction and equality comparisons; they do not assert those
separate results.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open CategoryTheory.Spectra CategoryTheory.Enriched.SphereOperator
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceOperatorFunctor

/-- The original orthogonal index category. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original block-sum monoidal structure on orthogonal indices. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The original pointed CGWH enriched ordinary structure on orthogonal indices. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original block symmetry on orthogonal indices. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}

attribute [local instance] Enriched.prodCategory

private theorem enrichedFunctor_eq_of_data
    (F G : EnrichedFunctor PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v} PointedCGWH.{u, v})
    (ho : F.obj = G.obj) (hm : HEq F.map G.map) : F = G := by
  cases F
  cases G
  cases ho
  cases hm
  rfl

variable
  (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
  (t : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj (𝟙_ PointedCGWH.{u, v}))
    (X.toEnrichedFunctor.externalTensor orthogonalSphereFunctor.{u, v})
    (OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor.comp
      PointedCGWH.{u, v} X.toEnrichedFunctor))
  (hu : ∀ n : OrthogonalIndex,
    (X.toEnrichedFunctor.obj n ◁ orthogonalSphereMonoidalData.{u, v}.epsilon) ≫
      Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n 0 ≫
      X.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom =
        (ρ_ (X.toEnrichedFunctor.obj n)).hom)
  (ha : ∀ n a b : OrthogonalIndex,
    (α_ (X.toEnrichedFunctor.obj n) (PointedCGWH.orthogonalSphere.{u, v} a)
      (PointedCGWH.orthogonalSphere.{u, v} b)).inv ≫
      (Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a ▷
          PointedCGWH.orthogonalSphere.{u, v} b) ≫
        Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
          orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t (n + a) b =
    (X.toEnrichedFunctor.obj n ◁ orthogonalSphereMonoidalData.{u, v}.mu a b) ≫
      Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n (a + b) ≫
          X.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n a b).inv)

/-- The original whole coend fields form a genuine functor using the original source laws. -/
def reverseFunctor : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) where
  toEnrichedFunctor :=
    { obj := fun n => X.toEnrichedFunctor.obj n.asIndex
      map := fun n k => reverseOperatorMapField.{u, v} X t n.asIndex k.asIndex
      map_id := fun n =>
        CanonicalSourceUnitCompatibility.reverseOperatorMapField_unit X t hu n.asIndex
      map_comp := fun ⟨n⟩ ⟨k⟩ ⟨l⟩ =>
        CanonicalSourceCompositionCompatibility.reverseOperatorMapField_comp X t ha n k l }

/-- Every original source value is literally the value of the assembled reverse functor. -/
theorem reverseFunctor_obj (n : OrthogonalIndex) :
    (reverseFunctor X t hu ha).toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) =
      X.toEnrichedFunctor.obj n := rfl

/-- The whole native map function is the literal original all-index coend supplier. -/
theorem reverseFunctor_fullMap :
    (reverseFunctor X t hu ha).toEnrichedFunctor.map =
      fun (n k : OrthogonalOperatorIndex.{u, v}) =>
        reverseOperatorMapField.{u, v} X t n.asIndex k.asIndex := rfl

/-- Uncurrying every native field gives the entire original reverse coend action. -/
theorem reverseFunctor_action (n k : OrthogonalIndex) :
    MonoidalClosed.uncurry ((reverseFunctor X t hu ha).toEnrichedFunctor.map
      (OrthogonalOperatorIndex.ofIndex.{u, v} n) (OrthogonalOperatorIndex.ofIndex.{u, v} k)) =
        reverseOperatorAction.{u, v} X t n k :=
  Reconstruction.uncurry_enrichedMapField OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t PointedCGWH.isSeparator_tensorUnit n k

/-- The original canonical restriction supplies its actual source sphere laws. -/
def originalReverseFunctor
    (F : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})) :
    (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
  reverseFunctor ((restrictionFunctor.{u, v}).obj F) (sphereTransformation.{u, v} F)
    (CanonicalSourceUnitCompatibility.original_source_unit F)
    (CanonicalSourceCoefficientCompatibility.original_source_assoc F)

/-- The reconstructed original functor has exactly all original operator values. -/
theorem originalReverseFunctor_obj
    (F : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))
    (n : OrthogonalOperatorIndex.{u, v}) :
    (originalReverseFunctor F).toEnrichedFunctor.obj n = F.toEnrichedFunctor.obj n := rfl

/-- Both entire original Hom map functions agree after source restriction and reconstruction. -/
theorem originalReverseFunctor_fullMap
    (F : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})) :
    (originalReverseFunctor F).toEnrichedFunctor.map = F.toEnrichedFunctor.map := by
  funext n k
  exact reverseOperatorMapField_original.{u, v} F n.asIndex k.asIndex

/-- The original whole operator functor is recovered as the same bundled enriched functor. -/
theorem originalReverseFunctor_eq
    (F : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})) :
    originalReverseFunctor F = F := by
  have h : (originalReverseFunctor F).toEnrichedFunctor = F.toEnrichedFunctor :=
    enrichedFunctor_eq_of_data _ _ rfl (heq_of_eq (originalReverseFunctor_fullMap F))
  exact congrArg (fun G : EnrichedFunctor PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}
    PointedCGWH.{u, v} =>
      (⟨G⟩ : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))) h

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceOperatorFunctor
