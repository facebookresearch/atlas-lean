/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SourceRightModuleActions
import MathlibExt.CategoryTheory.Enriched.SphereOperatorRightShiftAction
import MathlibExt.Topology.Category.PointedCGWH.Points

/-!
# Right shifts on the full continuous orthogonal operator category

The original coend shift is constructed over arbitrary enriched monoidal
index data, before specializing to the actual continuous orthogonal index
and representation sphere. It retains every complete Hom object, generator,
unit and composition map. The native block exchange keeps all associators
and the actual isometry in both directions. Lawful labelled action squares
are promoted to genuine enriched transformations by the proved native unit
separator, retaining the entire sphere coefficient and continuous weight.
This is the right-shift part of the MMSS Sections 1–3 and Example 4.4
free-function construction.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Spectra CategoryTheory.Enriched CategoryTheory.Enriched.SphereOperator
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.RightShift.Internal

-- Compatibility names for the canonical enriched right-shift implementation.
export CategoryTheory.Enriched.SphereOperator.RightShift
  (shift action action_eq_braid coefficientHom_shift shift_action action_postcompose blockSwap blockSwap_inv
    blockSwap_label adjoint adjoint_postcompose shift_adjoint cotensor_action)

end PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.RightShift.Internal

universe u v
namespace PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.RightShift

/-- The actual continuous orthogonal index category. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original block-sum monoidal structure on the orthogonal index. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The genuine continuous enriched structure on the orthogonal index. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original continuous block-exchange symmetry. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}

private abbrev d := OrthogonalIndex.enrichedMonoidalData.{u, v}
private abbrev S := orthogonalSphereFunctor.{u, v}
private abbrev L := orthogonalSphereMonoidalData.{u, v}

/-- The full original native enriched operator-functor carrier. -/
abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}

/-- The original ordinary isometry arrows retain their two independent native universes. -/
abbrev Arrow (n k : OrthogonalIndex) :=
  @Quiver.Hom OrthogonalIndex (OrthogonalIndex.category.{u, v}).toQuiver n k

/-- The unchanged original source I-space is restriction along the actual delta. -/
abbrev bare (F : Carrier.{u, v}) : OrthogonalIndex ⥤ PointedCGWH.{u, v} :=
  ((OrthogonalSourceRightModule.restrictionFunctor.{u, v}).obj
    F).toEnrichedFunctor.toOrdinaryFunctor

/-- The actual enriched native right-shift index functor uses the original coend maps. -/
abbrev indexShift (r : OrthogonalIndex) :
    EnrichedFunctor PointedCGWH.{u, v}
      OrthogonalOperatorIndex.{u, v} OrthogonalOperatorIndex.{u, v} :=
  GenericRightTensor.indexShift d.{u, v} S.{u, v} L.{u, v} r

/-- The genuine native right shift restricts through that whole enriched index functor. -/
abbrev shift (r : OrthogonalIndex) : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  Internal.shift d.{u, v} S.{u, v} L.{u, v} r

/-- The entire original coend Hom map, before any generator is selected. -/
abbrev hom (r n k : OrthogonalIndex) :
    OrthogonalOperatorIndex.hom.{u, v} n k ⟶
      OrthogonalOperatorIndex.hom.{u, v} (n + r) (k + r) :=
  GenericRightTensor.hom d.{u, v} S.{u, v} r n k

/-- Every full native sphere coefficient acts by the original coefficient-first map. -/
abbrev action (F : Carrier.{u, v}) (n k a : OrthogonalIndex)
    (f : Arrow.{u, v} (a + n) k) :
    S.{u, v}.obj a ⊗ F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) ⟶
      F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} k) :=
  Internal.action d.{u, v} S.{u, v} L.{u, v} F n k a f

/-- Every original index label is extended by the original final block and inverse associator. -/
abbrev label (r n k a : OrthogonalIndex) (f : Arrow.{u, v} (a + n) k) :
    Arrow.{u, v} (a + (n + r)) (k + r) := GenericRightTensor.label r n k a f

/-- The complete original source action transpose at every index and coefficient degree. -/
abbrev adjoint (F : Carrier.{u, v}) (n k a : OrthogonalIndex)
    (f : Arrow.{u, v} (a + n) k) :
    F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) ⟶
      (ihom (S.{u, v}.obj a)).obj
        (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} k)) :=
  Internal.adjoint d.{u, v} S.{u, v} L.{u, v} F n k a f

/-- The original three-block isometry exchanges the final two index blocks. -/
abbrev blockSwap (r n a : OrthogonalIndex) :
    @Iso OrthogonalIndex OrthogonalIndex.category.{u, v}
      ((n + r) + a) ((n + a) + r) := Internal.blockSwap r n a

/-- The source's reverse block exchange retains both associators and the actual reverse isometry. -/
theorem blockSwap_inv (r n a : OrthogonalIndex) :
    (blockSwap r n a).inv = (α_ n a r).hom ≫
      (n ◁ (β_ a r).hom) ≫ (α_ n r a).inv := Internal.blockSwap_inv r n a

/-- The original shifted stabilization label retains the actual full three-block exchange. -/
theorem blockSwap_label (r n a : OrthogonalIndex) :
    label r n (n + a) a (β_ a n).hom =
      (β_ a (n + r)).hom ≫ (blockSwap r n a).hom := Internal.blockSwap_label r n a

/-- Every original source space is the unchanged space at the original shifted index. -/
theorem shift_obj (r n : OrthogonalIndex) (F : Carrier.{u, v}) :
    ((shift r).obj F).toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) =
      F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r)) := rfl

/-- Every whole shifted native transformation retains its entire original component. -/
theorem shift_map_component (r n : OrthogonalIndex) {F G : Carrier.{u, v}} (q : F ⟶ G) :
    component ((shift r).map q) (OrthogonalOperatorIndex.ofIndex.{u, v} n) =
      component q (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r)) :=
  restrictionMap_component (indexShift r) q (OrthogonalOperatorIndex.ofIndex n)

/-- The whole original native Hom acts through the original complete coend shift map. -/
theorem shift_fullHom (r n k : OrthogonalIndex) (F : Carrier.{u, v}) :
    ((shift r).obj F).toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (OrthogonalOperatorIndex.ofIndex.{u, v} k) = hom r n k ≫
      F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r))
        (OrthogonalOperatorIndex.ofIndex.{u, v} (k + r)) := rfl

/-- All original source, target and coefficient actions survive the genuine right shift. -/
theorem shift_action (F : Carrier.{u, v}) (r n k a : OrthogonalIndex)
    (f : Arrow.{u, v} (a + n) k) :
    action ((shift r).obj F) n k a f = action F (n + r) (k + r) a (label r n k a f) :=
  Internal.shift_action d.{u, v} S.{u, v} L.{u, v} F r n k a f

/-- Every original full coefficient action keeps the exact source target isometry. -/
theorem action_target (F : Carrier.{u, v}) (n k l a : OrthogonalIndex)
    (f : Arrow.{u, v} (a + n) k) (g : Arrow.{u, v} k l) :
    action F n k a f ≫ (bare F).map g = action F n l a (f ≫ g) :=
  Internal.action_postcompose d.{u, v} S.{u, v} L.{u, v} F n k l a f g

/-- Every source, shift and added-degree triple retains its Omega transpose and target block map. -/
theorem shift_adjoint (F : Carrier.{u, v}) (r n a : OrthogonalIndex) :
    adjoint ((shift r).obj F) n (n + a) a (β_ a n).hom =
      adjoint F (n + r) ((n + r) + a) a (β_ a (n + r)).hom ≫
      (ihom (S.{u, v}.obj a)).map ((bare F).map (blockSwap r n a).hom) :=
  Internal.shift_adjoint d.{u, v} S.{u, v} L.{u, v} F r n a

private theorem ofIndex_asIndex (n : OrthogonalOperatorIndex.{u, v}) :
    OrthogonalOperatorIndex.ofIndex.{u, v} n.asIndex = n := by
  cases n
  rfl

private theorem remove_braid (A X Y T U : PointedCGWH.{u, v}) (q : X ⟶ Y) (t : T ⟶ U)
    (f : X ⊗ A ⟶ T) (g : Y ⊗ A ⟶ U)
    (h : (β_ A X).hom ≫ f ≫ t = (A ◁ q) ≫ (β_ A Y).hom ≫ g) :
    f ≫ t = (q ▷ A) ≫ g := by
  apply (cancel_epi (β_ A X).hom).1
  exact h.trans (by simpa only [Category.assoc] using
    (congrArg (fun z => z ≫ g) (braiding_naturality_right A q)))

/-- A whole labelled action square gives its exact original curried coefficient square. -/
theorem curried_label_naturality (F G : Carrier.{u, v})
    (q : ∀ n : OrthogonalIndex,
      F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) ⟶
        G.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n))
    (a n k : OrthogonalIndex) (f : Arrow.{u, v} (a + n) k)
    (h : action F n k a f ≫ q k = (S.{u, v}.obj a ◁ q n) ≫ action G n k a f) :
    (coefficientHom d.{u, v} S.{u, v} n k a f ≫
      F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
        (OrthogonalOperatorIndex.ofIndex.{u, v} k)) ≫
      (ihom (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n))).map (q k) =
    (coefficientHom d.{u, v} S.{u, v} n k a f ≫
      G.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
        (OrthogonalOperatorIndex.ofIndex.{u, v} k)) ≫
      (MonoidalClosed.pre (q n)).app
        (G.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} k)) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_pre_app]
  exact remove_braid _ _ _ _ _ (q n) (q k) _ _ h

/-- All continuous source labels determine naturality on the entire original coend Hom object. -/
theorem full_curried_naturality (F G : Carrier.{u, v})
    (q : ∀ n : OrthogonalIndex,
      F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) ⟶
        G.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n))
    (h : ∀ a n k : OrthogonalIndex, ∀ f : Arrow.{u, v} (a + n) k,
      action F n k a f ≫ q k = (S.{u, v}.obj a ◁ q n) ≫ action G n k a f)
    (n k : OrthogonalIndex) :
    F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (OrthogonalOperatorIndex.ofIndex.{u, v} k) ≫
      (ihom (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n))).map (q k) =
    G.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (OrthogonalOperatorIndex.ofIndex.{u, v} k) ≫
      (MonoidalClosed.pre (q n)).app
        (G.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} k)) := by
  apply weightedCoend.hom_ext (weight d.{u, v} n k) S.{u, v}
  intro a
  apply PointedCGWH.tensorLeftPoint_hom_ext
  intro p
  obtain ⟨f, rfl⟩ := (eHomEquiv PointedCGWH.{u, v}).surjective p
  let j := (λ_ (S.{u, v}.obj a)).inv ≫
    (eHomEquiv PointedCGWH.{u, v} f ⊗ₘ 𝟙 (S.{u, v}.obj a))
  let i := weightedCoend.ι (weight d.{u, v} n k) S.{u, v} a
  let fm := F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
    (OrthogonalOperatorIndex.ofIndex.{u, v} k)
  let gm := G.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
    (OrthogonalOperatorIndex.ofIndex.{u, v} k)
  let t := (ihom (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n))).map
    (q k)
  let s := (MonoidalClosed.pre (q n)).app
    (G.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} k))
  have hc := curried_label_naturality F G q a n k f (h a n k f)
  change ((j ≫ i) ≫ fm) ≫ t = ((j ≫ i) ≫ gm) ≫ s at hc
  change j ≫ i ≫ (fm ≫ t) = j ≫ i ≫ (gm ≫ s)
  have hc' : (j ≫ i) ≫ (fm ≫ t) = (j ≫ i) ≫ (gm ≫ s) :=
    (Category.assoc (j ≫ i) fm t).symm.trans
      (hc.trans (Category.assoc (j ≫ i) gm s))
  exact (Category.assoc j i (fm ≫ t)).symm.trans
    (hc'.trans (Category.assoc j i (gm ≫ s)))

/-- Full source label squares construct a genuine continuous enriched transformation. -/
def transformation (F G : Carrier.{u, v})
    (q : ∀ n : OrthogonalOperatorIndex.{u, v},
      F.toEnrichedFunctor.obj n ⟶ G.toEnrichedFunctor.obj n)
    (h : ∀ a n k : OrthogonalIndex, ∀ f : Arrow.{u, v} (a + n) k,
      action F n k a f ≫ q (OrthogonalOperatorIndex.ofIndex.{u, v} k) =
        (S.{u, v}.obj a ◁ q (OrthogonalOperatorIndex.ofIndex.{u, v} n)) ≫ action G n k a f) :
    F ⟶ G :=
  GradedNatTrans.unitOfComponents q (by
    intro n k
    rcases n with ⟨n⟩
    rcases k with ⟨k⟩
    rw [tensorHom_id]
    change MonoidalClosed.uncurry
        (F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
          (OrthogonalOperatorIndex.ofIndex.{u, v} k)) ≫
        q (OrthogonalOperatorIndex.ofIndex.{u, v} k) =
      (q (OrthogonalOperatorIndex.ofIndex.{u, v} n) ▷
        (OrthogonalOperatorIndex.ofIndex.{u, v} n ⟶[PointedCGWH.{u, v}]
          OrthogonalOperatorIndex.ofIndex.{u, v} k)) ≫
        MonoidalClosed.uncurry
          (G.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
            (OrthogonalOperatorIndex.ofIndex.{u, v} k))
    have hc := congrArg MonoidalClosed.uncurry (full_curried_naturality F G
      (fun n => q (OrthogonalOperatorIndex.ofIndex.{u, v} n)) h n k)
    exact (MonoidalClosed.uncurry_natural_right _ _).symm.trans
      (hc.trans (MonoidalClosed.uncurry_pre_app _ _ _)))

/-- The genuine transformation retains every original supplied level map. -/
theorem transformation_component (F G : Carrier.{u, v})
    (q : ∀ n : OrthogonalOperatorIndex.{u, v},
      F.toEnrichedFunctor.obj n ⟶ G.toEnrichedFunctor.obj n)
    (h : ∀ a n k : OrthogonalIndex, ∀ f : Arrow.{u, v} (a + n) k,
      action F n k a f ≫ q (OrthogonalOperatorIndex.ofIndex.{u, v} k) =
        (S.{u, v}.obj a ◁ q (OrthogonalOperatorIndex.ofIndex.{u, v} n)) ≫ action G n k a f)
    (n : OrthogonalOperatorIndex.{u, v}) : component (transformation F G q h) n = q n :=
  GradedNatTrans.unitOfComponents_component _ _ n

/-- The complete scalar cotensor action retains the actual coefficient shuffle and evaluation. -/
theorem cotensor_action (F : Carrier.{u, v}) (M : PointedCGWH.{u, v})
    (n k a : OrthogonalIndex) (f : Arrow.{u, v} (a + n) k) :
    action (cotensorObject M F) n k a f = MonoidalClosed.curry
      (NativeOmegaPreparation.CoefficientShuffle.map M (S.{u, v}.obj a)
        ((ihom M).obj (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n))) ≫
      (S.{u, v}.obj a ◁ (ihom.ev M).app
        (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n))) ≫ action F n k a f) :=
  Internal.cotensor_action d.{u, v} S.{u, v} L.{u, v} F M n k a f

end PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.RightShift
