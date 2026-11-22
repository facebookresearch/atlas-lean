/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalFunctorUniversal
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneFunctorDerivedUniversal

/-!
# The entire derived scalar mapping-space comparison

Every scalar source is kept in a functor, with independently fixed actual
scalar Q/R records. The original closed core comparison is weak after these
records. The strict original carrier identification and the already proved
one-fold universal mapping-space comparison identify precisely the same
original Q/R end. Changing scalar conventions retains their actual maps.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalClosed Opposite
open scoped MonoidalCategory SimplicialSpace.Cartesian SSet.modelCategoryQuillen
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived

namespace SimplicialSpace.FirstProjection

private abbrev H : SSet.{u} ⥤ SSet.realizationWeakEquivalences.{u}.Localization :=
  SSet.realizationWeakEquivalences.Q
private abbrev Scalar := SimplicialPresheaf.ScalarCoreReplacementSpans.ScalarConventions.{u}
private abbrev Targets := SimplicialPresheaf.OrderedJFS.OneFunctor.Core.LocalTargets.{u}

private local instance sourceLocallySmall : LocallySmall.{u} (FinitePowerSite.Source 1) :=
  @CategoryTheory.locallySmall_of_univLE _ _ UnivLE.zero

/-- The actual scalar Q-source and R-target mapping spaces, for every source K. -/
def fixedSpaceFunctor (e : Scalar.{u}) (X : SSet.{u}) : SSet.{u}ᵒᵖ ⥤ SSet.{u} :=
  e.Q.op ⋙ MonoidalClosed.internalHom ⋙ (CategoryTheory.evaluation SSet.{u} SSet.{u}).obj (e.R.obj X)

/-- The target action is the original R-map under the original Q-source internal Hom. -/
def fixedSpaceMap (e : Scalar.{u}) {X Y : SSet.{u}} (f : X ⟶ Y) :
    fixedSpaceFunctor e X ⟶ fixedSpaceFunctor e Y where
  app K := (ihom (e.Q.obj K.unop)).map (e.R.map f)
  naturality _ _ k := ((pre (e.Q.map k.unop)).naturality (e.R.map f)).symm

/-- These actual fixed mapping functions form a functor of their target objects. -/
def fixedSpaceObjects (e : Scalar.{u}) : SSet.{u} ⥤ (SSet.{u}ᵒᵖ ⥤ SSet.{u}) where
  obj X := fixedSpaceFunctor e X
  map f := fixedSpaceMap e f
  map_id X := by
    apply NatTrans.ext
    funext K
    change (ihom (e.Q.obj K.unop)).map (e.R.map (𝟙 X)) = 𝟙 _
    rw [e.R.map_id]
    exact (ihom (e.Q.obj K.unop)).map_id (e.R.obj X)
  map_comp f g := by
    apply NatTrans.ext
    funext K
    change (ihom (e.Q.obj K.unop)).map (e.R.map (f ≫ g)) = _
    rw [e.R.map_comp]
    exact (ihom (e.Q.obj K.unop)).map_comp (e.R.map f) (e.R.map g)

private theorem fixedSpaceMap_weak (e : Scalar.{u}) {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.realizationWeakEquivalences f) (K : SSet.{u}) :
    SSet.realizationWeakEquivalences ((fixedSpaceMap e f).app (op K)) := by
  have hr : SSet.realizationWeakEquivalences (e.R.map f) := by
    have hx : SSet.realizationWeakEquivalences (e.r.app X) := (e.r_trivialCofibration X).2
    have hy : SSet.realizationWeakEquivalences (e.r.app Y) := (e.r_trivialCofibration Y).2
    apply SSet.realizationWeakEquivalences.of_precomp _ _ hx
    have hn : f ≫ e.r.app Y = e.r.app X ≫ e.R.map f := e.r.naturality f
    rw [← hn]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ hf hy
  let _ : IsFibrant (e.R.obj X) := e.R_isFibrant X
  let _ : IsFibrant (e.R.obj Y) := e.R_isFibrant Y
  let _ : WeakEquivalence (e.R.map f) := (weakEquivalence_iff _).mpr hr
  let _ : (ihom.adjunction (e.Q.obj K)).IsQuillenAdjunction :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant _
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
      (adj := ihom.adjunction (e.Q.obj K)) (e.R.map f))

/-- All fixed scalar mapping spaces into the actual CSS power core. -/
def cssFixedCoreSpaces (e : Scalar.{u}) (W V : SimplicialSpace.{u}) :=
  fixedSpaceFunctor e (SSet.coreFunctor.obj (right.obj ((ihom W).obj V))) ⋙ H.{u}

/-- All fixed scalar mapping spaces into the actual native Joyal functor core. -/
def nativeFixedCoreSpaces (e : Scalar.{u}) (W V : SimplicialSpace.{u}) :=
  fixedSpaceFunctor e (functorCore W V) ⋙ H.{u}

/-- The literal closed comparison acts through the same fixed scalar Q/R records. -/
def fixedCoreComparison (e : Scalar.{u}) (W V : SimplicialSpace.{u}) :
    cssFixedCoreSpaces e W V ⟶ nativeFixedCoreSpaces e W V :=
  Functor.whiskerRight (fixedSpaceMap e (SSet.coreFunctor.map (comparison W V))) H

/-- Every fixed scalar component is weak by the actual core comparison and the original scalar units. -/
theorem fixedCoreComparison_weak (e : Scalar.{u}) (K : SSet.{u}) (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    SSet.realizationWeakEquivalences
      ((fixedSpaceMap e (SSet.coreFunctor.map (comparison W V))).app (op K)) :=
  fixedSpaceMap_weak e _ (comparison_coreWeak W V hW hV) K

/-- One natural Iso identifies every scalar mapping space of both actual functor cores. -/
def fixedCoreComparisonNatIso (e : Scalar.{u}) (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    cssFixedCoreSpaces e W V ≅ nativeFixedCoreSpaces e W V := by
  let _ : ∀ K : SSet.{u}ᵒᵖ, IsIso ((fixedCoreComparison e W V).app K) := fun K =>
    Localization.inverts H.{u} SSet.realizationWeakEquivalences _
      (fixedCoreComparison_weak e K.unop W V hW hV)
  let _ : IsIso (fixedCoreComparison e W V) := NatIso.isIso_of_isIso_app _
  exact asIso (fixedCoreComparison e W V)

private def originalFixedSpacesIso (e : Scalar.{u}) (W V : SimplicialSpace.{u})
    (hV : completeSegalSpaces V) :
    fixedSpaceFunctor e
        ((SimplicialPresheaf.OrderedJFS.OneFunctor.Core.nativeCoreFunctor (originalImage W)).obj
          (originalImage V)) ⋙ H.{u} ≅
      (SimplicialPresheaf.OrderedJFS.OneFunctor.Core.nativeScalarSpaces (originalImage W) e ⋙
        (SimplicialPresheaf.CoreUniversalMapping.localizeValues (SimplicialPresheaf.OrderedJFS.originalFamily.{u} 1))) ⋙
          (CategoryTheory.evaluation Targets.{u} SSet.realizationWeakEquivalences.{u}.Localization).obj
            ⟨originalImage V, originalImage_local V hV⟩ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro K L k
    change H.{u}.map ((pre (e.Q.map k.unop)).app
        (e.R.obj ((SimplicialPresheaf.OrderedJFS.OneFunctor.Core.nativeCoreFunctor (originalImage W)).obj
          (originalImage V)))) ≫ 𝟙 _ =
      𝟙 _ ≫ H.{u}.map ((pre (e.Q.map k.unop)).app
        (e.R.obj ((SimplicialPresheaf.OrderedJFS.OneFunctor.Core.nativeCoreFunctor (originalImage W)).obj
          (originalImage V))))
    rw [Category.comp_id, Category.id_comp])

/-- All scalar maps into the same original derived end, retaining its original Q/R functions. -/
def originalDerivedSpaces (e : Scalar.{u}) (W V : SimplicialSpace.{u}) (hV : completeSegalSpaces V) :=
  (SimplicialPresheaf.OrderedJFS.OneFunctor.Core.derivedScalarSpaces (originalImage W) e ⋙
    (SimplicialPresheaf.CoreUniversalMapping.localizeValues (SimplicialPresheaf.OrderedJFS.originalFamily.{u} 1))) ⋙
      (CategoryTheory.evaluation Targets.{u} SSet.realizationWeakEquivalences.{u}.Localization).obj
        ⟨originalImage V, originalImage_local V hV⟩

/-- The native Joyal functor core gives the entire original derived scalar mapping-space functor. -/
def fixedDerivedMappingNatIso (e : Scalar.{u}) (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    nativeFixedCoreSpaces e W V ≅ originalDerivedSpaces e W V hV :=
  (fixedCoreComparisonNatIso e W V hW hV).symm ≪≫
    Functor.isoWhiskerRight ((fixedSpaceObjects e).mapIso (originalNativeCoreIso W V)).symm H ≪≫
      originalFixedSpacesIso e W V hV ≪≫
        Functor.isoWhiskerRight
          (SimplicialPresheaf.OrderedJFS.OneFunctor.Core.nativeDerivedNatIso (originalImage W) e)
          ((CategoryTheory.evaluation Targets.{u} SSet.realizationWeakEquivalences.{u}.Localization).obj
            ⟨originalImage V, originalImage_local V hV⟩)

/-- Two actual scalar convention records give the same whole native universal function. -/
def fixedScalarConventionsChange (e e' : Scalar.{u}) (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    nativeFixedCoreSpaces e W V ≅ nativeFixedCoreSpaces e' W V :=
  fixedDerivedMappingNatIso e W V hW hV ≪≫
    Functor.isoWhiskerRight
      (SimplicialPresheaf.OrderedJFS.OneFunctor.Core.changeScalarConventionsNatIso (originalImage W) e e')
      ((CategoryTheory.evaluation Targets.{u} SSet.realizationWeakEquivalences.{u}.Localization).obj
        ⟨originalImage V, originalImage_local V hV⟩) ≪≫
      (fixedDerivedMappingNatIso e' W V hW hV).symm

/-- Scalar-choice independence retains the same original derived universal comparison. -/
private theorem changeIsoTriangle {C : Type*} [Category C] {X Y Z T : C}
    (a : X ≅ Y) (b : Y ≅ Z) (c : T ≅ Z) :
    (a ≪≫ b ≪≫ c.symm).hom ≫ c.hom = a.hom ≫ b.hom := by
  change (a.hom ≫ (b.hom ≫ c.inv)) ≫ c.hom = _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Scalar-choice independence retains the same original derived universal comparison. -/
theorem fixedScalarConventionsChange_triangle (e e' : Scalar.{u}) (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    (fixedScalarConventionsChange e e' W V hW hV).hom ≫ (fixedDerivedMappingNatIso e' W V hW hV).hom =
      (fixedDerivedMappingNatIso e W V hW hV).hom ≫
        (Functor.isoWhiskerRight
          (SimplicialPresheaf.OrderedJFS.OneFunctor.Core.changeScalarConventionsNatIso (originalImage W) e e')
          ((CategoryTheory.evaluation Targets.{u} SSet.realizationWeakEquivalences.{u}.Localization).obj
            ⟨originalImage V, originalImage_local V hV⟩)).hom := by
  exact changeIsoTriangle (fixedDerivedMappingNatIso e W V hW hV)
    (Functor.isoWhiskerRight
      (SimplicialPresheaf.OrderedJFS.OneFunctor.Core.changeScalarConventionsNatIso (originalImage W) e e')
      ((CategoryTheory.evaluation Targets.{u} SSet.realizationWeakEquivalences.{u}.Localization).obj
        ⟨originalImage V, originalImage_local V hV⟩)) (fixedDerivedMappingNatIso e' W V hW hV)

end SimplicialSpace.FirstProjection
