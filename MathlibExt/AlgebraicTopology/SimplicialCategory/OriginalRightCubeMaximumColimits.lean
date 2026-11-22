/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeRealizationMaximum
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeRealizationCofibrations
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceCoproducts
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.OriginalRealizationWeakFilteredUniverses
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AllCofibrant

/-!
# Genuine original maximum comparison under actual cells and colimits

The SAME full original natural maximum comparison is weak on
actual mono pushouts, whole coefficient coproducts and filtered
colimits whenever its existing source components are weak. Each
proof retains the supplied full cocones and original target map.
-/

noncomputable section
universe u v w
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.CoherentRealization.OriginalRightCubeRealization

/-- The SAME actual maximum is weak on a genuine mono pushout once it is weak on all three original span objects. -/
theorem maximum_weak_of_isPushout
    {A B X P : SSet.{u}} {i : A ⟶ B} {g : A ⟶ X} {p : B ⟶ P} {q : X ⟶ P}
    (sq : IsPushout i g p q) [Mono i]
    (hA : SSet.realizationWeakEquivalences (maximum A))
    (hB : SSet.realizationWeakEquivalences (maximum B))
    (hX : SSet.realizationWeakEquivalences (maximum X)) :
    SSet.realizationWeakEquivalences (maximum P) := by
  let _ : Cofibration i := (SSet.modelCategoryQuillen.cofibration_iff i).mpr inferInstance
  let _ : Mono (map i) := map_mono i
  let _ : Cofibration (map i) := (SSet.modelCategoryQuillen.cofibration_iff (map i)).mpr inferInstance
  let _ : Cofibration (functor.map i) :=
    (SSet.modelCategoryQuillen.cofibration_iff (functor.map i)).mpr (map_mono i)
  let _ : WeakEquivalence (maximum A) := (weakEquivalence_iff _).mpr hA
  let _ : WeakEquivalence (maximum B) := (weakEquivalence_iff _).mpr hB
  let _ : WeakEquivalence (maximum X) := (weakEquivalence_iff _).mpr hX
  have sq' : IsPushout (map i) (map g) (map p) (map q) := sq.map functor
  exact (weakEquivalence_iff _).mp
    (weakEquivalence_map_of_isPushouts_of_cofibrant sq' sq
      (maximum_naturality i) (maximum_naturality g) (maximum_naturality p) (maximum_naturality q))

/-- The SAME actual maximum is weak on the entire supplied original same-universe coefficient coproduct. -/
theorem maximum_weak_of_cofan {I : Type u} (X : I → SSet.{u})
    (c : Cofan X) (hc : IsColimit c)
    (hX : ∀ i, SSet.realizationWeakEquivalences (maximum (X i))) :
    SSet.realizationWeakEquivalences (maximum c.pt) := by
  let α := Functor.whiskerLeft (Discrete.functor X) maximumNatTrans
  exact MorphismProperty.IsStableUnderColimitsOfShape.condition
    ((Discrete.functor X) ⋙ functor) (Discrete.functor X)
    (functor.mapCocone c) c (isColimitOfPreserves functor hc) hc α
    (fun i => hX i.as) (maximum c.pt)
    (fun i => maximum_naturality (c.ι.app i))

/-- The SAME actual maximum is weak on every supplied full filtered colimit at independent small indexing universes. -/
theorem maximum_weak_of_filtered_cocone
    {J : Type v} [Category.{w} J] [IsFiltered J] [UnivLE.{v,u}] [UnivLE.{w,u}]
    (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, SSet.realizationWeakEquivalences (maximum (F.obj j))) :
    SSet.realizationWeakEquivalences (maximum c.pt) := by
  let α := Functor.whiskerLeft F maximumNatTrans
  exact SSet.realizationWeakEquivalences.of_isColimit_filtered_univLE α
    (isColimitOfPreserves functor hc) hc (maximum c.pt)
    (fun j => maximum_naturality (c.ι.app j)) hF

end CategoryTheory.CoherentRealization.OriginalRightCubeRealization
