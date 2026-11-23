/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCore
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanAugmentationRowsWeakOf
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveIndependentHomEquivalenceWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanDiagonalTotal
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceChains

/-!
# The native cover bar augmentation to its original base

The original endomorphism group acts by the existing native deck maps.
Its Bousfield--Kan augmentation uses the original cover projection. For a
connected Kan base, each scalar elements projection is an equivalence:
the native cover is onto original simplices, and deck transport is unique.
The existing row, diagonal, and signed shuffle comparisons then identify
the actual total homology with the homology of the original base.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v uA vA

namespace SSet.KanComplex

/-- The original native cover and deck maps, indexed by the literal
one-object category of the fundamental-groupoid endomorphism group. -/
def nativeCoverDeckFunctor (X : SSet.{u}) (x : X _⦋0⦌) :
    SingleObj (End (SSet.FundamentalGroupoid.mk x)) ⥤ SSet.{u} where
  obj _ := nativeCover X x
  map g := nativeCoverDeckMap g
  map_id _ := nativeCoverDeckMap_one
  map_comp f g := nativeCoverDeckMap_mul g f

/-- The diagram retains every original deck map. -/
@[simp]
theorem nativeCoverDeckFunctor_map (X : SSet.{u}) (x : X _⦋0⦌)
    {j j' : SingleObj (End (SSet.FundamentalGroupoid.mk x))} (g : j ⟶ j') :
    (nativeCoverDeckFunctor X x).map g = nativeCoverDeckMap g := rfl

/-- The original cover projection is a cocone for the literal deck diagram. -/
def nativeCoverProjectionCocone (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeCoverDeckFunctor X x ⟶
      (Functor.const (SingleObj (End (SSet.FundamentalGroupoid.mk x)))).obj X where
  app _ := nativeCoverProjection X x
  naturality _ _ g := by
    change nativeCoverDeckMap g ≫ nativeCoverProjection X x =
      nativeCoverProjection X x ≫ 𝟙 X
    rw [nativeCoverDeckMap_projection, Category.comp_id]

/-- Every cocone component is the original cover projection. -/
@[simp]
theorem nativeCoverProjectionCocone_app (X : SSet.{u}) (x : X _⦋0⦌)
    (j : SingleObj (End (SSet.FundamentalGroupoid.mk x))) :
    (nativeCoverProjectionCocone X x).app j = nativeCoverProjection X x := rfl

/-- The literal endomorphism deck action is free on every original cover simplex. -/
theorem nativeCoverDeckMap_app_free (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌)
    (n : ℕ) (s : (nativeCover X x) _⦋n⦌) :
    Function.Injective (fun g : End (SSet.FundamentalGroupoid.mk x) =>
      (nativeCoverDeckMap g).app (op ⦋n⦌) s) := by
  let e := piOneMulEquivFundamentalGroupoidEnd x
  let := nativeCoverPiOneSimplexAction x n
  intro g h hgh
  apply e.symm.injective
  apply nativeCoverPiOneSimplexAction_free x n s
  change (nativeCoverDeckMap (e (e.symm g))).app (op ⦋n⦌) s =
    (nativeCoverDeckMap (e (e.symm h))).app (op ⦋n⦌) s
  rw [e.apply_symm_apply, e.apply_symm_apply]
  exact hgh

/-- One unique original endomorphism transports two cover simplices with the
same original projected simplex. -/
theorem nativeCoverDeckMap_app_existsUnique_of_projection_eq
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) (n : ℕ)
    (s t : (nativeCover X x) _⦋n⦌)
    (hst : (nativeCoverProjection X x).app (op ⦋n⦌) s =
      (nativeCoverProjection X x).app (op ⦋n⦌) t) :
    ∃! g : End (SSet.FundamentalGroupoid.mk x),
      (nativeCoverDeckMap g).app (op ⦋n⦌) s = t := by
  let e := piOneMulEquivFundamentalGroupoidEnd x
  let := nativeCoverPiOneSimplexAction x n
  obtain ⟨a, ha, _⟩ := nativeCoverPiOneSimplexAction_existsUnique_of_projection_eq x n s t hst
  change (nativeCoverDeckMap (e a)).app (op ⦋n⦌) s = t at ha
  refine ⟨e a, ha, ?_⟩
  intro g hg
  exact nativeCoverDeckMap_app_free X x n s (hg.trans ha.symm)

/-- The actual scalar row projection keeps the original projected simplex. -/
theorem nativeCoverRowProjection_obj (X : SSet.{u}) (x : X _⦋0⦌)
    (q : SimplexCategoryᵒᵖ)
    (s : (SSet.BousfieldKanRowsOf.wbarDegreeCoefficient.{0, u, 0}
      (nativeCoverDeckFunctor X x) q).Elements) :
    (SSet.BousfieldKanRowsOf.rowProjection.{0, u, 0}
      (nativeCoverProjectionCocone X x) q).obj s =
        Discrete.mk ((nativeCoverProjection X x).app q s.val) := rfl

/-- For a connected Kan base, the canonical scalar elements projection is
an equivalence onto the original base simplices. -/
theorem nativeCoverRowProjection_isEquivalence (X : SSet.{u}) [KanComplex X]
    [X.IsConnected] (x : X _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    (SSet.BousfieldKanRowsOf.rowProjection.{0, u, 0}
      (nativeCoverProjectionCocone X x) q).IsEquivalence := by
  induction q using Opposite.rec with
  | _ q =>
    induction q using SimplexCategory.rec with
    | _ n =>
      let F := SSet.BousfieldKanRowsOf.rowProjection.{0, u, 0}
        (nativeCoverProjectionCocone X x) (op ⦋n⦌)
      let : F.Full :=
        { map_surjective := by
            intro s t f
            have hp : (nativeCoverProjection X x).app (op ⦋n⦌) s.val =
                (nativeCoverProjection X x).app (op ⦋n⦌) t.val := Discrete.eq_of_hom f
            obtain ⟨g, hg, _⟩ :=
              nativeCoverDeckMap_app_existsUnique_of_projection_eq X x n s.val t.val hp
            refine ⟨Functor.Elements.homMk g hg, Subsingleton.elim _ _⟩ }
      let : F.Faithful :=
        { map_injective := by
            intro s t f g _h
            apply Functor.Elements.hom_ext
            exact nativeCoverDeckMap_app_free X x n s.val (f.map_val.trans g.map_val.symm) }
      let : F.EssSurj :=
        { mem_essImage := by
            intro y
            obtain ⟨s, hs⟩ := nativeCoverProjection_app_surjective x n y.as
            refine ⟨(SSet.BousfieldKanRowsOf.wbarDegreeCoefficient.{0, u, 0}
              (nativeCoverDeckFunctor X x) (op ⦋n⦌)).elementsMk
                (SingleObj.star (End (SSet.FundamentalGroupoid.mk x))) s, ⟨?_⟩⟩
            exact Discrete.eqToIso hs }
      exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The canonical Bousfield--Kan augmentation uses the original native
projection and has the original simplicial set as its target. -/
def nativeCoverBarAugmentation (X : SSet.{u}) (x : X _⦋0⦌) :
    SSet.bkHocolim (nativeCoverDeckFunctor X x) ⟶ X :=
  SSet.bkAugmentation (nativeCoverProjectionCocone X x)

/-- On every original weighted summand, the augmentation is exactly the
original native cover projection. -/
theorem nativeCoverBarAugmentation_weighted (X : SSet.{u}) (x : X _⦋0⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx
      (SingleObj (End (SSet.FundamentalGroupoid.mk x)))
      (CategoryBar.replUnit (SingleObj (End (SSet.FundamentalGroupoid.mk x)))) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit (SingleObj (End (SSet.FundamentalGroupoid.mk x))))
      (nativeCoverDeckFunctor X x) n p).app (op ⦋n⦌) ≫
        (nativeCoverBarAugmentation X x).app (op ⦋n⦌) =
      (nativeCoverProjection X x).app (op ⦋n⦌) :=
  SSet.bkAugmentation_app_mk_ι (nativeCoverProjectionCocone X x) n p

/-- The actual native cover bar augmentation is weak by the original scalar
projection equivalences and the existing row/diagonal comparison. -/
theorem nativeCoverBarAugmentation_mem_realizationWeakEquivalences
    (X : SSet.{u}) [KanComplex X] [X.IsConnected] (x : X _⦋0⦌) :
    SSet.realizationWeakEquivalences (nativeCoverBarAugmentation X x) := by
  apply SSet.BousfieldKanRowsOf.bkAugmentation_weak.{0, u, 0}
  intro q
  let := nativeCoverRowProjection_isEquivalence X x q
  exact CategoryTheory.nerveMapHomDown_mem_realizationWeakEquivalences_of_isEquivalence
    (SSet.BousfieldKanRowsOf.rowProjection.{0, u, 0} (nativeCoverProjectionCocone X x) q)

section Total

variable (A : Type uA) [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{u} A] [HasCountableCoproducts A] (R : A)

/-- The original signed shuffle and carrier-chain dictionary followed by
the original augmentation give the total-to-original-base chain map. -/
def nativeCoverTotalAugmentation (X : SSet.{u}) (x : X _⦋0⦌) :
    SSet.bkAlternatingTotalComplex A R (nativeCoverDeckFunctor X x) ⟶ X.chainComplex R :=
  (SSet.bkDiagonalTotalHomotopyEquiv A R (nativeCoverDeckFunctor X x)).inv ≫
    (SSet.bkCarrierChainIso A R (nativeCoverDeckFunctor X x)).inv ≫
      SSet.chainComplexMap (nativeCoverBarAugmentation X x) R

/-- The total augmentation retains the actual signed shuffle, original
carrier-chain map, and original simplicial augmentation. -/
theorem nativeCoverTotalAugmentation_eq (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeCoverTotalAugmentation A R X x =
      (SSet.bkDiagonalTotalHomotopyEquiv A R (nativeCoverDeckFunctor X x)).inv ≫
        (SSet.bkCarrierChainIso A R (nativeCoverDeckFunctor X x)).inv ≫
          SSet.chainComplexMap (nativeCoverBarAugmentation X x) R := rfl

end Total

/-- The original total augmentation is a quasi-isomorphism for arbitrary
module coefficients, with independent ring and simplex universes. -/
theorem nativeCoverTotalAugmentation_quasiIso {k : Type v} [Ring k]
    (R : ModuleCat.{u} k) (X : SSet.{u}) [KanComplex X] [X.IsConnected] (x : X _⦋0⦌) :
    QuasiIso (nativeCoverTotalAugmentation (ModuleCat.{u} k) R X x) := by
  let e := SSet.bkDiagonalTotalHomotopyEquiv (ModuleCat.{u} k) R (nativeCoverDeckFunctor X x)
  let c := SSet.bkCarrierChainIso (ModuleCat.{u} k) R (nativeCoverDeckFunctor X x)
  let : QuasiIso (SSet.chainComplexMap (nativeCoverBarAugmentation X x) R) :=
    (nativeCoverBarAugmentation_mem_realizationWeakEquivalences X x).quasiIso_chainComplexMap R
  let : QuasiIso e.inv := e.quasiIso_inv
  let : QuasiIso c.inv := inferInstance
  change QuasiIso (e.inv ≫ c.inv ≫ SSet.chainComplexMap (nativeCoverBarAugmentation X x) R)
  let : QuasiIso (c.inv ≫ SSet.chainComplexMap (nativeCoverBarAugmentation X x) R) :=
    quasiIso_comp _ _
  exact quasiIso_comp _ _

/-- The same original total augmentation is a quasi-isomorphism for arbitrary
abelian-group coefficients. -/
theorem nativeCoverTotalAugmentation_quasiIso_addCommGrp (R : AddCommGrpCat.{u})
    (X : SSet.{u}) [KanComplex X] [X.IsConnected] (x : X _⦋0⦌) :
    QuasiIso (nativeCoverTotalAugmentation AddCommGrpCat.{u} R X x) := by
  let e := SSet.bkDiagonalTotalHomotopyEquiv AddCommGrpCat.{u} R (nativeCoverDeckFunctor X x)
  let c := SSet.bkCarrierChainIso AddCommGrpCat.{u} R (nativeCoverDeckFunctor X x)
  have hWeak := nativeCoverBarAugmentation_mem_realizationWeakEquivalences X x
  let : QuasiIso (SSet.chainComplexMap (nativeCoverBarAugmentation X x) R) :=
    hWeak.quasiIso_chainComplexMap_addCommGrp R
  let : QuasiIso e.inv := e.quasiIso_inv
  let : QuasiIso c.inv := inferInstance
  change QuasiIso (e.inv ≫ c.inv ≫ SSet.chainComplexMap (nativeCoverBarAugmentation X x) R)
  let : QuasiIso (c.inv ≫ SSet.chainComplexMap (nativeCoverBarAugmentation X x) R) :=
    quasiIso_comp _ _
  exact quasiIso_comp _ _

/-- Homology of the actual signed total identifies with homology of the
original base for arbitrary module coefficients in every degree. -/
def nativeCoverTotalHomologyIso {k : Type v} [Ring k] (R : ModuleCat.{u} k)
    (X : SSet.{u}) [KanComplex X] [X.IsConnected] (x : X _⦋0⦌) (n : ℕ) :
    (SSet.bkAlternatingTotalComplex (ModuleCat.{u} k) R (nativeCoverDeckFunctor X x)).homology n ≅
      X.homology R n := by
  letI := nativeCoverTotalAugmentation_quasiIso R X x
  exact isoOfQuasiIsoAt (nativeCoverTotalAugmentation (ModuleCat.{u} k) R X x) n

/-- The forward homology comparison is induced by the original total
augmentation, with its actual signed shuffle and original projection. -/
theorem nativeCoverTotalHomologyIso_hom {k : Type v} [Ring k] (R : ModuleCat.{u} k)
    (X : SSet.{u}) [KanComplex X] [X.IsConnected] (x : X _⦋0⦌) (n : ℕ) :
    (nativeCoverTotalHomologyIso R X x n).hom =
      HomologicalComplex.homologyMap
        (nativeCoverTotalAugmentation (ModuleCat.{u} k) R X x) n := rfl

/-- Homology of the same actual total identifies with original-base homology
for arbitrary abelian-group coefficients in every degree. -/
def nativeCoverTotalHomologyIsoAddCommGrp (R : AddCommGrpCat.{u})
    (X : SSet.{u}) [KanComplex X] [X.IsConnected] (x : X _⦋0⦌) (n : ℕ) :
    (SSet.bkAlternatingTotalComplex AddCommGrpCat.{u} R (nativeCoverDeckFunctor X x)).homology n ≅
      X.homology R n := by
  letI := nativeCoverTotalAugmentation_quasiIso_addCommGrp R X x
  exact isoOfQuasiIsoAt (nativeCoverTotalAugmentation AddCommGrpCat.{u} R X x) n

/-- The abelian-group homology comparison keeps the same original total
augmentation map. -/
theorem nativeCoverTotalHomologyIsoAddCommGrp_hom (R : AddCommGrpCat.{u})
    (X : SSet.{u}) [KanComplex X] [X.IsConnected] (x : X _⦋0⦌) (n : ℕ) :
    (nativeCoverTotalHomologyIsoAddCommGrp R X x n).hom =
      HomologicalComplex.homologyMap
        (nativeCoverTotalAugmentation AddCommGrpCat.{u} R X x) n := rfl

end SSet.KanComplex

end
