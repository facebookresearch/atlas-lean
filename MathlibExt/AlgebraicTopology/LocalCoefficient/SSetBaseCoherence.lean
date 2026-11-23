/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarBaseFunctoriality
public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetFunctoriality
public import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# Identity and composition coherence for SSet local-coefficient pullback maps

Pullback local systems are pseudofunctorial through the canonical identity
and composition Isos for the fundamental-groupoid functor.  The explicit
degree formula for the base-space chain map reduces both coherence laws to
coefficient transports on individual simplex coproduct summands.

This file makes no TopCat, CGWH, homology, acyclicity, or plus-construction
claim.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

universe uR uX

namespace SSet

namespace LocalSystem

variable {R : Type uR} [CommRing R]
variable {X Y Z : SSet.{uX}}

/-- Canonical comparison from pullback along the identity to the original
local system. -/
noncomputable def pullbackIdIso (L : SSet.LocalSystem R X) :
    L.pullback (𝟙 X) ≅ L :=
  Functor.isoWhiskerRight (SSet.mapFundamentalGroupoidId X) L ≪≫
    Functor.leftUnitor L

/-- Canonical comparison from pullback along a composite to iterated
pullback. -/
noncomputable def pullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : SSet.LocalSystem R Z) :
    L.pullback (f ≫ g) ≅ (L.pullback g).pullback f :=
  Functor.isoWhiskerRight (SSet.mapFundamentalGroupoidComp f g).symm L ≪≫
    Functor.associator
      (SSet.mapFundamentalGroupoid f)
      (SSet.mapFundamentalGroupoid g) L

/-- The identity-pullback comparison is the identity on every coefficient
object. -/
@[simp]
theorem pullbackIdIso_hom_app (L : SSet.LocalSystem R X)
    (x : SSet.FundamentalGroupoid X) :
    (pullbackIdIso L).hom.app x = 𝟙 _ := by
  simp only [pullbackIdIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    SSet.mapFundamentalGroupoidId_hom_app,
    Functor.leftUnitor_hom_app]
  erw [L.map_id]
  exact Category.id_comp _

/-- The composite-pullback comparison is the identity on every coefficient
object. -/
@[simp]
theorem pullbackCompIso_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : SSet.LocalSystem R Z) (x : SSet.FundamentalGroupoid X) :
    (pullbackCompIso f g L).hom.app x = 𝟙 _ := by
  simp only [pullbackCompIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
    SSet.mapFundamentalGroupoidComp_inv_app,
    Functor.associator_hom_app]
  erw [L.map_id]
  exact Category.id_comp _

/-- Pullbacks along equal simplicial maps are canonically isomorphic. -/
noncomputable def pullbackCongrIso
    {f g : X ⟶ Y} (h : f = g) (L : SSet.LocalSystem R Y) :
    L.pullback f ≅ L.pullback g :=
  Functor.isoWhiskerRight
    (SSet.congrMapFundamentalGroupoidOfEq h) L

/-- Component formula for the comparison of pullbacks along equal base
maps. -/
@[simp]
theorem pullbackCongrIso_hom_app
    {f g : X ⟶ Y} (h : f = g) (L : SSet.LocalSystem R Y)
    (x : SSet.FundamentalGroupoid X) :
    (pullbackCongrIso h L).hom.app x =
      L.map ((SSet.congrMapFundamentalGroupoidOfEq h).hom.app x) :=
  rfl

/-- Pull a natural transformation of local systems back along a simplicial
map. -/
noncomputable def pullbackMap {L K : SSet.LocalSystem R Y}
    (f : X ⟶ Y) (α : L ⟶ K) :
    L.pullback f ⟶ K.pullback f :=
  Functor.whiskerLeft (SSet.mapFundamentalGroupoid f) α

@[simp]
theorem pullbackMap_app {L K : SSet.LocalSystem R Y}
    (f : X ⟶ Y) (α : L ⟶ K) (x : SSet.FundamentalGroupoid X) :
    (pullbackMap f α).app x =
      α.app ((SSet.mapFundamentalGroupoid f).obj x) := rfl

end LocalSystem

variable {R : Type uR} [CommRing R]
variable {X Y Z : SSet.{uX}}

/-- For the identity base map, the coefficient transport in the generator
formula is reflexive. -/
theorem localCoefficientPullbackFamilyEq_id_eq_refl
    (L : SSet.LocalSystem R X) {n : ℕ} (σ : X _⦋n⦌) :
    localCoefficientPullbackFamilyEq (𝟙 X) L σ = rfl :=
  Subsingleton.elim _ _

/-- The index of a simplex under a composite is its iterated image. -/
theorem localCoefficientCompIndexEq
    (f : X ⟶ Y) (g : Y ⟶ Z) {n : ℕ} (σ : X _⦋n⦌) :
    (f ≫ g).app (op (SimplexCategory.mk n)) σ =
      g.app (op (SimplexCategory.mk n))
        (f.app (op (SimplexCategory.mk n)) σ) := by
  rw [NatTrans.comp_app]
  exact CategoryTheory.comp_apply _ _ _

/-- Equality transport between simplex indices is absorbed by the
corresponding coproduct inclusion. -/
theorem localCoefficientι_eqToHom_index
    (L : SSet.LocalSystem R Z) {n : ℕ} {σ τ : Z _⦋n⦌}
    (h : σ = τ) :
    eqToHom (congrArg (SSet.localCoefficientFamily L n) h) ≫
        nervePullbackCoefficientι
          (SSet.fundamentalGroupoidNerveUnit Z) L τ =
      nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit Z) L σ := by
  simpa only [eqToHom_refl, Category.comp_id] using
    (CategoryTheory.eqToHom_naturality
      (fun ρ => nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit Z) L ρ) h).symm

/-- Coefficient transports for a composite base map equal the two iterated
transports, including the final dependent simplex-index transport. -/
theorem localCoefficientPullbackFamilyEq_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (L : SSet.LocalSystem R Z)
    {n : ℕ} (σ : X _⦋n⦌) :
    eqToHom (localCoefficientPullbackFamilyEq (f ≫ g) L σ) ≫
        eqToHom (congrArg (SSet.localCoefficientFamily L n)
          (localCoefficientCompIndexEq f g σ)) =
      (SSet.LocalSystem.pullbackCompIso f g L).hom.app
          ((SSet.fundamentalGroupoidNerveUnit X).app _ σ).left ≫
        eqToHom
          (localCoefficientPullbackFamilyEq f (L.pullback g) σ) ≫
        eqToHom (localCoefficientPullbackFamilyEq g L
          (f.app (op (SimplexCategory.mk n)) σ)) := by
  rw [SSet.LocalSystem.pullbackCompIso_hom_app, Category.id_comp,
    eqToHom_trans, eqToHom_trans]

/-- Pullback chain maps preserve identities through the canonical
identity-pullback comparison. -/
theorem localCoefficientPullbackChainMap_id
    (L : SSet.LocalSystem R X) :
    SSet.localCoefficientPullbackChainMap (𝟙 X) L =
      SSet.localCoefficientChainMap (L.pullbackIdIso).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply nervePullbackCoefficient_hom_ext (n := n)
    (SSet.fundamentalGroupoidNerveUnit X) (L.pullback (𝟙 X))
  intro σ
  rw [SSet.localCoefficientι_pullbackChainMap,
    SSet.localCoefficientChainMap_f, SSet.localCoefficientι_map]
  rw [localCoefficientPullbackFamilyEq_id_eq_refl,
    eqToHom_refl, Category.id_comp,
    SSet.LocalSystem.pullbackIdIso_hom_app, Category.id_comp]
  rfl

/-- Pullback chain maps preserve composition through the canonical
composite-pullback comparison. -/
theorem localCoefficientPullbackChainMap_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (L : SSet.LocalSystem R Z) :
    SSet.localCoefficientPullbackChainMap (f ≫ g) L =
      SSet.localCoefficientChainMap
          (SSet.LocalSystem.pullbackCompIso f g L).hom ≫
        SSet.localCoefficientPullbackChainMap f (L.pullback g) ≫
        SSet.localCoefficientPullbackChainMap g L := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply nervePullbackCoefficient_hom_ext (n := n)
    (SSet.fundamentalGroupoidNerveUnit X) (L.pullback (f ≫ g))
  intro σ
  rw [SSet.localCoefficientι_pullbackChainMap]
  simp only [HomologicalComplex.comp_f, SSet.localCoefficientChainMap_f]
  slice_rhs 1 2 => rw [SSet.localCoefficientι_map]
  slice_rhs 2 3 => rw [SSet.localCoefficientι_pullbackChainMap]
  slice_rhs 3 4 => rw [SSet.localCoefficientι_pullbackChainMap]
  rw [← localCoefficientι_eqToHom_index L
    (localCoefficientCompIndexEq f g σ)]
  slice_lhs 1 2 => rw [localCoefficientPullbackFamilyEq_comp]
  simp only [Category.assoc]

/-- Equal simplicial base maps induce pullback chain maps related by the
canonical pullback comparison. -/
theorem localCoefficientPullbackChainMap_congr
    {f g : X ⟶ Y} (h : f = g) (L : SSet.LocalSystem R Y) :
    SSet.localCoefficientPullbackChainMap f L =
      SSet.localCoefficientChainMap
          (SSet.LocalSystem.pullbackCongrIso h L).hom ≫
        SSet.localCoefficientPullbackChainMap g L := by
  subst g
  simp [SSet.LocalSystem.pullbackCongrIso]

/-- Base-space pullback maps are natural in the coefficient local system. -/
theorem localCoefficientPullbackChainMap_naturality
    (f : X ⟶ Y) {L K : SSet.LocalSystem R Y} (α : L ⟶ K) :
    SSet.localCoefficientChainMap
          (SSet.LocalSystem.pullbackMap f α) ≫
        SSet.localCoefficientPullbackChainMap f K =
      SSet.localCoefficientPullbackChainMap f L ≫
        SSet.localCoefficientChainMap α := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply nervePullbackCoefficient_hom_ext (n := n)
    (SSet.fundamentalGroupoidNerveUnit X) (L.pullback f)
  intro σ
  simp only [HomologicalComplex.comp_f, SSet.localCoefficientChainMap_f]
  slice_lhs 1 2 => rw [SSet.localCoefficientι_map]
  slice_lhs 2 3 => rw [SSet.localCoefficientι_pullbackChainMap]
  slice_rhs 1 2 => rw [SSet.localCoefficientι_pullbackChainMap]
  slice_rhs 2 3 => rw [SSet.localCoefficientι_map]
  simp only [SSet.LocalSystem.pullbackMap_app]
  rw [← Category.assoc, CategoryTheory.eqToHom_naturality α.app
    (SSet.localCoefficientPullbackLeftIndex f σ).symm]
  simp only [Category.assoc]


/-- Monicity of an ACTUAL simplicial base inclusion gives monicity in each
local-system chain degree. The weighted-coproduct fact is the stock API. -/
theorem localCoefficientPullbackChainMap_f_mono_of_mono
    (f : X ⟶ Y) [Mono f] (L : SSet.LocalSystem R Y) (n : ℕ) :
    Mono ((localCoefficientPullbackChainMap f L).f n) := by
  rw [localCoefficientPullbackChainMap_f]
  have hinj : Function.Injective (f.app (op (SimplexCategory.mk n))) :=
    (mono_iff_injective _).mp inferInstance
  let : Mono (nervePullbackCoefficientBaseMap f
      (fundamentalGroupoidNerveUnit Y) L n) :=
    MonoCoprod.mono_map'_of_injective
      (nervePullbackCoefficientFamily (fundamentalGroupoidNerveUnit Y) L n)
      (fun σ => f.app (op (SimplexCategory.mk n)) σ) hinj
  infer_instance

/-- The same actual local-system pullback chain map is mono. -/
theorem localCoefficientPullbackChainMap_mono_of_mono
    (f : X ⟶ Y) [Mono f] (L : SSet.LocalSystem R Y) :
    Mono (localCoefficientPullbackChainMap f L) :=
  HomologicalComplex.mono_of_mono_f _
    (fun n => localCoefficientPullbackChainMap_f_mono_of_mono f L n)

/-- The original chain map between spaces over the SAME coefficient base.
Its source is the actual pullback along a, transported through the existing
congruence and composition Isos before the original map f. -/
def localCoefficientChainMapOver
    (f : X ⟶ Y) (g : Y ⟶ Z) (a : X ⟶ Z) (ha : a = f ≫ g)
    (L : SSet.LocalSystem R Z) :
    localCoefficientChainComplex (L.pullback a) ⟶
      localCoefficientChainComplex (L.pullback g) :=
  localCoefficientChainMap
      ((LocalSystem.pullbackCongrIso ha L) ≪≫ (LocalSystem.pullbackCompIso f g L)).hom ≫
    localCoefficientPullbackChainMap f (L.pullback g)

/-- The complete original source/target chain triangle commutes. This is
derived from the existing original base-map composition and equality laws. -/
@[reassoc]
theorem localCoefficientChainMapOver_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (a : X ⟶ Z) (ha : a = f ≫ g)
    (L : SSet.LocalSystem R Z) :
    localCoefficientChainMapOver f g a ha L ≫ localCoefficientPullbackChainMap g L =
      localCoefficientPullbackChainMap a L := by
  have he := localCoefficientPullbackChainMap_congr ha L
  have hc := localCoefficientPullbackChainMap_comp f g L
  unfold localCoefficientChainMapOver
  rw [Iso.trans_hom, localCoefficientChainMap_comp]
  simp only [Category.assoc]
  rw [← hc]
  exact he.symm

/-- The actual over-base map is mono when its simplicial base leg is mono.
No desired chain monicity or coefficient exactness is an input. -/
theorem localCoefficientChainMapOver_mono
    (f : X ⟶ Y) [Mono f] (g : Y ⟶ Z) (a : X ⟶ Z) (ha : a = f ≫ g)
    (L : SSet.LocalSystem R Z) : Mono (localCoefficientChainMapOver f g a ha L) := by
  let E := (LocalSystem.pullbackCongrIso ha L) ≪≫ (LocalSystem.pullbackCompIso f g L)
  let e := (localCoefficientChainComplexFunctor (R := R) (X := X)).mapIso E
  have he : e.hom = localCoefficientChainMap E.hom := by rfl
  let : IsIso (localCoefficientChainMap E.hom) := he ▸ (inferInstance : IsIso e.hom)
  let : Mono (localCoefficientPullbackChainMap f (L.pullback g)) :=
    localCoefficientPullbackChainMap_mono_of_mono f (L.pullback g)
  unfold localCoefficientChainMapOver
  infer_instance

section OverSquare

variable {S U V B T : SSet.{uX}}

/-- Four original maps over one coefficient base form a commutative chain
square. The ambient leg is an ACTUAL monomorphism; its chain monicity and
all four triangles are derived above, not assumed chain calibrations. -/
theorem localCoefficientChainMapOver_square
    (f : S ⟶ U) (g : S ⟶ V) (i : U ⟶ B) (j : V ⟶ B)
    (aS : S ⟶ T) (aU : U ⟶ T) (aV : V ⟶ T) (aB : B ⟶ T) [Mono aB]
    (hSU : aS = f ≫ aU) (hSV : aS = g ≫ aV)
    (hUB : aU = i ≫ aB) (hVB : aV = j ≫ aB)
    (L : SSet.LocalSystem R T) :
    localCoefficientChainMapOver f aU aS hSU L ≫
        localCoefficientChainMapOver i aB aU hUB L =
      localCoefficientChainMapOver g aV aS hSV L ≫
        localCoefficientChainMapOver j aB aV hVB L := by
  let mB := localCoefficientPullbackChainMap aB L
  let : Mono mB := localCoefficientPullbackChainMap_mono_of_mono aB L
  apply (cancel_mono mB).mp
  change (localCoefficientChainMapOver f aU aS hSU L ≫
      localCoefficientChainMapOver i aB aU hUB L) ≫
        localCoefficientPullbackChainMap aB L =
    (localCoefficientChainMapOver g aV aS hSV L ≫
      localCoefficientChainMapOver j aB aV hVB L) ≫
        localCoefficientPullbackChainMap aB L
  rw [Category.assoc, localCoefficientChainMapOver_comp,
    localCoefficientChainMapOver_comp, Category.assoc,
    localCoefficientChainMapOver_comp, localCoefficientChainMapOver_comp]

end OverSquare

end SSet
