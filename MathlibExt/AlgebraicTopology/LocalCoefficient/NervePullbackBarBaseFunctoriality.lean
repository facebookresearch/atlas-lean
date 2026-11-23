/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSet

/-!
# Base functoriality of the nerve-pullback coefficient bar

A simplicial map `f : X ⟶ Y` reindexes the simplex coproduct in the
coefficient bar pulled back along `ψ : Y ⟶ nerve G`.  The coefficient
map on each summand is the identity; the only non-definitional comparison in
the face and degeneracy squares is transport along naturality of `f`.

The degree maps are packaged as a morphism of simplicial data, a morphism of
simplicial objects, and a map of unnormalized alternating-face complexes.  As
one application, naturality of the fundamental-groupoid nerve unit gives the
single chain map associated to a map of simplicial sets and a local system on
its target.

This file does not assert identity or composition coherence for pullback,
construct maps for topological spaces, or pass to homology.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe vG uG vA uA

namespace CategoryTheory.CategoryHomology

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable {X Y : SSet.{max uG vG}}
variable (f : X ⟶ Y) (ψ : Y ⟶ CategoryTheory.nerve G) (M : G ⥤ A)
variable [HasCoproducts.{max uG vG} A]

/-- The degree map induced by reindexing simplices along a map of base
simplicial sets.  Its map on every coefficient summand is the identity. -/
noncomputable def nervePullbackCoefficientBaseMap (n : ℕ) :
    nervePullbackCoefficientObj (f ≫ ψ) M n ⟶
      nervePullbackCoefficientObj ψ M n :=
  Sigma.map'
    (f := nervePullbackCoefficientFamily ψ M n)
    (g := nervePullbackCoefficientFamily (f ≫ ψ) M n)
    (fun σ => f.app (op (SimplexCategory.mk n)) σ)
    (fun _ => 𝟙 _)

/-- Formula for base reindexing on one simplex summand. -/
@[reassoc (attr := simp)]
theorem nervePullbackCoefficientι_baseMap {n : ℕ}
    (σ : X.obj (op (SimplexCategory.mk n))) :
    nervePullbackCoefficientι (f ≫ ψ) M σ ≫
        nervePullbackCoefficientBaseMap f ψ M n =
      nervePullbackCoefficientι ψ M
        (f.app (op (SimplexCategory.mk n)) σ) := by
  change Sigma.ι (nervePullbackCoefficientFamily (f ≫ ψ) M n) σ ≫
      Sigma.map'
        (f := nervePullbackCoefficientFamily ψ M n)
        (g := nervePullbackCoefficientFamily (f ≫ ψ) M n)
        (fun τ => f.app (op (SimplexCategory.mk n)) τ) (fun _ => 𝟙 _) = _
  rw [Sigma.ι_comp_map', Category.id_comp]

omit [HasCoproducts.{max uG vG} A] in
/-- A restricted face component commutes with base reindexing. -/
theorem nervePullbackCoefficientFaceHom_base_naturality
    {n : ℕ} (i : Fin (n + 2))
    (σ : X.obj (op (SimplexCategory.mk (n + 1)))) :
    nervePullbackCoefficientFaceHom ψ M i
          (f.app (op (SimplexCategory.mk (n + 1))) σ) ≫
        eqToHom (congrArg
          (nervePullbackCoefficientFamily ψ M n)
          (SSet.δ_naturality_apply f i σ).symm) =
      nervePullbackCoefficientFaceHom (f ≫ ψ) M i σ := by
  dsimp only
  unfold nervePullbackCoefficientFaceHom coefficientFaceHom
  simp only [Category.assoc]
  apply congrArg (M.map (faceLeftHom i ((f ≫ ψ).app _ σ)) ≫ ·)
  rw [eqToHom_trans]

omit [HasCoproducts.{max uG vG} A] in
/-- A restricted degeneracy component commutes with base reindexing. -/
theorem nervePullbackCoefficientDegeneracyHom_base_naturality
    {n : ℕ} (i : Fin (n + 1))
    (σ : X.obj (op (SimplexCategory.mk n))) :
    nervePullbackCoefficientDegeneracyHom ψ M i
          (f.app (op (SimplexCategory.mk n)) σ) ≫
        eqToHom (congrArg
          (nervePullbackCoefficientFamily ψ M (n + 1))
          (SSet.σ_naturality_apply f i σ).symm) =
      nervePullbackCoefficientDegeneracyHom (f ≫ ψ) M i σ := by
  dsimp only
  unfold nervePullbackCoefficientDegeneracyHom coefficientDegeneracyHom
  simp only [Category.assoc]
  apply congrArg (M.map (degeneracyLeftHom i ((f ≫ ψ).app _ σ)) ≫ ·)
  rw [eqToHom_trans]

/-- Degreewise base maps commute with every face map. -/
theorem nervePullbackCoefficientBaseMap_naturality_face
    {n : ℕ} (i : Fin (n + 2)) :
    nervePullbackCoefficientBaseMap f ψ M (n + 1) ≫
        nervePullbackCoefficientFace ψ M i =
      nervePullbackCoefficientFace (f ≫ ψ) M i ≫
        nervePullbackCoefficientBaseMap f ψ M n := by
  unfold nervePullbackCoefficientBaseMap nervePullbackCoefficientFace
  exact Sigma.map'_comp_eq
    (X₀ := nervePullbackCoefficientFamily (f ≫ ψ) M (n + 1))
    (X₁ := nervePullbackCoefficientFamily ψ M (n + 1))
    (X₁' := nervePullbackCoefficientFamily (f ≫ ψ) M n)
    (X₂ := nervePullbackCoefficientFamily ψ M n)
    (fun σ => f.app (op (SimplexCategory.mk (n + 1))) σ)
    (fun τ => Y.δ i τ)
    (fun _ => 𝟙 _)
    (nervePullbackCoefficientFaceHom ψ M i)
    (fun σ => X.δ i σ)
    (fun τ => f.app (op (SimplexCategory.mk n)) τ)
    (nervePullbackCoefficientFaceHom (f ≫ ψ) M i)
    (fun _ => 𝟙 _)
    (fun σ => (SSet.δ_naturality_apply f i σ).symm)
    (fun σ => by
      simpa only [Category.id_comp, Category.comp_id] using
        nervePullbackCoefficientFaceHom_base_naturality f ψ M i σ)

/-- Degreewise base maps commute with every degeneracy map. -/
theorem nervePullbackCoefficientBaseMap_naturality_degeneracy
    {n : ℕ} (i : Fin (n + 1)) :
    nervePullbackCoefficientBaseMap f ψ M n ≫
        nervePullbackCoefficientDegeneracy ψ M i =
      nervePullbackCoefficientDegeneracy (f ≫ ψ) M i ≫
        nervePullbackCoefficientBaseMap f ψ M (n + 1) := by
  unfold nervePullbackCoefficientBaseMap nervePullbackCoefficientDegeneracy
  exact Sigma.map'_comp_eq
    (X₀ := nervePullbackCoefficientFamily (f ≫ ψ) M n)
    (X₁ := nervePullbackCoefficientFamily ψ M n)
    (X₁' := nervePullbackCoefficientFamily (f ≫ ψ) M (n + 1))
    (X₂ := nervePullbackCoefficientFamily ψ M (n + 1))
    (fun σ => f.app (op (SimplexCategory.mk n)) σ)
    (fun τ => Y.σ i τ)
    (fun _ => 𝟙 _)
    (nervePullbackCoefficientDegeneracyHom ψ M i)
    (fun σ => X.σ i σ)
    (fun τ => f.app (op (SimplexCategory.mk (n + 1))) τ)
    (nervePullbackCoefficientDegeneracyHom (f ≫ ψ) M i)
    (fun _ => 𝟙 _)
    (fun σ => (SSet.σ_naturality_apply f i σ).symm)
    (fun σ => by
      simpa only [Category.id_comp, Category.comp_id] using
        nervePullbackCoefficientDegeneracyHom_base_naturality f ψ M i σ)

/-- Morphism of restricted coefficient-bar simplicial data induced by a map
of base simplicial sets. -/
noncomputable def nervePullbackCoefficientBaseDataMap :
    nervePullbackCoefficientData (f ≫ ψ) M ⟶
      nervePullbackCoefficientData ψ M where
  app := nervePullbackCoefficientBaseMap f ψ M
  w_δ := nervePullbackCoefficientBaseMap_naturality_face f ψ M
  w_σ := nervePullbackCoefficientBaseMap_naturality_degeneracy f ψ M

/-- Degree component of the base-reindexing morphism of simplicial data. -/
@[simp]
theorem nervePullbackCoefficientBaseDataMap_app (n : ℕ) :
    (nervePullbackCoefficientBaseDataMap f ψ M).app n =
      nervePullbackCoefficientBaseMap f ψ M n := rfl

/-- Morphism of restricted coefficient-bar simplicial objects induced by a
map of base simplicial sets. -/
noncomputable def nervePullbackCoefficientBaseSimplicialMap :
    nervePullbackCoefficientSimplicial (f ≫ ψ) M ⟶
      nervePullbackCoefficientSimplicial ψ M :=
  SimplicialObject.Data.toSimplicialNatTrans
    (nervePullbackCoefficientBaseDataMap f ψ M)

/-- Degree component of the base-reindexing simplicial morphism. -/
@[simp]
theorem nervePullbackCoefficientBaseSimplicialMap_app_mk (n : ℕ) :
    (nervePullbackCoefficientBaseSimplicialMap f ψ M).app
        (op (SimplexCategory.mk n)) =
      nervePullbackCoefficientBaseMap f ψ M n := rfl

section Preadditive

variable [Preadditive A]

/-- Map of unnormalized alternating-face complexes induced by a map of base
simplicial sets. -/
noncomputable def nervePullbackCoefficientBaseComplexMap :
    nervePullbackCoefficientComplex (f ≫ ψ) M ⟶
      nervePullbackCoefficientComplex ψ M :=
  (AlgebraicTopology.alternatingFaceMapComplex A).map
    (nervePullbackCoefficientBaseSimplicialMap f ψ M)

/-- Degree component of the base-reindexing alternating-chain map. -/
@[simp]
theorem nervePullbackCoefficientBaseComplexMap_f (n : ℕ) :
    (nervePullbackCoefficientBaseComplexMap f ψ M).f n =
      nervePullbackCoefficientBaseMap f ψ M n := by
  exact AlgebraicTopology.alternatingFaceMapComplex_map_f
    (nervePullbackCoefficientBaseSimplicialMap f ψ M) n

end Preadditive

end CategoryTheory.CategoryHomology

universe uR uX

namespace SSet

open CategoryTheory.CategoryHomology

/-- Naturality of the canonical map from a simplicial set to the nerve of
its fundamental groupoid. -/
theorem fundamentalGroupoidNerveUnit_naturality
    {X Y : SSet.{uX}} (f : X ⟶ Y) :
    f ≫ fundamentalGroupoidNerveUnit Y =
      fundamentalGroupoidNerveUnit X ≫
        CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f) := by
  calc
    f ≫ fundamentalGroupoidNerveUnit Y =
        SSet.fundamentalGroupoidNerveEquiv X
          (SSet.FundamentalGroupoid Y)
          (SSet.mapFundamentalGroupoid f ⋙ 𝟭 _) :=
      (SSet.fundamentalGroupoidNerveEquiv_precomp f (𝟭 _)).symm
    _ = SSet.fundamentalGroupoidNerveEquiv X
        (SSet.FundamentalGroupoid Y)
        (SSet.mapFundamentalGroupoid f) :=
      congrArg (SSet.fundamentalGroupoidNerveEquiv X
        (SSet.FundamentalGroupoid Y))
        (Functor.comp_id (SSet.mapFundamentalGroupoid f))
    _ = fundamentalGroupoidNerveUnit X ≫
        CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f) := by
      have h := SSet.fundamentalGroupoidNerveEquiv_postcomp
        (X := X) (𝟭 (SSet.FundamentalGroupoid X))
        (SSet.mapFundamentalGroupoid f)
      exact (congrArg (SSet.fundamentalGroupoidNerveEquiv X
        (SSet.FundamentalGroupoid Y))
          (Functor.id_comp (SSet.mapFundamentalGroupoid f))).symm.trans h

namespace LocalSystem

variable {R : Type uR} [CommRing R]
variable {X Y : SSet.{uX}}

/-- Pull a covariant local system back along a simplicial map. -/
noncomputable abbrev pullback (f : X ⟶ Y) (L : SSet.LocalSystem R Y) :
    SSet.LocalSystem R X :=
  SSet.mapFundamentalGroupoid f ⋙ L

end LocalSystem

variable {R : Type uR} [CommRing R]
variable {X Y : SSet.{uX}}

/-- Equality of the coefficient indices selected by nerve-unit naturality.
The target simplex is written first so its symmetry transports coefficients
from the pulled-back local system to the target local system. -/
theorem localCoefficientPullbackLeftIndex
    (f : X ⟶ Y) {n : ℕ} (σ : X _⦋n⦌) :
    ((fundamentalGroupoidNerveUnit Y).app
        (op (SimplexCategory.mk n))
        (f.app (op (SimplexCategory.mk n)) σ)).left =
      (SSet.mapFundamentalGroupoid f).obj
        ((fundamentalGroupoidNerveUnit X).app
          (op (SimplexCategory.mk n)) σ).left := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (fundamentalGroupoidNerveUnit_naturality f)
      (op (SimplexCategory.mk n))) σ
  exact congrArg ComposableArrows.left h

/-- Equality of degree objects induced by nerve-unit naturality.  It is
stated through the simplicial-data objects so it is definitionally the
equality used by the explicit degree map below. -/
theorem localCoefficientPullbackObjEq
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) (n : ℕ) :
    (nervePullbackCoefficientData
        (fundamentalGroupoidNerveUnit X ≫
          CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f)) L).obj n =
      (nervePullbackCoefficientData
        (f ≫ fundamentalGroupoidNerveUnit Y) L).obj n :=
  congrArg (fun q => (nervePullbackCoefficientData q L).obj n)
    (fundamentalGroupoidNerveUnit_naturality f).symm

/-- Equality of the coefficient objects on one source simplex. -/
theorem localCoefficientPullbackFamilyEq
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y)
    {n : ℕ} (σ : X _⦋n⦌) :
    nervePullbackCoefficientFamily
        (fundamentalGroupoidNerveUnit X ≫
          CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f)) L n σ =
      nervePullbackCoefficientFamily
        (f ≫ fundamentalGroupoidNerveUnit Y) L n σ :=
  congrArg L.obj (localCoefficientPullbackLeftIndex f σ).symm

/-- Morphism of local-coefficient simplicial data induced by a map of base
simplicial sets.  Its degree component explicitly transports coefficients
through nerve-unit naturality and then reindexes simplices along `f`. -/
noncomputable def localCoefficientPullbackDataMap
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) :
    nervePullbackCoefficientData
        (fundamentalGroupoidNerveUnit X ≫
          CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f)) L ⟶
      nervePullbackCoefficientData (fundamentalGroupoidNerveUnit Y) L where
  app n := eqToHom (localCoefficientPullbackObjEq f L n) ≫
    nervePullbackCoefficientBaseMap
      f (fundamentalGroupoidNerveUnit Y) L n
  w_δ {n} i := by
    change (eqToHom (localCoefficientPullbackObjEq f L (n + 1)) ≫
          nervePullbackCoefficientBaseMap
            f (fundamentalGroupoidNerveUnit Y) L (n + 1)) ≫
        nervePullbackCoefficientFace
          (fundamentalGroupoidNerveUnit Y) L i =
      nervePullbackCoefficientFace
          (fundamentalGroupoidNerveUnit X ≫
            CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f)) L i ≫
        (eqToHom (localCoefficientPullbackObjEq f L n) ≫
          nervePullbackCoefficientBaseMap
            f (fundamentalGroupoidNerveUnit Y) L n)
    rw [Category.assoc,
      nervePullbackCoefficientBaseMap_naturality_face]
    rw [← Category.assoc]
    rw [(CategoryTheory.eqToHom_naturality
      (fun q => nervePullbackCoefficientFace q L i)
      (fundamentalGroupoidNerveUnit_naturality f).symm).symm]
    rw [Category.assoc]
  w_σ {n} i := by
    change (eqToHom (localCoefficientPullbackObjEq f L n) ≫
          nervePullbackCoefficientBaseMap
            f (fundamentalGroupoidNerveUnit Y) L n) ≫
        nervePullbackCoefficientDegeneracy
          (fundamentalGroupoidNerveUnit Y) L i =
      nervePullbackCoefficientDegeneracy
          (fundamentalGroupoidNerveUnit X ≫
            CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f)) L i ≫
        (eqToHom (localCoefficientPullbackObjEq f L (n + 1)) ≫
          nervePullbackCoefficientBaseMap
            f (fundamentalGroupoidNerveUnit Y) L (n + 1))
    rw [Category.assoc,
      nervePullbackCoefficientBaseMap_naturality_degeneracy]
    rw [← Category.assoc]
    rw [(CategoryTheory.eqToHom_naturality
      (fun q => nervePullbackCoefficientDegeneracy q L i)
      (fundamentalGroupoidNerveUnit_naturality f).symm).symm]
    rw [Category.assoc]

/-- Degree component of the local-coefficient pullback map on simplicial
data. -/
@[simp]
theorem localCoefficientPullbackDataMap_app
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) (n : ℕ) :
    (localCoefficientPullbackDataMap f L).app n =
      eqToHom (localCoefficientPullbackObjEq f L n) ≫
        nervePullbackCoefficientBaseMap
          f (fundamentalGroupoidNerveUnit Y) L n := rfl

/-- Simplicial-module map induced by a map of base simplicial sets and a
local system on its target. -/
noncomputable def localCoefficientPullbackSimplicialMap
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) :
    nervePullbackCoefficientSimplicial
        (fundamentalGroupoidNerveUnit X ≫
          CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f)) L ⟶
      nervePullbackCoefficientSimplicial
        (fundamentalGroupoidNerveUnit Y) L :=
  SimplicialObject.Data.toSimplicialNatTrans
    (localCoefficientPullbackDataMap f L)

/-- Degree component of the local-coefficient pullback simplicial map. -/
@[simp]
theorem localCoefficientPullbackSimplicialMap_app_mk
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) (n : ℕ) :
    (localCoefficientPullbackSimplicialMap f L).app
        (op (SimplexCategory.mk n)) =
      eqToHom (localCoefficientPullbackObjEq f L n) ≫
        nervePullbackCoefficientBaseMap
          f (fundamentalGroupoidNerveUnit Y) L n :=
  localCoefficientPullbackDataMap_app f L n

/-- Raw alternating-chain map underlying the local-coefficient pullback map.
Its separate definition keeps the degree formula transparent without
unfolding the local-system presentation of the source complex. -/
@[no_expose]
noncomputable def localCoefficientPullbackRawChainMap
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) :
    nervePullbackCoefficientComplex
        (fundamentalGroupoidNerveUnit X ≫
          CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f)) L ⟶
      nervePullbackCoefficientComplex (fundamentalGroupoidNerveUnit Y) L :=
  (AlgebraicTopology.alternatingFaceMapComplex
    (ModuleCat.{max uR uX} R)).map
      (localCoefficientPullbackSimplicialMap f L)

/-- The chain map induced by a simplicial map and a local system on its
target.  In every degree it transports coefficients through nerve-unit
naturality and then reindexes simplices along `f`. -/
noncomputable def localCoefficientPullbackChainMap
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) :
    SSet.localCoefficientChainComplex (L.pullback f) ⟶
      SSet.localCoefficientChainComplex L :=
  localCoefficientPullbackRawChainMap f L

/-- Degree component of the local-coefficient pullback chain map. -/
@[simp]
theorem localCoefficientPullbackChainMap_f
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) (n : ℕ) :
    (localCoefficientPullbackChainMap f L).f n =
      eqToHom (localCoefficientPullbackObjEq f L n) ≫
        nervePullbackCoefficientBaseMap
          f (fundamentalGroupoidNerveUnit Y) L n := by
  change (localCoefficientPullbackRawChainMap f L).f n = _
  unfold localCoefficientPullbackRawChainMap
  rw [AlgebraicTopology.alternatingFaceMapComplex_map_f]
  exact localCoefficientPullbackSimplicialMap_app_mk f L n

/-- Formula for the local-coefficient pullback chain map on one simplex
summand. -/
@[reassoc]
theorem localCoefficientι_pullbackChainMap
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y)
    {n : ℕ} (σ : X _⦋n⦌) :
    nervePullbackCoefficientι
          (fundamentalGroupoidNerveUnit X) (L.pullback f) σ ≫
        (localCoefficientPullbackChainMap f L).f n =
      eqToHom (localCoefficientPullbackFamilyEq f L σ) ≫
        nervePullbackCoefficientι (fundamentalGroupoidNerveUnit Y) L
          (f.app (op (SimplexCategory.mk n)) σ) := by
  rw [localCoefficientPullbackChainMap_f]
  have hι : nervePullbackCoefficientι
        (fundamentalGroupoidNerveUnit X ≫
          CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f)) L σ ≫
        eqToHom (localCoefficientPullbackObjEq f L n) =
      eqToHom (localCoefficientPullbackFamilyEq f L σ) ≫
        nervePullbackCoefficientι
          (f ≫ fundamentalGroupoidNerveUnit Y) L σ := by
    exact CategoryTheory.eqToHom_naturality
      (fun q => nervePullbackCoefficientι q L σ)
      (fundamentalGroupoidNerveUnit_naturality f).symm
  change nervePullbackCoefficientι
      (fundamentalGroupoidNerveUnit X ≫
        CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f)) L σ ≫
        eqToHom (localCoefficientPullbackObjEq f L n) ≫
          nervePullbackCoefficientBaseMap
            f (fundamentalGroupoidNerveUnit Y) L n = _
  rw [← Category.assoc, hι, Category.assoc,
    nervePullbackCoefficientι_baseMap]

/-- The original simplex computation through the ACTUAL degree-object Isos.
This statement is typed without identifying a complex degree with its
coefficient coproduct through opaque colimit choices. -/
@[reassoc]
public theorem localCoefficientι_pullbackChainMap_conjugate
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) (n : ℕ) (σ : X _⦋n⦌) :
    (nervePullbackCoefficientι (fundamentalGroupoidNerveUnit X) (L.pullback f) σ ≫
        (eqToIso (localCoefficientChainComplex_X (L.pullback f) n)).inv) ≫
      (localCoefficientPullbackChainMap f L).f n ≫
        (eqToIso (localCoefficientChainComplex_X L n)).hom =
      eqToHom (localCoefficientPullbackFamilyEq f L σ) ≫
        nervePullbackCoefficientι (fundamentalGroupoidNerveUnit Y) L
          (f.app (op (SimplexCategory.mk n)) σ) := by
  simpa only [eqToIso, eqToHom_refl, Category.id_comp, Category.comp_id,
    Category.assoc] using localCoefficientι_pullbackChainMap f L σ

end SSet
