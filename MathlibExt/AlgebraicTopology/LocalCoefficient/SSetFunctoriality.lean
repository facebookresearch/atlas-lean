/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSet

/-!
# Functoriality of simplicial-set local-coefficient chains

A natural transformation between two local systems on a fixed simplicial set
acts simplexwise on the coefficient coproduct.  Naturality, including the
dependent endpoint transports in the restricted coefficient bar, makes these
degree maps into a simplicial morphism and hence a map of unnormalized
alternating-face chain complexes.

The construction is functorial in the local system.  It does not vary the
base simplicial set, construct pullbacks along maps of spaces, take homology,
compare constant coefficients, or specialize to TopCat or CGWH.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

universe uR uX

namespace SSet

variable {R : Type uR} [CommRing R]
variable {X : SSet.{uX}}
variable {L K P : SSet.LocalSystem R X}

/-- Inclusion of one simplex-indexed summand into a local-coefficient degree
object. -/
noncomputable abbrev localCoefficientι
    (L : SSet.LocalSystem R X) {n : ℕ} (σ : X _⦋n⦌) :
    localCoefficientFamily L n σ ⟶ localCoefficientObj L n :=
  nervePullbackCoefficientι (fundamentalGroupoidNerveUnit X) L σ

/-- Degreewise map of local-coefficient coproducts induced by a natural
transformation of local systems. -/
noncomputable def localCoefficientMap (α : L ⟶ K) (n : ℕ) :
    localCoefficientObj L n ⟶ localCoefficientObj K n :=
  Sigma.map'
    (f := localCoefficientFamily K n)
    (g := localCoefficientFamily L n)
    id
    (fun σ => α.app
      ((fundamentalGroupoidNerveUnit X).app (op ⦋n⦌) σ).left)

/-- Formula for a local-coefficient degree map on one simplex summand. -/
@[reassoc (attr := simp)]
theorem localCoefficientι_map (α : L ⟶ K) {n : ℕ} (σ : X _⦋n⦌) :
    localCoefficientι L σ ≫ localCoefficientMap α n =
      α.app ((fundamentalGroupoidNerveUnit X).app (op ⦋n⦌) σ).left ≫
        localCoefficientι K σ := by
  exact Sigma.ι_comp_map'
    (f := localCoefficientFamily K n)
    (g := localCoefficientFamily L n)
    (fun τ : X _⦋n⦌ => τ)
    (fun τ => α.app
      ((fundamentalGroupoidNerveUnit X).app (op ⦋n⦌) τ).left) σ

/-- Identity natural transformations induce identity maps in every degree. -/
@[simp]
theorem localCoefficientMap_id (n : ℕ) :
    localCoefficientMap (𝟙 L) n = 𝟙 _ := by
  change Sigma.map' id
    (fun σ => 𝟙 ((localCoefficientFamily L n) σ)) = 𝟙 _
  exact Sigma.map'_id_id

/-- Composition of natural transformations induces composition of the
degreewise maps. -/
@[simp]
theorem localCoefficientMap_comp
    (α : L ⟶ K) (β : K ⟶ P) (n : ℕ) :
    localCoefficientMap (α ≫ β) n =
      localCoefficientMap α n ≫ localCoefficientMap β n := by
  change Sigma.map'
      (f := localCoefficientFamily P n)
      (g := localCoefficientFamily L n) id
      (fun σ => α.app
          ((fundamentalGroupoidNerveUnit X).app (op ⦋n⦌) σ).left ≫
        β.app
          ((fundamentalGroupoidNerveUnit X).app (op ⦋n⦌) σ).left) =
    Sigma.map'
        (f := localCoefficientFamily K n)
        (g := localCoefficientFamily L n) id
        (fun σ => α.app
          ((fundamentalGroupoidNerveUnit X).app (op ⦋n⦌) σ).left) ≫
      Sigma.map'
        (f := localCoefficientFamily P n)
        (g := localCoefficientFamily K n) id
        (fun σ => β.app
          ((fundamentalGroupoidNerveUnit X).app (op ⦋n⦌) σ).left)
  exact (Sigma.map'_comp_map'
    (f := localCoefficientFamily P n)
    (g := localCoefficientFamily K n)
    (h := localCoefficientFamily L n)
    id id
    (fun σ => β.app
      ((fundamentalGroupoidNerveUnit X).app (op ⦋n⦌) σ).left)
    (fun σ => α.app
      ((fundamentalGroupoidNerveUnit X).app (op ⦋n⦌) σ).left)).symm

/-- Naturality of a local-system morphism with the component of a restricted
face map, including the endpoint equality transport. -/
theorem localCoefficientFaceHom_naturality
    (α : L ⟶ K) {n : ℕ} (i : Fin (n + 2))
    (σ : X _⦋n + 1⦌) :
    α.app ((fundamentalGroupoidNerveUnit X).app _ σ).left ≫
        nervePullbackCoefficientFaceHom
          (fundamentalGroupoidNerveUnit X) K i σ =
      nervePullbackCoefficientFaceHom
          (fundamentalGroupoidNerveUnit X) L i σ ≫
        α.app
          ((fundamentalGroupoidNerveUnit X).app _ (X.δ i σ)).left := by
  let unit := fundamentalGroupoidNerveUnit X
  let F := unit.app (op ⦋n + 1⦌) σ
  let h := nervePullback_face_index unit i σ
  let hleft := congrArg ComposableArrows.left h
  have hnat := α.naturality (faceLeftHom i F)
  have htransport := CategoryTheory.eqToHom_naturality α.app hleft
  change α.app F.left ≫
      (K.map (faceLeftHom i F) ≫
        eqToHom (congrArg K.obj hleft)) =
    (L.map (faceLeftHom i F) ≫
      eqToHom (congrArg L.obj hleft)) ≫
        α.app (unit.app (op ⦋n⦌) (X.δ i σ)).left
  rw [← Category.assoc, ← hnat, Category.assoc, htransport,
    ← Category.assoc]

/-- Naturality of a local-system morphism with the component of a restricted
degeneracy map, including the endpoint equality transport. -/
theorem localCoefficientDegeneracyHom_naturality
    (α : L ⟶ K) {n : ℕ} (i : Fin (n + 1)) (σ : X _⦋n⦌) :
    α.app ((fundamentalGroupoidNerveUnit X).app _ σ).left ≫
        nervePullbackCoefficientDegeneracyHom
          (fundamentalGroupoidNerveUnit X) K i σ =
      nervePullbackCoefficientDegeneracyHom
          (fundamentalGroupoidNerveUnit X) L i σ ≫
        α.app
          ((fundamentalGroupoidNerveUnit X).app _ (X.σ i σ)).left := by
  let unit := fundamentalGroupoidNerveUnit X
  let F := unit.app (op ⦋n⦌) σ
  let h := nervePullback_degeneracy_index unit i σ
  let hleft := congrArg ComposableArrows.left h
  have hnat := α.naturality (degeneracyLeftHom i F)
  have htransport := CategoryTheory.eqToHom_naturality α.app hleft
  change α.app F.left ≫
      (K.map (degeneracyLeftHom i F) ≫
        eqToHom (congrArg K.obj hleft)) =
    (L.map (degeneracyLeftHom i F) ≫
      eqToHom (congrArg L.obj hleft)) ≫
        α.app (unit.app (op ⦋n + 1⦌) (X.σ i σ)).left
  rw [← Category.assoc, ← hnat, Category.assoc, htransport,
    ← Category.assoc]

/-- A local-system morphism commutes with the forward fundamental-groupoid
generator represented by an edge. -/
theorem localSystemHom_homMk_naturality
    (α : L ⟶ K) {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    α.app (SSet.FundamentalGroupoid.mk x) ≫
        K.map (SSet.FundamentalGroupoid.homMk e) =
      L.map (SSet.FundamentalGroupoid.homMk e) ≫
        α.app (SSet.FundamentalGroupoid.mk y) := by
  exact (α.naturality (SSet.FundamentalGroupoid.homMk e)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Degreewise local-coefficient maps commute with every face map. -/
theorem localCoefficientMap_naturality_face
    (α : L ⟶ K) {n : ℕ} (i : Fin (n + 2)) :
    localCoefficientMap α (n + 1) ≫ localCoefficientFace K i =
      localCoefficientFace L i ≫ localCoefficientMap α n := by
  let unit := fundamentalGroupoidNerveUnit X
  apply nervePullbackCoefficient_hom_ext unit L
  intro σ
  have hMapSource := localCoefficientι_map α σ
  have hMapTarget := localCoefficientι_map α (X.δ i σ)
  have hFaceL := nervePullbackCoefficientι_face unit L i σ
  have hFaceK := nervePullbackCoefficientι_face unit K i σ
  have hNat := localCoefficientFaceHom_naturality α i σ
  rw [← Category.assoc, hMapSource, Category.assoc, hFaceK,
    ← Category.assoc, hNat, Category.assoc, ← hMapTarget,
    ← Category.assoc, ← hFaceL, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Degreewise local-coefficient maps commute with every degeneracy map. -/
theorem localCoefficientMap_naturality_degeneracy
    (α : L ⟶ K) {n : ℕ} (i : Fin (n + 1)) :
    localCoefficientMap α n ≫ localCoefficientDegeneracy K i =
      localCoefficientDegeneracy L i ≫
        localCoefficientMap α (n + 1) := by
  let unit := fundamentalGroupoidNerveUnit X
  apply nervePullbackCoefficient_hom_ext unit L
  intro σ
  have hMapSource := localCoefficientι_map α σ
  have hMapTarget := localCoefficientι_map α (X.σ i σ)
  have hDegL := nervePullbackCoefficientι_degeneracy unit L i σ
  have hDegK := nervePullbackCoefficientι_degeneracy unit K i σ
  have hNat := localCoefficientDegeneracyHom_naturality α i σ
  rw [← Category.assoc, hMapSource, Category.assoc, hDegK,
    ← Category.assoc, hNat, Category.assoc, ← hMapTarget,
    ← Category.assoc, ← hDegL, Category.assoc]

/-- Simplicial data underlying the local-coefficient simplicial module. -/
noncomputable abbrev localCoefficientData
    (L : SSet.LocalSystem R X) :
    SimplicialObject.Data (ModuleCat.{max uR uX} R) :=
  nervePullbackCoefficientData (fundamentalGroupoidNerveUnit X) L

/-- Morphism of local-coefficient simplicial data induced by a natural
transformation of local systems. -/
noncomputable def localCoefficientDataMap (α : L ⟶ K) :
    localCoefficientData L ⟶ localCoefficientData K where
  app := localCoefficientMap α
  w_δ := localCoefficientMap_naturality_face α
  w_σ := localCoefficientMap_naturality_degeneracy α

/-- Identity law for local-coefficient simplicial-data maps. -/
@[simp]
theorem localCoefficientDataMap_id :
    localCoefficientDataMap (𝟙 L) = 𝟙 _ := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  exact localCoefficientMap_id n

/-- Composition law for local-coefficient simplicial-data maps. -/
@[simp]
theorem localCoefficientDataMap_comp
    (α : L ⟶ K) (β : K ⟶ P) :
    localCoefficientDataMap (α ≫ β) =
      localCoefficientDataMap α ≫ localCoefficientDataMap β := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  exact localCoefficientMap_comp α β n

/-- Local-coefficient simplicial data as a functor of the local system. -/
noncomputable def localCoefficientDataFunctor :
    SSet.LocalSystem R X ⥤
      SimplicialObject.Data (ModuleCat.{max uR uX} R) where
  obj := localCoefficientData
  map := localCoefficientDataMap
  map_id _ := localCoefficientDataMap_id
  map_comp := localCoefficientDataMap_comp

@[simp]
theorem localCoefficientDataFunctor_obj (L : SSet.LocalSystem R X) :
    localCoefficientDataFunctor.obj L = localCoefficientData L := rfl

@[simp]
theorem localCoefficientDataFunctor_map (α : L ⟶ K) :
    localCoefficientDataFunctor.map α = localCoefficientDataMap α := rfl

/-- Simplicial-module map induced by a natural transformation of local
systems. -/
noncomputable def localCoefficientSimplicialMap (α : L ⟶ K) :
    localCoefficientSimplicial L ⟶ localCoefficientSimplicial K :=
  SimplicialObject.Data.toSimplicialNatTrans (localCoefficientDataMap α)

/-- Degree component of the induced simplicial-module map. -/
@[simp]
theorem localCoefficientSimplicialMap_app_mk
    (α : L ⟶ K) (n : ℕ) :
    (localCoefficientSimplicialMap α).app (op ⦋n⦌) =
      localCoefficientMap α n := rfl

/-- Identity law for the induced simplicial-module maps. -/
@[simp]
theorem localCoefficientSimplicialMap_id :
    localCoefficientSimplicialMap (𝟙 L) = 𝟙 _ := by
  change SimplicialObject.Data.toSimplicialNatTrans
      (localCoefficientDataMap (𝟙 L)) = 𝟙 _
  rw [localCoefficientDataMap_id]
  rfl

/-- Composition law for the induced simplicial-module maps. -/
@[simp]
theorem localCoefficientSimplicialMap_comp
    (α : L ⟶ K) (β : K ⟶ P) :
    localCoefficientSimplicialMap (α ≫ β) =
      localCoefficientSimplicialMap α ≫
        localCoefficientSimplicialMap β := by
  change SimplicialObject.Data.toSimplicialNatTrans
      (localCoefficientDataMap (α ≫ β)) = _
  rw [localCoefficientDataMap_comp]
  rfl

/-- The local-coefficient simplicial module as a functor of the local
system. -/
noncomputable def localCoefficientSimplicialFunctor :
    SSet.LocalSystem R X ⥤
      SimplicialObject (ModuleCat.{max uR uX} R) :=
  localCoefficientDataFunctor ⋙
    SimplicialObject.Data.toSimplicialFunctor

@[simp]
theorem localCoefficientSimplicialFunctor_obj
    (L : SSet.LocalSystem R X) :
    localCoefficientSimplicialFunctor.obj L =
      localCoefficientSimplicial L := rfl

@[simp]
theorem localCoefficientSimplicialFunctor_map (α : L ⟶ K) :
    localCoefficientSimplicialFunctor.map α =
      localCoefficientSimplicialMap α := rfl

/-- Alternating-face chain map induced by a natural transformation of local
systems. -/
noncomputable def localCoefficientChainMap (α : L ⟶ K) :
    localCoefficientChainComplex L ⟶ localCoefficientChainComplex K :=
  (AlgebraicTopology.alternatingFaceMapComplex
    (ModuleCat.{max uR uX} R)).map (localCoefficientSimplicialMap α)

/-- Degree component of the induced alternating-face chain map. -/
@[simp]
theorem localCoefficientChainMap_f (α : L ⟶ K) (n : ℕ) :
    (localCoefficientChainMap α).f n = localCoefficientMap α n := by
  exact AlgebraicTopology.alternatingFaceMapComplex_map_f
    (localCoefficientSimplicialMap α) n

/-- Identity law for the induced local-coefficient chain maps. -/
@[simp]
theorem localCoefficientChainMap_id :
    localCoefficientChainMap (𝟙 L) = 𝟙 _ := by
  unfold localCoefficientChainMap
  rw [localCoefficientSimplicialMap_id]
  exact (AlgebraicTopology.alternatingFaceMapComplex
    (ModuleCat.{max uR uX} R)).map_id _

/-- Composition law for the induced local-coefficient chain maps. -/
@[simp]
theorem localCoefficientChainMap_comp
    (α : L ⟶ K) (β : K ⟶ P) :
    localCoefficientChainMap (α ≫ β) =
      localCoefficientChainMap α ≫ localCoefficientChainMap β := by
  unfold localCoefficientChainMap
  rw [localCoefficientSimplicialMap_comp]
  exact (AlgebraicTopology.alternatingFaceMapComplex
    (ModuleCat.{max uR uX} R)).map_comp _ _

/-- The unnormalized local-coefficient chain complex as a functor of the
local system. -/
noncomputable def localCoefficientChainComplexFunctor :
    SSet.LocalSystem R X ⥤
      ChainComplex (ModuleCat.{max uR uX} R) ℕ :=
  localCoefficientSimplicialFunctor ⋙
    AlgebraicTopology.alternatingFaceMapComplex
      (ModuleCat.{max uR uX} R)

@[simp]
theorem localCoefficientChainComplexFunctor_obj
    (L : SSet.LocalSystem R X) :
    localCoefficientChainComplexFunctor.obj L =
      localCoefficientChainComplex L := rfl

@[simp]
theorem localCoefficientChainComplexFunctor_map (α : L ⟶ K) :
    localCoefficientChainComplexFunctor.map α =
      localCoefficientChainMap α := rfl

end SSet
