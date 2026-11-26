/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Operad.Colored.Algebra.Analytic.Indexing
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Pi.Basic
public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Basic
public import MathlibExt.CategoryTheory.Operad.OperadObj.UnitInsertionNaturality
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensorInterfaces
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.EqToHom
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensorColimits
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Iso
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensor
public import MathlibExt.CategoryTheory.Operad.OperadObj.UnitLaws
public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Monad.Algebra
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Functor.EpiMono
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.UnitCopower
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# TensorOperadicFreeAlgebra

Colored tensor operations, free algebra monads, Eilenberg–Moore equivalences, and free
algebra adjunctions.
-/

/- Source proof segment: ProfileCoinvariants -/
section source_ProfileCoinvariants
/-!+# Tensor profile coinvariants

This is the coefficient-weighted heterogeneous finite-profile construction,
including nullary inputs and all color-preserving permutations. It reuses
the existing profile and unbiased tensor interfaces. The final operadic
monad additionally requires the source symmetric monoidal producer and
operad substitution; neither is assumed as an output here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

/-- Finite colored words form a small set of representatives of all
fixed-output finite colored profiles. The induced morphisms retain every
color-preserving permutation, including permutations changing the word. -/
abbrev ProfileSkeleton (Color : Type u) (d : Color) :=
  InducedCategory (AnalyticIndex Color d)
    (fun p : (Σ n : ℕ, Fin n → Color) => AnalyticIndex.ofFin p.2)

/-- The actual inclusion of the finite-word representatives into the
existing full profile groupoid. -/
def profileSkeletonInclusion (Color : Type u) (d : Color) :
    ProfileSkeleton Color d ⥤ AnalyticIndex Color d :=
  inducedFunctor _

instance profileSkeletonInclusionFull (Color : Type u) (d : Color) :
    (profileSkeletonInclusion Color d).Full :=
  inferInstanceAs (inducedFunctor _).Full

instance profileSkeletonInclusionFaithful (Color : Type u) (d : Color) :
    (profileSkeletonInclusion Color d).Faithful :=
  inferInstanceAs (inducedFunctor _).Faithful

/-- Every finite colored profile is represented by its colors along a
chosen equivalence with `Fin n`; the isomorphism retains those colors. -/
instance profileSkeletonInclusionEssSurj (Color : Type u) (d : Color) :
    (profileSkeletonInclusion Color d).EssSurj where
  mem_essImage P := by
    let : Fintype P.inputs := Fintype.ofFinite P.inputs
    let e : Fin (Fintype.card P.inputs) ≃ P.inputs :=
      (Fintype.equivFin P.inputs).symm
    let s : ProfileSkeleton Color d :=
      ⟨Fintype.card P.inputs, P.inputColor ∘ e⟩
    let f : (profileSkeletonInclusion Color d).obj s ⟶ P :=
      { inputEquiv := e
        inputColor_eq := fun _ => rfl
        outputColor_eq := rfl }
    exact ⟨s, ⟨asIso f⟩⟩

instance profileSkeletonInclusionIsEquivalence (Color : Type u) (d : Color) :
    (profileSkeletonInclusion Color d).IsEquivalence where

/-- The large presentation by arbitrary bundled finite input types is
equivalent to a genuinely small category at the color universe. -/
instance analyticIndexEssentiallySmall (Color : Type u) (d : Color) :
    EssentiallySmall.{u} (AnalyticIndex Color d) :=
  EssentiallySmall.mk'
    ((profileSkeletonInclusion Color d).asEquivalence.symm.trans
      (AsSmall.equiv : ProfileSkeleton Color d ≌ AsSmall.{u} (ProfileSkeleton Color d)))

variable {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]

/-- Small colimits at the color universe suffice for the full profile
groupoid, with no collapse of the carrier or morphism universe. -/
instance profileColimitsOfSmallColimits [HasColimitsOfSize.{u, u} V] (d : Color) :
    HasColimitsOfShape (AnalyticIndex Color d) V :=
  HasColimitsOfShape.of_essentiallySmall V (AnalyticIndex Color d)

variable [∀ d : Color, HasColimitsOfShape (AnalyticIndex Color d) V]

/-- The coefficient-weighted profile coinvariants, at every output color.
The groupoid colimit includes all finite profiles and quotients by the
actual simultaneous operation/input relabelling maps. -/
def profileCoinvariants (O : ColoredSymmetricCollection Color V) (A : Color → V) :
    Color → V :=
  fun d => colimit (analyticSummand (d := d) O A)

/-- The canonical map of a full finite-profile tensor summand into its
coinvariants. -/
def profileι (O : ColoredSymmetricCollection Color V) (A : Color → V)
    {d : Color} (P : AnalyticIndex Color d) :
    (analyticSummand O A).obj P ⟶ profileCoinvariants O A d :=
  colimit.ι (analyticSummand O A) P

/-- The symmetric coinvariant relation uses the actual tensor
relabelling, for arbitrary finite profiles and every input bijection. -/
@[reassoc]
theorem profile_relabel_ι (O : ColoredSymmetricCollection Color V) (A : Color → V)
    {d : Color} {P Q : AnalyticIndex Color d} (f : P ⟶ Q) :
    (analyticSummand O A).map f ≫ profileι O A Q = profileι O A P :=
  colimit.w _ f

/-- Coinvariants map covariantly in all input objects. -/
def profileMap (O : ColoredSymmetricCollection Color V) {A B : Color → V}
    (f : A ⟶ B) : profileCoinvariants O A ⟶ profileCoinvariants O B :=
  fun d => colim.map (analyticSummandCarrierMap (d := d) O f)

/-- The map of coinvariants is the tensor map of each original summand. -/
@[reassoc (attr := simp)]
theorem profileι_map (O : ColoredSymmetricCollection Color V) {A B : Color → V}
    (f : A ⟶ B) {d : Color} (P : AnalyticIndex Color d) :
    profileι O A P ≫ profileMap O f d =
      (analyticSummandCarrierMap O f).app P ≫ profileι O B P :=
  colimit.ι_map _ P

@[simp]
theorem profileMap_id (O : ColoredSymmetricCollection Color V) (A : Color → V) :
    profileMap O (𝟙 A) = 𝟙 (profileCoinvariants O A) := by
  funext d
  change colim.map (analyticSummandCarrierMap (d := d) O (fun c => 𝟙 (A c))) = _
  rw [analyticSummandCarrierMap_id, Functor.map_id]
  rfl

theorem profileMap_comp (O : ColoredSymmetricCollection Color V)
    {A B D : Color → V} (f : A ⟶ B) (g : B ⟶ D) :
    profileMap O (f ≫ g) = profileMap O f ≫ profileMap O g := by
  funext d
  change colim.map (analyticSummandCarrierMap (d := d) O (fun c => f c ≫ g c)) = _
  rw [analyticSummandCarrierMap_comp, Functor.map_comp]
  rfl

/-- The actual tensor-profile coinvariant endofunctor on color-indexed
objects. Monad units and multiplication are subsequent constructions. -/
def profileEndofunctor (O : ColoredSymmetricCollection Color V) :
    (Color → V) ⥤ (Color → V) where
  obj := profileCoinvariants O
  map := profileMap O
  map_id := profileMap_id O
  map_comp := profileMap_comp O

/-- A coefficient collection morphism induces the actual natural map
of tensor-profile coinvariant functors. -/
def profileCollectionMap {O O' : ColoredSymmetricCollection Color V} (a : O ⟶ O') :
    profileEndofunctor O ⟶ profileEndofunctor O' where
  app A d := colim.map (analyticSummandCollectionMap (d := d) A a)
  naturality A B f := by
    funext d
    change colim.map (analyticSummandCarrierMap (d := d) O f) ≫
        colim.map (analyticSummandCollectionMap (d := d) B a) =
      colim.map (analyticSummandCollectionMap (d := d) A a) ≫
        colim.map (analyticSummandCarrierMap (d := d) O' f)
    rw [← Functor.map_comp, ← Functor.map_comp,
      analyticSummandCollectionCarrier_mixed]

/-- Coefficient naturality on every original tensor profile. -/
@[reassoc (attr := simp)]
theorem profileι_collectionMap {O O' : ColoredSymmetricCollection Color V}
    (a : O ⟶ O') (A : Color → V) {d : Color} (P : AnalyticIndex Color d) :
    profileι O A P ≫ (profileCollectionMap a).app A d =
      (analyticSummandCollectionMap A a).app P ≫ profileι O' A P :=
  colimit.ι_map _ P

@[simp]
theorem profileCollectionMap_id (O : ColoredSymmetricCollection Color V) :
    profileCollectionMap (𝟙 O) = 𝟙 (profileEndofunctor O) := by
  apply NatTrans.ext
  funext A d
  change colim.map (analyticSummandCollectionMap (d := d) A (𝟙 O)) = _
  rw [analyticSummandCollectionMap_id, Functor.map_id]
  rfl

theorem profileCollectionMap_comp {O O' O'' : ColoredSymmetricCollection Color V}
    (a : O ⟶ O') (b : O' ⟶ O'') :
    profileCollectionMap (a ≫ b) = profileCollectionMap a ≫ profileCollectionMap b := by
  apply NatTrans.ext
  funext A d
  change colim.map (analyticSummandCollectionMap (d := d) A (a ≫ b)) = _
  rw [analyticSummandCollectionMap_comp, Functor.map_comp]
  rfl

/-- A full family of coefficient-weighted tensor operations with source
family `A` and target family `B`, equivariant under every profile map.
Unit and substitution equations are additional algebra conditions. -/
@[ext]
structure Operations (O : ColoredSymmetricCollection Color V)
    (A B : Color → V) where
  /-- The coefficient-weighted tensor operation at each original finite profile and output color. -/
  app : ∀ (d : Color) (P : AnalyticIndex Color d),
    (analyticSummand O A).obj P ⟶ B d
  equivariance : ∀ (d : Color) {P Q : AnalyticIndex Color d} (f : P ⟶ Q),
    (analyticSummand O A).map f ≫ app d Q = app d P

/-- Equivariant operations form an actual cocone on the profile tensor
diagram at each color. -/
def Operations.cocone {O : ColoredSymmetricCollection Color V} {A B : Color → V}
    (a : Operations O A B) (d : Color) : Cocone (analyticSummand (d := d) O A) where
  pt := B d
  ι :=
    { app := a.app d
      naturality := fun P Q f => by
        change (analyticSummand O A).map f ≫ a.app d Q = a.app d P ≫ 𝟙 (B d)
        rw [Category.comp_id]
        exact a.equivariance d f }

/-- Descent of a full equivariant operation family through the actual
symmetric profile coinvariants. -/
def Operations.desc {O : ColoredSymmetricCollection Color V} {A B : Color → V}
    (a : Operations O A B) : profileCoinvariants O A ⟶ B :=
  fun d => colimit.desc _ (a.cocone d)

@[reassoc (attr := simp)]
theorem Operations.ι_desc {O : ColoredSymmetricCollection Color V} {A B : Color → V}
    (a : Operations O A B) {d : Color} (P : AnalyticIndex Color d) :
    profileι O A P ≫ a.desc d = a.app d P :=
  colimit.ι_desc _ P

/-- Every map from the actual tensor-profile coinvariants is equivalent
to a full equivariant family of operations, with both inverse laws. -/
def operationsEquiv (O : ColoredSymmetricCollection Color V) (A B : Color → V) :
    (profileCoinvariants O A ⟶ B) ≃ Operations O A B where
  toFun f :=
    { app := fun d P => profileι O A P ≫ f d
      equivariance := fun d P Q e => by
        rw [← Category.assoc, profile_relabel_ι] }
  invFun a := a.desc
  left_inv f := by
    funext d
    apply colimit.hom_ext
    intro P
    exact Operations.ι_desc _ P
  right_inv a := by
    apply Operations.ext
    funext d P
    exact a.ι_desc P

/-- Target naturality of the full operation-map equivalence. -/
theorem operationsEquiv_target (O : ColoredSymmetricCollection Color V)
    {A B D : Color → V} (f : profileCoinvariants O A ⟶ B) (g : B ⟶ D)
    (d : Color) (P : AnalyticIndex Color d) :
    (operationsEquiv O A D (f ≫ g)).app d P =
      (operationsEquiv O A B f).app d P ≫ g d :=
  (Category.assoc _ _ _).symm

/-- Source naturality retains the actual heterogeneous tensor-input map
on every profile, including the empty one. -/
theorem operationsEquiv_source (O : ColoredSymmetricCollection Color V)
    {A B D : Color → V} (f : A ⟶ B) (g : profileCoinvariants O B ⟶ D)
    (d : Color) (P : AnalyticIndex Color d) :
    (operationsEquiv O A D (profileMap O f ≫ g)).app d P =
      (analyticSummandCarrierMap O f).app P ≫
        (operationsEquiv O B D g).app d P := by
  change profileι O A P ≫ (profileMap O f d ≫ g d) = _
  rw [← Category.assoc, profileι_map, Category.assoc]
  rfl






end CategoryTheory.Operad.Tensor
end
end
end source_ProfileCoinvariants

/- Source proof segment: SmallColoredProfiles -/
section source_SmallColoredProfiles
/-!
# Colored profile colimits at the source smallness universe

The displayed color type can live in an independent universe while
being small at the original colimit universe. The full profile groupoid
and all its actual colors are retained; smallness uses a witness only.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uc us uv uh

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type uc}

/-- Finite colored words are small at any universe at which the
actual displayed color type is small. -/
theorem profileSkeletonSmall [Small.{us} W] (d : W) :
    Small.{us} (ProfileSkeleton W d) :=
  inferInstanceAs (Small.{us} (Σ n : ℕ, Fin n → W))

/-- Profile-word morphisms retain their actual finite permutations;
their smallness does not require shrinking the color type. -/
theorem profileSkeletonLocallySmall (d : W) :
    LocallySmall.{us} (ProfileSkeleton W d) where
  hom_small P Q :=
    Small.mk' (S := ULift.{us} ((profileSkeletonInclusion W d).obj P ⟶
      (profileSkeletonInclusion W d).obj Q))
      (InducedCategory.homEquiv.trans Equiv.ulift.symm)

/-- The actual full profile groupoid is essentially small at the
source's smallness universe, with the original displayed colors. -/
theorem analyticIndexEssentiallySmallOfSmallColors [Small.{us} W] (d : W) :
    EssentiallySmall.{us} (AnalyticIndex W d) := by
  let : Small.{us} (ProfileSkeleton W d) := profileSkeletonSmall d
  let : LocallySmall.{us} (ProfileSkeleton W d) := profileSkeletonLocallySmall d
  exact (essentiallySmall_congr (profileSkeletonInclusion W d).asEquivalence).mp
    (essentiallySmall_of_small_of_locallySmall (ProfileSkeleton W d))

/-- Required source-sized colimits suffice for every actual profile,
even when the displayed color type has a larger independent universe. -/
theorem hasProfileColimitsOfSmallColors (C : Type uv) [Category.{uh} C]
    [HasColimitsOfSize.{us, us} C] [Small.{us} W] (d : W) :
    HasColimitsOfShape (AnalyticIndex W d) C := by
  let : EssentiallySmall.{us} (AnalyticIndex W d) :=
    analyticIndexEssentiallySmallOfSmallColors d
  exact HasColimitsOfShape.of_essentiallySmall C (AnalyticIndex W d)




end CategoryTheory.Operad.Tensor
end
end
end source_SmallColoredProfiles

/- Source proof segment: ProfileUnit -/
section source_ProfileUnit
/-!
# Nullary summands and the operadic generator unit

The nullary analytic summand is the operation coefficient itself,
via the actual singleton tensor isomorphism. The generator unit of
the tensor-profile functor inserts the operad's original unary unit,
using the existing coherent unit insertion maps. No monad or algebra
structure is an input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]

/-- The nullary coefficient/input factor family is the singleton
family containing its original operation coefficient. -/
def nullaryFactorsIso (O : ColoredSymmetricCollection Color V) (A : Color → V)
    (d : Color) :
    (analyticFactors (d := d) O A).obj AnalyticIndex.nullary ≅
      (FiniteFamily.singleton (C := V)).obj (O.obj (ColoredProfile.nullary d)) :=
  FiniteFamily.isoOfReindex (Equiv.ofUnique (Option (Fin 0)) PUnit)
    (fun i => by
      cases i with
      | none => rfl
      | some i => exact Fin.elim0 i)

/-- The empty input tensor contributes exactly the monoidal unit,
so the complete nullary summand is isomorphic to `O(;d)`. -/
def nullarySummandIso (O : ColoredSymmetricCollection Color V) (A : Color → V)
    (d : Color) :
    (analyticSummand (d := d) O A).obj AnalyticIndex.nullary ≅
      O.obj (ColoredProfile.nullary d) :=
  (FiniteTensor.tensor (V := V)).mapIso (nullaryFactorsIso O A d) ≪≫
    (FiniteTensor.singletonIso (V := V)).app (O.obj (ColoredProfile.nullary d))

/-- The generator's unary tensor factors: the original operad unit
at the coefficient slot and the singleton unitor at the input slot. -/
def unitFactors (O : ColoredOperadObj Color V) (A : Color → V) (d : Color) :
    UnitInsertion.leftTensorFamily (A d) ⟶
      (analyticFactors (d := d) O.toCollection A).obj (AnalyticIndex.unary d) where
  equiv := Equiv.refl (Option PUnit)
  hom i := match i with
    | none => O.unit d
    | some _ => (FiniteTensor.singletonIso (V := V)).hom.app (A d)

/-- Insert the original unary operadic unit before an input object.
The source is the input itself and the target is its actual unary
coefficient-weighted tensor summand. -/
def unitInsertion (O : ColoredOperadObj Color V) (A : Color → V) (d : Color) :
    A d ⟶ (analyticSummand O.toCollection A).obj (AnalyticIndex.unary (d := d) d) :=
  UnitInsertion.leftInsertFromFactor (A d) (unitFactors O A d)

/-- The unit factors commute with the original component of a
color-indexed input map, including its coherence unitor. -/
theorem unitFactors_naturality (O : ColoredOperadObj Color V)
    {A B : Color → V} (f : A ⟶ B) (d : Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map
        (UnitInsertion.leftNestedFamilyMap (f d)) ≫ unitFactors O B d =
      unitFactors O A d ≫
        (analyticFactorsCarrierMap (d := d) O.toCollection f).app (AnalyticIndex.unary d) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      change HEq
        ((FiniteTensor.tensor (V := V)).map (𝟙 FiniteFamily.empty) ≫ O.unit d)
        (O.unit d ≫ 𝟙 (O.toCollection.obj (ColoredSubstitutionData.unitProfile d)))
      have hi : (FiniteTensor.tensor (V := V)).map (𝟙 FiniteFamily.empty) =
          (𝟙 (operadUnitSource (V := V))) :=
        (FiniteTensor.tensor (V := V)).map_id FiniteFamily.empty
      exact heq_of_eq
        ((congrArg (fun t : operadUnitSource (V := V) ⟶ operadUnitSource (V := V) =>
          t ≫ O.unit d) hi).trans
          ((Category.id_comp (O.unit d)).trans (Category.comp_id (O.unit d)).symm))
    | some i =>
      change HEq
        ((FiniteTensor.tensor (V := V)).map ((FiniteFamily.singleton (C := V)).map (f d)) ≫
          (FiniteTensor.singletonIso (V := V)).hom.app (B d))
        ((FiniteTensor.singletonIso (V := V)).hom.app (A d) ≫ f d)
      exact heq_of_eq ((FiniteTensor.singletonIso (V := V)).hom.naturality (f d))

/-- Naturality of the actual operadic-unit insertion. -/
@[reassoc]
theorem unitInsertion_naturality (O : ColoredOperadObj Color V)
    {A B : Color → V} (f : A ⟶ B) (d : Color) :
    f d ≫ unitInsertion O B d =
      unitInsertion O A d ≫
        (analyticSummandCarrierMap O.toCollection f).app (AnalyticIndex.unary (d := d) d) := by
  let pA := UnitInsertion.leftInsertPrefix (A d)
  let pB := UnitInsertion.leftInsertPrefix (B d)
  let g : UnitInsertion.leftTensorFamily (A d) ⟶ UnitInsertion.leftTensorFamily (B d) :=
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map
      (UnitInsertion.leftNestedFamilyMap (f d))
  let a := unitFactors O A d
  let b := unitFactors O B d
  let h := (analyticFactorsCarrierMap (d := d) O.toCollection f).app (AnalyticIndex.unary d)
  have hp : f d ≫ pB = pA ≫ (FiniteTensor.tensor (V := V)).map g :=
    UnitInsertion.leftInsertPrefix_natural (f d)
  have hf : g ≫ b = a ≫ h := unitFactors_naturality O f d
  change f d ≫ (pB ≫ (FiniteTensor.tensor (V := V)).map b) =
    (pA ≫ (FiniteTensor.tensor (V := V)).map a) ≫ (FiniteTensor.tensor (V := V)).map h
  calc
    f d ≫ (pB ≫ (FiniteTensor.tensor (V := V)).map b) =
        (f d ≫ pB) ≫ (FiniteTensor.tensor (V := V)).map b :=
      (Category.assoc _ _ _).symm
    _ = (pA ≫ (FiniteTensor.tensor (V := V)).map g) ≫
        (FiniteTensor.tensor (V := V)).map b := congrArg (· ≫ _) hp
    _ = pA ≫ (FiniteTensor.tensor (V := V)).map (g ≫ b) := by
      rw [Category.assoc, ← Functor.map_comp]
    _ = pA ≫ (FiniteTensor.tensor (V := V)).map (a ≫ h) :=
      congrArg (fun t => pA ≫ (FiniteTensor.tensor (V := V)).map t) hf
    _ = (pA ≫ (FiniteTensor.tensor (V := V)).map a) ≫
        (FiniteTensor.tensor (V := V)).map h := by
      rw [Functor.map_comp, Category.assoc]

variable [∀ d : Color, HasColimitsOfShape (AnalyticIndex Color d) V]

/-- The original nullary operation coefficient maps into the free
tensor-profile construction. This summand is retained at degree zero. -/
def nullaryι (O : ColoredSymmetricCollection Color V) (A : Color → V) (d : Color) :
    O.obj (ColoredProfile.nullary d) ⟶ profileCoinvariants O A d :=
  (nullarySummandIso O A d).inv ≫ profileι O A AnalyticIndex.nullary

/-- Nullary operations descend to exactly their original nullary
operation maps, after the coherent unit tensor identification. -/
@[reassoc (attr := simp)]
theorem nullaryι_desc {O : ColoredSymmetricCollection Color V} {A B : Color → V}
    (a : Operations O A B) (d : Color) :
    nullaryι O A d ≫ a.desc d =
      (nullarySummandIso O A d).inv ≫ a.app d AnalyticIndex.nullary := by
  rw [nullaryι, Category.assoc, Operations.ι_desc]

/-- The natural generator unit of the tensor-profile endofunctor.
It uses the given operad unit and the actual unary profile inclusion. -/
def profileUnit (O : ColoredOperadObj Color V) :
    𝟭 (Color → V) ⟶ profileEndofunctor O.toCollection where
  app A d := unitInsertion O A d ≫ profileι O.toCollection A (AnalyticIndex.unary d)
  naturality A B f := by
    funext d
    change f d ≫ (unitInsertion O B d ≫ profileι O.toCollection B (AnalyticIndex.unary d)) =
      (unitInsertion O A d ≫ profileι O.toCollection A (AnalyticIndex.unary d)) ≫
        profileMap O.toCollection f d
    rw [← Category.assoc, unitInsertion_naturality, Category.assoc,
      Category.assoc, profileι_map]





end CategoryTheory.Operad.Tensor
end
end
end source_ProfileUnit

/- Source proof segment: TensorAlgebra -/
section source_TensorAlgebra
/-!
# Tensor algebras over colored operads

The algebra structure is defined by every finite-profile tensor operation,
profile equivariance, the original unary operad unit, and the actual
simultaneous substitution equation. The two substitution routes retain
all coefficients and heterogeneous input objects; regrouping is a
concrete bijection of their finite tensor factors.

No monad, adjunction, or created algebra colimit is supplied as an input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]

/-- The fixed-output input index of an existing full colored profile. -/
def profileInputs (P : ColoredProfile Color) : AnalyticIndex Color P.outputColor :=
  ⟨P.inputs, P.inputColor⟩

/-- The inner-first grouping of the operation coefficients and inputs
of a simultaneous substitution: a singleton outer coefficient and one
coefficient/input family for each inner operation. -/
def nestedOperationFactors (O : ColoredSymmetricCollection Color V)
    (A : Color → V) (s : ColoredSubstitutionData Color) :
    FiniteFamily (FiniteFamily V) where
  index := FintypeCat.of (Option s.inner.index)
  obj i := match i with
    | none => (FiniteFamily.singleton (C := V)).obj (O.obj s.outerProfile)
    | some i => (analyticFactors O A).obj (profileInputs (s.inner.obj i))

/-- The coefficient-first grouping: all operation coefficients in
one substitution block, and the original input objects as singletons. -/
def substitutionInputFactors (O : ColoredSymmetricCollection Color V)
    (A : Color → V) (s : ColoredSubstitutionData Color) :
    FiniteFamily (FiniteFamily V) where
  index := FintypeCat.of (Option s.totalProfile.inputs)
  obj i := match i with
    | none => (ColoredOperadObj.substitutionFactors O).obj s
    | some i => (FiniteFamily.singleton (C := V)).obj (A (s.totalProfile.inputColor i))

/-- The exact bijection regrouping outer coefficient, inner
coefficients, and leaf inputs from the inner-first to coefficient-first
finite family. It includes inner operations of arity zero. -/
def substitutionFactorEquiv (O : ColoredSymmetricCollection Color V)
    (A : Color → V) (s : ColoredSubstitutionData Color) :
    ((FiniteFamily.flatten (C := V)).obj (nestedOperationFactors O A s)).index ≃
      ((FiniteFamily.flatten (C := V)).obj (substitutionInputFactors O A s)).index where
  toFun i := match i with
    | ⟨none, _⟩ => ⟨none, none⟩
    | ⟨some i, none⟩ => ⟨none, some i⟩
    | ⟨some i, some j⟩ => ⟨some ⟨i, j⟩, PUnit.unit⟩
  invFun i := match i with
    | ⟨none, none⟩ => ⟨none, PUnit.unit⟩
    | ⟨none, some i⟩ => ⟨some i, none⟩
    | ⟨some ⟨i, j⟩, _⟩ => ⟨some i, some j⟩
  left_inv i := by
    rcases i with ⟨i, j⟩
    cases i with
    | none => cases j; rfl
    | some i => cases j <;> rfl
  right_inv i := by
    rcases i with ⟨i, j⟩
    cases i with
    | none => cases j <;> rfl
    | some i => rcases i with ⟨i, k⟩; cases j; rfl

/-- Regrouping changes the actual factor order by the displayed
bijection and preserves each coefficient/input object. -/
def substitutionFactorsIso (O : ColoredSymmetricCollection Color V)
    (A : Color → V) (s : ColoredSubstitutionData Color) :
    (FiniteFamily.flatten (C := V)).obj (nestedOperationFactors O A s) ≅
      (FiniteFamily.flatten (C := V)).obj (substitutionInputFactors O A s) :=
  FiniteFamily.isoOfReindex (substitutionFactorEquiv O A s)
    (fun i => by
      rcases i with ⟨i, j⟩
      cases i with
      | none => cases j; rfl
      | some i => cases j <;> rfl)

/-- The shared tensor source of the two actual algebra substitution
routes, with all operation coefficients and original leaf inputs. -/
def algebraSubstitutionSource (O : ColoredSymmetricCollection Color V)
    (A : Color → V) (s : ColoredSubstitutionData Color) : V :=
  (FiniteTensor.tensor (V := V)).obj
    ((FiniteFamily.flatten (C := V)).obj (nestedOperationFactors O A s))

/-- Evaluate the inner operation/input blocks while retaining the
outer operation coefficient. -/
def innerOperationMap {O : ColoredSymmetricCollection Color V} {A : Color → V}
    (a : Operations O A A) (s : ColoredSubstitutionData Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj (nestedOperationFactors O A s) ⟶
      (analyticFactors O A).obj (profileInputs s.outerProfile) where
  equiv := Equiv.refl (Option s.inner.index)
  hom i := match i with
    | none => (FiniteTensor.singletonIso (V := V)).hom.app (O.obj s.outerProfile)
    | some i => a.app (s.inner.obj i).outputColor (profileInputs (s.inner.obj i))

/-- The inner-first algebra route uses the actual inner operations,
then the actual outer operation. -/
def algebraSubstitutionInner {O : ColoredSymmetricCollection Color V} {A : Color → V}
    (a : Operations O A A) (s : ColoredSubstitutionData Color) :
    algebraSubstitutionSource O A s ⟶ A s.outputColor :=
  (FiniteTensor.flattenIso (V := V)).hom.app (nestedOperationFactors O A s) ≫
    (FiniteTensor.tensor (V := V)).map (innerOperationMap a s) ≫
      a.app s.outputColor (profileInputs s.outerProfile)

/-- Substitute the actual outer/inner operad coefficients while
retaining each original leaf input and its singleton tensor unitor. -/
def operadCoefficientMap (O : ColoredOperadObj Color V) (A : Color → V)
    (s : ColoredSubstitutionData Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj
        (substitutionInputFactors O.toCollection A s) ⟶
      (analyticFactors O.toCollection A).obj (profileInputs s.totalProfile) where
  equiv := Equiv.refl (Option s.totalProfile.inputs)
  hom i := match i with
    | none => O.subst.app s
    | some i => (FiniteTensor.singletonIso (V := V)).hom.app (A (s.totalProfile.inputColor i))

/-- The coefficient-first route applies the original operadic
substitution, with the original input tensor factors left in place. -/
def operadSubstitutionInputs (O : ColoredOperadObj Color V) (A : Color → V)
    (s : ColoredSubstitutionData Color) :
    algebraSubstitutionSource O.toCollection A s ⟶
      (analyticSummand O.toCollection A).obj (profileInputs s.totalProfile) :=
  (FiniteTensor.tensor (V := V)).map (substitutionFactorsIso O.toCollection A s).hom ≫
    (FiniteTensor.flattenIso (V := V)).hom.app (substitutionInputFactors O.toCollection A s) ≫
      (FiniteTensor.tensor (V := V)).map (operadCoefficientMap O A s)

/-- A tensor algebra over the original colored operad, specified by
every finite-profile operation and its actual equivariance, unit,
and substitution equations. -/
structure Algebra (O : ColoredOperadObj Color V) where
  /-- The original carrier object at every color. -/
  carrier : Color → V
  /-- The full equivariant family of original finite-profile tensor operations. -/
  operations : Operations O.toCollection carrier carrier
  unit : ∀ d : Color,
    unitInsertion O carrier d ≫ operations.app d (AnalyticIndex.unary d) = 𝟙 (carrier d)
  substitution : ∀ s : ColoredSubstitutionData Color,
    algebraSubstitutionInner operations s =
      operadSubstitutionInputs O carrier s ≫
        operations.app s.outputColor (profileInputs s.totalProfile)

namespace Algebra

variable {O : ColoredOperadObj Color V}

/-- Morphisms of tensor algebras preserve the full family of original
tensor operations, including nullary operations. -/
@[ext]
structure Hom (A B : Algebra O) where
  /-- The original colorwise map between the two algebra carrier families. -/
  hom : A.carrier ⟶ B.carrier
  comm : ∀ (d : Color) (P : AnalyticIndex Color d),
    A.operations.app d P ≫ hom d =
      (analyticSummandCarrierMap O.toCollection hom).app P ≫ B.operations.app d P

/-- Identity tensor algebra morphism. -/
def Hom.id (A : Algebra O) : Hom A A where
  hom := 𝟙 A.carrier
  comm d P := by
    change A.operations.app d P ≫ 𝟙 (A.carrier d) =
      (analyticSummandCarrierMap O.toCollection (fun c => 𝟙 (A.carrier c))).app P ≫
        A.operations.app d P
    rw [analyticSummandCarrierMap_id]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Composition preserves every original tensor operation square. -/
def Hom.comp {A B D : Algebra O} (f : Hom A B) (g : Hom B D) : Hom A D where
  hom := f.hom ≫ g.hom
  comm d P := by
    let F := (analyticSummandCarrierMap O.toCollection f.hom).app P
    let G := (analyticSummandCarrierMap O.toCollection g.hom).app P
    have hmap :
        (analyticSummandCarrierMap O.toCollection (f.hom ≫ g.hom)).app P = F ≫ G :=
      congrArg (fun a => a.app P) (analyticSummandCarrierMap_comp O.toCollection f.hom g.hom)
    calc
      A.operations.app d P ≫ (f.hom ≫ g.hom) d =
          (A.operations.app d P ≫ f.hom d) ≫ g.hom d :=
        (Category.assoc _ _ _).symm
      _ = (F ≫ B.operations.app d P) ≫ g.hom d :=
        congrArg (· ≫ g.hom d) (f.comm d P)
      _ = F ≫ (B.operations.app d P ≫ g.hom d) := Category.assoc _ _ _
      _ = F ≫ (G ≫ D.operations.app d P) := congrArg (F ≫ ·) (g.comm d P)
      _ = (F ≫ G) ≫ D.operations.app d P := (Category.assoc _ _ _).symm
      _ = (analyticSummandCarrierMap O.toCollection (f.hom ≫ g.hom)).app P ≫
          D.operations.app d P := congrArg (· ≫ D.operations.app d P) hmap.symm

instance : Category (Algebra O) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by
    apply Hom.ext
    funext d
    exact Category.id_comp (f.hom d)
  comp_id f := by
    apply Hom.ext
    funext d
    exact Category.comp_id (f.hom d)
  assoc f g h := by
    apply Hom.ext
    funext d
    exact Category.assoc (f.hom d) (g.hom d) (h.hom d)

/-- The actual tensor algebra forgetful functor keeps the original
color-indexed carrier and every original component of a morphism. -/
def forget (O : ColoredOperadObj Color V) : Algebra O ⥤ (Color → V) where
  obj A := A.carrier
  map f := f.hom

instance forgetFaithful (O : ColoredOperadObj Color V) : (forget O).Faithful where
  map_injective h := Hom.ext h

variable [∀ d : Color, HasColimitsOfShape (AnalyticIndex Color d) V]

/-- The equivariant tensor operations descend through the original
profile coinvariants to an action map on the underlying carrier. -/
def action (A : Algebra O) : profileCoinvariants O.toCollection A.carrier ⟶ A.carrier :=
  A.operations.desc

/-- The descended action recovers every actual operation map. -/
@[reassoc (attr := simp)]
theorem action_operation (A : Algebra O) (d : Color) (P : AnalyticIndex Color d) :
    profileι O.toCollection A.carrier P ≫ A.action d = A.operations.app d P :=
  A.operations.ι_desc P

/-- The source unary-unit operation equation implies the actual
unit equation for the descended profile action. -/
theorem action_unit (A : Algebra O) :
    (profileUnit O).app A.carrier ≫ A.action = 𝟙 A.carrier := by
  funext d
  change (unitInsertion O A.carrier d ≫
    profileι O.toCollection A.carrier (AnalyticIndex.unary d)) ≫ A.action d = _
  rw [Category.assoc, action_operation]
  exact A.unit d

/-- Preservation of every full operation square implies naturality
of the actual descended tensor-profile action. -/
theorem action_naturality {A B : Algebra O} (f : A ⟶ B) :
    A.action ≫ f.hom = profileMap O.toCollection f.hom ≫ B.action := by
  funext d
  apply colimit.hom_ext
  intro P
  change profileι O.toCollection A.carrier P ≫ (A.action d ≫ f.hom d) =
    profileι O.toCollection A.carrier P ≫
      (profileMap O.toCollection f.hom d ≫ B.action d)
  rw [← Category.assoc, action_operation, ← Category.assoc,
    profileι_map, Category.assoc, action_operation]
  exact f.comm d P

end Algebra






end CategoryTheory.Operad.Tensor
end
end
end source_TensorAlgebra

/- Source proof segment: TensorSubstitutionNaturality -/
section source_TensorSubstitutionNaturality
/-!
# Naturality of tensor algebra substitution

The fixed-output tensor summands extend to all colored profiles.
Their output transport and the simultaneous-substitution regrouping
retain the actual original operation and input relabellings.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {Color : Type u} {V : Type w} [Category.{v} V]

/-- The original operation coefficient and input objects as a finite
family, functorially on all colored profiles, including output-color
transport. Its fixed-output restriction is the existing analytic family. -/
def operationFactorsFunctor (O : ColoredSymmetricCollection Color V) (A : Color → V) :
    ColoredProfile Color ⥤ FiniteFamily V where
  obj P := (analyticFactors O A).obj (profileInputs P)
  map f :=
    { equiv := Equiv.optionCongr f.inputEquiv
      hom i := match i with
        | none => O.map f
        | some i => eqToHom (congrArg A (f.inputColor_eq i)) }
  map_id P := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro i
      cases i <;> rfl
    · intro i
      cases i with
      | none => exact heq_of_eq (O.map_id P)
      | some i => exact HEq.rfl
  map_comp f g := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro i
      cases i <;> rfl
    · intro i
      cases i with
      | none => exact heq_of_eq (O.map_comp f g)
      | some i =>
        change HEq
          (eqToHom (congrArg A ((f.inputColor_eq i).trans
            (g.inputColor_eq (f.inputEquiv i)))))
          (eqToHom (congrArg A (f.inputColor_eq i)) ≫
            eqToHom (congrArg A (g.inputColor_eq (f.inputEquiv i))))
        exact heq_of_eq (eqToHom_trans _ _).symm

/-- Full-profile relabelling restricts to the original analytic
coefficient/input map at a fixed output. -/
theorem operationFactorsFunctor_map_restrict (O : ColoredSymmetricCollection Color V)
    (A : Color → V) {d : Color} {P Q : AnalyticIndex Color d} (f : P ⟶ Q) :
    (operationFactorsFunctor O A).map ((analyticToProfileFunctor Color d).map f) =
      (analyticFactors (d := d) O A).map f := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i <;> exact HEq.rfl

/-- Restricting the full profile factor functor to a fixed output
recovers the original coefficient/input analytic factors exactly. -/
theorem operationFactorsFunctor_restrict (O : ColoredSymmetricCollection Color V)
    (A : Color → V) (d : Color) :
    analyticToProfileFunctor Color d ⋙ operationFactorsFunctor O A =
      analyticFactors (d := d) O A := by
  apply Functor.hext
    (F := analyticToProfileFunctor Color d ⋙ operationFactorsFunctor O A)
    (G := analyticFactors (d := d) O A) (fun _ => rfl)
  intro P Q f
  exact heq_of_eq (operationFactorsFunctor_map_restrict O A f)

variable [FiniteTensor V]

/-- The actual coefficient-weighted heterogeneous tensor on every
profile, with its original symmetric relabelling maps. -/
def operationSummandFunctor (O : ColoredSymmetricCollection Color V) (A : Color → V) :
    ColoredProfile Color ⥤ V :=
  operationFactorsFunctor O A ⋙ FiniteTensor.tensor

theorem operationSummandFunctor_restrict (O : ColoredSymmetricCollection Color V)
    (A : Color → V) (d : Color) :
    analyticToProfileFunctor Color d ⋙ operationSummandFunctor O A =
      analyticSummand (d := d) O A := by
  exact congrArg (fun F : AnalyticIndex Color d ⥤ FiniteFamily V =>
    F ⋙ FiniteTensor.tensor) (operationFactorsFunctor_restrict O A d)

/-- Fixed-output operation equivariance gives full profile naturality,
including the actual equality transport at the output color. -/
theorem Operations.profile_equivariance {O : ColoredSymmetricCollection Color V}
    {A B : Color → V} (a : Operations O A B) {P Q : ColoredProfile Color} (f : P ⟶ Q) :
    (operationSummandFunctor O A).map f ≫ a.app Q.outputColor (profileInputs Q) =
      a.app P.outputColor (profileInputs P) ≫ eqToHom (congrArg B f.outputColor_eq) := by
  rcases P with ⟨I, s, d⟩
  rcases Q with ⟨J, t, e⟩
  rcases f with ⟨f, h, he⟩
  cases he
  let g : (⟨I, s⟩ : AnalyticIndex Color d) ⟶ ⟨J, t⟩ := ⟨f, h, rfl⟩
  have hm := congrArg (FiniteTensor.tensor (V := V)).map
    (operationFactorsFunctor_map_restrict O A g)
  change (operationSummandFunctor O A).map (⟨f, h, rfl⟩ :
      (⟨I, s, d⟩ : ColoredProfile Color) ⟶ ⟨J, t, d⟩) ≫
        a.app d ⟨J, t⟩ = a.app d ⟨I, s⟩ ≫ 𝟙 (B d)
  calc
    _ = (analyticSummand (d := d) O A).map g ≫ a.app d ⟨J, t⟩ :=
      congrArg (· ≫ a.app d ⟨J, t⟩) hm
    _ = a.app d ⟨I, s⟩ := a.equivariance d g
    _ = a.app d ⟨I, s⟩ ≫ 𝟙 (B d) := (Category.comp_id _).symm




end CategoryTheory.Operad.Tensor
end
end
end source_TensorSubstitutionNaturality

/- Source proof segment: TensorSubstitutionFunctor -/
section source_TensorSubstitutionFunctor
/-!
# The actual tensor substitution map as a natural transformation

All operation coefficients and leaf inputs remain in the source.
The two finite groupings are related by the concrete factor bijection
from the operation-map algebra definition. Operadic substitution is
then applied in the coefficient block, naturally in every profile.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {Color : Type u} {V : Type w} [Category.{v} V]

/-- The inner-first finite grouping is functorial under the original
outer and inner colored profile relabellings. -/
def nestedOperationFactorsFunctor (O : ColoredSymmetricCollection Color V) (A : Color → V) :
    ColoredSubstitutionData Color ⥤ FiniteFamily (FiniteFamily V) where
  obj := nestedOperationFactors O A
  map f :=
    { equiv := Equiv.optionCongr f.innerHom.equiv
      hom i := match i with
        | none => (ColoredSubstitutionData.outerProfileFunctor ⋙ O ⋙
          FiniteFamily.singleton).map f
        | some i => (operationFactorsFunctor O A).map (f.innerHom.hom i) }
  map_id s := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro i
      cases i <;> rfl
    · intro i
      cases i with
      | none => exact heq_of_eq ((ColoredSubstitutionData.outerProfileFunctor ⋙ O ⋙
          FiniteFamily.singleton).map_id s)
      | some i => exact heq_of_eq ((operationFactorsFunctor O A).map_id (s.inner.obj i))
  map_comp f g := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro i
      cases i <;> rfl
    · intro i
      cases i with
      | none => exact heq_of_eq ((ColoredSubstitutionData.outerProfileFunctor ⋙ O ⋙
          FiniteFamily.singleton).map_comp f g)
      | some i => exact heq_of_eq ((operationFactorsFunctor O A).map_comp
          (f.innerHom.hom i) (g.innerHom.hom (f.innerHom.equiv i)))

/-- The coefficient-first grouping is functorial in the original
operation coefficient maps and leaf color transports. -/
def substitutionInputFactorsFunctor (O : ColoredSymmetricCollection Color V) (A : Color → V) :
    ColoredSubstitutionData Color ⥤ FiniteFamily (FiniteFamily V) where
  obj := substitutionInputFactors O A
  map f :=
    { equiv := Equiv.optionCongr (ColoredSubstitutionData.totalProfileMap f).inputEquiv
      hom i := match i with
        | none => (ColoredOperadObj.substitutionFactors O).map f
        | some i => (FiniteFamily.singleton (C := V)).map
          (eqToHom (congrArg A ((ColoredSubstitutionData.totalProfileMap f).inputColor_eq i))) }
  map_id s := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro i
      cases i with
      | none => rfl
      | some i => rcases i with ⟨i, j⟩; rfl
    · intro i
      cases i with
      | none => exact heq_of_eq ((ColoredOperadObj.substitutionFactors O).map_id s)
      | some i => exact heq_of_eq ((FiniteFamily.singleton (C := V)).map_id
          (A (s.totalProfile.inputColor i)))
  map_comp f g := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro i
      cases i with
      | none => rfl
      | some i => rcases i with ⟨i, j⟩; rfl
    · intro i
      cases i with
      | none => exact heq_of_eq ((ColoredOperadObj.substitutionFactors O).map_comp f g)
      | some i =>
        let a := eqToHom (congrArg A
          ((ColoredSubstitutionData.totalProfileMap f).inputColor_eq i))
        let b := eqToHom (congrArg A
          ((ColoredSubstitutionData.totalProfileMap g).inputColor_eq
            ((ColoredSubstitutionData.totalProfileMap f).inputEquiv i)))
        have h : eqToHom (congrArg A
            ((ColoredSubstitutionData.totalProfileMap (f ≫ g)).inputColor_eq i)) = a ≫ b :=
          (eqToHom_trans _ _).symm
        exact heq_of_eq
          ((congrArg (FiniteFamily.singleton (C := V)).map h).trans
            ((FiniteFamily.singleton (C := V)).map_comp a b))

/-- The concrete regrouping of all tensor factors is natural under
every original outer/inner relabelling and leaf color transport. -/
theorem substitutionFactorsIso_naturality (O : ColoredSymmetricCollection Color V)
    (A : Color → V) {s t : ColoredSubstitutionData Color} (f : s ⟶ t) :
    (FiniteFamily.flatten (C := V)).map ((nestedOperationFactorsFunctor O A).map f) ≫
        (substitutionFactorsIso O A t).hom =
      (substitutionFactorsIso O A s).hom ≫
        (FiniteFamily.flatten (C := V)).map ((substitutionInputFactorsFunctor O A).map f) := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro i
    rcases i with ⟨i, j⟩
    cases i with
    | none => cases j; rfl
    | some i => cases j <;> rfl
  · intro i
    rcases i with ⟨i, j⟩
    cases i with
    | none =>
      cases j
      let a := O.map (ColoredSubstitutionData.outerProfileMap f)
      change HEq (a ≫ 𝟙 _) (𝟙 _ ≫ a)
      exact heq_of_eq ((Category.comp_id a).trans (Category.id_comp a).symm)
    | some i =>
      cases j with
      | none =>
        let a := O.map (f.innerHom.hom i)
        change HEq (a ≫ 𝟙 _) (𝟙 _ ≫ a)
        exact heq_of_eq ((Category.comp_id a).trans (Category.id_comp a).symm)
      | some j =>
        let a := eqToHom (congrArg A ((f.innerHom.hom i).inputColor_eq j))
        change HEq (a ≫ 𝟙 _) (𝟙 _ ≫ a)
        exact heq_of_eq ((Category.comp_id a).trans (Category.id_comp a).symm)

/-- The two complete finite tensor factor groupings are naturally
isomorphic by the actual displayed factor bijection. -/
def substitutionFactorsNatIso (O : ColoredSymmetricCollection Color V) (A : Color → V) :
    nestedOperationFactorsFunctor O A ⋙ FiniteFamily.flatten ≅
      substitutionInputFactorsFunctor O A ⋙ FiniteFamily.flatten :=
  NatIso.ofComponents (substitutionFactorsIso O A)
    (fun f => substitutionFactorsIso_naturality O A f)

variable [FiniteTensor V]

/-- Applying original operadic substitution in the coefficient block
and singleton tensor unitors in the input blocks is natural. -/
def operadCoefficientNatTrans (O : ColoredOperadObj Color V) (A : Color → V) :
    substitutionInputFactorsFunctor O.toCollection A ⋙ FiniteFamily.map FiniteTensor.tensor ⟶
      ColoredSubstitutionData.totalProfileFunctor ⋙ operationFactorsFunctor O.toCollection A where
  app := operadCoefficientMap O A
  naturality s t f := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro i
      cases i <;> rfl
    · intro i
      cases i with
      | none =>
        change HEq
          ((FiniteTensor.tensor (V := V)).map ((ColoredOperadObj.substitutionFactors
            O.toCollection).map f) ≫
            O.subst.app t)
          (O.subst.app s ≫ O.toCollection.map (ColoredSubstitutionData.totalProfileMap f))
        exact heq_of_eq (O.subst.naturality f)
      | some i =>
        let a := eqToHom (congrArg A ((ColoredSubstitutionData.totalProfileMap f).inputColor_eq i))
        change HEq
          ((FiniteTensor.tensor (V := V)).map ((FiniteFamily.singleton (C := V)).map a) ≫
            (FiniteTensor.singletonIso (V := V)).hom.app _)
          ((FiniteTensor.singletonIso (V := V)).hom.app _ ≫ a)
        exact heq_of_eq ((FiniteTensor.singletonIso (V := V)).hom.naturality a)

/-- The complete source of operadic substitution is a functor of the
actual simultaneous-substitution profiles. -/
def algebraSubstitutionSourceFunctor (O : ColoredSymmetricCollection Color V) (A : Color → V) :
    ColoredSubstitutionData Color ⥤ V :=
  nestedOperationFactorsFunctor O A ⋙ FiniteFamily.flatten ⋙ FiniteTensor.tensor

/-- The actual substitution map is composed from the natural factor
regrouping, tensor flattening, and original operadic coefficient map. -/
def operadSubstitutionNatTrans (O : ColoredOperadObj Color V) (A : Color → V) :
    algebraSubstitutionSourceFunctor O.toCollection A ⟶
      ColoredSubstitutionData.totalProfileFunctor ⋙ operationSummandFunctor O.toCollection A :=
  Functor.whiskerRight (substitutionFactorsNatIso O.toCollection A).hom FiniteTensor.tensor ≫
    Functor.whiskerLeft (substitutionInputFactorsFunctor O.toCollection A)
      (FiniteTensor.flattenIso (V := V)).hom ≫
    Functor.whiskerRight (operadCoefficientNatTrans O A) FiniteTensor.tensor

/-- The natural transformation recovers the original tensor
substitution map used in the operation-algebra definition. -/
@[simp]
theorem operadSubstitutionNatTrans_app (O : ColoredOperadObj Color V) (A : Color → V)
    (s : ColoredSubstitutionData Color) :
    (operadSubstitutionNatTrans O A).app s = operadSubstitutionInputs O A s :=
  rfl

@[reassoc]
theorem operadSubstitutionInputs_naturality (O : ColoredOperadObj Color V) (A : Color → V)
    {s t : ColoredSubstitutionData Color} (f : s ⟶ t) :
    (algebraSubstitutionSourceFunctor O.toCollection A).map f ≫ operadSubstitutionInputs O A t =
      operadSubstitutionInputs O A s ≫
        (operationSummandFunctor O.toCollection A).map
          (ColoredSubstitutionData.totalProfileMap f) :=
  (operadSubstitutionNatTrans O A).naturality f





end CategoryTheory.Operad.Tensor
end
end
end source_TensorSubstitutionFunctor

/- Source proof segment: ProfileSubstitutionCocone -/
section source_ProfileSubstitutionCocone
/-!
# The original profile-substitution cocone

For each outer profile the indexing category is the finite product
of its inner profile groupoids. These are products of index categories;
every algebra input object is still combined by the supplied tensor.
The original operadic substitution gives a natural cocone into the
actual profile coinvariants.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {Color : Type u}

/-- All inner finite profiles whose output colors match the inputs
of the given outer profile. Empty outer profiles are included. -/
abbrev ProfileSubstitutionTuple {d : Color} (P : AnalyticIndex Color d) :=
  ∀ i : P.inputs, AnalyticIndex Color (P.inputColor i)

/-- A tuple determines the actual color-matching substitution shape,
with the original outer input type and all original inner profiles. -/
def tupleSubstitutionShape {d : Color} (P : AnalyticIndex Color d)
    (Q : ProfileSubstitutionTuple P) : ColoredSubstitutionData Color where
  outputColor := d
  inner :=
    { index := P.inputs
      obj i := (Q i).toColoredProfile }

/-- Every tuple morphism is the full family of original inner
profile relabellings; the outer inputs are retained. -/
def tupleSubstitutionFunctor {d : Color} (P : AnalyticIndex Color d) :
    ProfileSubstitutionTuple P ⥤ ColoredSubstitutionData Color where
  obj := tupleSubstitutionShape P
  map f :=
    { outputColor_eq := rfl
      innerHom :=
        { equiv := Equiv.refl P.inputs
          hom i := f i } }
  map_id Q := by
    apply ColoredSubstitutionData.Hom.ext
    apply FiniteFamily.Hom_ext
    · rfl
    · intro i
      exact HEq.rfl
  map_comp f g := by
    apply ColoredSubstitutionData.Hom.ext
    apply FiniteFamily.Hom_ext
    · rfl
    · intro i
      exact HEq.rfl

/-- The outer profile of a color-matching tuple is the original
outer profile, not a replacement profile. -/
@[simp]
theorem tupleSubstitutionShape_outer {d : Color} (P : AnalyticIndex Color d)
    (Q : ProfileSubstitutionTuple P) :
    (tupleSubstitutionShape P Q).outerProfile = P.toColoredProfile :=
  rfl

/-- Flatten the actual inner inputs while retaining the original
output color of the outer profile. -/
def tupleTotalFunctor {d : Color} (P : AnalyticIndex Color d) :
    ProfileSubstitutionTuple P ⥤ AnalyticIndex Color d where
  obj Q := profileInputs (tupleSubstitutionShape P Q).totalProfile
  map f := ColoredSubstitutionData.totalProfileMap ((tupleSubstitutionFunctor P).map f)
  map_id Q :=
    (ColoredSubstitutionData.totalProfileFunctor ⋙
      (Functor.id (ColoredProfile Color))).map_id (tupleSubstitutionShape P Q)
  map_comp f g := by
    exact (ColoredSubstitutionData.totalProfileFunctor).map_comp
      ((tupleSubstitutionFunctor P).map f) ((tupleSubstitutionFunctor P).map g)

variable {V : Type w} [Category.{v} V] [FiniteTensor V]

/-- The complete coefficient/input tensor source for every tuple
of inner operations. -/
def tupleSubstitutionSource (O : ColoredSymmetricCollection Color V) (A : Color → V)
    {d : Color} (P : AnalyticIndex Color d) : ProfileSubstitutionTuple P ⥤ V :=
  tupleSubstitutionFunctor P ⋙ algebraSubstitutionSourceFunctor O A

variable [∀ d : Color, HasColimitsOfShape (AnalyticIndex Color d) V]

/-- The original colored operad substitution and the original
profile quotient maps form an actual cocone over every inner-profile
tuple, including nullary inner and outer profiles. -/
def profileSubstitutionCocone (O : ColoredOperadObj Color V) (A : Color → V)
    {d : Color} (P : AnalyticIndex Color d) :
    Cocone (tupleSubstitutionSource O.toCollection A P) where
  pt := profileCoinvariants O.toCollection A d
  ι :=
    { app Q := operadSubstitutionInputs O A (tupleSubstitutionShape P Q) ≫
        profileι O.toCollection A ((tupleTotalFunctor P).obj Q)
      naturality Q R f := by
        let g := (tupleSubstitutionFunctor P).map f
        let u : algebraSubstitutionSource O.toCollection A (tupleSubstitutionShape P Q) ⟶
            algebraSubstitutionSource O.toCollection A (tupleSubstitutionShape P R) :=
          (algebraSubstitutionSourceFunctor O.toCollection A).map g
        let a : algebraSubstitutionSource O.toCollection A (tupleSubstitutionShape P Q) ⟶
            (analyticSummand O.toCollection A).obj ((tupleTotalFunctor P).obj Q) :=
          operadSubstitutionInputs O A (tupleSubstitutionShape P Q)
        let b : algebraSubstitutionSource O.toCollection A (tupleSubstitutionShape P R) ⟶
            (analyticSummand O.toCollection A).obj ((tupleTotalFunctor P).obj R) :=
          operadSubstitutionInputs O A (tupleSubstitutionShape P R)
        let z := (analyticSummand O.toCollection A).map ((tupleTotalFunctor P).map f)
        let iQ := profileι O.toCollection A ((tupleTotalFunctor P).obj Q)
        let iR := profileι O.toCollection A ((tupleTotalFunctor P).obj R)
        have hz : (operationSummandFunctor O.toCollection A).map
            (ColoredSubstitutionData.totalProfileMap g) = z :=
          congrArg (FiniteTensor.tensor (V := V)).map
            (operationFactorsFunctor_map_restrict O.toCollection A ((tupleTotalFunctor P).map f))
        have h : u ≫ b = a ≫ z :=
          (operadSubstitutionInputs_naturality O A g).trans (congrArg (a ≫ ·) hz)
        have hi : z ≫ iR = iQ := profile_relabel_ι O.toCollection A ((tupleTotalFunctor P).map f)
        change u ≫ (b ≫ iR) = (a ≫ iQ) ≫ 𝟙 _
        calc
          u ≫ (b ≫ iR) = (u ≫ b) ≫ iR := (Category.assoc _ _ _).symm
          _ = (a ≫ z) ≫ iR := congrArg (· ≫ iR) h
          _ = a ≫ (z ≫ iR) := Category.assoc _ _ _
          _ = a ≫ iQ := congrArg (a ≫ ·) hi
          _ = (a ≫ iQ) ≫ 𝟙 _ := (Category.comp_id _).symm }




end CategoryTheory.Operad.Tensor
end
end
end source_ProfileSubstitutionCocone

/- Source proof segment: ProfileSlotDiagram -/
section source_ProfileSlotDiagram
/-!
# Actual coefficient and input-slot diagrams

An outer profile has one coefficient slot and its original finite
input slots. The coefficient diagram has exactly one point and the
original operation object as its colimit. Every other diagram is the
actual corresponding profile-coinvariant diagram. All objects are
combined by the unbiased tensor functor.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

/-- A singleton coefficient index with object universe matching the
displayed profile groupoids and no nontrivial morphisms. -/
abbrev CoefficientIndex := ULift.{max 1 u} (Discrete PUnit.{1})

instance coefficientIndexCategory : Category.{0} CoefficientIndex.{u} :=
  uliftCategory (Discrete PUnit.{1})

instance coefficientIndexConnected : IsConnected CoefficientIndex.{u} := by
  infer_instance

instance coefficientIndexSmall : Small.{us} CoefficientIndex.{u} := by
  infer_instance

instance coefficientIndexLocallySmall : LocallySmall.{us} CoefficientIndex.{u} where
  hom_small P Q :=
    Small.mk' (S := ULift.{us} (P ⟶ Q)) Equiv.ulift.symm

instance coefficientIndexEssentiallySmall : EssentiallySmall.{us} CoefficientIndex.{u} :=
  essentiallySmall_of_small_of_locallySmall CoefficientIndex

variable {W : Type u}

/-- Each actual finite tensor slot carries its original input
profile groupoid, or the singleton coefficient diagram. -/
def profileSlotIndex {d : W} (P : AnalyticIndex W d) : Option P.inputs → Type (max 1 u)
  | none => CoefficientIndex
  | some i => AnalyticIndex W (P.inputColor i)

instance profileSlotCategory {d : W} (P : AnalyticIndex W d) (i : Option P.inputs) :
    Category.{0} (profileSlotIndex P i) :=
  match i with
  | none => coefficientIndexCategory
  | some i => inferInstanceAs (Category.{0} (AnalyticIndex W (P.inputColor i)))

instance profileSlotEssentiallySmall [Small.{us} W] {d : W}
    (P : AnalyticIndex W d) (i : Option P.inputs) :
    EssentiallySmall.{us} (profileSlotIndex P i) :=
  match i with
  | none => coefficientIndexEssentiallySmall
  | some i => analyticIndexEssentiallySmallOfSmallColors (P.inputColor i)

/-- All actual coefficient/input index choices. These are products
of index categories, and not products of algebra input objects. -/
abbrev ProfileSlotTuple {d : W} (P : AnalyticIndex W d) :=
  ∀ i : Option P.inputs, profileSlotIndex P i

/-- Keep every original inner profile from the actual slot tuple.
The unique coefficient index introduces no replacement operation. -/
def slotProfileTupleFunctor {d : W} (P : AnalyticIndex W d) :
    ProfileSlotTuple P ⥤ ProfileSubstitutionTuple P where
  obj Q i := Q (some i)
  map f i := f (some i)

variable {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original coefficient object and each original profile tensor
diagram, at the given actual tensor slot. -/
def profileSlotDiagram (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (i : Option P.inputs) → profileSlotIndex P i ⥤ C
  | none => (Functor.const CoefficientIndex).obj (O.obj P.toColoredProfile)
  | some i => analyticSummand (d := P.inputColor i) O A

variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- Each slot has its original colimit point: the coefficient itself
or the original profile coinvariants at that input color. -/
def profileSlotCocone (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (i : Option P.inputs) → Cocone (profileSlotDiagram O A P i)
  | none => constCocone CoefficientIndex (O.obj P.toColoredProfile)
  | some i => colimit.cocone (analyticSummand (d := P.inputColor i) O A)

/-- The displayed coefficient/input slot colimits are actual
colimits, constructed from the given profile colimits. -/
def isColimitProfileSlotCocone (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (i : Option P.inputs) → IsColimit (profileSlotCocone O A P i)
  | none => isColimitConstCocone CoefficientIndex (O.obj P.toColoredProfile)
  | some i => colimit.isColimit (analyticSummand (d := P.inputColor i) O A)

/-- The original object at every coefficient/input choice, as a
family with the actual fixed finite slot type. -/
def profileSlotFamilyFunctor (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    ProfileSlotTuple P ⥤ (Option P.inputs → C) where
  obj Q i := (profileSlotDiagram O A P i).obj (Q i)
  map f i := (profileSlotDiagram O A P i).map (f i)
  map_id Q := by
    funext i
    exact (profileSlotDiagram O A P i).map_id (Q i)
  map_comp f g := by
    funext i
    exact (profileSlotDiagram O A P i).map_comp (f i) (g i)

/-- The genuine coefficient-weighted finite tensor diagram at the
original actual slot indices. -/
def profileSlotTensorDiagram (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) : ProfileSlotTuple P ⥤ C :=
  profileSlotFamilyFunctor O A P ⋙
    fixedIndexTensorFunctor (analyticFactorsIndex P)

/-- The original operadic substitution cocone with all actual
coefficient/input choices retained. -/
def profileSlotSubstitutionCocone (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    Cocone (slotProfileTupleFunctor P ⋙ tupleSubstitutionSource O.toCollection A P) :=
  (profileSubstitutionCocone O A P).whisker (slotProfileTupleFunctor P)





end CategoryTheory.Operad.Tensor
end
end
end source_ProfileSlotDiagram

/- Source proof segment: ProfileSlotAssembly -/
section source_ProfileSlotAssembly
/-!
# Actual tensor assembly of profile substitution

The coefficient unitor and the source tensor flattening isomorphism
identify the coefficient/input slot tensor with the complete original
operadic substitution source. This is a constructed tensor isomorphism,
not a colimit or monad outcome supplied as an assumption.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u}

/-- Inner-profile relabellings retain the original outer profile and
therefore induce its identity map. -/
theorem tupleSubstitutionFunctor_outerMap {d : W} (P : AnalyticIndex W d)
    {Q R : ProfileSubstitutionTuple P} (f : Q ⟶ R) :
    ColoredSubstitutionData.outerProfileMap ((tupleSubstitutionFunctor P).map f) =
      𝟙 P.toColoredProfile := by
  apply ColoredProfile.Hom.ext
  rfl

variable {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original inner-first nested tensor factors, at all actual
coefficient/input index choices. -/
def slotNestedFactorsFunctor (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) : ProfileSlotTuple P ⥤ FiniteFamily (FiniteFamily C) :=
  slotProfileTupleFunctor P ⋙ tupleSubstitutionFunctor P ⋙ nestedOperationFactorsFunctor O A

/-- The original weighted coefficient/input factor family at the
actual finite slot indices. -/
def slotInputFactorsFunctor (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) : ProfileSlotTuple P ⥤ FiniteFamily C :=
  profileSlotFamilyFunctor O A P ⋙ FiniteFamily.fixedIndexFunctor (analyticFactorsIndex P)

/-- The actual coefficient singleton unitor identifies the weighted
slot factors with the tensor of each original nested block. -/
def coefficientTensorIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (slotInputFactorsFunctor O A P).obj Q ≅
      (slotNestedFactorsFunctor O A P ⋙ FiniteFamily.map FiniteTensor.tensor).obj Q :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option P.inputs))
    (fun i => match i with
      | none => ((FiniteTensor.singletonIso (V := C)).app (O.obj P.toColoredProfile)).symm
      | some i => Iso.refl ((analyticSummand O A).obj (Q (some i))))

/-- The coefficient unitor is natural under every original
coefficient/input profile diagram morphism. -/
theorem coefficientTensorIso_naturality (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) {Q R : ProfileSlotTuple P} (f : Q ⟶ R) :
    (slotInputFactorsFunctor O A P).map f ≫ (coefficientTensorIso O A P R).hom =
      (coefficientTensorIso O A P Q).hom ≫
        (slotNestedFactorsFunctor O A P ⋙ FiniteFamily.map FiniteTensor.tensor).map f := by
  let g := (tupleSubstitutionFunctor P).map ((slotProfileTupleFunctor P).map f)
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro i
    cases i <;> rfl
  · intro i
    cases i with
    | none =>
      let c := O.obj P.toColoredProfile
      let e := (FiniteTensor.singletonIso (V := C)).inv.app c
      have ho : O.map (ColoredSubstitutionData.outerProfileMap g) = 𝟙 c :=
        (congrArg O.map (tupleSubstitutionFunctor_outerMap P
          ((slotProfileTupleFunctor P).map f))).trans (O.map_id P.toColoredProfile)
      have hs : (FiniteFamily.singleton (C := C)).map
          (O.map (ColoredSubstitutionData.outerProfileMap g)) =
          𝟙 ((FiniteFamily.singleton (C := C)).obj c) :=
        (congrArg (FiniteFamily.singleton (C := C)).map ho).trans
          ((FiniteFamily.singleton (C := C)).map_id c)
      have ht : (FiniteTensor.tensor (V := C)).map
          ((FiniteFamily.singleton (C := C)).map
            (O.map (ColoredSubstitutionData.outerProfileMap g))) =
          𝟙 ((FiniteTensor.tensor (V := C)).obj ((FiniteFamily.singleton (C := C)).obj c)) :=
        (congrArg (FiniteTensor.tensor (V := C)).map hs).trans
          ((FiniteTensor.tensor (V := C)).map_id _)
      change HEq (𝟙 c ≫ e)
        (e ≫ (FiniteTensor.tensor (V := C)).map
          ((FiniteFamily.singleton (C := C)).map (O.map
            (ColoredSubstitutionData.outerProfileMap g))))
      exact heq_of_eq ((Category.id_comp e).trans
        ((congrArg (e ≫ ·) ht).trans (Category.comp_id e)).symm)
    | some i =>
      let m := (analyticSummand O A).map (f (some i))
      have hm : (FiniteTensor.tensor (V := C)).map
          ((operationFactorsFunctor O A).map (f (some i))) = m :=
        congrArg (FiniteTensor.tensor (V := C)).map
          (operationFactorsFunctor_map_restrict O A (f (some i)))
      change HEq (m ≫ 𝟙 _)
        (𝟙 _ ≫ (FiniteTensor.tensor (V := C)).map ((operationFactorsFunctor O A).map (f (some i))))
      exact heq_of_eq ((Category.comp_id m).trans
        ((congrArg (𝟙 _ ≫ ·) hm).trans (Category.id_comp m)).symm)

/-- The actual coefficient unitor assembles a full natural
isomorphism of coefficient/input factor families. -/
def coefficientTensorNatIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    slotInputFactorsFunctor O A P ≅
      slotNestedFactorsFunctor O A P ⋙ FiniteFamily.map FiniteTensor.tensor :=
  NatIso.ofComponents (coefficientTensorIso O A P)
    (fun f => coefficientTensorIso_naturality O A P f)

/-- The coefficient/input tensor is identified with the complete
original substitution source by the actual coefficient unitor and
the actual source tensor flattening isomorphism. -/
def profileSlotAssemblyIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    profileSlotTensorDiagram O A P ≅
      slotProfileTupleFunctor P ⋙ tupleSubstitutionSource O A P :=
  Functor.isoWhiskerRight (coefficientTensorNatIso O A P) FiniteTensor.tensor ≪≫
    Functor.isoWhiskerLeft (slotNestedFactorsFunctor O A P) (FiniteTensor.flattenIso (V := C)).symm

variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The original operadic substitution produces an actual cocone
on the coefficient/input tensor diagram, with every original map
and endpoint retained. -/
def assembledProfileSubstitutionCocone (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) : Cocone (profileSlotTensorDiagram O.toCollection A P) where
  pt := profileCoinvariants O.toCollection A d
  ι := (profileSlotAssemblyIso O.toCollection A P).hom ≫
    (profileSlotSubstitutionCocone O A P).ι





end CategoryTheory.Operad.Tensor
end
end
end source_ProfileSlotAssembly

/- Source proof segment: ProfileSlotColimit -/
section source_ProfileSlotColimit
/-!
# The original tensor slot cocone

The displayed cocone has the actual coefficient-weighted tensor of
profile colimit points as its point, and the original tensor maps of
the profile injections. The family cocone is not asserted to be a
colimit in the product category; the tensor colimit proof uses source
preservation separately in each slot.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The family of original coefficient/input colimit points and
the original injection maps at every actual slot. -/
def profileSlotFamilyCocone (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) : Cocone (profileSlotFamilyFunctor O A P) where
  pt i := (profileSlotCocone O A P i).pt
  ι :=
    { app Q i := (profileSlotCocone O A P i).ι.app (Q i)
      naturality Q R f := by
        funext i
        exact (profileSlotCocone O A P i).ι.naturality (f i) }

/-- Applying the actual finite tensor to the original slot cocone
gives the intended tensor of the original coefficient/input colimits. -/
def profileSlotTensorCocone (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) : Cocone (profileSlotTensorDiagram O A P) where
  pt := (analyticSummand O (profileCoinvariants O A)).obj P
  ι :=
    { app Q := (FiniteTensor.tensor (V := C)).map
        ({ equiv := Equiv.refl (Option P.inputs)
           hom i := match i with
             | none => 𝟙 (O.obj P.toColoredProfile)
             | some i => profileι O A (Q (some i)) } :
          (slotInputFactorsFunctor O A P).obj Q ⟶
            (analyticFactors O (profileCoinvariants O A)).obj P)
      naturality Q R f := by
        apply Eq.trans ((FiniteTensor.tensor (V := C)).map_comp _ _).symm
        apply Eq.trans ?_ (Category.comp_id _).symm
        apply congrArg (FiniteTensor.tensor (V := C)).map
        apply FiniteFamily.Hom_ext
        · rfl
        · intro i
          cases i with
          | none => exact heq_of_eq (Category.id_comp _)
          | some i => exact heq_of_eq (profile_relabel_ι O A (f (some i))) }

/-- The tensor cocone point is precisely the original analytic
summand with profile-coinvariant inputs, at every finite arity. -/
@[simp]
theorem profileSlotTensorCocone_pt (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (profileSlotTensorCocone O A P).pt =
      (analyticSummand O (profileCoinvariants O A)).obj P :=
  rfl

/-- Every actual slot injection is the original finite tensor map
of the coefficient identity and all original profile injections. -/
@[simp]
theorem profileSlotTensorCocone_ι (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (profileSlotTensorCocone O A P).ι.app Q =
      (FiniteTensor.tensor (V := C)).map
        ({ equiv := Equiv.refl (Option P.inputs)
           hom i := match i with
             | none => 𝟙 (O.obj P.toColoredProfile)
             | some i => profileι O A (Q (some i)) } :
          (slotInputFactorsFunctor O A P).obj Q ⟶
            (analyticFactors O (profileCoinvariants O A)).obj P) :=
  rfl




end CategoryTheory.Operad.Tensor
end
end
end source_ProfileSlotColimit

/- Source proof segment: ProfileOutputTransport -/
section source_ProfileOutputTransport
/-!
# Original output transport for colored profile substitutions

Changing an output color along its actual equality keeps all original
input types, input colors and permutations. The corresponding original
colored profile map retains that output equality explicitly.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u}

/-- Change the output along its original color equality while
retaining the original finite input type and input colors. -/
def outputTransportFunctor (c d : W) :
    AnalyticIndex W c ⥤ AnalyticIndex W d where
  obj P := ⟨P.inputs, P.inputColor⟩
  map f :=
    { inputEquiv := f.inputEquiv
      inputColor_eq := f.inputColor_eq
      outputColor_eq := rfl }
  map_id P := by
    apply ColoredProfile.Hom.ext
    rfl
  map_comp f g := by
    apply ColoredProfile.Hom.ext
    rfl

/-- The actual profile arrow identifying the old and transported
output colors, with identity input permutation. -/
def outputTransportProfileHom {c d : W} (h : c = d) (P : AnalyticIndex W c) :
    P.toColoredProfile ⟶ ((outputTransportFunctor c d).obj P).toColoredProfile where
  inputEquiv := Equiv.refl P.inputs
  inputColor_eq := fun _ => rfl
  outputColor_eq := h

/-- All original input relabellings commute with the actual output
transport profile arrow. -/
theorem outputTransportProfileHom_naturality {c d : W} (h : c = d)
    {P Q : AnalyticIndex W c} (f : P ⟶ Q) :
    ((analyticToProfileFunctor W c).map f) ≫ outputTransportProfileHom h Q =
      outputTransportProfileHom h P ≫
        ((analyticToProfileFunctor W d).map ((outputTransportFunctor c d).map f)) := by
  apply ColoredProfile.Hom.ext
  rfl

/-- The input-index groupoids are equivalent when the output label
changes; the coefficient transport still requires its actual equality. -/
def outputTransportEquivalence (c d : W) :
    AnalyticIndex W c ≌ AnalyticIndex W d where
  functor := outputTransportFunctor c d
  inverse := outputTransportFunctor d c
  unitIso := NatIso.ofComponents (fun P => Iso.refl P)
  counitIso := NatIso.ofComponents (fun P => Iso.refl P)

variable {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Output transport of the original weighted tensor summand is
the actual original collection relabelling. -/
def outputTransportSummandMap (O : ColoredSymmetricCollection W C) (A : W → C)
    {c d : W} (h : c = d) (P : AnalyticIndex W c) :
    (analyticSummand O A).obj P ⟶
      (analyticSummand O A).obj ((outputTransportFunctor c d).obj P) :=
  (operationSummandFunctor O A).map (outputTransportProfileHom h P)

/-- Full tensor operation families retain the actual output-color
transport square at every finite profile. -/
@[reassoc]
theorem Operations.output_transport {O : ColoredSymmetricCollection W C}
    {A B : W → C} (a : Operations O A B) {c d : W}
    (h : c = d) (P : AnalyticIndex W c) :
    outputTransportSummandMap O A h P ≫
        a.app d ((outputTransportFunctor c d).obj P) =
      a.app c P ≫ eqToHom (congrArg B h) :=
  a.profile_equivariance (outputTransportProfileHom h P)

variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The original profile quotient injections commute with output
transport; this retains the original color-indexed coinvariant objects. -/
@[reassoc]
theorem profileι_output_transport (O : ColoredSymmetricCollection W C) (A : W → C)
    {c d : W} (h : c = d) (P : AnalyticIndex W c) :
    outputTransportSummandMap O A h P ≫
        profileι O A ((outputTransportFunctor c d).obj P) =
      profileι O A P ≫ eqToHom (congrArg (profileCoinvariants O A) h) := by
  let a : Operations O A (profileCoinvariants O A) :=
    { app := fun _ Q => profileι O A Q
      equivariance := fun _ _ _ f => profile_relabel_ι O A f }
  exact a.output_transport h P





end CategoryTheory.Operad.Tensor
end
end
end source_ProfileOutputTransport

/- Source proof segment: ProfileTupleRelabel -/
section source_ProfileTupleRelabel
/-!
# Actual outer-profile relabelling of substitution tuples

An outer input bijection reindexes the original inner profiles and
uses exactly its original input-color equalities to transport their
outputs. No operation coefficient or inner finite input is replaced.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {d : W} {P Q : AnalyticIndex W d}

/-- The original input-color equality at a target input, including
the actual inverse-bijection endpoint transport. -/
theorem relabelInputColorEq (f : P ⟶ Q) (j : Q.inputs) :
    P.inputColor (f.inputEquiv.symm j) = Q.inputColor j :=
  (f.inputColor_eq (f.inputEquiv.symm j)).trans
    (congrArg Q.inputColor (f.inputEquiv.apply_symm_apply j))

/-- Relabel an actual tuple of inner profiles by the original outer
input bijection, retaining every original inner input. -/
def tupleRelabelFunctor (f : P ⟶ Q) :
    ProfileSubstitutionTuple P ⥤ ProfileSubstitutionTuple Q where
  obj R j :=
    (outputTransportFunctor
      (P.inputColor (f.inputEquiv.symm j)) (Q.inputColor j)).obj
        (R (f.inputEquiv.symm j))
  map h j :=
    (outputTransportFunctor
      (P.inputColor (f.inputEquiv.symm j)) (Q.inputColor j)).map
        (h (f.inputEquiv.symm j))
  map_id R := by
    funext j
    exact (outputTransportFunctor
      (P.inputColor (f.inputEquiv.symm j)) (Q.inputColor j)).map_id _
  map_comp h k := by
    funext j
    exact (outputTransportFunctor
      (P.inputColor (f.inputEquiv.symm j)) (Q.inputColor j)).map_comp _ _

/-- The actual original inner-profile map at every source input,
under the original outer relabelling. -/
def tupleRelabelInnerHom (f : P ⟶ Q) (R : ProfileSubstitutionTuple P) (i : P.inputs) :
    (R i).toColoredProfile ⟶ ((tupleRelabelFunctor f).obj R (f.inputEquiv i)).toColoredProfile :=
  eqToHom (congrArg (fun j => (R j).toColoredProfile)
      (f.inputEquiv.symm_apply_apply i).symm) ≫
    outputTransportProfileHom (relabelInputColorEq f (f.inputEquiv i))
      (R (f.inputEquiv.symm (f.inputEquiv i)))

/-- The original relabelling gives the actual map between complete
color-matching substitution shapes. -/
def tupleRelabelShapeHom (f : P ⟶ Q) (R : ProfileSubstitutionTuple P) :
    tupleSubstitutionShape P R ⟶
      tupleSubstitutionShape Q ((tupleRelabelFunctor f).obj R) where
  outputColor_eq := rfl
  innerHom :=
    { equiv := f.inputEquiv
      hom := tupleRelabelInnerHom f R }

/-- Every original inner-profile map commutes with the actual
outer-bijection and output-color transports. -/
theorem tupleRelabelInnerHom_naturality (f : P ⟶ Q)
    {R S : ProfileSubstitutionTuple P} (h : R ⟶ S) (i : P.inputs) :
    ((analyticToProfileFunctor W (P.inputColor i)).map (h i)) ≫ tupleRelabelInnerHom f S i =
      tupleRelabelInnerHom f R i ≫
        ((analyticToProfileFunctor W (Q.inputColor (f.inputEquiv i))).map
          ((tupleRelabelFunctor f).map h (f.inputEquiv i))) := by
  let j := f.inputEquiv.symm (f.inputEquiv i)
  let e : i = j := (f.inputEquiv.symm_apply_apply i).symm
  let r : (R i).toColoredProfile ⟶ (R j).toColoredProfile :=
    eqToHom (congrArg (fun k => (R k).toColoredProfile) e)
  let s : (S i).toColoredProfile ⟶ (S j).toColoredProfile :=
    eqToHom (congrArg (fun k => (S k).toColoredProfile) e)
  let p := relabelInputColorEq f (f.inputEquiv i)
  let hi : (R i).toColoredProfile ⟶ (S i).toColoredProfile :=
    (analyticToProfileFunctor W (P.inputColor i)).map (h i)
  let hj : (R j).toColoredProfile ⟶ (S j).toColoredProfile :=
    (analyticToProfileFunctor W (P.inputColor j)).map (h j)
  have he : hi ≫ s = r ≫ hj :=
    eqToHom_naturality (C := ColoredProfile W)
      (f := fun k => (R k).toColoredProfile) (g := fun k => (S k).toColoredProfile)
      (fun k => (analyticToProfileFunctor W (P.inputColor k)).map (h k)) e
  have hp := outputTransportProfileHom_naturality p (h j)
  change hi ≫ (s ≫ outputTransportProfileHom p (S j)) =
    (r ≫ outputTransportProfileHom p (R j)) ≫
      (outputTransportFunctor (P.inputColor j) (Q.inputColor (f.inputEquiv i))).map (h j)
  calc
    hi ≫ (s ≫ outputTransportProfileHom p (S j)) =
        (hi ≫ s) ≫ outputTransportProfileHom p (S j) := (Category.assoc _ _ _).symm
    _ = (r ≫ hj) ≫ outputTransportProfileHom p (S j) := congrArg (· ≫ _) he
    _ = r ≫ (hj ≫ outputTransportProfileHom p (S j)) := Category.assoc _ _ _
    _ = r ≫ (outputTransportProfileHom p (R j) ≫
        (outputTransportFunctor (P.inputColor j) (Q.inputColor (f.inputEquiv i))).map (h j)) :=
      congrArg (r ≫ ·) hp
    _ = (r ≫ outputTransportProfileHom p (R j)) ≫
        (outputTransportFunctor (P.inputColor j) (Q.inputColor (f.inputEquiv i))).map (h j) :=
      (Category.assoc _ _ _).symm

/-- All original inner-profile morphisms commute with the full
actual map of color-matching substitution shapes. -/
theorem tupleRelabelShapeHom_naturality (f : P ⟶ Q)
    {R S : ProfileSubstitutionTuple P} (h : R ⟶ S) :
    (tupleSubstitutionFunctor P).map h ≫ tupleRelabelShapeHom f S =
      tupleRelabelShapeHom f R ≫
        (tupleSubstitutionFunctor Q).map ((tupleRelabelFunctor f).map h) := by
  apply ColoredSubstitutionData.Hom.ext
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    exact heq_of_eq (tupleRelabelInnerHom_naturality f h i)

/-- The complete shape map retains the original outer input
bijection exactly. -/
theorem tupleRelabelShapeHom_outer (f : P ⟶ Q) (R : ProfileSubstitutionTuple P) :
    ColoredSubstitutionData.outerProfileMap (tupleRelabelShapeHom f R) = f := by
  apply ColoredProfile.Hom.ext
  rfl




end CategoryTheory.Operad.Tensor
end
end
end source_ProfileTupleRelabel

/- Source proof segment: ProfileSlotRelabel -/
section source_ProfileSlotRelabel
/-!
# Actual outer relabelling of coefficient/input slots

The coefficient index is retained and the original input bijection
reindexes every inner profile. Its original input-color equalities
transport the inner outputs. The map of tensor factors uses the
original coefficient relabelling and original inner profile maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {d : W} {P Q : AnalyticIndex W d}

/-- Keep the coefficient index and relabel each original input
profile by the actual outer input bijection. -/
def slotRelabelFunctor (f : P ⟶ Q) : ProfileSlotTuple P ⥤ ProfileSlotTuple Q where
  obj R i := match i with
    | none => R none
    | some i =>
      (outputTransportFunctor
        (P.inputColor (f.inputEquiv.symm i)) (Q.inputColor i)).obj
          (R (some (f.inputEquiv.symm i)))
  map h i := match i with
    | none => h none
    | some i =>
      (outputTransportFunctor
        (P.inputColor (f.inputEquiv.symm i)) (Q.inputColor i)).map
          (h (some (f.inputEquiv.symm i)))
  map_id R := by
    funext i
    cases i with
    | none => rfl
    | some i => exact (outputTransportFunctor
        (P.inputColor (f.inputEquiv.symm i)) (Q.inputColor i)).map_id _
  map_comp h k := by
    funext i
    cases i with
    | none => rfl
    | some i => exact (outputTransportFunctor
        (P.inputColor (f.inputEquiv.symm i)) (Q.inputColor i)).map_comp _ _

/-- Extracting the original inner profiles commutes with the actual
coefficient/input slot relabelling. -/
theorem slotRelabelFunctor_inputs (f : P ⟶ Q) :
    slotRelabelFunctor f ⋙ slotProfileTupleFunctor Q =
      slotProfileTupleFunctor P ⋙ tupleRelabelFunctor f :=
  rfl

variable {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Relabel the actual coefficient/input factor family, using the
original operad coefficient map and every original inner profile map. -/
def slotRelabelFactorsHom (O : ColoredSymmetricCollection W C) (A : W → C)
    (f : P ⟶ Q) (R : ProfileSlotTuple P) :
    (slotInputFactorsFunctor O A P).obj R ⟶
      (slotInputFactorsFunctor O A Q).obj ((slotRelabelFunctor f).obj R) where
  equiv := Equiv.optionCongr f.inputEquiv
  hom i := match i with
    | none => O.map ((analyticToProfileFunctor W d).map f)
    | some i => (operationSummandFunctor O A).map
      (tupleRelabelInnerHom f ((slotProfileTupleFunctor P).obj R) i)

/-- The actual coefficient/input factor relabelling is natural
under every original inner-profile tuple map. -/
theorem slotRelabelFactorsHom_naturality (O : ColoredSymmetricCollection W C) (A : W → C)
    (f : P ⟶ Q) {R S : ProfileSlotTuple P} (h : R ⟶ S) :
    (slotInputFactorsFunctor O A P).map h ≫ slotRelabelFactorsHom O A f S =
      slotRelabelFactorsHom O A f R ≫
        (slotInputFactorsFunctor O A Q).map ((slotRelabelFunctor f).map h) := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro i
    cases i <;> rfl
  · intro i
    cases i with
    | none =>
      change HEq (𝟙 _ ≫ O.map ((analyticToProfileFunctor W d).map f))
        (O.map ((analyticToProfileFunctor W d).map f) ≫ 𝟙 _)
      exact heq_of_eq ((Category.id_comp _).trans (Category.comp_id _).symm)
    | some i =>
      let r := ((slotProfileTupleFunctor P).obj R)
      let s := ((slotProfileTupleFunctor P).obj S)
      let k := ((slotProfileTupleFunctor P).map h)
      let a := (analyticSummand O A).map (h (some i))
      let b := (operationSummandFunctor O A).map (tupleRelabelInnerHom f s i)
      let c := (operationSummandFunctor O A).map (tupleRelabelInnerHom f r i)
      let e := (analyticSummand O A).map (((slotRelabelFunctor f).map h) (some (f.inputEquiv i)))
      have ha : (operationSummandFunctor O A).map
          ((analyticToProfileFunctor W (P.inputColor i)).map (k i)) = a :=
        congrArg (FiniteTensor.tensor (V := C)).map
          (operationFactorsFunctor_map_restrict O A (k i))
      have he : (operationSummandFunctor O A).map
          ((analyticToProfileFunctor W (Q.inputColor (f.inputEquiv i))).map
            ((tupleRelabelFunctor f).map k (f.inputEquiv i))) = e :=
        congrArg (FiniteTensor.tensor (V := C)).map
          (operationFactorsFunctor_map_restrict O A (((tupleRelabelFunctor f).map k)
            (f.inputEquiv i)))
      have hx := congrArg (operationSummandFunctor O A).map
        (tupleRelabelInnerHom_naturality f k i)
      have hx' := ((operationSummandFunctor O A).map_comp
        ((analyticToProfileFunctor W (P.inputColor i)).map (k i))
        (tupleRelabelInnerHom f s i)).symm.trans
          (hx.trans ((operationSummandFunctor O A).map_comp
            (tupleRelabelInnerHom f r i)
            ((analyticToProfileFunctor W (Q.inputColor (f.inputEquiv i))).map
              ((tupleRelabelFunctor f).map k (f.inputEquiv i)))))
      have hxe : a ≫ b = c ≫ e := by
        exact ((congrArg (· ≫ b) ha).symm.trans hx').trans (congrArg (c ≫ ·) he)
      exact heq_of_eq hxe

/-- The actual original coefficient/input relabelling assembles
into a natural transformation of finite factor diagrams. -/
def slotRelabelFactorsNatTrans (O : ColoredSymmetricCollection W C) (A : W → C)
    (f : P ⟶ Q) :
    slotInputFactorsFunctor O A P ⟶ slotRelabelFunctor f ⋙ slotInputFactorsFunctor O A Q where
  app := slotRelabelFactorsHom O A f
  naturality _ _ h := slotRelabelFactorsHom_naturality O A f h

/-- Tensor the actual original outer coefficient/input relabelling,
retaining the original finite input bijection. -/
def slotRelabelTensorNatTrans (O : ColoredSymmetricCollection W C) (A : W → C)
    (f : P ⟶ Q) :
    profileSlotTensorDiagram O A P ⟶ slotRelabelFunctor f ⋙ profileSlotTensorDiagram O A Q :=
  Functor.whiskerRight (slotRelabelFactorsNatTrans O A f) FiniteTensor.tensor




end CategoryTheory.Operad.Tensor
end
end
end source_ProfileSlotRelabel

/- Source proof segment: OperationInputNaturality -/
section source_OperationInputNaturality
/-!
# Full tensor operation input naturality

Maps of original color-indexed inputs induce the original component
maps on all operation-weighted profile tensors. They commute with
every actual input bijection and output-color transport.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C]

private theorem colorInputSquare {A B : W → C} (f : A ⟶ B) {c d : W} (h : c = d) :
    eqToHom (congrArg A h) ≫ f d = f c ≫ eqToHom (congrArg B h) := by
  cases h
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Original component maps on the full coefficient/input factor
family, keeping each operation coefficient fixed. -/
def operationFactorsCarrierMap (O : ColoredSymmetricCollection W C)
    {A B : W → C} (f : A ⟶ B) : operationFactorsFunctor O A ⟶ operationFactorsFunctor O B where
  app P := (analyticFactorsCarrierMap O f).app (profileInputs P)
  naturality P Q h := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro i
      cases i <;> rfl
    · intro i
      cases i with
      | none =>
        change HEq (O.map h ≫ 𝟙 _) (𝟙 _ ≫ O.map h)
        exact heq_of_eq ((Category.comp_id _).trans (Category.id_comp _).symm)
      | some i =>
        change HEq
          (eqToHom (congrArg A (h.inputColor_eq i)) ≫ f (Q.inputColor (h.inputEquiv i)))
          (f (P.inputColor i) ≫ eqToHom (congrArg B (h.inputColor_eq i)))
        exact heq_of_eq (colorInputSquare f (h.inputColor_eq i))

variable [FiniteTensor C]

/-- The original tensor-input map on every full colored profile. -/
def operationSummandCarrierMap (O : ColoredSymmetricCollection W C)
    {A B : W → C} (f : A ⟶ B) : operationSummandFunctor O A ⟶ operationSummandFunctor O B :=
  Functor.whiskerRight (operationFactorsCarrierMap O f) FiniteTensor.tensor

/-- Restriction recovers each original fixed-output analytic tensor
input map exactly. -/
@[simp]
theorem operationSummandCarrierMap_app (O : ColoredSymmetricCollection W C)
    {A B : W → C} (f : A ⟶ B) (P : ColoredProfile W) :
    (operationSummandCarrierMap O f).app P =
      (analyticSummandCarrierMap O f).app (profileInputs P) :=
  rfl

@[simp]
theorem operationSummandCarrierMap_id (O : ColoredSymmetricCollection W C) (A : W → C) :
    operationSummandCarrierMap O (𝟙 A) = 𝟙 (operationSummandFunctor O A) := by
  apply NatTrans.ext
  funext P
  exact congrArg (fun a => a.app (profileInputs P)) (analyticSummandCarrierMap_id O (A := A))

theorem operationSummandCarrierMap_comp (O : ColoredSymmetricCollection W C)
    {A B D : W → C} (f : A ⟶ B) (g : B ⟶ D) :
    operationSummandCarrierMap O (f ≫ g) =
      operationSummandCarrierMap O f ≫ operationSummandCarrierMap O g := by
  apply NatTrans.ext
  funext P
  exact congrArg (fun a => a.app (profileInputs P)) (analyticSummandCarrierMap_comp O f g)




end CategoryTheory.Operad.Tensor
end
end
end source_OperationInputNaturality

/- Source proof segment: SubstitutionInputMaps -/
section source_SubstitutionInputMaps
/-!
# Original input maps in tensor operadic substitution

The original input component map is applied in every leaf slot of
the full substitution source. Operation coefficients remain fixed.
Both original finite tensor groupings are retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Apply each original input component to each inner operation
block, while retaining the original outer coefficient block. -/
def nestedOperationInputMap (O : ColoredSymmetricCollection W C) {A B : W → C}
    (f : A ⟶ B) (s : ColoredSubstitutionData W) :
    nestedOperationFactors O A s ⟶ nestedOperationFactors O B s where
  equiv := Equiv.refl (Option s.inner.index)
  hom i := match i with
    | none => 𝟙 ((FiniteFamily.singleton (C := C)).obj (O.obj s.outerProfile))
    | some i => (operationFactorsCarrierMap O f).app (s.inner.obj i)

/-- Apply every original leaf-input component while retaining the
complete original operadic coefficient-substitution block. -/
def substitutionLeafInputMap (O : ColoredSymmetricCollection W C) {A B : W → C}
    (f : A ⟶ B) (s : ColoredSubstitutionData W) :
    substitutionInputFactors O A s ⟶ substitutionInputFactors O B s where
  equiv := Equiv.refl (Option s.totalProfile.inputs)
  hom i := match i with
    | none => 𝟙 ((ColoredOperadObj.substitutionFactors O).obj s)
    | some i => (FiniteFamily.singleton (C := C)).map (f (s.totalProfile.inputColor i))

omit [FiniteTensor C] in
/-- The exact original factor regrouping commutes with every
original leaf-input map. -/
theorem substitutionFactorsIso_input (O : ColoredSymmetricCollection W C) {A B : W → C}
    (f : A ⟶ B) (s : ColoredSubstitutionData W) :
    (FiniteFamily.flatten (C := C)).map (nestedOperationInputMap O f s) ≫
        (substitutionFactorsIso O B s).hom =
      (substitutionFactorsIso O A s).hom ≫
        (FiniteFamily.flatten (C := C)).map (substitutionLeafInputMap O f s) := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro i
    rcases i with ⟨i, j⟩
    cases i with
    | none => cases j; rfl
    | some i => cases j <;> rfl
  · intro i
    rcases i with ⟨i, j⟩
    cases i with
    | none => cases j; exact HEq.rfl
    | some i =>
      cases j with
      | none => exact HEq.rfl
      | some j =>
        let a := f ((s.inner.obj i).inputColor j)
        change HEq (a ≫ 𝟙 _) (𝟙 _ ≫ a)
        exact heq_of_eq ((Category.comp_id a).trans (Category.id_comp a).symm)

/-- The original coefficient substitution and singleton input
unitors commute with every original input component map. -/
theorem operadCoefficientMap_input (O : ColoredOperadObj W C) {A B : W → C}
    (f : A ⟶ B) (s : ColoredSubstitutionData W) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map
        (substitutionLeafInputMap O.toCollection f s) ≫ operadCoefficientMap O B s =
      operadCoefficientMap O A s ≫
        (operationFactorsCarrierMap O.toCollection f).app s.totalProfile := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      change HEq
        ((FiniteTensor.tensor (V := C)).map (𝟙 _) ≫ O.subst.app s)
        (O.subst.app s ≫ 𝟙 _)
      have hi := (FiniteTensor.tensor (V := C)).map_id
        ((ColoredOperadObj.substitutionFactors O.toCollection).obj s)
      exact heq_of_eq ((congrArg (· ≫ O.subst.app s) hi).trans
        ((Category.id_comp _).trans (Category.comp_id _).symm))
    | some i =>
      let a := f (s.totalProfile.inputColor i)
      change HEq
        ((FiniteTensor.tensor (V := C)).map ((FiniteFamily.singleton (C := C)).map a) ≫
          (FiniteTensor.singletonIso (V := C)).hom.app _)
        ((FiniteTensor.singletonIso (V := C)).hom.app _ ≫ a)
      exact heq_of_eq ((FiniteTensor.singletonIso (V := C)).hom.naturality a)

/-- The actual input map on the complete original substitution
tensor source. -/
def algebraSubstitutionInputMap (O : ColoredSymmetricCollection W C) {A B : W → C}
    (f : A ⟶ B) (s : ColoredSubstitutionData W) :
    algebraSubstitutionSource O A s ⟶ algebraSubstitutionSource O B s :=
  (FiniteTensor.tensor (V := C)).map
    ((FiniteFamily.flatten (C := C)).map (nestedOperationInputMap O f s))




end CategoryTheory.Operad.Tensor
end
end
end source_SubstitutionInputMaps

/- Source proof segment: SubstitutionInputNaturality -/
section source_SubstitutionInputNaturality
/-!
# Original tensor substitution input naturality

The actual coefficient regrouping, tensor flattening and operadic
substitution maps commute with every original color-indexed input
component. The operation coefficient maps remain unchanged.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem composeThreeSquares {V : Type*} [Category* V]
    {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : V}
    (a₀ : X₀ ⟶ Y₀) (a₁ : X₁ ⟶ Y₁) (a₂ : X₂ ⟶ Y₂) (a₃ : X₃ ⟶ Y₃)
    (b₀ : X₀ ⟶ X₁) (b₁ : X₁ ⟶ X₂) (b₂ : X₂ ⟶ X₃)
    (c₀ : Y₀ ⟶ Y₁) (c₁ : Y₁ ⟶ Y₂) (c₂ : Y₂ ⟶ Y₃)
    (h₀ : a₀ ≫ c₀ = b₀ ≫ a₁) (h₁ : a₁ ≫ c₁ = b₁ ≫ a₂)
    (h₂ : a₂ ≫ c₂ = b₂ ≫ a₃) :
    a₀ ≫ c₀ ≫ c₁ ≫ c₂ = (b₀ ≫ b₁ ≫ b₂) ≫ a₃ := by
  rw [← Category.assoc a₀ c₀, h₀]
  rw [Category.assoc b₀ a₁, ← Category.assoc a₁ c₁, h₁]
  rw [Category.assoc b₁ a₂, h₂]
  simp only [Category.assoc]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The complete original operadic coefficient/input substitution
commutes with every original input component map. -/
@[reassoc]
theorem operadSubstitutionInputs_input (O : ColoredOperadObj W C) {A B : W → C}
    (f : A ⟶ B) (s : ColoredSubstitutionData W) :
    algebraSubstitutionInputMap O.toCollection f s ≫ operadSubstitutionInputs O B s =
      operadSubstitutionInputs O A s ≫
        (operationSummandCarrierMap O.toCollection f).app s.totalProfile := by
  let a := (FiniteFamily.flatten (C := C)).map (nestedOperationInputMap O.toCollection f s)
  let b := (substitutionFactorsIso O.toCollection A s).hom
  let b' := (substitutionFactorsIso O.toCollection B s).hom
  let l := substitutionLeafInputMap O.toCollection f s
  let c := (FiniteTensor.flattenIso (V := C)).hom.app (substitutionInputFactors O.toCollection A s)
  let c' := (FiniteTensor.flattenIso (V := C)).hom.app (substitutionInputFactors O.toCollection B s)
  let e := operadCoefficientMap O A s
  let e' := operadCoefficientMap O B s
  let h := (operationFactorsCarrierMap O.toCollection f).app s.totalProfile
  have hb : (FiniteTensor.tensor (V := C)).map a ≫ (FiniteTensor.tensor (V := C)).map b' =
      (FiniteTensor.tensor (V := C)).map b ≫
        (FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map l) :=
    ((FiniteTensor.tensor (V := C)).map_comp a b').symm.trans
      ((congrArg (FiniteTensor.tensor (V := C)).map (substitutionFactorsIso_input
        O.toCollection f s)).trans
        ((FiniteTensor.tensor (V := C)).map_comp b _))
  have hc : (FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map l) ≫ c' =
      c ≫ (FiniteTensor.tensor (V := C)).map ((FiniteFamily.map FiniteTensor.tensor).map l) :=
    (FiniteTensor.flattenIso (V := C)).hom.naturality l
  have he : (FiniteTensor.tensor (V := C)).map ((FiniteFamily.map FiniteTensor.tensor).map l) ≫
      (FiniteTensor.tensor (V := C)).map e' =
      (FiniteTensor.tensor (V := C)).map e ≫ (FiniteTensor.tensor (V := C)).map h :=
    ((FiniteTensor.tensor (V := C)).map_comp _ e').symm.trans
      ((congrArg (FiniteTensor.tensor (V := C)).map (operadCoefficientMap_input O f s)).trans
        ((FiniteTensor.tensor (V := C)).map_comp e h))
  change (FiniteTensor.tensor (V := C)).map a ≫
      ((FiniteTensor.tensor (V := C)).map b' ≫ c' ≫ (FiniteTensor.tensor (V := C)).map e') =
    ((FiniteTensor.tensor (V := C)).map b ≫ c ≫ (FiniteTensor.tensor (V := C)).map e) ≫
      (FiniteTensor.tensor (V := C)).map h
  exact composeThreeSquares
    ((FiniteTensor.tensor (V := C)).map a)
    ((FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map l))
    ((FiniteTensor.tensor (V := C)).map ((FiniteFamily.map FiniteTensor.tensor).map l))
    ((FiniteTensor.tensor (V := C)).map h)
    ((FiniteTensor.tensor (V := C)).map b) c ((FiniteTensor.tensor (V := C)).map e)
    ((FiniteTensor.tensor (V := C)).map b') c' ((FiniteTensor.tensor (V := C)).map e') hb hc he



end CategoryTheory.Operad.Tensor
end
end
end source_SubstitutionInputNaturality

/- Source proof segment: SquareComposition -/
section source_SquareComposition
@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe v u

theorem composeTwoSquares {V : Type u} [Category.{v} V]
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : V}
    (a₀ : X₀ ⟶ Y₀) (a₁ : X₁ ⟶ Y₁) (a₂ : X₂ ⟶ Y₂)
    (b₀ : X₀ ⟶ X₁) (b₁ : X₁ ⟶ X₂)
    (c₀ : Y₀ ⟶ Y₁) (c₁ : Y₁ ⟶ Y₂)
    (h₀ : a₀ ≫ c₀ = b₀ ≫ a₁) (h₁ : a₁ ≫ c₁ = b₁ ≫ a₂) :
    a₀ ≫ c₀ ≫ c₁ = (b₀ ≫ b₁) ≫ a₂ := by
  rw [← Category.assoc a₀ c₀, h₀, Category.assoc b₀ a₁, h₁, Category.assoc]

theorem composeThreeOperationSquares {V : Type u} [Category.{v} V]
    {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : V}
    (a₀ : X₀ ⟶ Y₀) (a₁ : X₁ ⟶ Y₁) (a₂ : X₂ ⟶ Y₂) (a₃ : X₃ ⟶ Y₃)
    (b₀ : X₀ ⟶ X₁) (b₁ : X₁ ⟶ X₂) (b₂ : X₂ ⟶ X₃)
    (c₀ : Y₀ ⟶ Y₁) (c₁ : Y₁ ⟶ Y₂) (c₂ : Y₂ ⟶ Y₃)
    (h₀ : a₀ ≫ c₀ = b₀ ≫ a₁) (h₁ : a₁ ≫ c₁ = b₁ ≫ a₂)
    (h₂ : a₂ ≫ c₂ = b₂ ≫ a₃) :
    a₀ ≫ c₀ ≫ c₁ ≫ c₂ = (b₀ ≫ b₁ ≫ b₂) ≫ a₃ := by
  rw [← Category.assoc a₀ c₀, h₀]
  rw [Category.assoc b₀ a₁, ← Category.assoc a₁ c₁, h₁]
  rw [Category.assoc b₁ a₂, h₂]
  simp only [Category.assoc]

theorem descentInputSquare {V : Type u} [Category.{v} V]
    {X Y U V' A B : V}
    (iX : X ⟶ A) (iY : Y ⟶ B) (h : X ⟶ Y) (f : A ⟶ B)
    (a : A ⟶ U) (b : B ⟶ V') (g : U ⟶ V')
    (sX : X ⟶ U) (sY : Y ⟶ V')
    (hi : iX ≫ f = h ≫ iY) (ha : iX ≫ a = sX) (hb : iY ≫ b = sY)
    (hs : h ≫ sY = sX ≫ g) : iX ≫ (f ≫ b) = iX ≫ (a ≫ g) := by
  rw [← Category.assoc iX f, hi, Category.assoc h iY, hb, hs, ← ha, Category.assoc]

theorem descentRelabelSquare {V : Type u} [Category.{v} V]
    {X Y A B Z : V}
    (iX : X ⟶ A) (iY : Y ⟶ B) (h : X ⟶ Y) (f : A ⟶ B)
    (a : A ⟶ Z) (b : B ⟶ Z) (sX : X ⟶ Z) (sY : Y ⟶ Z)
    (hi : iX ≫ f = h ≫ iY) (ha : iX ≫ a = sX) (hb : iY ≫ b = sY)
    (hs : h ≫ sY = sX) : iX ≫ (f ≫ b) = iX ≫ a := by
  rw [← Category.assoc iX f, hi, Category.assoc h iY, hb, hs, ha]

end CategoryTheory.Operad.Tensor
end
end source_SquareComposition

/- Source proof segment: ProfileSlotInputMaps -/
section source_ProfileSlotInputMaps
/-!
# Actual input maps on coefficient/profile-slot diagrams

Every original color-indexed component induces the original
operation-summand tensor map at each input slot. The coefficient
slot remains its original identity map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Original component maps on the actual coefficient/input-slot
family diagram. -/
def profileSlotInputFamilyMap (O : ColoredSymmetricCollection W C) {A B : W → C}
    (f : A ⟶ B) {d : W} (P : AnalyticIndex W d) :
    profileSlotFamilyFunctor O A P ⟶ profileSlotFamilyFunctor O B P where
  app Q i := match i with
    | none => 𝟙 (O.obj P.toColoredProfile)
    | some i => (analyticSummandCarrierMap O f).app (Q (some i))
  naturality Q R h := by
    funext i
    cases i with
    | none => exact (Category.id_comp _).trans (Category.comp_id _).symm
    | some i => exact (analyticSummandCarrierMap O f).naturality (h (some i))

/-- The original input maps on actual finite coefficient/profile
factor families. -/
def profileSlotInputFactorsMap (O : ColoredSymmetricCollection W C) {A B : W → C}
    (f : A ⟶ B) {d : W} (P : AnalyticIndex W d) :
    slotInputFactorsFunctor O A P ⟶ slotInputFactorsFunctor O B P :=
  Functor.whiskerRight (profileSlotInputFamilyMap O f P)
    (FiniteFamily.fixedIndexFunctor (analyticFactorsIndex P))

/-- Tensor the original coefficient identity and all original
input operation-summand maps. -/
def profileSlotInputTensorMap (O : ColoredSymmetricCollection W C) {A B : W → C}
    (f : A ⟶ B) {d : W} (P : AnalyticIndex W d) :
    profileSlotTensorDiagram O A P ⟶ profileSlotTensorDiagram O B P :=
  Functor.whiskerRight (profileSlotInputFactorsMap O f P) FiniteTensor.tensor

/-- The original complete substitution source input map at each
actual coefficient/input tuple. -/
def profileSlotRawInputMap (O : ColoredSymmetricCollection W C) {A B : W → C}
    (f : A ⟶ B) {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (slotProfileTupleFunctor P ⋙ tupleSubstitutionSource O A P).obj Q ⟶
      (slotProfileTupleFunctor P ⋙ tupleSubstitutionSource O B P).obj Q :=
  algebraSubstitutionInputMap O f
    (tupleSubstitutionShape P ((slotProfileTupleFunctor P).obj Q))

variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- Each complete original substitution cocone leg commutes with
the original input component map and profile coinvariant map. -/
@[reassoc]
theorem profileSlotSubstitutionCocone_input (O : ColoredOperadObj W C) {A B : W → C}
    (f : A ⟶ B) {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    profileSlotRawInputMap O.toCollection f P Q ≫
        (profileSlotSubstitutionCocone O B P).ι.app Q =
      (profileSlotSubstitutionCocone O A P).ι.app Q ≫ profileMap O.toCollection f d := by
  let s := tupleSubstitutionShape P ((slotProfileTupleFunctor P).obj Q)
  let h := algebraSubstitutionInputMap O.toCollection f s
  let a := operadSubstitutionInputs O A s
  let b := operadSubstitutionInputs O B s
  let g := (analyticSummandCarrierMap O.toCollection f).app (profileInputs s.totalProfile)
  let iA := profileι O.toCollection A (profileInputs s.totalProfile)
  let iB := profileι O.toCollection B (profileInputs s.totalProfile)
  have hs : h ≫ b = a ≫ g := operadSubstitutionInputs_input O f s
  have hi : g ≫ iB = iA ≫ profileMap O.toCollection f d :=
    (profileι_map O.toCollection f (profileInputs s.totalProfile)).symm
  change h ≫ (b ≫ iB) = (a ≫ iA) ≫ profileMap O.toCollection f d
  exact composeTwoSquares h g (profileMap O.toCollection f d) a iA b iB hs hi




end CategoryTheory.Operad.Tensor
end
end
end source_ProfileSlotInputMaps

/- Source proof segment: ProfileSlotInjectionSquares -/
section source_ProfileSlotInjectionSquares
/-!
# Original input and relabelling squares for slot injections

The finite tensor of the actual coefficient identity and profile
injections commutes with every original input map and outer profile
relabelling. These are the squares used by uniqueness of the actual
finite tensor colimit descents.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The actual original factor map from a slot tuple into its
coefficient-weighted profile-colimit tensor factors. -/
def profileSlotInjectionFactors (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (slotInputFactorsFunctor O A P).obj Q ⟶
      (analyticFactors O (profileCoinvariants O A)).obj P where
  equiv := Equiv.refl (Option P.inputs)
  hom i := match i with
    | none => 𝟙 (O.obj P.toColoredProfile)
    | some i => profileι O A (Q (some i))

/-- Original input component maps commute with the actual
coefficient/input slot injection factors. -/
theorem profileSlotInjectionFactors_input (O : ColoredSymmetricCollection W C)
    {A B : W → C} (f : A ⟶ B) {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (profileSlotInputFactorsMap O f P).app Q ≫ profileSlotInjectionFactors O B P Q =
      profileSlotInjectionFactors O A P Q ≫
        (analyticFactorsCarrierMap O (profileMap O f)).app P := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      change HEq (𝟙 _ ≫ 𝟙 _) (𝟙 _ ≫ 𝟙 _)
      exact HEq.rfl
    | some i =>
      change HEq
        ((analyticSummandCarrierMap O f).app (Q (some i)) ≫ profileι O B (Q (some i)))
        (profileι O A (Q (some i)) ≫ profileMap O f (P.inputColor i))
      exact heq_of_eq (profileι_map O f (Q (some i))).symm

/-- Actual tensor slot injections commute with every original
color-indexed input map on the profile coinvariants. -/
@[reassoc]
theorem profileSlotTensorCocone_input (O : ColoredSymmetricCollection W C)
    {A B : W → C} (f : A ⟶ B) {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (profileSlotInputTensorMap O f P).app Q ≫ (profileSlotTensorCocone O B P).ι.app Q =
      (profileSlotTensorCocone O A P).ι.app Q ≫
        (analyticSummandCarrierMap O (profileMap O f)).app P :=
  ((FiniteTensor.tensor (V := C)).map_comp _ _).symm.trans
    ((congrArg (FiniteTensor.tensor (V := C)).map (profileSlotInjectionFactors_input O f P Q)).trans
      ((FiniteTensor.tensor (V := C)).map_comp _ _))

/-- The original outer input bijection commutes with the actual
profile-colimit factor injections, including each inner output-color
transport and the original coefficient relabelling. -/
theorem profileSlotInjectionFactors_relabel (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} {P Q : AnalyticIndex W d} (f : P ⟶ Q) (R : ProfileSlotTuple P) :
    slotRelabelFactorsHom O A f R ≫
        profileSlotInjectionFactors O A Q ((slotRelabelFunctor f).obj R) =
      profileSlotInjectionFactors O A P R ≫
        (analyticFactors O (profileCoinvariants O A)).map f := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro i
    cases i <;> rfl
  · intro i
    cases i with
    | none =>
      let a := O.map ((analyticToProfileFunctor W d).map f)
      change HEq (a ≫ 𝟙 _) (𝟙 _ ≫ a)
      exact heq_of_eq ((Category.comp_id a).trans (Category.id_comp a).symm)
    | some i =>
      let g := tupleRelabelInnerHom f ((slotProfileTupleFunctor P).obj R) i
      let a : Operations O A (profileCoinvariants O A) :=
        { app := fun _ P => profileι O A P
          equivariance := fun _ _ _ g => profile_relabel_ι O A g }
      exact heq_of_eq (a.profile_equivariance g)

/-- The original outer input bijection commutes with the actual
finite tensor slot injections and original analytic profile map. -/
@[reassoc]
theorem profileSlotTensorCocone_relabel (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} {P Q : AnalyticIndex W d} (f : P ⟶ Q) (R : ProfileSlotTuple P) :
    (slotRelabelTensorNatTrans O A f).app R ≫
        (profileSlotTensorCocone O A Q).ι.app ((slotRelabelFunctor f).obj R) =
      (profileSlotTensorCocone O A P).ι.app R ≫
        (analyticSummand O (profileCoinvariants O A)).map f :=
  ((FiniteTensor.tensor (V := C)).map_comp _ _).symm.trans
    ((congrArg (FiniteTensor.tensor (V := C)).map (profileSlotInjectionFactors_relabel O A f
      R)).trans
      ((FiniteTensor.tensor (V := C)).map_comp _ _))




end CategoryTheory.Operad.Tensor
end
end
end source_ProfileSlotInjectionSquares

/- Source proof segment: ProfileSlotCoconeComparison -/
section source_ProfileSlotCoconeComparison
/-!
# Original slot cocone comparison

The generic functor-applied cocone and the exact analytic-point
cocone have the same original coefficient/input injections. Their
point comparison is constructed from the component point equations,
with every original finite index retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The actual original tuple of slot colimit points is equal to
the coefficient/input point family of the original analytic summand. -/
theorem profileSlotPointFamilyEq (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (fun i : Option P.inputs => (profileSlotCocone O A P i).pt) =
      (fun i : Option P.inputs => match i with
        | none => O.obj P.toColoredProfile
        | some i => profileCoinvariants O A (P.inputColor i)) := by
  funext i
  cases i <;> rfl

/-- Tensor the original slot point equalities as the actual
point comparison isomorphism. -/
def profileSlotPointIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    ((fixedIndexTensorFunctor (analyticFactorsIndex P)).mapCocone
      (profileSlotFamilyCocone O A P)).pt ≅ (profileSlotTensorCocone O A P).pt :=
  (fixedIndexTensorFunctor (analyticFactorsIndex P)).mapIso
    (eqToIso (profileSlotPointFamilyEq O A P))

/-- The original point comparison commutes with every original
coefficient/input tuple injection. -/
theorem profileSlotPointIso_ι (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (((fixedIndexTensorFunctor (analyticFactorsIndex P)).mapCocone
      (profileSlotFamilyCocone O A P)).ι.app Q) ≫ (profileSlotPointIso O A P).hom =
      (profileSlotTensorCocone O A P).ι.app Q := by
  let c := profileSlotFamilyCocone O A P
  let h := profileSlotPointFamilyEq O A P
  let F := fixedIndexTensorFunctor (C := C) (analyticFactorsIndex P)
  have hf : c.ι.app Q ≫ eqToHom h =
      (fun i : Option P.inputs => match i with
        | none => 𝟙 (O.obj P.toColoredProfile)
        | some i => profileι O A (Q (some i))) := by
    funext i
    have hp := congrFun h i
    cases i with
    | none =>
      change 𝟙 _ ≫ (eqToHom h) none = 𝟙 _
      have he : (eqToHom h) none = eqToHom hp := by
        exact eqToHom_map (Pi.eval (fun _ : Option P.inputs => C) none) h
      rw [he]
      exact Category.id_comp _
    | some i =>
      change profileι O A (Q (some i)) ≫ (eqToHom h) (some i) = profileι O A (Q (some i))
      have he : (eqToHom h) (some i) = 𝟙 _ := by
        have hi := eqToHom_map (Pi.eval (fun _ : Option P.inputs => C) (some i)) h
        exact hi.trans (eqToHom_refl _ _)
      rw [he]
      exact Category.comp_id _
  have hm := (F.map_comp (c.ι.app Q) (eqToHom h)).symm.trans (congrArg F.map hf)
  change F.map (c.ι.app Q) ≫ F.map (eqToHom h) =
    (FiniteTensor.tensor (V := C)).map (profileSlotInjectionFactors O A P Q)
  have hfamily : (FiniteFamily.fixedIndexFunctor (analyticFactorsIndex P)).map
      (fun i : Option P.inputs => match i with
        | none => 𝟙 (O.obj P.toColoredProfile)
        | some i => profileι O A (Q (some i))) = profileSlotInjectionFactors O A P Q := by
    apply FiniteFamily.Hom_ext
    · rfl
    · intro i
      cases i <;> exact HEq.rfl
  exact hm.trans (congrArg (FiniteTensor.tensor (V := C)).map hfamily)

/-- The exact analytic-point slot cocone is isomorphic to the
generic cocone obtained by applying the original fixed-index tensor
functor to the original slot injections. -/
def profileSlotCoconeIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (fixedIndexTensorFunctor (analyticFactorsIndex P)).mapCocone (profileSlotFamilyCocone O A P) ≅
      profileSlotTensorCocone O A P :=
  Cocone.ext (profileSlotPointIso O A P) (fun Q => profileSlotPointIso_ι O A P Q)



end CategoryTheory.Operad.Tensor
end
end
end source_ProfileSlotCoconeComparison

/- Source proof segment: ProfileSubstitutionAssemblyMaps -/
section source_ProfileSubstitutionAssemblyMaps
/-!
# Original tensor-profile substitution assembly maps

The complete map from an actual coefficient/input tensor to the
coinvariants is the coefficient singleton unitor, original tensor
flattening, original operadic substitution and original profile
injection. These are the maps to be descended by the colimit proof.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The actual map from a coefficient/input tensor to the complete
original substitution source. -/
def profileSubstitutionAssemblyMap (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (profileSlotTensorDiagram O A P).obj Q ⟶
      algebraSubstitutionSource O A
        (tupleSubstitutionShape P ((slotProfileTupleFunctor P).obj Q)) :=
  (FiniteTensor.tensor (V := C)).map (coefficientTensorIso O A P Q).hom ≫
    (FiniteTensor.flattenIso (V := C)).inv.app
      (nestedOperationFactors O A (tupleSubstitutionShape P ((slotProfileTupleFunctor P).obj Q)))

/-- The natural tensor assembly uses precisely the original
coefficient unitor and tensor flattening maps. -/
@[simp]
theorem profileSlotAssemblyIso_hom_app (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (profileSlotAssemblyIso O A P).hom.app Q = profileSubstitutionAssemblyMap O A P Q :=
  rfl

variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- Every assembled cocone leg is the actual original substitution
map followed by its original profile quotient injection. -/
@[simp]
theorem assembledProfileSubstitutionCocone_ι (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (assembledProfileSubstitutionCocone O A P).ι.app Q =
      profileSubstitutionAssemblyMap O.toCollection A P Q ≫
        operadSubstitutionInputs O A
          (tupleSubstitutionShape P ((slotProfileTupleFunctor P).obj Q)) ≫
        profileι O.toCollection A
          ((tupleTotalFunctor P).obj ((slotProfileTupleFunctor P).obj Q)) :=
  rfl

/-- All original coefficient/input diagram maps commute with the
complete original assembly and substitution cocone legs. -/
@[reassoc]
theorem assembledProfileSubstitutionCocone_naturality (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) {Q R : ProfileSlotTuple P} (f : Q ⟶ R) :
    (profileSlotTensorDiagram O.toCollection A P).map f ≫
        (assembledProfileSubstitutionCocone O A P).ι.app R =
      (assembledProfileSubstitutionCocone O A P).ι.app Q := by
  have h := (assembledProfileSubstitutionCocone O A P).ι.naturality f
  exact h.trans (Category.comp_id _)




end CategoryTheory.Operad.Tensor
end
end
end source_ProfileSubstitutionAssemblyMaps

/- Source proof segment: ProfileAssemblyInput -/
section source_ProfileAssemblyInput
/-!
# Original input naturality of tensor-profile assembly

The actual coefficient singleton unitor and original tensor
flattening commute with each original input component map. The
assembled original operadic substitution cocone has the same square.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The actual coefficient unitor retains the original coefficient
and commutes with every original inner input tensor map. -/
theorem coefficientTensorIso_input (O : ColoredSymmetricCollection W C) {A B : W → C}
    (f : A ⟶ B) {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (profileSlotInputFactorsMap O f P).app Q ≫ (coefficientTensorIso O B P Q).hom =
      (coefficientTensorIso O A P Q).hom ≫
        (FiniteFamily.map FiniteTensor.tensor).map
          (nestedOperationInputMap O f
            (tupleSubstitutionShape P ((slotProfileTupleFunctor P).obj Q))) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      let c := O.obj P.toColoredProfile
      let a := (FiniteTensor.singletonIso (V := C)).inv.app c
      change HEq (𝟙 c ≫ a)
        (a ≫ (FiniteTensor.tensor (V := C)).map (𝟙 ((FiniteFamily.singleton (C := C)).obj c)))
      have h := (FiniteTensor.tensor (V := C)).map_id ((FiniteFamily.singleton (C := C)).obj c)
      exact heq_of_eq ((Category.id_comp a).trans
        ((congrArg (a ≫ ·) h).trans (Category.comp_id a)).symm)
    | some i =>
      let a := (analyticSummandCarrierMap O f).app (Q (some i))
      change HEq (a ≫ 𝟙 _) (𝟙 _ ≫ a)
      exact heq_of_eq ((Category.comp_id a).trans (Category.id_comp a).symm)

/-- The complete original tensor assembly commutes with every
original color-indexed input component map. -/
@[reassoc]
theorem profileSubstitutionAssemblyMap_input (O : ColoredSymmetricCollection W C) {A B : W → C}
    (f : A ⟶ B) {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (profileSlotInputTensorMap O f P).app Q ≫ profileSubstitutionAssemblyMap O B P Q =
      profileSubstitutionAssemblyMap O A P Q ≫ profileSlotRawInputMap O f P Q := by
  let s := tupleSubstitutionShape P ((slotProfileTupleFunctor P).obj Q)
  let h := nestedOperationInputMap O f s
  let a := (profileSlotInputFactorsMap O f P).app Q
  let b := (coefficientTensorIso O A P Q).hom
  let b' := (coefficientTensorIso O B P Q).hom
  let c := (FiniteTensor.flattenIso (V := C)).inv.app (nestedOperationFactors O A s)
  let c' := (FiniteTensor.flattenIso (V := C)).inv.app (nestedOperationFactors O B s)
  have hb : (FiniteTensor.tensor (V := C)).map a ≫ (FiniteTensor.tensor (V := C)).map b' =
      (FiniteTensor.tensor (V := C)).map b ≫
        (FiniteTensor.tensor (V := C)).map ((FiniteFamily.map FiniteTensor.tensor).map h) :=
    ((FiniteTensor.tensor (V := C)).map_comp a b').symm.trans
      ((congrArg (FiniteTensor.tensor (V := C)).map (coefficientTensorIso_input O f P Q)).trans
        ((FiniteTensor.tensor (V := C)).map_comp b _))
  have hc : (FiniteTensor.tensor (V := C)).map ((FiniteFamily.map FiniteTensor.tensor).map h) ≫ c' =
      c ≫ (FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map h) :=
    (FiniteTensor.flattenIso (V := C)).inv.naturality h
  change (FiniteTensor.tensor (V := C)).map a ≫
      ((FiniteTensor.tensor (V := C)).map b' ≫ c') =
    ((FiniteTensor.tensor (V := C)).map b ≫ c) ≫
      (FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map h)
  exact composeTwoSquares
    ((FiniteTensor.tensor (V := C)).map a)
    ((FiniteTensor.tensor (V := C)).map ((FiniteFamily.map FiniteTensor.tensor).map h))
    ((FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map h))
    ((FiniteTensor.tensor (V := C)).map b) c
    ((FiniteTensor.tensor (V := C)).map b') c' hb hc

variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The full assembled original substitution cocone commutes with
the original input map and its original coinvariant map. -/
@[reassoc]
theorem assembledProfileSubstitutionCocone_input (O : ColoredOperadObj W C) {A B : W → C}
    (f : A ⟶ B) {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (profileSlotInputTensorMap O.toCollection f P).app Q ≫
        (assembledProfileSubstitutionCocone O B P).ι.app Q =
      (assembledProfileSubstitutionCocone O A P).ι.app Q ≫ profileMap O.toCollection f d := by
  let a := profileSubstitutionAssemblyMap O.toCollection A P Q
  let b := profileSubstitutionAssemblyMap O.toCollection B P Q
  let u := (profileSlotInputTensorMap O.toCollection f P).app Q
  let v := profileSlotRawInputMap O.toCollection f P Q
  let iA := (profileSlotSubstitutionCocone O A P).ι.app Q
  let iB := (profileSlotSubstitutionCocone O B P).ι.app Q
  have h : u ≫ b = a ≫ v := profileSubstitutionAssemblyMap_input O.toCollection f P Q
  have hi : v ≫ iB = iA ≫ profileMap O.toCollection f d :=
    profileSlotSubstitutionCocone_input O f P Q
  change u ≫ (b ≫ iB) = (a ≫ iA) ≫ profileMap O.toCollection f d
  exact composeTwoSquares u v (profileMap O.toCollection f d) a iA b iB h hi



end CategoryTheory.Operad.Tensor
end
end
end source_ProfileAssemblyInput

/- Source proof segment: ProfileRelabelSubstitution -/
section source_ProfileRelabelSubstitution
/-!
# Original relabelling of operadic substitution maps

The actual outer profile input bijection and its original inner
output transports induce the complete source shape map. The original
operad coefficient substitution and original profile quotient maps
commute with that actual shape map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u}

/-- The original flattened profile map induced by an actual outer
input relabelling and every original inner input profile. -/
def tupleRelabelTotalHom {d : W} {P Q : AnalyticIndex W d} (f : P ⟶ Q)
    (R : ProfileSubstitutionTuple P) :
    (tupleTotalFunctor P).obj R ⟶
      (tupleTotalFunctor Q).obj ((tupleRelabelFunctor f).obj R) :=
  ColoredSubstitutionData.totalProfileMap (tupleRelabelShapeHom f R)

variable {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The actual complete-source relabelling commutes with the
original operadic substitution and original coinvariant injections. -/
@[reassoc]
theorem profileSubstitutionCocone_relabel (O : ColoredOperadObj W C) (A : W → C)
    {d : W} {P Q : AnalyticIndex W d} (f : P ⟶ Q) (R : ProfileSubstitutionTuple P) :
    (algebraSubstitutionSourceFunctor O.toCollection A).map (tupleRelabelShapeHom f R) ≫
        (profileSubstitutionCocone O A Q).ι.app ((tupleRelabelFunctor f).obj R) =
      (profileSubstitutionCocone O A P).ι.app R := by
  let s := tupleSubstitutionShape P R
  let t := tupleSubstitutionShape Q ((tupleRelabelFunctor f).obj R)
  let g := tupleRelabelShapeHom f R
  let u : algebraSubstitutionSource O.toCollection A s ⟶
      algebraSubstitutionSource O.toCollection A t :=
    (algebraSubstitutionSourceFunctor O.toCollection A).map g
  let a := operadSubstitutionInputs O A s
  let b := operadSubstitutionInputs O A t
  let iP := profileι O.toCollection A ((tupleTotalFunctor P).obj R)
  let iQ := profileι O.toCollection A ((tupleTotalFunctor Q).obj ((tupleRelabelFunctor f).obj R))
  let z := (analyticSummand O.toCollection A).map (tupleRelabelTotalHom f R)
  have hz : (operationSummandFunctor O.toCollection A).map
      (ColoredSubstitutionData.totalProfileMap g) = z :=
    congrArg (FiniteTensor.tensor (V := C)).map
      (operationFactorsFunctor_map_restrict O.toCollection A (tupleRelabelTotalHom f R))
  have hg : u ≫ b = a ≫ z :=
    (operadSubstitutionInputs_naturality O A g).trans (congrArg (a ≫ ·) hz)
  have hi : z ≫ iQ = iP := profile_relabel_ι O.toCollection A (tupleRelabelTotalHom f R)
  change u ≫ (b ≫ iQ) = a ≫ iP
  calc
    u ≫ (b ≫ iQ) = (u ≫ b) ≫ iQ := (Category.assoc _ _ _).symm
    _ = (a ≫ z) ≫ iQ := congrArg (· ≫ iQ) hg
    _ = a ≫ (z ≫ iQ) := Category.assoc _ _ _
    _ = a ≫ iP := congrArg (a ≫ ·) hi



end CategoryTheory.Operad.Tensor
end
end
end source_ProfileRelabelSubstitution

/- Source proof segment: ProfileAssemblyRelabel -/
section source_ProfileAssemblyRelabel
/-!
# Original outer relabelling of the tensor assembly

The original outer coefficient/input bijection commutes with the
actual coefficient singleton unitor and the original source tensor
flattening. These are the source maps needed for operation equivariance.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The coefficient singleton-unitor map commutes with the
original complete outer/inner relabelling. -/
theorem coefficientTensorIso_relabel (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} {P Q : AnalyticIndex W d} (f : P ⟶ Q) (R : ProfileSlotTuple P) :
    slotRelabelFactorsHom O A f R ≫
        (coefficientTensorIso O A Q ((slotRelabelFunctor f).obj R)).hom =
      (coefficientTensorIso O A P R).hom ≫
        (FiniteFamily.map (FiniteTensor.tensor (V := C))).map
          ((nestedOperationFactorsFunctor O A).map
            (tupleRelabelShapeHom f ((slotProfileTupleFunctor P).obj R))) := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro i
    cases i <;> rfl
  · intro i
    cases i with
    | none =>
      have ho := tupleRelabelShapeHom_outer f ((slotProfileTupleFunctor P).obj R)
      have h := (FiniteTensor.singletonIso (V := C)).inv.naturality
        (O.map ((analyticToProfileFunctor W d).map f))
      change HEq
        (O.map ((analyticToProfileFunctor W d).map f) ≫
          (FiniteTensor.singletonIso (V := C)).inv.app (O.obj Q.toColoredProfile))
        ((FiniteTensor.singletonIso (V := C)).inv.app (O.obj P.toColoredProfile) ≫
          (FiniteTensor.tensor (V := C)).map
            ((FiniteFamily.singleton (C := C)).map
              (O.map (ColoredSubstitutionData.outerProfileMap
                (tupleRelabelShapeHom f ((slotProfileTupleFunctor P).obj R))))))
      rw [ho]
      exact heq_of_eq h
    | some i =>
      let h := tupleRelabelInnerHom f ((slotProfileTupleFunctor P).obj R) i
      let a := (operationSummandFunctor O A).map h
      change HEq (a ≫ 𝟙 _) (𝟙 _ ≫ a)
      exact heq_of_eq ((Category.comp_id a).trans (Category.id_comp a).symm)

/-- The complete actual tensor assembly commutes with the
original outer input bijection and every original inner profile. -/
@[reassoc]
theorem profileSubstitutionAssemblyMap_relabel (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} {P Q : AnalyticIndex W d} (f : P ⟶ Q) (R : ProfileSlotTuple P) :
    (slotRelabelTensorNatTrans O A f).app R ≫
        profileSubstitutionAssemblyMap O A Q ((slotRelabelFunctor f).obj R) =
      profileSubstitutionAssemblyMap O A P R ≫
        (algebraSubstitutionSourceFunctor O A).map
          (tupleRelabelShapeHom f ((slotProfileTupleFunctor P).obj R)) := by
  let g := tupleRelabelShapeHom f ((slotProfileTupleFunctor P).obj R)
  let a := slotRelabelFactorsHom O A f R
  let b := (coefficientTensorIso O A P R).hom
  let b' := (coefficientTensorIso O A Q ((slotRelabelFunctor f).obj R)).hom
  let h := (nestedOperationFactorsFunctor O A).map g
  let c := (FiniteTensor.flattenIso (V := C)).inv.app
    (nestedOperationFactors O A (tupleSubstitutionShape P ((slotProfileTupleFunctor P).obj R)))
  let c' := (FiniteTensor.flattenIso (V := C)).inv.app
    (nestedOperationFactors O A
      (tupleSubstitutionShape Q ((tupleRelabelFunctor f).obj ((slotProfileTupleFunctor P).obj R))))
  have hb : (FiniteTensor.tensor (V := C)).map a ≫ (FiniteTensor.tensor (V := C)).map b' =
      (FiniteTensor.tensor (V := C)).map b ≫
        (FiniteTensor.tensor (V := C)).map ((FiniteFamily.map FiniteTensor.tensor).map h) :=
    ((FiniteTensor.tensor (V := C)).map_comp a b').symm.trans
      ((congrArg (FiniteTensor.tensor (V := C)).map (coefficientTensorIso_relabel O A f R)).trans
        ((FiniteTensor.tensor (V := C)).map_comp b _))
  have hc : (FiniteTensor.tensor (V := C)).map ((FiniteFamily.map FiniteTensor.tensor).map h) ≫ c' =
      c ≫ (FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map h) :=
    (FiniteTensor.flattenIso (V := C)).inv.naturality h
  change (FiniteTensor.tensor (V := C)).map a ≫
      ((FiniteTensor.tensor (V := C)).map b' ≫ c') =
    ((FiniteTensor.tensor (V := C)).map b ≫ c) ≫
      (FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map h)
  exact composeTwoSquares
    ((FiniteTensor.tensor (V := C)).map a)
    ((FiniteTensor.tensor (V := C)).map ((FiniteFamily.map FiniteTensor.tensor).map h))
    ((FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map h))
    ((FiniteTensor.tensor (V := C)).map b) c
    ((FiniteTensor.tensor (V := C)).map b') c' hb hc



end CategoryTheory.Operad.Tensor
end
end
end source_ProfileAssemblyRelabel

/- Source proof segment: AssembledProfileRelabel -/
section source_AssembledProfileRelabel
/-!
# Original equivariance of assembled tensor substitution

The original outer input bijection, coefficient relabelling and
inner output transports commute with the full original substitution
cocone. This is the equivariance square to be descended by the
finite tensor colimit constructor.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The complete original assembled substitution leg is equivariant
under every actual outer profile input bijection and color transport. -/
@[reassoc]
theorem assembledProfileSubstitutionCocone_relabel (O : ColoredOperadObj W C) (A : W → C)
    {d : W} {P Q : AnalyticIndex W d} (f : P ⟶ Q) (R : ProfileSlotTuple P) :
    (slotRelabelTensorNatTrans O.toCollection A f).app R ≫
        (assembledProfileSubstitutionCocone O A Q).ι.app ((slotRelabelFunctor f).obj R) =
      (assembledProfileSubstitutionCocone O A P).ι.app R := by
  let s := ((slotProfileTupleFunctor P).obj R)
  let g := tupleRelabelShapeHom f s
  let h := (algebraSubstitutionSourceFunctor O.toCollection A).map g
  let a := profileSubstitutionAssemblyMap O.toCollection A P R
  let b := profileSubstitutionAssemblyMap O.toCollection A Q ((slotRelabelFunctor f).obj R)
  let iP := (profileSlotSubstitutionCocone O A P).ι.app R
  let iQ := (profileSlotSubstitutionCocone O A Q).ι.app ((slotRelabelFunctor f).obj R)
  have ha : (slotRelabelTensorNatTrans O.toCollection A f).app R ≫ b = a ≫ h :=
    profileSubstitutionAssemblyMap_relabel O.toCollection A f R
  have hi : h ≫ iQ = iP := profileSubstitutionCocone_relabel O A f s
  change (slotRelabelTensorNatTrans O.toCollection A f).app R ≫ (b ≫ iQ) = a ≫ iP
  have h' := composeTwoSquares
    ((slotRelabelTensorNatTrans O.toCollection A f).app R) h (𝟙 _)
    a iP b iQ ha (hi.trans (Category.comp_id _).symm)
  exact h'.trans (Category.comp_id _)



end CategoryTheory.Operad.Tensor
end
end
end source_AssembledProfileRelabel

/- Source proof segment: FreeOperation -/
section source_FreeOperation
/-!
# Actual free tensor-operadic operation maps

The original coefficient/input slot diagrams are colimiting from
source preservation in each tensor slot. The original operadic
substitution cocone is descended through that constructed colimit.
Its characteristic equation retains every original finite profile,
operation coefficient, input map and quotient injection.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits
open CategoryTheory.Limits.FiniteMultifunctor

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- The original slot tensor cocone is an actual colimit, produced
from source one-slot preservation and the original factor colimits. -/
def isColimitProfileSlotTensorCocone (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) : IsColimit (profileSlotTensorCocone O A P) := by
  letI : DecidableEq (Option P.inputs) := Classical.decEq _
  letI : DecidableEq (analyticFactorsIndex P).obj := Classical.decEq _
  letI : ∀ i : (analyticFactorsIndex P).obj, Category.{0} (profileSlotIndex P i) :=
    fun i => profileSlotCategory P i
  letI : ∀ i : (analyticFactorsIndex P).obj, EssentiallySmall.{us} (profileSlotIndex P i) :=
    fun i => profileSlotEssentiallySmall P i
  letI : Category.{0} (∀ i : (analyticFactorsIndex P).obj, profileSlotIndex P i) :=
    CategoryTheory.pi (fun i : (analyticFactorsIndex P).obj => profileSlotIndex P i)
  letI : Functor.PreservesColimitsInEachSlot.{0, w, v, w, v, us}
      (fixedIndexTensorFunctor (C := C) (analyticFactorsIndex P)) :=
    FiniteTensorPreservesColimitsInEachSlot.preserves (C := C) (analyticFactorsIndex P)
  let F := fixedIndexTensorFunctor (C := C) (analyticFactorsIndex P)
  let K := profileSlotDiagram O A P
  let c := profileSlotCocone O A P
  have hc := isColimitFiniteIndexCocone F (isColimitProfileSlotCocone O A P)
  have hgeneric : IsColimit (F.mapCocone (profileSlotFamilyCocone O A P)) := by
    change IsColimit (finiteIndexCocone F c)
    exact hc
  exact IsColimit.ofIsoColimit hgeneric (profileSlotCoconeIso O A P)

/-- The actual free operadic operation is the unique descent of
the original operad substitution through the constructed finite
tensor/profile colimit. -/
def freeOperation (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (analyticSummand O.toCollection (profileCoinvariants O.toCollection A)).obj P ⟶
      profileCoinvariants O.toCollection A d :=
  (isColimitProfileSlotTensorCocone O.toCollection A P).desc
    (assembledProfileSubstitutionCocone O A P)

/-- Every actual coefficient/input tuple evaluates by the original
operadic substitution followed by the original profile injection. -/
@[reassoc]
theorem freeOperation_ι (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (profileSlotTensorCocone O.toCollection A P).ι.app Q ≫ freeOperation O A P =
      (assembledProfileSubstitutionCocone O A P).ι.app Q :=
  (isColimitProfileSlotTensorCocone O.toCollection A P).fac _ Q

/-- The original coefficient/input tuple maps determine maps from
the actual free-operation domain, at every finite arity. -/
theorem freeOperation_hom_ext (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) {X : C}
    {f g : (analyticSummand O (profileCoinvariants O A)).obj P ⟶ X}
    (h : ∀ Q : ProfileSlotTuple P,
      (profileSlotTensorCocone O A P).ι.app Q ≫ f =
        (profileSlotTensorCocone O A P).ι.app Q ≫ g) : f = g :=
  (isColimitProfileSlotTensorCocone O A P).hom_ext h





end CategoryTheory.Operad.Tensor
end
end
end source_FreeOperation

/- Source proof segment: RawSubstitutionColimit -/
section source_RawSubstitutionColimit
/-!
# Actual colimit cocones on original raw operadic substitution sources
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The original profile slot colimit transported through the
actual singleton-coefficient and flattening assembly isomorphism. -/
def rawSubstitutionCocone (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    Cocone (slotProfileTupleFunctor P ⋙ tupleSubstitutionSource O A P) :=
  (Cocone.precompose (profileSlotAssemblyIso O A P).inv).obj (profileSlotTensorCocone O A P)

/-- Its point is the original profile tensor with free profile
coinvariants in every original input slot. -/
theorem rawSubstitutionCocone_pt (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (rawSubstitutionCocone O A P).pt =
      (analyticSummand O (profileCoinvariants O A)).obj P := rfl

/-- Every raw source injection is the actual inverse assembly
and the actual coefficient/input slot tensor injection. -/
theorem rawSubstitutionCocone_ι (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (rawSubstitutionCocone O A P).ι.app Q =
      (profileSlotAssemblyIso O A P).inv.app Q ≫
        (profileSlotTensorCocone O A P).ι.app Q := rfl

variable [Small.{us} W] [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- The original raw source cocone is actually colimiting,
constructed from source finite tensor preservation in each slot. -/
def isColimitRawSubstitutionCocone (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) : IsColimit (rawSubstitutionCocone O A P) :=
  (IsColimit.precomposeInvEquiv (profileSlotAssemblyIso O A P) (profileSlotTensorCocone O A P)).symm
    (isColimitProfileSlotTensorCocone O A P)

/-- Actual free operation evaluation on every original raw
substitution source is the original coefficient substitution/injection. -/
@[reassoc]
theorem rawSubstitutionCocone_freeOperation (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (rawSubstitutionCocone O.toCollection A P).ι.app Q ≫ freeOperation O A P =
      operadSubstitutionInputs O A
        (tupleSubstitutionShape P ((slotProfileTupleFunctor P).obj Q)) ≫
        profileι O.toCollection A ((tupleTotalFunctor P).obj ((slotProfileTupleFunctor
          P).obj Q)) := by
  let e := (profileSlotAssemblyIso O.toCollection A P).app Q
  let i := (profileSlotTensorCocone O.toCollection A P).ι.app Q
  let f := freeOperation O A P
  let g := (profileSlotSubstitutionCocone O A P).ι.app Q
  have h : i ≫ f = e.hom ≫ g := freeOperation_ι O A P Q
  change (e.inv ≫ i) ≫ f = g
  exact (Category.assoc e.inv i f).trans (e.inv_comp_eq.mpr h)




end CategoryTheory.Operad.Tensor
end
end
end source_RawSubstitutionColimit

/- Source proof segment: NestedRawSubstitutionDiagram -/
section source_NestedRawSubstitutionDiagram
/-!
# Original three-level raw substitution diagrams

Each original inner coefficient/input tensor has its actual raw
source colimit. The outer coefficient is retained as its singleton
index; the original finite outer tensor combines these diagrams.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u}

/-- Each original outer input chooses all original innermost
profiles through its original slot tuple index. -/
def nestedRawSlotIndex (s : ColoredSubstitutionData W) : Option s.inner.index → Type (max 1 u)
  | none => CoefficientIndex
  | some i => ProfileSlotTuple (profileInputs (s.inner.obj i))

instance nestedRawSlotCategory (s : ColoredSubstitutionData W) (i : Option s.inner.index) :
    Category.{0} (nestedRawSlotIndex s i) :=
  match i with
  | none => coefficientIndexCategory
  | some i => inferInstanceAs (Category.{0} (ProfileSlotTuple (profileInputs (s.inner.obj i))))

instance nestedRawSlotCategories (s : ColoredSubstitutionData W) :
    ∀ i : Option s.inner.index, Category.{0} (nestedRawSlotIndex s i) := nestedRawSlotCategory s

instance nestedRawSlotAnalyticCategory (s : ColoredSubstitutionData W)
    (i : (analyticFactorsIndex (profileInputs s.outerProfile)).obj) :
    Category.{0} (nestedRawSlotIndex s i) := nestedRawSlotCategory s i

instance nestedRawSlotEssentiallySmall [Small.{us} W] (s : ColoredSubstitutionData W)
    (i : Option s.inner.index) : EssentiallySmall.{us} (nestedRawSlotIndex s i) := by
  cases i with
  | none => exact coefficientIndexEssentiallySmall
  | some i =>
    change EssentiallySmall.{us} (ProfileSlotTuple (profileInputs (s.inner.obj i)))
    let : ∀ j : Option (s.inner.obj i).inputs,
        Category.{0} (profileSlotIndex (profileInputs (s.inner.obj i)) j) :=
      profileSlotCategory (profileInputs (s.inner.obj i))
    let : ∀ j : Option (s.inner.obj i).inputs,
        EssentiallySmall.{us} (profileSlotIndex (profileInputs (s.inner.obj i)) j) :=
      profileSlotEssentiallySmall (profileInputs (s.inner.obj i))
    exact piEssentiallySmall.{0, max 1 u, 0, us}
      (profileSlotIndex (profileInputs (s.inner.obj i)))

/-- All original innermost profile tuples at every outer input. -/
abbrev NestedRawSlotTuple (s : ColoredSubstitutionData W) :=
  ∀ i : Option s.inner.index, nestedRawSlotIndex s i

variable {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original outer coefficient and complete raw inner
substitution tensor diagrams, before any original O.subst is applied. -/
def nestedRawSlotDiagram (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) : (i : Option s.inner.index) → nestedRawSlotIndex s i ⥤ C
  | none => (Functor.const CoefficientIndex).obj (O.obj s.outerProfile)
  | some i => slotProfileTupleFunctor (profileInputs (s.inner.obj i)) ⋙
      tupleSubstitutionSource O A (profileInputs (s.inner.obj i))

variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The actual original raw source cocones at every inner profile,
and the unchanged original coefficient cocone at the root. -/
def nestedRawSlotCocone (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) : (i : Option s.inner.index) →
      Cocone (nestedRawSlotDiagram O A s i)
  | none => constCocone CoefficientIndex (O.obj s.outerProfile)
  | some i => rawSubstitutionCocone O A (profileInputs (s.inner.obj i))

/-- Tensor the unchanged outer slot index of all original raw
source factor diagrams. -/
def nestedRawTensorDiagram (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) : NestedRawSlotTuple s ⥤ C :=
  FiniteMultifunctor.finiteIndexDiagram
    (fixedIndexTensorFunctor (C := C) (analyticFactorsIndex (profileInputs s.outerProfile)))
    (nestedRawSlotDiagram O A s)

/-- The original finite tensor of actual inner raw colimit points. -/
def nestedRawTensorCocone (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) : Cocone (nestedRawTensorDiagram O A s) := by
  letI : ∀ i : (analyticFactorsIndex (profileInputs s.outerProfile)).obj,
      Category.{0} (nestedRawSlotIndex s i) := nestedRawSlotCategory s
  exact FiniteMultifunctor.finiteIndexCocone
    (fixedIndexTensorFunctor (C := C) (analyticFactorsIndex (profileInputs s.outerProfile)))
    (nestedRawSlotCocone O A s)

variable [Small.{us} W] [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- Each original nested source slot is actually colimiting from
the source finite tensor preservation hypothesis. -/
def isColimitNestedRawSlotCocone (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) : (i : Option s.inner.index) →
      IsColimit (nestedRawSlotCocone O A s i)
  | none => isColimitConstCocone CoefficientIndex (O.obj s.outerProfile)
  | some i => isColimitRawSubstitutionCocone O A (profileInputs (s.inner.obj i))

/-- The complete original outer tensor of inner raw source
cocones is actually colimiting, with no joint-colimit premise. -/
def isColimitNestedRawTensorCocone (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) : IsColimit (nestedRawTensorCocone O A s) := by
  letI : DecidableEq (analyticFactorsIndex (profileInputs s.outerProfile)).obj := Classical.decEq _
  letI : DecidableEq (Option s.inner.index) := Classical.decEq _
  letI : ∀ i : (analyticFactorsIndex (profileInputs s.outerProfile)).obj,
      Category.{0} (nestedRawSlotIndex s i) := nestedRawSlotCategory s
  letI : ∀ i : (analyticFactorsIndex (profileInputs s.outerProfile)).obj,
      EssentiallySmall.{us} (nestedRawSlotIndex s i) := nestedRawSlotEssentiallySmall s
  letI : Functor.PreservesColimitsInEachSlot.{0, w, v, w, v, us}
      (fixedIndexTensorFunctor (C := C) (analyticFactorsIndex (profileInputs s.outerProfile))) :=
    FiniteTensorPreservesColimitsInEachSlot.preserves (C := C) _
  exact FiniteMultifunctor.isColimitFiniteIndexCocone _ (isColimitNestedRawSlotCocone O A s)



end CategoryTheory.Operad.Tensor
end
end
end source_NestedRawSubstitutionDiagram

/- Source proof segment: NestedRawPoint -/
section source_NestedRawPoint
/-!
# Actual original nested raw source colimit point
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The unchanged outer coefficient and inner raw colimit points
identify with tensors of the original inner-operation factors. -/
def nestedRawPointFactorsIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    (FiniteFamily.fixedIndexFunctor (analyticFactorsIndex (profileInputs s.outerProfile))).obj
        (fun i => (nestedRawSlotCocone O A s i).pt) ≅
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        (nestedOperationFactors O (profileCoinvariants O A) s) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option s.inner.index))
    (fun i => match i with
      | none => ((FiniteTensor.singletonIso (V := C)).app (O.obj s.outerProfile)).symm
      | some _ => Iso.refl _)

/-- The actual finite tensor colimit point is the original raw
two-level substitution source with profile coinvariants as leaves. -/
def nestedRawPointIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    (nestedRawTensorCocone O A s).pt ≅
      algebraSubstitutionSource O (profileCoinvariants O A) s :=
  (FiniteTensor.tensor (V := C)).mapIso (nestedRawPointFactorsIso O A s) ≪≫
    ((FiniteTensor.flattenIso (V := C)).app (nestedOperationFactors O (profileCoinvariants O
      A) s)).symm



end CategoryTheory.Operad.Tensor
end
end
end source_NestedRawPoint

/- Source proof segment: OperadUnitTensorLaws -/
section source_OperadUnitTensorLaws
/-!
# Original operadic unit laws with retained tensor leaves

The original right and left operadic unit equations remain equalities
after tensoring with every fixed finite family of original leaf inputs.
No free-algebra or monad unit law is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C]

/-- Prepend one original coefficient to a fixed family of original
leaf inputs, with every retained input map the identity. -/
def coefficientLeafFamilyFunctor (L : FiniteFamily C) : C ⥤ FiniteFamily C where
  obj X :=
    { index := FintypeCat.of (Option L.index)
      obj i := match i with
        | none => X
        | some i => L.obj i }
  map f :=
    { equiv := Equiv.refl (Option L.index)
      hom i := match i with
        | none => f
        | some i => 𝟙 (L.obj i) }
  map_id X := by
    apply FiniteFamily.Hom_ext
    · rfl
    · intro i
      cases i <;> exact HEq.rfl
  map_comp f g := by
    apply FiniteFamily.Hom_ext
    · rfl
    · intro i
      cases i with
      | none => exact HEq.rfl
      | some i => exact heq_of_eq (Category.id_comp _).symm

variable [FiniteTensor C]

/-- Tensor a varying original coefficient with a fixed original
leaf-input family, retaining their actual finite tensor indices. -/
def coefficientLeafTensorFunctor (L : FiniteFamily C) : C ⥤ C :=
  coefficientLeafFamilyFunctor L ⋙ FiniteTensor.tensor

/-- The source right operadic unit equation remains the identity
on the original coefficient tensor every retained leaf input. -/
theorem rightUnit_tensor_leaves (O : ColoredOperadObj W C) (P : ColoredProfile W)
    (L : FiniteFamily C) :
    (coefficientLeafTensorFunctor L).map
      (ColoredOperadObj.rightUnitInsert O.toCollection O.unit P ≫
        O.subst.app (ColoredSubstitutionData.rightUnit P) ≫
        O.toCollection.map (ColoredSubstitutionData.rightUnitTotalHom P)) =
      𝟙 ((coefficientLeafTensorFunctor L).obj (O.toCollection.obj P)) :=
  (congrArg (coefficientLeafTensorFunctor L).map (O.right_unit P)).trans
    ((coefficientLeafTensorFunctor L).map_id _)

/-- The source left operadic unit equation remains the identity
on the original coefficient tensor every retained leaf input. -/
theorem leftUnit_tensor_leaves (O : ColoredOperadObj W C) (P : ColoredProfile W)
    (L : FiniteFamily C) :
    (coefficientLeafTensorFunctor L).map
      (ColoredOperadObj.leftUnitInsert O.toCollection O.unit P ≫
        O.subst.app (ColoredSubstitutionData.leftUnit P) ≫
        O.toCollection.map (ColoredSubstitutionData.leftUnitTotalHom P)) =
      𝟙 ((coefficientLeafTensorFunctor L).obj (O.toCollection.obj P)) :=
  (congrArg (coefficientLeafTensorFunctor L).map (O.left_unit P)).trans
    ((coefficientLeafTensorFunctor L).map_id _)




end CategoryTheory.Operad.Tensor
end
end
end source_OperadUnitTensorLaws

/- Source proof segment: CoefficientLeaves -/
section source_CoefficientLeaves
/-!
# Original coefficient and leaf tensor normalization

All original coefficients and leaf objects occur in one finite
family. The actual finite tensor flattening and singleton unitors
identify it with the tensor of its coefficient block and original
leaf objects. Original coefficient maps act only in that block.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type w} [Category.{v} C]

/-- A complete original coefficient block and singleton blocks for
each retained original leaf object. -/
def coefficientLeavesNested (K L : FiniteFamily C) : FiniteFamily (FiniteFamily C) where
  index := FintypeCat.of (Option L.index)
  obj i := match i with
    | none => K
    | some i => (FiniteFamily.singleton (C := C)).obj (L.obj i)

variable [FiniteTensor C]

/-- The original coefficient block is kept, and each original leaf
singleton tensor is collapsed by its actual unitor. -/
def coefficientLeavesCollapse (K L : FiniteFamily C) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (coefficientLeavesNested K L) ⟶
      (coefficientLeafFamilyFunctor L).obj ((FiniteTensor.tensor (V := C)).obj K) where
  equiv := Equiv.refl (Option L.index)
  hom i := match i with
    | none => 𝟙 _
    | some i => (FiniteTensor.singletonIso (V := C)).hom.app (L.obj i)

/-- Apply an original coefficient map after evaluating the original
coefficient tensor block, retaining original leaf unitors. -/
def coefficientLeavesMap (K L : FiniteFamily C) {Y : C}
    (f : (FiniteTensor.tensor (V := C)).obj K ⟶ Y) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (coefficientLeavesNested K L) ⟶
      (coefficientLeafFamilyFunctor L).obj Y where
  equiv := Equiv.refl (Option L.index)
  hom i := match i with
    | none => f
    | some i => (FiniteTensor.singletonIso (V := C)).hom.app (L.obj i)

theorem coefficientLeavesCollapse_map (K L : FiniteFamily C) {Y : C}
    (f : (FiniteTensor.tensor (V := C)).obj K ⟶ Y) :
    coefficientLeavesCollapse K L ≫ (coefficientLeafFamilyFunctor L).map f =
      coefficientLeavesMap K L f := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none => exact heq_of_eq (Category.id_comp f)
    | some i =>
      exact heq_of_eq (Category.comp_id ((FiniteTensor.singletonIso (V := C)).hom.app (L.obj i)))

/-- Normalize the complete original coefficients and leaves using
the actual flattening map and original singleton leaf unitors. -/
def coefficientLeavesNormalization (K L : FiniteFamily C) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.flatten (C := C)).obj (coefficientLeavesNested K L)) ⟶
      (coefficientLeafTensorFunctor L).obj ((FiniteTensor.tensor (V := C)).obj K) :=
  (FiniteTensor.flattenIso (V := C)).hom.app (coefficientLeavesNested K L) ≫
    (FiniteTensor.tensor (V := C)).map (coefficientLeavesCollapse K L)

/-- An original coefficient map after normalization is precisely
the original coefficient map in its block and original leaf unitors. -/
@[reassoc]
theorem coefficientLeavesNormalization_map (K L : FiniteFamily C) {Y : C}
    (f : (FiniteTensor.tensor (V := C)).obj K ⟶ Y) :
    coefficientLeavesNormalization K L ≫ (coefficientLeafTensorFunctor L).map f =
      (FiniteTensor.flattenIso (V := C)).hom.app (coefficientLeavesNested K L) ≫
        (FiniteTensor.tensor (V := C)).map (coefficientLeavesMap K L f) := by
  let a := (FiniteTensor.flattenIso (V := C)).hom.app (coefficientLeavesNested K L)
  let b := coefficientLeavesCollapse K L
  let g := (coefficientLeafFamilyFunctor L).map f
  have hg : b ≫ g = coefficientLeavesMap K L f := coefficientLeavesCollapse_map K L f
  change (a ≫ (FiniteTensor.tensor (V := C)).map b) ≫ (FiniteTensor.tensor (V := C)).map g = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (a ≫ ·) ((FiniteTensor.tensor (V := C)).map_comp b g).symm).trans
      (congrArg (fun m => a ≫ (FiniteTensor.tensor (V := C)).map m) hg))

variable {W : Type u}

/-- The original leaf-input family of a full profile, retaining its
actual finite input type and input-color function. -/
def profileLeafFamily (A : W → C) (P : ColoredProfile W) : FiniteFamily C where
  index := P.inputs
  obj i := A (P.inputColor i)

omit [FiniteTensor C] in
theorem profileLeafFamily_eq_input (A : W → C) (P : ColoredProfile W) :
    profileLeafFamily A P = (analyticInputFamily A).obj (profileInputs P) :=
  rfl



end CategoryTheory.Operad.Tensor
end
end
end source_CoefficientLeaves

/- Source proof segment: TensorMapSquares -/
section source_TensorMapSquares
@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe u v u' v'

/-- A factor square in the source category gives the corresponding
tensor square after an original regrouping map. -/
theorem functorMapFactorSquare {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D] (F : C ⥤ D)
    {A B P Q : C} {X Y : D}
    (a : X ⟶ F.obj A) (m : X ⟶ Y) (d : Y ⟶ F.obj B)
    (g : A ⟶ B) (b : A ⟶ P) (c : B ⟶ Q) (t : P ⟶ Q)
    (hn : m ≫ d = a ≫ F.map g) (hc : g ≫ c = b ≫ t) :
    a ≫ F.map b ≫ F.map t = m ≫ d ≫ F.map c := by
  rw [← F.map_comp, ← hc, F.map_comp, ← Category.assoc, ← hn, Category.assoc]

/-- Cancel an actual inverse regrouping before a normalized map. -/
theorem cancelNormalizedRegrouping {C : Type u} [Category.{v} C]
    {X Y Z P Q : C} (p : X ⟶ Y) (i : Y ⟶ Z) (g : Z ⟶ Y)
    (a : Y ⟶ P) (c : P ⟶ Q) (r : Z ⟶ Q)
    (hi : i ≫ g = 𝟙 Y) (hr : r = g ≫ a ≫ c) :
    (p ≫ i) ≫ r = p ≫ a ≫ c := by
  rw [hr, Category.assoc, ← Category.assoc i g, hi, Category.id_comp]

end CategoryTheory.Operad.Tensor
end
end source_TensorMapSquares

/- Source proof segment: CoefficientLeavesNaturality -/
section source_CoefficientLeavesNaturality
/-!
# Coefficient-leaf normalization isomorphisms and original map naturality
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- An original coefficient map and an original finite leaf map. -/
def coefficientLeafMap {X Y : C} (f : X ⟶ Y)
    {L M : FiniteFamily C} (l : L ⟶ M) :
    (coefficientLeafFamilyFunctor L).obj X ⟶ (coefficientLeafFamilyFunctor M).obj Y where
  equiv := Equiv.optionCongr l.equiv
  hom i := match i with
    | none => f
    | some i => l.hom i

/-- The original maps on the nested coefficient block and singleton leaves. -/
def coefficientLeavesNestedMap {K N L M : FiniteFamily C} (k : K ⟶ N) (l : L ⟶ M) :
    coefficientLeavesNested K L ⟶ coefficientLeavesNested N M where
  equiv := Equiv.optionCongr l.equiv
  hom i := match i with
    | none => k
    | some i => (FiniteFamily.singleton (C := C)).map (l.hom i)

variable [FiniteTensor C]

/-- Collapse is invertible, using the original singleton unitor on every leaf. -/
def coefficientLeavesCollapseIso (K L : FiniteFamily C) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (coefficientLeavesNested K L) ≅
      (coefficientLeafFamilyFunctor L).obj ((FiniteTensor.tensor (V := C)).obj K) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option L.index))
    (fun i => match i with
      | none => Iso.refl _
      | some i => (FiniteTensor.singletonIso (V := C)).app (L.obj i))

theorem coefficientLeavesCollapseIso_hom (K L : FiniteFamily C) :
    (coefficientLeavesCollapseIso K L).hom = coefficientLeavesCollapse K L := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i <;> rfl

/-- The source factor normalization is an actual isomorphism. -/
def coefficientLeavesNormalizationIso (K L : FiniteFamily C) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.flatten (C := C)).obj (coefficientLeavesNested K L)) ≅
      (coefficientLeafTensorFunctor L).obj ((FiniteTensor.tensor (V := C)).obj K) :=
  (FiniteTensor.flattenIso (V := C)).app (coefficientLeavesNested K L) ≪≫
    (FiniteTensor.tensor (V := C)).mapIso (coefficientLeavesCollapseIso K L)

theorem coefficientLeavesNormalizationIso_hom (K L : FiniteFamily C) :
    (coefficientLeavesNormalizationIso K L).hom = coefficientLeavesNormalization K L := by
  change (FiniteTensor.flattenIso (V := C)).hom.app _ ≫
    (FiniteTensor.tensor (V := C)).map (coefficientLeavesCollapseIso K L).hom = _
  rw [coefficientLeavesCollapseIso_hom]
  rfl

/-- The coefficient/leaf collapse square retains both original maps,
including the original leaf-index bijection. -/
theorem coefficientLeavesCollapse_naturality {K N L M : FiniteFamily C}
    (k : K ⟶ N) (l : L ⟶ M) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (coefficientLeavesNestedMap k l) ≫
        coefficientLeavesCollapse N M =
      coefficientLeavesCollapse K L ≫
        coefficientLeafMap ((FiniteTensor.tensor (V := C)).map k) l := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      change HEq ((FiniteTensor.tensor (V := C)).map k ≫ 𝟙 _)
        (𝟙 _ ≫ (FiniteTensor.tensor (V := C)).map k)
      exact heq_of_eq ((Category.comp_id _).trans (Category.id_comp _).symm)
    | some i =>
      exact heq_of_eq ((FiniteTensor.singletonIso (V := C)).hom.naturality (l.hom i))

/-- Normalize an original coefficient/leaf map either before or after
applying it: the displayed original permutations and component maps agree. -/
@[reassoc]
theorem coefficientLeavesNormalization_naturality {K N L M : FiniteFamily C}
    (k : K ⟶ N) (l : L ⟶ M) :
    (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map (coefficientLeavesNestedMap k l)) ≫
      coefficientLeavesNormalization N M =
    coefficientLeavesNormalization K L ≫
      (FiniteTensor.tensor (V := C)).map
        (coefficientLeafMap ((FiniteTensor.tensor (V := C)).map k) l) := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let h := coefficientLeavesNestedMap k l
  let a := (FiniteTensor.flattenIso (V := C)).hom.app (coefficientLeavesNested K L)
  let d := (FiniteTensor.flattenIso (V := C)).hom.app (coefficientLeavesNested N M)
  let b := coefficientLeavesCollapse K L
  let c := coefficientLeavesCollapse N M
  let t := coefficientLeafMap (T.map k) l
  have hn := (FiniteTensor.flattenIso (V := C)).hom.naturality h
  have hc := coefficientLeavesCollapse_naturality k l
  change T.map (F.map h) ≫ d = a ≫ T.map ((FiniteFamily.map T).map h) at hn
  change (FiniteFamily.map T).map h ≫ c = b ≫ t at hc
  change T.map (F.map h) ≫ (d ≫ T.map c) = (a ≫ T.map b) ≫ T.map t
  exact (functorMapFactorSquare T a (T.map (F.map h)) d
      ((FiniteFamily.map T).map h) b c t hn hc).symm.trans (Category.assoc _ _ _).symm



end CategoryTheory.Operad.Tensor
end
end
end source_CoefficientLeavesNaturality

/- Source proof segment: EmptyLeafCoefficients -/
section source_EmptyLeafCoefficients
/-!
# Original coefficient tensors with an empty leaf family
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

/-- Identify the unique empty coefficient slot with the singleton unit index. -/
def optionEmptyUnitEquiv : Option Empty ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := none
  left_inv i := by cases i with
    | none => rfl
    | some e => cases e
  right_inv i := by cases i; rfl

variable {C : Type u} [Category.{v} C]

/-- The empty original leaf family leaves only the original coefficient
singleton, with the displayed original empty-index bijection. -/
def emptyLeafFamilyIso (X : C) :
    (coefficientLeafFamilyFunctor (FiniteFamily.empty : FiniteFamily C)).obj X ≅
      (FiniteFamily.singleton (C := C)).obj X :=
  FiniteFamily.isoOfComponents optionEmptyUnitEquiv
    (fun i => match i with
      | none => Iso.refl X
      | some e => e.elim)

theorem emptyLeafFamilyIso_naturality {X Y : C} (f : X ⟶ Y) :
    (coefficientLeafFamilyFunctor (FiniteFamily.empty : FiniteFamily C)).map f ≫
        (emptyLeafFamilyIso Y).hom =
      (emptyLeafFamilyIso X).hom ≫ (FiniteFamily.singleton (C := C)).map f := by
  apply FiniteFamily.Hom_ext
  · ext i
    cases i with
    | none => rfl
    | some e => cases e
  · intro i
    cases i with
    | none => exact heq_of_eq ((Category.comp_id f).trans (Category.id_comp f).symm)
    | some e => cases e

/-- The full empty-leaf family identification is natural in the
original coefficient map. -/
def emptyLeafFamilyNatIso :
    coefficientLeafFamilyFunctor (FiniteFamily.empty : FiniteFamily C) ≅ FiniteFamily.singleton :=
  NatIso.ofComponents emptyLeafFamilyIso (by
    intro X Y f
    exact emptyLeafFamilyIso_naturality f)

variable [FiniteTensor C]

/-- Tensoring a coefficient with an empty original leaf family is
the original coefficient, by its actual singleton tensor unitor. -/
def emptyLeafTensorNatIso :
    coefficientLeafTensorFunctor (FiniteFamily.empty : FiniteFamily C) ≅ 𝟭 C :=
  Functor.isoWhiskerRight emptyLeafFamilyNatIso (FiniteTensor.tensor (V := C)) ≪≫
    FiniteTensor.singletonIso

/-- The tensor of a coefficient with no input leaves is the original coefficient object. -/
def emptyLeafTensorIso (X : C) :
    (coefficientLeafTensorFunctor (FiniteFamily.empty : FiniteFamily C)).obj X ≅ X :=
  emptyLeafTensorNatIso.app X

theorem emptyLeafTensorIso_hom (X : C) :
    (emptyLeafTensorIso X).hom =
      (FiniteTensor.tensor (V := C)).map (emptyLeafFamilyIso X).hom ≫
        (FiniteTensor.singletonIso (V := C)).hom.app X := by
  rfl

omit [FiniteTensor C] in
/-- Empty leaves only change the original nested coefficient block
by its displayed singleton-index identification. -/
def emptyLeafNestedIso (K : FiniteFamily C) :
    coefficientLeavesNested K (FiniteFamily.empty : FiniteFamily C) ≅
      (FiniteFamily.singleton (C := FiniteFamily C)).obj K :=
  FiniteFamily.isoOfComponents optionEmptyUnitEquiv
    (fun i => match i with
      | none => Iso.refl K
      | some e => e.elim)

omit [FiniteTensor C] in
/-- Flatten a coefficient family with no input leaves to the original coefficient family. -/
def emptyLeafRawIso (K : FiniteFamily C) :
    (FiniteFamily.flatten (C := C)).obj
        (coefficientLeavesNested K (FiniteFamily.empty : FiniteFamily C)) ≅ K :=
  (FiniteFamily.flatten (C := C)).mapIso (emptyLeafNestedIso K) ≪≫
    FiniteFamily.singletonFlattenIso.app K

theorem emptyLeafCollapse_square (K : FiniteFamily C) :
    coefficientLeavesCollapse K (FiniteFamily.empty : FiniteFamily C) ≫
        (emptyLeafFamilyIso ((FiniteTensor.tensor (V := C)).obj K)).hom =
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (emptyLeafNestedIso K).hom := by
  apply FiniteFamily.Hom_ext
  · ext i
    cases i with
    | none => rfl
    | some e => cases e
  · intro i
    cases i with
    | none =>
      change HEq (𝟙 _ ≫ 𝟙 _) ((FiniteTensor.tensor (V := C)).map (𝟙 K))
      exact heq_of_eq ((Category.id_comp _).trans ((FiniteTensor.tensor (V := C)).map_id K).symm)
    | some e => cases e




end CategoryTheory.Operad.Tensor
end
end
end source_EmptyLeafCoefficients

/- Source proof segment: CoefficientLeavesAssociativityData -/
section source_CoefficientLeavesAssociativityData
/-!
# Original triple-nested coefficient blocks with retained leaf singletons
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The actual coefficient grouping occupies the coefficient block,
and each original leaf is retained as two singleton levels. -/
def coefficientLeavesTriple (N : FiniteFamily (FiniteFamily C)) (L : FiniteFamily C) :
    FiniteFamily (FiniteFamily (FiniteFamily C)) where
  index := FintypeCat.of (Option L.index)
  obj i := match i with
    | none => N
    | some i => (FiniteFamily.singleton (C := FiniteFamily C)).obj
        ((FiniteFamily.singleton (C := C)).obj (L.obj i))

/-- Flattening within the coefficient block preserves its original
grouping, and collapses only the extra singleton index on each leaf. -/
def coefficientLeavesTripleFlattenIso (N : FiniteFamily (FiniteFamily C))
    (L : FiniteFamily C) :
    (FiniteFamily.map (FiniteFamily.flatten (C := C))).obj (coefficientLeavesTriple N L) ≅
      coefficientLeavesNested ((FiniteFamily.flatten (C := C)).obj N) L :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option L.index))
    (fun i => match i with
      | none => Iso.refl _
      | some i => FiniteFamily.singletonFlattenIso.app
          ((FiniteFamily.singleton (C := C)).obj (L.obj i)))

variable [FiniteTensor C]

/-- After evaluating the original lowest blocks, collapse the
original singleton leaf tensor inside each retained leaf singleton. -/
def coefficientLeavesTripleTensorMap (N : FiniteFamily (FiniteFamily C))
    (L : FiniteFamily C) :
    (FiniteFamily.map (FiniteFamily.map (FiniteTensor.tensor (V := C)))).obj
        (coefficientLeavesTriple N L) ⟶
      coefficientLeavesNested ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj N) L where
  equiv := Equiv.refl (Option L.index)
  hom i := match i with
    | none => 𝟙 _
    | some i => (FiniteFamily.singleton (C := C)).map
        ((FiniteTensor.singletonIso (V := C)).hom.app (L.obj i))

/-- The actual complete collapse after the lowest coefficient
blocks have been evaluated. -/
def coefficientLeavesTripleCollapseMap (N : FiniteFamily (FiniteFamily C))
    (L : FiniteFamily C) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        ((FiniteFamily.map (FiniteFamily.map (FiniteTensor.tensor (V := C)))).obj
          (coefficientLeavesTriple N L)) ⟶
      (coefficientLeafFamilyFunctor L).obj
        ((FiniteTensor.tensor (V := C)).obj ((FiniteFamily.map (FiniteTensor.tensor (V :=
          C))).obj N)) :=
  (FiniteFamily.map (FiniteTensor.tensor (V := C))).map
      (coefficientLeavesTripleTensorMap N L) ≫
    coefficientLeavesCollapse ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj N) L

/-- Two ways of collapsing an original leaf double singleton agree
by the actual finite tensor singleton-flatten law. -/
theorem coefficientLeavesTriple_leaf (X : C) :
    (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.singleton (C := FiniteFamily C)).obj
          ((FiniteFamily.singleton (C := C)).obj X)) ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.singleton (C := C)).map ((FiniteTensor.singletonIso (V := C)).hom.app X)) ≫
      (FiniteTensor.singletonIso (V := C)).hom.app X =
    (FiniteTensor.tensor (V := C)).map
        (FiniteFamily.singletonFlattenIso.hom.app ((FiniteFamily.singleton (C := C)).obj X)) ≫
      (FiniteTensor.singletonIso (V := C)).hom.app X := by
  let a := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.singleton (C := FiniteFamily C)).obj
      ((FiniteFamily.singleton (C := C)).obj X))
  let e := (FiniteTensor.singletonIso (V := C)).hom.app X
  let b := (FiniteTensor.tensor (V := C)).map ((FiniteFamily.singleton (C := C)).map e)
  let d := (FiniteTensor.singletonIso (V := C)).hom.app
    ((FiniteTensor.tensor (V := C)).obj ((FiniteFamily.singleton (C := C)).obj X))
  have hn : b ≫ e = d ≫ e := (FiniteTensor.singletonIso (V := C)).hom.naturality e
  have hu := singletonFlattenLaw_app ((FiniteFamily.singleton (C := C)).obj X)
  change (FiniteTensor.tensor (V := C)).map
    (FiniteFamily.singletonFlattenIso.hom.app ((FiniteFamily.singleton (C := C)).obj X)) = a
      ≫ d at hu
  change a ≫ b ≫ e = _
  exact (congrArg (a ≫ ·) hn).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ e) hu.symm))

/-- The triple coefficient/leaf collapse agrees with coefficient
flattening while keeping the original leaf unitors. -/
theorem coefficientLeavesTripleCollapse_square (N : FiniteFamily (FiniteFamily C))
    (L : FiniteFamily C) :
    ((FiniteFamily.mapIso (FiniteTensor.flattenIso (V := C))).hom.app
        (coefficientLeavesTriple N L)) ≫ coefficientLeavesTripleCollapseMap N L =
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map
        (coefficientLeavesTripleFlattenIso N L).hom ≫
      coefficientLeavesMap ((FiniteFamily.flatten (C := C)).obj N) L
        ((FiniteTensor.flattenIso (V := C)).hom.app N) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      let f : (FiniteTensor.tensor (V := C)).obj ((FiniteFamily.flatten (C := C)).obj N) ⟶
        (FiniteTensor.tensor (V := C)).obj ((FiniteFamily.map (FiniteTensor.tensor (V :=
          C))).obj N) :=
          (FiniteTensor.flattenIso (V := C)).hom.app N
      change HEq (f ≫ (FiniteTensor.tensor (V := C)).map (𝟙 _) ≫ 𝟙 _)
        ((FiniteTensor.tensor (V := C)).map (𝟙 _) ≫ f)
      have hl : f ≫ (FiniteTensor.tensor (V := C)).map (𝟙 _) ≫ 𝟙 _ = f :=
        (congrArg (fun h => f ≫ h ≫ 𝟙 _) ((FiniteTensor.tensor (V := C)).map_id _)).trans
          ((congrArg (f ≫ ·) (Category.comp_id _)).trans (Category.comp_id f))
      have hr : (FiniteTensor.tensor (V := C)).map (𝟙 _) ≫ f = f :=
        (congrArg (· ≫ f) ((FiniteTensor.tensor (V := C)).map_id _)).trans (Category.id_comp f)
      exact heq_of_eq (hl.trans hr.symm)
    | some i =>
      exact heq_of_eq (coefficientLeavesTriple_leaf (L.obj i))



end CategoryTheory.Operad.Tensor
end
end
end source_CoefficientLeavesAssociativityData

/- Source proof segment: PartitionedCoefficientLeaves -/
section source_PartitionedCoefficientLeaves
/-!
# The original partition of coefficients and heterogeneous leaf families
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The original leaves in every block, with their actual dependent
sum of finite index types. Empty blocks contribute no leaves. -/
def partitionedLeafFamily (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) : FiniteFamily C :=
  let total : Type := Σ i : N.index, (L i).index
  haveI : Finite N.index := N.index.property
  haveI : (i : N.index) → Finite (L i).index := fun i => (L i).index.property
  haveI : Finite total := by infer_instance
  ⟨FintypeCat.of total, fun p => (L p.1).obj p.2⟩

/-- Each original branch keeps its complete coefficient block and
each of its original leaves as a singleton. -/
def partitionedCoefficientLeavesTriple (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) : FiniteFamily (FiniteFamily (FiniteFamily C)) where
  index := N.index
  obj i := coefficientLeavesNested (N.obj i) (L i)

/-- Reorder whole coefficient and singleton leaf blocks from the
original branch partition to coefficient-first order. -/
def partitionedCoefficientLeavesBlockEquiv (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) :
    ((FiniteFamily.flatten (C := FiniteFamily C)).obj
      (partitionedCoefficientLeavesTriple N L)).index ≃
    ((FiniteFamily.flatten (C := FiniteFamily C)).obj
      (coefficientLeavesTriple N (partitionedLeafFamily N L))).index where
  toFun p := match p with
    | ⟨i, none⟩ => ⟨none, i⟩
    | ⟨i, some l⟩ => ⟨some ⟨i, l⟩, PUnit.unit⟩
  invFun p := match p with
    | ⟨none, i⟩ => ⟨i, none⟩
    | ⟨some ⟨i, l⟩, _⟩ => ⟨i, some l⟩
  left_inv p := by
    rcases p with ⟨i, l⟩
    cases l <;> rfl
  right_inv p := by
    rcases p with ⟨l, i⟩
    cases l with
    | none => rfl
    | some p => rcases p with ⟨b, l⟩; cases i; rfl

/-- The displayed whole-block reordering retains every original
coefficient family and every original singleton leaf. -/
def partitionedCoefficientLeavesBlockIso (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) :
    (FiniteFamily.flatten (C := FiniteFamily C)).obj
        (partitionedCoefficientLeavesTriple N L) ≅
      (FiniteFamily.flatten (C := FiniteFamily C)).obj
        (coefficientLeavesTriple N (partitionedLeafFamily N L)) :=
  FiniteFamily.isoOfReindex (partitionedCoefficientLeavesBlockEquiv N L)
    (fun p => by rcases p with ⟨i, l⟩; cases l <;> rfl)

/-- The exact complete factor reordering: all original coefficients
are collected into one block and every original leaf is retained. -/
def partitionedCoefficientLeavesSourceEquiv (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) :
    ((FiniteFamily.flatten (C := C)).obj
      ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
        (partitionedCoefficientLeavesTriple N L))).index ≃
    ((FiniteFamily.flatten (C := C)).obj
      (coefficientLeavesNested ((FiniteFamily.flatten (C := C)).obj N)
        (partitionedLeafFamily N L))).index where
  toFun p := match p with
    | ⟨i, ⟨none, k⟩⟩ => ⟨none, ⟨i, k⟩⟩
    | ⟨i, ⟨some l, _⟩⟩ => ⟨some ⟨i, l⟩, PUnit.unit⟩
  invFun p := match p with
    | ⟨none, ⟨i, k⟩⟩ => ⟨i, ⟨none, k⟩⟩
    | ⟨some ⟨i, l⟩, _⟩ => ⟨i, ⟨some l, PUnit.unit⟩⟩
  left_inv p := by
    rcases p with ⟨i, ⟨l, k⟩⟩
    cases l with
    | none => rfl
    | some l => cases k; rfl
  right_inv p := by
    rcases p with ⟨l, k⟩
    cases l with
    | none => rcases k with ⟨i, k⟩; rfl
    | some p => rcases p with ⟨i, l⟩; cases k; rfl

/-- Identify the flattened partitioned coefficient-and-leaf source with the original
unpartitioned source. -/
def partitionedCoefficientLeavesSourceIso (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) :
    (FiniteFamily.flatten (C := C)).obj
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
          (partitionedCoefficientLeavesTriple N L)) ≅
      (FiniteFamily.flatten (C := C)).obj
        (coefficientLeavesNested ((FiniteFamily.flatten (C := C)).obj N)
          (partitionedLeafFamily N L)) :=
  FiniteFamily.isoOfReindex (partitionedCoefficientLeavesSourceEquiv N L)
    (fun p => by
      rcases p with ⟨i, ⟨l, k⟩⟩
      cases l with
      | none => rfl
      | some l => cases k; rfl)

variable [FiniteTensor C]

/-- The original normalized full operation factor family in each branch. -/
def partitionedCoefficientLeavesEvaluated (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) : FiniteFamily (FiniteFamily C) where
  index := N.index
  obj i := (coefficientLeafFamilyFunctor (L i)).obj ((FiniteTensor.tensor (V := C)).obj (N.obj i))

/-- Collapse the actual leaf singleton tensor in every original branch. -/
def partitionedCoefficientLeavesCollapse (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) :
    (FiniteFamily.map (FiniteFamily.map (FiniteTensor.tensor (V := C)))).obj
        (partitionedCoefficientLeavesTriple N L) ⟶
      partitionedCoefficientLeavesEvaluated N L where
  equiv := Equiv.refl N.index
  hom i := coefficientLeavesCollapse (N.obj i) (L i)

/-- Apply the original complete coefficient-leaf normalization
in every original branch, retaining the original branch indices. -/
def partitionedCoefficientLeavesNormalizationMap (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
          (partitionedCoefficientLeavesTriple N L)) ⟶
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        (partitionedCoefficientLeavesEvaluated N L) where
  equiv := Equiv.refl N.index
  hom i := coefficientLeavesNormalization (N.obj i) (L i)

theorem partitionedCoefficientLeavesNormalizationMap_eq (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) :
    partitionedCoefficientLeavesNormalizationMap N L =
      ((FiniteFamily.mapIso (FiniteTensor.flattenIso (V := C))).hom.app
        (partitionedCoefficientLeavesTriple N L)) ≫
        (FiniteFamily.map (FiniteTensor.tensor (V := C))).map
          (partitionedCoefficientLeavesCollapse N L) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    rfl

/-- The original scalar coefficients and leaves after branchwise
normalization, collected into coefficient-first order. -/
def partitionedCoefficientLeavesEvaluatedEquiv (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) :
    ((FiniteFamily.flatten (C := C)).obj
      (partitionedCoefficientLeavesEvaluated N L)).index ≃
    ((FiniteFamily.flatten (C := C)).obj
      (coefficientLeavesNested ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj N)
        (partitionedLeafFamily N L))).index where
  toFun p := match p with
    | ⟨i, none⟩ => ⟨none, i⟩
    | ⟨i, some l⟩ => ⟨some ⟨i, l⟩, PUnit.unit⟩
  invFun p := match p with
    | ⟨none, i⟩ => ⟨i, none⟩
    | ⟨some ⟨i, l⟩, _⟩ => ⟨i, some l⟩
  left_inv p := by
    rcases p with ⟨i, l⟩
    cases l <;> rfl
  right_inv p := by
    rcases p with ⟨l, i⟩
    cases l with
    | none => rfl
    | some p => rcases p with ⟨b, l⟩; cases i; rfl

/-- Identify the evaluated partitioned blocks with the coefficient tensors and their
original leaf family. -/
def partitionedCoefficientLeavesEvaluatedIso (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) :
    (FiniteFamily.flatten (C := C)).obj (partitionedCoefficientLeavesEvaluated N L) ≅
      (FiniteFamily.flatten (C := C)).obj
        (coefficientLeavesNested ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj N)
          (partitionedLeafFamily N L)) :=
  FiniteFamily.isoOfReindex (partitionedCoefficientLeavesEvaluatedEquiv N L)
    (fun p => by rcases p with ⟨i, l⟩; cases l <;> rfl)

end CategoryTheory.Operad.Tensor
end
end
end source_PartitionedCoefficientLeaves

/- Source proof segment: PartitionedScalarLeaves -/
section source_PartitionedScalarLeaves
/-!
# Original branch coefficient maps with unchanged heterogeneous leaves
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- An arbitrary original scalar coefficient in every original branch. -/
def partitionedScalarCoefficients (N : FiniteFamily (FiniteFamily C))
    (B : N.index → C) : FiniteFamily C where
  index := N.index
  obj := B

/-- The full original scalar coefficient and leaf family in each branch. -/
def partitionedScalarLeaves (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) (B : N.index → C) : FiniteFamily (FiniteFamily C) where
  index := N.index
  obj i := (coefficientLeafFamilyFunctor (L i)).obj (B i)

/-- The original coefficient maps on their original branch index. -/
def partitionedScalarCoefficientMap (N : FiniteFamily (FiniteFamily C))
    {B D : N.index → C} (g : ∀ i, B i ⟶ D i) :
    partitionedScalarCoefficients N B ⟶ partitionedScalarCoefficients N D where
  equiv := Equiv.refl N.index
  hom := g

/-- Each original coefficient map acts on its coefficient slot;
every original leaf map is the identity. -/
def partitionedScalarLeavesMap (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) {B D : N.index → C} (g : ∀ i, B i ⟶ D i) :
    partitionedScalarLeaves N L B ⟶ partitionedScalarLeaves N L D where
  equiv := Equiv.refl N.index
  hom i := (coefficientLeafFamilyFunctor (L i)).map (g i)

variable [FiniteTensor C]

/-- Identify the indices of the partitioned scalar-and-leaf family with the original
coefficient-and-leaf
indices. -/
def partitionedScalarLeavesEquiv (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) (B : N.index → C) :
    ((FiniteFamily.flatten (C := C)).obj (partitionedScalarLeaves N L B)).index ≃
      ((FiniteFamily.flatten (C := C)).obj
        (coefficientLeavesNested (partitionedScalarCoefficients N B) (partitionedLeafFamily
          N L))).index where
  toFun p := match p with
    | ⟨i, none⟩ => ⟨none, i⟩
    | ⟨i, some l⟩ => ⟨some ⟨i, l⟩, PUnit.unit⟩
  invFun p := match p with
    | ⟨none, i⟩ => ⟨i, none⟩
    | ⟨some ⟨i, l⟩, _⟩ => ⟨i, some l⟩
  left_inv p := by
    rcases p with ⟨i, l⟩
    cases l <;> rfl
  right_inv p := by
    rcases p with ⟨l, i⟩
    cases l with
    | none => rfl
    | some p => rcases p with ⟨b, l⟩; cases i; rfl

/-- The original full factors are collected by the same displayed
branch/leaf bijection, for arbitrary scalar coefficients. -/
def partitionedScalarLeavesIso (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) (B : N.index → C) :
    (FiniteFamily.flatten (C := C)).obj (partitionedScalarLeaves N L B) ≅
      (FiniteFamily.flatten (C := C)).obj
        (coefficientLeavesNested (partitionedScalarCoefficients N B) (partitionedLeafFamily N L)) :=
  FiniteFamily.isoOfReindex (partitionedScalarLeavesEquiv N L B)
    (fun p => by rcases p with ⟨i, l⟩; cases l <;> rfl)

/-- Distribute the actual branch tensor into its complete original
coefficient block and unchanged original leaves. -/
def partitionedScalarLeavesDistributionIso (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) (B : N.index → C) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (partitionedScalarLeaves N L B)) ≅
      (coefficientLeafTensorFunctor (partitionedLeafFamily N L)).obj
        ((FiniteTensor.tensor (V := C)).obj (partitionedScalarCoefficients N B)) :=
  ((FiniteTensor.flattenIso (V := C)).app (partitionedScalarLeaves N L B)).symm ≪≫
    (FiniteTensor.tensor (V := C)).mapIso (partitionedScalarLeavesIso N L B) ≪≫
      coefficientLeavesNormalizationIso (partitionedScalarCoefficients N B)
        (partitionedLeafFamily N L)

theorem partitionedScalarLeavesDistributionIso_hom (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) (B : N.index → C) :
    (partitionedScalarLeavesDistributionIso N L B).hom =
      (FiniteTensor.flattenIso (V := C)).inv.app (partitionedScalarLeaves N L B) ≫
        (FiniteTensor.tensor (V := C)).map (partitionedScalarLeavesIso N L B).hom ≫
        coefficientLeavesNormalization (partitionedScalarCoefficients N B)
          (partitionedLeafFamily N L) := by
  simp only [partitionedScalarLeavesDistributionIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, coefficientLeavesNormalizationIso_hom, Iso.app_inv]

/-- Evaluated original coefficient families have the original map-tensor family. -/
theorem partitionedScalarCoefficients_tensor (N : FiniteFamily (FiniteFamily C)) :
    partitionedScalarCoefficients N (fun i => (FiniteTensor.tensor (V := C)).obj (N.obj i)) =
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj N := rfl

theorem partitionedScalarLeaves_tensor (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) :
    partitionedScalarLeaves N L (fun i => (FiniteTensor.tensor (V := C)).obj (N.obj i)) =
      partitionedCoefficientLeavesEvaluated N L := rfl

/-- The original scalar factor permutation agrees with the
original branch normalization factor permutation after evaluation. -/
theorem partitionedScalarLeavesIso_tensor_hom (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) :
    (partitionedScalarLeavesIso N L (fun i => (FiniteTensor.tensor (V := C)).obj (N.obj i))).hom =
      (partitionedCoefficientLeavesEvaluatedIso N L).hom := by
  apply FiniteFamily.Hom_ext
  · ext p
    rcases p with ⟨i, l⟩
    cases l <;> rfl
  · intro p
    rcases p with ⟨i, l⟩
    cases l <;> rfl

end CategoryTheory.Operad.Tensor
end
end
end source_PartitionedScalarLeaves

/- Source proof segment: CoefficientLeavesFrozenMaps -/
section source_CoefficientLeavesFrozenMaps
@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- With the actual identity leaf map, the joint map is exactly
the original coefficient-only functor map. -/
theorem coefficientLeafMap_idLeaves {X Y : C} (f : X ⟶ Y) (L : FiniteFamily C) :
    coefficientLeafMap f (𝟙 L) = (coefficientLeafFamilyFunctor L).map f := by
  apply FiniteFamily.Hom_ext
  · ext i
    cases i <;> rfl
  · intro i
    cases i <;> rfl

end CategoryTheory.Operad.Tensor
end
end source_CoefficientLeavesFrozenMaps

/- Source proof segment: PartitionedScalarLeavesNaturality -/
section source_PartitionedScalarLeavesNaturality
/-!
# Original coefficient-map naturality of heterogeneous leaf distribution
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

omit [FiniteTensor C] in
/-- The exact original branch/leaf reordering commutes with each
original coefficient map and the identity maps on original leaves. -/
theorem partitionedScalarLeavesIso_square (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) {B D : N.index → C} (g : ∀ i, B i ⟶ D i) :
    (FiniteFamily.flatten (C := C)).map (partitionedScalarLeavesMap N L g) ≫
        (partitionedScalarLeavesIso N L D).hom =
      (partitionedScalarLeavesIso N L B).hom ≫
        (FiniteFamily.flatten (C := C)).map
          (coefficientLeavesNestedMap (partitionedScalarCoefficientMap N g)
            (𝟙 (partitionedLeafFamily N L))) := by
  apply FiniteFamily.Hom_ext
  · ext p
    rcases p with ⟨i, l⟩
    cases l <;> rfl
  · intro p
    rcases p with ⟨i, l⟩
    cases l with
    | none =>
      change HEq (g i ≫ 𝟙 _) (𝟙 _ ≫ g i)
      exact heq_of_eq ((Category.comp_id (g i)).trans (Category.id_comp (g i)).symm)
    | some l =>
      let X := (L i).obj l
      change HEq (𝟙 X ≫ 𝟙 X) (𝟙 X ≫ 𝟙 X)
      rfl

/-- The actual leaf distribution is natural in all original scalar
coefficient maps. Every leaf input is unchanged, with its original index. -/
@[reassoc]
theorem partitionedScalarLeavesDistributionIso_naturality
    (N : FiniteFamily (FiniteFamily C)) (L : N.index → FiniteFamily C)
    {B D : N.index → C} (g : ∀ i, B i ⟶ D i) :
    (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).map (partitionedScalarLeavesMap N L g)) ≫
      (partitionedScalarLeavesDistributionIso N L D).hom =
    (partitionedScalarLeavesDistributionIso N L B).hom ≫
      (coefficientLeafTensorFunctor (partitionedLeafFamily N L)).map
        ((FiniteTensor.tensor (V := C)).map (partitionedScalarCoefficientMap N g)) := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let L' := partitionedLeafFamily N L
  let h := partitionedScalarLeavesMap N L g
  let k := partitionedScalarCoefficientMap N g
  let j := coefficientLeavesNestedMap k (𝟙 L')
  let f₀ := T.map ((FiniteFamily.map T).map h)
  let f₁ := T.map (F.map h)
  let f₂ := T.map (F.map j)
  let f₃ := (coefficientLeafTensorFunctor L').map (T.map k)
  let uB := (FiniteTensor.flattenIso (V := C)).inv.app (partitionedScalarLeaves N L B)
  let uD := (FiniteTensor.flattenIso (V := C)).inv.app (partitionedScalarLeaves N L D)
  let vB := T.map (partitionedScalarLeavesIso N L B).hom
  let vD := T.map (partitionedScalarLeavesIso N L D).hom
  let wB := coefficientLeavesNormalization (partitionedScalarCoefficients N B) L'
  let wD := coefficientLeavesNormalization (partitionedScalarCoefficients N D) L'
  have h₀ := (FiniteTensor.flattenIso (V := C)).inv.naturality h
  change f₀ ≫ uD = uB ≫ f₁ at h₀
  have h₁ := congrArg T.map (partitionedScalarLeavesIso_square N L g)
  simp only [T.map_comp] at h₁
  change f₁ ≫ vD = vB ≫ f₂ at h₁
  have h₂ := coefficientLeavesNormalization_naturality k (𝟙 L')
  rw [coefficientLeafMap_idLeaves] at h₂
  change f₂ ≫ wD = wB ≫ f₃ at h₂
  rw [partitionedScalarLeavesDistributionIso_hom, partitionedScalarLeavesDistributionIso_hom]
  change f₀ ≫ uD ≫ vD ≫ wD = (uB ≫ vB ≫ wB) ≫ f₃
  exact composeThreeOperationSquares f₀ f₁ f₂ f₃ uB vB wB uD vD wD h₀ h₁ h₂



end CategoryTheory.Operad.Tensor
end
end
end source_PartitionedScalarLeavesNaturality

/- Source proof segment: TensorAssociativitySquares -/
section source_TensorAssociativitySquares
@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe u v u' v'

theorem functorMapPostSquare {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D] (F : C ⥤ D)
    {A B Q : C} {X Y : D}
    (p : X ⟶ Y) (d : Y ⟶ F.obj A) (a : X ⟶ F.obj B)
    (g : B ⟶ A) (c : A ⟶ Q)
    (hp : p ≫ d = a ≫ F.map g) :
    p ≫ (d ≫ F.map c) = a ≫ F.map (g ≫ c) := by
  rw [← Category.assoc, hp, Category.assoc, ← F.map_comp]

theorem eraseMiddleUnit {C : Type u} [Category.{v} C]
    {X A B R S : C} (a : X ⟶ A) (b : A ⟶ B)
    (r : X ⟶ R) (s : R ⟶ S) (h : S ⟶ S) (e : S ⟶ B)
    (hh : h = 𝟙 S) (ha : a ≫ b = r ≫ s ≫ h ≫ e) :
    a ≫ b = r ≫ s ≫ e := by
  rw [hh, Category.id_comp] at ha
  exact ha

/-- Combining the original source, pseudoalgebra associativity,
and target squares compares the two complete normalization routes. -/
theorem normalizeFromThreeSquares {C : Type u} [Category.{v} C]
    {X P Q Y A B R S T : C}
    (p : X ⟶ P) (n : P ⟶ Q) (f : Q ⟶ Y)
    (a : X ⟶ A) (b : A ⟶ B) (v : B ⟶ Y)
    (r : X ⟶ R) (s : R ⟶ S) (e : S ⟶ B)
    (t : S ⟶ T) (n' : T ⟶ Y)
    (hl : p ≫ n ≫ f = a ≫ b ≫ v)
    (ha : a ≫ b = r ≫ s ≫ e)
    (hr : t ≫ n' = e ≫ v) :
    p ≫ n ≫ f = r ≫ s ≫ t ≫ n' := by
  rw [hl, ← Category.assoc a b, ha]
  simp only [Category.assoc]
  rw [← hr]

end CategoryTheory.Operad.Tensor
end
end source_TensorAssociativitySquares

/- Source proof segment: CoefficientLeavesAssociativity -/
section source_CoefficientLeavesAssociativity
/-!
# Coherent normalization of original coefficient groupings and retained leaves
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- Evaluate two original coefficient levels before or after collecting
the retained original leaves. Both source factor regroupings are explicit;
the equality follows from the genuine finite tensor pseudoalgebra laws. -/
theorem coefficientLeavesNormalization_assoc (N : FiniteFamily (FiniteFamily C))
    (L : FiniteFamily C) :
    (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map (coefficientLeavesTripleFlattenIso N L).hom) ≫
      coefficientLeavesNormalization ((FiniteFamily.flatten (C := C)).obj N) L ≫
      (coefficientLeafTensorFunctor L).map ((FiniteTensor.flattenIso (V := C)).hom.app N) =
    (FiniteTensor.tensor (V := C)).map
        (FiniteFamily.flattenAssocIso.hom.app (coefficientLeavesTriple N L)) ≫
      (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.flatten (C := FiniteFamily C)).obj (coefficientLeavesTriple N L)) ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map (coefficientLeavesTripleTensorMap N L)) ≫
      coefficientLeavesNormalization ((FiniteFamily.map (FiniteTensor.tensor (V :=
        C))).obj N) L := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let M := coefficientLeavesTriple N L
  let K := F.obj N
  let K' := (FiniteFamily.map T).obj N
  let q := (coefficientLeavesTripleFlattenIso N L).hom
  let j := coefficientLeavesTripleTensorMap N L
  let p := T.map (F.map q)
  let a := (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.map F).obj M)
  let d := (FiniteTensor.flattenIso (V := C)).hom.app (coefficientLeavesNested K L)
  let b := ((FiniteFamily.mapIso (FiniteTensor.flattenIso (V := C))).hom.app M)
  let c := coefficientLeavesMap K L ((FiniteTensor.flattenIso (V := C)).hom.app N)
  let v := coefficientLeavesTripleCollapseMap N L
  let r := T.map (FiniteFamily.flattenAssocIso.hom.app M)
  let s := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.flatten (C := FiniteFamily C)).obj M)
  let e := (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.map (FiniteFamily.map
    T)).obj M)
  let t := T.map (F.map j)
  let d' := (FiniteTensor.flattenIso (V := C)).hom.app (coefficientLeavesNested K' L)
  let c' := coefficientLeavesCollapse K' L
  let f : T.obj K ⟶ T.obj K' := (FiniteTensor.flattenIso (V := C)).hom.app N
  have hq := (FiniteTensor.flattenIso (V := C)).hom.naturality q
  change p ≫ d = a ≫ T.map ((FiniteFamily.map T).map q) at hq
  have hc : (FiniteFamily.map T).map q ≫ c = b ≫ v :=
    (coefficientLeavesTripleCollapse_square N L).symm
  have hs := functorMapFactorSquare T a p d ((FiniteFamily.map T).map q) b c v hq hc
  have hn := coefficientLeavesNormalization_map K L f
  have hl : p ≫ coefficientLeavesNormalization K L ≫ (coefficientLeafTensorFunctor L).map f =
      a ≫ T.map b ≫ T.map v :=
    (congrArg (p ≫ ·) hn).trans hs.symm
  have hj := (FiniteTensor.flattenIso (V := C)).hom.naturality j
  change t ≫ d' = e ≫ T.map ((FiniteFamily.map T).map j) at hj
  have hr : t ≫ coefficientLeavesNormalization K' L = e ≫ T.map v :=
    functorMapPostSquare T t d' e ((FiniteFamily.map T).map j) c' hj
  let h := T.map ((FiniteFamily.flattenMapIso T).hom.app M)
  have hh : h = 𝟙 _ := by
    change T.map (𝟙 _) = 𝟙 _
    exact T.map_id _
  have ha := FiniteTensor.flattenAssocLaw_app_unfold M
  change a ≫ T.map b = r ≫ s ≫ h ≫ e at ha
  have hassoc := eraseMiddleUnit a (T.map b) r s h e hh ha
  exact normalizeFromThreeSquares p (coefficientLeavesNormalization K L)
    ((coefficientLeafTensorFunctor L).map f) a (T.map b) (T.map v) r s e
    t (coefficientLeavesNormalization K' L) hl hassoc hr



end CategoryTheory.Operad.Tensor
end
end
end source_CoefficientLeavesAssociativity

/- Source proof segment: PartitionedCoefficientLeavesComparisons -/
section source_PartitionedCoefficientLeavesComparisons
/-!
# Component comparisons for the original partition of coefficient and leaf factors
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The direct original factor permutation is precisely the actual
triple associator, whole-block shuffle, and singleton-index collapse. -/
theorem partitionedCoefficientLeavesSourceIso_hom (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) :
    (partitionedCoefficientLeavesSourceIso N L).hom =
      FiniteFamily.flattenAssocIso.hom.app (partitionedCoefficientLeavesTriple N L) ≫
        (FiniteFamily.flatten (C := C)).map (partitionedCoefficientLeavesBlockIso N L).hom ≫
        FiniteFamily.flattenAssocIso.inv.app
          (coefficientLeavesTriple N (partitionedLeafFamily N L)) ≫
        (FiniteFamily.flatten (C := C)).map
          (coefficientLeavesTripleFlattenIso N (partitionedLeafFamily N L)).hom := by
  apply FiniteFamily.Hom_ext
  · ext p
    rcases p with ⟨i, ⟨l, k⟩⟩
    cases l with
    | none => rfl
    | some l => cases k; rfl
  · intro p
    rcases p with ⟨i, ⟨l, k⟩⟩
    cases l with
    | none =>
      let X := (N.obj i).obj k
      change HEq (𝟙 X) (𝟙 X ≫ 𝟙 X ≫ 𝟙 X ≫ 𝟙 X)
      exact heq_of_eq (by simp only [Category.id_comp])
    | some l =>
      cases k
      let X := (L i).obj l
      change HEq (𝟙 X) (𝟙 X ≫ 𝟙 X ≫ 𝟙 X ≫ 𝟙 X)
      exact heq_of_eq (by simp only [Category.id_comp])

variable [FiniteTensor C]

/-- Collapse leaves in their original branches before or after the
whole-block shuffle. Both routes retain the original coefficient
tensor maps and the original singleton leaf unitors. -/
theorem partitionedCoefficientLeavesCollapse_square (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map
        (partitionedCoefficientLeavesBlockIso N L).hom ≫
      (FiniteFamily.flatten (C := C)).map
        (coefficientLeavesTripleTensorMap N (partitionedLeafFamily N L)) =
    (FiniteFamily.flatten (C := C)).map (partitionedCoefficientLeavesCollapse N L) ≫
      (partitionedCoefficientLeavesEvaluatedIso N L).hom := by
  apply FiniteFamily.Hom_ext
  · ext p
    rcases p with ⟨i, l⟩
    cases l <;> rfl
  · intro p
    rcases p with ⟨i, l⟩
    cases l with
    | none =>
      let X := (FiniteTensor.tensor (V := C)).obj (N.obj i)
      change HEq ((FiniteTensor.tensor (V := C)).map (𝟙 (N.obj i)) ≫ 𝟙 X) (𝟙 X ≫ 𝟙 X)
      exact heq_of_eq (congrArg (· ≫ 𝟙 X) ((FiniteTensor.tensor (V := C)).map_id _))
    | some l =>
      let f : (FiniteTensor.tensor (V := C)).obj ((FiniteFamily.singleton (C :=
        C)).obj ((L i).obj l)) ⟶
        (L i).obj l := (FiniteTensor.singletonIso (V := C)).hom.app ((L i).obj l)
      change HEq ((FiniteTensor.tensor (V := C)).map (𝟙 _) ≫ f) (f ≫ 𝟙 _)
      exact heq_of_eq ((congrArg (· ≫ f) ((FiniteTensor.tensor (V := C)).map_id _)).trans
        ((Category.id_comp f).trans (Category.comp_id f).symm))

/-- The actual whole-block tensor shuffle commutes with all original
singleton leaf collapses after the outer flattening. -/
theorem partitionedCoefficientLeavesTarget_square (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) :
    (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map (partitionedCoefficientLeavesBlockIso N L).hom) ≫
      (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.flatten (C := FiniteFamily C)).obj
          (coefficientLeavesTriple N (partitionedLeafFamily N L))) ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map
          (coefficientLeavesTripleTensorMap N (partitionedLeafFamily N L))) =
    (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.flatten (C := FiniteFamily C)).obj
          (partitionedCoefficientLeavesTriple N L)) ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map (partitionedCoefficientLeavesCollapse N L)) ≫
      (FiniteTensor.tensor (V := C)).map (partitionedCoefficientLeavesEvaluatedIso N L).hom := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let h := (partitionedCoefficientLeavesBlockIso N L).hom
  let a := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.flatten (C := FiniteFamily C)).obj (partitionedCoefficientLeavesTriple N L))
  let d := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.flatten (C := FiniteFamily C)).obj
      (coefficientLeavesTriple N (partitionedLeafFamily N L)))
  let b := F.map (partitionedCoefficientLeavesCollapse N L)
  let c := F.map (coefficientLeavesTripleTensorMap N (partitionedLeafFamily N L))
  let t := (partitionedCoefficientLeavesEvaluatedIso N L).hom
  have hn := (FiniteTensor.flattenIso (V := C)).hom.naturality h
  change T.map (F.map h) ≫ d = a ≫ T.map ((FiniteFamily.map T).map h) at hn
  have hc : (FiniteFamily.map T).map h ≫ c = b ≫ t :=
    partitionedCoefficientLeavesCollapse_square N L
  exact (functorMapFactorSquare T a (T.map (F.map h)) d
    ((FiniteFamily.map T).map h) b c t hn hc).symm





end CategoryTheory.Operad.Tensor
end
end
end source_PartitionedCoefficientLeavesComparisons

/- Source proof segment: TensorFoldSquares -/
section source_TensorFoldSquares
@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe u v

/-- Cancel the original outer flattening after evaluating its
original component maps, using pseudoalgebra associativity and naturality. -/
theorem foldAndCancel {C : Type u} [Category.{v} C]
    {X A B P R S Z : C} (a : X ⟶ A) (b : A ⟶ B) (c : B ⟶ P)
    (r : X ⟶ R) (s : R ⟶ S) (e : S ⟶ B)
    (j : S ⟶ Z) (q : Z ⟶ P) (i : P ⟶ Z)
    (ha : a ≫ b = r ≫ s ≫ e) (hc : e ≫ c = j ≫ q)
    (hq : q ≫ i = 𝟙 Z) :
    a ≫ (b ≫ c) ≫ i = r ≫ s ≫ j := by
  rw [Category.assoc b c i]
  rw [← Category.assoc a b, ha]
  simp only [Category.assoc]
  rw [← Category.assoc e c, hc]
  simp only [Category.assoc]
  rw [hq, Category.comp_id]

end CategoryTheory.Operad.Tensor
end
end source_TensorFoldSquares

/- Source proof segment: PartitionedCoefficientLeavesFold -/
section source_PartitionedCoefficientLeavesFold
/-!
# The actual branchwise coefficient-leaf normalization fold
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The original complete normalization in every branch is the
three-level flattening followed by the original singleton leaf collapses.
All factors and their dependent finite indices are retained. -/
theorem partitionedCoefficientLeaves_fold (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) :
    (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
          (partitionedCoefficientLeavesTriple N L)) ≫
      (FiniteTensor.tensor (V := C)).map (partitionedCoefficientLeavesNormalizationMap N L) ≫
      (FiniteTensor.flattenIso (V := C)).inv.app (partitionedCoefficientLeavesEvaluated N L) =
    (FiniteTensor.tensor (V := C)).map
        (FiniteFamily.flattenAssocIso.hom.app (partitionedCoefficientLeavesTriple N L)) ≫
      (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.flatten (C := FiniteFamily C)).obj
          (partitionedCoefficientLeavesTriple N L)) ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map (partitionedCoefficientLeavesCollapse N L)) := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let M := partitionedCoefficientLeavesTriple N L
  let E := partitionedCoefficientLeavesEvaluated N L
  let z := partitionedCoefficientLeavesCollapse N L
  let a := (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.map F).obj M)
  let b := ((FiniteFamily.mapIso (FiniteTensor.flattenIso (V := C))).hom.app M)
  let c := (FiniteFamily.map T).map z
  let r := T.map (FiniteFamily.flattenAssocIso.hom.app M)
  let s := (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.flatten (C :=
    FiniteFamily C)).obj M)
  let e := (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.map (FiniteFamily.map
    T)).obj M)
  let j := T.map (F.map z)
  let q := (FiniteTensor.flattenIso (V := C)).hom.app E
  let i := (FiniteTensor.flattenIso (V := C)).inv.app E
  let h := T.map ((FiniteFamily.flattenMapIso T).hom.app M)
  have hh : h = 𝟙 _ := by
    change T.map (𝟙 _) = 𝟙 _
    exact T.map_id _
  have ha := FiniteTensor.flattenAssocLaw_app_unfold M
  change a ≫ T.map b = r ≫ s ≫ h ≫ e at ha
  have hassoc := eraseMiddleUnit a (T.map b) r s h e hh ha
  have hc := (FiniteTensor.flattenIso (V := C)).hom.naturality z
  change j ≫ q = e ≫ T.map c at hc
  have hq : q ≫ i = 𝟙 _ := (FiniteTensor.flattenIso (V := C)).hom_inv_id_app E
  have hn : T.map (partitionedCoefficientLeavesNormalizationMap N L) = T.map b ≫ T.map c :=
    (congrArg T.map (partitionedCoefficientLeavesNormalizationMap_eq N L)).trans (T.map_comp b c)
  change a ≫ T.map (partitionedCoefficientLeavesNormalizationMap N L) ≫ i = r ≫ s ≫ j
  exact (congrArg (fun f => a ≫ f ≫ i) hn).trans
    (foldAndCancel a (T.map b) (T.map c) r s e j q i hassoc hc.symm hq)



end CategoryTheory.Operad.Tensor
end
end
end source_PartitionedCoefficientLeavesFold

/- Source proof segment: TensorPartitionSquares -/
section source_TensorPartitionSquares
@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe u v

/-- The actual complete factor permutation, pseudoalgebra
comparison, target square, and branch fold compare both routes. -/
theorem partitionNormalizationFromFiveSquares {C : Type u} [Category.{v} C]
    {X P Q Y A B R S U V Z Z₁ Z₂ : C}
    (p : X ⟶ P) (n : P ⟶ Q) (f : Q ⟶ Y)
    (a : X ⟶ A) (b : A ⟶ B) (im : B ⟶ R) (hm : R ⟶ B) (q : R ⟶ P)
    (c : B ⟶ S) (r : S ⟶ U) (n' : U ⟶ Y)
    (s : A ⟶ V) (z : V ⟶ Z) (t : Z ⟶ U)
    (l₀ : X ⟶ Z₁) (l₁ : Z₁ ⟶ Z₂) (l₂ : Z₂ ⟶ Z)
    (hp : p = a ≫ b ≫ im ≫ q) (hm' : q ≫ n ≫ f = hm ≫ c ≫ r ≫ n')
    (hi : im ≫ hm = 𝟙 B) (ht : b ≫ c ≫ r = s ≫ z ≫ t)
    (hf : l₀ ≫ l₁ ≫ l₂ = a ≫ s ≫ z) :
    p ≫ n ≫ f = l₀ ≫ l₁ ≫ l₂ ≫ t ≫ n' := by
  calc
    p ≫ n ≫ f = a ≫ b ≫ im ≫ q ≫ n ≫ f := by rw [hp]; simp only [Category.assoc]
    _ = a ≫ b ≫ im ≫ hm ≫ c ≫ r ≫ n' := by rw [hm']
    _ = a ≫ b ≫ c ≫ r ≫ n' := by rw [← Category.assoc im hm, hi, Category.id_comp]
    _ = a ≫ s ≫ z ≫ t ≫ n' := by
      simpa only [Category.assoc] using congrArg (fun g => a ≫ g ≫ n') ht
    _ = l₀ ≫ l₁ ≫ l₂ ≫ t ≫ n' := by
      simpa only [Category.assoc] using congrArg (fun g => g ≫ t ≫ n') hf.symm

end CategoryTheory.Operad.Tensor
end
end source_TensorPartitionSquares

/- Source proof segment: PartitionedCoefficientLeavesNormalization -/
section source_PartitionedCoefficientLeavesNormalization
/-!
# Source-faithful branch-partition coefficient-leaf normalization
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- Normalize complete original branch coefficient and leaf factors
before or after collecting the coefficient blocks. The actual factor
permutations, branchwise flattenings, and singleton unitors all remain
in the equation. It includes empty coefficient and leaf blocks. -/
theorem partitionedCoefficientLeaves_normalization
    (N : FiniteFamily (FiniteFamily C)) (L : N.index → FiniteFamily C) :
    (FiniteTensor.tensor (V := C)).map (partitionedCoefficientLeavesSourceIso N L).hom ≫
      coefficientLeavesNormalization ((FiniteFamily.flatten (C := C)).obj N)
        (partitionedLeafFamily N L) ≫
      (coefficientLeafTensorFunctor (partitionedLeafFamily N L)).map
        ((FiniteTensor.flattenIso (V := C)).hom.app N) =
    (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
          (partitionedCoefficientLeavesTriple N L)) ≫
      (FiniteTensor.tensor (V := C)).map (partitionedCoefficientLeavesNormalizationMap N L) ≫
      (FiniteTensor.flattenIso (V := C)).inv.app (partitionedCoefficientLeavesEvaluated N L) ≫
      (FiniteTensor.tensor (V := C)).map (partitionedCoefficientLeavesEvaluatedIso N L).hom ≫
      coefficientLeavesNormalization ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj N)
        (partitionedLeafFamily N L) := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let L' := partitionedLeafFamily N L
  let P := partitionedCoefficientLeavesTriple N L
  let M := coefficientLeavesTriple N L'
  let E := partitionedCoefficientLeavesEvaluated N L
  let p := T.map (partitionedCoefficientLeavesSourceIso N L).hom
  let n := coefficientLeavesNormalization (F.obj N) L'
  let f : (coefficientLeafTensorFunctor L').obj (T.obj (F.obj N)) ⟶
      (coefficientLeafTensorFunctor L').obj (T.obj ((FiniteFamily.map T).obj N)) :=
    (coefficientLeafTensorFunctor L').map ((FiniteTensor.flattenIso (V := C)).hom.app N)
  let a := T.map (FiniteFamily.flattenAssocIso.hom.app P)
  let b := T.map (F.map (partitionedCoefficientLeavesBlockIso N L).hom)
  let im := T.map (FiniteFamily.flattenAssocIso.inv.app M)
  let hm := T.map (FiniteFamily.flattenAssocIso.hom.app M)
  let q := T.map (F.map (coefficientLeavesTripleFlattenIso N L').hom)
  let c := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.flatten (C := FiniteFamily C)).obj M)
  let r := T.map (F.map (coefficientLeavesTripleTensorMap N L'))
  let n' := coefficientLeavesNormalization ((FiniteFamily.map T).obj N) L'
  let s := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.flatten (C := FiniteFamily C)).obj P)
  let z := T.map (F.map (partitionedCoefficientLeavesCollapse N L))
  let t := T.map (partitionedCoefficientLeavesEvaluatedIso N L).hom
  let fold := (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.map F).obj P) ≫
    T.map (partitionedCoefficientLeavesNormalizationMap N L) ≫
      (FiniteTensor.flattenIso (V := C)).inv.app E
  let a₀ := FiniteFamily.flattenAssocIso.hom.app P
  let b₀ := F.map (partitionedCoefficientLeavesBlockIso N L).hom
  let im₀ := FiniteFamily.flattenAssocIso.inv.app M
  let q₀ := F.map (coefficientLeavesTripleFlattenIso N L').hom
  have hs : (partitionedCoefficientLeavesSourceIso N L).hom = a₀ ≫ b₀ ≫ im₀ ≫ q₀ :=
    partitionedCoefficientLeavesSourceIso_hom N L
  have hp : p = a ≫ b ≫ im ≫ q :=
    (congrArg T.map hs).trans
      ((T.map_comp a₀ (b₀ ≫ im₀ ≫ q₀)).trans
        (congrArg (T.map a₀ ≫ ·)
          ((T.map_comp b₀ (im₀ ≫ q₀)).trans
            (congrArg (T.map b₀ ≫ ·) (T.map_comp im₀ q₀)))))
  have hm' : q ≫ n ≫ f = hm ≫ c ≫ r ≫ n' := coefficientLeavesNormalization_assoc N L'
  have hi : im ≫ hm = 𝟙 _ :=
    (T.map_comp _ _).symm.trans
      ((congrArg T.map (FiniteFamily.flattenAssocIso.inv_hom_id_app M)).trans (T.map_id _))
  have ht : b ≫ c ≫ r = s ≫ z ≫ t := partitionedCoefficientLeavesTarget_square N L
  have hf : fold = a ≫ s ≫ z := partitionedCoefficientLeaves_fold N L
  exact partitionNormalizationFromFiveSquares p n f a b im hm q c r n' s z t
    ((FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.map F).obj P))
    (T.map (partitionedCoefficientLeavesNormalizationMap N L))
    ((FiniteTensor.flattenIso (V := C)).inv.app E) hp hm' hi ht hf



end CategoryTheory.Operad.Tensor
end
end
end source_PartitionedCoefficientLeavesNormalization

/- Source proof segment: PartitionedScalarLeavesReadback -/
section source_PartitionedScalarLeavesReadback
/-!
# Original branch normalization readback in scalar leaf distribution
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

theorem partitionedScalarLeavesDistributionIso_tensor_hom
    (N : FiniteFamily (FiniteFamily C)) (L : N.index → FiniteFamily C) :
    (partitionedScalarLeavesDistributionIso N L
        (fun i => (FiniteTensor.tensor (V := C)).obj (N.obj i))).hom =
      (FiniteTensor.flattenIso (V := C)).inv.app (partitionedCoefficientLeavesEvaluated N L) ≫
        (FiniteTensor.tensor (V := C)).map (partitionedCoefficientLeavesEvaluatedIso N L).hom ≫
        coefficientLeavesNormalization ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj N)
          (partitionedLeafFamily N L) := by
  rw [partitionedScalarLeavesDistributionIso_hom, partitionedScalarLeavesIso_tensor_hom]
  rfl

/-- The complete branchwise normalization has the original scalar
leaf distribution, with every factor map retained. -/
theorem partitionedCoefficientLeaves_normalization_distribution
    (N : FiniteFamily (FiniteFamily C)) (L : N.index → FiniteFamily C) :
    (FiniteTensor.tensor (V := C)).map (partitionedCoefficientLeavesSourceIso N L).hom ≫
      coefficientLeavesNormalization ((FiniteFamily.flatten (C := C)).obj N)
        (partitionedLeafFamily N L) ≫
      (coefficientLeafTensorFunctor (partitionedLeafFamily N L)).map
        ((FiniteTensor.flattenIso (V := C)).hom.app N) =
    (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
          (partitionedCoefficientLeavesTriple N L)) ≫
      (FiniteTensor.tensor (V := C)).map (partitionedCoefficientLeavesNormalizationMap N L) ≫
      (partitionedScalarLeavesDistributionIso N L
        (fun i => (FiniteTensor.tensor (V := C)).obj (N.obj i))).hom := by
  rw [partitionedScalarLeavesDistributionIso_tensor_hom]
  exact partitionedCoefficientLeaves_normalization N L

end CategoryTheory.Operad.Tensor
end
end
end source_PartitionedScalarLeavesReadback

/- Source proof segment: TensorActionSquares -/
section source_TensorActionSquares
@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe u v

/-- Extend an original normalization square by the original
coefficient-map action and its distribution naturality square. -/
theorem coefficientActionFromTwoSquares {C : Type u} [Category.{v} C]
    {X P Q U Y A B D : C}
    (p : X ⟶ P) (n : P ⟶ Q) (u : Q ⟶ U) (v : U ⟶ Y) (f : Q ⟶ Y)
    (a : X ⟶ A) (b : A ⟶ B) (d : B ⟶ U)
    (c : B ⟶ D) (e : D ⟶ Y) (k : A ⟶ D)
    (hf : f = u ≫ v) (hs : p ≫ n ≫ u = a ≫ b ≫ d)
    (ha : c ≫ e = d ≫ v) (hc : b ≫ c = k) :
    p ≫ n ≫ f = a ≫ k ≫ e := by
  calc
    p ≫ n ≫ f = p ≫ n ≫ u ≫ v := by rw [hf]
    _ = a ≫ b ≫ d ≫ v := by
      simpa only [Category.assoc] using congrArg (· ≫ v) hs
    _ = a ≫ b ≫ c ≫ e := by rw [← ha]
    _ = a ≫ k ≫ e := by rw [← Category.assoc b c, hc]

end CategoryTheory.Operad.Tensor
end
end source_TensorActionSquares

/- Source proof segment: PartitionedCoefficientLeavesAction -/
section source_PartitionedCoefficientLeavesAction
/-!
# Actual branchwise coefficient substitutions with original retained leaves
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The original map from every original coefficient tensor block
to its original resulting coefficient object. -/
def partitionedCoefficientMap (N : FiniteFamily (FiniteFamily C))
    (B : N.index → C) (g : ∀ i, (FiniteTensor.tensor (V := C)).obj (N.obj i) ⟶ B i) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj N ⟶
      partitionedScalarCoefficients N B where
  equiv := Equiv.refl N.index
  hom := g

/-- Each original complete branch normalization is followed by
its original coefficient substitution, retaining original leaves. -/
def partitionedCoefficientLeavesActionMap (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) (B : N.index → C)
    (g : ∀ i, (FiniteTensor.tensor (V := C)).obj (N.obj i) ⟶ B i) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
          (partitionedCoefficientLeavesTriple N L)) ⟶
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (partitionedScalarLeaves N L B) where
  equiv := Equiv.refl N.index
  hom i := coefficientLeavesNormalization (N.obj i) (L i) ≫
    (coefficientLeafTensorFunctor (L i)).map (g i)

theorem partitionedCoefficientMap_eq_scalar (N : FiniteFamily (FiniteFamily C))
    (B : N.index → C) (g : ∀ i, (FiniteTensor.tensor (V := C)).obj (N.obj i) ⟶ B i) :
    partitionedCoefficientMap N B g = partitionedScalarCoefficientMap N g := rfl

theorem partitionedCoefficientLeavesActionMap_eq (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) (B : N.index → C)
    (g : ∀ i, (FiniteTensor.tensor (V := C)).obj (N.obj i) ⟶ B i) :
    partitionedCoefficientLeavesActionMap N L B g =
      partitionedCoefficientLeavesNormalizationMap N L ≫
        (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (partitionedScalarLeavesMap N
          L g) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    rfl

/-- The genuine complete branchwise substitutions equal the original
coefficient-block substitution with all original leaves retained.
The equation keeps the exact source permutation, original branch
normalizations, and original coefficient maps. -/
theorem partitionedCoefficientLeaves_action (N : FiniteFamily (FiniteFamily C))
    (L : N.index → FiniteFamily C) (B : N.index → C)
    (g : ∀ i, (FiniteTensor.tensor (V := C)).obj (N.obj i) ⟶ B i) :
    (FiniteTensor.tensor (V := C)).map (partitionedCoefficientLeavesSourceIso N L).hom ≫
      coefficientLeavesNormalization ((FiniteFamily.flatten (C := C)).obj N)
        (partitionedLeafFamily N L) ≫
      (coefficientLeafTensorFunctor (partitionedLeafFamily N L)).map
        ((FiniteTensor.flattenIso (V := C)).hom.app N ≫
          (FiniteTensor.tensor (V := C)).map (partitionedCoefficientMap N B g)) =
    (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
          (partitionedCoefficientLeavesTriple N L)) ≫
      (FiniteTensor.tensor (V := C)).map (partitionedCoefficientLeavesActionMap N L B g) ≫
      (partitionedScalarLeavesDistributionIso N L B).hom := by
  let T := FiniteTensor.tensor (V := C)
  let L' := partitionedLeafFamily N L
  let F := coefficientLeafTensorFunctor L'
  let p := T.map (partitionedCoefficientLeavesSourceIso N L).hom
  let n := coefficientLeavesNormalization ((FiniteFamily.flatten (C := C)).obj N) L'
  let u := F.map ((FiniteTensor.flattenIso (V := C)).hom.app N)
  let v := F.map (T.map (partitionedCoefficientMap N B g))
  let f := F.map ((FiniteTensor.flattenIso (V := C)).hom.app N ≫
    T.map (partitionedCoefficientMap N B g))
  let a := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
      (partitionedCoefficientLeavesTriple N L))
  let b := T.map (partitionedCoefficientLeavesNormalizationMap N L)
  let d := (partitionedScalarLeavesDistributionIso N L (fun i => T.obj (N.obj i))).hom
  let c := T.map ((FiniteFamily.map T).map (partitionedScalarLeavesMap N L g))
  let e := (partitionedScalarLeavesDistributionIso N L B).hom
  let k := T.map (partitionedCoefficientLeavesActionMap N L B g)
  have hf : f = u ≫ v := F.map_comp _ _
  have hs : p ≫ n ≫ u = a ≫ b ≫ d := partitionedCoefficientLeaves_normalization_distribution N L
  have ha := partitionedScalarLeavesDistributionIso_naturality N L g
  rw [← partitionedCoefficientMap_eq_scalar] at ha
  change c ≫ e = d ≫ v at ha
  have hc : b ≫ c = k :=
    (T.map_comp _ _).symm.trans
      (congrArg T.map (partitionedCoefficientLeavesActionMap_eq N L B g).symm)
  exact coefficientActionFromTwoSquares p n u v f a b d c e k hf hs ha hc



end CategoryTheory.Operad.Tensor
end
end
end source_PartitionedCoefficientLeavesAction

/- Source proof segment: SubstitutionCoefficientLeaves -/
section source_SubstitutionCoefficientLeaves
/-!
# Original two-level substitution and coefficient-leaf normalization
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Group the original coefficient and total-profile leaves into the actual substitution
input factors. -/
def substitutionLeavesGroupingIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    coefficientLeavesNested ((ColoredOperadObj.substitutionFactors O).obj s)
        (profileLeafFamily A s.totalProfile) ≅ substitutionInputFactors O A s :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option s.totalProfile.inputs))
    (fun i => match i with
      | none => Iso.refl _
      | some _ => Iso.refl _)

/-- Identify the coefficient-and-total-leaf target with the original operation factors. -/
def substitutionLeavesTargetIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    (coefficientLeafFamilyFunctor (profileLeafFamily A s.totalProfile)).obj (O.obj s.totalProfile) ≅
      (operationFactorsFunctor O A).obj s.totalProfile :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option s.totalProfile.inputs))
    (fun i => match i with
      | none => Iso.refl _
      | some _ => Iso.refl _)

/-- The actual coefficient substitution map and the original singleton
leaf unitors agree with the generic coefficient-leaf map after the
displayed original family identifications. -/
theorem substitutionLeavesCoefficientMap (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map
        (substitutionLeavesGroupingIso O.toCollection A s).hom ≫
      operadCoefficientMap O A s =
    coefficientLeavesMap ((ColoredOperadObj.substitutionFactors O.toCollection).obj s)
        (profileLeafFamily A s.totalProfile) (O.subst.app s) ≫
      (substitutionLeavesTargetIso O.toCollection A s).hom := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      let f : (FiniteTensor.tensor (V := C)).obj
          ((ColoredOperadObj.substitutionFactors O.toCollection).obj s) ⟶
            O.toCollection.obj s.totalProfile := O.subst.app s
      change HEq
        ((FiniteTensor.tensor (V := C)).map (𝟙 _) ≫ f) (f ≫ 𝟙 _)
      exact heq_of_eq ((congrArg (· ≫ f) ((FiniteTensor.tensor (V := C)).map_id _)).trans
        ((Category.id_comp f).trans (Category.comp_id f).symm))
    | some i =>
      change HEq
        ((FiniteTensor.tensor (V := C)).map (𝟙 _) ≫
          (FiniteTensor.singletonIso (V := C)).hom.app (A (s.totalProfile.inputColor i)))
        ((FiniteTensor.singletonIso (V := C)).hom.app (A (s.totalProfile.inputColor i)) ≫ 𝟙 _)
      exact heq_of_eq (by rw [Functor.map_id, Category.id_comp, Category.comp_id])

/-- The normalized coefficient-first map is exactly the actual
operadic substitution and original leaf unitors, after the original
finite-family comparison. -/
theorem substitutionLeavesNormalizedMap (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    coefficientLeavesNormalization
        ((ColoredOperadObj.substitutionFactors O.toCollection).obj s)
        (profileLeafFamily A s.totalProfile) ≫
      (coefficientLeafTensorFunctor (profileLeafFamily A s.totalProfile)).map
        (O.subst.app s) ≫
      (FiniteTensor.tensor (V := C)).map
        (substitutionLeavesTargetIso O.toCollection A s).hom =
    (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map
          (substitutionLeavesGroupingIso O.toCollection A s).hom) ≫
      (FiniteTensor.flattenIso (V := C)).hom.app
        (substitutionInputFactors O.toCollection A s) ≫
      (FiniteTensor.tensor (V := C)).map (operadCoefficientMap O A s) := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let K := (ColoredOperadObj.substitutionFactors O.toCollection).obj s
  let L := profileLeafFamily A s.totalProfile
  let f : T.obj K ⟶ O.toCollection.obj s.totalProfile := O.subst.app s
  let a := (FiniteTensor.flattenIso (V := C)).hom.app (coefficientLeavesNested K L)
  let b := coefficientLeavesMap K L f
  let t := (substitutionLeavesTargetIso O.toCollection A s).hom
  let g := (substitutionLeavesGroupingIso O.toCollection A s).hom
  let c := operadCoefficientMap O A s
  let d := (FiniteTensor.flattenIso (V := C)).hom.app (substitutionInputFactors O.toCollection A s)
  have hn := (FiniteTensor.flattenIso (V := C)).hom.naturality g
  have hc : (FiniteFamily.map T).map g ≫ c = b ≫ t :=
    substitutionLeavesCoefficientMap O A s
  have hp := coefficientLeavesNormalization_map K L f
  change T.map (F.map g) ≫ d = a ≫ T.map ((FiniteFamily.map T).map g) at hn
  change coefficientLeavesNormalization K L ≫ (coefficientLeafTensorFunctor L).map f ≫ T.map t =
    T.map (F.map g) ≫ d ≫ T.map c
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ T.map t) hp).trans
      ((Category.assoc _ _ _).trans
        (functorMapFactorSquare T a (T.map (F.map g)) d
          ((FiniteFamily.map T).map g) b c t hn hc)))

/-- Original input-first factors are regrouped into the complete
coefficient block with retained original leaves. -/
def substitutionToLeavesIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    (FiniteFamily.flatten (C := C)).obj (nestedOperationFactors O A s) ≅
      (FiniteFamily.flatten (C := C)).obj
        (coefficientLeavesNested ((ColoredOperadObj.substitutionFactors O).obj s)
          (profileLeafFamily A s.totalProfile)) :=
  substitutionFactorsIso O A s ≪≫
    (FiniteFamily.flatten (C := C)).mapIso (substitutionLeavesGroupingIso O A s).symm

/-- Complete source-faithful two-level factorization: the original
operadic substitution first regroups all original factors, normalizes
the coefficient block, and applies the original coefficient substitution. -/
theorem operadSubstitutionInputs_factorization (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    operadSubstitutionInputs O A s =
      (FiniteTensor.tensor (V := C)).map
          (substitutionToLeavesIso O.toCollection A s).hom ≫
        coefficientLeavesNormalization
          ((ColoredOperadObj.substitutionFactors O.toCollection).obj s)
          (profileLeafFamily A s.totalProfile) ≫
        (coefficientLeafTensorFunctor (profileLeafFamily A s.totalProfile)).map (O.subst.app s) ≫
        (FiniteTensor.tensor (V := C)).map
          (substitutionLeavesTargetIso O.toCollection A s).hom := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let p := (substitutionFactorsIso O.toCollection A s).hom
  let g := substitutionLeavesGroupingIso O.toCollection A s
  let a := (FiniteTensor.flattenIso (V := C)).hom.app
    (substitutionInputFactors O.toCollection A s)
  let c := operadCoefficientMap O A s
  let r := coefficientLeavesNormalization
    ((ColoredOperadObj.substitutionFactors O.toCollection).obj s)
    (profileLeafFamily A s.totalProfile) ≫
      (coefficientLeafTensorFunctor (profileLeafFamily A s.totalProfile)).map (O.subst.app s) ≫
        T.map (substitutionLeavesTargetIso O.toCollection A s).hom
  have hn := substitutionLeavesNormalizedMap O A s
  have hi : F.map g.inv ≫ F.map g.hom = 𝟙 _ := by
    rw [← F.map_comp, g.inv_hom_id, F.map_id]
  have ht : T.map (F.map g.inv) ≫ T.map (F.map g.hom) = 𝟙 _ :=
    (T.map_comp _ _).symm.trans ((congrArg T.map hi).trans (T.map_id _))
  change r = T.map (F.map g.hom) ≫ a ≫ T.map c at hn
  change T.map p ≫ a ≫ T.map c = T.map (p ≫ F.map g.inv) ≫ r
  symm
  exact (congrArg (· ≫ r) (T.map_comp _ _)).trans
    (cancelNormalizedRegrouping (T.map p) (T.map (F.map g.inv)) (T.map (F.map g.hom))
      a (T.map c) r ht hn)



end CategoryTheory.Operad.Tensor
end
end
end source_SubstitutionCoefficientLeaves

/- Source proof segment: OperadAssociativityTensorLeaves -/
section source_OperadAssociativityTensorLeaves
/-!
# Original operadic associativity with retained tensor leaves

The two original coefficient substitution routes remain equal
after tensoring with any original finite leaf-input family. Their
actual coefficient maps and original dependent-sum associator are
retained. Monad associativity requires the further colimit descent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original operadic coefficient associativity equality,
tensored with every original finite leaf-input family. -/
theorem operadAssociativity_tensor_leaves (O : ColoredOperadObj W C)
    (s : ColoredAssocData W) (L : FiniteFamily C) :
    (coefficientLeafTensorFunctor L).map
        (ColoredOperadObj.associativityRouteA O.toCollection O.subst s) =
      (coefficientLeafTensorFunctor L).map
        (ColoredOperadObj.associativityRouteB O.toCollection O.subst s) :=
  congrArg (coefficientLeafTensorFunctor L).map (O.assoc s)



end CategoryTheory.Operad.Tensor
end
end
end source_OperadAssociativityTensorLeaves

/- Source proof segment: OperadicLeafPartitions -/
section source_OperadicLeafPartitions
/-!
# Original colored three-level leaf partitions and the total-profile relabelling
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

/-- The original leaf family below every local substitution branch. -/
def associativityLeafBlocksA (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (ColoredOperadObj.AssocInsertion.groupingA O s).index → FiniteFamily C :=
  fun o => match o with
    | none => FiniteFamily.empty
    | some i => profileLeafFamily A (s.localData i).totalProfile

/-- The original leaf family below every flattened innermost operation. -/
def associativityLeafBlocksB (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (ColoredOperadObj.AssocInsertion.groupingB O s).index → FiniteFamily C :=
  fun o => match o with
    | none => FiniteFamily.empty
    | some p => profileLeafFamily A (s.innerData.inner.obj p)

/-- Remove only the empty root leaf block from the original branch
leaf partition. The original nested total-profile input type is retained. -/
def associativityLeafUnionEquivA (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (partitionedLeafFamily (ColoredOperadObj.AssocInsertion.groupingA O s)
      (associativityLeafBlocksA O A s)).index ≃ s.outerAfterInnerData.totalProfile.inputs where
  toFun p := match p with
    | ⟨none, e⟩ => e.elim
    | ⟨some i, p⟩ => ⟨i, p⟩
  invFun p := ⟨some p.1, p.2⟩
  left_inv p := by
    rcases p with ⟨o, p⟩
    cases o with
    | none => cases p
    | some i => rfl
  right_inv p := by rcases p with ⟨i, p⟩; rfl

/-- Identify route A of the associativity leaf partition with the original outer-after-inner
total profile. -/
def associativityLeafUnionIsoA (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    partitionedLeafFamily (ColoredOperadObj.AssocInsertion.groupingA O s)
        (associativityLeafBlocksA O A s) ≅
      profileLeafFamily A s.outerAfterInnerData.totalProfile :=
  FiniteFamily.isoOfReindex (associativityLeafUnionEquivA O A s)
    (fun p => by
      rcases p with ⟨o, p⟩
      cases o with
      | none => cases p
      | some i => rfl)

/-- Remove only the empty root leaf block from the original flat
inner-operation partition, retaining its actual total-profile inputs. -/
def associativityLeafUnionEquivB (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (partitionedLeafFamily (ColoredOperadObj.AssocInsertion.groupingB O s)
      (associativityLeafBlocksB O A s)).index ≃ s.innerData.totalProfile.inputs where
  toFun p := match p with
    | ⟨none, e⟩ => e.elim
    | ⟨some i, p⟩ => ⟨i, p⟩
  invFun p := ⟨some p.1, p.2⟩
  left_inv p := by
    rcases p with ⟨o, p⟩
    cases o with
    | none => cases p
    | some i => rfl
  right_inv p := by rcases p with ⟨i, p⟩; rfl

/-- Identify route B of the associativity leaf partition with the original inner total profile. -/
def associativityLeafUnionIsoB (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    partitionedLeafFamily (ColoredOperadObj.AssocInsertion.groupingB O s)
        (associativityLeafBlocksB O A s) ≅
      profileLeafFamily A s.innerData.totalProfile :=
  FiniteFamily.isoOfReindex (associativityLeafUnionEquivB O A s)
    (fun p => by
      rcases p with ⟨o, p⟩
      cases o with
      | none => cases p
      | some i => rfl)

/-- The original leaf-index bijection and its actual color transports
along a full colored profile map, including all nullary profiles. -/
def profileLeafIso (A : W → C) {P Q : ColoredProfile W} (f : P ⟶ Q) :
    profileLeafFamily A P ≅ profileLeafFamily A Q :=
  FiniteFamily.isoOfReindex f.inputEquiv (fun i => congrArg A (f.inputColor_eq i))

/-- The original dependent-sum associator on every original leaf
input in the three-level colored associativity datum. -/
def associativityTotalLeafIso (A : W → C) (s : ColoredAssocData W) :
    profileLeafFamily A s.innerData.totalProfile ≅
      profileLeafFamily A s.outerAfterInnerData.totalProfile :=
  profileLeafIso A s.totalHom

theorem associativityTotalLeafIso_equiv (A : W → C) (s : ColoredAssocData W) :
    (associativityTotalLeafIso A s).hom.equiv = s.totalHom.inputEquiv := rfl

theorem associativityTotalLeafIso_hom (A : W → C) (s : ColoredAssocData W)
    (i : s.branches.index) (j : (s.localData i).inner.index)
    (k : ((s.localData i).inner.obj j).inputs) :
    (associativityTotalLeafIso A s).hom.hom ⟨⟨i, j⟩, k⟩ =
      𝟙 (A (((s.localData i).inner.obj j).inputColor k)) := rfl





end CategoryTheory.Operad.Tensor
end
end
end source_OperadicLeafPartitions

/- Source proof segment: ProfileCoefficientLeaves -/
section source_ProfileCoefficientLeaves
/-!
# Original full-profile coefficient and leaf tensor maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

/-- A full original profile has its original coefficient and all
original leaf inputs, with the original finite input index. -/
def profileOperationFactorsIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (P : ColoredProfile W) :
    (coefficientLeafFamilyFunctor (profileLeafFamily A P)).obj (O.obj P) ≅
      (operationFactorsFunctor O A).obj P :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option P.inputs))
    (fun i => match i with
      | none => Iso.refl _
      | some _ => Iso.refl _)

theorem profileOperationFactorsIso_naturality (O : ColoredSymmetricCollection W C) (A : W → C)
    {P Q : ColoredProfile W} (f : P ⟶ Q) :
    (profileOperationFactorsIso O A P).hom ≫ (operationFactorsFunctor O A).map f =
      coefficientLeafMap (O.map f) (profileLeafIso A f).hom ≫
        (profileOperationFactorsIso O A Q).hom := by
  apply FiniteFamily.Hom_ext
  · ext i
    cases i <;> rfl
  · intro i
    cases i with
    | none =>
      let g : O.obj P ⟶ O.obj Q := O.map f
      change HEq (𝟙 _ ≫ g) (g ≫ 𝟙 _)
      exact heq_of_eq ((Category.id_comp g).trans (Category.comp_id g).symm)
    | some i =>
      let g : A (P.inputColor i) ⟶ A (Q.inputColor (f.inputEquiv i)) :=
        eqToHom (congrArg A (f.inputColor_eq i))
      change HEq (𝟙 _ ≫ g) (g ≫ 𝟙 _)
      exact heq_of_eq ((Category.id_comp g).trans (Category.comp_id g).symm)

theorem substitutionLeavesTargetIso_eq_profile (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    (substitutionLeavesTargetIso O A s).hom =
      (profileOperationFactorsIso O A s.totalProfile).hom := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i <;> rfl

variable [FiniteTensor C]

/-- Identify the tensor of the coefficient and original profile leaves with the operation
summand. -/
def profileCoefficientLeafTensorIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (P : ColoredProfile W) :
    (coefficientLeafTensorFunctor (profileLeafFamily A P)).obj (O.obj P) ≅
      (operationSummandFunctor O A).obj P :=
  (FiniteTensor.tensor (V := C)).mapIso (profileOperationFactorsIso O A P)

/-- The full original profile tensor map retains its original
coefficient map and all original leaf-index/color transports. -/
theorem profileCoefficientLeafTensorIso_naturality (O : ColoredSymmetricCollection W C) (A : W → C)
    {P Q : ColoredProfile W} (f : P ⟶ Q) :
    (profileCoefficientLeafTensorIso O A P).hom ≫ (operationSummandFunctor O A).map f =
      (FiniteTensor.tensor (V := C)).map (coefficientLeafMap (O.map f) (profileLeafIso A f).hom) ≫
        (profileCoefficientLeafTensorIso O A Q).hom := by
  let T := FiniteTensor.tensor (V := C)
  let a := (profileOperationFactorsIso O A P).hom
  let c := (operationFactorsFunctor O A).map f
  let b := coefficientLeafMap (O.map f) (profileLeafIso A f).hom
  let d := (profileOperationFactorsIso O A Q).hom
  have hs : a ≫ c = b ≫ d := profileOperationFactorsIso_naturality O A f
  change T.map a ≫ T.map c = T.map b ≫ T.map d
  exact (T.map_comp a c).symm.trans
    ((congrArg T.map hs).trans (T.map_comp b d))

/-- The original operadic substitution factorization has the actual
full-profile tensor at its target, including every original leaf. -/
theorem operadSubstitutionInputs_profile_factorization (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    operadSubstitutionInputs O A s =
      (FiniteTensor.tensor (V := C)).map (substitutionToLeavesIso O.toCollection A s).hom ≫
        coefficientLeavesNormalization
          ((ColoredOperadObj.substitutionFactors O.toCollection).obj s)
          (profileLeafFamily A s.totalProfile) ≫
        (coefficientLeafTensorFunctor (profileLeafFamily A s.totalProfile)).map (O.subst.app s) ≫
        (profileCoefficientLeafTensorIso O.toCollection A s.totalProfile).hom := by
  have h := operadSubstitutionInputs_factorization O A s
  rw [substitutionLeavesTargetIso_eq_profile] at h
  exact h




end CategoryTheory.Operad.Tensor
end
end
end source_ProfileCoefficientLeaves

/- Source proof segment: SubstitutionLeafFrame -/
section source_SubstitutionLeafFrame
/-!
# The full original two-level colored substitution frame
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

/-- An arbitrary original coefficient grouping on the displayed
root and inner-operation slots of the original substitution datum. -/
@[implicit_reducible]
def substitutionBranchGrouping (s : ColoredSubstitutionData W)
    (K : Option s.inner.index → FiniteFamily C) : FiniteFamily (FiniteFamily C) where
  index := FintypeCat.of (Option s.inner.index)
  obj := K

/-- The root has no leaf block; every inner operation retains its
actual full finite-profile original input family. -/
def substitutionBranchLeaves (A : W → C) (s : ColoredSubstitutionData W) :
    Option s.inner.index → FiniteFamily C :=
  fun i => match i with
    | none => FiniteFamily.empty
    | some i => profileLeafFamily A (s.inner.obj i)

/-- The exact original outer and inner operadic coefficients. -/
def substitutionBranchCoefficients (O : ColoredSymmetricCollection W C)
    (s : ColoredSubstitutionData W) : Option s.inner.index → C :=
  ((ColoredOperadObj.substitutionFactors O).obj s).obj

/-- Identify the original substitution-frame leaf indices with the total-profile inputs. -/
def substitutionFrameLeafEquiv (A : W → C) (s : ColoredSubstitutionData W)
    (K : Option s.inner.index → FiniteFamily C) :
    (partitionedLeafFamily (substitutionBranchGrouping s K)
      (substitutionBranchLeaves A s)).index ≃ s.totalProfile.inputs where
  toFun p := match p with
    | ⟨none, e⟩ => e.elim
    | ⟨some i, p⟩ => ⟨i, p⟩
  invFun p := ⟨some p.1, p.2⟩
  left_inv p := by
    rcases p with ⟨o, p⟩
    cases o with
    | none => cases p
    | some i => rfl
  right_inv p := by rcases p with ⟨i, p⟩; rfl

/-- The exact original total-profile leaf family, with only the
empty root leaf block removed. -/
def substitutionFrameLeafIso (A : W → C) (s : ColoredSubstitutionData W)
    (K : Option s.inner.index → FiniteFamily C) :
    partitionedLeafFamily (substitutionBranchGrouping s K) (substitutionBranchLeaves A s) ≅
      profileLeafFamily A s.totalProfile :=
  FiniteFamily.isoOfReindex (substitutionFrameLeafEquiv A s K)
    (fun p => by
      rcases p with ⟨o, p⟩
      cases o with
      | none => cases p
      | some i => rfl)

/-- The scalar frame retains the original substitution-factor
index and all original coefficient objects. -/
def substitutionFrameCoefficientsIso (O : ColoredSymmetricCollection W C)
    (s : ColoredSubstitutionData W) (K : Option s.inner.index → FiniteFamily C) :
    partitionedScalarCoefficients (substitutionBranchGrouping s K)
        (substitutionBranchCoefficients O s) ≅
      (ColoredOperadObj.substitutionFactors O).obj s :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option s.inner.index)) (fun _ => Iso.refl _)

/-- The root empty-leaf singleton and each original full inner
operation factor family are identified with the original input-first
substitution blocks. -/
def substitutionFrameFactorsIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) (K : Option s.inner.index → FiniteFamily C) :
    partitionedScalarLeaves (substitutionBranchGrouping s K)
        (substitutionBranchLeaves A s) (substitutionBranchCoefficients O s) ≅
      nestedOperationFactors O A s :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option s.inner.index))
    (fun i => match i with
      | none => emptyLeafFamilyIso (O.obj s.outerProfile)
      | some i => profileOperationFactorsIso O A (s.inner.obj i))

/-- Identify the flattened scalar substitution frame with its original
coefficient-and-total-leaf family. -/
def substitutionFrameRawIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) (K : Option s.inner.index → FiniteFamily C) :
    (FiniteFamily.flatten (C := C)).obj
        (partitionedScalarLeaves (substitutionBranchGrouping s K)
          (substitutionBranchLeaves A s) (substitutionBranchCoefficients O s)) ≅
      (FiniteFamily.flatten (C := C)).obj (nestedOperationFactors O A s) :=
  (FiniteFamily.flatten (C := C)).mapIso (substitutionFrameFactorsIso O A s K)

/-- The original coefficient identity and original total-input
bijection on the coefficient-first source family. -/
def substitutionFrameLeafSourceMap (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) (K : Option s.inner.index → FiniteFamily C) :
    coefficientLeavesNested
        (partitionedScalarCoefficients (substitutionBranchGrouping s K)
          (substitutionBranchCoefficients O s))
        (partitionedLeafFamily (substitutionBranchGrouping s K) (substitutionBranchLeaves A s)) ⟶
      coefficientLeavesNested ((ColoredOperadObj.substitutionFactors O).obj s)
        (profileLeafFamily A s.totalProfile) :=
  coefficientLeavesNestedMap (substitutionFrameCoefficientsIso O s K).hom
    (substitutionFrameLeafIso A s K).hom




end CategoryTheory.Operad.Tensor
end
end
end source_SubstitutionLeafFrame

/- Source proof segment: SubstitutionLeafFrameSource -/
section source_SubstitutionLeafFrameSource
/-!
# Exact original source permutation of the full colored substitution frame
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

/-- The original input-first substitution permutation is exactly
the original scalar coefficient/leaf shuffle and original total
profile leaf bijection. This is a comparison of actual source maps. -/
theorem substitutionFrameRaw_source_square (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) (K : Option s.inner.index → FiniteFamily C) :
    (substitutionFrameRawIso O A s K).hom ≫ (substitutionToLeavesIso O A s).hom =
      (partitionedScalarLeavesIso (substitutionBranchGrouping s K)
          (substitutionBranchLeaves A s) (substitutionBranchCoefficients O s)).hom ≫
        (FiniteFamily.flatten (C := C)).map (substitutionFrameLeafSourceMap O A s K) := by
  apply FiniteFamily.Hom_ext
  · ext p
    rcases p with ⟨o, a⟩
    cases o with
    | none =>
      cases a with
      | none => rfl
      | some e => cases e
    | some i => cases a <;> rfl
  · intro p
    rcases p with ⟨o, a⟩
    cases o with
    | none =>
      cases a with
      | none =>
        let X := O.obj s.outerProfile
        change HEq (𝟙 X ≫ 𝟙 X ≫ 𝟙 X ≫ 𝟙 X) (𝟙 X ≫ 𝟙 X)
        exact heq_of_eq (by simp only [Category.id_comp])
      | some e => cases e
    | some i =>
      cases a with
      | none =>
        let X := O.obj (s.inner.obj i)
        change HEq (𝟙 X ≫ 𝟙 X ≫ 𝟙 X ≫ 𝟙 X) (𝟙 X ≫ 𝟙 X)
        exact heq_of_eq (by simp only [Category.id_comp])
      | some k =>
        let X := A ((s.inner.obj i).inputColor k)
        change HEq (𝟙 X ≫ 𝟙 X ≫ 𝟙 X ≫ 𝟙 X) (𝟙 X ≫ 𝟙 X)
        exact heq_of_eq (by simp only [Category.id_comp])



end CategoryTheory.Operad.Tensor
end
end
end source_SubstitutionLeafFrameSource

/- Source proof segment: CoefficientLeafCompositions -/
section source_CoefficientLeafCompositions
@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- Joint original coefficient and leaf maps compose with their
actual coefficient composition and actual finite leaf composition. -/
theorem coefficientLeafMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    {L M N : FiniteFamily C} (l : L ⟶ M) (m : M ⟶ N) :
    coefficientLeafMap f l ≫ coefficientLeafMap g m = coefficientLeafMap (f ≫ g) (l ≫ m) := by
  apply FiniteFamily.Hom_ext
  · ext i
    cases i <;> rfl
  · intro i
    cases i <;> rfl

/-- Apply an original coefficient map after an original joint
coefficient/leaf map; the original leaf map is unchanged. -/
theorem coefficientLeafMap_post {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    {L M : FiniteFamily C} (l : L ⟶ M) :
    coefficientLeafMap f l ≫ (coefficientLeafFamilyFunctor M).map g =
      coefficientLeafMap (f ≫ g) l := by
  rw [← coefficientLeafMap_idLeaves g M, coefficientLeafMap_comp, Category.comp_id]

/-- Apply an original coefficient map before an original joint
coefficient/leaf map; the original leaf map is unchanged. -/
theorem coefficientLeafMap_pre {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    {L M : FiniteFamily C} (l : L ⟶ M) :
    (coefficientLeafFamilyFunctor L).map f ≫ coefficientLeafMap g l =
      coefficientLeafMap (f ≫ g) l := by
  rw [← coefficientLeafMap_idLeaves f L, coefficientLeafMap_comp, Category.id_comp]

end CategoryTheory.Operad.Tensor
end
end source_CoefficientLeafCompositions

/- Source proof segment: OperadicFactorSquares -/
section source_OperadicFactorSquares
@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe u v

/-- The original complete operation factorization follows from its
actual source permutation, normalization, and coefficient-map squares. -/
theorem factorFullOperationFromSourceSquares {C : Type u} [Category.{v} C]
    {X R S A B D E F G : C}
    (r : X ⟶ R) (q : R ⟶ S) (u : S ⟶ A) (v : R ⟶ B) (j : B ⟶ A)
    (nA : A ⟶ D) (nB : B ⟶ E) (z : E ⟶ D) (g : D ⟶ F) (h : E ⟶ F)
    (p : F ⟶ G) (op : S ⟶ G)
    (ho : op = u ≫ nA ≫ g ≫ p) (hs : q ≫ u = v ≫ j)
    (hn : j ≫ nA = nB ≫ z) (hg : z ≫ g = h) :
    (r ≫ q) ≫ op = (r ≫ v ≫ nB) ≫ h ≫ p := by
  rw [ho]
  simp only [Category.assoc]
  rw [← Category.assoc q u, hs]
  simp only [Category.assoc]
  rw [← Category.assoc j nA, hn]
  simp only [Category.assoc]
  rw [← Category.assoc z g, hg]

end CategoryTheory.Operad.Tensor
end
end source_OperadicFactorSquares

/- Source proof segment: SubstitutionLeafFrameFactorization -/
section source_SubstitutionLeafFrameFactorization
/-!
# Actual operadic substitution on the full original scalar branch frame
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The actual scalar branch tensor is flattened and identified
with the full original input-first operadic substitution source. -/
def substitutionFrameAssemblyIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) (K : Option s.inner.index → FiniteFamily C) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
          (partitionedScalarLeaves (substitutionBranchGrouping s K)
            (substitutionBranchLeaves A s) (substitutionBranchCoefficients O s))) ≅
      algebraSubstitutionSource O A s :=
  ((FiniteTensor.flattenIso (V := C)).app
      (partitionedScalarLeaves (substitutionBranchGrouping s K)
        (substitutionBranchLeaves A s) (substitutionBranchCoefficients O s))).symm ≪≫
    (FiniteTensor.tensor (V := C)).mapIso (substitutionFrameRawIso O A s K)

theorem substitutionFrameAssemblyIso_hom (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) (K : Option s.inner.index → FiniteFamily C) :
    (substitutionFrameAssemblyIso O A s K).hom =
      (FiniteTensor.flattenIso (V := C)).inv.app
          (partitionedScalarLeaves (substitutionBranchGrouping s K)
            (substitutionBranchLeaves A s) (substitutionBranchCoefficients O s)) ≫
        (FiniteTensor.tensor (V := C)).map (substitutionFrameRawIso O A s K).hom := by
  rfl

/-- The original coefficient-factor identification is followed by
the original operad substitution; no algebra or monad law is a premise. -/
def substitutionFrameCoefficient (O : ColoredOperadObj W C) (s : ColoredSubstitutionData W)
    (K : Option s.inner.index → FiniteFamily C) :
    (FiniteTensor.tensor (V := C)).obj
        (partitionedScalarCoefficients (substitutionBranchGrouping s K)
          (substitutionBranchCoefficients O.toCollection s)) ⟶
      O.toCollection.obj s.totalProfile :=
  (FiniteTensor.tensor (V := C)).map (substitutionFrameCoefficientsIso O.toCollection s K).hom ≫
    O.subst.app s

/-- Original operadic substitution on the actual full scalar branch
frame factors through the original coefficient substitution and
the original total-profile leaf bijection. -/
theorem operadSubstitutionInputs_frame_factorization (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) (K : Option s.inner.index → FiniteFamily C) :
    (substitutionFrameAssemblyIso O.toCollection A s K).hom ≫ operadSubstitutionInputs O A s =
      (partitionedScalarLeavesDistributionIso (substitutionBranchGrouping s K)
          (substitutionBranchLeaves A s) (substitutionBranchCoefficients O.toCollection s)).hom ≫
        (FiniteTensor.tensor (V := C)).map
          (coefficientLeafMap (substitutionFrameCoefficient O s K) (substitutionFrameLeafIso
            A s K).hom) ≫
        (profileCoefficientLeafTensorIso O.toCollection A s.totalProfile).hom := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let N := substitutionBranchGrouping s K
  let L := substitutionBranchLeaves A s
  let B := substitutionBranchCoefficients O.toCollection s
  let E := partitionedScalarLeaves N L B
  let L' := partitionedLeafFamily N L
  let C' := partitionedScalarCoefficients N B
  let C'' := (ColoredOperadObj.substitutionFactors O.toCollection).obj s
  let r := (FiniteTensor.flattenIso (V := C)).inv.app E
  let q₀ := (substitutionFrameRawIso O.toCollection A s K).hom
  let u₀ := (substitutionToLeavesIso O.toCollection A s).hom
  let v₀ := (partitionedScalarLeavesIso N L B).hom
  let j₀ := F.map (substitutionFrameLeafSourceMap O.toCollection A s K)
  let q := T.map q₀
  let u := T.map u₀
  let v := T.map v₀
  let j := T.map j₀
  let nA := coefficientLeavesNormalization C'' (profileLeafFamily A s.totalProfile)
  let nB := coefficientLeavesNormalization C' L'
  let k := (substitutionFrameCoefficientsIso O.toCollection s K).hom
  let l := (substitutionFrameLeafIso A s K).hom
  let γ : T.obj C'' ⟶ O.toCollection.obj s.totalProfile := O.subst.app s
  let z₀ := coefficientLeafMap (T.map k) l
  let z := T.map z₀
  let g₀ := (coefficientLeafFamilyFunctor (profileLeafFamily A s.totalProfile)).map γ
  let g := T.map g₀
  let h := T.map (coefficientLeafMap (substitutionFrameCoefficient O s K) l)
  let p := (profileCoefficientLeafTensorIso O.toCollection A s.totalProfile).hom
  let op := operadSubstitutionInputs O A s
  have ho : op = u ≫ nA ≫ g ≫ p := operadSubstitutionInputs_profile_factorization O A s
  have hs₀ : q₀ ≫ u₀ = v₀ ≫ j₀ := substitutionFrameRaw_source_square O.toCollection A s K
  have hs : q ≫ u = v ≫ j :=
    (T.map_comp q₀ u₀).symm.trans ((congrArg T.map hs₀).trans (T.map_comp v₀ j₀))
  have hn := coefficientLeavesNormalization_naturality k l
  change j ≫ nA = nB ≫ z at hn
  have hg₀ : z₀ ≫ g₀ = coefficientLeafMap (substitutionFrameCoefficient O s K) l :=
    coefficientLeafMap_post (T.map k) γ l
  have hg : z ≫ g = h := (T.map_comp z₀ g₀).symm.trans (congrArg T.map hg₀)
  rw [substitutionFrameAssemblyIso_hom, partitionedScalarLeavesDistributionIso_hom]
  change (r ≫ q) ≫ op = (r ≫ v ≫ nB) ≫ h ≫ p
  exact factorFullOperationFromSourceSquares r q u v j nA nB z g h p op ho hs hn hg



end CategoryTheory.Operad.Tensor
end
end
end source_SubstitutionLeafFrameFactorization

/- Source proof segment: BranchOuterSquares -/
section source_BranchOuterSquares
@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe u v

theorem branchOuterFactorizationFromSquares {C : Type u} [Category.{v} C]
    {X P Q A B D S U Y : C}
    (p : X ⟶ P) (n : P ⟶ Q) (u : Q ⟶ U)
    (a : X ⟶ A) (b : A ⟶ B) (d : B ⟶ U)
    (assembly : B ⟶ S) (op : S ⟶ Y) (h : U ⟶ D) (target : D ⟶ Y) (c : Q ⟶ D)
    (ha : p ≫ n ≫ u = a ≫ b ≫ d) (ho : assembly ≫ op = d ≫ h ≫ target)
    (hc : u ≫ h = c) :
    a ≫ b ≫ assembly ≫ op = p ≫ n ≫ c ≫ target := by
  rw [ho]
  have hs := congrArg (fun g => g ≫ h ≫ target) ha.symm
  simp only [Category.assoc] at hs
  rw [hs, ← Category.assoc u h, hc]

end CategoryTheory.Operad.Tensor
end
end source_BranchOuterSquares

/- Source proof segment: FullSubstitutionPartition -/
section source_FullSubstitutionPartition
/-!
# Full original branch substitutions followed by the original outer substitution
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original coefficient route evaluates the actual coefficient
grouping, applies every original branch coefficient map, and performs
the original outer operadic substitution. -/
def substitutionBranchCoefficientRoute (O : ColoredOperadObj W C)
    (s : ColoredSubstitutionData W) (K : Option s.inner.index → FiniteFamily C)
    (g : ∀ i, (FiniteTensor.tensor (V := C)).obj (K i) ⟶ substitutionBranchCoefficients
      O.toCollection s i) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.flatten (C := C)).obj (substitutionBranchGrouping s K)) ⟶
      O.toCollection.obj s.totalProfile :=
  (FiniteTensor.flattenIso (V := C)).hom.app (substitutionBranchGrouping s K) ≫
    (FiniteTensor.tensor (V := C)).map
      (partitionedCoefficientMap (substitutionBranchGrouping s K)
        (substitutionBranchCoefficients O.toCollection s) g) ≫
      substitutionFrameCoefficient O s K

/-- The actual branchwise full coefficient/leaf maps are assembled
into the original input-first outer substitution source and followed
by the original `operadSubstitutionInputs` map. -/
def fullSubstitutionPartitionRoute (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) (K : Option s.inner.index → FiniteFamily C)
    (g : ∀ i, (FiniteTensor.tensor (V := C)).obj (K i) ⟶ substitutionBranchCoefficients
      O.toCollection s i) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.flatten (C := C)).obj
          ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
            (partitionedCoefficientLeavesTriple (substitutionBranchGrouping s K)
              (substitutionBranchLeaves A s)))) ⟶
      (operationSummandFunctor O.toCollection A).obj s.totalProfile :=
  (FiniteTensor.flattenIso (V := C)).hom.app
      ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
        (partitionedCoefficientLeavesTriple (substitutionBranchGrouping s K)
          (substitutionBranchLeaves A s))) ≫
    (FiniteTensor.tensor (V := C)).map
      (partitionedCoefficientLeavesActionMap (substitutionBranchGrouping s K)
        (substitutionBranchLeaves A s) (substitutionBranchCoefficients O.toCollection s) g) ≫
    (substitutionFrameAssemblyIso O.toCollection A s K).hom ≫ operadSubstitutionInputs O A s

/-- Complete original branch substitutions and the original outer
substitution agree with the original coefficient route and every
retained original total-profile leaf. No associativity outcome is assumed. -/
theorem fullSubstitutionPartitionRoute_factorization (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) (K : Option s.inner.index → FiniteFamily C)
    (g : ∀ i, (FiniteTensor.tensor (V := C)).obj (K i) ⟶ substitutionBranchCoefficients
      O.toCollection s i) :
    fullSubstitutionPartitionRoute O A s K g =
      (FiniteTensor.tensor (V := C)).map
          (partitionedCoefficientLeavesSourceIso (substitutionBranchGrouping s K)
            (substitutionBranchLeaves A s)).hom ≫
        coefficientLeavesNormalization
          ((FiniteFamily.flatten (C := C)).obj (substitutionBranchGrouping s K))
          (partitionedLeafFamily (substitutionBranchGrouping s K) (substitutionBranchLeaves A s)) ≫
        (FiniteTensor.tensor (V := C)).map
          (coefficientLeafMap (substitutionBranchCoefficientRoute O s K g)
            (substitutionFrameLeafIso A s K).hom) ≫
        (profileCoefficientLeafTensorIso O.toCollection A s.totalProfile).hom := by
  let T := FiniteTensor.tensor (V := C)
  let N := substitutionBranchGrouping s K
  let L := substitutionBranchLeaves A s
  let B := substitutionBranchCoefficients O.toCollection s
  let L' := partitionedLeafFamily N L
  let coeffFirst := (FiniteTensor.flattenIso (V := C)).hom.app N ≫
    T.map (partitionedCoefficientMap N B g)
  let p := T.map (partitionedCoefficientLeavesSourceIso N L).hom
  let n := coefficientLeavesNormalization ((FiniteFamily.flatten (C := C)).obj N) L'
  let u := (coefficientLeafTensorFunctor L').map coeffFirst
  let a := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
      (partitionedCoefficientLeavesTriple N L))
  let b := T.map (partitionedCoefficientLeavesActionMap N L B g)
  let d := (partitionedScalarLeavesDistributionIso N L B).hom
  let assembly := (substitutionFrameAssemblyIso O.toCollection A s K).hom
  let op := operadSubstitutionInputs O A s
  let coeff := substitutionFrameCoefficient O s K
  let leaf := (substitutionFrameLeafIso A s K).hom
  let h := T.map (coefficientLeafMap coeff leaf)
  let target := (profileCoefficientLeafTensorIso O.toCollection A s.totalProfile).hom
  let c := T.map (coefficientLeafMap (substitutionBranchCoefficientRoute O s K g) leaf)
  have ha : p ≫ n ≫ u = a ≫ b ≫ d := partitionedCoefficientLeaves_action N L B g
  have ho : assembly ≫ op = d ≫ h ≫ target := operadSubstitutionInputs_frame_factorization O A s K
  have hroute : coeffFirst ≫ coeff = substitutionBranchCoefficientRoute O s K g :=
    Category.assoc ((FiniteTensor.flattenIso (V := C)).hom.app N)
      (T.map (partitionedCoefficientMap N B g)) coeff
  have hc₀ : (coefficientLeafFamilyFunctor L').map coeffFirst ≫ coefficientLeafMap coeff leaf =
      coefficientLeafMap (substitutionBranchCoefficientRoute O s K g) leaf :=
    (coefficientLeafMap_pre coeffFirst coeff leaf).trans
      (congrArg (fun h => coefficientLeafMap h leaf) hroute)
  have hc : u ≫ h = c :=
    (T.map_comp _ _).symm.trans (congrArg T.map hc₀)
  exact branchOuterFactorizationFromSquares p n u a b d assembly op h target c ha ho hc



end CategoryTheory.Operad.Tensor
end
end
end source_FullSubstitutionPartition

/- Source proof segment: CoefficientLeavesNestedIsomorphisms -/
section source_CoefficientLeavesNestedIsomorphisms
/-!
# Actual isomorphisms of coefficient blocks and original leaf families
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

theorem coefficientLeavesNestedMap_id (K L : FiniteFamily C) :
    coefficientLeavesNestedMap (𝟙 K) (𝟙 L) = 𝟙 (coefficientLeavesNested K L) := by
  apply FiniteFamily.Hom_ext
  · ext i
    cases i <;> rfl
  · intro i
    cases i with
    | none => rfl
    | some i => exact heq_of_eq ((FiniteFamily.singleton (C := C)).map_id (L.obj i))

theorem coefficientLeavesNestedMap_comp {K N P L M Q : FiniteFamily C}
    (k : K ⟶ N) (k' : N ⟶ P) (l : L ⟶ M) (l' : M ⟶ Q) :
    coefficientLeavesNestedMap k l ≫ coefficientLeavesNestedMap k' l' =
      coefficientLeavesNestedMap (k ≫ k') (l ≫ l') := by
  apply FiniteFamily.Hom_ext
  · ext i
    cases i <;> rfl
  · intro i
    cases i with
    | none => rfl
    | some i =>
      exact heq_of_eq ((FiniteFamily.singleton (C := C)).map_comp
        (l.hom i) (l'.hom (l.equiv i))).symm

/-- Original coefficient and leaf isomorphisms induce an actual
isomorphism of complete nested coefficient and leaf source blocks. -/
def coefficientLeavesNestedIso {K N L M : FiniteFamily C} (k : K ≅ N) (l : L ≅ M) :
    coefficientLeavesNested K L ≅ coefficientLeavesNested N M where
  hom := coefficientLeavesNestedMap k.hom l.hom
  inv := coefficientLeavesNestedMap k.inv l.inv
  hom_inv_id := by
    rw [coefficientLeavesNestedMap_comp, k.hom_inv_id, l.hom_inv_id,
      coefficientLeavesNestedMap_id]
  inv_hom_id := by
    rw [coefficientLeavesNestedMap_comp, k.inv_hom_id, l.inv_hom_id,
      coefficientLeavesNestedMap_id]

theorem coefficientLeavesNestedIso_hom {K N L M : FiniteFamily C} (k : K ≅ N) (l : L ≅ M) :
    (coefficientLeavesNestedIso k l).hom = coefficientLeavesNestedMap k.hom l.hom := rfl

/-- The actual complete raw factor isomorphism retains the
original coefficient and leaf-index permutations and component maps. -/
def coefficientLeavesRawIso {K N L M : FiniteFamily C} (k : K ≅ N) (l : L ≅ M) :
    (FiniteFamily.flatten (C := C)).obj (coefficientLeavesNested K L) ≅
      (FiniteFamily.flatten (C := C)).obj (coefficientLeavesNested N M) :=
  (FiniteFamily.flatten (C := C)).mapIso (coefficientLeavesNestedIso k l)



end CategoryTheory.Operad.Tensor
end
end
end source_CoefficientLeavesNestedIsomorphisms

/- Source proof segment: CanonicalSourceSquares -/
section source_CanonicalSourceSquares
@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe u v

theorem cancelLeadingIsoPair {C : Type u} [Category.{v} C]
    {X Y A B : C} (f : X ⟶ Y) (g : Y ⟶ X) (a : X ⟶ A) (b : A ⟶ B)
    (h : f ≫ g = 𝟙 X) : f ≫ g ≫ a ≫ b = a ≫ b := by
  rw [← Category.assoc f g, h, Category.id_comp]

/-- An actual source isomorphism, the original profile relabelling,
and the original coefficient/leaf squares determine the complete
operation on its common canonical tensor source. -/
theorem canonicalFactorizationFromSquares {C : Type u} [Category.{v} C]
    {X S R P Q A B Y Z : C}
    (e : X ≅ S) (op : X ⟶ A) (f : A ⟶ Z)
    (r : X ⟶ R) (nR : R ⟶ P) (j₁ : P ⟶ B) (pA : B ⟶ A)
    (j₂ : B ⟶ Y) (pZ : Y ⟶ Z) (a : P ⟶ Y)
    (nS : S ⟶ Q) (b : P ⟶ Q) (c : Q ⟶ Y)
    (ho : op = r ≫ nR ≫ j₁ ≫ pA) (hf : pA ≫ f = j₂ ≫ pZ)
    (hj : j₁ ≫ j₂ = a) (he : e.hom ≫ nS = r ≫ nR ≫ b) (hc : b ≫ c = a) :
    e.inv ≫ op ≫ f = nS ≫ c ≫ pZ := by
  have hleft : e.hom ≫ nS ≫ c ≫ pZ = r ≫ nR ≫ a ≫ pZ := by
    rw [← Category.assoc e.hom nS, he]
    simp only [Category.assoc]
    rw [← Category.assoc b c, hc]
  have hright : op ≫ f = r ≫ nR ≫ a ≫ pZ := by
    rw [ho]
    simp only [Category.assoc]
    rw [hf, ← Category.assoc j₁ j₂, hj]
  have h := hleft.trans hright.symm
  rw [← h, ← Category.assoc e.inv e.hom, e.inv_hom_id, Category.id_comp]

end CategoryTheory.Operad.Tensor
end
end source_CanonicalSourceSquares

/- Source proof segment: CanonicalSubstitutionSource -/
section source_CanonicalSubstitutionSource
/-!
# Original full substitutions on a common coefficient and leaf tensor source
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original full raw branch factors are identified with a
chosen original coefficient family and the original relabelled
total-profile leaves. Both source permutations are explicit. -/
def substitutionCanonicalSourceIso (A : W → C)
    (s : ColoredSubstitutionData W) (K : Option s.inner.index → FiniteFamily C)
    {Z : FiniteFamily C} (k : (FiniteFamily.flatten (C := C)).obj
      (substitutionBranchGrouping s K) ≅ Z)
    {P : ColoredProfile W} (f : s.totalProfile ⟶ P) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.flatten (C := C)).obj
          ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
            (partitionedCoefficientLeavesTriple (substitutionBranchGrouping s K)
              (substitutionBranchLeaves A s)))) ≅
      (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.flatten (C := C)).obj (coefficientLeavesNested Z (profileLeafFamily A P))) :=
  (FiniteTensor.tensor (V := C)).mapIso
    (partitionedCoefficientLeavesSourceIso (substitutionBranchGrouping s K)
      (substitutionBranchLeaves A s) ≪≫
      coefficientLeavesRawIso k (substitutionFrameLeafIso A s K ≪≫ profileLeafIso A f))

/-- The original branch and outer substitutions are assembled,
precomposed with their actual common-source isomorphism, and
postcomposed with the original full-profile relabelling. -/
def canonicalSubstitutionRoute (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) (K : Option s.inner.index → FiniteFamily C)
    (g : ∀ i, (FiniteTensor.tensor (V := C)).obj (K i) ⟶ substitutionBranchCoefficients
      O.toCollection s i)
    {Z : FiniteFamily C} (k : (FiniteFamily.flatten (C := C)).obj
      (substitutionBranchGrouping s K) ≅ Z)
    {P : ColoredProfile W} (f : s.totalProfile ⟶ P) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.flatten (C := C)).obj (coefficientLeavesNested Z (profileLeafFamily A P))) ⟶
      (operationSummandFunctor O.toCollection A).obj P :=
  (substitutionCanonicalSourceIso A s K k f).inv ≫
    fullSubstitutionPartitionRoute O A s K g ≫ (operationSummandFunctor O.toCollection A).map f

/-- The original coefficient route on the selected common source. -/
def canonicalSubstitutionCoefficient (O : ColoredOperadObj W C)
    (s : ColoredSubstitutionData W) (K : Option s.inner.index → FiniteFamily C)
    (g : ∀ i, (FiniteTensor.tensor (V := C)).obj (K i) ⟶ substitutionBranchCoefficients
      O.toCollection s i)
    {Z : FiniteFamily C} (k : (FiniteFamily.flatten (C := C)).obj
      (substitutionBranchGrouping s K) ≅ Z)
    {P : ColoredProfile W} (f : s.totalProfile ⟶ P) :
    (FiniteTensor.tensor (V := C)).obj Z ⟶ O.toCollection.obj P :=
  (FiniteTensor.tensor (V := C)).map k.inv ≫ substitutionBranchCoefficientRoute O s K g
    ≫ O.toCollection.map f

/-- The complete original substitutions on the actual common raw
tensor source factor through the original coefficient route and all
original relabelled profile leaves. Every source comparison is proved
from finite tensor coherence and original finite-family maps. -/
theorem canonicalSubstitutionRoute_factorization (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) (K : Option s.inner.index → FiniteFamily C)
    (g : ∀ i, (FiniteTensor.tensor (V := C)).obj (K i) ⟶ substitutionBranchCoefficients
      O.toCollection s i)
    {Z : FiniteFamily C} (k : (FiniteFamily.flatten (C := C)).obj
      (substitutionBranchGrouping s K) ≅ Z)
    {P : ColoredProfile W} (f : s.totalProfile ⟶ P) :
    canonicalSubstitutionRoute O A s K g k f =
      coefficientLeavesNormalization Z (profileLeafFamily A P) ≫
        (coefficientLeafTensorFunctor (profileLeafFamily A P)).map
          (canonicalSubstitutionCoefficient O s K g k f) ≫
        (profileCoefficientLeafTensorIso O.toCollection A P).hom := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let N := substitutionBranchGrouping s K
  let L := substitutionBranchLeaves A s
  let L' := partitionedLeafFamily N L
  let Γ : T.obj (F.obj N) ⟶ O.toCollection.obj s.totalProfile :=
    substitutionBranchCoefficientRoute O s K g
  let lf := substitutionFrameLeafIso A s K ≪≫ profileLeafIso A f
  let p₀ := (partitionedCoefficientLeavesSourceIso N L).hom
  let e₀ := (coefficientLeavesRawIso k lf).hom
  let e := substitutionCanonicalSourceIso A s K k f
  let op := fullSubstitutionPartitionRoute O A s K g
  let smap := (operationSummandFunctor O.toCollection A).map f
  let r := T.map p₀
  let nR := coefficientLeavesNormalization (F.obj N) L'
  let j₁₀ := coefficientLeafMap Γ (substitutionFrameLeafIso A s K).hom
  let j₁ := T.map j₁₀
  let pA := (profileCoefficientLeafTensorIso O.toCollection A s.totalProfile).hom
  let j₂₀ := coefficientLeafMap (O.toCollection.map f) (profileLeafIso A f).hom
  let j₂ := T.map j₂₀
  let pZ := (profileCoefficientLeafTensorIso O.toCollection A P).hom
  let a₀ := coefficientLeafMap (Γ ≫ O.toCollection.map f) lf.hom
  let a := T.map a₀
  let nS := coefficientLeavesNormalization Z (profileLeafFamily A P)
  let b₀ := coefficientLeafMap (T.map k.hom) lf.hom
  let b := T.map b₀
  let c := (coefficientLeafTensorFunctor (profileLeafFamily A P)).map
    (canonicalSubstitutionCoefficient O s K g k f)
  have ho : op = r ≫ nR ≫ j₁ ≫ pA := fullSubstitutionPartitionRoute_factorization O A s K g
  have hf : pA ≫ smap = j₂ ≫ pZ := profileCoefficientLeafTensorIso_naturality O.toCollection A f
  have hj₀ : j₁₀ ≫ j₂₀ = a₀ := coefficientLeafMap_comp Γ (O.toCollection.map f)
    (substitutionFrameLeafIso A s K).hom (profileLeafIso A f).hom
  have hj : j₁ ≫ j₂ = a := (T.map_comp _ _).symm.trans (congrArg T.map hj₀)
  have hn := coefficientLeavesNormalization_naturality k.hom lf.hom
  change T.map e₀ ≫ nS = nR ≫ b at hn
  have he₀ : e.hom = r ≫ T.map e₀ := T.map_comp p₀ e₀
  have he : e.hom ≫ nS = r ≫ nR ≫ b :=
    (congrArg (· ≫ nS) he₀).trans
      ((Category.assoc _ _ _).trans (congrArg (r ≫ ·) hn))
  have hki : T.map k.hom ≫ T.map k.inv = 𝟙 _ :=
    (T.map_comp _ _).symm.trans ((congrArg T.map k.hom_inv_id).trans (T.map_id _))
  have hcoeff : T.map k.hom ≫ canonicalSubstitutionCoefficient O s K g k f = Γ ≫
    O.toCollection.map f :=
    cancelLeadingIsoPair (T.map k.hom) (T.map k.inv) Γ (O.toCollection.map f) hki
  have hc₀ : b₀ ≫ (coefficientLeafFamilyFunctor (profileLeafFamily A P)).map
      (canonicalSubstitutionCoefficient O s K g k f) = a₀ :=
    (coefficientLeafMap_post (T.map k.hom) (canonicalSubstitutionCoefficient O s K g k f)
      lf.hom).trans
      (congrArg (fun h => coefficientLeafMap h lf.hom) hcoeff)
  have hc : b ≫ c = a := (T.map_comp _ _).symm.trans (congrArg T.map hc₀)
  exact canonicalFactorizationFromSquares e op smap r nR j₁ pA j₂ pZ a nS b c ho hf hj he hc



end CategoryTheory.Operad.Tensor
end
end
end source_CanonicalSubstitutionSource

/- Source proof segment: AssociativityBranchData -/
section source_AssociativityBranchData
/-!
# Original coefficient blocks and branch maps in colored operadic associativity
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

/-- The original coefficient blocks along the outer-after-inner associativity route. -/
def associativityCoefficientBlocksA (O : ColoredSymmetricCollection W C) (s : ColoredAssocData W) :
    Option s.outerAfterInnerData.inner.index → FiniteFamily C :=
  (ColoredOperadObj.AssocInsertion.groupingA O s).obj

/-- The original coefficient blocks along the inner associativity route. -/
def associativityCoefficientBlocksB (O : ColoredSymmetricCollection W C) (s : ColoredAssocData W) :
    Option s.innerData.inner.index → FiniteFamily C :=
  (ColoredOperadObj.AssocInsertion.groupingB O s).obj

theorem associativityBranchGroupingA (O : ColoredSymmetricCollection W C) (s : ColoredAssocData W) :
    substitutionBranchGrouping s.outerAfterInnerData (associativityCoefficientBlocksA O s) =
      ColoredOperadObj.AssocInsertion.groupingA O s := rfl

theorem associativityBranchGroupingB (O : ColoredSymmetricCollection W C) (s : ColoredAssocData W) :
    substitutionBranchGrouping s.innerData (associativityCoefficientBlocksB O s) =
      ColoredOperadObj.AssocInsertion.groupingB O s := rfl

/-- The actual original finite coefficient permutation connecting
the two source groupings is invertible, with all objects unchanged. -/
def associativityCoefficientIso (O : ColoredSymmetricCollection W C) (s : ColoredAssocData W) :
    ColoredOperadObj.AssocInsertion.flattenedGroupingA O s ≅
      ColoredOperadObj.AssocInsertion.flattenedGroupingB O s :=
  FiniteFamily.isoOfReindex
    (ColoredOperadObj.AssocInsertion.flattenAToFlattenBHom O s).equiv
    (fun p => by
      rcases p with ⟨o, a⟩
      cases o with
      | none => cases a; rfl
      | some i => cases a <;> rfl)

theorem associativityCoefficientIso_hom (O : ColoredSymmetricCollection W C) (s :
  ColoredAssocData W) :
    (associativityCoefficientIso O s).hom =
      ColoredOperadObj.AssocInsertion.flattenAToFlattenBHom O s := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro p
    rcases p with ⟨o, a⟩
    cases o with
    | none => cases a; rfl
    | some i => cases a <;> rfl

variable [FiniteTensor C]

/-- The original local substitutions and original root singleton
unitor on the branch-first associativity grouping. -/
def associativityCoefficientMapsA (O : ColoredOperadObj W C) (s : ColoredAssocData W) :
    ∀ i, (FiniteTensor.tensor (V := C)).obj (associativityCoefficientBlocksA O.toCollection s i) ⟶
      substitutionBranchCoefficients O.toCollection s.outerAfterInnerData i :=
  (ColoredOperadObj.AssocInsertion.groupingAToFactorsHom O.toCollection O.subst s).hom

/-- The original middle substitution and original innermost
coefficient singleton unitors on the flattened associativity grouping. -/
def associativityCoefficientMapsB (O : ColoredOperadObj W C) (s : ColoredAssocData W) :
    ∀ i, (FiniteTensor.tensor (V := C)).obj (associativityCoefficientBlocksB O.toCollection s i) ⟶
      substitutionBranchCoefficients O.toCollection s.innerData i :=
  (ColoredOperadObj.AssocInsertion.groupingBToFactorsHom O.toCollection O.subst s).hom

theorem associativityCoefficientFactorMapA (O : ColoredOperadObj W C) (s : ColoredAssocData W) :
    partitionedCoefficientMap
        (substitutionBranchGrouping s.outerAfterInnerData (associativityCoefficientBlocksA
          O.toCollection s))
        (substitutionBranchCoefficients O.toCollection s.outerAfterInnerData)
        (associativityCoefficientMapsA O s) ≫
      (substitutionFrameCoefficientsIso O.toCollection s.outerAfterInnerData
        (associativityCoefficientBlocksA O.toCollection s)).hom =
      ColoredOperadObj.AssocInsertion.groupingAToFactorsHom O.toCollection O.subst s := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    let g : (FiniteTensor.tensor (V := C)).obj (associativityCoefficientBlocksA
      O.toCollection s i) ⟶
      substitutionBranchCoefficients O.toCollection s.outerAfterInnerData i :=
        associativityCoefficientMapsA O s i
    change HEq (g ≫ 𝟙 _) g
    exact heq_of_eq (Category.comp_id g)

theorem associativityCoefficientFactorMapB (O : ColoredOperadObj W C) (s : ColoredAssocData W) :
    partitionedCoefficientMap
        (substitutionBranchGrouping s.innerData (associativityCoefficientBlocksB O.toCollection s))
        (substitutionBranchCoefficients O.toCollection s.innerData)
        (associativityCoefficientMapsB O s) ≫
      (substitutionFrameCoefficientsIso O.toCollection s.innerData
        (associativityCoefficientBlocksB O.toCollection s)).hom =
      ColoredOperadObj.AssocInsertion.groupingBToFactorsHom O.toCollection O.subst s := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    let g : (FiniteTensor.tensor (V := C)).obj (associativityCoefficientBlocksB
      O.toCollection s i) ⟶
      substitutionBranchCoefficients O.toCollection s.innerData i :=
        associativityCoefficientMapsB O s i
    change HEq (g ≫ 𝟙 _) g
    exact heq_of_eq (Category.comp_id g)





end CategoryTheory.Operad.Tensor
end
end
end source_AssociativityBranchData

/- Source proof segment: OperadicCoefficientSquares -/
section source_OperadicCoefficientSquares
@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe u v u' v'

theorem mapCoefficientsIntoSubstitution {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D] (F : C ⥤ D)
    {X Y Z : C} {A B : D} (a : A ⟶ F.obj X)
    (k : X ⟶ Y) (l : Y ⟶ Z) (m : X ⟶ Z) (g : F.obj Z ⟶ B)
    (h : k ≫ l = m) :
    a ≫ F.map k ≫ F.map l ≫ g = a ≫ F.map m ≫ g := by
  rw [← Category.assoc (F.map k) (F.map l), ← F.map_comp, h]

theorem postcomposeTripleCoefficient {C : Type u} [Category.{v} C]
    {X Y A B P Q : C} (r : X ⟶ Y) (a : Y ⟶ A) (b : A ⟶ B)
    (g : B ⟶ P) (m : P ⟶ Q) (f : Y ⟶ P) (hf : f = a ≫ b ≫ g) :
    r ≫ f ≫ m = r ≫ a ≫ b ≫ g ≫ m := by
  rw [hf]
  simp only [Category.assoc]

end CategoryTheory.Operad.Tensor
end
end source_OperadicCoefficientSquares

/- Source proof segment: AssociativityCoefficientRoutes -/
section source_AssociativityCoefficientRoutes
/-!
# The complete branch coefficient routes are the original operad associativity routes
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

theorem associativityBranchCoefficientRouteA (O : ColoredOperadObj W C) (s : ColoredAssocData W) :
    substitutionBranchCoefficientRoute O s.outerAfterInnerData
        (associativityCoefficientBlocksA O.toCollection s) (associativityCoefficientMapsA O s) =
      ColoredOperadObj.associativityRouteA O.toCollection O.subst s := by
  let T := FiniteTensor.tensor (V := C)
  let N := ColoredOperadObj.AssocInsertion.groupingA O.toCollection s
  let a : T.obj ((FiniteFamily.flatten (C := C)).obj N) ⟶ T.obj ((FiniteFamily.map T).obj N) :=
    (FiniteTensor.flattenIso (V := C)).hom.app N
  let k := partitionedCoefficientMap
    (substitutionBranchGrouping s.outerAfterInnerData (associativityCoefficientBlocksA
      O.toCollection s))
    (substitutionBranchCoefficients O.toCollection s.outerAfterInnerData)
      (associativityCoefficientMapsA O s)
  let l := (substitutionFrameCoefficientsIso O.toCollection s.outerAfterInnerData
    (associativityCoefficientBlocksA O.toCollection s)).hom
  let m := ColoredOperadObj.AssocInsertion.groupingAToFactorsHom O.toCollection O.subst s
  let γ : T.obj ((ColoredOperadObj.substitutionFactors O.toCollection).obj s.outerAfterInnerData) ⟶
    O.toCollection.obj s.outerAfterInnerData.totalProfile := O.subst.app s.outerAfterInnerData
  have h : k ≫ l = m := associativityCoefficientFactorMapA O s
  change a ≫ T.map k ≫ T.map l ≫ γ = a ≫ T.map m ≫ γ
  exact mapCoefficientsIntoSubstitution T a k l m γ h

theorem associativityBranchCoefficientRouteB_prefix (O : ColoredOperadObj W C) (s :
  ColoredAssocData W) :
    substitutionBranchCoefficientRoute O s.innerData
        (associativityCoefficientBlocksB O.toCollection s) (associativityCoefficientMapsB O s) =
      (FiniteTensor.flattenIso (V := C)).hom.app (ColoredOperadObj.AssocInsertion.groupingB
        O.toCollection s) ≫
        (FiniteTensor.tensor (V := C)).map
          (ColoredOperadObj.AssocInsertion.groupingBToFactorsHom O.toCollection O.subst s) ≫
        O.subst.app s.innerData := by
  let T := FiniteTensor.tensor (V := C)
  let N := ColoredOperadObj.AssocInsertion.groupingB O.toCollection s
  let a : T.obj ((FiniteFamily.flatten (C := C)).obj N) ⟶ T.obj ((FiniteFamily.map T).obj N) :=
    (FiniteTensor.flattenIso (V := C)).hom.app N
  let k := partitionedCoefficientMap
    (substitutionBranchGrouping s.innerData (associativityCoefficientBlocksB O.toCollection s))
    (substitutionBranchCoefficients O.toCollection s.innerData) (associativityCoefficientMapsB O s)
  let l := (substitutionFrameCoefficientsIso O.toCollection s.innerData
    (associativityCoefficientBlocksB O.toCollection s)).hom
  let m := ColoredOperadObj.AssocInsertion.groupingBToFactorsHom O.toCollection O.subst s
  let γ : T.obj ((ColoredOperadObj.substitutionFactors O.toCollection).obj s.innerData) ⟶
    O.toCollection.obj s.innerData.totalProfile := O.subst.app s.innerData
  have h : k ≫ l = m := associativityCoefficientFactorMapB O s
  change a ≫ T.map k ≫ T.map l ≫ γ = a ≫ T.map m ≫ γ
  exact mapCoefficientsIntoSubstitution T a k l m γ h

/-- The actual finite coefficient permutation and actual output
profile relabelling give the original second operad associativity route. -/
theorem associativityBranchCoefficientRouteB (O : ColoredOperadObj W C) (s : ColoredAssocData W) :
    (FiniteTensor.tensor (V := C)).map
        (ColoredOperadObj.AssocInsertion.flattenAToFlattenBHom O.toCollection s) ≫
      substitutionBranchCoefficientRoute O s.innerData
        (associativityCoefficientBlocksB O.toCollection s) (associativityCoefficientMapsB O s) ≫
      O.toCollection.map s.totalHom =
    ColoredOperadObj.associativityRouteB O.toCollection O.subst s := by
  let T := FiniteTensor.tensor (V := C)
  let r := T.map (ColoredOperadObj.AssocInsertion.flattenAToFlattenBHom O.toCollection s)
  let N := ColoredOperadObj.AssocInsertion.groupingB O.toCollection s
  let a := (FiniteTensor.flattenIso (V := C)).hom.app N
  let b := T.map (ColoredOperadObj.AssocInsertion.groupingBToFactorsHom O.toCollection O.subst s)
  let γ := O.subst.app s.innerData
  let m := O.toCollection.map s.totalHom
  let f := substitutionBranchCoefficientRoute O s.innerData
    (associativityCoefficientBlocksB O.toCollection s) (associativityCoefficientMapsB O s)
  have hf : f = a ≫ b ≫ γ := associativityBranchCoefficientRouteB_prefix O s
  exact postcomposeTripleCoefficient r a b γ m f hf




end CategoryTheory.Operad.Tensor
end
end
end source_AssociativityCoefficientRoutes

/- Source proof segment: AssociativityCanonicalCoefficients -/
section source_AssociativityCanonicalCoefficients
/-!
# Original operad associativity coefficients on the common tensor source
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

theorem associativityCanonicalCoefficientA (O : ColoredOperadObj W C) (s : ColoredAssocData W) :
    canonicalSubstitutionCoefficient O s.outerAfterInnerData
        (associativityCoefficientBlocksA O.toCollection s) (associativityCoefficientMapsA O s)
        (Iso.refl (ColoredOperadObj.AssocInsertion.flattenedGroupingA O.toCollection s))
        (𝟙 s.outerAfterInnerData.totalProfile) =
      ColoredOperadObj.associativityRouteA O.toCollection O.subst s := by
  let T := FiniteTensor.tensor (V := C)
  let K := ColoredOperadObj.AssocInsertion.flattenedGroupingA O.toCollection s
  let P := s.outerAfterInnerData.totalProfile
  let Γ : T.obj K ⟶ O.toCollection.obj P := substitutionBranchCoefficientRoute O
    s.outerAfterInnerData
    (associativityCoefficientBlocksA O.toCollection s) (associativityCoefficientMapsA O s)
  have hT : T.map (𝟙 K) = 𝟙 _ := T.map_id K
  have hO : O.toCollection.map (𝟙 P) = 𝟙 _ := O.toCollection.map_id P
  have h : T.map (𝟙 K) ≫ Γ ≫ O.toCollection.map (𝟙 P) = Γ :=
    (congrArg (fun t => t ≫ Γ ≫ O.toCollection.map (𝟙 P)) hT).trans
      ((Category.id_comp _).trans
        ((congrArg (Γ ≫ ·) hO).trans (Category.comp_id Γ)))
  exact h.trans (associativityBranchCoefficientRouteA O s)

/-- The original coefficient regrouping and original totalHom are
both retained in the second coefficient route on the common source. -/
theorem associativityCanonicalCoefficientB (O : ColoredOperadObj W C) (s : ColoredAssocData W) :
    canonicalSubstitutionCoefficient O s.innerData
        (associativityCoefficientBlocksB O.toCollection s) (associativityCoefficientMapsB O s)
        (associativityCoefficientIso O.toCollection s).symm s.totalHom =
      ColoredOperadObj.associativityRouteB O.toCollection O.subst s := by
  change (FiniteTensor.tensor (V := C)).map (associativityCoefficientIso O.toCollection s).hom ≫
    substitutionBranchCoefficientRoute O s.innerData
      (associativityCoefficientBlocksB O.toCollection s) (associativityCoefficientMapsB O s) ≫
    O.toCollection.map s.totalHom = _
  rw [associativityCoefficientIso_hom]
  exact associativityBranchCoefficientRouteB O s




end CategoryTheory.Operad.Tensor
end
end
end source_AssociativityCanonicalCoefficients

/- Source proof segment: CoefficientSingletonLeaves -/
section source_CoefficientSingletonLeaves
/-!
# Original singleton coefficient normalization with retained leaves

A singleton coefficient block plus singleton original leaves is
normalized by the source map-singleton-flatten unit law. The
original coefficient and all original finite input positions are
retained in the resulting coefficient/leaf tensor.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The singleton coefficient and each original leaf singleton are
the mapped singleton family of the original coefficient/leaf family. -/
def singletonCoefficientLeavesIso (X : C) (L : FiniteFamily C) :
    coefficientLeavesNested ((FiniteFamily.singleton (C := C)).obj X) L ≅
      (FiniteFamily.map (FiniteFamily.singleton (C := C))).obj
        ((coefficientLeafFamilyFunctor L).obj X) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option L.index))
    (fun i => match i with
      | none => Iso.refl ((FiniteFamily.singleton (C := C)).obj X)
      | some i => Iso.refl ((FiniteFamily.singleton (C := C)).obj (L.obj i)))

/-- The actual original singleton coefficient/leaf normalization
agrees with the source tensor's map-singleton-flatten unit collapse. -/
theorem coefficientLeavesNormalization_singleton (X : C) (L : FiniteFamily C) :
    coefficientLeavesNormalization ((FiniteFamily.singleton (C := C)).obj X) L ≫
      (coefficientLeafTensorFunctor L).map ((FiniteTensor.singletonIso (V := C)).hom.app X) =
    (FiniteTensor.tensor (V := C)).map
      ((FiniteFamily.flatten (C := C)).map (singletonCoefficientLeavesIso X L).hom ≫
        FiniteFamily.mapSingletonFlattenIso.hom.app ((coefficientLeafFamilyFunctor L).obj X)) := by
  let N := coefficientLeavesNested ((FiniteFamily.singleton (C := C)).obj X) L
  let M := (FiniteFamily.map (FiniteFamily.singleton (C := C))).obj
    ((coefficientLeafFamilyFunctor L).obj X)
  let e := (singletonCoefficientLeavesIso X L).hom
  let a := (FiniteTensor.flattenIso (V := C)).hom.app N
  let b := coefficientLeavesMap ((FiniteFamily.singleton (C := C)).obj X) L
    ((FiniteTensor.singletonIso (V := C)).hom.app X)
  have hnat := (FiniteTensor.flattenIso (V := C)).hom.naturality e
  have hcollapse : (FiniteFamily.map FiniteTensor.tensor).map e ≫
      (FiniteFamily.mapIso (FiniteTensor.singletonIso (V := C))).hom.app
        ((coefficientLeafFamilyFunctor L).obj X) = b := by
    apply FiniteFamily.Hom_ext
    · rfl
    · intro i
      cases i with
      | none =>
        change HEq ((FiniteTensor.tensor (V := C)).map (𝟙 _) ≫
          (FiniteTensor.singletonIso (V := C)).hom.app X)
          ((FiniteTensor.singletonIso (V := C)).hom.app X)
        exact heq_of_eq ((congrArg (· ≫ _) ((FiniteTensor.tensor (V := C)).map_id _)).trans
          (Category.id_comp _))
      | some i =>
        change HEq ((FiniteTensor.tensor (V := C)).map (𝟙 _) ≫
          (FiniteTensor.singletonIso (V := C)).hom.app (L.obj i))
          ((FiniteTensor.singletonIso (V := C)).hom.app (L.obj i))
        exact heq_of_eq ((congrArg (· ≫ _) ((FiniteTensor.tensor (V := C)).map_id _)).trans
          (Category.id_comp _))
  have hunit := CategoryTheory.mapSingletonFlattenLaw_app ((coefficientLeafFamilyFunctor L).obj X)
  have hn := coefficientLeavesNormalization_map ((FiniteFamily.singleton (C := C)).obj X) L
    ((FiniteTensor.singletonIso (V := C)).hom.app X)
  have hmap := (FiniteTensor.tensor (V := C)).map_comp
    ((FiniteFamily.flatten (C := C)).map e)
    (FiniteFamily.mapSingletonFlattenIso.hom.app ((coefficientLeafFamilyFunctor L).obj X))
  have h : (FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map e) ≫
      (FiniteTensor.flattenIso (V := C)).hom.app M ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.mapIso (FiniteTensor.singletonIso (V := C))).hom.app
          ((coefficientLeafFamilyFunctor L).obj X)) = a ≫ (FiniteTensor.tensor (V := C)).map b := by
    change _ = _ at hnat
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hnat).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (a ≫ ·) ((FiniteTensor.tensor (V := C)).map_comp _ _).symm).trans
          (congrArg (fun f => a ≫ (FiniteTensor.tensor (V := C)).map f) hcollapse))))
  have hfull := hmap.trans
    ((congrArg ((FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map e)
      ≫ ·) hunit).trans h)
  exact hn.trans hfull.symm

end CategoryTheory.Operad.Tensor
end
end
end source_CoefficientSingletonLeaves

/- Source proof segment: OperadicLocalBranchMaps -/
section source_OperadicLocalBranchMaps
/-!
# Original local operadic substitutions and retained innermost operations
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The actual normalized coefficient-and-leaf local substitution
is exactly the original operadic substitution after the inverse of
its original input-factor permutation. -/
theorem operadSubstitutionInputs_coefficient_frame (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    coefficientLeavesNormalization
        ((ColoredOperadObj.substitutionFactors O.toCollection).obj s)
        (profileLeafFamily A s.totalProfile) ≫
      (coefficientLeafTensorFunctor (profileLeafFamily A s.totalProfile)).map (O.subst.app s) ≫
      (profileCoefficientLeafTensorIso O.toCollection A s.totalProfile).hom =
    (FiniteTensor.tensor (V := C)).map (substitutionToLeavesIso O.toCollection A s).inv ≫
      operadSubstitutionInputs O A s := by
  symm
  exact ((FiniteTensor.tensor (V := C)).mapIso (substitutionToLeavesIso O.toCollection A
    s)).inv_comp_eq.mpr
    (operadSubstitutionInputs_profile_factorization O A s)

/-- Every actual local branch in route A performs the original
`operadSubstitutionInputs`, retaining all original coefficient and leaf maps. -/
theorem associativityLocalBranchA (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) (i : s.branches.index) :
    (partitionedCoefficientLeavesActionMap
        (substitutionBranchGrouping s.outerAfterInnerData (associativityCoefficientBlocksA
          O.toCollection s))
        (substitutionBranchLeaves A s.outerAfterInnerData)
        (substitutionBranchCoefficients O.toCollection s.outerAfterInnerData)
        (associativityCoefficientMapsA O s)).hom (some i) ≫
      (profileCoefficientLeafTensorIso O.toCollection A (s.localData i).totalProfile).hom =
    (FiniteTensor.tensor (V := C)).map (substitutionToLeavesIso O.toCollection A
      (s.localData i)).inv ≫
      operadSubstitutionInputs O A (s.localData i) := by
  let L := profileLeafFamily A (s.localData i).totalProfile
  let K := (ColoredOperadObj.substitutionFactors O.toCollection).obj (s.localData i)
  let γ : (FiniteTensor.tensor (V := C)).obj K ⟶ O.toCollection.obj (s.localData i).totalProfile :=
    O.subst.app (s.localData i)
  let n := coefficientLeavesNormalization K L
  let f := (coefficientLeafTensorFunctor L).map γ
  let p := (profileCoefficientLeafTensorIso O.toCollection A (s.localData i).totalProfile).hom
  change (n ≫ f) ≫ p = _
  exact (Category.assoc n f p).trans (operadSubstitutionInputs_coefficient_frame O A
    (s.localData i))

/-- The innermost branch in route B retains its actual full original
operation tensor: only the source singleton-index structure is collapsed. -/
theorem associativityInnermostBranchB (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) (i : s.innerData.inner.index) :
    (partitionedCoefficientLeavesActionMap
        (substitutionBranchGrouping s.innerData (associativityCoefficientBlocksB O.toCollection s))
        (substitutionBranchLeaves A s.innerData)
        (substitutionBranchCoefficients O.toCollection s.innerData)
        (associativityCoefficientMapsB O s)).hom (some i) =
    (FiniteTensor.tensor (V := C)).map
      ((FiniteFamily.flatten (C := C)).map
          (singletonCoefficientLeavesIso (O.toCollection.obj (s.innerData.inner.obj i))
            (profileLeafFamily A (s.innerData.inner.obj i))).hom ≫
        FiniteFamily.mapSingletonFlattenIso.hom.app
          ((coefficientLeafFamilyFunctor (profileLeafFamily A (s.innerData.inner.obj i))).obj
            (O.toCollection.obj (s.innerData.inner.obj i)))) := by
  exact coefficientLeavesNormalization_singleton (O.toCollection.obj (s.innerData.inner.obj i))
    (profileLeafFamily A (s.innerData.inner.obj i))




end CategoryTheory.Operad.Tensor
end
end
end source_OperadicLocalBranchMaps

/- Source proof segment: EmptyLeafNormalization -/
section source_EmptyLeafNormalization
/-!
# Actual normalization of a coefficient block with no original leaves
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

theorem sourceUnitorNormalizationSquare {C : Type u} [Category.{v} C]
    {X A B R S Y : C} (d : X ⟶ A) (b : A ⟶ B) (c : B ⟶ S)
    (s : S ⟶ Y) (r : X ⟶ R) (a : R ⟶ S) (u : A ⟶ S) (z : R ⟶ Y)
    (hbc : b ≫ c = u) (hn : r ≫ a = d ≫ u) (hu : a ≫ s = z) :
    (d ≫ b) ≫ (c ≫ s) = r ≫ z := by
  simp only [Category.assoc]
  rw [← Category.assoc b c, hbc, ← Category.assoc d u, ← hn, Category.assoc r a, hu]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- With no original leaves, normalization is precisely the actual
singleton-index identification of the original coefficient block. -/
theorem coefficientLeavesNormalization_empty (K : FiniteFamily C) :
    coefficientLeavesNormalization K (FiniteFamily.empty : FiniteFamily C) ≫
      (emptyLeafTensorIso ((FiniteTensor.tensor (V := C)).obj K)).hom =
    (FiniteTensor.tensor (V := C)).map (emptyLeafRawIso K).hom := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let N := coefficientLeavesNested K (FiniteFamily.empty : FiniteFamily C)
  let M := (FiniteFamily.singleton (C := FiniteFamily C)).obj K
  let e := (emptyLeafNestedIso K).hom
  let d := (FiniteTensor.flattenIso (V := C)).hom.app N
  let b₀ := coefficientLeavesCollapse K (FiniteFamily.empty : FiniteFamily C)
  let c₀ := (emptyLeafFamilyIso (T.obj K)).hom
  let b := T.map b₀
  let c := T.map c₀
  let s := (FiniteTensor.singletonIso (V := C)).hom.app (T.obj K)
  let r := T.map (F.map e)
  let a := (FiniteTensor.flattenIso (V := C)).hom.app M
  let u := T.map ((FiniteFamily.map T).map e)
  let z := T.map (FiniteFamily.singletonFlattenIso.hom.app K)
  have hbc : b ≫ c = u :=
    (T.map_comp b₀ c₀).symm.trans (congrArg T.map (emptyLeafCollapse_square K))
  have hn := (FiniteTensor.flattenIso (V := C)).hom.naturality e
  change r ≫ a = d ≫ u at hn
  have hu : a ≫ s = z := (singletonFlattenLaw_app K).symm
  have h := sourceUnitorNormalizationSquare d b c s r a u z hbc hn hu
  have hm : r ≫ z = T.map (emptyLeafRawIso K).hom := (T.map_comp _ _).symm
  rw [emptyLeafTensorIso_hom]
  exact h.trans hm

/-- The original coefficient map with no retained leaves is the
original coefficient map after its actual raw index identification. -/
theorem coefficientLeavesNormalization_empty_map (K : FiniteFamily C) {Y : C}
    (f : (FiniteTensor.tensor (V := C)).obj K ⟶ Y) :
    coefficientLeavesNormalization K (FiniteFamily.empty : FiniteFamily C) ≫
      (coefficientLeafTensorFunctor (FiniteFamily.empty : FiniteFamily C)).map f ≫
      (emptyLeafTensorIso Y).hom =
    (FiniteTensor.tensor (V := C)).map (emptyLeafRawIso K).hom ≫ f := by
  have hn := emptyLeafTensorNatIso.hom.naturality f
  have hu := coefficientLeavesNormalization_empty K
  let n := coefficientLeavesNormalization K (FiniteFamily.empty : FiniteFamily C)
  let e := (emptyLeafTensorIso ((FiniteTensor.tensor (V := C)).obj K)).hom
  have h : (coefficientLeafTensorFunctor (FiniteFamily.empty : FiniteFamily C)).map f ≫
      (emptyLeafTensorIso Y).hom = e ≫ f := hn
  exact (congrArg (n ≫ ·) h).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) hu))




end CategoryTheory.Operad.Tensor
end
end
end source_EmptyLeafNormalization

/- Source proof segment: AssociativityRootBranches -/
section source_AssociativityRootBranches
/-!
# Original root coefficient maps in both three-level tensor routes
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Route A's root coefficient is the original singleton unitor;
its empty original leaf block contributes only the displayed index map. -/
theorem associativityRootBranchA (O : ColoredOperadObj W C) (A : W → C) (s : ColoredAssocData W) :
    (partitionedCoefficientLeavesActionMap
        (substitutionBranchGrouping s.outerAfterInnerData (associativityCoefficientBlocksA
          O.toCollection s))
        (substitutionBranchLeaves A s.outerAfterInnerData)
        (substitutionBranchCoefficients O.toCollection s.outerAfterInnerData)
        (associativityCoefficientMapsA O s)).hom none ≫
      (emptyLeafTensorIso (O.toCollection.obj s.outerAfterInnerData.outerProfile)).hom =
    (FiniteTensor.tensor (V := C)).map
        (emptyLeafRawIso ((FiniteFamily.singleton (C := C)).obj
          (O.toCollection.obj s.outerAfterInnerData.outerProfile))).hom ≫
      (FiniteTensor.singletonIso (V := C)).hom.app (O.toCollection.obj
        s.outerAfterInnerData.outerProfile) := by
  let X := O.toCollection.obj s.outerAfterInnerData.outerProfile
  let K := (FiniteFamily.singleton (C := C)).obj X
  let γ := (FiniteTensor.singletonIso (V := C)).hom.app X
  let n := coefficientLeavesNormalization K (FiniteFamily.empty : FiniteFamily C)
  let f := (coefficientLeafTensorFunctor (FiniteFamily.empty : FiniteFamily C)).map γ
  let p := (emptyLeafTensorIso X).hom
  change (n ≫ f) ≫ p = _
  exact (Category.assoc n f p).trans (coefficientLeavesNormalization_empty_map K γ)

/-- Route B's root performs exactly the original middle operadic
substitution. Its empty original leaf block contributes only the
actual coefficient-source index identification. -/
theorem associativityRootBranchB (O : ColoredOperadObj W C) (A : W → C) (s : ColoredAssocData W) :
    (partitionedCoefficientLeavesActionMap
        (substitutionBranchGrouping s.innerData (associativityCoefficientBlocksB O.toCollection s))
        (substitutionBranchLeaves A s.innerData)
        (substitutionBranchCoefficients O.toCollection s.innerData)
        (associativityCoefficientMapsB O s)).hom none ≫
      (emptyLeafTensorIso (O.toCollection.obj s.middleData.totalProfile)).hom =
    (FiniteTensor.tensor (V := C)).map
        (emptyLeafRawIso ((ColoredOperadObj.substitutionFactors O.toCollection).obj
          s.middleData)).hom ≫
      O.subst.app s.middleData := by
  let K := (ColoredOperadObj.substitutionFactors O.toCollection).obj s.middleData
  let X := O.toCollection.obj s.middleData.totalProfile
  let γ : (FiniteTensor.tensor (V := C)).obj K ⟶ X := O.subst.app s.middleData
  let n := coefficientLeavesNormalization K (FiniteFamily.empty : FiniteFamily C)
  let f := (coefficientLeafTensorFunctor (FiniteFamily.empty : FiniteFamily C)).map γ
  let p := (emptyLeafTensorIso X).hom
  change (n ≫ f) ≫ p = _
  exact (Category.assoc n f p).trans (coefficientLeavesNormalization_empty_map K γ)




end CategoryTheory.Operad.Tensor
end
end
end source_AssociativityRootBranches

/- Source proof segment: ThreeLevelTensorSubstitution -/
section source_ThreeLevelTensorSubstitution
/-!
# Actual three-level colored tensor substitution associativity

Both routes use one tensor of the original three levels of coefficients
and the original nested-total-profile leaves. Route A performs the original
local branch substitutions and original outer substitution. Route B performs
the original middle coefficient substitution, retains each original full
innermost operation tensor, performs the original flattened substitution,
and applies the original total-profile map. All factor permutations,
singleton unitors, and finite tensor flattening maps are actual source maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The actual common source contains every original operadic
coefficient and every original nested-total-profile input. -/
def threeLevelTensorSource (O : ColoredSymmetricCollection W C) (A : W →
  C) (s : ColoredAssocData W) : C :=
  (FiniteTensor.tensor (V := C)).obj
    ((FiniteFamily.flatten (C := C)).obj
      (coefficientLeavesNested (ColoredOperadObj.AssocInsertion.flattenedGroupingA O s)
        (profileLeafFamily A s.outerAfterInnerData.totalProfile)))

/-- Original local branch substitutions followed by the original
outer substitution, on their actual complete common tensor source. -/
def threeLevelTensorRouteA (O : ColoredOperadObj W C) (A : W → C) (s : ColoredAssocData W) :
    threeLevelTensorSource O.toCollection A s ⟶
      (operationSummandFunctor O.toCollection A).obj s.outerAfterInnerData.totalProfile :=
  canonicalSubstitutionRoute O A s.outerAfterInnerData
    (associativityCoefficientBlocksA O.toCollection s) (associativityCoefficientMapsA O s)
    (Iso.refl (ColoredOperadObj.AssocInsertion.flattenedGroupingA O.toCollection s))
    (𝟙 s.outerAfterInnerData.totalProfile)

/-- Original middle substitution, original retained innermost
operations, original flattened substitution, and original totalHom
on all original coefficient and leaf factors. -/
def threeLevelTensorRouteB (O : ColoredOperadObj W C) (A : W → C) (s : ColoredAssocData W) :
    threeLevelTensorSource O.toCollection A s ⟶
      (operationSummandFunctor O.toCollection A).obj s.outerAfterInnerData.totalProfile :=
  canonicalSubstitutionRoute O A s.innerData
    (associativityCoefficientBlocksB O.toCollection s) (associativityCoefficientMapsB O s)
    (associativityCoefficientIso O.toCollection s).symm s.totalHom

/-- The first route is the original complete inner/outer substitution
composite after its actual common-source isomorphism. -/
theorem threeLevelTensorRouteA_original (O : ColoredOperadObj W C) (A : W →
  C) (s : ColoredAssocData W) :
    threeLevelTensorRouteA O A s =
      (substitutionCanonicalSourceIso A s.outerAfterInnerData
          (associativityCoefficientBlocksA O.toCollection s)
          (Iso.refl (ColoredOperadObj.AssocInsertion.flattenedGroupingA O.toCollection s))
          (𝟙 s.outerAfterInnerData.totalProfile)).inv ≫
        fullSubstitutionPartitionRoute O A s.outerAfterInnerData
          (associativityCoefficientBlocksA O.toCollection s) (associativityCoefficientMapsA
            O s) := by
  let F := operationSummandFunctor O.toCollection A
  let P := s.outerAfterInnerData.totalProfile
  let e := (substitutionCanonicalSourceIso A s.outerAfterInnerData
    (associativityCoefficientBlocksA O.toCollection s)
    (Iso.refl (ColoredOperadObj.AssocInsertion.flattenedGroupingA O.toCollection s)) (𝟙 P)).inv
  let r := fullSubstitutionPartitionRoute O A s.outerAfterInnerData
    (associativityCoefficientBlocksA O.toCollection s) (associativityCoefficientMapsA O s)
  have hi := F.map_id P
  change e ≫ r ≫ F.map (𝟙 P) = e ≫ r
  exact congrArg (e ≫ ·) ((congrArg (r ≫ ·) hi).trans (Category.comp_id r))

/-- The second route retains the original middle and flattened
substitutions and the actual total-profile tensor relabelling. -/
theorem threeLevelTensorRouteB_original (O : ColoredOperadObj W C) (A : W →
  C) (s : ColoredAssocData W) :
    threeLevelTensorRouteB O A s =
      (substitutionCanonicalSourceIso A s.innerData (associativityCoefficientBlocksB
        O.toCollection s)
          (associativityCoefficientIso O.toCollection s).symm s.totalHom).inv ≫
        fullSubstitutionPartitionRoute O A s.innerData
          (associativityCoefficientBlocksB O.toCollection s) (associativityCoefficientMapsB O s) ≫
        (operationSummandFunctor O.toCollection A).map s.totalHom := rfl

theorem threeLevelTensorRouteA_factorization (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    threeLevelTensorRouteA O A s =
      coefficientLeavesNormalization (ColoredOperadObj.AssocInsertion.flattenedGroupingA
        O.toCollection s)
        (profileLeafFamily A s.outerAfterInnerData.totalProfile) ≫
      (coefficientLeafTensorFunctor (profileLeafFamily A s.outerAfterInnerData.totalProfile)).map
        (ColoredOperadObj.associativityRouteA O.toCollection O.subst s) ≫
      (profileCoefficientLeafTensorIso O.toCollection A
        s.outerAfterInnerData.totalProfile).hom := by
  have h := canonicalSubstitutionRoute_factorization O A s.outerAfterInnerData
    (associativityCoefficientBlocksA O.toCollection s) (associativityCoefficientMapsA O s)
    (Iso.refl (ColoredOperadObj.AssocInsertion.flattenedGroupingA O.toCollection s))
    (𝟙 s.outerAfterInnerData.totalProfile)
  rw [associativityCanonicalCoefficientA] at h
  exact h

theorem threeLevelTensorRouteB_factorization (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    threeLevelTensorRouteB O A s =
      coefficientLeavesNormalization (ColoredOperadObj.AssocInsertion.flattenedGroupingA
        O.toCollection s)
        (profileLeafFamily A s.outerAfterInnerData.totalProfile) ≫
      (coefficientLeafTensorFunctor (profileLeafFamily A s.outerAfterInnerData.totalProfile)).map
        (ColoredOperadObj.associativityRouteB O.toCollection O.subst s) ≫
      (profileCoefficientLeafTensorIso O.toCollection A
        s.outerAfterInnerData.totalProfile).hom := by
  have h := canonicalSubstitutionRoute_factorization O A s.innerData
    (associativityCoefficientBlocksB O.toCollection s) (associativityCoefficientMapsB O s)
    (associativityCoefficientIso O.toCollection s).symm s.totalHom
  rw [associativityCanonicalCoefficientB] at h
  exact h

/-- Actual three-level substitution associativity, derived from
the original operad associativity and the genuine finite tensor
pseudoalgebra laws. Empty branches and profiles are included. -/
theorem threeLevelTensorSubstitution_assoc (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) : threeLevelTensorRouteA O A s = threeLevelTensorRouteB O A s := by
  let n := coefficientLeavesNormalization
    (ColoredOperadObj.AssocInsertion.flattenedGroupingA O.toCollection s)
    (profileLeafFamily A s.outerAfterInnerData.totalProfile)
  let F := coefficientLeafTensorFunctor (profileLeafFamily A s.outerAfterInnerData.totalProfile)
  let p := (profileCoefficientLeafTensorIso O.toCollection A s.outerAfterInnerData.totalProfile).hom
  have h := congrArg (fun f => n ≫ F.map f ≫ p) (O.assoc s)
  exact (threeLevelTensorRouteA_factorization O A s).trans
    (h.trans (threeLevelTensorRouteB_factorization O A s).symm)



end CategoryTheory.Operad.Tensor
end
end
end source_ThreeLevelTensorSubstitution

/- Source proof segment: NestedRawAssocShape -/
section source_NestedRawAssocShape
/-!
# Original associativity shapes from nested profile slot tuples
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u}

/-- The actual three-level substitution datum chosen by the
original inner raw slot tuple, with unchanged finite input indices. -/
def nestedRawAssocShape (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s) :
    ColoredAssocData W where
  outputColor := s.outputColor
  branches :=
    { index := s.inner.index
      obj i := tupleSubstitutionShape (profileInputs (s.inner.obj i))
        ((slotProfileTupleFunctor (profileInputs (s.inner.obj i))).obj (Q (some i))) }

/-- The middle profile family is the original unchanged two-level
datum from which the nested original choices were made. -/
theorem nestedRawAssocShape_middle (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s) :
    (nestedRawAssocShape s Q).middleData = s := by
  cases s with
  | mk output inner =>
    cases inner
    rfl

/-- Every actual local datum is the original inner profile's
actual complete raw profile tuple. -/
theorem nestedRawAssocShape_local (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s)
    (i : s.inner.index) :
    (nestedRawAssocShape s Q).localData i =
      tupleSubstitutionShape (profileInputs (s.inner.obj i))
        ((slotProfileTupleFunctor (profileInputs (s.inner.obj i))).obj (Q (some i))) := rfl



end CategoryTheory.Operad.Tensor
end
end
end source_NestedRawAssocShape

/- Source proof segment: NestedRawInjection -/
section source_NestedRawInjection
/-!
# Original nested raw tensor source injections
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The original coefficient and raw inner-source factor objects
at an actual complete three-level profile tuple. -/
def nestedRawSourceFactors (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s) : FiniteFamily C :=
  (FiniteFamily.fixedIndexFunctor (analyticFactorsIndex (profileInputs s.outerProfile))).obj
    (fun i => (nestedRawSlotDiagram O A s i).obj (Q i))

/-- Every original raw branch injection is retained at its original
outer input, with the original coefficient identity at the root. -/
def nestedRawInjectionFactors (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s) :
    nestedRawSourceFactors O A s Q ⟶
      (FiniteFamily.fixedIndexFunctor (analyticFactorsIndex (profileInputs s.outerProfile))).obj
        (fun i => (nestedRawSlotCocone O A s i).pt) where
  equiv := Equiv.refl (Option s.inner.index)
  hom i := match i with
    | none => 𝟙 (O.obj s.outerProfile)
    | some i => (rawSubstitutionCocone O A (profileInputs (s.inner.obj i))).ι.app (Q (some i))

/-- The exact original nested tensor source injection uses every
original raw factor injection and no selected-profile restriction. -/
theorem nestedRawTensorCocone_ι (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s) :
    (nestedRawTensorCocone O A s).ι.app Q =
      (FiniteTensor.tensor (V := C)).map (nestedRawInjectionFactors O A s Q) := by
  apply congrArg (FiniteTensor.tensor (V := C)).map
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none => exact HEq.rfl
    | some i => exact HEq.rfl

/-- Compose the actual original nested source injection with its
actual original raw-point coefficient and flattening isomorphism. -/
theorem nestedRawPointInjection (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s) :
    (nestedRawTensorCocone O A s).ι.app Q ≫ (nestedRawPointIso O A s).hom =
      (FiniteTensor.tensor (V := C)).map
        (nestedRawInjectionFactors O A s Q ≫ (nestedRawPointFactorsIso O A s).hom) ≫
      (FiniteTensor.flattenIso (V := C)).inv.app
        (nestedOperationFactors O (profileCoinvariants O A) s) := by
  rw [nestedRawTensorCocone_ι]
  change _ ≫ (_ ≫ _) = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) ((FiniteTensor.tensor (V := C)).map_comp _ _).symm)




end CategoryTheory.Operad.Tensor
end
end
end source_NestedRawInjection

/- Source proof segment: NestedRawThreeLevelSource -/
section source_NestedRawThreeLevelSource
/-!
# Actual nested raw source and original three-level factor tensor
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The root singleton and complete local raw factor families
of an original three-level operadic substitution. -/
def nestedThreeLevelFactors (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) : FiniteFamily (FiniteFamily C) where
  index := FintypeCat.of (Option s.branches.index)
  obj i := match i with
    | none => (FiniteFamily.singleton (C := C)).obj (O.obj s.middleData.outerProfile)
    | some i => (FiniteFamily.flatten (C := C)).obj (nestedOperationFactors O A (s.localData i))

/-- Original inner-first factors regroup into the original
coefficient blocks and each branch's actual complete leaf profile. -/
def nestedThreeLevelBranchSourceIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    nestedThreeLevelFactors O A s ≅
      (FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
        (partitionedCoefficientLeavesTriple
          (substitutionBranchGrouping s.outerAfterInnerData (associativityCoefficientBlocksA O s))
          (substitutionBranchLeaves A s.outerAfterInnerData)) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option s.branches.index))
    (fun i => match i with
      | none => (emptyLeafRawIso ((FiniteFamily.singleton (C :=
        C)).obj (O.obj s.middleData.outerProfile))).symm
      | some i => substitutionToLeavesIso O A (s.localData i))

/-- The original tensor of all nested raw factors has precisely
the original three levels of coefficients and original total leaves. -/
def nestedThreeLevelSourceIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (nestedThreeLevelFactors O A s)) ≅
      threeLevelTensorSource O A s :=
  ((FiniteTensor.flattenIso (V := C)).app (nestedThreeLevelFactors O A s)).symm ≪≫
    (FiniteTensor.tensor (V := C)).mapIso
      ((FiniteFamily.flatten (C := C)).mapIso (nestedThreeLevelBranchSourceIso O A s)) ≪≫
    substitutionCanonicalSourceIso A s.outerAfterInnerData (associativityCoefficientBlocksA O s)
      (Iso.refl (ColoredOperadObj.AssocInsertion.flattenedGroupingA O s))
      (𝟙 s.outerAfterInnerData.totalProfile)



end CategoryTheory.Operad.Tensor
end
end
end source_NestedRawThreeLevelSource

/- Source proof segment: FreeOperationNaturality -/
section source_FreeOperationNaturality
/-!
# Original input naturality and equivariance of free operations

Uniqueness of the constructed finite tensor colimit descent and
the original coefficient/input injection squares give naturality
and full outer-profile equivariance of the actual free operations.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- The actual free operations commute with every original
color-indexed input component and its original coinvariant map. -/
@[reassoc]
theorem freeOperation_input (O : ColoredOperadObj W C) {A B : W → C}
    (f : A ⟶ B) {d : W} (P : AnalyticIndex W d) :
    (analyticSummandCarrierMap O.toCollection (profileMap O.toCollection f)).app P ≫
        freeOperation O B P =
      freeOperation O A P ≫ profileMap O.toCollection f d := by
  apply freeOperation_hom_ext O.toCollection A P
  intro Q
  let iA := (profileSlotTensorCocone O.toCollection A P).ι.app Q
  let iB := (profileSlotTensorCocone O.toCollection B P).ι.app Q
  let h := (profileSlotInputTensorMap O.toCollection f P).app Q
  have hi := (profileSlotTensorCocone_input O.toCollection f P Q).symm
  have hA := freeOperation_ι O A P Q
  have hB := freeOperation_ι O B P Q
  have hsub := assembledProfileSubstitutionCocone_input O f P Q
  change iA ≫
      ((analyticSummandCarrierMap O.toCollection (profileMap O.toCollection f)).app P ≫
        freeOperation O B P) =
    iA ≫ (freeOperation O A P ≫ profileMap O.toCollection f d)
  exact descentInputSquare iA iB h
    ((analyticSummandCarrierMap O.toCollection (profileMap O.toCollection f)).app P)
    (freeOperation O A P) (freeOperation O B P) (profileMap O.toCollection f d)
    ((assembledProfileSubstitutionCocone O A P).ι.app Q)
    ((assembledProfileSubstitutionCocone O B P).ι.app Q) hi hA hB hsub

/-- The actual free operations are equivariant under every
original outer-profile input bijection and color transport. -/
@[reassoc]
theorem freeOperation_relabel (O : ColoredOperadObj W C) (A : W → C)
    {d : W} {P Q : AnalyticIndex W d} (f : P ⟶ Q) :
    (analyticSummand O.toCollection (profileCoinvariants O.toCollection A)).map f ≫
        freeOperation O A Q = freeOperation O A P := by
  apply freeOperation_hom_ext O.toCollection A P
  intro R
  let iP := (profileSlotTensorCocone O.toCollection A P).ι.app R
  let iQ := (profileSlotTensorCocone O.toCollection A Q).ι.app ((slotRelabelFunctor f).obj R)
  let h := (slotRelabelTensorNatTrans O.toCollection A f).app R
  have hi := (profileSlotTensorCocone_relabel O.toCollection A f R).symm
  have hP := freeOperation_ι O A P R
  have hQ := freeOperation_ι O A Q ((slotRelabelFunctor f).obj R)
  have hsub := assembledProfileSubstitutionCocone_relabel O A f R
  change iP ≫
      ((analyticSummand O.toCollection (profileCoinvariants O.toCollection A)).map f ≫
        freeOperation O A Q) =
    iP ≫ freeOperation O A P
  exact descentRelabelSquare iP iQ h
    ((analyticSummand O.toCollection (profileCoinvariants O.toCollection A)).map f)
    (freeOperation O A P) (freeOperation O A Q)
    ((assembledProfileSubstitutionCocone O A P).ι.app R)
    ((assembledProfileSubstitutionCocone O A Q).ι.app ((slotRelabelFunctor f).obj R)) hi hP hQ hsub

/-- The constructed free operation family includes every finite
profile and is equivariant under all original profile maps. -/
def freeOperations (O : ColoredOperadObj W C) (A : W → C) :
    Operations O.toCollection (profileCoinvariants O.toCollection A) (profileCoinvariants
      O.toCollection A) where
  app _ P := freeOperation O A P
  equivariance _ _ _ f := freeOperation_relabel O A f




end CategoryTheory.Operad.Tensor
end
end
end source_FreeOperationNaturality

/- Source proof segment: NestedRawOperationEvaluation -/
section source_NestedRawOperationEvaluation
/-!
# Actual branch free-operation evaluation on original nested raw sources
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem singletonInverseIdentity {V : Type*} [Category* V]
    {X S : V} (e : S ≅ X) : 𝟙 X ≫ (e.inv ≫ e.hom) = 𝟙 X := by
  rw [e.inv_hom_id, Category.comp_id]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- The actual branch substitutions on every original inner raw
source, followed by the corresponding original total profile injection. -/
def nestedRawBranchEvaluationFactors (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s) :
    nestedRawSourceFactors O.toCollection A s Q ⟶
      (analyticFactors O.toCollection (profileCoinvariants O.toCollection A)).obj
        (profileInputs s.outerProfile) where
  equiv := Equiv.refl (Option s.inner.index)
  hom i := match i with
    | none => 𝟙 (O.toCollection.obj s.outerProfile)
    | some i =>
      operadSubstitutionInputs O A ((nestedRawAssocShape s Q).localData i) ≫
        profileι O.toCollection A (profileInputs ((nestedRawAssocShape s Q).localData
          i).totalProfile)

/-- The original raw branch colimit injection followed by the
actual free operation is precisely the original branch substitution. -/
theorem nestedRawBranchEvaluation (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s) :
    nestedRawInjectionFactors O.toCollection A s Q ≫ (nestedRawPointFactorsIso
      O.toCollection A s).hom ≫
      innerOperationMap (freeOperations O A) s = nestedRawBranchEvaluationFactors O A s Q := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      exact heq_of_eq (singletonInverseIdentity
        ((FiniteTensor.singletonIso (V := C)).app (O.toCollection.obj s.outerProfile)))
    | some i =>
      change HEq
        ((rawSubstitutionCocone O.toCollection A (profileInputs (s.inner.obj i))).ι.app (Q
          (some i)) ≫
          (𝟙 _ ≫ freeOperation O A (profileInputs (s.inner.obj i))))
        (operadSubstitutionInputs O A ((nestedRawAssocShape s Q).localData i) ≫
          profileι O.toCollection A (profileInputs ((nestedRawAssocShape s Q).localData
            i).totalProfile))
      exact heq_of_eq ((congrArg (_ ≫ ·) (Category.id_comp _)).trans
        (rawSubstitutionCocone_freeOperation O A (profileInputs (s.inner.obj i)) (Q (some i))))



end CategoryTheory.Operad.Tensor
end
end
end source_NestedRawOperationEvaluation

/- Source proof segment: NestedThreeLevelBranchEvaluation -/
section source_NestedThreeLevelBranchEvaluation
/-!
# Actual original three-level branch operation tensor readback
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

private theorem mapIsoHomReadback {V : Type*} [Category* V]
    {X Y Z : V} (e : X ≅ Y) (f : Y ⟶ Z) (g : X ⟶ Z)
    (h : f = e.inv ≫ g) : e.hom ≫ f = g := by
  rw [h, Iso.hom_inv_id_assoc]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The complete original local operation evaluations, retaining
the original singleton coefficient and all original raw leaves. -/
def nestedThreeLevelOperationFactors (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (nestedThreeLevelFactors
      O.toCollection A s) ⟶
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        (nestedOperationFactors O.toCollection A s.outerAfterInnerData) where
  equiv := Equiv.refl (Option s.branches.index)
  hom i := match i with
    | none => 𝟙 ((FiniteTensor.tensor (V := C)).obj ((FiniteFamily.singleton (C :=
      C)).obj (O.toCollection.obj
      s.middleData.outerProfile)))
    | some i => operadSubstitutionInputs O A (s.localData i)

/-- Tensoring the original local source regrouping, original
partition action, and original scalar frame gives exactly the
original local operation substitutions at every branch. -/
theorem nestedThreeLevelBranchEvaluation (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (nestedThreeLevelBranchSourceIso
      O.toCollection A s).hom ≫
      partitionedCoefficientLeavesActionMap
        (substitutionBranchGrouping s.outerAfterInnerData (associativityCoefficientBlocksA
          O.toCollection s))
        (substitutionBranchLeaves A s.outerAfterInnerData)
        (substitutionBranchCoefficients O.toCollection s.outerAfterInnerData)
        (associativityCoefficientMapsA O s) ≫
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).map
        (substitutionFrameFactorsIso O.toCollection A s.outerAfterInnerData
          (associativityCoefficientBlocksA O.toCollection s)).hom =
    nestedThreeLevelOperationFactors O A s := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      apply heq_of_eq
      let K := (FiniteFamily.singleton (C := C)).obj (O.toCollection.obj s.middleData.outerProfile)
      let a := (FiniteTensor.tensor (V := C)).map (emptyLeafRawIso K).inv
      let b := (partitionedCoefficientLeavesActionMap
        (substitutionBranchGrouping s.outerAfterInnerData (associativityCoefficientBlocksA
          O.toCollection s))
        (substitutionBranchLeaves A s.outerAfterInnerData)
        (substitutionBranchCoefficients O.toCollection s.outerAfterInnerData)
        (associativityCoefficientMapsA O s)).hom none
      let p := (FiniteTensor.tensor (V := C)).map (emptyLeafFamilyIso (O.toCollection.obj
        s.middleData.outerProfile)).hom
      let e := (FiniteTensor.singletonIso (V := C)).app (O.toCollection.obj
        s.middleData.outerProfile)
      have h := associativityRootBranchA O A s
      have h' : b ≫ p ≫ e.hom = (FiniteTensor.tensor (V :=
        C)).map (emptyLeafRawIso K).hom ≫ e.hom := by
        change b ≫ (p ≫ e.hom) = _ at h
        exact h
      have hh : b ≫ p = (FiniteTensor.tensor (V := C)).map (emptyLeafRawIso K).hom :=
        (cancel_mono e.hom).1 ((Category.assoc _ _ _).trans h')
      change a ≫ (b ≫ p) = 𝟙 _
      exact (congrArg (a ≫ ·) hh).trans ((FiniteTensor.tensor (V :=
        C)).mapIso (emptyLeafRawIso K)).inv_hom_id
    | some i =>
      apply heq_of_eq
      let e := (FiniteTensor.tensor (V := C)).mapIso (substitutionToLeavesIso O.toCollection
        A (s.localData i))
      have h := associativityLocalBranchA O A s i
      change e.hom ≫ _ = _
      exact mapIsoHomReadback e _ _ h



end CategoryTheory.Operad.Tensor
end
end
end source_NestedThreeLevelBranchEvaluation

/- Source proof segment: ProfileAssemblyInverse -/
section source_ProfileAssemblyInverse
/-!
# Original inverse coefficient tensor assembly maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The exact inverse of original tensor source assembly is its
original flattening followed by the coefficient singleton collapse. -/
theorem profileSlotAssemblyIso_inv_app (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (profileSlotAssemblyIso O A P).inv.app Q =
      (FiniteTensor.flattenIso (V := C)).hom.app
        (nestedOperationFactors O A (tupleSubstitutionShape P ((slotProfileTupleFunctor
          P).obj Q))) ≫
      (FiniteTensor.tensor (V := C)).map (coefficientTensorIso O A P Q).inv := rfl



end CategoryTheory.Operad.Tensor
end
end
end source_ProfileAssemblyInverse

/- Source proof segment: RawOperationSlotInjection -/
section source_RawOperationSlotInjection
/-!
# Exact original raw source tensor injection at profile slot tuples
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The actual raw source coefficient/input injection factors. -/
def rawOperationSlotInjectionFactors (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        (nestedOperationFactors O A (tupleSubstitutionShape P ((slotProfileTupleFunctor
          P).obj Q))) ⟶
      (analyticFactors O (profileCoinvariants O A)).obj P :=
  (coefficientTensorIso O A P Q).inv ≫
    ({ equiv := Equiv.refl (Option P.inputs)
       hom i := match i with
         | none => 𝟙 (O.obj P.toColoredProfile)
         | some i => profileι O A (Q (some i)) } :
      (slotInputFactorsFunctor O A P).obj Q ⟶ (analyticFactors O (profileCoinvariants O A)).obj P)

/-- Every original raw source cocone injection is the original
flattening map and the actual raw injection factor tensor. -/
theorem rawOperationSlotInjection (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (rawSubstitutionCocone O A P).ι.app Q =
      (FiniteTensor.flattenIso (V := C)).hom.app
        (nestedOperationFactors O A (tupleSubstitutionShape P ((slotProfileTupleFunctor
          P).obj Q))) ≫
        (FiniteTensor.tensor (V := C)).map (rawOperationSlotInjectionFactors O A P Q) := by
  rw [rawSubstitutionCocone_ι, profileSlotAssemblyIso_inv_app, profileSlotTensorCocone_ι]
  exact (Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((FiniteTensor.tensor (V := C)).map_comp _ _).symm)



end CategoryTheory.Operad.Tensor
end
end
end source_RawOperationSlotInjection

/- Source proof segment: TwoLevelOperationInjection -/
section source_TwoLevelOperationInjection
/-!
# Actual raw operation injection with original profile leaves
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- Insert every original inner profile operation tensor into its
actual profile coinvariants, retaining the root coefficient identity. -/
def operationInjectionFactors (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (nestedOperationFactors O A s) ⟶
      (analyticFactors O (profileCoinvariants O A)).obj (profileInputs s.outerProfile) where
  equiv := Equiv.refl (Option s.inner.index)
  hom i := match i with
    | none => (FiniteTensor.singletonIso (V := C)).hom.app (O.obj s.outerProfile)
    | some i => profileι O A (profileInputs (s.inner.obj i))

/-- The original inner profiles form their actual coefficient and
input slot tuple, with the singleton root index. -/
def operationSlotTuple (s : ColoredSubstitutionData W) : ProfileSlotTuple (profileInputs
  s.outerProfile)
  | none => ⟨⟨PUnit.unit⟩⟩
  | some i => profileInputs (s.inner.obj i)

omit [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C] [FiniteTensor C] in
theorem operationSlotTuple_shape (s : ColoredSubstitutionData W) :
    tupleSubstitutionShape (profileInputs s.outerProfile)
      ((slotProfileTupleFunctor (profileInputs s.outerProfile)).obj (operationSlotTuple s))
        = s := by
  cases s with
  | mk output inner => cases inner; rfl

variable [Small.{us} W] [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- The original tensor injection with every original inner
profile evaluates free operations by the actual operad substitution. -/
theorem operationInjection_freeOperation (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    (FiniteTensor.tensor (V := C)).map (operationInjectionFactors O.toCollection A s) ≫
      freeOperation O A (profileInputs s.outerProfile) =
    (FiniteTensor.flattenIso (V := C)).inv.app (nestedOperationFactors O.toCollection A s) ≫
      operadSubstitutionInputs O A s ≫ profileι O.toCollection A (profileInputs
        s.totalProfile) := by
  rcases s with ⟨output, ⟨I, inner⟩⟩
  let s : ColoredSubstitutionData W := ⟨output, ⟨I, inner⟩⟩
  let P := profileInputs s.outerProfile
  let Q := operationSlotTuple s
  let f := freeOperation O A P
  let op := operadSubstitutionInputs O A s ≫ profileι O.toCollection A (profileInputs
    s.totalProfile)
  have h := rawSubstitutionCocone_freeOperation O A P Q
  let T := FiniteTensor.tensor (V := C)
  let M := nestedOperationFactors O.toCollection A s
  let eF := coefficientTensorIso O.toCollection A P Q
  let inj := ({
      equiv := Equiv.refl (Option s.inner.index)
      hom j := match j with
        | none => 𝟙 (O.toCollection.obj s.outerProfile)
        | some j => profileι O.toCollection A (profileInputs (s.inner.obj j)) } :
    (slotInputFactorsFunctor O.toCollection A P).obj Q ⟶
      (analyticFactors O.toCollection (profileCoinvariants O.toCollection A)).obj P)
  have hcoef : eF.inv ≫ inj = operationInjectionFactors O.toCollection A s := by
    apply FiniteFamily.Hom_ext
    · rfl
    · intro j
      cases j with
      | none =>
        with_unfolding_all
          exact heq_of_eq (show (𝟙 _ ≫ (FiniteTensor.singletonIso (V := C)).hom.app _) ≫ 𝟙 _ =
            (FiniteTensor.singletonIso (V := C)).hom.app _ from by simp only
              [Category.id_comp, Category.comp_id])
      | some j =>
        with_unfolding_all
          exact heq_of_eq (show (𝟙 _ ≫ (𝟙 _)) ≫ profileι O.toCollection A
            (profileInputs (s.inner.obj j)) =
            profileι O.toCollection A (profileInputs (s.inner.obj j)) from by simp only
              [Category.id_comp])
  have hi : (rawSubstitutionCocone O.toCollection A P).ι.app Q =
      (FiniteTensor.flattenIso (V := C)).hom.app M ≫ T.map (operationInjectionFactors
        O.toCollection A s) := by
    have hraw := rawOperationSlotInjection O.toCollection A P Q
    have hfactor : rawOperationSlotInjectionFactors O.toCollection A P Q =
        operationInjectionFactors O.toCollection A s := by
      have hinj : rawOperationSlotInjectionFactors O.toCollection A P Q = eF.inv ≫ inj := by
        apply FiniteFamily.Hom_ext
        · rfl
        · intro j
          cases j <;> exact HEq.rfl
      exact hinj.trans hcoef
    exact hraw.trans (congrArg (_ ≫ ·) (congrArg T.map hfactor))
  have h' : (rawSubstitutionCocone O.toCollection A P).ι.app Q ≫ freeOperation O A P = op := by
    with_unfolding_all exact h
  have hh : (FiniteTensor.flattenIso (V := C)).hom.app (nestedOperationFactors O.toCollection A s) ≫
      (FiniteTensor.tensor (V := C)).map (operationInjectionFactors O.toCollection A s) ≫ f = op :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) hi.symm).trans h')
  exact ((FiniteTensor.flattenIso (V := C)).app (nestedOperationFactors O.toCollection A
    s)).eq_inv_comp.mpr hh

end CategoryTheory.Operad.Tensor
end
end
end source_TwoLevelOperationInjection

/- Source proof segment: NestedRawSourceFrame -/
section source_NestedRawSourceFrame
/-!
# Original nested raw source tensor frame
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem sourceSingletonCancel {V : Type*} [Category* V]
    {X Y : V} (e : Y ≅ X) : e.inv ≫ (𝟙 Y ≫ e.hom) = 𝟙 X := by
  rw [Category.id_comp, e.inv_hom_id]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The actual root coefficient singleton and original local raw
source tensors identify with the original nested tensor diagram. -/
def nestedRawSourceFactorsIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s) :
    nestedRawSourceFactors O A s Q ≅
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        (nestedThreeLevelFactors O A (nestedRawAssocShape s Q)) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option s.inner.index))
    (fun i => match i with
      | none => ((FiniteTensor.singletonIso (V := C)).app (O.obj s.outerProfile)).symm
      | some _ => Iso.refl _)

/-- The actual original raw-source object of the nested colimit
diagram maps isomorphically to the common three-level tensor source. -/
def nestedRawThreeLevelIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s) :
    (nestedRawTensorDiagram O A s).obj Q ≅ threeLevelTensorSource O A (nestedRawAssocShape s Q) :=
  (FiniteTensor.tensor (V := C)).mapIso (nestedRawSourceFactorsIso O A s Q) ≪≫
    nestedThreeLevelSourceIso O A (nestedRawAssocShape s Q)

/-- The actual original local branch operation evaluations after
their tensor source-frame isomorphism are the original nested raw
branch evaluations and original root identity. -/
theorem nestedRawSource_operationInjection (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s) :
    (nestedRawSourceFactorsIso O.toCollection A s Q).hom ≫
      nestedThreeLevelOperationFactors O A (nestedRawAssocShape s Q) ≫
      operationInjectionFactors O.toCollection A (nestedRawAssocShape s Q).outerAfterInnerData =
    nestedRawBranchEvaluationFactors O A s Q := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      exact heq_of_eq (sourceSingletonCancel ((FiniteTensor.singletonIso (V := C)).app
        (O.toCollection.obj s.outerProfile)))
    | some i => exact heq_of_eq (Category.id_comp _)




end CategoryTheory.Operad.Tensor
end
end
end source_NestedRawSourceFrame

/- Source proof segment: NestedRawInnerRoute -/
section source_NestedRawInnerRoute
/-!
# Actual inner-first free operation route on nested raw colimit injections
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem tensorInnerRouteSquare {V : Type*} [Category* V]
    {X A B S T Y : V} (i : X ⟶ A) (frame : A ⟶ B) (e : S ≅ B)
    (op : B ⟶ T) (eval : T ⟶ Y) (r : X ⟶ T)
    (h : i ≫ frame ≫ op = r) :
    i ≫ (frame ≫ e.inv) ≫ (e.hom ≫ op ≫ eval) = r ≫ eval := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using congrArg (· ≫ eval) h

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- Tensoring every actual local free-operation beta square
evaluates the original inner-first algebra route on each nested
raw source colimit injection. -/
theorem nestedRawInnerRoute (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s) :
    (nestedRawTensorCocone O.toCollection A s).ι.app Q ≫
      (nestedRawPointIso O.toCollection A s).hom ≫
      algebraSubstitutionInner (freeOperations O A) s =
    (FiniteTensor.tensor (V := C)).map (nestedRawBranchEvaluationFactors O A s Q) ≫
      freeOperation O A (profileInputs s.outerProfile) := by
  let T := FiniteTensor.tensor (V := C)
  let i := T.map (nestedRawInjectionFactors O.toCollection A s Q)
  let frame := T.map (nestedRawPointFactorsIso O.toCollection A s).hom
  let e := (FiniteTensor.flattenIso (V := C)).app (nestedOperationFactors O.toCollection
    (profileCoinvariants
    O.toCollection A) s)
  let op := T.map (innerOperationMap (freeOperations O A) s)
  let eval := freeOperation O A (profileInputs s.outerProfile)
  let r := T.map (nestedRawBranchEvaluationFactors O A s Q)
  have h : i ≫ frame ≫ op = r :=
    ((congrArg (i ≫ ·) (T.map_comp _ _).symm).trans (T.map_comp _ _).symm).trans
      (congrArg T.map (nestedRawBranchEvaluation O A s Q))
  rw [nestedRawTensorCocone_ι]
  change i ≫ (frame ≫ e.inv) ≫ (e.hom ≫ op ≫ eval) = r ≫ eval
  exact tensorInnerRouteSquare i frame e op eval r h



end CategoryTheory.Operad.Tensor
end
end
end source_NestedRawInnerRoute

/- Source proof segment: NestedThreeLevelRawRouteA -/
section source_NestedThreeLevelRawRouteA
/-!
# Original route A on the actual nested raw source tensor
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

private theorem inverseNaturalPost {V : Type*} [Category* V]
    {X Y Z : V} (e : Z ≅ Y) (a : X ⟶ Y) (b : X ⟶ Z)
    (h : a ≫ e.inv = b) : b ≫ e.hom = a := by
  rw [← h]
  exact (Category.assoc _ _ _).trans
    ((congrArg (a ≫ ·) e.inv_hom_id).trans (Category.comp_id _))

private theorem routeAAssemblySquares {V : Type*} [Category* V]
    {X A B D E F G H Y : V} (p : X ⟶ A) (q : A ⟶ B) (canonical : B ≅ D)
    (a : B ⟶ E) (b : E ⟶ F) (r : F ⟶ G) (s : G ⟶ H) (op : H ⟶ Y)
    (c : X ⟶ E) (f : F ⟶ H) (g : X ⟶ G)
    (hn : p ≫ q ≫ a = c) (hf : r ≫ s = f) (hg : c ≫ b ≫ r = g) :
    (p ≫ q ≫ canonical.hom) ≫
      (canonical.inv ≫ (a ≫ b ≫ f ≫ op)) = g ≫ s ≫ op := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hn' : (p ≫ q) ≫ a = c := (Category.assoc _ _ _).trans hn
  rw [← Category.assoc p q, ← Category.assoc (p ≫ q) a, hn', ← hf]
  simp only [Category.assoc]
  have hg' : (c ≫ b) ≫ r = g := (Category.assoc _ _ _).trans hg
  rw [← Category.assoc c b, ← Category.assoc (c ≫ b) r, hg']

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Original local substitutions on the nested raw source followed
by original outer substitution are the sealed source route A. -/
theorem nestedThreeLevelRawRouteA (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    (nestedThreeLevelSourceIso O.toCollection A s).hom ≫ threeLevelTensorRouteA O A s =
      (FiniteTensor.tensor (V := C)).map (nestedThreeLevelOperationFactors O A s) ≫
        (FiniteTensor.flattenIso (V := C)).inv.app (nestedOperationFactors O.toCollection A
          s.outerAfterInnerData) ≫
        operadSubstitutionInputs O A s.outerAfterInnerData := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let M := FiniteFamily.map T
  let N := nestedThreeLevelFactors O.toCollection A s
  let L := (FiniteFamily.map F).obj
    (partitionedCoefficientLeavesTriple
      (substitutionBranchGrouping s.outerAfterInnerData (associativityCoefficientBlocksA
        O.toCollection s))
      (substitutionBranchLeaves A s.outerAfterInnerData))
  let E := partitionedScalarLeaves
    (substitutionBranchGrouping s.outerAfterInnerData (associativityCoefficientBlocksA
      O.toCollection s))
    (substitutionBranchLeaves A s.outerAfterInnerData)
    (substitutionBranchCoefficients O.toCollection s.outerAfterInnerData)
  let e := (nestedThreeLevelBranchSourceIso O.toCollection A s).hom
  let a := partitionedCoefficientLeavesActionMap
    (substitutionBranchGrouping s.outerAfterInnerData (associativityCoefficientBlocksA
      O.toCollection s))
    (substitutionBranchLeaves A s.outerAfterInnerData)
    (substitutionBranchCoefficients O.toCollection s.outerAfterInnerData)
      (associativityCoefficientMapsA O s)
  let f := (substitutionFrameFactorsIso O.toCollection A s.outerAfterInnerData
    (associativityCoefficientBlocksA O.toCollection s)).hom
  let r := nestedThreeLevelOperationFactors O A s
  let op := operadSubstitutionInputs O A s.outerAfterInnerData
  let eN := (FiniteTensor.flattenIso (V := C)).app N
  let eL := (FiniteTensor.flattenIso (V := C)).app L
  let eE := (FiniteTensor.flattenIso (V := C)).app E
  let eR := (FiniteTensor.flattenIso (V := C)).app (nestedOperationFactors O.toCollection A
    s.outerAfterInnerData)
  let canonical := substitutionCanonicalSourceIso A s.outerAfterInnerData
    (associativityCoefficientBlocksA
    O.toCollection s)
    (Iso.refl (ColoredOperadObj.AssocInsertion.flattenedGroupingA O.toCollection s)) (𝟙
      s.outerAfterInnerData.totalProfile)
  have hn' : eN.inv ≫ T.map (F.map e) ≫ eL.hom = T.map (M.map e) := by
    have hnat := (FiniteTensor.flattenIso (V := C)).inv.naturality e
    change T.map (M.map e) ≫ eL.inv = eN.inv ≫ T.map (F.map e) at hnat
    exact (Category.assoc _ _ _).symm.trans
      (inverseNaturalPost eL (T.map (M.map e)) (eN.inv ≫ T.map (F.map e)) hnat)
  have hf₀ : M.map e ≫ a ≫ M.map f = r := nestedThreeLevelBranchEvaluation O A s
  have hf : T.map (M.map e) ≫ T.map a ≫ T.map (M.map f) = T.map r :=
    ((congrArg (_ ≫ ·) (T.map_comp _ _).symm).trans (T.map_comp _ _).symm).trans
      (congrArg T.map hf₀)
  have he := (FiniteTensor.flattenIso (V := C)).inv.naturality f
  change T.map (M.map f) ≫ eR.inv = eE.inv ≫ T.map (F.map f) at he
  rw [threeLevelTensorRouteA_original]
  change (eN.inv ≫ T.map (F.map e) ≫ canonical.hom) ≫
    (canonical.inv ≫ (eL.hom ≫ T.map a ≫ (eE.inv ≫ T.map (F.map f)) ≫ op)) = _
  exact routeAAssemblySquares eN.inv (T.map (F.map e)) canonical eL.hom
    (T.map a) (T.map (M.map f)) eR.inv op (T.map (M.map e))
    (eE.inv ≫ T.map (F.map f)) (T.map r) hn' he hf



end CategoryTheory.Operad.Tensor
end
end
end source_NestedThreeLevelRawRouteA

/- Source proof segment: NestedThreeLevelRouteA -/
section source_NestedThreeLevelRouteA
/-!
# Original local and outer free operation evaluation of source route A
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem originalRouteAFromBeta {V : Type*} [Category* V]
    {X B D E F Y : V} (b : X ⟶ B) (i : B ⟶ D) (free : D ⟶ Y)
    (raw : B ⟶ E) (op : E ⟶ F) (ι : F ⟶ Y)
    (source : X ⟶ F) (hi : i ≫ free = raw ≫ op ≫ ι)
    (hs : b ≫ raw ≫ op = source) : b ≫ i ≫ free = source ≫ ι := by
  rw [hi]
  simpa only [Category.assoc] using congrArg (· ≫ ι) hs

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- Original local raw operation substitution followed by every
original total profile injection recovers the original outer input
injection factors. -/
theorem nestedThreeLevelOperationInjection (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    nestedThreeLevelOperationFactors O A s ≫ operationInjectionFactors O.toCollection A
      s.outerAfterInnerData =
    ({ equiv := Equiv.refl (Option s.branches.index)
       hom i := match i with
         | none => (FiniteTensor.singletonIso (V := C)).hom.app (O.toCollection.obj
           s.middleData.outerProfile)
         | some i => operadSubstitutionInputs O A (s.localData i) ≫
           profileι O.toCollection A (profileInputs (s.localData i).totalProfile) } :
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (nestedThreeLevelFactors
        O.toCollection A s) ⟶
        (analyticFactors O.toCollection (profileCoinvariants O.toCollection A)).obj (profileInputs
          s.outerAfterInnerData.outerProfile)) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none => exact heq_of_eq (Category.id_comp _)
    | some i => exact HEq.rfl

variable [Small.{us} W] [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- The actual original local-operation tensor and the actual
outer free operation evaluate the original three-level source route A. -/
theorem nestedThreeLevelRouteA_freeOperation (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteTensor.tensor (V := C)).map (nestedThreeLevelOperationFactors O A s) ≫
      (FiniteTensor.tensor (V := C)).map (operationInjectionFactors O.toCollection A
        s.outerAfterInnerData) ≫
      freeOperation O A (profileInputs s.outerAfterInnerData.outerProfile) =
    (nestedThreeLevelSourceIso O.toCollection A s).hom ≫ threeLevelTensorRouteA O A s ≫
      profileι O.toCollection A (profileInputs s.outerAfterInnerData.totalProfile) := by
  exact (originalRouteAFromBeta
    ((FiniteTensor.tensor (V := C)).map (nestedThreeLevelOperationFactors O A s))
    ((FiniteTensor.tensor (V := C)).map (operationInjectionFactors O.toCollection A
      s.outerAfterInnerData))
    (freeOperation O A (profileInputs s.outerAfterInnerData.outerProfile))
    ((FiniteTensor.flattenIso (V := C)).inv.app (nestedOperationFactors O.toCollection A
      s.outerAfterInnerData))
    (operadSubstitutionInputs O A s.outerAfterInnerData)
    (profileι O.toCollection A (profileInputs s.outerAfterInnerData.totalProfile))
    ((nestedThreeLevelSourceIso O.toCollection A s).hom ≫ threeLevelTensorRouteA O A s)
    (operationInjection_freeOperation O A s.outerAfterInnerData)
    (nestedThreeLevelRawRouteA O A s).symm).trans (Category.assoc _ _ _)



end CategoryTheory.Operad.Tensor
end
end
end source_NestedThreeLevelRouteA

/- Source proof segment: NestedRawInnerSourceRouteA -/
section source_NestedRawInnerSourceRouteA
/-!
# Original inner-first free operation route equals source route A
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem framedSourceRoute {V : Type*} [Category* V]
    {X B E F D Y : V} (frame : X ⟶ B) (op : B ⟶ E) (inj : E ⟶ F)
    (eval : F ⟶ Y) (source : B ⟶ D) (route : D ⟶ Y) (f : X ⟶ F)
    (hf : frame ≫ op ≫ inj = f) (hroute : op ≫ inj ≫ eval = source ≫ route) :
    f ≫ eval = (frame ≫ source) ≫ route := by
  rw [← hf]
  simp only [Category.assoc]
  rw [hroute]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- Every original nested raw colimit injection sends the actual
inner-first algebra operation composite to the original source
route A and original nested total-profile quotient injection. -/
theorem nestedRawInnerSourceRouteA (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s) :
    (nestedRawTensorCocone O.toCollection A s).ι.app Q ≫
      (nestedRawPointIso O.toCollection A s).hom ≫
      algebraSubstitutionInner (freeOperations O A) s =
    (nestedRawThreeLevelIso O.toCollection A s Q).hom ≫
      threeLevelTensorRouteA O A (nestedRawAssocShape s Q) ≫
      profileι O.toCollection A (profileInputs (nestedRawAssocShape s
        Q).outerAfterInnerData.totalProfile) := by
  let T := FiniteTensor.tensor (V := C)
  let shape := nestedRawAssocShape s Q
  let frame := T.map (nestedRawSourceFactorsIso O.toCollection A s Q).hom
  let op := T.map (nestedThreeLevelOperationFactors O A shape)
  let inj := T.map (operationInjectionFactors O.toCollection A shape.outerAfterInnerData)
  let eval := freeOperation O A (profileInputs s.outerProfile)
  let source := (nestedThreeLevelSourceIso O.toCollection A shape).hom
  let route := threeLevelTensorRouteA O A shape
  let ι := profileι O.toCollection A (profileInputs shape.outerAfterInnerData.totalProfile)
  have hfactor : frame ≫ op ≫ inj = T.map (nestedRawBranchEvaluationFactors O A s Q) :=
    ((congrArg (frame ≫ ·) (T.map_comp _ _).symm).trans (T.map_comp _ _).symm).trans
      (congrArg T.map (nestedRawSource_operationInjection O A s Q))
  have hroute : op ≫ inj ≫ eval = source ≫ route ≫ ι :=
    nestedThreeLevelRouteA_freeOperation O A shape
  change _ = (frame ≫ source) ≫ route ≫ ι
  exact (nestedRawInnerRoute O A s Q).trans
    (framedSourceRoute frame op inj eval source (route ≫ ι)
      (T.map (nestedRawBranchEvaluationFactors O A s Q)) hfactor hroute)



end CategoryTheory.Operad.Tensor
end
end
end source_NestedRawInnerSourceRouteA

/- Source proof segment: NestedRawMiddleDiagram -/
section source_NestedRawMiddleDiagram
/-!
# Original innermost operation tensors and middle substitution source maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- In the middle-first source, all original innermost operation
summands are retained as the original middle-profile input leaves. -/
def middleTensorLeafFamily (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) : FiniteFamily C where
  index := s.middleData.totalProfile.inputs
  obj p := (operationSummandFunctor O A).obj (s.innerData.inner.obj p)

/-- The original input-first nested local raw factors are collected
into the original middle coefficient block and original innermost
operation tensors, before original O.subst at the root. -/
def middleNestedSourceFactors (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) : FiniteFamily (FiniteFamily C) where
  index := FintypeCat.of (Option s.branches.index)
  obj i := match i with
    | none => (FiniteFamily.singleton (C := C)).obj (O.obj s.middleData.outerProfile)
    | some i =>
      { index := FintypeCat.of (Option (s.localData i).inner.index)
        obj j := match j with
          | none => O.obj (s.localData i).outerProfile
          | some j => (operationSummandFunctor O A).obj ((s.localData i).inner.obj j) }

/-- The original raw local tensor becomes its original middle
coefficient and every actual innermost operation tensor. -/
def middleLocalFactorIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) (i : s.branches.index) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (nestedOperationFactors O A
      (s.localData i)) ≅
      (middleNestedSourceFactors O A s).obj (some i) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option (s.localData i).inner.index))
    (fun j => match j with
      | none => (FiniteTensor.singletonIso (V := C)).app (O.obj (s.localData i).outerProfile)
      | some _ => Iso.refl _)

/-- Each original local raw tensor is grouped into its original
middle coefficient and every original innermost tensor. -/
def middleNestedFactorsIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (nestedThreeLevelFactors O A s) ≅
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (middleNestedSourceFactors O A s) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option s.branches.index))
    (fun i => match i with
      | none => Iso.refl _
      | some i =>
        (FiniteTensor.flattenIso (V := C)).app (nestedOperationFactors O A (s.localData i)) ≪≫
          (FiniteTensor.tensor (V := C)).mapIso (middleLocalFactorIso O A s i))

/-- Regroup all original middle coefficients and original
innermost operation tensor leaves by the displayed original factor bijection. -/
def middleNestedFactorEquiv (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    ((FiniteFamily.flatten (C := C)).obj (middleNestedSourceFactors O A s)).index ≃
      ((FiniteFamily.flatten (C := C)).obj
        (coefficientLeavesNested ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
          (middleTensorLeafFamily O A s))).index where
  toFun p := match p with
    | ⟨none, _⟩ => ⟨none, none⟩
    | ⟨some i, none⟩ => ⟨none, some i⟩
    | ⟨some i, some j⟩ => ⟨some ⟨i, j⟩, PUnit.unit⟩
  invFun p := match p with
    | ⟨none, none⟩ => ⟨none, PUnit.unit⟩
    | ⟨none, some i⟩ => ⟨some i, none⟩
    | ⟨some ⟨i, j⟩, _⟩ => ⟨some i, some j⟩
  left_inv p := by
    rcases p with ⟨i, j⟩
    cases i with
    | none => cases j; rfl
    | some i => cases j <;> rfl
  right_inv p := by
    rcases p with ⟨i, j⟩
    cases i with
    | none => cases j <;> rfl
    | some p => rcases p with ⟨i, j⟩; cases j; rfl

/-- The original middle source bijection retains every coefficient
and every innermost full tensor object. -/
def middleNestedSourceIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.flatten (C := C)).obj (middleNestedSourceFactors O A s) ≅
      (FiniteFamily.flatten (C := C)).obj
        (coefficientLeavesNested ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
          (middleTensorLeafFamily O A s)) :=
  FiniteFamily.isoOfReindex (middleNestedFactorEquiv O A s)
    (fun p => by
      rcases p with ⟨i, j⟩
      cases i with
      | none => cases j; rfl
      | some i => cases j <;> rfl)



end CategoryTheory.Operad.Tensor
end
end
end source_NestedRawMiddleDiagram

/- Source proof segment: MiddleOperationTensor -/
section source_MiddleOperationTensor
/-!
# Actual original middle coefficient tensor and retained innermost operations
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The exact source middle coefficient and every original
innermost full operation tensor after source regrouping. -/
def middleOperationTensorSourceIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (nestedThreeLevelFactors O A s)) ≅
      (coefficientLeafTensorFunctor (middleTensorLeafFamily O A s)).obj
        ((FiniteTensor.tensor (V := C)).obj ((ColoredOperadObj.substitutionFactors O).obj
          s.middleData)) :=
  (FiniteTensor.tensor (V := C)).mapIso (middleNestedFactorsIso O A s) ≪≫
    ((FiniteTensor.flattenIso (V := C)).app (middleNestedSourceFactors O A s)).symm ≪≫
    (FiniteTensor.tensor (V := C)).mapIso (middleNestedSourceIso O A s) ≪≫
    coefficientLeavesNormalizationIso ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
      (middleTensorLeafFamily O A s)

/-- The original middle operad coefficient substitution acts in
its sole coefficient block; all original innermost tensors are retained. -/
def middleOperationTensorMap (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (nestedThreeLevelFactors
          O.toCollection A s)) ⟶
      (coefficientLeafTensorFunctor (middleTensorLeafFamily O.toCollection A s)).obj
        (O.toCollection.obj s.middleData.totalProfile) :=
  (middleOperationTensorSourceIso O.toCollection A s).hom ≫
    (coefficientLeafTensorFunctor (middleTensorLeafFamily O.toCollection A s)).map
      (O.subst.app s.middleData)

/-- The retained original innermost operation tensors are exactly
the original coefficient/input tensor family for the flattened
second substitution. -/
def middleOperationTensorTargetIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (coefficientLeafFamilyFunctor (middleTensorLeafFamily O A s)).obj (O.obj
      s.middleData.totalProfile) ≅
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (nestedOperationFactors O A
        s.innerData) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option s.middleData.totalProfile.inputs))
    (fun i => match i with
      | none => ((FiniteTensor.singletonIso (V := C)).app (O.obj s.middleData.totalProfile)).symm
      | some _ => Iso.refl _)

/-- The original middle and flattened substitution route on
the complete actual nested source, before applying its totalHom. -/
def middleOperationTensorRoute (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (nestedThreeLevelFactors
          O.toCollection A s)) ⟶
      (operationSummandFunctor O.toCollection A).obj s.innerData.totalProfile :=
  middleOperationTensorMap O A s ≫
    (FiniteTensor.tensor (V := C)).map (middleOperationTensorTargetIso O.toCollection A s).hom ≫
    (FiniteTensor.flattenIso (V := C)).inv.app (nestedOperationFactors O.toCollection A
      s.innerData) ≫
    operadSubstitutionInputs O A s.innerData



end CategoryTheory.Operad.Tensor
end
end
end source_MiddleOperationTensor

/- Source proof segment: MiddleTensorFrameNaturality -/
section source_MiddleTensorFrameNaturality
/-!
# Original nested raw source injections and middle coefficient tensor maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- Map every retained original innermost tensor to its actual
profile quotient point at its original middle-profile position. -/
def middleTensorLeafInjection (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    middleTensorLeafFamily O A s ⟶ profileLeafFamily (profileCoinvariants O A)
      s.middleData.totalProfile where
  equiv := Equiv.refl s.middleData.totalProfile.inputs
  hom p := profileι O A (profileInputs (s.innerData.inner.obj p))

/-- The original middle coefficient and all original leaf profile
injections form the actual middle total-profile input tensor map. -/
def middleTensorPointInjection (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (coefficientLeafTensorFunctor (middleTensorLeafFamily O A s)).obj (O.obj
      s.middleData.totalProfile) ⟶
      (operationSummandFunctor O (profileCoinvariants O A)).obj s.middleData.totalProfile :=
  (FiniteTensor.tensor (V := C)).map
    (coefficientLeafMap (𝟙 (O.obj s.middleData.totalProfile)) (middleTensorLeafInjection O A s)) ≫
      (profileCoefficientLeafTensorIso O (profileCoinvariants O A) s.middleData.totalProfile).hom

/-- Original quotient injections commute with the actual original
middle coefficient map, retaining their displayed leaf bijection. -/
theorem middleTensorCoefficientInjection (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    (coefficientLeafTensorFunctor (middleTensorLeafFamily O.toCollection A s)).map
      (O.subst.app s.middleData) ≫
      middleTensorPointInjection O.toCollection A s =
    (FiniteTensor.tensor (V := C)).map
      (coefficientLeafMap (O.subst.app s.middleData) (middleTensorLeafInjection
        O.toCollection A s)) ≫
      (profileCoefficientLeafTensorIso O.toCollection (profileCoinvariants O.toCollection A)
        s.middleData.totalProfile).hom := by
  let T := FiniteTensor.tensor (V := C)
  let f := O.subst.app s.middleData
  let l := middleTensorLeafInjection O.toCollection A s
  let p := (profileCoefficientLeafTensorIso O.toCollection (profileCoinvariants O.toCollection A)
    s.middleData.totalProfile).hom
  have h := coefficientLeafMap_pre f (𝟙 _) l
  rw [Category.comp_id] at h
  change T.map ((coefficientLeafFamilyFunctor (middleTensorLeafFamily O.toCollection A s)).map f) ≫
    (T.map (coefficientLeafMap (𝟙 _) l) ≫ p) = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ p) ((T.map_comp _ _).symm.trans (congrArg T.map h)))



end CategoryTheory.Operad.Tensor
end
end
end source_MiddleTensorFrameNaturality

/- Source proof segment: MiddleNestedInjectionFactors -/
section source_MiddleNestedInjectionFactors
/-!
# Original innermost tensor injection factors at each local source
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem mapIdentityCommuting {V : Type*} [Category* V]
    {X Y : V} (f : X ⟶ Y) : f ≫ 𝟙 Y = 𝟙 X ≫ f := by simp only [Category.comp_id, Category.id_comp]

private theorem reflexiveTransportId {V : Type*} [Category* V] {X Y : V} (f : X ⟶ Y) (h : X = X) :
    f = (eqToHom h ≫ 𝟙 X) ≫ f := by
  have hh : h = rfl := Subsingleton.elim _ _
  rw [hh]
  simp only [eqToHom_refl, Category.id_comp]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The original local middle coefficient and every actual
innermost operation profile injection are applied independently. -/
def middleNestedInputMap (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    middleNestedSourceFactors O A s ⟶ nestedOperationFactors O (profileCoinvariants O A)
      s.middleData where
  equiv := Equiv.refl (Option s.branches.index)
  hom i := match i with
    | none => 𝟙 ((FiniteFamily.singleton (C := C)).obj (O.obj s.middleData.outerProfile))
    | some i =>
      { equiv := Equiv.refl (Option (s.localData i).inner.index)
        hom j := match j with
          | none => 𝟙 (O.obj (s.localData i).outerProfile)
          | some j => profileι O A (profileInputs ((s.localData i).inner.obj j)) }

/-- The original local raw source injection equals the original
local flattening and original coefficient singleton collapse followed
by all actual innermost profile injections. -/
theorem middleNestedRawInputMap (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s) :
    (nestedRawSourceFactorsIso O A s Q).hom ≫
      (middleNestedFactorsIso O A (nestedRawAssocShape s Q)).hom ≫
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).map
        (middleNestedInputMap O A (nestedRawAssocShape s Q)) =
    nestedRawInjectionFactors O A s Q ≫ (nestedRawPointFactorsIso O A s).hom := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      let e := (FiniteTensor.singletonIso (V := C)).app (O.obj s.outerProfile)
      change HEq (e.inv ≫ (𝟙 _ ≫ (FiniteTensor.tensor (V := C)).map (𝟙 _))) (𝟙 _ ≫ e.inv)
      exact heq_of_eq ((congrArg (e.inv ≫ ·) ((congrArg (_ ≫
        ·) ((FiniteTensor.tensor (V := C)).map_id _)).trans
        (Category.id_comp _))).trans (mapIdentityCommuting e.inv))
    | some i =>
      apply heq_of_eq
      let P := profileInputs (s.inner.obj i)
      let R := Q (some i)
      let a := (FiniteTensor.flattenIso (V := C)).hom.app
        (nestedOperationFactors O A (tupleSubstitutionShape P ((slotProfileTupleFunctor P).obj R)))
      let b := (middleLocalFactorIso O A (nestedRawAssocShape s Q) i).hom
      let c := (middleNestedInputMap O A (nestedRawAssocShape s Q)).hom (some i)
      have hfactor : b ≫ c = rawOperationSlotInjectionFactors O A P R := by
        apply FiniteFamily.Hom_ext
        · rfl
        · intro j
          cases j with
          | none =>
            with_unfolding_all
              exact heq_of_eq (show (FiniteTensor.singletonIso (V := C)).hom.app _ ≫ 𝟙 _ =
                (𝟙 _ ≫ (FiniteTensor.singletonIso (V := C)).hom.app _) ≫ 𝟙 _ from
                  congrArg (· ≫ 𝟙 _) (Category.id_comp _).symm)
          | some j =>
            with_unfolding_all
              exact heq_of_eq (show 𝟙 _ ≫ profileι O A (R (some j)) =
                (eqToHom _ ≫ 𝟙 _) ≫ profileι O A (R (some j)) from
                  (Category.id_comp _).trans (reflexiveTransportId (profileι O A (R (some j))) _))
      have h := rawOperationSlotInjection O A P R
      change 𝟙 _ ≫ (a ≫ (FiniteTensor.tensor (V := C)).map b) ≫
          (FiniteTensor.tensor (V := C)).map c =
        (rawSubstitutionCocone O A P).ι.app R ≫ 𝟙 _
      have hs : (a ≫ (FiniteTensor.tensor (V := C)).map b) ≫ (FiniteTensor.tensor (V := C)).map c =
          a ≫ (FiniteTensor.tensor (V := C)).map (rawOperationSlotInjectionFactors O A P R) :=
        (Category.assoc _ _ _).trans
          (congrArg (a ≫ ·) (((FiniteTensor.tensor (V := C)).map_comp _ _).symm.trans
            (congrArg (FiniteTensor.tensor (V := C)).map hfactor)))
      exact (Category.id_comp _).trans (hs.trans (h.symm.trans (Category.comp_id _).symm))



end CategoryTheory.Operad.Tensor
end
end
end source_MiddleNestedInjectionFactors

/- Source proof segment: MiddleSourceInjectionSquare -/
section source_MiddleSourceInjectionSquare
/-!
# Actual middle tensor source and original raw profile injections
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, Limits.HasColimitsOfShape (AnalyticIndex W d) C]

/-- The original middle coefficient/innermost tensor source
regrouping commutes with each actual original leaf profile injection. -/
theorem middleNestedSource_injection (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.flatten (C := C)).map (middleNestedInputMap O A s) ≫
      (substitutionToLeavesIso O (profileCoinvariants O A) s.middleData).hom =
    (middleNestedSourceIso O A s).hom ≫
      (FiniteFamily.flatten (C := C)).map
        (coefficientLeavesNestedMap (𝟙 ((ColoredOperadObj.substitutionFactors O).obj s.middleData))
          (middleTensorLeafInjection O A s)) := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro p
    rcases p with ⟨i, j⟩
    cases i with
    | none => cases j; rfl
    | some i => cases j <;> rfl
  · intro p
    rcases p with ⟨i, j⟩
    cases i with
    | none =>
      cases j
      exact heq_of_eq (show (𝟙 (O.obj s.middleData.outerProfile)) ≫ ((𝟙 _) ≫ ((𝟙 _) ≫ 𝟙 _)) =
        (𝟙 _) ≫ 𝟙 _ from by simp only [Category.id_comp])
    | some i =>
      cases j with
      | none =>
        exact heq_of_eq (show (𝟙 (O.obj (s.localData i).outerProfile)) ≫ ((𝟙 _) ≫ ((𝟙 _) ≫ 𝟙 _)) =
          (𝟙 _) ≫ 𝟙 _ from by simp only [Category.id_comp])
      | some j =>
        let f := profileι O A (profileInputs ((s.localData i).inner.obj j))
        exact heq_of_eq (show f ≫ ((𝟙 _) ≫ ((𝟙 _) ≫ 𝟙 _)) = (𝟙 _) ≫ f from by
          simp only [Category.id_comp, Category.comp_id])



end CategoryTheory.Operad.Tensor
end
end
end source_MiddleSourceInjectionSquare

/- Source proof segment: CoefficientLeafComposition -/
section source_CoefficientLeafComposition
/-!
# Actual coefficient and retained-leaf map composition
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Apply an original coefficient map before or after changing the
original retained leaf family. -/
theorem coefficientLeafMap_naturality {X Y : C} {L M : FiniteFamily C}
    (f : X ⟶ Y) (l : L ⟶ M) :
    (coefficientLeafFamilyFunctor L).map f ≫ coefficientLeafMap (𝟙 Y) l =
      coefficientLeafMap (𝟙 X) l ≫ (coefficientLeafFamilyFunctor M).map f := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro i
    cases i <;> rfl
  · intro i
    cases i with
    | none => exact heq_of_eq ((Category.comp_id f).trans (Category.id_comp f).symm)
    | some i => exact heq_of_eq ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- Separate the original coefficient map from the original leaf
map without changing either of their finite positions. -/
theorem coefficientLeafMap_eq {X Y : C} {L M : FiniteFamily C}
    (f : X ⟶ Y) (l : L ⟶ M) :
    coefficientLeafMap f l = (coefficientLeafFamilyFunctor L).map f ≫
      coefficientLeafMap (𝟙 Y) l := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro i
    cases i <;> rfl
  · intro i
    cases i with
    | none => exact heq_of_eq (Category.comp_id f).symm
    | some i => exact heq_of_eq (Category.id_comp _).symm

/-- Original coefficient tensor substitution followed by the
actual target leaf-frame map is a single original joint slot map. -/
theorem coefficientLeafMap_post_reframe {X Y Z : C} {L M N : FiniteFamily C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (l : L ⟶ M) (m : M ⟶ N) :
    coefficientLeafMap f l ≫ (coefficientLeafFamilyFunctor M).map g ≫
      coefficientLeafMap (𝟙 Z) m = coefficientLeafMap (f ≫ g) (l ≫ m) := by
  rw [← Category.assoc, coefficientLeafMap_post, coefficientLeafMap_comp, Category.comp_id]




end CategoryTheory.Operad.Tensor
end
end
end source_CoefficientLeafComposition

/- Source proof segment: MiddleTensorInjectionEvaluation -/
section source_MiddleTensorInjectionEvaluation
/-!
# Actual middle tensor substitution evaluation on original leaf injections
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

private theorem middleInjectionFourSquares {V : Type*} [Category* V]
    {X A B C D E F G H I Y : V}
    (a : X ⟶ A) (r' : A ⟶ B) (op : B ⟶ Y) (r : X ⟶ C) (b : C ⟶ B)
    (q : C ⟶ D) (u : B ⟶ E) (j : D ⟶ E) (n : D ⟶ F) (n' : E ⟶ G)
    (z : F ⟶ G) (c : F ⟶ H) (c' : G ⟶ I) (p : I ⟶ Y) (h : H ⟶ Y)
    (hraw : a ≫ r' = r ≫ b) (hs : b ≫ u = q ≫ j) (hn : j ≫ n' = n ≫ z)
    (hcoef : z ≫ c' ≫ p = c ≫ h) (hop : op = u ≫ n' ≫ c' ≫ p) :
    a ≫ r' ≫ op = r ≫ q ≫ n ≫ c ≫ h := by
  rw [← Category.assoc a r', hraw, hop]
  simp only [Category.assoc]
  rw [← Category.assoc b u, hs]
  simp only [Category.assoc]
  rw [← Category.assoc j n', hn]
  simp only [Category.assoc]
  rw [hcoef]
variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, Limits.HasColimitsOfShape (AnalyticIndex W d) C]

/-- After grouping original middle coefficients and innermost
operation tensors, the original leaf profile injections commute
with actual original operadic substitution. -/
theorem middleTensorInjectionEvaluation (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).map (middleNestedInputMap
          O.toCollection A s)) ≫
      (FiniteTensor.flattenIso (V := C)).inv.app
        (nestedOperationFactors O.toCollection (profileCoinvariants O.toCollection A)
          s.middleData) ≫
      operadSubstitutionInputs O (profileCoinvariants O.toCollection A) s.middleData =
    (FiniteTensor.flattenIso (V := C)).inv.app (middleNestedSourceFactors O.toCollection A s) ≫
      (FiniteTensor.tensor (V := C)).map (middleNestedSourceIso O.toCollection A s).hom ≫
      coefficientLeavesNormalization ((ColoredOperadObj.substitutionFactors
        O.toCollection).obj s.middleData)
        (middleTensorLeafFamily O.toCollection A s) ≫
      (coefficientLeafTensorFunctor (middleTensorLeafFamily O.toCollection A s)).map
        (O.subst.app s.middleData) ≫
      middleTensorPointInjection O.toCollection A s := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let M := FiniteFamily.map T
  let N := middleNestedSourceFactors O.toCollection A s
  let N' := nestedOperationFactors O.toCollection (profileCoinvariants O.toCollection A)
    s.middleData
  let k := (ColoredOperadObj.substitutionFactors O.toCollection).obj s.middleData
  let l := middleTensorLeafFamily O.toCollection A s
  let l' := profileLeafFamily (profileCoinvariants O.toCollection A) s.middleData.totalProfile
  let a₀ := middleNestedInputMap O.toCollection A s
  let q₀ := (middleNestedSourceIso O.toCollection A s).hom
  let u₀ := (substitutionToLeavesIso O.toCollection (profileCoinvariants O.toCollection A)
    s.middleData).hom
  let j₀ := F.map (coefficientLeavesNestedMap (𝟙 k) (middleTensorLeafInjection O.toCollection A s))
  let a := T.map (M.map a₀)
  let r := (FiniteTensor.flattenIso (V := C)).inv.app N
  let r' := (FiniteTensor.flattenIso (V := C)).inv.app N'
  let b := T.map (F.map a₀)
  let q := T.map q₀
  let u := T.map u₀
  let j := T.map j₀
  let n := coefficientLeavesNormalization k l
  let n' := coefficientLeavesNormalization k l'
  let f := O.subst.app s.middleData
  let c := (coefficientLeafTensorFunctor l).map f
  let c' := (coefficientLeafTensorFunctor l').map f
  let z := T.map (coefficientLeafMap (𝟙 (T.obj k)) (middleTensorLeafInjection O.toCollection A s))
  let p := (profileCoefficientLeafTensorIso O.toCollection (profileCoinvariants O.toCollection A)
    s.middleData.totalProfile).hom
  let h := middleTensorPointInjection O.toCollection A s
  let op := operadSubstitutionInputs O (profileCoinvariants O.toCollection A) s.middleData
  have hraw : a ≫ r' = r ≫ b := (FiniteTensor.flattenIso (V := C)).inv.naturality a₀
  have hs₀ : F.map a₀ ≫ u₀ = q₀ ≫ j₀ := middleNestedSource_injection O.toCollection A s
  have hs : b ≫ u = q ≫ j := (T.map_comp _ _).symm.trans
    ((congrArg T.map hs₀).trans (T.map_comp _ _))
  have hn : j ≫ n' = n ≫ z := by
    have hh := coefficientLeavesNormalization_naturality (𝟙 k) (middleTensorLeafInjection
      O.toCollection A s)
    rw [T.map_id] at hh
    exact hh
  have hcoef : z ≫ c' ≫ p = c ≫ h := by
    have hh := coefficientLeafMap_naturality f (middleTensorLeafInjection O.toCollection A s)
    have hc : z ≫ c' = c ≫ T.map (coefficientLeafMap (𝟙 _) (middleTensorLeafInjection
      O.toCollection A s)) :=
      (T.map_comp _ _).symm.trans ((congrArg T.map hh.symm).trans (T.map_comp _ _))
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ p) hc).trans (Category.assoc _ _ _))
  have hop : op = u ≫ n' ≫ c' ≫ p := operadSubstitutionInputs_profile_factorization O _ s.middleData
  change a ≫ r' ≫ op = r ≫ q ≫ n ≫ c ≫ h
  exact middleInjectionFourSquares a r' op r b q u j n n' z c c' p h hraw hs hn hcoef hop



end CategoryTheory.Operad.Tensor
end
end
end source_MiddleTensorInjectionEvaluation

/- Source proof segment: NestedRawMiddleEvaluation -/
section source_NestedRawMiddleEvaluation
/-!
# Actual original middle substitution on nested raw source colimit injections
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem sourceInputFactorThree {V : Type*} [Category* V]
    {X A B C D E Y : V} (i : X ⟶ A) (p : A ⟶ B) (r : B ⟶ C) (op : C ⟶ Y)
    (frame : X ⟶ D) (branchFrame : D ⟶ E) (input : E ⟶ B) (tail : E ⟶ Y)
    (hi : i ≫ p = frame ≫ branchFrame ≫ input) (ht : input ≫ r ≫ op = tail) :
    i ≫ (p ≫ r) ≫ op = frame ≫ branchFrame ≫ tail := by
  simp only [Category.assoc]
  rw [← Category.assoc i p, hi]
  simp only [Category.assoc]
  rw [ht]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- Every actual nested source injection evaluates the original
middle substitution by original O.subst and retains every original
innermost tensor quotient injection. -/
theorem nestedRawMiddleEvaluation (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s) :
    (nestedRawTensorCocone O.toCollection A s).ι.app Q ≫
      (nestedRawPointIso O.toCollection A s).hom ≫
      operadSubstitutionInputs O (profileCoinvariants O.toCollection A) s =
    (FiniteTensor.tensor (V := C)).map (nestedRawSourceFactorsIso O.toCollection A s Q).hom ≫
      middleOperationTensorMap O A (nestedRawAssocShape s Q) ≫
      middleTensorPointInjection O.toCollection A (nestedRawAssocShape s Q) := by
  let T := FiniteTensor.tensor (V := C)
  let M := FiniteFamily.map T
  let shape := nestedRawAssocShape s Q
  let i := (nestedRawTensorCocone O.toCollection A s).ι.app Q
  let p := T.map (nestedRawPointFactorsIso O.toCollection A s).hom
  let r := (FiniteTensor.flattenIso (V := C)).inv.app
    (nestedOperationFactors O.toCollection (profileCoinvariants O.toCollection A) s)
  let op := operadSubstitutionInputs O (profileCoinvariants O.toCollection A) s
  let frame := T.map (nestedRawSourceFactorsIso O.toCollection A s Q).hom
  let branchFrame := T.map (middleNestedFactorsIso O.toCollection A shape).hom
  let input := T.map (M.map (middleNestedInputMap O.toCollection A shape))
  let tail := (FiniteTensor.flattenIso (V := C)).inv.app (middleNestedSourceFactors
    O.toCollection A shape) ≫
    T.map (middleNestedSourceIso O.toCollection A shape).hom ≫
    coefficientLeavesNormalization ((ColoredOperadObj.substitutionFactors
      O.toCollection).obj shape.middleData)
      (middleTensorLeafFamily O.toCollection A shape) ≫
    (coefficientLeafTensorFunctor (middleTensorLeafFamily O.toCollection A shape)).map
      (O.subst.app shape.middleData) ≫
    middleTensorPointInjection O.toCollection A shape
  have hi : i ≫ p = frame ≫ branchFrame ≫ input := by
    have h := middleNestedRawInputMap O.toCollection A s Q
    have hmap := congrArg T.map h
    have hleft : T.map (nestedRawInjectionFactors O.toCollection A s Q ≫
      (nestedRawPointFactorsIso O.toCollection A
      s).hom) = i ≫ p :=
      (T.map_comp _ _).trans (congrArg (· ≫ p) (nestedRawTensorCocone_ι O.toCollection A s Q).symm)
    have hright : T.map ((nestedRawSourceFactorsIso O.toCollection A s Q).hom ≫
        (middleNestedFactorsIso O.toCollection A shape).hom ≫
          M.map (middleNestedInputMap O.toCollection A shape)) =
        frame ≫ branchFrame ≫ input := by rw [T.map_comp, T.map_comp]
    exact hleft.symm.trans (hmap.symm.trans hright)
  have ht : input ≫ r ≫ op = tail := by
    have h := middleTensorInjectionEvaluation O A shape
    with_unfolding_all exact h
  change i ≫ (p ≫ r) ≫ op = _
  exact (sourceInputFactorThree i p r op frame branchFrame input tail hi ht).trans
    (by simp only [middleOperationTensorMap, middleOperationTensorSourceIso, Iso.trans_hom,
      Functor.mapIso_hom, coefficientLeavesNormalizationIso_hom, Category.assoc]; rfl)



end CategoryTheory.Operad.Tensor
end
end
end source_NestedRawMiddleEvaluation

/- Source proof segment: MiddleTensorFreeOperation -/
section source_MiddleTensorFreeOperation
/-!
# Actual original flattened free operation evaluated by middle tensor leaf injections
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem middleFreeOperationBeta {V : Type*} [Category* V]
    {X B C D E Y : V} (a : X ⟶ B) (b : B ⟶ D) (c : B ⟶ C) (i : C ⟶ D)
    (f : D ⟶ Y) (r : C ⟶ E) {F : V} (op : E ⟶ F) (ι : F ⟶ Y)
    (hb : b = c ≫ i) (hβ : i ≫ f = r ≫ op ≫ ι) :
    a ≫ b ≫ f = (a ≫ c ≫ r ≫ op) ≫ ι := by
  rw [hb]
  simp only [Category.assoc]
  rw [hβ]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The original source middle point leaf injections are the
original flattened inner profile operation injection factors,
with the actual coefficient singleton unitor retained. -/
theorem middleTensorPointInjection_factors (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    coefficientLeafMap (𝟙 (O.obj s.middleData.totalProfile)) (middleTensorLeafInjection O A s) ≫
      (profileOperationFactorsIso O (profileCoinvariants O A) s.middleData.totalProfile).hom =
    (middleOperationTensorTargetIso O A s).hom ≫ operationInjectionFactors O A s.innerData := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro i
    cases i <;> rfl
  · intro i
    cases i with
    | none =>
      let e := (FiniteTensor.singletonIso (V := C)).app (O.obj s.middleData.totalProfile)
      change HEq (𝟙 _ ≫ 𝟙 _) (e.inv ≫ e.hom)
      exact heq_of_eq ((Category.id_comp _).trans e.inv_hom_id.symm)
    | some p =>
      let f := profileι O A (profileInputs (s.innerData.inner.obj p))
      change HEq (f ≫ 𝟙 _) (𝟙 _ ≫ f)
      exact heq_of_eq ((Category.comp_id f).trans (Category.id_comp f).symm)

variable [Small.{us} W] [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- Apply the actual middle coefficient map, retain every original
innermost profile injection, and evaluate the actual flattened
free operation by the original operad coefficient substitution. -/
theorem middleTensorMap_freeOperation (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    middleOperationTensorMap O A s ≫ middleTensorPointInjection O.toCollection A s ≫
      freeOperation O A (profileInputs s.middleData.totalProfile) =
    middleOperationTensorRoute O A s ≫ profileι O.toCollection A (profileInputs
      s.innerData.totalProfile) := by
  let T := FiniteTensor.tensor (V := C)
  let a := middleOperationTensorMap O A s
  let b := middleTensorPointInjection O.toCollection A s
  let c := T.map (middleOperationTensorTargetIso O.toCollection A s).hom
  let i := T.map (operationInjectionFactors O.toCollection A s.innerData)
  let f := freeOperation O A (profileInputs s.middleData.totalProfile)
  let r := (FiniteTensor.flattenIso (V := C)).inv.app (nestedOperationFactors O.toCollection
    A s.innerData)
  let op := operadSubstitutionInputs O A s.innerData
  let ι := profileι O.toCollection A (profileInputs s.innerData.totalProfile)
  have hb : b = c ≫ i :=
    (T.map_comp _ _).symm.trans
      ((congrArg T.map (middleTensorPointInjection_factors O.toCollection A s)).trans
        (T.map_comp _ _))
  have hβ : i ≫ f = r ≫ op ≫ ι := operationInjection_freeOperation O A s.innerData
  change a ≫ b ≫ f = (a ≫ c ≫ r ≫ op) ≫ ι
  exact middleFreeOperationBeta a b c i f r op ι hb hβ



end CategoryTheory.Operad.Tensor
end
end
end source_MiddleTensorFreeOperation

/- Source proof segment: OperadicMultiplication -/
section source_OperadicMultiplication
/-!
# Original tensor-operadic multiplication

The actual free operation family descends through the original
profile coinvariants. Its naturality and characteristic original
profile/slot equations are proved; the three monad laws remain
separate source-operad unit/associativity descents.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- The original profilewise free operation maps descend to the
actual original operadic multiplication on profile coinvariants. -/
def profileMultiplication (O : ColoredOperadObj W C) (A : W → C) :
    profileCoinvariants O.toCollection (profileCoinvariants O.toCollection A) ⟶
      profileCoinvariants O.toCollection A :=
  (freeOperations O A).desc

/-- Every original outer profile recovers its actual constructed
free operation from the original multiplication. -/
@[reassoc (attr := simp)]
theorem profileMultiplication_profile (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    profileι O.toCollection (profileCoinvariants O.toCollection A) P ≫ profileMultiplication O A d =
      freeOperation O A P :=
  (freeOperations O A).ι_desc P

/-- Every original coefficient/input tuple evaluates the actual
multiplication by the original operadic substitution and profile
quotient map, including empty profiles. -/
@[reassoc]
theorem profileMultiplication_slot (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (profileSlotTensorCocone O.toCollection A P).ι.app Q ≫
        profileι O.toCollection (profileCoinvariants O.toCollection A) P ≫
          profileMultiplication O A d =
      (assembledProfileSubstitutionCocone O A P).ι.app Q := by
  exact (congrArg ((profileSlotTensorCocone O.toCollection A P).ι.app Q ≫ ·)
    (profileMultiplication_profile O A P)).trans (freeOperation_ι O A P Q)

/-- Original input naturality of the actual profile multiplication. -/
theorem profileMultiplication_input (O : ColoredOperadObj W C) {A B : W → C} (f : A ⟶ B) :
    profileMap O.toCollection (profileMap O.toCollection f) ≫ profileMultiplication O B =
      profileMultiplication O A ≫ profileMap O.toCollection f := by
  funext d
  apply colimit.hom_ext
  intro P
  let iA := profileι O.toCollection (profileCoinvariants O.toCollection A) P
  let iB := profileι O.toCollection (profileCoinvariants O.toCollection B) P
  let h := (analyticSummandCarrierMap O.toCollection (profileMap O.toCollection f)).app P
  change iA ≫ (profileMap O.toCollection (profileMap O.toCollection f) d ≫
    profileMultiplication O B d) =
    iA ≫ (profileMultiplication O A d ≫ profileMap O.toCollection f d)
  exact descentInputSquare iA iB h
    (profileMap O.toCollection (profileMap O.toCollection f) d)
    (profileMultiplication O A d) (profileMultiplication O B d) (profileMap O.toCollection f d)
    (freeOperation O A P) (freeOperation O B P)
    (profileι_map O.toCollection (profileMap O.toCollection f) P)
    (profileMultiplication_profile O A P) (profileMultiplication_profile O B P)
    (freeOperation_input O f P)

/-- The actual original operadic multiplication is a natural
transformation on the color-indexed tensor profile functor. -/
def profileMultiplicationNatTrans (O : ColoredOperadObj W C) :
    profileEndofunctor O.toCollection ⋙ profileEndofunctor O.toCollection ⟶
      profileEndofunctor O.toCollection where
  app := profileMultiplication O
  naturality _ _ f := profileMultiplication_input O f




end CategoryTheory.Operad.Tensor
end
end
end source_OperadicMultiplication

/- Source proof segment: NestedRawMiddleFreeOperation -/
section source_NestedRawMiddleFreeOperation
/-!
# Actual middle-first free operation evaluation on original nested injections
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem prependEvaluation {V : Type*} [Category* V]
    {X P Z S U E Y : V} (i : X ⟶ P) (point : P ⟶ Z) (op : Z ⟶ S)
    (free : S ⟶ Y) (frame : X ⟶ U) (middle : U ⟶ E) (inj : E ⟶ S) (route : U ⟶ Y)
    (heval : i ≫ point ≫ op = frame ≫ middle ≫ inj)
    (hβ : middle ≫ inj ≫ free = route) :
    i ≫ point ≫ op ≫ free = frame ≫ route := by
  have h := congrArg (· ≫ free) heval
  simpa only [Category.assoc, hβ] using h

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- The actual coefficient-first algebra route at every original
nested tensor injection is its actual middle/flattened tensor route
and original flattened total-profile injection. -/
theorem nestedRawMiddleFreeOperation (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) (Q : NestedRawSlotTuple s) :
    (nestedRawTensorCocone O.toCollection A s).ι.app Q ≫
      (nestedRawPointIso O.toCollection A s).hom ≫
      operadSubstitutionInputs O (profileCoinvariants O.toCollection A) s ≫
      freeOperation O A (profileInputs s.totalProfile) =
    (FiniteTensor.tensor (V := C)).map (nestedRawSourceFactorsIso O.toCollection A s Q).hom ≫
      middleOperationTensorRoute O A (nestedRawAssocShape s Q) ≫
      profileι O.toCollection A (profileInputs (nestedRawAssocShape s
        Q).innerData.totalProfile) := by
  let shape := nestedRawAssocShape s Q
  let frame := (FiniteTensor.tensor (V := C)).map (nestedRawSourceFactorsIso O.toCollection
    A s Q).hom
  exact prependEvaluation ((nestedRawTensorCocone O.toCollection A s).ι.app Q)
    ((nestedRawPointIso O.toCollection A s).hom)
    (operadSubstitutionInputs O (profileCoinvariants O.toCollection A) s)
    (freeOperation O A (profileInputs s.totalProfile)) frame
    (middleOperationTensorMap O A shape) (middleTensorPointInjection O.toCollection A shape)
    (middleOperationTensorRoute O A shape ≫ profileι O.toCollection A (profileInputs
      shape.innerData.totalProfile))
    (nestedRawMiddleEvaluation O A s Q) (middleTensorMap_freeOperation O A shape)



end CategoryTheory.Operad.Tensor
end
end
end source_NestedRawMiddleFreeOperation

/- Source proof segment: ProfileQuotientOperations -/
section source_ProfileQuotientOperations
/-!
# Original full-profile coinvariant injection operations
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The original profile quotient injections form the actual
full equivariant operation-map family on all original profiles. -/
def profileQuotientOperations (O : ColoredSymmetricCollection W C) (A : W → C) :
    Operations O A (profileCoinvariants O A) where
  app _ P := profileι O A P
  equivariance _ _ _ f := profile_relabel_ι O A f

/-- Every original full profile map, including its actual output
color equality, commutes with the original profile quotient injections. -/
@[reassoc]
theorem profileι_full_relabel (O : ColoredSymmetricCollection W C) (A : W → C)
    {P Q : ColoredProfile W} (f : P ⟶ Q) :
    (operationSummandFunctor O A).map f ≫ profileι O A (profileInputs Q) =
      profileι O A (profileInputs P) ≫ eqToHom (congrArg (profileCoinvariants O A)
        f.outputColor_eq) :=
  (profileQuotientOperations O A).profile_equivariance f

/-- The original nested-total-profile quotient map uses the
original sigma-associator of all innermost operation inputs. -/
theorem profileι_assoc_total (O : ColoredSymmetricCollection W C) (A : W →
  C) (s : ColoredAssocData W) :
    (operationSummandFunctor O A).map s.totalHom ≫
      profileι O A (profileInputs s.outerAfterInnerData.totalProfile) =
    profileι O A (profileInputs s.innerData.totalProfile) :=
  (profileι_full_relabel O A s.totalHom).trans (Category.comp_id _)




end CategoryTheory.Operad.Tensor
end
end
end source_ProfileQuotientOperations

/- Source proof segment: MiddleRetainedBlocks -/
section source_MiddleRetainedBlocks
/-!
# Original retained innermost blocks in the middle tensor source
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- One original middle coefficient block and all original full
innermost operation factor families, before evaluating their tensors. -/
def middleRetainedNestedBlocks (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) : FiniteFamily (FiniteFamily C) where
  index := FintypeCat.of (Option s.middleData.totalProfile.inputs)
  obj i := match i with
    | none => (ColoredOperadObj.substitutionFactors O).obj s.middleData
    | some p => (operationFactorsFunctor O A).obj (s.innerData.inner.obj p)

/-- The original middle raw triple keeps the root and each local
coefficient singleton, and every original full innermost factor block. -/
def middleRetainedTriple (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) : FiniteFamily (FiniteFamily (FiniteFamily C)) where
  index := FintypeCat.of (Option s.branches.index)
  obj i := match i with
    | none => (FiniteFamily.singleton (C := FiniteFamily C)).obj
        ((FiniteFamily.singleton (C := C)).obj (O.obj s.middleData.outerProfile))
    | some i => nestedOperationFactors O A (s.localData i)

/-- Identify the locally flattened retained middle triple with the original three-level factors. -/
def middleRetainedTripleRawIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.map (FiniteFamily.flatten (C := C))).obj (middleRetainedTriple O A s) ≅
      nestedThreeLevelFactors O A s :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option s.branches.index))
    (fun i => match i with
      | none => FiniteFamily.singletonFlattenIso.app
          ((FiniteFamily.singleton (C := C)).obj (O.obj s.middleData.outerProfile))
      | some _ => Iso.refl _)

/-- The original flat middle coefficient singletons and original
full innermost operation factor blocks before coefficient evaluation. -/
def middleRetainedFlatBlocks (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) : FiniteFamily (FiniteFamily C) where
  index := FintypeCat.of (Sum (Option s.branches.index) s.middleData.totalProfile.inputs)
  obj i := match i with
    | Sum.inl i => (FiniteFamily.singleton (C := C)).obj
        (((ColoredOperadObj.substitutionFactors O).obj s.middleData).obj i)
    | Sum.inr p => (operationFactorsFunctor O A).obj (s.innerData.inner.obj p)

/-- The original triple outer flattening reorders only whole
singleton coefficient and whole innermost operation blocks. -/
def middleRetainedTripleFlatIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.flatten (C := FiniteFamily C)).obj (middleRetainedTriple O A s) ≅
      middleRetainedFlatBlocks O A s :=
  FiniteFamily.isoOfReindex
    { toFun := fun p => match p with
        | ⟨none, _⟩ => Sum.inl none
        | ⟨some i, none⟩ => Sum.inl (some i)
        | ⟨some i, some j⟩ => Sum.inr ⟨i, j⟩
      invFun := fun p => match p with
        | Sum.inl none => ⟨none, PUnit.unit⟩
        | Sum.inl (some i) => ⟨some i, none⟩
        | Sum.inr ⟨i, j⟩ => ⟨some i, some j⟩
      left_inv := fun p => by
        rcases p with ⟨o, i⟩
        cases o with
        | none => cases i; rfl
        | some i => cases i <;> rfl
      right_inv := fun p => by
        cases p with
        | inl i => cases i <;> rfl
        | inr p => rcases p with ⟨i, j⟩; rfl }
    (fun p => by
      rcases p with ⟨o, i⟩
      cases o with
      | none => cases i; rfl
      | some i => cases i <;> rfl)

/-- The original coefficient-first triple for the actual middle
substitution and retained full innermost operation factor families. -/
def middleCoefficientFirstTriple (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) : FiniteFamily (FiniteFamily (FiniteFamily C)) where
  index := FintypeCat.of (Option s.middleData.totalProfile.inputs)
  obj i := match i with
    | none => (FiniteFamily.map (FiniteFamily.singleton (C := C))).obj
        ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
    | some p => (FiniteFamily.singleton (C := FiniteFamily C)).obj
        ((operationFactorsFunctor O A).obj (s.innerData.inner.obj p))

/-- Identify the flattened coefficient-first middle triple with the retained middle blocks. -/
def middleCoefficientFirstFlatIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.flatten (C := FiniteFamily C)).obj (middleCoefficientFirstTriple O A s) ≅
      middleRetainedFlatBlocks O A s :=
  FiniteFamily.isoOfReindex
    { toFun := fun p => match p with
        | ⟨none, i⟩ => Sum.inl i
        | ⟨some p, _⟩ => Sum.inr p
      invFun := fun p => match p with
        | Sum.inl i => ⟨none, i⟩
        | Sum.inr p => ⟨some p, PUnit.unit⟩
      left_inv := fun p => by
        rcases p with ⟨o, i⟩
        cases o with
        | none => rfl
        | some p => cases i; rfl
      right_inv := fun p => by cases p <;> rfl }
    (fun p => by
      rcases p with ⟨o, i⟩
      cases o with
      | none => rfl
      | some p => cases i; rfl)

/-- Regroup the retained middle triple into the coefficient-first middle triple after flattening. -/
def middleTripleRegroupIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.flatten (C := FiniteFamily C)).obj (middleRetainedTriple O A s) ≅
      (FiniteFamily.flatten (C := FiniteFamily C)).obj (middleCoefficientFirstTriple O A s) :=
  middleRetainedTripleFlatIso O A s ≪≫ (middleCoefficientFirstFlatIso O A s).symm

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleRetainedBlocks

/- Source proof segment: MiddleNestedSourceMaps -/
section source_MiddleNestedSourceMaps
/-!
# Original middle coefficient and retained-operation source collapse maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Evaluate the original coefficient singletons in each local
branch, retaining every full innermost operation tensor. -/
def middleRetainedLocalCollapse (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.map (FiniteFamily.map (FiniteTensor.tensor (V :=
      C)))).obj (middleRetainedTriple O A s) ⟶
      middleNestedSourceFactors O A s where
  equiv := Equiv.refl (Option s.branches.index)
  hom i := match i with
    | none => (FiniteFamily.singleton (C := C)).map
        ((FiniteTensor.singletonIso (V := C)).hom.app (O.obj s.middleData.outerProfile))
    | some i => (middleLocalFactorIso O A s i).hom

/-- The source raw triple tensor has exactly the original middle
branch flattening and coefficient singleton maps. -/
theorem middleRetainedLocal_source (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (middleRetainedTripleRawIso O A s).hom ≫
      (middleNestedFactorsIso O A s).hom =
    (FiniteFamily.mapIso (FiniteTensor.flattenIso (V := C))).hom.app (middleRetainedTriple O A s) ≫
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (middleRetainedLocalCollapse O A
        s) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      let X := O.obj s.middleData.outerProfile
      let a := (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.singleton (C := FiniteFamily C)).obj ((FiniteFamily.singleton (C :=
          C)).obj X))
      let sX := (FiniteTensor.singletonIso (V := C)).hom.app X
      let h := (FiniteTensor.tensor (V := C)).map
        (FiniteFamily.singletonFlattenIso.hom.app ((FiniteFamily.singleton (C := C)).obj X))
      change HEq (h ≫ 𝟙 _) (a ≫ (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.singleton (C := C)).map sX))
      -- The actual double-singleton root map is fixed by the two source unit laws.
      apply heq_of_eq
      apply (cancel_mono (FiniteTensor.singletonIso.hom.app X)).1
      have hc := coefficientLeavesTriple_leaf X
      exact (congrArg (· ≫ sX) (Category.comp_id h)).trans
        (hc.symm.trans (Category.assoc _ _ _).symm)
    | some i =>
      let T := FiniteTensor.tensor (V := C)
      let N := nestedOperationFactors O A (s.localData i)
      let a := (FiniteTensor.flattenIso (V := C)).hom.app N
      let b := T.map (middleLocalFactorIso O A s i).hom
      change HEq (T.map (𝟙 ((FiniteFamily.flatten (C := C)).obj N)) ≫ (a ≫ b)) (a ≫ b)
      exact heq_of_eq ((congrArg (· ≫ (a ≫ b)) (T.map_id _)).trans (Category.id_comp _))

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleNestedSourceMaps

/- Source proof segment: MiddleFlatSourceCollapse -/
section source_MiddleFlatSourceCollapse
/-!
# Exact original flat-block source collapse toward the middle tensor frame
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The tensor of the original flat singleton coefficients and
full innermost factor blocks is collected into the middle raw source. -/
def middleFlatScalarCollapse (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (middleRetainedFlatBlocks O A s) ⟶
      (FiniteFamily.flatten (C := C)).obj (middleNestedSourceFactors O A s) where
  equiv :=
    { toFun := fun i => match i with
        | Sum.inl none => ⟨none, PUnit.unit⟩
        | Sum.inl (some i) => ⟨some i, none⟩
        | Sum.inr ⟨i, j⟩ => ⟨some i, some j⟩
      invFun := fun p => match p with
        | ⟨none, _⟩ => Sum.inl none
        | ⟨some i, none⟩ => Sum.inl (some i)
        | ⟨some i, some j⟩ => Sum.inr ⟨i, j⟩
      left_inv := fun i => by cases i with
        | inl i => cases i <;> rfl
        | inr p => rcases p with ⟨i, j⟩; rfl
      right_inv := fun p => by
        rcases p with ⟨o, i⟩
        cases o with
        | none => cases i; rfl
        | some i => cases i <;> rfl }
  hom i := match i with
    | Sum.inl none => (FiniteTensor.singletonIso (V := C)).hom.app (O.obj s.middleData.outerProfile)
    | Sum.inl (some i) => (FiniteTensor.singletonIso (V :=
      C)).hom.app (O.obj (s.localData i).outerProfile)
    | Sum.inr p => 𝟙 _

theorem middleRetainedFlatCollapse_square (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (middleRetainedTripleFlatIso O A s).hom ≫
      middleFlatScalarCollapse O A s =
    (FiniteFamily.flatten (C := C)).map (middleRetainedLocalCollapse O A s) := by
  apply FiniteFamily.Hom_ext
  · ext p
    rcases p with ⟨o, i⟩
    cases o with
    | none => cases i; rfl
    | some i => cases i <;> rfl
  · intro p
    rcases p with ⟨o, i⟩
    cases o with
    | none =>
      cases i
      let X := O.obj s.middleData.outerProfile
      let f := (FiniteTensor.singletonIso (V := C)).hom.app X
      change HEq ((FiniteTensor.tensor (V := C)).map (𝟙 ((FiniteFamily.singleton (C :=
        C)).obj X)) ≫ f) f
      exact heq_of_eq ((congrArg (· ≫ f) ((FiniteTensor.tensor (V :=
        C)).map_id _)).trans (Category.id_comp f))
    | some i =>
      cases i with
      | none =>
        let X := O.obj (s.localData i).outerProfile
        let f := (FiniteTensor.singletonIso (V := C)).hom.app X
        change HEq ((FiniteTensor.tensor (V := C)).map (𝟙 ((FiniteFamily.singleton (C :=
          C)).obj X)) ≫ f) f
        exact heq_of_eq ((congrArg (· ≫ f) ((FiniteTensor.tensor (V :=
          C)).map_id _)).trans (Category.id_comp f))
      | some j =>
        let L := (operationFactorsFunctor O A).obj ((s.localData i).inner.obj j)
        let X := (FiniteTensor.tensor (V := C)).obj L
        change HEq ((FiniteTensor.tensor (V := C)).map (𝟙 L) ≫ 𝟙 X) (𝟙 X)
        exact heq_of_eq ((congrArg (· ≫ 𝟙 X) ((FiniteTensor.tensor (V :=
          C)).map_id L)).trans (Category.id_comp _))

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleFlatSourceCollapse

/- Source proof segment: NestedTensorRegrouping -/
section source_NestedTensorRegrouping
/-!
# Actual triple tensor regrouping through the original flat block family
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- Identify local then global tensor assembly of the original three-level finite family. -/
def nestedTensorAssemblyIso (N : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.flatten (C := C)).obj
          ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj N)) ≅
      (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
          ((FiniteFamily.map (FiniteFamily.map (FiniteTensor.tensor (V := C)))).obj N)) :=
  (FiniteTensor.flattenIso (V := C)).app ((FiniteFamily.map (FiniteFamily.flatten (C :=
    C))).obj N) ≪≫
    (FiniteTensor.tensor (V := C)).mapIso ((FiniteFamily.mapIso (FiniteTensor.flattenIso (V
      := C))).app N)

/-- Identify tensor assembly after flattening the outer two levels of the original finite family. -/
def flatNestedTensorAssemblyIso (N : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.flatten (C := C)).obj
          ((FiniteFamily.flatten (C := FiniteFamily C)).obj N)) ≅
      (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
          ((FiniteFamily.map (FiniteFamily.map (FiniteTensor.tensor (V := C)))).obj N)) :=
  (FiniteTensor.flattenIso (V := C)).app ((FiniteFamily.flatten (C := FiniteFamily C)).obj N) ≪≫
    (FiniteTensor.tensor (V := C)).mapIso ((FiniteFamily.flattenMapIso (FiniteTensor.tensor
      (V := C))).app N) ≪≫
    (FiniteTensor.flattenIso (V := C)).app ((FiniteFamily.map (FiniteFamily.map
      (FiniteTensor.tensor (V := C)))).obj N)

theorem nestedTensorAssembly_assoc (N : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (nestedTensorAssemblyIso N).hom =
      (FiniteTensor.tensor (V := C)).map (FiniteFamily.flattenAssocIso.hom.app N) ≫
        (flatNestedTensorAssemblyIso N).hom :=
  FiniteTensor.flattenAssocLaw_app_unfold N

/-- The actual tensor of a whole-block map between the two flat
triple groupings is compatible with the original nested assembly. -/
theorem flatNestedTensorAssembly_naturality
    {N M : FiniteFamily (FiniteFamily (FiniteFamily C))}
    (k : (FiniteFamily.flatten (C := FiniteFamily C)).obj N ≅
      (FiniteFamily.flatten (C := FiniteFamily C)).obj M) :
    (FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map k.hom) ≫
      (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.flatten (C :=
        FiniteFamily C)).obj M) =
    (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.flatten (C :=
      FiniteFamily C)).obj N) ≫
      (FiniteTensor.tensor (V := C)).map ((FiniteFamily.map (FiniteTensor.tensor (V :=
        C))).map k.hom) :=
  (FiniteTensor.flattenIso (V := C)).hom.naturality k.hom

end CategoryTheory.Operad.Tensor
end
end
end source_NestedTensorRegrouping

/- Source proof segment: MiddleOriginalAssembly -/
section source_MiddleOriginalAssembly
/-!
# Original middle local tensor source assembly through its flat block tensors
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Original local raw tensor evaluation is precisely the triple
assembly and original coefficient singleton collapse maps. -/
theorem middleOriginalNestedAssembly (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).map (middleRetainedTripleRawIso O
          A s).hom) ≫
      (FiniteTensor.tensor (V := C)).map (middleNestedFactorsIso O A s).hom =
    (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.mapIso (FiniteTensor.flattenIso (V :=
          C))).hom.app (middleRetainedTriple O A s)) ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).map (middleRetainedLocalCollapse
          O A s)) := by
  let T := FiniteTensor.tensor (V := C)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map (middleRetainedLocal_source O A s)).trans (T.map_comp _ _))

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleOriginalAssembly

/- Source proof segment: MiddleSourceScalarSquares -/
section source_MiddleSourceScalarSquares
@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe u v

theorem middleSourceNestedFromSquares {C : Type u} [Category.{v} C]
    {X R S A B D E Y : C}
    (q : X ⟶ R) (r : R ⟶ S) (g : S ⟶ A) (inv : A ⟶ B) (j : B ⟶ D) (n : D ⟶ Y)
    (a : X ⟶ E) (b : E ⟶ S)
    (h : q ≫ r = a ≫ b) :
    q ≫ r ≫ g ≫ inv ≫ j ≫ n = a ≫ b ≫ g ≫ inv ≫ j ≫ n := by
  have h' := congrArg (fun z => z ≫ g ≫ inv ≫ j ≫ n) h
  simpa only [Category.assoc] using h'

theorem middleSourceMappedPair {C : Type u} [Category.{v} C]
    {X A B D E Y : C} (a : X ⟶ A) (b : A ⟶ B) (c : B ⟶ D)
    (d : A ⟶ E) (e : E ⟶ D) (f : D ⟶ Y)
    (h : b ≫ c = d ≫ e) : a ≫ b ≫ c ≫ f = a ≫ d ≫ e ≫ f := by
  have h' := congrArg (fun z => a ≫ z ≫ f) h
  simpa only [Category.assoc] using h'

theorem middleSourcePairedAssembly {C : Type u} [Category.{v} C]
    {X R S A B D E F Y : C}
    (q : X ⟶ R) (r : R ⟶ S) (g : S ⟶ A) (inv : A ⟶ B) (j : B ⟶ D) (n : D ⟶ Y)
    (a : X ⟶ E) (b : E ⟶ S) (d : E ⟶ F) (c : F ⟶ A)
    (h : q ≫ r = a ≫ b) (hc : b ≫ g = d ≫ c) :
    (q ≫ r) ≫ ((g ≫ inv ≫ j) ≫ n) = (a ≫ d) ≫ c ≫ inv ≫ j ≫ n := by
  simp only [Category.assoc]
  rw [← Category.assoc q r, h]
  simp only [Category.assoc]
  rw [← Category.assoc b g, hc]
  simp only [Category.assoc]

end CategoryTheory.Operad.Tensor
end
end source_MiddleSourceScalarSquares

/- Source proof segment: MiddleRawRegrouping -/
section source_MiddleRawRegrouping
/-!
# Actual original full raw factors between the middle tensor groupings
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The complete original input-first triple is regrouped by the
actual finite associator and whole coefficient/operation block permutation. -/
def middleRawTripleIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.flatten (C := C)).obj
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj (middleRetainedTriple O A s)) ≅
      (FiniteFamily.flatten (C := C)).obj
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
          (middleCoefficientFirstTriple O A s)) :=
  FiniteFamily.flattenAssocIso.app (middleRetainedTriple O A s) ≪≫
    (FiniteFamily.flatten (C := C)).mapIso (middleTripleRegroupIso O A s) ≪≫
    (FiniteFamily.flattenAssocIso.app (middleCoefficientFirstTriple O A s)).symm

/-- The original nested raw tensor source is identified with the
coefficient-first full raw tensor before any coefficient substitution. -/
def middleRawSourceIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (nestedThreeLevelFactors O A s)) ≅
      (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.flatten (C := C)).obj
          ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
            (middleCoefficientFirstTriple O A s))) :=
  ((FiniteTensor.flattenIso (V := C)).app (nestedThreeLevelFactors O A s)).symm ≪≫
    (FiniteTensor.tensor (V := C)).mapIso
      ((FiniteFamily.flatten (C := C)).mapIso (middleRetainedTripleRawIso O A s)).symm ≪≫
    (FiniteTensor.tensor (V := C)).mapIso (middleRawTripleIso O A s)

/-- The original raw triple source tensor before any local block
evaluation is identified with the original tensor of nested raw branches. -/
def middleOriginalRawTensorIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.flatten (C := C)).obj
          ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj (middleRetainedTriple O A s))) ≅
      (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (nestedThreeLevelFactors O A s)) :=
  (FiniteTensor.tensor (V := C)).mapIso
      ((FiniteFamily.flatten (C := C)).mapIso (middleRetainedTripleRawIso O A s)) ≪≫
    (FiniteTensor.flattenIso (V := C)).app (nestedThreeLevelFactors O A s)

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleRawRegrouping

/- Source proof segment: MiddleSourceNestedComparison -/
section source_MiddleSourceNestedComparison
/-!
# Original middle source before its common flat-block normalization
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

theorem middleSourceNestedComparison (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (middleOriginalRawTensorIso O A s).hom ≫ (middleOperationTensorSourceIso O A s).hom =
      (nestedTensorAssemblyIso (middleRetainedTriple O A s)).hom ≫
        (FiniteTensor.tensor (V := C)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := C))).map
            (middleRetainedLocalCollapse O A s)) ≫
        (FiniteTensor.flattenIso (V := C)).inv.app (middleNestedSourceFactors O A s) ≫
        (FiniteTensor.tensor (V := C)).map (middleNestedSourceIso O A s).hom ≫
        coefficientLeavesNormalization ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
          (middleTensorLeafFamily O A s) := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let N := middleRetainedTriple O A s
  let raw := nestedThreeLevelFactors O A s
  let e := (middleRetainedTripleRawIso O A s).hom
  let q := T.map (F.map e)
  let r := (FiniteTensor.flattenIso (V := C)).hom.app raw
  let g := T.map (middleNestedFactorsIso O A s).hom
  let inv := (FiniteTensor.flattenIso (V := C)).inv.app (middleNestedSourceFactors O A s)
  let j := T.map (middleNestedSourceIso O A s).hom
  let n := coefficientLeavesNormalization ((ColoredOperadObj.substitutionFactors O).obj
    s.middleData)
    (middleTensorLeafFamily O A s)
  let a := (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.map F).obj N)
  let b := T.map ((FiniteFamily.map T).map e)
  let d := T.map ((FiniteFamily.mapIso (FiniteTensor.flattenIso (V := C))).hom.app N)
  let c := T.map ((FiniteFamily.map T).map (middleRetainedLocalCollapse O A s))
  have hn : q ≫ r = a ≫ b := (FiniteTensor.flattenIso (V := C)).hom.naturality e
  have hc : b ≫ g = d ≫ c := middleOriginalNestedAssembly O A s
  have hraw : (middleOriginalRawTensorIso O A s).hom = q ≫ r := rfl
  have hsource : (middleOperationTensorSourceIso O A s).hom = (g ≫ inv ≫ j) ≫ n := by
    change g ≫ inv ≫ j ≫
      (coefficientLeavesNormalizationIso ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
        (middleTensorLeafFamily O A s)).hom = _
    rw [coefficientLeavesNormalizationIso_hom]
    exact (congrArg (g ≫ ·) (Category.assoc inv j n).symm).trans
      (Category.assoc g (inv ≫ j) n).symm
  have hassembly : (nestedTensorAssemblyIso N).hom = a ≫ d := rfl
  rw [hraw, hsource, hassembly]
  exact middleSourcePairedAssembly q r g inv j n a b d c hn hc



end CategoryTheory.Operad.Tensor
end
end
end source_MiddleSourceNestedComparison

/- Source proof segment: MiddleCoefficientFirstMaps -/
section source_MiddleCoefficientFirstMaps
/-!
# Original coefficient-first middle source evaluation maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Identify the locally flattened coefficient-first middle triple with the retained nested
blocks. -/
def middleCoefficientFirstRawIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.map (FiniteFamily.flatten (C := C))).obj (middleCoefficientFirstTriple O A s) ≅
      middleRetainedNestedBlocks O A s :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option s.middleData.totalProfile.inputs))
    (fun i => match i with
      | none => FiniteFamily.mapSingletonFlattenIso.app
          ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
      | some p => FiniteFamily.singletonFlattenIso.app ((operationFactorsFunctor O A).obj
        (s.innerData.inner.obj p)))

/-- Identify evaluated retained middle blocks with the original middle coefficient and leaf
family. -/
def middleRetainedEvaluatedIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (middleRetainedNestedBlocks O A s) ≅
      (coefficientLeafFamilyFunctor (middleTensorLeafFamily O A s)).obj
        ((FiniteTensor.tensor (V := C)).obj ((ColoredOperadObj.substitutionFactors O).obj
          s.middleData)) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option s.middleData.totalProfile.inputs))
    (fun i => match i with
      | none => Iso.refl _
      | some _p => Iso.refl _)

/-- The original coefficient-first triple's block tensors collapse
only their original coefficient and operation singleton indices. -/
def middleCoefficientFirstScalarCollapse (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        ((FiniteFamily.map (FiniteFamily.map (FiniteTensor.tensor (V :=
          C)))).obj (middleCoefficientFirstTriple O A s))
          ⟶
      (coefficientLeafFamilyFunctor (middleTensorLeafFamily O A s)).obj
        ((FiniteTensor.tensor (V := C)).obj ((ColoredOperadObj.substitutionFactors O).obj
          s.middleData)) where
  equiv := Equiv.refl (Option s.middleData.totalProfile.inputs)
  hom i := match i with
    | none => (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.mapIso (FiniteTensor.singletonIso (V := C))).hom.app
          ((ColoredOperadObj.substitutionFactors O).obj s.middleData))
    | some p => (FiniteTensor.singletonIso (V := C)).hom.app
        ((operationSummandFunctor O A).obj (s.innerData.inner.obj p))

theorem middleCoefficientFirstCollapse_square (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.mapIso (FiniteTensor.flattenIso (V := C))).hom.app
      (middleCoefficientFirstTriple O A s) ≫
      middleCoefficientFirstScalarCollapse O A s =
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (middleCoefficientFirstRawIso O A s).hom ≫
      (middleRetainedEvaluatedIso O A s).hom := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      let K := (ColoredOperadObj.substitutionFactors O).obj s.middleData
      have h := mapSingletonFlattenLaw_app K
      change HEq
        ((FiniteTensor.flattenIso (V := C)).hom.app
          ((FiniteFamily.map (FiniteFamily.singleton (C := C))).obj K) ≫
          (FiniteTensor.tensor (V := C)).map ((FiniteFamily.mapIso
            (FiniteTensor.singletonIso (V := C))).hom.app K))
        ((FiniteTensor.tensor (V := C)).map (FiniteFamily.mapSingletonFlattenIso.hom.app K) ≫ 𝟙 _)
      exact heq_of_eq (h.symm.trans (Category.comp_id _).symm)
    | some p =>
      let L := (operationFactorsFunctor O A).obj (s.innerData.inner.obj p)
      let X := (FiniteTensor.tensor (V := C)).obj L
      have h := singletonFlattenLaw_app L
      change HEq
        ((FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.singleton (C :=
          FiniteFamily C)).obj L) ≫
          (FiniteTensor.singletonIso (V := C)).hom.app X)
        ((FiniteTensor.tensor (V := C)).map (FiniteFamily.singletonFlattenIso.hom.app L) ≫ 𝟙 _)
      exact heq_of_eq (h.symm.trans (Category.comp_id _).symm)

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleCoefficientFirstMaps

/- Source proof segment: MiddleRetainedNormalization -/
section source_MiddleRetainedNormalization
/-!
# Original middle retained-tensor source normalization
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Identify the original coefficient-first tensor source with the retained middle tensor source. -/
def middleRetainedSourceIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.flatten (C := C)).obj
          ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
            (middleCoefficientFirstTriple O A s))) ≅
      (coefficientLeafTensorFunctor (middleTensorLeafFamily O A s)).obj
        ((FiniteTensor.tensor (V := C)).obj ((ColoredOperadObj.substitutionFactors O).obj
          s.middleData)) :=
  (FiniteTensor.tensor (V := C)).mapIso
      ((FiniteFamily.flatten (C := C)).mapIso (middleCoefficientFirstRawIso O A s)) ≪≫
    (FiniteTensor.flattenIso (V := C)).app (middleRetainedNestedBlocks O A s) ≪≫
    (FiniteTensor.tensor (V := C)).mapIso (middleRetainedEvaluatedIso O A s)

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleRetainedNormalization

/- Source proof segment: MiddleFlatCollapseComparison -/
section source_MiddleFlatCollapseComparison
/-!
# Original flat block coefficient and operation singleton collapse comparison
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- All original singleton coefficient tensors are collapsed and
all original whole innermost operation tensors are retained. -/
def middleFlatRetainedScalarMap (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (middleRetainedFlatBlocks O A s) ⟶
      (FiniteFamily.flatten (C := C)).obj
        (coefficientLeavesNested ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
          (middleTensorLeafFamily O A s)) where
  equiv :=
    { toFun := fun i => match i with
        | Sum.inl i => ⟨none, i⟩
        | Sum.inr p => ⟨some p, PUnit.unit⟩
      invFun := fun p => match p with
        | ⟨none, i⟩ => Sum.inl i
        | ⟨some p, _⟩ => Sum.inr p
      left_inv := fun i => by cases i <;> rfl
      right_inv := fun p => by
        rcases p with ⟨o, i⟩
        cases o with
        | none => rfl
        | some p => cases i; rfl }
  hom i := match i with
    | Sum.inl i => (FiniteTensor.singletonIso (V := C)).hom.app
        (((ColoredOperadObj.substitutionFactors O).obj s.middleData).obj i)
    | Sum.inr p => 𝟙 _

theorem middleFlatRetainedScalarMap_original (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    middleFlatRetainedScalarMap O A s =
      middleFlatScalarCollapse O A s ≫ (middleNestedSourceIso O A s).hom := by
  apply FiniteFamily.Hom_ext
  · ext i
    cases i with
    | inl i => cases i <;> rfl
    | inr p => rcases p with ⟨i, j⟩; rfl
  · intro i
    cases i with
    | inl i =>
      cases i with
      | none => exact heq_of_eq (Category.comp_id _).symm
      | some i => exact heq_of_eq (Category.comp_id _).symm
    | inr p =>
      exact heq_of_eq (Category.id_comp _).symm

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleFlatCollapseComparison

/- Source proof segment: MiddleCoefficientFirstNormalization -/
section source_MiddleCoefficientFirstNormalization
/-!
# Original coefficient-first tensor assembly with whole retained operation leaves
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Normalize the assembled retained middle blocks to the original coefficient-and-leaf tensor. -/
def middleFlatTensorNormalize (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (middleRetainedFlatBlocks O A s)) ⟶
      (coefficientLeafTensorFunctor (middleTensorLeafFamily O A s)).obj
        ((FiniteTensor.tensor (V := C)).obj ((ColoredOperadObj.substitutionFactors O).obj
          s.middleData)) :=
  (FiniteTensor.tensor (V := C)).map (middleFlatRetainedScalarMap O A s) ≫
    coefficientLeavesNormalization ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
      (middleTensorLeafFamily O A s)

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleCoefficientFirstNormalization

/- Source proof segment: MiddleCoefficientFlatComparison -/
section source_MiddleCoefficientFlatComparison
/-!
# Actual flat coefficient-first source comparison retaining operation tensors
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The retained middle coefficient block and each original tensor block of its leaves. -/
def middleCoefficientTensorBlocks (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) : FiniteFamily (FiniteFamily C) where
  index := FintypeCat.of (Option s.middleData.totalProfile.inputs)
  obj i := match i with
    | none => (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        ((FiniteFamily.map (FiniteFamily.singleton (C := C))).obj
          ((ColoredOperadObj.substitutionFactors O).obj s.middleData))
    | some p => (FiniteFamily.singleton (C := C)).obj
        ((operationSummandFunctor O A).obj (s.innerData.inner.obj p))

/-- Identify the evaluated coefficient-first triple with the retained middle tensor blocks. -/
def middleCoefficientTensorBlocksIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.map (FiniteFamily.map (FiniteTensor.tensor (V :=
      C)))).obj (middleCoefficientFirstTriple O A s) ≅
      middleCoefficientTensorBlocks O A s :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option s.middleData.totalProfile.inputs))
    (fun i => match i with
      | none => Iso.refl _
      | some _ => Iso.refl _)

/-- Collapse each retained middle tensor block to its original coefficient or leaf tensor. -/
def middleCoefficientTensorCollapse (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    middleCoefficientTensorBlocks O A s ⟶
      coefficientLeavesNested ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
        (middleTensorLeafFamily O A s) where
  equiv := Equiv.refl (Option s.middleData.totalProfile.inputs)
  hom i := match i with
    | none => (FiniteFamily.mapIso (FiniteTensor.singletonIso (V := C))).hom.app
        ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
    | some _ => 𝟙 _

theorem middleCoefficientScalarCollapse_factor (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    middleCoefficientFirstScalarCollapse O A s =
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).map
        (middleCoefficientTensorBlocksIso O A s).hom ≫
        (FiniteFamily.map (FiniteTensor.tensor (V := C))).map
          (middleCoefficientTensorCollapse O A s) ≫
        coefficientLeavesCollapse ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
          (middleTensorLeafFamily O A s) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      let T := FiniteTensor.tensor (V := C)
      let f := T.map ((FiniteFamily.mapIso (FiniteTensor.singletonIso (V := C))).hom.app
        ((ColoredOperadObj.substitutionFactors O).obj s.middleData))
      change HEq f (T.map (𝟙 _) ≫ f ≫ 𝟙 _)
      exact heq_of_eq ((congrArg (fun h => h ≫ f ≫ 𝟙 _) (T.map_id _)).trans
        ((Category.id_comp _).trans (Category.comp_id f))).symm
    | some p =>
      let T := FiniteTensor.tensor (V := C)
      let X := (operationSummandFunctor O A).obj (s.innerData.inner.obj p)
      let f := (FiniteTensor.singletonIso (V := C)).hom.app X
      change HEq f (T.map (𝟙 ((FiniteFamily.singleton (C := C)).obj X)) ≫
        T.map (𝟙 ((FiniteFamily.singleton (C := C)).obj X)) ≫ f)
      exact heq_of_eq (by rw [T.map_id, Category.id_comp, Category.id_comp])

theorem middleCoefficientFlatCollapse_factor (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (middleCoefficientFirstFlatIso O A
      s).hom ≫
      middleFlatRetainedScalarMap O A s =
    (FiniteFamily.flatten (C := C)).map (middleCoefficientTensorBlocksIso O A s).hom ≫
      (FiniteFamily.flatten (C := C)).map (middleCoefficientTensorCollapse O A s) := by
  apply FiniteFamily.Hom_ext
  · ext p
    rcases p with ⟨o, i⟩
    cases o with
    | none => rfl
    | some p => cases i; rfl
  · intro p
    rcases p with ⟨o, i⟩
    cases o with
    | none =>
      let X := ((ColoredOperadObj.substitutionFactors O).obj s.middleData).obj i
      let f := (FiniteTensor.singletonIso (V := C)).hom.app X
      change HEq ((FiniteTensor.tensor (V := C)).map (𝟙 ((FiniteFamily.singleton (C :=
        C)).obj X)) ≫ f) (𝟙 _ ≫ f)
      exact heq_of_eq (congrArg (· ≫ f) ((FiniteTensor.tensor (V := C)).map_id _))
    | some p =>
      cases i
      let X := (operationSummandFunctor O A).obj (s.innerData.inner.obj p)
      change HEq ((FiniteTensor.tensor (V := C)).map (𝟙 ((operationFactorsFunctor O A).obj
        (s.innerData.inner.obj p))) ≫ 𝟙 X) (𝟙 X ≫ 𝟙 X)
      exact heq_of_eq (congrArg (· ≫ 𝟙 X) ((FiniteTensor.tensor (V := C)).map_id _))

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleCoefficientFlatComparison

/- Source proof segment: MiddleCoefficientFlatAssembly -/
section source_MiddleCoefficientFlatAssembly
/-!
# Original coefficient-first flat tensor assembly
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

theorem middleFlatCollapseFromSquares {C : Type u} [Category.{v} C]
    {X A B D E F P Y : C} (d : X ⟶ A) (te : A ⟶ B) (tk : B ⟶ D) (c : D ⟶ Y)
    (fe : X ⟶ E) (fk : E ⟶ F) (n : F ⟶ D)
    (p : X ⟶ P) (q : P ⟶ F)
    (hpre : d ≫ te ≫ tk = fe ≫ fk ≫ n) (hmap : p ≫ q = fe ≫ fk) :
    d ≫ te ≫ tk ≫ c = p ≫ q ≫ n ≫ c := by
  have h := congrArg (· ≫ c) hpre
  simp only [Category.assoc] at h
  have hm := congrArg (fun z => z ≫ n ≫ c) hmap.symm
  simp only [Category.assoc] at hm
  exact h.trans hm

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The actual coefficient-first flat tensor assembly collapses
only the original coefficient and whole-operation singleton indices. -/
theorem middleCoefficientFlatAssembly (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (flatNestedTensorAssemblyIso (middleCoefficientFirstTriple O A s)).hom ≫
      (FiniteTensor.tensor (V := C)).map (middleCoefficientFirstScalarCollapse O A s) =
    (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.flatten (C := FiniteFamily C)).obj (middleCoefficientFirstTriple O A s)) ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).map
          (middleCoefficientFirstFlatIso O A s).hom) ≫
      middleFlatTensorNormalize O A s := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let N := middleCoefficientFirstTriple O A s
  let a := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.flatten (C := FiniteFamily C)).obj N)
  let M := (FiniteFamily.map (FiniteFamily.map T)).obj N
  let e := (middleCoefficientTensorBlocksIso O A s).hom
  let k := middleCoefficientTensorCollapse O A s
  let c := coefficientLeavesCollapse ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
    (middleTensorLeafFamily O A s)
  have hn := (FiniteTensor.flattenIso (V := C)).hom.naturality e
  have hk := (FiniteTensor.flattenIso (V := C)).hom.naturality k
  have hf := middleCoefficientScalarCollapse_factor O A s
  have hflat := middleCoefficientFlatCollapse_factor O A s
  let d := (FiniteTensor.flattenIso (V := C)).hom.app M
  let p := T.map ((FiniteFamily.map T).map (middleCoefficientFirstFlatIso O A s).hom)
  let q := T.map (middleFlatRetainedScalarMap O A s)
  let n := (FiniteTensor.flattenIso (V := C)).hom.app
    (coefficientLeavesNested ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
      (middleTensorLeafFamily O A s))
  let fe := T.map (F.map e)
  let fk := T.map (F.map k)
  let te := T.map ((FiniteFamily.map T).map e)
  let tk := T.map ((FiniteFamily.map T).map k)
  let d' := (FiniteTensor.flattenIso (V := C)).hom.app (middleCoefficientTensorBlocks O A s)
  have h1 : fe ≫ d' = d ≫ te := hn
  have h2 : fk ≫ n = d' ≫ tk := hk
  have hmap : p ≫ q = fe ≫ fk :=
    (T.map_comp _ _).symm.trans ((congrArg T.map hflat).trans (T.map_comp _ _))
  have hc : d ≫ T.map (middleCoefficientFirstScalarCollapse O A s) = p ≫ q ≫ n ≫ T.map c := by
    have hscalar := congrArg T.map hf
    let e' := (FiniteFamily.map T).map e
    let k' := (FiniteFamily.map T).map k
    have hcomp : T.map (e' ≫ k' ≫ c) = te ≫ tk ≫ T.map c :=
      (T.map_comp e' (k' ≫ c)).trans (congrArg (te ≫ ·) (T.map_comp k' c))
    have hh : T.map (middleCoefficientFirstScalarCollapse O A s) = te ≫ tk ≫ T.map c :=
      hscalar.trans hcomp
    have hpre : d ≫ te ≫ tk = fe ≫ fk ≫ n := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ tk) h1.symm).trans
          ((Category.assoc _ _ _).trans (congrArg (fe ≫ ·) h2.symm)))
    exact (congrArg (d ≫ ·) hh).trans
      (middleFlatCollapseFromSquares d te tk (T.map c) fe fk n p q hpre hmap)
  let z := T.map ((FiniteFamily.flattenMapIso T).hom.app N)
  have hz : z = 𝟙 _ := by
    change T.map (𝟙 _) = 𝟙 _
    exact T.map_id _
  have hleft : (flatNestedTensorAssemblyIso N).hom = a ≫ d := by
    change a ≫ z ≫ d = a ≫ d
    exact (congrArg (a ≫ ·) (congrArg (· ≫ d) hz)).trans (congrArg (a ≫ ·) (Category.id_comp d))
  exact (congrArg (· ≫ T.map (middleCoefficientFirstScalarCollapse O A s)) hleft).trans
    ((Category.assoc _ _ _).trans (congrArg (a ≫ ·) hc))

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleCoefficientFlatAssembly

/- Source proof segment: MiddleOriginalFlatSource -/
section source_MiddleOriginalFlatSource
/-!
# Original middle source collapse and coefficient-first input bijection
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

theorem middleOriginalFlatSource_square (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.flatten (C := C)).map (middleRetainedLocalCollapse O A s) ≫
        (middleNestedSourceIso O A s).hom =
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (middleRetainedTripleFlatIso O A
        s).hom ≫
        middleFlatRetainedScalarMap O A s := by
  have h := middleRetainedFlatCollapse_square O A s
  have q := middleFlatRetainedScalarMap_original O A s
  exact (congrArg (· ≫ (middleNestedSourceIso O A s).hom) h.symm).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) q.symm))

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleOriginalFlatSource

/- Source proof segment: MiddleOriginalNormalization -/
section source_MiddleOriginalNormalization
/-!
# Original middle raw source normalization after local singleton collapse
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

theorem middleOriginalNormalizationFromSquares {C : Type u} [Category.{v} C]
    {X A B D E P Y : C} (a : X ⟶ A) (d : A ⟶ B) (c : B ⟶ D) (f : D ⟶ E)
    (r : A ⟶ E) (q : E ⟶ Y) {Z : C} (n : Y ⟶ Z)
    (p : A ⟶ P) (b : P ⟶ Y)
    (hc : d ≫ c ≫ f = r) (hm : r ≫ q = p ≫ b) :
    a ≫ d ≫ c ≫ f ≫ q ≫ n = a ≫ p ≫ b ≫ n := by
  have h := congrArg (fun z => a ≫ z ≫ q ≫ n) hc
  have hq := congrArg (fun z => a ≫ z ≫ n) hm
  simp only [Category.assoc] at h hq
  exact h.trans hq

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Local raw tensor evaluation followed by original middle source
regrouping agrees with the tensor of the original flat block scalar map. -/
theorem middleOriginalNormalization (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (flatNestedTensorAssemblyIso (middleRetainedTriple O A s)).hom ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).map (middleRetainedLocalCollapse
          O A s)) ≫
      (FiniteTensor.flattenIso (V := C)).inv.app (middleNestedSourceFactors O A s) ≫
      (FiniteTensor.tensor (V := C)).map (middleNestedSourceIso O A s).hom ≫
      coefficientLeavesNormalization ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
        (middleTensorLeafFamily O A s) =
    (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.flatten (C := FiniteFamily C)).obj (middleRetainedTriple O A s)) ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).map (middleRetainedTripleFlatIso
          O A s).hom) ≫
      middleFlatTensorNormalize O A s := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let N := middleRetainedTriple O A s
  let M := (FiniteFamily.map (FiniteFamily.map T)).obj N
  let k := middleRetainedLocalCollapse O A s
  let j := (middleNestedSourceIso O A s).hom
  let a := (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.flatten (C :=
    FiniteFamily C)).obj N)
  let d := (FiniteTensor.flattenIso (V := C)).hom.app M
  let di := (FiniteTensor.flattenIso (V := C)).inv.app M
  let c := T.map ((FiniteFamily.map T).map k)
  let f := (FiniteTensor.flattenIso (V := C)).inv.app (middleNestedSourceFactors O A s)
  let r := T.map (F.map k)
  let q := T.map j
  let p := T.map ((FiniteFamily.map T).map (middleRetainedTripleFlatIso O A s).hom)
  let b := T.map (middleFlatRetainedScalarMap O A s)
  let n := coefficientLeavesNormalization ((ColoredOperadObj.substitutionFactors O).obj
    s.middleData)
    (middleTensorLeafFamily O A s)
  have hn := (FiniteTensor.flattenIso (V := C)).inv.naturality k
  have hs := middleOriginalFlatSource_square O A s
  change c ≫ f = di ≫ r at hn
  have hi : d ≫ di = 𝟙 _ := (FiniteTensor.flattenIso (V := C)).hom_inv_id_app M
  have hm : r ≫ q = p ≫ b :=
    (T.map_comp _ _).symm.trans ((congrArg T.map hs).trans (T.map_comp _ _))
  let z := T.map ((FiniteFamily.flattenMapIso T).hom.app N)
  have hz : z = 𝟙 _ := by
    change T.map (𝟙 _) = 𝟙 _
    exact T.map_id _
  have hflat : (flatNestedTensorAssemblyIso N).hom = a ≫ d := by
    change a ≫ z ≫ d = a ≫ d
    exact (congrArg (a ≫ ·) (congrArg (· ≫ d) hz)).trans (congrArg (a ≫ ·) (Category.id_comp d))
  have hdc : d ≫ c ≫ f = r := by
    exact (congrArg (d ≫ ·) hn).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ r) hi).trans (Category.id_comp r)))
  have h : a ≫ d ≫ c ≫ f ≫ q ≫ n = a ≫ p ≫ b ≫ n := by
    exact middleOriginalNormalizationFromSquares a d c f r q n p b hdc hm
  exact (congrArg (fun g => g ≫ c ≫ f ≫ q ≫ n) hflat).trans
    ((Category.assoc _ _ _).trans h)

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleOriginalNormalization

/- Source proof segment: MiddleFlatRegroupingComparison -/
section source_MiddleFlatRegroupingComparison
/-!
# Original flat middle block tensor regrouping
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

omit [FiniteTensor C] in
theorem middleFlatBlockMap_composition (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (middleTripleRegroupIso O A s).hom ≫ (middleCoefficientFirstFlatIso O A s).hom =
      (middleRetainedTripleFlatIso O A s).hom := by
  change ((middleRetainedTripleFlatIso O A s).hom ≫ (middleCoefficientFirstFlatIso O A s).inv) ≫
    (middleCoefficientFirstFlatIso O A s).hom = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (middleCoefficientFirstFlatIso O A s).inv_hom_id).trans (Category.comp_id _))

theorem middleFlatTensorRegrouping (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map (middleTripleRegroupIso O A s).hom) ≫
      (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.flatten (C := FiniteFamily C)).obj (middleCoefficientFirstTriple O A s)) ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).map
          (middleCoefficientFirstFlatIso O A s).hom) =
    (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.flatten (C := FiniteFamily C)).obj (middleRetainedTriple O A s)) ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).map (middleRetainedTripleFlatIso
          O A s).hom) := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let k := (middleTripleRegroupIso O A s).hom
  let j := (middleCoefficientFirstFlatIso O A s).hom
  let h := (middleRetainedTripleFlatIso O A s).hom
  let a := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.flatten (C := FiniteFamily C)).obj (middleRetainedTriple O A s))
  let b := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.flatten (C := FiniteFamily C)).obj (middleCoefficientFirstTriple O A s))
  have hn : T.map (F.map k) ≫ b = a ≫ T.map ((FiniteFamily.map T).map k) :=
    (FiniteTensor.flattenIso (V := C)).hom.naturality k
  have hk : (FiniteFamily.map T).map k ≫ (FiniteFamily.map T).map j = (FiniteFamily.map T).map h :=
    ((FiniteFamily.map T).map_comp _ _).symm.trans
      (congrArg (FiniteFamily.map T).map (middleFlatBlockMap_composition O A s))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ T.map ((FiniteFamily.map T).map j)) hn).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (a ≫ ·) (T.map_comp _ _).symm).trans (congrArg (fun g => a ≫ T.map g) hk))))

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleFlatRegroupingComparison

/- Source proof segment: MiddleAssemblyScalarChain -/
section source_MiddleAssemblyScalarChain
@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe u v

theorem middleAssemblyScalarChain {C : Type u} [Category.{v} C]
    {X R A B D E F P Y : C}
    (n : X ⟶ R) (source : R ⟶ Y) (nestedN : X ⟶ A) (branch : A ⟶ Y)
    (assocN : X ⟶ B) (flatN : B ⟶ D) (norm : D ⟶ Y)
    (k : B ⟶ E) (flatM : E ⟶ D) (assemblyM : E ⟶ F) (collapse : F ⟶ Y)
    (assocM : P ≅ E) (nestedM : P ⟶ F) (retained : P ⟶ Y)
    (h1 : n ≫ source = nestedN ≫ branch)
    (h2 : nestedN ≫ branch = assocN ≫ flatN ≫ norm)
    (h3 : flatN = k ≫ flatM)
    (h4 : flatM ≫ norm = assemblyM ≫ collapse)
    (h5 : nestedM = assocM.hom ≫ assemblyM)
    (h6 : nestedM ≫ collapse = retained) :
    n ≫ source = assocN ≫ k ≫ assocM.inv ≫ retained := by
  have hM : assemblyM ≫ collapse = assocM.inv ≫ retained := by
    rw [← h6, h5]
    simp only [Category.assoc]
    rw [← Category.assoc assocM.inv assocM.hom, assocM.inv_hom_id, Category.id_comp]
  rw [h1, h2, h3]
  simp only [Category.assoc]
  rw [h4, hM]

theorem middleAssemblyPostcomposeTriple {C : Type u} [Category.{v} C]
    {X A B D Y : C} (a : X ⟶ A) (b : A ⟶ B) (c : B ⟶ D) (f : D ⟶ Y)
    (g : X ⟶ D) (h : g = a ≫ b ≫ c) :
    a ≫ b ≫ c ≫ f = g ≫ f := by
  simpa only [Category.assoc] using congrArg (· ≫ f) h.symm

end CategoryTheory.Operad.Tensor
end
end source_MiddleAssemblyScalarChain

/- Source proof segment: TripleAssemblyCollapse -/
section source_TripleAssemblyCollapse
/-!
# Actual two-step nested tensor assembly and scalar block maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The genuine tensor associativity law compares nested block
evaluation with flat block evaluation before any operation map. -/
theorem nestedTensorAssembly_collapse
    (N : FiniteFamily (FiniteFamily (FiniteFamily C))) {Y : C}
    (f : (FiniteTensor.tensor (V := C)).obj
      ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        ((FiniteFamily.map (FiniteFamily.map (FiniteTensor.tensor (V := C)))).obj N)) ⟶ Y) :
    (nestedTensorAssemblyIso N).hom ≫ f =
      (FiniteTensor.tensor (V := C)).map (FiniteFamily.flattenAssocIso.hom.app N) ≫
        (flatNestedTensorAssemblyIso N).hom ≫ f := by
  exact (congrArg (· ≫ f) (nestedTensorAssembly_assoc N)).trans (Category.assoc _ _ _)

end CategoryTheory.Operad.Tensor
end
end
end source_TripleAssemblyCollapse

/- Source proof segment: MiddleCoefficientAssemblyComparison -/
section source_MiddleCoefficientAssemblyComparison
/-!
# Actual coefficient-first nested assembly source comparison
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Original coefficient-first nested evaluation equals the original
middle coefficient tensor with every whole innermost operation retained. -/
theorem middleCoefficientNestedAssembly (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (nestedTensorAssemblyIso (middleCoefficientFirstTriple O A s)).hom ≫
      (FiniteTensor.tensor (V := C)).map (middleCoefficientFirstScalarCollapse O A s) =
    (middleRetainedSourceIso O A s).hom := by
  let T := FiniteTensor.tensor (V := C)
  let N := middleCoefficientFirstTriple O A s
  let q := (middleCoefficientFirstRawIso O A s).hom
  let a := (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.map
    (FiniteFamily.flatten (C := C))).obj N)
  let b := (FiniteFamily.mapIso (FiniteTensor.flattenIso (V := C))).hom.app N
  let c := middleCoefficientFirstScalarCollapse O A s
  let d := (FiniteTensor.flattenIso (V := C)).hom.app (middleRetainedNestedBlocks O A s)
  let p := (middleRetainedEvaluatedIso O A s).hom
  have hn := (FiniteTensor.flattenIso (V := C)).hom.naturality q
  have hc := middleCoefficientFirstCollapse_square O A s
  change _ = _ at hn
  change b ≫ c = (FiniteFamily.map T).map q ≫ p at hc
  change (a ≫ T.map b) ≫ T.map c = T.map ((FiniteFamily.flatten (C := C)).map q) ≫ d ≫ T.map p
  exact (Category.assoc _ _ _).trans
    ((congrArg (a ≫ ·) (T.map_comp b c).symm).trans
      ((congrArg (fun f => a ≫ T.map f) hc).trans
        ((congrArg (a ≫ ·) (T.map_comp _ _)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ T.map p) hn.symm).trans (Category.assoc _ _ _))))))

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleCoefficientAssemblyComparison

/- Source proof segment: MiddleSourceAssemblyComparison -/
section source_MiddleSourceAssemblyComparison
/-!
# Original middle source tensor assembly comparison
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

theorem middleNestedSource_regrouped (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (middleOriginalRawTensorIso O A s).hom ≫ (middleOperationTensorSourceIso O A s).hom =
      (FiniteTensor.tensor (V := C)).map (middleRawTripleIso O A s).hom ≫
        (middleRetainedSourceIso O A s).hom := by
  let T := FiniteTensor.tensor (V := C)
  let N := middleRetainedTriple O A s
  let M := middleCoefficientFirstTriple O A s
  let k := (middleTripleRegroupIso O A s).hom
  let source := (middleOperationTensorSourceIso O A s).hom
  let n := (middleOriginalRawTensorIso O A s).hom
  let branch := T.map ((FiniteFamily.map T).map (middleRetainedLocalCollapse O A s)) ≫
    (FiniteTensor.flattenIso (V := C)).inv.app (middleNestedSourceFactors O A s) ≫
    T.map (middleNestedSourceIso O A s).hom ≫
    coefficientLeavesNormalization ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
      (middleTensorLeafFamily O A s)
  let norm := middleFlatTensorNormalize O A s
  let flatN := (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.flatten (C :=
    FiniteFamily C)).obj N) ≫
    T.map ((FiniteFamily.map T).map (middleRetainedTripleFlatIso O A s).hom)
  let flatM := (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.flatten (C :=
    FiniteFamily C)).obj M) ≫
    T.map ((FiniteFamily.map T).map (middleCoefficientFirstFlatIso O A s).hom)
  let assocN := T.map (FiniteFamily.flattenAssocIso.hom.app N)
  let regroup := T.map ((FiniteFamily.flatten (C := C)).map k)
  let nestedN := (nestedTensorAssemblyIso N).hom
  let nestedM := (nestedTensorAssemblyIso M).hom
  let assemblyM := (flatNestedTensorAssemblyIso M).hom
  let collapse := T.map (middleCoefficientFirstScalarCollapse O A s)
  let assocM := T.mapIso (FiniteFamily.flattenAssocIso.app M)
  let retained := (middleRetainedSourceIso O A s).hom
  have h1 : n ≫ source = nestedN ≫ branch := middleSourceNestedComparison O A s
  have h2 : nestedN ≫ branch = assocN ≫ flatN ≫ norm := by
    have h := nestedTensorAssembly_collapse N branch
    let aN := (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.flatten (C :=
      FiniteFamily C)).obj N)
    let pN := T.map ((FiniteFamily.map T).map (middleRetainedTripleFlatIso O A s).hom)
    have hN : (flatNestedTensorAssemblyIso N).hom ≫ branch = flatN ≫ norm :=
      (middleOriginalNormalization O A s).trans (Category.assoc aN pN norm).symm
    have h' := congrArg (assocN ≫ ·) hN
    exact h.trans h'
  have h3 : flatN = regroup ≫ flatM := (middleFlatTensorRegrouping O A s).symm
  have h4 : flatM ≫ norm = assemblyM ≫ collapse :=
    (Category.assoc _ _ _).trans (middleCoefficientFlatAssembly O A s).symm
  have h5 : nestedM = assocM.hom ≫ assemblyM := nestedTensorAssembly_assoc M
  have h6 : nestedM ≫ collapse = retained := middleCoefficientNestedAssembly O A s
  have h := middleAssemblyScalarChain n source nestedN branch assocN flatN norm regroup flatM
    assemblyM collapse assocM nestedM retained h1 h2 h3 h4 h5 h6
  exact h.trans (by
    change assocN ≫ regroup ≫ T.map (FiniteFamily.flattenAssocIso.inv.app M) ≫ retained = _
    have hm := T.map_comp (FiniteFamily.flattenAssocIso.hom.app N)
      ((FiniteFamily.flatten (C := C)).map k ≫ FiniteFamily.flattenAssocIso.inv.app M)
    have hm' := T.map_comp ((FiniteFamily.flatten (C := C)).map k)
      (FiniteFamily.flattenAssocIso.inv.app M)
    exact middleAssemblyPostcomposeTriple assocN regroup
      (T.map (FiniteFamily.flattenAssocIso.inv.app M)) retained
      (T.map (middleRawTripleIso O A s).hom)
      (hm.trans (congrArg (assocN ≫ ·) hm')))

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleSourceAssemblyComparison

/- Source proof segment: MiddleSourceFactorization -/
section source_MiddleSourceFactorization
/-! # Exact original middle source factorization -/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v w
namespace CategoryTheory.Operad.Tensor
open CategoryTheory
variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

theorem middleOriginalRawTensorIso_cancel (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (middleOriginalRawTensorIso O A s).hom ≫ (middleRawSourceIso O A s).hom =
      (FiniteTensor.tensor (V := C)).map (middleRawTripleIso O A s).hom := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let a := T.map (F.map (middleRetainedTripleRawIso O A s).hom)
  let ai := T.map (F.map (middleRetainedTripleRawIso O A s).inv)
  let e := (FiniteTensor.flattenIso (V := C)).app (nestedThreeLevelFactors O A s)
  let q := T.map (middleRawTripleIso O A s).hom
  have hi : a ≫ ai = 𝟙 _ :=
    (T.map_comp _ _).symm.trans
      ((congrArg T.map ((F.map_comp _ _).symm.trans
        ((congrArg F.map (middleRetainedTripleRawIso O A s).hom_inv_id).trans (F.map_id
          _)))).trans (T.map_id _))
  change (a ≫ e.hom) ≫ e.inv ≫ ai ≫ q = q
  simp only [Category.assoc]
  rw [← Category.assoc e.hom e.inv, e.hom_inv_id, Category.id_comp,
    ← Category.assoc a ai, hi, Category.id_comp]

/-- Original weighted middle source factorization from actual finite tensor coherence. -/
theorem middleOperationTensorSource_factorization (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (middleOperationTensorSourceIso O A s).hom =
      (middleRawSourceIso O A s).hom ≫ (middleRetainedSourceIso O A s).hom := by
  let e := middleOriginalRawTensorIso O A s
  have h := middleNestedSource_regrouped O A s
  have hc := middleOriginalRawTensorIso_cancel O A s
  apply (cancel_epi e.hom).1
  exact h.trans
    ((congrArg (· ≫ (middleRetainedSourceIso O A s).hom) hc.symm).trans (Category.assoc _ _ _))


end CategoryTheory.Operad.Tensor
end
end
end source_MiddleSourceFactorization

/- Source proof segment: MiddleRetainedTarget -/
section source_MiddleRetainedTarget
/-!
# Original retained middle operation tensor after its original coefficient map
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Apply the original operad coefficient operations to the evaluated retained middle blocks. -/
def middleRetainedCoefficientMap (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (middleRetainedNestedBlocks
      O.toCollection A s) ⟶
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (nestedOperationFactors
        O.toCollection A s.innerData) where
  equiv := Equiv.refl (Option s.middleData.totalProfile.inputs)
  hom i := match i with
    | none => O.subst.app s.middleData ≫
        (FiniteTensor.singletonIso (V := C)).inv.app (O.toCollection.obj s.middleData.totalProfile)
    | some _ => 𝟙 _

/-- Original middle substitution retains the complete innermost
operation tensors as the original innerData input blocks. -/
theorem middleRetainedCoefficientMap_factor (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    (middleRetainedEvaluatedIso O.toCollection A s).hom ≫
      (coefficientLeafFamilyFunctor (middleTensorLeafFamily O.toCollection A s)).map
        (O.subst.app s.middleData) ≫
      (middleOperationTensorTargetIso O.toCollection A s).hom =
    middleRetainedCoefficientMap O A s := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      change HEq (𝟙 _ ≫ O.subst.app s.middleData ≫ (FiniteTensor.singletonIso (V := C)).inv.app _) _
      exact heq_of_eq (Category.id_comp _)
    | some i =>
      change HEq (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) (𝟙 _)
      exact heq_of_eq (by simp only [Category.id_comp])

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleRetainedTarget

/- Source proof segment: MiddleFinalScalarSquares -/
section source_MiddleFinalScalarSquares
@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe u v

theorem middleRetainedRouteScalar {C : Type u} [Category.{v} C]
    {X A B D E F P Y : C} (source : X ⟶ A) (coef : A ⟶ B) (target : B ⟶ P)
    (r : X ⟶ D) (p : D ⟶ E) (n : E ⟶ F) (j : F ⟶ A) (q : F ⟶ P)
    {R : C} (inv : P ⟶ R) (op : R ⟶ Y)
    (hs : source = r ≫ p ≫ n ≫ j) (hq : j ≫ coef ≫ target = q) :
    (source ≫ coef) ≫ target ≫ inv ≫ op = r ≫ p ≫ n ≫ q ≫ inv ≫ op := by
  rw [hs]
  simp only [Category.assoc]
  simpa only [Category.assoc] using
    congrArg (fun f => r ≫ p ≫ n ≫ f ≫ inv ≫ op) hq

theorem middleFrameScalar {C : Type u} [Category.{v} C]
    {X A B D E F Q P Y : C} (a : X ⟶ A) (b : A ⟶ B) (inv : B ⟶ D)
    (flat : D ⟶ P) (map : B ⟶ E) (ti : E ⟶ P)
    (raw : X ⟶ F) (d : F ⟶ Q) (block : A ⟶ Q) (c : Q ⟶ E)
    (op : P ⟶ Y)
    (hf : map ≫ ti = inv ≫ flat) (ha : b ≫ map = block ≫ c) (hb : raw ≫ d = a ≫ block) :
    a ≫ b ≫ inv ≫ flat ≫ op = raw ≫ d ≫ c ≫ ti ≫ op := by
  have h1 := congrArg (fun f => a ≫ b ≫ f ≫ op) hf.symm
  have h2 := congrArg (fun f => a ≫ f ≫ ti ≫ op) ha
  have h3 := congrArg (fun f => f ≫ c ≫ ti ≫ op) hb.symm
  simp only [Category.assoc] at h1 h2 h3
  exact h1.trans (h2.trans h3)

theorem middleFrameReadbackScalar {C : Type u} [Category.{v} C]
    {X A B D P Y : C} (a : X ⟶ A) (b : A ⟶ B) (frame : B ⟶ P)
    (inv : B ⟶ D) (flat : D ⟶ P) (op : P ⟶ Y) (rhs : X ⟶ Y)
    (hs : frame = inv ≫ flat) (h : a ≫ b ≫ inv ≫ flat ≫ op = rhs) :
    a ≫ b ≫ frame ≫ op = rhs := by
  rw [hs]
  simpa only [Category.assoc] using h

end CategoryTheory.Operad.Tensor
end
end source_MiddleFinalScalarSquares

/- Source proof segment: MiddleRetainedRouteFactorization -/
section source_MiddleRetainedRouteFactorization
@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Original middle and flattened operations in their exact
coefficient-first raw block source, before the original totalHom. -/
theorem middleOperationTensorRoute_retained (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    middleOperationTensorRoute O A s =
      (middleRawSourceIso O.toCollection A s).hom ≫
        (FiniteTensor.tensor (V := C)).map
          ((FiniteFamily.flatten (C := C)).map (middleCoefficientFirstRawIso O.toCollection
            A s).hom) ≫
        (FiniteTensor.flattenIso (V := C)).hom.app (middleRetainedNestedBlocks O.toCollection A s) ≫
        (FiniteTensor.tensor (V := C)).map (middleRetainedCoefficientMap O A s) ≫
        (FiniteTensor.flattenIso (V := C)).inv.app (nestedOperationFactors O.toCollection A
          s.innerData) ≫
        operadSubstitutionInputs O A s.innerData := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let source := (middleOperationTensorSourceIso O.toCollection A s).hom
  let r := (middleRawSourceIso O.toCollection A s).hom
  let p := T.map (F.map (middleCoefficientFirstRawIso O.toCollection A s).hom)
  let n := (FiniteTensor.flattenIso (V := C)).hom.app (middleRetainedNestedBlocks
    O.toCollection A s)
  let j := T.map (middleRetainedEvaluatedIso O.toCollection A s).hom
  let γ : T.obj ((ColoredOperadObj.substitutionFactors O.toCollection).obj s.middleData) ⟶
    O.toCollection.obj s.middleData.totalProfile := O.subst.app s.middleData
  let c := (coefficientLeafTensorFunctor (middleTensorLeafFamily O.toCollection A s)).map γ
  let t := T.map (middleOperationTensorTargetIso O.toCollection A s).hom
  let q := T.map (middleRetainedCoefficientMap O A s)
  have hs : source = r ≫ p ≫ n ≫ j := middleOperationTensorSource_factorization O.toCollection A s
  have hq : j ≫ c ≫ t = q := by
    let j₀ := (middleRetainedEvaluatedIso O.toCollection A s).hom
    let c₀ := (coefficientLeafFamilyFunctor (middleTensorLeafFamily O.toCollection A s)).map γ
    let t₀ := (middleOperationTensorTargetIso O.toCollection A s).hom
    exact (congrArg (j ≫ ·) (T.map_comp c₀ t₀).symm).trans
      ((T.map_comp j₀ (c₀ ≫ t₀)).symm.trans
        (congrArg T.map (middleRetainedCoefficientMap_factor O A s)))
  exact middleRetainedRouteScalar source c t r p n j q
    ((FiniteTensor.flattenIso (V := C)).inv.app (nestedOperationFactors O.toCollection A
      s.innerData))
    (operadSubstitutionInputs O A s.innerData) hs hq

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleRetainedRouteFactorization

/- Source proof segment: MiddleRouteBRawBlocks -/
section source_MiddleRouteBRawBlocks
/-!
# Actual route-B raw coefficient and whole-operation source blocks
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The route-B raw branch grouping has the original middle
coefficient block and original complete innermost factor families. -/
def middleRouteBRawBlocksIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
        (partitionedCoefficientLeavesTriple
          (substitutionBranchGrouping s.innerData (associativityCoefficientBlocksB O s))
          (substitutionBranchLeaves A s.innerData)) ≅
      middleRetainedNestedBlocks O A s :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option s.middleData.totalProfile.inputs))
    (fun i => match i with
      | none => emptyLeafRawIso ((ColoredOperadObj.substitutionFactors O).obj s.middleData)
      | some p =>
          (FiniteFamily.flatten (C := C)).mapIso
              (singletonCoefficientLeavesIso (O.obj (s.innerData.inner.obj p))
                (profileLeafFamily A (s.innerData.inner.obj p))) ≪≫
            FiniteFamily.mapSingletonFlattenIso.app
              ((coefficientLeafFamilyFunctor (profileLeafFamily A (s.innerData.inner.obj p))).obj
                (O.obj (s.innerData.inner.obj p))) ≪≫
            profileOperationFactorsIso O A (s.innerData.inner.obj p))

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleRouteBRawBlocks

/- Source proof segment: MiddleRouteBAction -/
section source_MiddleRouteBAction
/-!
# Original middle and innermost coefficient maps in route B
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

theorem middleRouteBActionMap (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    partitionedCoefficientLeavesActionMap
        (substitutionBranchGrouping s.innerData (associativityCoefficientBlocksB O.toCollection s))
        (substitutionBranchLeaves A s.innerData)
        (substitutionBranchCoefficients O.toCollection s.innerData)
        (associativityCoefficientMapsB O s) ≫
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).map
        (substitutionFrameFactorsIso O.toCollection A s.innerData
          (associativityCoefficientBlocksB O.toCollection s)).hom =
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (middleRouteBRawBlocksIso
      O.toCollection A s).hom ≫
      middleRetainedCoefficientMap O A s := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      let K := (ColoredOperadObj.substitutionFactors O.toCollection).obj s.middleData
      let γ : (FiniteTensor.tensor (V := C)).obj K ⟶ O.toCollection.obj s.middleData.totalProfile :=
        O.subst.app s.middleData
      let T := FiniteTensor.tensor (V := C)
      let X := O.toCollection.obj s.middleData.totalProfile
      let n := coefficientLeavesNormalization K (FiniteFamily.empty : FiniteFamily C)
      let f := (coefficientLeafTensorFunctor (FiniteFamily.empty : FiniteFamily C)).map γ
      let a := T.map (emptyLeafFamilyIso X).hom
      let unitor := (FiniteTensor.singletonIso (V := C)).hom.app X
      let inv := (FiniteTensor.singletonIso (V := C)).inv.app X
      have h := coefficientLeavesNormalization_empty_map K γ
      change HEq ((n ≫ f) ≫ a) (T.map (emptyLeafRawIso K).hom ≫ γ ≫ inv)
      apply heq_of_eq
      apply (cancel_mono unitor).1
      have hi := (FiniteTensor.singletonIso (V := C)).inv_hom_id_app X
      have hr : (T.map (emptyLeafRawIso K).hom ≫ γ ≫ inv) ≫ unitor =
          T.map (emptyLeafRawIso K).hom ≫ γ := by
        exact (Category.assoc _ _ _).trans
          ((congrArg (T.map (emptyLeafRawIso K).hom ≫ ·) (Category.assoc γ inv unitor)).trans
            ((congrArg (fun z => T.map (emptyLeafRawIso K).hom ≫ γ ≫ z) hi).trans
              (congrArg (T.map (emptyLeafRawIso K).hom ≫ ·) (Category.comp_id γ))))
      have hl : ((n ≫ f) ≫ a) ≫ unitor = T.map (emptyLeafRawIso K).hom ≫ γ := by
        have ht := emptyLeafTensorIso_hom X
        exact (Category.assoc _ _ _).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (n ≫ f ≫ ·) ht.symm).trans h))
      exact hl.trans hr.symm
    | some p =>
      have h := coefficientLeavesNormalization_singleton (O.toCollection.obj
        (s.innerData.inner.obj p))
        (profileLeafFamily A (s.innerData.inner.obj p))
      let q := (profileOperationFactorsIso O.toCollection A (s.innerData.inner.obj p)).hom
      let T := FiniteTensor.tensor (V := C)
      let X := O.toCollection.obj (s.innerData.inner.obj p)
      let L := profileLeafFamily A (s.innerData.inner.obj p)
      let k₀ := (FiniteFamily.flatten (C := C)).map (singletonCoefficientLeavesIso X L).hom
      let k₁ := FiniteFamily.mapSingletonFlattenIso.hom.app ((coefficientLeafFamilyFunctor L).obj X)
      change HEq
        ((coefficientLeavesNormalization ((FiniteFamily.singleton (C := C)).obj X) L ≫
          (coefficientLeafTensorFunctor L).map ((FiniteTensor.singletonIso (V :=
            C)).hom.app X)) ≫ T.map q)
        (T.map (k₀ ≫ k₁ ≫ q) ≫ 𝟙 _)
      exact heq_of_eq ((congrArg (· ≫ T.map q) h).trans
        (((T.map_comp (k₀ ≫ k₁) q).symm.trans (congrArg T.map (Category.assoc k₀ k₁ q))).trans
          (Category.comp_id _).symm))

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleRouteBAction

/- Source proof segment: MiddleRouteBFrame -/
section source_MiddleRouteBFrame
@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original route-B branch action followed by the original
frame assembly is the retained middle coefficient map on its raw blocks. -/
theorem middleRouteBFrame_action (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    fullSubstitutionPartitionRoute O A s.innerData (associativityCoefficientBlocksB
      O.toCollection s)
        (associativityCoefficientMapsB O s) =
      (FiniteTensor.tensor (V := C)).map
          ((FiniteFamily.flatten (C := C)).map (middleRouteBRawBlocksIso O.toCollection A s).hom) ≫
        (FiniteTensor.flattenIso (V := C)).hom.app (middleRetainedNestedBlocks O.toCollection A s) ≫
        (FiniteTensor.tensor (V := C)).map (middleRetainedCoefficientMap O A s) ≫
        (FiniteTensor.flattenIso (V := C)).inv.app (nestedOperationFactors O.toCollection A
          s.innerData) ≫
        operadSubstitutionInputs O A s.innerData := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let N := substitutionBranchGrouping s.innerData (associativityCoefficientBlocksB O.toCollection s)
  let L := substitutionBranchLeaves A s.innerData
  let B := substitutionBranchCoefficients O.toCollection s.innerData
  let g := associativityCoefficientMapsB O s
  let action := partitionedCoefficientLeavesActionMap N L B g
  let frame := (substitutionFrameFactorsIso O.toCollection A s.innerData
    (associativityCoefficientBlocksB O.toCollection s)).hom
  let blocks := (middleRouteBRawBlocksIso O.toCollection A s).hom
  let coef := middleRetainedCoefficientMap O A s
  have hf := (FiniteTensor.flattenIso (V := C)).inv.naturality frame
  have ha := middleRouteBActionMap O A s
  have hb := (FiniteTensor.flattenIso (V := C)).hom.naturality blocks
  let a := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.map F).obj (partitionedCoefficientLeavesTriple N L))
  let b := T.map action
  let invE := (FiniteTensor.flattenIso (V := C)).inv.app (partitionedScalarLeaves N L B)
  let flatFrame := T.map (F.map frame)
  let target := nestedOperationFactors O.toCollection A s.innerData
  let ti := (FiniteTensor.flattenIso (V := C)).inv.app target
  let mapFrame := T.map ((FiniteFamily.map T).map frame)
  let rawMap := T.map (F.map blocks)
  let d := (FiniteTensor.flattenIso (V := C)).hom.app (middleRetainedNestedBlocks
    O.toCollection A s)
  let blockMap := T.map ((FiniteFamily.map T).map blocks)
  let c := T.map coef
  have hframe : mapFrame ≫ ti = invE ≫ flatFrame := hf
  have haction : b ≫ mapFrame = blockMap ≫ c :=
    (T.map_comp _ _).symm.trans ((congrArg T.map ha).trans (T.map_comp _ _))
  have hblocks : rawMap ≫ d = a ≫ blockMap := hb
  -- Compose only fixed source tensor and original coefficient maps.
  let op := operadSubstitutionInputs O A s.innerData
  have h : a ≫ b ≫ invE ≫ flatFrame ≫ op = rawMap ≫ d ≫ c ≫ ti ≫ op := by
    exact middleFrameScalar a b invE flatFrame mapFrame ti rawMap d blockMap c op hframe
      haction hblocks
  have hs := substitutionFrameAssemblyIso_hom O.toCollection A s.innerData
    (associativityCoefficientBlocksB O.toCollection s)
  exact middleFrameReadbackScalar a b
    (substitutionFrameAssemblyIso O.toCollection A s.innerData
      (associativityCoefficientBlocksB O.toCollection s)).hom
    invE flatFrame op (rawMap ≫ d ≫ c ≫ ti ≫ op) hs h

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleRouteBFrame

/- Source proof segment: MiddleRouteBSource -/
section source_MiddleRouteBSource
/-!
# Original complete raw factor permutation toward route B
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Identify the original three-level route B source with its partitioned
coefficient-and-leaf source. -/
def middleRouteBRawSourceIso (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (FiniteFamily.flatten (C := C)).obj (nestedThreeLevelFactors O A s) ≅
      (FiniteFamily.flatten (C := C)).obj
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
          (partitionedCoefficientLeavesTriple
            (substitutionBranchGrouping s.innerData (associativityCoefficientBlocksB O s))
            (substitutionBranchLeaves A s.innerData))) :=
  (FiniteFamily.flatten (C := C)).mapIso (nestedThreeLevelBranchSourceIso O A s) ≪≫
    (partitionedCoefficientLeavesSourceIso
      (substitutionBranchGrouping s.outerAfterInnerData (associativityCoefficientBlocksA O s))
      (substitutionBranchLeaves A s.outerAfterInnerData)) ≪≫
    coefficientLeavesRawIso (associativityCoefficientIso O s)
      ((substitutionFrameLeafIso A s.outerAfterInnerData (associativityCoefficientBlocksA O s) ≪≫
          (profileLeafIso A s.totalHom).symm) ≪≫
        (substitutionFrameLeafIso A s.innerData (associativityCoefficientBlocksB O s)).symm) ≪≫
    (partitionedCoefficientLeavesSourceIso
      (substitutionBranchGrouping s.innerData (associativityCoefficientBlocksB O s))
      (substitutionBranchLeaves A s.innerData)).symm

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleRouteBSource

/- Source proof segment: SourceIdentityComponentIsos -/
section source_SourceIdentityComponentIsos
@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

theorem profileOperationFactorsIso_identity (O : ColoredSymmetricCollection W C) (A : W → C)
    (P : ColoredProfile W) : (profileOperationFactorsIso O A P).hom.HasIdentityComponents := by
  intro i
  cases i with
  | none => exact ⟨rfl, rfl⟩
  | some i => exact ⟨rfl, rfl⟩

theorem singletonCoefficientLeavesIso_identity (X : C) (L : FiniteFamily C) :
    (singletonCoefficientLeavesIso X L).hom.HasIdentityComponents := by
  intro i
  cases i with
  | none => exact ⟨rfl, rfl⟩
  | some i => exact ⟨rfl, rfl⟩

theorem singletonCoefficientLeavesIso_fibers_identity (X : C) (L : FiniteFamily C) :
    ∀ i, ((singletonCoefficientLeavesIso X L).hom.hom i).HasIdentityComponents := by
  intro i
  cases i with
  | none => exact FiniteFamily.Hom.hasIdentityComponents_id _
  | some i => exact FiniteFamily.Hom.hasIdentityComponents_id _

theorem mapSingletonFlatten_identity (L : FiniteFamily C) :
    (FiniteFamily.mapSingletonFlattenIso.hom.app L).HasIdentityComponents := by
  intro i
  rcases i with ⟨i, u⟩
  exact ⟨rfl, rfl⟩

theorem singletonFlatten_identity (L : FiniteFamily C) :
    (FiniteFamily.singletonFlattenIso.hom.app L).HasIdentityComponents := by
  intro i
  rcases i with ⟨u, i⟩
  exact ⟨rfl, rfl⟩

theorem singletonFlatten_inv_identity (L : FiniteFamily C) :
    (FiniteFamily.singletonFlattenIso.inv.app L).HasIdentityComponents := by
  intro i
  exact ⟨rfl, rfl⟩

theorem flattenAssoc_identity (N : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (FiniteFamily.flattenAssocIso.hom.app N).HasIdentityComponents := by
  intro i
  rcases i with ⟨a, ⟨b, c⟩⟩
  exact ⟨rfl, rfl⟩

theorem flattenAssoc_inv_identity (N : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (FiniteFamily.flattenAssocIso.inv.app N).HasIdentityComponents := by
  intro i
  rcases i with ⟨⟨a, b⟩, c⟩
  exact ⟨rfl, rfl⟩

end CategoryTheory.Operad.Tensor
end
end
end source_SourceIdentityComponentIsos

/- Source proof segment: RawIdentityComponentMaps -/
section source_RawIdentityComponentMaps
@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

theorem profileLeafIso_identity (A : W → C) {P Q : ColoredProfile W} (f : P ⟶ Q) :
    (profileLeafIso A f).hom.HasIdentityComponents :=
  FiniteFamily.isoOfReindex_identityComponents _ _

theorem profileLeafIso_inv_identity (A : W → C) {P Q : ColoredProfile W} (f : P ⟶ Q) :
    (profileLeafIso A f).inv.HasIdentityComponents :=
  FiniteFamily.isoOfReindex_inv_identityComponents _ _

theorem substitutionFrameLeafIso_identity (A : W → C) (s : ColoredSubstitutionData W)
    (K : Option s.inner.index → FiniteFamily C) :
    (substitutionFrameLeafIso A s K).hom.HasIdentityComponents :=
  FiniteFamily.isoOfReindex_identityComponents _ _

theorem substitutionFrameLeafIso_inv_identity (A : W → C) (s : ColoredSubstitutionData W)
    (K : Option s.inner.index → FiniteFamily C) :
    (substitutionFrameLeafIso A s K).inv.HasIdentityComponents :=
  FiniteFamily.isoOfReindex_inv_identityComponents _ _

theorem associativityCoefficientIso_identity (O : ColoredSymmetricCollection W C) (s :
  ColoredAssocData W) :
    (associativityCoefficientIso O s).hom.HasIdentityComponents :=
  FiniteFamily.isoOfReindex_identityComponents _ _

theorem coefficientLeavesNestedMap_fibers_identity {K N L M : FiniteFamily C}
    {k : K ⟶ N} {l : L ⟶ M} (hk : k.HasIdentityComponents) (hl : l.HasIdentityComponents) :
    ∀ i, ((coefficientLeavesNestedMap k l).hom i).HasIdentityComponents := by
  intro i
  cases i with
  | none => exact hk
  | some i =>
    intro u
    cases u
    obtain ⟨h, hh⟩ := hl i
    exact ⟨h, hh⟩

theorem coefficientLeavesRawIso_identity {K N L M : FiniteFamily C}
    (k : K ≅ N) (l : L ≅ M) (hk : k.hom.HasIdentityComponents) (hl : l.hom.HasIdentityComponents) :
    (coefficientLeavesRawIso k l).hom.HasIdentityComponents :=
  FiniteFamily.Hom.HasIdentityComponents.flatten_fibers
    (coefficientLeavesNestedMap_fibers_identity hk hl)

theorem coefficientLeavesRawIso_inv_identity {K N L M : FiniteFamily C}
    (k : K ≅ N) (l : L ≅ M) (hk : k.inv.HasIdentityComponents) (hl : l.inv.HasIdentityComponents) :
    (coefficientLeavesRawIso k l).inv.HasIdentityComponents :=
  FiniteFamily.Hom.HasIdentityComponents.flatten_fibers
    (coefficientLeavesNestedMap_fibers_identity hk hl)

end CategoryTheory.Operad.Tensor
end
end
end source_RawIdentityComponentMaps

/- Source proof segment: BranchIdentityComponents -/
section source_BranchIdentityComponents
@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

theorem emptyLeafNestedIso_fibers_identity (K : FiniteFamily C) :
    ∀ i, ((emptyLeafNestedIso K).hom.hom i).HasIdentityComponents := by
  intro i
  cases i with
  | none => exact FiniteFamily.Hom.hasIdentityComponents_id _
  | some e => cases e

theorem emptyLeafRawIso_identity (K : FiniteFamily C) :
    (emptyLeafRawIso K).hom.HasIdentityComponents := by
  exact (FiniteFamily.Hom.HasIdentityComponents.flatten_fibers
    (emptyLeafNestedIso_fibers_identity K)).comp
    (singletonFlatten_identity K)

theorem emptyLeafNestedIso_inv_fibers_identity (K : FiniteFamily C) :
    ∀ i, ((emptyLeafNestedIso K).inv.hom i).HasIdentityComponents := by
  intro i
  cases i
  intro j
  refine ⟨rfl, ?_⟩
  change 𝟙 (K.obj j) ≫ 𝟙 (K.obj j) = 𝟙 (K.obj j)
  exact Category.id_comp _

theorem emptyLeafRawIso_inv_identity (K : FiniteFamily C) :
    (emptyLeafRawIso K).inv.HasIdentityComponents := by
  exact (singletonFlatten_inv_identity K).comp
    (FiniteFamily.Hom.HasIdentityComponents.flatten_fibers
      (emptyLeafNestedIso_inv_fibers_identity K))

end CategoryTheory.Operad.Tensor
end
end
end source_BranchIdentityComponents

/- Source proof segment: SubstitutionIdentityComponents -/
section source_SubstitutionIdentityComponents
@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

theorem substitutionLeavesGroupingIso_inv_fibers_identity (O : ColoredSymmetricCollection W
  C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    ∀ i, ((substitutionLeavesGroupingIso O A s).inv.hom i).HasIdentityComponents := by
  intro i
  cases i with
  | none =>
    intro j
    refine ⟨rfl, ?_⟩
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  | some i =>
    intro j
    cases j
    refine ⟨rfl, ?_⟩
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _

theorem substitutionToLeavesIso_identity (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    (substitutionToLeavesIso O A s).hom.HasIdentityComponents := by
  exact (FiniteFamily.isoOfReindex_identityComponents _ _).comp
    (FiniteFamily.Hom.HasIdentityComponents.flatten_fibers
      (substitutionLeavesGroupingIso_inv_fibers_identity O A s))

theorem substitutionLeavesGroupingIso_hom_fibers_identity (O : ColoredSymmetricCollection W
  C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    ∀ i, ((substitutionLeavesGroupingIso O A s).hom.hom i).HasIdentityComponents := by
  intro i
  cases i with
  | none => exact FiniteFamily.Hom.hasIdentityComponents_id _
  | some i => exact FiniteFamily.Hom.hasIdentityComponents_id _

theorem substitutionToLeavesIso_inv_identity (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    (substitutionToLeavesIso O A s).inv.HasIdentityComponents := by
  exact (FiniteFamily.Hom.HasIdentityComponents.flatten_fibers
    (substitutionLeavesGroupingIso_hom_fibers_identity O A s)).comp
    (FiniteFamily.isoOfReindex_inv_identityComponents _ _)

end CategoryTheory.Operad.Tensor
end
end
end source_SubstitutionIdentityComponents

/- Source proof segment: NestedBranchIdentityComponents -/
section source_NestedBranchIdentityComponents
@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

theorem nestedThreeLevelBranchSourceIso_fibers_identity (O : ColoredSymmetricCollection W C)
  (A : W → C)
    (s : ColoredAssocData W) :
    ∀ i, ((nestedThreeLevelBranchSourceIso O A s).hom.hom i).HasIdentityComponents := by
  intro i
  cases i with
  | none => exact emptyLeafRawIso_inv_identity _
  | some i => exact substitutionToLeavesIso_identity O A (s.localData i)

theorem middleRouteBRawBlocksIso_fibers_identity (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    ∀ i, ((middleRouteBRawBlocksIso O A s).hom.hom i).HasIdentityComponents := by
  intro i
  cases i with
  | none => exact emptyLeafRawIso_identity _
  | some p =>
    let P := s.innerData.inner.obj p
    exact (FiniteFamily.Hom.HasIdentityComponents.flatten_fibers
      (singletonCoefficientLeavesIso_fibers_identity (O.obj P) (profileLeafFamily A P))).comp
      ((mapSingletonFlatten_identity ((coefficientLeafFamilyFunctor (profileLeafFamily A
        P)).obj (O.obj P))).comp
        (profileOperationFactorsIso_identity O A P))

theorem middleRetainedTripleRawIso_inv_fibers_identity (O : ColoredSymmetricCollection W C)
  (A : W → C)
    (s : ColoredAssocData W) :
    ∀ i, ((middleRetainedTripleRawIso O A s).inv.hom i).HasIdentityComponents := by
  intro i
  cases i with
  | none =>
    intro p
    refine ⟨rfl, ?_⟩
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  | some i =>
    intro p
    refine ⟨rfl, ?_⟩
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _

theorem middleCoefficientFirstRawIso_fibers_identity (O : ColoredSymmetricCollection W C) (A
  : W → C)
    (s : ColoredAssocData W) :
    ∀ i, ((middleCoefficientFirstRawIso O A s).hom.hom i).HasIdentityComponents := by
  intro i
  cases i with
  | none => exact mapSingletonFlatten_identity _
  | some p => exact singletonFlatten_identity _

end CategoryTheory.Operad.Tensor
end
end
end source_NestedBranchIdentityComponents

/- Source proof segment: PartitionIdentityComponents -/
section source_PartitionIdentityComponents
@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

theorem partitionSourceIso_identity (N : FiniteFamily (FiniteFamily C)) (L : N.index →
  FiniteFamily C) :
    (partitionedCoefficientLeavesSourceIso N L).hom.HasIdentityComponents :=
  FiniteFamily.isoOfReindex_identityComponents _ _

theorem partitionSourceIso_inv_identity (N : FiniteFamily (FiniteFamily C)) (L : N.index →
  FiniteFamily C) :
    (partitionedCoefficientLeavesSourceIso N L).inv.HasIdentityComponents :=
  FiniteFamily.isoOfReindex_inv_identityComponents _ _

theorem middleTripleRegroupIso_identity (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) : (middleTripleRegroupIso O A s).hom.HasIdentityComponents :=
  (FiniteFamily.isoOfReindex_identityComponents _ _).comp
    (FiniteFamily.isoOfReindex_inv_identityComponents _ _)

theorem middleRawTripleIso_identity (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) : (middleRawTripleIso O A s).hom.HasIdentityComponents := by
  exact (flattenAssoc_identity _).comp
    ((FiniteFamily.Hom.HasIdentityComponents.flatten (middleTripleRegroupIso_identity O A s)).comp
      (flattenAssoc_inv_identity _))

theorem middleRouteBRawSourceIso_identity (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) : (middleRouteBRawSourceIso O A s).hom.HasIdentityComponents := by
  let leaf := (substitutionFrameLeafIso A s.outerAfterInnerData
    (associativityCoefficientBlocksA O s) ≪≫
    (profileLeafIso A s.totalHom).symm) ≪≫
    (substitutionFrameLeafIso A s.innerData (associativityCoefficientBlocksB O s)).symm
  have hl : leaf.hom.HasIdentityComponents :=
    ((substitutionFrameLeafIso_identity A _ _).comp (profileLeafIso_inv_identity A _)).comp
      (substitutionFrameLeafIso_inv_identity A _ _)
  exact (FiniteFamily.Hom.HasIdentityComponents.flatten_fibers
    (nestedThreeLevelBranchSourceIso_fibers_identity O A s)).comp
      ((partitionSourceIso_identity _ _).comp
        ((coefficientLeavesRawIso_identity (associativityCoefficientIso O s) leaf
          (associativityCoefficientIso_identity O s) hl).comp
            (partitionSourceIso_inv_identity _ _)))

end CategoryTheory.Operad.Tensor
end
end
end source_PartitionIdentityComponents

/- Source proof segment: MiddleRouteBSourceComparison -/
section source_MiddleRouteBSourceComparison
/-!
# Exact original whole raw source permutation for middle-first route B
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

/-- The original source coefficient and leaf permutation reaches
the same complete middle raw factors as the two actual triple associators. -/
theorem middleRouteBSource_raw (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (middleRouteBRawSourceIso O A s).hom ≫
        (FiniteFamily.flatten (C := C)).map (middleRouteBRawBlocksIso O A s).hom =
    (FiniteFamily.flatten (C := C)).map (middleRetainedTripleRawIso O A s).inv ≫
      (middleRawTripleIso O A s).hom ≫
      (FiniteFamily.flatten (C := C)).map (middleCoefficientFirstRawIso O A s).hom := by
  apply FiniteFamily.Hom.ext_identityComponents
  · ext p
    rcases p with ⟨o, i⟩
    cases o with
    | none => cases i; rfl
    | some i =>
      rcases i with ⟨o, j⟩
      cases o with
      | none => cases j; rfl
      | some j => cases j <;> rfl
  · exact (middleRouteBRawSourceIso_identity O A s).comp
      (FiniteFamily.Hom.HasIdentityComponents.flatten_fibers
        (middleRouteBRawBlocksIso_fibers_identity O A s))
  · exact (FiniteFamily.Hom.HasIdentityComponents.flatten_fibers
      (middleRetainedTripleRawIso_inv_fibers_identity O A s)).comp
      ((middleRawTripleIso_identity O A s).comp
        (FiniteFamily.Hom.HasIdentityComponents.flatten_fibers
          (middleCoefficientFirstRawIso_fibers_identity O A s)))

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleRouteBSourceComparison

/- Source proof segment: MiddleCanonicalScalarSquares -/
section source_MiddleCanonicalScalarSquares
@[expose] public section

set_option autoImplicit false

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

/-- Compose the actual mapped raw source factors after fixed scalar readbacks. -/
theorem middleCanonicalSourceScalar {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (T : C ⥤ D)
    {X A B E F Y : C} {Z : D}
    (r : Z ⟶ T.obj X) (a : X ⟶ A) (p : A ⟶ B) (ca : B ⟶ E)
    (cb : E ⟶ F) (q : F ⟶ Y) (raw : X ⟶ Y)
    (source : Z ⟶ T.obj E) (cinv : T.obj E ⟶ T.obj Y)
    (hs : source = (r ≫ T.map a) ≫ T.map (p ≫ ca))
    (hi : cinv = T.map (cb ≫ q))
    (hr : a ≫ p ≫ ca ≫ cb ≫ q = raw) :
    source ≫ cinv = r ≫ T.map raw := by
  rw [hs, hi]
  simp only [Category.assoc, ← T.map_comp]
  exact congrArg (fun f => r ≫ T.map f) hr

end CategoryTheory.Operad.Tensor
end
end source_MiddleCanonicalScalarSquares

/- Source proof segment: MiddleRouteBCanonicalSource -/
section source_MiddleRouteBCanonicalSource
@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

theorem middleRouteBCanonicalSource (O : ColoredSymmetricCollection W C) (A : W → C)
    (s : ColoredAssocData W) :
    (nestedThreeLevelSourceIso O A s).hom ≫
      (substitutionCanonicalSourceIso A s.innerData (associativityCoefficientBlocksB O s)
        (associativityCoefficientIso O s).symm s.totalHom).inv =
    (FiniteTensor.flattenIso (V := C)).inv.app (nestedThreeLevelFactors O A s) ≫
      (FiniteTensor.tensor (V := C)).map (middleRouteBRawSourceIso O A s).hom := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let a := F.map (nestedThreeLevelBranchSourceIso O A s).hom
  let p := (partitionedCoefficientLeavesSourceIso
    (substitutionBranchGrouping s.outerAfterInnerData (associativityCoefficientBlocksA O s))
    (substitutionBranchLeaves A s.outerAfterInnerData)).hom
  let la := substitutionFrameLeafIso A s.outerAfterInnerData (associativityCoefficientBlocksA O s)
  let lb := substitutionFrameLeafIso A s.innerData (associativityCoefficientBlocksB O s)
  let lc := profileLeafIso A s.totalHom
  let ca := coefficientLeavesRawIso (Iso.refl
    (ColoredOperadObj.AssocInsertion.flattenedGroupingA O s))
    (la ≪≫ profileLeafIso A (𝟙 s.outerAfterInnerData.totalProfile))
  let cb := coefficientLeavesRawIso (associativityCoefficientIso O s).symm (lb ≪≫ lc)
  let q := partitionedCoefficientLeavesSourceIso
    (substitutionBranchGrouping s.innerData (associativityCoefficientBlocksB O s))
    (substitutionBranchLeaves A s.innerData)
  -- The actual raw source coefficient/leaf iso composition will be shown using its original
  -- index maps.
  have hraw : a ≫ p ≫ ca.hom ≫ cb.inv ≫ q.inv = (middleRouteBRawSourceIso O A s).hom := by
    apply FiniteFamily.Hom.ext_identityComponents
    · ext i
      rcases i with ⟨o, i⟩
      cases o with
      | none => cases i; rfl
      | some i => rcases i with ⟨o, j⟩; cases o with
        | none => cases j; rfl
        | some j => cases j <;> rfl
    · exact (FiniteFamily.Hom.HasIdentityComponents.flatten_fibers
        (nestedThreeLevelBranchSourceIso_fibers_identity O A s)).comp
        ((partitionSourceIso_identity _ _).comp
          ((coefficientLeavesRawIso_identity _ _ (FiniteFamily.Hom.hasIdentityComponents_id _)
            ((substitutionFrameLeafIso_identity A _ _).comp (profileLeafIso_identity A _))).comp
              ((coefficientLeavesRawIso_inv_identity _ _ (associativityCoefficientIso_identity O s)
                ((profileLeafIso_inv_identity A _).comp
                  (substitutionFrameLeafIso_inv_identity A _ _))).comp
                  (partitionSourceIso_inv_identity _ _))))
    · exact middleRouteBRawSourceIso_identity O A s
  let r := (FiniteTensor.flattenIso (V := C)).inv.app (nestedThreeLevelFactors O A s)
  let eb := substitutionCanonicalSourceIso A s.innerData (associativityCoefficientBlocksB O s)
    (associativityCoefficientIso O s).symm s.totalHom
  have hsource : (nestedThreeLevelSourceIso O A s).hom = (r ≫ T.map a) ≫ T.map (p ≫ ca.hom) := by
    change r ≫ T.map a ≫ T.map (p ≫ ca.hom) = (r ≫ T.map a) ≫ T.map (p ≫ ca.hom)
    exact (Category.assoc _ _ _).symm
  have hinv : eb.inv = T.map (cb.inv ≫ q.inv) := rfl
  exact middleCanonicalSourceScalar T r a p ca.hom cb.inv q.inv
    (middleRouteBRawSourceIso O A s).hom (nestedThreeLevelSourceIso O A s).hom eb.inv
      hsource hinv hraw

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleRouteBCanonicalSource

/- Source proof segment: MiddleRouteJoinSquares -/
section source_MiddleRouteJoinSquares
@[expose] public section

set_option autoImplicit false

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

/-- Join the original raw source permutation with the proved retained route. -/
theorem middleRouteJoinScalar {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (T : C ⥤ D)
    {X B N M K : C} {Z P Y : D}
    (source : Z ⟶ P) (cinv : P ⟶ T.obj B) (r : Z ⟶ T.obj X)
    (raw : X ⟶ B) (blocks : B ⟶ K) (einv : X ⟶ N) (k : N ⟶ M)
    (p : M ⟶ K) (tail : T.obj K ⟶ Y) (full : T.obj B ⟶ Y)
    (middle : Z ⟶ Y)
    (hc : source ≫ cinv = r ≫ T.map raw)
    (hf : full = T.map blocks ≫ tail)
    (hr : raw ≫ blocks = einv ≫ k ≫ p)
    (hm : middle = r ≫ T.map einv ≫ T.map k ≫ T.map p ≫ tail) :
    source ≫ cinv ≫ full = middle := by
  have h1 := congrArg (· ≫ full) hc
  have h2 := congrArg (fun f => r ≫ T.map raw ≫ f) hf
  have h3 := congrArg (fun f => r ≫ T.map f ≫ tail) hr
  simp only [Category.assoc] at h1 h2
  simp only [T.map_comp, Category.assoc] at h3
  exact h1.trans (h2.trans (h3.trans hm.symm))

/-- Retain a final original profile map after the complete source join. -/
theorem middleRoutePostcomposeScalar {C : Type u₁} [Category.{v₁} C]
    {X P B Y Z : C} (source : X ⟶ P) (cinv : P ⟶ B) (full : B ⟶ Y)
    (final : Y ⟶ Z) (route : P ⟶ Z) (middle : X ⟶ Y)
    (hr : route = cinv ≫ full ≫ final) (hm : source ≫ cinv ≫ full = middle) :
    source ≫ route = middle ≫ final := by
  rw [hr]
  simpa only [Category.assoc] using congrArg (· ≫ final) hm

end CategoryTheory.Operad.Tensor
end
end source_MiddleRouteJoinSquares

/- Source proof segment: MiddleTensorRouteGeometryProof -/
section source_MiddleTensorRouteGeometryProof
/-!
# Exact weighted middle-first tensor substitution geometry

The original weighted middle operation, all original inner operation
factors, the original coefficient permutation, and every original leaf
are retained through the actual source isomorphisms. No desired geometry,
monad, or algebra outcome is a premise.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original three-level route B is the actual middle-first
weighted operation route, with the original total-profile map. This
includes empty branches and nullary profiles. -/
theorem middleOperationTensorRoute_geometry (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredAssocData W) :
    (nestedThreeLevelSourceIso O.toCollection A s).hom ≫ threeLevelTensorRouteB O A s =
      middleOperationTensorRoute O A s ≫
        (operationSummandFunctor O.toCollection A).map s.totalHom := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let source := (nestedThreeLevelSourceIso O.toCollection A s).hom
  let cinv := (substitutionCanonicalSourceIso A s.innerData
    (associativityCoefficientBlocksB O.toCollection s)
    (associativityCoefficientIso O.toCollection s).symm s.totalHom).inv
  let r := (FiniteTensor.flattenIso (V := C)).inv.app (nestedThreeLevelFactors O.toCollection A s)
  let raw := (middleRouteBRawSourceIso O.toCollection A s).hom
  let blocks := F.map (middleRouteBRawBlocksIso O.toCollection A s).hom
  let einv := F.map (middleRetainedTripleRawIso O.toCollection A s).inv
  let k := (middleRawTripleIso O.toCollection A s).hom
  let p := F.map (middleCoefficientFirstRawIso O.toCollection A s).hom
  let tail := (FiniteTensor.flattenIso (V := C)).hom.app (middleRetainedNestedBlocks
    O.toCollection A s) ≫
    T.map (middleRetainedCoefficientMap O A s) ≫
    (FiniteTensor.flattenIso (V := C)).inv.app (nestedOperationFactors O.toCollection A
      s.innerData) ≫
    operadSubstitutionInputs O A s.innerData
  let full := fullSubstitutionPartitionRoute O A s.innerData
    (associativityCoefficientBlocksB O.toCollection s) (associativityCoefficientMapsB O s)
  let middle := middleOperationTensorRoute O A s
  have hc : source ≫ cinv = r ≫ T.map raw := middleRouteBCanonicalSource O.toCollection A s
  have hf : full = T.map blocks ≫ tail := middleRouteBFrame_action O A s
  have hr : raw ≫ blocks = einv ≫ k ≫ p := middleRouteBSource_raw O.toCollection A s
  have hraw : (middleRawSourceIso O.toCollection A s).hom = (r ≫ T.map einv) ≫ T.map k := by
    change r ≫ T.map einv ≫ T.map k = (r ≫ T.map einv) ≫ T.map k
    exact (Category.assoc _ _ _).symm
  have hm : middle = r ≫ T.map einv ≫ T.map k ≫ T.map p ≫ tail := by
    have h := middleOperationTensorRoute_retained O A s
    change middle = (middleRawSourceIso O.toCollection A s).hom ≫ T.map p ≫ tail at h
    exact h.trans ((congrArg (fun f => f ≫ T.map p ≫ tail) hraw).trans
      (by simp only [Category.assoc]))
  have hjoin : source ≫ cinv ≫ full = middle :=
    middleRouteJoinScalar T source cinv r raw blocks einv k p tail full middle hc hf hr hm
  exact middleRoutePostcomposeScalar source cinv full
    ((operationSummandFunctor O.toCollection A).map s.totalHom)
    (threeLevelTensorRouteB O A s) middle (threeLevelTensorRouteB_original O A s) hjoin

end CategoryTheory.Operad.Tensor
end
end
end source_MiddleTensorRouteGeometryProof

/- Source proof segment: FreeOperationSubstitution -/
section source_FreeOperationSubstitution
/-!
# Original full tensor substitution law for constructed free operations
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem freeSubstitutionThreeLevel {V : Type*} [Category* V]
    {X S Y F N : V} (frame : X ⟶ S) (source : S ⟶ Y)
    (routeA routeB : Y ⟶ N) (middle : S ⟶ F) (total : F ⟶ N)
    {P : V} (ι : N ⟶ P) (ι' : F ⟶ P)
    (hassoc : routeA = routeB) (hm : source ≫ routeB = middle ≫ total)
    (hι : total ≫ ι = ι') :
    (frame ≫ source) ≫ routeA ≫ ι = frame ≫ middle ≫ ι' := by
  rw [hassoc]
  simp only [Category.assoc]
  rw [← Category.assoc source routeB, hm]
  simp only [Category.assoc]
  rw [hι]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- The original raw operad associativity law descends through
actual nested finite tensor/profile colimits to the full original
tensor substitution law of constructed free operations. -/
theorem freeOperations_substitution (O : ColoredOperadObj W C) (A : W → C)
    (s : ColoredSubstitutionData W) :
    algebraSubstitutionInner (freeOperations O A) s =
      operadSubstitutionInputs O (profileCoinvariants O.toCollection A) s ≫
        freeOperation O A (profileInputs s.totalProfile) := by
  let e := nestedRawPointIso O.toCollection A s
  apply (cancel_epi e.hom).1
  apply (isColimitNestedRawTensorCocone O.toCollection A s).hom_ext
  intro Q
  let shape := nestedRawAssocShape s Q
  let frame := (FiniteTensor.tensor (V := C)).map (nestedRawSourceFactorsIso O.toCollection
    A s Q).hom
  let source := (nestedThreeLevelSourceIso O.toCollection A shape).hom
  let routeA := threeLevelTensorRouteA O A shape
  let routeB := threeLevelTensorRouteB O A shape
  let middle := middleOperationTensorRoute O A shape
  let total := (operationSummandFunctor O.toCollection A).map shape.totalHom
  let ι := profileι O.toCollection A (profileInputs shape.outerAfterInnerData.totalProfile)
  let ι' := profileι O.toCollection A (profileInputs shape.innerData.totalProfile)
  have hA := nestedRawInnerSourceRouteA O A s Q
  have hB := nestedRawMiddleFreeOperation O A s Q
  have hs := freeSubstitutionThreeLevel frame source routeA routeB middle total ι ι'
    (threeLevelTensorSubstitution_assoc O A shape) (middleOperationTensorRoute_geometry O A shape)
    (profileι_assoc_total O.toCollection A shape)
  change (nestedRawTensorCocone O.toCollection A s).ι.app Q ≫
      (e.hom ≫ algebraSubstitutionInner (freeOperations O A) s) =
    (nestedRawTensorCocone O.toCollection A s).ι.app Q ≫
      (e.hom ≫ operadSubstitutionInputs O (profileCoinvariants O.toCollection A) s ≫
        freeOperation O A (profileInputs s.totalProfile))
  exact hA.trans (hs.trans hB.symm)



end CategoryTheory.Operad.Tensor
end
end
end source_FreeOperationSubstitution

/- Source proof segment: AlgebraActionFactors -/
section source_AlgebraActionFactors
/-!
# Original tensor algebra operations and profile action factor maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem actionSlotAssembly {V : Type*} [Category* V]
    {X P Q R S Y : V} (slot : X ⟶ P) (carrier : P ⟶ Q) (outer : Q ⟶ Y)
    (coefficient : X ⟶ S) (e : R ≅ S) (inner : S ⟶ Q)
    (h : slot ≫ carrier = coefficient ≫ inner) :
    slot ≫ carrier ≫ outer = (coefficient ≫ e.inv) ≫ (e.hom ≫ inner ≫ outer) := by
  have q := congrArg (· ≫ outer) h
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using q

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The actual profile injections followed by an original tensor
algebra action give its original inner operation tensor factors. -/
theorem Operations.slotDescFactors {O : ColoredSymmetricCollection W C} {A : W →
  C} (a : Operations O A A)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    profileSlotInjectionFactors O A P Q ≫
      (analyticFactorsCarrierMap O a.desc).app P =
    (coefficientTensorIso O A P Q).hom ≫
      innerOperationMap a
        (tupleSubstitutionShape P ((slotProfileTupleFunctor P).obj Q)) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      let e := (FiniteTensor.singletonIso (V := C)).app (O.obj P.toColoredProfile)
      change HEq (𝟙 _ ≫ 𝟙 _) (e.inv ≫ e.hom)
      exact heq_of_eq ((Category.id_comp _).trans e.inv_hom_id.symm)
    | some i =>
      change HEq (profileι O A (Q (some i)) ≫ a.desc (P.inputColor i))
        (𝟙 _ ≫ a.app (P.inputColor i) (Q (some i)))
      exact heq_of_eq ((a.ι_desc _).trans (Category.id_comp _).symm)

/-- The full original slot tensor injection followed by the input
action tensor map is the original coefficient unitor and inner operation tensor map. -/
theorem Operations.slotDescTensor {O : ColoredSymmetricCollection W C} {A : W →
  C} (a : Operations O A A)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (profileSlotTensorCocone O A P).ι.app Q ≫
      (analyticSummandCarrierMap O a.desc).app P =
    (FiniteTensor.tensor (V := C)).map
      ((coefficientTensorIso O A P Q).hom ≫
        innerOperationMap a (tupleSubstitutionShape P ((slotProfileTupleFunctor P).obj Q))) := by
  let T := FiniteTensor.tensor (V := C)
  have hι : (profileSlotTensorCocone O A P).ι.app Q =
      T.map (profileSlotInjectionFactors O A P Q) := by
    apply congrArg T.map
    apply FiniteFamily.Hom_ext
    · rfl
    · intro i
      cases i <;> exact HEq.rfl
  rw [hι, analyticSummandCarrierMap_app]
  exact (T.map_comp _ _).symm.trans (congrArg T.map (a.slotDescFactors P Q))

/-- The actual original slot injection and carrier action tensor
evaluate the original source assembly followed by all inner and
outer algebra operations. -/
theorem Operations.slotDescAssembly {O : ColoredSymmetricCollection W C} {A : W →
  C} (a : Operations O A A)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (profileSlotTensorCocone O A P).ι.app Q ≫
      (analyticSummandCarrierMap O a.desc).app P ≫ a.app d P =
    profileSubstitutionAssemblyMap O A P Q ≫
      algebraSubstitutionInner a (tupleSubstitutionShape P ((slotProfileTupleFunctor P).obj
        Q)) := by
  let T := FiniteTensor.tensor (V := C)
  let s := tupleSubstitutionShape P ((slotProfileTupleFunctor P).obj Q)
  let e := (FiniteTensor.flattenIso (V := C)).app (nestedOperationFactors O A s)
  let c := T.map (coefficientTensorIso O A P Q).hom
  let inner := T.map (innerOperationMap a s)
  have h : (profileSlotTensorCocone O A P).ι.app Q ≫
      (analyticSummandCarrierMap O a.desc).app P = c ≫ inner :=
    (a.slotDescTensor P Q).trans (T.map_comp _ _)
  exact actionSlotAssembly _ _ _ c e inner h



end CategoryTheory.Operad.Tensor
end
end
end source_AlgebraActionFactors

/- Source proof segment: AlgebraActionAssociativity -/
section source_AlgebraActionAssociativity
/-!
# Actual tensor algebra action associativity from original operation maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem algebraActionSlotEquality {V : Type*} [Category* V]
    {X P Q R S U Y : V} (slot : X ⟶ P) (μ : P ⟶ Q) (action : Q ⟶ Y)
    (input : P ⟶ R) (outer : R ⟶ Y) (assembly : X ⟶ S)
    (op : S ⟶ U) (ι : U ⟶ Q) (eval : U ⟶ Y)
    (inner : S ⟶ Y) (hβ : slot ≫ μ = assembly ≫ op ≫ ι)
    (hι : ι ≫ action = eval) (hinput : slot ≫ input ≫ outer = assembly ≫ inner)
    (halg : inner = op ≫ eval) :
    slot ≫ μ ≫ action = slot ≫ input ≫ outer := by
  rw [← Category.assoc slot μ, hβ]
  simp only [Category.assoc]
  rw [hι, ← halg, ← hinput]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- The independently defined original tensor algebra substitution
law gives associativity for its actual descended profile action. -/
theorem Algebra.action_assoc {O : ColoredOperadObj W C} (B : Algebra O) :
    profileMultiplication O B.carrier ≫ B.action = profileMap O.toCollection B.action ≫
      B.action := by
  funext d
  apply colimit.hom_ext
  intro P
  let ι := profileι O.toCollection (profileCoinvariants O.toCollection B.carrier) P
  have hleft : ι ≫ (profileMultiplication O B.carrier d ≫ B.action d) =
      freeOperation O B.carrier P ≫ B.action d := by
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫
      B.action d) (profileMultiplication_profile O B.carrier P))
  have hright : ι ≫ (profileMap O.toCollection B.action d ≫ B.action d) =
      (analyticSummandCarrierMap O.toCollection B.action).app P ≫ B.operations.app d P := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ B.action d) (profileι_map O.toCollection B.action P)).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (B.action_operation d P))))
  refine hleft.trans (Eq.trans ?_ hright.symm)
  apply freeOperation_hom_ext O.toCollection B.carrier P
  intro Q
  let slot := (profileSlotTensorCocone O.toCollection B.carrier P).ι.app Q
  let assembly := profileSubstitutionAssemblyMap O.toCollection B.carrier P Q
  let s := tupleSubstitutionShape P ((slotProfileTupleFunctor P).obj Q)
  let op := operadSubstitutionInputs O B.carrier s
  let i := profileι O.toCollection B.carrier (profileInputs s.totalProfile)
  let eval := B.operations.app d (profileInputs s.totalProfile)
  let inner := algebraSubstitutionInner B.operations s
  have hβ : slot ≫ freeOperation O B.carrier P = assembly ≫ op ≫ i :=
    freeOperation_ι O B.carrier P Q
  have hinput : slot ≫ (analyticSummandCarrierMap O.toCollection B.action).app P ≫
      B.operations.app d P = assembly ≫ inner := by
    exact B.operations.slotDescAssembly P Q
  change slot ≫ (freeOperation O B.carrier P ≫ B.action d) =
    slot ≫ ((analyticSummandCarrierMap O.toCollection B.action).app P ≫ B.operations.app d P)
  exact algebraActionSlotEquality slot (freeOperation O B.carrier P) (B.action d)
    ((analyticSummandCarrierMap O.toCollection B.action).app P) (B.operations.app d P)
    assembly op i eval inner hβ (B.action_operation _ _) hinput (B.substitution s)



end CategoryTheory.Operad.Tensor
end
end
end source_AlgebraActionAssociativity

/- Source proof segment: AlgebraActionMorphisms -/
section source_AlgebraActionMorphisms
/-!
# Original tensor algebra morphisms and actual profile action maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

/-- Original operation maps are preserved whenever their actual
profile quotient actions and carrier map squares commute. -/
theorem operationMorphismFromAction {V : Type*} [Category* V]
    {X Y P Q A B : V} (i : X ⟶ P) (j : Y ⟶ Q) (a : P ⟶ A) (b : Q ⟶ B)
    (f : A ⟶ B) (tf : P ⟶ Q) (h : X ⟶ Y) (opX : X ⟶ A) (opY : Y ⟶ B)
    (hi : i ≫ a = opX) (hj : j ≫ b = opY) (hf : tf ≫ b = a ≫ f)
    (hh : i ≫ tf = h ≫ j) : opX ≫ f = h ≫ opY := by
  rw [← hi, Category.assoc, ← hf, ← Category.assoc i tf, hh, Category.assoc h j, hj]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- An original carrier map preserving the actual descended
actions preserves every original finite tensor operation, including
nullary operations and arbitrary original profile colors. -/
def Algebra.Hom.ofActionEquation {O : ColoredOperadObj W C} (A B : Algebra O)
    (f : A.carrier ⟶ B.carrier)
    (h : profileMap O.toCollection f ≫ B.action = A.action ≫ f) : A ⟶ B where
  hom := f
  comm d P :=
    operationMorphismFromAction (profileι O.toCollection A.carrier P)
      (profileι O.toCollection B.carrier P) (A.action d) (B.action d) (f d)
      (profileMap O.toCollection f d) ((analyticSummandCarrierMap O.toCollection f).app P)
      (A.operations.app d P) (B.operations.app d P)
      (A.action_operation d P) (B.action_operation d P) (congrFun h d) (profileι_map
        O.toCollection f P)

/-- Full operation-preserving maps and original action-preserving
carrier maps are in bijection, with exactly the same carrier map. -/
def Algebra.homEquivAction {O : ColoredOperadObj W C} (A B : Algebra O) :
    (A ⟶ B) ≃ {f : A.carrier ⟶ B.carrier // profileMap O.toCollection f ≫ B.action =
      A.action ≫ f} where
  toFun f := ⟨f.hom, (Algebra.action_naturality f).symm⟩
  invFun f := Hom.ofActionEquation A B f.1 f.2
  left_inv _ := Hom.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The actual morphism comparison leaves every original carrier
component exactly as supplied, at every original color. -/
@[simp]
theorem Algebra.homEquivAction_hom {O : ColoredOperadObj W C} (A B : Algebra O)
    (f : A ⟶ B) : (A.homEquivAction B f).1 = f.hom := rfl



end CategoryTheory.Operad.Tensor
end
end
end source_AlgebraActionMorphisms

/- Source proof segment: UnaryTensorUnit -/
section source_UnaryTensorUnit
/-!
# Actual unary coefficient tensor and original operadic unit

The original unary operad coefficient tensors a varying object.
The original operadic unit and input singleton unitor give a natural
map from that object to its actual unary coefficient/input tensor.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original unary operation coefficient with a varying
original object in its sole input slot. -/
def unaryTensorFunctor (O : ColoredSymmetricCollection W C) (d : W) : C ⥤ C where
  obj X := (analyticSummand O (fun _ : W => X)).obj (AnalyticIndex.unary (d := d) d)
  map f := (analyticSummandCarrierMap O (fun _ : W => f)).app (AnalyticIndex.unary (d := d) d)
  map_id X := congrArg (fun a => a.app (AnalyticIndex.unary (d := d) d))
    (analyticSummandCarrierMap_id O (A := fun _ : W => X))
  map_comp f g := congrArg (fun a => a.app (AnalyticIndex.unary (d := d) d))
    (analyticSummandCarrierMap_comp O (fun _ : W => f) (fun _ : W => g))

/-- The original source operadic unit gives the actual natural
unary coefficient tensor insertion for a varying object. -/
def unaryTensorUnit (O : ColoredOperadObj W C) (d : W) : 𝟭 C ⟶ unaryTensorFunctor
  O.toCollection d where
  app X := unitInsertion O (fun _ : W => X) d
  naturality _ _ f := unitInsertion_naturality O (fun _ : W => f) d

/-- Evaluating the varying-object unit at an original input object
recovers the original color-indexed unit insertion exactly. -/
@[simp]
theorem unaryTensorUnit_app (O : ColoredOperadObj W C) (A : W → C) (d : W) :
    (unaryTensorUnit O d).app (A d) = unitInsertion O A d :=
  by
    have h : unitFactors O (fun _ : W => A d) d = unitFactors O A d := by
      apply FiniteFamily.Hom_ext
      · rfl
      · intro i
        cases i <;> exact HEq.rfl
    exact congrArg (UnitInsertion.leftInsertFromFactor (A d)) h



end CategoryTheory.Operad.Tensor
end
end
end source_UnaryTensorUnit

/- Source proof segment: ProfileUnitSubstitution -/
section source_ProfileUnitSubstitution
/-!
# Actual operadic unit profile tuples

These are the original right/left unit substitution shapes, retained
as actual finite profile tuples. Their input types, units and original
flattened-profile bijections are used in the monad unit-law descent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u}

/-- Substitute the original unary identity profile at every input
of the original outer profile, including an empty outer profile. -/
def rightUnitProfileTuple {d : W} (P : AnalyticIndex W d) : ProfileSubstitutionTuple P :=
  fun i => AnalyticIndex.unary (P.inputColor i)

/-- The tuple represents the original right-unit substitution
datum of the colored operad exactly. -/
theorem rightUnitProfileTuple_shape {d : W} (P : AnalyticIndex W d) :
    tupleSubstitutionShape P (rightUnitProfileTuple P) =
      ColoredSubstitutionData.rightUnit P.toColoredProfile :=
  rfl

/-- The actual original flattened right-unit profile map. -/
def rightUnitTupleTotalHom {d : W} (P : AnalyticIndex W d) :
    (tupleTotalFunctor P).obj (rightUnitProfileTuple P) ⟶ P :=
  ColoredSubstitutionData.rightUnitTotalHom P.toColoredProfile

/-- Insert an original profile into the sole input of the original
unary identity profile at its output. -/
def leftUnitProfileTuple {d : W} (P : AnalyticIndex W d) :
    ProfileSubstitutionTuple (AnalyticIndex.unary (d := d) d) :=
  fun _ => P

/-- The tuple represents the original left-unit substitution datum
of the colored operad exactly. -/
theorem leftUnitProfileTuple_shape {d : W} (P : AnalyticIndex W d) :
    tupleSubstitutionShape (AnalyticIndex.unary (d := d) d) (leftUnitProfileTuple P) =
      ColoredSubstitutionData.leftUnit P.toColoredProfile :=
  rfl

/-- The actual original flattened left-unit profile map. -/
def leftUnitTupleTotalHom {d : W} (P : AnalyticIndex W d) :
    (tupleTotalFunctor (AnalyticIndex.unary (d := d) d)).obj (leftUnitProfileTuple P) ⟶ P :=
  ColoredSubstitutionData.leftUnitTotalHom P.toColoredProfile




end CategoryTheory.Operad.Tensor
end
end
end source_ProfileUnitSubstitution

/- Source proof segment: UnitOperationBeta -/
section source_UnitOperationBeta
/-!
# Original unit-profile operation beta maps

The actual multiplication evaluates original right/left unit
profile tuples by their original assembled operadic substitution.
These beta equations precede the source coherence proof that turns
them into the two monad unit equations.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u}

/-- The actual coefficient/input tuple of right-unit profiles,
including an empty outer profile's coefficient. -/
def rightUnitSlotTuple {d : W} (P : AnalyticIndex W d) : ProfileSlotTuple P
  | none => ⟨⟨PUnit.unit⟩⟩
  | some i => AnalyticIndex.unary (d := P.inputColor i) (P.inputColor i)

/-- The actual coefficient/input tuple of left-unit substitution,
retaining the original arbitrary inner profile. -/
def leftUnitSlotTuple {d : W} (P : AnalyticIndex W d) :
    ProfileSlotTuple (AnalyticIndex.unary (d := d) d)
  | none => ⟨⟨PUnit.unit⟩⟩
  | some _ => P

variable {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- The actual multiplication beta equation at every original
right-unit profile tuple. -/
theorem profileMultiplication_right_unit_slot (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (profileSlotTensorCocone O.toCollection A P).ι.app (rightUnitSlotTuple P) ≫
      profileι O.toCollection (profileCoinvariants O.toCollection A) P ≫
        profileMultiplication O A d =
    (assembledProfileSubstitutionCocone O A P).ι.app (rightUnitSlotTuple P) :=
  profileMultiplication_slot O A P (rightUnitSlotTuple P)

/-- The actual multiplication beta equation at every original
left-unit profile tuple, including an original nullary inner profile. -/
theorem profileMultiplication_left_unit_slot (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (profileSlotTensorCocone O.toCollection A (AnalyticIndex.unary (d := d) d)).ι.app
        (leftUnitSlotTuple P) ≫
      profileι O.toCollection (profileCoinvariants O.toCollection A) (AnalyticIndex.unary
        (d := d) d) ≫
        profileMultiplication O A d =
    (assembledProfileSubstitutionCocone O A (AnalyticIndex.unary (d :=
      d) d)).ι.app (leftUnitSlotTuple P) :=
  profileMultiplication_slot O A (AnalyticIndex.unary (d := d) d) (leftUnitSlotTuple P)

end CategoryTheory.Operad.Tensor
end
end
end source_UnitOperationBeta

/- Source proof segment: LeftUnitRawAssembly -/
section source_LeftUnitRawAssembly
/-!
# Original raw left-unit tensor assembly

The original unary operad coefficient is inserted before an actual
arbitrary profile tensor. The original singleton and flattening maps
retain every input coefficient and leaf, including nullary profiles.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The actual original two-level left-unit substitution source. -/
def leftUnitNestedFactors (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) : FiniteFamily (FiniteFamily C) :=
  nestedOperationFactors O A
    (tupleSubstitutionShape (AnalyticIndex.unary (d := d) d) (leftUnitProfileTuple P))

/-- The actual weighted left-unit operation/input family, retaining
the whole original inner profile tensor as its sole input. -/
def leftUnitExpandedFamily (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) : FiniteFamily C where
  index := FintypeCat.of (Option PUnit)
  obj i := match i with
    | none => O.obj (ColoredSubstitutionData.unitProfile d)
    | some _ => (analyticSummand O A).obj P

/-- The original coefficient singleton unitor assembles the whole
original profile input tensor into the original nested source. -/
def leftUnitExpandedFactorsIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    leftUnitExpandedFamily O A P ≅
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (leftUnitNestedFactors O A P) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option PUnit))
    (fun i => match i with
      | none => ((FiniteTensor.singletonIso (V := C)).app
          (O.obj (ColoredSubstitutionData.unitProfile d))).symm
      | some _ => Iso.refl ((analyticSummand O A).obj P))

/-- The actual original unary unit insertion before the arbitrary
profile tensor, followed by its actual nested source assembly. -/
def leftUnitRawInsertion (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (analyticSummand O.toCollection A).obj P ⟶
      algebraSubstitutionSource O.toCollection A
        (tupleSubstitutionShape (AnalyticIndex.unary (d := d) d) (leftUnitProfileTuple P)) :=
  UnitInsertion.leftInsertFromFactor ((analyticSummand O.toCollection A).obj P)
    ({ equiv := Equiv.refl (Option PUnit)
       hom i := match i with
         | none => O.unit d
         | some _ => (FiniteTensor.singletonIso (V := C)).hom.app
             ((analyticSummand O.toCollection A).obj P) } :
      UnitInsertion.leftTensorFamily ((analyticSummand O.toCollection A).obj P) ⟶
        leftUnitExpandedFamily O.toCollection A P) ≫
    (FiniteTensor.tensor (V := C)).map (leftUnitExpandedFactorsIso O.toCollection A P).hom ≫
    (FiniteTensor.flattenIso (V := C)).inv.app (leftUnitNestedFactors O.toCollection A P)



end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitRawAssembly

/- Source proof segment: LeftUnitInjection -/
section source_LeftUnitInjection
/-!
# Original left-unit unary tensor injection

The unary coefficient tensor of an original profile injection is
the actual original slot-cocone injection for left-unit substitution.
This identifies the maps used in the monad left-unit descent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The original unary scalar tensor and the original left-unit
slot tensor have the same coefficient/input values, retained as
an actual finite-family isomorphism. -/
def leftUnitSlotFactorsIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (analyticFactors O (fun _ : W => (analyticSummand O A).obj P)).obj
        (AnalyticIndex.unary (d := d) d) ≅
      (slotInputFactorsFunctor O A (AnalyticIndex.unary (d := d) d)).obj (leftUnitSlotTuple P) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option PUnit))
    (fun i => match i with
      | none => Iso.refl (O.obj (ColoredSubstitutionData.unitProfile d))
      | some _ => Iso.refl ((analyticSummand O A).obj P))

/-- Identify the original unary coefficient tensor with the selected left-unit substitution slot. -/
def leftUnitSlotTensorIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (unaryTensorFunctor O d).obj ((analyticSummand O A).obj P) ≅
      (profileSlotTensorDiagram O A (AnalyticIndex.unary (d := d) d)).obj (leftUnitSlotTuple P) :=
  (FiniteTensor.tensor (V := C)).mapIso (leftUnitSlotFactorsIso O A P)

/-- The original unary tensor map of a profile quotient injection
is precisely the left-unit tuple's actual slot tensor injection. -/
theorem unaryTensor_profileι (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (unaryTensorFunctor O d).map (profileι O A P) =
      (leftUnitSlotTensorIso O A P).hom ≫
        (profileSlotTensorCocone O A (AnalyticIndex.unary (d :=
          d) d)).ι.app (leftUnitSlotTuple P) := by
  symm
  apply Eq.trans ((FiniteTensor.tensor (V := C)).map_comp _ _).symm
  apply congrArg (FiniteTensor.tensor (V := C)).map
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none => exact heq_of_eq (Category.id_comp _)
    | some i => exact heq_of_eq (Category.id_comp _)

/-- The actual source operadic unit commutes with an arbitrary
original profile injection, with every original input retained. -/
@[reassoc]
theorem profileι_unary_unit (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    profileι O.toCollection A P ≫ unitInsertion O (profileCoinvariants O.toCollection A) d =
      (unaryTensorUnit O d).app ((analyticSummand O.toCollection A).obj P) ≫
        (leftUnitSlotTensorIso O.toCollection A P).hom ≫
        (profileSlotTensorCocone O.toCollection A (AnalyticIndex.unary (d := d) d)).ι.app
          (leftUnitSlotTuple P) := by
  have h := (unaryTensorUnit O d).naturality (profileι O.toCollection A P)
  exact (congrArg (profileι O.toCollection A P ≫ ·)
    (unaryTensorUnit_app O (profileCoinvariants O.toCollection A) d).symm).trans
      (h.trans (congrArg ((unaryTensorUnit O d).app ((analyticSummand O.toCollection A).obj P) ≫ ·)
        (unaryTensor_profileι O.toCollection A P)))



end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitInjection

/- Source proof segment: LeftUnitBetaAssembly -/
section source_LeftUnitBetaAssembly
/-!
# Actual original left-unit tuple tensor assembly
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

private theorem leftAssemblyFromFactor {V : Type*} [Category* V]
    {X B C D E F : V} (a : X ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (r : D ⟶ F) (e : B ⟶ E) (f : E ⟶ D) (u : X ⟶ E)
    (hb : b ≫ c = e ≫ f) (ha : a ≫ e = u) :
    a ≫ b ≫ c ≫ r = u ≫ f ≫ r := by
  rw [← Category.assoc b c, hb]
  simp only [Category.assoc]
  rw [← Category.assoc a e, ha]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original unary scalar tensor factors identify with the
original expanded source family by their actual coefficient/input slots. -/
def leftUnitScalarFactorsIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (analyticFactors O (fun _ : W => (analyticSummand O A).obj P)).obj (AnalyticIndex.unary
      (d := d) d) ≅
      leftUnitExpandedFamily O A P :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option PUnit))
    (fun i => match i with
      | none => Iso.refl _
      | some _ => Iso.refl _)

/-- The original arbitrary profile scalar unit insertion is the
original unit insertion into its actual expanded factor family. -/
theorem leftUnitScalarInsertion (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (unaryTensorUnit O d).app ((analyticSummand O.toCollection A).obj P) ≫
      (FiniteTensor.tensor (V := C)).map (leftUnitScalarFactorsIso O.toCollection A P).hom =
    UnitInsertion.leftInsertFromFactor ((analyticSummand O.toCollection A).obj P)
      ({ equiv := Equiv.refl (Option PUnit)
         hom i := match i with
           | none => O.unit d
           | some _ => (FiniteTensor.singletonIso (V := C)).hom.app ((analyticSummand
             O.toCollection A).obj P) } :
        UnitInsertion.leftTensorFamily ((analyticSummand O.toCollection A).obj P) ⟶
          leftUnitExpandedFamily O.toCollection A P) := by
  let X := (analyticSummand O.toCollection A).obj P
  let f := unitFactors O (fun _ : W => X) d
  let e := (leftUnitScalarFactorsIso O.toCollection A P).hom
  have h := UnitInsertion.leftInsertFromFactor_comp X f e
  refine h.trans ?_
  apply congrArg (UnitInsertion.leftInsertFromFactor X)
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none => exact heq_of_eq (Category.comp_id _)
    | some i => exact heq_of_eq (Category.comp_id _)

/-- The actual left-unit scalar-to-slot source frame retains the
coefficient singleton and every original profile input tensor. -/
theorem leftUnitTupleCoefficientFrame (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (leftUnitSlotFactorsIso O A P).hom ≫
      (coefficientTensorIso O A (AnalyticIndex.unary (d := d) d) (leftUnitSlotTuple P)).hom =
    (leftUnitScalarFactorsIso O A P).hom ≫ (leftUnitExpandedFactorsIso O A P).hom := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none => exact HEq.rfl
    | some i => exact HEq.rfl

/-- The actual original unary scalar unit followed by its original
left-unit slot assembly is precisely the original raw insertion. -/
theorem leftUnitTupleAssembly (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (unaryTensorUnit O d).app ((analyticSummand O.toCollection A).obj P) ≫
      (leftUnitSlotTensorIso O.toCollection A P).hom ≫
      profileSubstitutionAssemblyMap O.toCollection A (AnalyticIndex.unary (d :=
        d) d) (leftUnitSlotTuple P) =
    leftUnitRawInsertion O A P := by
  let T := FiniteTensor.tensor (V := C)
  let a := (unaryTensorUnit O d).app ((analyticSummand O.toCollection A).obj P)
  let b := (leftUnitSlotFactorsIso O.toCollection A P).hom
  let c := (coefficientTensorIso O.toCollection A (AnalyticIndex.unary (d :=
    d) d) (leftUnitSlotTuple P)).hom
  let r := (FiniteTensor.flattenIso (V := C)).inv.app (leftUnitNestedFactors O.toCollection A P)
  have hbc : T.map b ≫ T.map c = T.map (leftUnitScalarFactorsIso O.toCollection A P).hom ≫
      T.map (leftUnitExpandedFactorsIso O.toCollection A P).hom :=
    (T.map_comp _ _).symm.trans ((congrArg T.map (leftUnitTupleCoefficientFrame
      O.toCollection A P)).trans
      (T.map_comp _ _))
  change a ≫ T.map b ≫ (T.map c ≫ r) = _
  exact leftAssemblyFromFactor a (T.map b) (T.map c) r
    (T.map (leftUnitScalarFactorsIso O.toCollection A P).hom)
    (T.map (leftUnitExpandedFactorsIso O.toCollection A P).hom) _ hbc
      (leftUnitScalarInsertion O A P)



end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitBetaAssembly

/- Source proof segment: ProfileLeafRelabel -/
section source_ProfileLeafRelabel
/-!
# Original leaf-input relabelling

Every original colored profile bijection reindexes the same leaf
input family, retaining each original input-color equality. Unit
and associativity total-profile maps use this exact source map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

/-- The actual original leaf-input map induced by a full colored
profile bijection, preserving every original input color. -/
def profileLeafRelabel (A : W → C) {P Q : ColoredProfile W} (f : P ⟶ Q) :
    profileLeafFamily A P ⟶ profileLeafFamily A Q where
  equiv := f.inputEquiv
  hom i := eqToHom (congrArg A (f.inputColor_eq i))

/-- The original profile relabelling gives an actual isomorphism
of its original finite leaf-input families. -/
def profileLeafRelabelIso (A : W → C) {P Q : ColoredProfile W} (f : P ⟶ Q) :
    profileLeafFamily A P ≅ profileLeafFamily A Q :=
  FiniteFamily.isoOfReindex f.inputEquiv (fun i => congrArg A (f.inputColor_eq i))

@[simp]
theorem profileLeafRelabelIso_hom (A : W → C) {P Q : ColoredProfile W} (f : P ⟶ Q) :
    (profileLeafRelabelIso A f).hom = profileLeafRelabel A f :=
  rfl

variable [FiniteTensor C]

/-- Tensor the actual original leaf-input profile reindexing. -/
def profileLeafTensorIso (A : W → C) {P Q : ColoredProfile W} (f : P ⟶ Q) :
    (FiniteTensor.tensor (V := C)).obj (profileLeafFamily A P) ≅
      (FiniteTensor.tensor (V := C)).obj (profileLeafFamily A Q) :=
  (FiniteTensor.tensor (V := C)).mapIso (profileLeafRelabelIso A f)



end CategoryTheory.Operad.Tensor
end
end
end source_ProfileLeafRelabel

/- Source proof segment: LeftUnitCoefficientLeaves -/
section source_LeftUnitCoefficientLeaves
/-!
# Original left-unit coefficient grouping with unchanged leaves

The source coefficient grouping is exactly the existing left-unit
insertion grouping. The original profile leaf-input family occupies
its matching branch; the original outer unary-unit source is empty.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original source left-unit coefficient grouping. -/
def leftUnitCoefficientGrouping (O : ColoredSymmetricCollection W C)
    {d : W} (P : AnalyticIndex W d) : FiniteFamily (FiniteFamily C) :=
  UnitInsertion.leftNestedFamily (O.obj P.toColoredProfile)

/-- The original leaf family remains in its original inner
coefficient block, while the outer unit source has no leaf. -/
def leftUnitLeafBlocks (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) : (leftUnitCoefficientGrouping O P).index → FiniteFamily C
  | none => FiniteFamily.empty
  | some _ => profileLeafFamily A P.toColoredProfile

/-- The original unary unit and coefficient singleton unitor map
to the original left-unit operadic coefficient factors. -/
def leftUnitCoefficientFactorMap (O : ColoredOperadObj W C)
    {d : W} (P : AnalyticIndex W d) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        (leftUnitCoefficientGrouping O.toCollection P) ⟶
      (ColoredOperadObj.substitutionFactors O.toCollection).obj
        (ColoredSubstitutionData.leftUnit P.toColoredProfile) :=
  ColoredOperadObj.UnitInsertion.leftFactorHom O.toCollection O.unit P.toColoredProfile

/-- The original source left-unit total profile uses its original
sigma-singleton input bijection on every retained leaf input. -/
def leftUnitLeafTotalIso (A : W → C) {d : W} (P : AnalyticIndex W d) :
    profileLeafFamily A (ColoredSubstitutionData.leftUnit P.toColoredProfile).totalProfile ≅
      profileLeafFamily A P.toColoredProfile :=
  profileLeafRelabelIso A (ColoredSubstitutionData.leftUnitTotalHom P.toColoredProfile)



end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitCoefficientLeaves

/- Source proof segment: LeftUnitPartitionSource -/
section source_LeftUnitPartitionSource
/-!
# Actual original left-unit partition source

The original coefficient and all original A inputs occupy the
inner block, while the outer unary unit source is empty. The actual
flat source bijection retains every input position and object.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The exact original left-unit partition source input bijection. -/
def leftUnitPartitionSourceEquiv (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    ((analyticFactors O A).obj P).index ≃
      ((FiniteFamily.flatten (C := C)).obj
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
          (partitionedCoefficientLeavesTriple (leftUnitCoefficientGrouping O P)
            (leftUnitLeafBlocks O A P)))).index where
  toFun i := match i with
    | none => ⟨some PUnit.unit, ⟨none, PUnit.unit⟩⟩
    | some i => ⟨some PUnit.unit, ⟨some i, PUnit.unit⟩⟩
  invFun i := match i with
    | ⟨none, ⟨none, k⟩⟩ => nomatch k
    | ⟨none, ⟨some l, _⟩⟩ => nomatch l
    | ⟨some _, ⟨none, _⟩⟩ => none
    | ⟨some _, ⟨some i, _⟩⟩ => some i
  left_inv i := by cases i <;> rfl
  right_inv i := by
    rcases i with ⟨i, ⟨l, k⟩⟩
    cases i with
    | none =>
      cases l with
      | none => nomatch k
      | some l => nomatch l
    | some i =>
      cases i
      cases l with
      | none => cases k; rfl
      | some l => cases k; rfl

/-- The exact original left-unit partition source isomorphism
retains each original operation coefficient and A input object. -/
def leftUnitPartitionSourceIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (analyticFactors O A).obj P ≅
      (FiniteFamily.flatten (C := C)).obj
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
          (partitionedCoefficientLeavesTriple (leftUnitCoefficientGrouping O P)
            (leftUnitLeafBlocks O A P))) :=
  FiniteFamily.isoOfReindex (leftUnitPartitionSourceEquiv O A P)
    (fun i => by cases i <;> rfl)

end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitPartitionSource

/- Source proof segment: EmptyFlattenCoherence -/
section source_EmptyFlattenCoherence
/-!
# Actual empty-block finite tensor flattening coherence
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Flatten the original empty family of finite families. -/
def emptyNestedFlattenIso :
    (FiniteFamily.flatten (C := C)).obj (FiniteFamily.empty : FiniteFamily (FiniteFamily C)) ≅
      (FiniteFamily.empty : FiniteFamily C) :=
  FiniteFamily.isoOfReindex
    { toFun := fun p => p.1
      invFun := fun e => e.elim
      left_inv := fun p => by cases p.1
      right_inv := fun e => by cases e }
    (fun p => by cases p.1)

theorem emptyFlattenMapSquare :
    (FiniteFamily.flatten (C := C)).map
        (FiniteFamily.mapEmptyIso (FiniteFamily.singleton (C := C))).hom ≫
      (emptyNestedFlattenIso (C := C)).hom =
    FiniteFamily.mapSingletonFlattenIso.hom.app (FiniteFamily.empty : FiniteFamily C) := by
  apply FiniteFamily.Hom_ext
  · ext p
    cases p.1
  · intro p
    cases p.1

variable [FiniteTensor C]

theorem emptyFlattenTensorSquare :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map
        (FiniteFamily.mapEmptyIso (FiniteFamily.singleton (C := C))).hom ≫
      (FiniteFamily.mapEmptyIso (FiniteTensor.tensor (V := C))).hom =
    (FiniteFamily.mapIso (FiniteTensor.singletonIso (V := C))).hom.app
      (FiniteFamily.empty : FiniteFamily C) := by
  apply FiniteFamily.Hom_ext
  · ext p
    cases p
  · intro p
    cases p

/-- The actual empty-block flattening followed by its original
empty tensor-family identification equals the original empty index
identification. It follows from the finite tensor right unit law. -/
theorem flattenIso_empty_collapse :
    (FiniteTensor.flattenIso (V := C)).hom.app
        (FiniteFamily.empty : FiniteFamily (FiniteFamily C)) ≫
      (FiniteTensor.tensor (V := C)).map
        (FiniteFamily.mapEmptyIso (FiniteTensor.tensor (V := C))).hom =
    (FiniteTensor.tensor (V := C)).map (emptyNestedFlattenIso (C := C)).hom := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let E := (FiniteFamily.empty : FiniteFamily C)
  let N := (FiniteFamily.map (FiniteFamily.singleton (C := C))).obj E
  let M := (FiniteFamily.empty : FiniteFamily (FiniteFamily C))
  let e := (FiniteFamily.mapEmptyIso (FiniteFamily.singleton (C := C))).hom
  let r := T.map (F.map e)
  let a := (FiniteTensor.flattenIso (V := C)).hom.app N
  let b := (FiniteTensor.flattenIso (V := C)).hom.app M
  let c := T.map ((FiniteFamily.map T).map e)
  let d := T.map ((FiniteFamily.mapIso (FiniteTensor.singletonIso (V := C))).hom.app E)
  let u := T.map (FiniteFamily.mapEmptyIso T).hom
  let z := T.map (emptyNestedFlattenIso (C := C)).hom
  let q := T.map (FiniteFamily.mapSingletonFlattenIso.hom.app E)
  have hn := (FiniteTensor.flattenIso (V := C)).hom.naturality e
  change r ≫ b = a ≫ c at hn
  have hc : c ≫ u = d :=
    (T.map_comp _ _).symm.trans (congrArg T.map (emptyFlattenTensorSquare (C := C)))
  have hs : r ≫ z = q :=
    (T.map_comp _ _).symm.trans (congrArg T.map (emptyFlattenMapSquare (C := C)))
  have hu : q = a ≫ d := mapSingletonFlattenLaw_app E
  have h : r ≫ b ≫ u = r ≫ z :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ u) hn).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (a ≫ ·) hc).trans (hu.symm.trans hs.symm))))
  have : IsIso r := by dsimp [r, e]; infer_instance
  exact (cancel_epi r).1 h



end CategoryTheory.Operad.Tensor
end
end
end source_EmptyFlattenCoherence

/- Source proof segment: SparseUnitTensorData -/
section source_SparseUnitTensorData
/-!
# Original sparse empty-root tensor source data
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- An empty coefficient block followed by the original full input family. -/
@[implicit_reducible]
def sparseUnitOriginalBlocks (L : FiniteFamily C) : FiniteFamily (FiniteFamily C) where
  index := FintypeCat.of (Option PUnit)
  obj i := match i with
    | none => FiniteFamily.empty
    | some _ => L

/-- The original sparse left-insertion shape in the category of finite families. -/
@[implicit_reducible]
def sparseUnitTriple (L : FiniteFamily C) : FiniteFamily (FiniteFamily (FiniteFamily C)) :=
  UnitInsertion.leftNestedFamily (V := FiniteFamily C) L

/-- Locally flatten the empty unit block and original leaf block of the sparse left-unit triple. -/
def sparseUnitFlattenIso (L : FiniteFamily C) :
    (FiniteFamily.map (FiniteFamily.flatten (C := C))).obj (sparseUnitTriple L) ≅
      sparseUnitOriginalBlocks L :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option PUnit))
    (fun i => match i with
      | none => emptyNestedFlattenIso
      | some _ => FiniteFamily.singletonFlattenIso.app L)

/-- Identify the singleton original leaf block with the sparse left-unit triple after outer
flattening. -/
def sparseUnitBlockIso (L : FiniteFamily C) :
    (FiniteFamily.singleton (C := FiniteFamily C)).obj L ≅
      (FiniteFamily.flatten (C := FiniteFamily C)).obj (sparseUnitTriple L) :=
  FiniteFamily.isoOfComponents (UnitInsertion.leftSingletonToFlatten (V := FiniteFamily C) L).equiv
    (fun _ => Iso.refl L)

theorem sparseUnitBlockIso_hom (L : FiniteFamily C) :
    (sparseUnitBlockIso L).hom = UnitInsertion.leftSingletonToFlatten (V := FiniteFamily C) L := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i
    rfl

/-- The original input family in the actual triple flattening source. -/
def sparseUnitTripleSourceIso (L : FiniteFamily C) :
    L ≅ (FiniteFamily.flatten (C := C)).obj
      ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj (sparseUnitTriple L)) :=
  (FiniteFamily.singletonFlattenIso.app L).symm ≪≫
    (FiniteFamily.flatten (C := C)).mapIso (sparseUnitBlockIso L) ≪≫
    (FiniteFamily.flattenAssocIso.app (sparseUnitTriple L)).symm

theorem sparseUnitTripleSourceIso_hom (L : FiniteFamily C) :
    (sparseUnitTripleSourceIso L).hom =
      FiniteFamily.singletonFlattenIso.inv.app L ≫
        (FiniteFamily.flatten (C := C)).map (sparseUnitBlockIso L).hom ≫
        FiniteFamily.flattenAssocIso.inv.app (sparseUnitTriple L) := rfl

/-- The original sparse input bijection inserts no root factors and
retains every original input position. -/
def sparseUnitOriginalSourceEquiv (L : FiniteFamily C) :
    L.index ≃ ((FiniteFamily.flatten (C := C)).obj (sparseUnitOriginalBlocks L)).index where
  toFun i := ⟨some PUnit.unit, i⟩
  invFun p := match p with
    | ⟨none, e⟩ => e.elim
    | ⟨some _, i⟩ => i
  left_inv i := rfl
  right_inv p := by
    rcases p with ⟨o, i⟩
    cases o with
    | none => cases i
    | some o => cases o; rfl

/-- Identify the original leaf family with the flattened sparse left-unit blocks. -/
def sparseUnitOriginalSourceIso (L : FiniteFamily C) :
    L ≅ (FiniteFamily.flatten (C := C)).obj (sparseUnitOriginalBlocks L) :=
  FiniteFamily.isoOfReindex (sparseUnitOriginalSourceEquiv L) (fun _ => rfl)

/-- The actual associator and singleton-index maps give the original
sparse insertion source bijection. -/
theorem sparseUnitOriginalSourceIso_hom (L : FiniteFamily C) :
    (sparseUnitOriginalSourceIso L).hom =
      (sparseUnitTripleSourceIso L).hom ≫
        (FiniteFamily.flatten (C := C)).map (sparseUnitFlattenIso L).hom := by
  apply FiniteFamily.Hom_ext
  · ext i
    rfl
  · intro i
    change HEq (𝟙 (L.obj i)) ((𝟙 (L.obj i) ≫ 𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _)
    exact heq_of_eq (by simp only [Category.id_comp])

/-- The two-slot family of the unit coefficient and original leaf tensor. -/
def sparseUnitScalarFamily (Y X : C) : FiniteFamily C where
  index := FintypeCat.of (Option PUnit)
  obj i := match i with
    | none => Y
    | some _ => X

variable [FiniteTensor C]

/-- Evaluating the original lowest blocks gives the actual sparse
left-insertion family of the whole original input tensor. -/
def sparseUnitTensorIso (L : FiniteFamily C) :
    (FiniteFamily.map (FiniteFamily.map (FiniteTensor.tensor (V := C)))).obj (sparseUnitTriple L) ≅
      UnitInsertion.leftNestedFamily ((FiniteTensor.tensor (V := C)).obj L) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option PUnit))
    (fun i => match i with
      | none => FiniteFamily.mapEmptyIso (FiniteTensor.tensor (V := C))
      | some _ => Iso.refl _)

/-- The original coefficient map is inserted before the whole
original input tensor, with its original singleton unitor. -/
def sparseUnitFactor {Y : C}
    (η : (FiniteTensor.tensor (V := C)).obj (FiniteFamily.empty : FiniteFamily C) ⟶ Y)
    (L : FiniteFamily C) :
    UnitInsertion.leftTensorFamily ((FiniteTensor.tensor (V := C)).obj L) ⟶
      sparseUnitScalarFamily Y ((FiniteTensor.tensor (V := C)).obj L) where
  equiv := Equiv.refl (Option PUnit)
  hom i := match i with
    | none => η
    | some _ => (FiniteTensor.singletonIso (V := C)).hom.app ((FiniteTensor.tensor (V := C)).obj L)

/-- Insert the original unit map into the evaluated sparse left-unit blocks. -/
def sparseUnitOriginalFactor {Y : C}
    (η : (FiniteTensor.tensor (V := C)).obj (FiniteFamily.empty : FiniteFamily C) ⟶ Y)
    (L : FiniteFamily C) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (sparseUnitOriginalBlocks L) ⟶
      sparseUnitScalarFamily Y ((FiniteTensor.tensor (V := C)).obj L) where
  equiv := Equiv.refl (Option PUnit)
  hom i := match i with
    | none => η
    | some _ => 𝟙 _

/-- Insert the original unit map after local flattening of the sparse left-unit triple. -/
def sparseUnitFlatFactor {Y : C}
    (η : (FiniteTensor.tensor (V := C)).obj (FiniteFamily.empty : FiniteFamily C) ⟶ Y)
    (L : FiniteFamily C) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj (sparseUnitTriple L)) ⟶
      sparseUnitScalarFamily Y ((FiniteTensor.tensor (V := C)).obj L) :=
  (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (sparseUnitFlattenIso L).hom ≫
    sparseUnitOriginalFactor η L

/-- Insert the original unit map into the locally evaluated sparse left-unit triple. -/
def sparseUnitEvaluatedFactor {Y : C}
    (η : (FiniteTensor.tensor (V := C)).obj (FiniteFamily.empty : FiniteFamily C) ⟶ Y)
    (L : FiniteFamily C) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        ((FiniteFamily.map (FiniteFamily.map (FiniteTensor.tensor (V :=
          C)))).obj (sparseUnitTriple L)) ⟶
      sparseUnitScalarFamily Y ((FiniteTensor.tensor (V := C)).obj L) :=
  (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (sparseUnitTensorIso L).hom ≫
    sparseUnitFactor η L

/-- The original local empty and singleton-block collapses retain
the same original coefficient insertion and whole input tensor. -/
theorem sparseUnitLocalCollapse {Y : C}
    (η : (FiniteTensor.tensor (V := C)).obj (FiniteFamily.empty : FiniteFamily C) ⟶ Y)
    (L : FiniteFamily C) :
    (FiniteFamily.mapIso (FiniteTensor.flattenIso (V := C))).hom.app (sparseUnitTriple L) ≫
      sparseUnitEvaluatedFactor η L = sparseUnitFlatFactor η L := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      change HEq
        ((FiniteTensor.flattenIso (V := C)).hom.app (FiniteFamily.empty : FiniteFamily
          (FiniteFamily C)) ≫
          (FiniteTensor.tensor (V := C)).map (FiniteFamily.mapEmptyIso (FiniteTensor.tensor
            (V := C))).hom ≫ η)
        ((FiniteTensor.tensor (V := C)).map (emptyNestedFlattenIso (C := C)).hom ≫ η)
      exact heq_of_eq ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ η) (flattenIso_empty_collapse (C := C))))
    | some i =>
      let T := FiniteTensor.tensor (V := C)
      let X := T.obj L
      let a := (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.singleton (C := FiniteFamily C)).obj L)
      let s := (FiniteTensor.singletonIso (V := C)).hom.app X
      let r := T.map (FiniteFamily.singletonFlattenIso.hom.app L)
      have hu : a ≫ s = r := (singletonFlattenLaw_app L).symm
      change HEq (a ≫ T.map (𝟙 ((FiniteFamily.singleton (C := C)).obj X)) ≫ s) (r ≫ 𝟙 X)
      exact heq_of_eq ((congrArg (fun f => a ≫ f ≫ s) (T.map_id _)).trans
        ((congrArg (a ≫ ·) (Category.id_comp s)).trans (hu.trans (Category.comp_id r).symm)))



end CategoryTheory.Operad.Tensor
end
end
end source_SparseUnitTensorData

/- Source proof segment: LeftUnitSourceData -/
section source_LeftUnitSourceData
/-!
# Original left-unit source partitions and coefficient data
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

theorem leftUnitOuterHom_identity {d : W} (P : AnalyticIndex W d) :
    ColoredSubstitutionData.leftUnitOuterHom P.toColoredProfile =
      𝟙 (ColoredSubstitutionData.unitProfile d) := rfl

variable [FiniteTensor C]

/-- Actual original left-unit coefficient blocks on the original
unary substitution slots. -/
def leftUnitSourceBlocks (O : ColoredSymmetricCollection W C) {d : W} (P : AnalyticIndex W d) :
    Option (ColoredSubstitutionData.leftUnit P.toColoredProfile).inner.index → FiniteFamily C :=
  (leftUnitCoefficientGrouping O P).obj

omit [FiniteTensor C] in
theorem leftUnitSourceGrouping (O : ColoredSymmetricCollection W C) {d : W} (P :
  AnalyticIndex W d) :
    substitutionBranchGrouping (ColoredSubstitutionData.leftUnit P.toColoredProfile)
      (leftUnitSourceBlocks O P) =
      leftUnitCoefficientGrouping O P := rfl

/-- The original coefficient components of the left-unit substitution map. -/
def leftUnitSourceCoefficientMap (O : ColoredOperadObj W C) {d : W} (P : AnalyticIndex W d) :
    ∀ i, (FiniteTensor.tensor (V := C)).obj (leftUnitSourceBlocks O.toCollection P i) ⟶
      substitutionBranchCoefficients O.toCollection (ColoredSubstitutionData.leftUnit
        P.toColoredProfile) i :=
  (leftUnitCoefficientFactorMap O P).hom

theorem leftUnitSourceCoefficientMap_none (O : ColoredOperadObj W C) {d : W} (P :
  AnalyticIndex W d) :
    leftUnitSourceCoefficientMap O P none = O.unit d := by
  change O.unit d ≫ O.toCollection.map (ColoredSubstitutionData.leftUnitOuterHom
    P.toColoredProfile) = _
  rw [leftUnitOuterHom_identity]
  let η : (FiniteTensor.tensor (V := C)).obj (FiniteFamily.empty : FiniteFamily C) ⟶
    O.toCollection.obj (ColoredSubstitutionData.unitProfile d) := O.unit d
  change η ≫ O.toCollection.map (𝟙 (ColoredSubstitutionData.unitProfile d)) = η
  exact (congrArg (η ≫ ·) (O.toCollection.map_id _)).trans (Category.comp_id η)

/-- The actual left coefficient insertion source has only the
original inner coefficient, with its original singleton index map. -/
def leftUnitCoefficientSourceIso (O : ColoredSymmetricCollection W C) {d : W} (P :
  AnalyticIndex W d) :
    (FiniteFamily.flatten (C := C)).obj (leftUnitCoefficientGrouping O P) ≅
      (FiniteFamily.singleton (C := C)).obj (O.obj P.toColoredProfile) :=
  FiniteFamily.isoOfReindex
    (UnitInsertion.leftSingletonToFlatten (O.obj P.toColoredProfile)).equiv.symm
    (fun i => by
      rcases i with ⟨o, i⟩
      cases o with
      | none => cases i
      | some o => cases o; cases i; rfl)

end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitSourceData

/- Source proof segment: SparseUnitTensorPrefix -/
section source_SparseUnitTensorPrefix
/-!
# Original sparse tensor insertion source prefix
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

theorem sparseCancelRightPair {C : Type u} [Category.{v} C]
    {X A B D : C} (a : X ⟶ A) (b : A ⟶ B) (i : B ⟶ D) (h : D ⟶ B)
    (hi : i ≫ h = 𝟙 B) : (a ≫ b ≫ i) ≫ h = a ≫ b := by
  simp only [Category.assoc]
  rw [hi, Category.comp_id]

theorem sparseUnitSource_assoc (L : FiniteFamily C) :
    (sparseUnitTripleSourceIso L).hom ≫
        FiniteFamily.flattenAssocIso.hom.app (sparseUnitTriple L) =
      FiniteFamily.singletonFlattenIso.inv.app L ≫
        (FiniteFamily.flatten (C := C)).map (sparseUnitBlockIso L).hom := by
  let a := FiniteFamily.singletonFlattenIso.inv.app L
  let b := (FiniteFamily.flatten (C := C)).map (sparseUnitBlockIso L).hom
  let e := FiniteFamily.flattenAssocIso.app (sparseUnitTriple L)
  have hp := sparseUnitTripleSourceIso_hom L
  exact (congrArg (· ≫ e.hom) hp).trans (sparseCancelRightPair a b e.inv e.hom e.inv_hom_id)

theorem sparsePrefixFromTwoSquares {C : Type u} [Category.{v} C]
    {X A B P Q R : C} (p : X ⟶ A) (q : A ⟶ B) (s : B ⟶ R)
    (a : X ⟶ P) (b : P ⟶ B) (c : P ⟶ Q) (d : Q ⟶ R) (e : X ⟶ Q)
    (hs : p ≫ q = a ≫ b) (hn : b ≫ s = c ≫ d) (hu : a ≫ c = e) :
    p ≫ q ≫ s = e ≫ d := by
  rw [← Category.assoc p q, hs, Category.assoc a b, hn, ← Category.assoc a c, hu]

variable [FiniteTensor C]

/-- The actual singleton-flatten unit law in inverse firing form. -/
theorem singletonFlatten_tensor_prefix (L : FiniteFamily C) :
    (FiniteTensor.tensor (V := C)).map (FiniteFamily.singletonFlattenIso.inv.app L) ≫
        (FiniteTensor.flattenIso (V := C)).hom.app
          ((FiniteFamily.singleton (C := FiniteFamily C)).obj L) =
      (FiniteTensor.singletonIso (V := C)).inv.app ((FiniteTensor.tensor (V := C)).obj L) := by
  let T := FiniteTensor.tensor (V := C)
  let X := T.obj L
  let q := T.map (FiniteFamily.singletonFlattenIso.inv.app L)
  let a := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.singleton (C := FiniteFamily C)).obj L)
  let s := (FiniteTensor.singletonIso (V := C)).hom.app X
  have hunit := singletonFlattenLaw_app L
  have hi : q ≫ T.map (FiniteFamily.singletonFlattenIso.hom.app L) = 𝟙 _ :=
    (T.map_comp _ _).symm.trans
      ((congrArg T.map (FiniteFamily.singletonFlattenIso.inv_hom_id_app L)).trans (T.map_id _))
  have : IsIso s := by dsimp [s]; infer_instance
  apply (cancel_mono s).1
  exact (Category.assoc _ _ _).trans
    ((congrArg (q ≫ ·) hunit.symm).trans
      (hi.trans ((FiniteTensor.singletonIso (V := C)).inv_hom_id_app X).symm))

/-- The original whole input tensor singleton map is exactly the
mapped original finite-family singleton map, retaining sparse indices. -/
theorem sparseUnitMappedBlock (L : FiniteFamily C) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (sparseUnitBlockIso L).hom =
      UnitInsertion.leftSingletonToFlatten ((FiniteTensor.tensor (V := C)).obj L) ≫
        (FiniteFamily.flatten (C := C)).map (sparseUnitTensorIso L).inv := by
  apply FiniteFamily.Hom_ext
  · ext i
    cases i
    rfl
  · intro i
    cases i
    let T := FiniteTensor.tensor (V := C)
    let X := T.obj L
    change HEq (T.map (𝟙 L)) (𝟙 X ≫ 𝟙 X ≫ 𝟙 X)
    exact heq_of_eq ((T.map_id L).trans (show (𝟙 X) ≫ 𝟙 X ≫ 𝟙 X = 𝟙 X from by
      simp only [Category.id_comp]).symm)

/-- The original sparse triple source before its final tensor
flattening is the original whole-tensor singleton insertion prefix. -/
theorem sparseUnitTensorPrefix (L : FiniteFamily C) :
    (FiniteTensor.tensor (V := C)).map (sparseUnitTripleSourceIso L).hom ≫
      (FiniteTensor.tensor (V := C)).map (FiniteFamily.flattenAssocIso.hom.app
        (sparseUnitTriple L)) ≫
      (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.flatten (C := FiniteFamily C)).obj (sparseUnitTriple L)) =
    (FiniteTensor.singletonIso (V := C)).inv.app ((FiniteTensor.tensor (V := C)).obj L) ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).map (sparseUnitBlockIso L).hom) := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let N := sparseUnitTriple L
  let p := T.map (sparseUnitTripleSourceIso L).hom
  let q := T.map (FiniteFamily.flattenAssocIso.hom.app N)
  let s := (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.flatten (C :=
    FiniteFamily C)).obj N)
  let a := T.map (FiniteFamily.singletonFlattenIso.inv.app L)
  let b := T.map (F.map (sparseUnitBlockIso L).hom)
  let c := (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.singleton (C :=
    FiniteFamily C)).obj L)
  let d := T.map ((FiniteFamily.map T).map (sparseUnitBlockIso L).hom)
  let e := (FiniteTensor.singletonIso (V := C)).inv.app (T.obj L)
  have hs : p ≫ q = a ≫ b :=
    (T.map_comp _ _).symm.trans
      ((congrArg T.map (sparseUnitSource_assoc L)).trans (T.map_comp _ _))
  have hn := (FiniteTensor.flattenIso (V := C)).hom.naturality (sparseUnitBlockIso L).hom
  change b ≫ s = c ≫ d at hn
  have hu : a ≫ c = e := singletonFlatten_tensor_prefix L
  exact sparsePrefixFromTwoSquares p q s a b c d e hs hn hu



end CategoryTheory.Operad.Tensor
end
end
end source_SparseUnitTensorPrefix

/- Source proof segment: SparseUnitTensorAssembly -/
section source_SparseUnitTensorAssembly
/-!
# Original unit insertion before a whole finite tensor
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

theorem sparseTensorMappedSquare {C : Type u} [Category.{v} C]
    {X A B P Q Y : C} (k : X ⟶ A) (l : X ⟶ B) (q : B ⟶ A)
    (e : A ⟶ P) (u : P ⟶ Y) (m : B ⟶ Q) (f : Q ⟶ Y)
    (hk : k = l ≫ q) (hq : q ≫ e ≫ u = m ≫ f) :
    k ≫ e ≫ u = l ≫ m ≫ f := by
  rw [hk]
  simp only [Category.assoc]
  rw [hq]

theorem sparseTensorAssemblyFromSquares {C : Type u} [Category.{v} C]
    {X R A B S D P Q W Y : C}
    (p : X ⟶ R) (a : R ⟶ A) (b : A ⟶ B) (u : B ⟶ Y) (w : A ⟶ Y)
    (q : R ⟶ S) (d : S ⟶ D) (e : D ⟶ B)
    (r : X ⟶ P) (k : P ⟶ D) (l : P ⟶ Q) (m : Q ⟶ W) (f : W ⟶ Y)
    (ha : a ≫ b = q ≫ d ≫ e) (hw : b ≫ u = w)
    (hp : p ≫ q ≫ d = r ≫ k) (hm : k ≫ e ≫ u = l ≫ m ≫ f) :
    p ≫ a ≫ w = (r ≫ l ≫ m) ≫ f := by
  calc
    p ≫ a ≫ w = p ≫ a ≫ b ≫ u := by rw [← hw]
    _ = p ≫ q ≫ d ≫ e ≫ u := by
      simpa only [Category.assoc] using congrArg (fun z => p ≫ z ≫ u) ha
    _ = r ≫ k ≫ e ≫ u := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ e ≫ u) hp
    _ = (r ≫ l ≫ m) ≫ f := by
      simpa only [Category.assoc] using congrArg (r ≫ ·) hm

theorem sparseTensorSourceAdaptation {C : Type u} [Category.{v} C]
    {X R A B D Y : C} (r : X ⟶ R) (p : X ⟶ A) (q : A ⟶ R)
    (s : R ⟶ B) (o : B ⟶ Y) (a : A ⟶ D) (b : D ⟶ B) (w : D ⟶ Y)
    (hr : r = p ≫ q) (hn : q ≫ s = a ≫ b) (hf : b ≫ o = w) :
    r ≫ s ≫ o = p ≫ a ≫ w := by
  rw [hr]
  simp only [Category.assoc]
  rw [← Category.assoc q s, hn]
  simp only [Category.assoc]
  rw [hf]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

theorem sparseUnitEvaluated_cancel {Y : C}
    (η : (FiniteTensor.tensor (V := C)).obj (FiniteFamily.empty : FiniteFamily C) ⟶ Y)
    (L : FiniteFamily C) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (sparseUnitTensorIso L).inv ≫
      sparseUnitEvaluatedFactor η L = sparseUnitFactor η L := by
  let F := FiniteFamily.map (FiniteTensor.tensor (V := C))
  let e := sparseUnitTensorIso L
  let f : F.obj (UnitInsertion.leftNestedFamily ((FiniteTensor.tensor (V := C)).obj L)) ⟶
    sparseUnitScalarFamily Y ((FiniteTensor.tensor (V := C)).obj L) := sparseUnitFactor η L
  have hi : F.map e.inv ≫ F.map e.hom = 𝟙 _ :=
    (F.map_comp _ _).symm.trans ((congrArg F.map e.inv_hom_id).trans (F.map_id _))
  change F.map e.inv ≫ F.map e.hom ≫ f = f
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ f) hi).trans (Category.id_comp f))

/-- The source tensor unit coefficient is inserted before the whole
original finite tensor by exactly its sparse empty-root source assembly. -/
theorem sparseUnit_beforeTensor {Y : C}
    (η : (FiniteTensor.tensor (V := C)).obj (FiniteFamily.empty : FiniteFamily C) ⟶ Y)
    (L : FiniteFamily C) :
    UnitInsertion.leftInsertFromFactor ((FiniteTensor.tensor (V :=
      C)).obj L) (sparseUnitFactor η L) =
      (FiniteTensor.tensor (V := C)).map (sparseUnitOriginalSourceIso L).hom ≫
        (FiniteTensor.flattenIso (V := C)).hom.app (sparseUnitOriginalBlocks L) ≫
        (FiniteTensor.tensor (V := C)).map (sparseUnitOriginalFactor η L) := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let N := sparseUnitTriple L
  let A := (FiniteFamily.map F).obj N
  let B := (FiniteFamily.flatten (C := FiniteFamily C)).obj N
  let M := (FiniteFamily.map (FiniteFamily.map T)).obj N
  let X := T.obj L
  let p := T.map (sparseUnitTripleSourceIso L).hom
  let a := (FiniteTensor.flattenIso (V := C)).hom.app A
  let b := T.map ((FiniteFamily.mapIso (FiniteTensor.flattenIso (V := C))).hom.app N)
  let u := T.map (sparseUnitEvaluatedFactor η L)
  let w := T.map (sparseUnitFlatFactor η L)
  let q := T.map (FiniteFamily.flattenAssocIso.hom.app N)
  let d := (FiniteTensor.flattenIso (V := C)).hom.app B
  let e := (FiniteTensor.flattenIso (V := C)).hom.app M
  let r := (FiniteTensor.singletonIso (V := C)).inv.app X
  let k := T.map ((FiniteFamily.map T).map (sparseUnitBlockIso L).hom)
  let l := T.map (UnitInsertion.leftSingletonToFlatten X)
  let m := (FiniteTensor.flattenIso (V := C)).hom.app (UnitInsertion.leftNestedFamily X)
  let f := T.map (sparseUnitFactor η L)
  let h := T.map ((FiniteFamily.flattenMapIso T).hom.app N)
  have hh : h = 𝟙 _ := by
    change T.map (𝟙 _) = 𝟙 _
    exact T.map_id _
  have ha := FiniteTensor.flattenAssocLaw_app_unfold N
  change a ≫ b = q ≫ d ≫ h ≫ e at ha
  have hassoc := eraseMiddleUnit a b q d h e hh ha
  have hw : b ≫ u = w :=
    (T.map_comp _ _).symm.trans (congrArg T.map (sparseUnitLocalCollapse η L))
  have hp : p ≫ q ≫ d = r ≫ k := sparseUnitTensorPrefix L
  let z := T.map (F.map (sparseUnitTensorIso L).inv)
  have hk : k = l ≫ z :=
    (congrArg T.map (sparseUnitMappedBlock L)).trans (T.map_comp _ _)
  have hn := (FiniteTensor.flattenIso (V := C)).hom.naturality (sparseUnitTensorIso L).inv
  change z ≫ e = m ≫ T.map ((FiniteFamily.map T).map (sparseUnitTensorIso L).inv) at hn
  have hq : z ≫ e ≫ u = m ≫ f :=
    (functorMapPostSquare T z e m ((FiniteFamily.map T).map (sparseUnitTensorIso L).inv)
      (sparseUnitEvaluatedFactor η L) hn).trans
      (congrArg (fun g => m ≫ T.map g) (sparseUnitEvaluated_cancel η L))
  have hm : k ≫ e ≫ u = l ≫ m ≫ f := sparseTensorMappedSquare k l z e u m f hk hq
  have ht : p ≫ a ≫ w = UnitInsertion.leftInsertFromFactor X (sparseUnitFactor η L) :=
    sparseTensorAssemblyFromSquares p a b u w q d e r k l m f hassoc hw hp hm
  let src := T.map (sparseUnitOriginalSourceIso L).hom
  let qa := T.map (F.map (sparseUnitFlattenIso L).hom)
  let sa := (FiniteTensor.flattenIso (V := C)).hom.app (sparseUnitOriginalBlocks L)
  let oa := T.map (sparseUnitOriginalFactor η L)
  let ba := T.map ((FiniteFamily.map T).map (sparseUnitFlattenIso L).hom)
  have hsrc : src = p ≫ qa :=
    (congrArg T.map (sparseUnitOriginalSourceIso_hom L)).trans (T.map_comp _ _)
  have hna := (FiniteTensor.flattenIso (V := C)).hom.naturality (sparseUnitFlattenIso L).hom
  change qa ≫ sa = a ≫ ba at hna
  have hfa : ba ≫ oa = w := (T.map_comp _ _).symm
  have hadapt := sparseTensorSourceAdaptation src p qa sa oa a ba w hsrc hna hfa
  exact ht.symm.trans hadapt.symm



end CategoryTheory.Operad.Tensor
end
end
end source_SparseUnitTensorAssembly

/- Source proof segment: LeftUnitRawBlockData -/
section source_LeftUnitRawBlockData
/-!
# Original sparse block and scalar identifications for left-unit insertion
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original sparse left partition consists of an empty root
and the complete original inner profile factor family. -/
def leftUnitRawBlocksIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
        (partitionedCoefficientLeavesTriple (leftUnitCoefficientGrouping O P)
          (leftUnitLeafBlocks O A P)) ≅
      sparseUnitOriginalBlocks ((analyticFactors O A).obj P) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option PUnit))
    (fun i => match i with
      | none => emptyLeafRawIso (FiniteFamily.empty : FiniteFamily C)
      | some _ =>
          (FiniteFamily.flatten (C := C)).mapIso
              (singletonCoefficientLeavesIso (O.obj P.toColoredProfile) (profileLeafFamily A
                P.toColoredProfile)) ≪≫
            FiniteFamily.mapSingletonFlattenIso.app
              ((coefficientLeafFamilyFunctor (profileLeafFamily A P.toColoredProfile)).obj
                (O.obj P.toColoredProfile))
                ≪≫
            profileOperationFactorsIso O A P.toColoredProfile)

/-- The original unit coefficient and the full original profile
tensor in the scalar left-unit branch frame. -/
def leftUnitScalarExpandedIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        (partitionedScalarLeaves (leftUnitCoefficientGrouping O P) (leftUnitLeafBlocks O A P)
          (substitutionBranchCoefficients O (ColoredSubstitutionData.leftUnit
            P.toColoredProfile))) ≅
      leftUnitExpandedFamily O A P :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option PUnit))
    (fun i => match i with
      | none => emptyLeafTensorIso (O.obj (ColoredSubstitutionData.unitProfile d))
      | some _ => profileCoefficientLeafTensorIso O A P.toColoredProfile)

/-- The scalar sparse insertion uses the original operad unary
coefficient map before the actual whole profile tensor. -/
def leftUnitSparseExpandedIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    sparseUnitScalarFamily (O.obj (ColoredSubstitutionData.unitProfile d))
        ((analyticSummand O A).obj P) ≅ leftUnitExpandedFamily O A P :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option PUnit)) (fun _ => Iso.refl _)

/-- The original coefficient-factor scalar map in the full left-unit partition. -/
def leftUnitPartitionActionMap (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :=
  partitionedCoefficientLeavesActionMap (leftUnitCoefficientGrouping O.toCollection P)
    (leftUnitLeafBlocks O.toCollection A P)
    (substitutionBranchCoefficients O.toCollection (ColoredSubstitutionData.leftUnit
      P.toColoredProfile))
    (leftUnitSourceCoefficientMap O P)

end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitRawBlockData

/- Source proof segment: LeftUnitRawBlockComparisons -/
section source_LeftUnitRawBlockComparisons
/-!
# Exact original left-unit sparse source and branch comparisons
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

omit [FiniteTensor C] in
/-- The original left partition source followed by its original
block collapse is precisely the sparse whole-profile insertion source. -/
theorem leftUnitRawBlocks_source (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (leftUnitPartitionSourceIso O A P).hom ≫
        (FiniteFamily.flatten (C := C)).map (leftUnitRawBlocksIso O A P).hom =
      (sparseUnitOriginalSourceIso ((analyticFactors O A).obj P)).hom := by
  apply FiniteFamily.Hom_ext
  · ext i
    cases i <;> rfl
  · intro i
    cases i with
    | none =>
      let X := O.obj P.toColoredProfile
      change HEq (𝟙 X ≫ 𝟙 X ≫ 𝟙 X ≫ 𝟙 X) (𝟙 X)
      exact heq_of_eq (by simp only [Category.id_comp])
    | some i =>
      let X := A (P.inputColor i)
      change HEq (𝟙 X ≫ 𝟙 X ≫ 𝟙 X ≫ 𝟙 X) (𝟙 X)
      exact heq_of_eq (by simp only [Category.id_comp])

/-- Each full original left-unit branch map is the original
sparse unit coefficient map after its exact original block collapse. -/
theorem leftUnitRawBlocks_action (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    leftUnitPartitionActionMap O A P ≫ (leftUnitScalarExpandedIso O.toCollection A P).hom =
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (leftUnitRawBlocksIso
        O.toCollection A P).hom ≫
        sparseUnitOriginalFactor (O.unit d) ((analyticFactors O.toCollection A).obj P) ≫
        (leftUnitSparseExpandedIso O.toCollection A P).hom := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      let η : (FiniteTensor.tensor (V := C)).obj (FiniteFamily.empty : FiniteFamily C) ⟶
        O.toCollection.obj (ColoredSubstitutionData.unitProfile d) := O.unit d
      have h := coefficientLeavesNormalization_empty_map (FiniteFamily.empty : FiniteFamily C) η
      have hg := leftUnitSourceCoefficientMap_none O P
      change HEq
        ((coefficientLeavesNormalization (FiniteFamily.empty : FiniteFamily C)
          (FiniteFamily.empty : FiniteFamily C) ≫
          (coefficientLeafTensorFunctor (FiniteFamily.empty : FiniteFamily C)).map
            (leftUnitSourceCoefficientMap O P none)) ≫
          (emptyLeafTensorIso (O.toCollection.obj (ColoredSubstitutionData.unitProfile d))).hom)
        ((FiniteTensor.tensor (V := C)).map (emptyLeafRawIso (FiniteFamily.empty :
          FiniteFamily C)).hom ≫ η ≫ 𝟙 _)
      rw [hg]
      exact heq_of_eq ((Category.assoc _ _ _).trans
        (h.trans (congrArg ((FiniteTensor.tensor (V := C)).map
          (emptyLeafRawIso (FiniteFamily.empty : FiniteFamily C)).hom ≫
            ·) (Category.comp_id η).symm)))
    | some i =>
      cases i
      let X := O.toCollection.obj P.toColoredProfile
      let L := profileLeafFamily A P.toColoredProfile
      let q := (profileOperationFactorsIso O.toCollection A P.toColoredProfile).hom
      let T := FiniteTensor.tensor (V := C)
      let k := (FiniteFamily.flatten (C := C)).map (singletonCoefficientLeavesIso X L).hom ≫
        FiniteFamily.mapSingletonFlattenIso.hom.app ((coefficientLeafFamilyFunctor L).obj X)
      let k₀ := (FiniteFamily.flatten (C := C)).map (singletonCoefficientLeavesIso X L).hom
      let k₁ := FiniteFamily.mapSingletonFlattenIso.hom.app ((coefficientLeafFamilyFunctor L).obj X)
      have h := coefficientLeavesNormalization_singleton X L
      change HEq
        ((coefficientLeavesNormalization ((FiniteFamily.singleton (C := C)).obj X) L ≫
          (coefficientLeafTensorFunctor L).map ((FiniteTensor.singletonIso (V :=
            C)).hom.app X)) ≫ T.map q)
        (T.map (k₀ ≫ k₁ ≫ q) ≫ 𝟙 _ ≫ 𝟙 _)
      have hmap : T.map k ≫ T.map q = T.map (k₀ ≫ k₁ ≫ q) :=
        (T.map_comp k q).symm.trans (congrArg T.map (Category.assoc k₀ k₁ q))
      exact heq_of_eq ((congrArg (· ≫ T.map q) h).trans
        (hmap.trans
          ((congrArg (T.map (k₀ ≫ k₁ ≫ q) ≫ ·) (Category.id_comp (𝟙 _))).trans
            (Category.comp_id _)).symm))

end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitRawBlockComparisons

/- Source proof segment: LeftUnitFrameData -/
section source_LeftUnitFrameData
/-!
# Actual original left-unit scalar frame and its generic source readback
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The full original scalar branch frame maps to the original
nested unit coefficient and original inner operation/input family. -/
def leftUnitOriginalScalarFrameIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    partitionedScalarLeaves (leftUnitCoefficientGrouping O P) (leftUnitLeafBlocks O A P)
        (substitutionBranchCoefficients O (ColoredSubstitutionData.leftUnit P.toColoredProfile)) ≅
      leftUnitNestedFactors O A P :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option PUnit))
    (fun i => match i with
      | none => emptyLeafFamilyIso (O.obj (ColoredSubstitutionData.unitProfile d))
      | some _ => profileOperationFactorsIso O A P.toColoredProfile)

omit [FiniteTensor C] in
/-- Original and generic left leaf blocks are equal at every actual
unary input slot, retaining the original profile family. -/
theorem leftUnitLeafBlocks_generic (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    leftUnitLeafBlocks O A P = substitutionBranchLeaves A (ColoredSubstitutionData.leftUnit
      P.toColoredProfile) := by
  funext i
  cases i with
  | none => rfl
  | some i => cases i; rfl

omit [FiniteTensor C] in
theorem leftUnitScalarFamily_generic (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    partitionedScalarLeaves (leftUnitCoefficientGrouping O P) (leftUnitLeafBlocks O A P)
        (substitutionBranchCoefficients O (ColoredSubstitutionData.leftUnit P.toColoredProfile)) =
      partitionedScalarLeaves
        (substitutionBranchGrouping (ColoredSubstitutionData.leftUnit P.toColoredProfile)
          (leftUnitSourceBlocks O P))
        (substitutionBranchLeaves A (ColoredSubstitutionData.leftUnit P.toColoredProfile))
        (substitutionBranchCoefficients O (ColoredSubstitutionData.leftUnit
          P.toColoredProfile)) := by
  rw [leftUnitLeafBlocks_generic]
  rfl

/-- The generic frame uses the same original scalar objects at
every root and original whole-profile branch slot. -/
def leftUnitGenericScalarIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    partitionedScalarLeaves (leftUnitCoefficientGrouping O P) (leftUnitLeafBlocks O A P)
        (substitutionBranchCoefficients O (ColoredSubstitutionData.leftUnit P.toColoredProfile)) ≅
      partitionedScalarLeaves
        (substitutionBranchGrouping (ColoredSubstitutionData.leftUnit P.toColoredProfile)
          (leftUnitSourceBlocks O P))
        (substitutionBranchLeaves A (ColoredSubstitutionData.leftUnit P.toColoredProfile))
        (substitutionBranchCoefficients O (ColoredSubstitutionData.leftUnit P.toColoredProfile)) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option PUnit))
    (fun i => match i with
      | none => Iso.refl _
      | some i => by cases i; exact Iso.refl _)

omit [FiniteTensor C] in
theorem leftUnitGenericScalar_factors (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (leftUnitGenericScalarIso O A P).hom ≫
        (substitutionFrameFactorsIso O A (ColoredSubstitutionData.leftUnit P.toColoredProfile)
          (leftUnitSourceBlocks O P)).hom = (leftUnitOriginalScalarFrameIso O A P).hom := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none => exact heq_of_eq (Category.id_comp _)
    | some i => cases i; exact heq_of_eq (Category.id_comp _)

/-- Identify the original generic left-unit coefficient-and-leaf blocks with the canonical
unit blocks. -/
def leftUnitGenericRawBlocksIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
        (partitionedCoefficientLeavesTriple (leftUnitCoefficientGrouping O P)
          (leftUnitLeafBlocks O A P)) ≅
      (FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
        (partitionedCoefficientLeavesTriple
          (substitutionBranchGrouping (ColoredSubstitutionData.leftUnit P.toColoredProfile)
            (leftUnitSourceBlocks O P))
          (substitutionBranchLeaves A (ColoredSubstitutionData.leftUnit P.toColoredProfile))) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option PUnit))
    (fun i => match i with
      | none => Iso.refl _
      | some i => by cases i; exact Iso.refl _)

theorem leftUnitPartitionAction_generic (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    leftUnitPartitionActionMap O A P ≫
        (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (leftUnitGenericScalarIso
          O.toCollection A P).hom =
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (leftUnitGenericRawBlocksIso
        O.toCollection A P).hom ≫
        partitionedCoefficientLeavesActionMap
        (substitutionBranchGrouping (ColoredSubstitutionData.leftUnit P.toColoredProfile)
          (leftUnitSourceBlocks O.toCollection P))
        (substitutionBranchLeaves A (ColoredSubstitutionData.leftUnit P.toColoredProfile))
        (substitutionBranchCoefficients O.toCollection (ColoredSubstitutionData.leftUnit
          P.toColoredProfile))
        (leftUnitSourceCoefficientMap O P) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      let f := (leftUnitPartitionActionMap O A P).hom none
      change HEq (f ≫ (FiniteTensor.tensor (V := C)).map (𝟙 _))
        ((FiniteTensor.tensor (V := C)).map (𝟙 _) ≫ f)
      exact heq_of_eq ((congrArg (f ≫ ·) ((FiniteTensor.tensor (V := C)).map_id _)).trans
        ((Category.comp_id f).trans
          ((congrArg (· ≫ f) ((FiniteTensor.tensor (V :=
            C)).map_id _)).trans (Category.id_comp f)).symm))
    | some i =>
      cases i
      let f := (leftUnitPartitionActionMap O A P).hom (some PUnit.unit)
      change HEq (f ≫ (FiniteTensor.tensor (V := C)).map (𝟙 _))
        ((FiniteTensor.tensor (V := C)).map (𝟙 _) ≫ f)
      exact heq_of_eq ((congrArg (f ≫ ·) ((FiniteTensor.tensor (V := C)).map_id _)).trans
        ((Category.comp_id f).trans
          ((congrArg (· ≫ f) ((FiniteTensor.tensor (V :=
            C)).map_id _)).trans (Category.id_comp f)).symm))

end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitFrameData

/- Source proof segment: LeftUnitFrameComparison -/
section source_LeftUnitFrameComparison
/-!
# Original left-unit scalar frame and original nested assembly
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original scalar branch maps followed by the original
coefficient singleton assembly give the original generic frame map. -/
theorem leftUnitScalarExpanded_factors (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (leftUnitScalarExpandedIso O A P).hom ≫ (leftUnitExpandedFactorsIso O A P).hom =
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).map
        (leftUnitOriginalScalarFrameIso O A P).hom := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      let X := O.obj (ColoredSubstitutionData.unitProfile d)
      let T := FiniteTensor.tensor (V := C)
      let a := T.map (emptyLeafFamilyIso X).hom
      let s := (FiniteTensor.singletonIso (V := C)).hom.app X
      let si := (FiniteTensor.singletonIso (V := C)).inv.app X
      change HEq ((a ≫ s) ≫ si) a
      exact heq_of_eq ((Category.assoc _ _ _).trans
        ((congrArg (a ≫ ·) ((FiniteTensor.singletonIso (V :=
          C)).hom_inv_id_app X)).trans (Category.comp_id a)))
    | some i =>
      let a := (FiniteTensor.tensor (V := C)).map (profileOperationFactorsIso O A
        P.toColoredProfile).hom
      change HEq (a ≫ 𝟙 _) a
      exact heq_of_eq (Category.comp_id a)

/-- The original expanded unary tensor followed by its original
nested assembly equals the actual generic scalar frame assembly. -/
theorem leftUnitScalarExpanded_assembly (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (FiniteTensor.tensor (V := C)).map (leftUnitScalarExpandedIso O A P).hom ≫
      (FiniteTensor.tensor (V := C)).map (leftUnitExpandedFactorsIso O A P).hom ≫
      (FiniteTensor.flattenIso (V := C)).inv.app (leftUnitNestedFactors O A P) =
    (FiniteTensor.flattenIso (V := C)).inv.app
        (partitionedScalarLeaves (leftUnitCoefficientGrouping O P) (leftUnitLeafBlocks O A P)
          (substitutionBranchCoefficients O (ColoredSubstitutionData.leftUnit
            P.toColoredProfile))) ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map (leftUnitOriginalScalarFrameIso O A P).hom) := by
  let T := FiniteTensor.tensor (V := C)
  let a := (leftUnitScalarExpandedIso O A P).hom
  let b := (leftUnitExpandedFactorsIso O A P).hom
  let f := (leftUnitOriginalScalarFrameIso O A P).hom
  let inv := (FiniteTensor.flattenIso (V := C)).inv.app (leftUnitNestedFactors O A P)
  have hmap : T.map a ≫ T.map b = T.map ((FiniteFamily.map T).map f) :=
    (T.map_comp a b).symm.trans (congrArg T.map (leftUnitScalarExpanded_factors O A P))
  have hn := (FiniteTensor.flattenIso (V := C)).inv.naturality f
  change T.map ((FiniteFamily.map T).map f) ≫ inv = _ at hn
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ inv) hmap).trans hn)

/-- The original sparse coefficient/unit factor is exactly the
original anonymous factor map used by leftUnitRawInsertion. -/
theorem leftUnitSparseFactor_original (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    sparseUnitFactor (O.unit d) ((analyticFactors O.toCollection A).obj P) ≫
      (leftUnitSparseExpandedIso O.toCollection A P).hom =
    ({ equiv := Equiv.refl (Option PUnit)
       hom i := match i with
         | none => O.unit d
         | some _ => (FiniteTensor.singletonIso (V := C)).hom.app
             ((analyticSummand O.toCollection A).obj P) } :
      UnitInsertion.leftTensorFamily ((analyticSummand O.toCollection A).obj P) ⟶
        leftUnitExpandedFamily O.toCollection A P) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none => exact heq_of_eq (Category.comp_id _)
    | some i => exact heq_of_eq (Category.comp_id _)

end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitFrameComparison

/- Source proof segment: LeftUnitGenericRouteComparison -/
section source_LeftUnitGenericRouteComparison
/-!
# Original left-unit partition route and the generic full source route
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

theorem leftUnitGenericRouteFromSquares {C : Type u} [Category.{v} C]
    {X A B D E P Y V : C} (a : X ⟶ A) (act : A ⟶ B) (c : B ⟶ D)
    (frame : B ⟶ P) (assembly : D ⟶ P) (op : P ⟶ Y)
    (raw : X ⟶ E) (n : E ⟶ V) (b : V ⟶ D) (k : A ⟶ D)
    (hframe : frame = c ≫ assembly) (hact : act ≫ c = k)
    (hn : raw ≫ n ≫ b = a ≫ k) :
    a ≫ act ≫ frame ≫ op = raw ≫ n ≫ b ≫ assembly ≫ op := by
  rw [hframe]
  simp only [Category.assoc]
  rw [← Category.assoc act c, hact, ← Category.assoc a k, ← hn]
  simp only [Category.assoc]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Assemble the original left-unit frame with the canonical tensor-flattening maps. -/
def leftUnitOriginalFrameAssembly (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :=
  (FiniteTensor.flattenIso (V := C)).inv.app
      (partitionedScalarLeaves (leftUnitCoefficientGrouping O P) (leftUnitLeafBlocks O A P)
        (substitutionBranchCoefficients O (ColoredSubstitutionData.leftUnit P.toColoredProfile))) ≫
    (FiniteTensor.tensor (V := C)).map
      ((FiniteFamily.flatten (C := C)).map (leftUnitOriginalScalarFrameIso O A P).hom)

theorem leftUnitOriginalFrameAssembly_generic (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    leftUnitOriginalFrameAssembly O A P =
      (FiniteTensor.tensor (V := C)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := C))).map (leftUnitGenericScalarIso O
            A P).hom) ≫
        (substitutionFrameAssemblyIso O A (ColoredSubstitutionData.leftUnit P.toColoredProfile)
          (leftUnitSourceBlocks O P)).hom := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let h := (leftUnitGenericScalarIso O A P).hom
  let g := (substitutionFrameFactorsIso O A (ColoredSubstitutionData.leftUnit P.toColoredProfile)
    (leftUnitSourceBlocks O P)).hom
  have hn := (FiniteTensor.flattenIso (V := C)).inv.naturality h
  have hc := congrArg F.map (leftUnitGenericScalar_factors O A P)
  have ht := T.map_comp (F.map h) (F.map g)
  rw [substitutionFrameAssemblyIso_hom]
  have hs := congrArg (· ≫ T.map (F.map g)) hn
  exact ((Category.assoc _ _ _).symm.trans hs).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) ht.symm).trans
        (congrArg (fun f => (FiniteTensor.flattenIso (V := C)).inv.app _ ≫ T.map f)
          ((F.map_comp h g).symm.trans hc)))) |>.symm

theorem leftUnitOriginalRoute_generic (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
          (partitionedCoefficientLeavesTriple (leftUnitCoefficientGrouping O.toCollection P)
            (leftUnitLeafBlocks O.toCollection A P))) ≫
      (FiniteTensor.tensor (V := C)).map (leftUnitPartitionActionMap O A P) ≫
      leftUnitOriginalFrameAssembly O.toCollection A P ≫
      operadSubstitutionInputs O A (ColoredSubstitutionData.leftUnit P.toColoredProfile) =
    (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map (leftUnitGenericRawBlocksIso O.toCollection A P).hom) ≫
      fullSubstitutionPartitionRoute O A (ColoredSubstitutionData.leftUnit P.toColoredProfile)
        (leftUnitSourceBlocks O.toCollection P) (leftUnitSourceCoefficientMap O P) := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let raw := (leftUnitGenericRawBlocksIso O.toCollection A P).hom
  let a := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.map F).obj
      (partitionedCoefficientLeavesTriple (leftUnitCoefficientGrouping O.toCollection P)
        (leftUnitLeafBlocks O.toCollection A P)))
  let act := T.map (leftUnitPartitionActionMap O A P)
  let c := T.map ((FiniteFamily.map T).map (leftUnitGenericScalarIso O.toCollection A P).hom)
  let frame := leftUnitOriginalFrameAssembly O.toCollection A P
  let assembly := (substitutionFrameAssemblyIso O.toCollection A
    (ColoredSubstitutionData.leftUnit P.toColoredProfile) (leftUnitSourceBlocks
      O.toCollection P)).hom
  let op := operadSubstitutionInputs O A (ColoredSubstitutionData.leftUnit P.toColoredProfile)
  let r := T.map (F.map raw)
  let n := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.map F).obj
      (partitionedCoefficientLeavesTriple
        (substitutionBranchGrouping (ColoredSubstitutionData.leftUnit P.toColoredProfile)
          (leftUnitSourceBlocks O.toCollection P))
        (substitutionBranchLeaves A (ColoredSubstitutionData.leftUnit P.toColoredProfile))))
  let k := T.map ((FiniteFamily.map T).map raw) ≫
    T.map (partitionedCoefficientLeavesActionMap
      (substitutionBranchGrouping (ColoredSubstitutionData.leftUnit P.toColoredProfile)
        (leftUnitSourceBlocks O.toCollection P))
      (substitutionBranchLeaves A (ColoredSubstitutionData.leftUnit P.toColoredProfile))
      (substitutionBranchCoefficients O.toCollection (ColoredSubstitutionData.leftUnit
        P.toColoredProfile))
      (leftUnitSourceCoefficientMap O P))
  have hn := (FiniteTensor.flattenIso (V := C)).hom.naturality raw
  have ha := congrArg T.map (leftUnitPartitionAction_generic O A P)
  have hact : act ≫ c = k :=
    (T.map_comp _ _).symm.trans (ha.trans (T.map_comp _ _))
  have hframe : frame = c ≫ assembly := leftUnitOriginalFrameAssembly_generic O.toCollection A P
  have hnat : r ≫ n = a ≫ T.map ((FiniteFamily.map T).map raw) := hn
  let b := T.map (partitionedCoefficientLeavesActionMap
    (substitutionBranchGrouping (ColoredSubstitutionData.leftUnit P.toColoredProfile)
      (leftUnitSourceBlocks O.toCollection P))
    (substitutionBranchLeaves A (ColoredSubstitutionData.leftUnit P.toColoredProfile))
    (substitutionBranchCoefficients O.toCollection (ColoredSubstitutionData.leftUnit
      P.toColoredProfile))
    (leftUnitSourceCoefficientMap O P))
  have hx : r ≫ n ≫ b = a ≫ k :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ b) hnat).trans (Category.assoc _ _ _))
  -- The paired source square is composed before any original op map.
  have h := leftUnitGenericRouteFromSquares a act c frame assembly op r n b k
    hframe hact hx
  exact h

end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitGenericRouteComparison

/- Source proof segment: LeftUnitRawPartition -/
section source_LeftUnitRawPartition
/-!
# Original left-unit raw insertion through its actual coefficient/leaf partition
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

theorem leftUnitRawPartitionFromSquares {C : Type u} [Category.{v} C]
    {X P Q R S A B D E Y : C}
    (src : X ⟶ P) (z : P ⟶ Q) (m : Q ⟶ R) (f : R ⟶ S)
    (t : S ⟶ A) (ex : A ⟶ B) (inv : B ⟶ Y)
    (source : X ⟶ Q) (a : P ⟶ D) (b : D ⟶ R)
    (action : D ⟶ E) (scalar : E ⟶ A) (assembly : E ⟶ Y)
    (hs : src ≫ z = source) (hn : z ≫ m = a ≫ b)
    (ha : action ≫ scalar = b ≫ f ≫ t) (he : scalar ≫ ex ≫ inv = assembly) :
    ((source ≫ m ≫ f) ≫ t) ≫ ex ≫ inv = src ≫ a ≫ action ≫ assembly := by
  simp only [Category.assoc]
  rw [← hs]
  simp only [Category.assoc]
  rw [← Category.assoc z m, hn]
  simp only [Category.assoc]
  have h := congrArg (fun q => src ≫ a ≫ q ≫ ex ≫ inv) ha.symm
  simp only [Category.assoc] at h
  rw [h, he]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original left-unit insertion before the whole profile
tensor is exactly the actual original coefficient/leaf branch action
and original scalar frame assembly. -/
theorem leftUnitRawInsertion_partition (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    leftUnitRawInsertion O A P =
      (FiniteTensor.tensor (V := C)).map (leftUnitPartitionSourceIso O.toCollection A P).hom ≫
        (FiniteTensor.flattenIso (V := C)).hom.app
          ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
            (partitionedCoefficientLeavesTriple (leftUnitCoefficientGrouping O.toCollection P)
              (leftUnitLeafBlocks O.toCollection A P))) ≫
        (FiniteTensor.tensor (V := C)).map (leftUnitPartitionActionMap O A P) ≫
        leftUnitOriginalFrameAssembly O.toCollection A P := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let L := (analyticFactors O.toCollection A).obj P
  let X := T.obj L
  let source := T.map (leftUnitPartitionSourceIso O.toCollection A P).hom
  let block := (leftUnitRawBlocksIso O.toCollection A P).hom
  let a := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.map F).obj
      (partitionedCoefficientLeavesTriple (leftUnitCoefficientGrouping O.toCollection P)
        (leftUnitLeafBlocks O.toCollection A P)))
  let z := T.map (F.map block)
  let m := (FiniteTensor.flattenIso (V := C)).hom.app (sparseUnitOriginalBlocks L)
  let b := T.map ((FiniteFamily.map T).map block)
  let f := T.map (sparseUnitOriginalFactor (O.unit d) L)
  let t := T.map (leftUnitSparseExpandedIso O.toCollection A P).hom
  let action := T.map (leftUnitPartitionActionMap O A P)
  let scalar := T.map (leftUnitScalarExpandedIso O.toCollection A P).hom
  let ex := T.map (leftUnitExpandedFactorsIso O.toCollection A P).hom
  let inv := (FiniteTensor.flattenIso (V := C)).inv.app (leftUnitNestedFactors O.toCollection A P)
  let assembly := leftUnitOriginalFrameAssembly O.toCollection A P
  let orig : UnitInsertion.leftTensorFamily ((analyticSummand O.toCollection A).obj P) ⟶
      leftUnitExpandedFamily O.toCollection A P :=
    { equiv := Equiv.refl (Option PUnit)
      hom i := match i with
        | none => O.unit d
        | some _ => (FiniteTensor.singletonIso (V := C)).hom.app ((analyticSummand
          O.toCollection A).obj P) }
  have hs : source ≫ z = T.map (sparseUnitOriginalSourceIso L).hom :=
    (T.map_comp _ _).symm.trans (congrArg T.map (leftUnitRawBlocks_source O.toCollection A P))
  have hn := (FiniteTensor.flattenIso (V := C)).hom.naturality block
  change z ≫ m = a ≫ b at hn
  have ha : action ≫ scalar = b ≫ f ≫ t := by
    let u := (FiniteFamily.map T).map block
    let v := sparseUnitOriginalFactor (O.unit d) L
    let w := (leftUnitSparseExpandedIso O.toCollection A P).hom
    have h := congrArg T.map (leftUnitRawBlocks_action O A P)
    exact (T.map_comp _ _).symm.trans
      (h.trans ((T.map_comp u (v ≫ w)).trans
        (congrArg (T.map u ≫ ·) (T.map_comp v w))))
  have hunit := sparseUnit_beforeTensor (O.unit d) L
  have hex : UnitInsertion.leftInsertFromFactor X (sparseUnitFactor (O.unit d) L) ≫ t =
      UnitInsertion.leftInsertFromFactor X orig :=
    (UnitInsertion.leftInsertFromFactor_comp X (sparseUnitFactor (O.unit d) L)
      (leftUnitSparseExpandedIso O.toCollection A P).hom).trans
      (congrArg (UnitInsertion.leftInsertFromFactor X) (leftUnitSparseFactor_original O A P))
  have hscalar : scalar ≫ ex ≫ inv = assembly := leftUnitScalarExpanded_assembly O.toCollection A P
  have hraw : leftUnitRawInsertion O A P =
      ((T.map (sparseUnitOriginalSourceIso L).hom ≫ m ≫ f) ≫ t) ≫ ex ≫ inv := by
    have h := (congrArg (· ≫ t) hunit).symm.trans hex
    have hd : leftUnitRawInsertion O A P =
        UnitInsertion.leftInsertFromFactor X orig ≫ ex ≫ inv := rfl
    exact hd.trans (congrArg (fun q => q ≫ ex ≫ inv) h).symm
  exact hraw.trans (leftUnitRawPartitionFromSquares source z m f t ex inv
    (T.map (sparseUnitOriginalSourceIso L).hom) a b action scalar assembly hs hn ha hscalar)



end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitRawPartition

/- Source proof segment: LeftUnitCoefficientLaw -/
section source_LeftUnitCoefficientLaw
/-!
# Original left-unit coefficient equation on its actual tensor source
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

theorem leftUnitExpansionFromFactorSquare {C : Type u} [Category.{v} C]
    {X A B D E F : C} (i : X ⟶ A) (a : A ⟶ B) (b : B ⟶ D)
    (k : D ⟶ E) (j : E ⟶ F) (g : D ⟶ F) (raw : X ⟶ F)
    {Y Z : C} (γ : F ⟶ Y) (h : Y ⟶ Z)
    (hf : k ≫ j = g) (hr : raw = (i ≫ a ≫ b) ≫ g) :
    i ≫ a ≫ b ≫ k ≫ j ≫ γ ≫ h = raw ≫ γ ≫ h := by
  rw [← Category.assoc k j, hf, hr]
  simp only [Category.assoc]

theorem leftUnitReassociateCoefficient {C : Type u} [Category.{v} C]
    {X A B D E F G : C} (a : X ⟶ A) (b : A ⟶ B) (c : B ⟶ D)
    (d : D ⟶ E) (e : E ⟶ F) (f : F ⟶ G) :
    a ≫ (b ≫ c ≫ (d ≫ e)) ≫ f = a ≫ b ≫ c ≫ d ≫ e ≫ f := by
  simp only [Category.assoc]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

omit [FiniteTensor C] in
theorem leftUnitCoefficientSourceIso_inv (O : ColoredSymmetricCollection W C) {d : W}
    (P : AnalyticIndex W d) :
    (leftUnitCoefficientSourceIso O P).inv = UnitInsertion.leftSingletonToFlatten (O.obj
      P.toColoredProfile) := by
  apply FiniteFamily.Hom_ext
  · ext i
    cases i
    rfl
  · intro i
    cases i
    change HEq (𝟙 (O.obj P.toColoredProfile) ≫ 𝟙 _) (𝟙 (O.obj P.toColoredProfile))
    exact heq_of_eq (Category.id_comp _)

theorem leftUnitSourceCoefficientFactors (O : ColoredOperadObj W C) {d : W} (P :
  AnalyticIndex W d) :
    partitionedCoefficientMap (leftUnitCoefficientGrouping O.toCollection P)
        (substitutionBranchCoefficients O.toCollection (ColoredSubstitutionData.leftUnit
          P.toColoredProfile))
        (leftUnitSourceCoefficientMap O P) ≫
      (substitutionFrameCoefficientsIso O.toCollection (ColoredSubstitutionData.leftUnit
        P.toColoredProfile)
        (leftUnitSourceBlocks O.toCollection P)).hom =
      leftUnitCoefficientFactorMap O P := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    let g := leftUnitSourceCoefficientMap O P i
    change HEq (g ≫ 𝟙 _) g
    exact heq_of_eq (Category.comp_id g)

/-- The original left-unit coefficient route on the singleton
coefficient source is exactly its original singleton tensor unitor. -/
theorem leftUnitCanonicalCoefficient (O : ColoredOperadObj W C) {d : W} (P : AnalyticIndex W d) :
    canonicalSubstitutionCoefficient O (ColoredSubstitutionData.leftUnit P.toColoredProfile)
        (leftUnitSourceBlocks O.toCollection P) (leftUnitSourceCoefficientMap O P)
        (leftUnitCoefficientSourceIso O.toCollection P)
        (ColoredSubstitutionData.leftUnitTotalHom P.toColoredProfile) =
      (FiniteTensor.singletonIso (V := C)).hom.app (O.toCollection.obj P.toColoredProfile) := by
  let T := FiniteTensor.tensor (V := C)
  let X := O.toCollection.obj P.toColoredProfile
  let N := leftUnitCoefficientGrouping O.toCollection P
  let k := partitionedCoefficientMap N
    (substitutionBranchCoefficients O.toCollection (ColoredSubstitutionData.leftUnit
      P.toColoredProfile))
    (leftUnitSourceCoefficientMap O P)
  let j := (substitutionFrameCoefficientsIso O.toCollection
    (ColoredSubstitutionData.leftUnit P.toColoredProfile)
    (leftUnitSourceBlocks O.toCollection P)).hom
  let coeff := canonicalSubstitutionCoefficient O (ColoredSubstitutionData.leftUnit
    P.toColoredProfile)
    (leftUnitSourceBlocks O.toCollection P) (leftUnitSourceCoefficientMap O P)
    (leftUnitCoefficientSourceIso O.toCollection P)
      (ColoredSubstitutionData.leftUnitTotalHom P.toColoredProfile)
  let i := (FiniteTensor.singletonIso (V := C)).inv.app X
  let a := T.map (UnitInsertion.leftSingletonToFlatten X)
  let b := (FiniteTensor.flattenIso (V := C)).hom.app N
  let g := T.map (leftUnitCoefficientFactorMap O P)
  let γ := O.subst.app (ColoredSubstitutionData.leftUnit P.toColoredProfile)
  let h := O.toCollection.map (ColoredSubstitutionData.leftUnitTotalHom P.toColoredProfile)
  let raw := ColoredOperadObj.leftUnitInsert O.toCollection O.unit P.toColoredProfile
  have hf : T.map k ≫ T.map j = g :=
    (T.map_comp _ _).symm.trans (congrArg T.map (leftUnitSourceCoefficientFactors O P))
  have hunit := O.left_unit P.toColoredProfile
  have hr : raw = (i ≫ a ≫ b) ≫ g := rfl
  have hcoeff : coeff = T.map (leftUnitCoefficientSourceIso O.toCollection P).inv ≫
      b ≫ T.map k ≫ T.map j ≫ γ ≫ h :=
    leftUnitReassociateCoefficient (T.map (leftUnitCoefficientSourceIso O.toCollection P).inv)
      b (T.map k) (T.map j) γ h
  have hc : i ≫ coeff = 𝟙 X := by
    have hinv := leftUnitCoefficientSourceIso_inv O.toCollection P
    have h1 := congrArg (i ≫ ·) hcoeff
    rw [hinv] at h1
    exact h1.trans
      ((leftUnitExpansionFromFactorSquare i a b (T.map k) (T.map j) g raw γ h hf hr).trans hunit)
  let s : T.obj ((FiniteFamily.singleton (C := C)).obj X) ⟶ X :=
    (FiniteTensor.singletonIso (V := C)).hom.app X
  have hs : i ≫ s = 𝟙 X := (FiniteTensor.singletonIso (V := C)).inv_hom_id_app X
  have hp : coeff = s := by
    apply (cancel_epi i).1
    exact hc.trans hs.symm
  exact hp



end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitCoefficientLaw

/- Source proof segment: LeftUnitLeafData -/
section source_LeftUnitLeafData
@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

/-- Identify the original left-unit partitioned leaf indices with the substitution
total-profile inputs. -/
def leftUnitOriginalLeafEquiv (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (partitionedLeafFamily (leftUnitCoefficientGrouping O P) (leftUnitLeafBlocks O A P)).index ≃
      (profileLeafFamily A (ColoredSubstitutionData.leftUnit
        P.toColoredProfile).totalProfile).index where
  toFun p := match p with
    | ⟨none, e⟩ => e.elim
    | ⟨some i, p⟩ => ⟨i, p⟩
  invFun p := ⟨some p.1, p.2⟩
  left_inv p := by
    rcases p with ⟨i, p⟩
    cases i with
    | none => cases p
    | some i => cases i; rfl
  right_inv p := by rcases p with ⟨i, p⟩; cases i; rfl

/-- Identify the original left-unit partitioned leaves with the substitution total-profile
leaf family. -/
def leftUnitOriginalLeafIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    partitionedLeafFamily (leftUnitCoefficientGrouping O P) (leftUnitLeafBlocks O A P) ≅
      profileLeafFamily A (ColoredSubstitutionData.leftUnit P.toColoredProfile).totalProfile :=
  FiniteFamily.isoOfReindex (leftUnitOriginalLeafEquiv O A P)
    (fun p => by
      rcases p with ⟨i, p⟩
      cases i with
      | none => cases p
      | some i => cases i; rfl)

/-- Identify the original left-unit partitioned leaves with the unchanged input-profile leaf
family. -/
def leftUnitOriginalTotalLeafIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    partitionedLeafFamily (leftUnitCoefficientGrouping O P) (leftUnitLeafBlocks O A P) ≅
      profileLeafFamily A P.toColoredProfile :=
  leftUnitOriginalLeafIso O A P ≪≫ profileLeafIso A
    (ColoredSubstitutionData.leftUnitTotalHom P.toColoredProfile)

end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitLeafData

/- Source proof segment: LeftUnitOriginalSource -/
section source_LeftUnitOriginalSource
/-!
# Original left-unit coefficient and leaf source permutation collapse
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

omit [FiniteTensor C] in
/-- The actual common-source isomorphism followed by singleton
coefficient/leaf collapse retains every original coefficient and
every original input map, yielding the original profile factor identity. -/
theorem leftUnitOriginalSource (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (leftUnitPartitionSourceIso O A P).hom ≫
      (partitionedCoefficientLeavesSourceIso (leftUnitCoefficientGrouping O P)
        (leftUnitLeafBlocks O A P)).hom ≫
      (coefficientLeavesRawIso (leftUnitCoefficientSourceIso O P)
        (leftUnitOriginalTotalLeafIso O A P)).hom ≫
      (FiniteFamily.flatten (C := C)).map
        (singletonCoefficientLeavesIso (O.obj P.toColoredProfile) (profileLeafFamily A
          P.toColoredProfile)).hom ≫
      FiniteFamily.mapSingletonFlattenIso.hom.app
        ((coefficientLeafFamilyFunctor (profileLeafFamily A P.toColoredProfile)).obj (O.obj
          P.toColoredProfile)) ≫
      (profileOperationFactorsIso O A P.toColoredProfile).hom =
        𝟙 ((analyticFactors O A).obj P) := by
  apply FiniteFamily.Hom_ext
  · ext i
    cases i <;> rfl
  · intro i
    cases i with
    | none =>
      let X := O.obj P.toColoredProfile
      change HEq (𝟙 X ≫ 𝟙 X ≫ 𝟙 X ≫ 𝟙 X ≫ 𝟙 X ≫ 𝟙 X) (𝟙 X)
      exact heq_of_eq (by simp only [Category.id_comp])
    | some i =>
      let X := A (P.inputColor i)
      change HEq (𝟙 X ≫ 𝟙 X ≫ (𝟙 X ≫ 𝟙 X) ≫ 𝟙 X ≫ 𝟙 X ≫ 𝟙 X) (𝟙 X)
      exact heq_of_eq (by simp only [Category.id_comp])

end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitOriginalSource

/- Source proof segment: LeftUnitCanonicalSourceComparison -/
section source_LeftUnitCanonicalSourceComparison
/-!
# Original and generic left-unit common coefficient/leaf source maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Identify the original left-unit tensor source with its canonical coefficient-and-profile
tensor. -/
def leftUnitOriginalCanonicalSourceIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.flatten (C := C)).obj
          ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
            (partitionedCoefficientLeavesTriple (leftUnitCoefficientGrouping O P)
              (leftUnitLeafBlocks O A P)))) ≅
      (FiniteTensor.tensor (V := C)).obj
        ((FiniteFamily.flatten (C := C)).obj
          (coefficientLeavesNested ((FiniteFamily.singleton (C :=
            C)).obj (O.obj P.toColoredProfile))
            (profileLeafFamily A P.toColoredProfile))) :=
  (FiniteTensor.tensor (V := C)).mapIso
    (partitionedCoefficientLeavesSourceIso (leftUnitCoefficientGrouping O P)
      (leftUnitLeafBlocks O A P) ≪≫
      coefficientLeavesRawIso (leftUnitCoefficientSourceIso O P)
        (leftUnitOriginalTotalLeafIso O A P))

omit [FiniteTensor C] in
/-- The original raw partition isomorphism followed by the generic
common-source isomorphism is exactly the original coefficient/leaf
permutation on every original input position. -/
theorem leftUnitCanonicalSource_map (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (FiniteFamily.flatten (C := C)).map (leftUnitGenericRawBlocksIso O A P).hom ≫
      (partitionedCoefficientLeavesSourceIso
        (substitutionBranchGrouping (ColoredSubstitutionData.leftUnit P.toColoredProfile)
          (leftUnitSourceBlocks O P))
        (substitutionBranchLeaves A (ColoredSubstitutionData.leftUnit P.toColoredProfile))).hom ≫
      (coefficientLeavesRawIso (leftUnitCoefficientSourceIso O P)
        (substitutionFrameLeafIso A (ColoredSubstitutionData.leftUnit P.toColoredProfile)
          (leftUnitSourceBlocks O P) ≪≫
          profileLeafIso A (ColoredSubstitutionData.leftUnitTotalHom P.toColoredProfile))).hom =
    (partitionedCoefficientLeavesSourceIso (leftUnitCoefficientGrouping O P)
      (leftUnitLeafBlocks O A P)).hom ≫
      (coefficientLeavesRawIso (leftUnitCoefficientSourceIso O P)
        (leftUnitOriginalTotalLeafIso O A P)).hom := by
  apply FiniteFamily.Hom_ext
  · ext p
    rcases p with ⟨o, ⟨l, k⟩⟩
    cases o with
    | none => cases l with
      | none => cases k
      | some l => cases l
    | some o =>
      cases o
      cases l with
      | none => cases k; rfl
      | some l => cases k; rfl
  · intro p
    rcases p with ⟨o, ⟨l, k⟩⟩
    cases o with
    | none => cases l with
      | none => cases k
      | some l => cases l
    | some o =>
      cases o
      cases l with
      | none =>
        cases k
        let X := O.obj P.toColoredProfile
        change HEq (𝟙 X ≫ 𝟙 X ≫ 𝟙 X) (𝟙 X ≫ 𝟙 X)
        exact heq_of_eq (by simp only [Category.id_comp])
      | some l =>
        cases k
        let X := A (P.inputColor l)
        change HEq (𝟙 X ≫ 𝟙 X ≫ (𝟙 X ≫ 𝟙 X)) (𝟙 X ≫ (𝟙 X ≫ 𝟙 X))
        exact heq_of_eq (by simp only [Category.id_comp])

theorem leftUnitCanonicalSource_tensor (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map (leftUnitGenericRawBlocksIso O A P).hom) ≫
      (substitutionCanonicalSourceIso A (ColoredSubstitutionData.leftUnit P.toColoredProfile)
        (leftUnitSourceBlocks O P) (leftUnitCoefficientSourceIso O P)
        (ColoredSubstitutionData.leftUnitTotalHom P.toColoredProfile)).hom =
    (leftUnitOriginalCanonicalSourceIso O A P).hom := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let r := F.map (leftUnitGenericRawBlocksIso O A P).hom
  let b := (partitionedCoefficientLeavesSourceIso
    (substitutionBranchGrouping (ColoredSubstitutionData.leftUnit P.toColoredProfile)
      (leftUnitSourceBlocks O P))
    (substitutionBranchLeaves A (ColoredSubstitutionData.leftUnit P.toColoredProfile))).hom
  let j := (coefficientLeavesRawIso (leftUnitCoefficientSourceIso O P)
    (substitutionFrameLeafIso A (ColoredSubstitutionData.leftUnit P.toColoredProfile)
      (leftUnitSourceBlocks O P) ≪≫
      profileLeafIso A (ColoredSubstitutionData.leftUnitTotalHom P.toColoredProfile))).hom
  let b' := (partitionedCoefficientLeavesSourceIso (leftUnitCoefficientGrouping O P)
    (leftUnitLeafBlocks O A P)).hom
  let j' := (coefficientLeavesRawIso (leftUnitCoefficientSourceIso O P)
    (leftUnitOriginalTotalLeafIso O A P)).hom
  have h : r ≫ b ≫ j = b' ≫ j' := leftUnitCanonicalSource_map O A P
  change T.map r ≫ T.map (b ≫ j) = T.map (b' ≫ j')
  exact (T.map_comp r (b ≫ j)).symm.trans (congrArg T.map h)

end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitCanonicalSourceComparison

/- Source proof segment: LeftUnitFinalSquares -/
section source_LeftUnitFinalSquares
@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe u v

theorem leftUnitOriginalRouteFromSourceIso {C : Type u} [Category.{v} C]
    {X R S P Y : C} (source : X ⟶ R) (raw : R ⟶ P) (map : P ⟶ Y)
    (rg : R ⟶ S) (f : S ⟶ P) (raw' : X ⟶ P)
    (hr : raw' = source ≫ raw) (hg : raw = rg ≫ f) :
    raw' ≫ map = source ≫ rg ≫ f ≫ map := by
  rw [hr, hg]
  simp only [Category.assoc]

theorem leftUnitRawCompositeFromSquares {C : Type u} [Category.{v} C]
    {X R A B S P Y : C} (raw : X ⟶ P) (op : P ⟶ Y)
    (source : X ⟶ R) (a : R ⟶ A) (b : A ⟶ B) (frame : B ⟶ P)
    (rg : R ⟶ S) (f : S ⟶ Y)
    {Z : C} (map : Y ⟶ Z)
    (hr : raw = source ≫ a ≫ b ≫ frame) (hg : a ≫ b ≫ frame ≫ op = rg ≫ f) :
    raw ≫ op ≫ map = source ≫ rg ≫ f ≫ map := by
  rw [hr]
  simp only [Category.assoc]
  have h := congrArg (fun f => source ≫ f ≫ map) hg
  simp only [Category.assoc] at h
  exact h

theorem leftUnitFinalFromSquares {C : Type u} [Category.{v} C]
    {X R S P A B D : C} (raw : X ⟶ P) (map : P ⟶ X)
    (source : X ⟶ R) (rg : R ⟶ S) (f : S ⟶ P)
    (eg : S ≅ A) (e : R ≅ A) (route : A ⟶ X)
    (n : A ⟶ B) (c : B ⟶ D) (target : D ⟶ X) (collapse : A ⟶ D)
    (hr : raw ≫ map = source ≫ rg ≫ f ≫ map)
    (he : rg ≫ eg.hom = e.hom) (hroute : route = eg.inv ≫ f ≫ map)
    (hc : route = n ≫ c ≫ target) (hn : n ≫ c = collapse)
    (hs : source ≫ e.hom ≫ collapse ≫ target = 𝟙 X) :
    raw ≫ map = 𝟙 X := by
  have hi : source ≫ rg ≫ f ≫ map = source ≫ e.hom ≫ route := by
    rw [hroute, ← he]
    simp only [Category.assoc]
    rw [← Category.assoc eg.hom eg.inv, eg.hom_inv_id, Category.id_comp]
  rw [hr, hi, hc]
  rw [← Category.assoc n c, hn, hs]

end CategoryTheory.Operad.Tensor
end
end source_LeftUnitFinalSquares

/- Source proof segment: LeftUnitGeometryProof -/
section source_LeftUnitGeometryProof
/-!
# Full original left-unit tensor-operadic geometry
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The exact original left-unit insertion/substitution/total-map
composite is the identity on every original weighted profile tensor.
It is derived from O.left_unit and actual finite tensor coherence. -/
theorem leftUnitRawInsertion_geometry (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    leftUnitRawInsertion O A P ≫
      operadSubstitutionInputs O A
        (tupleSubstitutionShape (AnalyticIndex.unary (d := d) d) (leftUnitProfileTuple P)) ≫
      (operationSummandFunctor O.toCollection A).map
        (ColoredSubstitutionData.leftUnitTotalHom P.toColoredProfile) =
      𝟙 ((analyticSummand O.toCollection A).obj P) := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let s := ColoredSubstitutionData.leftUnit P.toColoredProfile
  let K := leftUnitSourceBlocks O.toCollection P
  let g := leftUnitSourceCoefficientMap O P
  let Z := (FiniteFamily.singleton (C := C)).obj (O.toCollection.obj P.toColoredProfile)
  let L := profileLeafFamily A P.toColoredProfile
  let k := leftUnitCoefficientSourceIso O.toCollection P
  let f := ColoredSubstitutionData.leftUnitTotalHom P.toColoredProfile
  let source := T.map (leftUnitPartitionSourceIso O.toCollection A P).hom
  let e := leftUnitOriginalCanonicalSourceIso O.toCollection A P
  let eg := substitutionCanonicalSourceIso A s K k f
  let rg := T.map ((F.map (leftUnitGenericRawBlocksIso O.toCollection A P).hom))
  let raw := fullSubstitutionPartitionRoute O A s K g
  let smap := (operationSummandFunctor O.toCollection A).map f
  let route := canonicalSubstitutionRoute O A s K g k f
  let n := coefficientLeavesNormalization Z L
  let c := (coefficientLeafTensorFunctor L).map
    ((FiniteTensor.singletonIso (V := C)).hom.app (O.toCollection.obj P.toColoredProfile))
  let target := (profileCoefficientLeafTensorIso O.toCollection A P.toColoredProfile).hom
  have hc : route = n ≫ c ≫ target := by
    have h := canonicalSubstitutionRoute_factorization O A s K g k f
    rw [leftUnitCanonicalCoefficient] at h
    exact h
  have hr : leftUnitRawInsertion O A P ≫ operadSubstitutionInputs O A s ≫ smap = source
    ≫ rg ≫ raw ≫ smap := by
    have h := leftUnitRawInsertion_partition O A P
    have hgeneric := leftUnitOriginalRoute_generic O A P
    let a := (FiniteTensor.flattenIso (V := C)).hom.app
      ((FiniteFamily.map F).obj
        (partitionedCoefficientLeavesTriple (leftUnitCoefficientGrouping O.toCollection P)
          (leftUnitLeafBlocks O.toCollection A P)))
    let b := T.map (leftUnitPartitionActionMap O A P)
    let frame := leftUnitOriginalFrameAssembly O.toCollection A P
    let op := operadSubstitutionInputs O A s
    exact leftUnitRawCompositeFromSquares (leftUnitRawInsertion O A P) op source a b frame
      rg raw smap h hgeneric
  have he : rg ≫ eg.hom = e.hom := leftUnitCanonicalSource_tensor O.toCollection A P
  have hnorm := coefficientLeavesNormalization_singleton (O.toCollection.obj P.toColoredProfile) L
  let collapse := F.map (singletonCoefficientLeavesIso (O.toCollection.obj
    P.toColoredProfile) L).hom ≫
    FiniteFamily.mapSingletonFlattenIso.hom.app
      ((coefficientLeafFamilyFunctor L).obj (O.toCollection.obj P.toColoredProfile))
  have hcollapse : n ≫ c = T.map collapse := hnorm
  have hsource : source ≫ e.hom ≫ T.map collapse ≫ target = 𝟙 _ := by
    have h := congrArg T.map (leftUnitOriginalSource O.toCollection A P)
    let a := (leftUnitPartitionSourceIso O.toCollection A P).hom
    let b := (partitionedCoefficientLeavesSourceIso (leftUnitCoefficientGrouping O.toCollection P)
      (leftUnitLeafBlocks O.toCollection A P)).hom
    let j := (coefficientLeavesRawIso k (leftUnitOriginalTotalLeafIso O.toCollection A P)).hom
    let q := (profileOperationFactorsIso O.toCollection A P.toColoredProfile).hom
    have hm : T.map (a ≫ b ≫ j ≫ collapse ≫ q) =
      source ≫ e.hom ≫ T.map collapse ≫ target := by
      have h1 := T.map_comp a (b ≫ j ≫ collapse ≫ q)
      have h2 := T.map_comp (b ≫ j) (collapse ≫ q)
      have h3 := T.map_comp collapse q
      have ha : T.map (a ≫ b ≫ j ≫ collapse ≫ q) = T.map a ≫ T.map (b ≫ j) ≫
        T.map collapse ≫ T.map q := by
        exact h1.trans (congrArg (T.map a ≫ ·)
          ((congrArg T.map (Category.assoc b j (collapse ≫ q)).symm).trans
            (h2.trans (congrArg (T.map (b ≫ j) ≫ ·) h3))))
      exact ha
    let k₀ := F.map (singletonCoefficientLeavesIso (O.toCollection.obj P.toColoredProfile) L).hom
    let k₁ := FiniteFamily.mapSingletonFlattenIso.hom.app
      ((coefficientLeafFamilyFunctor L).obj (O.toCollection.obj P.toColoredProfile))
    have hg : a ≫ b ≫ j ≫ collapse ≫ q = a ≫ b ≫ j ≫ k₀ ≫ k₁ ≫ q :=
      congrArg (fun m => a ≫ b ≫ j ≫ m) (Category.assoc k₀ k₁ q)
    have ht : T.map (a ≫ b ≫ j ≫ collapse ≫ q) = 𝟙 _ :=
      (congrArg T.map hg).trans (h.trans (T.map_id _))
    exact hm.symm.trans ht
  let rawOp := leftUnitRawInsertion O A P ≫ operadSubstitutionInputs O A s
  have hassoc : rawOp ≫ smap = leftUnitRawInsertion O A P ≫ operadSubstitutionInputs O A s ≫ smap :=
    Category.assoc (leftUnitRawInsertion O A P) (operadSubstitutionInputs O A s) smap
  have hrr : rawOp ≫ smap = source ≫ rg ≫ raw ≫ smap := hassoc.trans hr
  have hroute : route = eg.inv ≫ raw ≫ smap := rfl
  exact hassoc.symm.trans
    (leftUnitFinalFromSquares rawOp smap source rg raw eg e route n c target (T.map collapse)
      hrr he hroute hc hcollapse hsource)



end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitGeometryProof

/- Source proof segment: LeftUnitMonadLaw -/
section source_LeftUnitMonadLaw
/-!
# Actual tensor-profile monad left-unit law
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem leftUnitDescent {V : Type*} [Category* V]
    {X T S R Z Y U : V} (i : X ⟶ T) (unit : T ⟶ S) (j : S ⟶ U) (μ : U ⟶ T)
    (a : X ⟶ R) (slot : R ⟶ S) (assembly : R ⟶ Z) (op : Z ⟶ Y)
    (ι : Y ⟶ T) (total : Y ⟶ X) (raw : X ⟶ Z)
    (hi : i ≫ unit = a ≫ slot) (hβ : slot ≫ j ≫ μ = assembly ≫ op ≫ ι)
    (ha : a ≫ assembly = raw) (hι : total ≫ i = ι) (hu : raw ≫ op ≫ total = 𝟙 X) :
    i ≫ (unit ≫ j ≫ μ) = i := by
  rw [← Category.assoc i unit, hi]
  simp only [Category.assoc]
  rw [hβ, ← Category.assoc a assembly, ha, ← hι]
  have h := congrArg (· ≫ i) hu
  simpa only [Category.assoc, Category.id_comp] using h

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- The actual original unary operadic unit at the profile
coinvariants followed by the constructed multiplication is identity. -/
theorem profileMultiplication_left_unit (O : ColoredOperadObj W C) (A : W → C) :
    (profileUnit O).app (profileCoinvariants O.toCollection A) ≫ profileMultiplication O A =
      𝟙 (profileCoinvariants O.toCollection A) := by
  funext d
  apply colimit.hom_ext
  intro P
  let i := profileι O.toCollection A P
  let unit := unitInsertion O (profileCoinvariants O.toCollection A) d
  let j := profileι O.toCollection (profileCoinvariants O.toCollection A)
    (AnalyticIndex.unary (d := d) d)
  let μ := profileMultiplication O A d
  let a := (unaryTensorUnit O d).app ((analyticSummand O.toCollection A).obj P) ≫
    (leftUnitSlotTensorIso O.toCollection A P).hom
  let slot := (profileSlotTensorCocone O.toCollection A (AnalyticIndex.unary (d :=
    d) d)).ι.app (leftUnitSlotTuple P)
  let assembly := profileSubstitutionAssemblyMap O.toCollection A (AnalyticIndex.unary (d :=
    d) d) (leftUnitSlotTuple P)
  let op := operadSubstitutionInputs O A
    (tupleSubstitutionShape (AnalyticIndex.unary (d := d) d) (leftUnitProfileTuple P))
  let ι := profileι O.toCollection A ((tupleTotalFunctor (AnalyticIndex.unary (d :=
    d) d)).obj (leftUnitProfileTuple P))
  let total := (operationSummandFunctor O.toCollection A).map
    (ColoredSubstitutionData.leftUnitTotalHom P.toColoredProfile)
  have hi : i ≫ unit = a ≫ slot := (profileι_unary_unit O A P).trans (Category.assoc _ _ _).symm
  have hβ : slot ≫ j ≫ μ = assembly ≫ op ≫ ι := profileMultiplication_left_unit_slot O A P
  have ha : a ≫ assembly = leftUnitRawInsertion O A P :=
    (Category.assoc _ _ _).trans (leftUnitTupleAssembly O A P)
  have hι : total ≫ i = ι := by
    have h := profile_relabel_ι O.toCollection A (leftUnitTupleTotalHom P)
    have hm := operationFactorsFunctor_map_restrict O.toCollection A (leftUnitTupleTotalHom P)
    exact (congrArg (· ≫ i) (congrArg (FiniteTensor.tensor (V := C)).map hm)).trans h
  change i ≫ ((unit ≫ j) ≫ μ) = i ≫ 𝟙 _
  exact (congrArg (i ≫ ·) (Category.assoc _ _ _)).trans
    ((leftUnitDescent i unit j μ a slot assembly op ι total (leftUnitRawInsertion O A P)
      hi hβ ha hι (leftUnitRawInsertion_geometry O A P)).trans (Category.comp_id _).symm)



end CategoryTheory.Operad.Tensor
end
end
end source_LeftUnitMonadLaw

/- Source proof segment: SingletonBranchAssembly -/
section source_SingletonBranchAssembly
/-!
# Original singleton branch assembly

Mapping every original input into an original branch family and then
flattening the branch tensor agrees with the source map-singleton
flatten identification. This is a direct finite-tensor coherence
construction, with the actual finite indices and maps retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- Original component singleton maps into each retained branch. -/
def singletonBranchFamilyMap (X : FiniteFamily C) (N : FiniteFamily (FiniteFamily C))
    (e : X.index ≃ N.index)
    (f : ∀ i, (FiniteFamily.singleton (C := C)).obj (X.obj i) ⟶ N.obj (e i)) :
    (FiniteFamily.map (FiniteFamily.singleton (C := C))).obj X ⟶ N where
  equiv := e
  hom := f

/-- The source singleton-input maps are the actual tensor maps
obtained from singleton inversion followed by the original branch
component map. -/
def singletonBranchTensorMap (X : FiniteFamily C) (N : FiniteFamily (FiniteFamily C))
    (e : X.index ≃ N.index)
    (f : ∀ i, (FiniteFamily.singleton (C := C)).obj (X.obj i) ⟶ N.obj (e i)) :
    X ⟶ (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj N where
  equiv := e
  hom i := (FiniteTensor.singletonIso (V := C)).inv.app (X.obj i) ≫
    (FiniteTensor.tensor (V := C)).map (f i)

/-- The source tensor singleton-flatten coherence gives the
complete branchwise input assembly equation with all original maps. -/
theorem singletonBranchAssembly (X : FiniteFamily C) (N : FiniteFamily (FiniteFamily C))
    (e : X.index ≃ N.index)
    (f : ∀ i, (FiniteFamily.singleton (C := C)).obj (X.obj i) ⟶ N.obj (e i)) :
    (FiniteTensor.tensor (V := C)).map (singletonBranchTensorMap X N e f) =
      (FiniteTensor.tensor (V := C)).map
        (FiniteFamily.mapSingletonFlattenIso.inv.app X ≫
          (FiniteFamily.flatten (C := C)).map (singletonBranchFamilyMap X N e f)) ≫
      (FiniteTensor.flattenIso (V := C)).hom.app N := by
  let M := (FiniteFamily.map (FiniteFamily.singleton (C := C))).obj X
  let k := singletonBranchFamilyMap X N e f
  let c := (FiniteFamily.mapIso (FiniteTensor.singletonIso (V := C))).hom.app X
  let ci := (FiniteFamily.mapIso (FiniteTensor.singletonIso (V := C))).inv.app X
  let a := (FiniteTensor.flattenIso (V := C)).hom.app M
  have hunit := CategoryTheory.mapSingletonFlattenLaw_app X
  have hn := (FiniteTensor.flattenIso (V := C)).hom.naturality k
  have hf : ci ≫ (FiniteFamily.map FiniteTensor.tensor).map k =
    singletonBranchTensorMap X N e f := by
    apply FiniteFamily.Hom_ext
    · rfl
    · intro i
      exact HEq.rfl
  have hu : (FiniteTensor.tensor (V := C)).map (FiniteFamily.mapSingletonFlattenIso.inv.app X) ≫ a =
      (FiniteTensor.tensor (V := C)).map ci := by
    apply (cancel_mono ((FiniteTensor.tensor (V := C)).map c)).1
    have h := congrArg ((FiniteTensor.tensor (V := C)).map
      (FiniteFamily.mapSingletonFlattenIso.inv.app X) ≫ ·) hunit
    have hi := (FiniteFamily.mapSingletonFlattenIso).inv_hom_id_app X
    have hti := ((FiniteTensor.tensor (V := C)).map_comp _ _).symm.trans
      ((congrArg (FiniteTensor.tensor (V := C)).map hi).trans ((FiniteTensor.tensor (V :=
        C)).map_id _))
    have hci := ((FiniteTensor.tensor (V := C)).map_comp ci c).symm.trans
      ((congrArg (FiniteTensor.tensor (V := C)).map
        (Iso.inv_hom_id_app (FiniteFamily.mapIso (FiniteTensor.singletonIso (V := C))) X)).trans
        ((FiniteTensor.tensor (V := C)).map_id _))
    exact (Category.assoc _ _ _).trans (h.symm.trans (hti.trans hci.symm))
  have hk := (FiniteTensor.tensor (V := C)).map_comp
    (FiniteFamily.mapSingletonFlattenIso.inv.app X) ((FiniteFamily.flatten (C := C)).map k)
  have hn' : (FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map k) ≫
      (FiniteTensor.flattenIso (V := C)).hom.app N =
      a ≫ (FiniteTensor.tensor (V := C)).map ((FiniteFamily.map FiniteTensor.tensor).map k) := hn
  symm
  exact (congrArg (· ≫ _) hk).trans
    ((Category.assoc _ _ _).trans
      ((congrArg ((FiniteTensor.tensor (V := C)).map
        (FiniteFamily.mapSingletonFlattenIso.inv.app X) ≫ ·) hn').trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) hu).trans
            (((FiniteTensor.tensor (V := C)).map_comp _ _).symm.trans
              (congrArg (FiniteTensor.tensor (V := C)).map hf))))))



end CategoryTheory.Operad.Tensor
end
end
end source_SingletonBranchAssembly

/- Source proof segment: RightUnitInputFactors -/
section source_RightUnitInputFactors
/-!
# Original input-unit factors for right operadic substitution

The original unary operadic unit is inserted in every original
input slot. These maps retain the outer operation coefficient and
each original A input; no monad unit equation is an input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original coefficient and inputs, before inserting unary
identity operation coefficients at every original input. -/
def rightUnitInputFamily (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) : FiniteFamily C :=
  (analyticFactors O A).obj P

/-- The original outer coefficient and unary operation-input
tensor at every original input after source unit insertion. -/
def rightUnitExpandedFamily (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) : FiniteFamily C where
  index := analyticFactorsIndex P
  obj i := match i with
    | none => O.obj P.toColoredProfile
    | some i => (analyticSummand O A).obj (AnalyticIndex.unary (d :=
      P.inputColor i) (P.inputColor i))

/-- Insert the original unary unit into each original input tensor,
retaining the outer coefficient as its actual identity map. -/
def rightUnitInputFactorMap (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    rightUnitInputFamily O.toCollection A P ⟶ rightUnitExpandedFamily O.toCollection A P where
  equiv := Equiv.refl (Option P.inputs)
  hom i := match i with
    | none => 𝟙 (O.toCollection.obj P.toColoredProfile)
    | some i => unitInsertion O A (P.inputColor i)

/-- Tensor the original coefficient identity and all original
input unary-unit insertions. -/
def rightUnitInputTensorMap (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (analyticSummand O.toCollection A).obj P ⟶
      (FiniteTensor.tensor (V := C)).obj (rightUnitExpandedFamily O.toCollection A P) :=
  (FiniteTensor.tensor (V := C)).map (rightUnitInputFactorMap O A P)

variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The actual original profile-unit map on all carrier inputs is
the original input-unit tensor map followed by every actual unary
profile injection. -/
theorem rightUnitInputTensorMap_profileUnit (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (analyticSummandCarrierMap O.toCollection ((profileUnit O).app A)).app P =
      rightUnitInputTensorMap O A P ≫
        (FiniteTensor.tensor (V := C)).map
          ({ equiv := Equiv.refl (Option P.inputs)
             hom i := match i with
               | none => 𝟙 (O.toCollection.obj P.toColoredProfile)
               | some i => profileι O.toCollection A (AnalyticIndex.unary (d :=
                 P.inputColor i) (P.inputColor i)) } :
            rightUnitExpandedFamily O.toCollection A P ⟶
              (analyticFactors O.toCollection (profileCoinvariants O.toCollection A)).obj P) := by
  apply Eq.trans ?_ ((FiniteTensor.tensor (V := C)).map_comp _ _)
  apply congrArg (FiniteTensor.tensor (V := C)).map
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none => exact heq_of_eq (Category.id_comp _).symm
    | some i => exact HEq.rfl



end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitInputFactors

/- Source proof segment: RightUnitRawAssembly -/
section source_RightUnitRawAssembly
/-!
# Original raw right-unit tensor assembly

The original input unit maps assemble to the actual raw two-level
source for right-unit substitution. Coefficient and leaf unitors
are retained; the operad right-unit equation will be applied after
the original coefficient/leaf regrouping comparison.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original right-unit substitution source tuple, with every
original input's unary identity profile. -/
def rightUnitNestedFactors (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) : FiniteFamily (FiniteFamily C) :=
  nestedOperationFactors O A (tupleSubstitutionShape P (rightUnitProfileTuple P))

/-- The coefficient singleton unitor identifies the original
expanded right-unit input family with the original tensor of inner
operation blocks, retaining every actual input type. -/
def rightUnitExpandedFactorsIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    rightUnitExpandedFamily O A P ≅
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (rightUnitNestedFactors O A P) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option P.inputs))
    (fun i => match i with
      | none => ((FiniteTensor.singletonIso (V := C)).app (O.obj P.toColoredProfile)).symm
      | some i => Iso.refl ((analyticSummand O A).obj (AnalyticIndex.unary (d :=
        P.inputColor i) (P.inputColor i))))

/-- The actual original input-unit tensor followed by coefficient
unitor and source flattening reaches the original raw right-unit
operadic substitution source. -/
def rightUnitRawInsertion (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (analyticSummand O.toCollection A).obj P ⟶
      algebraSubstitutionSource O.toCollection A
        (tupleSubstitutionShape P (rightUnitProfileTuple P)) :=
  rightUnitInputTensorMap O A P ≫
    (FiniteTensor.tensor (V := C)).map (rightUnitExpandedFactorsIso O.toCollection A P).hom ≫
    (FiniteTensor.flattenIso (V := C)).inv.app (rightUnitNestedFactors O.toCollection A P)



end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitRawAssembly

/- Source proof segment: RightUnitCoefficientLeaves -/
section source_RightUnitCoefficientLeaves
/-!
# Original right-unit coefficient grouping with unchanged leaves

The source coefficient grouping is exactly the existing right-unit
insertion grouping. Original A input leaves occupy their matching
singleton blocks; no operation or leaf is replaced.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original source right-unit coefficient grouping. -/
def rightUnitCoefficientGrouping (O : ColoredSymmetricCollection W C)
    {d : W} (P : AnalyticIndex W d) : FiniteFamily (FiniteFamily C) :=
  UnitInsertion.rightNestedFamily (O.obj P.toColoredProfile) P.inputs

/-- The original input leaves, retained as their matching
singleton blocks; the outer coefficient block has no leaf input. -/
def rightUnitLeafBlocks (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) : (rightUnitCoefficientGrouping O P).index → FiniteFamily C
  | none => FiniteFamily.empty
  | some i => (FiniteFamily.singleton (C := C)).obj (A (P.inputColor i))

/-- The original source coefficient-unit factors map to the
original operadic substitution coefficient factors. -/
def rightUnitCoefficientFactorMap (O : ColoredOperadObj W C)
    {d : W} (P : AnalyticIndex W d) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        (rightUnitCoefficientGrouping O.toCollection P) ⟶
      (ColoredOperadObj.substitutionFactors O.toCollection).obj
        (ColoredSubstitutionData.rightUnit P.toColoredProfile) :=
  ColoredOperadObj.UnitInsertion.rightFactorHom O.toCollection O.unit P.toColoredProfile

/-- Original leaf reindexing for the source right-unit total
profile map; the actual sigma-unit bijection is retained. -/
def rightUnitLeafTotalIso (A : W → C) {d : W} (P : AnalyticIndex W d) :
    profileLeafFamily A (ColoredSubstitutionData.rightUnit P.toColoredProfile).totalProfile ≅
      profileLeafFamily A P.toColoredProfile :=
  profileLeafRelabelIso A (ColoredSubstitutionData.rightUnitTotalHom P.toColoredProfile)



end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitCoefficientLeaves

/- Source proof segment: RightUnitPartitionSource -/
section source_RightUnitPartitionSource
/-!
# Actual original right-unit partition source

The original coefficient and every original input object are
identified with the source singleton/empty-unit coefficient grouping
and matching singleton leaf blocks by a displayed actual bijection.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The actual original coefficient/input factors equal the flat
right-unit partition source, with all original input positions retained. -/
def rightUnitPartitionSourceEquiv (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    ((analyticFactors O A).obj P).index ≃
      ((FiniteFamily.flatten (C := C)).obj
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
          (partitionedCoefficientLeavesTriple (rightUnitCoefficientGrouping O P)
            (rightUnitLeafBlocks O A P)))).index where
  toFun i := match i with
    | none => ⟨none, ⟨none, PUnit.unit⟩⟩
    | some i => ⟨some i, ⟨some PUnit.unit, PUnit.unit⟩⟩
  invFun i := match i with
    | ⟨none, ⟨none, _⟩⟩ => none
    | ⟨none, ⟨some i, _⟩⟩ => nomatch i
    | ⟨some i, ⟨none, j⟩⟩ => nomatch j
    | ⟨some i, ⟨some _, _⟩⟩ => some i
  left_inv i := by cases i <;> rfl
  right_inv i := by
    rcases i with ⟨i, ⟨l, k⟩⟩
    cases i with
    | none =>
      cases l with
      | none => cases k; rfl
      | some l => nomatch l
    | some i =>
      cases l with
      | none => nomatch k
      | some l => cases l; cases k; rfl

/-- The exact original right-unit partition source isomorphism
retains each original coefficient and input object. -/
def rightUnitPartitionSourceIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (analyticFactors O A).obj P ≅
      (FiniteFamily.flatten (C := C)).obj
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
          (partitionedCoefficientLeavesTriple (rightUnitCoefficientGrouping O P)
            (rightUnitLeafBlocks O A P))) :=
  FiniteFamily.isoOfReindex (rightUnitPartitionSourceEquiv O A P)
    (fun i => by cases i <;> rfl)

end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitPartitionSource

/- Source proof segment: RightUnitPartitionLeaves -/
section source_RightUnitPartitionLeaves
/-!
# Original leaf bijection in right-unit partition normalization

All original input leaves are retained; the outer coefficient
block and empty unit-source blocks contribute no additional leaves.
The displayed bijection reaches the original right-unit total profile.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original unit partition leaves identify with the original
right-unit total input positions, preserving their actual colors. -/
def rightUnitPartitionLeafEquiv (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (partitionedLeafFamily (rightUnitCoefficientGrouping O P) (rightUnitLeafBlocks O A P)).index ≃
      (profileLeafFamily A (ColoredSubstitutionData.rightUnit
        P.toColoredProfile).totalProfile).index where
  toFun i := match i with
    | ⟨none, j⟩ => nomatch j
    | ⟨some i, j⟩ => ⟨i, j⟩
  invFun i := ⟨some i.1, i.2⟩
  left_inv i := by
    rcases i with ⟨i, j⟩
    cases i with
    | none => nomatch j
    | some i => rfl
  right_inv i := by rcases i with ⟨i, j⟩; rfl

/-- The actual source right-unit partition leaves have precisely
the original total-profile A values at every leaf input. -/
def rightUnitPartitionLeafIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    partitionedLeafFamily (rightUnitCoefficientGrouping O P) (rightUnitLeafBlocks O A P) ≅
      profileLeafFamily A (ColoredSubstitutionData.rightUnit P.toColoredProfile).totalProfile :=
  FiniteFamily.isoOfReindex (rightUnitPartitionLeafEquiv O A P)
    (fun i => by rcases i with ⟨i, j⟩; cases i with
      | none => nomatch j
      | some i => cases j; rfl)

end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitPartitionLeaves

/- Source proof segment: RightUnitPartitionAction -/
section source_RightUnitPartitionAction
/-!
# Original coefficient action in right-unit partition geometry

The original outer coefficient unitor and every original unary
operad unit are the branch coefficient maps of the source partition
normalization. No right-unit or monad equation is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original coefficient objects produced by the right-unit
source coefficient maps at every retained original input. -/
def rightUnitPartitionCoefficients (O : ColoredSymmetricCollection W C)
    {d : W} (P : AnalyticIndex W d) : (rightUnitCoefficientGrouping O P).index → C
  | none => O.obj P.toColoredProfile
  | some i => O.obj (ColoredSubstitutionData.unitProfile (P.inputColor i))

/-- The actual original operadic unit and outer singleton unitor
at every original coefficient block. -/
def rightUnitPartitionCoefficientMap (O : ColoredOperadObj W C) {d : W} (P : AnalyticIndex W d) :
    ∀ i : (rightUnitCoefficientGrouping O.toCollection P).index,
      (FiniteTensor.tensor (V := C)).obj ((rightUnitCoefficientGrouping O.toCollection P).obj i) ⟶
        rightUnitPartitionCoefficients O.toCollection P i
  | none => (FiniteTensor.singletonIso (V := C)).hom.app (O.toCollection.obj P.toColoredProfile)
  | some i => O.unit (P.inputColor i)

/-- Identify the original right-unit partitioned coefficients with the operad substitution
factors. -/
def rightUnitPartitionCoefficientIso (O : ColoredSymmetricCollection W C)
    {d : W} (P : AnalyticIndex W d) :
    partitionedScalarCoefficients (rightUnitCoefficientGrouping O P)
        (rightUnitPartitionCoefficients O P) ≅
      (ColoredOperadObj.substitutionFactors O).obj (ColoredSubstitutionData.rightUnit
        P.toColoredProfile) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option P.inputs))
    (fun i => match i with
      | none => Iso.refl (O.obj P.toColoredProfile)
      | some i => Iso.refl (O.obj (ColoredSubstitutionData.unitProfile (P.inputColor i))))

/-- The partition coefficient family map is the original source
right-unit coefficient map, with no replacement operations. -/
theorem rightUnitPartitionCoefficientMap_eq (O : ColoredOperadObj W C) {d : W} (P :
  AnalyticIndex W d) :
    partitionedCoefficientMap (rightUnitCoefficientGrouping O.toCollection P)
        (rightUnitPartitionCoefficients O.toCollection P) (rightUnitPartitionCoefficientMap O P) ≫
      (rightUnitPartitionCoefficientIso O.toCollection P).hom =
      rightUnitCoefficientFactorMap O P := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      have h := ColoredSubstitutionData.rightUnitOuterHom_eq_id P.toColoredProfile
      change HEq (((FiniteTensor.singletonIso (V := C)).hom.app _) ≫ 𝟙 _)
        ((FiniteTensor.singletonIso (V := C)).hom.app _ ≫ O.toCollection.map _)
      have hm := (congrArg O.toCollection.map h).trans (O.toCollection.map_id P.toColoredProfile)
      exact heq_of_eq (congrArg ((FiniteTensor.singletonIso (V := C)).hom.app
        (O.toCollection.obj P.toColoredProfile) ≫ ·) hm).symm
    | some i => exact heq_of_eq (Category.comp_id _)

end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitPartitionAction

/- Source proof segment: EmptyCoefficientUnitInsertion -/
section source_EmptyCoefficientUnitInsertion
/-!
# Original unit insertion through coefficient/leaf normalization

The original empty coefficient block and singleton input leaf form
the source left-unit nested family. Its original tensor maps factor
the actual unit insertion through coefficient/leaf normalization.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

private theorem reassociateFour {V : Type*} [Category* V] {A B C D E : V}
    (p : A ⟶ B) (q : B ⟶ C) (r : C ⟶ D) (s : D ⟶ E) :
    (p ≫ q ≫ r) ≫ s = p ≫ q ≫ (r ≫ s) := by
  simp only [Category.assoc]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- Identify the empty coefficient and singleton leaf partition with the original
left-nested unit family. -/
def emptyCoefficientUnitNestedIso (X : C) :
    UnitInsertion.leftNestedFamily X ≅
      coefficientLeavesNested (FiniteFamily.empty (C := C))
        ((FiniteFamily.singleton (C := C)).obj X) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option PUnit))
    (fun i => match i with
      | none => Iso.refl FiniteFamily.empty
      | some _ => Iso.refl ((FiniteFamily.singleton (C := C)).obj X))

/-- Apply the original unit map in the empty coefficient slot, retaining the singleton leaf. -/
def emptyCoefficientUnitFactor {Y : C} (η : operadUnitSource (V := C) ⟶ Y) (X : C) :
    UnitInsertion.leftTensorFamily X ⟶
      (coefficientLeafFamilyFunctor ((FiniteFamily.singleton (C := C)).obj X)).obj Y where
  equiv := Equiv.refl (Option PUnit)
  hom i := match i with
    | none => η
    | some _ => (FiniteTensor.singletonIso (V := C)).hom.app X

/-- The original unit-factor map agrees after the actual empty
coefficient/singleton leaf nested-family identification. -/
theorem emptyCoefficientUnitFactor_eq {Y : C} (η : operadUnitSource (V := C) ⟶ Y) (X : C) :
    (FiniteFamily.map FiniteTensor.tensor).map (emptyCoefficientUnitNestedIso X).hom ≫
      coefficientLeavesMap FiniteFamily.empty ((FiniteFamily.singleton (C := C)).obj X) η =
    emptyCoefficientUnitFactor η X := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      change HEq ((FiniteTensor.tensor (V := C)).map (𝟙 FiniteFamily.empty) ≫ η) η
      exact heq_of_eq ((congrArg (· ≫ η) ((FiniteTensor.tensor (V := C)).map_id _)).trans
        (Category.id_comp _))
    | some i =>
      change HEq ((FiniteTensor.tensor (V := C)).map (𝟙 ((FiniteFamily.singleton (C := C)).obj X)) ≫
        (FiniteTensor.singletonIso (V := C)).hom.app X) ((FiniteTensor.singletonIso (V :=
          C)).hom.app X)
      exact heq_of_eq ((congrArg (· ≫ _) ((FiniteTensor.tensor (V := C)).map_id _)).trans
        (Category.id_comp _))

/-- The actual source unit insertion factors through its original
empty coefficient block and singleton leaf normalization. -/
theorem emptyCoefficientUnitInsertion_factorization {Y : C}
    (η : operadUnitSource (V := C) ⟶ Y) (X : C) :
    UnitInsertion.leftInsertFromFactor X (emptyCoefficientUnitFactor η X) =
      (FiniteTensor.singletonIso (V := C)).inv.app X ≫
        (FiniteTensor.tensor (V := C)).map (UnitInsertion.leftSingletonToFlatten X) ≫
        (FiniteTensor.tensor (V := C)).map
          ((FiniteFamily.flatten (C := C)).map (emptyCoefficientUnitNestedIso X).hom) ≫
        coefficientLeavesNormalization FiniteFamily.empty ((FiniteFamily.singleton (C :=
          C)).obj X) ≫
        (coefficientLeafTensorFunctor ((FiniteFamily.singleton (C := C)).obj X)).map η := by
  let T := FiniteTensor.tensor (V := C)
  let e := (emptyCoefficientUnitNestedIso X).hom
  let a := (FiniteTensor.flattenIso (V := C)).hom.app (UnitInsertion.leftNestedFamily X)
  let b := (FiniteTensor.flattenIso (V := C)).hom.app
    (coefficientLeavesNested FiniteFamily.empty ((FiniteFamily.singleton (C := C)).obj X))
  let f := coefficientLeavesMap FiniteFamily.empty ((FiniteFamily.singleton (C := C)).obj X) η
  have hn := (FiniteTensor.flattenIso (V := C)).hom.naturality e
  change T.map ((FiniteFamily.flatten (C := C)).map e) ≫ b =
    a ≫ T.map ((FiniteFamily.map T).map e) at hn
  have hf := emptyCoefficientUnitFactor_eq η X
  have hh : T.map ((FiniteFamily.map T).map e) ≫ T.map f = T.map (emptyCoefficientUnitFactor η X) :=
    (T.map_comp _ _).symm.trans (congrArg T.map hf)
  have hnorm := coefficientLeavesNormalization_map FiniteFamily.empty
    ((FiniteFamily.singleton (C := C)).obj X) η
  have h : T.map ((FiniteFamily.flatten (C := C)).map e) ≫
      coefficientLeavesNormalization FiniteFamily.empty ((FiniteFamily.singleton (C := C)).obj X) ≫
      (coefficientLeafTensorFunctor ((FiniteFamily.singleton (C := C)).obj X)).map η =
      a ≫ T.map (emptyCoefficientUnitFactor η X) := by
    exact (congrArg (T.map ((FiniteFamily.flatten (C := C)).map e) ≫ ·) hnorm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ T.map f) hn).trans
          ((Category.assoc _ _ _).trans (congrArg (a ≫ ·) hh))))
  change ((FiniteTensor.singletonIso (V := C)).inv.app X ≫
      T.map (UnitInsertion.leftSingletonToFlatten X) ≫ a) ≫
        T.map (emptyCoefficientUnitFactor η X) = _
  have ha : (((FiniteTensor.singletonIso (V := C)).inv.app X ≫
      T.map (UnitInsertion.leftSingletonToFlatten X) ≫ a) ≫
        T.map (emptyCoefficientUnitFactor η X)) =
      (FiniteTensor.singletonIso (V := C)).inv.app X ≫ T.map
        (UnitInsertion.leftSingletonToFlatten X) ≫
        (a ≫ T.map (emptyCoefficientUnitFactor η X)) :=
    reassociateFour _ _ _ _
  exact ha.trans
    (congrArg ((FiniteTensor.singletonIso (V := C)).inv.app X ≫
      T.map (UnitInsertion.leftSingletonToFlatten X) ≫ ·)
      h.symm)



end CategoryTheory.Operad.Tensor
end
end
end source_EmptyCoefficientUnitInsertion

/- Source proof segment: UnaryUnitCoefficientLeaves -/
section source_UnaryUnitCoefficientLeaves
/-!
# Original unary operadic unit as coefficient/leaf normalization

The original unary operad coefficient map is inserted through its
actual empty tensor source and singleton original A input. The
source factorization is the actual coefficient/leaf normalization,
with original unitors retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

private theorem postcomposeFive {V : Type*} [Category* V] {A B C D E F G : V}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E) (e : E ⟶ F) (f : F ⟶ G) :
    (a ≫ b ≫ c ≫ d ≫ e) ≫ f = a ≫ b ≫ c ≫ d ≫ e ≫ f := by
  simp only [Category.assoc]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Identify the original unary unit coefficient-and-leaf family with its analytic operation
factors. -/
def unaryUnitCoefficientLeavesTargetIso (O : ColoredSymmetricCollection W C) (X : C) (d : W) :
    (coefficientLeafFamilyFunctor ((FiniteFamily.singleton (C := C)).obj X)).obj
        (O.obj (ColoredSubstitutionData.unitProfile d)) ≅
      (analyticFactors O (fun _ : W => X)).obj (AnalyticIndex.unary (d := d) d) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option PUnit))
    (fun i => match i with
      | none => Iso.refl (O.obj (ColoredSubstitutionData.unitProfile d))
      | some _ => Iso.refl X)

/-- The original unary coefficient/input factor map is exactly
the original empty-coefficient unit factor map followed by the
original finite family target identification. -/
theorem unaryUnitCoefficientLeaves_factor (O : ColoredOperadObj W C) (X : C) (d : W) :
    emptyCoefficientUnitFactor (O.unit d) X ≫
      (unaryUnitCoefficientLeavesTargetIso O.toCollection X d).hom =
    unitFactors O (fun _ : W => X) d := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none => exact heq_of_eq (Category.comp_id _)
    | some i => exact heq_of_eq (Category.comp_id _)

/-- Every original scalar unary unit insertion factors through the
actual empty coefficient and singleton leaf normalization. -/
theorem unaryTensorUnit_coefficientLeaves (O : ColoredOperadObj W C) (X : C) (d : W) :
    (unaryTensorUnit O d).app X =
      (FiniteTensor.singletonIso (V := C)).inv.app X ≫
        (FiniteTensor.tensor (V := C)).map (UnitInsertion.leftSingletonToFlatten X) ≫
        (FiniteTensor.tensor (V := C)).map
          ((FiniteFamily.flatten (C := C)).map (emptyCoefficientUnitNestedIso X).hom) ≫
        coefficientLeavesNormalization FiniteFamily.empty ((FiniteFamily.singleton (C :=
          C)).obj X) ≫
        (coefficientLeafTensorFunctor ((FiniteFamily.singleton (C := C)).obj X)).map (O.unit d) ≫
        (FiniteTensor.tensor (V := C)).map (unaryUnitCoefficientLeavesTargetIso
          O.toCollection X d).hom := by
  have h := unaryUnitCoefficientLeaves_factor O X d
  have hu := UnitInsertion.leftInsertFromFactor_comp X (emptyCoefficientUnitFactor (O.unit d) X)
    (unaryUnitCoefficientLeavesTargetIso O.toCollection X d).hom
  have hf := emptyCoefficientUnitInsertion_factorization (O.unit d) X
  have hs : (unaryTensorUnit O d).app X =
      UnitInsertion.leftInsertFromFactor X (emptyCoefficientUnitFactor (O.unit d) X) ≫
        (FiniteTensor.tensor (V := C)).map (unaryUnitCoefficientLeavesTargetIso
          O.toCollection X d).hom := by
    exact (congrArg (UnitInsertion.leftInsertFromFactor X) h.symm).trans hu.symm
  let q := (FiniteTensor.tensor (V := C)).map (unaryUnitCoefficientLeavesTargetIso
    O.toCollection X d).hom
  have hpost := congrArg (fun z : X ⟶ _ => z ≫ q) hf
  exact hs.trans (hpost.trans (postcomposeFive _ _ _ _ _ q))



end CategoryTheory.Operad.Tensor
end
end
end source_UnaryUnitCoefficientLeaves

/- Source proof segment: RightUnitPartitionBranchMaps -/
section source_RightUnitPartitionBranchMaps
/-!
# Original right-unit branch maps into partition normalization

Each original A input is inserted into the actual empty-unit-source
and singleton-leaf branch. The outer coefficient uses its original
singleton. These are the original source maps of the partition action.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original coefficient/input factor family before each
branchwise partition normalization. -/
def rightUnitPartitionBranchFactors (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) : FiniteFamily C :=
  (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
    ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
      (partitionedCoefficientLeavesTriple (rightUnitCoefficientGrouping O P)
        (rightUnitLeafBlocks O A P)))

/-- The original original coefficient singleton/input branch maps
reach the actual original partition source branch tensors. -/
def rightUnitPartitionBranchMap (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (analyticFactors O A).obj P ⟶ rightUnitPartitionBranchFactors O A P where
  equiv := Equiv.refl (Option P.inputs)
  hom i := match i with
    | none => (FiniteTensor.singletonIso (V := C)).inv.app (O.obj P.toColoredProfile) ≫
      (FiniteTensor.tensor (V := C)).map
        ({ equiv :=
            { toFun := fun _ => ⟨none, PUnit.unit⟩
              invFun := fun _ => PUnit.unit
              left_inv := by intro x; cases x; rfl
              right_inv := by intro x; rcases x with ⟨l, k⟩; cases l with
                | none => cases k; rfl
                | some l => nomatch l }
           hom _ := 𝟙 (O.obj P.toColoredProfile) } :
          (FiniteFamily.singleton (C := C)).obj (O.obj P.toColoredProfile) ⟶
            (FiniteFamily.flatten (C := C)).obj
              (coefficientLeavesNested ((FiniteFamily.singleton (C :=
                C)).obj (O.obj P.toColoredProfile))
                FiniteFamily.empty))
    | some i => (FiniteTensor.singletonIso (V := C)).inv.app (A (P.inputColor i)) ≫
      (FiniteTensor.tensor (V := C)).map (UnitInsertion.leftSingletonToFlatten (A
        (P.inputColor i))) ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map (emptyCoefficientUnitNestedIso (A (P.inputColor
          i))).hom)

end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitPartitionBranchMaps

/- Source proof segment: RightUnitBranchAssembly -/
section source_RightUnitBranchAssembly
/-!
# Actual original right-unit branch assembly

The original coefficient/input source bijection followed by tensor
flattening is the tensor of the original singleton branch insertion
maps. This is the complete source unit assembly, not a monad axiom.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Insert each original right-unit input into its singleton coefficient-and-leaf branch. -/
def rightUnitBranchSingletonMap (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (FiniteFamily.map (FiniteFamily.singleton (C := C))).obj ((analyticFactors O A).obj P) ⟶
      (FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
        (partitionedCoefficientLeavesTriple (rightUnitCoefficientGrouping O P)
          (rightUnitLeafBlocks O A P)) where
  equiv := Equiv.refl (Option P.inputs)
  hom i := match i with
    | none =>
      { equiv :=
          { toFun := fun _ => ⟨none, PUnit.unit⟩
            invFun := fun _ => PUnit.unit
            left_inv := by intro x; cases x; rfl
            right_inv := by intro x; rcases x with ⟨l, k⟩; cases l with
              | none => cases k; rfl
              | some l => nomatch l }
        hom _ := 𝟙 (O.obj P.toColoredProfile) }
    | some i => UnitInsertion.leftSingletonToFlatten (A (P.inputColor i)) ≫
        (FiniteFamily.flatten (C := C)).map (emptyCoefficientUnitNestedIso (A (P.inputColor i))).hom

/-- Every tensor branch component is the actual singleton inversion
and original source branch map. -/
theorem rightUnitPartitionBranchMap_eq (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    singletonBranchTensorMap ((analyticFactors O A).obj P)
      ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
        (partitionedCoefficientLeavesTriple (rightUnitCoefficientGrouping O P)
          (rightUnitLeafBlocks O A P)))
      (Equiv.refl (Option P.inputs)) (rightUnitBranchSingletonMap O A P).hom =
    rightUnitPartitionBranchMap O A P := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none => exact HEq.rfl
    | some i =>
      exact heq_of_eq (congrArg ((FiniteTensor.singletonIso (V :=
        C)).inv.app (A (P.inputColor i)) ≫ ·)
        ((FiniteTensor.tensor (V := C)).map_comp _ _))

omit [FiniteTensor C] in
/-- The exact flattened source map obtained from the original
singleton branch family is the original right-unit input bijection. -/
theorem rightUnitBranchSource_eq (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    FiniteFamily.mapSingletonFlattenIso.inv.app ((analyticFactors O A).obj P) ≫
      (FiniteFamily.flatten (C := C)).map (rightUnitBranchSingletonMap O A P) =
    (rightUnitPartitionSourceIso O A P).hom := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro i
    cases i <;> rfl
  · intro i
    cases i with
    | none =>
      exact heq_of_eq (show (𝟙 (O.obj P.toColoredProfile)) ≫ 𝟙 _ = 𝟙 _ from Category.id_comp _)
    | some i =>
      exact heq_of_eq (show (𝟙 (A (P.inputColor i))) ≫ ((𝟙 _) ≫ 𝟙 _) = 𝟙 _ from by
        simp only [Category.id_comp])

/-- The original input tensor source assembles through the exact
right-unit source bijection and original tensor flattening. -/
theorem rightUnitPartitionBranchAssembly (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (FiniteTensor.tensor (V := C)).map (rightUnitPartitionBranchMap O A P) =
      (FiniteTensor.tensor (V := C)).map (rightUnitPartitionSourceIso O A P).hom ≫
        (FiniteTensor.flattenIso (V := C)).hom.app
          ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
            (partitionedCoefficientLeavesTriple (rightUnitCoefficientGrouping O P)
              (rightUnitLeafBlocks O A P))) := by
  have h := singletonBranchAssembly ((analyticFactors O A).obj P)
    ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
      (partitionedCoefficientLeavesTriple (rightUnitCoefficientGrouping O P)
        (rightUnitLeafBlocks O A P)))
    (Equiv.refl (Option P.inputs)) (rightUnitBranchSingletonMap O A P).hom
  exact (congrArg (FiniteTensor.tensor (V := C)).map (rightUnitPartitionBranchMap_eq O A
    P).symm).trans
    (h.trans (congrArg (· ≫ _) (congrArg (FiniteTensor.tensor (V :=
      C)).map (rightUnitBranchSource_eq O A P))))



end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitBranchAssembly

/- Source proof segment: RightUnitScalarFrame -/
section source_RightUnitScalarFrame
/-!
# Actual right-unit scalar branch frame

The original partition scalar coefficient/leaf factors identify
with the original nested right-unit operation factors, including
the coefficient's original singleton and every unary input profile.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Identify the original right-unit empty leaf frame index with its singleton outer
coefficient slot. -/
def rightUnitScalarOuterEquiv (O : ColoredSymmetricCollection W C)
    {d : W} (P : AnalyticIndex W d) :
    ((coefficientLeafFamilyFunctor FiniteFamily.empty).obj (O.obj P.toColoredProfile)).index
      ≃ PUnit where
  toFun i := PUnit.unit
  invFun _ := none
  left_inv i := by cases i with
    | none => rfl
    | some i => nomatch i
  right_inv i := by cases i; rfl

/-- Identify the original right-unit empty leaf frame with its singleton coefficient family. -/
def rightUnitScalarOuterIso (O : ColoredSymmetricCollection W C)
    {d : W} (P : AnalyticIndex W d) :
    (coefficientLeafFamilyFunctor FiniteFamily.empty).obj (O.obj P.toColoredProfile) ≅
      (FiniteFamily.singleton (C := C)).obj (O.obj P.toColoredProfile) :=
  FiniteFamily.isoOfReindex (rightUnitScalarOuterEquiv O P)
    (fun i => by cases i with
      | none => rfl
      | some i => nomatch i)

/-- Identify the partitioned right-unit scalar frame with its original nested operation factors. -/
def rightUnitScalarFrameIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    partitionedScalarLeaves (rightUnitCoefficientGrouping O P) (rightUnitLeafBlocks O A P)
        (rightUnitPartitionCoefficients O P) ≅ rightUnitNestedFactors O A P :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option P.inputs))
    (fun i => match i with
      | none => rightUnitScalarOuterIso O P
      | some i => FiniteFamily.isoOfComponents (Equiv.refl (Option PUnit))
          (fun j => match j with
            | none => Iso.refl (O.obj (ColoredSubstitutionData.unitProfile (P.inputColor i)))
            | some _ => Iso.refl (A (P.inputColor i))))

end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitScalarFrame

/- Source proof segment: RightUnitBranchAction -/
section source_RightUnitBranchAction
/-!
# Actual original right-unit branch coefficient actions

The branch coefficient substitutions recover the original
coefficient identity and every original unary input unit map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

private theorem coefficientBranchReadback {V : Type*} [Category* V]
    {X S R U : V} (s : S ≅ X) (r : S ≅ R) (b : R ⟶ U) (e : U ⟶ S)
    (h : b ≫ e ≫ s.hom = r.inv ≫ s.hom) :
    (s.inv ≫ r.hom ≫ b) ≫ e = s.inv := by
  apply (cancel_mono s.hom).1
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id] using
    congrArg (fun k => s.inv ≫ r.hom ≫ k) h

private theorem reassociateInputBranch {V : Type*} [Category* V]
    {A B C D E F G : V} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (d : D ⟶ E) (e : E ⟶ F) (f : F ⟶ G) :
    (a ≫ b ≫ c) ≫ (d ≫ e) ≫ f = a ≫ b ≫ c ≫ d ≫ e ≫ f := by
  simp only [Category.assoc]

private theorem coefficientBranchReadbackSource {V : Type*} [Category* V]
    {X S R U : V} (s : S ≅ X) (r : S ≅ R) (a : S ⟶ R)
    (b : R ⟶ U) (e : U ⟶ S)
    (h : b ≫ e ≫ s.hom = r.inv ≫ s.hom) (ha : a = r.hom) :
    (s.inv ≫ a) ≫ b ≫ e = 𝟙 X ≫ s.inv := by
  subst a
  simpa only [Category.assoc, Category.id_comp] using coefficientBranchReadback s r b e h

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

omit [FiniteTensor C] in
/-- The original coefficient branch source is the inverse of its
actual empty-leaf singleton index identification. -/
theorem rightUnitOuterSource_eq (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (rightUnitBranchSingletonMap O A P).hom none =
      (emptyLeafRawIso ((FiniteFamily.singleton (C := C)).obj (O.obj P.toColoredProfile))).inv := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro i
    cases i
    rfl
  · intro i
    cases i
    exact heq_of_eq (show 𝟙 (O.obj P.toColoredProfile) =
      (𝟙 _) ≫ ((𝟙 _) ≫ 𝟙 _) from by simp only [Category.id_comp])

omit [FiniteTensor C] in
/-- The original scalar coefficient frame is the original
empty-leaf singleton family identification. -/
theorem rightUnitScalarOuterIso_hom (O : ColoredSymmetricCollection W C)
    {d : W} (P : AnalyticIndex W d) :
    (rightUnitScalarOuterIso O P).hom = (emptyLeafFamilyIso (O.obj P.toColoredProfile)).hom := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro i
    cases i with
    | none => rfl
    | some i => nomatch i
  · intro i
    cases i with
    | none => exact HEq.rfl
    | some i => nomatch i

omit [FiniteTensor C] in
/-- Each input branch of the original scalar frame is the
original unary coefficient/input target isomorphism. -/
theorem rightUnitScalarFrame_input (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) (i : P.inputs) :
    (rightUnitScalarFrameIso O A P).hom.hom (some i) =
      (unaryUnitCoefficientLeavesTargetIso O (A (P.inputColor i)) (P.inputColor i)).hom := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro j
    cases j <;> exact HEq.rfl

/-- Every original branch coefficient action equals the original
input-unit factor map followed by its coefficient singleton frame. -/
theorem rightUnitPartitionBranchAction (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    rightUnitPartitionBranchMap O.toCollection A P ≫
      partitionedCoefficientLeavesActionMap (rightUnitCoefficientGrouping O.toCollection P)
        (rightUnitLeafBlocks O.toCollection A P) (rightUnitPartitionCoefficients O.toCollection P)
        (rightUnitPartitionCoefficientMap O P) ≫
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).map
        (rightUnitScalarFrameIso O.toCollection A P).hom =
    rightUnitInputFactorMap O A P ≫ (rightUnitExpandedFactorsIso O.toCollection A P).hom := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      change HEq
        (((FiniteTensor.singletonIso (V := C)).inv.app (O.toCollection.obj P.toColoredProfile) ≫
          (FiniteTensor.tensor (V := C)).map
            ((rightUnitBranchSingletonMap O.toCollection A P).hom none)) ≫
          ((coefficientLeavesNormalization ((FiniteFamily.singleton (C := C)).obj
            (O.toCollection.obj P.toColoredProfile)) FiniteFamily.empty ≫
            (coefficientLeafTensorFunctor FiniteFamily.empty).map
              ((FiniteTensor.singletonIso (V := C)).hom.app (O.toCollection.obj
                P.toColoredProfile))) ≫
          (FiniteTensor.tensor (V := C)).map (rightUnitScalarOuterIso O.toCollection P).hom))
        (𝟙 _ ≫ (FiniteTensor.singletonIso (V := C)).inv.app _)
      let X := O.toCollection.obj P.toColoredProfile
      let K := (FiniteFamily.singleton (C := C)).obj X
      let s := (FiniteTensor.singletonIso (V := C)).app X
      let r := (FiniteTensor.tensor (V := C)).mapIso (emptyLeafRawIso K).symm
      let b := coefficientLeavesNormalization K FiniteFamily.empty ≫
        (coefficientLeafTensorFunctor FiniteFamily.empty).map s.hom
      let e := (FiniteTensor.tensor (V := C)).map (rightUnitScalarOuterIso O.toCollection P).hom
      have he : (emptyLeafTensorIso X).hom = e ≫ s.hom := by
        rw [emptyLeafTensorIso_hom, ← rightUnitScalarOuterIso_hom O.toCollection P]
        rfl
      have h := coefficientLeavesNormalization_empty_map K s.hom
      change coefficientLeavesNormalization K FiniteFamily.empty ≫
        (coefficientLeafTensorFunctor FiniteFamily.empty).map s.hom ≫ (emptyLeafTensorIso X).hom =
          (FiniteTensor.tensor (V := C)).map (emptyLeafRawIso K).hom ≫ s.hom at h
      rw [he] at h
      have hh : b ≫ e ≫ s.hom = r.inv ≫ s.hom := by
        exact (Category.assoc _ _ _).trans h
      have hsource := rightUnitOuterSource_eq O.toCollection A P
      have hsrc : (FiniteTensor.tensor (V := C)).map
          ((rightUnitBranchSingletonMap O.toCollection A P).hom none) = r.hom := by
        exact congrArg (FiniteTensor.tensor (V := C)).map hsource
      exact heq_of_eq (by
        exact coefficientBranchReadbackSource s r
          ((FiniteTensor.tensor (V := C)).map ((rightUnitBranchSingletonMap O.toCollection A
            P).hom none))
          b e hh hsrc)
    | some i =>
      change HEq
        (((FiniteTensor.singletonIso (V := C)).inv.app (A (P.inputColor i)) ≫
          (FiniteTensor.tensor (V := C)).map (UnitInsertion.leftSingletonToFlatten (A
            (P.inputColor i))) ≫
          (FiniteTensor.tensor (V := C)).map
            ((FiniteFamily.flatten (C := C)).map (emptyCoefficientUnitNestedIso (A
              (P.inputColor i))).hom)) ≫
          ((coefficientLeavesNormalization FiniteFamily.empty ((FiniteFamily.singleton (C :=
            C)).obj (A (P.inputColor
            i))) ≫
            (coefficientLeafTensorFunctor ((FiniteFamily.singleton (C :=
              C)).obj (A (P.inputColor i)))).map (O.unit
              (P.inputColor i))) ≫
          (FiniteTensor.tensor (V := C)).map ((rightUnitScalarFrameIso O.toCollection A
            P).hom.hom (some i))))
        (unitInsertion O A (P.inputColor i) ≫ 𝟙 _)
      exact heq_of_eq (by
        rw [rightUnitScalarFrame_input]
        rw [← unaryTensorUnit_app O A (P.inputColor i)]
        exact (reassociateInputBranch _ _ _ _ _ _).trans
          ((unaryTensorUnit_coefficientLeaves O (A (P.inputColor i)) (P.inputColor i)).symm.trans
            (Category.comp_id _).symm))



end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitBranchAction

/- Source proof segment: RightUnitSourceCollapse -/
section source_RightUnitSourceCollapse
/-!
# Original source collapse before right-unit insertion

The original singleton coefficient and retained leaf inputs collapse
to their original analytic tensor. Empty source unit blocks contribute
only the actual monoidal unit. Every finite input position is retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Collapse the source coefficient grouping to its original
singleton coefficient, without changing any source leaf. -/
def rightUnitCoefficientSourceIso (O : ColoredSymmetricCollection W C)
    {d : W} (P : AnalyticIndex W d) :
    (FiniteFamily.flatten (C := C)).obj (rightUnitCoefficientGrouping O P) ≅
      (FiniteFamily.singleton (C := C)).obj (O.obj P.toColoredProfile) :=
  (FiniteFamily.isoOfComponents
    (UnitInsertion.rightSingletonToFlatten (O.obj P.toColoredProfile) P.inputs).equiv
    (fun i => by cases i; exact Iso.refl (O.obj P.toColoredProfile))).symm

omit [FiniteTensor C] in
/-- The actual coefficient source singleton collapse agrees with
the original source right-unit singleton-to-flatten map. -/
theorem rightUnitCoefficientSourceIso_inv (O : ColoredSymmetricCollection W C)
    {d : W} (P : AnalyticIndex W d) :
    (rightUnitCoefficientSourceIso O P).inv =
      UnitInsertion.rightSingletonToFlatten (O.obj P.toColoredProfile) P.inputs := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i
    exact HEq.rfl

/-- Retain original coefficient and original input leaves after
source partition collapse, with the original profile colors. -/
def rightUnitSourceLeavesIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (coefficientLeafFamilyFunctor
      (partitionedLeafFamily (rightUnitCoefficientGrouping O P) (rightUnitLeafBlocks O A P))).obj
        (O.obj P.toColoredProfile) ≅ (analyticFactors O A).obj P :=
  FiniteFamily.isoOfReindex
    (Equiv.optionCongr ((rightUnitPartitionLeafIso O A P ≪≫ rightUnitLeafTotalIso A P).hom.equiv))
    (fun i => by
      cases i with
      | none => rfl
      | some i =>
        rcases i with ⟨i, j⟩
        cases i with
        | none => nomatch j
        | some i => cases j; rfl)

end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitSourceCollapse

/- Source proof segment: RightUnitNormalizationMaps -/
section source_RightUnitNormalizationMaps
/-!
# Original right-unit normalization map square

Collecting all original empty unit-source coefficient blocks and
retained input leaves commutes with the original coefficient singleton
and original leaf total-profile bijection. These are actual source maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original coefficient source and original partition leaf
family collapse map is the actual normalization naturality square. -/
theorem rightUnitNormalization_source (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (FiniteTensor.tensor (V := C)).map
      ((FiniteFamily.flatten (C := C)).map
        (coefficientLeavesNestedMap (rightUnitCoefficientSourceIso O P).hom
          (rightUnitPartitionLeafIso O A P ≪≫ rightUnitLeafTotalIso A P).hom)) ≫
      coefficientLeavesNormalization ((FiniteFamily.singleton (C :=
        C)).obj (O.obj P.toColoredProfile))
        (profileLeafFamily A P.toColoredProfile) =
    coefficientLeavesNormalization
        ((FiniteFamily.flatten (C := C)).obj (rightUnitCoefficientGrouping O P))
        (partitionedLeafFamily (rightUnitCoefficientGrouping O P) (rightUnitLeafBlocks O A P)) ≫
      (FiniteTensor.tensor (V := C)).map
        (coefficientLeafMap
          ((FiniteTensor.tensor (V := C)).map (rightUnitCoefficientSourceIso O P).hom)
          (rightUnitPartitionLeafIso O A P ≪≫ rightUnitLeafTotalIso A P).hom) :=
  coefficientLeavesNormalization_naturality _ _

end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitNormalizationMaps

/- Source proof segment: RightUnitPartitionEquation -/
section source_RightUnitPartitionEquation
/-!
# Original right-unit partition coefficient-action equation

The source partition normalization is instantiated at the original
right-unit coefficient grouping and original leaves, with the actual
O.unit component maps. This is a proved source map equality used
to derive, rather than assume, the monad right-unit geometry.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The source branch coefficient-action theorem applied to the
actual original O.unit maps and unchanged original input leaves. -/
theorem rightUnitPartition_action (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (FiniteTensor.tensor (V := C)).map
        (partitionedCoefficientLeavesSourceIso (rightUnitCoefficientGrouping O.toCollection P)
          (rightUnitLeafBlocks O.toCollection A P)).hom ≫
      coefficientLeavesNormalization
        ((FiniteFamily.flatten (C := C)).obj (rightUnitCoefficientGrouping O.toCollection P))
        (partitionedLeafFamily (rightUnitCoefficientGrouping O.toCollection P)
          (rightUnitLeafBlocks O.toCollection A P))
          ≫
      (coefficientLeafTensorFunctor
        (partitionedLeafFamily (rightUnitCoefficientGrouping O.toCollection P)
          (rightUnitLeafBlocks O.toCollection A
          P))).map
        ((FiniteTensor.flattenIso (V := C)).hom.app (rightUnitCoefficientGrouping
          O.toCollection P) ≫
          (FiniteTensor.tensor (V := C)).map
            (partitionedCoefficientMap (rightUnitCoefficientGrouping O.toCollection P)
              (rightUnitPartitionCoefficients O.toCollection P)
                (rightUnitPartitionCoefficientMap O P))) =
    (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
          (partitionedCoefficientLeavesTriple (rightUnitCoefficientGrouping O.toCollection P)
            (rightUnitLeafBlocks O.toCollection A P))) ≫
      (FiniteTensor.tensor (V := C)).map
        (partitionedCoefficientLeavesActionMap (rightUnitCoefficientGrouping O.toCollection P)
          (rightUnitLeafBlocks O.toCollection A P) (rightUnitPartitionCoefficients O.toCollection P)
          (rightUnitPartitionCoefficientMap O P)) ≫
      (partitionedScalarLeavesDistributionIso (rightUnitCoefficientGrouping O.toCollection P)
        (rightUnitLeafBlocks O.toCollection A P) (rightUnitPartitionCoefficients
          O.toCollection P)).hom :=
  partitionedCoefficientLeaves_action _ _ _ _



end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitPartitionEquation

/- Source proof segment: RightUnitRawPartition -/
section source_RightUnitRawPartition
/-!
# Original right-unit raw insertion and branch partition assembly
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

private theorem branchInsertionFromTwoSquares {V : Type*} [Category* V]
    {X B S N E R : V} (b : X ⟶ B) (a : B ⟶ S) (f : S ⟶ N)
    (i : X ⟶ E) (e : E ⟶ N) (r : N ⟶ R) (s : S ⟶ R)
    {Q : V} (p : X ⟶ Q) (flat : Q ⟶ B)
    (hh : b ≫ a ≫ f = i ≫ e) (hn : f ≫ r = s) (hb : b = p ≫ flat) :
    i ≫ e ≫ r = p ≫ flat ≫ a ≫ s := by
  have h := congrArg (fun k => k ≫ r) hh.symm
  simp only [Category.assoc] at h
  rw [h, hn, hb, Category.assoc]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The actual original raw unit insertion is the original
partition branch insertion/action and original scalar assembly. -/
theorem rightUnitRawInsertion_partition (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    rightUnitRawInsertion O A P =
    (FiniteTensor.tensor (V := C)).map (rightUnitPartitionSourceIso O.toCollection A P).hom ≫
      (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
          (partitionedCoefficientLeavesTriple (rightUnitCoefficientGrouping O.toCollection P)
            (rightUnitLeafBlocks O.toCollection A P))) ≫
      (FiniteTensor.tensor (V := C)).map
        (partitionedCoefficientLeavesActionMap (rightUnitCoefficientGrouping O.toCollection P)
          (rightUnitLeafBlocks O.toCollection A P) (rightUnitPartitionCoefficients O.toCollection P)
          (rightUnitPartitionCoefficientMap O P)) ≫
      (FiniteTensor.flattenIso (V := C)).inv.app
        (partitionedScalarLeaves (rightUnitCoefficientGrouping O.toCollection P)
          (rightUnitLeafBlocks O.toCollection A P) (rightUnitPartitionCoefficients
            O.toCollection P)) ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map (rightUnitScalarFrameIso O.toCollection A P).hom) := by
  let T := FiniteTensor.tensor (V := C)
  let M := FiniteFamily.map T
  let N := rightUnitNestedFactors O.toCollection A P
  let E := partitionedScalarLeaves (rightUnitCoefficientGrouping O.toCollection P)
    (rightUnitLeafBlocks O.toCollection A P) (rightUnitPartitionCoefficients O.toCollection P)
  let b₀ := rightUnitPartitionBranchMap O.toCollection A P
  let a₀ := partitionedCoefficientLeavesActionMap (rightUnitCoefficientGrouping O.toCollection P)
    (rightUnitLeafBlocks O.toCollection A P) (rightUnitPartitionCoefficients O.toCollection P)
    (rightUnitPartitionCoefficientMap O P)
  let e₀ := (rightUnitScalarFrameIso O.toCollection A P).hom
  let i₀ := rightUnitInputFactorMap O A P
  let f₀ := (rightUnitExpandedFactorsIso O.toCollection A P).hom
  have hh₀ : b₀ ≫ a₀ ≫ M.map e₀ = i₀ ≫ f₀ := rightUnitPartitionBranchAction O A P
  have hh : T.map b₀ ≫ T.map a₀ ≫ T.map (M.map e₀) = T.map i₀ ≫ T.map f₀ := by
    exact ((congrArg (T.map b₀ ≫ ·) (T.map_comp _ _).symm).trans (T.map_comp _ _).symm).trans
      ((congrArg T.map hh₀).trans (T.map_comp _ _))
  have hn := (FiniteTensor.flattenIso (V := C)).inv.naturality e₀
  change T.map (M.map e₀) ≫ (FiniteTensor.flattenIso (V := C)).inv.app N =
    (FiniteTensor.flattenIso (V := C)).inv.app E ≫ T.map ((FiniteFamily.flatten (C :=
      C)).map e₀) at hn
  change T.map i₀ ≫ T.map f₀ ≫ (FiniteTensor.flattenIso (V := C)).inv.app N = _
  exact branchInsertionFromTwoSquares (T.map b₀) (T.map a₀) (T.map (M.map e₀))
    (T.map i₀) (T.map f₀) ((FiniteTensor.flattenIso (V := C)).inv.app N)
    ((FiniteTensor.flattenIso (V := C)).inv.app E ≫ T.map ((FiniteFamily.flatten (C := C)).map e₀))
    (T.map (rightUnitPartitionSourceIso O.toCollection A P).hom)
    ((FiniteTensor.flattenIso (V := C)).hom.app
      ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
        (partitionedCoefficientLeavesTriple (rightUnitCoefficientGrouping O.toCollection P)
          (rightUnitLeafBlocks O.toCollection A P))))
    hh hn (rightUnitPartitionBranchAssembly O.toCollection A P)



end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitRawPartition

/- Source proof segment: RightUnitDistributionSource -/
section source_RightUnitDistributionSource
/-!
# Original right-unit scalar distribution source

The original partition scalar frame followed by the original raw
substitution regrouping is the same coefficient/leaf family map.
All original unary leaves and source coefficient maps are retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

/-- The original scalar partition grouping has precisely the
original right-unit coefficient and leaf reindexings. -/
theorem rightUnitDistribution_source (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (FiniteFamily.flatten (C := C)).map (rightUnitScalarFrameIso O A P).hom ≫
      (substitutionToLeavesIso O A (ColoredSubstitutionData.rightUnit P.toColoredProfile)).hom =
    (partitionedScalarLeavesIso (rightUnitCoefficientGrouping O P) (rightUnitLeafBlocks O A P)
        (rightUnitPartitionCoefficients O P)).hom ≫
      (FiniteFamily.flatten (C := C)).map
        (coefficientLeavesNestedMap (rightUnitPartitionCoefficientIso O P).hom
          (rightUnitPartitionLeafIso O A P).hom) := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro i
    rcases i with ⟨i, j⟩
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => nomatch j
    | some i =>
      cases j with
      | none => rfl
      | some j => cases j; rfl
  · intro i
    rcases i with ⟨i, j⟩
    cases i with
    | none =>
      cases j with
      | none =>
        apply heq_of_eq
        exact (show (𝟙 (O.obj P.toColoredProfile)) ≫ ((𝟙 _) ≫ ((𝟙 _) ≫ 𝟙 _)) =
          (𝟙 _) ≫ 𝟙 _ from by simp only [Category.id_comp])
      | some j => nomatch j
    | some i =>
      cases j with
      | none =>
        apply heq_of_eq
        exact (show (𝟙 (O.obj (ColoredSubstitutionData.unitProfile (P.inputColor i)))) ≫
          ((𝟙 _) ≫ ((𝟙 _) ≫ 𝟙 _)) = (𝟙 _) ≫ 𝟙 _ from by simp only [Category.id_comp])
      | some j =>
        cases j
        apply heq_of_eq
        exact (show (𝟙 (A (P.inputColor i))) ≫ ((𝟙 _) ≫ ((𝟙 _) ≫ 𝟙 _)) =
          (𝟙 _) ≫ 𝟙 _ from by simp only [Category.id_comp])



end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitDistributionSource

/- Source proof segment: RightUnitScalarSubstitution -/
section source_RightUnitScalarSubstitution
/-!
# Original operadic substitution on the actual right-unit scalar frame
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- Complete original scalar-frame substitution retains the original
right-unit coefficient substitution and original total leaf bijection. -/
theorem rightUnitScalarSubstitution (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    ((FiniteTensor.flattenIso (V := C)).inv.app
        (partitionedScalarLeaves (rightUnitCoefficientGrouping O.toCollection P)
          (rightUnitLeafBlocks O.toCollection A P) (rightUnitPartitionCoefficients
            O.toCollection P)) ≫
      (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map (rightUnitScalarFrameIso O.toCollection A P).hom)) ≫
      operadSubstitutionInputs O A (ColoredSubstitutionData.rightUnit P.toColoredProfile) =
    (partitionedScalarLeavesDistributionIso (rightUnitCoefficientGrouping O.toCollection P)
        (rightUnitLeafBlocks O.toCollection A P) (rightUnitPartitionCoefficients
          O.toCollection P)).hom ≫
      (FiniteTensor.tensor (V := C)).map
        (coefficientLeafMap
          ((FiniteTensor.tensor (V := C)).map (rightUnitPartitionCoefficientIso
            O.toCollection P).hom ≫
            O.subst.app (ColoredSubstitutionData.rightUnit P.toColoredProfile))
          (rightUnitPartitionLeafIso O.toCollection A P).hom) ≫
      (profileCoefficientLeafTensorIso O.toCollection A
        (ColoredSubstitutionData.rightUnit P.toColoredProfile).totalProfile).hom := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let N := rightUnitCoefficientGrouping O.toCollection P
  let L := rightUnitLeafBlocks O.toCollection A P
  let B := rightUnitPartitionCoefficients O.toCollection P
  let E := partitionedScalarLeaves N L B
  let L' := partitionedLeafFamily N L
  let C' := partitionedScalarCoefficients N B
  let C'' := (ColoredOperadObj.substitutionFactors O.toCollection).obj
    (ColoredSubstitutionData.rightUnit P.toColoredProfile)
  let r := (FiniteTensor.flattenIso (V := C)).inv.app E
  let q₀ := F.map (rightUnitScalarFrameIso O.toCollection A P).hom
  let u₀ := (substitutionToLeavesIso O.toCollection A (ColoredSubstitutionData.rightUnit
    P.toColoredProfile)).hom
  let v₀ := (partitionedScalarLeavesIso N L B).hom
  let k := (rightUnitPartitionCoefficientIso O.toCollection P).hom
  let l := (rightUnitPartitionLeafIso O.toCollection A P).hom
  let j₀ := F.map (coefficientLeavesNestedMap k l)
  let q := T.map q₀
  let u := T.map u₀
  let v := T.map v₀
  let j := T.map j₀
  let nA := coefficientLeavesNormalization C''
    (profileLeafFamily A (ColoredSubstitutionData.rightUnit P.toColoredProfile).totalProfile)
  let nB := coefficientLeavesNormalization C' L'
  let z₀ := coefficientLeafMap (T.map k) l
  let z := T.map z₀
  let γ := O.subst.app (ColoredSubstitutionData.rightUnit P.toColoredProfile)
  let g₀ := (coefficientLeafFamilyFunctor
    (profileLeafFamily A (ColoredSubstitutionData.rightUnit P.toColoredProfile).totalProfile)).map γ
  let g := T.map g₀
  let h := T.map (coefficientLeafMap (T.map k ≫ γ) l)
  let p := (profileCoefficientLeafTensorIso O.toCollection A
    (ColoredSubstitutionData.rightUnit P.toColoredProfile).totalProfile).hom
  let op := operadSubstitutionInputs O A (ColoredSubstitutionData.rightUnit P.toColoredProfile)
  have ho : op = u ≫ nA ≫ g ≫ p :=
    operadSubstitutionInputs_profile_factorization O A (ColoredSubstitutionData.rightUnit
      P.toColoredProfile)
  have hs₀ : q₀ ≫ u₀ = v₀ ≫ j₀ := rightUnitDistribution_source O.toCollection A P
  have hs : q ≫ u = v ≫ j :=
    (T.map_comp _ _).symm.trans ((congrArg T.map hs₀).trans (T.map_comp _ _))
  have hn : j ≫ nA = nB ≫ z := coefficientLeavesNormalization_naturality k l
  have hg₀ : z₀ ≫ g₀ = coefficientLeafMap (T.map k ≫ γ) l := coefficientLeafMap_post _ _ _
  have hg : z ≫ g = h := (T.map_comp _ _).symm.trans (congrArg T.map hg₀)
  rw [partitionedScalarLeavesDistributionIso_hom]
  exact factorFullOperationFromSourceSquares r q u v j nA nB z g h p op ho hs hn hg



end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitScalarSubstitution

/- Source proof segment: RightUnitTensorFactorization -/
section source_RightUnitTensorFactorization
/-!
# Complete right-unit tensor substitution coefficient factorization
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

private theorem postcomposeBranchEquation {V : Type*} [Category* V]
    {X Z A B S Y P Q D : V}
    (source : X ⟶ Z) (raw : X ⟶ S) (op : S ⟶ Y)
    (a : Z ⟶ A) (b : A ⟶ B) (assembly : B ⟶ S)
    (p : Z ⟶ P) (n : P ⟶ Q) (c : Q ⟶ D) (target : D ⟶ Y)
    (hr : raw = source ≫ a ≫ b ≫ assembly)
    (h : a ≫ b ≫ assembly ≫ op = p ≫ n ≫ c ≫ target) :
    raw ≫ op = source ≫ p ≫ n ≫ c ≫ target := by
  rw [hr]
  simp only [Category.assoc]
  rw [h]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original source coefficient route contains the original
outer coefficient unitor, every original input unit, and O.subst. -/
def rightUnitFullCoefficientRoute (O : ColoredOperadObj W C) {d : W} (P : AnalyticIndex W d) :
    (FiniteTensor.tensor (V := C)).obj
      ((FiniteFamily.flatten (C := C)).obj (rightUnitCoefficientGrouping O.toCollection P)) ⟶
        O.toCollection.obj (ColoredSubstitutionData.rightUnit P.toColoredProfile).totalProfile :=
  (FiniteTensor.flattenIso (V := C)).hom.app (rightUnitCoefficientGrouping O.toCollection P) ≫
    (FiniteTensor.tensor (V := C)).map (rightUnitCoefficientFactorMap O P) ≫
      O.subst.app (ColoredSubstitutionData.rightUnit P.toColoredProfile)

/-- Full original right-unit input substitution is exactly its
original coefficient route and every original retained input leaf. -/
theorem rightUnitTensor_factorization (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    rightUnitRawInsertion O A P ≫
      operadSubstitutionInputs O A (ColoredSubstitutionData.rightUnit P.toColoredProfile) =
    (FiniteTensor.tensor (V := C)).map (rightUnitPartitionSourceIso O.toCollection A P).hom ≫
      (FiniteTensor.tensor (V := C)).map
        (partitionedCoefficientLeavesSourceIso (rightUnitCoefficientGrouping O.toCollection P)
          (rightUnitLeafBlocks O.toCollection A P)).hom ≫
      coefficientLeavesNormalization
        ((FiniteFamily.flatten (C := C)).obj (rightUnitCoefficientGrouping O.toCollection P))
        (partitionedLeafFamily (rightUnitCoefficientGrouping O.toCollection P)
          (rightUnitLeafBlocks O.toCollection A P))
          ≫
      (FiniteTensor.tensor (V := C)).map
        (coefficientLeafMap (rightUnitFullCoefficientRoute O P) (rightUnitPartitionLeafIso
          O.toCollection A P).hom) ≫
      (profileCoefficientLeafTensorIso O.toCollection A
        (ColoredSubstitutionData.rightUnit P.toColoredProfile).totalProfile).hom := by
  let T := FiniteTensor.tensor (V := C)
  let N := rightUnitCoefficientGrouping O.toCollection P
  let L := rightUnitLeafBlocks O.toCollection A P
  let B := rightUnitPartitionCoefficients O.toCollection P
  let g := rightUnitPartitionCoefficientMap O P
  let coeffFirst := (FiniteTensor.flattenIso (V := C)).hom.app N ≫
    T.map (partitionedCoefficientMap N B g)
  let p := T.map (partitionedCoefficientLeavesSourceIso N L).hom
  let n := coefficientLeavesNormalization ((FiniteFamily.flatten (C :=
    C)).obj N) (partitionedLeafFamily N L)
  let u := (coefficientLeafTensorFunctor (partitionedLeafFamily N L)).map coeffFirst
  let a := (FiniteTensor.flattenIso (V := C)).hom.app
    ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
      (partitionedCoefficientLeavesTriple N L))
  let b := T.map (partitionedCoefficientLeavesActionMap N L B g)
  let dist := (partitionedScalarLeavesDistributionIso N L B).hom
  let assembly := (FiniteTensor.flattenIso (V := C)).inv.app (partitionedScalarLeaves N L B) ≫
    T.map ((FiniteFamily.flatten (C := C)).map (rightUnitScalarFrameIso O.toCollection A P).hom)
  let op := operadSubstitutionInputs O A (ColoredSubstitutionData.rightUnit P.toColoredProfile)
  let coeff := T.map (rightUnitPartitionCoefficientIso O.toCollection P).hom ≫
    O.subst.app (ColoredSubstitutionData.rightUnit P.toColoredProfile)
  let leaf := (rightUnitPartitionLeafIso O.toCollection A P).hom
  let h := T.map (coefficientLeafMap coeff leaf)
  let target := (profileCoefficientLeafTensorIso O.toCollection A
    (ColoredSubstitutionData.rightUnit P.toColoredProfile).totalProfile).hom
  let c := T.map (coefficientLeafMap (rightUnitFullCoefficientRoute O P) leaf)
  have ha : p ≫ n ≫ u = a ≫ b ≫ dist := rightUnitPartition_action O A P
  have ho : assembly ≫ op = dist ≫ h ≫ target := rightUnitScalarSubstitution O A P
  have hroute : coeffFirst ≫ coeff = rightUnitFullCoefficientRoute O P := by
    change (_ ≫ _) ≫ (_ ≫ _) = _
    have hm : T.map (partitionedCoefficientMap N B g) ≫
        T.map (rightUnitPartitionCoefficientIso O.toCollection P).hom =
      T.map (rightUnitCoefficientFactorMap O P) :=
      (T.map_comp _ _).symm.trans (congrArg T.map (rightUnitPartitionCoefficientMap_eq O P))
    exact (Category.assoc _ _ _).trans
      (congrArg ((FiniteTensor.flattenIso (V := C)).hom.app N ≫ ·)
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hm)))
  have hc₀ : (coefficientLeafFamilyFunctor (partitionedLeafFamily N L)).map coeffFirst ≫
      coefficientLeafMap coeff leaf = coefficientLeafMap (rightUnitFullCoefficientRoute O P) leaf :=
    (coefficientLeafMap_pre coeffFirst coeff leaf).trans (congrArg (fun f =>
      coefficientLeafMap f leaf) hroute)
  have hc : u ≫ h = c := (T.map_comp _ _).symm.trans (congrArg T.map hc₀)
  have hs := branchOuterFactorizationFromSquares p n u a b dist assembly op h target c ha ho hc
  exact postcomposeBranchEquation (T.map (rightUnitPartitionSourceIso O.toCollection A P).hom)
    (rightUnitRawInsertion O A P) op a b assembly p n c target
    (rightUnitRawInsertion_partition O A P) hs



end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitTensorFactorization

/- Source proof segment: RightUnitCoefficientEquation -/
section source_RightUnitCoefficientEquation
/-!
# Original right-unit coefficient equation in the source singleton frame
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

private theorem sourceCoefficientUnit {V : Type*} [Category* V]
    {A B C D E F : V} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (d : D ⟶ E) (e : E ⟶ F) :
    ((a ≫ b ≫ c) ≫ d) ≫ e = a ≫ b ≫ (c ≫ d ≫ e) := by
  simp only [Category.assoc]

private theorem isoUnitCancel {V : Type*} [Category* V]
    {X R : V} (e : R ≅ X) (g : R ⟶ X) (h : e.inv ≫ g = 𝟙 X) : g = e.hom := by
  have q := congrArg (fun f => e.hom ≫ f) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id] using q

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The actual original operadic coefficient unit insertion is
the source singleton-to-grouping map followed by O's original factors. -/
theorem rightUnitCoefficientInsertion (O : ColoredOperadObj W C)
    {d : W} (P : AnalyticIndex W d) :
    ColoredOperadObj.rightUnitInsert O.toCollection O.unit P.toColoredProfile ≫
      O.subst.app (ColoredSubstitutionData.rightUnit P.toColoredProfile) =
    (FiniteTensor.singletonIso (V := C)).inv.app (O.toCollection.obj P.toColoredProfile) ≫
      (FiniteTensor.tensor (V := C)).map (rightUnitCoefficientSourceIso O.toCollection P).inv ≫
      rightUnitFullCoefficientRoute O P := by
  rw [rightUnitCoefficientSourceIso_inv]
  change
    (((FiniteTensor.singletonIso (V := C)).inv.app _ ≫
      (FiniteTensor.tensor (V := C)).map _ ≫ (FiniteTensor.flattenIso (V := C)).hom.app _) ≫
      (FiniteTensor.tensor (V := C)).map _) ≫ _ = _
  exact sourceCoefficientUnit _ _ _ _ _

/-- The original operad right-unit axiom, in the source complete
coefficient grouping, collapses to the original singleton coefficient. -/
theorem rightUnitFullCoefficientRoute_total (O : ColoredOperadObj W C)
    {d : W} (P : AnalyticIndex W d) :
    rightUnitFullCoefficientRoute O P ≫
      O.toCollection.map (ColoredSubstitutionData.rightUnitTotalHom P.toColoredProfile) =
    (FiniteTensor.tensor (V := C)).map (rightUnitCoefficientSourceIso O.toCollection P).hom ≫
      (FiniteTensor.singletonIso (V := C)).hom.app (O.toCollection.obj P.toColoredProfile) := by
  let e := (FiniteTensor.tensor (V := C)).mapIso (rightUnitCoefficientSourceIso O.toCollection P) ≪≫
    (FiniteTensor.singletonIso (V := C)).app (O.toCollection.obj P.toColoredProfile)
  let g := rightUnitFullCoefficientRoute O P ≫
    O.toCollection.map (ColoredSubstitutionData.rightUnitTotalHom P.toColoredProfile)
  have hi : e.inv ≫ g = 𝟙 (O.toCollection.obj P.toColoredProfile) := by
    have he : e.inv = (FiniteTensor.singletonIso (V := C)).inv.app (O.toCollection.obj
      P.toColoredProfile) ≫
        (FiniteTensor.tensor (V := C)).map (rightUnitCoefficientSourceIso O.toCollection
          P).inv := rfl
    have hinsert : e.inv ≫ rightUnitFullCoefficientRoute O P =
        ColoredOperadObj.rightUnitInsert O.toCollection O.unit P.toColoredProfile ≫
          O.subst.app (ColoredSubstitutionData.rightUnit P.toColoredProfile) :=
      (congrArg (· ≫ rightUnitFullCoefficientRoute O P) he).trans
        ((Category.assoc _ _ _).trans (rightUnitCoefficientInsertion O P).symm)
    have h := congrArg (fun f => f ≫ O.toCollection.map
      (ColoredSubstitutionData.rightUnitTotalHom P.toColoredProfile)) hinsert
    have hu := O.right_unit P.toColoredProfile
    exact (Category.assoc _ _ _).symm.trans
      (h.trans ((Category.assoc _ _ _).trans hu))
  exact isoUnitCancel e g hi



end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitCoefficientEquation

/- Source proof segment: RightUnitOriginalSource -/
section source_RightUnitOriginalSource
/-!
# Original right-unit coefficient and leaf source collapse
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C]

private theorem rightUnitCoefficientSource_hom (O : ColoredSymmetricCollection W C)
    {d : W} (P : AnalyticIndex W d) :
    ((rightUnitCoefficientSourceIso O P).hom).hom ⟨none, PUnit.unit⟩ =
      𝟙 (O.obj P.toColoredProfile) := by
  change (eqToHom _ ≫ (𝟙 _)) = _
  exact Category.id_comp _

/-- Collapse the exact source coefficient grouping and original
leaf sigma-unit map; the result is the original mapped singleton
family of the coefficient and every original carrier input. -/
theorem rightUnitOriginalSource (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (rightUnitPartitionSourceIso O A P).hom ≫
      (partitionedCoefficientLeavesSourceIso (rightUnitCoefficientGrouping O P)
        (rightUnitLeafBlocks O A P)).hom ≫
      (FiniteFamily.flatten (C := C)).map
        (coefficientLeavesNestedMap (rightUnitCoefficientSourceIso O P).hom
          (rightUnitPartitionLeafIso O A P ≪≫ rightUnitLeafTotalIso A P).hom) ≫
      (FiniteFamily.flatten (C := C)).map
        (singletonCoefficientLeavesIso (O.obj P.toColoredProfile)
          (profileLeafFamily A P.toColoredProfile)).hom ≫
      FiniteFamily.mapSingletonFlattenIso.hom.app
        ((coefficientLeafFamilyFunctor (profileLeafFamily A P.toColoredProfile)).obj (O.obj
          P.toColoredProfile)) ≫
      (profileOperationFactorsIso O A P.toColoredProfile).hom =
        𝟙 ((analyticFactors O A).obj P) := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro i
    cases i <;> rfl
  · intro i
    cases i with
    | none =>
      apply heq_of_eq
      change (𝟙 (O.obj P.toColoredProfile)) ≫ (𝟙 _) ≫
        ((rightUnitCoefficientSourceIso O P).hom.hom ⟨none, PUnit.unit⟩) ≫
        (𝟙 _) ≫ (𝟙 _) ≫ (𝟙 _) = 𝟙 _
      exact (congrArg (fun h => (𝟙 _) ≫ (𝟙 _) ≫ h ≫ (𝟙 _) ≫ (𝟙 _) ≫ (𝟙 _))
        (rightUnitCoefficientSource_hom O P)).trans
          (show (𝟙 (O.obj P.toColoredProfile)) ≫ (𝟙 _) ≫ (𝟙 _) ≫ (𝟙 _) ≫ (𝟙 _) ≫ (𝟙 _) = 𝟙 _ from by
            simp only [Category.id_comp])
    | some i =>
      exact heq_of_eq (show (𝟙 (A (P.inputColor i))) ≫
        ((𝟙 _) ≫ (((𝟙 _) ≫ 𝟙 _) ≫ ((𝟙 _) ≫ ((𝟙 _) ≫ 𝟙 _)))) = 𝟙 _ from by
        simp only [Category.id_comp])

end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitOriginalSource

/- Source proof segment: RightUnitTensorGeometry -/
section source_RightUnitTensorGeometry
/-!
# Full original right-unit tensor geometry
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

private theorem normalizedUnitCollapse {V : Type*} [Category* V]
    {X A B D E Y : V} (p : X ⟶ A) (n : A ⟶ B) (f : B ⟶ D) (h : D ⟶ E)
    (k : A ⟶ Y) (n' : Y ⟶ D) (s : Y ⟶ E)
    (hn : k ≫ n' = n ≫ f) (hh : n' ≫ h = s) :
    p ≫ n ≫ f ≫ h = p ≫ k ≫ s := by
  rw [← Category.assoc n f, ← hn, Category.assoc k n', hh]

private theorem pairSourceAssociation {V : Type*} [Category* V]
    {A B C D E F : V} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E) (e : E ⟶ F) :
    a ≫ b ≫ c ≫ d ≫ e = (a ≫ b) ≫ c ≫ d ≫ e := (Category.assoc _ _ _).symm

private theorem fullOperationPost {V : Type*} [Category* V]
    {X Q N U D E Y : V} (raw : X ⟶ U) (op : U ⟶ D) (out : D ⟶ Y)
    (q : X ⟶ Q) (n : Q ⟶ N) (s : N ⟶ E) (p : E ⟶ D)
    (t : E ⟶ Y) (f : N ⟶ Y)
    (hf : raw ≫ op = q ≫ n ≫ s ≫ p) (hp : p ≫ out = t) (hs : s ≫ t = f) :
    raw ≫ op ≫ out = q ≫ n ≫ f := by
  have h := congrArg (fun z => z ≫ out) hf
  simp only [Category.assoc] at h
  rw [h, hp, hs]

private theorem mapSix {V : Type*} [Category* V] {D : Type*} [Category* D]
    (T : V ⥤ D) {A B C E F G H : V}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (d : E ⟶ F) (e : F ⟶ G) (f : G ⟶ H) :
    T.map a ≫ T.map b ≫ T.map c ≫ T.map d ≫ T.map e ≫ T.map f =
      T.map (a ≫ b ≫ c ≫ d ≫ e ≫ f) := by
  simp only [Functor.map_comp]

private theorem normalizedUnitCollapsePost {V : Type*} [Category* V]
    {X A B D E Y Z : V} (p : X ⟶ A) (n : A ⟶ B) (f : B ⟶ D) (h : D ⟶ E)
    (k : A ⟶ Y) (n' : Y ⟶ D) (s : Y ⟶ E) (target : E ⟶ Z)
    (hn : k ≫ n' = n ≫ f) (hh : n' ≫ h = s) :
    p ≫ n ≫ (f ≫ h) ≫ target = p ≫ k ≫ s ≫ target := by
  have q := congrArg (· ≫ target) (normalizedUnitCollapse p n f h k n' s hn hh)
  simpa only [Category.assoc] using q

private theorem mapSixPairSource {V : Type*} [Category* V] {D : Type*} [Category* D]
    (T : V ⥤ D) {A B C E F G H : V}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (d : E ⟶ F) (e : F ⟶ G) (f : G ⟶ H) :
    (T.map a ≫ T.map b) ≫ T.map c ≫ T.map (d ≫ e) ≫ T.map f =
      T.map (a ≫ b ≫ c ≫ d ≫ e ≫ f) := by
  simp only [Functor.map_comp, Category.assoc]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The source operad's right-unit axiom gives the full tensor
operation identity, retaining every original finite input leaf. -/
theorem rightUnitTensorGeometry (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    rightUnitRawInsertion O A P ≫
      operadSubstitutionInputs O A (tupleSubstitutionShape P (rightUnitProfileTuple P)) ≫
      (operationSummandFunctor O.toCollection A).map
        (ColoredSubstitutionData.rightUnitTotalHom P.toColoredProfile) =
      𝟙 ((analyticSummand O.toCollection A).obj P) := by
  let T := FiniteTensor.tensor (V := C)
  let L := partitionedLeafFamily (rightUnitCoefficientGrouping O.toCollection P)
    (rightUnitLeafBlocks O.toCollection A P)
  let L' := profileLeafFamily A P.toColoredProfile
  let leaf := (rightUnitPartitionLeafIso O.toCollection A P ≪≫ rightUnitLeafTotalIso A P).hom
  let q := T.map (rightUnitPartitionSourceIso O.toCollection A P).hom ≫
    T.map (partitionedCoefficientLeavesSourceIso (rightUnitCoefficientGrouping O.toCollection P)
      (rightUnitLeafBlocks O.toCollection A P)).hom
  let n := coefficientLeavesNormalization
    ((FiniteFamily.flatten (C := C)).obj (rightUnitCoefficientGrouping O.toCollection P)) L
  let f := T.map (coefficientLeafMap
    (rightUnitFullCoefficientRoute O P ≫ O.toCollection.map
      (ColoredSubstitutionData.rightUnitTotalHom
      P.toColoredProfile))
    leaf)
  let f' := T.map (coefficientLeafMap
    (T.map (rightUnitCoefficientSourceIso O.toCollection P).hom ≫
      (FiniteTensor.singletonIso (V := C)).hom.app (O.toCollection.obj P.toColoredProfile)) leaf)
  let target := (profileCoefficientLeafTensorIso O.toCollection A P.toColoredProfile).hom
  have hc : f = f' := congrArg (fun z => T.map (coefficientLeafMap z leaf))
    (rightUnitFullCoefficientRoute_total O P)
  have hfactor : rightUnitRawInsertion O A P ≫
      operadSubstitutionInputs O A (tupleSubstitutionShape P (rightUnitProfileTuple P)) ≫
      (operationSummandFunctor O.toCollection A).map
        (ColoredSubstitutionData.rightUnitTotalHom P.toColoredProfile) = q ≫ n ≫ f ≫ target := by
    have hn := profileCoefficientLeafTensorIso_naturality O.toCollection A
      (ColoredSubstitutionData.rightUnitTotalHom P.toColoredProfile)
    have hm := coefficientLeafMap_comp (rightUnitFullCoefficientRoute O P)
      (O.toCollection.map (ColoredSubstitutionData.rightUnitTotalHom P.toColoredProfile))
      (rightUnitPartitionLeafIso O.toCollection A P).hom (rightUnitLeafTotalIso A P).hom
    let s := T.map (coefficientLeafMap (rightUnitFullCoefficientRoute O P)
      (rightUnitPartitionLeafIso O.toCollection A P).hom)
    let t := T.map (coefficientLeafMap
      (O.toCollection.map (ColoredSubstitutionData.rightUnitTotalHom P.toColoredProfile))
      (rightUnitLeafTotalIso A P).hom)
    have hst : s ≫ t = f := (T.map_comp _ _).symm.trans (congrArg T.map hm)
    let p := (profileCoefficientLeafTensorIso O.toCollection A
      (ColoredSubstitutionData.rightUnit P.toColoredProfile).totalProfile).hom
    let out := (operationSummandFunctor O.toCollection A).map
      (ColoredSubstitutionData.rightUnitTotalHom P.toColoredProfile)
    have hp : p ≫ out = t ≫ target := hn
    have hs : s ≫ (t ≫ target) = f ≫ target :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ target) hst)
    change _ = q ≫ n ≫ f ≫ target
    have hf₀ : rightUnitRawInsertion O A P ≫
        operadSubstitutionInputs O A (tupleSubstitutionShape P (rightUnitProfileTuple P)) =
          q ≫ n ≫ s ≫ p :=
      (rightUnitTensor_factorization O A P).trans (pairSourceAssociation _ _ _ _ _)
    exact fullOperationPost (rightUnitRawInsertion O A P)
      (operadSubstitutionInputs O A (tupleSubstitutionShape P (rightUnitProfileTuple P)))
      out q n s p (t ≫ target) (f ≫ target) hf₀ hp hs
  exact hfactor.trans
    ((congrArg (fun z => q ≫ n ≫ z ≫ target) hc).trans
      (by
        let k := T.map ((FiniteFamily.flatten (C := C)).map
          (coefficientLeavesNestedMap (rightUnitCoefficientSourceIso O.toCollection P).hom leaf))
        let n' := coefficientLeavesNormalization ((FiniteFamily.singleton (C := C)).obj
          (O.toCollection.obj P.toColoredProfile)) L'
        let b := T.map (coefficientLeafMap (T.map (rightUnitCoefficientSourceIso
          O.toCollection P).hom) leaf)
        let s := (coefficientLeafTensorFunctor L').map
          ((FiniteTensor.singletonIso (V := C)).hom.app (O.toCollection.obj P.toColoredProfile))
        have hn : k ≫ n' = n ≫ b := rightUnitNormalization_source O.toCollection A P
        have hb : b ≫ s = f' := (T.map_comp _ _).symm.trans
          (congrArg T.map (coefficientLeafMap_post _ _ _))
        have hs := coefficientLeavesNormalization_singleton (O.toCollection.obj
          P.toColoredProfile) L'
        have hi := rightUnitOriginalSource O.toCollection A P
        change q ≫ n ≫ f' ≫ target = _
        have hf := congrArg (fun z => q ≫ n ≫ z ≫ target) hb.symm
        let z := T.map ((FiniteFamily.flatten (C := C)).map
          (singletonCoefficientLeavesIso (O.toCollection.obj P.toColoredProfile) L').hom ≫
            FiniteFamily.mapSingletonFlattenIso.hom.app ((coefficientLeafFamilyFunctor
              L').obj (O.toCollection.obj
              P.toColoredProfile)))
        have hnorm' : q ≫ n ≫ (b ≫ s) ≫ target = q ≫ k ≫ z ≫ target := by
          exact normalizedUnitCollapsePost q n b s k n' z target hn hs
        have hmaps : q ≫ k ≫ z ≫ target = 𝟙 ((analyticSummand O.toCollection A).obj P) := by
          exact (mapSixPairSource T _ _ _ _ _ _).trans ((congrArg T.map hi).trans (T.map_id _))
        exact hf.trans (hnorm'.trans hmaps)))



end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitTensorGeometry

/- Source proof segment: RightUnitInjection -/
section source_RightUnitInjection
/-!
# Original right-unit tensor injections

The original source input unit maps followed by unary profile
injections are the exact right-unit slot-cocone maps. Their original
coefficient singleton unitor and tensor flattening source are retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem inverseInsertion {V : Type*} [Category* V] {X Y Z T : V}
    (a : X ⟶ Y) (e : Z ≅ Y) (b : Y ⟶ T) (i : Z ⟶ T)
    (h : i = e.hom ≫ b) : a ≫ e.inv ≫ i = a ≫ b := by
  rw [h]
  simp only [Iso.inv_hom_id_assoc]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The original right-unit slot values identify with their original
expanded input family, retaining the exact finite input type. -/
def rightUnitSlotFactorsIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (slotInputFactorsFunctor O A P).obj (rightUnitSlotTuple P) ≅ rightUnitExpandedFamily O A P :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option P.inputs))
    (fun i => match i with
      | none => Iso.refl (O.obj P.toColoredProfile)
      | some i => Iso.refl ((analyticSummand O A).obj
          (AnalyticIndex.unary (d := P.inputColor i) (P.inputColor i))))

/-- Identify the selected right-unit slot tensor with the original expanded input family. -/
def rightUnitSlotTensorIso (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (profileSlotTensorDiagram O A P).obj (rightUnitSlotTuple P) ≅
      (FiniteTensor.tensor (V := C)).obj (rightUnitExpandedFamily O A P) :=
  (FiniteTensor.tensor (V := C)).mapIso (rightUnitSlotFactorsIso O A P)

/-- The original unary profile injection at every input is the
actual right-unit tuple injection, with coefficient identity retained. -/
theorem rightUnitSlotInjection (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (profileSlotTensorCocone O A P).ι.app (rightUnitSlotTuple P) =
      (rightUnitSlotTensorIso O A P).hom ≫ (FiniteTensor.tensor (V := C)).map
        ({ equiv := Equiv.refl (Option P.inputs)
           hom i := match i with
             | none => 𝟙 (O.obj P.toColoredProfile)
             | some i => profileι O A (AnalyticIndex.unary (d :=
               P.inputColor i) (P.inputColor i)) } :
          rightUnitExpandedFamily O A P ⟶
            (analyticFactors O (profileCoinvariants O A)).obj P) :=
  by
    symm
    apply Eq.trans ((FiniteTensor.tensor (V := C)).map_comp _ _).symm
    apply congrArg (FiniteTensor.tensor (V := C)).map
    apply FiniteFamily.Hom_ext
    · rfl
    · intro i
      cases i with
      | none => exact heq_of_eq (Category.id_comp _)
      | some i => exact heq_of_eq (Category.id_comp _)

/-- The original color-indexed unit tensor map factors through
the actual right-unit tuple slot injection. -/
theorem rightUnit_profileUnit_input (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (analyticSummandCarrierMap O.toCollection ((profileUnit O).app A)).app P =
      rightUnitInputTensorMap O A P ≫
        (rightUnitSlotTensorIso O.toCollection A P).inv ≫
        (profileSlotTensorCocone O.toCollection A P).ι.app (rightUnitSlotTuple P) :=
  by
    let a := rightUnitInputTensorMap O A P
    let e := rightUnitSlotTensorIso O.toCollection A P
    let i := (profileSlotTensorCocone O.toCollection A P).ι.app (rightUnitSlotTuple P)
    let b := (FiniteTensor.tensor (V := C)).map
      ({ equiv := Equiv.refl (Option P.inputs)
         hom j := match j with
           | none => 𝟙 (O.toCollection.obj P.toColoredProfile)
           | some j => profileι O.toCollection A
               (AnalyticIndex.unary (d := P.inputColor j) (P.inputColor j)) } :
        rightUnitExpandedFamily O.toCollection A P ⟶
          (analyticFactors O.toCollection (profileCoinvariants O.toCollection A)).obj P)
    have h : i = e.hom ≫ b := by
      have hs := rightUnitSlotInjection O.toCollection A P
      change i = e.hom ≫ _ at hs
      apply hs.trans
      apply congrArg (e.hom ≫ ·)
      apply congrArg (FiniteTensor.tensor (V := C)).map
      apply FiniteFamily.Hom_ext
      · rfl
      · intro j
        cases j <;> exact HEq.rfl
    exact (rightUnitInputTensorMap_profileUnit O A P).trans (inverseInsertion a e b i h).symm



end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitInjection

/- Source proof segment: RightUnitBetaAssembly -/
section source_RightUnitBetaAssembly
/-!
# Original right-unit profile tuple assembly readback
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

private theorem inverseFrameComposition {V : Type*} [Category* V]
    {X Y Z R S : V} (a : X ⟶ Y) (e : Z ≅ Y) (f : Y ⟶ R) (r : R ⟶ S) :
    a ≫ e.inv ≫ ((e.hom ≫ f) ≫ r) = a ≫ f ≫ r := by
  simp only [Category.assoc]
  simp only [Iso.inv_hom_id_assoc]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The source coefficient/input frame of the unit tuple equals
the original expanded source frame, with its actual singleton unitor. -/
theorem rightUnitTupleCoefficientFrame (O : ColoredSymmetricCollection W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    (coefficientTensorIso O A P (rightUnitSlotTuple P)).hom =
    (rightUnitSlotFactorsIso O A P).hom ≫ (rightUnitExpandedFactorsIso O A P).hom := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none => exact heq_of_eq (Category.id_comp _).symm
    | some i => exact heq_of_eq (Category.id_comp _).symm

/-- Actual original right-unit tuple assembly after the original
input-unit tensor recovers precisely the original raw insertion. -/
theorem rightUnitTupleAssembly (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) :
    rightUnitInputTensorMap O A P ≫ (rightUnitSlotTensorIso O.toCollection A P).inv ≫
      profileSubstitutionAssemblyMap O.toCollection A P (rightUnitSlotTuple P) =
    rightUnitRawInsertion O A P := by
  let T := FiniteTensor.tensor (V := C)
  let a := rightUnitInputTensorMap O A P
  let e := rightUnitSlotTensorIso O.toCollection A P
  let f := T.map (rightUnitExpandedFactorsIso O.toCollection A P).hom
  let r := (FiniteTensor.flattenIso (V := C)).inv.app (rightUnitNestedFactors O.toCollection A P)
  have h : T.map (coefficientTensorIso O.toCollection A P (rightUnitSlotTuple P)).hom = e.hom ≫ f :=
    (congrArg T.map (rightUnitTupleCoefficientFrame O.toCollection A P)).trans (T.map_comp _ _)
  change a ≫ e.inv ≫ (T.map (coefficientTensorIso O.toCollection A P (rightUnitSlotTuple
    P)).hom ≫ r) = a ≫ f ≫ r
  exact (congrArg (a ≫ e.inv ≫ ·) (congrArg (· ≫ r) h)).trans
    (inverseFrameComposition a e f r)



end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitBetaAssembly

/- Source proof segment: RightUnitMonadLaw -/
section source_RightUnitMonadLaw
/-!
# Actual tensor-profile monad right-unit law
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem rightUnitDescent {V : Type*} [Category* V]
    {X T U S R Z Y : V} (i : X ⟶ T) (f : T ⟶ U) (μ : U ⟶ T)
    (h : X ⟶ S) (j : S ⟶ U) (a : X ⟶ R) (slot : R ⟶ S)
    (assembly : R ⟶ Z) (op : Z ⟶ Y) (ι : Y ⟶ T)
    (total : Y ⟶ X) (raw : X ⟶ Z)
    (hi : i ≫ f = h ≫ j) (hh : h = a ≫ slot)
    (hβ : slot ≫ j ≫ μ = assembly ≫ op ≫ ι)
    (ha : a ≫ assembly = raw) (hι : total ≫ i = ι)
    (hu : raw ≫ op ≫ total = 𝟙 X) : i ≫ (f ≫ μ) = i := by
  rw [← Category.assoc i f, hi, hh]
  simp only [Category.assoc]
  rw [hβ, ← Category.assoc a assembly, ha, ← hι]
  have h := congrArg (· ≫ i) hu
  simpa only [Category.assoc, Category.id_comp] using h

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- The actual profile tensor functor's unit on every input,
followed by the constructed multiplication, is the identity. -/
theorem profileMultiplication_right_unit (O : ColoredOperadObj W C) (A : W → C) :
    profileMap O.toCollection ((profileUnit O).app A) ≫ profileMultiplication O A =
      𝟙 (profileCoinvariants O.toCollection A) := by
  funext d
  apply colimit.hom_ext
  intro P
  let i := profileι O.toCollection A P
  let f := profileMap O.toCollection ((profileUnit O).app A) d
  let μ := profileMultiplication O A d
  let h := (analyticSummandCarrierMap O.toCollection ((profileUnit O).app A)).app P
  let j := profileι O.toCollection (profileCoinvariants O.toCollection A) P
  let a := rightUnitInputTensorMap O A P ≫ (rightUnitSlotTensorIso O.toCollection A P).inv
  let slot := (profileSlotTensorCocone O.toCollection A P).ι.app (rightUnitSlotTuple P)
  let assembly := profileSubstitutionAssemblyMap O.toCollection A P (rightUnitSlotTuple P)
  let op := operadSubstitutionInputs O A (tupleSubstitutionShape P (rightUnitProfileTuple P))
  let ι := profileι O.toCollection A ((tupleTotalFunctor P).obj (rightUnitProfileTuple P))
  let total := (operationSummandFunctor O.toCollection A).map
    (ColoredSubstitutionData.rightUnitTotalHom P.toColoredProfile)
  have hβ : slot ≫ j ≫ μ = assembly ≫ op ≫ ι := profileMultiplication_right_unit_slot O A P
  have ha : a ≫ assembly = rightUnitRawInsertion O A P :=
    (Category.assoc _ _ _).trans (rightUnitTupleAssembly O A P)
  have hι : total ≫ i = ι := by
    have h := profile_relabel_ι O.toCollection A (rightUnitTupleTotalHom P)
    have hm := operationFactorsFunctor_map_restrict O.toCollection A (rightUnitTupleTotalHom P)
    exact (congrArg (· ≫ i) (congrArg (FiniteTensor.tensor (V := C)).map hm)).trans h
  have hh : h = a ≫ slot :=
    (rightUnit_profileUnit_input O A P).trans (Category.assoc _ _ _).symm
  change i ≫ (f ≫ μ) = i ≫ 𝟙 _
  exact (rightUnitDescent i f μ h j a slot assembly op ι total (rightUnitRawInsertion O A P)
    (profileι_map O.toCollection ((profileUnit O).app A) P)
    hh hβ ha hι (rightUnitTensorGeometry O A P)).trans
    (Category.comp_id _).symm



end CategoryTheory.Operad.Tensor
end
end
end source_RightUnitMonadLaw

/- Source proof segment: TensorProfileMonad -/
section source_TensorProfileMonad
/-!
# Actual colored tensor-operadic free algebra and monad
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- The actual profile-coinvariant tensor free algebra carries
every constructed original profile operation, with both its
unit and full substitution laws proved from the source operad. -/
def freeAlgebra (O : ColoredOperadObj W C) (A : W → C) : Algebra O where
  carrier := profileCoinvariants O.toCollection A
  operations := freeOperations O A
  unit d := by
    let i := unitInsertion O (profileCoinvariants O.toCollection A) d
    let p := profileι O.toCollection (profileCoinvariants O.toCollection A)
      (AnalyticIndex.unary (d := d) d)
    let μ := profileMultiplication O A d
    have h := congrFun (profileMultiplication_left_unit O A) d
    have hβ : p ≫ μ = freeOperation O A (AnalyticIndex.unary (d := d) d) :=
      profileMultiplication_profile O A _
    change i ≫ freeOperation O A (AnalyticIndex.unary (d := d) d) = _
    exact (congrArg (i ≫ ·) hβ.symm).trans ((Category.assoc _ _ _).symm.trans h)
  substitution := freeOperations_substitution O A

/-- Descending all original operations of the constructed free
algebra is precisely the original profile multiplication. -/
@[simp]
theorem freeAlgebra_action (O : ColoredOperadObj W C) (A : W → C) :
    (freeAlgebra O A).action = profileMultiplication O A := rfl

/-- The original full operation substitution law implies actual
associativity of the constructed profile multiplication. -/
theorem profileMultiplication_assoc (O : ColoredOperadObj W C) (A : W → C) :
    profileMap O.toCollection (profileMultiplication O A) ≫ profileMultiplication O A =
      profileMultiplication O (profileCoinvariants O.toCollection A) ≫
        profileMultiplication O A := by
  have h := (freeAlgebra O A).action_assoc
  rw [freeAlgebra_action] at h
  exact h.symm

/-- The original tensor profile coinvariants, operadic units and
actual operadic substitution form the actual colored tensor monad.
All three laws are derived from the original operad and tensor
colimit constructions, including nullary profiles. -/
def profileMonad (O : ColoredOperadObj W C) : Monad (W → C) where
  toFunctor := profileEndofunctor O.toCollection
  η := profileUnit O
  μ := profileMultiplicationNatTrans O
  assoc := profileMultiplication_assoc O
  left_unit := profileMultiplication_left_unit O
  right_unit := profileMultiplication_right_unit O

/-- The actual monad carrier functor is exactly the original
operation-weighted profile coinvariant functor. -/
@[simp]
theorem profileMonad_toFunctor (O : ColoredOperadObj W C) :
    (profileMonad O).toFunctor = profileEndofunctor O.toCollection := rfl

/-- The monad's unit at each original color is the original
unary coefficient unit insertion and original unary profile injection. -/
@[simp]
theorem profileMonad_unit (O : ColoredOperadObj W C) (A : W → C) (d : W) :
    (profileMonad O).η.app A d = unitInsertion O A d ≫
      profileι O.toCollection A (AnalyticIndex.unary (d := d) d) := rfl

/-- Every original coefficient/input tuple evaluates the actual
monad multiplication by original operad substitution and profile injection. -/
theorem profileMonad_multiplication_slot (O : ColoredOperadObj W C) (A : W → C)
    {d : W} (P : AnalyticIndex W d) (Q : ProfileSlotTuple P) :
    (profileSlotTensorCocone O.toCollection A P).ι.app Q ≫
      profileι O.toCollection (profileCoinvariants O.toCollection A) P ≫
        (profileMonad O).μ.app A d =
    (assembledProfileSubstitutionCocone O A P).ι.app Q := profileMultiplication_slot O A P Q

/-- Actual free algebras are functorial in every original carrier
map, using the original profile map and proved multiplication naturality. -/
def freeAlgebraFunctor (O : ColoredOperadObj W C) : (W → C) ⥤ Algebra O where
  obj := freeAlgebra O
  map f := Algebra.Hom.ofActionEquation _ _ (profileMap O.toCollection f)
    (profileMultiplication_input O f)
  map_id A := by
    apply Algebra.Hom.ext
    exact profileMap_id O.toCollection A
  map_comp f g := by
    apply Algebra.Hom.ext
    exact profileMap_comp O.toCollection f g




end CategoryTheory.Operad.Tensor
end
end
end source_TensorProfileMonad

/- Source proof segment: OperationActionComparison -/
section source_OperationActionComparison
/-!
# Original tensor operation substitution and actual profile action equations
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem inverseAssemblyEvaluation {V : Type*} [Category* V]
    {X S P Q Y : V} (e : X ≅ S) (slot : X ⟶ P) (input : P ⟶ Q) (outer : Q ⟶ Y)
    (inner : S ⟶ Y) (h : slot ≫ input ≫ outer = e.hom ≫ inner) :
    (e.inv ≫ slot) ≫ input ≫ outer = inner := by
  simp only [Category.assoc]
  rw [h, Iso.inv_hom_id_assoc]

private theorem actionAssocSource {V : Type*} [Category* V]
    {X T U P Q R Y : V} (j : X ⟶ T) (i : T ⟶ U) (μ tκ : U ⟶ P) (κ : P ⟶ Y)
    (free : T ⟶ P) (op : X ⟶ Q) (totalι : Q ⟶ P) (carrier : T ⟶ R)
    (outer : R ⟶ Y) (inner : X ⟶ Y) (eval : Q ⟶ Y)
    (hμ : i ≫ μ = free) (hβ : j ≫ free = op ≫ totalι)
    (htκ : i ≫ tκ ≫ κ = carrier ≫ outer) (hin : j ≫ carrier ≫ outer = inner)
    (heval : totalι ≫ κ = eval)
    (h : j ≫ i ≫ (μ ≫ κ) = j ≫ i ≫ (tκ ≫ κ)) : inner = op ≫ eval := by
  have hleft : j ≫ i ≫ (μ ≫ κ) = op ≫ eval := by
    rw [← Category.assoc i μ, hμ, ← Category.assoc j free, hβ]
    simp only [Category.assoc]
    rw [heval]
  have hright : j ≫ i ≫ (tκ ≫ κ) = inner :=
    (congrArg (j ≫ ·) htκ).trans hin
  exact hright.symm.trans (h.symm.trans hleft)

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- Associativity of an individual original descended profile action
implies the original full tensor operation substitution law. The
actual constructed μ is used; no monad structure is an input. -/
theorem Operations.substitution_of_desc_assoc {O : ColoredOperadObj W C} {A : W → C}
    (a : Operations O.toCollection A A)
    (hassoc : profileMultiplication O A ≫ a.desc = profileMap O.toCollection a.desc ≫ a.desc)
    (s : ColoredSubstitutionData W) :
    algebraSubstitutionInner a s = operadSubstitutionInputs O A s ≫
      a.app s.outputColor (profileInputs s.totalProfile)
      := by
  let P := profileInputs s.outerProfile
  let Q := operationSlotTuple s
  let e := (profileSlotAssemblyIso O.toCollection A P).app Q
  let slot := (profileSlotTensorCocone O.toCollection A P).ι.app Q
  let j := (rawSubstitutionCocone O.toCollection A P).ι.app Q
  let i := profileι O.toCollection (profileCoinvariants O.toCollection A) P
  let μ := profileMultiplication O A s.outputColor
  let κ := a.desc s.outputColor
  let tκ := profileMap O.toCollection a.desc s.outputColor
  let carrier := (analyticSummandCarrierMap O.toCollection a.desc).app P
  let outer := a.app s.outputColor P
  let inner := algebraSubstitutionInner a s
  let op := operadSubstitutionInputs O A s
  let totalι := profileι O.toCollection A (profileInputs s.totalProfile)
  have hμ : i ≫ μ = freeOperation O A P := profileMultiplication_profile O A P
  have hβ : j ≫ freeOperation O A P = op ≫ totalι := by
    have h := rawSubstitutionCocone_freeOperation O A P Q
    with_unfolding_all exact h
  have htκ : i ≫ tκ ≫ κ = carrier ≫ outer := by
    have h := profileι_map O.toCollection a.desc P
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ κ) h).trans ((Category.assoc _ _ _).trans (congrArg (carrier ≫
        ·) (a.ι_desc P))))
  have hin : j ≫ carrier ≫ outer = inner := by
    have h := a.slotDescAssembly P Q
    have h' : slot ≫ carrier ≫ outer = e.hom ≫ inner := by
      with_unfolding_all exact h
    exact inverseAssemblyEvaluation e slot carrier outer inner h'
  have h := congrArg (fun f => j ≫ i ≫ f s.outputColor) hassoc
  change j ≫ i ≫ (μ ≫ κ) = j ≫ i ≫ (tκ ≫ κ) at h
  exact actionAssocSource j i μ tκ κ (freeOperation O A P) op totalι carrier outer inner
    (a.app s.outputColor (profileInputs s.totalProfile)) hμ hβ htκ hin (a.ι_desc _) h



end CategoryTheory.Operad.Tensor
end
end
end source_OperationActionComparison

/- Source proof segment: AlgebraFromAction -/
section source_AlgebraFromAction
/-!
# Original tensor algebras constructed from actual profile action maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

omit [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
    [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C] in
/-- Original tensor algebras are determined by their original
color-indexed carriers and every original operation map. -/
theorem Algebra.ext_carrier_operations {O : ColoredOperadObj W C} {A B : Algebra O}
    (hc : A.carrier = B.carrier) (ha : HEq A.operations B.operations) : A = B := by
  cases A with
  | mk A a hu hs =>
    cases B with
    | mk B b ku ks =>
      cases hc
      have h : a = b := eq_of_heq ha
      cases h
      rfl

/-- Construct every original tensor operation from an actual
profile action satisfying its individual unit and multiplication
equations. No monad structure or categorical outcome is an input. -/
def Algebra.ofAction (O : ColoredOperadObj W C) (A : W → C)
    (κ : profileCoinvariants O.toCollection A ⟶ A)
    (hunit : (profileUnit O).app A ≫ κ = 𝟙 A)
    (hassoc : profileMultiplication O A ≫ κ = profileMap O.toCollection κ ≫ κ) : Algebra O where
  carrier := A
  operations := operationsEquiv O.toCollection A A κ
  unit d := by
    have h := congrFun hunit d
    change unitInsertion O A d ≫ (profileι O.toCollection A (AnalyticIndex.unary d) ≫ κ d) = _
    exact (Category.assoc _ _ _).symm.trans h
  substitution s := by
    let a := operationsEquiv O.toCollection A A κ
    have hdesc : a.desc = κ := (operationsEquiv O.toCollection A A).symm_apply_apply κ
    have h : profileMultiplication O A ≫ a.desc = profileMap O.toCollection a.desc ≫ a.desc := by
      rw [hdesc]
      exact hassoc
    exact a.substitution_of_desc_assoc h s

/-- The action constructor recovers the original full-profile
tensor operation map at every actual profile, including nullary ones. -/
@[simp]
theorem Algebra.ofAction_operation (O : ColoredOperadObj W C) (A : W → C)
    (κ : profileCoinvariants O.toCollection A ⟶ A)
    (hu : (profileUnit O).app A ≫ κ = 𝟙 A)
    (ha : profileMultiplication O A ≫ κ = profileMap O.toCollection κ ≫ κ)
    (d : W) (P : AnalyticIndex W d) :
    (Algebra.ofAction O A κ hu ha).operations.app d P = profileι O.toCollection A P ≫ κ d := rfl

/-- Descending all original operation maps of the action constructor
returns precisely the original given profile action. -/
@[simp]
theorem Algebra.ofAction_action (O : ColoredOperadObj W C) (A : W → C)
    (κ : profileCoinvariants O.toCollection A ⟶ A)
    (hu : (profileUnit O).app A ≫ κ = 𝟙 A)
    (ha : profileMultiplication O A ≫ κ = profileMap O.toCollection κ ≫ κ) :
    (Algebra.ofAction O A κ hu ha).action = κ :=
  (operationsEquiv O.toCollection A A).symm_apply_apply κ

/-- The individual actual action and original tensor operations
are inverse constructions on every original tensor algebra. -/
@[simp]
theorem Algebra.ofAction_action_self {O : ColoredOperadObj W C} (B : Algebra O) :
    Algebra.ofAction O B.carrier B.action B.action_unit B.action_assoc = B := by
  apply Algebra.ext_carrier_operations
    (A := Algebra.ofAction O B.carrier B.action B.action_unit B.action_assoc) (B := B) rfl
  exact heq_of_eq ((operationsEquiv O.toCollection B.carrier B.carrier).apply_symm_apply
    B.operations)




end CategoryTheory.Operad.Tensor
end
end
end source_AlgebraFromAction

/- Source proof segment: TensorAlgebraEM -/
section source_TensorAlgebraEM
/-!
# Actual original tensor-operadic algebras and Eilenberg–Moore algebras
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- Descend every original tensor algebra operation and operation
square to the actual Eilenberg–Moore algebra and algebra map. -/
def tensorAlgebraToEM (O : ColoredOperadObj W C) : Algebra O ⥤ Monad.Algebra (profileMonad O) where
  obj B :=
    { A := B.carrier
      a := B.action
      unit := B.action_unit
      assoc := B.action_assoc }
  map f :=
    { f := f.hom
      h := (Algebra.action_naturality f).symm }

/-- Recover every original tensor operation and full operation
square from an actual Eilenberg–Moore action and algebra map. -/
def emToTensorAlgebra (O : ColoredOperadObj W C) : Monad.Algebra (profileMonad O) ⥤ Algebra O where
  obj B := Algebra.ofAction O B.A B.a B.unit B.assoc
  map {A B} f := Algebra.Hom.ofActionEquation _ _ f.f (by
    exact (congrArg (fun k => profileMap O.toCollection f.f ≫ k)
      (Algebra.ofAction_action O B.A B.a B.unit B.assoc)).trans
      (f.h.trans (congrArg (fun k => k ≫ f.f)
        (Algebra.ofAction_action O A.A A.a A.unit A.assoc).symm)))
  map_id B := Algebra.Hom.ext rfl
  map_comp f g := Algebra.Hom.ext rfl

/-- Both actual conversions have the original carrier and every
original carrier-map component exactly as their forgetful functors. -/
theorem tensorAlgebraToEM_forget (O : ColoredOperadObj W C) :
    tensorAlgebraToEM O ⋙ Monad.forget (profileMonad O) = Algebra.forget O := by
  exact Functor.ext (fun _ => rfl) (fun A B f =>
    (Category.id_comp f.hom).symm.trans (congrArg (𝟙 _ ≫ ·) (Category.comp_id f.hom).symm))

/-- The explicit inverse conversion leaves the original carrier
and every original carrier-map component exactly as supplied. -/
theorem emToTensorAlgebra_forget (O : ColoredOperadObj W C) :
    emToTensorAlgebra O ⋙ Algebra.forget O = Monad.forget (profileMonad O) := by
  exact Functor.ext (fun _ => rfl) (fun A B f =>
    (Category.id_comp f.f).symm.trans (congrArg (𝟙 _ ≫ ·) (Category.comp_id f.f).symm))

/-- The actual unit comparison is the inverse operation/action
construction on the original tensor algebra category. -/
def tensorAlgebraEMUnitIso (O : ColoredOperadObj W C) :
    𝟭 (Algebra O) ≅ tensorAlgebraToEM O ⋙ emToTensorAlgebra O :=
  NatIso.ofComponents (fun B => eqToIso (Algebra.ofAction_action_self B).symm) (by
    intro A B f
    apply (Algebra.forget O).map_injective
    rw [Functor.map_comp, Functor.map_comp]
    have hA : (Algebra.forget O).map (eqToIso (Algebra.ofAction_action_self A).symm).hom =
      𝟙 A.carrier :=
      (eqToHom_map (Algebra.forget O) (Algebra.ofAction_action_self A).symm).trans
        (eqToHom_refl A.carrier _)
    have hB : (Algebra.forget O).map (eqToIso (Algebra.ofAction_action_self B).symm).hom =
      𝟙 B.carrier :=
      (eqToHom_map (Algebra.forget O) (Algebra.ofAction_action_self B).symm).trans
        (eqToHom_refl B.carrier _)
    exact (congrArg (f.hom ≫ ·) hB).trans
      ((Category.comp_id _).trans ((Category.id_comp _).symm.trans
        (congrArg (· ≫ f.hom) hA.symm))))

/-- Recovering all original operations and descending them gives
the original Eilenberg–Moore action, through its actual carrier identity. -/
def tensorAlgebraEMCounitIso (O : ColoredOperadObj W C) :
    emToTensorAlgebra O ⋙ tensorAlgebraToEM O ≅ 𝟭 (Monad.Algebra (profileMonad O)) :=
  NatIso.ofComponents (fun B => Monad.Algebra.isoMk (Iso.refl B.A) (by
    change profileMap O.toCollection (𝟙 B.A) ≫ B.a =
      (Algebra.ofAction O B.A B.a B.unit B.assoc).action ≫ 𝟙 B.A
    exact (congrArg (· ≫ B.a) (profileMap_id O.toCollection B.A)).trans
      ((Category.id_comp _).trans ((Algebra.ofAction_action O B.A B.a B.unit B.assoc).symm.trans
        (Category.comp_id _).symm)))) (by
      intro A B f
      apply (Monad.forget (profileMonad O)).map_injective
      change f.f ≫ 𝟙 _ = 𝟙 _ ≫ f.f
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The actual profile-coinvariant monad's Eilenberg–Moore category
is the original tensor operadic algebra category, with explicit
forward/inverse object and morphism maps and proved natural inverse isos. -/
def tensorAlgebraEMEquivalence (O : ColoredOperadObj W C) :
    Algebra O ≌ Monad.Algebra (profileMonad O) :=
  Equivalence.mk (tensorAlgebraToEM O) (emToTensorAlgebra O)
    (tensorAlgebraEMUnitIso O) (tensorAlgebraEMCounitIso O)

/-- Every original tensor operation is recovered from the
actual Eilenberg–Moore action and original profile quotient injection. -/
@[simp]
theorem emToTensorAlgebra_operation (O : ColoredOperadObj W C)
    (B : Monad.Algebra (profileMonad O)) (d : W) (P : AnalyticIndex W d) :
    ((emToTensorAlgebra O).obj B).operations.app d P = profileι O.toCollection B.A P ≫ B.a d := rfl

/-- The forward comparison has exactly the original carrier-map
components, including every original color. -/
@[simp]
theorem tensorAlgebraToEM_map (O : ColoredOperadObj W C) {A B : Algebra O} (f : A ⟶ B) :
    ((tensorAlgebraToEM O).map f).f = f.hom := rfl

/-- The explicit inverse comparison retains exactly the actual
Eilenberg–Moore carrier-map components at every original color. -/
@[simp]
theorem emToTensorAlgebra_map (O : ColoredOperadObj W C)
    {A B : Monad.Algebra (profileMonad O)} (f : A ⟶ B) :
    ((emToTensorAlgebra O).map f).hom = f.f := rfl





end CategoryTheory.Operad.Tensor
end
end
end source_TensorAlgebraEM

/- Source proof segment: TensorFreeAdjunction -/
section source_TensorFreeAdjunction
/-!
# Actual original tensor-operadic free and forgetful adjunction
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem liftActionFromSquares {V : Type*} [Category* V]
    {X A B D Y : V} (k : X ⟶ B) (a : X ⟶ A) (b : A ⟶ B) (c : B ⟶ Y)
    (n : A ⟶ B) (m : X ⟶ D) (t : D ⟶ B)
    (hk : k = a ≫ b) (hb : b ≫ c = n ≫ c) (hn : a ≫ n = m ≫ t) :
    k ≫ c = m ≫ (t ≫ c) := by
  rw [hk, Category.assoc a b, hb, ← Category.assoc a n, hn, Category.assoc]

private theorem liftRestrictionInverse {V : Type*} [Category* V]
    {T U V' Y : V} (mapGen : T ⟶ U) (mapF : U ⟶ V') (action : V' ⟶ Y)
    (μ : U ⟶ T) (f : T ⟶ Y) (k : T ⟶ V')
    (hk : k = mapGen ≫ mapF) (hf : mapF ≫ action = μ ≫ f)
    (hu : mapGen ≫ μ = 𝟙 T) : k ≫ action = f := by
  rw [hk, Category.assoc mapGen mapF, hf, ← Category.assoc mapGen μ, hu, Category.id_comp]

theorem restrictLiftInverse {V : Type*} [Category* V]
    {X T U Y : V} (genX : X ⟶ T) (mapF : T ⟶ U) (action : U ⟶ Y)
    (f : X ⟶ Y) (genY : Y ⟶ U)
    (hn : genX ≫ mapF = f ≫ genY) (hu : genY ≫ action = 𝟙 Y) :
    genX ≫ (mapF ≫ action) = f := by
  rw [← Category.assoc genX mapF, hn, Category.assoc f genY, hu, Category.comp_id]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- Extend every original carrier map into the original tensor
algebra by its actual profile tensor map and original algebra action. -/
def freeAlgebraLift (O : ColoredOperadObj W C) {A : W → C} (B : Algebra O)
    (f : A ⟶ B.carrier) : freeAlgebra O A ⟶ B :=
  Algebra.Hom.ofActionEquation _ _ (profileMap O.toCollection f ≫ B.action) (by
    let k := profileMap O.toCollection (profileMap O.toCollection f ≫ B.action)
    let a := profileMap O.toCollection (profileMap O.toCollection f)
    let b := profileMap O.toCollection B.action
    let c := B.action
    let n := profileMultiplication O B.carrier
    let m := profileMultiplication O A
    let t := profileMap O.toCollection f
    exact liftActionFromSquares k a b c n m t
      (profileMap_comp O.toCollection _ _) B.action_assoc.symm (profileMultiplication_input O f))

/-- Restrict an actual original free algebra map along the original
unary generator, inverse to the full operation-preserving extension. -/
def tensorFreeHomEquiv (O : ColoredOperadObj W C) (A : W → C) (B : Algebra O) :
    (freeAlgebra O A ⟶ B) ≃ (A ⟶ B.carrier) where
  toFun f := (profileUnit O).app A ≫ f.hom
  invFun := freeAlgebraLift O B
  left_inv f := by
    apply Algebra.Hom.ext
    exact liftRestrictionInverse
      (profileMap O.toCollection ((profileUnit O).app A)) (profileMap O.toCollection f.hom) B.action
      (profileMultiplication O A) f.hom
      (profileMap O.toCollection ((profileUnit O).app A ≫ f.hom))
      (profileMap_comp O.toCollection _ _) (Algebra.action_naturality f).symm
      (profileMultiplication_right_unit O A)
  right_inv f :=
    restrictLiftInverse ((profileUnit O).app A) (profileMap O.toCollection f) B.action f
      ((profileUnit O).app B.carrier) ((profileUnit O).naturality f).symm B.action_unit

/-- The original extension map is natural under every original
carrier map in the source, with actual tensor profile maps. -/
theorem tensorFreeHomEquiv_source (O : ColoredOperadObj W C) {A A' : W → C} (f : A ⟶ A')
    {B : Algebra O} (g : A' ⟶ B.carrier) :
    (tensorFreeHomEquiv O A B).symm (f ≫ g) =
      (freeAlgebraFunctor O).map f ≫ (tensorFreeHomEquiv O A' B).symm g := by
  apply Algebra.Hom.ext
  exact (congrArg (· ≫ B.action) (profileMap_comp O.toCollection f g)).trans (Category.assoc _ _ _)

/-- The original extension/restriction bijection is natural under
every full original operation-preserving map in the target algebra. -/
theorem tensorFreeHomEquiv_target (O : ColoredOperadObj W C) (A : W → C)
    {B D : Algebra O} (f : freeAlgebra O A ⟶ B) (g : B ⟶ D) :
    tensorFreeHomEquiv O A D (f ≫ g) = tensorFreeHomEquiv O A B f ≫ g.hom := by
  exact (Category.assoc ((profileUnit O).app A) f.hom g.hom).symm

/-- The actual original tensor free algebra functor is left adjoint
to the original operation-map algebra forgetful functor. Its full
Hom equivalence is the constructed original extension/restriction map. -/
def tensorFreeAdjunction (O : ColoredOperadObj W C) :
    freeAlgebraFunctor O ⊣ Algebra.forget O :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorFreeHomEquiv O
      homEquiv_naturality_left_symm := fun f g => tensorFreeHomEquiv_source O f g
      homEquiv_naturality_right := fun f g => tensorFreeHomEquiv_target O _ f g }

/-- The adjunction unit is the original operadic unary unit
insertion followed by its original unary profile quotient injection. -/
@[simp]
theorem tensorFreeAdjunction_unit (O : ColoredOperadObj W C) (A : W → C) :
    (tensorFreeAdjunction O).unit.app A = (profileUnit O).app A := by
  change (profileUnit O).app A ≫ 𝟙 _ = (profileUnit O).app A
  exact Category.comp_id _

/-- The actual adjunction counit is extension of the original
carrier identity into its original full tensor algebra operations. -/
@[simp]
theorem tensorFreeAdjunction_counit (O : ColoredOperadObj W C) (B : Algebra O) :
    (tensorFreeAdjunction O).counit.app B = freeAlgebraLift O B (𝟙 B.carrier) := rfl

/-- The counit carrier map is precisely the original algebra action,
which evaluates every original operation-weighted profile. -/
theorem tensorFreeAdjunction_counit_hom (O : ColoredOperadObj W C) (B : Algebra O) :
    ((tensorFreeAdjunction O).counit.app B).hom = B.action := by
  change profileMap O.toCollection (𝟙 B.carrier) ≫ B.action = B.action
  rw [profileMap_id, Category.id_comp]

/-- The original free/forgetful left triangle is precisely the
proved tensor profile unit-substitution equation on the free carrier. -/
theorem tensorFreeAdjunction_left_triangle (O : ColoredOperadObj W C) (A : W → C) :
    (freeAlgebraFunctor O).map ((profileUnit O).app A) ≫
        (tensorFreeAdjunction O).counit.app (freeAlgebra O A) = 𝟙 (freeAlgebra O A) := by
  apply Algebra.Hom.ext
  exact (congrArg (fun f => profileMap O.toCollection ((profileUnit O).app A) ≫ f)
    (tensorFreeAdjunction_counit_hom O (freeAlgebra O A))).trans
      (profileMultiplication_right_unit O A)

/-- The original right triangle evaluates the original unary
generator by the original full tensor algebra action. -/
theorem tensorFreeAdjunction_right_triangle (O : ColoredOperadObj W C) (B : Algebra O) :
    (profileUnit O).app B.carrier ≫ ((tensorFreeAdjunction O).counit.app B).hom =
      𝟙 B.carrier :=
  (congrArg ((profileUnit O).app B.carrier ≫ ·) (tensorFreeAdjunction_counit_hom O B)).trans
    B.action_unit

/-- The monad multiplication induced by the original adjunction
is the actual original profile substitution multiplication. -/
theorem tensorFreeAdjunction_toMonad_multiplication (O : ColoredOperadObj W C) (A : W → C) :
    (tensorFreeAdjunction O).toMonad.μ.app A = profileMultiplication O A :=
  tensorFreeAdjunction_counit_hom O (freeAlgebra O A)

/-- The monad induced by the constructed full tensor free/forgetful
adjunction is the actual original profile coinvariant monad, with
identity carrier components and proved unit/multiplication squares. -/
def tensorFreeAdjunctionMonadIso (O : ColoredOperadObj W C) :
    (tensorFreeAdjunction O).toMonad ≅ profileMonad O :=
  MonadIso.mk (NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    exact (Category.comp_id _).trans (Category.id_comp _).symm))
    (fun A => (Category.comp_id _).trans (tensorFreeAdjunction_unit O A))
    (fun A => by
      change (tensorFreeAdjunction O).toMonad.μ.app A ≫ 𝟙 _ =
        (profileMap O.toCollection (𝟙 _) ≫ 𝟙 _) ≫ profileMultiplication O A
      rw [profileMap_id, Category.id_comp, Category.id_comp, Category.comp_id]
      exact tensorFreeAdjunction_toMonad_multiplication O A)





end CategoryTheory.Operad.Tensor
end
end
end source_TensorFreeAdjunction

/- Source proof segment: AlgebraCarrierIsomorphisms -/
section source_AlgebraCarrierIsomorphisms
/-!
# Isomorphisms of the original tensor algebra carriers
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- An invertible original carrier map has an inverse preserving
every original tensor operation. The inverse is constructed from
the original action square and the actual tensor profile functor. -/
def Algebra.Hom.inverse {O : ColoredOperadObj W C} {A B : Algebra O}
    (f : A ⟶ B) [IsIso f.hom] : B ⟶ A :=
  Algebra.Hom.ofActionEquation B A (inv f.hom) (by
    apply (cancel_mono f.hom).1
    rw [Category.assoc, Algebra.action_naturality f, ← Category.assoc,
      ← profileMap_comp, IsIso.inv_hom_id, profileMap_id, Category.id_comp]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id])

/-- The original full-operation algebra forgetful functor reflects
isomorphisms by the explicitly constructed inverse carrier map. -/
instance algebraForgetReflectsIsomorphisms (O : ColoredOperadObj W C) :
    (Algebra.forget O).ReflectsIsomorphisms where
  reflects {A B} f _ := by
    change IsIso f.hom at *
    exact ⟨⟨f.inverse, Algebra.Hom.ext (IsIso.hom_inv_id f.hom),
      Algebra.Hom.ext (IsIso.inv_hom_id f.hom)⟩⟩

/-- The inverse operation-preserving map has exactly the inverse
original carrier map at every color. -/
@[simp]
theorem Algebra.Hom.inverse_hom {O : ColoredOperadObj W C} {A B : Algebra O}
    (f : A ⟶ B) [IsIso f.hom] : f.inverse.hom = inv f.hom := rfl



end CategoryTheory.Operad.Tensor
end
end
end source_AlgebraCarrierIsomorphisms

/- Source proof segment: CoefficientLeafColimitPreservation -/
section source_CoefficientLeafColimitPreservation
/-!
# Actual source colimit commutation for a varying tensor coefficient
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- Use classical equality on the original coefficient-and-leaf slot index. -/
local instance coefficientSlotDecidableEq (L : FiniteFamily C) :
    DecidableEq (Option L.index) := Classical.decEq _

/-- The original leaf family with its actual empty-tensor
coefficient in the retained root slot. -/
def coefficientSlotBase (L : FiniteFamily C) : Option L.index → C :=
  ((coefficientLeafFamilyFunctor L).obj (FiniteTensor.UnitCopower.unitObject C)).obj

/-- Replacing precisely the coefficient slot gives the actual
coefficient/leaf input objects, with every original leaf retained. -/
theorem coefficientSlotUpdate_obj (L : FiniteFamily C) (X : C) (i : Option L.index) :
    Function.update (coefficientSlotBase L) none X i =
      ((coefficientLeafFamilyFunctor L).obj X).obj i := by
  classical
  cases i with
  | none => exact Function.update_self _ _ _
  | some i => exact Function.update_of_ne (Option.some_ne_none i) _ _

/-- The actual one-slot replacement functor is the original
coefficient-family functor, through the displayed identity index
map and original object transports. -/
def coefficientSlotFamilyIso (L : FiniteFamily C) :
    Pi.replaceFunctor (coefficientSlotBase L) none ⋙
        FiniteFamily.fixedIndexFunctor (FintypeCat.of (Option L.index)) ≅
      coefficientLeafFamilyFunctor L := by
  classical
  refine NatIso.ofComponents (fun X =>
    FiniteFamily.isoOfComponents (Equiv.refl (Option L.index))
      (fun i => eqToIso (coefficientSlotUpdate_obj L X i))) ?_
  intro X Y f
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      change HEq (Pi.replaceMap (coefficientSlotBase L) none f none ≫
          eqToHom (coefficientSlotUpdate_obj L Y none))
        (eqToHom (coefficientSlotUpdate_obj L X none) ≫ f)
      exact ((comp_eqToHom_heq _ (coefficientSlotUpdate_obj L Y none)).trans
        (Pi.replaceMap_at (coefficientSlotBase L) none f)).trans
          (eqToHom_comp_heq f (coefficientSlotUpdate_obj L X none)).symm
    | some i =>
      change HEq (Pi.replaceMap (coefficientSlotBase L) none f (some i) ≫
          eqToHom (coefficientSlotUpdate_obj L Y (some i)))
        (eqToHom (coefficientSlotUpdate_obj L X (some i)) ≫ 𝟙 (L.obj i))
      exact ((comp_eqToHom_heq _ (coefficientSlotUpdate_obj L Y (some i))).trans
        (Pi.replaceMap_other (coefficientSlotBase L) none (some i)
          (Option.some_ne_none i) f)).trans
          (eqToHom_comp_heq (𝟙 (L.obj i)) (coefficientSlotUpdate_obj L X (some i))).symm

/-- The actual source one-slot tensor functor is identified with
tensoring the varying original coefficient and every fixed leaf. -/
def coefficientSlotTensorIso (L : FiniteFamily C) :
    Pi.replaceFunctor (coefficientSlotBase L) none ⋙
        fixedIndexTensorFunctor (FintypeCat.of (Option L.index)) ≅
      coefficientLeafTensorFunctor L :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coefficientSlotFamilyIso L) FiniteTensor.tensor

variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- A varying original coefficient tensor commutes with the
required source-sized colimits, derived from the single original
coefficient slot preservation hypothesis. -/
instance coefficientLeafTensorPreservesColimits (L : FiniteFamily C) :
    PreservesColimitsOfSize.{us, us} (coefficientLeafTensorFunctor L) := by
  classical
  let : Functor.PreservesColimitsInEachSlot
      (fixedIndexTensorFunctor (C := C) (FintypeCat.of (Option L.index))) :=
    FiniteTensorPreservesColimitsInEachSlot.preserves _
  let : PreservesColimitsOfSize.{us, us}
      (Pi.replaceFunctor (coefficientSlotBase L) none ⋙
        fixedIndexTensorFunctor (C := C) (FintypeCat.of (Option L.index))) :=
    Functor.PreservesColimitsInEachSlot.preserves (coefficientSlotBase L) none
  exact preservesColimits_of_natIso (coefficientSlotTensorIso L)




end CategoryTheory.Operad.Tensor
end
end
end source_CoefficientLeafColimitPreservation

/- Source proof segment: UnitCoefficientTensor -/
section source_UnitCoefficientTensor
/-!
# Remove the actual empty-tensor coefficient before original input leaves
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The original input positions in the actual empty-coefficient
and singleton-leaf flattening, including empty input families. -/
def unitCoefficientInputEquiv (L : FiniteFamily C) :
    L.index ≃ ((FiniteFamily.flatten (C := C)).obj
      (coefficientLeavesNested (FiniteFamily.empty : FiniteFamily C) L)).index where
  toFun i := ⟨some i, PUnit.unit⟩
  invFun p := match p with
    | ⟨none, e⟩ => e.elim
    | ⟨some i, _⟩ => i
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨i, j⟩
    cases i with
    | none => cases j
    | some i => cases j; rfl

/-- The original finite input family is precisely the flattened
empty coefficient and its original singleton input blocks. -/
def unitCoefficientFlattenIso (L : FiniteFamily C) :
    L ≅ (FiniteFamily.flatten (C := C)).obj
      (coefficientLeavesNested (FiniteFamily.empty : FiniteFamily C) L) :=
  FiniteFamily.isoOfReindex (unitCoefficientInputEquiv L) (fun _ => rfl)

/-- Every original input map commutes with the actual displayed
empty-coefficient input bijection. -/
theorem unitCoefficientFlattenIso_naturality {L M : FiniteFamily C} (l : L ⟶ M) :
    (unitCoefficientFlattenIso L).hom ≫
        (FiniteFamily.flatten (C := C)).map
          (coefficientLeavesNestedMap (𝟙 FiniteFamily.empty) l) =
      l ≫ (unitCoefficientFlattenIso M).hom := by
  apply FiniteFamily.Hom_ext
  · ext i
    rfl
  · intro i
    change HEq (𝟙 (L.obj i) ≫ l.hom i) (l.hom i ≫ 𝟙 (M.obj (l.equiv i)))
    exact heq_of_eq ((Category.id_comp _).trans (Category.comp_id _).symm)

variable [FiniteTensor C]

/-- Tensoring the actual tensor-unit coefficient with the
original finite input leaves gives their original finite tensor.
This is derived from original flattening and singleton maps. -/
def unitCoefficientTensorIso (L : FiniteFamily C) :
    (coefficientLeafTensorFunctor L).obj (FiniteTensor.UnitCopower.unitObject C) ≅
      (FiniteTensor.tensor (V := C)).obj L :=
  (coefficientLeavesNormalizationIso FiniteFamily.empty L).symm ≪≫
    (FiniteTensor.tensor (V := C)).mapIso (unitCoefficientFlattenIso L).symm

/-- Inserting the actual empty coefficient is the original input
bijection followed by its actual coefficient/leaf normalization. -/
theorem unitCoefficientTensorIso_inv (L : FiniteFamily C) :
    (unitCoefficientTensorIso L).inv =
      (FiniteTensor.tensor (V := C)).map (unitCoefficientFlattenIso L).hom ≫
        coefficientLeavesNormalization FiniteFamily.empty L := by
  change (FiniteTensor.tensor (V := C)).map (unitCoefficientFlattenIso L).hom ≫
      (coefficientLeavesNormalizationIso FiniteFamily.empty L).hom = _
  exact congrArg (fun f => (FiniteTensor.tensor (V := C)).map
    (unitCoefficientFlattenIso L).hom ≫ f) (coefficientLeavesNormalizationIso_hom _ _)




end CategoryTheory.Operad.Tensor
end
end
end source_UnitCoefficientTensor

/- Source proof segment: UnitCoefficientNaturality -/
section source_UnitCoefficientNaturality
/-!
# Actual original input naturality of tensor-unit coefficient removal
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

private theorem unitCoefficientInverseSquare {V : Type*} [Category* V]
    {X Y NX NY TX TY : V} (p : X ⟶ NX) (q : Y ⟶ NY) (r : NX ⟶ NY)
    (a : NX ⟶ TX) (b : NY ⟶ TY) (f : X ⟶ Y) (g : TX ⟶ TY)
    (hp : p ≫ r = f ≫ q) (ha : r ≫ b = a ≫ g) :
    f ≫ (q ≫ b) = (p ≫ a) ≫ g := by
  rw [← Category.assoc f q, ← hp, Category.assoc p r, ha, ← Category.assoc]

private theorem unitCoefficientForwardOfInverse {V : Type*} [Category* V]
    {X Y TX TY : V} (e : X ≅ TX) (d : Y ≅ TY) (f : X ⟶ Y) (g : TX ⟶ TY)
    (h : e.inv ≫ f = g ≫ d.inv) : f ≫ d.hom = e.hom ≫ g := by
  apply (cancel_epi e.inv).1
  rw [← Category.assoc e.inv f, h, Category.assoc g d.inv,
    d.inv_hom_id, Category.comp_id, e.inv_hom_id_assoc]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The actual empty-coefficient insertion commutes with every
original leaf input map and original finite input permutation. -/
theorem unitCoefficientTensorIso_inv_naturality {L M : FiniteFamily C} (l : L ⟶ M) :
    (FiniteTensor.tensor (V := C)).map l ≫ (unitCoefficientTensorIso M).inv =
      (unitCoefficientTensorIso L).inv ≫ (FiniteTensor.tensor (V := C)).map
        (coefficientLeafMap (𝟙 (FiniteTensor.UnitCopower.unitObject C)) l) := by
  let T := FiniteTensor.tensor (V := C)
  let r := (FiniteFamily.flatten (C := C)).map
    (coefficientLeavesNestedMap (𝟙 FiniteFamily.empty) l)
  let g := coefficientLeafMap (𝟙 (FiniteTensor.UnitCopower.unitObject C)) l
  have hp : T.map (unitCoefficientFlattenIso L).hom ≫ T.map r =
      T.map l ≫ T.map (unitCoefficientFlattenIso M).hom :=
    (T.map_comp _ _).symm.trans
      ((congrArg T.map (unitCoefficientFlattenIso_naturality l)).trans (T.map_comp _ _))
  have hg : T.map (coefficientLeafMap (T.map (𝟙 FiniteFamily.empty)) l) = T.map g :=
    congrArg T.map (congrArg (fun f => coefficientLeafMap f l) (T.map_id FiniteFamily.empty))
  have hn : T.map r ≫ coefficientLeavesNormalization FiniteFamily.empty M =
      coefficientLeavesNormalization FiniteFamily.empty L ≫ T.map g :=
    (coefficientLeavesNormalization_naturality (𝟙 FiniteFamily.empty) l).trans
      (congrArg (coefficientLeavesNormalization FiniteFamily.empty L ≫ ·) hg)
  have h := unitCoefficientInverseSquare
    (T.map (unitCoefficientFlattenIso L).hom) (T.map (unitCoefficientFlattenIso M).hom)
    (T.map r) (coefficientLeavesNormalization FiniteFamily.empty L)
    (coefficientLeavesNormalization FiniteFamily.empty M) (T.map l) (T.map g) hp hn
  exact (congrArg (T.map l ≫ ·) (unitCoefficientTensorIso_inv M)).trans
    (h.trans (congrArg (· ≫ T.map g) (unitCoefficientTensorIso_inv L).symm))

/-- Removing the actual tensor-unit coefficient is natural in
all original input objects, maps and input bijections. -/
theorem unitCoefficientTensorIso_naturality {L M : FiniteFamily C} (l : L ⟶ M) :
    (FiniteTensor.tensor (V := C)).map
        (coefficientLeafMap (𝟙 (FiniteTensor.UnitCopower.unitObject C)) l) ≫
        (unitCoefficientTensorIso M).hom =
      (unitCoefficientTensorIso L).hom ≫ (FiniteTensor.tensor (V := C)).map l :=
  unitCoefficientForwardOfInverse (unitCoefficientTensorIso L) (unitCoefficientTensorIso M)
    _ _ (unitCoefficientTensorIso_inv_naturality l).symm



end CategoryTheory.Operad.Tensor
end
end
end source_UnitCoefficientNaturality

/- Source proof segment: CoefficientCopowerTensor -/
section source_CoefficientCopowerTensor
/-!
# Actual tensor copowers before the original finite input leaves
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- Tensoring a source-sized actual unit copower before the
original finite leaf family is the actual coproduct of their
original finite tensor. This follows from proved coefficient-slot
commutation and actual empty-coefficient tensor removal. -/
def coefficientCopowerTensorIso (S : Type us) (L : FiniteFamily C) :
    (coefficientLeafTensorFunctor L).obj ((FiniteTensor.UnitCopower.functor C).obj S) ≅
      ∐ (fun _ : S => (FiniteTensor.tensor (V := C)).obj L) :=
  preservesColimitIso (coefficientLeafTensorFunctor L)
      (Discrete.functor (fun _ : S => FiniteTensor.UnitCopower.unitObject C)) ≪≫
    (Sigma.isoColimit
      (Discrete.functor (fun _ : S => FiniteTensor.UnitCopower.unitObject C) ⋙
        coefficientLeafTensorFunctor L)).symm ≪≫
    Sigma.mapIso (fun _ : S => unitCoefficientTensorIso L)

/-- Each original coefficient copower injection gives exactly
the corresponding original tensor-word copy, through the proved
tensor-unit coefficient removal. -/
@[reassoc]
theorem coefficientCopowerTensorIso_ι (S : Type us) (L : FiniteFamily C) (s : S) :
    (coefficientLeafTensorFunctor L).map
        (Sigma.ι (fun _ : S => FiniteTensor.UnitCopower.unitObject C) s) ≫
        (coefficientCopowerTensorIso S L).hom =
      (unitCoefficientTensorIso L).hom ≫ Sigma.ι (fun _ : S =>
        (FiniteTensor.tensor (V := C)).obj L) s := by
  change (coefficientLeafTensorFunctor L).map
      (Sigma.ι (fun _ : S => FiniteTensor.UnitCopower.unitObject C) s) ≫
    ((preservesColimitIso (coefficientLeafTensorFunctor L)
        (Discrete.functor (fun _ : S => FiniteTensor.UnitCopower.unitObject C))).hom ≫
      (Sigma.isoColimit
        (Discrete.functor (fun _ : S => FiniteTensor.UnitCopower.unitObject C) ⋙
          coefficientLeafTensorFunctor L)).inv ≫
      (Sigma.mapIso (fun _ : S => unitCoefficientTensorIso L)).hom) = _
  rw [ι_preservesColimitIso_hom_assoc, Sigma.ι_isoColimit_inv_assoc,
    Sigma.ι_mapIso_hom]




end CategoryTheory.Operad.Tensor
end
end
end source_CoefficientCopowerTensor

/- Source proof segment: CoefficientCopowerNaturality -/
section source_CoefficientCopowerNaturality
/-!
# Actual source index and input naturality of coefficient tensor copowers
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem coefficientCopyTensorNaturality {V : Type*} [Category* V]
    {C0 C1 CS CT L0 L1 S0 S1 : V}
    (i : C0 ⟶ CS) (g : CS ⟶ CT) (j : C1 ⟶ CT) (k : C0 ⟶ C1)
    (a : CS ⟶ S0) (b : CT ⟶ S1) (n0 : C0 ⟶ L0) (n1 : C1 ⟶ L1)
    (p : L0 ⟶ S0) (q : L1 ⟶ S1) (l : L0 ⟶ L1) (s : S0 ⟶ S1)
    (hc : i ≫ g = k ≫ j) (hb : j ≫ b = n1 ≫ q) (ha : i ≫ a = n0 ≫ p)
    (hn : k ≫ n1 = n0 ≫ l) (hs : p ≫ s = l ≫ q) :
    i ≫ (g ≫ b) = i ≫ (a ≫ s) := by
  rw [← Category.assoc i g, hc, Category.assoc k j, hb,
    ← Category.assoc k n1, hn, Category.assoc n0 l, ← hs,
    ← Category.assoc n0 p, ← ha, Category.assoc]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]

/-- Applying an actual coefficient index map and original input
map to one original unit copy gives the corresponding target copy,
while retaining the original input maps. -/
theorem coefficientUnitCopyMap {S T : Type us} (f : S ⟶ T)
    {L M : FiniteFamily C} (l : L ⟶ M) (s : S) :
    (coefficientLeafFamilyFunctor L).map
        (Sigma.ι (fun _ : S => FiniteTensor.UnitCopower.unitObject C) s) ≫
        coefficientLeafMap ((FiniteTensor.UnitCopower.functor C).map f) l =
      coefficientLeafMap (𝟙 (FiniteTensor.UnitCopower.unitObject C)) l ≫
        (coefficientLeafFamilyFunctor M).map
          (Sigma.ι (fun _ : T => FiniteTensor.UnitCopower.unitObject C) (f s)) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      exact heq_of_eq ((FiniteTensor.UnitCopower.ι_map C f s).trans (Category.id_comp _).symm)
    | some i =>
      exact heq_of_eq ((Category.id_comp (l.hom i)).trans (Category.comp_id _).symm)

variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- The actual tensor/copower identification is natural in every
original coefficient index map and every original finite leaf map,
including arbitrary input permutations and empty leaf families. -/
theorem coefficientCopowerTensorIso_naturality {S T : Type us} (f : S ⟶ T)
    {L M : FiniteFamily C} (l : L ⟶ M) :
    (FiniteTensor.tensor (V := C)).map
        (coefficientLeafMap ((FiniteTensor.UnitCopower.functor C).map f) l) ≫
        (coefficientCopowerTensorIso T M).hom =
      (coefficientCopowerTensorIso S L).hom ≫
        Sigma.map' f (fun _ => (FiniteTensor.tensor (V := C)).map l) := by
  let F := coefficientLeafTensorFunctor L
  let D := Discrete.functor (fun _ : S => FiniteTensor.UnitCopower.unitObject C)
  apply (isColimitOfPreserves F (colimit.isColimit D)).hom_ext
  rintro ⟨s⟩
  let A := FiniteTensor.tensor (V := C)
  let g := coefficientLeafMap ((FiniteTensor.UnitCopower.functor C).map f) l
  let k := coefficientLeafMap (𝟙 (FiniteTensor.UnitCopower.unitObject C)) l
  have hc :
      F.map (Sigma.ι (fun _ : S => FiniteTensor.UnitCopower.unitObject C) s) ≫ A.map g =
        A.map k ≫ (coefficientLeafTensorFunctor M).map
          (Sigma.ι (fun _ : T => FiniteTensor.UnitCopower.unitObject C) (f s)) :=
    (A.map_comp _ _).symm.trans
      ((congrArg A.map (coefficientUnitCopyMap f l s)).trans (A.map_comp _ _))
  exact coefficientCopyTensorNaturality _ _ _ _ _ _ _ _ _ _ _ _ hc
    (coefficientCopowerTensorIso_ι T M (f s)) (coefficientCopowerTensorIso_ι S L s)
    (unitCoefficientTensorIso_naturality l)
    (Sigma.ι_comp_map' (g := fun _ : S => A.obj L) (f := fun _ : T => A.obj M)
      f (fun _ => A.map l) s)



end CategoryTheory.Operad.Tensor
end
end
end source_CoefficientCopowerNaturality
