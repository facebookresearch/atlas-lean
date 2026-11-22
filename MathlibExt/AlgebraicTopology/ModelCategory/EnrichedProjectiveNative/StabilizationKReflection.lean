/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKLocalLifting
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKLocalReplacement
import Mathlib.CategoryTheory.InducedCategory
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction
import Mathlib.CategoryTheory.Localization.Composition
import MathlibExt.CategoryTheory.Functor.CoaugmentedReflection

/-!
# Actual original-K reflection and categorical localization

The SAME original I-Q then K-Z replacement preserves native level weakness.
It therefore acts on the actual native level homotopy category. Its original
Q-projection inverse followed by K-unit gives the full reflection into the
induced category of actual K-local objects with genuine level-Ho morphisms.
The composite is an actual categorical localization at the original K-local
Hom tests. Native Omega/source identification, K-cell model recognition and
all five stable model classes remain separate required joins.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- On actual local cofibrant input the same original K-unit is level weak. -/
theorem localReplacementUnit_weak_of_local
    (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) [IsCofibrant X]
    (hX : (generators s).rlp (toZero X)) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) ((localReplacementUnit s).app X) :=
  ((localTestEquivalences_iff_levelWeak_of_local s) _ hX
    ((localReplacement_isLocal s) X)).mp ((localReplacementUnit_localTestEquivalence s) X)

/-- The SAME original I-Q of an actual local object is local through its original TF projection. -/
theorem originalCofibrantReplacement_local
    (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (hX : (generators s).rlp (toZero X)) :
    (generators s).rlp (toZero ((Replacement.cofibrantReplacement (B := B)).obj X)) :=
  (local_of_levelTrivialFibration s) (Replacement.cofibrantReplacementCounit.app X)
    (Replacement.cofibrantReplacementCounit_mem_trivialFibrations X) hX

/-- Its actual all-object comparison is a native level-Ho isomorphism
at every actual local input. -/
theorem cofibrantLocalComparison_isIso_of_local
    (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (hX : (generators s).rlp (toZero X)) :
    IsIso ((cofibrantLocalComparison s).app X) := by
  let Q : (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤ (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
    Replacement.cofibrantReplacement (B := B)
  let e : Q ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ≅
      toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
    Replacement.cofibrantReplacementProjectionIso (B := B)
  let _ : IsCofibrant (Q.obj X) := Replacement.isCofibrant_cofibrantReplacement X
  let _ : IsIso (e.inv.app X) := by infer_instance
  have hη := (localReplacementUnit_weak_of_local s) (Q.obj X)
    ((originalCofibrantReplacement_local s) X hX)
  let _ : IsIso ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
      ((localReplacementUnit s).app (Q.obj X))) :=
    (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp hη
  rw [(cofibrantLocalComparison_app s)]
  change IsIso (e.inv.app X ≫
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
      ((localReplacementUnit s).app (Q.obj X)))
  infer_instance

/-- The literal original I-Q/K-Z action followed by the native projection inverts level weakness. -/
theorem localReplacementHo_inverts :
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)).IsInvertedBy
      ((cofibrantLocalReplacement s) ⋙
        toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) :=
  fun _ _ f hf => (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp
    ((cofibrantLocalReplacement_map_weak s) f hf)

/-- The actual action of the SAME original I-Q/K-Z functor on native level Ho. -/
def localReplacementHo : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤
    HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  Localization.Construction.lift
    ((cofibrantLocalReplacement s) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (localReplacementHo_inverts s)

/-- The complete strict projection retains the original functor and every projected arrow. -/
theorem localReplacementHo_projection :
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ⋙ (localReplacementHo s) =
      (cofibrantLocalReplacement s) ⋙
        toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  Localization.Construction.fac _ _

/-- Every actual native arrow keeps its SAME chosen I-Q/K-Z map under Ho projection. -/
theorem localReplacementHo_map_projected
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) :
    (localReplacementHo s).map
        ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((cofibrantLocalReplacement s).map f) :=
  Functor.congr_hom (localReplacementHo_projection s) f

/-- This is the actual constructed strict lifting witness, with no incoming localization data. -/
@[instance_reducible]
def localReplacementHoLifting :
    Localization.Lifting (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
      (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I))
      ((cofibrantLocalReplacement s) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
      (localReplacementHo s) :=
  ⟨eqToIso (localReplacementHo_projection s)⟩

attribute [local instance] localReplacementHoLifting

@[instance_reducible]
private def identityHoLifting :
    Localization.Lifting (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
      (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I))
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
      (𝟭 (HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))) :=
  ⟨Functor.rightUnitor _⟩

attribute [local instance] identityHoLifting

/-- The complete actual original comparison lifts naturally to every level-Ho morphism. -/
def localReplacementHoUnit :
    𝟭 (HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) ⟶ (localReplacementHo s) :=
  Localization.liftNatTrans (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    ((cofibrantLocalReplacement s) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (𝟭 _) (localReplacementHo s) (cofibrantLocalComparison s)

/-- Its projected component is the SAME original Q-inverse followed by original K-unit. -/
theorem localReplacementHoUnit_app_projected (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (localReplacementHoUnit s).app
        ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X) =
      (cofibrantLocalComparison s).app X := by
  rw [localReplacementHoUnit, Localization.liftNatTrans_app]
  dsimp only [Localization.Lifting.iso, identityHoLifting, localReplacementHoLifting]
  change 𝟙 _ ≫ (cofibrantLocalComparison s).app X ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- Complete unit naturality retains every actual level-Ho arrow. -/
theorem localReplacementHoUnit_naturality
    {X Y : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) :
    f ≫ (localReplacementHoUnit s).app Y =
      (localReplacementHoUnit s).app X ≫ (localReplacementHo s).map f :=
  (localReplacementHoUnit s).naturality f

/-- The native Ho object equivalence supplies the original source object, without new choice. -/
abbrev localHoUnderlying (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  (Localization.Construction.objEquiv
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I))).symm X

/-- Every Ho output is the projection of that SAME native I-Q/K-Z object. -/
theorem localReplacementHo_obj (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (localReplacementHo s).obj X =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        ((cofibrantLocalReplacement s).obj (localHoUnderlying X)) := rfl

/-- The full original comparison is universal at each actual K-local target for every Ho source. -/
theorem localReplacementHoUnit_precomp_bijective
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (Z : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (hZ : (generators s).rlp (toZero Z)) :
    Function.Bijective
      (fun g : (localReplacementHo s).obj X ⟶
          (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z =>
        (localReplacementHoUnit s).app X ≫ g) := by
  obtain ⟨Y, rfl⟩ := (Localization.Construction.objEquiv
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I))).surjective X
  change Function.Bijective
    (fun g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        ((cofibrantLocalReplacement s).obj Y) ⟶
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z =>
      (localReplacementHoUnit s).app
        ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Y) ≫ g)
  rw [(localReplacementHoUnit_app_projected s)]
  exact (cofibrantLocalComparison_precomp_bijective s) Y Z hZ

/-- The actual lifted functor inverts every original local-test map. -/
theorem localReplacementHo_map_isIso_of_localTest
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : localTestEquivalences s f) :
    IsIso ((localReplacementHo s).map
      ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f)) := by
  rw [localReplacementHo_map_projected]
  exact (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp
    (((cofibrantLocalReplacement_map_weak_iff s) f).mpr hf)

/-- Every image of the same lifted C_s has its actual original unit invertible. -/
theorem localReplacementHoUnit_isIso_at_image
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    IsIso ((localReplacementHoUnit s).app ((localReplacementHo s).obj X)) := by
  rw [localReplacementHo_obj, localReplacementHoUnit_app_projected]
  exact cofibrantLocalComparison_isIso_of_local s _
    (cofibrantLocalReplacement_isLocal s _)

/-- The same lifted C_s inverts its unit using the proved original local universal comparison. -/
theorem localReplacementHo_mapUnit_isIso
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    IsIso ((localReplacementHo s).map ((localReplacementHoUnit s).app X)) := by
  let Z := (cofibrantLocalReplacement s).obj
    (localHoUnderlying ((localReplacementHo s).obj X))
  have hInject : Function.Injective
      (fun g : (localReplacementHo s).obj X ⟶
          (localReplacementHo s).obj ((localReplacementHo s).obj X) =>
        (localReplacementHoUnit s).app X ≫ g) :=
    (localReplacementHoUnit_precomp_bijective s X Z
      (cofibrantLocalReplacement_isLocal s _)).injective
  have hEq : (localReplacementHo s).map ((localReplacementHoUnit s).app X) =
      (localReplacementHoUnit s).app ((localReplacementHo s).obj X) := by
    apply hInject
    simpa only [Functor.id_map, Functor.id_obj] using
      ((localReplacementHoUnit s).naturality ((localReplacementHoUnit s).app X)).symm
  let _ : IsIso ((localReplacementHoUnit s).app ((localReplacementHo s).obj X)) :=
    localReplacementHoUnit_isIso_at_image s X
  rw [hEq]
  infer_instance

/-- The object is an actual native spectrum together with its literal K-local lifting proof. -/
structure LocalObject where
  /-- The original native spectrum underlying this K-local object. -/
  diagram : EnrichedFunctorCat PointedCGWH.{u, v} I
  isLocal : (generators s).rlp (toZero diagram)

/-- Actual native local objects with the SAME complete ordinary level-Ho morphisms. -/
abbrev localHoObjects :=
  InducedCategory (HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (fun X : LocalObject s =>
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X.diagram)

/-- The genuine fully faithful inclusion uses the original level-Ho object and all morphisms. -/
abbrev localHoInclusion : (localHoObjects s) ⥤
    HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := inducedFunctor _

/-- This full faithfulness is derived from the actual induced Hom carrier. -/
def localHoInclusionFullyFaithful : (localHoInclusion s).FullyFaithful :=
  fullyFaithfulInducedFunctor _

/-- At an actual local target the same original lifted unit is an isomorphism. -/
theorem localReplacementHoUnit_isIso_at_local (Z : localHoObjects s) :
    IsIso ((localReplacementHoUnit s).app ((localHoInclusion s).obj Z)) := by
  change IsIso ((localReplacementHoUnit s).app
    ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z.diagram))
  rw [localReplacementHoUnit_app_projected]
  exact cofibrantLocalComparison_isIso_of_local s Z.diagram Z.isLocal

/-- The actual original replacement defines the entire reflector on ordinary level Ho. -/
def localHoReflector : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤
    (localHoObjects s) where
  obj X := ⟨(cofibrantLocalReplacement s).obj (localHoUnderlying X),
    (cofibrantLocalReplacement_isLocal s) _⟩
  map f := InducedCategory.homMk ((localReplacementHo s).map f)
  map_id X := by
    apply InducedCategory.hom_ext
    exact (localReplacementHo s).map_id X
  map_comp f g := by
    apply InducedCategory.hom_ext
    exact (localReplacementHo s).map_comp f g

/-- Equality retains both entire actual reflector and original Ho replacement functors. -/
theorem localHoReflector_comp_inclusion :
    (localHoReflector s) ⋙ (localHoInclusion s) = (localReplacementHo s) := rfl

/-- Every reflected Ho arrow keeps the SAME actual chosen replacement action. -/
theorem localHoReflector_map_hom
    {X Y : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) :
    ((localHoReflector s).map f).hom = (localReplacementHo s).map f := rfl

/-- The full Hom equivalence is precisely precomposition by the given original lifted comparison. -/
def localHoHomEquiv (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (Z : (localHoObjects s)) :
    ((localHoReflector s).obj X ⟶ Z) ≃ (X ⟶ (localHoInclusion s).obj Z) := by
  let _ : IsIso ((localReplacementHoUnit s).app ((localHoInclusion s).obj Z)) :=
    localReplacementHoUnit_isIso_at_local s Z
  exact InducedCategory.homEquiv.trans
    (Functor.CoaugmentedReflection.unitHomEquiv (localReplacementHo s)
      (localReplacementHoUnit s) (localReplacementHoUnit_isIso_at_image s)
      (localReplacementHo_mapUnit_isIso s) X ((localHoInclusion s).obj Z))

/-- The computed shared Hom equivalence is the whole original precomposition equivalence. -/
theorem localHoHomEquiv_original_equivalence
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (Z : localHoObjects s) :
    localHoHomEquiv s X Z =
      InducedCategory.homEquiv.trans
        (Equiv.ofBijective
          (fun g : (localReplacementHo s).obj X ⟶ (localHoInclusion s).obj Z =>
            (localReplacementHoUnit s).app X ≫ g)
          (localReplacementHoUnit_precomp_bijective s X Z.diagram Z.isLocal)) := by
  apply Equiv.ext
  intro g
  rfl

/-- The complete original inverse is computed by the same lifted functor and inverse unit. -/
theorem localHoHomEquiv_symm_hom
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (Z : localHoObjects s) (g : X ⟶ (localHoInclusion s).obj Z) :
    letI : IsIso ((localReplacementHoUnit s).app ((localHoInclusion s).obj Z)) :=
      localReplacementHoUnit_isIso_at_local s Z
    (((localHoHomEquiv s X Z).symm g).hom) =
      (localReplacementHo s).map g ≫
        inv ((localReplacementHoUnit s).app ((localHoInclusion s).obj Z)) := by
  rfl

/-- The forward function retains every given original morphism. -/
theorem localHoHomEquiv_apply
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (Z : (localHoObjects s)) (g : (localHoReflector s).obj X ⟶ Z) :
    (localHoHomEquiv s) X Z g = (localReplacementHoUnit s).app X ≫ g.hom := rfl

/-- Its inverse is the unique original local morphism with the prescribed comparison composite. -/
theorem localHoHomEquiv_symm_section
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (Z : (localHoObjects s)) (g : X ⟶ (localHoInclusion s).obj Z) :
    (localReplacementHoUnit s).app X ≫ (((localHoHomEquiv s) X Z).symm g).hom = g :=
  ((localHoHomEquiv s) X Z).apply_symm_apply g

/-- Both complete Hom functions and original source/target naturalities
give the actual adjunction. -/
def localHoAdjunction : (localHoReflector s) ⊣ (localHoInclusion s) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := (localHoHomEquiv s)
      homEquiv_naturality_left_symm := by
        intro X' X Z f g
        let t : (localReplacementHo s).obj X ⟶ (localHoInclusion s).obj Z :=
          (((localHoHomEquiv s) X Z).symm g).hom
        have ht : (localReplacementHoUnit s).app X ≫ t = g :=
          (localHoHomEquiv_symm_section s) X Z g
        apply ((localHoHomEquiv s) X' Z).injective
        rw [Equiv.apply_symm_apply, (localHoHomEquiv_apply s)]
        change f ≫ g = (localReplacementHoUnit s).app X' ≫ ((localReplacementHo s).map f ≫ t)
        calc
          f ≫ g = f ≫ ((localReplacementHoUnit s).app X ≫ t) := congrArg (fun q => f ≫ q) ht.symm
          _ = (f ≫ (localReplacementHoUnit s).app X) ≫ t := (Category.assoc _ _ _).symm
          _ = ((localReplacementHoUnit s).app X' ≫ (localReplacementHo s).map f) ≫ t :=
            congrArg (fun q => q ≫ t) ((localReplacementHoUnit_naturality s) f)
          _ = (localReplacementHoUnit s).app X' ≫ ((localReplacementHo s).map f ≫ t) :=
            Category.assoc _ _ _
      homEquiv_naturality_right := by
        intro X Z Z' f g
        change (localReplacementHoUnit s).app X ≫ (f.hom ≫ g.hom) =
          ((localReplacementHoUnit s).app X ≫ f.hom) ≫ g.hom
        exact (Category.assoc _ _ _).symm }

/-- The stock adjunction keeps the complete original Hom equivalence. -/
theorem localHoAdjunction_homEquiv :
    (localHoAdjunction s).homEquiv = (localHoHomEquiv s) := by
  unfold localHoAdjunction
  exact Adjunction.mkOfHomEquiv_homEquiv _

/-- Every ordinary-Ho source map preserves the full original forward Hom function. -/
theorem localHoHomEquiv_source
    {X X' : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)}
    (f : X' ⟶ X) (Z : localHoObjects s)
    (g : (localHoReflector s).obj X ⟶ Z) :
    localHoHomEquiv s X' Z ((localHoReflector s).map f ≫ g) =
      f ≫ localHoHomEquiv s X Z g := by
  simpa only [localHoAdjunction_homEquiv s] using
    (localHoAdjunction s).homEquiv_naturality_left f g

/-- Every ordinary-Ho source map preserves the full original inverse Hom function. -/
theorem localHoHomEquiv_source_symm
    {X X' : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)}
    (f : X' ⟶ X) (Z : localHoObjects s)
    (g : X ⟶ (localHoInclusion s).obj Z) :
    (localHoHomEquiv s X' Z).symm (f ≫ g) =
      (localHoReflector s).map f ≫ (localHoHomEquiv s X Z).symm g := by
  simpa only [localHoAdjunction_homEquiv s] using
    (localHoAdjunction s).homEquiv_naturality_left_symm f g

/-- Arbitrary local-Ho target maps preserve the full original forward Hom function. -/
theorem localHoHomEquiv_target
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    {Z Z' : localHoObjects s} (f : (localHoReflector s).obj X ⟶ Z) (g : Z ⟶ Z') :
    localHoHomEquiv s X Z' (f ≫ g) =
      localHoHomEquiv s X Z f ≫ (localHoInclusion s).map g := by
  simpa only [localHoAdjunction_homEquiv s] using
    (localHoAdjunction s).homEquiv_naturality_right f g

/-- Arbitrary local-Ho target maps preserve the full original inverse Hom function. -/
theorem localHoHomEquiv_target_symm
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    {Z Z' : localHoObjects s} (f : X ⟶ (localHoInclusion s).obj Z) (g : Z ⟶ Z') :
    (localHoHomEquiv s X Z').symm (f ≫ (localHoInclusion s).map g) =
      (localHoHomEquiv s X Z).symm f ≫ g := by
  simpa only [localHoAdjunction_homEquiv s] using
    (localHoAdjunction s).homEquiv_naturality_right_symm f g

/-- The full forward Hom function is precomposition by the original lifted unit. -/
theorem localHoHomEquiv_whole_forward
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (Z : localHoObjects s) :
    (localHoHomEquiv s X Z).toFun =
      fun g => (localReplacementHoUnit s).app X ≫ g.hom := rfl

/-- The full inverse function retains the prescribed original unit composite. -/
theorem localHoHomEquiv_whole_inverse_section
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (Z : localHoObjects s) :
    (fun g => (localReplacementHoUnit s).app X ≫
      ((localHoHomEquiv s X Z).symm g).hom) = fun g => g := by
  funext g
  exact localHoHomEquiv_symm_section s X Z g

/-- Both complete original Hom functions round trip at every local target. -/
theorem localHoHomEquiv_roundtrips
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (Z : localHoObjects s) :
    (∀ f, (localHoHomEquiv s X Z).symm (localHoHomEquiv s X Z f) = f) ∧
      (∀ g, localHoHomEquiv s X Z ((localHoHomEquiv s X Z).symm g) = g) :=
  ⟨(localHoHomEquiv s X Z).symm_apply_apply, (localHoHomEquiv s X Z).apply_symm_apply⟩

/-- The actual counit is the original inverse Hom function at the identity. -/
theorem localHoAdjunction_counit_hom
    (Z : localHoObjects s) :
    ((localHoAdjunction s).counit.app Z).hom =
      ((localHoHomEquiv s ((localHoInclusion s).obj Z) Z).symm (𝟙 _)).hom := rfl

/-- The complete left triangle keeps the original unit, reflector and counit maps. -/
theorem localHoAdjunction_whole_left_triangle :
    (fun X => (localHoReflector s).map ((localHoAdjunction s).unit.app X) ≫
      (localHoAdjunction s).counit.app ((localHoReflector s).obj X)) =
      fun X => 𝟙 ((localHoReflector s).obj X) := by
  funext X
  exact (localHoAdjunction s).left_triangle_components X

/-- The complete right triangle retains the original local-object inclusion. -/
theorem localHoAdjunction_whole_right_triangle :
    (fun Z => (localHoAdjunction s).unit.app ((localHoInclusion s).obj Z) ≫
      (localHoInclusion s).map ((localHoAdjunction s).counit.app Z)) =
      fun Z => 𝟙 ((localHoInclusion s).obj Z) := by
  funext Z
  exact (localHoAdjunction s).right_triangle_components Z

/-- The actual adjunction unit is the SAME original comparison on every Ho object. -/
theorem localHoAdjunction_unit_app
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (localHoAdjunction s).unit.app X = (localReplacementHoUnit s).app X := by
  change (localReplacementHoUnit s).app X ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The actual counit projection is inverse to the original unit at a local object. -/
theorem localHoAdjunction_counit_projection_inverse
    (Z : localHoObjects s) :
    (localReplacementHoUnit s).app ((localHoInclusion s).obj Z) ≫
      ((localHoAdjunction s).counit.app Z).hom = 𝟙 _ := by
  rw [localHoAdjunction_counit_hom]
  exact localHoHomEquiv_symm_section s ((localHoInclusion s).obj Z) Z (𝟙 _)

/-- The projected counit is the actual inverse of the same original local unit. -/
theorem localHoAdjunction_counit_projection_eq_inv
    (Z : localHoObjects s) :
    letI : IsIso ((localReplacementHoUnit s).app ((localHoInclusion s).obj Z)) :=
      localReplacementHoUnit_isIso_at_local s Z
    ((localHoAdjunction s).counit.app Z).hom =
      inv ((localReplacementHoUnit s).app ((localHoInclusion s).obj Z)) := by
  let _ : IsIso ((localReplacementHoUnit s).app ((localHoInclusion s).obj Z)) :=
    localReplacementHoUnit_isIso_at_local s Z
  apply (cancel_epi ((localReplacementHoUnit s).app ((localHoInclusion s).obj Z))).mp
  rw [localHoAdjunction_counit_projection_inverse, IsIso.hom_inv_id]

/-- The original induced inclusion is reflective by this actual full adjunction. -/
@[instance_reducible]
def localHoReflective : Reflective (localHoInclusion s) where
  toFull := inferInstance
  toFaithful := inferInstance
  L := (localHoReflector s)
  adj := (localHoAdjunction s)

/-- The ordinary Ho weak class is the image of the SAME original native local Hom tests. -/
def localHoTestClass :
    MorphismProperty (HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) :=
  (localTestEquivalences s).map (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))

private instance localHoTestClass_respectsIso : (localHoTestClass s).RespectsIso := by
  unfold localHoTestClass
  infer_instance

/-- The entire actual reflector inverts every original native local testing arrow. -/
theorem localTestLocalization_inverts :
    (localTestEquivalences s).IsInvertedBy
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ⋙ (localHoReflector s)) := by
  intro X Y f hf
  have h : IsIso ((localReplacementHo s).map
      ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f)) := by
    rw [(localReplacementHo_map_projected s)]
    exact (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp
      (((cofibrantLocalReplacement_map_weak_iff s) f).mpr hf)
  let _ : IsIso ((localHoInclusion s).map ((localHoReflector s).map
      ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f))) := h
  change IsIso ((localHoReflector s).map
    ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f))
  exact isIso_of_reflects_iso _ (localHoInclusion s)

/-- The actual reflector also inverts the complete ordinary-Ho image class. -/
theorem localHoReflector_inverts : (localHoTestClass s).IsInvertedBy (localHoReflector s) := by
  simpa only [localHoTestClass, MorphismProperty.IsInvertedBy.map_iff] using
    (localTestLocalization_inverts s)

/-- Every original Ho reflection unit is in that actual image class via a whole Arrow Iso. -/
theorem localHoAdjunction_unit_mem
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (localHoTestClass s) ((localHoAdjunction s).unit.app X) := by
  obtain ⟨Y, rfl⟩ := (Localization.Construction.objEquiv
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I))).surjective X
  let Q : (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤ (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
    Replacement.cofibrantReplacement (B := B)
  let e : Q ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ≅
      toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
    Replacement.cofibrantReplacementProjectionIso (B := B)
  let _ : IsCofibrant (Q.obj Y) := Replacement.isCofibrant_cofibrantReplacement Y
  let a : Arrow.mk ((localHoAdjunction s).unit.app
      ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Y)) ≅
      Arrow.mk ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((localReplacementUnit s).app (Q.obj Y))) :=
    Arrow.isoMk' _ _ (e.app Y).symm (Iso.refl _) (by
      rw [(localHoAdjunction_unit_app s), (localReplacementHoUnit_app_projected s),
        (cofibrantLocalComparison_app s)]
      change e.inv.app Y ≫ (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((localReplacementUnit s).app (Q.obj Y)) =
        (e.inv.app Y ≫ (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
          ((localReplacementUnit s).app (Q.obj Y))) ≫ 𝟙 _
      exact (Category.comp_id _).symm)
  have h := (localTestEquivalences s).map_mem_map
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    ((localReplacementUnit s).app (Q.obj Y)) ((localReplacementUnit_localTestEquivalence s) _)
  exact ((localHoTestClass s).arrow_mk_iso_iff a).mpr h

/-- This actual ordinary-Ho reflector is a categorical localization of the original local tests. -/
theorem localHoReflector_isLocalization :
    (localHoReflector s).IsLocalization (localHoTestClass s) :=
  (localHoAdjunction s).isLocalization_leftAdjoint (localHoTestClass s)
    (localHoReflector_inverts s) (localHoAdjunction_unit_mem s)

/-- The actual native categorical localization functor
uses the original level projection and reflector. -/
def localTestLocalization : (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤ (localHoObjects s) :=
  toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ⋙ (localHoReflector s)

/-- The full composite is an actual categorical localization
at the SAME original K-local Hom tests. -/
theorem localTestLocalization_isLocalization :
    (localTestLocalization s).IsLocalization (localTestEquivalences s) := by
  let _ : (localHoReflector s).IsLocalization (localHoTestClass s) :=
    (localHoReflector_isLocalization s)
  exact Functor.IsLocalization.comp
    (L₁ := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (W₁ := weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (L₂ := (localHoReflector s)) (W₂ := (localHoTestClass s))
    (localTestEquivalences s) (localTestLocalization_inverts s)
    (levelWeak_le_localTestEquivalences s) le_rfl

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The actual original Q-inverse/K-unit comparison is invertible precisely on original Ω inputs. -/
theorem localReplacementHoUnit_isIso_iff_isOmega_projected
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    IsIso ((localReplacementHoUnit s).app
        ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X)) ↔
      IsOmega s X := by
  constructor
  · intro h
    let Q := Replacement.cofibrantReplacement (A := I) (B := B)
    let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
    let e : Q ⋙ H ≅ H := Replacement.cofibrantReplacementProjectionIso (B := B)
    rw [localReplacementHoUnit_app_projected, cofibrantLocalComparison_app] at h
    change IsIso (e.inv.app X ≫ H.map ((localReplacementUnit s).app (Q.obj X))) at h
    let _ : IsIso (e.inv.app X) := inferInstance
    let _ : IsIso (e.inv.app X ≫ H.map ((localReplacementUnit s).app (Q.obj X))) := h
    have hUnit : IsIso (H.map ((localReplacementUnit s).app (Q.obj X))) :=
      IsIso.of_isIso_comp_left (e.inv.app X) _
    have hWeak : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)
        ((localReplacementUnit s).app (Q.obj X)) :=
      (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mpr hUnit
    have hQ : IsOmega s (Q.obj X) :=
      (originalOmega_iff_of_levelWeak s _ hWeak).mpr
        ((lifting_toZero_iff_isOmega s _).mp (localReplacement_isLocal s (Q.obj X)))
    exact (originalOmega_iff_of_levelWeak s _
      (Replacement.cofibrantReplacementCounit_mem_weakEquivalences X)).mp hQ
  · intro hX
    rw [localReplacementHoUnit_app_projected]
    exact cofibrantLocalComparison_isIso_of_local s X
      ((lifting_toZero_iff_isOmega s X).mpr hX)

/-- Every ordinary Ho object retains the original native Ω predicate through its actual object
equivalence. -/
theorem localReplacementHoUnit_isIso_iff_isOmega
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    IsIso ((localReplacementHoUnit s).app X) ↔ IsOmega s (localHoUnderlying X) := by
  change IsIso ((localReplacementHoUnit s).app
    ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
      (localHoUnderlying X))) ↔ IsOmega s (localHoUnderlying X)
  exact localReplacementHoUnit_isIso_iff_isOmega_projected s (localHoUnderlying X)

/-- The full native Ω subcategory uses actual original level-Ho objects and all their Hom
morphisms. -/
def omegaHoObjectProperty :
    ObjectProperty (HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) :=
  fun X => IsOmega s (localHoUnderlying X)

/-- Every original lifted Q/K image satisfies this actual original native Ω predicate. -/
theorem omegaHoObjectProperty_image
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    omegaHoObjectProperty s ((localReplacementHo s).obj X) :=
  (localReplacementHoUnit_isIso_iff_isOmega s _).mp
    (localReplacementHoUnit_isIso_at_image s X)

/-- This target-unit Iso is derived from the actual native Ω predicate, rather than supplied. -/
theorem omegaHoObjectProperty_unit_isIso
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hX : omegaHoObjectProperty s X) : IsIso ((localReplacementHoUnit s).app X) :=
  (localReplacementHoUnit_isIso_iff_isOmega s X).mpr hX

/-- Actual original Ω objects with complete ordinary level-Ho morphisms. -/
abbrev omegaHoObjects := (omegaHoObjectProperty s).FullSubcategory

/-- The full inclusion retains the original level-Ho object and every original Ho map. -/
abbrev omegaHoInclusion := (omegaHoObjectProperty s).ι

/-- The original Q/K reflector has values in the actual full native Ω category. -/
def omegaHoReflector : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤
    omegaHoObjects s :=
  CategoryTheory.Functor.CoaugmentedReflection.testFunctor (localReplacementHo s)
    (omegaHoObjectProperty s) (omegaHoObjectProperty_image s)

/-- The complete Ω reflector followed by its full inclusion is the original Q/K action. -/
theorem omegaHoReflector_comp_inclusion :
    omegaHoReflector s ⋙ omegaHoInclusion s = localReplacementHo s := rfl

/-- The actual target-unit Iso retains the original lifted Q-inverse/K-unit comparison. -/
def omegaHoUnitIso (Z : omegaHoObjects s) :
    Z.obj ≅ (localReplacementHo s).obj Z.obj :=
  CategoryTheory.Functor.CoaugmentedReflection.testUnitIso (localReplacementHo s)
    (localReplacementHoUnit s) (omegaHoObjectProperty s)
    (omegaHoObjectProperty_unit_isIso s) Z

/-- The complete Ω Hom equivalence uses the original lifted unit and original Q/K map action. -/
def omegaHoHomEquiv
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) (Z : omegaHoObjects s) :
    ((omegaHoReflector s).obj X ⟶ Z) ≃ (X ⟶ Z.obj) :=
  CategoryTheory.Functor.CoaugmentedReflection.testHomEquiv (localReplacementHo s)
    (localReplacementHoUnit s) (localReplacementHoUnit_isIso_at_image s)
    (localReplacementHo_mapUnit_isIso s) (omegaHoObjectProperty s)
    (omegaHoObjectProperty_image s) (omegaHoObjectProperty_unit_isIso s) X Z

/-- The entire forward Ω Hom function is literal original lifted-unit precomposition. -/
theorem omegaHoHomEquiv_wholeForward
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) (Z : omegaHoObjects s) :
    (omegaHoHomEquiv s X Z).toFun = fun g => (localReplacementHoUnit s).app X ≫ g.hom := rfl

/-- The entire inverse Ω Hom function acts on arbitrary ordinary Ho maps by the original Q/K
functor. -/
theorem omegaHoHomEquiv_wholeInverse
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) (Z : omegaHoObjects s) :
    (fun g => ((omegaHoHomEquiv s X Z).symm g).hom) =
      fun g => (localReplacementHo s).map g ≫ (omegaHoUnitIso s Z).inv := by
  funext g
  exact CategoryTheory.Functor.CoaugmentedReflection.testHomEquiv_symm_apply
    (localReplacementHo s) (localReplacementHoUnit s)
    (localReplacementHoUnit_isIso_at_image s) (localReplacementHo_mapUnit_isIso s)
    (omegaHoObjectProperty s) (omegaHoObjectProperty_image s)
    (omegaHoObjectProperty_unit_isIso s) X Z g

/-- This native Ω adjunction is derived from the complete original lifted Hom functions. -/
def omegaHoAdjunction : omegaHoReflector s ⊣ omegaHoInclusion s :=
  CategoryTheory.Functor.CoaugmentedReflection.testAdjunction (localReplacementHo s)
    (localReplacementHoUnit s) (localReplacementHoUnit_isIso_at_image s)
    (localReplacementHo_mapUnit_isIso s) (omegaHoObjectProperty s)
    (omegaHoObjectProperty_image s) (omegaHoObjectProperty_unit_isIso s)

/-- The full native Ω adjunction retains the entire original Ω Hom equivalence. -/
theorem omegaHoAdjunction_homEquiv :
    (omegaHoAdjunction s).homEquiv = omegaHoHomEquiv s := by
  funext X Z
  exact CategoryTheory.Functor.CoaugmentedReflection.testAdjunction_homEquiv
    (localReplacementHo s) (localReplacementHoUnit s)
    (localReplacementHoUnit_isIso_at_image s) (localReplacementHo_mapUnit_isIso s)
    (omegaHoObjectProperty s) (omegaHoObjectProperty_image s)
    (omegaHoObjectProperty_unit_isIso s) X Z

/-- The actual Ω adjunction unit is the same original Q-inverse/K-unit at every Ho object. -/
theorem omegaHoAdjunction_unit_app
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (omegaHoAdjunction s).unit.app X = (localReplacementHoUnit s).app X :=
  CategoryTheory.Functor.CoaugmentedReflection.testAdjunction_unit_app
    (localReplacementHo s) (localReplacementHoUnit s)
    (localReplacementHoUnit_isIso_at_image s) (localReplacementHo_mapUnit_isIso s)
    (omegaHoObjectProperty s) (omegaHoObjectProperty_image s)
    (omegaHoObjectProperty_unit_isIso s) X

/-- The whole actual counit function is the original inverse target-unit function. -/
theorem omegaHoAdjunction_wholeCounit :
    (fun Z => ((omegaHoAdjunction s).counit.app Z).hom) =
      fun Z => (omegaHoUnitIso s Z).inv := by
  funext Z
  exact CategoryTheory.Functor.CoaugmentedReflection.testAdjunction_counit_app
    (localReplacementHo s) (localReplacementHoUnit s)
    (localReplacementHoUnit_isIso_at_image s) (localReplacementHo_mapUnit_isIso s)
    (omegaHoObjectProperty s) (omegaHoObjectProperty_image s)
    (omegaHoObjectProperty_unit_isIso s) Z

/-- Both entire Ω adjunction triangles retain all original ordinary-Ho input maps. -/
theorem omegaHoAdjunction_wholeTriangles :
    ((fun X => (omegaHoReflector s).map ((omegaHoAdjunction s).unit.app X) ≫
      (omegaHoAdjunction s).counit.app ((omegaHoReflector s).obj X)) =
      fun X => 𝟙 ((omegaHoReflector s).obj X)) ∧
      ((fun Z => (omegaHoAdjunction s).unit.app ((omegaHoInclusion s).obj Z) ≫
        (omegaHoInclusion s).map ((omegaHoAdjunction s).counit.app Z)) =
        fun Z => 𝟙 ((omegaHoInclusion s).obj Z)) := by
  constructor
  · funext X
    exact (omegaHoAdjunction s).left_triangle_components X
  · funext Z
    exact (omegaHoAdjunction s).right_triangle_components Z

/-- Arbitrary ordinary-Ho source arrows retain the complete native Ω forward Hom function. -/
theorem omegaHoHomEquiv_source
    {X X' : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)}
    (a : X' ⟶ X) (Z : omegaHoObjects s) (g : (omegaHoReflector s).obj X ⟶ Z) :
    omegaHoHomEquiv s X' Z ((omegaHoReflector s).map a ≫ g) =
      a ≫ omegaHoHomEquiv s X Z g := by
  simpa only [omegaHoAdjunction_homEquiv s] using
    (omegaHoAdjunction s).homEquiv_naturality_left a g

/-- Arbitrary ordinary-Ho source arrows retain the complete native Ω inverse Hom function. -/
theorem omegaHoHomEquiv_source_symm
    {X X' : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)}
    (a : X' ⟶ X) (Z : omegaHoObjects s) (g : X ⟶ Z.obj) :
    (omegaHoHomEquiv s X' Z).symm (a ≫ g) =
      (omegaHoReflector s).map a ≫ (omegaHoHomEquiv s X Z).symm g := by
  simpa only [omegaHoAdjunction_homEquiv s] using
    (omegaHoAdjunction s).homEquiv_naturality_left_symm a g

/-- Every actual Ω-category target arrow retains the full native forward Hom function. -/
theorem omegaHoHomEquiv_target
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    {Z Z' : omegaHoObjects s} (g : (omegaHoReflector s).obj X ⟶ Z) (b : Z ⟶ Z') :
    omegaHoHomEquiv s X Z' (g ≫ b) =
      omegaHoHomEquiv s X Z g ≫ (omegaHoInclusion s).map b := by
  simpa only [omegaHoAdjunction_homEquiv s] using
    (omegaHoAdjunction s).homEquiv_naturality_right g b

/-- Every actual Ω-category target arrow retains the entire native inverse Hom function. -/
theorem omegaHoHomEquiv_target_symm
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    {Z Z' : omegaHoObjects s} (g : X ⟶ Z.obj) (b : Z ⟶ Z') :
    (omegaHoHomEquiv s X Z').symm (g ≫ (omegaHoInclusion s).map b) =
      (omegaHoHomEquiv s X Z).symm g ≫ b := by
  simpa only [omegaHoAdjunction_homEquiv s] using
    (omegaHoAdjunction s).homEquiv_naturality_right_symm g b

/-- Every actual local native diagram is an original Ω diagram in the same ordinary Ho carrier. -/
def localHoToOmegaHo : localHoObjects s ⥤ omegaHoObjects s where
  obj Z := ⟨(toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z.diagram,
    (lifting_toZero_iff_isOmega s Z.diagram).mp Z.isLocal⟩
  map g := ObjectProperty.homMk g.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Every Ω Ho object recovers its original native diagram through the same original object
equivalence. -/
def omegaHoToLocalHo : omegaHoObjects s ⥤ localHoObjects s where
  obj Z := ⟨localHoUnderlying Z.obj,
    (lifting_toZero_iff_isOmega s (localHoUnderlying Z.obj)).mpr Z.property⟩
  map g := InducedCategory.homMk g.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The actual native object equivalence gives the entire local-to-Ω-to-local unit Iso. -/
def localHoOmegaUnitIso :
    𝟭 (localHoObjects s) ≅ localHoToOmegaHo s ⋙ omegaHoToLocalHo s :=
  NatIso.ofComponents (fun _ => InducedCategory.isoMk (Iso.refl _)) (by
    intro X Y f
    apply InducedCategory.hom_ext
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    rw [Category.comp_id, Category.id_comp])

/-- The same native object equivalence gives the entire Ω-to-local-to-Ω counit Iso. -/
def localHoOmegaCounitIso :
    omegaHoToLocalHo s ⋙ localHoToOmegaHo s ≅ 𝟭 (omegaHoObjects s) :=
  NatIso.ofComponents (fun _ => (omegaHoObjectProperty s).isoMk (Iso.refl _)) (by
    intro X Y f
    apply ObjectProperty.hom_ext
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    rw [Category.comp_id, Category.id_comp])

/-- K-local native objects and actual full Ω Ho objects have the same whole Ho carrier. -/
def localHoOmegaEquivalence : localHoObjects s ≌ omegaHoObjects s where
  functor := localHoToOmegaHo s
  inverse := omegaHoToLocalHo s
  unitIso := localHoOmegaUnitIso s
  counitIso := localHoOmegaCounitIso s
  functor_unitIso_comp X := by
    apply ObjectProperty.hom_ext
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _

/-- The complete Ω Hom carrier is the original native local-Ho Hom carrier through identity maps. -/
def omegaToOriginalLocalHomEquiv
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) (Z : omegaHoObjects s) :
    ((omegaHoReflector s).obj X ⟶ Z) ≃
      ((localHoReflector s).obj X ⟶ (omegaHoToLocalHo s).obj Z) :=
  ((omegaHoObjectProperty s).fullyFaithfulι.homEquiv
    (X := (omegaHoReflector s).obj X) (Y := Z)).trans
      (InducedCategory.homEquiv
        (D := HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
        (F := fun T : LocalObject s =>
          (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj T.diagram)
        (X := (localHoReflector s).obj X) (Y := (omegaHoToLocalHo s).obj Z)).symm

/-- The entire Ω Hom equivalence retains the original local reflector's full chosen equivalence. -/
theorem omegaHoHomEquiv_original_equivalence
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) (Z : omegaHoObjects s) :
    omegaHoHomEquiv s X Z =
      (omegaToOriginalLocalHomEquiv s X Z).trans
        (localHoHomEquiv s X ((omegaHoToLocalHo s).obj Z)) := by
  apply Equiv.ext
  intro g
  rfl

/-- The complete original K-local reflector has exactly the same Ω-reflected object and Ho map
action. -/
theorem localHoReflector_comp_omega :
    localHoReflector s ⋙ localHoToOmegaHo s = omegaHoReflector s := rfl

/-- The actual native Ω reflector inverts the same complete original local testing arrows. -/
theorem omegaTestLocalization_inverts :
    (localTestEquivalences s).IsInvertedBy
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ⋙ omegaHoReflector s) := by
  intro X Y f hf
  have h := localReplacementHo_map_isIso_of_localTest s f hf
  let _ : IsIso ((omegaHoInclusion s).map ((omegaHoReflector s).map
      ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f))) := h
  change IsIso ((omegaHoReflector s).map
    ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f))
  exact isIso_of_reflects_iso _ (omegaHoInclusion s)

/-- The full original local-test image class is inverted on arbitrary ordinary Ho inputs. -/
theorem omegaHoReflector_inverts : (localHoTestClass s).IsInvertedBy (omegaHoReflector s) := by
  simpa only [localHoTestClass, MorphismProperty.IsInvertedBy.map_iff] using
    omegaTestLocalization_inverts s

/-- Every new Ω adjunction unit is the same actual original unit-class witness. -/
theorem omegaHoAdjunction_unit_mem
    (X : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (localHoTestClass s) ((omegaHoAdjunction s).unit.app X) := by
  rw [omegaHoAdjunction_unit_app, ← localHoAdjunction_unit_app]
  exact localHoAdjunction_unit_mem s X

/-- The actual full ordinary-Ho Ω reflector is a localization of the original Ho image class. -/
theorem omegaHoReflector_isLocalization :
    (omegaHoReflector s).IsLocalization (localHoTestClass s) :=
  (omegaHoAdjunction s).isLocalization_leftAdjoint (localHoTestClass s)
    (omegaHoReflector_inverts s) (omegaHoAdjunction_unit_mem s)

/-- The native projection followed by the actual Ω reflector is the original Ω localization. -/
def omegaTestLocalization : EnrichedFunctorCat PointedCGWH.{u, v} I ⥤ omegaHoObjects s :=
  toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ⋙ omegaHoReflector s

/-- This whole native functor localizes the complete canonical original Ω Hom-testing class. -/
theorem omegaTestLocalization_isLocalization :
    (omegaTestLocalization s).IsLocalization (localTestEquivalences s) := by
  let _ : (omegaHoReflector s).IsLocalization (localHoTestClass s) :=
    omegaHoReflector_isLocalization s
  exact Functor.IsLocalization.comp
    (L₁ := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (W₁ := weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (L₂ := omegaHoReflector s) (W₂ := localHoTestClass s)
    (localTestEquivalences s) (omegaTestLocalization_inverts s)
    (levelWeak_le_localTestEquivalences s) le_rfl

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
