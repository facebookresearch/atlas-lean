/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.ProperShuffleCotangentNaturality
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Proper-shuffle cotangent diagrams

Algebras augmented into B act on a B-module M through
the augmentation. Proper quotients and coefficient
cotangents form functors, and their shifted chain
augmentations are natural under simplicial operators.
The rational kernel identification supports these
quotient maps; flatness is not required.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.AugmentedAlgebra

variable (k : Type u) [CommRing k] [Algebra ℚ k] (B : CommAlgCat.{max u v} k)
  (M : Type w) [AddCommGroup M] [Module k M] [Module B M]
  [SMulCommClass k B M] [IsScalarTower k B M]

/-- The original coefficient action is pulled back along the stored augmentation. -/
local instance coefficientModule (P : Over B) : Module P.left M :=
  Module.compHom M P.hom.hom.toRingHom

/-- The original ground and pulled-back algebra actions commute by the original B-action law. -/
local instance coefficientCommutes (P : Over B) : SMulCommClass k P.left M where
  smul_comm r p m := by
    change r • (P.hom.hom p • m) = P.hom.hom p • (r • m)
    exact smul_comm r (P.hom.hom p) m

/-- The original ground action and pulled-back algebra action form a tower by the algebra-map scalar law. -/
local instance coefficientTower (P : Over B) : IsScalarTower k P.left M where
  smul_assoc r p m := by
    change P.hom.hom (r • p) • m = r • (P.hom.hom p • m)
    exact (congrArg (fun b : B => b • m) (P.hom.hom.toLinearMap.map_smul r p)).trans
      (smul_assoc r (P.hom.hom p) m)

omit [Algebra ℚ k] [SMulCommClass k B M] [IsScalarTower k B M] in
/-- The original augmentation-square equation earns the coefficient-map action compatibility. -/
theorem coefficientCompatibility {P Q : Over B} (f : P ⟶ Q) :
    ∀ p : P.left, ∀ m : M, (LinearMap.id : M →ₗ[k] M) (p • m) =
      f.left.hom p • (LinearMap.id : M →ₗ[k] M) m := by
  intro p m
  change P.hom.hom p • m = Q.hom.hom (f.left.hom p) • m
  exact congrArg (fun b : B => b • m) (ConcreteCategory.congr_hom f.w p).symm

/-- The shifted proper quotient of the original algebra, with the original coefficient M. -/
def complex (P : Over B) : ChainComplex (ModuleCat.{max u v w} k) ℕ := properCotangentComplex k P.left M

/-- The original operator on the shifted quotient; the coefficient remains unchanged. -/
def map {P Q : Over B} (f : P ⟶ Q) : complex k B M P ⟶ complex k B M Q :=
  cotangentChainMap k f.left.hom (LinearMap.id : M →ₗ[k] M) (coefficientCompatibility k B M f)

/-- The full shifted proper-quotient functor of the original augmented algebras. -/
def functor : Over B ⥤ ChainComplex (ModuleCat.{max u v w} k) ℕ where
  obj := complex k B M
  map := map k B M
  map_id P := by
    change HomologicalComplex.restrictionMap
        (chainMap k (AlgHom.id k P.left) (LinearMap.id : M →ₗ[k] M) _) ComplexShape.positiveNatEmbedding =
      𝟙 ((positiveQuotient k P.left M).restriction ComplexShape.positiveNatEmbedding)
    exact (congrArg (fun t : positiveQuotient k P.left M ⟶ positiveQuotient k P.left M =>
      HomologicalComplex.restrictionMap t ComplexShape.positiveNatEmbedding) (chainMap_id k)).trans
        (HomologicalComplex.restrictionMap_id (K := positiveQuotient k P.left M) ComplexShape.positiveNatEmbedding)
  map_comp {P Q S} f g := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change quotientLinearMap k (g.left.hom.comp f.left.hom) (LinearMap.id : M →ₗ[k] M) (n + 1) =
      (quotientLinearMap k g.left.hom (LinearMap.id : M →ₗ[k] M) (n + 1)).comp
        (quotientLinearMap k f.left.hom (LinearMap.id : M →ₗ[k] M) (n + 1))
    exact (by
      simpa only [LinearMap.id_comp] using
        (quotientLinearMap_comp k f.left.hom g.left.hom (LinearMap.id : M →ₗ[k] M)
          (LinearMap.id : M →ₗ[k] M) (n + 1)).symm)

/-- Each original shifted representative is mapped by the original tail algebra map. -/
theorem map_mkQ {P Q : Over B} (f : P ⟶ Q) (n : ℕ)
    (x : M ⊗[k] TensorPower k (n + 1) P.left) :
    ((map k B M f).f n).hom ((rawPositiveRelations k P.left M (n + 1)).mkQ x) =
      (rawPositiveRelations k Q.left M (n + 1)).mkQ
        (ModuleCat.Algebra.Hochschild.linearMap f.left.hom.toNonUnitalAlgHom LinearMap.id (n + 1) x) :=
  quotientLinearMap_mkQ k f.left.hom (LinearMap.id : M →ₗ[k] M) (n + 1) x

/-- The original coefficient cotangent object for the specified augmented algebra. -/
def cotangentModule (P : Over B) : (ModuleCat.{max u v w} k) := coefficientCotangentModule k P.left M

/-- The coefficient cotangent map retains the original one-form coordinates. -/
def cotangentMap {P Q : Over B} (f : P ⟶ Q) : cotangentModule k B M P ⟶ cotangentModule k B M Q :=
  cotangentModuleMap k f.left.hom (LinearMap.id : M →ₗ[k] M) (coefficientCompatibility k B M f)

/-- The original scalar augmentation of the shifted proper quotient. -/
def scalarAugmentation (P : Over B) : (complex k B M P).X 0 ⟶ cotangentModule k B M P :=
  properCotangentScalarAugmentation k P.left M

/-- The original scalar augmentation is surjective, without a coefficient-flatness condition. -/
local instance scalarAugmentation_epi (P : Over B) : Epi (scalarAugmentation k B M P) :=
  (ModuleCat.epi_iff_surjective _).mpr (properCotangentScalarAugmentation_surjective k P.left M)

/-- Every original operator preserves the scalar augmentation. -/
@[reassoc]
theorem scalarAugmentation_naturality {P Q : Over B} (f : P ⟶ Q) :
    (map k B M f).f 0 ≫ scalarAugmentation k B M Q =
      scalarAugmentation k B M P ≫ cotangentMap k B M f :=
  RationalProperShuffle.scalarAugmentation_naturality k f.left.hom (LinearMap.id : M →ₗ[k] M)
    (coefficientCompatibility k B M f)

/-- The original coefficient cotangent identity is forced by the surjective augmentation square. -/
theorem cotangentMap_id (P : Over B) : cotangentMap k B M (𝟙 P) = 𝟙 (cotangentModule k B M P) := by
  apply (cancel_epi (scalarAugmentation k B M P)).mp
  let t : (complex k B M P).X 0 ⟶ (complex k B M P).X 0 := (map k B M (𝟙 P)).f 0
  have ht : t = 𝟙 ((complex k B M P).X 0) :=
    congrArg (fun q : complex k B M P ⟶ complex k B M P => q.f 0) ((functor k B M).map_id P)
  have h : t ≫ scalarAugmentation k B M P =
      scalarAugmentation k B M P ≫ cotangentMap k B M (𝟙 P) :=
    scalarAugmentation_naturality k B M (𝟙 P)
  exact h.symm.trans
    (((congrArg (fun q : (complex k B M P).X 0 ⟶ (complex k B M P).X 0 =>
      q ≫ scalarAugmentation k B M P) ht).trans (Category.id_comp _)).trans (Category.comp_id _).symm)

/-- Actual coefficient cotangent composition is from the original chain functor and augmentation squares. -/
theorem cotangentMap_comp {P Q S : Over B} (f : P ⟶ Q) (g : Q ⟶ S) :
    cotangentMap k B M (f ≫ g) = cotangentMap k B M f ≫ cotangentMap k B M g := by
  apply (cancel_epi (scalarAugmentation k B M P)).mp
  let tf : (complex k B M P).X 0 ⟶ (complex k B M Q).X 0 := (map k B M f).f 0
  let tg : (complex k B M Q).X 0 ⟶ (complex k B M S).X 0 := (map k B M g).f 0
  let tfg : (complex k B M P).X 0 ⟶ (complex k B M S).X 0 := (map k B M (f ≫ g)).f 0
  have hcomp : tfg = tf ≫ tg :=
    congrArg (fun t : complex k B M P ⟶ complex k B M S => t.f 0) ((functor k B M).map_comp f g)
  have hfg : tfg ≫ scalarAugmentation k B M S =
      scalarAugmentation k B M P ≫ cotangentMap k B M (f ≫ g) :=
    scalarAugmentation_naturality k B M (f ≫ g)
  have hf : tf ≫ scalarAugmentation k B M Q = scalarAugmentation k B M P ≫ cotangentMap k B M f :=
    scalarAugmentation_naturality k B M f
  have hg : tg ≫ scalarAugmentation k B M S = scalarAugmentation k B M Q ≫ cotangentMap k B M g :=
    scalarAugmentation_naturality k B M g
  exact hfg.symm.trans
    ((congrArg (fun t : (complex k B M P).X 0 ⟶ (complex k B M S).X 0 =>
      t ≫ scalarAugmentation k B M S) hcomp).trans
      ((Category.assoc tf tg (scalarAugmentation k B M S)).trans
        ((congrArg (fun t => tf ≫ t) hg).trans
          ((Category.assoc tf (scalarAugmentation k B M Q) (cotangentMap k B M g)).symm.trans
            ((congrArg (fun t => t ≫ cotangentMap k B M g) hf).trans
              (Category.assoc (scalarAugmentation k B M P) (cotangentMap k B M f) (cotangentMap k B M g)))))))

/-- The original coefficient cotangents form an functor on augmented algebras. -/
def cotangentFunctor : Over B ⥤ (ModuleCat.{max u v w} k) where
  obj := cotangentModule k B M
  map := cotangentMap k B M
  map_id := cotangentMap_id k B M
  map_comp := cotangentMap_comp k B M

/-- The all-degree proper-shuffle cotangent augmentations form a natural transformation. -/
def augmentationNat : functor k B M ⟶ cotangentFunctor k B M ⋙ ChainComplex.single₀ (ModuleCat.{max u v w} k) where
  app P := properShuffleCotangentMap k P.left M
  naturality {P Q} (f : P ⟶ Q) := by
    change map k B M f ≫ properShuffleCotangentMap k Q.left M =
      properShuffleCotangentMap k P.left M ≫
        (ChainComplex.single₀ (ModuleCat.{max u v w} k)).map (cotangentMap k B M f)
    exact augmentation_naturality k f.left.hom (LinearMap.id : M →ₗ[k] M)
      (coefficientCompatibility k B M f)

/-- The natural transformation retains the original chain map in every augmented-algebra component. -/
theorem augmentationNat_app (P : Over B) :
    (augmentationNat k B M).app P = properShuffleCotangentMap k P.left M := rfl

end ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.AugmentedAlgebra
