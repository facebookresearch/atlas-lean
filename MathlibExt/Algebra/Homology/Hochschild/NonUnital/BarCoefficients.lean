/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.ConnesBoundary
public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Nonunital bar complexes with coefficients

The coefficient bar has terms V ⊗[k] C*(I),
with b′ on the algebra word and the identity on V.
Tensor bifunctor maps preserve the coefficient and
algebra actions. H-unitality quantifies over every
coefficient module in the specified carrier universe.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  (V : Type w) [AddCommGroup V] [Module k V]

/-- The original source bar with arbitrary coefficients and zero augmentation. -/
def barComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  (((ModuleCat.tensorBifunctorAt k :
      ModuleCat.{w} k ⥤ ModuleCat.{max u v} k ⥤ ModuleCat.{max u v w} k).obj (ModuleCat.of k V)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (bPrimeComplex k A)

/-- Every bar degree retains the original V and algebra tensor word. -/
@[simp]
theorem barComplex_X (n : ℕ) :
    (barComplex k A V).X n = ModuleCat.of k (V ⊗[k] (A ⊗[k] TensorPower k n A)) := rfl

/-- The original differential is identity on V and the original b-prime on the algebra word. -/
@[simp]
theorem barComplex_d (n : ℕ) :
    (barComplex k A V).d (n + 1) n =
      ModuleCat.ofHom (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
        ((bPrimeComplex k A).d (n + 1) n).hom) := rfl

/-- An left unit contracts the coefficient bar by the same original insertion. -/
def barContractionOfLeftUnit (e : A) (hLeft : ∀ a : A, e * a = a) :
    Homotopy (𝟙 (barComplex k A V)) 0 := by
  unfold barComplex
  let F : ModuleCat.{max u v} k ⥤ ModuleCat.{max u v w} k :=
    (ModuleCat.tensorBifunctorAt k :
      ModuleCat.{w} k ⥤ ModuleCat.{max u v} k ⥤ ModuleCat.{max u v w} k).obj (ModuleCat.of k V)
  change Homotopy (𝟙 ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (bPrimeComplex k A))) 0
  let H := F.mapHomotopy (bPrimeContractionOfLeftUnit k A e hLeft)
  refine { hom := H.hom, zero := H.zero, comm := ?_ }
  intro n
  have hi : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map (𝟙 (bPrimeComplex k A))).f n =
      𝟙 (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (bPrimeComplex k A)).X n) := by
    rw [(F.mapHomologicalComplex (ComplexShape.down ℕ)).map_id]
    rfl
  have hz : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (0 : bPrimeComplex k A ⟶ bPrimeComplex k A)).f n = 0 := by
    rw [(F.mapHomologicalComplex (ComplexShape.down ℕ)).map_zero]
    rfl
  simpa only [hi, hz, HomologicalComplex.id_f, HomologicalComplex.zero_f_apply] using H.comm n

/-- The contraction leaves V unchanged and inserts the unit into the original algebra word. -/
theorem barContractionOfLeftUnit_hom (e : A) (hLeft : ∀ a : A, e * a = a) (n : ℕ) :
    (barContractionOfLeftUnit k A V e hLeft).hom n (n + 1) =
      ModuleCat.ofHom (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
        (extraDegeneracyWith k A e n).hom) := by
  change ((ModuleCat.tensorBifunctorAt k :
      ModuleCat.{w} k ⥤ ModuleCat.{max u v} k ⥤ ModuleCat.{max u v w} k).obj (ModuleCat.of k V)).map
    ((bPrimeContractionOfLeftUnit k A e hLeft).hom n (n + 1)) = _
  rw [bPrimeContractionOfLeftUnit_hom]
  rfl

/-- The mapped contraction proves acyclicity for arbitrary V, without coefficient flatness. -/
theorem barComplex_acyclic_of_leftUnit (e : A) (hLeft : ∀ a : A, e * a = a) :
    (barComplex k A V).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).mpr
  have h := (barContractionOfLeftUnit k A V e hLeft).homologyMap_eq n
  simpa only [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] using h

/-- The source H-unital predicate checks every coefficient module, with its independent universe. -/
def IsHUnital : Prop :=
  ∀ (V : Type w) [AddCommGroup V] [Module k V], (barComplex k A V).Acyclic

/-- The source left-unit condition earns H-unitality for every coefficient module. -/
theorem isHUnital_of_leftUnit (e : A) (hLeft : ∀ a : A, e * a = a) : IsHUnital.{u, v, w} k A := by
  intro V _ _
  exact barComplex_acyclic_of_leftUnit k A V e hLeft

section OriginalMaps

variable {k A V} {B : Type v} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]
  {W : Type w} [AddCommGroup W] [Module k W]

/-- The original nonunital map acts on all original b-prime factors. -/
def barAlgebraComplexMap (f : A →ₙₐ[k] B) : bPrimeComplex k A ⟶ bPrimeComplex k B :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (TensorPower.consLevelMap (f : A →ₗ[k] B) n))
    (fun n => by
      apply ModuleCat.hom_ext
      exact (bPrimeComplex_d_natural f n).symm)

/-- The native independently sized tensor transformation maps the coefficient V. -/
def barCoefficientMap (f : V →ₗ[k] W) : barComplex k A V ⟶ barComplex k A W :=
  (((ModuleCat.tensorBifunctorAt k :
      ModuleCat.{w} k ⥤ ModuleCat.{max u v} k ⥤ ModuleCat.{max u v w} k).map (ModuleCat.ofHom f)).mapHomologicalComplex
    (ComplexShape.down ℕ)).app (bPrimeComplex k A)

/-- The original algebra map gives the coefficient-identity bar map. -/
def barAlgebraMap (f : A →ₙₐ[k] B) : barComplex k A V ⟶ barComplex k B V :=
  (((ModuleCat.tensorBifunctorAt k :
      ModuleCat.{w} k ⥤ ModuleCat.{max u v} k ⥤ ModuleCat.{max u v w} k).obj (ModuleCat.of k V)).mapHomologicalComplex
    (ComplexShape.down ℕ)).map (barAlgebraComplexMap f)

/-- The source joint map retains both original maps. -/
def barJointMap (f : V →ₗ[k] W) (g : A →ₙₐ[k] B) : barComplex k A V ⟶ barComplex k B W :=
  barCoefficientMap f ≫ barAlgebraMap g

/-- Every original joint degree map is the native tensor map on f and the original algebra factors of g. -/
theorem barJointMap_f (f : V →ₗ[k] W) (g : A →ₙₐ[k] B) (n : ℕ) :
    (barJointMap f g).f n = ModuleCat.ofHom
      (TensorProduct.map f (TensorPower.consLevelMap (g : A →ₗ[k] B) n)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext' (M := V) (N := (A ⊗[k] TensorPower k n A))
  intro v x
  simp only [barJointMap, HomologicalComplex.comp_f, barCoefficientMap, barAlgebraMap,
    ModuleCat.hom_comp, LinearMap.comp_apply]
  change TensorProduct.map (LinearMap.id : W →ₗ[k] W) (TensorPower.consLevelMap (g : A →ₗ[k] B) n)
      (TensorProduct.map f (LinearMap.id : (A ⊗[k] TensorPower k n A) →ₗ[k] _) (v ⊗ₜ[k] x)) = _
  simp only [TensorProduct.map_tmul, LinearMap.id_apply]
  change f v ⊗ₜ[k] TensorPower.consLevelMap (g : A →ₗ[k] B) n x =
    TensorProduct.map f (TensorPower.consLevelMap (g : A →ₗ[k] B) n) (v ⊗ₜ[k] x)
  exact (TensorProduct.map_tmul _ _ _ _).symm

/-- The joint map preserves the original coefficient and every original word value. -/
theorem barJointMap_tprod (f : V →ₗ[k] W) (g : A →ₙₐ[k] B) (n : ℕ) (v : V) (m : A) (a : Fin n → A) :
    ((barJointMap f g).f n).hom (v ⊗ₜ[k] (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      f v ⊗ₜ[k] (g m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => g (a i))) := by
  rw [barJointMap_f]
  change TensorProduct.map f (TensorPower.consLevelMap (g : A →ₗ[k] B) n)
    (v ⊗ₜ[k] (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = _
  simp only [TensorProduct.map_tmul,
    TensorPower.consLevelMap, PiTensorProduct.map_tprod]
  rfl

end OriginalMaps

end ModuleCat.Algebra.Hochschild.NonUnital
