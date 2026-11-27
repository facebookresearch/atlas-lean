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
# Coefficient bars and H-unital nonunital algebras

Let k be a commutative ring and A a nonunital associative k-algebra,
meaning a nonunital ring with a k-module structure and k-bilinear
multiplication. For a k-module V, the coefficient bar has terms
Bar_n(A;V) = V ⊗[k] (A ⊗[k] A^⊗n), n ≥ 0, and differential
id_V ⊗ b′, where b′ multiplies adjacent entries in the algebra word
with alternating signs and omits the cyclic last face. There is no
augmentation term below degree zero.

If e ∈ A satisfies e a = a for every a, inserting e at the front of
the algebra word gives a homotopy id ≃ 0, leaving V unchanged. Hence
this coefficient bar is acyclic for every V, without a flatness condition.
For a specified coefficient world w, H-unitality means precisely that
Bar_*(A;V) is acyclic for every k-module V in Type w.

A k-linear coefficient map f : V → W and a nonunital k-algebra map
g : A → B give a joint chain map that applies f to the coefficient
and g to all algebra entries. The worlds u, v and w of k, A and V
are independent, and the coefficient bar lies in ModuleCat^max(u,v,w)(k).
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

/-- For a commutative ring k, a nonunital k-algebra A with
k-bilinear multiplication and a k-module V, the coefficient bar is
the ℕ-indexed chain complex with degree n equal to
V ⊗[k] (A ⊗[k] A^⊗n) and differential id_V ⊗ b′.
Its degree-zero outgoing differential is zero, with no augmentation
module below it; its carrier height is max(u,v,w). -/
def barComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  (((ModuleCat.tensorBifunctorAt k :
      ModuleCat.{w} k ⥤ ModuleCat.{max u v} k ⥤ ModuleCat.{max u v w} k).obj (ModuleCat.of k V)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (bPrimeComplex k A)

/-- For a nonunital k-algebra A, a k-module V and n ≥ 0, the
degree-n coefficient-bar object is the k-module
V ⊗[k] (A ⊗[k] A^⊗n), retaining the independent worlds of A and V
in the common height max(u,v,w). -/
@[simp]
theorem barComplex_X (n : ℕ) :
    (barComplex k A V).X n = ModuleCat.of k (V ⊗[k] (A ⊗[k] TensorPower k n A)) := rfl

/-- For a nonunital k-algebra A with k-bilinear multiplication,
a k-module V and n ≥ 0, the coefficient-bar differential from
degree n+1 to n is id_V ⊗ b′_n. On the algebra word of length n+2,
b′_n is the alternating sum of the n+1 adjacent products. -/
@[simp]
theorem barComplex_d (n : ℕ) :
    (barComplex k A V).d (n + 1) n =
      ModuleCat.ofHom (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
        ((bPrimeComplex k A).d (n + 1) n).hom) := rfl

/-- For a nonunital k-algebra A, a k-module V and e ∈ A with
e a = a for all a ∈ A, inserting e before the algebra word gives
a chain homotopy from id of Bar_*(A;V) to zero. The coefficient V is
left unchanged, and no flatness of V is assumed. -/
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

/-- Let e be a left unit of the nonunital k-algebra A. For any
k-module V, the degree-n to degree-n+1 component of the coefficient-bar
contraction is id_V ⊗ s_e, where
s_e(a₀ ⊗ ⋯ ⊗ aₙ) = e ⊗ a₀ ⊗ ⋯ ⊗ aₙ.
Thus it sends v ⊗ (a₀ ⊗ ⋯ ⊗ aₙ) to
v ⊗ (e ⊗ a₀ ⊗ ⋯ ⊗ aₙ). -/
theorem barContractionOfLeftUnit_hom (e : A) (hLeft : ∀ a : A, e * a = a) (n : ℕ) :
    (barContractionOfLeftUnit k A V e hLeft).hom n (n + 1) =
      ModuleCat.ofHom (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
        (extraDegeneracyWith k A e n).hom) := by
  change ((ModuleCat.tensorBifunctorAt k :
      ModuleCat.{w} k ⥤ ModuleCat.{max u v} k ⥤ ModuleCat.{max u v w} k).obj (ModuleCat.of k V)).map
    ((bPrimeContractionOfLeftUnit k A e hLeft).hom n (n + 1)) = _
  rw [bPrimeContractionOfLeftUnit_hom]
  rfl

/-- For a nonunital k-algebra A with k-bilinear multiplication
and a left unit e, the homology of Bar_*(A;V) vanishes in every
degree n ≥ 0 for every k-module V. The result uses the insertion
contraction and does not require V to be flat. -/
theorem barComplex_acyclic_of_leftUnit (e : A) (hLeft : ∀ a : A, e * a = a) :
    (barComplex k A V).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).mpr
  have h := (barContractionOfLeftUnit k A V e hLeft).homologyMap_eq n
  simpa only [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] using h

/-- For a nonunital k-algebra A and a coefficient universe w,
H-unitality means that Bar_*(A;V), with differential id_V ⊗ b′,
is acyclic for every additive commutative group V in Type w equipped
with a k-module structure. The worlds of k, A and V remain independent. -/
def IsHUnital : Prop :=
  ∀ (V : Type w) [AddCommGroup V] [Module k V], (barComplex k A V).Acyclic

/-- If a nonunital k-algebra A with k-bilinear multiplication
has an element e satisfying e a = a for all a, then A is H-unital
in every specified coefficient universe w: Bar_*(A;V) is acyclic
for every k-module V in Type w. -/
theorem isHUnital_of_leftUnit (e : A) (hLeft : ∀ a : A, e * a = a) : IsHUnital.{u, v, w} k A := by
  intro V _ _
  exact barComplex_acyclic_of_leftUnit k A V e hLeft

section OriginalMaps

variable {k A V} {B : Type v} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]
  {W : Type w} [AddCommGroup W] [Module k W]

/-- For nonunital k-algebras A and B in the same carrier world
and a nonunital k-algebra map g : A → B, the chain map between their
b′-complexes applies g to all n+1 entries of the degree-n algebra word.
It commutes with each alternating adjacent-product differential. -/
def barAlgebraComplexMap (f : A →ₙₐ[k] B) : bPrimeComplex k A ⟶ bPrimeComplex k B :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (TensorPower.consLevelMap (f : A →ₗ[k] B) n))
    (fun n => by
      apply ModuleCat.hom_ext
      exact (bPrimeComplex_d_natural f n).symm)

/-- For k-modules V and W in the same coefficient world and
a k-linear map f : V → W, the coefficient-bar chain map
Bar_*(A;V) → Bar_*(A;W) has degree-n map id on the A-word and f on
the coefficient: f ⊗ id_(A ⊗ A^⊗n). -/
def barCoefficientMap (f : V →ₗ[k] W) : barComplex k A V ⟶ barComplex k A W :=
  (((ModuleCat.tensorBifunctorAt k :
      ModuleCat.{w} k ⥤ ModuleCat.{max u v} k ⥤ ModuleCat.{max u v w} k).map (ModuleCat.ofHom f)).mapHomologicalComplex
    (ComplexShape.down ℕ)).app (bPrimeComplex k A)

/-- For nonunital k-algebras A and B in the same carrier world,
a nonunital k-algebra map g : A → B and a k-module V, the chain map
Bar_*(A;V) → Bar_*(B;V) fixes V and applies g to all entries of each
algebra word. -/
def barAlgebraMap (f : A →ₙₐ[k] B) : barComplex k A V ⟶ barComplex k B V :=
  (((ModuleCat.tensorBifunctorAt k :
      ModuleCat.{w} k ⥤ ModuleCat.{max u v} k ⥤ ModuleCat.{max u v w} k).obj (ModuleCat.of k V)).mapHomologicalComplex
    (ComplexShape.down ℕ)).map (barAlgebraComplexMap f)

/-- For a k-linear map f : V → W and a nonunital k-algebra map
g : A → B, with each source and target pair in its common carrier
world, the joint map Bar_*(A;V) → Bar_*(B;W) first changes V by f and
then changes A by g. The coefficient and algebra worlds are independent. -/
def barJointMap (f : V →ₗ[k] W) (g : A →ₙₐ[k] B) : barComplex k A V ⟶ barComplex k B W :=
  barCoefficientMap f ≫ barAlgebraMap g

/-- For a k-linear coefficient map f : V → W, a nonunital
k-algebra map g : A → B and n ≥ 0, the degree-n joint coefficient-bar
map is f ⊗ (g ⊗ g^⊗n) from
V ⊗[k] (A ⊗[k] A^⊗n) to W ⊗[k] (B ⊗[k] B^⊗n). -/
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

/-- For f : V →ₗ[k] W, a nonunital k-algebra map g : A → B,
v ∈ V and a₀,…,aₙ ∈ A, the joint coefficient-bar map sends
v ⊗ (a₀ ⊗ ⋯ ⊗ aₙ) to
f(v) ⊗ (g(a₀) ⊗ ⋯ ⊗ g(aₙ)).
Both algebras have k-bilinear multiplication. -/
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
