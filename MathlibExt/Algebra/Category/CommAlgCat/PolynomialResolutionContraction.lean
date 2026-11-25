/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialResolution
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# The actual set contraction of the polynomial simplicial object

After forgetting commutative algebras to sets, the section of the augmentation
is `a ↦ X_a`, and the extra degeneracy in degree `n` inserts the whole element
of degree `n` as a variable in degree `n+1`. The existing generator formulas
for every face and degeneracy prove all the extra degeneracy identities.

These are functions of sets. Their additivity, linearity or multiplicativity
is neither assumed nor asserted. Thus this construction applies to arbitrary
commutative algebras, including algebras for which the polynomial evaluation
counit has no algebra section.

References: Stacks Project, Definition 92.3.1 and Simplicial Methods, the
standard construction from an adjunction; Weibel, Example 8.6.16.

-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- The actual augmented simplicial set obtained by forgetting the polynomial
augmented simplicial algebra. -/
def polynomialResolutionUnderlying : SimplicialObject.Augmented (Type (max u v)) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj
    (forget (CommAlgCat.{max u v} k))).obj (polynomialResolution.{u, v} k A)

/-- The generator insertion is a genuine extra degeneracy on the underlying
augmented simplicial set. -/
def polynomialResolutionExtraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy (polynomialResolutionUnderlying.{u, v} k A) where
  s' := TypeCat.ofHom (polynomialResolutionGenerator.{u, v} k A 0)
  s n := TypeCat.ofHom (polynomialResolutionGenerator.{u, v} k A (n + 1))
  s'_comp_ε := by
    apply ConcreteCategory.ext_apply
    intro a
    change ((polynomialResolution.{u, v} k A).hom.app (op ⦋0⦌)).hom
      (polynomialResolutionGenerator.{u, v} k A 0 a) = a
    exact polynomialResolution_augmentation_zero_generator.{u, v} k A a
  s₀_comp_δ₁ := by
    apply ConcreteCategory.ext_apply
    intro p
    change ((polynomialResolution.{u, v} k A).left.map
      (SimplexCategory.δ (1 : Fin 2)).op).hom
      (polynomialResolutionGenerator.{u, v} k A 1 p) =
      polynomialResolutionGenerator.{u, v} k A 0
        (((polynomialResolution.{u, v} k A).hom.app (op ⦋0⦌)).hom p)
    rw [polynomialResolution_augmentation_zero]
    exact polynomialResolution_face_succ_generator.{u, v} k A (0 : Fin 1) p
  s_comp_δ₀ n := by
    apply ConcreteCategory.ext_apply
    intro x
    change ((polynomialResolution.{u, v} k A).left.map
      (SimplexCategory.δ (0 : Fin (n + 2))).op).hom
      (polynomialResolutionGenerator.{u, v} k A (n + 1) x) = x
    exact polynomialResolution_face_zero_generator.{u, v} k A n x
  s_comp_δ n i := by
    apply ConcreteCategory.ext_apply
    intro x
    let x' : (polynomialPower.{u, v} k (n + 1 + 1)).obj A := x
    change ((polynomialResolution.{u, v} k A).left.map
      (SimplexCategory.δ i.succ).op).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1 + 1) x') =
      polynomialResolutionGenerator.{u, v} k A (n + 1)
        (((polynomialResolution.{u, v} k A).left.map (SimplexCategory.δ i).op).hom x')
    have h := polynomialResolution_face_succ_generator.{u, v} k A (n := n + 1) i x'
    have hd := congrArg (fun f => f.hom x')
      (polynomialResolution_map_δ.{u, v} k A (n := n) i)
    exact h.trans (congrArg (polynomialResolutionGenerator.{u, v} k A (n + 1)) hd.symm)
  s_comp_σ n i := by
    apply ConcreteCategory.ext_apply
    intro x
    let x' : (polynomialPower.{u, v} k (n + 1)).obj A := x
    change ((polynomialResolution.{u, v} k A).left.map
      (SimplexCategory.σ i.succ).op).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x') =
      polynomialResolutionGenerator.{u, v} k A (n + 2)
        (((polynomialResolution.{u, v} k A).left.map (SimplexCategory.σ i).op).hom x')
    have h := polynomialResolution_degeneracy_succ_generator.{u, v} k A (n := n) i x'
    have hd := congrArg (fun f => f.hom x')
      (polynomialResolution_map_σ.{u, v} k A (n := n) i)
    exact h.trans (congrArg (polynomialResolutionGenerator.{u, v} k A (n + 2)) hd.symm)

/-- The actual simplicial section induced by the constructed extra degeneracy. -/
def polynomialResolutionUnderlyingSection :
    (SimplicialObject.const (Type (max u v))).obj A ⟶
      (polynomialResolutionUnderlying.{u, v} k A).left :=
  (polynomialResolutionExtraDegeneracy.{u, v} k A).section_

/-- The augmentation followed by the constructed section is simplicially
homotopic to the identity, by the native extra degeneracy theorem. -/
def polynomialResolutionUnderlyingHomotopy :
    SimplicialObject.Homotopy
      ((polynomialResolutionUnderlying.{u, v} k A).hom ≫
        polynomialResolutionUnderlyingSection.{u, v} k A)
      (𝟙 (polynomialResolutionUnderlying.{u, v} k A).left) :=
  (polynomialResolutionExtraDegeneracy.{u, v} k A).homotopy

/-- The constructed section is a right inverse of the actual augmentation. -/
@[reassoc]
theorem polynomialResolutionUnderlyingSection_augmentation :
    polynomialResolutionUnderlyingSection.{u, v} k A ≫
      (polynomialResolutionUnderlying.{u, v} k A).hom = 𝟙 _ :=
  (polynomialResolutionExtraDegeneracy.{u, v} k A).section_comp_hom

end CommAlgCat

end
