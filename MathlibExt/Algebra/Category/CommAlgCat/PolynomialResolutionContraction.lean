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
# Contraction of the underlying polynomial simplicial set

Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. After forgetting the
polynomial-comonad resolution to types, the augmentation admits a section induced by `a ↦
X_a`. An extra degeneracy inserts each entire degree-`n` element as a variable in degree
`n+1`.

The induced simplicial section is a right inverse of the augmentation, and augmentation
followed by section is simplicially homotopic to the identity. All these maps are in the
category of types.

## References

* Stacks Project, Definition 92.3.1 and *Simplicial Methods*.
* C. Weibel, *An Introduction to Homological Algebra*, Example 8.6.16.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- For a commutative ring `k : Type u` and `A : CommAlgCat.{max u v} k`,
`polynomialResolutionUnderlying k A` is the augmented simplicial object in `Type(max u v)`
obtained by applying the forgetful functor to `polynomialResolution k A`. Its augmentation
point is the carrier of `A`. -/
def polynomialResolutionUnderlying : SimplicialObject.Augmented (Type (max u v)) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj
    (forget (CommAlgCat.{max u v} k))).obj (polynomialResolution.{u, v} k A)

/-- Let `k` be a commutative ring and `A` a `k`-algebra. The underlying augmented polynomial
resolution has an extra degeneracy whose point section is `a ↦ X_a` and whose map from degree
`n` to degree `n+1` inserts the whole degree-`n` element as a new polynomial variable. These
are maps of types satisfying the augmented extra-degeneracy identities. -/
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

/-- For a commutative ring `k` and `k`-algebra `A`, the extra degeneracy of the underlying
polynomial resolution induces `polynomialResolutionUnderlyingSection k A : const A →
polynomialResolutionUnderlying.left`. This is a simplicial map of types from the constant
carrier of `A` to the resolution. -/
def polynomialResolutionUnderlyingSection :
    (SimplicialObject.const (Type (max u v))).obj A ⟶
      (polynomialResolutionUnderlying.{u, v} k A).left :=
  (polynomialResolutionExtraDegeneracy.{u, v} k A).section_

/-- For a commutative ring `k` and `k`-algebra `A`, let `P` be the underlying augmented polynomial
simplicial set, `ε:P.left→const A` its augmentation, and `s:const A→P.left` the section from
its extra degeneracy. There is a simplicial homotopy `ε ≫ s ∼ 𝟙 P.left` in the category of
types. -/
def polynomialResolutionUnderlyingHomotopy :
    SimplicialObject.Homotopy
      ((polynomialResolutionUnderlying.{u, v} k A).hom ≫
        polynomialResolutionUnderlyingSection.{u, v} k A)
      (𝟙 (polynomialResolutionUnderlying.{u, v} k A).left) :=
  (polynomialResolutionExtraDegeneracy.{u, v} k A).homotopy

/-- For a commutative ring `k` and `k`-algebra `A`, `polynomialResolutionUnderlyingSection k A ≫
polynomialResolutionUnderlying.hom = 𝟙 (const A)`. Thus the simplicial section is a right
inverse of the underlying augmentation. -/
@[reassoc]
theorem polynomialResolutionUnderlyingSection_augmentation :
    polynomialResolutionUnderlyingSection.{u, v} k A ≫
      (polynomialResolutionUnderlying.{u, v} k A).hom = 𝟙 _ :=
  (polynomialResolutionExtraDegeneracy.{u, v} k A).section_comp_hom

end CommAlgCat

end
