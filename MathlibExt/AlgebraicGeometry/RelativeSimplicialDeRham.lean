/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels
public import Mathlib.Algebra.Category.CommAlgCat.Monoidal

/-!
# Actual relative de Rham projection on simplicial product charts

The product algebra is the native degreewise tensor of commutative
algebras. Projection to forms from A with coefficient B sends every
literal generator (a0⊗b0) d(a1⊗b1)⋯d(ap⊗bp) to
(a0 da1⋯dap)⊗(b0⋯bp). Thus all B differentials are killed and the
actual A forms and every B coefficient, including nilpotents, remain.

Both simplicial maps and the de Rham differential are retained.
Native Moore/Alexander--Whitney comparison is a subsequent normalized
construction layer. Reference: PTVV arXiv:1111.3209v4, §2.1, pp.30--32.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeSimplicialDeRham

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels
open _root_.AlgebraicTopology
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]

/-- The actual simplicial tensor algebra retains its native algebra maps and coefficients. -/
def productAlgebra (A B : SAlg k) : SAlg k := A ⊗ B

/-- The native coefficient module functor of the second algebra. -/
def coefficients (B : SAlg k) : SimplicialObject (ModuleCat.{u} k) :=
  B ⋙ toModules k

/-- A relative projection fixes every product generator and its differential. -/
structure ProjectionModel (A B : SAlg k) (M : SimplicialDRModel A)
    (P : SimplicialDRModel (productAlgebra A B)) where
  map : ∀ p : ℕ, P.forms p ⟶ M.forms p ⊗ coefficients B
  generator : ∀ (p : ℕ) (n : SimplexCategoryᵒᵖ)
    (a : Fin (p + 1) → A.obj n) (b : Fin (p + 1) → B.obj n),
    (((P.termIso p n).inv ≫ (map p).app n ≫
      ((M.termIso p n).hom ⊗ₘ 𝟙 ((coefficients B).obj n))).hom
      (formGenerator (productAlgebra A B) p n
        (fun i => TensorProduct.tmul k (a i) (b i)))) =
      TensorProduct.tmul k (formGenerator A p n a) (∏ i : Fin (p + 1), b i)
  differential : ∀ p : ℕ,
    P.differential p ≫ map (p + 1) = map p ≫ (M.differential p ⊗ₘ 𝟙 (coefficients B))

/-- The native normalized coefficient degree, with all product-chart forms retained. -/
def normalizedProjection {A B : SAlg k} {M : SimplicialDRModel A}
    {P : SimplicialDRModel (productAlgebra A B)} (F : ProjectionModel A B M P) (p : ℕ) :
    ((normalizedMooreComplex (ModuleCat.{u} k)).obj (P.forms p)) ⟶
      ((normalizedMooreComplex (ModuleCat.{u} k)).obj (M.forms p ⊗ coefficients B)) :=
  (normalizedMooreComplex (ModuleCat.{u} k)).map (F.map p)

end MathlibExt.AlgebraicGeometry.RelativeSimplicialDeRham
