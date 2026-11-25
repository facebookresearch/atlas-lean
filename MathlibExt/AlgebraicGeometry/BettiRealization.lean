/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import MathlibExt.AlgebraicGeometry.PerverseSheaves

@[expose] public noncomputable section

/-!
# Rational Betti coefficients and Yoneda products

The coefficient object is the constant rational sheaf in the actual derived
category on the analytification topology. Cohomology consists of its shifted
endomorphisms. The product below is shifted composition (`ShiftedHom.comp`),
rather than an unspecified multiplication on a named cohomology carrier.

The imported analytification retains its AxiomMath/Weil source and license
notice. These definitions use Mathlib's derived category and linear structure
directly. Reference: Kashiwara--Schapira, *Sheaves on Manifolds*, §2.6.
-/

namespace MathlibExt.AlgebraicGeometry.BettiRealization

open CategoryTheory CategoryTheory.Limits TopCat
open MathlibExt.AlgebraicGeometry.PerverseSheaves

attribute [local instance] HasDerivedCategory.standard

/-- Rational sheaves inherit the scalar action on natural transformations. -/
instance rationalSheafLinear (Z : TopCat.{0}) : Linear ℚ (RationalSheaf Z) := by
  change Linear ℚ (CategoryTheory.Sheaf
    (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ))
  unfold CategoryTheory.Sheaf
  infer_instance

/-- The constant rational coefficient complex in degree zero. -/
abbrev rationalUnit (Z : TopCat.{0}) : RationalDerived Z :=
  (DerivedCategory.singleFunctor _ 0).obj (rationalConstantSheaf Z)

/-- Rational cohomology `Hⁿ(Z; ℚ) = Hom(ℚ_Z, ℚ_Z[n])` in the derived category
of rational sheaves: the cohomology of the constant sheaf. For locally
contractible spaces, such as the complex points of a variety with their
analytic topology, it is singular (Betti) cohomology; on general spaces sheaf
and singular cohomology can differ (even in degree zero, on the Cantor
set). -/
abbrev Cohomology (Z : TopCat.{0}) (n : ℤ) : Type 1 :=
  rationalUnit Z ⟶ (rationalUnit Z)⟦n⟧

/-! The rational vector space structure on `Cohomology Z n` is Mathlib's
`Linear.homModule` on morphisms of the `ℚ`-linear derived category. -/

/-- Transport a class along an equality of degrees. -/
def cohomologyCast {Z : TopCat.{0}} {m n : ℤ} (h : m = n) :
    Cohomology Z m →ₗ[ℚ] Cohomology Z n := by
  subst h
  exact LinearMap.id

@[simp]
theorem cohomologyCast_rfl {Z : TopCat.{0}} {m : ℤ} (x : Cohomology Z m) :
    cohomologyCast rfl x = x :=
  rfl

/-- Cup product $H^i(Z; \mathbb{Q}) \times H^j(Z; \mathbb{Q}) \to H^{i+j}(Z; \mathbb{Q})$: the
Yoneda product `ShiftedHom.comp` of shifted morphisms, in the order `x` then `y`, that is, the
composite $\mathbb{Q}_Z \to \mathbb{Q}_Z[i] \to \mathbb{Q}_Z[j][i] \cong \mathbb{Q}_Z[i+j]$ of $x$
followed by the shift $y[i]$ of $y$. -/
def cup (Z : TopCat.{0}) {i j : ℤ}
    (x : Cohomology Z i) (y : Cohomology Z j) : Cohomology Z (i + j) :=
  ShiftedHom.comp x y (add_comm j i)

/-- The product is rational-linear in its first argument. -/
def cupLeft (Z : TopCat.{0}) {i j : ℤ} (y : Cohomology Z j) :
    Cohomology Z i →ₗ[ℚ] Cohomology Z (i + j) where
  toFun x := cup Z x y
  map_add' _ _ := ShiftedHom.add_comp _ _ _ _
  map_smul' _ _ := ShiftedHom.smul_comp _ _ _ _

/-- The product is rational-linear in its second argument. -/
def cupRight (Z : TopCat.{0}) {i j : ℤ} (x : Cohomology Z i) :
    Cohomology Z j →ₗ[ℚ] Cohomology Z (i + j) where
  toFun y := cup Z x y
  map_add' _ _ := ShiftedHom.comp_add _ _ _ _
  map_smul' _ _ := ShiftedHom.comp_smul _ _ _ _

end MathlibExt.AlgebraicGeometry.BettiRealization
