/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Basic

/-!
# Transporting a chain complex to exterior-power coordinates

Let R be commutative, L an R-Lie algebra and K a nonnegative R-module chain complex. Given
degreewise isomorphisms e_n : K_n ≅ ⋀[R]^n L, transport the boundary by D_n = e_(n+1).inv ≫
d_K(n+1,n) ≫ e_n.hom. This defines exterior chain data with square-zero boundary and a complex
Q_D isomorphic to K.

The isomorphism K ≅ Q_D has degree-n component e_n.hom and inverse component e_n.inv. Its
homology gives H_n(K) ≅ H_n(Q_D) for every n. The boundary in Q_D is the transported boundary
of K; the construction does not impose equality with the canonical CE bracket boundary.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory

universe u v

namespace ChevalleyEilenberg.ChainData

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let K : ChainComplex (ModuleCat.{max u v} R) ℕ and e_n : K.X n ≅ chainObject R L n
for every n, where chainObject has carrier ⋀[R]^n L. Then K ≅ (ChainData.ofComplex R L K
e).complex, whose boundary is e_(n+1).inv ≫ K.d (n + 1) n ≫ e_n.hom. The forward and inverse
components are e_n.hom and e_n.inv. -/
def ofComplexIso
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (e : ∀ n : ℕ, K.X n ≅ chainObject R L n) :
    K ≅ (ofComplex R L K e).complex := by
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro i j hij
  simp only [ComplexShape.down_Rel] at hij
  subst i
  simp [ofComplex, Category.assoc]

@[simp]
theorem ofComplexIso_hom_f
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (e : ∀ n : ℕ, K.X n ≅ chainObject R L n) (n : ℕ) :
    (ofComplexIso R L K e).hom.f n = (e n).hom :=
  rfl

@[simp]
theorem ofComplexIso_inv_f
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (e : ∀ n : ℕ, K.X n ≅ chainObject R L n) (n : ℕ) :
    (ofComplexIso R L K e).inv.f n = (e n).inv :=
  rfl

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let K be an ℕ-indexed R-module chain complex in universe max u v and e_n : K.X n ≅
⋀[R]^n L degreewise coordinates. For every n : ℕ, the complex isomorphism with the
conjugated-boundary exterior model induces K.homology n ≅ (ChainData.ofComplex R L K
e).complex.homology n. Its forward map is homologyMap (ChainData.ofComplexIso R L K e).hom n. -/
def ofComplexHomologyIso
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (e : ∀ n : ℕ, K.X n ≅ chainObject R L n) (n : ℕ) :
    K.homology n ≅ (ofComplex R L K e).complex.homology n :=
  HomologicalComplex.homologyMapIso (ofComplexIso R L K e) n

@[simp]
theorem ofComplexHomologyIso_hom
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (e : ∀ n : ℕ, K.X n ≅ chainObject R L n) (n : ℕ) :
    (ofComplexHomologyIso R L K e n).hom =
      HomologicalComplex.homologyMap (ofComplexIso R L K e).hom n :=
  rfl

end ChevalleyEilenberg.ChainData
