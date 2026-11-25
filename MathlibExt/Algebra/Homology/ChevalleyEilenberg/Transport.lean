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
# Transport of Chevalley–Eilenberg chain models

Degreewise exterior-power coordinates conjugate a chain differential to
`ChainData`. The resulting exterior-coordinate complex is isomorphic to the
given complex, and the isomorphism induces the homology comparison.
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

/-- The canonical complex obtained by transporting a model through its
degreewise exterior-power coordinates is isomorphic to the original model. -/
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

/-- Homology transport associated to degreewise exterior-power coordinates. -/
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
