/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import MathlibExt.AlgebraicGeometry.ComplexAnalytification
public import Mathlib.Geometry.RingedSpace.Basic

/-!
# Polynomial local models for complex analytic spaces

The local model of Spec(C[x]/I) is the actual zero set of I in C^n,
with the inverse image of the sheafification of O_hol / I O_hol.
The quotient is by the ideal I itself, not by its radical.
Polynomial sections are actual holomorphic functions and are fixed by
evaluation. These definitions provide local models for general analytic
realization contracts, without assuming a manifold structure on a singular
zero set.

References: Serre, Geometrie algebrique et geometrie analytique,
https://doi.org/10.5802/aif.59; SGA1, Expose XII.
Mathlib's complex smooth-function sheaf, ring quotients, sheafification and
inverse image are completed constructors reused here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.PolynomialAnalyticSpaces

open CategoryTheory Opposite TopologicalSpace
open scoped Manifold ContDiff

abbrev Coordinates (n : ℕ) := Fin n → ℂ
abbrev PolynomialRing (n : ℕ) := MvPolynomial (Fin n) ℂ

abbrev HolomorphicFunctions (n : ℕ) (U : Opens (Coordinates n)) :=
  C^∞⟮𝓘(ℂ, Coordinates n), U; 𝓘(ℂ), ℂ⟯

def ambientPresheaf (n : ℕ) : (Opens (Coordinates n))ᵒᵖ ⥤ CommRingCat where
  obj U := .of (HolomorphicFunctions n U.unop)
  map f := CommRingCat.ofHom
    (ContMDiffMap.restrictRingHom 𝓘(ℂ, Coordinates n) 𝓘(ℂ) ℂ (leOfHom f.unop))
  map_id _U := rfl
  map_comp _f _g := rfl

def ambientSheaf (n : ℕ) : TopCat.Sheaf CommRingCat (TopCat.of (Coordinates n)) where
  obj := ambientPresheaf n
  property :=
    (smoothSheafCommRing 𝓘(ℂ, Coordinates n) 𝓘(ℂ) (Coordinates n) ℂ).property

def coordinate (n : ℕ) (U : Opens (Coordinates n)) (i : Fin n) :
    HolomorphicFunctions n U :=
  ⟨fun p ↦ p.1 i,
    (ContinuousLinearMap.proj i : Coordinates n →L[ℂ] ℂ).contMDiff.comp
      contMDiff_subtype_val⟩

def polynomialSections (n : ℕ) (U : Opens (Coordinates n)) :
    PolynomialRing n →+* HolomorphicFunctions n U :=
  MvPolynomial.eval₂Hom ContMDiffMap.C (coordinate n U)

@[simp] theorem polynomialSections_eval (n : ℕ) (U : Opens (Coordinates n))
    (f : PolynomialRing n) (p : U) :
    (polynomialSections n U f) p =
      MvPolynomial.eval p.1 f := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [polynomialSections, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C]
    change (algebraMap ℂ ℂ) c = c
    exact RingHom.congr_fun Algebra.algebraMap_self c
  | add f g hf hg =>
    rw [map_add, map_add]
    calc
      ((polynomialSections n U f + polynomialSections n U g) p) =
          (polynomialSections n U f) p + (polynomialSections n U g) p := rfl
      _ = _ := congrArg₂ (· + ·) hf hg
  | mul_X f i hf =>
    rw [map_mul, map_mul]
    calc
      ((polynomialSections n U f * polynomialSections n U (MvPolynomial.X i)) p) =
          (polynomialSections n U f) p *
            (polynomialSections n U (MvPolynomial.X i)) p := rfl
      _ = _ := by
        rw [hf]
        simp [polynomialSections, coordinate]

theorem polynomialSections_naturality (n : ℕ) {U V : Opens (Coordinates n)}
    (f : op U ⟶ op V) :
    ((ambientPresheaf n).map f).hom.comp (polynomialSections n U) =
      polynomialSections n V := by
  apply RingHom.ext
  intro g
  apply ContMDiffMap.ext
  intro p
  change (polynomialSections n U g) (Set.inclusion (leOfHom f.unop) p) =
    (polynomialSections n V g) p
  rw [polynomialSections_eval, polynomialSections_eval]

def analyticIdeal (n : ℕ) (I : Ideal (PolynomialRing n))
    (U : Opens (Coordinates n)) : Ideal (HolomorphicFunctions n U) :=
  I.map (polynomialSections n U)

theorem analyticIdeal_restrict (n : ℕ) (I : Ideal (PolynomialRing n))
    {U V : Opens (Coordinates n)} (f : op U ⟶ op V) :
    (analyticIdeal n I U).map ((ambientPresheaf n).map f).hom = analyticIdeal n I V := by
  rw [analyticIdeal, Ideal.map_map, polynomialSections_naturality]
  rfl

def quotientPresheaf (n : ℕ) (I : Ideal (PolynomialRing n)) :
    (Opens (Coordinates n))ᵒᵖ ⥤ CommRingCat where
  obj U := .of (HolomorphicFunctions n U.unop ⧸ analyticIdeal n I U.unop)
  map f := CommRingCat.ofHom
    (Ideal.Quotient.lift _
      ((Ideal.Quotient.mk (analyticIdeal n I _)).comp ((ambientPresheaf n).map f).hom)
      (by
        intro a ha
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        rw [← analyticIdeal_restrict n I f]
        exact Ideal.mem_map_of_mem _ ha))
  map_id U := by ext a; rfl
  map_comp f g := by ext a; rfl

abbrev quotientSheaf (n : ℕ) (I : Ideal (PolynomialRing n)) :
    TopCat.Sheaf CommRingCat (TopCat.of (Coordinates n)) :=
  (presheafToSheaf (Opens.grothendieckTopology (Coordinates n)) CommRingCat).obj
    (quotientPresheaf n I)

def zeroSet (n : ℕ) (I : Ideal (PolynomialRing n)) : Set (Coordinates n) :=
  {p | ∀ f ∈ I, MvPolynomial.eval p f = 0}

def inclusion (n : ℕ) (I : Ideal (PolynomialRing n)) :
    TopCat.of (zeroSet n I) ⟶ TopCat.of (Coordinates n) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

abbrev structureSheaf (n : ℕ) (I : Ideal (PolynomialRing n)) :
    TopCat.Sheaf CommRingCat (TopCat.of (zeroSet n I)) :=
  (TopCat.Sheaf.pullback CommRingCat (inclusion n I)).obj (quotientSheaf n I)

def ringedSpace (n : ℕ) (I : Ideal (PolynomialRing n)) :
    _root_.AlgebraicGeometry.RingedSpace where
  carrier := TopCat.of (zeroSet n I)
  presheaf := (structureSheaf n I).obj
  IsSheaf := (structureSheaf n I).property

/-- Polynomial coefficients and nilpotent relations map through the actual
quotient, sheafification and inverse-image units. -/
def polynomialMap (n : ℕ) (I : Ideal (PolynomialRing n)) :
    PolynomialRing n →+* (structureSheaf n I).obj.obj (op ⊤) :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat (inclusion n I)).unit.app
      (quotientSheaf n I)).hom.app (op ⊤)).hom.comp
    (((toSheafify (Opens.grothendieckTopology (Coordinates n))
      (quotientPresheaf n I)).app (op ⊤)).hom.comp
      ((Ideal.Quotient.mk (analyticIdeal n I ⊤)).comp (polynomialSections n ⊤)))

theorem polynomialMap_relation (n : ℕ) (I : Ideal (PolynomialRing n))
    (f : PolynomialRing n) (hf : f ∈ I) : polynomialMap n I f = 0 := by
  have h : Ideal.Quotient.mk (analyticIdeal n I ⊤) (polynomialSections n ⊤ f) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hf)
  let a := (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat (inclusion n I)).unit.app
    (quotientSheaf n I)).hom.app (op ⊤)).hom
  let b := ((toSheafify (Opens.grothendieckTopology (Coordinates n))
    (quotientPresheaf n I)).app (op ⊤)).hom
  change a (b (Ideal.Quotient.mk (analyticIdeal n I ⊤) (polynomialSections n ⊤ f))) = 0
  rw [h, map_zero, map_zero]

abbrev affine (n : ℕ) (I : Ideal (PolynomialRing n)) :
    _root_.CategoryTheory.Over (_root_.AlgebraicGeometry.Spec (.of ℂ)) :=
  _root_.CategoryTheory.Over.mk
    (_root_.AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap ℂ (PolynomialRing n ⧸ I))))

def evaluation (n : ℕ) (I : Ideal (PolynomialRing n)) (p : zeroSet n I) :
    PolynomialRing n ⧸ I →+* ℂ :=
  Ideal.Quotient.lift I (MvPolynomial.eval p.1) (fun f hf ↦ p.2 f hf)

def point (n : ℕ) (I : Ideal (PolynomialRing n)) (p : zeroSet n I) :
    MathlibExt.AlgebraicGeometry.ComplexAnalytification.space (affine n I) :=
  ⟨_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom (evaluation n I p)), by
    change _root_.AlgebraicGeometry.Spec.map _ ≫
      _root_.AlgebraicGeometry.Spec.map _ = 𝟙 _
    rw [← _root_.AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : (evaluation n I p).comp (algebraMap ℂ (PolynomialRing n ⧸ I)) =
        RingHom.id ℂ := by
      ext c
      change (evaluation n I p) (Ideal.Quotient.mk I (MvPolynomial.C c)) = c
      rw [evaluation, Ideal.Quotient.lift_mk, MvPolynomial.eval_C]
    rw [h]
    exact _root_.AlgebraicGeometry.Spec.map_id _⟩

end MathlibExt.AlgebraicGeometry.PolynomialAnalyticSpaces
