/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# General proper strictly semistable models and their actual strata

These definitions work over an actual discrete valuation ring R, with
an actual irreducible uniformizer pi, its fraction field and its residue
field. The charts are actual spectra of R[t_0,...,t_d]/(t_0...t_(r-1)-pi).
The local maps, global smooth components, component intersections and
stratum inclusion maps use the native scheme and ideal-sheaf operations.

Providing such a model for a geometric family is an additional geometric
input. These definitions do not assert that every variety has semistable
reduction, or construct nearby cycles, a weight spectral sequence, its
Gysin differential or its generic-fibre abutment comparison.

References: L. Illusie, *Autour du theoreme de monodromie locale*,
Astérisque 223 (1994), Exposé I, section 3.1, pp. 33--34, and section 3.8,
pp. 40--41; T. Ito, *Weight-monodromy conjecture over equal characteristic
local fields*, section 1, for the strata in Rapoport--Zink, Satz 2.10.
https://www.numdam.org/item/AST_1994__223__9_0/
https://arxiv.org/abs/math/0308141
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.SemistableModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.TopologicalSpace _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme

universe u

variable (R : Type u) [CommRing R]

/-- The actual affine base; the semistable model below requires a DVR. -/
abbrev trait : Scheme.{u} := Spec (.of R)

/-- The actual fraction-field point, with its prescribed inclusion. -/
def genericInclusion (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] : Spec (.of K) ⟶ trait R :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The actual generic-fibre functor for the prescribed fraction field. -/
abbrev genericFunctor (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] : Over (trait R) ⥤ Over (Spec (.of K)) :=
  Over.pullback (genericInclusion R K)

/-- The exact uniformizer-product chart equation. -/
def crossingEquation (π : R) (d r : ℕ) : MvPolynomial (Fin (d + 1)) R :=
  (∏ i ∈ Finset.univ.filter (fun i : Fin (d + 1) ↦ i.val < r),
    MvPolynomial.X i) - MvPolynomial.C π

/-- The actual chart algebra, with its native R-algebra structure. -/
abbrev crossingRing (π : R) (d r : ℕ) :=
  MvPolynomial (Fin (d + 1)) R ⧸ Ideal.span {crossingEquation R π d r}

/-- The actual affine semistable chart. -/
abbrev crossingScheme (π : R) (d r : ℕ) : Scheme.{u} :=
  Spec (.of (crossingRing R π d r))

/-- Its actual structural map to Spec R. -/
def crossingMap (π : R) (d r : ℕ) :
    crossingScheme R π d r ⟶ trait R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (crossingRing R π d r)))

/-- The quotient class of an actual polynomial coordinate. -/
def crossingCoordinate (π : R) (d r : ℕ) (i : Fin (d + 1)) :
    crossingRing R π d r :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

/-- The chart coordinates satisfy the exact prescribed equation. -/
theorem crossingCoordinate_product (π : R) (d r : ℕ) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (d + 1) ↦ i.val < r),
      crossingCoordinate R π d r i) =
        algebraMap R (crossingRing R π d r) π := by
  have h : Ideal.Quotient.mk (Ideal.span {crossingEquation R π d r})
      (crossingEquation R π d r) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))
  change Ideal.Quotient.mk _
      ((∏ i ∈ Finset.univ.filter (fun i : Fin (d + 1) ↦ i.val < r),
        MvPolynomial.X i) - MvPolynomial.C π) = 0 at h
  rw [map_sub, map_prod, sub_eq_zero] at h
  exact h

/-- A genuine semistable etale neighbourhood at every point. Relative
dimension may vary between connected components. -/
def HasSemistableCharts (π : R) (X : Over (trait R)) : Prop :=
  ∀ x : X.left, ∃ (d r : ℕ), 1 ≤ r ∧ r ≤ d + 1 ∧
    ∃ (U : Scheme.{u}) (a : U ⟶ X.left)
      (b : U ⟶ crossingScheme R π d r) (z : U),
      Etale a ∧ Etale b ∧ a z = x ∧ a ≫ X.hom = b ≫ crossingMap R π d r

section LocalBase

variable [IsLocalRing R]

/-- The actual residue-field point of the base. -/
abbrev specialBase : Scheme.{u} := Spec (.of (IsLocalRing.ResidueField R))

/-- The actual quotient to the residue field. -/
def specialInclusion : specialBase R ⟶ trait R :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

/-- Scheme-theoretic special fibres along the actual residue quotient. -/
abbrev specialFunctor : Over (trait R) ⥤ Over (specialBase R) :=
  Over.pullback (specialInclusion R)

variable (X : Over (trait R))

/-- A global irreducible component with its actual reduced closed
scheme structure inside the special fibre. -/
def specialComponent
    (C : irreducibleComponents ((specialFunctor R).obj X).left) :
    ((specialFunctor R).obj X).left.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨closure (C : Set ((specialFunctor R).obj X).left), isClosed_closure⟩

/-- Every actual global component is smooth over the actual residue field.
This excludes globally self-intersecting components. -/
def HasSmoothSpecialComponents : Prop :=
  ∀ C : irreducibleComponents ((specialFunctor R).obj X).left,
    Smooth ((specialComponent R X C).subschemeι ≫
      ((specialFunctor R).obj X).hom)

/-- The actual scheme-theoretic intersection ideal of a finite set of
components: sum of their actual ideal sheaves, not their radical union. -/
def stratumIdeal
    (s : Finset (irreducibleComponents ((specialFunctor R).obj X).left)) :
    ((specialFunctor R).obj X).left.IdealSheafData := by
  classical
  exact s.sup (specialComponent R X)

/-- The actual closed intersection scheme, before any geometric base change. -/
abbrev stratum
    (s : Finset (irreducibleComponents ((specialFunctor R).obj X).left)) :
    Scheme.{u} := (stratumIdeal R X s).subscheme

/-- Its structural map to the actual residue field. -/
def stratumToBase
    (s : Finset (irreducibleComponents ((specialFunctor R).obj X).left)) :
    stratum R X s ⟶ specialBase R :=
  (stratumIdeal R X s).subschemeι ≫ ((specialFunctor R).obj X).hom

/-- Adding components enlarges the actual intersection ideal. -/
theorem stratumIdeal_mono
    {s t : Finset (irreducibleComponents ((specialFunctor R).obj X).left)}
    (h : s ⊆ t) : stratumIdeal R X s ≤ stratumIdeal R X t := by
  classical
  exact Finset.sup_mono h

/-- The actual inclusion from a deeper intersection to a shallower one. -/
def stratumMap
    {s t : Finset (irreducibleComponents ((specialFunctor R).obj X).left)}
    (h : s ⊆ t) : stratum R X t ⟶ stratum R X s :=
  Scheme.IdealSheafData.inclusion (stratumIdeal_mono R X h)

/-- The inclusion has its fixed structural comparison square. -/
@[reassoc (attr := simp)]
theorem stratumMap_toBase
    {s t : Finset (irreducibleComponents ((specialFunctor R).obj X).left)}
    (h : s ⊆ t) :
    stratumMap R X h ≫ stratumToBase R X s = stratumToBase R X t := by
  simp [stratumMap, stratumToBase]

/-- These are the native identity inclusions. -/
@[simp]
theorem stratumMap_id
    (s : Finset (irreducibleComponents ((specialFunctor R).obj X).left)) :
    stratumMap R X (show s ⊆ s from fun _ h ↦ h) = 𝟙 (stratum R X s) := by
  exact Scheme.IdealSheafData.inclusion_id _

/-- These are the native compositions of intersection inclusions. -/
@[reassoc (attr := simp)]
theorem stratumMap_comp
    {s t v : Finset (irreducibleComponents ((specialFunctor R).obj X).left)}
    (h₁ : s ⊆ t) (h₂ : t ⊆ v) :
    stratumMap R X h₂ ≫ stratumMap R X h₁ = stratumMap R X (h₁.trans h₂) := by
  exact Scheme.IdealSheafData.inclusion_comp _ _

end LocalBase

/-- General strict semistability over an actual DVR and uniformizer, with
the exact etale chart, reduced-fibre and global-component conditions. -/
def IsStrictlySemistable (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (π : R) (X : Over (trait R)) : Prop :=
  Irreducible π ∧ HasSemistableCharts R π X ∧
    IsReduced ((specialFunctor R).obj X).left ∧ HasSmoothSpecialComponents R X

/-- An actual proper strictly semistable model. Constructing a model of
a given generic fibre is separate geometric input. -/
structure ProperStrictlySemistableModel (R : Type u) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] (π : R) where
  model : Over (trait R)
  [proper : IsProper model.hom]
  semistable : IsStrictlySemistable R π model

attribute [instance] ProperStrictlySemistableModel.proper

end MathlibExt.AlgebraicGeometry.SemistableModels
