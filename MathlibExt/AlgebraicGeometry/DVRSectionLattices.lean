/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GenericSectionMaps
public import MathlibExt.AlgebraicGeometry.RelativeReflexiveCanonicalPowers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Actual DVR section lattices and two-model specialization filtration

Lattices are the images of actual R-global sections in actual generic-fibre
K-global sections through the pure-tensor normalized base-change comparison.
Reduction is the actual special-fibre pullback of those same sections,
transported through the injective generic-section map. The comparison of
a second model is normalized against an actual generic scheme/module
isomorphism. Uniformizer rescaling and the intersection/image filtration
are literal submodule operations, not freely chosen lattices or scores.

The coefficient/base-change/injectivity adapters are completed cohomology
integration inputs. The same construction applies to the fixed relative
canonical/reflexive powers from RelativeReflexiveCanonicalPowers; it does
not assert they are line bundles or commute with all base changes.

Source: Blum--Xu, arXiv1812.03538v2, §§2--3 (two degeneration section
lattices and their specialization filtration).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DVRSectionLattices

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GenericSectionMaps
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open scoped TensorProduct

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Literal scalar extension of the scheme to the fraction field. -/
def genericFiber (X : Over (Spec (.of R))) : Over (Spec (.of K)) :=
  Over.mk (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))

abbrev genericProjection (X : Over (Spec (.of R))) :
    (genericFiber (K := K) X).left ⟶ X.left :=
  pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))

abbrev genericModule (X : Over (Spec (.of R))) (M : X.left.Modules) :=
  (Scheme.Modules.pullback (genericProjection (K := K) X)).obj M

/-- Actual native restriction of a global section to the generic fibre. -/
def genericSection (X : Over (Spec (.of R))) (M : X.left.Modules) (s : Sections X M) :
    Sections (genericFiber (K := K) X) (genericModule (K := K) X M) :=
  homSection (genericFiber (K := K) X)
    (pullbackSection (genericProjection (K := K) X) (sectionHom X M s))

/-- Base-change comparison on the actual scalar extension, normalized on every pure tensor. -/
structure SectionBaseChange (X : Over (Spec (.of R))) (M : X.left.Modules) where
  comparison : K ⊗[R] Sections X M ≃ₗ[K]
    Sections (genericFiber (K := K) X) (genericModule (K := K) X M)
  normalized : ∀ a s, comparison (a ⊗ₜ[R] s) = a • genericSection X M s

/-- The common generic section module with scalars restricted through the actual R→K. -/
abbrev GenericRSections (X : Over (Spec (.of R))) (M : X.left.Modules) :=
  (ModuleCat.restrictScalars (algebraMap R K)).obj
    ((sections (genericFiber (K := K) X)).obj (genericModule (K := K) X M))

/-- The actual generic-section injection is computed by 1⊗section. -/
def genericSectionMap {X : Over (Spec (.of R))} {M : X.left.Modules}
    (B : SectionBaseChange (K := K) X M) : Sections X M →ₗ[R] GenericRSections (K := K) X M where
  toFun s := B.comparison (1 ⊗ₜ[R] s)
  map_add' a b := by simp [TensorProduct.tmul_add]
  map_smul' a s := by
    change B.comparison (1 ⊗ₜ[R] (a • s)) =
      (algebraMap R K a) • B.comparison (1 ⊗ₜ[R] s)
    rw [TensorProduct.tmul_smul]
    simpa only [TensorProduct.smul_tmul', Algebra.smul_def, Algebra.algebraMap_self,
      RingHom.id_apply,
      mul_one] using
      B.comparison.map_smul (algebraMap R K a) (1 ⊗ₜ[R] s)

/-- The image of the `R`-sections inside the generic fibre's `H⁰`, an `R`-submodule
spanning it over `K`. It is a lattice (finitely generated) when the `R`-sections are
finitely generated, e.g. for a coherent module on a proper `R`-scheme; the section
comparison alone does not ensure this. -/
def sectionLattice {X : Over (Spec (.of R))} {M : X.left.Modules}
    (B : SectionBaseChange (K := K) X M) :=
  LinearMap.range (genericSectionMap B)

/-- Literal special-fibre scalar extension using the actual residue homomorphism. -/
def specialFiber (X : Over (Spec (.of R))) :
    Over (Spec (.of (IsLocalRing.ResidueField R))) :=
  Over.mk (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))

abbrev specialProjection (X : Over (Spec (.of R))) : (specialFiber X).left ⟶ X.left :=
  pullback.fst X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))

/-- Actual pullback of the same section to the special fibre. -/
def specialSection (X : Over (Spec (.of R))) (M : X.left.Modules) (s : Sections X M) :=
  homSection (specialFiber X)
    (pullbackSection (specialProjection X) (sectionHom X M s))

abbrev SpecialRSections (X : Over (Spec (.of R))) (M : X.left.Modules) :=
  (ModuleCat.restrictScalars (IsLocalRing.residue R)).obj
    ((sections (specialFiber X)).obj ((Scheme.Modules.pullback (specialProjection X)).obj M))

/-- Proof-only linearity of the actual special-fibre section map. -/
structure SpecialSectionMap (X : Over (Spec (.of R))) (M : X.left.Modules) where
  map : Sections X M →ₗ[R] SpecialRSections X M
  normalized : ∀ s, map s = specialSection X M s

/-- Reduction of the actual lattice uses the unique original R-section representative. -/
def latticeReduction {X : Over (Spec (.of R))} {M : X.left.Modules}
    (B : SectionBaseChange (K := K) X M) (h : Function.Injective (genericSectionMap B))
    (S : SpecialSectionMap X M) :
    sectionLattice B →ₗ[R] SpecialRSections X M :=
  S.map.comp (LinearEquiv.ofInjective (genericSectionMap B) h).symm.toLinearMap

/-- Uniformizer data pins the actual maximal-ideal generator and its fraction-field image. -/
structure Uniformizer where
  element : R
  maximal : Ideal.span {element} = IsLocalRing.maximalIdeal R
  nonzero : element ≠ 0
  genericUnit : Kˣ
  normalized : (genericUnit : K) = algebraMap R K element

/-- Actual scalar rescaling on the common generic section carrier. -/
def scalarLinearMap {X : Over (Spec (.of R))} {M : X.left.Modules} (a : K) :
    GenericRSections (K := K) X M →ₗ[R] GenericRSections (K := K) X M where
  toFun s := a • (s : Sections (genericFiber (K := K) X) (genericModule (K := K) X M))
  map_add' _ _ := smul_add _ _ _
  map_smul' r s := by
    change a • ((algebraMap R K r) • s) = (algebraMap R K r) • (a • s)
    simp only [smul_smul, mul_comm]

/-- The second lattice is an actual submodule in the same identified generic H0.
A model comparison must identify it by an actual normalized scheme/module pullback. -/
def specializationFiltration {X : Over (Spec (.of R))} {M : X.left.Modules}
    (B : SectionBaseChange (K := K) X M) (h : Function.Injective (genericSectionMap B))
    (S : SpecialSectionMap X M) (u : Uniformizer (R := R) (K := K))
    (other : Submodule R (GenericRSections (K := K) X M)) (a : ℤ) :
    Submodule R (SpecialRSections X M) :=
  Submodule.map (latticeReduction B h S)
    (Submodule.comap (sectionLattice B).subtype
      (sectionLattice B ⊓ Submodule.map (scalarLinearMap ((u.genericUnit : K)^a)) other))


/-- The second model and its common-generic-fibre identification are actual geometric data. -/
structure ModelComparison (X₁ : Over (Spec (.of R))) (M₁ : X₁.left.Modules) where
  model : Over (Spec (.of R))
  module : model.left.Modules
  baseChange : SectionBaseChange (K := K) model module
  genericIso : genericFiber (K := K) X₁ ≅ genericFiber (K := K) model
  moduleIso : (Scheme.Modules.pullback genericIso.hom.left).obj
    (genericModule (K := K) model module) ≅ genericModule (K := K) X₁ M₁
  sectionComparison : PullbackLinear genericIso.hom
    (genericModule (K := K) model module) (genericModule (K := K) X₁ M₁) moduleIso.hom

/-- The second lattice is computed by the actual normalized generic scheme/module pullback. -/
def secondLattice {X₁ : Over (Spec (.of R))} {M₁ : X₁.left.Modules}
    (C : ModelComparison (K := K) X₁ M₁) :
    Submodule R (GenericRSections (K := K) X₁ M₁) :=
  Submodule.map
    (((ModuleCat.restrictScalars (algebraMap R K)).map
      (ModuleCat.ofHom C.sectionComparison.map)).hom)
    (sectionLattice C.baseChange)

/-- Geometric two-model filtration; both lattices are fixed images of actual section maps. -/
def modelSpecializationFiltration {X₁ : Over (Spec (.of R))} {M₁ : X₁.left.Modules}
    (B : SectionBaseChange (K := K) X₁ M₁) (h : Function.Injective (genericSectionMap B))
    (S : SpecialSectionMap X₁ M₁) (u : Uniformizer (R := R) (K := K))
    (C : ModelComparison (K := K) X₁ M₁) (a : ℤ) :=
  specializationFiltration B h S u (secondLattice C) a

end MathlibExt.AlgebraicGeometry.DVRSectionLattices
