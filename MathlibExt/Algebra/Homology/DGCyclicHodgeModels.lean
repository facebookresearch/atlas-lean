/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Homology.DGCyclicMixedModels
public import MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
public import MathlibExt.CategoryTheory.DGAlgebraCategoryModels
public import MathlibExt.HomologicalAlgebra.FilteredCochainSpectralSequence
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# The actual polynomial cyclic object and increasing Hodge filtration

Ordinary cyclic terms are the direct sum of C^(r+2i) u^-i for i≥0.
The differential is b+uB: internal b stays at i and Connes B takes
i+1 to i. The i=0 Connes output is killed by the polynomial quotient.
This is HC of Kaledin equation1.17, not completed HC^- or periodic HP.

The increasing Hodge step F_j is the actual sum of the generators
u^-i with i≤j. For the native cohomological spectral sequence it is
indexed by the decreasing coordinate p=-j. E1(-j,q) is the actual
HH_(-j-q) u^-j piece. HC and its graded abutment use the actual cyclic
complex and the images of the filtration maps on homology.

Nonnegative DG degrees, characteristic zero, bounded finite-dimensional
cohomology and perfection of the actual enveloping diagonal are explicit
hypotheses of the degeneration/convergence requests.

Reference: Kaledin arXiv:math/0611623v4, equations1.16--1.17,
Definition5.1 and Theorem5.5. The cone spectral sequence is completed
native source support.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.Algebra.Homology.DGCyclicHodgeModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology.DGCyclicBarModels
open MathlibExt.Algebra.Homology.DGCyclicMixedModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGAlgebraCategoryModels
open MathlibExt.HomologicalAlgebra.FilteredCochainSpectralSequence

universe u

variable {k : Type u} [CommRing k]

/-- The actual u^-i coefficient in ordinary cyclic cochain degree r. -/
abbrev CyclicSummand {A : DGAlgebra k} (M : HochschildMixedModel A) (r : ℤ) (i : ℕ) : Type u :=
  M.total.complex.X (r + 2 * (i : ℤ))

/-- The source polynomial quotient retains finite support in u^-1. -/
abbrev CyclicValues {A : DGAlgebra k} (M : HochschildMixedModel A) (r : ℤ) :=
  DirectSum ℕ (CyclicSummand M r)

/-- Native inclusion of one actual polynomial coefficient. -/
def includeCoefficient {A : DGAlgebra k} (M : HochschildMixedModel A) (r : ℤ) (i : ℕ) :
    CyclicSummand M r i →ₗ[k] CyclicValues M r :=
  DirectSum.lof k ℕ (CyclicSummand M r) i

/-- Internal b acts on the same actual u^-i coefficient. -/
def internalBlock {A : DGAlgebra k} (M : HochschildMixedModel A) (r : ℤ) (i : ℕ) :
    CyclicSummand M r i →ₗ[k] CyclicValues M (r + 1) :=
  (includeCoefficient M (r + 1) i).comp
    ((M.total.complex.d (r + 2 * (i : ℤ)) (r + 1 + 2 * (i : ℤ))).hom)

/-- uB lowers the inverse-power index; its i=0 term is literally zero. -/
def connesBlock {A : DGAlgebra k} (M : HochschildMixedModel A) (r : ℤ) :
    (i : ℕ) → (CyclicSummand M r i →ₗ[k] CyclicValues M (r + 1))
  | 0 => 0
  | i + 1 => (includeCoefficient M (r + 1) i).comp
      ((M.connes.v (r + 2 * ((i + 1 : ℕ) : ℤ))
        (r + 1 + 2 * (i : ℤ)) (by omega)).hom)

/-- The actual ordinary cyclic differential b+uB on all direct-sum generators. -/
def cyclicDifferential {A : DGAlgebra k} (M : HochschildMixedModel A) (r : ℤ) :
    CyclicValues M r →ₗ[k] CyclicValues M (r + 1) :=
  DirectSum.toModule k ℕ (CyclicValues M (r + 1))
    (fun i => internalBlock M r i + connesBlock M r i)

/-- The source cyclic complex is fixed in every degree and differential. -/
structure PolynomialCyclicModel {A : DGAlgebra k} (M : HochschildMixedModel A) where
  complex : Cochains k
  termIso : ∀ r : ℤ, complex.X r ≅ ModuleCat.of k (CyclicValues M r)
  differential_eq : ∀ r : ℤ,
    complex.d r (r + 1) ≫ (termIso (r + 1)).hom =
      (termIso r).hom ≫ ModuleCat.ofHom (cyclicDifferential M r)

/-- The actual increasing Hodge coefficient submodule F_j. Negative j gives zero. -/
def hodgeSubmodule {A : DGAlgebra k} (M : HochschildMixedModel A) (r j : ℤ) :
    Submodule k (CyclicValues M r) :=
  if j < 0 then ⊥ else
    ⨆ i : Fin (j.toNat + 1), LinearMap.range (includeCoefficient M r i.val)

/-- The native filtered object has the same cyclic complex and actual polynomial steps. -/
structure HodgeFiltrationModel {A : DGAlgebra k} {M : HochschildMixedModel A}
    (C : PolynomialCyclicModel M) where
  filtered : FilteredObject (Cochains k) ℤᵒᵖ
  baseIso : filtered.X ≅ C.complex
  stepIso : ∀ (p r : ℤ), (filtered.filtration.obj (op p)).X r ≅
    ModuleCat.of k (hodgeSubmodule M r (-p))
  inclusion_eq : ∀ (p r : ℤ),
    ((filtered.filtration.ι.app (op p) ≫ baseIso.hom).f r) ≫ (C.termIso r).hom =
      (stepIso p r).hom ≫ ModuleCat.ofHom (hodgeSubmodule M r (-p)).subtype

/-- The actual consecutive increasing-filtration map F_(j-1)→F_j. -/
def consecutiveInclusion {A : DGAlgebra k} {M : HochschildMixedModel A}
    {C : PolynomialCyclicModel M} (H : HodgeFiltrationModel C) (j : ℕ) :
    H.filtered.filtration.obj (op (-(j : ℤ) + 1)) ⟶
      H.filtered.filtration.obj (op (-(j : ℤ))) :=
  H.filtered.filtration.diagram.map
    ((homOfLE (show -(j : ℤ) ≤ -(j : ℤ) + 1 by omega)).op)

/-- The actual u^-j projection on a Hodge step in every cochain degree. -/
def coefficientProjection {A : DGAlgebra k} {M : HochschildMixedModel A}
    {C : PolynomialCyclicModel M} (H : HodgeFiltrationModel C) (j : ℕ) (r : ℤ) :
    (H.filtered.filtration.obj (op (-(j : ℤ)))).X r ⟶
      M.total.complex.X (r + 2 * (j : ℤ)) :=
  (H.filtered.filtration.ι.app (op (-(j : ℤ))) ≫ H.baseIso.hom).f r ≫
    (C.termIso r).hom ≫ ModuleCat.ofHom (DirectSum.component k ℕ (CyclicSummand M r) j)

/-- The canonical associated-graded comparison is fixed on both native cone summands.
Its right block is the literal u^-j projection and its shifted left block is zero. -/
structure AssociatedGradedComparison {A : DGAlgebra k} {M : HochschildMixedModel A}
    {C : PolynomialCyclicModel M} (H : HodgeFiltrationModel C) (j : ℕ) where
  map : CochainComplex.mappingCone (consecutiveInclusion H j) ⟶
    M.total.complex⟦2 * (j : ℤ)⟧
  right_eq : ∀ r : ℤ,
    ((CochainComplex.mappingCone.inr (consecutiveInclusion H j)).f r) ≫ map.f r ≫
      (M.total.complex.shiftFunctorObjXIso (2 * (j : ℤ)) r (r + 2 * (j : ℤ)) rfl).hom =
        coefficientProjection H j r
  left_eq : ∀ r : ℤ,
    (CochainComplex.mappingCone.inl (consecutiveInclusion H j)).v
      (r + 1) r (by omega) ≫ map.f r = 0
  quasiIso : QuasiIso map

/-- The actual E1 cone spectral sequence of this fixed filtration. -/
def hodgeSpectralSequence {A : DGAlgebra k} {M : HochschildMixedModel A}
    {C : PolynomialCyclicModel M} (H : HodgeFiltrationModel C) := spectralSequence H.filtered

/-- The native first page is cohomology of the actual consecutive-step cone. -/
def hodgeFirstPageConeIso {A : DGAlgebra k} {M : HochschildMixedModel A}
    {C : PolynomialCyclicModel M} (H : HodgeFiltrationModel C) (j : ℕ) (q : ℤ) :
    ((hodgeSpectralSequence H).page 1).X (-(j : ℤ), q) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℤ) (-(j : ℤ) + q)).obj
        (CochainComplex.mappingCone (consecutiveInclusion H j)) :=
  firstPageIso H.filtered (-(j : ℤ)) q ≪≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat k) (.up ℤ) (-(j : ℤ) + q)).app
      (CochainComplex.mappingCone (consecutiveInclusion H j))

/-- The Hochschild identification uses the fixed cone projection and native shift.
No independent automorphism of Hochschild homology is part of this map. -/
def hodgeFirstPageIso {A : DGAlgebra k} {M : HochschildMixedModel A}
    {C : PolynomialCyclicModel M} (H : HodgeFiltrationModel C) (j : ℕ)
    (G : AssociatedGradedComparison H j) (q : ℤ) :
    ((hodgeSpectralSequence H).page 1).X (-(j : ℤ), q) ≅
      hochschildHomology M.total (-(j : ℤ) - q) := by
  letI := G.quasiIso
  exact hodgeFirstPageConeIso H j q ≪≫
    asIso (HomologicalComplex.homologyMap G.map (-(j : ℤ) + q)) ≪≫
      ((HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℤ) 0).shiftIso
        (2 * (j : ℤ)) (-(j : ℤ) + q) (-(-(j : ℤ) - q)) (by omega)).app M.total.complex

/-- HC is the actual homology of the polynomial cyclic complex in source homological degree. -/
def cyclicHomology {A : DGAlgebra k} {M : HochschildMixedModel A}
    (C : PolynomialCyclicModel M) (n : ℤ) : ModuleCat.{u} k :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℤ) (-n)).obj C.complex

/-- The actual increasing Hodge step on HC, as the image of its homology map. -/
def hodgeHomologyStep {A : DGAlgebra k} {M : HochschildMixedModel A}
    {C : PolynomialCyclicModel M} (H : HodgeFiltrationModel C) (j n : ℤ) :
    Submodule k (cyclicHomology C n) :=
  LinearMap.range
    ((HomologicalComplex.homologyMap
      (H.filtered.filtration.ι.app (op (-j)) ≫ H.baseIso.hom) (-n)).hom)

/-- The actual graded quotient of the Hodge filtration on HC. -/
def gradedCyclicHomology {A : DGAlgebra k} {M : HochschildMixedModel A}
    {C : PolynomialCyclicModel M} (H : HodgeFiltrationModel C) (j n : ℤ) : ModuleCat.{u} k :=
  ModuleCat.of k
    ((hodgeHomologyStep H j n) ⧸
      ((hodgeHomologyStep H (j - 1) n).comap (hodgeHomologyStep H j n).subtype))

/-- Properness of a DG algebra over a field: bounded, finite-dimensional total cohomology. Over a
field this is perfection over the base. Over a general base finite cohomology does not imply
perfection (`ℚ[ε]/(ε²) → ℚ` has infinite projective dimension), so the predicate is only stated over
fields. -/
def IsProperAlgebra {k : Type u} [Field k] (A : DGAlgebra k) : Prop :=
  (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
    IsZero ((HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℤ) i).obj A.X)) ∧
  ∀ i : ℤ, _root_.Module.Finite k
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℤ) i).obj A.X)

/-- E1 degeneration is vanishing of the native differentials on every page r≥1. -/
def IsE1Degenerate {A : DGAlgebra k} {M : HochschildMixedModel A}
    {C : PolynomialCyclicModel M} (H : HodgeFiltrationModel C) : Prop :=
  ∀ (r : ℤ) (hr : 1 ≤ r) (p q : ℤ × ℤ),
    ((hodgeSpectralSequence H).page r hr).d p q = 0

end MathlibExt.Algebra.Homology.DGCyclicHodgeModels
