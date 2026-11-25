/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Module.Projective
/-!
# Finite-free obstruction complexes and real affine presentation maps

A differential between actual finite-free B-modules is placed in degrees
−1 and 0 using Mathlib's mapping cone; the terms are finite projective by
Mathlib's instances and the complex vanishes in all other degrees
(`supportedDegrees`). The presentation comparison is a genuine cochain map to
Mathlib's naive cotangent complex `I/I² → Ω_P⊗B`
(`Algebra.Extension.cotangentComplex`); its kernel/cokernel maps are the
H⁻¹/H⁰ maps of that two-term presentation model.

The actual full cotangent complex is constructed separately from polynomial
resolution data. No presentation cone is silently identified with the full
cotangent complex on a singular scheme. The obstruction module with
coefficients in `M` is the cokernel of the dual differential, that is
`Hom_{D(B)}(E, M[1])`. For a morphism of extensions from the presentation to
an extension `Q`, `obstruction` is the pullback of the presentation obstruction
(the class of `I/I² → Q.Cotangent`) along a comparison. A lift of `B → A` to
`Q` (`HasLift`) forces it to vanish for every comparison; the converse is
requested for square-zero `Q` only when the comparison is a `PresentationTheory`
(`AffinePerfectObstructionTheoryWanted.presentation_obstruction_eq_zero_iff`):
for instance the zero comparison always gives the zero class.

Reference: Behrend--Fantechi, *The intrinsic normal cone*, §4,
https://arxiv.org/abs/alg-geom/9601010. Generic cotangent/deformation
constructions already occur in AxiomMath/Stacks and are not reasserted here.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.AffineObstructionComplexes
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard

variable (B : Type) [CommRing B]

/-- A differential `B^a → B^b` between finite free `B`-modules, to be placed in degrees `-1`
and `0`. -/
structure FreeTwoTerm where
  /-- The rank `a` of the term in degree `-1`. -/
  negativeRank : ℕ
  /-- The rank `b` of the term in degree `0`. -/
  zeroRank : ℕ
  /-- The differential `B^a → B^b`. -/
  differential : (Fin negativeRank → B) →ₗ[B] (Fin zeroRank → B)

/-- The term `B^a` in degree `-1`. -/
abbrev negative (E : FreeTwoTerm B) := Fin E.negativeRank → B
/-- The term `B^b` in degree `0`. -/
abbrev degreeZero (E : FreeTwoTerm B) := Fin E.zeroRank → B

/-- The two-term complex `B^a → B^b` in degrees `-1` and `0`, as the mapping cone of the
differential between the corresponding complexes concentrated in degree `0`. -/
def complex (E : FreeTwoTerm B) : CochainComplex (ModuleCat.{0} B) ℤ :=
  CochainComplex.mappingCone
    ((CochainComplex.singleFunctor (ModuleCat.{0} B) 0).map (ModuleCat.ofHom E.differential))

/-- The image of `complex B E` in the derived category of `B`-modules. -/
def derived (E : FreeTwoTerm B) : DerivedCategory (ModuleCat.{0} B) :=
  DerivedCategory.Q.obj (complex B E)

variable {B}
variable {k : Type} [Field k] [Algebra k B] {n : ℕ} (G : _root_.Algebra.Generators k B (Fin n))

/-- The naive cotangent complex `I/I² → Ω[P⁄k] ⊗[P] B` of a finite presentation of `B`, in degrees
`-1` and `0`. -/
def naiveComplex : CochainComplex (ModuleCat.{0} B) ℤ :=
  CochainComplex.mappingCone ((CochainComplex.singleFunctor (ModuleCat.{0} B) 0).map
    (ModuleCat.ofHom G.toExtension.cotangentComplex))

/-- A morphism of two-term complexes from `E` to the naive cotangent complex of `G`. -/
structure Comparison (E : FreeTwoTerm B) where
  /-- The component in degree `-1`. -/
  negative : (Fin E.negativeRank → B) →ₗ[B] G.toExtension.Cotangent
  /-- The component in degree `0`. -/
  degreeZero : (Fin E.zeroRank → B) →ₗ[B] G.toExtension.CotangentSpace
  /-- The square with the two differentials commutes. -/
  comm : G.toExtension.cotangentComplex ∘ₗ negative = degreeZero ∘ₗ E.differential

variable {G} {E : FreeTwoTerm B}

/-- The map induced by a comparison on the cohomology in degree `-1` (the kernels). -/
def negativeHomology (F : Comparison G E) :
    LinearMap.ker E.differential →ₗ[B] LinearMap.ker G.toExtension.cotangentComplex where
  toFun x := ⟨F.negative x.1, by
    change G.toExtension.cotangentComplex (F.negative x.1) = 0
    rw [← LinearMap.comp_apply, F.comm, LinearMap.comp_apply, x.2, map_zero]⟩
  map_add' x y := by ext; exact F.negative.map_add x.1 y.1
  map_smul' r x := by ext; exact F.negative.map_smul r x.1

/-- The map induced by a comparison on the cohomology in degree `0` (the cokernels). -/
def zeroHomology (F : Comparison G E) :
    ((Fin E.zeroRank → B) ⧸ LinearMap.range E.differential) →ₗ[B]
      G.toExtension.CotangentSpace ⧸ LinearMap.range G.toExtension.cotangentComplex :=
  Submodule.mapQ _ _ F.degreeZero (by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨F.negative y, (LinearMap.congr_fun F.comm y)⟩)

/-- A comparison as a morphism of cochain complexes. -/
def cochainMap (F : Comparison G E) : complex B E ⟶ naiveComplex G :=
  CochainComplex.mappingCone.map _ _
    ((CochainComplex.singleFunctor (ModuleCat.{0} B) 0).map (ModuleCat.ofHom F.negative))
    ((CochainComplex.singleFunctor (ModuleCat.{0} B) 0).map (ModuleCat.ofHom F.degreeZero)) (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      exact ModuleCat.hom_ext F.comm.symm)

variable (E) (M : Type) [AddCommGroup M] [Module B M]

/-- Composition with the differential: `Hom(B^b, M) → Hom(B^a, M)`. -/
def dualDifferential : ((Fin E.zeroRank → B) →ₗ[B] M) →ₗ[B]
    ((Fin E.negativeRank → B) →ₗ[B] M) where
  toFun f := f ∘ₗ E.differential
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The cokernel of `dualDifferential E M`, that is `Hom_{D(B)}(E, M[1])`, where the obstructions
with coefficients in `M` live. -/
abbrev ObstructionModule := ((Fin E.negativeRank → B) →ₗ[B] M) ⧸
  LinearMap.range (dualDifferential E M)

variable {M}
variable {A : Type} [CommRing A] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
  (Q : _root_.Algebra.Extension.{0} k A) (h : _root_.Algebra.Extension.Hom G.toExtension Q)

/-- The obstruction class of a morphism of extensions `h` from the extension of the presentation `G`
(of the $k$-algebra $B$, for a field $k$) to an extension `Q` of the $k$-algebra $A$ over $B$,
pulled back along the comparison `F` from $E = (B^a → B^b)$ to the naive cotangent complex of `G`:
the class of the composite of the degree $-1$ component $B^a → I/I^2$ of `F` with the map from
$I/I^2$ to `Q.Cotangent` induced by `h`, modulo the maps that factor through the differential of
$E$. -/
def obstruction (F : Comparison G E) : ObstructionModule E Q.Cotangent :=
  (LinearMap.range (dualDifferential E Q.Cotangent)).mkQ
    (_root_.Algebra.Extension.Cotangent.map h ∘ₗ F.negative)

/-- The algebra map `B → A` lifts to a `k`-algebra map `B → Q.Ring`. -/
def HasLift : Prop :=
  ∃ f : B →ₐ[k] Q.Ring, (IsScalarTower.toAlgHom k Q.Ring A).comp f = IsScalarTower.toAlgHom k B A

variable {E}

/-- The image of the naive cotangent complex of `G` in the derived category. -/
def presentedDerived (G : _root_.Algebra.Generators k B (Fin n)) :
    DerivedCategory (ModuleCat.{0} B) :=
  DerivedCategory.Q.obj (naiveComplex G)

/-- The image of a comparison in the derived category. -/
def derivedMap (F : Comparison G E) : derived B E ⟶ presentedDerived G :=
  DerivedCategory.Q.map (cochainMap F)

/-- A perfect obstruction theory relative to the naive cotangent complex of a presentation
(Behrend--Fantechi, Definition 4.4, with `τ_{≥ -1} L_{B/k}` modelled by the naive cotangent
complex): a finite free two-term complex with a comparison that is surjective on cohomology in
degree `-1` and bijective in degree `0`. -/
structure PresentationTheory (G : _root_.Algebra.Generators k B (Fin n)) where
  /-- The finite free two-term complex. -/
  model : FreeTwoTerm B
  /-- The comparison to the naive cotangent complex. -/
  comparison : Comparison G model
  /-- Surjectivity on cohomology in degree `-1`. -/
  surjectiveNegative : Function.Surjective (negativeHomology comparison)
  /-- Bijectivity on cohomology in degree `0`. -/
  bijectiveZero : Function.Bijective (zeroHomology comparison)

/-- The complex of a finite free two-term complex vanishes outside degrees `-1` and `0`. -/
theorem supportedDegrees (E : FreeTwoTerm B) (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((complex B E).X i) := by
  rw [complex, CochainComplex.mappingCone.isZero_X_iff]
  constructor
  · exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (ModuleCat.of B (negative B E)) (i + 1) (by omega)
  · exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (ModuleCat.of B (degreeZero B E)) i hzero

end MathlibExt.AlgebraicGeometry.AffineObstructionComplexes
