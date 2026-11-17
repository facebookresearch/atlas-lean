/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GlobalBoundedDeterminantModels
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Canonical torsion and the ordered subset determinant comparison

An acyclic bounded cochain is trivialized by the exterior products of its
actual adapted bases: a basis of the kernel of each differential, followed
by lifts of the next kernel basis. Odd factors are the actual top exterior
coordinate functionals. The tensor follows the original increasing list
of cochain degrees.

The determinant comparison uses the same subset presentations, shifted by
`card(subset) - numberOfLines`. Every term is their literal ordered direct
sum. Its determinant map is recursively computed from the native product
projection and `ShortExactDeterminant`'s kernel/quotient exterior product.
Normalization on genuine affine localization covers fixes the remaining
tensor regrouping and every coefficient. Construction and independence
are separate direct Wanted requests; no determinant word is a generator.

Sources: Knudsen--Mumford, *The projectivity of the moduli space of stable
curves I*, Sections 1--2; Yuan--Zhang, arXiv:2105.13587v9, Section 4.2.1,
pp108--110. The imported exterior-annihilator and exact-sequence primitives
retain the Apache-2.0 source attribution in ProjectiveDeterminantModules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CanonicalKoszulDeterminants

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open ProjectiveDeterminantModules BoundedProjectiveDeterminants
open GlobalBoundedDeterminantModels BoundedScalarDeterminants
open scoped TensorProduct

variable (R : Type) [CommRing R]

/-- The original cochain degree of a subset in the section Koszul complex. -/
def subsetDegree {m : ℕ} (t : Finset (Fin m)) : ℤ := (t.card : ℤ) - m

/-- Exactly the subset order used by the original local pairing. -/
def subsets (m : ℕ) : List (Finset (Fin m)) :=
  (Finset.univ : Finset (Finset (Fin m))).toList

/-- The literal top exterior product, together with its required membership proof. -/
def basisWedge {M : Type} [AddCommGroup M] [Module R M] {r : ℕ}
    (b : Module.Basis (Fin r) R M)
    (h : ExteriorAlgebra.ιMulti R r b ∈ determinantSubmodule R M) :
    determinantModule R M := ⟨ExteriorAlgebra.ιMulti R r b, h⟩

/-- The actual top exterior coordinate restricted to the determinant submodule. -/
def basisCoordinate {M : Type} [AddCommGroup M] [Module R M] {r : ℕ}
    (b : Module.Basis (Fin r) R M) : Module.Dual R (determinantModule R M) :=
  (b.ExteriorAlgebra.coord Finset.univ).comp (determinantSubmodule R M).subtype

/-- Evaluation at an actual vector, as a functional on the actual module dual. -/
def dualCoordinate {M : Type} [AddCommGroup M] [Module R M] (x : M) :
    Module.Dual R (Module.Dual R M) where
  toFun a := a x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual free term bases, including the literal exterior membership proofs. -/
structure FreeBases (C : BoundedProjectiveDeterminants.Complex R) where
  rank : ℤ → ℕ
  basis : ∀ i : ℤ, Module.Basis (Fin (rank i)) R (C.cochain.X i)
  wedge_mem : ∀ i : ℤ,
    ExteriorAlgebra.ιMulti R (rank i) (basis i) ∈ determinantSubmodule R (C.cochain.X i)

/-- The actual boundary quotient into the next differential kernel. -/
def boundaryMap (C : BoundedProjectiveDeterminants.Complex R) (i : ℤ) :
    C.cochain.X i →ₗ[R] LinearMap.ker ((C.cochain.d (i+1) (i+2)).hom) :=
  ((C.cochain.d i (i+1)).hom).codRestrict _ (by
    intro x
    change (C.cochain.d (i+1) (i+2)) ((C.cochain.d i (i+1)) x) = 0
    exact congrArg (fun q : C.cochain.X i ⟶ C.cochain.X (i+2) ↦ q x)
      (C.cochain.d_comp_d i (i+1) (i+2)))

/-- No adapted vector can be replaced by an assigned torsion scalar. -/
structure AdaptedBases (C : BoundedProjectiveDeterminants.Complex R) where
  acyclic : ∀ i : ℤ, Function.Surjective (boundaryMap R C i)
  kernelRank : ℤ → ℕ
  kernelBasis : ∀ i : ℤ, Module.Basis (Fin (kernelRank i)) R
    (LinearMap.ker ((C.cochain.d i (i+1)).hom))
  lift : ∀ i : ℤ, Fin (kernelRank (i+1)) → C.cochain.X i
  lift_source : ∀ (i : ℤ) (j : Fin (kernelRank (i+1))),
    (C.cochain.d i (i+1)) (lift i j) = (kernelBasis (i+1) j).val
  termBasis : ∀ i : ℤ,
    Module.Basis (Fin (kernelRank i + kernelRank (i+1))) R (C.cochain.X i)
  termBasis_source : ∀ i : ℤ,
    (termBasis i : Fin (kernelRank i + kernelRank (i+1)) → C.cochain.X i) =
      Fin.append (fun j ↦ (kernelBasis i j).val) (lift i)
  wedge_mem : ∀ i : ℤ,
    ExteriorAlgebra.ιMulti R (kernelRank i + kernelRank (i+1)) (termBasis i) ∈
      determinantSubmodule R (C.cochain.X i)

variable {R} in
def AdaptedBases.asFree {C : BoundedProjectiveDeterminants.Complex R} (B : AdaptedBases R C) :
    FreeBases R C := ⟨fun i ↦ B.kernelRank i + B.kernelRank (i+1), B.termBasis, B.wedge_mem⟩

variable (C : BoundedProjectiveDeterminants.Complex R) (B : FreeBases R C)

/-- Even factors are exterior products; odd factors are literal dual coordinates. -/
def termVector (i : ℤ) : term R C i := by
  classical
  by_cases h : Even i
  · simpa only [term, h, ite_true] using basisWedge R (B.basis i) (B.wedge_mem i)
  · simpa only [term, h, ite_false] using basisCoordinate R (B.basis i)

def termCoordinate (i : ℤ) : Module.Dual R (term R C i) := by
  classical
  by_cases h : Even i
  · have hi : term R C i = ModuleCat.of R (determinantModule R (C.cochain.X i)) := by
      simp [term, h]
    rw [hi]
    exact basisCoordinate R (B.basis i)
  · have hi : term R C i =
        ModuleCat.of R (Module.Dual R (determinantModule R (C.cochain.X i))) := by
      simp [term, h]
    rw [hi]
    exact dualCoordinate R (basisWedge R (B.basis i) (B.wedge_mem i))

/-- The literal ordered pure tensor, including its actual empty scalar unit. -/
def tensorVector : (is : List ℤ) → tensorTerms R C is
  | [] => (1 : R)
  | i :: is => termVector R C B i ⊗ₜ[R] tensorVector is

/-- Tensor dual coordinates are computed by the native tensor universal property. -/
def tensorCoordinate : (is : List ℤ) → Module.Dual R (tensorTerms R C is)
  | [] => LinearMap.id
  | i :: is => TensorProduct.lift ((termCoordinate R C B i).smulRight (tensorCoordinate is))

def determinantVector : determinantObject R C := tensorVector R C B (degrees R C)
def determinantCoordinate : Module.Dual R (determinantObject R C) :=
  tensorCoordinate R C B (degrees R C)

/-- The canonical acyclic torsion in the SAME original cochain degree order. -/
def acyclicTorsion (A : AdaptedBases R C) : determinantObject R C :=
  determinantVector R C A.asFree

variable {m : ℕ} (Q : Finset (Fin m) → BoundedProjectiveDeterminants.Complex R)

abbrev FreeSubsetBases := ∀ t : Finset (Fin m), FreeBases R (Q t)

def signedFactor (t : Finset (Fin m)) : ModuleCat.{0} R := by
  classical
  exact if RelativeDeterminantPairings.IsPositive t then determinantObject R (Q t)
    else ModuleCat.of R (Module.Dual R (determinantObject R (Q t)))

def pairingFold (ss : List (Finset (Fin m))) : ModuleCat.{0} R :=
  ss.foldr (fun t M ↦ signedFactor R Q t ⊗ M) (𝟙_ (ModuleCat.{0} R))

def pairingObject : ModuleCat.{0} R := pairingFold R Q (subsets m)

def factorVector (A : FreeSubsetBases R Q) (t : Finset (Fin m)) : signedFactor R Q t := by
  classical
  by_cases h : RelativeDeterminantPairings.IsPositive t
  · simpa only [signedFactor, h, ite_true] using determinantVector R (Q t) (A t)
  · simpa only [signedFactor, h, ite_false] using determinantCoordinate R (Q t) (A t)

def pairingVector (A : FreeSubsetBases R Q) :
    (ss : List (Finset (Fin m))) → pairingFold R Q ss
  | [] => (1 : R)
  | t :: ss => factorVector R Q A t ⊗ₜ[R] pairingVector A ss

/-- The actual ordered source term sum; the empty sum is the native zero module. -/
def sumTerms (i : ℤ) : (ss : List (Finset (Fin m))) → ModuleCat.{0} R
  | [] => ModuleCat.of R PUnit
  | t :: ss => ModuleCat.of R ((Q t).cochain.X (i-subsetDegree t) × sumTerms i ss)

def sumProjection (i : ℤ) (t : Finset (Fin m)) : (ss : List (Finset (Fin m))) →
    sumTerms R Q i ss →ₗ[R] (Q t).cochain.X (i-subsetDegree t)
  | [] => 0
  | u :: ss => by
    classical
    by_cases h : u = t
    · subst u
      exact LinearMap.fst R _ _
    · exact (sumProjection i t ss).comp (LinearMap.snd R _ _)

def sumInclusion (i : ℤ) (t : Finset (Fin m)) : (ss : List (Finset (Fin m))) →
    (Q t).cochain.X (i-subsetDegree t) →ₗ[R] sumTerms R Q i ss
  | [] => 0
  | u :: ss => by
    classical
    by_cases h : u = t
    · subst u
      exact LinearMap.inl R _ _
    · exact (LinearMap.inr R _ _).comp (sumInclusion i t ss)

/-- The actual sum inclusion/projection between two specified subset lists. -/
def sumBetween (i : ℤ) (ss ts : List (Finset (Fin m))) :
    sumTerms R Q i ss →ₗ[R] sumTerms R Q i ts :=
  ss.foldr (fun t a ↦ (sumInclusion R Q i t ts).comp (sumProjection R Q i t ss) + a) 0

/-- A specified subset filtration piece retains its literal original term modules. -/
structure ListTermModel (ss : List (Finset (Fin m))) where
  complex : BoundedProjectiveDeterminants.Complex R
  terms : ∀ i : ℤ, complex.cochain.X i = sumTerms R Q i ss

variable {R Q} in
def ListTermModel.termIso {ss : List (Finset (Fin m))} (M : ListTermModel R Q ss) (i : ℤ) :
    M.complex.cochain.X i ≅ sumTerms R Q i ss := eqToIso (M.terms i)

instance sumTerms_finite (i : ℤ) (ss : List (Finset (Fin m))) :
    Module.Finite R (sumTerms R Q i ss) := by
  induction ss with
  | nil => exact inferInstanceAs (Module.Finite R PUnit)
  | cons t ss ih =>
    exact inferInstanceAs (Module.Finite R ((Q t).cochain.X (i-subsetDegree t) × sumTerms R Q i ss))

instance sumTerms_projective (i : ℤ) (ss : List (Finset (Fin m))) :
    Module.Projective R (sumTerms R Q i ss) := by
  induction ss with
  | nil => exact inferInstanceAs (Module.Projective R PUnit)
  | cons t ss ih =>
    exact inferInstanceAs (Module.Projective R ((Q t).cochain.X (i-subsetDegree t) × sumTerms R Q i ss))

def sumDeterminants (i : ℤ) (ss : List (Finset (Fin m))) : ModuleCat.{0} R :=
  ss.foldr (fun t M ↦ ModuleCat.of R
    (determinantModule R ((Q t).cochain.X (i-subsetDegree t))) ⊗ M)
      (𝟙_ (ModuleCat.{0} R))

theorem sndSurjective (M N : ModuleCat.{0} R) : Function.Surjective (LinearMap.snd R M N) :=
  fun n ↦ ⟨(0,n), rfl⟩

/-- The actual kernel inclusion of the native product projection. -/
def fstKernelEquiv (M N : ModuleCat.{0} R) : M ≃ₗ[R] LinearMap.ker (LinearMap.snd R M N) where
  toFun m := ⟨(m,0), rfl⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact x.property.symm
  map_add' x y := by
    apply Subtype.ext
    exact Prod.ext rfl (zero_add 0).symm
  map_smul' r x := by
    apply Subtype.ext
    exact Prod.ext rfl (smul_zero r).symm

/-- Every termwise determinant primitive uses this fixed actual projection. -/
structure SumExactSources where
  exact : ∀ (i : ℤ) (t : Finset (Fin m)) (ss : List (Finset (Fin m))),
    ShortExactDeterminant
      (LinearMap.snd R ((Q t).cochain.X (i-subsetDegree t)) (sumTerms R Q i ss))
      (sndSurjective R ((Q t).cochain.X (i-subsetDegree t)) (sumTerms R Q i ss))

variable (E : SumExactSources R Q)

/-- Literal recursive exact-sequence exterior comparison in the original subset order. -/
def sumDeterminant : (i : ℤ) → (ss : List (Finset (Fin m))) →
    ModuleCat.of R (determinantModule R (sumTerms R Q i ss)) ≅ sumDeterminants R Q i ss
  | _i, [] => (DeterminantZeroUnits.zeroEquiv R (ModuleCat.of R PUnit)
      (ModuleCat.isZero_of_subsingleton _)).toModuleIso
  | i, t :: ss =>
    (E.exact i t ss).comparison.toModuleIso.symm ≪≫
      tensorIso (determinantEquiv
        (fstKernelEquiv R ((Q t).cochain.X (i-subsetDegree t)) (sumTerms R Q i ss)).symm).toModuleIso
        (sumDeterminant i ss)

def sumVector (A : FreeSubsetBases R Q) (i : ℤ) :
    (ss : List (Finset (Fin m))) → sumDeterminants R Q i ss
  | [] => (1 : R)
  | t :: ss =>
    basisWedge R ((A t).basis (i-subsetDegree t)) ((A t).wedge_mem (i-subsetDegree t)) ⊗ₜ[R]
      sumVector A i ss

def sumCoordinate (A : FreeSubsetBases R Q) (i : ℤ) :
    (ss : List (Finset (Fin m))) → Module.Dual R (sumDeterminants R Q i ss)
  | [] => LinearMap.id
  | t :: ss => TensorProduct.lift
    ((basisCoordinate R ((A t).basis (i-subsetDegree t))).smulRight (sumCoordinate A i ss))

/-- Original terms are a literal sum. Scalar-localized terms carry the uniquely
normalized native sum comparison, rather than a new affine presentation. -/
structure TermAssembly where
  termIso : ∀ i : ℤ, C.cochain.X i ≅ sumTerms R Q i (subsets m)

/-- The total cochain terms are literally the same ordered subset presentation modules. -/
structure TotalTermModel where
  complex : BoundedProjectiveDeterminants.Complex R
  terms : ∀ i : ℤ, complex.cochain.X i = sumTerms R Q i (subsets m)

variable {R Q} in
def TotalTermModel.assembly (M : TotalTermModel R Q) : TermAssembly R M.complex Q :=
  ⟨fun i ↦ eqToIso (M.terms i)⟩

variable {R Q} in
def TotalTermModel.block (M : TotalTermModel R Q) (i : ℤ) (t u : Finset (Fin m)) :
    (Q t).cochain.X (i-subsetDegree t) ⟶ (Q u).cochain.X (i+1-subsetDegree u) :=
  ModuleCat.ofHom (sumInclusion R Q i t (subsets m)) ≫ (M.assembly.termIso i).inv ≫
    M.complex.cochain.d i (i+1) ≫ (M.assembly.termIso (i+1)).hom ≫
      ModuleCat.ofHom (sumProjection R Q (i+1) u (subsets m))

variable (T : TermAssembly R C Q)

def termAssemblyDeterminant (i : ℤ) :
    ModuleCat.of R (determinantModule R (C.cochain.X i)) ≅ sumDeterminants R Q i (subsets m) :=
  (determinantEquiv (T.termIso i).toLinearEquiv).toModuleIso ≪≫ sumDeterminant R Q E i (subsets m)

/-- Exact-sequence exterior products in even degree; their actual duals in odd degree. -/
def assembledTermVector (A : FreeSubsetBases R Q) (i : ℤ) : term R C i := by
  classical
  by_cases h : Even i
  · simpa only [term, h, ite_true] using
      (termAssemblyDeterminant R C Q E T i).inv (sumVector R Q A i (subsets m))
  · simpa only [term, h, ite_false] using
      (sumCoordinate R Q A i (subsets m)).comp (termAssemblyDeterminant R C Q E T i).hom.hom

def assembledTensorVector (A : FreeSubsetBases R Q) :
    (is : List ℤ) → tensorTerms R C is
  | [] => (1 : R)
  | i :: is => assembledTermVector R C Q E T A i ⊗ₜ[R] assembledTensorVector A is

def assembledVector (A : FreeSubsetBases R Q) : determinantObject R C :=
  assembledTensorVector R C Q E T A (degrees R C)

section Scalar

variable [FourierMukai.HasDerivedPullbacks.{0}]
  [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ A : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor A)]
  [∀ A : CommRingCat.{0}, BoundedProjectiveDeterminants.ProjectiveSources A]

variable (I : DeterminantSources) {R₀ S₀ : CommRingCat.{0}} (g : R₀ ⟶ S₀)
  {m : ℕ} (Q₀ : Finset (Fin m) → BoundedProjectiveDeterminants.Complex R₀)

/-- These are scalar extensions of the ORIGINAL subset cochains, never fresh affine sources. -/
def scalarFamily : Finset (Fin m) → BoundedProjectiveDeterminants.Complex S₀ :=
  fun t ↦ (I.scalar g (Q₀ t)).target

/-- Scalar normalization uses the actual determinant counit and actual dual evaluation. -/
def scalarFactorComparison (A : DeterminantScalarTensorModels.ScalarTensorSources g)
    (t : Finset (Fin m)) :
    (ModuleCat.extendScalars g.hom).obj (signedFactor R₀ Q₀ t) ≅
      signedFactor S₀ (scalarFamily I g Q₀) t := by
  classical
  let e := (I.comparison g (Q₀ t)).comparison
  by_cases h : RelativeDeterminantPairings.IsPositive t
  · simpa only [signedFactor, h, ite_true, scalarFamily] using e
  · haveI := determinantObject_invertible R₀ (Q₀ t)
    let M := determinantObject R₀ (Q₀ t)
    let d := A.dual M inferInstance inferInstance ≪≫ e.toLinearEquiv.symm.dualMap.toModuleIso
    simpa only [signedFactor, h, ite_false, scalarFamily] using d

def scalarPairingFoldComparison (A : DeterminantScalarTensorModels.ScalarTensorSources g) :
    (ss : List (Finset (Fin m))) →
      (ModuleCat.extendScalars g.hom).obj (pairingFold R₀ Q₀ ss) ≅
        pairingFold S₀ (scalarFamily I g Q₀) ss
  | [] => A.unit
  | t :: ss => A.tensor (signedFactor R₀ Q₀ t) (pairingFold R₀ Q₀ ss) ≪≫
      tensorIso (scalarFactorComparison I g Q₀ A t) (scalarPairingFoldComparison A ss)

def scalarPairingComparison (A : DeterminantScalarTensorModels.ScalarTensorSources g) :
    (ModuleCat.extendScalars g.hom).obj (pairingObject R₀ Q₀) ≅
      pairingObject S₀ (scalarFamily I g Q₀) :=
  scalarPairingFoldComparison I g Q₀ A (subsets m)

/-- The direct sum scalar map is computed from the actual degreewise cochain counits. -/
def sumScalarMap (i : ℤ) : (ss : List (Finset (Fin m))) →
    sumTerms R₀ Q₀ i ss →ₛₗ[g.hom] sumTerms S₀ (scalarFamily I g Q₀) i ss
  | [] => 0
  | t :: ss =>
    { toFun x := (component g (Q₀ t) (I.scalar g (Q₀ t)) (i-subsetDegree t) x.1,
        sumScalarMap i ss x.2)
      map_add' _x _y := Prod.ext (map_add _ _ _) (map_add _ _ _)
      map_smul' _r _x := Prod.ext (map_smulₛₗ _ _ _) (map_smulₛₗ _ _ _) }

variable (C₀ : BoundedProjectiveDeterminants.Complex R₀) (T₀ : TermAssembly R₀ C₀ Q₀)

/-- Every localized sum comparison is fixed on all original source vectors. -/
structure LocalizedAssembly extends
    TermAssembly S₀ (I.scalar g C₀).target (scalarFamily I g Q₀) where
  normalized : ∀ (i : ℤ) (x : C₀.cochain.X i),
    (termIso i).hom (component g C₀ (I.scalar g C₀) i x) =
      sumScalarMap I g Q₀ i (subsets m) ((T₀.termIso i).hom x)

/-- A genuine principal affine localization cover, with actual free sources
for both the original subset modules and the differential kernels. -/
structure EvaluationCover where
  index : Type
  ring : index → CommRingCat.{0}
  element : index → R₀
  map : ∀ c : index, R₀ ⟶ ring c
  [algebra : ∀ c : index, Algebra R₀ (ring c)]
  map_normalized : ∀ c : index, (map c).hom = algebraMap R₀ (ring c)
  [localization : ∀ c : index, IsLocalization.Away (element c) (ring c)]
  [openMap : ∀ c : index, IsOpenImmersion (Spec.map (map c))]
  cover : ∀ x : Spec R₀, ∃ (c : index) (y : Spec (ring c)), Spec.map (map c) y = x
  subsetBases : ∀ c : index, FreeSubsetBases (ring c) (scalarFamily I (map c) Q₀)
  adaptedBases : ∀ c : index, AdaptedBases (ring c) (I.scalar (map c) C₀).target

variable {g T₀}

/-- Localization of a fixed comparison uses only the same native scalar maps. -/
def localizedComparison (e : determinantObject R₀ C₀ ≅ pairingObject R₀ Q₀)
    (A : DeterminantScalarTensorModels.ScalarTensorSources g) :
    determinantObject S₀ (I.scalar g C₀).target ≅
      pairingObject S₀ (scalarFamily I g Q₀) :=
  (I.comparison g C₀).comparison.symm ≪≫
    (ModuleCat.extendScalars g.hom).mapIso e ≪≫ scalarPairingComparison I g Q₀ A

variable (T₀) in
/-- The fixed canonical comparison and torsion are normalized on every actual
localization and every actual basis choice. The inhabited principal cover
keeps the normalization nonvacuous for finite projective nonfree terms. -/
structure CanonicalEvaluation where
  assembly : ∀ {A : CommRingCat.{0}} (h : R₀ ⟶ A), LocalizedAssembly I h Q₀ C₀ T₀
  exact : ∀ {A : CommRingCat.{0}} (h : R₀ ⟶ A), SumExactSources A (scalarFamily I h Q₀)
  freeCover : EvaluationCover I Q₀ C₀
  torsion : determinantObject R₀ C₀
  torsion_normalized : ∀ {A : CommRingCat.{0}} (h : R₀ ⟶ A)
    (B : AdaptedBases A (I.scalar h C₀).target),
    (I.comparison h C₀).comparison.hom
      (DeterminantScalarTensorModels.vector h (determinantObject R₀ C₀) torsion) =
        acyclicTorsion A (I.scalar h C₀).target B
  comparison : determinantObject R₀ C₀ ≅ pairingObject R₀ Q₀
  comparison_normalized : ∀ {A : CommRingCat.{0}} (h : R₀ ⟶ A)
    (V : DeterminantScalarTensorModels.ScalarTensorSources h)
    (B : FreeSubsetBases A (scalarFamily I h Q₀)),
    (localizedComparison I Q₀ C₀ comparison V).hom
      (assembledVector A (I.scalar h C₀).target (scalarFamily I h Q₀)
        (exact h) (assembly h).toTermAssembly B) =
      pairingVector A (scalarFamily I h Q₀) B (subsets m)

variable {I Q₀ C₀} in
/-- The symbol is the image of THAT fixed acyclic torsion, with no inverse-unit word. -/
def CanonicalEvaluation.value (E₀ : CanonicalEvaluation I Q₀ C₀ T₀) : pairingObject R₀ Q₀ :=
  E₀.comparison.hom E₀.torsion

end Scalar

end MathlibExt.AlgebraicGeometry.CanonicalKoszulDeterminants
