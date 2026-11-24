/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.ProperShuffleEulerianSection
public import MathlibExt.Algebra.Homology.Hochschild.ProperShuffleCotangentQuasiIsoDegreeZero
public import MathlibExt.Algebra.Homology.Hochschild.PolynomialEulerianRepresentatives
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology

/-!
# Polynomial proper-shuffle acyclicity

For a polynomial algebra over a rational ground ring and
an arbitrary symmetric coefficient module, degree-n
Hochschild homology has Eulerian weight n. The proper
quotient retains weights zero and one, so its homology
vanishes above degree one. After positive-index restriction,
all positive degrees of the shifted cotangent complex vanish.
Variables and coefficient universes are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] [Algebra ℚ k] (σ : Type v)
  (M : Type w) [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [SMulCommClass k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]

local notation "A" => MvPolynomial σ k

/-- The first projector kills each original signed polynomial class above degree one. -/
theorem polynomialFirstEulerianHomology_polynomialClass_zero (n : ℕ) (hn : 2 ≤ n)
    (x : M ⊗[k] (⋀[k]^n (σ →₀ k))) :
    HomologicalComplex.homologyMap (Symmetric.firstEulerianChainMap k A M) n
      (polynomialAntisymmetricExteriorClass k σ M n x) = 0 := by
  have hx : ((Symmetric.firstEulerianChainMap k A M).f n).hom
      (polynomialSignedRepresentative k σ M n x) = 0 := by
    change Symmetric.coefficientEulerianOperator k A M n 0
        (polynomialSignedRepresentative k σ M n x) +
      Symmetric.coefficientEulerianOperator k A M n 1
        (polynomialSignedRepresentative k σ M n x) = 0
    rw [polynomialSignedRepresentative_eulerian, polynomialSignedRepresentative_eulerian,
      ite_eq_right (by omega : (0 : ℕ) ≠ n), ite_eq_right (by omega : (1 : ℕ) ≠ n), zero_add]
  let K := Symmetric.chainComplex k A M
  let F : K ⟶ K := Symmetric.firstEulerianChainMap k A M
  let y : K.X n := polynomialSignedRepresentative k σ M n x
  have hy : (K.sc n).g.hom y = 0 := polynomialSignedRepresentative_cycle k σ M n x
  have hClass := polynomialAntisymmetricExteriorClass_eq_cycle k σ M n x
  have hMap := HomologicalComplex.moduleCatCycleClass_naturality F n y hy
  have hz : (F.f n).hom y = (0 : K.X n) := hx
  have hFcycle : (K.sc n).g.hom ((F.f n).hom y) = 0 := by
    have h := ConcreteCategory.congr_hom (F.comm n ((ComplexShape.down ℕ).next n)) y
    change (K.sc n).g.hom ((F.f n).hom y) =
      (F.f ((ComplexShape.down ℕ).next n)).hom ((K.sc n).g.hom y) at h
    exact h.trans ((congrArg (F.f ((ComplexShape.down ℕ).next n)).hom hy).trans
      (F.f ((ComplexShape.down ℕ).next n)).hom.map_zero)
  have hZero (z : K.X n) (hc : (K.sc n).g.hom z = 0) (hz' : z = 0) :
      HomologicalComplex.moduleCatCycleClass K n z hc = 0 := by
    subst z
    exact HomologicalComplex.moduleCatCycleClass_zero K n hc
  change (HomologicalComplex.homologyMap F n).hom (polynomialAntisymmetricExteriorClass k σ M n x) = 0
  exact (congrArg (HomologicalComplex.homologyMap F n).hom hClass).trans
    (hMap.trans (hZero ((F.f n).hom y) hFcycle hz))

/-- The polynomial first chain projector is zero on every homology degree above one.
The polynomial comparison supplies every original homology class. -/
theorem polynomialFirstEulerianHomology_zero (n : ℕ) (hn : 2 ≤ n) :
    HomologicalComplex.homologyMap (Symmetric.firstEulerianChainMap k A M) n = 0 := by
  apply ModuleCat.hom_ext
  let H := (HomologicalComplex.homologyMap (Symmetric.firstEulerianChainMap k A M) n).hom
  change H = 0
  apply LinearMap.ext
  intro z
  let e := polynomialAntisymmetrizationHomologyEquiv k σ M n
  obtain ⟨ω, hω⟩ := e.surjective z
  have he : e ω = polynomialAntisymmetrizationHomology k σ M n ω :=
    (congrFun (LinearEquiv.coe_toLinearMap e) ω).symm.trans
      (LinearMap.congr_fun (polynomialAntisymmetrizationHomologyEquiv_toLinearMap k σ M n) ω)
  have hclass : polynomialAntisymmetrizationHomology k σ M n ω =
      polynomialAntisymmetricExteriorClass k σ M n
        ((KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n).symm ω) := rfl
  have hz := polynomialFirstEulerianHomology_polynomialClass_zero k σ M n hn
    ((KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n).symm ω)
  exact (congrArg H hω.symm).trans ((congrArg H (he.trans hclass)).trans hz)

/-- The split quotient and polynomial Hodge purity force every higher proper homology identity to zero. -/
theorem polynomialProperShuffleHomology_id_zero (n : ℕ) (hn : 2 ≤ n) :
    𝟙 ((Symmetric.positiveQuotient k A M).homology n) = 0 := by
  let s := HomologicalComplex.homologyMap (Symmetric.properEulerianSection k A M) n
  let p := HomologicalComplex.homologyMap (Symmetric.properShuffleProjection k A M) n
  have hs : s ≫ p = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, Symmetric.properEulerianSection_projection,
      HomologicalComplex.homologyMap_id]
  have hp : p ≫ s = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, Symmetric.properShuffleProjection_eulerianSection]
    exact polynomialFirstEulerianHomology_zero k σ M n hn
  have hz : s = 0 := by
    calc
      s = (s ≫ p) ≫ s := by rw [hs, Category.id_comp]
      _ = s ≫ (p ≫ s) := Category.assoc _ _ _
      _ = 0 := by rw [hp, Limits.comp_zero]
  exact hs.symm.trans ((congrArg (fun f => f ≫ p) hz).trans Limits.zero_comp)

/-- The original polynomial proper quotient has no homology in degrees n greater than one. -/
theorem polynomialProperShuffleHomology_isZero (n : ℕ) (hn : 2 ≤ n) :
    IsZero ((Symmetric.positiveQuotient k A M).homology n) :=
  (IsZero.iff_id_eq_zero _).mpr (polynomialProperShuffleHomology_id_zero k σ M n hn)

/-- Native restriction compares every positive shifted degree with the original proper quotient degree n+1. -/
def polynomialProperCotangentRestrictionHomologyIso (n : ℕ) (hn : 0 < n) :
    (Symmetric.properCotangentComplex k A M).homology n ≅
      (Symmetric.positiveQuotient k A M).homology (n + 1) :=
  (Symmetric.positiveQuotient k A M).restrictionHomologyIso ComplexShape.positiveNatEmbedding
    (n + 1) n (n - 1)
    ((ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl))
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel n (n - 1) from by
      change n - 1 + 1 = n
      omega))
    (show ComplexShape.positiveNatEmbedding.f (n + 1) = n + 2 from rfl)
    (show ComplexShape.positiveNatEmbedding.f n = n + 1 from rfl)
    (show ComplexShape.positiveNatEmbedding.f (n - 1) = n from by
      change n - 1 + 1 = n
      omega)
    ((ComplexShape.down ℕ).prev_eq'
      (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl))
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl))

/-- The original shifted polynomial proper cotangent complex is acyclic in every positive degree. -/
theorem polynomialProperCotangentHomology_isZero (n : ℕ) (hn : 0 < n) :
    IsZero ((Symmetric.properCotangentComplex k A M).homology n) :=
  (polynomialProperShuffleHomology_isZero k σ M (n + 1) (by omega)).of_iso
    (polynomialProperCotangentRestrictionHomologyIso k σ M n hn)

/-- Every degree of the original polynomial proper-shuffle cotangent map is a quasi-isomorphism.
Degree zero uses the Leibniz cokernel, and positive degrees use the polynomial Hodge purity. -/
instance polynomialProperShuffleCotangentMap_quasiIso :
    _root_.QuasiIso (Symmetric.properShuffleCotangentMap k A M) where
  quasiIsoAt n := by
    cases n with
    | zero => infer_instance
    | succ n =>
      apply (_root_.quasiIsoAt_iff_isIso_homologyMap _ _).mpr
      exact (polynomialProperCotangentHomology_isZero k σ M (n + 1) (by omega)).isIso
        (HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0
          (Symmetric.coefficientCotangentModule k A M) (n + 1) (by omega))
        (HomologicalComplex.homologyMap (Symmetric.properShuffleCotangentMap k A M) (n + 1))

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
