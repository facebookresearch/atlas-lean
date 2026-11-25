/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.ProperShuffleCotangentNaturality
public import MathlibExt.Algebra.Homology.Hochschild.ProperShuffleEulerianSection
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Naturality of rational proper-shuffle sections

Compatible algebra and coefficient
maps commute with the zero-plus-first
Eulerian projector. The proper quotient
projection and section are natural,
giving arrow retracts of the original
Hochschild maps. Rational ground
structure and independent carrier
universes are retained.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  {A B : Type v} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  {M N : Type w} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module B N]
  [SMulCommClass k A M] [SMulCommClass k B N]
  [IsScalarTower k A M] [IsScalarTower k B N]

/-- Original coefficient and algebra maps preserve the original full first chain projector. -/
@[reassoc]
theorem firstChainMap_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    originalAlgebraCoefficientChainMap k g f hf ≫ firstEulerianChainMap k B N =
      firstEulerianChainMap k A M ≫ originalAlgebraCoefficientChainMap k g f hf := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp,
    originalAlgebraCoefficientChainMap_f, firstEulerianChainMap_f]
  change (firstEulerianOperator k B N n).comp (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) =
    (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n).comp (firstEulerianOperator k A M n)
  exact (firstOperator_naturality k g f n).symm

/-- Surjectivity of the quotient projection makes the original section natural. -/
@[reassoc]
theorem section_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    chainMap k g f hf ≫ properEulerianSection k B N =
      properEulerianSection k A M ≫ originalAlgebraCoefficientChainMap k g f hf := by
  let πA := properShuffleProjection k A M
  let πB := properShuffleProjection k B N
  let sA := properEulerianSection k A M
  let sB := properEulerianSection k B N
  let Γ := originalAlgebraCoefficientChainMap k g f hf
  let β := chainMap k g f hf
  have h : πA ≫ (β ≫ sB) = πA ≫ (sA ≫ Γ) := by
    calc
      _ = (πA ≫ β) ≫ sB := (Category.assoc _ _ _).symm
      _ = (Γ ≫ πB) ≫ sB := congrArg (fun t => t ≫ sB) (chainMap_projection k g f hf)
      _ = Γ ≫ firstEulerianChainMap k B N :=
        (Category.assoc _ _ _).trans
          (congrArg (fun t => Γ ≫ t) (properShuffleProjection_eulerianSection k B N))
      _ = firstEulerianChainMap k A M ≫ Γ := firstChainMap_naturality k g f hf
      _ = (πA ≫ sA) ≫ Γ :=
        congrArg (fun t => t ≫ Γ) (properShuffleProjection_eulerianSection k A M).symm
      _ = _ := Category.assoc _ _ _
  apply HomologicalComplex.hom_ext
  intro n
  let _ : Epi (πA.f n) := (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
  apply (cancel_epi (πA.f n)).mp
  have hn := congrArg (fun t : chainComplex k A M ⟶ chainComplex k B N => t.f n) h
  simpa only [HomologicalComplex.comp_f, Category.assoc] using hn

/-- The original quotient map is an arrow retract of the original Hochschild map. -/
def mapRetract (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    RetractArrow (chainMap k g f hf) (originalAlgebraCoefficientChainMap k g f hf) where
  i := Arrow.homMk (properEulerianSection k A M) (properEulerianSection k B N)
    (section_naturality k g f hf).symm
  r := Arrow.homMk (properShuffleProjection k A M) (properShuffleProjection k B N)
    (chainMap_projection k g f hf)
  retract := by
    apply Arrow.hom_ext
    · change properEulerianSection k A M ≫ properShuffleProjection k A M = 𝟙 (positiveQuotient k A M)
      exact properEulerianSection_projection k A M
    · change properEulerianSection k B N ≫ properShuffleProjection k B N = 𝟙 (positiveQuotient k B N)
      exact properEulerianSection_projection k B N

end ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle
