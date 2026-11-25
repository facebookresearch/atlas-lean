/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.KoszulComplexCoefficientExact
public import MathlibExt.Algebra.Homology.KoszulComplexAnnihilation
public import MathlibExt.Algebra.Homology.FiniteHomology
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Support

/-!
# Annihilation of Koszul homology with coefficients

Tensoring the Koszul scalar null-homotopies with a coefficient module shows
that the coefficient ideal annihilates tensor homology. The annihilator of
the module also annihilates this homology. Over a Noetherian ring, a finite coefficient module whose module-annihilator
quotient has finite length has finite Koszul homology lengths. The finite
exterior rank bounds the complex.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v w

namespace KoszulComplex

variable (R : Type u) [CommRing R] {n : ℕ}

/-- The original finite Koszul tensor complex has finite terms for finite
original coefficient modules. -/
theorem familyTensorCoefficientComplex_finite
    (a : Fin n → R) (M : ModuleCat.{v} R) [Module.Finite R M] (j : ℕ) :
    Module.Finite R ((familyTensorCoefficientComplex R a M).X j) := by
  let : Module.Finite R ((familyComplex R a).X j) := familyComplex_finite R a j
  exact inferInstanceAs (Module.Finite R (M ⊗[R] ((familyComplex R a).X j)))

/-- Every original coefficient value acts by a null-homotopic map on the
original tensor coefficient complex. -/
def familyTensorCoefficientSmulHomotopy (a : Fin n → R) (M : ModuleCat.{v} R)
    (i : Fin n) :
    Homotopy (a i • 𝟙 (familyTensorCoefficientComplex R a M)) 0 := by
  let F := coefficientTensorFunctor R M
  let x := familyFunctional R a
  let v : Fin n → R := Pi.single i 1
  have hx : x v = a i := familyFunctional_single R a i
  have h := F.mapHomotopy (smulIdHomotopyZero R (Fin n → R) x v)
  rw [hx] at h
  change Homotopy
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (a i • 𝟙 (familyComplex R a)))
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map 0) at h
  have he : (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (a i • 𝟙 (familyComplex R a)) =
      a i • 𝟙 (familyTensorCoefficientComplex R a M) := by
    apply HomologicalComplex.hom_ext
    intro j
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro m
    apply LinearMap.ext
    intro z
    change m ⊗ₜ[R] (a i • z) = a i • (m ⊗ₜ[R] z)
    exact TensorProduct.tmul_smul _ _ _
  rw [he, Functor.map_zero] at h
  exact h

/-- Scalar multiplication on an original module complex induces literal
scalar multiplication on its original homology. -/
theorem homologyMap_smul_id_module (K : ChainComplex (ModuleCat.{v} R) ℕ)
    (r : R) (j : ℕ) :
    HomologicalComplex.homologyMap (r • 𝟙 K) j = r • 𝟙 (K.homology j) := by
  have h := HomologicalComplex.homologyπ_naturality (r • 𝟙 K) j
  apply (cancel_epi (K.homologyπ j)).mp
  rw [h]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change K.homologyπ j ((HomologicalComplex.cyclesMap (r • 𝟙 K) j) z) =
    r • (K.homologyπ j z)
  have hz : (HomologicalComplex.cyclesMap (r • 𝟙 K) j) z = r • z := by
    apply ((ModuleCat.mono_iff_injective (K.iCycles j)).mp inferInstance)
    have hi := HomologicalComplex.cyclesMap_i (r • 𝟙 K) j
    have hi' := congrArg (fun f : K.cycles j ⟶ K.X j => f z) hi
    change K.iCycles j ((HomologicalComplex.cyclesMap (r • 𝟙 K) j) z) =
      r • (K.iCycles j z) at hi'
    simpa only [map_smul] using hi'
  rw [hz, map_smul]

/-- Every original graph coefficient annihilates the actual tensor-complex homology. -/
theorem familyTensorCoefficient_smul_homology_eq_zero
    (a : Fin n → R) (M : ModuleCat.{v} R) (i : Fin n) (j : ℕ)
    (z : (familyTensorCoefficientComplex R a M).homology j) :
    a i • z = 0 := by
  have h := (familyTensorCoefficientSmulHomotopy R a M i).homologyMap_eq j
  rw [homologyMap_smul_id_module, HomologicalComplex.homologyMap_zero] at h
  have hz := congrArg (fun f :
    (familyTensorCoefficientComplex R a M).homology j ⟶
      (familyTensorCoefficientComplex R a M).homology j => f z) h
  simpa using hz

/-- The original coefficient ideal annihilates the actual tensor homology. -/
theorem familyTensorCoefficient_ideal_le_annihilator
    (a : Fin n → R) (M : ModuleCat.{v} R) (j : ℕ) :
    Ideal.span (Set.range a) ≤
      Module.annihilator R ((familyTensorCoefficientComplex R a M).homology j) := by
  apply Ideal.span_le.mpr
  rintro r ⟨i, rfl⟩
  exact Module.mem_annihilator.mpr
    (familyTensorCoefficient_smul_homology_eq_zero R a M i j)

/-- An original module annihilator annihilates its actual tensor product. -/
theorem module_annihilator_smul_tensor_eq_zero
    (M : Type v) (N : Type w) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (r : R) (hr : r ∈ Module.annihilator R M) (z : M ⊗[R] N) : r • z = 0 := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [smul_add, hz, hw, add_zero]
  | tmul m x =>
      rw [TensorProduct.smul_tmul', Module.mem_annihilator.mp hr m,
        TensorProduct.zero_tmul]

/-- The original module annihilator annihilates every actual tensor term. -/
theorem familyTensorCoefficient_module_smul_term_eq_zero
    (a : Fin n → R) (M : ModuleCat.{v} R) (j : ℕ)
    (r : R) (hr : r ∈ Module.annihilator R M)
    (z : (familyTensorCoefficientComplex R a M).X j) : r • z = 0 :=
  module_annihilator_smul_tensor_eq_zero R M ((familyComplex R a).X j) r hr z

/-- The original module annihilator annihilates the actual tensor homology. -/
theorem familyTensorCoefficient_module_le_annihilator
    (a : Fin n → R) (M : ModuleCat.{v} R) (j : ℕ) :
    Module.annihilator R M ≤
      Module.annihilator R ((familyTensorCoefficientComplex R a M).homology j) := by
  intro r hr
  apply Module.mem_annihilator.mpr
  intro z
  let K := familyTensorCoefficientComplex R a M
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ j)).mp inferInstance z
  have hc : r • c = 0 := by
    apply (ModuleCat.mono_iff_injective (K.iCycles j)).mp inferInstance
    rw [map_smul, map_zero]
    exact familyTensorCoefficient_module_smul_term_eq_zero R a M j r hr _
  rw [← map_smul, hc, map_zero]

/-- The actual tensor homology is finite length whenever the original
coefficient/module-annihilator quotient has finite length. -/
theorem familyTensorCoefficient_homology_length_ne_top
    [IsNoetherianRing R] (a : Fin n → R) (M : ModuleCat.{v} R) [Module.Finite R M]
    (hquot : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤) (j : ℕ) :
    Module.length R ((familyTensorCoefficientComplex R a M).homology j) ≠ ⊤ := by
  let : Module.Finite R ((familyTensorCoefficientComplex R a M).X j) :=
    familyTensorCoefficientComplex_finite R a M j
  let : Module.Finite R ((familyTensorCoefficientComplex R a M).homology j) :=
    HomologicalComplex.homology_finite_of_finite R _ j
  exact Module.length_ne_top_of_finite_of_ideal_le_annihilator R _ _
    (sup_le (familyTensorCoefficient_ideal_le_annihilator R a M j)
      (familyTensorCoefficient_module_le_annihilator R a M j)) hquot

/-- The actual tensor complex vanishes above its finite exterior rank. -/
theorem familyTensorCoefficientComplex_isZero_above
    (a : Fin n → R) (M : ModuleCat.{v} R) (j : ℕ) (hj : n < j) :
    IsZero ((familyTensorCoefficientComplex R a M).X j) :=
  (coefficientTensorFunctor R M).map_isZero
    (familyComplex_isZero_above R a j (by simpa only [Fintype.card_fin] using hj))

end KoszulComplex
