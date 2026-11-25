/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CyclicAlternatization
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.MatrixPositiveTail

/-!
# Finite matrix exterior-to-Connes degree maps

For a unital algebra over a commutative rational algebra, the degree-n map from exterior
degree n + 1 of a finite matrix algebra to the Connes quotient is normalized tail
antisymmetrization followed by generalized trace.

Its pure-wedge formula sums over signed tail permutations and cycles of matrix indices. The
degree-sign variant multiplies this map by `(-1)^n`; zero extension and algebra homomorphisms
preserve both formulas.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [Ring A] [Algebra k A]

local notation "Cλ" => ModuleCat.Algebra.Hochschild.NonUnital.connesComplex

/-- The exterior-to-Connes map on finite matrices, obtained by normalized tail antisymmetrization
followed by generalized trace. -/
def matrixCyclicDegreeMap (r n : ℕ) :
    (⋀[k]^(n + 1) (Matrix (Fin r) (Fin r) A)) →ₗ[k] ((Cλ k A).X n) :=
  ((ModuleCat.Algebra.Hochschild.Matrix.connesTrace k A r).f n).hom.comp
    (cyclicExterior k (Matrix (Fin r) (Fin r) A) n)

/-- The exterior-to-Connes map on finite matrices multiplied in degree n by `(-1)^n`. -/
def matrixCyclicWeibelDegreeMap (r n : ℕ) :
    (⋀[k]^(n + 1) (Matrix (Fin r) (Fin r) A)) →ₗ[k] ((Cλ k A).X n) :=
  (-1 : k) ^ n • matrixCyclicDegreeMap k A r n

/-- The complete closed-index-cycle trace of the tail antisymmetrization. -/
theorem matrixCyclicDegreeMap_pure (r n : ℕ)
    (a : Fin (n + 1) → Matrix (Fin r) (Fin r) A) :
    matrixCyclicDegreeMap k A r n (exteriorPower.ιMulti k (n + 1) a) =
      ∑ σ : Equiv.Perm (Fin n), σ.sign •
        ∑ γ : Fin (n + 1) → Fin r,
          ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
            (a 0 (γ 0) (γ 1) ⊗ₜ[k] PiTensorProduct.tprod k
              (fun j => a (σ j).succ (γ j.succ) (γ (j.succ + 1)))) := by
  rw [matrixCyclicDegreeMap, LinearMap.comp_apply, cyclicExterior_pure, cyclicTailSum,
    map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact (map_zsmul_unit ((ModuleCat.Algebra.Hochschild.Matrix.connesTrace k A r).f n).hom
    σ.sign _).trans (congrArg (fun x => σ.sign • x)
      (ModuleCat.Algebra.Hochschild.Matrix.connesTraceComponent_tprod k A r n
        (a 0) (fun j => a (σ j).succ)))

/-- The pure-wedge formula is `(-1)^n` times the normalized tail trace formula. -/
theorem matrixCyclicWeibelDegreeMap_pure (r n : ℕ)
    (a : Fin (n + 1) → Matrix (Fin r) (Fin r) A) :
    matrixCyclicWeibelDegreeMap k A r n (exteriorPower.ιMulti k (n + 1) a) =
      (-1 : k) ^ n • matrixCyclicDegreeMap k A r n (exteriorPower.ιMulti k (n + 1) a) := rfl

/-- Finite zero corners leave the complete exterior-to-cyclic trace component unchanged. -/
theorem matrixCyclicDegreeMap_zeroCorner {r s : ℕ} (h : r ≤ s) (n : ℕ) :
    (matrixCyclicDegreeMap k A s n).comp
      (exteriorPower.map (n + 1) (Matrix.zeroExtendLinear (k := k) (A := A) h)) =
      matrixCyclicDegreeMap k A r n := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change matrixCyclicDegreeMap k A s n
      (exteriorPower.map (n + 1) (Matrix.zeroExtendLinear (k := k) (A := A) h)
        (exteriorPower.ιMulti k (n + 1) a)) =
    matrixCyclicDegreeMap k A r n (exteriorPower.ιMulti k (n + 1) a)
  rw [exteriorPower.map_apply_ιMulti, matrixCyclicDegreeMap_pure, matrixCyclicDegreeMap_pure]
  apply Finset.sum_congr rfl
  intro σ _
  have ht := ModuleCat.Algebra.Hochschild.Matrix.generalizedTrace_zeroExtend k h n
    (a 0) (fun j => a (σ j).succ)
  simpa only [ModuleCat.Algebra.Hochschild.Matrix.generalizedTrace_tmul_tprod, map_sum,
    Function.comp_apply, Matrix.zeroExtendLinear_apply] using
    congrArg (fun x => σ.sign • ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n x) ht

/-- Top-left zero extension commutes with the signed exterior trace degree maps. -/
theorem matrixCyclicWeibelDegreeMap_zeroCorner {r s : ℕ} (h : r ≤ s) (n : ℕ) :
    (matrixCyclicWeibelDegreeMap k A s n).comp
      (exteriorPower.map (n + 1) (Matrix.zeroExtendLinear (k := k) (A := A) h)) =
      matrixCyclicWeibelDegreeMap k A r n := by
  rw [matrixCyclicWeibelDegreeMap, matrixCyclicWeibelDegreeMap, LinearMap.smul_comp,
    matrixCyclicDegreeMap_zeroCorner]

section Coefficients

variable {B : Type v} [Ring B] [Algebra k B]

/-- Coefficient naturality of the finite matrix exterior trace component. -/
theorem matrixCyclicDegreeMap_natural (f : A →ₐ[k] B) (r n : ℕ) :
    (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f.toNonUnitalAlgHom).f n).hom).comp
        (matrixCyclicDegreeMap k A r n) =
      (matrixCyclicDegreeMap k B r n).comp
        (exteriorPower.map (n + 1) (f.mapMatrix (m := Fin r)).toLinearMap) := by
  rw [matrixCyclicDegreeMap, matrixCyclicDegreeMap, ← LinearMap.comp_assoc]
  have ht := congrArg (fun g => (g.f n).hom)
    (ModuleCat.Algebra.Hochschild.Matrix.connesTrace_natural k A f r)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp] at ht
  have hn := cyclicExterior_natural k (Matrix (Fin r) (Fin r) A)
    (f.mapMatrix (m := Fin r)).toNonUnitalAlgHom n
  change (((ModuleCat.Algebra.Hochschild.Matrix.connesMatrixCoefficientMap k A f r).f n).hom).comp
      (cyclicExterior k (Matrix (Fin r) (Fin r) A) n) =
    (cyclicExterior k (Matrix (Fin r) (Fin r) B) n).comp
      (exteriorPower.map (n + 1) (f.mapMatrix (m := Fin r)).toLinearMap) at hn
  rw [← ht, LinearMap.comp_assoc, hn, ← LinearMap.comp_assoc]

end Coefficients

end ChevalleyEilenberg

end
