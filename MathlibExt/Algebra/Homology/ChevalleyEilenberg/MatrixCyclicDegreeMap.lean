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
# Closed matrix cycles in exterior-to-cyclic degree maps

Let `k` be a commutative `ℚ`-algebra and `A` a unital `k`-algebra. In degree `n`, tail
alternation on `n+1` matrix inputs followed by generalized trace gives a map `⋀^(n+1)[k]
gl_r(A) → Cλ_n(A)`.

Its pure-wedge formula sums over signed permutations of the last `n` matrix factors and closed
index cycles `i₀,…,iₙ,i₀`. Each cycle contributes the coefficient-first tensor of the
successive matrix entries, in that order. The canonical CE convention multiplies this map by
`(-1)^n`. Zero extension and entry-algebra homomorphisms preserve these degree maps.
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

/-- The finite matrix exterior-to-cyclic quotient degree map.

Apply the rational tail-alternating exterior map and then the generalized matrix trace in
degree `n`. -/
def matrixCyclicDegreeMap (r n : ℕ) :
    (⋀[k]^(n + 1) (Matrix (Fin r) (Fin r) A)) →ₗ[k] ((Cλ k A).X n) :=
  ((ModuleCat.Algebra.Hochschild.Matrix.connesTrace k A r).f n).hom.comp
    (cyclicExterior k (Matrix (Fin r) (Fin r) A) n)

/-- The degree-signed matrix exterior-to-cyclic quotient map.

Multiply the tail-alternating trace map in degree `n` by `(-1)^n`. -/
def matrixCyclicWeibelDegreeMap (r n : ℕ) :
    (⋀[k]^(n + 1) (Matrix (Fin r) (Fin r) A)) →ₗ[k] ((Cλ k A).X n) :=
  (-1 : k) ^ n • matrixCyclicDegreeMap k A r n

/-- The signed tail-permutation and closed-index-cycle formula.

The map of a pure wedge is the sum over tail permutations and closed matrix-index cycles of
their coefficient-first cyclic tensor representatives, weighted by the permutation sign. -/
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

/-- The degree-sign formula on a pure matrix wedge.

The canonical-convention degree map is `(-1)^n` times the closed-cycle tail-alternation map. -/
theorem matrixCyclicWeibelDegreeMap_pure (r n : ℕ)
    (a : Fin (n + 1) → Matrix (Fin r) (Fin r) A) :
    matrixCyclicWeibelDegreeMap k A r n (exteriorPower.ιMulti k (n + 1) a) =
      (-1 : k) ^ n • matrixCyclicDegreeMap k A r n (exteriorPower.ιMulti k (n + 1) a) := rfl

/-- Stability of the finite matrix cyclic degree map under zero extension.

Extending all matrix factors by zeros and applying the larger-size degree map gives the
smaller-size map. -/
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

/-- Stability of the degree-signed cyclic trace under zero extension.

The exterior zero-extension map commutes with the degree-signed matrix trace map. -/
theorem matrixCyclicWeibelDegreeMap_zeroCorner {r s : ℕ} (h : r ≤ s) (n : ℕ) :
    (matrixCyclicWeibelDegreeMap k A s n).comp
      (exteriorPower.map (n + 1) (Matrix.zeroExtendLinear (k := k) (A := A) h)) =
      matrixCyclicWeibelDegreeMap k A r n := by
  rw [matrixCyclicWeibelDegreeMap, matrixCyclicWeibelDegreeMap, LinearMap.smul_comp,
    matrixCyclicDegreeMap_zeroCorner]

section Coefficients

variable {B : Type v} [Ring B] [Algebra k B]

/-- Coefficient naturality of the finite matrix cyclic degree map.

An entry-algebra homomorphism commutes with the exterior matrix coefficient map, generalized
trace, and induced cyclic quotient map. -/
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
