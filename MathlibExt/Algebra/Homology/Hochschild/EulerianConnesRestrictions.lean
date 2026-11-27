/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.EulerianConnesHomology

/-!
# Boundaries restricted to normalized Eulerian weight spaces

Let k be a commutative ℚ-algebra and A a commutative unital k-algebra.
In N_n=A⊗[k](A/span_k{1})^{⊗n}, define
W_{n,i}=range(e_n^{(i)}) for the normalized Eulerian projector.
The normalized Hochschild boundary preserves weight and restricts to
b_{n,i}:W_{n+1,i}→W_{n,i}. Regular Connes boundary raises weight,
giving B_{n,i}:W_{n,i}→W_{n+1,i+1}.

The restrictions have the same values as b and B in the ambient
tensor modules. They satisfy b²=0, B²=0 and bB+Bb=0 on the
corresponding weight spaces, in every degree and weight.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]

/-- Let k be a commutative ℚ-algebra and A a commutative unital
k-algebra. Set Ā=A/span_k{1}, N_n=A⊗[k]Ā^{⊗n}, and
let e_n^{(i)} be the normalized rational Eulerian projectors.
The degree-n Eulerian weight-i space is the k-submodule
W_{n,i}=range(e_n^{(i)}) of N_n. -/
def normalizedEulerianWeightSpace (n i : ℕ) :
    Submodule k (A ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) :=
  LinearMap.range (normalizedEulerianOperator k A A n i)

/-- Let k be a commutative ℚ-algebra and A a commutative unital
k-algebra. Set Ā=A/span_k{1}, N_n=A⊗[k]Ā^{⊗n}, and
let e_n^{(i)} be the normalized rational Eulerian projectors.
Write W_{n,i}=range(e_n^{(i)}), b for normalized Hochschild
boundary and B for the regular normalized Connes boundary.
The Hochschild boundary restricts to the k-linear map
b_{n,i}:W_{n+1,i}→W_{n,i}. -/
def normalizedEulerianWeightBoundary (n i : ℕ) :
    normalizedEulerianWeightSpace k A (n + 1) i →ₗ[k] normalizedEulerianWeightSpace k A n i :=
  (((normalizedChainComplex k A A).d (n + 1) n).hom.comp
    (normalizedEulerianWeightSpace k A (n + 1) i).subtype).codRestrict _ (by
      intro x
      obtain ⟨y, hy⟩ := x.property
      refine ⟨((normalizedChainComplex k A A).d (n + 1) n).hom y, ?_⟩
      have h := DFunLike.congr_fun (normalizedEulerianOperator_boundary k A A n i) y
      exact h.symm.trans (congrArg ((normalizedChainComplex k A A).d (n + 1) n).hom hy))

/-- Let k be a commutative ℚ-algebra and A a commutative unital
k-algebra. Set Ā=A/span_k{1}, N_n=A⊗[k]Ā^{⊗n}, and
let e_n^{(i)} be the normalized rational Eulerian projectors.
Write W_{n,i}=range(e_n^{(i)}), b for normalized Hochschild
boundary and B for the regular normalized Connes boundary.
The Connes boundary restricts to the k-linear map
B_{n,i}:W_{n,i}→W_{n+1,i+1}. -/
def normalizedEulerianWeightConnes (n i : ℕ) :
    normalizedEulerianWeightSpace k A n i →ₗ[k] normalizedEulerianWeightSpace k A (n + 1) (i + 1) :=
  ((regularNormalizedConnes k A n).hom.comp
    (normalizedEulerianWeightSpace k A n i).subtype).codRestrict _ (by
      intro x
      obtain ⟨y, hy⟩ := x.property
      refine ⟨(regularNormalizedConnes k A n).hom y, ?_⟩
      have h := DFunLike.congr_fun (normalizedEulerian_connes_shift k A n i) y
      exact h.symm.trans (congrArg (regularNormalizedConnes k A n).hom hy))

/-- Let k be a commutative ℚ-algebra and A a commutative unital
k-algebra. Set Ā=A/span_k{1}, N_n=A⊗[k]Ā^{⊗n}, and
let e_n^{(i)} be the normalized rational Eulerian projectors.
Write W_{n,i}=range(e_n^{(i)}), b for normalized Hochschild
boundary and B for the regular normalized Connes boundary.
For x∈W_{n+1,i}, the underlying value of b_{n,i}(x)
is the ambient normalized Hochschild boundary b_{n+1}(x). -/
theorem normalizedEulerianWeightBoundary_val (n i : ℕ)
    (x : normalizedEulerianWeightSpace k A (n + 1) i) :
    (normalizedEulerianWeightBoundary k A n i x).val =
      ((normalizedChainComplex k A A).d (n + 1) n).hom x.val := rfl

/-- Let k be a commutative ℚ-algebra and A a commutative unital
k-algebra. Set Ā=A/span_k{1}, N_n=A⊗[k]Ā^{⊗n}, and
let e_n^{(i)} be the normalized rational Eulerian projectors.
Write W_{n,i}=range(e_n^{(i)}), b for normalized Hochschild
boundary and B for the regular normalized Connes boundary.
For x∈W_{n,i}, the underlying value of B_{n,i}(x)
is the ambient regular normalized Connes value B_n(x). -/
theorem normalizedEulerianWeightConnes_val (n i : ℕ)
    (x : normalizedEulerianWeightSpace k A n i) :
    (normalizedEulerianWeightConnes k A n i x).val = (regularNormalizedConnes k A n).hom x.val := rfl

/-- Let k be a commutative ℚ-algebra and A a commutative unital
k-algebra. Set Ā=A/span_k{1}, N_n=A⊗[k]Ā^{⊗n}, and
let e_n^{(i)} be the normalized rational Eulerian projectors.
Write W_{n,i}=range(e_n^{(i)}), b for normalized Hochschild
boundary and B for the regular normalized Connes boundary.
Two consecutive fixed-weight Hochschild restrictions have
zero composite: b_{n,i}b_{n+1,i}=0. -/
theorem normalizedEulerianWeightBoundary_square (n i : ℕ) :
    (normalizedEulerianWeightBoundary k A n i).comp
      (normalizedEulerianWeightBoundary k A (n + 1) i) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, normalizedEulerianWeightBoundary_val,
    Submodule.coe_zero]
  change algebraNormalizedBoundary k A A n (algebraNormalizedBoundary k A A (n + 1) x.val) = 0
  exact congrArg (fun f :
    A ⊗[k] TensorPower k (n + 2) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) →ₗ[A]
    A ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) => f x.val)
      (algebraNormalizedBoundary_comp k A A n)

/-- Let k be a commutative ℚ-algebra and A a commutative unital
k-algebra. Set Ā=A/span_k{1}, N_n=A⊗[k]Ā^{⊗n}, and
let e_n^{(i)} be the normalized rational Eulerian projectors.
Write W_{n,i}=range(e_n^{(i)}), b for normalized Hochschild
boundary and B for the regular normalized Connes boundary.
Successive raised-weight Connes restrictions satisfy
B_{n+1,i+1}B_{n,i}=0. -/
theorem normalizedEulerianWeightConnes_square (n i : ℕ) :
    (normalizedEulerianWeightConnes k A (n + 1) (i + 1)).comp
      (normalizedEulerianWeightConnes k A n i) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := congrArg ModuleCat.Hom.hom (regularNormalizedConnes_square k A n)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, regularNormalizedConnes_hom] at h
  rw [normalizedConnesBoundary_eq_formula, normalizedConnesBoundary_eq_formula] at h
  change (normalizedConnesFormula k A (n + 1)).comp (normalizedConnesFormula k A n) = 0 at h
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, normalizedEulerianWeightConnes_val,
    Submodule.coe_zero, regularNormalizedConnes_hom]
  rw [normalizedConnesBoundary_eq_formula, normalizedConnesBoundary_eq_formula]
  change normalizedConnesFormula k A (n + 1) (normalizedConnesFormula k A n x.val) = 0
  exact congrArg (fun f :
    A ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) →ₗ[k]
    A ⊗[k] TensorPower k (n + 2) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) => f x.val) h

/-- Let k be a commutative ℚ-algebra and A a commutative unital
k-algebra. Set Ā=A/span_k{1}, N_n=A⊗[k]Ā^{⊗n}, and
let e_n^{(i)} be the normalized rational Eulerian projectors.
Write W_{n,i}=range(e_n^{(i)}), b for normalized Hochschild
boundary and B for the regular normalized Connes boundary.
On W_{n+1,i}, the mixed identity is
b_{n+1,i+1}B_{n+1,i}+B_{n,i}b_{n,i}=0,
with target W_{n+1,i+1}. -/
theorem normalizedEulerianWeight_mixed (n i : ℕ) :
    (normalizedEulerianWeightBoundary k A (n + 1) (i + 1)).comp
        (normalizedEulerianWeightConnes k A (n + 1) i) +
      (normalizedEulerianWeightConnes k A n i).comp (normalizedEulerianWeightBoundary k A n i) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := congrArg ModuleCat.Hom.hom (regularNormalizedConnes_mixed k A n)
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_zero, regularNormalizedConnes_hom] at h
  rw [normalizedConnesBoundary_eq_formula, normalizedConnesBoundary_eq_formula] at h
  change ((algebraNormalizedBoundary k A A (n + 1)).restrictScalars k).comp
      (normalizedConnesFormula k A (n + 1)) +
    (normalizedConnesFormula k A n).comp ((algebraNormalizedBoundary k A A n).restrictScalars k) = 0 at h
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.zero_apply,
    normalizedEulerianWeightBoundary_val, normalizedEulerianWeightConnes_val,
    Submodule.coe_add, Submodule.coe_zero, regularNormalizedConnes_hom]
  rw [normalizedConnesBoundary_eq_formula, normalizedConnesBoundary_eq_formula]
  change algebraNormalizedBoundary k A A (n + 1) (normalizedConnesFormula k A (n + 1) x.val) +
    normalizedConnesFormula k A n (algebraNormalizedBoundary k A A n x.val) = 0
  exact congrArg (fun f :
    A ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) →ₗ[k]
    A ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) => f x.val) h

end ModuleCat.Algebra.Hochschild.Symmetric
