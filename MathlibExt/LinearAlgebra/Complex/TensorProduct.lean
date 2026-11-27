/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.FieldTheory.Galois.TensorProductDecomposition
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Ring.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Complex self-tensor over the real scalars

The ℂ-algebra equivalence Θ:ℂ⊗_ℝℂ≃ℂ×ℂ sends z⊗w to (zw,z*conj(w)), with complex scalars acting
on the first tensor factor. Its inverse sends (p,q) to ((p+q)/2)⊗1+((p-q)/(2i))⊗i. The two
real-algebra automorphisms are identity and conjugation.
-/

@[expose] public section
noncomputable section

open TensorProduct
open scoped ComplexConjugate

namespace Complex

private theorem realTensorIdentity_ne_conjugation :
    ((AlgEquiv.refl : ℂ ≃ₐ[ℝ] ℂ)) ≠ Complex.conjAe := by
  intro h
  have hI := congrArg (fun e : ℂ ≃ₐ[ℝ] ℂ => (e Complex.I).im) h
  norm_num at hI

/-- **Indexing the real-algebra automorphisms of ℂ.**

The equivalence realTensorAutomorphismIndex:Fin 2≃Aut_ℝ(ℂ) sends 0 to the identity and 1 to
complex conjugation.
-/
def realTensorAutomorphismIndex : Fin 2 ≃ (ℂ ≃ₐ[ℝ] ℂ) :=
  Equiv.ofBijective
    (fun j => if j = 0 then (AlgEquiv.refl : ℂ ≃ₐ[ℝ] ℂ) else Complex.conjAe) (by
      constructor
      · intro i j h
        fin_cases i <;> fin_cases j <;>
          simp_all [realTensorIdentity_ne_conjugation, Ne.symm realTensorIdentity_ne_conjugation]
      · intro σ
        rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with h | h
        · refine ⟨0, ?_⟩
          ext z
          exact (DFunLike.congr_fun h z).symm
        · refine ⟨1, ?_⟩
          ext z
          exact (DFunLike.congr_fun h z).symm)

/-- **Complex algebra equivalence of the real self-tensor.**

With the usual real scalar structure on ℂ, tensorProductRealAlgEquiv:ℂ⊗_ℝℂ≃ₐ[ℂ]ℂ×ℂ has pure
value z⊗w↦(zw,z*conj(w)).
-/
def tensorProductRealAlgEquiv :
    letI : Module ℝ ℂ := Complex.ofRealHom.toModule
    letI : Algebra ℝ ℂ := Complex.ofRealHom.toAlgebra
    (ℂ ⊗[ℝ] ℂ) ≃ₐ[ℂ] ℂ × ℂ := by
  letI : Module ℝ ℂ := Complex.ofRealHom.toModule
  letI : Algebra ℝ ℂ := Complex.ofRealHom.toAlgebra
  letI : IsAlgClosure ℝ ℂ :=
    { isAlgClosed := Complex.isAlgClosed
      isAlgebraic := inferInstance }
  exact (MilnorK.finiteGaloisTensorProductEquiv ℝ ℂ).trans
    ((AlgEquiv.piCongrLeft' ℂ (fun _ : ℂ ≃ₐ[ℝ] ℂ => ℂ)
      realTensorAutomorphismIndex.symm).trans
      (AlgEquiv.ofRingEquiv (f := RingEquiv.piFinTwo (fun _ : Fin 2 => ℂ)) (by
        intro z
        rfl)))

/-- **Pure tensor coordinates of the complex algebra equivalence.**

For z,w∈ℂ, tensorProductRealAlgEquiv(z⊗_ℝw)=(zw,z*conj(w)), using complex scalars on the left
factor.
-/
@[simp]
theorem tensorProductRealAlgEquiv_tmul (z w : ℂ) :
    letI : Module ℝ ℂ := Complex.ofRealHom.toModule
    letI : Algebra ℝ ℂ := Complex.ofRealHom.toAlgebra
    tensorProductRealAlgEquiv (z ⊗ₜ[ℝ] w) = (z * w, z * conj w) := by
  let : Module ℝ ℂ := Complex.ofRealHom.toModule
  let : Algebra ℝ ℂ := Complex.ofRealHom.toAlgebra
  let : IsAlgClosure ℝ ℂ :=
    { isAlgClosed := Complex.isAlgClosed
      isAlgebraic := inferInstance }
  apply Prod.ext
  · change MilnorK.finiteGaloisTensorProductEquiv ℝ ℂ (z ⊗ₜ[ℝ] w)
      (realTensorAutomorphismIndex 0) = z * w
    rw [MilnorK.finiteGaloisTensorProductEquiv_tmul]
    rfl
  · change MilnorK.finiteGaloisTensorProductEquiv ℝ ℂ (z ⊗ₜ[ℝ] w)
      (realTensorAutomorphismIndex 1) = z * conj w
    rw [MilnorK.finiteGaloisTensorProductEquiv_tmul]
    rfl

/-- **Additive equivalence of the real complex self-tensor.**

The additive equivalence tensorProductRealAddEquiv:ℂ⊗_ℝℂ≃+ℂ×ℂ is Θ, with
Θ(z⊗w)=(zw,z*conj(w)).
-/
def tensorProductRealAddEquiv :
    letI : Module ℝ ℂ := Complex.ofRealHom.toModule
    letI : Algebra ℝ ℂ := Complex.ofRealHom.toAlgebra
    (ℂ ⊗[ℝ] ℂ) ≃+ ℂ × ℂ :=
  tensorProductRealAlgEquiv.toAddEquiv

/-- **Pure tensor coordinates of the additive self-tensor map.**

For z,w∈ℂ, tensorProductRealAddEquiv(z⊗_ℝw)=(zw,z*conj(w)).
-/
@[simp]
theorem tensorProductRealAddEquiv_tmul (z w : ℂ) :
    letI : Module ℝ ℂ := Complex.ofRealHom.toModule
    letI : Algebra ℝ ℂ := Complex.ofRealHom.toAlgebra
    tensorProductRealAddEquiv (z ⊗ₜ[ℝ] w) = (z * w, z * conj w) :=
  tensorProductRealAlgEquiv_tmul z w

/-- **Complex-linear equivalence of the real self-tensor.**

The ℂ-linear equivalence tensorProductRealEquiv:ℂ⊗_ℝℂ≃ₗ[ℂ]ℂ×ℂ is Θ(z⊗w)=(zw,z*conj(w)), with
the left-factor complex action.
-/
def tensorProductRealEquiv :
    letI : Module ℝ ℂ := Complex.ofRealHom.toModule
    letI : Algebra ℝ ℂ := Complex.ofRealHom.toAlgebra
    (ℂ ⊗[ℝ] ℂ) ≃ₗ[ℂ] ℂ × ℂ :=
  tensorProductRealAlgEquiv.toLinearEquiv

/-- **Pure tensor coordinates of the complex-linear map.**

For z,w∈ℂ, tensorProductRealEquiv(z⊗_ℝw)=(zw,z*conj(w)).
-/
@[simp]
theorem tensorProductRealEquiv_tmul (z w : ℂ) :
    letI : Module ℝ ℂ := Complex.ofRealHom.toModule
    letI : Algebra ℝ ℂ := Complex.ofRealHom.toAlgebra
    tensorProductRealEquiv (z ⊗ₜ[ℝ] w) = (z * w, z * conj w) :=
  tensorProductRealAlgEquiv_tmul z w

/-- **Inverse coordinates of the real complex self-tensor.**

For (p,q)∈ℂ×ℂ, tensorProductRealEquiv⁻¹(p,q)=((p+q)/2)⊗_ℝ1+((p-q)/(2i))⊗_ℝi.
-/
theorem tensorProductRealEquiv_symm_apply (p : ℂ × ℂ) :
    letI : Module ℝ ℂ := Complex.ofRealHom.toModule
    letI : Algebra ℝ ℂ := Complex.ofRealHom.toAlgebra
    tensorProductRealEquiv.symm p =
      ((p.1 + p.2) * (1 / 2 : ℂ)) ⊗ₜ[ℝ] (1 : ℂ) +
        ((p.1 - p.2) * (-Complex.I * (1 / 2 : ℂ))) ⊗ₜ[ℝ] Complex.I := by
  let : Module ℝ ℂ := Complex.ofRealHom.toModule
  let : Algebra ℝ ℂ := Complex.ofRealHom.toAlgebra
  apply tensorProductRealEquiv.injective
  rw [tensorProductRealEquiv.apply_symm_apply, map_add,
    tensorProductRealEquiv_tmul, tensorProductRealEquiv_tmul]
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, map_one, mul_one, conj_I]
  all_goals
    ring_nf
    simp [Complex.I_sq]
    ring

/-- **Twisted right complex action in tensor coordinates.**

For t∈ℂ⊗_ℝℂ and s∈ℂ, Θ(t*(1⊗s))=(Θ(t)_1*s,Θ(t)_2*conj(s)), where Θ=tensorProductRealEquiv.
-/
theorem tensorProductRealEquiv_right_action :
    letI : Module ℝ ℂ := Complex.ofRealHom.toModule
    letI : Algebra ℝ ℂ := Complex.ofRealHom.toAlgebra
    ∀ (t : ℂ ⊗[ℝ] ℂ) (s : ℂ),
      tensorProductRealEquiv (t * (1 ⊗ₜ[ℝ] s)) =
        ((tensorProductRealEquiv t).1 * s, (tensorProductRealEquiv t).2 * conj s) := by
  let : Module ℝ ℂ := Complex.ofRealHom.toModule
  let : Algebra ℝ ℂ := Complex.ofRealHom.toAlgebra
  intro t s
  change tensorProductRealAlgEquiv (t * (1 ⊗ₜ[ℝ] s)) =
    ((tensorProductRealAlgEquiv t).1 * s, (tensorProductRealAlgEquiv t).2 * conj s)
  rw [map_mul, tensorProductRealAlgEquiv_tmul]
  simp only [one_mul, Prod.mul_def]

end Complex

end
