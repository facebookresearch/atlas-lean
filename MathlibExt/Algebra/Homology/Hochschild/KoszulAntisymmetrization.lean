/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.AntisymmetricBarWords
public import MathlibExt.Algebra.Homology.Hochschild.AdjacentBarResolution
public import MathlibExt.Algebra.Homology.KoszulComplex
public import MathlibExt.LinearAlgebra.ExteriorPower.BaseChange

/-!
# Exterior Koszul terms and bar antisymmetrization

Let k be a commutative ring, A a commutative unital k-algebra,
V a k-module in an independent carrier universe, and f : V → A k-linear.
Set E = A ⊗[k] Aᵐᵒᵖ and
α(e ⊗ v) = e(f(v) ⊗ 1ᵐᵒᵖ − 1 ⊗ f(v)ᵐᵒᵖ).
This E-linear functional defines a Koszul differential on
∧_E^n(E ⊗[k] V).

Exterior scalar extension, full signed tensor antisymmetrization along f,
and the outer bar coordinates give E-linear maps
Φ_n : ∧_E^n(E ⊗[k] V) → P_n(A).
For an elementary generator wedge their value is
Φ_n(e • ((1 ⊗ v_0) ∧ ⋯ ∧ (1 ⊗ v_{n-1}))) =
e • ∑_{π ∈ S_n} sign(π)
(1 ⊗ f(v_{π(0)}) ⊗ ⋯ ⊗ f(v_{π(n-1)}) ⊗ 1).
The maps satisfy d_bar Φ_{n+1} = Φ_n d_α. The coefficients are integral,
and V is an arbitrary k-module.

Reference: J.-L. Loday, Cyclic Homology, §§1.1 and 3.2.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct
open MulOpposite

universe u v w

namespace ModuleCat.Algebra.Hochschild.AdjacentBar

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]

local notation "E" => EnvelopingAlgebra k A

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
The left outer inclusion is the k-linear map
A → E, a ↦ a ⊗ 1ᵐᵒᵖ. -/
def leftOuterLinear : A →ₗ[k] E :=
  (TensorProduct.mk k A Aᵐᵒᵖ).flip (op (1 : A))

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
The right outer inclusion is the k-linear map
A → E, a ↦ 1 ⊗ aᵐᵒᵖ. -/
def rightOuterLinear : A →ₗ[k] E where
  toFun a := (1 : A) ⊗ₜ[k] op a
  map_add' a b := by rw [MulOpposite.op_add, TensorProduct.tmul_add]
  map_smul' c a := by
    change (1 : A) ⊗ₜ[k] (c • op a) = c • ((1 : A) ⊗ₜ[k] op a)
    exact TensorProduct.tmul_smul _ _ _

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
Subtracting the right inclusion from the left gives the k-linear map
Δ : A → E, with Δ(a) = a ⊗ 1ᵐᵒᵖ − 1 ⊗ aᵐᵒᵖ. -/
def outerDifferenceLinear : A →ₗ[k] E := leftOuterLinear k A - rightOuterLinear k A

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
The k-linear outer-difference map evaluates at a ∈ A as
Δ(a) = a ⊗ 1ᵐᵒᵖ − 1 ⊗ aᵐᵒᵖ. -/
theorem outerDifferenceLinear_apply (a : A) :
    outerDifferenceLinear k A a = outerDifference k A a := rfl

variable (V : Type w) [AddCommGroup V] [Module k V] (f : V →ₗ[k] A)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
Let V be a k-module and f : V → A a k-linear map.
The generator-difference functional is the E-linear map
α : E ⊗[k] V → E with α(e ⊗ v) = e Δ(f(v)), where
Δ(a) = a ⊗ 1ᵐᵒᵖ − 1 ⊗ aᵐᵒᵖ. -/
def generatorDifferenceFunctional : E ⊗[k] V →ₗ[E] E :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.lsmul E (V →ₗ[k] E)).flip ((outerDifferenceLinear k A).comp f))

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
Let V be a k-module and f : V → A a k-linear map.
On a scalar-extended generator, the difference functional has value
α(e ⊗ v) = e(f(v) ⊗ 1ᵐᵒᵖ − 1 ⊗ f(v)ᵐᵒᵖ). -/
theorem generatorDifferenceFunctional_tmul (e : E) (v : V) :
    generatorDifferenceFunctional k A V f (e ⊗ₜ[k] v) = e * outerDifference k A (f v) := by
  rw [generatorDifferenceFunctional, TensorProduct.AlgebraTensorModule.lift_tmul]
  rfl

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
Let V be a k-module and f : V → A a k-linear map.
In degree n, exterior antisymmetrization followed by f on each factor
defines the k-linear map ∧_k^n V → A^{⊗n}. It uses the full
signed-permutation tensor sum. -/
def exteriorAntisymmetrizationAlong (n : ℕ) : (⋀[k]^n V) →ₗ[k] TensorPower k n A :=
  (PiTensorProduct.map (fun _ : Fin n => f)).comp (TensorPower.exteriorAntisymmetrization k V n)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
Let V be a k-module and f : V → A a k-linear map.
For a : Fin n → V, alternation along f sends
 a_0 ∧ ⋯ ∧ a_{n-1} to
∑_{π ∈ S_n} sign(π) tprod((f ∘ a) ∘ π). -/
theorem exteriorAntisymmetrizationAlong_ιMulti (n : ℕ) (a : Fin n → V) :
    exteriorAntisymmetrizationAlong k A V f n (exteriorPower.ιMulti k n a) =
      ∑ π : Equiv.Perm (Fin n), (π.sign : ℤ) • PiTensorProduct.tprod k ((f ∘ a) ∘ π) := by
  rw [exteriorAntisymmetrizationAlong, LinearMap.comp_apply,
    TensorPower.exteriorAntisymmetrization_ιMulti, map_sum]
  apply Finset.sum_congr rfl
  intro π _
  change PiTensorProduct.map (fun _ : Fin n => f)
    ((π.sign : ℤ) • PiTensorProduct.tprod k (a ∘ π)) = _
  rw [map_zsmul, PiTensorProduct.map_tprod]
  rfl

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
The inverse outer-coordinate isomorphism E ⊗[k] A^{⊗n} ≃ P_n
sends e ⊗ tprod(a) to e • u_n(a), where
u_n(a) = 1 ⊗ a_0 ⊗ ⋯ ⊗ a_{n-1} ⊗ 1. -/
theorem envelopingBarDegreeEquivBaseChange_symm_tprod
    (n : ℕ) (e : E) (a : Fin n → A) :
    (envelopingBarDegreeEquivBaseChange k A n).symm (e ⊗ₜ[k] PiTensorProduct.tprod k a) =
      e • unitOuterWord k A n a := by
  have hunit : (envelopingBarDegreeEquivBaseChange k A n).symm
      ((1 : E) ⊗ₜ[k] PiTensorProduct.tprod k a) = unitOuterWord k A n a := by
    apply (envelopingBarDegreeEquivBaseChange k A n).injective
    rw [LinearEquiv.apply_symm_apply, unitOuterWord, envelopingBarDegreeEquivBaseChange_tprod,
      Fin.snoc_last, Fin.init_snoc]
    rfl
  rw [← hunit, ← map_smul]
  congr 1
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
Let V be a k-module and f : V → A a k-linear map.
The E-linear comparison ∧_E^n(E ⊗[k] V) → P_n first uses
∧_E^n(E ⊗[k] V) ≃ E ⊗[k] ∧_k^n V, then alternates along f,
and finally uses the inverse outer bar coordinates. -/
def koszulAntisymmetrizationLevel (n : ℕ) :
    (⋀[E]^n (E ⊗[k] V)) →ₗ[E] envelopingBarDegree k A n :=
  (envelopingBarDegreeEquivBaseChange k A n).symm.toLinearMap.comp
    (((exteriorAntisymmetrizationAlong k A V f n).baseChange E).comp
      (exteriorPower.baseChangeEquiv k E V n).symm.toLinearMap)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
Let V be a k-module and f : V → A a k-linear map.
For e ∈ E and a : Fin n → V, the degree-n comparison satisfies
Φ_n(e • ((1 ⊗ a_0) ∧ ⋯ ∧ (1 ⊗ a_{n-1}))) =
e • Alt_n(f ∘ a), where Alt_n is the signed sum of the middle
word between two outer units. -/
theorem koszulAntisymmetrizationLevel_smul_ιMulti
    (n : ℕ) (e : E) (a : Fin n → V) :
    koszulAntisymmetrizationLevel k A V f n
      (e • exteriorPower.ιMulti E n (fun j => (1 : E) ⊗ₜ[k] a j)) =
      e • antisymmetricBarWord k A n (f ∘ a) := by
  let g := exteriorPower.baseChangeEquiv k E V n
  let b := (envelopingBarDegreeEquivBaseChange k A n).symm.toLinearMap
  let F := (exteriorAntisymmetrizationAlong k A V f n).baseChange E
  let w := e • exteriorPower.ιMulti E n (fun j => (1 : E) ⊗ₜ[k] a j)
  have hg : g.symm.toLinearMap w = e ⊗ₜ[k] exteriorPower.ιMulti k n a :=
    (congrFun (LinearEquiv.coe_toLinearMap g.symm) w).trans
      (exteriorPower.baseChangeEquiv_symm_apply_smul_ιMulti k E V n e a)
  have hstart : koszulAntisymmetrizationLevel k A V f n w =
      b (F (e ⊗ₜ[k] exteriorPower.ιMulti k n a)) :=
    ((LinearMap.comp_apply b (F.comp g.symm.toLinearMap) w).trans
      (congrArg b (LinearMap.comp_apply F g.symm.toLinearMap w))).trans
        (congrArg (fun z : E ⊗[k] (⋀[k]^n V) => b (F z)) hg)
  refine hstart.trans ?_
  rw [LinearMap.baseChange_tmul, exteriorAntisymmetrizationAlong_ιMulti]
  simp only [antisymmetricBarWord, TensorProduct.tmul_sum, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro π _
  have ht : e ⊗ₜ[k] ((π.sign : ℤ) • PiTensorProduct.tprod k ((f ∘ a) ∘ π)) =
      (π.sign : ℤ) • (e ⊗ₜ[k] PiTensorProduct.tprod k ((f ∘ a) ∘ π)) :=
    map_zsmul (TensorProduct.mk k E (TensorPower k n A) e) _ _
  rw [ht, map_zsmul]
  have hb : b (e ⊗ₜ[k] PiTensorProduct.tprod k ((f ∘ a) ∘ π)) =
      e • unitOuterWord k A n ((f ∘ a) ∘ π) :=
    (congrFun (LinearEquiv.coe_toLinearMap (envelopingBarDegreeEquivBaseChange k A n).symm)
      (e ⊗ₜ[k] PiTensorProduct.tprod k ((f ∘ a) ∘ π))).trans
        (envelopingBarDegreeEquivBaseChange_symm_tprod k A n e ((f ∘ a) ∘ π))
  exact (congrArg (fun z : envelopingBarDegree k A n => (π.sign : ℤ) • z) hb).trans
    (smul_comm (π.sign : ℤ) e (unitOuterWord k A n ((f ∘ a) ∘ π)))

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
Let V be a k-module and f : V → A a k-linear map.
The degree-n comparison sends
(1 ⊗ a_0) ∧ ⋯ ∧ (1 ⊗ a_{n-1}) to
Alt_n(f ∘ a) = ∑_{π ∈ S_n} sign(π)
(1 ⊗ f(a_{π(0)}) ⊗ ⋯ ⊗ f(a_{π(n-1)}) ⊗ 1). -/
theorem koszulAntisymmetrizationLevel_ιMulti (n : ℕ) (a : Fin n → V) :
    koszulAntisymmetrizationLevel k A V f n
      (exteriorPower.ιMulti E n (fun j => (1 : E) ⊗ₜ[k] a j)) =
      antisymmetricBarWord k A n (f ∘ a) := by
  simpa only [one_smul] using
    koszulAntisymmetrizationLevel_smul_ιMulti k A V f n (1 : E) a

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
Let V be a k-module and f : V → A a k-linear map.
Let α(e ⊗ v) = e Δ(f(v)) and let d_α be its exterior Koszul
differential. On every e • ((1 ⊗ a_0) ∧ ⋯ ∧ (1 ⊗ a_n)),
the exterior-to-bar comparison satisfies
 d_bar Φ_{n+1} = Φ_n d_α. The bar and Koszul boundaries use
the ordered deletion coefficients (−1)^i. -/
theorem koszulAntisymmetrizationLevel_boundary_word
    (n : ℕ) (e : E) (a : Fin (n + 1) → V) :
    letI := TensorPower.outerModule k A n
    (((envelopingBar k A).d (n + 1) n).hom
        (koszulAntisymmetrizationLevel k A V f (n + 1)
          (e • exteriorPower.ιMulti E (n + 1) (fun j => (1 : E) ⊗ₜ[k] a j))) :
      A ⊗[k] TensorPower k (n + 1) A) =
      (koszulAntisymmetrizationLevel k A V f n
        (KoszulComplex.differential E (E ⊗[k] V)
          (generatorDifferenceFunctional k A V f) n
            (e • exteriorPower.ιMulti E (n + 1) (fun j => (1 : E) ⊗ₜ[k] a j))) :
        A ⊗[k] TensorPower k (n + 1) A) := by
  letI := TensorPower.outerModule k A n
  letI := TensorPower.outerModule k A (n + 1)
  let D : (A ⊗[k] TensorPower k (n + 2) A) →ₗ[E]
      (A ⊗[k] TensorPower k (n + 1) A) := ((envelopingBar k A).d (n + 1) n).hom
  let K : (⋀[E]^n (E ⊗[k] V)) →ₗ[E] A ⊗[k] TensorPower k (n + 1) A :=
    koszulAntisymmetrizationLevel k A V f n
  let K' : (⋀[E]^(n + 1) (E ⊗[k] V)) →ₗ[E] A ⊗[k] TensorPower k (n + 2) A :=
    koszulAntisymmetrizationLevel k A V f (n + 1)
  change D (K' (e • exteriorPower.ιMulti E (n + 1) (fun j => (1 : E) ⊗ₜ[k] a j))) =
    K (KoszulComplex.differential E (E ⊗[k] V) (generatorDifferenceFunctional k A V f) n
      (e • exteriorPower.ιMulti E (n + 1) (fun j => (1 : E) ⊗ₜ[k] a j)))
  let U (j : Fin (n + 1)) : A ⊗[k] TensorPower k (n + 1) A :=
    (-1 : ℤ) ^ j.val • (outerDifference k A ((f ∘ a) j) •
      (antisymmetricBarWord k A n ((f ∘ a) ∘ j.succAbove) : A ⊗[k] TensorPower k (n + 1) A))
  have hbar : D (antisymmetricBarWord k A (n + 1) (f ∘ a)) =
      ∑ j : Fin (n + 1), U j :=
    antisymmetricBarWord_boundary k A n (f ∘ a)
  have hleft :=
    (congrArg D (koszulAntisymmetrizationLevel_smul_ιMulti k A V f (n + 1) e a)).trans
      ((D.map_smul e (antisymmetricBarWord k A (n + 1) (f ∘ a))).trans
        (congrArg (fun z : A ⊗[k] TensorPower k (n + 1) A => e • z) hbar))
  let b : Fin (n + 1) → E ⊗[k] V := fun j => (1 : E) ⊗ₜ[k] a j
  let d : (⋀[E]^(n + 1) (E ⊗[k] V)) →ₗ[E] (⋀[E]^n (E ⊗[k] V)) :=
    KoszulComplex.differential E (E ⊗[k] V) (generatorDifferenceFunctional k A V f) n
  let W (j : Fin (n + 1)) : A ⊗[k] TensorPower k (n + 1) A :=
    antisymmetricBarWord k A n ((f ∘ a) ∘ j.succAbove)
  let T (j : Fin (n + 1)) : A ⊗[k] TensorPower k (n + 1) A :=
    (-1 : E) ^ j.val • (outerDifference k A (f (a j)) • W j)
  have hright_unscaled : K (d (exteriorPower.ιMulti E (n + 1) b)) =
      ∑ j : Fin (n + 1), T j := by
    have hsplit := congrArg K
      (KoszulComplex.differential_apply_ιMulti E (E ⊗[k] V)
        (generatorDifferenceFunctional k A V f) n b)
    have hmap : K (∑ j : Fin (n + 1), (-1 : E) ^ j.val •
        (generatorDifferenceFunctional k A V f (b j) •
          exteriorPower.ιMulti E n (b ∘ j.succAbove))) =
        ∑ j : Fin (n + 1), K ((-1 : E) ^ j.val •
          (generatorDifferenceFunctional k A V f (b j) •
            exteriorPower.ιMulti E n (b ∘ j.succAbove))) := map_sum K _ _
    refine (hsplit.trans hmap).trans ?_
    apply Finset.sum_congr rfl
    intro j _
    have hcoef : generatorDifferenceFunctional k A V f (b j) =
        outerDifference k A (f (a j)) :=
      (generatorDifferenceFunctional_tmul k A V f (1 : E) (a j)).trans (one_mul _)
    have hword : K (exteriorPower.ιMulti E n (b ∘ j.succAbove)) = W j :=
      koszulAntisymmetrizationLevel_ιMulti k A V f n (a ∘ j.succAbove)
    exact ((K.map_smul ((-1 : E) ^ j.val)
      (generatorDifferenceFunctional k A V f (b j) •
        exteriorPower.ιMulti E n (b ∘ j.succAbove))).trans
          (congrArg (fun z : A ⊗[k] TensorPower k (n + 1) A => (-1 : E) ^ j.val • z)
            (K.map_smul (generatorDifferenceFunctional k A V f (b j))
              (exteriorPower.ιMulti E n (b ∘ j.succAbove))))).trans
        (congrArg₂ (fun r : E => fun z : A ⊗[k] TensorPower k (n + 1) A =>
          (-1 : E) ^ j.val • (r • z)) hcoef hword)
  have hright : K (d (e • exteriorPower.ιMulti E (n + 1) b)) =
      e • ∑ j : Fin (n + 1), T j :=
    ((congrArg K (d.map_smul e (exteriorPower.ιMulti E (n + 1) b))).trans
      (K.map_smul e (d (exteriorPower.ιMulti E (n + 1) b)))).trans
        (congrArg (fun z : A ⊗[k] TensorPower k (n + 1) A => e • z) hright_unscaled)
  have hsign : (∑ j : Fin (n + 1), U j) = ∑ j : Fin (n + 1), T j := by
    apply Finset.sum_congr rfl
    intro j _
    let C := TensorPower.outerCoordinate k A n
    let S := envelopingBarDegreeEquivBaseChange k A n
    have hraw (c : E) (x : A ⊗[k] TensorPower k (n + 1) A) :
        C (c • x) = c • C x :=
      (congrArg C (TensorPower.outerRepresentation_apply k A n c x)).trans
        (C.apply_symm_apply (c • C x))
    have hT : C (T j) = (-1 : E) ^ j.val •
        (outerDifference k A (f (a j)) • C (W j)) :=
      (hraw ((-1 : E) ^ j.val) (outerDifference k A (f (a j)) • W j)).trans
        (congrArg (fun z : E ⊗[k] TensorPower k n A => (-1 : E) ^ j.val • z)
          (hraw (outerDifference k A (f (a j))) (W j)))
    let y : envelopingBarDegree k A n :=
      outerDifference k A ((f ∘ a) j) •
        antisymmetricBarWord k A n ((f ∘ a) ∘ j.succAbove)
    have hy : S y = outerDifference k A (f (a j)) • C (W j) :=
      S.map_smul (outerDifference k A ((f ∘ a) j))
        (antisymmetricBarWord k A n ((f ∘ a) ∘ j.succAbove))
    have hU : C (U j) = (-1 : ℤ) ^ j.val •
        (outerDifference k A (f (a j)) • C (W j)) :=
      (map_zsmul S ((-1 : ℤ) ^ j.val) y).trans
        (congrArg (fun z : E ⊗[k] TensorPower k n A => (-1 : ℤ) ^ j.val • z) hy)
    have hcast : (-1 : E) ^ j.val •
        (outerDifference k A (f (a j)) • C (W j)) = (-1 : ℤ) ^ j.val •
          (outerDifference k A (f (a j)) • C (W j)) := by
      simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using
        Int.cast_smul_eq_zsmul (R := E) ((-1 : ℤ) ^ j.val)
          (outerDifference k A (f (a j)) • C (W j))
    exact C.injective (hU.trans (hT.trans hcast).symm)
  exact hleft.trans
    ((congrArg (fun z : A ⊗[k] TensorPower k (n + 1) A => e • z) hsign).trans hright.symm)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
Let V be a k-module and f : V → A a k-linear map.
For α(e ⊗ v) = e Δ(f(v)), the E-linear degree maps from the
exterior Koszul terms to the bar satisfy
 d_bar Φ_{n+1} = Φ_n d_α
on the whole module ∧_E^{n+1}(E ⊗[k] V). -/
theorem koszulAntisymmetrizationLevel_boundary (n : ℕ) :
    (((envelopingBar k A).d (n + 1) n).hom :
      (envelopingBarDegree k A (n + 1)).carrier →ₗ[E] (envelopingBarDegree k A n).carrier).comp
        (koszulAntisymmetrizationLevel k A V f (n + 1)) =
      (koszulAntisymmetrizationLevel k A V f n).comp
        (KoszulComplex.differential E (E ⊗[k] V)
          (generatorDifferenceFunctional k A V f) n) := by
  letI : Module k (envelopingBarDegree k A n) :=
    inferInstanceAs (Module k (A ⊗[k] TensorPower k (n + 1) A))
  letI : IsScalarTower k E (envelopingBarDegree k A n) :=
    TensorPower.outerScalarTower k A n
  let g := exteriorPower.baseChangeEquiv k E V (n + 1)
  have h :
      (((envelopingBar k A).d (n + 1) n).hom.comp
        (koszulAntisymmetrizationLevel k A V f (n + 1))).comp g.toLinearMap =
      ((koszulAntisymmetrizationLevel k A V f n).comp
        (KoszulComplex.differential E (E ⊗[k] V)
          (generatorDifferenceFunctional k A V f) n)).comp g.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    apply LinearMap.ext
    intro e
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    change ((envelopingBar k A).d (n + 1) n).hom
        (koszulAntisymmetrizationLevel k A V f (n + 1)
          (g (e ⊗ₜ[k] exteriorPower.ιMulti k (n + 1) a))) =
      koszulAntisymmetrizationLevel k A V f n
        (KoszulComplex.differential E (E ⊗[k] V)
          (generatorDifferenceFunctional k A V f) n
            (g (e ⊗ₜ[k] exteriorPower.ιMulti k (n + 1) a)))
    rw [exteriorPower.baseChangeEquiv_apply_tmul_ιMulti]
    exact koszulAntisymmetrizationLevel_boundary_word k A V f n e a
  exact (LinearMap.cancel_right (g := g.toLinearMap) g.surjective).1 h

end ModuleCat.Algebra.Hochschild.AdjacentBar
