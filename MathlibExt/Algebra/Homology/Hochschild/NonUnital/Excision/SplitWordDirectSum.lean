/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.SplitWords
public import Mathlib.Algebra.DirectSum.Module

/-!
# Direct sums of split-word coordinates

For a ground-linear split quotient A → A/I, the word colours form a finite type. Composing the
finite direct-sum/product equivalence with the split-word coordinate equivalence identifies ⨁
c, W_c with A^⊗N.

Each summand inclusion maps by the tensor of ideal inclusions and quotient sections, and the
inverse coordinate is the tensor of ideal projections and quotient maps. The same construction
with V ⊗ W_c gives a direct-sum equivalence to V ⊗ A^⊗N for any ground module V.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct DirectSum NonUnitalSubalgebra.Quotient

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. The finite
direct-sum/product equivalence gives splitWordDirectSumEquiv : (⨁ c : Fin N → Bool, W_c) ≃ₗ[k]
A^⊗N. Its forward map is the sum of J_c and its inverse has coordinate P_c. -/
def splitWordDirectSumEquiv (splitting : I.KSplit) (N : ℕ) :
    (⨁ colour : Fin N → Bool, splitWordTensor k A I colour) ≃ₗ[k] TensorPower k N A :=
  (DirectSum.linearEquivFunOnFintype k (Fin N → Bool)
    (fun colour => splitWordTensor k A I colour)).trans
      (splitWordCoordinatesEquiv k A I splitting N)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. For a colour c and x :
W_c, splitWordDirectSumEquiv sends DirectSum.lof c x to J_c(x). -/
theorem splitWordDirectSumEquiv_lof (splitting : I.KSplit) (N : ℕ)
    (colour : Fin N → Bool) (x : splitWordTensor k A I colour) :
    splitWordDirectSumEquiv k A I splitting N
        (DirectSum.lof k (Fin N → Bool)
          (fun c => splitWordTensor k A I c) colour x) =
      splitWordToAmbient k A I splitting colour x := by
  classical
  rw [splitWordDirectSumEquiv, LinearEquiv.trans_apply,
    DirectSum.linearEquivFunOnFintype_lof, splitWordCoordinatesEquiv_apply]
  simp_rw [LinearMap.apply_single]
  simp

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. For x : A^⊗N and a
colour c, (splitWordDirectSumEquiv.symm x) c = P_c(x). -/
theorem splitWordDirectSumEquiv_symm_apply (splitting : I.KSplit) (N : ℕ)
    (x : TensorPower k N A) (colour : Fin N → Bool) :
    (splitWordDirectSumEquiv k A I splitting N).symm x colour =
      splitAmbientToWord k A I splitting colour x := by
  change ((DirectSum.linearEquivFunOnFintype k (Fin N → Bool)
      (fun c => splitWordTensor k A I c)).symm
        ((splitWordCoordinatesEquiv k A I splitting N).symm x)) colour = _
  exact congrArg (fun f => f colour)
    ((DirectSum.linearEquivFunOnFintype k (Fin N → Bool)
      (fun c => splitWordTensor k A I c)).apply_symm_apply
        ((splitWordCoordinatesEquiv k A I splitting N).symm x))

variable (V : Type w) [AddCommGroup V] [Module k V]

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be any k-module,
with J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. coefficientSplitWordDirectSumEquiv : (⨁ c, V
⊗[k] W_c) ≃ₗ[k] V ⊗[k] A^⊗N sums J_c^V and has inverse coordinates P_c^V. -/
def coefficientSplitWordDirectSumEquiv (splitting : I.KSplit) (N : ℕ) :
    (⨁ colour : Fin N → Bool, V ⊗[k] splitWordTensor k A I colour) ≃ₗ[k]
      V ⊗[k] TensorPower k N A :=
  (DirectSum.linearEquivFunOnFintype k (Fin N → Bool)
    (fun colour => V ⊗[k] splitWordTensor k A I colour)).trans
      (coefficientSplitWordCoordinatesEquiv k A I V splitting N)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be any k-module,
with J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. For x : V ⊗ W_c,
coefficientSplitWordDirectSumEquiv sends the c-th direct-sum inclusion of x to J_c^V(x). -/
theorem coefficientSplitWordDirectSumEquiv_lof (splitting : I.KSplit) (N : ℕ)
    (colour : Fin N → Bool) (x : V ⊗[k] splitWordTensor k A I colour) :
    coefficientSplitWordDirectSumEquiv k A I V splitting N
        (DirectSum.lof k (Fin N → Bool)
          (fun c => V ⊗[k] splitWordTensor k A I c) colour x) =
      coefficientSplitWordToAmbient k A I V splitting colour x := by
  classical
  rw [coefficientSplitWordDirectSumEquiv, LinearEquiv.trans_apply,
    DirectSum.linearEquivFunOnFintype_lof, coefficientSplitWordCoordinatesEquiv_apply]
  simp_rw [LinearMap.apply_single]
  simp

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be any k-module,
with J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. For x : V ⊗ A^⊗N and a colour c, the c-th
coordinate of coefficientSplitWordDirectSumEquiv.symm x is P_c^V(x). -/
theorem coefficientSplitWordDirectSumEquiv_symm_apply (splitting : I.KSplit) (N : ℕ)
    (x : V ⊗[k] TensorPower k N A) (colour : Fin N → Bool) :
    (coefficientSplitWordDirectSumEquiv k A I V splitting N).symm x colour =
      coefficientSplitAmbientToWord k A I V splitting colour x := by
  change ((DirectSum.linearEquivFunOnFintype k (Fin N → Bool)
      (fun c => V ⊗[k] splitWordTensor k A I c)).symm
        ((coefficientSplitWordCoordinatesEquiv k A I V splitting N).symm x)) colour = _
  exact congrArg (fun f => f colour)
    ((DirectSum.linearEquivFunOnFintype k (Fin N → Bool)
      (fun c => V ⊗[k] splitWordTensor k A I c)).apply_symm_apply
        ((coefficientSplitWordCoordinatesEquiv k A I V splitting N).symm x))

end ModuleCat.Algebra.Hochschild.NonUnital
