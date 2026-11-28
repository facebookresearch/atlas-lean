/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# The Hochschild presentation of Kähler differentials

Let `k,A` be commutative rings with a `k`-algebra structure on `A`. The degree-two Hochschild
boundary is the `A`-linear map `b₂ : A ⊗[k] (A ⊗[k] A) → A ⊗[k] A` given by `a ⊗ (b ⊗ c) ↦ ab
⊗ c - a ⊗ bc + ca ⊗ b`.

Its cokernel is `Ω¹(A/k)`. The comparison sends `[a ⊗ b]` to `a db`, and the inverse sends
`db` to `[1 ⊗ b]`. The sequence `A ⊗[k] (A ⊗[k] A) → A ⊗[k] A → Ω¹(A/k) → 0` is exact, with
the last map `a ⊗ b ↦ a db`.

Reference: Loday, *Cyclic Homology*, Section 1.1.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace KaehlerDifferential.Hochschild

universe u v

variable (k : Type u) (A : Type v) [CommRing k] [CommRing A] [Algebra k A]

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. This is the `k`-linear
endomorphism of `A ⊗[k] A` defined by `a ⊗ b ↦ a ⊗ b - 1 ⊗ (a*b) + b ⊗ a`. -/
def relationMap : (A ⊗[k] A) →ₗ[k] A ⊗[k] A :=
  LinearMap.id -
    (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A).toLinearMap.comp
      (Algebra.TensorProduct.lmul' k : A ⊗[k] A →ₐ[k] A).toLinearMap +
    (TensorProduct.comm k A A).toLinearMap

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. For `a,b : A`,
`relationMap k A (a ⊗ b) = a ⊗ b - 1 ⊗ (a*b) + b ⊗ a` in `A ⊗[k] A`. -/
lemma relationMap_tmul (a b : A) :
    relationMap k A (a ⊗ₜ[k] b) =
      a ⊗ₜ[k] b - 1 ⊗ₜ[k] (a * b) + b ⊗ₜ[k] a := by
  change a ⊗ₜ[k] b -
      (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A)
        (Algebra.TensorProduct.lmul' k (a ⊗ₜ[k] b)) +
      (TensorProduct.comm k A A) (a ⊗ₜ[k] b) = _
  rw [Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.includeRight_apply,
    TensorProduct.comm_tmul]

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. The `A`-linear map
`boundaryTwo k A : A ⊗[k] (A ⊗[k] A) → A ⊗[k] A` is `a ⊗ (b ⊗ c) ↦ (a*b) ⊗ c - a ⊗ (b*c) +
(c*a) ⊗ b`. The `A`-action on both tensor modules is in the first factor. -/
def boundaryTwo : (A ⊗[k] (A ⊗[k] A)) →ₗ[A] A ⊗[k] A :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.lsmul A ((A ⊗[k] A) →ₗ[k] A ⊗[k] A)).flip (relationMap k A))

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. For `a,b,c : A`,
`boundaryTwo k A (a ⊗ (b ⊗ c)) = (a*b) ⊗ c - a ⊗ (b*c) + (c*a) ⊗ b`. The endpoint terms both
have positive sign. -/
lemma boundaryTwo_tmul (a b c : A) :
    boundaryTwo k A (a ⊗ₜ[k] (b ⊗ₜ[k] c)) =
      (a * b) ⊗ₜ[k] c - a ⊗ₜ[k] (b * c) + (c * a) ⊗ₜ[k] b := by
  rw [boundaryTwo, TensorProduct.AlgebraTensorModule.lift_tmul]
  change a • relationMap k A (b ⊗ₜ[k] c) = _
  rw [relationMap_tmul, smul_add, smul_sub]
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, mul_comm a c]

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. The `A`-module
`BoundaryQuotient k A` is `(A ⊗[k] A)/im b₂`, where `b₂(a ⊗ (b ⊗ c)) = ab ⊗ c - a ⊗ bc + ca ⊗
b`. Thus the denominator is the `A`-span of these degree-two boundary expressions. -/
abbrev BoundaryQuotient : Type v :=
  (A ⊗[k] A) ⧸ LinearMap.range (boundaryTwo k A)

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Let `Q` be `A ⊗[k] A`
modulo the `A`-span of the elements `ab ⊗ c - a ⊗ bc + ca ⊗ b` for `a,b,c : A`, and let `q : A
⊗[k] A → Q` be the quotient map. `quotientMap k A` is the `A`-linear projection `A ⊗[k] A →
Q`, sending each tensor to its boundary-quotient class. -/
def quotientMap : (A ⊗[k] A) →ₗ[A] BoundaryQuotient k A :=
  (LinearMap.range (boundaryTwo k A)).mkQ

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Write `T₁ = A ⊗[k] A`, `T₂
= A ⊗[k] (A ⊗[k] A)`, `b₂(a ⊗ (b ⊗ c)) = ab ⊗ c - a ⊗ bc + ca ⊗ b`, and `η(a ⊗ b) = a • D k A
b : Ω¹(A/k)`. For every `x : T₂`, the quotient projection `q : T₁ → T₁/im b₂` satisfies `q (b₂
x) = 0`. -/
lemma quotientMap_boundaryTwo (x : A ⊗[k] (A ⊗[k] A)) :
    quotientMap k A (boundaryTwo k A x) = 0 := by
  rw [quotientMap, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨x, rfl⟩

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Let `Q` be `A ⊗[k] A`
modulo the `A`-span of the elements `ab ⊗ c - a ⊗ bc + ca ⊗ b` for `a,b,c : A`, and let `q : A
⊗[k] A → Q` be the quotient map. For every `a : A`, `q(a ⊗ 1) = 0` in `Q`. -/
lemma quotientMap_tmul_one (a : A) : quotientMap k A (a ⊗ₜ[k] (1 : A)) = 0 := by
  have h := quotientMap_boundaryTwo k A (a ⊗ₜ[k] ((1 : A) ⊗ₜ[k] (1 : A)))
  simpa only [boundaryTwo_tmul, mul_one, one_mul, sub_self, zero_add] using h

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Let `Q` be `A ⊗[k] A`
modulo the `A`-span of the elements `ab ⊗ c - a ⊗ bc + ca ⊗ b` for `a,b,c : A`, and let `q : A
⊗[k] A → Q` be the quotient map. For `a,b : A`, `q(a ⊗ b) = a • q(1 ⊗ b)`, where `A` acts on
the first tensor factor and hence on the quotient. -/
lemma quotientMap_tmul_eq_smul (a b : A) :
    quotientMap k A (a ⊗ₜ[k] b) = a • quotientMap k A (1 ⊗ₜ[k] b) := by
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
    (quotientMap k A).map_smul a (1 ⊗ₜ[k] b)

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Let `Q` be `A ⊗[k] A`
modulo the `A`-span of the elements `ab ⊗ c - a ⊗ bc + ca ⊗ b` for `a,b,c : A`, and let `q : A
⊗[k] A → Q` be the quotient map. For `a,b : A`, `q(1 ⊗ (a*b)) = q(a ⊗ b) + q(b ⊗ a)`. -/
lemma quotientMap_leibniz (a b : A) :
    quotientMap k A (1 ⊗ₜ[k] (a * b)) =
      quotientMap k A (a ⊗ₜ[k] b) + quotientMap k A (b ⊗ₜ[k] a) := by
  have h := quotientMap_boundaryTwo k A ((1 : A) ⊗ₜ[k] (a ⊗ₜ[k] b))
  simp only [boundaryTwo_tmul, one_mul, mul_one, map_add, map_sub] at h
  have h' : (quotientMap k A (a ⊗ₜ[k] b) + quotientMap k A (b ⊗ₜ[k] a)) -
      quotientMap k A (1 ⊗ₜ[k] (a * b)) = 0 := by
    simpa only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  exact (sub_eq_zero.mp h').symm

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Let `Q` be `A ⊗[k] A`
modulo the `A`-span of the elements `ab ⊗ c - a ⊗ bc + ca ⊗ b` for `a,b,c : A`, and let `q : A
⊗[k] A → Q` be the quotient map. The function `d_Q(a) = q(1 ⊗ a)` is a `k`-derivation `A → Q`:
it is `k`-linear, sends `1` to zero, and satisfies `d_Q(ab) = a • d_Q(b) + b • d_Q(a)`. -/
def quotientDerivation : Derivation k A (BoundaryQuotient k A) where
  toLinearMap := ((quotientMap k A).restrictScalars k).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A).toLinearMap
  map_one_eq_zero' := by
    change quotientMap k A (1 ⊗ₜ[k] (1 : A)) = 0
    exact quotientMap_tmul_one k A 1
  leibniz' a b := by
    change quotientMap k A (1 ⊗ₜ[k] (a * b)) =
      a • quotientMap k A (1 ⊗ₜ[k] b) + b • quotientMap k A (1 ⊗ₜ[k] a)
    exact (quotientMap_leibniz k A a b).trans
      (congrArg₂ (fun x y => x + y)
        (quotientMap_tmul_eq_smul k A a b) (quotientMap_tmul_eq_smul k A b a))

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Let `Q` be `A ⊗[k] A`
modulo the `A`-span of the elements `ab ⊗ c - a ⊗ bc + ca ⊗ b` for `a,b,c : A`, and let `q : A
⊗[k] A → Q` be the quotient map. For every `a : A`, `quotientDerivation k A a = q(1 ⊗ a)`. -/
lemma quotientDerivation_apply (a : A) :
    quotientDerivation k A a = quotientMap k A (1 ⊗ₜ[k] a) := rfl

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Write `T₁ = A ⊗[k] A`, `T₂
= A ⊗[k] (A ⊗[k] A)`, `b₂(a ⊗ (b ⊗ c)) = ab ⊗ c - a ⊗ bc + ca ⊗ b`, and `η(a ⊗ b) = a • D k A
b : Ω¹(A/k)`. The composite `η ∘ b₂ : T₂ → Ω¹(A/k)` is zero, equivalently `(D k
A).tensorProductTo.comp (boundaryTwo k A) = 0`. -/
lemma boundaryTwo_comp_tensorProductTo :
    (KaehlerDifferential.D k A).tensorProductTo.comp (boundaryTwo k A) = 0 := by
  apply LinearMap.ext
  intro x
  change (KaehlerDifferential.D k A).tensorProductTo (boundaryTwo k A x) = 0
  refine TensorProduct.induction_on (motive := fun t : A ⊗[k] (A ⊗[k] A) =>
    (KaehlerDifferential.D k A).tensorProductTo (boundaryTwo k A t) = 0) x ?_ ?_ ?_
  · simp only [map_zero]
  · intro a y
    refine TensorProduct.induction_on (motive := fun t : A ⊗[k] A =>
      (KaehlerDifferential.D k A).tensorProductTo (boundaryTwo k A (a ⊗ₜ[k] t)) = 0)
      y ?_ ?_ ?_
    · simp only [TensorProduct.tmul_zero, map_zero]
    · intro b c
      rw [boundaryTwo_tmul]
      simp only [map_add, map_sub, Derivation.tensorProductTo_tmul,
        Derivation.leibniz, smul_add, smul_smul]
      rw [mul_comm c a]
      abel
    · intro y z hy hz
      simp only [TensorProduct.tmul_add, map_add, hy, hz, zero_add]
  · intro x y hx hy
    simp only [map_add, hx, hy, zero_add]

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Let `Q` be `A ⊗[k] A`
modulo the `A`-span of the elements `ab ⊗ c - a ⊗ bc + ca ⊗ b` for `a,b,c : A`, and let `q : A
⊗[k] A → Q` be the quotient map. The `A`-linear map `toKaehler k A : Q → Ω¹(A/k)` is defined
by `[a ⊗ b] ↦ a • D k A b`. The degree-two boundary expressions map to zero by the Leibniz
rule. -/
def toKaehler : BoundaryQuotient k A →ₗ[A] KaehlerDifferential k A :=
  (LinearMap.range (boundaryTwo k A)).liftQ (KaehlerDifferential.D k A).tensorProductTo (by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    change (KaehlerDifferential.D k A).tensorProductTo (boundaryTwo k A y) = 0
    exact congrArg (fun f : (A ⊗[k] (A ⊗[k] A)) →ₗ[A] KaehlerDifferential k A => f y)
      (boundaryTwo_comp_tensorProductTo k A))

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Let `Q` be `A ⊗[k] A`
modulo the `A`-span of the elements `ab ⊗ c - a ⊗ bc + ca ⊗ b` for `a,b,c : A`, and let `q : A
⊗[k] A → Q` be the quotient map. For `x : A ⊗[k] A`, `toKaehler k A (q x) = (D k
A).tensorProductTo x`. On pure tensors the latter map is `a ⊗ b ↦ a db`. -/
lemma toKaehler_quotientMap (x : A ⊗[k] A) :
    toKaehler k A (quotientMap k A x) = (KaehlerDifferential.D k A).tensorProductTo x := rfl

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Let `Q` be `A ⊗[k] A`
modulo the `A`-span of the elements `ab ⊗ c - a ⊗ bc + ca ⊗ b` for `a,b,c : A`, and let `q : A
⊗[k] A → Q` be the quotient map. For `a,b : A`, `toKaehler k A (q(a ⊗ b)) = a • D k A b` in
`Ω¹(A/k)`. -/
lemma toKaehler_tmul (a b : A) :
    toKaehler k A (quotientMap k A (a ⊗ₜ[k] b)) = a • KaehlerDifferential.D k A b :=
  (toKaehler_quotientMap k A (a ⊗ₜ[k] b)).trans
    (Derivation.tensorProductTo_tmul (KaehlerDifferential.D k A) a b)

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Let `Q` be `A ⊗[k] A`
modulo the `A`-span of the elements `ab ⊗ c - a ⊗ bc + ca ⊗ b` for `a,b,c : A`, and let `q : A
⊗[k] A → Q` be the quotient map. The universal property of `Ω¹(A/k)` gives the `A`-linear map
`fromKaehler k A : Ω¹(A/k) → Q` with `db ↦ q(1 ⊗ b)`. More generally, it sends `a db` to `q(a
⊗ b)`. -/
def fromKaehler : KaehlerDifferential k A →ₗ[A] BoundaryQuotient k A :=
  (quotientDerivation k A).liftKaehlerDifferential

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Let `Q` be `A ⊗[k] A`
modulo the `A`-span of the elements `ab ⊗ c - a ⊗ bc + ca ⊗ b` for `a,b,c : A`, and let `q : A
⊗[k] A → Q` be the quotient map. For every `a : A`, `fromKaehler k A (D k A a) = q(1 ⊗ a)`. -/
lemma fromKaehler_D (a : A) :
    fromKaehler k A (KaehlerDifferential.D k A a) = quotientMap k A (1 ⊗ₜ[k] a) :=
  (Derivation.liftKaehlerDifferential_comp_D (quotientDerivation k A) a).trans
    (quotientDerivation_apply k A a)

lemma fromKaehler_toKaehler (x : BoundaryQuotient k A) :
    fromKaehler k A (toKaehler k A x) = x := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (boundaryTwo k A)) x
  change fromKaehler k A (toKaehler k A (quotientMap k A y)) = quotientMap k A y
  refine TensorProduct.induction_on (motive := fun t : A ⊗[k] A =>
    fromKaehler k A (toKaehler k A (quotientMap k A t)) = quotientMap k A t)
    y ?_ ?_ ?_
  · simp only [map_zero]
  · intro a b
    exact (congrArg (fromKaehler k A) (toKaehler_tmul k A a b)).trans
      (((fromKaehler k A).map_smul a (KaehlerDifferential.D k A b)).trans
        ((congrArg (fun x => a • x) (fromKaehler_D k A b)).trans
          (quotientMap_tmul_eq_smul k A a b).symm))
  · intro y z hy hz
    simp only [map_add, hy, hz]

lemma toKaehler_fromKaehler (x : KaehlerDifferential k A) :
    toKaehler k A (fromKaehler k A x) = x := by
  have h : (toKaehler k A).comp (fromKaehler k A) = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    change toKaehler k A (fromKaehler k A (KaehlerDifferential.D k A a)) =
      KaehlerDifferential.D k A a
    rw [fromKaehler_D, toKaehler_tmul, one_smul]
  exact congrArg (fun f : KaehlerDifferential k A →ₗ[A] KaehlerDifferential k A => f x) h

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Let `Q` be `A ⊗[k] A`
modulo the `A`-span of the elements `ab ⊗ c - a ⊗ bc + ca ⊗ b` for `a,b,c : A`, and let `q : A
⊗[k] A → Q` be the quotient map. There is an `A`-linear equivalence `Q ≃ₗ[A] Ω¹(A/k)` whose
forward map is `[a ⊗ b] ↦ a db` and whose inverse sends `db` to `[1 ⊗ b]`. -/
def quotientLinearEquiv : BoundaryQuotient k A ≃ₗ[A] KaehlerDifferential k A :=
  { toKaehler k A with
    invFun := fromKaehler k A
    left_inv := fromKaehler_toKaehler k A
    right_inv := toKaehler_fromKaehler k A }

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Write `T₁ = A ⊗[k] A`, `T₂
= A ⊗[k] (A ⊗[k] A)`, `b₂(a ⊗ (b ⊗ c)) = ab ⊗ c - a ⊗ bc + ca ⊗ b`, and `η(a ⊗ b) = a • D k A
b : Ω¹(A/k)`. These maps satisfy `Function.Exact b₂ η`. For `x : T₁`, `η(x) = 0` if and only
if `x` belongs to the range of `b₂`. -/
lemma boundaryTwo_exact : Function.Exact (boundaryTwo k A)
    (KaehlerDifferential.D k A).tensorProductTo := by
  intro x
  constructor
  · intro hx
    have hq : quotientMap k A x = 0 := (quotientLinearEquiv k A).injective
      ((toKaehler_quotientMap k A x).trans (hx.trans (map_zero (toKaehler k A)).symm))
    have hm : x ∈ LinearMap.range (boundaryTwo k A) := by
      simpa only [quotientMap, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hq
    exact hm
  · rintro ⟨y, rfl⟩
    exact congrArg (fun f : (A ⊗[k] (A ⊗[k] A)) →ₗ[A] KaehlerDifferential k A => f y)
      (boundaryTwo_comp_tensorProductTo k A)

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Write `T₁ = A ⊗[k] A`, `T₂
= A ⊗[k] (A ⊗[k] A)`, `b₂(a ⊗ (b ⊗ c)) = ab ⊗ c - a ⊗ bc + ca ⊗ b`, and `η(a ⊗ b) = a • D k A
b : Ω¹(A/k)`. The maps form the short complex `T₂ —b₂→ T₁ —η→ Ω¹(A/k)` in `ModuleCat A`; its
zero-composite relation is `η ∘ b₂ = 0`. -/
def presentation : ShortComplex (ModuleCat.{v} A) :=
  ShortComplex.mk (ModuleCat.ofHom (boundaryTwo k A))
    (ModuleCat.ofHom (KaehlerDifferential.D k A).tensorProductTo) (by
      apply ModuleCat.hom_ext
      change (KaehlerDifferential.D k A).tensorProductTo.comp (boundaryTwo k A) = 0
      exact boundaryTwo_comp_tensorProductTo k A)

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Write `T₁ = A ⊗[k] A`, `T₂
= A ⊗[k] (A ⊗[k] A)`, `b₂(a ⊗ (b ⊗ c)) = ab ⊗ c - a ⊗ bc + ca ⊗ b`, and `η(a ⊗ b) = a • D k A
b : Ω¹(A/k)`. The map `η : T₁ → Ω¹(A/k)` is a cokernel of `b₂` in `ModuleCat A`. Every
`A`-linear map from `T₁` that kills `b₂` factors uniquely through `η`. -/
def presentationIsCokernel :
    IsColimit (CokernelCofork.ofπ (presentation k A).g (presentation k A).zero) :=
  ModuleCat.isColimitCokernelCofork
    (ModuleCat.ofHom (boundaryTwo k A))
    (ModuleCat.ofHom (KaehlerDifferential.D k A).tensorProductTo)
    (boundaryTwo_exact k A) (KaehlerDifferential.tensorProductTo_surjective k A)

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Write `T₁ = A ⊗[k] A`, `T₂
= A ⊗[k] (A ⊗[k] A)`, `b₂(a ⊗ (b ⊗ c)) = ab ⊗ c - a ⊗ bc + ca ⊗ b`, and `η(a ⊗ b) = a • D k A
b : Ω¹(A/k)`. The short complex `T₂ —b₂→ T₁ —η→ Ω¹(A/k)` is exact at `T₁`: its boundary image
`im b₂` equals `ker η`. -/
lemma presentation_exact : (presentation k A).Exact :=
  ShortComplex.exact_of_g_is_cokernel (presentation k A) (presentationIsCokernel k A)

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Write `T₁ = A ⊗[k] A`, `T₂
= A ⊗[k] (A ⊗[k] A)`, `b₂(a ⊗ (b ⊗ c)) = ab ⊗ c - a ⊗ bc + ca ⊗ b`, and `η(a ⊗ b) = a • D k A
b : Ω¹(A/k)`. This is the isomorphism `cokernel b₂ ≅ ModuleCat.of A (Ω¹(A/k))` obtained from
the quotient equivalence `(T₁/im b₂) ≃ₗ[A] Ω¹(A/k)`. It sends the cokernel class of `a ⊗ b` to
`a db`. -/
def presentationCokernelIso : cokernel (presentation k A).f ≅
    ModuleCat.of A (KaehlerDifferential k A) :=
  ModuleCat.cokernelIsoRangeQuotient (presentation k A).f ≪≫
    (quotientLinearEquiv k A).toModuleIso

/-- Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Write `T₁ = A ⊗[k] A`, `T₂
= A ⊗[k] (A ⊗[k] A)`, `b₂(a ⊗ (b ⊗ c)) = ab ⊗ c - a ⊗ bc + ca ⊗ b`, and `η(a ⊗ b) = a • D k A
b : Ω¹(A/k)`. Let `π : T₁ → cokernel b₂` be the cokernel projection and `E : cokernel b₂ ≅
Ω¹(A/k)` the presentation isomorphism. Then `E.hom ∘ π = η`, or categorically `cokernel.π
(presentation k A).f ≫ (presentationCokernelIso k A).hom = (presentation k A).g`. -/
@[reassoc]
lemma presentationCokernelIso_π :
    cokernel.π (presentation k A).f ≫ (presentationCokernelIso k A).hom =
      (presentation k A).g := by
  let e : cokernel (ModuleCat.ofHom (boundaryTwo k A)) ≅
      ModuleCat.of A (BoundaryQuotient k A) :=
    ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom (boundaryTwo k A))
  let φ : ModuleCat.of A (BoundaryQuotient k A) ⟶
      ModuleCat.of A (KaehlerDifferential k A) := ModuleCat.ofHom (toKaehler k A)
  change cokernel.π (ModuleCat.ofHom (boundaryTwo k A)) ≫ (e.hom ≫ φ) =
    ModuleCat.ofHom (KaehlerDifferential.D k A).tensorProductTo
  have hπ : cokernel.π (ModuleCat.ofHom (boundaryTwo k A)) ≫ e.hom =
      ModuleCat.ofHom (quotientMap k A) :=
    ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom _
  have hφ : ModuleCat.ofHom (quotientMap k A) ≫ φ =
      ModuleCat.ofHom (KaehlerDifferential.D k A).tensorProductTo := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact toKaehler_quotientMap k A x
  exact (Category.assoc (cokernel.π (ModuleCat.ofHom (boundaryTwo k A))) e.hom φ).symm.trans
    ((congrArg (fun f => f ≫ φ) hπ).trans hφ)

end KaehlerDifferential.Hochschild
