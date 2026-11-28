/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.TensorPower.PermutationRepresentation
public import MathlibExt.LinearAlgebra.TensorPower.ShuffleCuts
public import MathlibExt.Combinatorics.Perm.EulerianShuffleMultiplication

/-!
# Permutation actions and signed shuffle products

Let k be a commutative ring and V a k-module. The place-permutation representation extends to a
k[Sₙ]-action on V⊗n. In the commutative ℚ-algebra setup, concatenation identifies a block
permutation with the tensor product of its two block actions. The Eulerian element Λₙ(a)
acts by its signed descent-polynomial coefficients, and at natural parameters these actions
preserve the signed shuffle product.

See J.-L. Loday, Cyclic Homology, 2nd ed., §4.5, for Eulerian operations and shuffle relations.
-/

@[expose] public section
noncomputable section

open scoped BigOperators TensorProduct

universe u v w

namespace TensorPower

variable {k : Type u} [CommRing k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {M : Type w} [AddCommGroup M] [Module k M]

/-- The group-algebra action on a tensor power.

For a commutative ring k and a k-module V, this k-algebra homomorphism k[Sₙ] → End_k(V⊗n) is
the linear extension of σ ↦ ρₙ(σ), with ρₙ(σ)tprod(a) = tprod(a ∘ σ⁻¹). -/
def permutationGroupAlgebraAction (n : ℕ) :
    MonoidAlgebra k (Equiv.Perm (Fin n)) →ₐ[k] Module.End k (TensorPower k n V) :=
  MonoidAlgebra.lift k (Module.End k (TensorPower k n V)) (Equiv.Perm (Fin n))
    (permutationRepresentation (k := k) (V := V) n)

variable [Algebra ℚ k]

/-- The rational permutation action on a tensor power.

For a commutative ℚ-algebra k and a k-module V, this ring homomorphism ℚ[Sₙ] → End_k(V⊗n)
extends rational coefficients along ℚ → k and applies the inverse-word permutation
representation. -/
def rationalPermutationAction (n : ℕ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin n)) →+* Module.End k (TensorPower k n V) :=
  (permutationGroupAlgebraAction (k := k) (V := V) n).toRingHom.comp
    (MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (algebraMap ℚ k))

/-- The action of a rational monomial on tensor factors.

For a commutative ℚ-algebra k, a k-module V, c ∈ ℚ and σ ∈ Sₙ, the action of c[σ] on V⊗n is
algebraMap(c) · ρₙ(σ). -/
theorem rationalPermutationAction_single (n : ℕ) (σ : Equiv.Perm (Fin n)) (c : ℚ) :
    rationalPermutationAction (k := k) (V := V) n (MonoidAlgebra.single σ c) =
      algebraMap ℚ k c • permutationRepresentation (k := k) (V := V) n σ := by
  rw [rationalPermutationAction, RingHom.comp_apply, MonoidAlgebra.mapRingHom_single]
  change MonoidAlgebra.lift k (Module.End k (TensorPower k n V)) (Equiv.Perm (Fin n))
      (permutationRepresentation (k := k) (V := V) n) (MonoidAlgebra.single σ (algebraMap ℚ k c)) =
        _
  exact MonoidAlgebra.lift_single (permutationRepresentation (k := k) (V := V) n) σ (algebraMap ℚ k
    c)

/-- The rational coefficient action is the tensor extension of the tail action.

For a commutative ℚ-algebra k, k-modules M,V and x ∈ ℚ[Sₙ], its action on M ⊗ V⊗n is id_M ⊗
ρₙ(x), where ρₙ(x) is the rational action on V⊗n. -/
theorem coefficientRationalPermutationAction_eq_map (n : ℕ)
    (x : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) :
    coefficientRationalPermutationAction (k := k) (M := M) (V := V) n x =
      TensorProduct.map LinearMap.id (rationalPermutationAction (k := k) (V := V) n x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, TensorProduct.map_zero_right]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, TensorProduct.map_add_right]
  | single σ c =>
    change coefficientPermutationGroupAlgebraAction (k := k) (M := M) (V := V) n
      ((MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (algebraMap ℚ k))
        (MonoidAlgebra.single σ c)) = _
    rw [MonoidAlgebra.mapRingHom_single, coefficientPermutationGroupAlgebraAction_single,
      rationalPermutationAction_single, TensorProduct.map_smul_right]
    rfl

/-- The signed descent-polynomial formula for Eulerian convolution.

For a commutative ℚ-algebra k, a k-module V and a ∈ ℚ, the action of Λₙ(a) on V⊗n is ∑σ
algebraMap(Bₙ,d(σ)(a) · sign(σ))ρₙ(σ). Here d(σ) is the descent number and Bₙ,d(X) =
(1/n!)∏ⱼ₌₀ⁿ⁻¹(X+j-d). -/
theorem rationalPermutationAction_eulerianLambda (n : ℕ) (a : ℚ) :
    rationalPermutationAction (k := k) (V := V) n (Equiv.Perm.eulerianLambda n a) =
      ∑ σ : Equiv.Perm (Fin n), algebraMap ℚ k
        ((Equiv.Perm.descentBinomialPolynomial n (Equiv.Perm.descentNumber σ)).eval a *
          ((σ.sign : ℤ) : ℚ)) • permutationRepresentation (k := k) (V := V) n σ := by
  classical
  rw [Equiv.Perm.eulerianLambda, map_sum]
  simp_rw [rationalPermutationAction_single]

/-- The signed shuffle element acts as the shuffle endomorphism.

For a commutative ℚ-algebra k, a k-module V and p,q ≥ 0, the action of the signed
(p,q)-shuffle element ∑σ sign(σ)[σ] on V⊗(p+q) equals signedShuffleEnd. -/
theorem rationalPermutationAction_signedShuffle (p q : ℕ) :
    rationalPermutationAction (k := k) (V := V) (p + q) (Equiv.Perm.signedShuffleElement p q) =
      signedShuffleEnd (k := k) (V := V) p q := by
  classical
  rw [Equiv.Perm.signedShuffleElement, map_sum]
  simp_rw [rationalPermutationAction_single]
  unfold signedShuffleEnd
  apply Finset.sum_congr rfl
  intro s _
  rw [map_intCast]
  change (((s.perm.sign : ℤ) : k) •
      (PiTensorProduct.reindex k (fun _ : Fin (p + q) => V) s.perm).toLinearMap) =
    (s.perm.sign : ℤ) • (PiTensorProduct.reindex k (fun _ : Fin (p + q) => V) s.perm).toLinearMap
  exact Int.cast_smul_eq_zsmul k (s.perm.sign : ℤ)
    (PiTensorProduct.reindex k (fun _ : Fin (p + q) => V) s.perm).toLinearMap

/-- Block permutations commute with tensor concatenation.

For a commutative ℚ-algebra k, a k-module V, α ∈ Sₚ and β ∈ Sᵩ, let μ : V⊗p ⊗ V⊗q ≃ V⊗(p+q)
be concatenation. Then ρₚ₊ᵩ(block(α,β)) ∘ μ = μ ∘ (ρₚ(α) ⊗ ρᵩ(β)). -/
theorem permutationRepresentation_block_mulEquiv (p q : ℕ)
    (α : Equiv.Perm (Fin p)) (β : Equiv.Perm (Fin q)) :
    (permutationRepresentation (k := k) (V := V) (p + q) (Equiv.Perm.blockPermutation p q α β)).comp
        (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)).toLinearMap =
      (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)).toLinearMap.comp
        (TensorProduct.map (permutationRepresentation (k := k) (V := V) p α)
          (permutationRepresentation (k := k) (V := V) q β)) := by
  apply TensorProduct.curry_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro a
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro b
  have hinv : (Equiv.Perm.blockPermutation p q α β).symm =
      Equiv.Perm.blockPermutation p q α.symm β.symm := by
    change (Equiv.Perm.blockPermutationHom p q (α, β))⁻¹ =
      Equiv.Perm.blockPermutationHom p q ((α, β)⁻¹)
    exact (map_inv _ _).symm
  change PiTensorProduct.reindex k (fun _ : Fin (p + q) => V) (Equiv.Perm.blockPermutation p q α β)
      (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)
        (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b)) =
    TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)
      (TensorProduct.map (permutationRepresentation (k := k) (V := V) p α)
        (permutationRepresentation (k := k) (V := V) q β)
          (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b))
  simp only [TensorProduct.map_tmul]
  change PiTensorProduct.reindex k (fun _ : Fin (p + q) => V) (Equiv.Perm.blockPermutation p q α β)
      (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)
        (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b)) =
    TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)
      (PiTensorProduct.reindex k (fun _ : Fin p => V) α (PiTensorProduct.tprod k a) ⊗ₜ[k]
        PiTensorProduct.reindex k (fun _ : Fin q => V) β (PiTensorProduct.tprod k b))
  have hconcat (a : Fin p → V) (b : Fin q → V) :
      TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)
          (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b) =
        PiTensorProduct.tprod k (Fin.append a b) :=
    (TensorPower.gMul_def (R := k) (M := V) (PiTensorProduct.tprod k a) (PiTensorProduct.tprod k
      b)).symm.trans
      (TensorPower.tprod_mul_tprod k a b)
  simp only [hconcat, PiTensorProduct.reindex_tprod]
  rw [hinv]
  apply congrArg (PiTensorProduct.tprod k)
  funext i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).surjective i
  cases j <;> simp

/-- The two-block Eulerian action in concatenation coordinates.

For a commutative ℚ-algebra k, a k-module V and a ∈ ℚ, the action of
splitEulerianLambda(p,q,a) on V⊗(p+q), conjugated by concatenation, is Aₚ(a) ⊗ Aᵩ(a), where
Aⱼ(a) is the action of Λⱼ(a). -/
theorem rationalPermutationAction_splitEulerianLambda (p q : ℕ) (a : ℚ) :
    (rationalPermutationAction (k := k) (V := V) (p + q) (Equiv.Perm.splitEulerianLambda p q
      a)).comp
        (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)).toLinearMap =
      (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)).toLinearMap.comp
        (TensorProduct.map
          (rationalPermutationAction (k := k) (V := V) p (Equiv.Perm.eulerianLambda p a))
          (rationalPermutationAction (k := k) (V := V) q (Equiv.Perm.eulerianLambda q a))) := by
  classical
  apply TensorProduct.curry_injective
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change rationalPermutationAction (k := k) (V := V) (p + q) (Equiv.Perm.splitEulerianLambda p q a)
      (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q) (x ⊗ₜ[k] y)) =
    TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)
      (TensorProduct.map
        (rationalPermutationAction (k := k) (V := V) p (Equiv.Perm.eulerianLambda p a))
        (rationalPermutationAction (k := k) (V := V) q (Equiv.Perm.eulerianLambda q a)) (x ⊗ₜ[k] y))
  simp only [TensorProduct.map_tmul,
    Equiv.Perm.splitEulerianLambda_eq_sum, map_sum, LinearMap.sum_apply,
    rationalPermutationAction_single, LinearMap.smul_apply,
    rationalPermutationAction_eulerianLambda, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_sum, map_smul, smul_smul, map_mul]
  simp only [Finset.smul_sum, ← TensorProduct.smul_tmul', map_smul, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro α _
  let cα : k := algebraMap ℚ k
    ((Equiv.Perm.descentBinomialPolynomial p (Equiv.Perm.descentNumber α)).eval a) *
      algebraMap ℚ k ((α.sign : ℤ) : ℚ)
  let cβ : k := algebraMap ℚ k
    ((Equiv.Perm.descentBinomialPolynomial q (Equiv.Perm.descentNumber β)).eval a) *
      algebraMap ℚ k ((β.sign : ℤ) : ℚ)
  let u := (permutationRepresentation (k := k) (V := V) (p + q)
    (Equiv.Perm.blockPermutation p q α β))
      (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q) (x ⊗ₜ[k] y))
  let v := TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)
    ((permutationRepresentation (k := k) (V := V) p α) x ⊗ₜ[k]
      (permutationRepresentation (k := k) (V := V) q β) y)
  change (cα * cβ) • u = (cβ * cα) • v
  have hblock : u = v := by
    have h := DFunLike.congr_fun (permutationRepresentation_block_mulEquiv (k := k) (V := V) p q α
      β)
      (x ⊗ₜ[k] y)
    change (permutationRepresentation (k := k) (V := V) (p + q) (Equiv.Perm.blockPermutation p q α
      β))
        (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q) (x ⊗ₜ[k] y)) =
      TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)
        (TensorProduct.map (permutationRepresentation (k := k) (V := V) p α)
          (permutationRepresentation (k := k) (V := V) q β) (x ⊗ₜ[k] y)) at h
    exact h.trans (congrArg (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q))
      (TensorProduct.map_tmul _ _ x y))
  exact (congrArg (fun v => (cα * cβ) • v) hblock).trans
    (congrArg (fun c : k => c • v) (mul_comm cα cβ))

/-- Shuffle multiplicativity at natural Eulerian parameters.

For a commutative ℚ-algebra k, a k-module V and p,q,m ≥ 0, the Eulerian actions satisfy
Aₚ₊ᵩ(m) ∘ shₚ,ᵩ = shₚ,ᵩ ∘ (Aₚ(m) ⊗ Aᵩ(m)). Here shₚ,ᵩ is the tensor shuffle product with
permutation signs. -/
theorem rationalEulerianLambda_signedShuffleProduct (p q m : ℕ) :
    (rationalPermutationAction (k := k) (V := V) (p + q) (Equiv.Perm.eulerianLambda (p + q) (m :
      ℚ))).comp
        (signedShuffleProduct (k := k) (V := V) p q) =
      (signedShuffleProduct (k := k) (V := V) p q).comp (TensorProduct.map
        (rationalPermutationAction (k := k) (V := V) p (Equiv.Perm.eulerianLambda p (m : ℚ)))
        (rationalPermutationAction (k := k) (V := V) q (Equiv.Perm.eulerianLambda q (m : ℚ)))) := by
  have h := congrArg (rationalPermutationAction (k := k) (V := V) (p + q))
    (Equiv.Perm.eulerianLambda_mul_signedShuffle p q m)
  rw [map_mul, map_mul, rationalPermutationAction_signedShuffle] at h
  change (rationalPermutationAction (k := k) (V := V) (p + q)
      (Equiv.Perm.eulerianLambda (p + q) (m : ℚ))).comp (signedShuffleEnd (k := k) (V := V) p q) =
    (signedShuffleEnd (k := k) (V := V) p q).comp
      (rationalPermutationAction (k := k) (V := V) (p + q) (Equiv.Perm.splitEulerianLambda p q (m :
        ℚ))) at h
  have hcomp := congrArg (fun f => f.comp
    (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)).toLinearMap) h
  simpa only [signedShuffleProduct, LinearMap.comp_assoc,
    rationalPermutationAction_splitEulerianLambda] using hcomp

end TensorPower
