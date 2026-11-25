/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.ExteriorAlgebra.PrimitiveEquation
public import MathlibExt.LinearAlgebra.ExteriorPower.UnshuffleCoproduct
public import MathlibExt.LinearAlgebra.ExteriorPower.DeletionBasis
public import MathlibExt.LinearAlgebra.ExteriorAlgebra.CoalgebraGraded

/-!
# Homogeneous exterior primitives on free modules

The singleton coproduct component is the exterior deletion map under its
one-variable coordinate equivalence. A homogeneous primitive of degree at
least two has zero deletion; deletion injectivity on free modules then
forces it to vanish. The theorem includes positive characteristic and
degrees divisible by that characteristic, without division by the degree.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

local notation "E" => ExteriorAlgebra R M

/-- The actual degree-two reduced coproduct has the alternating middle term. -/
theorem primitiveEquation_ι_mul_ι (x y : M) :
    primitiveEquation R M (ι R x * ι R y) =
      ι R x ⊗ₜ[R] ι R y - ι R y ⊗ₜ[R] ι R x := by
  rw [primitiveEquation_apply, coproduct_ι_mul, coproduct_ι]
  simp only [map_add, signedInsertion_tmul, map_one, mul_one,
    CliffordAlgebra.involute_ι, TensorProduct.neg_tmul]
  abel

private theorem domCoprod_postcomp {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    {p q : ℕ} (a : M [⋀^Fin p]→ₗ[R] A) (b : M [⋀^Fin q]→ₗ[R] B)
    (f : A →ₗ[R] A') (g : B →ₗ[R] B') :
    (TensorProduct.map f g).compAlternatingMap (a.domCoprod b) =
      (f.compAlternatingMap a).domCoprod (g.compAlternatingMap b) := by
  ext w
  simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.domCoprod_apply,
    _root_.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  induction c using Quotient.inductionOn' with
  | _ σ =>
      change (TensorProduct.map f g)
        ((Equiv.Perm.sign σ : ℤ) • (a (fun i => w (σ (Sum.inl i))) ⊗ₜ[R]
          b (fun j => w (σ (Sum.inr j))))) =
        (Equiv.Perm.sign σ : ℤ) •
          (f (a (fun i => w (σ (Sum.inl i)))) ⊗ₜ[R]
            g (b (fun j => w (σ (Sum.inr j)))))
      rw [map_zsmul, TensorProduct.map_tmul]

private theorem ιMulti_transport (p q : ℕ) (h : p = q) (w : Fin q → M) :
    ιMulti R p (w ∘ finCongr h) = ιMulti R q w := by
  subst q
  rfl

-- These private adapters reindex the already constructed unshuffle. The stock deletion
-- operator is used only through its public generator formula, not by unfolding its
-- unexposed implementation or reconstructing the operator.
private def singletonBlock (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
  finSumFinEquiv.trans (finCongr (Nat.one_add n))

private def singletonRepresentative (n : ℕ) (r : Fin (n + 1)) :
    Equiv.Perm (Fin 1 ⊕ Fin n) :=
  (Equiv.permCongr (singletonBlock n)).symm r.cycleRange.symm

private theorem singletonRepresentative_head (n : ℕ) (r : Fin (n + 1)) :
    singletonBlock n (singletonRepresentative n r (Sum.inl 0)) = r := by
  calc
    singletonBlock n (singletonRepresentative n r (Sum.inl 0)) =
        ((singletonBlock n).permCongr (singletonRepresentative n r))
          (singletonBlock n (Sum.inl 0)) := by
            rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    _ = r.cycleRange.symm 0 := by
      unfold singletonRepresentative
      rw [(Equiv.permCongr (singletonBlock n)).apply_symm_apply]
      rfl
    _ = r := Fin.cycleRange_symm_zero r

private theorem singletonRepresentative_tail (n : ℕ) (r : Fin (n + 1)) (j : Fin n) :
    singletonBlock n (singletonRepresentative n r (Sum.inr j)) = r.succAbove j := by
  calc
    singletonBlock n (singletonRepresentative n r (Sum.inr j)) =
        ((singletonBlock n).permCongr (singletonRepresentative n r))
          (singletonBlock n (Sum.inr j)) := by
            rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    _ = r.cycleRange.symm j.succ := by
      unfold singletonRepresentative
      rw [(Equiv.permCongr (singletonBlock n)).apply_symm_apply]
      congr 1
      apply Fin.ext
      simp [singletonBlock]
    _ = r.succAbove j := Fin.cycleRange_symm_succ r j

private theorem singletonRepresentative_sign (n : ℕ) (r : Fin (n + 1)) :
    Equiv.Perm.sign (singletonRepresentative n r) = (-1) ^ r.val := by
  rw [← Equiv.Perm.sign_permCongr (singletonBlock n) (singletonRepresentative n r),
    singletonRepresentative, (Equiv.permCongr (singletonBlock n)).apply_symm_apply]
  change Equiv.Perm.sign r.cycleRange⁻¹ = (-1) ^ r.val
  rw [Equiv.Perm.sign_inv, Fin.sign_cycleRange]

private def singletonPositionEquiv (n : ℕ) :
    Equiv.Perm.ModSumCongr (Fin 1) (Fin n) ≃ Fin (n + 1) :=
  ((AlgebraicTopology.EilenbergZilber.Shuffle.cosetPositionsEquiv 1 n).trans
    Set.powersetCard.ofSingleton.symm).trans (finCongr (Nat.one_add n))

private theorem singletonPositionEquiv_symm (n : ℕ) (r : Fin (n + 1)) :
    (singletonPositionEquiv n).symm r = Quotient.mk'' (singletonRepresentative n r) := by
  classical
  apply (AlgebraicTopology.EilenbergZilber.Shuffle.cosetPositionsEquiv 1 n).injective
  change (AlgebraicTopology.EilenbergZilber.Shuffle.cosetPositionsEquiv 1 n)
      ((AlgebraicTopology.EilenbergZilber.Shuffle.cosetPositionsEquiv 1 n).symm
        (Set.powersetCard.ofSingleton ((finCongr (Nat.one_add n)).symm r))) =
    AlgebraicTopology.EilenbergZilber.Shuffle.cosetLeftPositions 1 n
      (Quotient.mk'' (singletonRepresentative n r))
  rw [Equiv.apply_symm_apply,
    AlgebraicTopology.EilenbergZilber.Shuffle.cosetLeftPositions_mk]
  apply SetLike.ext
  intro k
  rw [AlgebraicTopology.EilenbergZilber.Shuffle.mem_blockLeftPositions]
  change k ∈ ({(finCongr (Nat.one_add n)).symm r} : Finset (Fin (1 + n))) ↔ _
  rw [Finset.mem_singleton]
  have hh : finSumFinEquiv (singletonRepresentative n r (Sum.inl 0)) =
      (finCongr (Nat.one_add n)).symm r := by
    apply (finCongr (Nat.one_add n)).injective
    rw [Equiv.apply_symm_apply]
    exact singletonRepresentative_head n r
  constructor
  · intro hk
    exact ⟨0, hh.trans hk.symm⟩
  · rintro ⟨i, hi⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact hi.symm.trans hh

private theorem singletonSummand (n : ℕ) (r : Fin (n + 1)) (w : Fin (n + 1) → M) :
    (TensorProduct.comm R M (⋀[R]^n M))
      ((AlternatingMap.domCoprod.summand
        ((AlternatingMap.ofSubsingleton R M M (0 : Fin 1)) LinearMap.id)
        (exteriorPower.ιMulti R n) (Quotient.mk'' (singletonRepresentative n r)))
          (w ∘ singletonBlock n)) =
      (-1 : R) ^ r.val • ((exteriorPower.ιMulti R n (w ∘ r.succAbove)) ⊗ₜ[R] w r) := by
  rw [AlternatingMap.domCoprod.summand_mk'', _root_.smul_apply, singletonRepresentative_sign]
  rw [@Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R, LinearEquiv.map_smul]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  change (-1 : R) ^ r.val •
      (TensorProduct.comm R M (⋀[R]^n M))
        ((((AlternatingMap.ofSubsingleton R M M (0 : Fin 1)) LinearMap.id).toMultilinearMap.domCoprod
          (exteriorPower.ιMulti R n).toMultilinearMap).domDomCongr
            (singletonRepresentative n r) (w ∘ singletonBlock n)) = _
  rw [MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply, TensorProduct.comm_tmul]
  have ht : (fun j : Fin n => (w ∘ singletonBlock n)
      (singletonRepresentative n r (Sum.inr j))) = w ∘ r.succAbove := by
    funext j
    simp only [Function.comp_apply, singletonRepresentative_tail]
  have hh : ((AlternatingMap.ofSubsingleton R M M (0 : Fin 1)) LinearMap.id)
      (fun i => (w ∘ singletonBlock n) (singletonRepresentative n r (Sum.inl i))) = w r := by
    rw [AlternatingMap.ofSubsingleton_apply_apply]
    change w (singletonBlock n (singletonRepresentative n r (Sum.inl 0))) = w r
    rw [singletonRepresentative_head]
  rw [ht]
  exact congrArg (fun x => (-1 : R) ^ r.val •
    ((exteriorPower.ιMulti R n (w ∘ r.succAbove)) ⊗ₜ[R] x)) hh

private theorem singletonDomCoprod (n : ℕ) (w : Fin (n + 1) → M) :
    (TensorProduct.comm R M (⋀[R]^n M))
      ((((AlternatingMap.ofSubsingleton R M M (0 : Fin 1)) LinearMap.id).domCoprod
        (exteriorPower.ιMulti R n)) (w ∘ singletonBlock n)) =
      ∑ r : Fin (n + 1), (-1 : R) ^ r.val •
        ((exteriorPower.ιMulti R n (w ∘ r.succAbove)) ⊗ₜ[R] w r) := by
  rw [AlternatingMap.domCoprod_apply, _root_.sum_apply, map_sum]
  calc
    _ = ∑ r : Fin (n + 1), (TensorProduct.comm R M (⋀[R]^n M))
        ((AlternatingMap.domCoprod.summand
          ((AlternatingMap.ofSubsingleton R M M (0 : Fin 1)) LinearMap.id)
          (exteriorPower.ιMulti R n) ((singletonPositionEquiv n).symm r))
            (w ∘ singletonBlock n)) := ((singletonPositionEquiv n).symm.sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [singletonPositionEquiv_symm]
      exact singletonSummand R M n r w

/-- The stock deletion map is the actual singleton coproduct component, not an independent certificate. -/
theorem deletion_eq_coproductProjection (n : ℕ) :
    exteriorPower.deletion R M n =
      (TensorProduct.comm R M (⋀[R]^n M)).toLinearMap.comp
        ((TensorProduct.map (exteriorPower.oneEquiv R M).toLinearMap LinearMap.id).comp
          ((TensorProduct.map (exteriorPower.projection R M 1) (exteriorPower.projection R M n)).comp
            ((coproduct R M).comp (⋀[R]^(n + 1) M).subtype))) := by
  let one : M [⋀^Fin 1]→ₗ[R] M :=
    (AlternatingMap.ofSubsingleton R M M (0 : Fin 1)) LinearMap.id
  have hOne : (exteriorPower.oneEquiv R M).toLinearMap.compAlternatingMap
      (exteriorPower.ιMulti R 1) = one := by
    ext w
    change exteriorPower.oneEquiv R M (exteriorPower.ιMulti R 1 w) = w 0
    exact exteriorPower.oneEquiv_ιMulti (R := R) (M := M) w
  apply exteriorPower.linearMap_ext (R := R) (n := n + 1) (M := M) (N := (⋀[R]^n M) ⊗[R] M)
  apply AlternatingMap.ext
  intro w
  have hp := LinearMap.congr_fun (exteriorPower.projectedCoproduct_eq_unshuffle R M 1 n)
    (exteriorPower.ιMulti R (1 + n) (w ∘ finCongr (Nat.one_add n)))
  simp only [LinearMap.comp_apply, Submodule.subtype_apply,
    exteriorPower.ιMulti_apply_coe] at hp
  rw [ιMulti_transport R M (1 + n) (n + 1) (Nat.one_add n) w] at hp
  rw [exteriorPower.unshuffle, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti] at hp
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, exteriorPower.ιMulti_apply_coe]
  rw [exteriorPower.deletion_apply_ιMulti, ← singletonDomCoprod R M n w]
  change (TensorProduct.comm R M (⋀[R]^n M))
      ((one.domCoprod (exteriorPower.ιMulti R n))
        (w ∘ ((finSumFinEquiv : Fin 1 ⊕ Fin n ≃ Fin (1 + n)).trans (finCongr (Nat.one_add n))))) =
    (TensorProduct.comm R M (⋀[R]^n M))
      (TensorProduct.map (exteriorPower.oneEquiv R M).toLinearMap LinearMap.id
        (TensorProduct.map (exteriorPower.projection R M 1) (exteriorPower.projection R M n)
          (coproduct R M (ιMulti R (n + 1) w))))
  rw [hp]
  have hpost := domCoprod_postcomp R M (exteriorPower.ιMulti R 1)
    (exteriorPower.ιMulti R n) (exteriorPower.oneEquiv R M).toLinearMap LinearMap.id
  rw [hOne] at hpost
  have hId : (LinearMap.id : (⋀[R]^n M) →ₗ[R] (⋀[R]^n M)).compAlternatingMap
      (exteriorPower.ιMulti R n) = exteriorPower.ιMulti R n := by ext v; rfl
  rw [hId] at hpost
  exact congrArg (TensorProduct.comm R M (⋀[R]^n M))
    (DFunLike.congr_fun hpost
      (w ∘ ((finSumFinEquiv : Fin 1 ⊕ Fin n ≃ Fin (1 + n)).trans (finCongr (Nat.one_add n))))).symm

/-- Every homogeneous primitive in degree at least two has zero actual deletion. -/
theorem deletion_eq_zero_of_primitive (n : ℕ) (hn : n ≠ 0)
    (a : ⋀[R]^(n + 1) M)
    (ha : Coalgebra.IsSkewPrimitiveElem R (1 : E) (1 : E) (a : E)) :
    exteriorPower.deletion R M n a = 0 := by
  rw [deletion_eq_coproductProjection]
  change (TensorProduct.comm R M (⋀[R]^n M))
      (TensorProduct.map (exteriorPower.oneEquiv R M).toLinearMap LinearMap.id
        (TensorProduct.map (exteriorPower.projection R M 1) (exteriorPower.projection R M n)
          (Coalgebra.comul (a : E)))) = 0
  rw [ha.comul_eq_tmul_add_tmul, map_add, TensorProduct.map_tmul, TensorProduct.map_tmul]
  have h0 : (1 : E) = ιMulti R 0 Fin.elim0 := (ιMulti_zero_apply (R := R) (M := M) Fin.elim0).symm
  rw [h0, exteriorPower.projection_ιMulti_ne R M 1 0 (by decide),
    exteriorPower.projection_ιMulti_ne R M n 0 hn.symm,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, zero_add, map_zero, map_zero]

/-- A homogeneous degree-zero primitive is zero, without any freeness assumption. -/
theorem primitive_degree_zero (a : ⋀[R]^0 M)
    (ha : Coalgebra.IsSkewPrimitiveElem R (1 : E) (1 : E) (a : E)) : a = 0 := by
  apply (exteriorPower.zeroEquiv R M).injective
  have h := ha.counit_eq_zero
  change augmentation R M (a : E) = 0 at h
  rw [augmentation_degree_zero] at h
  simpa only [map_zero] using h

/-- On free modules, exterior primitives in any homogeneous degree other than one vanish,
including positive characteristic and degrees divisible by that characteristic. -/
theorem primitive_homogeneous_eq_zero [Module.Free R M] (n : ℕ) (hn : n ≠ 1)
    (a : ⋀[R]^n M)
    (ha : Coalgebra.IsSkewPrimitiveElem R (1 : E) (1 : E) (a : E)) : a = 0 := by
  cases n with
  | zero => exact primitive_degree_zero R M a ha
  | succ n =>
      cases n with
      | zero => exact False.elim (hn rfl)
      | succ n =>
          apply exteriorPower.deletion_injective R M (n + 1)
          rw [deletion_eq_zero_of_primitive R M (n + 1) (Nat.succ_ne_zero n) a ha, map_zero]

end ExteriorAlgebra
