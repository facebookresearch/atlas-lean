/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Full permutation sums from native head uncurrying

Applying native alternating uncurrying to a head-linear, tail-multilinear
map gives its full alternatization after the tail is alternatized. The
ordered first-coordinate decomposition proves the exact formula without
integer division. Repeating it supplies the two-head product formula used
by the cyclic exterior boundary.
-/

@[expose] public section

noncomputable section

open Equiv

namespace MultilinearMap

universe u v w

variable {k : Type u} [CommRing k] {M : Type v} [AddCommGroup M] [Module k M]
  {N : Type w} [AddCommGroup N] [Module k N]

/-- Tail alternatization is linear in the original singled-out head input. -/
def alternatizeTail {n : ℕ}
    (f : M →ₗ[k] MultilinearMap (RingHom.id k) (fun _ : Fin n => M) N) :
    M →ₗ[k] M [⋀^Fin n]→ₗ[k] N where
  toFun x := (f x).alternatization
  map_add' x y := by rw [f.map_add, map_add]
  map_smul' c x := by
    apply AlternatingMap.ext
    intro a
    rw [f.map_smul]
    simp only [MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
      smul_apply, Finset.smul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro σ _
    exact smul_comm _ c _

/-- Tail alternatization as a linear map on the original head-linear maps. -/
def alternatizeTailLinearMap (n : ℕ) :
    (M →ₗ[k] MultilinearMap (RingHom.id k) (fun _ : Fin n => M) N) →ₗ[k]
      (M →ₗ[k] M [⋀^Fin n]→ₗ[k] N) where
  toFun := alternatizeTail
  map_add' f g := by ext x a; simp [alternatizeTail, map_add]
  map_smul' c f := by
    ext x a
    change ((c • f x).alternatization a) = c • ((f x).alternatization a)
    simp only [MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
      smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    exact smul_comm _ c _

/-- The original full permutation sum is the native alternating head-uncurry of its tail sum. -/
theorem alternatization_uncurryLeft {n : ℕ}
    (f : M →ₗ[k] MultilinearMap (RingHom.id k) (fun _ : Fin n => M) N) :
    f.uncurryLeft.alternatization = AlternatingMap.alternatizeUncurryFin (alternatizeTail f) := by
  apply AlternatingMap.ext
  intro a
  rw [MultilinearMap.alternatization_apply, AlternatingMap.alternatizeUncurryFin_apply]
  cases n with
  | zero =>
      change (∑ τ : Equiv.Perm (Fin 1), τ.sign •
          f (a (τ 0)) (Fin.tail (a ∘ τ))) =
        ∑ i : Fin 1, (-1 : ℤ) ^ i.val •
          (f (a i)).alternatization (i.removeNth a)
      simp [MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply]
  | succ n =>
    have h :
        (∑ τ : Equiv.Perm (Fin (n + 2)), τ.sign •
          f.uncurryLeft.domDomCongr τ a) =
        ∑ p : Fin (n + 2) × Equiv.Perm (Fin (n + 1)),
          (-1 : ℤ) ^ p.1.val • p.2.sign • f (a p.1) (p.1.removeNth a ∘ p.2) := by
      apply Fintype.sum_equiv (Equiv.Perm.decomposeFin' (n := n))
      intro τ
      obtain ⟨⟨i, σ⟩, rfl⟩ := (Equiv.Perm.decomposeFin' (n := n)).symm.surjective τ
      have he : Equiv.Perm.decomposeFin' (Equiv.Perm.decomposeFin'Symm i σ) = (i, σ) :=
        (Equiv.Perm.decomposeFin' (n := n)).apply_symm_apply (i, σ)
      simp only [Equiv.Perm.decomposeFin'_symm] at *
      rw [he]
      simp only [MultilinearMap.domDomCongr_apply,
        LinearMap.uncurryLeft_apply, Equiv.Perm.decomposeFin'Symm_zero,
        Equiv.Perm.sign_decomposeFin'Symm, mul_smul, Units.smul_def,
        Units.val_pow_eq_pow_val, Units.coe_neg_one]
      congr 2
    rw [h, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    change (∑ σ : Equiv.Perm (Fin (n + 1)), (-1 : ℤ) ^ i.val • σ.sign •
        f (a i) (i.removeNth a ∘ σ)) =
      (-1 : ℤ) ^ i.val • (f (a i)).alternatization (i.removeNth a)
    rw [← Finset.smul_sum, MultilinearMap.alternatization_apply]
    rfl

/-- Alternating two original head inputs is the full native permutation sum with an alternating tail. -/
theorem alternatization_uncurryLeft_twice {n : ℕ}
    (f : M →ₗ[k] M →ₗ[k] MultilinearMap (RingHom.id k) (fun _ : Fin n => M) N) :
    (LinearMap.uncurryLeft
      (((multilinearCurryLeftEquiv (RingHom.id k) (fun _ : Fin (n + 1) => M) N).symm.toLinearMap).comp
        f)).alternatization =
      AlternatingMap.alternatizeUncurryFin
        (AlternatingMap.alternatizeUncurryFinLM.comp
          ((alternatizeTailLinearMap n).comp f)) := by
  rw [alternatization_uncurryLeft]
  congr 1
  apply LinearMap.ext
  intro x
  apply AlternatingMap.ext
  intro a
  change (LinearMap.uncurryLeft (f x)).alternatization a =
    AlternatingMap.alternatizeUncurryFin (alternatizeTail (f x)) a
  exact congrArg (fun g => g a) (alternatization_uncurryLeft (f x))

end MultilinearMap

end
