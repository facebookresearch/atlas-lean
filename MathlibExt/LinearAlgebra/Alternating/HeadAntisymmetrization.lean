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
# Full alternatization from head uncurrying

Let k be a commutative ring and M,N be k-modules. For a head-linear, n-tail-multilinear map f,
alternatize the tail by its full signed permutation sum. Alternating head uncurrying then yields
the full alternatization in n+1 arguments: the term with head aᵢ has coefficient (-1)^i and the
remaining arguments are taken in their inherited order.

Applying this identity twice gives the full n+2 argument alternatization of a two-head-linear
map. In the second deletion, its position is counted after the first argument is removed. These
formulas use integer signs and require no factorial inverses or characteristic restriction.
-/

@[expose] public section

noncomputable section

open Equiv

namespace MultilinearMap

universe u v w

variable {k : Type u} [CommRing k] {M : Type v} [AddCommGroup M] [Module k M]
  {N : Type w} [AddCommGroup N] [Module k N]

/-- Let k be a commutative ring and M,N be k-modules with additive inverses, in arbitrary module
universes. For f : M →ₗ[k] MultilinearMap(Fin n,M,N), alternatizeTail f is the head-linear map x
↦ Altₙ(f(x)). On a tail a it has value ∑σ sign(σ)·f(x)(a∘σ), summed over permutations of Fin n. -/
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

/-- Let k be a commutative ring and M,N be k-modules with additive inverses, in arbitrary module
universes. For each n : ℕ, f ↦ alternatizeTail f is a k-linear map from head-linear
n-tail-multilinear maps to head-linear n-tail-alternating maps. -/
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

/-- Let k be a commutative ring and M,N be k-modules with additive inverses, in arbitrary module
universes. For a head-linear n-tail-multilinear map f, Altₙ₊₁(uncurryLeft f) equals alternating
head uncurrying of alternatizeTail f. At a : Fin(n+1) → M, the value is
∑ᵢ(-1)^i·Altₙ(f(aᵢ))(removeᵢ(a)), with the inherited order on each deleted tail. -/
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

/-- Let k be a commutative ring and M,N be k-modules with additive inverses, in arbitrary module
universes. For f linear in two head inputs and multilinear in n tail inputs, fully alternatizing
the doubly uncurried map equals alternating head uncurrying twice after tail alternatization.
The first head deletion has sign (-1)^i; the second has sign (-1)^j, where j is counted in the
list after the first deletion. -/
theorem alternatization_uncurryLeft_twice {n : ℕ}
    (f : M →ₗ[k] M →ₗ[k] MultilinearMap (RingHom.id k) (fun _ : Fin n => M) N) :
    (LinearMap.uncurryLeft
      (((multilinearCurryLeftEquiv (RingHom.id k)
        (fun _ : Fin (n + 1) => M) N).symm.toLinearMap).comp
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
