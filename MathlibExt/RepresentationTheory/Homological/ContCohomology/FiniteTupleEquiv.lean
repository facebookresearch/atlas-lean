/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import Mathlib.Topology.CompactOpen
public import MathlibExt.CategoryTheory.Monad.TopologicalClassifyingBar
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.FiniteTupleEvaluation

/-! # Complete continuous finite-tuple comparison
Canonical compact-open linear equivalence, action and deletion laws in all degrees. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u v w
namespace ContinuousCohomology
variable {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Canonical compact-open homeomorphism in every finite-tuple degree. -/
def resolutionFinHomeomorph (X : TopRep.{max v w, u, v} k G) :
    (n : ℕ) → TopRep.resolutionX X n ≃ₜ C(Fin n → G, X)
  | 0 => Homeomorph.continuousMapOfUnique
  | n + 1 => by
      change C(G, TopRep.resolutionX X n) ≃ₜ C(Fin (n + 1) → G, X)
      exact ((Homeomorph.refl G).arrowCongr (resolutionFinHomeomorph X n)).trans
        ((Homeomorph.curry (X := G) (Y := Fin n → G) (Z := X)).symm.trans
          ((CategoryTheory.Monad.topFinConsHomeomorph (G := G) n).arrowCongr (Homeomorph.refl X)))

private theorem resolutionFinHomeomorph_apply (X : TopRep.{max v w, u, v} k G) :
    ∀ (n : ℕ) (c : TopRep.resolutionX X n) (t : Fin n → G),
      resolutionFinHomeomorph X n c t = resolutionFinUncurry X n c t
  | 0, c, t => rfl
  | n + 1, c, t => by
      rw [resolutionFinHomeomorph, resolutionFinUncurry_succ]
      dsimp only [Homeomorph.trans, Homeomorph.arrowCongr,
        Homeomorph.curry, Homeomorph.symm, Homeomorph.refl,
        ContinuousMap.comp, ContinuousMap.uncurry,
        CategoryTheory.Monad.topFinConsHomeomorph, Fin.consEquiv]
      exact resolutionFinHomeomorph_apply X n (c (t 0)) (Fin.tail t)

omit [LocallyCompactSpace G] in
private theorem uncurry_add (X : TopRep.{max v w, u, v} k G) :
    ∀ (n : ℕ) (a b : TopRep.resolutionX X n) (t : Fin n → G),
      resolutionFinUncurry X n (a + b) t =
        resolutionFinUncurry X n a t + resolutionFinUncurry X n b t
  | 0, a, b, t => rfl
  | n + 1, a, b, t => by
      change resolutionFinUncurry X n (a (t 0) + b (t 0)) (Fin.tail t) = _
      exact uncurry_add X n (a (t 0)) (b (t 0)) (Fin.tail t)

omit [LocallyCompactSpace G] in
private theorem uncurry_smul (X : TopRep.{max v w, u, v} k G) :
    ∀ (n : ℕ) (r : k) (a : TopRep.resolutionX X n) (t : Fin n → G),
      resolutionFinUncurry X n (r • a) t = r • resolutionFinUncurry X n a t
  | 0, r, a, t => rfl
  | n + 1, r, a, t => by
      change resolutionFinUncurry X n (r • a (t 0)) (Fin.tail t) = _
      exact uncurry_smul X n r (a (t 0)) (Fin.tail t)

/-- Canonical continuous linear equivalence on all finite tuples, including empty tuples. -/
noncomputable def resolutionFinContinuousLinearEquiv
    (X : TopRep.{max v w, u, v} k G) (n : ℕ) :
    TopRep.resolutionX X n ≃L[k] C(Fin n → G, X) where
  toEquiv := (resolutionFinHomeomorph X n).toEquiv
  map_add' a b := by
    apply ContinuousMap.ext
    intro t
    change resolutionFinHomeomorph X n (a + b) t =
      resolutionFinHomeomorph X n a t + resolutionFinHomeomorph X n b t
    rw [resolutionFinHomeomorph_apply, resolutionFinHomeomorph_apply,
      resolutionFinHomeomorph_apply]
    exact uncurry_add X n a b t
  map_smul' r a := by
    apply ContinuousMap.ext
    intro t
    change resolutionFinHomeomorph X n (r • a) t =
      r • resolutionFinHomeomorph X n a t
    rw [resolutionFinHomeomorph_apply, resolutionFinHomeomorph_apply]
    exact uncurry_smul X n r a t
  continuous_toFun := (resolutionFinHomeomorph X n).continuous_toFun
  continuous_invFun := (resolutionFinHomeomorph X n).continuous_invFun

/-- The forward comparison is the original literal finite-tuple evaluator. -/
@[simp] theorem resolutionFinContinuousLinearEquiv_apply
    (X : TopRep.{max v w, u, v} k G) (n : ℕ)
    (c : TopRep.resolutionX X n) (t : Fin n → G) :
    resolutionFinContinuousLinearEquiv X n c t = resolutionFinUncurry X n c t :=
  resolutionFinHomeomorph_apply X n c t

/-- Repeated currying recovers every value of every original continuous tuple map. -/
@[simp] theorem resolutionFinContinuousLinearEquiv_symm_apply
    (X : TopRep.{max v w, u, v} k G) (n : ℕ)
    (f : C(Fin n → G, X)) (t : Fin n → G) :
    resolutionFinUncurry X n ((resolutionFinContinuousLinearEquiv X n).symm f) t =
      f t := by
  rw [← resolutionFinContinuousLinearEquiv_apply]
  exact congrArg (fun z : C(Fin n → G, X) => z t)
    ((resolutionFinContinuousLinearEquiv X n).apply_symm_apply f)

/-- Equivariance for the same coefficient-plus-diagonal group action. -/
theorem resolutionFinContinuousLinearEquiv_action
    (X : TopRep.{max v w, u, v} k G) (n : ℕ) (g : G)
    (c : TopRep.resolutionX X n) (t : Fin n → G) :
    resolutionFinContinuousLinearEquiv X n ((TopRep.resolutionX X n).ρ g c) t =
      X.ρ g (resolutionFinContinuousLinearEquiv X n c (fun i => g⁻¹ * t i)) := by
  rw [resolutionFinContinuousLinearEquiv_apply, resolutionFinContinuousLinearEquiv_apply]
  exact resolutionFinUncurry_action X n g c t

/-- The full recursive differential is the alternating coordinate-deletion operator. -/
theorem resolutionFinContinuousLinearEquiv_d
    (X : TopRep.{max v w, u, v} k G) (q : ℕ)
    (c : TopRep.resolution'X X q) (t : Fin (q + 2) → G) :
    resolutionFinContinuousLinearEquiv X (q + 2) ((TopRep.d X (q + 1)).hom c) t =
      ∑ j : Fin (q + 2), (-1 : k) ^ (j : ℕ) •
        resolutionFinContinuousLinearEquiv X (q + 1) c (fun i => t (j.succAbove i)) := by
  calc
    resolutionFinContinuousLinearEquiv X (q + 2)
        ((TopRep.d X (q + 1)).hom c) t =
      resolutionFinUncurry X (q + 2) ((TopRep.d X (q + 1)).hom c) t :=
        resolutionFinContinuousLinearEquiv_apply X (q + 2) _ t
    _ = ∑ j : Fin (q + 2), (-1 : k) ^ (j : ℕ) •
        resolutionFinUncurry X (q + 1) c (fun i => t (j.succAbove i)) :=
      resolutionFinUncurry_d X q c t
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [resolutionFinContinuousLinearEquiv_apply]

/-- Every original continuous homogeneous cochain has an actual invariant nested lift. -/
theorem homogeneousFinContinuousLinearEquiv_lift
    (X : TopRep.{max v w, u, v} k G) (q : ℕ)
    (f : C(Fin (q + 1) → G, X))
    (hf : ∀ (g : G) (t : Fin (q + 1) → G), f (fun i => g * t i) = X.ρ g (f t)) :
    ∃ c : (TopRep.homogeneousCochains X).X q,
      ∀ t : Fin (q + 1) → G, resolutionFinUncurry X (q + 1) c.val t = f t := by
  let c := (resolutionFinContinuousLinearEquiv X (q + 1)).symm f
  have hc (t : Fin (q + 1) → G) : resolutionFinUncurry X (q + 1) c t = f t :=
    resolutionFinContinuousLinearEquiv_symm_apply X (q + 1) f t
  have hinv : c ∈ (TopRep.resolution'X X q).ρ.invariants := by
    change ∀ g : G, (TopRep.resolutionX X (q + 1)).ρ g c = c
    intro g
    apply resolutionFinUncurry_injective X (q + 1)
    funext t
    rw [resolutionFinUncurry_action, hc, hc]
    have h := hf g (fun i => g⁻¹ * t i)
    have ht : (fun i => g * (g⁻¹ * t i)) = t := by
      funext i
      simp only [mul_inv_cancel_left]
    rw [ht] at h
    exact h.symm
  exact ⟨⟨c, hinv⟩, hc⟩
end ContinuousCohomology
