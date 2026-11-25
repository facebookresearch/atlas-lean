/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.CategoryTheory.Action.Continuous
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.InvariantHomogeneousComplex

/-! # The original continuous homogeneous and inhomogeneous complexes -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u v w
namespace ContinuousCohomology
variable {k : Type u} [Ring k] [TopologicalSpace k]
variable (G : ProfiniteGrp.{v})

private theorem partialProd_continuous (q : ℕ) (i : Fin (q + 1)) :
    Continuous (fun g : Fin q → G => Fin.partialProd g i) := by
  induction i using Fin.induction with
  | zero => simpa only [Fin.partialProd_zero] using
      (continuous_const : Continuous (fun _ : Fin q → G => (1 : G)))
  | succ i hi =>
      have h := hi.mul (continuous_apply i)
      change Continuous (fun g : Fin q → G => Fin.partialProd g i.castSucc * g i) at h
      simpa only [Fin.partialProd_succ] using h

/-- Actual ordered prefix-product vertices in every degree. -/
def inhomogeneousVerticesCM (q : ℕ) : C(Fin q → G, Fin (q + 1) → G) :=
  ⟨Fin.partialProd, continuous_pi fun i => by exact partialProd_continuous G q i⟩

/-- Actual consecutive quotients of homogeneous vertices. -/
def homogeneousDifferencesCM (q : ℕ) : C(Fin (q + 1) → G, Fin q → G) :=
  ⟨fun t i => (t i.castSucc)⁻¹ * t i.succ,
    continuous_pi fun i => (continuous_apply i.castSucc).inv.mul (continuous_apply i.succ)⟩

variable (A : DiscreteContAction (TopModuleCat.{max v w} k) G)
/-- The same original coefficient carrier and action, merely bundled as TopRep. -/
abbrev inhomogeneousOriginalTopRep : TopRep.{max v w, u, v} k G :=
  (TopRep.fromActionTopModFunc (k := k) (G := G)).obj A.obj.obj
local notation "X" => inhomogeneousOriginalTopRep G A

private theorem original_action_continuous :
    Continuous (fun p : G × X => (inhomogeneousOriginalTopRep G A).ρ p.1 p.2) := by
  have h := (Action.isContinuous_def A.obj.obj).mp A.obj.property
  change Continuous (fun p : G × X => (inhomogeneousOriginalTopRep G A).ρ p.1 p.2) at h
  exact h

/-- Continuous linear inhomogenization by literal prefix vertices. -/
def inhomogeneousPhi (q : ℕ) :
    flatHomogeneousCochains X q →L[k] C(Fin q → G, X) where
  toFun f := f.val.comp (inhomogeneousVerticesCM G q)
  map_add' _ _ := by ext t; rfl
  map_smul' _ _ := by ext t; rfl
  cont := (ContinuousMap.continuous_precomp (inhomogeneousVerticesCM G q)).comp
    continuous_subtype_val

/-- Continuous linear homogenization using the original joint action. -/
def inhomogeneousPsi (q : ℕ) :
    C(Fin q → G, X) →L[k] flatHomogeneousCochains X q where
  toFun h := ⟨⟨fun t => (inhomogeneousOriginalTopRep G A).ρ (t 0)
    (h (homogeneousDifferencesCM G q t)),
    by exact (original_action_continuous G A).comp ((continuous_apply 0).prodMk
      (h.continuous.comp (homogeneousDifferencesCM G q).continuous))⟩, by
    intro g t
    have hd : homogeneousDifferencesCM G q (fun i => g * t i) =
        homogeneousDifferencesCM G q t := by
      funext i
      change (g * t i.castSucc)⁻¹ * (g * t i.succ) = (t i.castSucc)⁻¹ * t i.succ
      simp [mul_assoc]
    change (inhomogeneousOriginalTopRep G A).ρ (g * t 0)
      (h (homogeneousDifferencesCM G q (fun i => g * t i))) =
      (inhomogeneousOriginalTopRep G A).ρ g
        ((inhomogeneousOriginalTopRep G A).ρ (t 0) (h (homogeneousDifferencesCM G q t)))
    rw [hd, map_mul]
    rfl⟩
  map_add' _ _ := by
    apply Subtype.ext
    ext t
    exact map_add ((inhomogeneousOriginalTopRep G A).ρ (t 0)) _ _
  map_smul' _ _ := by
    apply Subtype.ext
    ext t
    exact map_smul ((inhomogeneousOriginalTopRep G A).ρ (t 0)) _ _
  cont := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (original_action_continuous G A).comp
      (((continuous_apply 0).comp continuous_snd).prodMk
        (continuous_fst.eval ((homogeneousDifferencesCM G q).continuous.comp continuous_snd)))

/-- Canonical continuous linear equivalence on all original continuous cochains. -/
def inhomogeneousContinuousEquiv (q : ℕ) :
    flatHomogeneousCochains X q ≃L[k] C(Fin q → G, X) :=
  ContinuousLinearEquiv.equivOfInverse (inhomogeneousPhi G A q) (inhomogeneousPsi G A q)
    (by
      intro f
      apply Subtype.ext
      ext t
      change (inhomogeneousOriginalTopRep G A).ρ (t 0)
        (f.val (Fin.partialProd (homogeneousDifferencesCM G q t))) = f.val t
      have ht : (fun i => t 0 * Fin.partialProd (homogeneousDifferencesCM G q t) i) = t := by
        have h := Fin.partialProd_left_inv t
        change (fun i => t 0 * Fin.partialProd (fun j => (t j.castSucc)⁻¹ * t j.succ) i) = t at h
        exact h
      exact (f.property (t 0) _).symm.trans (congrArg f.val ht))
    (by
      intro h
      ext g
      have hd : homogeneousDifferencesCM G q (Fin.partialProd g) = g := by
        funext i
        exact Fin.partialProd_right_inv g i
      change (inhomogeneousOriginalTopRep G A).ρ (Fin.partialProd g 0)
        (h (homogeneousDifferencesCM G q (Fin.partialProd g))) = h g
      rw [Fin.partialProd_zero, hd]
      simp)

/-- Full original forward value formula. -/
theorem inhomogeneousContinuousEquiv_apply (q : ℕ)
    (f : flatHomogeneousCochains X q) (g : Fin q → G) :
    inhomogeneousContinuousEquiv G A q f g = f.val (Fin.partialProd g) := rfl

/-- Full original inverse value formula. -/
theorem inhomogeneousContinuousEquiv_symm_apply (q : ℕ)
    (h : C(Fin q → G, X)) (t : Fin (q + 1) → G) :
    ((inhomogeneousContinuousEquiv G A q).symm h).val t =
      (inhomogeneousOriginalTopRep G A).ρ (t 0) (h (homogeneousDifferencesCM G q t)) := rfl

/-- The empty-tuple function space is canonically the original coefficient. -/
def inhomogeneousZeroEquiv : flatHomogeneousCochains X 0 ≃L[k] X :=
  (inhomogeneousContinuousEquiv G A 0).trans
    (resolutionFinContinuousLinearEquiv X 0).symm

/-- Degree-zero inhomogenization evaluates at the original identity vertex. -/
theorem inhomogeneousContinuousEquiv_zero (f : flatHomogeneousCochains X 0)
    (g : Fin 0 → G) :
    inhomogeneousContinuousEquiv G A 0 f g = f.val (fun _ => 1) := by
  rw [inhomogeneousContinuousEquiv_apply]
  congr 1
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact Fin.partialProd_zero g
end ContinuousCohomology
