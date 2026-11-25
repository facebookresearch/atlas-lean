/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientTensor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.InvariantHomogeneousComplex
public import MathlibExt.RepresentationTheory.Continuous.ContinuousActionBridge

/-!
# Continuous cochains with actual tensor coefficients

The coefficient tensor is the algebraic tensor of the original discrete
coefficient modules with its discrete topology and tensor group action.
The scalar ring keeps its given topology. Homogeneous cup uses the original
continuous invariant cochains and the shared middle coordinate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v w a b c x

namespace ContinuousCohomology

variable {R : Type u} [CommRing R] [TopologicalSpace R]
variable {G : ProfiniteGrp.{v}}

/-- The front coordinates of the original homogeneous cup tuple. -/
def homogeneousCupFront (p q : ℕ) (t : Fin (p + q + 1) → G) : Fin (p + 1) → G :=
  fun i => t ⟨i, by omega⟩

/-- The back coordinates include the shared middle coordinate p. -/
def homogeneousCupBack (p q : ℕ) (t : Fin (p + q + 1) → G) : Fin (q + 1) → G :=
  fun i => t ⟨p + i, by omega⟩

/-- Actual invariant continuous homogeneous cochains pair by the tensor cup formula. -/
def flatHomogeneousCup
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ)
    (f : flatHomogeneousCochains A p) (g : flatHomogeneousCochains B q) :
    flatHomogeneousCochains (discreteTensorCoefficient A B) (p + q) := by
  let F : C(Fin (p + q + 1) → G, discreteTensorCoefficient A B) :=
    { toFun := fun t => f.val (homogeneousCupFront p q t) ⊗ₜ[R]
        g.val (homogeneousCupBack p q t)
      continuous_toFun := by
        have ht : Continuous (fun x : A × B =>
            (show discreteTensorCoefficient A B from x.1 ⊗ₜ[R] x.2)) :=
          continuous_of_discreteTopology
        have hf : Continuous (fun t : Fin (p + q + 1) → G =>
            f.val (homogeneousCupFront p q t)) :=
          f.val.continuous.comp (continuous_pi fun _ => continuous_apply _)
        have hg : Continuous (fun t : Fin (p + q + 1) → G =>
            g.val (homogeneousCupBack p q t)) :=
          g.val.continuous.comp (continuous_pi fun _ => continuous_apply _)
        exact ht.comp (hf.prodMk hg) }
  refine ⟨F, ?_⟩
  intro h t
  change f.val (fun i => h * t ⟨i, by omega⟩) ⊗ₜ[R]
      g.val (fun i => h * t ⟨p + i, by omega⟩) = _
  exact (congrArg₂ (fun a b => a ⊗ₜ[R] b)
      (f.property h (homogeneousCupFront p q t))
      (g.property h (homogeneousCupBack p q t))).trans
    (discreteTensorCoefficient_action_tmul A B h
      (f.val (homogeneousCupFront p q t))
      (g.val (homogeneousCupBack p q t))).symm

/-- The homogeneous cup retains every original tuple value. -/
theorem flatHomogeneousCup_apply
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ)
    (f : flatHomogeneousCochains A p) (g : flatHomogeneousCochains B q)
    (t : Fin (p + q + 1) → G) :
    (flatHomogeneousCup A B p q f g).val t =
      f.val (homogeneousCupFront p q t) ⊗ₜ[R] g.val (homogeneousCupBack p q t) := rfl

/-- The actual homogeneous tensor cup is linear in each original cochain. -/
def flatHomogeneousCupLinear
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ) :
    flatHomogeneousCochains A p →ₗ[R] flatHomogeneousCochains B q →ₗ[R]
      flatHomogeneousCochains (discreteTensorCoefficient A B) (p + q) where
  toFun f :=
    { toFun := flatHomogeneousCup A B p q f
      map_add' := by
        intro g h
        apply Subtype.ext
        apply ContinuousMap.ext
        intro t
        change f.val (homogeneousCupFront p q t) ⊗ₜ[R]
            (g.val (homogeneousCupBack p q t) + h.val (homogeneousCupBack p q t)) = _
        exact TensorProduct.tmul_add _ _ _
      map_smul' := by
        intro r g
        apply Subtype.ext
        apply ContinuousMap.ext
        intro t
        change f.val (homogeneousCupFront p q t) ⊗ₜ[R]
            (r • g.val (homogeneousCupBack p q t)) = _
        exact TensorProduct.tmul_smul _ _ _ }
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    change (f.val (homogeneousCupFront p q t) + g.val (homogeneousCupFront p q t)) ⊗ₜ[R]
        h.val (homogeneousCupBack p q t) = _
    exact TensorProduct.add_tmul _ _ _
  map_smul' := by
    intro r f
    apply LinearMap.ext
    intro g
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    change (r • f.val (homogeneousCupFront p q t)) ⊗ₜ[R]
        g.val (homogeneousCupBack p q t) = _
    exact TensorProduct.smul_tmul' _ _ _

/-- The cochain-level tensor cup, on the same original module carriers. -/
def flatHomogeneousCupTensorMap
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ) :
    ModuleCat.of R (TensorProduct R (flatHomogeneousCochains A p)
      (flatHomogeneousCochains B q)) ⟶
    ModuleCat.of R (flatHomogeneousCochains (discreteTensorCoefficient A B) (p + q)) :=
  ModuleCat.ofHom (TensorProduct.lift (flatHomogeneousCupLinear A B p q))

private theorem front_delete_left (p q : ℕ) (j i : Fin (p + 1)) :
    (⟨j, by omega⟩ : Fin (p + q + 2)).succAbove
      (⟨i, by omega⟩ : Fin (p + q + 1)) =
    (⟨(j.castSucc.succAbove i).val, by omega⟩ : Fin (p + q + 2)) := by
  apply Fin.ext
  by_cases h : (i : ℕ) < j
  · simp [Fin.succAbove, Fin.lt_def, h]
  · simp [Fin.succAbove, Fin.lt_def, h]

private theorem back_delete_left (p q : ℕ) (j : Fin (p + 1)) (i : Fin (q + 1)) :
    (⟨j, by omega⟩ : Fin (p + q + 2)).succAbove
      (⟨p + i, by omega⟩ : Fin (p + q + 1)) =
    (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2)) := by
  rw [Fin.succAbove_of_le_castSucc]
  · apply Fin.ext
    simp
    omega
  · change (j : ℕ) ≤ p + i
    omega

private theorem front_delete_right (p q : ℕ) (j : Fin (q + 1)) (i : Fin (p + 1)) :
    (⟨p + 1 + j, by omega⟩ : Fin (p + q + 2)).succAbove
      (⟨i, by omega⟩ : Fin (p + q + 1)) =
    (⟨i, by omega⟩ : Fin (p + q + 2)) := by
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · change (i : ℕ) < p + 1 + j
    omega

private theorem back_delete_right (p q : ℕ) (j i : Fin (q + 1)) :
    (⟨p + 1 + j, by omega⟩ : Fin (p + q + 2)).succAbove
      (⟨p + i, by omega⟩ : Fin (p + q + 1)) =
    (⟨p + (j.succ.succAbove i).val, by omega⟩ : Fin (p + q + 2)) := by
  apply Fin.ext
  by_cases h : (i : ℕ) < j + 1
  · have hp : p + (i : ℕ) < p + 1 + j := by omega
    simp [Fin.succAbove, Fin.lt_def, h, hp]
  · have hp : ¬ p + (i : ℕ) < p + 1 + j := by omega
    simp [Fin.succAbove, Fin.lt_def, h, hp]
    omega



private theorem splitCupDeletionSum
    {R : Type u} [CommRing R] {M : Type a} {N : Type b} {P : Type c}
    [AddCommGroup P] [Module R P] {X : Type x}
    (mu : M → N → P) (p q : ℕ)
    (f : (Fin (p + 1) → X) → M) (g : (Fin (q + 1) → X) → N)
    (t : Fin (p + q + 2) → X) :
    (∑ j : Fin (p + q + 2), (-1 : R) ^ (j : ℕ) •
      mu (f (fun i => t (j.succAbove ⟨i, by omega⟩)))
        (g (fun i => t (j.succAbove ⟨p + i, by omega⟩)))) =
    (∑ j : Fin (p + 1), (-1 : R) ^ (j : ℕ) •
      mu (f (fun i => t ⟨(j.castSucc.succAbove i).val, by omega⟩))
        (g (fun i => t ⟨p + 1 + i, by omega⟩))) +
    (∑ j : Fin (q + 1), (-1 : R) ^ (p + 1 + (j : ℕ)) •
      mu (f (fun i => t ⟨i, by omega⟩))
        (g (fun i => t ⟨p + (j.succ.succAbove i).val, by omega⟩))) := by
  let F : Fin (p + q + 2) → P := fun j => (-1 : R) ^ (j : ℕ) •
    mu (f (fun i => t (j.succAbove ⟨i, by omega⟩)))
      (g (fun i => t (j.succAbove ⟨p + i, by omega⟩)))
  let L : Fin (p + 1) → P := fun j => (-1 : R) ^ (j : ℕ) •
    mu (f (fun i => t ⟨(j.castSucc.succAbove i).val, by omega⟩))
      (g (fun i => t ⟨p + 1 + i, by omega⟩))
  let T : Fin (q + 1) → P := fun j => (-1 : R) ^ (p + 1 + (j : ℕ)) •
    mu (f (fun i => t ⟨i, by omega⟩))
      (g (fun i => t ⟨p + (j.succ.succAbove i).val, by omega⟩))
  change (∑ j, F j) = (∑ j, L j) + ∑ j, T j
  have he : (p + 1) + (q + 1) = p + q + 2 := by omega
  calc
    (∑ j, F j) = ∑ j : Fin ((p + 1) + (q + 1)), F (j.cast he) :=
      (Fin.sum_congr' F he).symm
    _ = (∑ j : Fin (p + 1), F ((j.castAdd (q + 1)).cast he)) +
        ∑ j : Fin (q + 1), F ((j.natAdd (p + 1)).cast he) :=
      Fin.sum_univ_add _
    _ = (∑ j, L j) + ∑ j, T j := by
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        have hJ : (j.castAdd (q + 1)).cast he =
            (⟨j, by omega⟩ : Fin (p + q + 2)) := by
          apply Fin.ext
          rfl
        dsimp only [F, L]
        rw [hJ]
        have hf : (fun i : Fin (p + 1) =>
            t ((⟨j, by omega⟩ : Fin (p + q + 2)).succAbove ⟨i, by omega⟩)) =
            (fun i => t ⟨(j.castSucc.succAbove i).val, by omega⟩) := by
          funext i
          exact congrArg t (front_delete_left p q j i)
        have hg : (fun i : Fin (q + 1) =>
            t ((⟨j, by omega⟩ : Fin (p + q + 2)).succAbove ⟨p + i, by omega⟩)) =
            (fun i : Fin (q + 1) => t ⟨p + 1 + i, by omega⟩) := by
          funext i
          exact congrArg t (back_delete_left p q j i)
        rw [hf, hg]
      · apply Finset.sum_congr rfl
        intro j _
        have hJ : (j.natAdd (p + 1)).cast he =
            (⟨p + 1 + j, by omega⟩ : Fin (p + q + 2)) := by
          apply Fin.ext
          rfl
        dsimp only [F, T]
        rw [hJ]
        have hf : (fun i : Fin (p + 1) =>
            t ((⟨p + 1 + j, by omega⟩ : Fin (p + q + 2)).succAbove ⟨i, by omega⟩)) =
            (fun i : Fin (p + 1) => t ⟨i, by omega⟩) := by
          funext i
          exact congrArg t (front_delete_right p q j i)
        have hg : (fun i : Fin (q + 1) =>
            t ((⟨p + 1 + j, by omega⟩ : Fin (p + q + 2)).succAbove ⟨p + i, by omega⟩)) =
            (fun i => t ⟨p + (j.succ.succAbove i).val, by omega⟩) := by
          funext i
          exact congrArg t (back_delete_right p q j i)
        rw [hf, hg]


/-- The alternating deletion differential obeys the homogeneous bilinear cup Leibniz identity. -/
theorem homogeneousDeletionLeibniz
    {R : Type u} [CommRing R] {M : Type a} {N : Type b} {P : Type c}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] {X : Type x}
    (mu : M →ₗ[R] N →ₗ[R] P) (p q : ℕ)
    (f : (Fin (p + 1) → X) → M) (g : (Fin (q + 1) → X) → N)
    (t : Fin (p + q + 2) → X) :
    (∑ j : Fin (p + q + 2), (-1 : R) ^ (j : ℕ) •
      mu (f (fun i => t (j.succAbove ⟨i, by omega⟩)))
        (g (fun i => t (j.succAbove ⟨p + i, by omega⟩)))) =
    mu (∑ j : Fin (p + 2), (-1 : R) ^ (j : ℕ) •
        f (fun i => t ⟨(j.succAbove i).val, by omega⟩))
      (g (fun i => t ⟨p + 1 + i, by omega⟩)) +
    (-1 : R) ^ p • mu (f (fun i => t ⟨i, by omega⟩))
      (∑ j : Fin (q + 2), (-1 : R) ^ (j : ℕ) •
        g (fun i => t ⟨p + (j.succAbove i).val, by omega⟩)) := by
  let f0 := f (fun i : Fin (p + 1) => t ⟨i, by omega⟩)
  let g0 := g (fun i : Fin (q + 1) => t ⟨p + 1 + i, by omega⟩)
  let fa : Fin (p + 2) → M := fun j =>
    f (fun i => t ⟨(j.succAbove i).val, by omega⟩)
  let gb : Fin (q + 2) → N := fun j =>
    g (fun i => t ⟨p + (j.succAbove i).val, by omega⟩)
  let L : P := ∑ j : Fin (p + 1), (-1 : R) ^ (j : ℕ) •
    mu (fa j.castSucc) g0
  let T : P := ∑ j : Fin (q + 1), (-1 : R) ^ (p + 1 + (j : ℕ)) •
    mu f0 (gb j.succ)
  let z := mu f0 g0
  have hlast : fa (Fin.last (p + 1)) = f0 := by
    dsimp only [fa, f0]
    congr 1
    funext i
    apply congrArg t
    apply Fin.ext
    change ((Fin.last (p + 1)).succAbove i).val = i.val
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · change (i : ℕ) < p + 1
      exact i.isLt
  have hzero : gb 0 = g0 := by
    dsimp only [gb, g0]
    congr 1
    funext i
    apply congrArg t
    apply Fin.ext
    change p + ((0 : Fin (q + 2)).succAbove i).val = p + 1 + i.val
    rw [Fin.succAbove_of_le_castSucc]
    · simp
      omega
    · exact Fin.zero_le _
  have hleft : mu (∑ j : Fin (p + 2), (-1 : R) ^ (j : ℕ) • fa j) g0 =
      L + (-1 : R) ^ (p + 1) • z := by
    rw [Fin.sum_univ_castSucc]
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, Fin.val_castSucc, Fin.val_last, hlast]
    rfl
  have hright : (-1 : R) ^ p •
      mu f0 (∑ j : Fin (q + 2), (-1 : R) ^ (j : ℕ) • gb j) =
      (-1 : R) ^ p • z + T := by
    rw [Fin.sum_univ_succ]
    simp only [map_add, map_sum, map_smul, Fin.val_zero, Fin.val_succ,
      pow_zero, one_smul, hzero, smul_add, Finset.smul_sum, smul_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← pow_add]
    congr 2
    omega
  have hmid : (-1 : R) ^ (p + 1) • z + (-1 : R) ^ p • z = 0 := by
    rw [pow_succ', mul_smul, neg_one_smul, neg_add_cancel]
  have hs := splitCupDeletionSum (R := R) (M := M) (N := N) (P := P) (X := X)
    (fun a b => mu a b) p q f g t
  change _ = mu (∑ j : Fin (p + 2), (-1 : R) ^ (j : ℕ) • fa j) g0 +
    (-1 : R) ^ p • mu f0 (∑ j : Fin (q + 2), (-1 : R) ^ (j : ℕ) • gb j)
  rw [hleft, hright]
  calc
    _ = L + T := hs
    _ = (L + (-1 : R) ^ (p + 1) • z) + ((-1 : R) ^ p • z + T) := by
      symm
      calc
        _ = L + ((-1 : R) ^ (p + 1) • z + (-1 : R) ^ p • z) + T := by abel
        _ = L + T := by rw [hmid, add_zero]


/-- The original homogeneous differential satisfies the tensor cup Leibniz formula
in every pair of nonnegative degrees, including degree zero. -/
theorem flatHomogeneousCup_leibniz
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ)
    (f : flatHomogeneousCochains A p) (g : flatHomogeneousCochains B q)
    (t : Fin (p + q + 2) → G) :
    (flatHomogeneousD (discreteTensorCoefficient A B) (p + q)
      (flatHomogeneousCup A B p q f g)).val t =
      (flatHomogeneousCup A B (p + 1) q
        (flatHomogeneousD A p f) g).val
        (fun i : Fin ((p + 1) + q + 1) => t ⟨i, by omega⟩) +
      (-1 : R) ^ p •
        (flatHomogeneousCup A B p (q + 1) f
          (flatHomogeneousD B q g)).val
          (fun i : Fin (p + (q + 1) + 1) => t ⟨i, by omega⟩) := by
  have h := homogeneousDeletionLeibniz
    (R := R) (M := A) (N := B) (P := TensorProduct R A B) (X := G)
    (TensorProduct.mk R A B) p q f.val g.val t
  change (show TensorProduct R A B from
    (flatHomogeneousD (discreteTensorCoefficient A B) (p + q)
      (flatHomogeneousCup A B p q f g)).val t) =
    ((flatHomogeneousD A p f).val (fun i => t ⟨i, by omega⟩) ⊗ₜ[R]
      g.val (fun i => t ⟨p + 1 + i, by omega⟩)) +
    (-1 : R) ^ p • (f.val (fun i => t ⟨i, by omega⟩) ⊗ₜ[R]
      (flatHomogeneousD B q g).val (fun i => t ⟨p + i, by omega⟩))
  rw [flatHomogeneousD_apply]
  simp only [flatHomogeneousCup_apply]
  rw [flatHomogeneousD_apply, flatHomogeneousD_apply]
  exact h

private theorem flatCup_zero_left
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ)
    (g : flatHomogeneousCochains B q) : flatHomogeneousCup A B p q 0 g = 0 := by
  exact DFunLike.congr_fun (map_zero (flatHomogeneousCupLinear A B p q)) g

private theorem flatCup_zero_right
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ)
    (f : flatHomogeneousCochains A p) : flatHomogeneousCup A B p q f 0 = 0 :=
  map_zero (flatHomogeneousCupLinear A B p q f)

private theorem flatCup_cocycle
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ)
    (f : flatHomogeneousCochains A p) (g : flatHomogeneousCochains B q)
    (hf : flatHomogeneousD A p f = 0) (hg : flatHomogeneousD B q g = 0) :
    flatHomogeneousD (discreteTensorCoefficient A B) (p + q)
      (flatHomogeneousCup A B p q f g) = 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  have h := flatHomogeneousCup_leibniz A B p q f g t
  rw [hf, hg, flatCup_zero_left, flatCup_zero_right] at h
  exact h.trans (by simp)

/-- The underlying module complex of the original flat homogeneous cochains. -/
abbrev flatHomogeneousModuleComplex (X : TopRep.{max v w, u, v} R G) :
    CochainComplex (ModuleCat.{max v w} R) ℕ :=
  ((forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (flatHomogeneousComplex X)

private theorem flatModuleComplex_d (X : TopRep.{max v w, u, v} R G) (p : ℕ) :
    (flatHomogeneousModuleComplex X).d p (p + 1) =
      ModuleCat.ofHom (flatHomogeneousD X p).hom.toLinearMap := by
  change (forget₂ (TopModuleCat R) (ModuleCat R)).map
    ((flatHomogeneousComplex X).d p (p + 1)) = _
  exact congrArg
    (fun d : flatHomogeneousTerm X p ⟶ flatHomogeneousTerm X (p + 1) =>
      (forget₂ (TopModuleCat R) (ModuleCat R)).map d)
    (CochainComplex.of_d (flatHomogeneousTerm X) (flatHomogeneousD X) p)

private theorem flatModuleCycles_closed
    (X : TopRep.{max v w, u, v} R G) (p : ℕ)
    (z : (flatHomogeneousModuleComplex X).cycles p) :
    flatHomogeneousD X p ((flatHomogeneousModuleComplex X).iCycles p z) = 0 := by
  have h := ConcreteCategory.congr_hom ((flatHomogeneousModuleComplex X).iCycles_d p (p + 1)) z
  rw [flatModuleComplex_d] at h
  exact h

/-- The original cochain cup applied to the inclusions of both actual cycle modules. -/
def flatHomogeneousCycleCupCochain
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ) :
    (flatHomogeneousModuleComplex A).cycles p →ₗ[R] (flatHomogeneousModuleComplex B).cycles q →ₗ[R]
      (flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).X (p + q) :=
  ((flatHomogeneousCupLinear A B p q).compl₂ ((flatHomogeneousModuleComplex B).iCycles q).hom).comp
    ((flatHomogeneousModuleComplex A).iCycles p).hom

/-- The cup of two actual cycles is again a cycle for the original differential. -/
theorem flatHomogeneousCycleCupCochain_closed
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ)
    (x : (flatHomogeneousModuleComplex A).cycles p) (y : (flatHomogeneousModuleComplex B).cycles q) :
    (flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).d (p + q) (p + q + 1)
      (flatHomogeneousCycleCupCochain A B p q x y) = 0 := by
  rw [flatModuleComplex_d]
  exact flatCup_cocycle A B p q _ _ (flatModuleCycles_closed A p x)
    (flatModuleCycles_closed B q y)

omit [TopologicalSpace R] in
private theorem liftCycles_value_i
    (K : CochainComplex (ModuleCat.{a} R) ℕ) (n : ℕ)
    {M : ModuleCat.{a} R} (k : M ⟶ K.X n)
    (hk : k ≫ K.d n (n + 1) = 0) (x : M) :
    (K.iCycles n).hom ((K.liftCycles k (n + 1)
      ((ComplexShape.up ℕ).next_eq' rfl) hk).hom x) = k.hom x := by
  exact ConcreteCategory.congr_hom
    (K.liftCycles_i k (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hk) x

/-- The continuous homogeneous cup lifted to the actual target cycles for a fixed left cycle. -/
def flatHomogeneousCycleCupRight
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ)
    (x : (flatHomogeneousModuleComplex A).cycles p) :
    (flatHomogeneousModuleComplex B).cycles q →ₗ[R]
      (flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).cycles (p + q) :=
  ((flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).liftCycles
    (ModuleCat.ofHom (flatHomogeneousCycleCupCochain A B p q x)) (p + q + 1)
    ((ComplexShape.up ℕ).next_eq' rfl) (by
      ext y
      exact flatHomogeneousCycleCupCochain_closed A B p q x y)).hom

/-- The cycle lift retains its original cochain cup after the actual cycle inclusion. -/
theorem flatHomogeneousCycleCupRight_iCycles
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ)
    (x : (flatHomogeneousModuleComplex A).cycles p) (y : (flatHomogeneousModuleComplex B).cycles q) :
    ((flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).iCycles (p + q)).hom
      (flatHomogeneousCycleCupRight A B p q x y) = flatHomogeneousCycleCupCochain A B p q x y := by
  exact liftCycles_value_i (flatHomogeneousModuleComplex (discreteTensorCoefficient A B)) (p + q)
    (ModuleCat.ofHom (flatHomogeneousCycleCupCochain A B p q x)) _ y

/-- The bilinear cup on the actual cycles of the underlying flat module complex. -/
def flatHomogeneousCycleCupLinear
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ) :
    (flatHomogeneousModuleComplex A).cycles p →ₗ[R] (flatHomogeneousModuleComplex B).cycles q →ₗ[R]
      (flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).cycles (p + q) where
  toFun := flatHomogeneousCycleCupRight A B p q
  map_add' := by
    intro x x'
    apply LinearMap.ext
    intro y
    apply (ModuleCat.mono_iff_injective
      ((flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).iCycles (p + q))).mp inferInstance
    change ((flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).iCycles (p + q)).hom
        (flatHomogeneousCycleCupRight A B p q (x + x') y) =
      ((flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).iCycles (p + q)).hom
        (flatHomogeneousCycleCupRight A B p q x y + flatHomogeneousCycleCupRight A B p q x' y)
    rw [map_add]
    exact (flatHomogeneousCycleCupRight_iCycles A B p q (x + x') y).trans
      ((DFunLike.congr_fun (map_add (flatHomogeneousCycleCupCochain A B p q) x x') y).trans
        (congrArg₂ (· + ·) (flatHomogeneousCycleCupRight_iCycles A B p q x y).symm
          (flatHomogeneousCycleCupRight_iCycles A B p q x' y).symm))
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro y
    apply (ModuleCat.mono_iff_injective
      ((flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).iCycles (p + q))).mp inferInstance
    change ((flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).iCycles (p + q)).hom
        (flatHomogeneousCycleCupRight A B p q (r • x) y) =
      ((flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).iCycles (p + q)).hom
        (r • flatHomogeneousCycleCupRight A B p q x y)
    rw [map_smul]
    exact (flatHomogeneousCycleCupRight_iCycles A B p q (r • x) y).trans
      ((DFunLike.congr_fun (map_smul (flatHomogeneousCycleCupCochain A B p q) r x) y).trans
        (congrArg (r • ·) (flatHomogeneousCycleCupRight_iCycles A B p q x y).symm))

private theorem flatHomogeneousCycleCupLinear_iCycles
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ)
    (x : (flatHomogeneousModuleComplex A).cycles p) (y : (flatHomogeneousModuleComplex B).cycles q) :
    ((flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).iCycles (p + q)).hom
      (flatHomogeneousCycleCupLinear A B p q x y) = flatHomogeneousCycleCupCochain A B p q x y :=
  flatHomogeneousCycleCupRight_iCycles A B p q x y

/-- The class of the original cycle cup under the actual homology projection. -/
def flatHomogeneousCycleCupClass
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ) :
    (flatHomogeneousModuleComplex A).cycles p →ₗ[R] (flatHomogeneousModuleComplex B).cycles q →ₗ[R]
      (flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).homology (p + q) :=
  (flatHomogeneousCycleCupLinear A B p q).compr₂
    ((flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).homologyπ (p + q)).hom

omit [TopologicalSpace R] in
private theorem cycleProjection_zero_of_boundary
    (K : CochainComplex (ModuleCat.{a} R) ℕ) (n m : ℕ)
    (x : K.X n) (z : K.cycles m)
    (h : (K.iCycles m).hom z = (K.d n m).hom x) :
    (K.homologyπ m).hom z = 0 := by
  have hz : z = (K.toCycles n m).hom x := by
    apply (ModuleCat.mono_iff_injective (K.iCycles m)).mp inferInstance
    exact h.trans (ConcreteCategory.congr_hom (K.toCycles_i n m) x).symm
  rw [hz]
  exact ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ n m) x

private theorem flatModuleComplex_d_value
    (X : TopRep.{max v w, u, v} R G) (n m : ℕ) (h : n + 1 = m)
    (f : flatHomogeneousCochains X n) (t : Fin (m + 1) → G) :
    ((flatHomogeneousModuleComplex X).d n m f).val t =
      (flatHomogeneousD X n f).val
        (fun i : Fin (n + 2) => t ⟨i, by omega⟩) := by
  subst m
  rw [flatModuleComplex_d]
  rfl

private theorem cycleCupHomology_boundary_left
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ)
    (a : (flatHomogeneousModuleComplex A).X p) (y : (flatHomogeneousModuleComplex B).cycles q) :
    flatHomogeneousCycleCupClass A B (p + 1) q
      ((flatHomogeneousModuleComplex A).toCycles p (p + 1) a) y = 0 := by
  let g := ((flatHomogeneousModuleComplex B).iCycles q).hom y
  let c := flatHomogeneousCup A B p q a g
  have hg : flatHomogeneousD B q g = 0 := flatModuleCycles_closed B q y
  have hda : ((flatHomogeneousModuleComplex A).iCycles (p + 1)).hom
      (((flatHomogeneousModuleComplex A).toCycles p (p + 1)).hom a) = flatHomogeneousD A p a := by
    have h := ConcreteCategory.congr_hom ((flatHomogeneousModuleComplex A).toCycles_i p (p + 1)) a
    rw [flatModuleComplex_d] at h
    exact h
  apply cycleProjection_zero_of_boundary
    (flatHomogeneousModuleComplex (discreteTensorCoefficient A B)) (p + q) ((p + 1) + q) c
  refine (flatHomogeneousCycleCupLinear_iCycles A B (p + 1) q _ y).trans ?_
  change flatHomogeneousCup A B (p + 1) q
      (((flatHomogeneousModuleComplex A).iCycles (p + 1)).hom
        (((flatHomogeneousModuleComplex A).toCycles p (p + 1)).hom a)) g = _
  rw [hda]
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  let tt : Fin (p + q + 2) → G := fun i => t ⟨i, by omega⟩
  have h := flatHomogeneousCup_leibniz A B p q a g tt
  rw [hg, flatCup_zero_right] at h
  have ht : (fun i : Fin ((p + 1) + q + 1) => tt ⟨i, by omega⟩) = t := by
    funext i
    exact congrArg t (Fin.ext rfl)
  rw [ht] at h
  have hD := flatModuleComplex_d_value (discreteTensorCoefficient A B)
    (p + q) ((p + 1) + q) (by omega) c t
  exact (h.trans (by simp)).symm.trans hD.symm

omit [TopologicalSpace R] in
private theorem negOnePow_smul_cancel {P : Type a} [AddCommGroup P] [Module R P]
    (n : ℕ) (z : P) : (-1 : R) ^ n • ((-1 : R) ^ n • z) = z := by
  rw [smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul]

private theorem cycleCupHomology_boundary_right
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ)
    (x : (flatHomogeneousModuleComplex A).cycles p) (b : (flatHomogeneousModuleComplex B).X q) :
    flatHomogeneousCycleCupClass A B p (q + 1) x
      ((flatHomogeneousModuleComplex B).toCycles q (q + 1) b) = 0 := by
  let f := ((flatHomogeneousModuleComplex A).iCycles p).hom x
  let c := flatHomogeneousCup A B p q f b
  let z := flatHomogeneousCycleCupLinear A B p (q + 1) x ((flatHomogeneousModuleComplex B).toCycles q (q + 1) b)
  have hf : flatHomogeneousD A p f = 0 := flatModuleCycles_closed A p x
  have hdb : ((flatHomogeneousModuleComplex B).iCycles (q + 1)).hom
      (((flatHomogeneousModuleComplex B).toCycles q (q + 1)).hom b) = flatHomogeneousD B q b := by
    have h := ConcreteCategory.congr_hom ((flatHomogeneousModuleComplex B).toCycles_i q (q + 1)) b
    rw [flatModuleComplex_d] at h
    exact h
  have hz : ((flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).iCycles (p + (q + 1))).hom z =
      flatHomogeneousCup A B p (q + 1) f (flatHomogeneousD B q b) := by
    refine (flatHomogeneousCycleCupLinear_iCycles A B p (q + 1) x _).trans ?_
    change flatHomogeneousCup A B p (q + 1) f
      (((flatHomogeneousModuleComplex B).iCycles (q + 1)).hom
        (((flatHomogeneousModuleComplex B).toCycles q (q + 1)).hom b)) = _
    rw [hdb]
  have hE : ((flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).d
      (p + q) (p + (q + 1))).hom c =
      (-1 : R) ^ p • ((flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).iCycles
        (p + (q + 1))).hom z := by
    rw [hz]
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    let tt : Fin (p + q + 2) → G := fun i => t ⟨i, by omega⟩
    have h := flatHomogeneousCup_leibniz A B p q f b tt
    rw [hf, flatCup_zero_left] at h
    have ht : (fun i : Fin (p + (q + 1) + 1) => tt ⟨i, by omega⟩) = t := by
      funext i
      exact congrArg t (Fin.ext rfl)
    rw [ht] at h
    have hD := flatModuleComplex_d_value (discreteTensorCoefficient A B)
      (p + q) (p + (q + 1)) (by omega) c t
    exact hD.trans (h.trans (by
      change 0 + _ = _
      rw [zero_add]
      rfl))
  have hh : ((flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).homologyπ
      (p + (q + 1))).hom ((-1 : R) ^ p • z) = 0 :=
    cycleProjection_zero_of_boundary (flatHomogeneousModuleComplex (discreteTensorCoefficient A B))
      (p + q) (p + (q + 1)) c ((-1 : R) ^ p • z)
      ((map_smul _ _ _).trans hE.symm)
  have hh' : (-1 : R) ^ p • ((flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).homologyπ
      (p + (q + 1))).hom z = 0 := (map_smul _ _ _).symm.trans hh
  have hval := congrArg ((-1 : R) ^ p • ·) hh'
  exact (negOnePow_smul_cancel p _).symm.trans (hval.trans (smul_zero _))

private theorem cycleCupHomology_boundary_left_general
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (i p q : ℕ) (hip : i + 1 = p)
    (a : (flatHomogeneousModuleComplex A).X i) (y : (flatHomogeneousModuleComplex B).cycles q) :
    flatHomogeneousCycleCupClass A B p q ((flatHomogeneousModuleComplex A).toCycles i p a) y = 0 := by
  subst p
  exact cycleCupHomology_boundary_left A B i q a y

private theorem cycleCupHomology_boundary_right_general
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p i q : ℕ) (hiq : i + 1 = q)
    (x : (flatHomogeneousModuleComplex A).cycles p) (b : (flatHomogeneousModuleComplex B).X i) :
    flatHomogeneousCycleCupClass A B p q x ((flatHomogeneousModuleComplex B).toCycles i q b) = 0 := by
  subst q
  exact cycleCupHomology_boundary_right A B p i x b

/-- Every incoming left boundary has zero cup class, including degree zero. -/
theorem flatHomogeneousCycleCupClass_boundary_left
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ)
    (a : ((flatHomogeneousModuleComplex A).sc p).X₁) (y : (flatHomogeneousModuleComplex B).cycles q) :
    flatHomogeneousCycleCupClass A B p q (((flatHomogeneousModuleComplex A).sc p).toCycles a) y = 0 := by
  by_cases hp : (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev p) p
  · exact cycleCupHomology_boundary_left_general A B _ p q hp a y
  · have hz := ConcreteCategory.congr_hom
      ((flatHomogeneousModuleComplex A).toCycles_eq_zero hp) a
    change flatHomogeneousCycleCupClass A B p q ((flatHomogeneousModuleComplex A).toCycles _ p a) y = 0
    rw [hz]
    exact DFunLike.congr_fun (map_zero (flatHomogeneousCycleCupClass A B p q)) y

/-- Every incoming right boundary has zero cup class, including degree zero. -/
theorem flatHomogeneousCycleCupClass_boundary_right
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ)
    (x : (flatHomogeneousModuleComplex A).cycles p) (b : ((flatHomogeneousModuleComplex B).sc q).X₁) :
    flatHomogeneousCycleCupClass A B p q x (((flatHomogeneousModuleComplex B).sc q).toCycles b) = 0 := by
  by_cases hq : (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev q) q
  · exact cycleCupHomology_boundary_right_general A B p _ q hq x b
  · have hz := ConcreteCategory.congr_hom
      ((flatHomogeneousModuleComplex B).toCycles_eq_zero hq) b
    change flatHomogeneousCycleCupClass A B p q x ((flatHomogeneousModuleComplex B).toCycles _ q b) = 0
    rw [hz]
    exact map_zero (flatHomogeneousCycleCupClass A B p q x)

omit [TopologicalSpace R] in
/- The native coefficient and ring universes are independent. The monoidal
graded-pairing API requires a monoidal category of modules, whose current
instance uses the same ring and module universe. The cup applies the existing
ShortComplex.descHomology to each variable and keeps the original native objects. -/
private theorem descHomology_apply
    (S : ShortComplex (ModuleCat.{a} R)) {T : ModuleCat.{a} R}
    (k : S.cycles ⟶ T) (hk : S.toCycles ≫ k = 0) (z : S.cycles) :
    (S.descHomology k hk).hom (S.homologyπ z) = k.hom z := by
  exact ConcreteCategory.congr_hom (S.π_descHomology k hk) z

/-- The actual flat module homology cup, with both boundary conditions proved internally. -/
def flatHomogeneousModuleCupLinear
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ) :
    (flatHomogeneousModuleComplex A).homology p →ₗ[R] (flatHomogeneousModuleComplex B).homology q →ₗ[R]
      (flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).homology (p + q) := by
  let S := (flatHomogeneousModuleComplex A).sc p
  let T := (flatHomogeneousModuleComplex B).sc q
  let P := (flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).homology (p + q)
  change S.homology →ₗ[R] T.homology →ₗ[R] P
  let b := flatHomogeneousCycleCupClass A B p q
  let left : S.homology →ₗ[R] T.cycles →ₗ[R] P :=
    (S.descHomology (ModuleCat.ofHom b) (by
      ext x y
      exact flatHomogeneousCycleCupClass_boundary_left A B p q x y)).hom
  have left_pi (x : S.cycles) : left (S.homologyπ x) = b x :=
    ConcreteCategory.congr_hom (S.π_descHomology (ModuleCat.ofHom b) (by
      ext x y
      exact flatHomogeneousCycleCupClass_boundary_left A B p q x y)) x
  have right_boundary (x : S.homology) (y : T.X₁) : left x (T.toCycles y) = 0 := by
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance x
    rw [left_pi]
    exact flatHomogeneousCycleCupClass_boundary_right A B p q z y
  let right : S.homology → T.homology →ₗ[R] P := fun x =>
    (T.descHomology (ModuleCat.ofHom (left x)) (by
      ext y
      exact right_boundary x y)).hom
  have right_pi (x : S.homology) (y : T.cycles) : right x (T.homologyπ y) = left x y :=
    ConcreteCategory.congr_hom (T.π_descHomology (ModuleCat.ofHom (left x)) (by
      ext y
      exact right_boundary x y)) y
  exact
    { toFun := right
      map_add' := by
        intro x x'
        apply LinearMap.ext
        intro y
        obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).mp inferInstance y
        calc
          _ = left (x + x') z := right_pi (x + x') z
          _ = left x z + left x' z := by rw [map_add]; rfl
          _ = _ := congrArg₂ (· + ·) (right_pi x z).symm (right_pi x' z).symm
      map_smul' := by
        intro r x
        apply LinearMap.ext
        intro y
        obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).mp inferInstance y
        calc
          _ = left (r • x) z := right_pi (r • x) z
          _ = r • left x z := by rw [map_smul]; rfl
          _ = _ := congrArg (r • ·) (right_pi x z).symm }

/-- The flat homology cup preserves both original cycle projections. -/
theorem flatHomogeneousModuleCupLinear_pi
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ)
    (x : (flatHomogeneousModuleComplex A).cycles p) (y : (flatHomogeneousModuleComplex B).cycles q) :
    flatHomogeneousModuleCupLinear A B p q ((flatHomogeneousModuleComplex A).homologyπ p x)
      ((flatHomogeneousModuleComplex B).homologyπ q y) =
      (flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).homologyπ (p + q)
        (flatHomogeneousCycleCupLinear A B p q x y) := by
  let S := (flatHomogeneousModuleComplex A).sc p
  let T := (flatHomogeneousModuleComplex B).sc q
  let P := (flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).homology (p + q)
  let b : S.cycles →ₗ[R] T.cycles →ₗ[R] P := flatHomogeneousCycleCupClass A B p q
  have hS : S.toCycles ≫ ModuleCat.ofHom b = 0 := by
    ext z y
    exact flatHomogeneousCycleCupClass_boundary_left A B p q z y
  let left : S.homology →ₗ[R] T.cycles →ₗ[R] P :=
    (S.descHomology (ModuleCat.ofHom b) hS).hom
  have hx : left (S.homologyπ x) = b x := descHomology_apply S (ModuleCat.ofHom b) hS x
  have hT : T.toCycles ≫ ModuleCat.ofHom (left (S.homologyπ x)) = 0 := by
    ext z
    rw [hx]
    exact flatHomogeneousCycleCupClass_boundary_right A B p q x z
  change (T.descHomology (ModuleCat.ofHom (left (S.homologyπ x))) hT).hom (T.homologyπ y) =
    b x y
  exact (descHomology_apply T (ModuleCat.ofHom (left (S.homologyπ x))) hT y).trans
    (congrArg (fun f : T.cycles →ₗ[R] P => f y) hx)

/-- The genuine native-to-flat homology comparison after forgetting only topology. -/
def homogeneousNativeModuleHomologyIso
    (X : TopRep.{max v w, u, v} R G) (p : ℕ) :
    (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).obj
      (continuousCohomology p X) ≅ (flatHomogeneousModuleComplex X).homology p :=
  (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).mapIso
    ((HomologicalComplex.homologyFunctor (TopModuleCat.{max v w} R)
      (ComplexShape.up ℕ) p).mapIso (homogeneousFlatComplexIso X)) ≪≫
    (((flatHomogeneousComplex X).sc p).mapHomologyIso
      (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R))).symm

/-- The genuine native-to-flat cycle comparison after forgetting only topology. -/
def homogeneousNativeModuleCyclesIso
    (X : TopRep.{max v w, u, v} R G) (p : ℕ) :
    (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).obj
      (cocycles X p) ≅ (flatHomogeneousModuleComplex X).cycles p :=
  (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).mapIso
    ((HomologicalComplex.cyclesFunctor (TopModuleCat.{max v w} R)
      (ComplexShape.up ℕ) p).mapIso (homogeneousFlatComplexIso X)) ≪≫
    (((flatHomogeneousComplex X).sc p).mapCyclesIso
      (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R))).symm

/-- Cup on the original native continuous cohomology of arbitrary discrete coefficients. -/
def discreteContinuousCup
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ) :
    continuousCohomology p A →ₗ[R] continuousCohomology q B →ₗ[R]
      continuousCohomology (p + q) (discreteTensorCoefficient A B) :=
  (((flatHomogeneousModuleCupLinear A B p q).compr₂
    (homogeneousNativeModuleHomologyIso (discreteTensorCoefficient A B) (p + q)).inv.hom).compl₂
      (homogeneousNativeModuleHomologyIso B q).hom.hom).comp
        (homogeneousNativeModuleHomologyIso A p).hom.hom

/-- The tensor cup on the original native cohomology carriers in all nonnegative degrees. -/
def discreteContinuousCupTensorMap
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ) :
    ModuleCat.of R (TensorProduct R (continuousCohomology p A) (continuousCohomology q B)) ⟶
      ModuleCat.of R (continuousCohomology (p + q) (discreteTensorCoefficient A B)) :=
  ModuleCat.ofHom (TensorProduct.lift (discreteContinuousCup A B p q))

private theorem forgetTopModule_pi
    (S : ShortComplex (TopModuleCat.{a} R)) :
    (S.map (forget₂ (TopModuleCat.{a} R) (ModuleCat.{a} R))).homologyπ ≫
        (S.mapHomologyIso (forget₂ (TopModuleCat.{a} R) (ModuleCat.{a} R))).hom =
      (S.mapCyclesIso (forget₂ (TopModuleCat.{a} R) (ModuleCat.{a} R))).hom ≫
        (forget₂ (TopModuleCat.{a} R) (ModuleCat.{a} R)).map S.homologyπ := by
  let F := forget₂ (TopModuleCat.{a} R) (ModuleCat.{a} R)
  let h := S.homologyData.left
  have h₁ : (S.map F).homologyπ ≫ (h.map F).homologyIso.hom =
      (h.map F).cyclesIso.hom ≫ F.map h.π :=
    (h.map F).homologyπ_comp_homologyIso_hom
  have h₂ : F.map h.π ≫ F.map h.homologyIso.inv =
      F.map h.cyclesIso.inv ≫ F.map S.homologyπ :=
    (F.map_comp h.π h.homologyIso.inv).symm.trans
      ((F.congr_map h.π_comp_homologyIso_inv).trans
        (F.map_comp h.cyclesIso.inv S.homologyπ))
  have hc : (S.map F).homologyπ ≫
      ((h.map F).homologyIso.hom ≫ F.map h.homologyIso.inv) =
      ((h.map F).cyclesIso.hom ≫ F.map h.cyclesIso.inv) ≫ F.map S.homologyπ :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ F.map h.homologyIso.inv) h₁).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => (h.map F).cyclesIso.hom ≫ k) h₂).trans
            (Category.assoc _ _ _).symm)))
  have hh : (S.mapHomologyIso F).hom =
      (h.map F).homologyIso.hom ≫ F.map h.homologyIso.inv :=
    congrArg (fun e : (S.map F).homology ≅ F.obj S.homology => e.hom)
      (h.mapHomologyIso_eq F)
  have hz : (S.mapCyclesIso F).hom =
      (h.map F).cyclesIso.hom ≫ F.map h.cyclesIso.inv :=
    congrArg (fun e : (S.map F).cycles ≅ F.obj S.cycles => e.hom)
      (h.mapCyclesIso_eq F)
  exact (congrArg (fun k => (S.map F).homologyπ ≫ k) hh).trans
    (hc.trans (congrArg (fun k => k ≫ F.map S.homologyπ) hz.symm))

private theorem forgetTopModule_pi_inverse
    (S : ShortComplex (TopModuleCat.{a} R)) :
    (forget₂ (TopModuleCat.{a} R) (ModuleCat.{a} R)).map S.homologyπ ≫
        (S.mapHomologyIso (forget₂ (TopModuleCat.{a} R) (ModuleCat.{a} R))).inv =
      (S.mapCyclesIso (forget₂ (TopModuleCat.{a} R) (ModuleCat.{a} R))).inv ≫
        (S.map (forget₂ (TopModuleCat.{a} R) (ModuleCat.{a} R))).homologyπ := by
  let F := forget₂ (TopModuleCat.{a} R) (ModuleCat.{a} R)
  change F.map S.homologyπ ≫ (S.mapHomologyIso F).inv =
    (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ
  calc
    _ = (S.mapCyclesIso F).inv ≫
        ((S.mapCyclesIso F).hom ≫ F.map S.homologyπ) ≫ (S.mapHomologyIso F).inv := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = (S.mapCyclesIso F).inv ≫
        ((S.map F).homologyπ ≫ (S.mapHomologyIso F).hom) ≫ (S.mapHomologyIso F).inv := by
      rw [forgetTopModule_pi]
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The native-to-flat comparison preserves the original homology projection. -/
theorem homogeneousNativeModuleHomologyIso_pi
    (X : TopRep.{max v w, u, v} R G) (p : ℕ) :
    (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).map (π X p) ≫
        (homogeneousNativeModuleHomologyIso X p).hom =
      (homogeneousNativeModuleCyclesIso X p).hom ≫ (flatHomogeneousModuleComplex X).homologyπ p := by
  let F := forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)
  let S := (flatHomogeneousComplex X).sc p
  have h : F.map (π X p) ≫
      F.map (HomologicalComplex.homologyMap (homogeneousFlatComplexIso X).hom p) =
      F.map (HomologicalComplex.cyclesMap (homogeneousFlatComplexIso X).hom p) ≫
        F.map S.homologyπ :=
    (F.map_comp _ _).symm.trans
      ((F.congr_map (HomologicalComplex.homologyπ_naturality
        (homogeneousFlatComplexIso X).hom p)).trans (F.map_comp _ _))
  have h' := congrArg
    (fun m : F.obj (cocycles X p) ⟶ F.obj S.homology =>
      m ≫ (S.mapHomologyIso F).inv) h
  have k := congrArg
    (fun m : F.obj S.cycles ⟶ (S.map F).homology =>
      F.map (HomologicalComplex.cyclesMap (homogeneousFlatComplexIso X).hom p) ≫ m)
    (forgetTopModule_pi_inverse S)
  change F.map (π X p) ≫
      (F.map (HomologicalComplex.homologyMap (homogeneousFlatComplexIso X).hom p) ≫
        (S.mapHomologyIso F).inv) =
    (F.map (HomologicalComplex.cyclesMap (homogeneousFlatComplexIso X).hom p) ≫
      (S.mapCyclesIso F).inv) ≫ (S.map F).homologyπ
  exact (Category.assoc _ _ _).symm.trans
    (h'.trans ((Category.assoc _ _ _).trans (k.trans (Category.assoc _ _ _).symm)))

/-- The comparison preserves every original native cycle class value. -/
theorem homogeneousNativeModuleHomologyIso_pi_value
    (X : TopRep.{max v w, u, v} R G) (p : ℕ) (z : cocycles X p) :
    (homogeneousNativeModuleHomologyIso X p).hom.hom (π X p z) =
      ((flatHomogeneousModuleComplex X).homologyπ p).hom
        ((homogeneousNativeModuleCyclesIso X p).hom.hom z) := by
  exact ConcreteCategory.congr_hom (homogeneousNativeModuleHomologyIso_pi X p) z

private theorem homogeneousNativeModuleHomologyIso_pi_inverse
    (X : TopRep.{max v w, u, v} R G) (p : ℕ) :
    (flatHomogeneousModuleComplex X).homologyπ p ≫ (homogeneousNativeModuleHomologyIso X p).inv =
      (homogeneousNativeModuleCyclesIso X p).inv ≫
        (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).map (π X p) := by
  calc
    _ = (homogeneousNativeModuleCyclesIso X p).inv ≫
        ((homogeneousNativeModuleCyclesIso X p).hom ≫ (flatHomogeneousModuleComplex X).homologyπ p) ≫
          (homogeneousNativeModuleHomologyIso X p).inv := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = (homogeneousNativeModuleCyclesIso X p).inv ≫
        ((forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).map (π X p) ≫
          (homogeneousNativeModuleHomologyIso X p).hom) ≫ (homogeneousNativeModuleHomologyIso X p).inv := by
      rw [← homogeneousNativeModuleHomologyIso_pi]
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The cup of original native cocycles, transported through the genuine flat complex comparison. -/
def discreteContinuousCupCocycles
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ) :
    cocycles A p →ₗ[R] cocycles B q →ₗ[R]
      cocycles (discreteTensorCoefficient A B) (p + q) :=
  (((flatHomogeneousCycleCupLinear A B p q).compr₂
    (homogeneousNativeModuleCyclesIso (discreteTensorCoefficient A B) (p + q)).inv.hom).compl₂
      (homogeneousNativeModuleCyclesIso B q).hom.hom).comp
        (homogeneousNativeModuleCyclesIso A p).hom.hom

/-- The native cup of two original cycle classes equals the original projection of their cup. -/
theorem discreteContinuousCup_pi
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (p q : ℕ)
    (x : cocycles A p) (y : cocycles B q) :
    discreteContinuousCup A B p q (π A p x) (π B q y) =
      π (discreteTensorCoefficient A B) (p + q) (discreteContinuousCupCocycles A B p q x y) := by
  change (homogeneousNativeModuleHomologyIso (discreteTensorCoefficient A B) (p + q)).inv.hom
      (flatHomogeneousModuleCupLinear A B p q
        ((homogeneousNativeModuleHomologyIso A p).hom.hom (π A p x))
        ((homogeneousNativeModuleHomologyIso B q).hom.hom (π B q y))) = _
  rw [homogeneousNativeModuleHomologyIso_pi_value, homogeneousNativeModuleHomologyIso_pi_value, flatHomogeneousModuleCupLinear_pi]
  exact ConcreteCategory.congr_hom
    (homogeneousNativeModuleHomologyIso_pi_inverse (discreteTensorCoefficient A B) (p + q))
    (flatHomogeneousCycleCupLinear A B p q ((homogeneousNativeModuleCyclesIso A p).hom.hom x)
      ((homogeneousNativeModuleCyclesIso B q).hom.hom y))


/-- The genuine native-to-flat cycle comparison preserves the original cycle inclusion. -/
theorem homogeneousNativeModuleCyclesIso_iCycles
    (X : TopRep.{max v w, u, v} R G) (p : ℕ) :
    (homogeneousNativeModuleCyclesIso X p).hom ≫
        (flatHomogeneousModuleComplex X).iCycles p =
      (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).map
        ((TopRep.homogeneousCochains X).iCycles p) ≫
      (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).map
        ((homogeneousFlatComplexIso X).hom.f p) := by
  let F := forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)
  let S := (flatHomogeneousComplex X).sc p
  have hi : (S.mapCyclesIso F).inv ≫ (S.map F).iCycles = F.map S.iCycles := by
    calc
      _ = (S.mapCyclesIso F).inv ≫ ((S.mapCyclesIso F).hom ≫ F.map S.iCycles) :=
        congrArg (fun k => (S.mapCyclesIso F).inv ≫ k)
          (S.mapCyclesIso_hom_iCycles F).symm
      _ = _ := by simp only [Iso.inv_hom_id_assoc]
  have hn : F.map (HomologicalComplex.cyclesMap (homogeneousFlatComplexIso X).hom p) ≫
      F.map S.iCycles = F.map ((TopRep.homogeneousCochains X).iCycles p) ≫
        F.map ((homogeneousFlatComplexIso X).hom.f p) :=
    (F.map_comp _ _).symm.trans
      ((F.congr_map (HomologicalComplex.cyclesMap_i (homogeneousFlatComplexIso X).hom p)).trans
        (F.map_comp _ _))
  change (F.map (HomologicalComplex.cyclesMap (homogeneousFlatComplexIso X).hom p) ≫
      (S.mapCyclesIso F).inv) ≫ (S.map F).iCycles = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k =>
      F.map (HomologicalComplex.cyclesMap (homogeneousFlatComplexIso X).hom p) ≫ k) hi).trans hn)

/-- The cycle comparison preserves every original finite-tuple value. -/
theorem homogeneousNativeModuleCyclesIso_tuple_value
    (X : TopRep.{max v w, u, v} R G) (p : ℕ) (z : cocycles X p)
    (t : Fin (p + 1) → G) :
    (((flatHomogeneousModuleComplex X).iCycles p).hom
      ((homogeneousNativeModuleCyclesIso X p).hom.hom z)).val t =
      resolutionFinUncurry X (p + 1) (((TopRep.homogeneousCochains X).iCycles p z).val) t := by
  have h := ConcreteCategory.congr_hom (homogeneousNativeModuleCyclesIso_iCycles X p) z
  exact (congrArg (fun c : flatHomogeneousCochains X p => c.val t) h).trans
    (homogeneousFlatComplexIso_hom_apply X p ((TopRep.homogeneousCochains X).iCycles p z) t)

/-- The original native cycle cup is the tensor of the original front and back tuple values. -/
theorem discreteContinuousCupCocycles_tuple_value
    (A B : TopRep.{max v w, u, v} R G) [DiscreteTopology A] [DiscreteTopology B]
    (p q : ℕ) (x : cocycles A p) (y : cocycles B q) (t : Fin (p + q + 1) → G) :
    resolutionFinUncurry (discreteTensorCoefficient A B) (p + q + 1)
        (((TopRep.homogeneousCochains (discreteTensorCoefficient A B)).iCycles (p + q)
          (discreteContinuousCupCocycles A B p q x y)).val) t =
      resolutionFinUncurry A (p + 1) (((TopRep.homogeneousCochains A).iCycles p x).val)
          (homogeneousCupFront p q t) ⊗ₜ[R]
      resolutionFinUncurry B (q + 1) (((TopRep.homogeneousCochains B).iCycles q y).val)
          (homogeneousCupBack p q t) := by
  let xx := (homogeneousNativeModuleCyclesIso A p).hom.hom x
  let yy := (homogeneousNativeModuleCyclesIso B q).hom.hom y
  have hc : (homogeneousNativeModuleCyclesIso (discreteTensorCoefficient A B) (p + q)).hom.hom
      (discreteContinuousCupCocycles A B p q x y) =
      flatHomogeneousCycleCupLinear A B p q xx yy := by
    exact ConcreteCategory.congr_hom
      (homogeneousNativeModuleCyclesIso (discreteTensorCoefficient A B) (p + q)).inv_hom_id
      (flatHomogeneousCycleCupLinear A B p q xx yy)
  have h := homogeneousNativeModuleCyclesIso_tuple_value (discreteTensorCoefficient A B) (p + q)
    (discreteContinuousCupCocycles A B p q x y) t
  have h₁ := congrArg
    (fun z : (flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).cycles (p + q) =>
      (((flatHomogeneousModuleComplex (discreteTensorCoefficient A B)).iCycles (p + q)).hom z).val t) hc
  have h₂ := congrArg
    (fun z : flatHomogeneousCochains (discreteTensorCoefficient A B) (p + q) => z.val t)
    (flatHomogeneousCycleCupRight_iCycles A B p q xx yy)
  have h₃ := flatHomogeneousCup_apply A B p q
    (((flatHomogeneousModuleComplex A).iCycles p).hom xx)
    (((flatHomogeneousModuleComplex B).iCycles q).hom yy) t
  exact h.symm.trans (h₁.trans (h₂.trans (h₃.trans
    (congrArg₂ (fun a b => a ⊗ₜ[R] b)
      (homogeneousNativeModuleCyclesIso_tuple_value A p x (homogeneousCupFront p q t))
      (homogeneousNativeModuleCyclesIso_tuple_value B q y (homogeneousCupBack p q t))))))

/-- The original cochain coefficient map acts on every tuple by its original coefficient morphism. -/
theorem cochainsMap_id_tuple_value
    {A A' : TopRep.{max v w, u, v} R G} (f : A ⟶ A') (n : ℕ)
    (c : (TopRep.homogeneousCochains A).X n) (t : Fin (n + 1) → G) :
    resolutionFinUncurry A' (n + 1)
        (((cochainsMap (ContinuousMonoidHom.id G) f).f n c).val) t =
      f.hom (resolutionFinUncurry A (n + 1) c.val t) := by
  change resolutionFinUncurry A' (n + 1)
      ((resolutionMap (ContinuousMonoidHom.id G) f (n + 1)).hom c.val) t = _
  exact resolutionFinUncurry_resolutionMap (ContinuousMonoidHom.id G)
    f (n + 1) c.val t

/-- The original cycle coefficient map preserves the same literal finite-tuple formula. -/
theorem cocyclesMap_id_tuple_value
    {A A' : TopRep.{max v w, u, v} R G} (f : A ⟶ A') (n : ℕ)
    (z : cocycles A n) (t : Fin (n + 1) → G) :
    resolutionFinUncurry A' (n + 1)
        (((TopRep.homogeneousCochains A').iCycles n
          (cocyclesMap (ContinuousMonoidHom.id G) f n z)).val) t =
      f.hom (resolutionFinUncurry A (n + 1) (((TopRep.homogeneousCochains A).iCycles n z).val) t) := by
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (cochainsMap (ContinuousMonoidHom.id G) f) n) z
  exact (congrArg (fun c : (TopRep.homogeneousCochains A').X n =>
      resolutionFinUncurry A' (n + 1) c.val t) h).trans
    (cochainsMap_id_tuple_value f n ((TopRep.homogeneousCochains A).iCycles n z) t)

private theorem nativeCycles_ext
    (X : TopRep.{max v w, u, v} R G) (n : ℕ) (z z' : cocycles X n)
    (h : ∀ t : Fin (n + 1) → G,
      resolutionFinUncurry X (n + 1) (((TopRep.homogeneousCochains X).iCycles n z).val) t =
      resolutionFinUncurry X (n + 1) (((TopRep.homogeneousCochains X).iCycles n z').val) t) :
    z = z' := by
  apply (ModuleCat.mono_iff_injective (homogeneousNativeModuleCyclesIso X n).hom).mp inferInstance
  apply (ModuleCat.mono_iff_injective ((flatHomogeneousModuleComplex X).iCycles n)).mp inferInstance
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact (homogeneousNativeModuleCyclesIso_tuple_value X n z t).trans
    ((h t).trans (homogeneousNativeModuleCyclesIso_tuple_value X n z' t).symm)

/-- The original native cycle cup is natural in both coefficient morphisms. -/
theorem discreteContinuousCupCocycles_naturality
    {A B A' B' : TopRep.{max v w, u, v} R G}
    [DiscreteTopology A] [DiscreteTopology B] [DiscreteTopology A'] [DiscreteTopology B']
    (f : A ⟶ A') (g : B ⟶ B') (p q : ℕ) (x : cocycles A p) (y : cocycles B q) :
    cocyclesMap (X := discreteTensorCoefficient A B) (Y := discreteTensorCoefficient A' B')
      (ContinuousMonoidHom.id G) (discreteTensorCoefficientMap f g)
        (p + q) (discreteContinuousCupCocycles A B p q x y) =
      discreteContinuousCupCocycles A' B' p q
        (cocyclesMap (ContinuousMonoidHom.id G) f p x)
        (cocyclesMap (ContinuousMonoidHom.id G) g q y) := by
  apply nativeCycles_ext (discreteTensorCoefficient A' B') (p + q)
  intro t
  have h₁ := cocyclesMap_id_tuple_value (discreteTensorCoefficientMap f g) (p + q)
    (discreteContinuousCupCocycles A B p q x y) t
  have h₂ := congrArg (discreteTensorCoefficientMap f g).hom (discreteContinuousCupCocycles_tuple_value A B p q x y t)
  have h₃ := discreteTensorCoefficientMap_tmul f g
    (resolutionFinUncurry A (p + 1) (((TopRep.homogeneousCochains A).iCycles p x).val)
      (homogeneousCupFront p q t))
    (resolutionFinUncurry B (q + 1) (((TopRep.homogeneousCochains B).iCycles q y).val)
      (homogeneousCupBack p q t))
  have h₄ := congrArg₂ (fun a b => a ⊗ₜ[R] b)
    (cocyclesMap_id_tuple_value f p x (homogeneousCupFront p q t)).symm
    (cocyclesMap_id_tuple_value g q y (homogeneousCupBack p q t)).symm
  exact h₁.trans (h₂.trans (h₃.trans
    (h₄.trans (discreteContinuousCupCocycles_tuple_value A' B' p q _ _ t).symm)))

private theorem nativePi_surjective
    (X : TopRep.{max v w, u, v} R G) (n : ℕ) : Function.Surjective (π X n) := by
  exact (ModuleCat.epi_iff_surjective
    ((forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).map (π X n))).mp inferInstance

private theorem coefficientH_pi
    {A A' : TopRep.{max v w, u, v} R G} (f : A ⟶ A') (n : ℕ) (z : cocycles A n) :
    ContinuousCohomology.map (ContinuousMonoidHom.id G) f n (π A n z) =
      π A' n (cocyclesMap (ContinuousMonoidHom.id G) f n z) := by
  exact ConcreteCategory.congr_hom (π_map (ContinuousMonoidHom.id G) f n) z

/-- The original native cohomology cup commutes with both actual coefficient maps. -/
theorem discreteContinuousCup_naturality
    {A B A' B' : TopRep.{max v w, u, v} R G}
    [DiscreteTopology A] [DiscreteTopology B] [DiscreteTopology A'] [DiscreteTopology B']
    (f : A ⟶ A') (g : B ⟶ B') (p q : ℕ)
    (a : continuousCohomology p A) (b : continuousCohomology q B) :
    ContinuousCohomology.map (X := discreteTensorCoefficient A B)
        (Y := discreteTensorCoefficient A' B') (ContinuousMonoidHom.id G)
        (discreteTensorCoefficientMap f g) (p + q)
        (discreteContinuousCup A B p q a b) =
      discreteContinuousCup A' B' p q
        (ContinuousCohomology.map (ContinuousMonoidHom.id G) f p a)
        (ContinuousCohomology.map (ContinuousMonoidHom.id G) g q b) := by
  obtain ⟨x, rfl⟩ := nativePi_surjective A p a
  obtain ⟨y, rfl⟩ := nativePi_surjective B q b
  calc
    _ = ContinuousCohomology.map (X := discreteTensorCoefficient A B)
        (Y := discreteTensorCoefficient A' B') (ContinuousMonoidHom.id G)
        (discreteTensorCoefficientMap f g) (p + q)
        (π (discreteTensorCoefficient A B) (p + q) (discreteContinuousCupCocycles A B p q x y)) :=
      congrArg (ContinuousCohomology.map (X := discreteTensorCoefficient A B)
        (Y := discreteTensorCoefficient A' B') (ContinuousMonoidHom.id G)
        (discreteTensorCoefficientMap f g) (p + q)) (discreteContinuousCup_pi A B p q x y)
    _ = π (discreteTensorCoefficient A' B') (p + q)
        (cocyclesMap (X := discreteTensorCoefficient A B) (Y := discreteTensorCoefficient A' B')
      (ContinuousMonoidHom.id G) (discreteTensorCoefficientMap f g)
          (p + q) (discreteContinuousCupCocycles A B p q x y)) :=
      coefficientH_pi (discreteTensorCoefficientMap f g) (p + q) _
    _ = π (discreteTensorCoefficient A' B') (p + q)
        (discreteContinuousCupCocycles A' B' p q
          (cocyclesMap (ContinuousMonoidHom.id G) f p x)
          (cocyclesMap (ContinuousMonoidHom.id G) g q y)) :=
      congrArg (π (discreteTensorCoefficient A' B') (p + q)) (discreteContinuousCupCocycles_naturality f g p q x y)
    _ = discreteContinuousCup A' B' p q
        (π A' p (cocyclesMap (ContinuousMonoidHom.id G) f p x))
        (π B' q (cocyclesMap (ContinuousMonoidHom.id G) g q y)) :=
      (discreteContinuousCup_pi A' B' p q _ _).symm
    _ = _ := congrArg₂ (fun a b => discreteContinuousCup A' B' p q a b)
      (coefficientH_pi f p x).symm (coefficientH_pi g q y).symm

/-- The tensor cup map evaluates every pure tensor by the original native cup. -/
theorem discreteContinuousCupTensorMap_tmul
    (A B : TopRep.{max v w, u, v} R G) [DiscreteTopology A] [DiscreteTopology B]
    (p q : ℕ) (a : continuousCohomology p A) (b : continuousCohomology q B) :
    (discreteContinuousCupTensorMap A B p q).hom (a ⊗ₜ[R] b) =
      discreteContinuousCup A B p q a b := by
  exact TensorProduct.lift.tmul a b

/-- The tensor native cohomology cup satisfies the actual coefficient-map square. -/
theorem discreteContinuousCupTensorMap_naturality
    {A B A' B' : TopRep.{max v w, u, v} R G}
    [DiscreteTopology A] [DiscreteTopology B] [DiscreteTopology A'] [DiscreteTopology B']
    (f : A ⟶ A') (g : B ⟶ B') (p q : ℕ) :
    ModuleCat.ofHom (TensorProduct.map
        (ContinuousCohomology.map (ContinuousMonoidHom.id G) f p).hom.toLinearMap
        (ContinuousCohomology.map (ContinuousMonoidHom.id G) g q).hom.toLinearMap) ≫
      discreteContinuousCupTensorMap A' B' p q =
    discreteContinuousCupTensorMap A B p q ≫ ModuleCat.ofHom
      (ContinuousCohomology.map (X := discreteTensorCoefficient A B)
        (Y := discreteTensorCoefficient A' B') (ContinuousMonoidHom.id G)
        (discreteTensorCoefficientMap f g) (p + q)).hom.toLinearMap := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  exact (discreteContinuousCup_naturality f g p q a b).symm


end ContinuousCohomology
