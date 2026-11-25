/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferCupOneAnyProjection
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Tactic.NormNum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory
open scoped BigOperators

-- The canonical left projection formula also applies beyond the low degrees.
open groupCohomology in
example {k G : Type} [CommRing k] [Group G] (H : Subgroup G) [H.FiniteIndex]
    (A B : Rep k G) (x : H1 A)
    (y : groupCohomology (Rep.res H.subtype B) 4) :
    schreierCorestriction H (A ⊗ B) 5
      (groupCohomology.map (MonoidHom.id H)
        (Rep.resTensorIso H.subtype A B).hom 5
        (cupOneAny (Rep.res H.subtype A) (Rep.res H.subtype B) 4
          (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) 1 x ⊗ₜ[k] y))) =
      cupOneAny A B 4 (x ⊗ₜ[k] schreierCorestriction H B 4 y) :=
  schreierCorestriction_cup_one_any A B 4 x y

namespace groupCohomology.SchreierSignClient

private abbrev G := ℤˣ
private abbrev H : Subgroup G := ⊥

-- The same canonical Rep.of scalar action used by the existing Main
-- ProfiniteCoefficientConnectorStageTests sign fixture.
private abbrev A : Rep ℤ G := Rep.of
  { toFun u := (u : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)
    map_one' := by
      apply LinearMap.ext
      intro z
      change (1 : ℤ) • z = z
      exact one_smul ℤ z
    map_mul' := by
      intro u v
      apply LinearMap.ext
      intro z
      change ((u * v : G) : ℤ) • z = (u : ℤ) • ((v : ℤ) • z)
      rw [Units.val_mul, mul_smul] }

private abbrev B : Rep ℤ G := 𝟙_ (Rep ℤ G)

private def T : H.RightTransversal :=
  ⟨Set.univ, by
    change Subgroup.IsComplement' (⊥ : Subgroup G) ⊤
    exact Subgroup.isComplement'_bot_top⟩

-- Match the provider's ofFinite construction instead of depending on a
-- different synthesized Fintype for a subtype of univ.
noncomputable local instance signTransversalFintype : Fintype (T : Set G) :=
  Fintype.ofFinite _

private lemma minus_ne_one : (-1 : G) ≠ 1 := by
  intro h
  have hv := congrArg (fun u : G => (u : ℤ)) h
  change (-1 : ℤ) = 1 at hv
  norm_num at hv

private lemma minus_mul_minus : (-1 : G) * (-1) = 1 := by
  apply Units.ext
  change (-1 : ℤ) * (-1) = 1
  norm_num

private lemma inverse_minus : (-1 : G)⁻¹ = -1 := by
  apply Units.ext
  rfl

private lemma rhoA_apply (u : G) (z : ℤ) :
    A.ρ u z = (u : ℤ) * z := by
  change (u : ℤ) • z = (u : ℤ) * z
  exact Int.zsmul_eq_mul _ _

private lemma rhoB_apply (u : G) (z : ℤ) : B.ρ u z = z := by
  change ((Representation.trivial ℤ G ℤ) u) z = z
  rfl

private def rawX (u : G) : ℤ := if u = 1 then 0 else 1

private lemma rawX_one : rawX (1 : G) = 0 := by
  simp [rawX]

private lemma rawX_minus : rawX (-1 : G) = 1 := by
  simp [rawX]

private def x : cocycles₁ A :=
  ⟨rawX, (mem_cocycles₁_iff (A := A) rawX).2 (by
    intro u v
    rw [rhoA_apply]
    rcases Int.units_eq_one_or u with rfl | rfl
    · simp only [one_mul, rawX_one, Units.val_one, add_zero]
    · rcases Int.units_eq_one_or v with rfl | rfl
      · norm_num only [mul_one, rawX_one, rawX_minus,
          Units.val_neg, Units.val_one]
      · norm_num only [minus_mul_minus, rawX_one, rawX_minus,
          Units.val_neg, Units.val_one])⟩

private lemma x_apply (u : G) : x u = rawX u := rfl

private def y : (Fin 0 → H) → B := fun _ => (1 : ℤ)

-- Use the canonical tensor right unitor for the coefficient pairing.
private abbrev μ : (A ⊗ B : Rep ℤ G) →ₗ[ℤ] A :=
  (ρ_ A).hom.hom.toLinearMap

private lemma mu_tmul (a b : ℤ) :
    μ (a ⊗ₜ[ℤ] b) = b * a := by
  change (ρ_ A).hom.hom (a ⊗ₜ[ℤ] b) = b * a
  rw [Rep.hom_hom_rightUnitor]
  change Representation.TensorProduct.rid ℤ A.ρ (a ⊗ₜ[ℤ] b) = b * a
  rw [Representation.TensorProduct.rid_apply, Int.zsmul_eq_mul]

private lemma mu_action (g : G) (v : (A ⊗ B : Rep ℤ G)) :
    μ ((A ⊗ B).ρ g v) = A.ρ g (μ v) :=
  Rep.hom_comm_apply (ρ_ A).hom g v

-- Enumerate the sum explicitly using the canonical integer-unit instance.
private lemma sumT (f : G → ℤ) :
    (∑ t : (T : Set G), f (t : G)) = f 1 + f (-1) := by
  classical
  let e : (T : Set G) ≃ G := Equiv.Set.univ G
  calc
    (∑ t : (T : Set G), f (t : G)) = ∑ u : G, f u := e.sum_comp f
    _ = f 1 + f (-1) := by
      rw [UnitsInt.univ]
      rw [Finset.sum_insert
        (by simpa only [Finset.mem_singleton] using Ne.symm minus_ne_one),
        Finset.sum_singleton]

-- Evaluate the degree-zero differential on its unique empty tuple.
private lemma d0_apply {J : Type} [Group J]
    (C : Rep ℤ J) (f : (Fin 0 → J) → C) (g : Fin 1 → J) :
    (inhomogeneousCochains.d C 0).hom f g =
      C.ρ (g 0) (f Fin.elim0) - f Fin.elim0 := by
  rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_one]
  have htail : (fun i : Fin 0 => g i.succ) = Fin.elim0 :=
    Subsingleton.elim _ _
  have hface :
      Fin.contractNth (0 : Fin 1) (fun a b : J => a * b) g = Fin.elim0 :=
    Subsingleton.elim _ _
  rw [htail, hface]
  simp only [Fin.val_zero, zero_add, pow_one, neg_one_smul, sub_eq_add_neg]

private lemma y_cycle :
    (inhomogeneousCochains.d (Rep.res H.subtype B) 0).hom y = 0 := by
  funext g
  rw [d0_apply]
  change (B.ρ (g 0 : G) (1 : ℤ) : ℤ) - (1 : ℤ) = 0
  rw [rhoB_apply, sub_self]

private abbrev homotopy : (Fin 0 → G) → (A ⊗ B : Rep ℤ G) :=
  cupProjectionHomotopyOneAny A B T 0 x y

private lemma term_mu (t : (T : Set G)) (g : Fin 0 → G) :
    μ (cupProjectionHomotopyOneAnyTerm A B T 0 x y t g) =
      (↑((t : G)⁻¹) : ℤ) * rawX (t : G) := by
  change μ (A.ρ ((t : G)⁻¹) (rawX (t : G)) ⊗ₜ[ℤ] (1 : ℤ)) = _
  calc
    _ = (1 : ℤ) * A.ρ ((t : G)⁻¹) (rawX (t : G)) :=
      mu_tmul (A.ρ ((t : G)⁻¹) (rawX (t : G))) 1
    _ = (↑((t : G)⁻¹) : ℤ) * rawX (t : G) := by
      change 1 * ((↑((t : G)⁻¹) : ℤ) * rawX (t : G)) = _
      ring

private lemma homotopy_mu (g : Fin 0 → G) :
    μ (homotopy g) = (-1 : ℤ) := by
  change μ (cupProjectionHomotopyOneAny A B T 0 x y g) = -1
  rw [cupProjectionHomotopyOneAny_apply, map_sum]
  calc
    _ = ∑ t : (T : Set G), (↑((t : G)⁻¹) : ℤ) * rawX (t : G) :=
      Finset.sum_congr rfl (fun t _ => term_mu t g)
    _ = (-1 : ℤ) := by
      have h := sumT (fun t : G => (↑t⁻¹ : ℤ) * rawX t)
      exact h.trans (by norm_num [inverse_minus, rawX_one, rawX_minus])

private def minusTuple : Fin 1 → G := fun _ => -1

private lemma boundary_mu :
    μ ((inhomogeneousCochains.d (A ⊗ B) 0).hom homotopy minusTuple) = 2 := by
  rw [d0_apply, map_sub, mu_action]
  change A.ρ (-1) (μ (homotopy Fin.elim0)) - μ (homotopy Fin.elim0) = 2
  calc
    _ = A.ρ (-1) (-1 : ℤ) - (-1 : ℤ) :=
      congrArg (fun z : ℤ => A.ρ (-1) z - z) (homotopy_mu Fin.elim0)
    _ = (2 : ℤ) := by
      change (-1 : ℤ) * (-1) - (-1) = 2
      norm_num

private lemma norm_y (g : Fin 0 → G) :
    corestrictionCochain B T 0 y g = (2 : ℤ) := by
  rw [corestrictionCochain_apply]
  have hterm (t : (T : Set G)) :
      B.ρ (t : G)⁻¹ (y (T.schreierFactorTuple t g)) = (1 : ℤ) := by
    simp only [y, rhoB_apply]
  simp_rw [hterm]
  change (∑ t : (T : Set G), (fun _ : G => (1 : ℤ)) (t : G)) = 2
  exact sumT (fun _ : G => (1 : ℤ))

private lemma restricted_x_zero (h : H) : x (h : G) = 0 := by
  have hh : (h : G) = 1 := Subgroup.mem_bot.mp h.property
  rw [hh, x_apply, rawX_one]

private abbrev transferredLeft : (Fin 1 → G) → (A ⊗ B : Rep ℤ G) :=
  corestrictionCochain (A ⊗ B) T 1
    (cupCochainOneAny (Rep.res H.subtype A) (Rep.res H.subtype B) 0
      (fun h : H => x (h : G)) y)

private abbrev projectedRight : (Fin 1 → G) → (A ⊗ B : Rep ℤ G) :=
  cupCochainOneAny A B 0 x (corestrictionCochain B T 0 y)

private lemma left_mu : μ (transferredLeft minusTuple) = (0 : ℤ) := by
  have hzero :
      (cupCochainOneAny (Rep.res H.subtype A) (Rep.res H.subtype B) 0
        (fun h : H => x (h : G)) y :
        (Fin 1 → H) → (A ⊗ B : Rep ℤ G)) = 0 := by
    funext g
    simp only [cupCochainOneAny_apply, restricted_x_zero,
      TensorProduct.zero_tmul, Pi.zero_apply]
  simp only [transferredLeft, hzero, map_zero, Pi.zero_apply]

private lemma right_mu : μ (projectedRight minusTuple) = (2 : ℤ) := by
  norm_num only [projectedRight, cupCochainOneAny_apply, minusTuple,
    x_apply, rawX_minus, rhoB_apply, norm_y, mu_tmul]

-- Apply the public cochain equation and verify its nonzero boundary correction.
example :
    μ (transferredLeft minusTuple) =
        μ (projectedRight minusTuple) -
          μ ((inhomogeneousCochains.d (A ⊗ B) 0).hom homotopy minusTuple) ∧
      μ (transferredLeft minusTuple) = 0 ∧
      μ (projectedRight minusTuple) = 2 ∧
      μ ((inhomogeneousCochains.d (A ⊗ B) 0).hom homotopy minusTuple) = 2 ∧
      (2 : ℤ) ≠ 0 := by
  refine ⟨?_, left_mu, right_mu, boundary_mu, by norm_num⟩
  have h := congrArg
    (fun f : (Fin 1 → G) → (A ⊗ B : Rep ℤ G) => μ (f minusTuple))
    (corestrictionCochain_cup_one_any A B T 0 x y y_cycle)
  simpa only [transferredLeft, projectedRight, homotopy, Pi.sub_apply, map_sub] using h

end groupCohomology.SchreierSignClient

end
