/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Analysis.LocallyConvex.PointwiseConvergence
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

@[expose] public section

open scoped PointwiseConvergenceCLM
open Topology

namespace MathlibExt.Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

/-- Conversion from SOT operators `H →Lₚₜ[ℂ] H` to bounded operators `H →L[ℂ] H`. -/
noncomputable abbrev toBounded {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (x : H →Lₚₜ[ℂ] H) : H →L[ℂ] H :=
  (ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) H {s : Set H | Finite s}).symm x

section KapPlumbing

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Forward map `B(H) → SOT(H)`, the inverse of `toBounded`. -/
private noncomputable def kapOfBounded (T : H →L[ℂ] H) : H →Lₚₜ[ℂ] H :=
  ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) H {s : Set H | Finite s} T

/-- Adjoint read through the SOT equivalence. -/
private noncomputable def kapStar (p : H →Lₚₜ[ℂ] H) : H →Lₚₜ[ℂ] H :=
  kapOfBounded (star (toBounded p))

private theorem kapToBounded_ofBounded (T : H →L[ℂ] H) :
    toBounded (kapOfBounded T) = T :=
  LinearEquiv.symm_apply_apply _ T

private theorem kapOfBounded_toBounded (p : H →Lₚₜ[ℂ] H) :
    kapOfBounded (toBounded p) = p :=
  LinearEquiv.apply_symm_apply _ p

private theorem kapToBounded_apply (p : H →Lₚₜ[ℂ] H) (v : H) :
    (toBounded p) v = p v :=
  ContinuousLinearMap.toUniformConvergenceCLM_symm_apply

omit [CompleteSpace H] in
private theorem kapOfBounded_apply (T : H →L[ℂ] H) (v : H) :
    (kapOfBounded T) v = T v :=
  ContinuousLinearMap.toUniformConvergenceCLM_apply

private theorem kapToBounded_add (p q : H →Lₚₜ[ℂ] H) :
    toBounded (p + q) = toBounded p + toBounded q :=
  map_add _ _ _

private theorem kapToBounded_smul (c : ℂ) (p : H →Lₚₜ[ℂ] H) :
    toBounded (c • p) = c • toBounded p :=
  map_smul _ _ _

private theorem kapToBounded_zero : toBounded (0 : H →Lₚₜ[ℂ] H) = 0 :=
  map_zero _

omit [CompleteSpace H] in
private theorem kapOfBounded_add (T U : H →L[ℂ] H) :
    kapOfBounded (T + U) = kapOfBounded T + kapOfBounded U :=
  map_add _ _ _

omit [CompleteSpace H] in
private theorem kapOfBounded_smul (c : ℂ) (T : H →L[ℂ] H) :
    kapOfBounded (c • T) = c • kapOfBounded T :=
  map_smul _ _ _

omit [CompleteSpace H] in
private theorem kapOfBounded_zero : kapOfBounded (0 : H →L[ℂ] H) = 0 :=
  map_zero _

omit [CompleteSpace H] in
private theorem kapReal_smul_sot (r : ℝ) (p : H →Lₚₜ[ℂ] H) :
    r • p = (r : ℂ) • p :=
  RCLike.real_smul_eq_coe_smul r p

omit [CompleteSpace H] in
private theorem kapReal_smul_clm (r : ℝ) (T : H →L[ℂ] H) :
    r • T = (r : ℂ) • T :=
  RCLike.real_smul_eq_coe_smul r T

private theorem kapToBounded_real_smul (r : ℝ) (p : H →Lₚₜ[ℂ] H) :
    toBounded (r • p) = r • toBounded p := by
  rw [kapReal_smul_sot, kapReal_smul_clm, kapToBounded_smul]

omit [CompleteSpace H] in
/-- `ofBounded` is continuous from the norm topology to SOT. -/
private theorem kapOfBounded_continuous :
    Continuous (kapOfBounded : (H →L[ℂ] H) → H →Lₚₜ[ℂ] H) :=
  (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H).continuous

omit [CompleteSpace H] in
/-- Evaluation at a vector is SOT-continuous. -/
private theorem kapEval_continuous (v : H) :
    Continuous (fun p : H →Lₚₜ[ℂ] H => p v) :=
  (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) H v).continuous

private theorem kapToBounded_star (p : H →Lₚₜ[ℂ] H) :
    toBounded (kapStar p) = star (toBounded p) :=
  kapToBounded_ofBounded _

private theorem kapStar_add (p q : H →Lₚₜ[ℂ] H) :
    kapStar (p + q) = kapStar p + kapStar q := by
  unfold kapStar
  rw [kapToBounded_add, star_add, kapOfBounded_add]

private theorem kapStar_real_smul (r : ℝ) (p : H →Lₚₜ[ℂ] H) :
    kapStar (r • p) = r • kapStar p := by
  unfold kapStar
  rw [kapToBounded_real_smul, kapReal_smul_clm r (toBounded p), star_smul]
  have hstar : star (r : ℂ) = (r : ℂ) := RCLike.conj_ofReal r
  rw [hstar, kapOfBounded_smul, ← kapReal_smul_sot]

private theorem kapStar_kapStar (p : H →Lₚₜ[ℂ] H) :
    kapStar (kapStar p) = p := by
  unfold kapStar
  rw [kapToBounded_ofBounded, star_star, kapOfBounded_toBounded]

private theorem kapStar_eq_iff (p : H →Lₚₜ[ℂ] H) :
    kapStar p = p ↔ IsSelfAdjoint (toBounded p) := by
  constructor
  · intro h
    rw [isSelfAdjoint_iff]
    have h2 := congrArg toBounded h
    rwa [kapToBounded_star] at h2
  · intro h
    unfold kapStar
    rw [h.star_eq, kapOfBounded_toBounded]

omit [CompleteSpace H] in
private theorem kapOfBounded_mul_post (T U : H →L[ℂ] H) :
    kapOfBounded (T * U) =
      PointwiseConvergenceCLM.postcomp H T (kapOfBounded U) := by
  rw [ContinuousLinearMap.mul_def]
  rfl

omit [CompleteSpace H] in
private theorem kapOfBounded_mul_pre (T U : H →L[ℂ] H) :
    kapOfBounded (T * U) =
      PointwiseConvergenceCLM.precomp H U (kapOfBounded T) := by
  rw [ContinuousLinearMap.mul_def]
  rfl

/-- The SOT unit ball is SOT-closed. -/
private theorem kapIsClosed_ball :
    IsClosed {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1} := by
  have hset : {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1} = ⋂ v : H, {p | ‖p v‖ ≤ ‖v‖} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [ContinuousLinearMap.opNorm_le_iff zero_le_one]
    constructor
    · intro h v
      calc ‖p v‖ = ‖(toBounded p) v‖ := by rw [kapToBounded_apply]
        _ ≤ 1 * ‖v‖ := h v
        _ = ‖v‖ := one_mul _
    · intro h v
      calc ‖(toBounded p) v‖ = ‖p v‖ := by rw [kapToBounded_apply]
        _ ≤ 1 * ‖v‖ := by rw [one_mul]; exact h v
  rw [hset]
  exact isClosed_iInter fun v =>
    isClosed_le (continuous_norm.comp (kapEval_continuous v)) continuous_const

end KapPlumbing

section KapDual

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every SOT-continuous linear functional is a finite sum of vector functionals. -/
private theorem kapExists_sum_inner (f : StrongDual ℂ (H →Lₚₜ[ℂ] H)) :
    ∃ (s : Finset H) (w : ↥s → H), ∀ p : H →Lₚₜ[ℂ] H,
      f p = ∑ x : ↥s, inner ℂ (w x) (p (x : H)) := by
  classical
  have hqq : ∀ p : H →Lₚₜ[ℂ] H,
      (normSeminorm ℂ ℂ).comp (↑f : (H →Lₚₜ[ℂ] H) →ₛₗ[RingHom.id ℂ] ℂ) p
      = ‖f p‖ := by
    intro p
    simp [Seminorm.comp_apply, coe_normSeminorm]
  have hqcont : Continuous
      ⇑((normSeminorm ℂ ℂ).comp (↑f : (H →Lₚₜ[ℂ] H) →ₛₗ[RingHom.id ℂ] ℂ)) := by
    have hfun : ⇑((normSeminorm ℂ ℂ).comp (↑f : (H →Lₚₜ[ℂ] H) →ₛₗ[RingHom.id ℂ] ℂ))
        = fun p => ‖f p‖ := funext hqq
    rw [hfun]
    exact continuous_norm.comp f.cont
  obtain ⟨s, C, hC0, hC⟩ := Seminorm.bound_of_continuous
    (PointwiseConvergenceCLM.withSeminorms :
      WithSeminorms (PointwiseConvergenceCLM.seminormFamily (RingHom.id ℂ) H H))
    _ hqcont
  set Φ : (H →Lₚₜ[ℂ] H) →ₗ[ℂ] (↥s → H) :=
    LinearMap.pi fun x : ↥s =>
      (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) H (x : H)).toLinearMap with hΦdef
  have hΦapply : ∀ (p : H →Lₚₜ[ℂ] H) (x : ↥s), Φ p x = p (x : H) := fun p x => rfl
  have hfam : ∀ (x : H) (p : H →Lₚₜ[ℂ] H),
      (PointwiseConvergenceCLM.seminormFamily (RingHom.id ℂ) H H) x p = ‖p x‖ :=
    fun x p => rfl
  have hsup : ∀ p : H →Lₚₜ[ℂ] H,
      (C • s.sup (PointwiseConvergenceCLM.seminormFamily (RingHom.id ℂ) H H)) p
        ≤ (C : ℝ) * ‖Φ p‖ := by
    intro p
    rw [smul_apply, NNReal.smul_def, smul_eq_mul]
    refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg C)
    refine Seminorm.finset_sup_apply_le (norm_nonneg _) fun x hx => ?_
    rw [hfam]
    calc ‖p x‖ = ‖Φ p ⟨x, hx⟩‖ := by rw [hΦapply]
      _ ≤ ‖Φ p‖ := norm_le_pi_norm _ _
  have hbound : ∀ p : H →Lₚₜ[ℂ] H, ‖f p‖ ≤ (C : ℝ) * ‖Φ p‖ := by
    intro p
    calc ‖f p‖ = ((normSeminorm ℂ ℂ).comp
            (↑f : (H →Lₚₜ[ℂ] H) →ₛₗ[RingHom.id ℂ] ℂ)) p := (hqq p).symm
      _ ≤ (C • s.sup
            (PointwiseConvergenceCLM.seminormFamily (RingHom.id ℂ) H H)) p :=
          Seminorm.le_def.mp hC p
      _ ≤ (C : ℝ) * ‖Φ p‖ := hsup p
  have hker : LinearMap.ker Φ ≤
      LinearMap.ker (↑f : (H →Lₚₜ[ℂ] H) →ₛₗ[RingHom.id ℂ] ℂ) := by
    intro p hp
    rw [LinearMap.mem_ker] at hp
    rw [LinearMap.mem_ker]
    have hb := hbound p
    rw [hp, norm_zero, mul_zero] at hb
    have hfp : f p = 0 := norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
    exact hfp
  set g₀ : LinearMap.range Φ →ₗ[ℂ] ℂ :=
    ((LinearMap.ker Φ).liftQ (↑f : (H →Lₚₜ[ℂ] H) →ₛₗ[RingHom.id ℂ] ℂ) hker).comp
      (LinearMap.quotKerEquivRange Φ).symm.toLinearMap with hg₀def
  have hg₀apply : ∀ (p : H →Lₚₜ[ℂ] H) (h : Φ p ∈ LinearMap.range Φ),
      g₀ ⟨Φ p, h⟩ = f p := by
    intro p h
    rw [hg₀def, LinearMap.comp_apply]
    have hsymm : ((LinearMap.quotKerEquivRange Φ).symm.toLinearMap) ⟨Φ p, h⟩
        = (LinearMap.ker Φ).mkQ p :=
      LinearMap.quotKerEquivRange_symm_apply_image Φ p h
    rw [hsymm, Submodule.mkQ_apply]
    exact Submodule.liftQ_apply _ _ _
  have hg₀bound : ∀ v : LinearMap.range Φ, ‖g₀ v‖ ≤ (C : ℝ) * ‖v‖ := by
    intro v
    obtain ⟨p, hp⟩ := v.property
    have hmem2 : Φ p ∈ LinearMap.range Φ := ⟨p, rfl⟩
    have hv : v = ⟨Φ p, hmem2⟩ := Subtype.ext hp.symm
    rw [hv, hg₀apply, ← Submodule.norm_coe]
    exact hbound p
  obtain ⟨G, hG, -⟩ := exists_extension_norm_eq (LinearMap.range Φ)
    (LinearMap.mkContinuous g₀ (C : ℝ) hg₀bound)
  have hfp : ∀ p : H →Lₚₜ[ℂ] H, f p = G (Φ p) := by
    intro p
    have hmem : Φ p ∈ LinearMap.range Φ := ⟨p, rfl⟩
    have e1 : G (Φ p) = (LinearMap.mkContinuous g₀ (C : ℝ) hg₀bound) ⟨Φ p, hmem⟩ :=
      hG ⟨Φ p, hmem⟩
    have e2 : (LinearMap.mkContinuous g₀ (C : ℝ) hg₀bound) ⟨Φ p, hmem⟩ = f p := by
      rw [LinearMap.mkContinuous_apply]
      exact hg₀apply _ _
    exact e2.symm.trans e1.symm
  refine ⟨s, fun x => (InnerProductSpace.toDual ℂ H).symm
    (ContinuousLinearMap.comp G
      (ContinuousLinearMap.single ℂ (fun _ : ↥s => H) x)), fun p => ?_⟩
  rw [hfp p, ← ContinuousLinearMap.sum_comp_single ℂ _ G (Φ p)]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact (InnerProductSpace.toDual_symm_apply).symm

end KapDual

section KapStarCont

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Precomposition with `kapStar` preserves SOT-continuity of functionals. -/
private theorem kapContinuous_starApply (f : StrongDual ℂ (H →Lₚₜ[ℂ] H)) :
    Continuous fun p : H →Lₚₜ[ℂ] H => f (kapStar p) := by
  obtain ⟨s, w, hw⟩ := kapExists_sum_inner f
  have hfun : (fun p : H →Lₚₜ[ℂ] H => f (kapStar p))
      = fun p => ∑ x : ↥s, inner ℂ (p (w x)) ((x : H)) := by
    funext p
    rw [hw]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold kapStar
    rw [kapOfBounded_apply, ContinuousLinearMap.star_eq_adjoint]
    have hadj : inner ℂ (w x) ((ContinuousLinearMap.adjoint (toBounded p)) ↑x)
        = inner ℂ ((toBounded p) (w x)) ↑x :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    rw [hadj, kapToBounded_apply]
  rw [hfun]
  exact continuous_finsetSum _ fun x _ => (kapEval_continuous (w x)).inner continuous_const

/-- Real part of `f` after `kapStar` is continuous. -/
private theorem kapContinuous_re_starApply (f : StrongDual ℂ (H →Lₚₜ[ℂ] H)) :
    Continuous fun p : H →Lₚₜ[ℂ] H => Complex.re (f (kapStar p)) :=
  Complex.continuous_re.comp (kapContinuous_starApply f)

/-- Sum of real parts before and after `kapStar` is continuous. -/
private theorem kapContinuous_re_add (f : StrongDual ℂ (H →Lₚₜ[ℂ] H)) :
    Continuous fun p : H →Lₚₜ[ℂ] H => Complex.re (f p) + Complex.re (f (kapStar p)) :=
  (Complex.continuous_re.comp f.cont).add (kapContinuous_re_starApply f)

end KapStarCont

section KapConvex

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The SOT-closure of a convex `kapStar`-invariant set is `kapStar`-invariant. -/
private theorem kapStar_mem_closure_of_convex {C : Set (H →Lₚₜ[ℂ] H)}
    (hconv : Convex ℝ C) (hstar : ∀ p ∈ C, kapStar p ∈ C)
    {q : H →Lₚₜ[ℂ] H} (hq : q ∈ closure C) :
    kapStar q ∈ closure C := by
  by_contra hmem
  let : ContinuousSMul ℂ (H →Lₚₜ[ℂ] H) :=
    WithSeminorms.continuousSMul (PointwiseConvergenceCLM.withSeminorms :
      WithSeminorms (PointwiseConvergenceCLM.seminormFamily (RingHom.id ℂ) H H))
  obtain ⟨f, u, hlt, hgt⟩ := RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ)
    hconv.closure isClosed_closure hmem
  have hle : ∀ p ∈ C, u ≤ RCLike.re (f (kapStar p)) := by
    intro p hp
    exact le_of_lt (hgt _ (subset_closure (hstar p hp)))
  have hcont : Continuous fun p : H →Lₚₜ[ℂ] H => RCLike.re (f (kapStar p)) := by
    simpa only [RCLike.re_to_complex] using kapContinuous_re_starApply f
  have hclosed : IsClosed {p : H →Lₚₜ[ℂ] H | u ≤ RCLike.re (f (kapStar p))} :=
    isClosed_le continuous_const hcont
  have hqle : u ≤ RCLike.re (f (kapStar q)) :=
    closure_minimal (fun p hp => hle p hp) hclosed hq
  exact (not_le.mpr hlt) hqle

/-- Fixed points of `kapStar` in the closure are limits of fixed points. -/
private theorem kapMem_closure_fixed_of_convex {C : Set (H →Lₚₜ[ℂ] H)}
    (hconv : Convex ℝ C) (hstar : ∀ p ∈ C, kapStar p ∈ C)
    {y : H →Lₚₜ[ℂ] H} (hy : y ∈ closure C) (hyy : kapStar y = y) :
    y ∈ closure {p : H →Lₚₜ[ℂ] H | p ∈ C ∧ kapStar p = p} := by
  by_contra hmem
  let : ContinuousSMul ℂ (H →Lₚₜ[ℂ] H) :=
    WithSeminorms.continuousSMul (PointwiseConvergenceCLM.withSeminorms :
      WithSeminorms (PointwiseConvergenceCLM.seminormFamily (RingHom.id ℂ) H H))
  have hconv_sa : Convex ℝ {p : H →Lₚₜ[ℂ] H | p ∈ C ∧ kapStar p = p} := by
    intro p hp q hq a b ha hb hab
    obtain ⟨hpp, hppstar⟩ := hp
    obtain ⟨hqq, hqqstar⟩ := hq
    refine ⟨hconv hpp hqq ha hb hab, ?_⟩
    rw [kapStar_add, kapStar_real_smul, kapStar_real_smul, hppstar, hqqstar]
  obtain ⟨f, u, hlt, hgt⟩ := RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ)
    hconv_sa.closure isClosed_closure hmem
  have hmem_sa : ∀ p ∈ C, ((1/2 : ℝ) • (p + kapStar p))
      ∈ {p : H →Lₚₜ[ℂ] H | p ∈ C ∧ kapStar p = p} := by
    intro p hp
    refine ⟨?_, ?_⟩
    · have h1 : ((1/2 : ℝ) • (p + kapStar p))
          = (1/2 : ℝ) • p + (1/2 : ℝ) • kapStar p := smul_add _ _ _
      rw [h1]
      exact hconv hp (hstar p hp) (by norm_num) (by norm_num) (by norm_num)
    · rw [kapStar_real_smul, kapStar_add, kapStar_kapStar, add_comm (kapStar p) p]
  have hval : ∀ p : H →Lₚₜ[ℂ] H, RCLike.re (f ((1/2 : ℝ) • (p + kapStar p)))
      = (1/2 : ℝ) * (RCLike.re (f p) + RCLike.re (f (kapStar p))) := by
    intro p
    have eC : Complex.re (f ((1/2 : ℝ) • (p + kapStar p)))
        = (1/2 : ℝ) * (Complex.re (f p) + Complex.re (f (kapStar p))) := by
      have e : f ((1/2 : ℝ) • (p + kapStar p))
          = (((1/2 : ℝ) : ℂ)) * (f p + f (kapStar p)) := by
        rw [kapReal_smul_sot, map_smul, map_add, smul_eq_mul]
      rw [e, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    simpa only [RCLike.re_to_complex] using eC
  have hle : ∀ p ∈ C,
      u ≤ (1/2 : ℝ) * (RCLike.re (f p) + RCLike.re (f (kapStar p))) := by
    intro p hp
    have h2 := hgt _ (subset_closure (hmem_sa p hp))
    rw [hval] at h2
    exact le_of_lt h2
  have hcont : Continuous fun p : H →Lₚₜ[ℂ] H =>
      (1/2 : ℝ) * (RCLike.re (f p) + RCLike.re (f (kapStar p))) := by
    have h2 : Continuous fun p : H →Lₚₜ[ℂ] H =>
        (1/2 : ℝ) * (Complex.re (f p) + Complex.re (f (kapStar p))) :=
      continuous_const.mul (kapContinuous_re_add f)
    simpa only [← RCLike.re_to_complex] using h2
  have hclosed : IsClosed {p : H →Lₚₜ[ℂ] H |
      u ≤ (1/2 : ℝ) * (RCLike.re (f p) + RCLike.re (f (kapStar p)))} :=
    isClosed_le continuous_const hcont
  have hy_le : u ≤ (1/2 : ℝ) * (RCLike.re (f y) + RCLike.re (f (kapStar y))) :=
    closure_minimal (fun p hp => hle p hp) hclosed hy
  rw [hyy] at hy_le
  have hhalf : (1/2 : ℝ) * (RCLike.re (f y) + RCLike.re (f y))
      = RCLike.re (f y) := by
    ring
  rw [hhalf] at hy_le
  exact (not_le.mpr hlt) hy_le

end KapConvex

section KapClosure

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The pullback of `S` along `toBounded`, as a submodule of SOT. -/
private noncomputable def kapSotSub (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Submodule ℂ (H →Lₚₜ[ℂ] H) :=
  S.toSubmodule.comap
    (ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) H
      {s : Set H | Finite s}).symm.toLinearMap

private theorem kapSotSub_mem {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    {p : H →Lₚₜ[ℂ] H} : p ∈ kapSotSub S ↔ toBounded p ∈ ↑S :=
  Submodule.mem_comap

private theorem kapSotSub_coe (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ↑(kapSotSub S) = {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := by
  ext p
  exact kapSotSub_mem

/-- The preimage set is convex. -/
private theorem kapSotConvex (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Convex ℝ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := by
  intro x hx y hy a b ha hb hab
  change toBounded (a • x + b • y) ∈ ↑S
  rw [kapToBounded_add, kapReal_smul_sot, kapReal_smul_sot, kapToBounded_smul,
    kapToBounded_smul]
  exact add_mem (S.smul_mem hx _) (S.smul_mem hy _)

/-- The preimage set is `kapStar`-invariant. -/
private theorem kapSotStar (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ∀ p ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S},
      kapStar p ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := by
  intro p hp
  change toBounded (kapStar p) ∈ ↑S
  rw [kapToBounded_star]
  exact star_mem hp

/-- The carrier of the topological closure is the norm-closure of the preimage. -/
private theorem kapTopClosure_coe (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ↑(Submodule.topologicalClosure (kapSotSub S))
      = closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := by
  rw [Submodule.topologicalClosure_coe, kapSotSub_coe]

private theorem kapToBounded_postcomp (a : H →L[ℂ] H) (p : H →Lₚₜ[ℂ] H) :
    toBounded (PointwiseConvergenceCLM.postcomp H a p) = a * toBounded p := by
  ext v
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, kapToBounded_apply]
  rfl

omit [CompleteSpace H] in
private theorem kapPostcomp_cont (a : H →L[ℂ] H) :
    Continuous ⇑(PointwiseConvergenceCLM.postcomp H a :
      (H →Lₚₜ[ℂ] H) →L[ℂ] (H →Lₚₜ[ℂ] H)) :=
  (PointwiseConvergenceCLM.postcomp H a : _ →L[ℂ] _).cont

omit [CompleteSpace H] in
private theorem kapPrecomp_cont (u : H →L[ℂ] H) :
    Continuous ⇑(PointwiseConvergenceCLM.precomp H u :
      (H →Lₚₜ[ℂ] H) →L[ℂ] (H →Lₚₜ[ℂ] H)) :=
  (PointwiseConvergenceCLM.precomp H u : _ →L[ℂ] _).cont

/-- The SOT-closure of `S`, read back as a star subalgebra of `B(H)`. -/
private noncomputable def kapSotClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {T | kapOfBounded T ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}}
  zero_mem' := by
    change kapOfBounded (0 : H →L[ℂ] H) ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
    rw [kapOfBounded_zero]
    apply subset_closure
    change toBounded (0 : H →Lₚₜ[ℂ] H) ∈ ↑S
    rw [kapToBounded_zero]
    exact zero_mem S
  add_mem' := by
    intro T U hT hU
    have hT' : kapOfBounded T ∈ Submodule.topologicalClosure (kapSotSub S) := by
      rw [← SetLike.mem_coe, kapTopClosure_coe]
      exact hT
    have hU' : kapOfBounded U ∈ Submodule.topologicalClosure (kapSotSub S) := by
      rw [← SetLike.mem_coe, kapTopClosure_coe]
      exact hU
    change kapOfBounded (T + U) ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
    rw [kapOfBounded_add, ← kapTopClosure_coe]
    exact add_mem hT' hU'
  mul_mem' := by
    intro T U hT hU
    have hT' : kapOfBounded T ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := hT
    have hU' : kapOfBounded U ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := hU
    have step1 : ∀ (a : H →L[ℂ] H), a ∈ (↑S : Set (H →L[ℂ] H)) →
        ∀ (V : H →L[ℂ] H),
          kapOfBounded V ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} →
          kapOfBounded (a * V) ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := by
      intro a ha V hV
      rw [kapOfBounded_mul_post]
      exact map_mem_closure (kapPostcomp_cont a) hV (fun p hp => by
        change toBounded (PointwiseConvergenceCLM.postcomp H a p) ∈ ↑S
        rw [kapToBounded_postcomp]
        exact mul_mem ha hp)
    have hmaps : Set.MapsTo (PointwiseConvergenceCLM.precomp H U)
        {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
        (closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}) := by
      intro q hq
      have e1 : PointwiseConvergenceCLM.precomp H U q
          = kapOfBounded (toBounded q * U) := by
        rw [kapOfBounded_mul_pre, kapOfBounded_toBounded]
      rw [e1]
      exact step1 _ hq _ hU'
    have hmem := map_mem_closure (kapPrecomp_cont U) hT' hmaps
    rw [closure_closure] at hmem
    change kapOfBounded (T * U) ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
    rw [kapOfBounded_mul_pre]
    exact hmem
  algebraMap_mem' := by
    intro c
    have hmem : kapOfBounded (algebraMap ℂ (H →L[ℂ] H) c)
        ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := by
      change toBounded (kapOfBounded (algebraMap ℂ (H →L[ℂ] H) c)) ∈ ↑S
      rw [kapToBounded_ofBounded]
      exact S.algebraMap_mem c
    change kapOfBounded (algebraMap ℂ (H →L[ℂ] H) c)
      ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
    exact subset_closure hmem
  star_mem' := by
    intro x hx
    have hx' : kapOfBounded x ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := hx
    have e : kapOfBounded (star x) = kapStar (kapOfBounded x) := by
      unfold kapStar
      rw [kapToBounded_ofBounded]
    change kapOfBounded (star x) ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
    rw [e]
    exact kapStar_mem_closure_of_convex (kapSotConvex S) (kapSotStar S) hx'

/-- Membership in `kapSotClosure` unfolds definitionally. -/
private theorem kapMem_sotClosure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) :
    T ∈ kapSotClosure S ↔
      kapOfBounded T ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} :=
  Iff.rfl

/-- The SOT-closure is norm-closed. -/
private theorem kapIsClosed_sotClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    IsClosed (↑(kapSotClosure S) : Set (H →L[ℂ] H)) := by
  have heq : (↑(kapSotClosure S) : Set (H →L[ℂ] H))
      = kapOfBounded ⁻¹' (closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}) := by
    ext T
    exact Iff.rfl
  rw [heq]
  exact IsClosed.preimage kapOfBounded_continuous isClosed_closure

end KapClosure

section KapScale

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Norm-closure points of `S` in the unit ball lie in the SOT-closure of the ball. -/
private theorem kapOfBounded_mem_closure_ball (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H} (hT : T ∈ S.topologicalClosure) (hnorm : ‖T‖ ≤ 1) :
    kapOfBounded T ∈ closure ({p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} ∩
      {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1}) := by
  have hTmem : T ∈ (S.topologicalClosure : Set (H →L[ℂ] H)) := hT
  rw [StarSubalgebra.topologicalClosure_coe] at hTmem
  obtain ⟨s, hsS, hsLim⟩ := mem_closure_iff_seq_limit.mp hTmem
  set c : ℕ → ℝ := fun n => max 1 ‖s n‖ with hcdef
  have hc1 : ∀ n, 1 ≤ c n := fun n => le_max_left _ _
  have hcnorm : ∀ n, ‖s n‖ ≤ c n := fun n => le_max_right _ _
  have hcpos : ∀ n, (0 : ℝ) < c n := fun n => lt_of_lt_of_le zero_lt_one (hc1 n)
  have hclim : Filter.Tendsto c Filter.atTop (𝓝 1) := by
    have h1 : Filter.Tendsto (fun n => ‖s n‖) Filter.atTop (𝓝 ‖T‖) :=
      hsLim.norm
    have h2 := (tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop)).max h1
    rwa [max_eq_left hnorm] at h2
  set t : ℕ → H →L[ℂ] H := fun n => ((((c n)⁻¹ : ℝ) : ℂ)) • s n with htdef
  have htS : ∀ n, t n ∈ (↑S : Set (H →L[ℂ] H)) := fun n => S.smul_mem (hsS n) _
  have htnorm : ∀ n, ‖t n‖ ≤ 1 := by
    intro n
    have hpos : (0 : ℝ) ≤ (c n)⁻¹ := le_of_lt (inv_pos.mpr (hcpos n))
    calc ‖t n‖ = (c n)⁻¹ * ‖s n‖ := by
          rw [htdef]
          simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hpos]
      _ ≤ (c n)⁻¹ * c n := by
          exact mul_le_mul_of_nonneg_left (hcnorm n) hpos
      _ = 1 := inv_mul_cancel₀ (ne_of_gt (hcpos n))
  have hinv : Filter.Tendsto (fun n => (c n)⁻¹) Filter.atTop (𝓝 1) := by
    have h := hclim.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h
  have hscal : Filter.Tendsto (fun n => ((((c n)⁻¹ : ℝ) : ℂ))) Filter.atTop (𝓝 1) := by
    have hcast := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hinv
    simp only [Complex.ofReal_one] at hcast
    exact hcast
  have htlim : Filter.Tendsto t Filter.atTop (𝓝 T) := by
    have h := hscal.smul hsLim
    simpa [htdef, one_smul] using h
  have hsot : Filter.Tendsto (fun n => kapOfBounded (t n)) Filter.atTop
      (𝓝 (kapOfBounded T)) :=
    (kapOfBounded_continuous.tendsto _).comp htlim
  apply mem_closure_of_tendsto hsot
  filter_upwards with n
  constructor
  · change toBounded (kapOfBounded (t n)) ∈ ↑S
    rw [kapToBounded_ofBounded]
    exact htS n
  · change ‖toBounded (kapOfBounded (t n))‖ ≤ 1
    rw [kapToBounded_ofBounded]
    exact htnorm n

end KapScale

section KapCayley

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Scalar resolvent function `t ↦ (1 + t ^ 2)⁻¹`. -/
private noncomputable def kapR : ℝ → ℝ := fun t => (1 + t ^ 2)⁻¹

/-- Scalar Cayley-type function `t ↦ 2 * t / (1 + t ^ 2)`. -/
private noncomputable def kapF : ℝ → ℝ := fun t => 2 * t / (1 + t ^ 2)

/-- cfc of `kapR` at `a`. -/
private noncomputable def kapCfcR (a : H →L[ℂ] H) : H →L[ℂ] H := cfc kapR a

/-- cfc of `kapF` at `a`. -/
private noncomputable def kapCfcF (a : H →L[ℂ] H) : H →L[ℂ] H := cfc kapF a

private theorem kapR_cont : Continuous kapR := by
  unfold kapR
  refine Continuous.inv₀ (by continuity) (fun t => ?_)
  exact ne_of_gt (by positivity : (0 : ℝ) < 1 + t ^ 2)

private theorem kapF_cont : Continuous kapF := by
  unfold kapF
  refine Continuous.div (by continuity) (by continuity) (fun t => ?_)
  exact ne_of_gt (by positivity : (0 : ℝ) < 1 + t ^ 2)

private theorem kapMul_cont : Continuous (fun t : ℝ => t * kapR t) :=
  continuous_id.mul kapR_cont

private theorem kapMulR_cont : Continuous (fun t : ℝ => kapR t * t) :=
  kapR_cont.mul continuous_id

private theorem kapR_nonneg (t : ℝ) : 0 ≤ kapR t := by
  unfold kapR
  exact le_of_lt (inv_pos.mpr (by positivity : (0 : ℝ) < 1 + t ^ 2))

private theorem kapR_le_one (t : ℝ) : kapR t ≤ 1 := by
  unfold kapR
  refine inv_le_one_of_one_le₀ ?_
  have h : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  linarith

private theorem kapF_abs_le_one (t : ℝ) : |kapF t| ≤ 1 := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have h := two_mul_le_add_sq (|t|) (1 : ℝ)
  rw [mul_one, one_pow, sq_abs] at h
  have hab : |2 * t| = 2 * |t| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  unfold kapF
  rw [abs_div, abs_of_pos hpos, div_le_one hpos, hab]
  linarith

/-- The resolvent cfc has norm at most one. -/
private theorem kapNorm_cfcR_le (a : H →L[ℂ] H) :
    ‖kapCfcR a‖ ≤ 1 := by
  unfold kapCfcR
  refine norm_cfc_le zero_le_one (fun t _ => ?_)
  calc ‖kapR t‖ = |kapR t| := Real.norm_eq_abs _
    _ = kapR t := abs_of_nonneg (kapR_nonneg t)
    _ ≤ 1 := kapR_le_one t

/-- The Cayley cfc has norm at most one. -/
private theorem kapNorm_cfcF_le (a : H →L[ℂ] H) :
    ‖kapCfcF a‖ ≤ 1 := by
  unfold kapCfcF
  refine norm_cfc_le zero_le_one (fun t _ => ?_)
  calc ‖kapF t‖ = |kapF t| := Real.norm_eq_abs _
    _ ≤ 1 := kapF_abs_le_one t

private theorem kapCfc_sq (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    cfc (fun t : ℝ => t * t) a = a * a := by
  have h2 := cfc_pow_id (R := ℝ) (a := a) (n := 2) (ha := ha)
  have e : (fun t : ℝ => t * t) = (· ^ 2 : ℝ → ℝ) :=
    funext fun t => (pow_two t).symm
  rw [e, h2, pow_two]

private theorem kapCfc_one_add_sq (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    cfc (fun t : ℝ => 1 + t * t) a = 1 + a * a := by
  have h := cfc_const_add (r := (1 : ℝ)) (f := fun t : ℝ => t * t) (a := a)
    (hf := (by continuity : Continuous (fun t : ℝ => t * t)).continuousOn) (ha := ha)
  rw [kapCfc_sq a ha, map_one] at h
  exact h

private theorem kapScalar_inv_left (t : ℝ) : kapR t * (1 + t * t) = 1 := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have e : (1 : ℝ) + t * t = 1 + t ^ 2 := by ring
  unfold kapR
  rw [e]
  exact inv_mul_cancel₀ (ne_of_gt hpos)

private theorem kapScalar_inv_right (t : ℝ) : (1 + t * t) * kapR t = 1 := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have e : (1 : ℝ) + t * t = 1 + t ^ 2 := by ring
  unfold kapR
  rw [e]
  exact mul_inv_cancel₀ (ne_of_gt hpos)

/-- Left inverse identity for the resolvent cfc. -/
private theorem kapCfcR_mul_left (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    kapCfcR a * (1 + a * a) = 1 := by
  have hmul := cfc_mul (f := kapR) (g := fun t : ℝ => 1 + t * t) (a := a)
    (hf := kapR_cont.continuousOn)
    (hg := (by continuity : Continuous (fun t : ℝ => 1 + t * t)).continuousOn)
  have hcfc : cfc (fun t : ℝ => kapR t * (1 + t * t)) a = 1 :=
    (cfc_congr (fun t _ => kapScalar_inv_left t)).trans
      (cfc_one (R := ℝ) (a := a) (ha := ha))
  unfold kapCfcR
  rw [← kapCfc_one_add_sq a ha, ← hmul]
  exact hcfc

/-- Right inverse identity for the resolvent cfc. -/
private theorem kapCfcR_mul_right (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    (1 + a * a) * kapCfcR a = 1 := by
  have hmul := cfc_mul (f := fun t : ℝ => 1 + t * t) (g := kapR) (a := a)
    (hf := (by continuity : Continuous (fun t : ℝ => 1 + t * t)).continuousOn)
    (hg := kapR_cont.continuousOn)
  have hcfc : cfc (fun t : ℝ => (1 + t * t) * kapR t) a = 1 :=
    (cfc_congr (fun t _ => kapScalar_inv_right t)).trans
      (cfc_one (R := ℝ) (a := a) (ha := ha))
  unfold kapCfcR
  rw [← kapCfc_one_add_sq a ha, ← hmul]
  exact hcfc

private theorem kapCfc_mul_self_left (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    a * kapCfcR a = cfc (fun t : ℝ => t * kapR t) a := by
  have h := cfc_mul (f := fun t : ℝ => t) (g := kapR) (a := a)
    (hf := (by continuity : Continuous (fun t : ℝ => t)).continuousOn)
    (hg := kapR_cont.continuousOn)
  have hid : cfc (fun t : ℝ => t) a = a := cfc_id' (R := ℝ) (ha := ha)
  rw [hid] at h
  unfold kapCfcR
  exact h.symm

private theorem kapCfc_mul_self_right (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    kapCfcR a * a = cfc (fun t : ℝ => kapR t * t) a := by
  have h := cfc_mul (f := kapR) (g := fun t : ℝ => t) (a := a)
    (hf := kapR_cont.continuousOn)
    (hg := (by continuity : Continuous (fun t : ℝ => t)).continuousOn)
  have hid : cfc (fun t : ℝ => t) a = a := cfc_id' (R := ℝ) (ha := ha)
  rw [hid] at h
  unfold kapCfcR
  exact h.symm

/-- The Cayley cfc factors through `a * R a`. -/
private theorem kapCfcF_eq_left (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    kapCfcF a = (2 : ℝ) • (a * kapCfcR a) := by
  have hscalar : ∀ t : ℝ, kapF t = 2 * (t * kapR t) := by
    intro t
    unfold kapF kapR
    ring
  have hF : cfc kapF a = cfc (fun t : ℝ => 2 * (t * kapR t)) a :=
    cfc_congr (fun t _ => hscalar t)
  have hsmul : (2 : ℝ) • cfc (fun t : ℝ => t * kapR t) a
      = cfc (fun t : ℝ => 2 * (t * kapR t)) a := by
    have h := cfc_const_mul (r := (2 : ℝ)) (f := fun t : ℝ => t * kapR t) (a := a)
      (hf := kapMul_cont.continuousOn)
    exact h.symm
  have hmul := kapCfc_mul_self_left a ha
  unfold kapCfcF
  rw [hF, ← hsmul, ← hmul]

/-- The Cayley cfc factors through `R a * a`. -/
private theorem kapCfcF_eq_right (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    kapCfcF a = (2 : ℝ) • (kapCfcR a * a) := by
  have hscalar : ∀ t : ℝ, kapF t = 2 * (kapR t * t) := by
    intro t
    unfold kapF kapR
    ring
  have hF : cfc kapF a = cfc (fun t : ℝ => 2 * (kapR t * t)) a :=
    cfc_congr (fun t _ => hscalar t)
  have hsmul : (2 : ℝ) • cfc (fun t : ℝ => kapR t * t) a
      = cfc (fun t : ℝ => 2 * (kapR t * t)) a := by
    have h := cfc_const_mul (r := (2 : ℝ)) (f := fun t : ℝ => kapR t * t) (a := a)
      (hf := kapMulR_cont.continuousOn)
    exact h.symm
  have hmul := kapCfc_mul_self_right a ha
  unfold kapCfcF
  rw [hF, ← hsmul, ← hmul]

end KapCayley

section KapCayleyTendsto

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Algebraic identity for the difference of Cayley maps at self-adjoint points. -/
private theorem kapCfcF_sub (a b : H →L[ℂ] H) (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) :
    kapCfcF a - kapCfcF b = (2 : ℝ) • (kapCfcR a * (a - b) * kapCfcR b)
      + (1 / 2 : ℝ) • (kapCfcF a * (b - a) * kapCfcF b) := by
  have hFa := kapCfcF_eq_right a ha
  have hFb := kapCfcF_eq_left b hb
  have hRa := kapCfcR_mul_left a ha
  have hRb := kapCfcR_mul_right b hb
  have e1 : kapCfcR a * (a * (1 + b * b)) * kapCfcR b = kapCfcR a * a := by
    rw [mul_assoc (kapCfcR a) _ _, mul_assoc a _ _, hRb, mul_one]
  have e2 : kapCfcR a * ((1 + a * a) * b) * kapCfcR b = b * kapCfcR b := by
    rw [mul_assoc (kapCfcR a) _ _, mul_assoc (1 + a * a) _ _,
      ← mul_assoc (kapCfcR a) _ _, hRa, one_mul]
  have e3 : a * (1 + b * b) - (1 + a * a) * b
      = (a - b) + a * (b - a) * b := by
    noncomm_ring
  have eSub : kapCfcR a * (a * (1 + b * b)) * kapCfcR b
          - kapCfcR a * ((1 + a * a) * b) * kapCfcR b
        = kapCfcR a * (a - b) * kapCfcR b
          + (kapCfcR a * a) * (b - a) * (b * kapCfcR b) := by
    have hbridge : kapCfcR a * (a * (b - a) * b) * kapCfcR b
        = (kapCfcR a * a) * (b - a) * (b * kapCfcR b) := by
      noncomm_ring
    rw [← sub_mul, ← mul_sub, e3, mul_add, add_mul, hbridge]
  have eF : kapCfcF a * (b - a) * kapCfcF b
        = (4 : ℝ) • ((kapCfcR a * a) * (b - a) * (b * kapCfcR b)) := by
    rw [hFa, hFb, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_smul]
    norm_num
  have eMain : kapCfcF a - kapCfcF b
        = (2 : ℝ) • (kapCfcR a * (a * (1 + b * b)) * kapCfcR b)
        - (2 : ℝ) • (kapCfcR a * ((1 + a * a) * b) * kapCfcR b) := by
    rw [hFa, hFb, ← e1, ← e2]
  rw [eMain, ← smul_sub, eSub, smul_add, eF, smul_smul,
    show (1 / 2 : ℝ) * 4 = 2 by norm_num]

/-- Pointwise norm bound for the Cayley map difference. -/
private theorem kapCfcF_bound (a b : H →L[ℂ] H) (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (v : H) :
    ‖(kapCfcF a - kapCfcF b) v‖ ≤ 2 * ‖(a - b) (kapCfcR b v)‖
      + (1 / 2) * ‖(a - b) (kapCfcF b v)‖ := by
  have hsub := kapCfcF_sub a b ha hb
  have hR := kapNorm_cfcR_le a
  have hF := kapNorm_cfcF_le a
  have smul2 : ∀ w : H, ‖(2 : ℝ) • w‖ = 2 * ‖w‖ := by
    intro w
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have smulh : ∀ w : H, ‖(1 / 2 : ℝ) • w‖ = (1 / 2) * ‖w‖ := by
    intro w
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have b1 : ‖((kapCfcR a * (a - b) * kapCfcR b) v)‖
      ≤ ‖(a - b) (kapCfcR b v)‖ := by
    have e : (kapCfcR a * (a - b) * kapCfcR b) v
        = kapCfcR a ((a - b) (kapCfcR b v)) := by
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [e]
    calc ‖kapCfcR a ((a - b) (kapCfcR b v))‖
        ≤ ‖kapCfcR a‖ * ‖(a - b) (kapCfcR b v)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖(a - b) (kapCfcR b v)‖ :=
          mul_le_mul_of_nonneg_right hR (norm_nonneg _)
      _ = ‖(a - b) (kapCfcR b v)‖ := one_mul _
  have b2 : ‖((kapCfcF a * (b - a) * kapCfcF b) v)‖
      ≤ ‖(a - b) (kapCfcF b v)‖ := by
    have e : (kapCfcF a * (b - a) * kapCfcF b) v
        = kapCfcF a ((b - a) (kapCfcF b v)) := by
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    have e2 : (b - a) (kapCfcF b v) = -((a - b) (kapCfcF b v)) := by
      have d : (b - a) (kapCfcF b v) = b (kapCfcF b v) - a (kapCfcF b v) :=
        sub_apply _ _ _
      have d2 : (a - b) (kapCfcF b v) = a (kapCfcF b v) - b (kapCfcF b v) :=
        sub_apply _ _ _
      rw [d, d2, neg_sub]
    have hle : ‖kapCfcF a ((b - a) (kapCfcF b v))‖ ≤ ‖(b - a) (kapCfcF b v)‖ := by
      calc ‖kapCfcF a ((b - a) (kapCfcF b v))‖
          ≤ ‖kapCfcF a‖ * ‖(b - a) (kapCfcF b v)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖(b - a) (kapCfcF b v)‖ :=
            mul_le_mul_of_nonneg_right hF (norm_nonneg _)
        _ = ‖(b - a) (kapCfcF b v)‖ := one_mul _
    have hneg : ‖(b - a) (kapCfcF b v)‖ = ‖(a - b) (kapCfcF b v)‖ := by
      rw [e2, norm_neg]
    rw [e]
    rw [hneg] at hle
    exact hle
  rw [hsub, add_apply, IsSMulApply.smul_apply, IsSMulApply.smul_apply]
  refine (norm_add_le _ _).trans ?_
  rw [smul2, smulh]
  exact add_le_add (mul_le_mul_of_nonneg_left b1 (by norm_num))
    (mul_le_mul_of_nonneg_left b2 (by norm_num))

/-- The Cayley map is SOT-continuous along self-adjoint nets. -/
private theorem kapTendsto_cfcF (b : H →L[ℂ] H) (hb : IsSelfAdjoint b) :
    Filter.Tendsto (fun p : H →Lₚₜ[ℂ] H => kapOfBounded (kapCfcF (toBounded p)))
      (𝓝[{p : H →Lₚₜ[ℂ] H | IsSelfAdjoint (toBounded p)}] (kapOfBounded b))
      (𝓝 (kapOfBounded (kapCfcF b))) := by
  rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
  intro v
  change Filter.Tendsto
    (fun p : H →Lₚₜ[ℂ] H => (kapOfBounded (kapCfcF (toBounded p))) v)
    (𝓝[{p : H →Lₚₜ[ℂ] H | IsSelfAdjoint (toBounded p)}] (kapOfBounded b))
    (𝓝 ((kapOfBounded (kapCfcF b)) v))
  have hblim : ∀ w : H, Filter.Tendsto
      (fun p : H →Lₚₜ[ℂ] H => ‖(toBounded p - b) w‖)
      (𝓝[{p : H →Lₚₜ[ℂ] H | IsSelfAdjoint (toBounded p)}] (kapOfBounded b))
      (𝓝 0) := by
    intro w
    have h1 : Filter.Tendsto (fun p : H →Lₚₜ[ℂ] H => p w)
        (𝓝 (kapOfBounded b)) (𝓝 ((kapOfBounded b) w)) :=
      (kapEval_continuous w).tendsto _
    have h2 : Filter.Tendsto (fun p : H →Lₚₜ[ℂ] H => p w)
        (𝓝[{p : H →Lₚₜ[ℂ] H | IsSelfAdjoint (toBounded p)}] (kapOfBounded b))
        (𝓝 ((kapOfBounded b) w)) :=
      h1.mono_left nhdsWithin_le_nhds
    have e : (fun p : H →Lₚₜ[ℂ] H => ‖(toBounded p - b) w‖)
        = (fun p : H →Lₚₜ[ℂ] H => ‖p w - (kapOfBounded b) w‖) := by
      funext p
      have d1 : (toBounded p - b) w = (toBounded p) w - b w := sub_apply _ _ _
      rw [d1, kapToBounded_apply, kapOfBounded_apply]
    rw [e]
    exact tendsto_iff_norm_sub_tendsto_zero.mp h2
  have hlim : Filter.Tendsto
      (fun p : H →Lₚₜ[ℂ] H => 2 * ‖(toBounded p - b) (kapCfcR b v)‖
        + (1 / 2) * ‖(toBounded p - b) (kapCfcF b v)‖)
      (𝓝[{p : H →Lₚₜ[ℂ] H | IsSelfAdjoint (toBounded p)}] (kapOfBounded b))
      (𝓝 0) := by
    have h1 := (hblim (kapCfcR b v)).const_mul 2
    have h2 := (hblim (kapCfcF b v)).const_mul (1 / 2)
    rw [mul_zero] at h1 h2
    have h12 := h1.add h2
    rwa [add_zero] at h12
  have hbound : ∀ᶠ p in
      𝓝[{p : H →Lₚₜ[ℂ] H | IsSelfAdjoint (toBounded p)}] (kapOfBounded b),
      ‖(kapOfBounded (kapCfcF (toBounded p))) v - (kapOfBounded (kapCfcF b)) v‖
        ≤ 2 * ‖(toBounded p - b) (kapCfcR b v)‖
          + (1 / 2) * ‖(toBounded p - b) (kapCfcF b v)‖ := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have ha : IsSelfAdjoint (toBounded p) := hp
    have h := kapCfcF_bound (toBounded p) b ha hb v
    have e1 : (kapOfBounded (kapCfcF (toBounded p))) v
          - (kapOfBounded (kapCfcF b)) v
        = (kapCfcF (toBounded p) - kapCfcF b) v := by
      simp only [kapOfBounded_apply, sub_apply]
    rw [e1]
    exact h
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound hlim

end KapCayleyTendsto

section KapCayleyInverse

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Scalar inverse Cayley function `t ↦ t / (1 + √(1 - t ^ 2))`. -/
private noncomputable def kapG : ℝ → ℝ := fun t => t / (1 + Real.sqrt (1 - t ^ 2))

private theorem kapG_cont : Continuous kapG := by
  unfold kapG
  refine Continuous.div continuous_id
    (continuous_const.add
      (Real.continuous_sqrt.comp
        (by continuity : Continuous (fun t : ℝ => 1 - t ^ 2)))) (fun t => ?_)
  have hnn : (0 : ℝ) ≤ Real.sqrt (1 - t ^ 2) := Real.sqrt_nonneg _
  have hpos : (0 : ℝ) < 1 + Real.sqrt (1 - t ^ 2) := by linarith
  exact ne_of_gt hpos

/-- The inverse Cayley cfc inverts `kapCfcF` on the unit ball. -/
private theorem kapCfcF_cfcG (x : H →L[ℂ] H) (hx : IsSelfAdjoint x)
    (hnorm : ‖x‖ ≤ 1) :
    kapCfcF (cfc kapG x) = x := by
  have hspec : ∀ t ∈ spectrum ℝ x, |t| ≤ 1 := by
    have h := (norm_cfc_le_iff (id : ℝ → ℝ) x zero_le_one
      (hf := continuous_id.continuousOn) (ha := hx)).mp ?_
    · intro t ht
      have ht1 := h t ht
      simpa [Real.norm_eq_abs] using ht1
    · have hid : cfc (id : ℝ → ℝ) x = x := cfc_id (R := ℝ) (a := x) (ha := hx)
      rwa [hid]
  have hscalar : ∀ t ∈ spectrum ℝ x, (kapF ∘ kapG) t = id t := by
    intro t ht
    have habs : |t| ≤ 1 := hspec t ht
    have hnn : (0 : ℝ) ≤ 1 - t ^ 2 := by
      have h2 : |t| ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr habs) (abs_nonneg t)]
      rw [sq_abs] at h2
      linarith
    have hsnn : (0 : ℝ) ≤ Real.sqrt (1 - t ^ 2) := Real.sqrt_nonneg _
    have hs2 : (Real.sqrt (1 - t ^ 2)) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hnn
    have hspos : (0 : ℝ) < 1 + Real.sqrt (1 - t ^ 2) := by linarith
    have hne : (1 : ℝ) + Real.sqrt (1 - t ^ 2) ≠ 0 := ne_of_gt hspos
    set s : ℝ := Real.sqrt (1 - t ^ 2) with hsdef
    have hden : 1 + (t / (1 + s)) ^ 2 = 2 / (1 + s) := by
      have e1 : (t / (1 + s)) ^ 2 = t ^ 2 / ((1 + s) * (1 + s)) := by
        simp only [pow_two, div_mul_div_comm]
      have e3 : ((1 + s) ^ 2 + t ^ 2) = 2 * (1 + s) := by
        linear_combination hs2
      have e4 : (1 : ℝ) + t ^ 2 / ((1 + s) * (1 + s))
          = ((1 + s) ^ 2 + t ^ 2) / ((1 + s) * (1 + s)) := by
        have hD : ((1 + s) * (1 + s)) ≠ 0 := mul_ne_zero hne hne
        field_simp
      rw [e1, e4, e3, div_eq_div_iff (mul_ne_zero hne hne) hne]
      ring
    change kapF (kapG t) = t
    unfold kapG kapF
    rw [hden, div_eq_iff (ne_of_gt (div_pos (by norm_num) hspos)),
      ← mul_div_assoc, ← mul_div_assoc, mul_comm (2 : ℝ) t]
  have hfin : cfc (kapF ∘ kapG) x = cfc id x := cfc_congr hscalar
  have hcomp := cfc_comp (g := kapF) (f := kapG) (a := x) (ha := hx)
    (hg := kapF_cont.continuousOn) (hf := kapG_cont.continuousOn)
  have hid : cfc (id : ℝ → ℝ) x = x := cfc_id (R := ℝ) (a := x) (ha := hx)
  unfold kapCfcF
  rw [← hcomp, hfin, hid]

/-- The inverse Cayley cfc of a self-adjoint element is self-adjoint. -/
private theorem kapIsSelfAdjoint_cfcG (x : H →L[ℂ] H) :
    IsSelfAdjoint (cfc kapG x) :=
  IsSelfAdjoint.cfc

end KapCayleyInverse

section KapSelfAdjoint

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Self-adjoint Kaplansky density: a self-adjoint norm-one element of the SOT-closure
    of `S` is an SOT-limit of the unit ball of `S`. -/
private theorem kapSelfAdjoint_mem_closure_ball (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : H →L[ℂ] H) (hx : IsSelfAdjoint x) (hnorm : ‖x‖ ≤ 1)
    (hxmem : kapOfBounded x
      ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}) :
    kapOfBounded x ∈ closure ({p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} ∩
      {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1}) := by
  have hxS : x ∈ kapSotClosure S := (kapMem_sotClosure S x).mpr hxmem
  have hclosed : IsClosed (↑(kapSotClosure S) : Set (H →L[ℂ] H)) :=
    kapIsClosed_sotClosure S
  have hyS : cfc kapG x ∈ kapSotClosure S := cfc_mem kapG hxS
  have hymem : kapOfBounded (cfc kapG x)
      ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} :=
    (kapMem_sotClosure S _).mp hyS
  have hysa : IsSelfAdjoint (cfc kapG x) := kapIsSelfAdjoint_cfcG x
  have hyfix : kapStar (kapOfBounded (cfc kapG x))
      = kapOfBounded (cfc kapG x) := by
    rw [kapStar_eq_iff, kapToBounded_ofBounded]
    exact hysa
  have hysa_mem : kapOfBounded (cfc kapG x)
      ∈ closure {p : H →Lₚₜ[ℂ] H | p ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
        ∧ kapStar p = p} :=
    kapMem_closure_fixed_of_convex (kapSotConvex S) (kapSotStar S) hymem hyfix
  have hsub : {p : H →Lₚₜ[ℂ] H | p ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
        ∧ kapStar p = p}
      ⊆ {p : H →Lₚₜ[ℂ] H | IsSelfAdjoint (toBounded p)} := by
    intro p hp
    obtain ⟨-, hfix⟩ := hp
    exact (kapStar_eq_iff p).mp hfix
  have hne : (𝓝[{p : H →Lₚₜ[ℂ] H | p ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
        ∧ kapStar p = p}] (kapOfBounded (cfc kapG x))).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hysa_mem
  have : Filter.NeBot (𝓝[{p : H →Lₚₜ[ℂ] H | p ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
        ∧ kapStar p = p}] (kapOfBounded (cfc kapG x))) := hne
  have htend0 := kapTendsto_cfcF (cfc kapG x) hysa
  have hmono : 𝓝[{p : H →Lₚₜ[ℂ] H | p ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
          ∧ kapStar p = p}] (kapOfBounded (cfc kapG x))
        ≤ 𝓝[{p : H →Lₚₜ[ℂ] H | IsSelfAdjoint (toBounded p)}]
          (kapOfBounded (cfc kapG x)) :=
    nhdsWithin_mono _ hsub
  have htend := htend0.mono_left hmono
  have hlim : kapCfcF (cfc kapG x) = x := kapCfcF_cfcG x hx hnorm
  rw [hlim] at htend
  have hmaps : ∀ᶠ p in 𝓝[{p : H →Lₚₜ[ℂ] H | p ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
          ∧ kapStar p = p}] (kapOfBounded (cfc kapG x)),
      kapOfBounded (kapCfcF (toBounded p))
        ∈ closure ({p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} ∩
          {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1}) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    obtain ⟨hpmem, hpfix⟩ := hp
    have hmemS : toBounded p ∈ (↑S : Set (H →L[ℂ] H)) := hpmem
    have hclosedS : IsClosed (↑(S.topologicalClosure) : Set (H →L[ℂ] H)) :=
      S.isClosed_topologicalClosure
    have hmemT : kapCfcF (toBounded p) ∈ S.topologicalClosure :=
      cfc_mem kapF (S.le_topologicalClosure hmemS)
    have hsa : IsSelfAdjoint (toBounded p) := by
      rw [← kapStar_eq_iff]
      exact hpfix
    have hnormF : ‖kapCfcF (toBounded p)‖ ≤ 1 := kapNorm_cfcF_le _
    exact kapOfBounded_mem_closure_ball _ hmemT hnormF
  exact isClosed_closure.mem_of_tendsto htend hmaps

end KapSelfAdjoint

section KapL2Prod

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- First projection `WithLp 2 (H × H) →L[ℂ] H`. -/
private noncomputable def kapFst : WithLp 2 (H × H) →L[ℂ] H :=
  WithLp.fstL 2 ℂ H H

/-- Second projection. -/
private noncomputable def kapSnd : WithLp 2 (H × H) →L[ℂ] H :=
  WithLp.sndL 2 ℂ H H

/-- First inclusion `H →L[ℂ] WithLp 2 (H × H)`. -/
private noncomputable def kapInl : H →L[ℂ] WithLp 2 (H × H) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inl ℂ H H

/-- Second inclusion. -/
private noncomputable def kapInr : H →L[ℂ] WithLp 2 (H × H) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℂ H H

omit [CompleteSpace H] in
private theorem kapInl_ofLp (v : H) : (kapInl v).ofLp = (v, 0) := rfl

omit [CompleteSpace H] in
private theorem kapInr_ofLp (v : H) : (kapInr v).ofLp = (0, v) := rfl

omit [CompleteSpace H] in
private theorem kapFst_ofLp (w : WithLp 2 (H × H)) : kapFst w = (w.ofLp).1 := by
  have h1 : kapFst w = w.fst := WithLp.fstL_apply 2 ℂ H H w
  have h2 : w.fst = (w.ofLp).1 := (WithLp.ofLp_fst w).symm
  exact h1.trans h2

omit [CompleteSpace H] in
private theorem kapSnd_ofLp (w : WithLp 2 (H × H)) : kapSnd w = (w.ofLp).2 := by
  have h1 : kapSnd w = w.snd := WithLp.sndL_apply 2 ℂ H H w
  have h2 : w.snd = (w.ofLp).2 := (WithLp.ofLp_snd w).symm
  exact h1.trans h2

omit [CompleteSpace H] in
private theorem kapInl_apply' (v : H) : kapInl v = WithLp.toLp 2 (v, (0 : H)) := by
  conv_lhs => rw [← WithLp.toLp_ofLp 2 (kapInl v), kapInl_ofLp]

omit [CompleteSpace H] in
private theorem kapInr_apply' (v : H) : kapInr v = WithLp.toLp 2 ((0 : H), v) := by
  conv_lhs => rw [← WithLp.toLp_ofLp 2 (kapInr v), kapInr_ofLp]

omit [CompleteSpace H] in
private theorem kapFst_inl : kapFst ∘L kapInl = ContinuousLinearMap.id ℂ H := by
  ext v
  change kapFst (kapInl v) = v
  rw [kapFst_ofLp, kapInl_ofLp]

omit [CompleteSpace H] in
private theorem kapSnd_inr : kapSnd ∘L kapInr = ContinuousLinearMap.id ℂ H := by
  ext v
  change kapSnd (kapInr v) = v
  rw [kapSnd_ofLp, kapInr_ofLp]

omit [CompleteSpace H] in
private theorem kapFst_inr : kapFst ∘L kapInr = (0 : H →L[ℂ] H) := by
  ext v
  change kapFst (kapInr v) = 0
  rw [kapFst_ofLp, kapInr_ofLp]

omit [CompleteSpace H] in
private theorem kapSnd_inl : kapSnd ∘L kapInl = (0 : H →L[ℂ] H) := by
  ext v
  change kapSnd (kapInl v) = 0
  rw [kapSnd_ofLp, kapInl_ofLp]

omit [CompleteSpace H] in
private theorem kapProj_sum : kapInl ∘L kapFst + kapInr ∘L kapSnd
    = ContinuousLinearMap.id ℂ (WithLp 2 (H × H)) := by
  ext w
  change kapInl (kapFst w) + kapInr (kapSnd w) = w
  rw [kapInl_apply', kapInr_apply', kapFst_ofLp, kapSnd_ofLp, ← WithLp.toLp_add,
    Prod.mk_add_mk, add_zero, zero_add]

private theorem kapAdjoint_inl :
    ContinuousLinearMap.adjoint (kapInl : H →L[ℂ] WithLp 2 (H × H)) = kapFst := by
  have h : kapFst
      = ContinuousLinearMap.adjoint (kapInl : H →L[ℂ] WithLp 2 (H × H)) := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [WithLp.prod_inner_apply, kapInl_ofLp, kapFst_ofLp]
    have e1 : ((y, (0 : H)).1) = y := rfl
    have e2 : ((y, (0 : H)).2) = 0 := rfl
    rw [e1, e2, inner_zero_right, add_zero]
  exact h.symm

private theorem kapAdjoint_inr :
    ContinuousLinearMap.adjoint (kapInr : H →L[ℂ] WithLp 2 (H × H)) = kapSnd := by
  have h : kapSnd
      = ContinuousLinearMap.adjoint (kapInr : H →L[ℂ] WithLp 2 (H × H)) := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [WithLp.prod_inner_apply, kapInr_ofLp, kapSnd_ofLp]
    have e1 : (((0 : H), y).1) = 0 := rfl
    have e2 : (((0 : H), y).2) = y := rfl
    rw [e1, e2, inner_zero_right, zero_add]
  exact h.symm

private theorem kapAdjoint_fst :
    ContinuousLinearMap.adjoint (kapFst : WithLp 2 (H × H) →L[ℂ] H) = kapInl := by
  have h : kapInl
      = ContinuousLinearMap.adjoint (kapFst : WithLp 2 (H × H) →L[ℂ] H) := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x v
    rw [WithLp.prod_inner_apply, kapInl_ofLp, kapFst_ofLp]
    have e1 : ((x, (0 : H)).1) = x := rfl
    have e2 : ((x, (0 : H)).2) = 0 := rfl
    rw [e1, e2, inner_zero_left, add_zero]
  exact h.symm

private theorem kapAdjoint_snd :
    ContinuousLinearMap.adjoint (kapSnd : WithLp 2 (H × H) →L[ℂ] H) = kapInr := by
  have h : kapInr
      = ContinuousLinearMap.adjoint (kapSnd : WithLp 2 (H × H) →L[ℂ] H) := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x v
    rw [WithLp.prod_inner_apply, kapInr_ofLp, kapSnd_ofLp]
    have e1 : (((0 : H), x).1) = 0 := rfl
    have e2 : (((0 : H), x).2) = x := rfl
    rw [e1, e2, inner_zero_left, zero_add]
  exact h.symm

omit [CompleteSpace H] in
private theorem kapNorm_sq (v : WithLp 2 (H × H)) :
    ‖v‖ ^ 2 = ‖kapFst v‖ ^ 2 + ‖kapSnd v‖ ^ 2 := by
  have h := WithLp.prod_norm_sq_eq_of_L2 v
  have e1 : kapFst v = v.fst := WithLp.fstL_apply 2 ℂ H H v
  have e2 : kapSnd v = v.snd := WithLp.sndL_apply 2 ℂ H H v
  rw [e1, e2]
  exact h

omit [CompleteSpace H] in
private theorem kapNorm_fst_le : ‖(kapFst : WithLp 2 (H × H) →L[ℂ] H)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => ?_)
  rw [one_mul]
  have h := WithLp.prod_norm_sq_eq_of_L2 w
  have e1 : kapFst w = w.fst := WithLp.fstL_apply 2 ℂ H H w
  rw [e1]
  have h2 : ‖w.fst‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    have hnn : (0 : ℝ) ≤ ‖w.snd‖ ^ 2 := sq_nonneg _
    linarith
  have h3 : |‖w.fst‖| ≤ ‖w‖ := abs_le_of_sq_le_sq h2 (norm_nonneg _)
  rwa [abs_of_nonneg (norm_nonneg _)] at h3

omit [CompleteSpace H] in
private theorem kapNorm_inr_le : ‖(kapInr : H →L[ℂ] WithLp 2 (H × H))‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  rw [one_mul, kapInr_apply', WithLp.norm_toLp_snd]

omit [CompleteSpace H] in
private theorem kapFst_kapInl_apply (v : H) : kapFst (kapInl v) = v := by
  have h : (kapFst ∘L kapInl) v = (ContinuousLinearMap.id ℂ H) v :=
    congrArg (fun F => F v) kapFst_inl
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h

omit [CompleteSpace H] in
private theorem kapFst_kapInr_apply (v : H) : kapFst (kapInr v) = 0 := by
  have h : (kapFst ∘L kapInr) v = (0 : H →L[ℂ] H) v :=
    congrArg (fun F => F v) kapFst_inr
  simpa only [ContinuousLinearMap.comp_apply, zero_apply] using h

omit [CompleteSpace H] in
private theorem kapSnd_kapInl_apply (v : H) : kapSnd (kapInl v) = 0 := by
  have h : (kapSnd ∘L kapInl) v = (0 : H →L[ℂ] H) v :=
    congrArg (fun F => F v) kapSnd_inl
  simpa only [ContinuousLinearMap.comp_apply, zero_apply] using h

omit [CompleteSpace H] in
private theorem kapSnd_kapInr_apply (v : H) : kapSnd (kapInr v) = v := by
  have h : (kapSnd ∘L kapInr) v = (ContinuousLinearMap.id ℂ H) v :=
    congrArg (fun F => F v) kapSnd_inr
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h

omit [CompleteSpace H] in
private theorem kapProj_apply (w : WithLp 2 (H × H)) :
    kapInl (kapFst w) + kapInr (kapSnd w) = w := by
  have h := DFunLike.congr_fun kapProj_sum w
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using h

omit [CompleteSpace H] in
/-- A corner of a product expands over the middle projection sum. -/
private theorem kapCorner_mul_eq
    (T U : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H))
    (A : WithLp 2 (H × H) →L[ℂ] H) (B : H →L[ℂ] WithLp 2 (H × H)) :
    A ∘L (T * U) ∘L B
      = (A ∘L T ∘L kapInl) * (kapFst ∘L U ∘L B)
        + (A ∘L T ∘L kapInr) * (kapSnd ∘L U ∘L B) := by
  ext v
  simp only [add_apply, mul_apply_eq_comp, ContinuousLinearMap.comp_apply]
  have hproj := kapProj_apply (U (B v))
  conv_lhs => rw [← hproj]
  simp only [map_add]

/-- The `(1,1)` corner of `star T` is the star of the `(1,1)` corner of `T`. -/
private theorem kapCorner_star_11 (T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) :
    kapFst ∘L star T ∘L kapInl = star (kapFst ∘L T ∘L kapInl) := by
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc, kapAdjoint_inl, kapAdjoint_fst]

/-- The `(1,2)` corner of `star T` is the star of the `(2,1)` corner of `T`. -/
private theorem kapCorner_star_12 (T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) :
    kapFst ∘L star T ∘L kapInr = star (kapSnd ∘L T ∘L kapInl) := by
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc, kapAdjoint_inl, kapAdjoint_snd]

/-- The `(2,1)` corner of `star T` is the star of the `(1,2)` corner of `T`. -/
private theorem kapCorner_star_21 (T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) :
    kapSnd ∘L star T ∘L kapInl = star (kapFst ∘L T ∘L kapInr) := by
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc, kapAdjoint_inr, kapAdjoint_fst]

/-- The `(2,2)` corner of `star T` is the star of the `(2,2)` corner of `T`. -/
private theorem kapCorner_star_22 (T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) :
    kapSnd ∘L star T ∘L kapInr = star (kapSnd ∘L T ∘L kapInr) := by
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc, kapAdjoint_inr, kapAdjoint_snd]

omit [CompleteSpace H] in
/-- A corner of a sum is the sum of the corners. -/
private theorem kapCorner_add_eq
    (S T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H))
    (A : WithLp 2 (H × H) →L[ℂ] H) (B : H →L[ℂ] WithLp 2 (H × H)) :
    A ∘L (S + T) ∘L B = A ∘L S ∘L B + A ∘L T ∘L B := by
  ext v
  simp only [add_apply, ContinuousLinearMap.comp_apply, map_add]

omit [CompleteSpace H] in
/-- A corner of zero is zero. -/
private theorem kapCorner_zero_eq
    (A : WithLp 2 (H × H) →L[ℂ] H) (B : H →L[ℂ] WithLp 2 (H × H)) :
    A ∘L (0 : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) ∘L B = 0 := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, map_zero, zero_apply]

omit [CompleteSpace H] in
/-- The `(1,1)` corner of a scalar is the scalar. -/
private theorem kapCorner_alg_11 (c : ℂ) :
    kapFst ∘L algebraMap ℂ (WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) c ∘L kapInl
      = algebraMap ℂ (H →L[ℂ] H) c := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply_eq_self, map_smul, kapFst_kapInl_apply]

omit [CompleteSpace H] in
/-- The `(1,2)` corner of a scalar is zero. -/
private theorem kapCorner_alg_12 (c : ℂ) :
    kapFst ∘L algebraMap ℂ (WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) c ∘L kapInr
      = 0 := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply_eq_self, map_smul, kapFst_kapInr_apply, smul_zero,
    zero_apply]

omit [CompleteSpace H] in
/-- The `(2,1)` corner of a scalar is zero. -/
private theorem kapCorner_alg_21 (c : ℂ) :
    kapSnd ∘L algebraMap ℂ (WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) c ∘L kapInl
      = 0 := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply_eq_self, map_smul, kapSnd_kapInl_apply, smul_zero,
    zero_apply]

omit [CompleteSpace H] in
/-- The `(2,2)` corner of a scalar is the scalar. -/
private theorem kapCorner_alg_22 (c : ℂ) :
    kapSnd ∘L algebraMap ℂ (WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) c ∘L kapInr
      = algebraMap ℂ (H →L[ℂ] H) c := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply_eq_self, map_smul, kapSnd_kapInr_apply]

end KapL2Prod

section KapCorner

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The 2x2 corner algebra on `H ⊕ H`: operators whose four corners lie in `S`. -/
private noncomputable def kapCorner (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    StarSubalgebra ℂ (WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) where
  carrier := {T | kapFst ∘L T ∘L kapInl ∈ S ∧ kapFst ∘L T ∘L kapInr ∈ S ∧
    kapSnd ∘L T ∘L kapInl ∈ S ∧ kapSnd ∘L T ∘L kapInr ∈ S}
  zero_mem' := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (rw [kapCorner_zero_eq]; exact zero_mem S)
  add_mem' := by
    intro T U hT hU
    obtain ⟨hT11, hT12, hT21, hT22⟩ := hT
    obtain ⟨hU11, hU12, hU21, hU22⟩ := hU
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [kapCorner_add_eq]; exact add_mem hT11 hU11
    · rw [kapCorner_add_eq]; exact add_mem hT12 hU12
    · rw [kapCorner_add_eq]; exact add_mem hT21 hU21
    · rw [kapCorner_add_eq]; exact add_mem hT22 hU22
  mul_mem' := by
    intro T U hT hU
    obtain ⟨hT11, hT12, hT21, hT22⟩ := hT
    obtain ⟨hU11, hU12, hU21, hU22⟩ := hU
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [kapCorner_mul_eq]; exact add_mem (mul_mem hT11 hU11) (mul_mem hT12 hU21)
    · rw [kapCorner_mul_eq]; exact add_mem (mul_mem hT11 hU12) (mul_mem hT12 hU22)
    · rw [kapCorner_mul_eq]; exact add_mem (mul_mem hT21 hU11) (mul_mem hT22 hU21)
    · rw [kapCorner_mul_eq]; exact add_mem (mul_mem hT21 hU12) (mul_mem hT22 hU22)
  algebraMap_mem' := by
    intro c
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [kapCorner_alg_11]; exact S.algebraMap_mem c
    · rw [kapCorner_alg_12]; exact zero_mem S
    · rw [kapCorner_alg_21]; exact zero_mem S
    · rw [kapCorner_alg_22]; exact S.algebraMap_mem c
  star_mem' := by
    intro T hT
    obtain ⟨hT11, hT12, hT21, hT22⟩ := hT
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [kapCorner_star_11]; exact star_mem hT11
    · rw [kapCorner_star_12]; exact star_mem hT21
    · rw [kapCorner_star_21]; exact star_mem hT12
    · rw [kapCorner_star_22]; exact star_mem hT22

/-- Membership in `kapCorner` unfolds definitionally. -/
private theorem kapMem_corner (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) :
    T ∈ kapCorner S ↔ kapFst ∘L T ∘L kapInl ∈ S ∧ kapFst ∘L T ∘L kapInr ∈ S ∧
      kapSnd ∘L T ∘L kapInl ∈ S ∧ kapSnd ∘L T ∘L kapInr ∈ S :=
  Iff.rfl

end KapCorner

section KapOffDiag

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The off-diagonal lift of `x : B(H)` to `B(H ⊕ H)`. -/
private noncomputable def kapOffDiag (x : H →L[ℂ] H) :
    WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H) :=
  kapInl ∘L x ∘L kapSnd + kapInr ∘L star x ∘L kapFst

/-- The adjoint of `star x` is `x`. -/
private theorem kapAdjoint_star (x : H →L[ℂ] H) :
    ContinuousLinearMap.adjoint (star x) = x := by
  rw [← ContinuousLinearMap.star_eq_adjoint, star_star]

/-- Star swaps the first off-diagonal summand to the second. -/
private theorem kapOffDiag_star_fst (x : H →L[ℂ] H) :
    star (kapInl ∘L x ∘L kapSnd) = kapInr ∘L star x ∘L kapFst := by
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc, kapAdjoint_inl, kapAdjoint_snd]

/-- Star swaps the second off-diagonal summand to the first. -/
private theorem kapOffDiag_star_snd (x : H →L[ℂ] H) :
    star (kapInr ∘L star x ∘L kapFst) = kapInl ∘L x ∘L kapSnd := by
  conv_lhs => rw [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    kapAdjoint_inr, kapAdjoint_fst, kapAdjoint_star,
    ContinuousLinearMap.comp_assoc]

/-- The off-diagonal lift is self-adjoint. -/
private theorem kapOffDiag_selfAdjoint (x : H →L[ℂ] H) :
    IsSelfAdjoint (kapOffDiag x) := by
  rw [isSelfAdjoint_iff]
  unfold kapOffDiag
  rw [StarRing.star_add, kapOffDiag_star_fst, kapOffDiag_star_snd, add_comm]

/-- First component of the off-diagonal lift applied to a vector. -/
private theorem kapOffDiag_fst_apply (x : H →L[ℂ] H) (v : WithLp 2 (H × H)) :
    kapFst ((kapOffDiag x) v) = x (kapSnd v) := by
  unfold kapOffDiag
  simp only [add_apply, ContinuousLinearMap.comp_apply, map_add,
    kapFst_kapInl_apply, kapFst_kapInr_apply, add_zero]

/-- Second component of the off-diagonal lift applied to a vector. -/
private theorem kapOffDiag_snd_apply (x : H →L[ℂ] H) (v : WithLp 2 (H × H)) :
    kapSnd ((kapOffDiag x) v) = star x (kapFst v) := by
  unfold kapOffDiag
  simp only [add_apply, ContinuousLinearMap.comp_apply, map_add,
    kapSnd_kapInl_apply, kapSnd_kapInr_apply, zero_add]

/-- The off-diagonal lift does not increase the norm. -/
private theorem kapOffDiag_norm (x : H →L[ℂ] H) (hnorm : ‖x‖ ≤ 1) :
    ‖kapOffDiag x‖ ≤ 1 := by
  have hstar : ‖star x‖ ≤ 1 := by
    rw [norm_star]
    exact hnorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  rw [one_mul]
  have b1 : ‖x (kapSnd v)‖ ≤ ‖kapSnd v‖ := by
    calc ‖x (kapSnd v)‖ ≤ ‖x‖ * ‖kapSnd v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖kapSnd v‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ = ‖kapSnd v‖ := one_mul _
  have b2 : ‖star x (kapFst v)‖ ≤ ‖kapFst v‖ := by
    calc ‖star x (kapFst v)‖ ≤ ‖star x‖ * ‖kapFst v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖kapFst v‖ :=
        mul_le_mul_of_nonneg_right hstar (norm_nonneg _)
      _ = ‖kapFst v‖ := one_mul _
  have hsq := kapNorm_sq ((kapOffDiag x) v)
  rw [kapOffDiag_fst_apply, kapOffDiag_snd_apply] at hsq
  have hsqv := kapNorm_sq v
  have g1 : ‖x (kapSnd v)‖ ^ 2 ≤ ‖kapSnd v‖ ^ 2 := by
    nlinarith [b1, sub_nonneg.mpr b1,
      add_nonneg (norm_nonneg (kapSnd v)) (norm_nonneg (x (kapSnd v)))]
  have g2 : ‖star x (kapFst v)‖ ^ 2 ≤ ‖kapFst v‖ ^ 2 := by
    nlinarith [b2, sub_nonneg.mpr b2,
      add_nonneg (norm_nonneg (kapFst v)) (norm_nonneg (star x (kapFst v)))]
  have hle : ‖(kapOffDiag x) v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    linarith [hsq, hsqv, g1, g2]
  have h3 : |‖(kapOffDiag x) v‖| ≤ ‖v‖ :=
    abs_le_of_sq_le_sq hle (norm_nonneg _)
  rwa [abs_of_nonneg (norm_nonneg _)] at h3

/-- The `(1,2)` corner of the off-diagonal lift recovers `x`. -/
private theorem kapOffDiag_corner (x : H →L[ℂ] H) :
    kapFst ∘L kapOffDiag x ∘L kapInr = x := by
  ext v
  unfold kapOffDiag
  simp only [ContinuousLinearMap.comp_apply, add_apply, map_zero,
    kapSnd_kapInr_apply, kapFst_kapInr_apply, kapFst_kapInl_apply, add_zero]

end KapOffDiag

section KapPsi

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The pair-to-corner map `SOT(H) × SOT(H) → SOT(H ⊕ H)`. -/
private noncomputable def kapPsi (p q : H →Lₚₜ[ℂ] H) :
    WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) :=
  kapOfBounded (kapInl ∘L toBounded p ∘L kapSnd + kapInr ∘L toBounded q ∘L kapFst)

/-- The pair-to-corner map is SOT-continuous. -/
private theorem kapPsi_continuous :
    Continuous (fun pq : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) => kapPsi pq.1 pq.2) := by
  refine PointwiseConvergenceCLM.continuous_of_continuous_eval fun w => ?_
  have key : ∀ pq : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H), kapPsi pq.1 pq.2 w
      = kapInl (pq.1 (kapSnd w)) + kapInr (pq.2 (kapFst w)) := by
    intro pq
    unfold kapPsi
    simp only [kapOfBounded_apply, add_apply, ContinuousLinearMap.comp_apply,
      kapToBounded_apply]
  simp only [key]
  exact (kapInl.cont.comp ((kapEval_continuous _).comp continuous_fst)).add
    (kapInr.cont.comp ((kapEval_continuous _).comp continuous_snd))

/-- The four corners of `Ψ p q` are `0`, `toBounded p`, `toBounded q`, `0`. -/
private theorem kapPsi_corners (p q : H →Lₚₜ[ℂ] H) :
    kapFst ∘L toBounded (kapPsi p q) ∘L kapInl = 0 ∧
    kapFst ∘L toBounded (kapPsi p q) ∘L kapInr = toBounded p ∧
    kapSnd ∘L toBounded (kapPsi p q) ∘L kapInl = toBounded q ∧
    kapSnd ∘L toBounded (kapPsi p q) ∘L kapInr = 0 := by
  have hT : toBounded (kapPsi p q)
      = kapInl ∘L toBounded p ∘L kapSnd + kapInr ∘L toBounded q ∘L kapFst :=
    kapToBounded_ofBounded _
  rw [hT]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext v
    simp only [ContinuousLinearMap.comp_apply, add_apply, map_add, map_zero,
      kapSnd_kapInl_apply, kapFst_kapInl_apply, kapFst_kapInr_apply, add_zero,
      zero_apply]
  · ext v
    simp only [ContinuousLinearMap.comp_apply, add_apply, map_zero,
      kapSnd_kapInr_apply, kapFst_kapInr_apply, kapFst_kapInl_apply, add_zero]
  · ext v
    simp only [ContinuousLinearMap.comp_apply, add_apply, map_zero,
      kapSnd_kapInl_apply, kapFst_kapInl_apply, kapSnd_kapInr_apply, zero_add]
  · ext v
    simp only [ContinuousLinearMap.comp_apply, add_apply, map_add, map_zero,
      kapSnd_kapInr_apply, kapFst_kapInr_apply, kapSnd_kapInl_apply, zero_add,
      zero_apply]

/-- `Ψ` maps `Ŝ ×ˢ Ŝ` into the corner preimage set. -/
private theorem kapPsi_mem_corner (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {p q : H →Lₚₜ[ℂ] H} (hp : toBounded p ∈ (↑S : Set (H →L[ℂ] H)))
    (hq : toBounded q ∈ (↑S : Set (H →L[ℂ] H))) :
    kapPsi p q ∈ {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) |
      toBounded P ∈ ↑(kapCorner S)} := by
  obtain ⟨e11, e12, e21, e22⟩ := kapPsi_corners p q
  have h11 : kapFst ∘L toBounded (kapPsi p q) ∘L kapInl ∈ (↑S : Set (H →L[ℂ] H)) := by
    rw [e11]; exact zero_mem S
  have h12 : kapFst ∘L toBounded (kapPsi p q) ∘L kapInr ∈ (↑S : Set (H →L[ℂ] H)) := by
    rw [e12]; exact hp
  have h21 : kapSnd ∘L toBounded (kapPsi p q) ∘L kapInl ∈ (↑S : Set (H →L[ℂ] H)) := by
    rw [e21]; exact hq
  have h22 : kapSnd ∘L toBounded (kapPsi p q) ∘L kapInr ∈ (↑S : Set (H →L[ℂ] H)) := by
    rw [e22]; exact zero_mem S
  exact ⟨h11, h12, h21, h22⟩

/-- The off-diagonal lift lies in the SOT-closure of the corner algebra. -/
private theorem kapOffDiag_mem_closure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : H →L[ℂ] H)
    (hxmem : kapOfBounded x
      ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))}) :
    kapOfBounded (kapOffDiag x) ∈ closure
      {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) |
        toBounded P ∈ ↑(kapCorner S)} := by
  have hstar : kapStar (kapOfBounded x)
      ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))} :=
    kapStar_mem_closure_of_convex (kapSotConvex S) (kapSotStar S) hxmem
  have hpair : (kapOfBounded x, kapStar (kapOfBounded x)) ∈ closure
      ({p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))} ×ˢ
        {p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))}) := by
    rw [closure_prod_eq]
    exact ⟨hxmem, hstar⟩
  have hmaps : Set.MapsTo
      (fun pq : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) => kapPsi pq.1 pq.2)
      ({p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))} ×ˢ
        {p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))})
      {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) |
        toBounded P ∈ ↑(kapCorner S)} := by
    intro pq hpq
    obtain ⟨hp1, hp2⟩ := hpq
    exact kapPsi_mem_corner S hp1 hp2
  have hmap := map_mem_closure kapPsi_continuous hpair hmaps
  have hmap' : kapPsi (kapOfBounded x) (kapStar (kapOfBounded x)) ∈ closure
      {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) |
        toBounded P ∈ ↑(kapCorner S)} := hmap
  have heq : kapPsi (kapOfBounded x) (kapStar (kapOfBounded x))
      = kapOfBounded (kapOffDiag x) := by
    unfold kapPsi kapOffDiag
    rw [kapToBounded_star, kapToBounded_ofBounded]
  rw [heq] at hmap'
  exact hmap'

end KapPsi

section KapGamma

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The `(1,2)` corner map `SOT(H ⊕ H) → SOT(H)`. -/
private noncomputable def kapGamma (P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H)) :
    H →Lₚₜ[ℂ] H :=
  kapOfBounded (kapFst ∘L toBounded P ∘L kapInr)

/-- The corner map is SOT-continuous. -/
private theorem kapGamma_continuous :
    Continuous (fun P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) => kapGamma P) := by
  refine PointwiseConvergenceCLM.continuous_of_continuous_eval fun w => ?_
  have key : ∀ P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H),
      kapGamma P w = kapFst (P (kapInr w)) := by
    intro P
    unfold kapGamma
    simp only [kapOfBounded_apply, ContinuousLinearMap.comp_apply,
      kapToBounded_apply]
  simp only [key]
  exact kapFst.cont.comp (kapEval_continuous (kapInr w))

omit [CompleteSpace H] in
/-- The corner map does not increase the norm. -/
private theorem kapGamma_norm (T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H))
    (hT : ‖T‖ ≤ 1) : ‖kapFst ∘L T ∘L kapInr‖ ≤ 1 := by
  have hF : ∀ w : WithLp 2 (H × H), ‖kapFst w‖ ≤ ‖w‖ := by
    intro w
    calc ‖kapFst w‖ ≤ ‖(kapFst : WithLp 2 (H × H) →L[ℂ] H)‖ * ‖w‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖w‖ :=
        mul_le_mul_of_nonneg_right kapNorm_fst_le (norm_nonneg w)
      _ = ‖w‖ := one_mul _
  have hT' : ∀ u : WithLp 2 (H × H), ‖T u‖ ≤ ‖u‖ := by
    intro u
    calc ‖T u‖ ≤ ‖T‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg u)
      _ = ‖u‖ := one_mul _
  have hI : ∀ v : H, ‖kapInr v‖ ≤ ‖v‖ := by
    intro v
    calc ‖kapInr v‖ ≤ ‖(kapInr : H →L[ℂ] WithLp 2 (H × H))‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right kapNorm_inr_le (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  rw [one_mul]
  calc ‖(kapFst ∘L T ∘L kapInr) v‖ = ‖kapFst (T (kapInr v))‖ := rfl
    _ ≤ ‖T (kapInr v)‖ := hF _
    _ ≤ ‖kapInr v‖ := hT' _
    _ ≤ ‖v‖ := hI _

/-- The corner map sends the corner ball into the ball of `S`. -/
private theorem kapGamma_maps (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H)}
    (hP : P ∈ {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) |
        toBounded P ∈ ↑(kapCorner S)} ∩
      {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) | ‖toBounded P‖ ≤ 1}) :
    kapGamma P ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))} ∩
      {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1} := by
  obtain ⟨hPcorner, hPnorm⟩ := hP
  have hcorn : toBounded (kapGamma P) = kapFst ∘L toBounded P ∘L kapInr :=
    kapToBounded_ofBounded _
  have h12 : kapFst ∘L toBounded P ∘L kapInr ∈ (↑S : Set (H →L[ℂ] H)) :=
    ((kapMem_corner S _).mp hPcorner).2.1
  have hmem : toBounded (kapGamma P) ∈ (↑S : Set (H →L[ℂ] H)) := by
    rw [hcorn]; exact h12
  have hnorm : ‖toBounded (kapGamma P)‖ ≤ 1 := by
    rw [hcorn]; exact kapGamma_norm _ hPnorm
  exact ⟨hmem, hnorm⟩

end KapGamma

/--
For a complex Hilbert space `H` and unital `∗`-subalgebra `S ⊆ B(H)`, the SOT-closure of its
operator-norm unit ball equals the unit ball of its SOT-closure, with norm and membership read via
`toBounded` and closure taken in `H →Lₚₜ[ℂ] H`. Source: Kaplansky density theorem, I. Kaplansky,
Pacific J. Math. 1 (1951), 227–232; see Takesaki, Theory of Operator Algebras I, Density Theorem
and Kadison–Ringrose Vol I; Lean is SOT-closure equality of unit balls via toBounded conversion,
full infinite-dimensional form.

Proves `Wanted` entry `kaplansky_density_theorem`.
-/
public theorem kaplansky_density_theorem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure ({x : H →Lₚₜ[ℂ] H | toBounded x ∈ (S : Set (H →L[ℂ] H)) ∧ ‖toBounded x‖ ≤ 1} :
      Set (H →Lₚₜ[ℂ] H))
    = {y : H →Lₚₜ[ℂ] H | y ∈ closure ({p : H →Lₚₜ[ℂ] H | toBounded p ∈ (S : Set (H →L[ℂ] H))} :
      Set (H →Lₚₜ[ℂ] H)) ∧ ‖toBounded y‖ ≤ 1} := by
  have hset : ({x : H →Lₚₜ[ℂ] H | toBounded x ∈ (S : Set (H →L[ℂ] H)) ∧
      ‖toBounded x‖ ≤ 1} : Set (H →Lₚₜ[ℂ] H))
      = {p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))} ∩
        {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1} := rfl
  rw [hset]
  apply Set.ext
  intro z
  constructor
  · intro hz
    constructor
    · exact closure_mono Set.inter_subset_left hz
    · exact closure_minimal Set.inter_subset_right kapIsClosed_ball hz
  · intro hz
    obtain ⟨hymem, hnorm⟩ := hz
    have hxmem : kapOfBounded (toBounded z)
        ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))} := by
      rw [kapOfBounded_toBounded]
      exact hymem
    have hXsa : IsSelfAdjoint (kapOffDiag (toBounded z)) :=
      kapOffDiag_selfAdjoint _
    have hXnorm : ‖kapOffDiag (toBounded z)‖ ≤ 1 :=
      kapOffDiag_norm _ hnorm
    have hXmem : kapOfBounded (kapOffDiag (toBounded z)) ∈ closure
        {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) |
          toBounded P ∈ ↑(kapCorner S)} :=
      kapOffDiag_mem_closure S _ hxmem
    have hball := kapSelfAdjoint_mem_closure_ball (kapCorner S)
      (kapOffDiag (toBounded z)) hXsa hXnorm hXmem
    have hmaps : Set.MapsTo
        (fun P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) => kapGamma P)
        ({P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) |
            toBounded P ∈ ↑(kapCorner S)} ∩
          {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) | ‖toBounded P‖ ≤ 1})
        ({p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))} ∩
          {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1}) := by
      intro P hP
      exact kapGamma_maps S hP
    have hfin := map_mem_closure kapGamma_continuous hball hmaps
    have hfin' : kapGamma (kapOfBounded (kapOffDiag (toBounded z))) ∈ closure
        ({p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))} ∩
          {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1}) := hfin
    have heq : kapGamma (kapOfBounded (kapOffDiag (toBounded z))) = z := by
      have h1 : kapGamma (kapOfBounded (kapOffDiag (toBounded z)))
          = kapOfBounded (kapFst ∘L kapOffDiag (toBounded z) ∘L kapInr) := by
        unfold kapGamma
        rw [kapToBounded_ofBounded]
      rw [h1, kapOffDiag_corner, kapOfBounded_toBounded]
    rw [heq] at hfin'
    exact hfin'

end MathlibExt.Analysis.CStarAlgebra.KaplanskyDensityWanted
