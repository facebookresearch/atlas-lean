/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.LocalReflexivityWanted

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable section

/-- Real scalar structure on a `𝕜`-normed space, from restriction of scalars. -/
private noncomputable instance plrNormedReal (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ 𝕜 E

/-- Real-`𝕜` scalar tower on a `𝕜`-normed space. -/
private instance plrTowerReal (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    IsScalarTower ℝ 𝕜 E :=
  IsScalarTower.restrictScalars ℝ 𝕜 E

/-- The norm of a scalar is the real part of its product with some unit scalar. -/
private theorem plr_exists_unit_mul (c : 𝕜) :
    ∃ u : 𝕜, ‖u‖ = 1 ∧ RCLike.re (u * c) = ‖c‖ := by
  by_cases hc : c = 0
  · subst hc
    exact ⟨1, norm_one, by simp⟩
  · have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hne : ‖c‖ ≠ 0 := ne_of_gt hpos
    refine ⟨(↑(‖c‖⁻¹) : 𝕜) * starRingEnd 𝕜 c, ?_, ?_⟩
    · rw [norm_mul, RCLike.norm_ofReal, RCLike.norm_conj,
        abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hne]
    · have hcc : starRingEnd 𝕜 c * c = (↑‖c‖ : 𝕜) ^ 2 := by
        rw [mul_comm]
        exact RCLike.mul_conj c
      have hreal : ‖c‖⁻¹ * ‖c‖ ^ 2 = ‖c‖ := by
        rw [sq, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      have hmul2 : (↑(‖c‖⁻¹) : 𝕜) * ((↑‖c‖ : 𝕜) ^ 2) = (↑‖c‖ : 𝕜) := by
        have h : (↑(‖c‖⁻¹ * ‖c‖ ^ 2) : 𝕜) = (↑‖c‖ : 𝕜) := by rw [hreal]
        rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, h]
      rw [mul_assoc, hcc, hmul2, RCLike.ofReal_re]

/-- The canonical embedding into the double dual is injective. -/
private theorem plr_J_inj {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    Function.Injective (NormedSpace.inclusionInDoubleDual 𝕜 E) := by
  intro x y h
  apply (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E)).injective
  change (NormedSpace.inclusionInDoubleDual 𝕜 E) x =
    (NormedSpace.inclusionInDoubleDual 𝕜 E) y
  exact h

/-- The subspace of `M'` consisting of points in the range of `J`. -/
private def plr_M0 {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))) : Submodule 𝕜 ↥Mp :=
  (LinearMap.range (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap).comap
    Mp.subtype

/-- The inverse of `J` on `M₀`, as a linear map. -/
private noncomputable def plr_S0 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))) :
    ↥(plr_M0 Mp) →ₗ[𝕜] E :=
  (LinearEquiv.ofInjective (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap
    plr_J_inj).symm.toLinearMap.comp
    (LinearMap.codRestrict
      (LinearMap.range (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap)
      (Mp.subtype.comp (plr_M0 Mp).subtype) (fun u => u.prop))

/-- `S₀` inverts `J`: applying `J` after `S₀` recovers the coercion. -/
private theorem plr_S0_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    (u : ↥(plr_M0 Mp)) :
    (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap (plr_S0 Mp u)
      = Mp.subtype u.val :=
  LinearEquiv.ofInjective_symm_apply _ (h := plr_J_inj) _

/-- Real part of a finite sum is the sum of the real parts. -/
private theorem plr_re_sum {ι : Type*} (s : Finset ι) (F : ι → 𝕜) :
    RCLike.re (∑ i ∈ s, F i) = ∑ i ∈ s, RCLike.re (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty, RCLike.zero_re]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add RCLike.re, ih]

/-- A continuous linear functional on a pi type is the sum of its
single-coordinate composites. -/
private theorem plr_clm_pi_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Psi : (ι → E) →L[𝕜] 𝕜) (v : ι → E) :
    Psi v = ∑ k, (Psi.comp (ContinuousLinearMap.single 𝕜 (fun _ => E) k)) (v k) :=
  (ContinuousLinearMap.sum_comp_single 𝕜 (fun _ => E) Psi v).symm

/-- Normed group structure on a submodule of the bidual. Stated with ground `R M`
so that typeclass resolution unifies first-order (the generic submodule instances
leave `↥?p` stuck). -/
private instance plrNACG_Mp {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))) :
    NormedAddCommGroup ↥Mp :=
  @Submodule.normedAddCommGroup 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) _ _ _ Mp

/-- Normed space structure on a submodule of the bidual. -/
private instance plrNS_Mp {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))) : NormedSpace 𝕜 ↥Mp :=
  @Submodule.normedSpace 𝕜 𝕜 _ _ _
    (StrongDual 𝕜 (StrongDual 𝕜 E)) _ _ _ _ Mp

/-- Normed group structure on the `M₀` submodule. -/
private instance plrNACG_M0 {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))) :
    NormedAddCommGroup ↥(plr_M0 Mp) :=
  @Submodule.normedAddCommGroup 𝕜 ↥Mp _ _ _ (plr_M0 Mp)

/-- Normed group structure on a complement submodule. -/
private instance plrNACG_C {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    (C : Submodule 𝕜 ↥Mp) : NormedAddCommGroup ↥C :=
  @Submodule.normedAddCommGroup 𝕜 ↥Mp _ _ _ C

/-- A finite-dimensional submodule of the bidual is a proper metric space. -/
private instance plrProper_Mp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp] : ProperSpace ↥Mp :=
  FiniteDimensional.proper_rclike 𝕜 ↥Mp

/-- First projection of the `M₀ ⊕ C` decomposition inside `M'`. -/
private def plr_pi0 {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C) :
    ↥Mp →ₗ[𝕜] ↥(plr_M0 Mp) :=
  (plr_M0 Mp).projectionOnto C hC

/-- Second projection of the `M₀ ⊕ C` decomposition inside `M'`. -/
private def plr_pi1 {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C) :
    ↥Mp →ₗ[𝕜] ↥C :=
  C.projectionOnto (plr_M0 Mp) hC.symm

/-- The first projection fixes `M₀`. -/
private theorem plr_pi0_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (u : ↥(plr_M0 Mp)) :
    plr_pi0 Mp C hC ((plr_M0 Mp).subtype u) = u :=
  Submodule.projectionOnto_apply_left hC u

/-- The second projection vanishes on `M₀`. -/
private theorem plr_pi1_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (u : ↥(plr_M0 Mp)) :
    plr_pi1 Mp C hC ((plr_M0 Mp).subtype u) = 0 :=
  Submodule.projectionOnto_apply_right hC.symm u

/-- The two projections sum to the identity on `M'`. -/
private theorem plr_add_id {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C) :
    (plr_M0 Mp).subtype.comp (plr_pi0 Mp C hC)
      + C.subtype.comp (plr_pi1 Mp C hC) = LinearMap.id :=
  Submodule.subtype_comp_projectionOnto_add_eq_id hC

/-- Decomposition of a point of `M'` into its `M₀` part and `C` coordinates,
pushed into the bidual. -/
private theorem plr_decomp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp]
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (m : ↥Mp) :
    Mp.subtype m = (NormedSpace.inclusionInDoubleDual 𝕜 E)
          (plr_S0 Mp (plr_pi0 Mp C hC m))
        + ∑ j, ((Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC m) j)
          • Mp.subtype (C.subtype ((Module.finBasis 𝕜 ↥C) j)) := by
  have hmod : (plr_M0 Mp).subtype (plr_pi0 Mp C hC m)
      + C.subtype (plr_pi1 Mp C hC m) = m := by
    have h := LinearMap.congr_fun (plr_add_id Mp C hC) m
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.id_apply] at h
    exact h
  have hCexp : plr_pi1 Mp C hC m
      = ∑ j, ((Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC m) j)
        • ((Module.finBasis 𝕜 ↥C) j) :=
    (Module.Basis.sum_repr _ _).symm
  have hJ : Mp.subtype ((plr_M0 Mp).subtype (plr_pi0 Mp C hC m))
      = (NormedSpace.inclusionInDoubleDual 𝕜 E)
        (plr_S0 Mp (plr_pi0 Mp C hC m)) :=
    (plr_S0_mem Mp _).symm
  have hbase := congrArg Mp.subtype hmod
  rw [map_add, hCexp, map_sum, map_sum] at hbase
  simp only [map_smul] at hbase
  rw [hJ] at hbase
  exact hbase.symm

/-- The homogenized upper-bound map of N5: `(t, y)` goes to
`t • a + Σ c • y` at each net point. -/
private noncomputable def plr_L {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜) :
    (𝕜 × (Fin p → E)) →L[𝕜] (ι → E) :=
  (ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.id 𝕜 𝕜).smulRight (a k)).comp
      (ContinuousLinearMap.fst 𝕜 𝕜 (Fin p → E))
    + (ContinuousLinearMap.pi fun k =>
      ∑ j, (c k j) • ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.snd 𝕜 𝕜 (Fin p → E))

/-- The homogenized equation map of N5. -/
private noncomputable def plr_Phi {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (f : Fin q → StrongDual 𝕜 E) (g : ι → StrongDual 𝕜 E) :
    (𝕜 × (Fin p → E)) →L[𝕜]
      (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) :=
  (ContinuousLinearMap.fst 𝕜 𝕜 (Fin p → E)).prod
    ((ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
        ((f i).comp (ContinuousLinearMap.proj j)).comp
          (ContinuousLinearMap.snd 𝕜 𝕜 (Fin p → E))).prod
      (ContinuousLinearMap.pi fun k =>
        (g k).comp ((ContinuousLinearMap.proj k).comp (plr_L a c))))

/-- The target point of N5. -/
private def plr_w {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {p q : ℕ} {ι : Type*}
    (b : Fin p → StrongDual 𝕜 (StrongDual 𝕜 E))
    (f : Fin q → StrongDual 𝕜 E)
    (m : ι → StrongDual 𝕜 (StrongDual 𝕜 E))
    (g : ι → StrongDual 𝕜 E) :
    𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜) :=
  (1, (fun i j => b j (f i)), (fun k => m k (g k)))

/-- Application formula for `plr_L`. -/
private theorem plr_L_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜) (z : 𝕜 × (Fin p → E)) (k : ι) :
    plr_L a c z k = z.1 • a k + ∑ j, c k j • z.2 j := by
  simp only [plr_L, Pi.add_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.id_apply,
    FunLike.coe_sum, Finset.sum_apply]

/-- Application formula for `plr_Phi`. -/
private theorem plr_Phi_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (f : Fin q → StrongDual 𝕜 E) (g : ι → StrongDual 𝕜 E)
    (z : 𝕜 × (Fin p → E)) :
    plr_Phi a c f g z
      = (z.1, (fun i j => f i (z.2 j)),
        (fun k => g k (plr_L a c z k))) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [plr_Phi, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst']
  · funext i j
    simp only [plr_Phi, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply]
  · funext k
    simp only [plr_Phi, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply]

/-- A continuous linear functional on `𝕜` is determined by its value at `1`. -/
private theorem plr_clm_smul_apply (f : 𝕜 →L[𝕜] 𝕜) (x : 𝕜) :
    f x = x * f 1 := by
  have hx : x = x • (1 : 𝕜) := by rw [smul_eq_mul, mul_one]
  conv_lhs => rw [hx, map_smul, smul_eq_mul]

/-- The first-coordinate part of the `λ`-expansion on `V`. -/
private theorem plr_lam_fst {p q : ℕ} {ι : Type*}
    (lam : (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) →L[𝕜] 𝕜) (s : 𝕜) :
    lam (s, 0, 0) = s * lam (1, 0, 0) := by
  have e : ((s, 0, 0) : 𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜))
      = s • ((1, 0, 0) : 𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) := by
    ext <;> simp
  rw [e, map_smul, smul_eq_mul]

/-- The third-coordinate part of the `λ`-expansion on `V`. -/
private theorem plr_lam_last {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) →L[𝕜] 𝕜) (h : ι → 𝕜) :
    lam (0, 0, h) = ∑ k, h k * lam (0, 0, Pi.single k 1) := by
  have hg : ∀ x : ι → 𝕜,
      lam.comp ((ContinuousLinearMap.inr 𝕜 𝕜
        ((Fin q → Fin p → 𝕜) × (ι → 𝕜))).comp
        (ContinuousLinearMap.inr 𝕜 (Fin q → Fin p → 𝕜) (ι → 𝕜))) x
        = lam (0, 0, x) := fun x => rfl
  rw [← hg h, plr_clm_pi_sum _ h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [plr_clm_smul_apply]
  congr 1

/-- The middle-coordinate part of the `λ`-expansion on `V`, by applying the
one-index expansion twice. -/
private theorem plr_lam_mid {p q : ℕ} {ι : Type*}
    (lam : (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) →L[𝕜] 𝕜)
    (r : Fin q → Fin p → 𝕜) :
    lam (0, r, 0)
      = ∑ i, ∑ j, r i j * lam (0, Pi.single i (Pi.single j 1), 0) := by
  have hg : ∀ x : Fin q → Fin p → 𝕜,
      lam.comp ((ContinuousLinearMap.inr 𝕜 𝕜
        ((Fin q → Fin p → 𝕜) × (ι → 𝕜))).comp
        (ContinuousLinearMap.inl 𝕜 (Fin q → Fin p → 𝕜) (ι → 𝕜))) x
        = lam (0, x, 0) := fun x => rfl
  rw [← hg r, plr_clm_pi_sum _ r]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [plr_clm_pi_sum _ (r i)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [plr_clm_smul_apply]
  congr 1

/-- Full `λ`-expansion on `V = 𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)`. -/
private theorem plr_lam_expand {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) →L[𝕜] 𝕜)
    (v : 𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) :
    lam v = v.1 * lam (1, 0, 0)
      + (∑ i, ∑ j, v.2.1 i j * lam (0, Pi.single i (Pi.single j 1), 0))
      + ∑ k, v.2.2 k * lam (0, 0, Pi.single k 1) := by
  have hsplit : v = (v.1, 0, 0) + (0, v.2.1, 0) + (0, 0, v.2.2) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
  conv_lhs => rw [hsplit]
  rw [map_add, map_add, plr_lam_fst, plr_lam_mid, plr_lam_last]

/-- The value of `plr_Phi` at `(1, 0)`. -/
private theorem plr_Phi10 {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (f : Fin q → StrongDual 𝕜 E) (g : ι → StrongDual 𝕜 E) :
    plr_Phi a c f g (1, 0) = (1, 0, fun k => g k (a k)) := by
  have hL10 : ∀ k, plr_L a c (1, 0) k = a k := by
    intro k
    rw [plr_L_apply]
    simp
  rw [plr_Phi_apply]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext i j
    simp
  · funext k
    exact congrArg (g k) (hL10 k)

/-- The value of `plr_Phi` at `(0, s)`. -/
private theorem plr_Phi0 {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (f : Fin q → StrongDual 𝕜 E) (g : ι → StrongDual 𝕜 E)
    (s : Fin p → E) :
    plr_Phi a c f g (0, s)
      = (0, (fun i j' => f i (s j')),
        (fun k => g k (∑ j', c k j' • s j'))) := by
  have hL0 : ∀ k, plr_L a c (0, s) k = ∑ j', c k j' • s j' := by
    intro k
    rw [plr_L_apply]
    simp
  rw [plr_Phi_apply]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext k
  exact congrArg (g k) (hL0 k)

/-- A coefficient-weighted point-mass sum collapses. -/
private theorem plr_single_smul_sum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p : ℕ} (c : Fin p → 𝕜) (y : E) (j : Fin p) :
    (∑ j', c j' • Pi.single (M := fun _ => E) j y j') = c j • y := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hne
    simp [hne]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The key functional of N5: evaluation at `(1, 0)` plus the `b`-weighted
coordinate functionals. -/
private noncomputable def plr_B {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p : ℕ}
    (b : Fin p → StrongDual 𝕜 (StrongDual 𝕜 E))
    (psi : (𝕜 × (Fin p → E)) →L[𝕜] 𝕜) : 𝕜 :=
  psi (1, 0) + ∑ j, b j ((psi.comp ((ContinuousLinearMap.inr 𝕜 𝕜 (Fin p → E)).comp
    (ContinuousLinearMap.single 𝕜 (fun _ => E) j))) : StrongDual 𝕜 E)

/-- Claim 1, one coordinate: applying `b j` to the `j`-th coordinate
functional of `ψ = λ ∘ Φ` gives the `β/γ` expansion. -/
private theorem plr_claim1_term {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (f : Fin q → StrongDual 𝕜 E) (g : ι → StrongDual 𝕜 E)
    (b : Fin p → StrongDual 𝕜 (StrongDual 𝕜 E))
    (lam : (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) →L[𝕜] 𝕜)
    (psi : (𝕜 × (Fin p → E)) →L[𝕜] 𝕜)
    (hpsi : psi = lam.comp (plr_Phi a c f g)) (j : Fin p) :
    b j ((psi.comp ((ContinuousLinearMap.inr 𝕜 𝕜 (Fin p → E)).comp
      (ContinuousLinearMap.single 𝕜 (fun _ => E) j))) : StrongDual 𝕜 E)
      = (∑ i', lam (0, Pi.single i' (Pi.single j 1), 0) * b j (f i'))
        + ∑ k, ((c k j * lam (0, 0, Pi.single k 1)) * b j (g k)) := by
  have hfun : ((psi.comp ((ContinuousLinearMap.inr 𝕜 𝕜 (Fin p → E)).comp
      (ContinuousLinearMap.single 𝕜 (fun _ => E) j))) : StrongDual 𝕜 E)
      = ((∑ i', lam (0, Pi.single i' (Pi.single j 1), 0) • (f i') :
        StrongDual 𝕜 E)
        + ∑ k, ((c k j * lam (0, 0, Pi.single k 1)) • (g k) :
          StrongDual 𝕜 E)) := by
    ext y
    have eL : ((psi.comp ((ContinuousLinearMap.inr 𝕜 𝕜 (Fin p → E)).comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) j))) : StrongDual 𝕜 E) y
        = lam (0, (fun i' j' => f i' (Pi.single (M := fun _ => E) j y j')),
          (fun k => g k (∑ j', c k j' • Pi.single (M := fun _ => E) j y j'))) := by
      subst hpsi
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
        ContinuousLinearMap.single_apply]
      exact congrArg lam (plr_Phi0 a c f g (Pi.single (M := fun _ => E) j y))
    have eR : ((((∑ i', lam (0, Pi.single i' (Pi.single j 1), 0) • (f i') :
          StrongDual 𝕜 E)
          + ∑ k, ((c k j * lam (0, 0, Pi.single k 1)) • (g k) :
            StrongDual 𝕜 E))) : StrongDual 𝕜 E) y
        = (∑ i', lam (0, Pi.single i' (Pi.single j 1), 0) * f i' y)
          + ∑ k, ((c k j * lam (0, 0, Pi.single k 1)) * g k y) := by
      simp only [sum_apply, add_apply, smul_apply, smul_eq_mul]
    have hmid : ∀ i' : Fin q,
        (∑ j', f i' (Pi.single (M := fun _ => E) j y j')
          * lam (0, Pi.single i' (Pi.single j' 1), 0))
        = lam (0, Pi.single i' (Pi.single j 1), 0) * f i' y := by
      intro i'
      rw [Finset.sum_eq_single j]
      · rw [show Pi.single (M := fun _ => E) j y j = y from
          Pi.single_eq_same (M := fun _ => E) j y]
        exact mul_comm _ _
      · intro j' _ hne
        have hz : Pi.single (M := fun _ => E) j y j' = 0 := by simp [hne]
        rw [hz, map_zero, zero_mul]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have hthird : ∀ k : ι, g k (∑ j', c k j' • Pi.single (M := fun _ => E) j y j')
          * lam (0, 0, Pi.single k 1)
        = ((c k j * lam (0, 0, Pi.single k 1)) * g k y) := by
      intro k
      rw [plr_single_smul_sum, map_smul, smul_eq_mul]
      ring
    have hfst : ∀ (M : Fin q → Fin p → 𝕜) (T : ι → 𝕜),
        (((0, M, T) : 𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜))).1 = 0 :=
      fun M T => rfl
    rw [eL, plr_lam_expand, hfst, zero_mul, zero_add, eR,
      Finset.sum_congr rfl (fun i' _ => hmid i'),
      Finset.sum_congr rfl (fun k _ => hthird k)]
  rw [hfun, map_add, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- Claim 1: the key functional agrees with evaluation at `w` on
functionals of the form `λ ∘ Φ`. -/
private theorem plr_claim1 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (f : Fin q → StrongDual 𝕜 E) (g : ι → StrongDual 𝕜 E)
    (b : Fin p → StrongDual 𝕜 (StrongDual 𝕜 E))
    (m : ι → StrongDual 𝕜 (StrongDual 𝕜 E))
    (hm : ∀ k (h : StrongDual 𝕜 E), m k h = h (a k) + ∑ j, c k j * b j h)
    (lam : (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) →L[𝕜] 𝕜) :
    plr_B b (lam.comp (plr_Phi a c f g)) = lam (plr_w b f m g) := by
  have hL10 : (lam.comp (plr_Phi a c f g)) (1, 0)
      = lam (1, 0, 0) + ∑ k, g k (a k) * lam (0, 0, Pi.single k 1) := by
    rw [show (lam.comp (plr_Phi a c f g)) (1, 0)
        = lam (plr_Phi a c f g (1, 0)) from rfl,
      plr_Phi10, plr_lam_expand]
    dsimp only
    simp only [one_mul, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      add_zero]
  have hR : lam (plr_w b f m g)
      = lam (1, 0, 0)
        + ((∑ i', ∑ j, (b j (f i'))
            * lam (0, Pi.single i' (Pi.single j 1), 0))
          + ∑ k, (m k (g k)) * lam (0, 0, Pi.single k 1)) := by
    rw [show plr_w b f m g
        = (1, (fun i j => b j (f i)), (fun k => m k (g k))) from rfl,
      plr_lam_expand]
    dsimp only
    rw [one_mul, add_assoc]
  have hterms : ∀ j : Fin p,
      b j (((lam.comp (plr_Phi a c f g)).comp
        ((ContinuousLinearMap.inr 𝕜 𝕜 (Fin p → E)).comp
          (ContinuousLinearMap.single 𝕜 (fun _ => E) j))) :
        StrongDual 𝕜 E)
      = (∑ i', lam (0, Pi.single i' (Pi.single j 1), 0) * b j (f i'))
        + ∑ k, ((c k j * lam (0, 0, Pi.single k 1)) * b j (g k)) :=
    fun j => plr_claim1_term a c f g b lam _ rfl j
  have hswap1 : (∑ j, ∑ i', lam (0, Pi.single i' (Pi.single j 1), 0)
        * b j (f i'))
      = ∑ i', ∑ j, lam (0, Pi.single i' (Pi.single j 1), 0) * b j (f i') :=
    Finset.sum_comm
  have hswap2 : (∑ j, ∑ k, ((c k j * lam (0, 0, Pi.single k 1)) * b j (g k)))
      = ∑ k, ∑ j, ((c k j * lam (0, 0, Pi.single k 1)) * b j (g k)) :=
    Finset.sum_comm
  have hB : (∑ i', ∑ j, lam (0, Pi.single i' (Pi.single j 1), 0) * b j (f i'))
      = ∑ i', ∑ j, (b j (f i'))
        * lam (0, Pi.single i' (Pi.single j 1), 0) :=
    Finset.sum_congr rfl
      (fun i' _ => Finset.sum_congr rfl (fun j _ => mul_comm _ _))
  have hk : ∀ k : ι, g k (a k) * lam (0, 0, Pi.single k 1)
        + (∑ j, ((c k j * lam (0, 0, Pi.single k 1)) * b j (g k)))
      = m k (g k) * lam (0, 0, Pi.single k 1) := by
    intro k
    rw [hm k (g k), add_mul, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun j _ =>
      show ((c k j * lam (0, 0, Pi.single k 1)) * b j (g k))
        = ((c k j * b j (g k)) * lam (0, 0, Pi.single k 1)) from by ring)]
  have hAC : (∑ k, g k (a k) * lam (0, 0, Pi.single k 1))
        + (∑ k, ∑ j, ((c k j * lam (0, 0, Pi.single k 1)) * b j (g k)))
      = ∑ k, m k (g k) * lam (0, 0, Pi.single k 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => hk k)
  unfold plr_B
  rw [hL10, hR, Finset.sum_congr rfl (fun j _ => hterms j),
    Finset.sum_add_distrib, hswap1, hswap2, hB, ← hAC]
  abel

/-- Claim 2: the key functional on `Ψ ∘ L` equals the sum of the net
point evaluations. -/
private theorem plr_claim2 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (b : Fin p → StrongDual 𝕜 (StrongDual 𝕜 E))
    (m : ι → StrongDual 𝕜 (StrongDual 𝕜 E))
    (hm : ∀ k (h : StrongDual 𝕜 E), m k h = h (a k) + ∑ j, c k j * b j h)
    (Psi : (ι → E) →L[𝕜] 𝕜) :
    plr_B b (Psi.comp (plr_L a c))
      = ∑ k, m k (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E) := by
  have hL10 : plr_L a c (1, 0) = a := by
    funext k
    rw [plr_L_apply]
    simp
  have e10 : (Psi.comp (plr_L a c)) (1, 0)
      = ∑ k, (Psi.comp (ContinuousLinearMap.single 𝕜 (fun _ => E) k)) (a k) := by
    rw [show (Psi.comp (plr_L a c)) (1, 0) = Psi (plr_L a c (1, 0)) from rfl,
      hL10]
    exact plr_clm_pi_sum Psi a
  have hfun : ∀ j : Fin p,
      (((Psi.comp (plr_L a c)).comp
        ((ContinuousLinearMap.inr 𝕜 𝕜 (Fin p → E)).comp
          (ContinuousLinearMap.single 𝕜 (fun _ => E) j))) :
        StrongDual 𝕜 E)
      = ((∑ k, c k j • (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E)) :
        StrongDual 𝕜 E) := by
    intro j
    ext y
    have eL : (((Psi.comp (plr_L a c)).comp
        ((ContinuousLinearMap.inr 𝕜 𝕜 (Fin p → E)).comp
          (ContinuousLinearMap.single 𝕜 (fun _ => E) j))) :
        StrongDual 𝕜 E) y
        = Psi (fun k => c k j • y) := by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
        ContinuousLinearMap.single_apply]
      congr 1
      funext k
      rw [plr_L_apply]
      simp only [zero_smul, zero_add]
      exact plr_single_smul_sum (c k) y j
    have eR : ((((∑ k, c k j • (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E)) :
        StrongDual 𝕜 E))) y
        = ∑ k, (c k j * (Psi.comp
          (ContinuousLinearMap.single 𝕜 (fun _ => E) k)) y) := by
      simp only [sum_apply, smul_apply, smul_eq_mul]
    rw [eL, eR, plr_clm_pi_sum Psi (fun k => c k j • y)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    change (Psi.comp (ContinuousLinearMap.single 𝕜 (fun _ => E) k))
      (c k j • y) = _
    rw [map_smul, smul_eq_mul]
  have hbj : ∀ j : Fin p,
      b j (((Psi.comp (plr_L a c)).comp
        ((ContinuousLinearMap.inr 𝕜 𝕜 (Fin p → E)).comp
          (ContinuousLinearMap.single 𝕜 (fun _ => E) j))) :
        StrongDual 𝕜 E)
      = ∑ k, (c k j) * b j (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E) := by
    intro j
    rw [hfun j, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, smul_eq_mul]
  have hswap : (∑ j, ∑ k, (c k j) * b j (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E))
      = ∑ k, ∑ j, (c k j) * b j (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E) :=
    Finset.sum_comm
  have hk : ∀ k : ι, ((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k)) (a k))
        + (∑ j, (c k j) * b j (((Psi.comp
          (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E))
      = m k (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E) :=
    fun k => (hm k _).symm
  have hfin : (∑ k, (Psi.comp
          (ContinuousLinearMap.single 𝕜 (fun _ => E) k)) (a k))
        + (∑ k, ∑ j, (c k j) * b j (((Psi.comp
          (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E))
      = ∑ k, m k (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => hk k)
  unfold plr_B
  rw [e10, Finset.sum_congr rfl (fun j _ => hbj j), hswap]
  exact hfin

/-- Finite `δ`-net of the unit sphere of a finite-dimensional subspace. -/
private theorem plr_net_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp]
    {δ : ℝ} (hδ0 : 0 < δ) :
    ∃ n : ℕ, ∃ mk : Fin n → ↥Mp,
      (∀ k, ‖mk k‖ = 1) ∧ ∀ u : ↥Mp, ‖u‖ = 1 → ∃ k, ‖u - mk k‖ < δ := by
  obtain ⟨t, hts, hfin, hcover⟩ :=
    (isCompact_sphere (0 : ↥Mp) 1).finite_cover_balls hδ0
  have hf : Fintype ↥t := hfin.fintype
  have hmem1 : ∀ x : ↥Mp, x ∈ Metric.sphere (0 : ↥Mp) 1 → ‖x‖ = 1 := by
    intro x hx
    have h := Metric.mem_sphere.mp hx
    rwa [dist_zero_right] at h
  have hmem2 : ∀ x : ↥Mp, ‖x‖ = 1 → x ∈ Metric.sphere (0 : ↥Mp) 1 := by
    intro x hx
    rw [Metric.mem_sphere, dist_zero_right]
    exact hx
  refine ⟨@Fintype.card ↥t hf,
    fun k => ((@Fintype.equivFin ↥t hf).symm k).val, ?_, ?_⟩
  · intro k
    exact hmem1 _ (hts ((@Fintype.equivFin ↥t hf).symm k).prop)
  · intro u hu
    have hcov := hcover (hmem2 u hu)
    simp only [Set.mem_iUnion] at hcov
    obtain ⟨x, hxt, hxu⟩ := hcov
    refine ⟨(@Fintype.equivFin ↥t hf) ⟨x, hxt⟩, ?_⟩
    have hxk : (((@Fintype.equivFin ↥t hf).symm
        ((@Fintype.equivFin ↥t hf) ⟨x, hxt⟩))).val = x := by simp
    have h := Metric.mem_ball.mp hxu
    rw [dist_eq_norm] at h
    simpa [hxk] using h

/-- Norming functionals: an almost-norming `g` with `‖g‖ ≤ 1` for a unit vector. -/
private theorem plr_norming
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (u : StrongDual 𝕜 (StrongDual 𝕜 E)) (hu : ‖u‖ = 1)
    {δ : ℝ} (hδ0 : 0 < δ) :
    ∃ g : StrongDual 𝕜 E, ‖g‖ ≤ 1 ∧ 1 - δ ≤ RCLike.re (u g) := by
  have hlt : 1 - δ < ‖u‖ := by linarith
  obtain ⟨g, hg1, hg2⟩ :=
    ContinuousLinearMap.exists_lt_apply_of_lt_opNorm u hlt
  obtain ⟨w, hw1, hw2⟩ := plr_exists_unit_mul (u g)
  refine ⟨w • g, ?_, ?_⟩
  · rw [norm_smul, hw1, one_mul]
    exact hg1.le
  · have e : u (w • g) = w * u g := by rw [map_smul, smul_eq_mul]
    rw [e, hw2]
    exact hg2.le

/-- Scaling a nonzero vector to the unit sphere, with the inverse relation. -/
private theorem plr_scale_to_sphere {V : Type*} [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] (m : V) (hm : m ≠ 0) :
    ‖((↑(‖m‖⁻¹) : 𝕜) • m)‖ = 1
      ∧ m = (↑‖m‖ : 𝕜) • ((↑(‖m‖⁻¹) : 𝕜) • m) := by
  have hpos : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hne : ‖m‖ ≠ 0 := ne_of_gt hpos
  refine ⟨?_, ?_⟩
  · rw [norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hne]
  · rw [smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ hne,
      RCLike.ofReal_one, one_smul]

/-- Net argument, upper bound: if `T` is bounded by `1 + δ` on a `δ`-net of the
unit sphere, then `‖T‖ ≤ (1 + δ) / (1 - δ)`. -/
private theorem plr_opNorm_of_net
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T : V →L[𝕜] E) {t : Finset V} {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hcover : ∀ m : V, ‖m‖ = 1 → ∃ k ∈ t, ‖m - k‖ < δ)
    (hup : ∀ k ∈ t, ‖T k‖ ≤ 1 + δ) :
    ‖T‖ ≤ (1 + δ) / (1 - δ) := by
  have hδ1' : 0 < 1 - δ := by linarith
  have hMnn : 0 ≤ 1 + δ + ‖T‖ * δ :=
    add_nonneg (add_nonneg zero_le_one hδ0.le)
      (mul_nonneg (norm_nonneg _) hδ0.le)
  have key : ∀ m : V, ‖T m‖ ≤ (1 + δ + ‖T‖ * δ) * ‖m‖ := by
    intro m
    by_cases hm : m = 0
    · subst hm
      simp only [map_zero, norm_zero, mul_zero, le_refl]
    · obtain ⟨hnorm, hback⟩ := plr_scale_to_sphere (𝕜 := 𝕜) m hm
      set u : V := (↑(‖m‖⁻¹) : 𝕜) • m with hu
      obtain ⟨k, hkt, hclose⟩ := hcover u hnorm
      have hkT : ‖T k‖ ≤ 1 + δ := hup k hkt
      have himg : ‖T (u - k)‖ ≤ ‖T‖ * δ := by
        have h1 : ‖T (u - k)‖ ≤ ‖T‖ * ‖u - k‖ :=
          ContinuousLinearMap.le_opNorm _ _
        have h2 : ‖T‖ * ‖u - k‖ ≤ ‖T‖ * δ :=
          mul_le_mul_of_nonneg_left hclose.le (norm_nonneg _)
        linarith
      have hTu : ‖T u‖ ≤ 1 + δ + ‖T‖ * δ := by
        have hkk : k + (u - k) = u := by abel
        have hdecomp : T u = T k + T (u - k) := by
          conv_lhs => rw [← hkk]
          rw [map_add]
        calc ‖T u‖ = ‖T k + T (u - k)‖ := by rw [hdecomp]
        _ ≤ ‖T k‖ + ‖T (u - k)‖ := norm_add_le _ _
        _ ≤ (1 + δ) + ‖T‖ * δ := by linarith
      have hTm : T m = (↑‖m‖ : 𝕜) • T u := by
        conv_lhs => rw [hback, map_smul]
      rw [hTm, norm_smul, RCLike.norm_ofReal,
        abs_of_nonneg (norm_nonneg m), mul_comm ‖m‖]
      exact mul_le_mul_of_nonneg_right hTu (norm_nonneg m)
  have hTop0 : ‖T‖ ≤ 1 + δ + ‖T‖ * δ :=
    ContinuousLinearMap.opNorm_le_bound _ hMnn key
  have h1 : ‖T‖ * δ ≤ ‖T‖ := by
    calc ‖T‖ * δ ≤ ‖T‖ * 1 :=
          mul_le_mul_of_nonneg_left hδ1.le (norm_nonneg _)
    _ = ‖T‖ := mul_one _
  have hexp : ‖T‖ * (1 - δ) = ‖T‖ - ‖T‖ * δ := by ring
  have hTop : ‖T‖ * (1 - δ) ≤ 1 + δ := by linarith
  rw [le_div_iff₀ hδ1']
  exact hTop

/-- Net argument, lower bound: with `‖T‖ ≤ (1 + δ) / (1 - δ)` and `1 - δ ≤ ‖T k‖`
on the net, every vector satisfies `((1 - 3δ) / (1 - δ)) * ‖m‖ ≤ ‖T m‖`. -/
private theorem plr_lower_of_net
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T : V →L[𝕜] E) {t : Finset V} {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hcover : ∀ m : V, ‖m‖ = 1 → ∃ k ∈ t, ‖m - k‖ < δ)
    (hlow : ∀ k ∈ t, 1 - δ ≤ ‖T k‖)
    (hTop : ‖T‖ ≤ (1 + δ) / (1 - δ)) :
    ∀ m : V, ((1 - 3 * δ) / (1 - δ)) * ‖m‖ ≤ ‖T m‖ := by
  have hδ1' : 0 < 1 - δ := by linarith
  have hTop' : ‖T‖ * (1 - δ) ≤ 1 + δ := (le_div_iff₀ hδ1').mp hTop
  have key : ∀ m : V, ((1 - δ) - ‖T‖ * δ) * ‖m‖ ≤ ‖T m‖ := by
    intro m
    by_cases hm : m = 0
    · subst hm
      simp only [map_zero, norm_zero, mul_zero, le_refl]
    · obtain ⟨hnorm, hback⟩ := plr_scale_to_sphere (𝕜 := 𝕜) m hm
      set u : V := (↑(‖m‖⁻¹) : 𝕜) • m with hu
      obtain ⟨k, hkt, hclose⟩ := hcover u hnorm
      have hkT : 1 - δ ≤ ‖T k‖ := hlow k hkt
      have himg : ‖T (k - u)‖ ≤ ‖T‖ * δ := by
        have h1 : ‖T (k - u)‖ ≤ ‖T‖ * ‖k - u‖ :=
          ContinuousLinearMap.le_opNorm _ _
        have h2 : ‖k - u‖ = ‖u - k‖ := norm_sub_rev _ _
        have h3 : ‖T‖ * ‖k - u‖ ≤ ‖T‖ * δ := by
          rw [h2]
          exact mul_le_mul_of_nonneg_left hclose.le (norm_nonneg _)
        linarith
      have hTu : (1 - δ) - ‖T‖ * δ ≤ ‖T u‖ := by
        have hkk : k = u + (k - u) := by abel
        have hdecomp : T k = T u + T (k - u) := by
          have h := congrArg T hkk
          rwa [map_add] at h
        have hle : ‖T k‖ ≤ ‖T u‖ + ‖T (k - u)‖ := by
          rw [hdecomp]
          exact norm_add_le _ _
        linarith
      have hTm : T m = (↑‖m‖ : 𝕜) • T u := by
        conv_lhs => rw [hback, map_smul]
      rw [hTm, norm_smul, RCLike.norm_ofReal,
        abs_of_nonneg (norm_nonneg m), mul_comm ‖m‖]
      exact mul_le_mul_of_nonneg_right hTu (norm_nonneg m)
  have hexpand : ((1 - δ) - ‖T‖ * δ) * (1 - δ)
      = (1 - δ) * (1 - δ) - (‖T‖ * (1 - δ)) * δ := by ring
  have hle : 1 - 3 * δ ≤ ((1 - δ) - ‖T‖ * δ) * (1 - δ) := by
    have hmul : (‖T‖ * (1 - δ)) * δ ≤ (1 + δ) * δ :=
      mul_le_mul_of_nonneg_right hTop' hδ0.le
    have hring : (1 - δ) * (1 - δ) - (1 + δ) * δ = 1 - 3 * δ := by ring
    linarith
  have hC : (1 - 3 * δ) / (1 - δ) ≤ (1 - δ) - ‖T‖ * δ := by
    rw [div_le_iff₀ hδ1']
    exact hle
  intro m
  have hm := key m
  have hmul := mul_le_mul_of_nonneg_right hC (norm_nonneg m)
  linarith

/-- Helly's lemma, general form: a finite system of linear equations with one norm
bound is solvable whenever the dual inequality holds. -/
private theorem plr_helly
    {Z Y V : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (L : Z →L[𝕜] Y) (Φ : Z →L[𝕜] V) (w : V) {s r : ℝ} (hs : 0 ≤ s)
    (hsr : s < r)
    (hD : ∀ lam : V →L[𝕜] 𝕜, ∀ Psi : Y →L[𝕜] 𝕜,
      lam.comp Φ = Psi.comp L → RCLike.re (lam w) ≤ s * ‖Psi‖) :
    ∃ z : Z, ‖L z‖ < r ∧ Φ z = w := by
  have hr0 : 0 < r := lt_of_le_of_lt hs hsr
  -- Step 1: `w` lies in the range of `Φ`.
  have hmem : w ∈ Φ.range := by
    by_contra hw
    obtain ⟨lam0, hne, hbot⟩ :=
      Submodule.exists_dual_map_eq_bot_of_notMem (p := Φ.range) (x := w)
        hw inferInstance
    have hw1 : ((lam0 w)⁻¹ • lam0) w = 1 := by
      rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hne]
    have hvan : ∀ z : Z, lam0 (Φ z) = 0 := by
      intro z
      have hm : lam0 (Φ z) ∈ Submodule.map lam0 Φ.range :=
        ⟨Φ z, ⟨z, rfl⟩, rfl⟩
      rw [hbot] at hm
      exact (Submodule.mem_bot 𝕜).mp hm
    set lam1c : V →L[𝕜] 𝕜 :=
      LinearMap.toContinuousLinearMap ((lam0 w)⁻¹ • lam0) with hlam1c
    have hlc : ∀ v : V, lam1c v = ((lam0 w)⁻¹ • lam0) v := fun v => rfl
    have hw1c : lam1c w = 1 := hw1
    have hcomp : lam1c.comp Φ = 0 := by
      ext z
      simp only [ContinuousLinearMap.comp_apply, zero_apply]
      rw [hlc, LinearMap.smul_apply, hvan z, smul_zero]
    have hD0 := hD lam1c 0 (by simp [hcomp])
    simp only [hw1c, RCLike.one_re, norm_zero, mul_zero] at hD0
    linarith
  -- Step 2 setup: the restricted map, the sublevel set and its image.
  have hsurj : Function.Surjective (Φ.rangeRestrict) := by
    intro y
    obtain ⟨z, hz⟩ := y.prop
    exact ⟨z, Subtype.ext (by simpa using hz)⟩
  have hsurj' : Function.Surjective (Φ.rangeRestrict.toLinearMap) := hsurj
  have hopen : IsOpenMap (Φ.rangeRestrict) :=
    LinearMap.isOpenMap_of_finiteDimensional _ hsurj'
  set C : Set Z := L ⁻¹' Metric.ball (0 : Y) r with hC
  have hCopen : IsOpen C := Metric.isOpen_ball.preimage L.continuous
  have hCconv : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    have hx' : ‖L x‖ < r := by
      have h := Metric.mem_ball.mp hx
      rwa [dist_zero_right] at h
    have hy' : ‖L y‖ < r := by
      have h := Metric.mem_ball.mp hy
      rwa [dist_zero_right] at h
    have e1 : a • x = ((a : 𝕜)) • x := RCLike.real_smul_eq_coe_smul a x
    have e2 : b • y = ((b : 𝕜)) • y := RCLike.real_smul_eq_coe_smul b y
    have hL : L (a • x + b • y) = (a : 𝕜) • L x + (b : 𝕜) • L y := by
      rw [e1, e2, map_add, map_smul, map_smul]
    have hfin : a * ‖L x‖ + b * ‖L y‖ < r := by
      have h1 : a * ‖L x‖ ≤ a * r := mul_le_mul_of_nonneg_left hx'.le ha
      have h2 : b * ‖L y‖ ≤ b * r := mul_le_mul_of_nonneg_left hy'.le hb
      have h3 : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
      rcases eq_or_ne a 0 with rfl | ha0
      · have hb1 : b = 1 := by linarith
        rw [zero_mul, zero_add, hb1, one_mul]
        exact hy'
      · have ha0' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hlt1 : a * ‖L x‖ < a * r := mul_lt_mul_of_pos_left hx' ha0'
        linarith
    have hmemC : L (a • x + b • y) ∈ Metric.ball (0 : Y) r := by
      rw [Metric.mem_ball, dist_zero_right, hL]
      calc ‖(a : 𝕜) • L x + (b : 𝕜) • L y‖
          ≤ ‖(a : 𝕜) • L x‖ + ‖(b : 𝕜) • L y‖ := norm_add_le _ _
        _ = a * ‖L x‖ + b * ‖L y‖ := by
          rw [norm_smul, norm_smul, RCLike.norm_ofReal, RCLike.norm_ofReal,
            abs_of_nonneg ha, abs_of_nonneg hb]
        _ < r := hfin
    exact hmemC
  have hImOpen : IsOpen (Φ.rangeRestrict '' C) := hopen _ hCopen
  have hImConv : Convex ℝ (Φ.rangeRestrict '' C) := by
    intro y1 hy1 y2 hy2 a b ha hb hab
    obtain ⟨x1, hx1C, rfl⟩ := hy1
    obtain ⟨x2, hx2C, rfl⟩ := hy2
    refine ⟨a • x1 + b • x2, hCconv hx1C hx2C ha hb hab, ?_⟩
    have e1 : a • x1 = ((a : 𝕜)) • x1 := RCLike.real_smul_eq_coe_smul a x1
    have e2 : b • x2 = ((b : 𝕜)) • x2 := RCLike.real_smul_eq_coe_smul b x2
    have e3 : a • Φ.rangeRestrict x1 = ((a : 𝕜)) • Φ.rangeRestrict x1 :=
      RCLike.real_smul_eq_coe_smul a _
    have e4 : b • Φ.rangeRestrict x2 = ((b : 𝕜)) • Φ.rangeRestrict x2 :=
      RCLike.real_smul_eq_coe_smul b _
    rw [e3, e4, ← map_smul, ← map_smul, ← map_add, ← e1, ← e2]
  by_contra hcon
  have hcon' : ∀ z : Z, ‖L z‖ < r → Φ z ≠ w := fun z hz he => hcon ⟨z, hz, he⟩
  set w' : ↥(Φ.range) := ⟨w, hmem⟩ with hw'
  have hnotmem : w' ∉ Φ.rangeRestrict '' C := by
    rintro ⟨z, hzC, hzz⟩
    have hzC' : ‖L z‖ < r := by
      have h := Metric.mem_ball.mp hzC
      rwa [dist_zero_right] at h
    have hzw : Φ z = w := by
      have h := Subtype.ext_iff.mp hzz
      simpa using h
    exact hcon' z hzC' hzw
  obtain ⟨mu, hmu⟩ :=
    RCLike.geometric_hahn_banach_open_point (𝕜 := 𝕜) (E := ↥(Φ.range))
      hImConv hImOpen hnotmem
  obtain ⟨lam, hlamEq, -⟩ := exists_extension_norm_eq (Φ.range) mu
  set beta : ℝ := RCLike.re (lam w) with hbeta
  have hbeta0 : 0 < beta := by
    have h0C : (0 : Z) ∈ C := by
      have hmem7 : L (0 : Z) ∈ Metric.ball (0 : Y) r := by
        rw [Metric.mem_ball, map_zero, dist_zero_right, norm_zero]
        exact hr0
      exact hmem7
    have him := hmu (Φ.rangeRestrict 0) ⟨0, h0C, rfl⟩
    have ew : ((w' : ↥(Φ.range)) : V) = w := rfl
    rw [map_zero, map_zero, RCLike.zero_re, ← hlamEq, ew, ← hbeta] at him
    exact him
  have e2 : mu w' = lam w := (hlamEq w').symm
  have hltC : ∀ z : Z, z ∈ C → RCLike.re (lam (Φ z)) < beta := by
    intro z hz
    have him := hmu (Φ.rangeRestrict z) ⟨z, hz, rfl⟩
    have h := hlamEq (Φ.rangeRestrict z)
    have e : ((Φ.rangeRestrict z : ↥(Φ.range)) : V) = Φ z := rfl
    rw [e] at h
    rw [h, hbeta, ← e2]
    exact him
  -- Step 3: every value of `lam ∘ Φ` is controlled by `L`.
  have hbound : ∀ z : Z, ‖lam (Φ z)‖ ≤ (beta / r) * ‖L z‖ := by
    intro z
    by_contra hlt
    have hlt : (beta / r) * ‖L z‖ < ‖lam (Φ z)‖ := lt_of_not_ge hlt
    have hc0 : lam (Φ z) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlt
      have hnn : 0 ≤ (beta / r) * ‖L z‖ :=
        mul_nonneg (div_nonneg hbeta0.le hr0.le) (norm_nonneg _)
      linarith
    have hcn : 0 < ‖lam (Φ z)‖ := norm_pos_iff.mpr hc0
    have hkey : beta * ‖L z‖ < r * ‖lam (Φ z)‖ := by
      have h := hlt
      rw [div_mul_eq_mul_div, div_lt_iff₀ hr0] at h
      linarith
    set d : 𝕜 := (↑(beta / ‖lam (Φ z)‖ ^ 2) : 𝕜) * starRingEnd 𝕜 (lam (Φ z))
      with hd
    set z' : Z := d • z with hz'
    have hne2 : (‖lam (Φ z)‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hcn.ne'
    have hlamz' : lam (Φ z') = (↑beta : 𝕜) := by
      have e1 : Φ z' = d • Φ z := by rw [hz', map_smul]
      have e2' : lam (d • Φ z) = d • lam (Φ z) := by rw [map_smul]
      rw [e1, e2', hd, smul_eq_mul, mul_assoc, RCLike.conj_mul,
        ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, div_mul_cancel₀ _ hne2]
    have hnormz' : ‖L z'‖ < r := by
      have e1 : L z' = d • L z := by rw [hz', map_smul]
      rw [e1, norm_smul, hd, norm_mul, RCLike.norm_ofReal, RCLike.norm_conj,
        abs_of_nonneg (div_nonneg hbeta0.le (by positivity))]
      have e3 : beta / ‖lam (Φ z)‖ ^ 2 * ‖lam (Φ z)‖ * ‖L z‖
          = beta * ‖L z‖ / ‖lam (Φ z)‖ := by
        field_simp
      rw [e3, div_lt_iff₀ hcn]
      exact hkey
    have hmemC : z' ∈ C := by
      have hmem7 : L z' ∈ Metric.ball (0 : Y) r := by
        rw [Metric.mem_ball, dist_zero_right]
        exact hnormz'
      exact hmem7
    have hlt2 := hltC z' hmemC
    rw [hlamz', RCLike.ofReal_re] at hlt2
    exact lt_irrefl _ hlt2
  -- Step 4: factor `lam ∘ Φ` through `L`.
  have hker : LinearMap.ker L.toLinearMap
      ≤ LinearMap.ker (lam.comp Φ).toLinearMap := by
    intro z hz
    have hz' : L z = 0 := LinearMap.mem_ker.mp hz
    have hb := hbound z
    rw [hz', norm_zero, mul_zero] at hb
    have h0 : lam (Φ z) = 0 :=
      norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
    refine LinearMap.mem_ker.mpr ?_
    have e : (lam.comp Φ).toLinearMap z = lam (Φ z) := rfl
    rw [e]
    exact h0
  set qe := LinearMap.quotKerEquivRange L.toLinearMap with hqe
  set phi1 : ↥(LinearMap.range L.toLinearMap) →ₗ[𝕜] 𝕜 :=
    (Submodule.liftQ (LinearMap.ker L.toLinearMap) (lam.comp Φ).toLinearMap
      hker).comp qe.symm.toLinearMap with hphi1
  have hphi1 : ∀ z : Z, phi1 ⟨L.toLinearMap z, z, rfl⟩ = lam (Φ z) := by
    intro z
    have hsym : qe.symm ⟨L.toLinearMap z, z, rfl⟩
        = Submodule.Quotient.mk z := by
      apply qe.injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      exact (LinearMap.quotKerEquivRange_apply_mk _ z).symm
    have hsym' : qe.symm.toLinearMap ⟨L.toLinearMap z, z, rfl⟩
        = Submodule.Quotient.mk z :=
      hsym
    rw [hphi1, LinearMap.comp_apply, hsym']
    exact Submodule.liftQ_apply _ _ z
  have hphi1bd : ∀ y : ↥(LinearMap.range L.toLinearMap),
      ‖phi1 y‖ ≤ (beta / r) * ‖(y : Y)‖ := by
    rintro ⟨y, z, rfl⟩
    rw [hphi1]
    exact hbound z
  set Psi0 : ↥(LinearMap.range L.toLinearMap) →L[𝕜] 𝕜 :=
    LinearMap.mkContinuous phi1 (beta / r) hphi1bd with hPsi0
  have hPsi0bd : ‖Psi0‖ ≤ beta / r :=
    LinearMap.mkContinuous_norm_le _ (div_nonneg hbeta0.le hr0.le) _
  obtain ⟨Psi, hPsiEq, hPsiNorm⟩ :=
    exists_extension_norm_eq (LinearMap.range L.toLinearMap) Psi0
  have hPsi : ‖Psi‖ ≤ beta / r := hPsiNorm ▸ hPsi0bd
  have hPsiSpec : ∀ z : Z, Psi (L z) = lam (Φ z) := by
    intro z
    have h1 := hPsiEq (⟨L.toLinearMap z, z, rfl⟩
      : ↥(LinearMap.range L.toLinearMap))
    have h2 : Psi0 ⟨L.toLinearMap z, z, rfl⟩
        = phi1 ⟨L.toLinearMap z, z, rfl⟩ := rfl
    have h3 : ((⟨L.toLinearMap z, z, rfl⟩
      : ↥(LinearMap.range L.toLinearMap)) : Y) = L z := rfl
    rw [h3] at h1
    rw [h1, h2, hphi1]
  have hcomp2 : lam.comp Φ = Psi.comp L := by
    ext z
    simp only [ContinuousLinearMap.comp_apply]
    exact (hPsiSpec z).symm
  -- Step 5: the dual inequality contradicts `beta > 0`.
  have hle := hD lam Psi hcomp2
  rw [← hbeta] at hle
  have h3 : s * ‖Psi‖ ≤ s * (beta / r) :=
    mul_le_mul_of_nonneg_left hPsi hs
  have h4 : s * (beta / r) < beta := by
    have h1 : s * beta < beta * r := by
      have h := mul_lt_mul_of_pos_right hsr hbeta0
      linarith
    have h2 : s * (beta / r) = (s * beta) / r := by ring
    rw [h2, div_lt_iff₀ hr0]
    exact h1
  linarith

/-- Evaluation at a point, summed over an orthonormal-style decomposition, is bounded
by the operator norm: the `ℓ¹` bound on a product dual. -/
private theorem plr_sum_norm_single_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (Psi : (ι → E) →L[𝕜] 𝕜) :
    ∑ k, ‖Psi.comp (ContinuousLinearMap.single 𝕜 (fun _ => E) k)‖ ≤ ‖Psi‖ := by
  set psi : ι → E →L[𝕜] 𝕜 :=
    fun k => Psi.comp (ContinuousLinearMap.single 𝕜 (fun _ => E) k) with hpsi
  have hsum : ∀ v : ι → E, Psi v = ∑ k, psi k (v k) := by
    intro v
    have h : v = ∑ k, Pi.single k (v k) := (Finset.univ_sum_single v).symm
    conv_lhs => rw [h]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [hpsi, ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
  have key : ∀ eta : ℝ, 0 < eta →
      ∑ k, ‖psi k‖ ≤ ‖Psi‖ + (Fintype.card ι) * eta := by
    intro eta heta
    have hex : ∀ k : ι, ∃ x : E, ‖x‖ ≤ 1 ∧ ‖psi k‖ - eta ≤ ‖psi k x‖ := by
      intro k
      by_cases hk : psi k = 0
      · refine ⟨0, by simp, ?_⟩
        rw [hk, norm_zero, zero_apply, norm_zero, zero_sub]
        exact neg_nonpos.mpr heta.le
      · have hlt : ‖psi k‖ - eta < ‖psi k‖ := by linarith
        obtain ⟨x, hx1, hx2⟩ :=
          ContinuousLinearMap.exists_lt_apply_of_lt_opNorm (psi k) hlt
        exact ⟨x, hx1.le, hx2.le⟩
    choose x hx1 hx2 using hex
    have hrot : ∀ k : ι, ∃ y : E,
        ‖y‖ ≤ 1 ∧ ‖psi k (x k)‖ ≤ RCLike.re (psi k y) := by
      intro k
      obtain ⟨u, hu1, hu2⟩ := plr_exists_unit_mul (psi k (x k))
      refine ⟨u • x k, ?_, ?_⟩
      · rw [norm_smul, hu1, one_mul]
        exact hx1 k
      · have e : psi k (u • x k) = u * psi k (x k) := by
          rw [map_smul, smul_eq_mul]
        rw [e, hu2]
    choose y hy1 hy2 using hrot
    have hvn : ‖y‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro k
      exact hy1 k
    have hre : RCLike.re (Psi y) = ∑ k, RCLike.re (psi k (y k)) := by
      rw [hsum y]
      have h : ∀ s : Finset ι, RCLike.re (s.sum fun k => psi k (y k))
          = s.sum fun k => RCLike.re (psi k (y k)) := by
        intro s
        induction s using Finset.induction with
        | empty => simp only [Finset.sum_empty, RCLike.zero_re]
        | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add RCLike.re, ih]
      exact h Finset.univ
    have hfin : ∑ k, ‖psi k‖ ≤ ‖Psi‖ + (Fintype.card ι) * eta := by
      have h1 : ∑ k, (‖psi k‖ - eta) ≤ RCLike.re (Psi y) := by
        rw [hre]
        apply Finset.sum_le_sum
        intro k _
        have a := hx2 k
        have b := hy2 k
        linarith
      have h2 : RCLike.re (Psi y) ≤ ‖Psi‖ := by
        have a : RCLike.re (Psi y) ≤ ‖Psi y‖ := RCLike.re_le_norm _
        have b : ‖Psi y‖ ≤ ‖Psi‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
        have c : ‖Psi‖ * ‖y‖ ≤ ‖Psi‖ * 1 :=
          mul_le_mul_of_nonneg_left hvn (ContinuousLinearMap.opNorm_nonneg _)
        linarith
      have h3 : ∑ k, (‖psi k‖ - eta)
          = (∑ k, ‖psi k‖) - (Fintype.card ι) * eta := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
      linarith
    exact hfin
  apply le_of_forall_pos_le_add
  intro eps heps
  by_cases hcard : Fintype.card ι = 0
  · have h0 : ∑ k, ‖psi k‖ ≤ ‖Psi‖ := by
      have h := key 1 one_pos
      rw [hcard] at h
      simpa using h
    linarith [ContinuousLinearMap.opNorm_nonneg Psi, heps.le,
      add_nonneg (norm_nonneg (‖Psi‖)) heps.le]
  · have hpos : 0 < (Fintype.card ι : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard)
    have h := key (eps / Fintype.card ι) (div_pos heps hpos)
    have hcancel : (Fintype.card ι : ℝ) * (eps / Fintype.card ι) = eps := by
      field_simp
    linarith

/-- Dual inequality: the Helly hypothesis (D) with `s = 1`. -/
private theorem plr_dual_ineq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (f : Fin q → StrongDual 𝕜 E) (g : ι → StrongDual 𝕜 E)
    (b : Fin p → StrongDual 𝕜 (StrongDual 𝕜 E))
    (m : ι → StrongDual 𝕜 (StrongDual 𝕜 E))
    (hm : ∀ k (h : StrongDual 𝕜 E), m k h = h (a k) + ∑ j, c k j * b j h)
    (hmnorm : ∀ k, ‖m k‖ = 1)
    (lam : (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) →L[𝕜] 𝕜)
    (Psi : (ι → E) →L[𝕜] 𝕜)
    (hcomp : lam.comp (plr_Phi a c f g) = Psi.comp (plr_L a c)) :
    RCLike.re (lam (plr_w b f m g)) ≤ 1 * ‖Psi‖ := by
  have hterm : ∀ k : ι,
      ‖m k (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E)‖
      ≤ ‖(((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E)‖ := by
    intro k
    calc ‖m k (((Psi.comp
            (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E)‖
        ≤ ‖m k‖ * ‖(((Psi.comp
            (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖(((Psi.comp
            (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) :
            StrongDual 𝕜 E)‖ := by
          rw [hmnorm k, one_mul]
  rw [← plr_claim1 a c f g b m hm lam, hcomp,
    plr_claim2 a c b m hm Psi, one_mul, plr_re_sum]
  exact calc ∑ k, RCLike.re (m k (((Psi.comp
              (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E))
          ≤ ∑ k, ‖m k (((Psi.comp
              (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) :
              StrongDual 𝕜 E)‖ :=
            Finset.sum_le_sum (fun k _ => RCLike.re_le_norm _)
        _ ≤ ∑ k, ‖(((Psi.comp
              (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) :
              StrongDual 𝕜 E)‖ :=
            Finset.sum_le_sum (fun k _ => hterm k)
        _ ≤ ‖Psi‖ := plr_sum_norm_single_le Psi

/-- Solving the finite system via Helly's lemma. The solution `y` satisfies
the dual pairings, the norming equations and the norm bound at every net point. -/
private theorem plr_solve {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {p q : ℕ} {ι : Type*} (hF : Fintype ι)
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (f : Fin q → StrongDual 𝕜 E) (g : ι → StrongDual 𝕜 E)
    (b : Fin p → StrongDual 𝕜 (StrongDual 𝕜 E))
    (m : ι → StrongDual 𝕜 (StrongDual 𝕜 E))
    (hm : ∀ k (h : StrongDual 𝕜 E), m k h = h (a k) + ∑ j, c k j * b j h)
    (hmnorm : ∀ k, ‖m k‖ = 1)
    {δ : ℝ} (hδ0 : 0 < δ) :
    ∃ y : Fin p → E,
      (∀ i j, f i (y j) = b j (f i))
      ∧ (∀ k, g k (a k + ∑ j, c k j • y j) = m k (g k))
      ∧ (∀ k, ‖a k + ∑ j, c k j • y j‖ < 1 + δ) := by
  classical
  have hw : plr_w b f m g
      = (1, (fun i j => b j (f i)), (fun k => m k (g k))) := rfl
  have hD : ∀ lam : (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) →L[𝕜] 𝕜,
      ∀ Psi : (ι → E) →L[𝕜] 𝕜,
      lam.comp (plr_Phi a c f g) = Psi.comp (plr_L a c) →
      RCLike.re (lam (plr_w b f m g)) ≤ 1 * ‖Psi‖ :=
    fun lam Psi hcomp => plr_dual_ineq a c f g b m hm hmnorm lam Psi hcomp
  obtain ⟨z, hzL, hzPhi⟩ := plr_helly (plr_L a c) (plr_Phi a c f g)
    (plr_w b f m g) zero_le_one (by linarith : (1 : ℝ) < 1 + δ) hD
  have ePhi : plr_w b f m g
      = (z.1, (fun i j => f i (z.2 j)),
        (fun k => g k (plr_L a c z k))) := by
    rw [← hzPhi]
    exact plr_Phi_apply a c f g z
  have ht : z.1 = 1 := by
    have h := congrArg Prod.fst ePhi
    rw [hw] at h
    simpa using h.symm
  have hLk : ∀ k, plr_L a c z k = a k + ∑ j, c k j • z.2 j := by
    intro k
    rw [plr_L_apply, ht, one_smul]
  have hmid : ∀ i j, f i (z.2 j) = b j (f i) := by
    intro i j
    have h := congrArg (fun v : 𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜) =>
      v.2.1 i j) ePhi
    rw [hw] at h
    simpa using h.symm
  have hlast : ∀ k, g k (a k + ∑ j, c k j • z.2 j) = m k (g k) := by
    intro k
    have h2 : m k (g k) = g k (plr_L a c z k) := by
      have h := congrArg (fun v : 𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜) =>
        v.2.2 k) ePhi
      rw [hw] at h
      simpa using h
    rw [hLk k] at h2
    exact h2.symm
  have hnorm : ∀ k, ‖a k + ∑ j, c k j • z.2 j‖ < 1 + δ := by
    intro k
    rw [← hLk k]
    exact lt_of_le_of_lt (norm_le_pi_norm (plr_L a c z) k) hzL
  exact ⟨z.2, hmid, hlast, hnorm⟩

/-- The operator `T'` on `M'`, as a linear map. -/
private def plr_T'lin {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp]
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (y : Fin (Module.finrank 𝕜 ↥C) → E) : ↥Mp →ₗ[𝕜] E where
  toFun u := plr_S0 Mp (plr_pi0 Mp C hC u)
    + ∑ j, (Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC u) j • y j
  map_add' u v := by
    have e1 : plr_pi0 Mp C hC (u + v)
        = plr_pi0 Mp C hC u + plr_pi0 Mp C hC v := map_add _ _ _
    have e2 : plr_pi1 Mp C hC (u + v)
        = plr_pi1 Mp C hC u + plr_pi1 Mp C hC v := map_add _ _ _
    simp only [e1, e2, map_add, Finsupp.add_apply, add_smul,
      Finset.sum_add_distrib]
    abel
  map_smul' c u := by
    have e1 : plr_pi0 Mp C hC (c • u) = c • plr_pi0 Mp C hC u :=
      map_smul _ _ _
    have e2 : plr_pi1 Mp C hC (c • u) = c • plr_pi1 Mp C hC u :=
      map_smul _ _ _
    simp only [e1, e2, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_smul,
      RingHom.id_apply, smul_add, Finset.smul_sum]

/-- The operator `T'` on `M'`, continuous. -/
private noncomputable def plr_T' {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp]
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (y : Fin (Module.finrank 𝕜 ↥C) → E) : ↥Mp →L[𝕜] E :=
  LinearMap.toContinuousLinearMap (plr_T'lin Mp C hC y)

/-- Application formula for `plr_T'`. -/
private theorem plr_T'_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp]
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (y : Fin (Module.finrank 𝕜 ↥C) → E) (u : ↥Mp) :
    plr_T' Mp C hC y u = plr_S0 Mp (plr_pi0 Mp C hC u)
      + ∑ j, (Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC u) j • y j :=
  rfl

/-- Values of `T'` at the net points, with two-sided norm bounds. -/
private theorem plr_T'_net {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp]
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (y : Fin (Module.finrank 𝕜 ↥C) → E)
    {ι : Type*}
    (a : ι → E) (c : ι → Fin (Module.finrank 𝕜 ↥C) → 𝕜)
    (g : ι → StrongDual 𝕜 E) (m : ι → StrongDual 𝕜 (StrongDual 𝕜 E))
    (mk : ι → ↥Mp)
    (ha : ∀ k, a k = plr_S0 Mp (plr_pi0 Mp C hC (mk k)))
    (hc : ∀ k j, c k j
      = (Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC (mk k)) j)
    (hg : ∀ k, ‖g k‖ ≤ 1)
    {δ : ℝ}
    (hgnorm : ∀ k, 1 - δ ≤ RCLike.re (m k (g k)))
    (hN6g : ∀ k, g k (a k + ∑ j, c k j • y j) = m k (g k))
    (hN6n : ∀ k, ‖a k + ∑ j, c k j • y j‖ < 1 + δ) :
    ∀ k, 1 - δ ≤ ‖plr_T' Mp C hC y (mk k)‖
      ∧ ‖plr_T' Mp C hC y (mk k)‖ ≤ 1 + δ := by
  intro k
  have hTeq : plr_T' Mp C hC y (mk k) = a k + ∑ j, c k j • y j := by
    rw [plr_T'_apply, ← ha k]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by rw [hc k j])
  refine ⟨?_, ?_⟩
  · calc 1 - δ ≤ RCLike.re (m k (g k)) := hgnorm k
      _ = RCLike.re (g k (plr_T' Mp C hC y (mk k))) := by
        rw [hTeq, hN6g k]
      _ ≤ ‖g k (plr_T' Mp C hC y (mk k))‖ := RCLike.re_le_norm _
      _ ≤ ‖plr_T' Mp C hC y (mk k)‖ := by
        calc ‖g k (plr_T' Mp C hC y (mk k))‖
            ≤ ‖g k‖ * ‖plr_T' Mp C hC y (mk k)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖plr_T' Mp C hC y (mk k)‖ :=
            mul_le_mul_of_nonneg_right (hg k) (norm_nonneg _)
          _ = ‖plr_T' Mp C hC y (mk k)‖ := one_mul _
  · rw [hTeq]
    exact le_of_lt (hN6n k)

set_option maxHeartbeats 800000 in
-- The two finite-basis expansions exceed the default elaboration heartbeat limit.
/-- `T'` preserves all dual pairings. -/
private theorem plr_T'_pair {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp]
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (y : Fin (Module.finrank 𝕜 ↥C) → E)
    {q : ℕ} (f : Fin q → StrongDual 𝕜 E)
    (b : Fin (Module.finrank 𝕜 ↥C) → StrongDual 𝕜 (StrongDual 𝕜 E))
    (hfy : ∀ i j, f i (y j) = b j (f i))
    (hb : ∀ j, Mp.subtype (C.subtype ((Module.finBasis 𝕜 ↥C) j)) = b j)
    (u : ↥Mp) (i : Fin q) :
    f i (plr_T' Mp C hC y u) = (Mp.subtype u) (f i) := by
  have e1 : (Mp.subtype u) (f i)
      = f i (plr_S0 Mp (plr_pi0 Mp C hC u))
        + ∑ j, (Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC u) j
          * b j (f i) := by
    have h := congrArg (· (f i)) (plr_decomp Mp C hC u)
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul,
      NormedSpace.dual_def] at h
    have h2 : (∑ j, (Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC u) j
          * (Mp.subtype (C.subtype ((Module.finBasis 𝕜 ↥C) j))) (f i))
        = (∑ j, (Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC u) j
          * b j (f i)) :=
      Finset.sum_congr rfl (fun j _ => by rw [hb j])
    rw [h2] at h
    exact h
  have e2 : f i (plr_T' Mp C hC y u)
      = f i (plr_S0 Mp (plr_pi0 Mp C hC u))
        + ∑ j, (Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC u) j
          * b j (f i) := by
    rw [plr_T'_apply, map_add, map_sum]
    congr 1
    exact Finset.sum_congr rfl
      (fun j _ => by rw [map_smul, smul_eq_mul, hfy i j])
  exact e2.trans e1.symm

/-- `T'` fixes the `J(E)` part. -/
private theorem plr_T'_fix {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp]
    (C : Submodule 𝕜 ↥Mp) (hC : IsCompl (plr_M0 Mp) C)
    (y : Fin (Module.finrank 𝕜 ↥C) → E)
    (u : ↥Mp) (x : E)
    (hx : Mp.subtype u
      = NormedSpace.inclusionInDoubleDual 𝕜 E x) :
    plr_T' Mp C hC y u = x := by
  have hmem : u ∈ plr_M0 Mp := ⟨x, hx.symm⟩
  have hpi0 : plr_pi0 Mp C hC u = ⟨u, hmem⟩ :=
    plr_pi0_mem Mp C hC ⟨u, hmem⟩
  have hpi1 : plr_pi1 Mp C hC u = 0 :=
    plr_pi1_mem Mp C hC ⟨u, hmem⟩
  have hSx : plr_S0 Mp ⟨u, hmem⟩ = x := by
    apply plr_J_inj (𝕜 := 𝕜)
    change (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap
        (plr_S0 Mp ⟨u, hmem⟩)
      = (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap x
    rw [plr_S0_mem]
    exact hx
  rw [plr_T'_apply, hpi0, hpi1, hSx]
  simp only [map_zero, Finsupp.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]

/-- The choice `δ = ε / (8 + 4ε)` has the numerical bounds needed by N8. -/
private theorem plr_delta_estimates (ε : ℝ) (hε : 0 < ε) :
    let δ := ε / (8 + 4 * ε)
    0 < δ ∧ δ < 1
      ∧ (1 + δ) / (1 - δ) ≤ 1 + ε
      ∧ (1 + ε)⁻¹ ≤ (1 - 3 * δ) / (1 - δ) := by
  let δ := ε / (8 + 4 * ε)
  have hden : 0 < 8 + 4 * ε := by linarith
  have hδ0 : 0 < δ := div_pos hε hden
  have hδeq : δ * (8 + 4 * ε) = ε := by
    rw [show δ = ε / (8 + 4 * ε) from rfl, div_mul_cancel₀]
    exact ne_of_gt hden
  have hδ1 : δ < 1 := by
    rw [show δ = ε / (8 + 4 * ε) from rfl, div_lt_one hden]
    linarith
  have hsub : 0 < 1 - δ := by linarith
  have hup : (1 + δ) / (1 - δ) ≤ 1 + ε := by
    rw [div_le_iff₀ hsub]
    nlinarith
  have he : 0 < 1 + ε := by linarith
  have hlow : (1 + ε)⁻¹ ≤ (1 - 3 * δ) / (1 - δ) := by
    rw [le_div_iff₀ hsub, inv_mul_eq_div, div_le_iff₀ he]
    nlinarith
  exact ⟨hδ0, hδ1, hup, hlow⟩

/-- The net-point estimates imply the required global norm bounds. -/
private theorem plr_norm_bounds
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T : V →L[𝕜] E) {n : ℕ} (mk : Fin n → V) (ε : ℝ) (hε : 0 < ε)
    (hcover : ∀ u : V, ‖u‖ = 1 →
      ∃ k, ‖u - mk k‖ < ε / (8 + 4 * ε))
    (hnet : ∀ k,
      1 - ε / (8 + 4 * ε) ≤ ‖T (mk k)‖
        ∧ ‖T (mk k)‖ ≤ 1 + ε / (8 + 4 * ε)) :
    ∀ u : V,
      (1 + ε)⁻¹ * ‖u‖ ≤ ‖T u‖ ∧ ‖T u‖ ≤ (1 + ε) * ‖u‖ := by
  classical
  let δ := ε / (8 + 4 * ε)
  obtain ⟨hδ0, hδ1, hupRatio, hlowRatio⟩ := plr_delta_estimates ε hε
  let t : Finset V := Finset.univ.image mk
  have hcover' : ∀ u : V, ‖u‖ = 1 → ∃ k ∈ t, ‖u - k‖ < δ := by
    intro u hu
    obtain ⟨k, hk⟩ := hcover u hu
    refine ⟨mk k, Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩, ?_⟩
    simpa [δ] using hk
  have hup : ∀ k ∈ t, ‖T k‖ ≤ 1 + δ := by
    intro k hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
    simpa [δ] using (hnet i).2
  have hlow : ∀ k ∈ t, 1 - δ ≤ ‖T k‖ := by
    intro k hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
    simpa [δ] using (hnet i).1
  have hTop : ‖T‖ ≤ (1 + δ) / (1 - δ) :=
    plr_opNorm_of_net T hδ0 hδ1 hcover' hup
  have hLow : ∀ u : V, ((1 - 3 * δ) / (1 - δ)) * ‖u‖ ≤ ‖T u‖ :=
    plr_lower_of_net T hδ0 hδ1 hcover' hlow hTop
  intro u
  constructor
  · exact (mul_le_mul_of_nonneg_right hlowRatio (norm_nonneg u)).trans (hLow u)
  · calc
      ‖T u‖ ≤ ‖T‖ * ‖u‖ := ContinuousLinearMap.le_opNorm T u
      _ ≤ ((1 + δ) / (1 - δ)) * ‖u‖ :=
        mul_le_mul_of_nonneg_right hTop (norm_nonneg u)
      _ ≤ (1 + ε) * ‖u‖ :=
        mul_le_mul_of_nonneg_right hupRatio (norm_nonneg u)

/-- Pairing equality on the canonical finite basis extends to the whole space. -/
private theorem plr_pair_from_finBasis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
    [FiniteDimensional 𝕜 N]
    (iN : N →L[𝕜] StrongDual 𝕜 E) (z : StrongDual 𝕜 (StrongDual 𝕜 E)) (x : E)
    (hpair : ∀ i, (iN ((Module.finBasis 𝕜 N) i)) x
      = z (iN ((Module.finBasis 𝕜 N) i))) :
    ∀ n : N, (iN n) x = z (iN n) := by
  intro n
  rw [show n = ∑ i, (Module.finBasis 𝕜 N).repr n i
      • (Module.finBasis 𝕜 N) i from (Module.finBasis 𝕜 N).sum_repr n |>.symm]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => by rw [hpair i])

/-- Assembly of N1--N8 on the range of `iM`. -/
private theorem plr_assemble
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    [FiniteDimensional 𝕜 M]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
    [FiniteDimensional 𝕜 N]
    (iM : M →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E))
    (iN : N →L[𝕜] StrongDual 𝕜 E)
    (hM_inj : Function.Injective iM) (hN_inj : Function.Injective iN)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : M →L[𝕜] E),
      (∀ u : M, (1 + ε)⁻¹ * ‖iM u‖ ≤ ‖T u‖
        ∧ ‖T u‖ ≤ (1 + ε) * ‖iM u‖)
      ∧ (∀ (u : M) (n : N), (iN n) (T u) = (iM u) (iN n))
      ∧ (∀ (u : M) (x : E),
        iM u = NormedSpace.inclusionInDoubleDual 𝕜 E x → T u = x) := by
  let Mp := LinearMap.range iM.toLinearMap
  let _ : NormedAddCommGroup ↥Mp := plrNACG_Mp Mp
  let _ : NormedSpace 𝕜 ↥Mp := plrNS_Mp Mp
  let iMr : M →L[𝕜] ↥Mp := iM.rangeRestrict
  let iMEquiv : M ≃ₗ[𝕜] ↥Mp :=
    LinearEquiv.ofBijective iMr.toLinearMap ⟨(by
      intro u v huv
      apply hM_inj
      exact congrArg Subtype.val huv), (by
      intro u
      obtain ⟨v, hv⟩ := u.prop
      exact ⟨v, Subtype.ext hv⟩)⟩
  let _ : FiniteDimensional 𝕜 ↥Mp :=
    FiniteDimensional.of_surjective iMEquiv.toLinearMap iMEquiv.surjective
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (plr_M0 Mp)
  let _ : NormedAddCommGroup ↥C := plrNACG_C Mp C
  let b : Fin (Module.finrank 𝕜 ↥C) → StrongDual 𝕜 (StrongDual 𝕜 E) :=
    fun j => Mp.subtype (C.subtype ((Module.finBasis 𝕜 ↥C) j))
  let Np := LinearMap.range iN.toLinearMap
  let iNr : N →ₗ[𝕜] ↥Np := iN.toLinearMap.rangeRestrict
  let iNEquiv : N ≃ₗ[𝕜] ↥Np :=
    LinearEquiv.ofBijective iNr ⟨(by
      intro u v huv
      apply hN_inj
      exact congrArg Subtype.val huv), (by
      intro u
      obtain ⟨v, hv⟩ := u.prop
      exact ⟨v, Subtype.ext hv⟩)⟩
  let f : Fin (Module.finrank 𝕜 N) → StrongDual 𝕜 E :=
    fun i => Np.subtype (iNEquiv ((Module.finBasis 𝕜 N) i))
  let δ := ε / (8 + 4 * ε)
  have hδ0 : 0 < δ := by
    simpa [δ] using (plr_delta_estimates ε hε).1
  obtain ⟨card, mk, hmknorm, hcover⟩ := plr_net_exists Mp hδ0
  have hexg : ∀ k : Fin card, ∃ g : StrongDual 𝕜 E,
      ‖g‖ ≤ 1 ∧ 1 - δ ≤ RCLike.re ((Mp.subtype (mk k)) g) := by
    intro k
    apply plr_norming (Mp.subtype (mk k))
    · exact hmknorm k
    · exact hδ0
  choose g hg hgnorm using hexg
  let a : Fin card → E :=
    fun k => plr_S0 Mp (plr_pi0 Mp C hC (mk k))
  let c : Fin card → Fin (Module.finrank 𝕜 ↥C) → 𝕜 :=
    fun k j => (Module.finBasis 𝕜 ↥C).repr (plr_pi1 Mp C hC (mk k)) j
  let mBid : Fin card → StrongDual 𝕜 (StrongDual 𝕜 E) :=
    fun k => Mp.subtype (mk k)
  have hm : ∀ k (h : StrongDual 𝕜 E),
      mBid k h = h (a k) + ∑ j, c k j * b j h := by
    intro k h
    have hd := congrArg (fun z : StrongDual 𝕜 (StrongDual 𝕜 E) => z h)
      (plr_decomp Mp C hC (mk k))
    simpa only [mBid, a, c, b, add_apply, sum_apply, smul_apply, smul_eq_mul,
      NormedSpace.dual_def] using hd
  have hmnorm : ∀ k, ‖mBid k‖ = 1 := by
    intro k
    exact hmknorm k
  obtain ⟨y, hfy, hyg, hynorm⟩ := plr_solve
    (inferInstance : Fintype (Fin card)) a c f g b mBid hm hmnorm hδ0
  let Tp : ↥Mp →L[𝕜] E := plr_T' Mp C hC y
  have hnet : ∀ k, 1 - δ ≤ ‖Tp (mk k)‖ ∧ ‖Tp (mk k)‖ ≤ 1 + δ :=
    plr_T'_net Mp C hC y a c g mBid mk (fun _ => rfl) (fun _ _ => rfl)
      hg hgnorm hyg hynorm
  have hbounds : ∀ u : ↥Mp,
      (1 + ε)⁻¹ * ‖u‖ ≤ ‖Tp u‖ ∧ ‖Tp u‖ ≤ (1 + ε) * ‖u‖ := by
    apply plr_norm_bounds Tp mk ε hε
    · simpa [δ] using hcover
    · simpa [δ] using hnet
  let T : M →L[𝕜] E := Tp.comp iMr
  refine ⟨T, ?_, ?_, ?_⟩
  · intro u
    change (1 + ε)⁻¹ * ‖iMr u‖ ≤ ‖Tp (iMr u)‖
      ∧ ‖Tp (iMr u)‖ ≤ (1 + ε) * ‖iMr u‖
    exact hbounds (iMr u)
  · intro u n
    apply plr_pair_from_finBasis iN (iM u) (T u)
    intro i
    change f i (Tp (iMr u)) = (Mp.subtype (iMr u)) (f i)
    exact plr_T'_pair Mp C hC y f b hfy (fun _ => rfl) (iMr u) i
  · intro u x hux
    change Tp (iMr u) = x
    apply plr_T'_fix Mp C hC y (iMr u) x
    exact hux

/--
**Principle of local reflexivity.** Let $E$ be a Banach space over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, with dual $E^*$, bidual $E^{**}$ and canonical embedding $J \colon E \to E^{**}$.
Let $M$ and $N$ be finite-dimensional normed spaces over $\mathbb{K}$ with injective bounded
linear maps $i_M \colon M \to E^{**}$ and $i_N \colon N \to E^*$, and let $\varepsilon > 0$. Then
there is a bounded linear map $T \colon M \to E$ such that for all $m \in M$, $n \in N$ and
$x \in E$ we have
$(1 + \varepsilon)^{-1} \|i_M(m)\| \le \|T m\| \le (1 + \varepsilon) \|i_M(m)\|$,
$i_N(n)(T m) = i_M(m)(i_N(n))$, and $T m = x$ whenever $i_M(m) = J x$.

Proof: Helly's lemma applied to finitely many linear conditions plus one norm bound, then a finite
$\delta$-net of the unit sphere of $i_M(M)$ turns net-point bounds into the $(1+\varepsilon)$
bounds (the elementary proof in Albiac–Kalton, *Topics in Banach Space Theory*).

Proves `Wanted` entry `principle_of_local_reflexivity`.

Source: J.
Lindenstrauss and H. Rosenthal, Israel J. Math. 7 (1969) 325-349, principle of local reflexivity;
Johnson-Rosenthal-Zippin 1971 refinements; Albiac and Kalton, Topics in Banach Space Theory; Lean
states `RCLike` Banach finite- dimensional `M, N` version with `(1+ε)`-isometry and pairing
preservation.
-/
public theorem principle_of_local_reflexivity
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M] [FiniteDimensional 𝕜 M]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N] [FiniteDimensional 𝕜 N]
    (iM : M →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E))
    (iN : N →L[𝕜] StrongDual 𝕜 E)
    (hM_inj : Function.Injective iM)
    (hN_inj : Function.Injective iN)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : M →L[𝕜] E),
      (∀ m : M, (1 + ε)⁻¹ * ‖iM m‖ ≤ ‖T m‖ ∧ ‖T m‖ ≤ (1 + ε) * ‖iM m‖)
      ∧ (∀ (m : M) (n : N), (iN n) (T m) = (iM m) (iN n))
      ∧ (∀ (m : M) (x : E), iM m = NormedSpace.inclusionInDoubleDual 𝕜 E x → T m = x) := by
  exact plr_assemble iM iN hM_inj hN_inj ε hε

end

end MathlibExt.Analysis.FunctionalAnalysis.LocalReflexivityWanted
