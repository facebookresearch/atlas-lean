/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Weak convergence in normed spaces

Three standard consequences of weak convergence of a sequence in a
normed space `E` over `ℝ` or `ℂ`:

* a weakly convergent sequence is norm-bounded (by the uniform boundedness
  principle applied to the evaluation functionals);
* the norm is weakly lower semicontinuous along sequences: if `u n`
  converges weakly to `x`, then `‖x‖ ≤ liminf ‖u n‖`;
* bounded linear operators preserve weak convergence.

This file packages supporting sequence corollaries using canonical
Mathlib APIs. For boundedness, Banach–Steinhaus is applied to the complete
strong dual, and the bidual isometry returns a norm bound in `E`.
The lower-semicontinuity proof uses a Hahn–Banach functional `g` with
`‖g‖ ≤ 1` and `g x = ‖x‖`. No completeness hypothesis on `E` is needed.

Weak convergence is stated as convergence of every continuous linear
functional, with equivalent `toWeakSpace` interfaces. These conversions
specialize `WeakBilin.tendsto_iff_forall_eval_tendsto`; Mathlib's
`WeakSpace.map` already gives preservation by continuous linear maps.

The archived `v1/Atlas/IntroductionToFunctionalAnalysis/code/HahnBanach.lean`
provides related Hahn–Banach context. The weak convergence of orthonormal
sequences and Mazur's lemma are supporting companions from batches 24
and 37. The present sequential results are not imported from a v1 target.
See also Rudin, *Functional Analysis*, 2nd edition, Chapter 3.
-/

@[expose] public section

namespace MathlibExt.Analysis.Normed.Module.WeakConvergence

open Set Filter Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Weakly convergent sequences are norm-bounded.** If `f (u n) → f x`
for every continuous linear functional `f`, then the norms `‖u n‖` are
uniformly bounded. -/
theorem bddAbove_norm_range_of_forall_tendsto {u : ℕ → E} {x : E}
    (h : ∀ f : StrongDual 𝕜 E, Tendsto (fun n => f (u n)) atTop (𝓝 (f x))) :
    BddAbove (Set.range fun n => ‖u n‖) := by
  have hpoint : ∀ f : StrongDual 𝕜 E, ∃ C, ∀ n,
      ‖(NormedSpace.inclusionInDoubleDual 𝕜 E (u n)) f‖ ≤ C := by
    intro f
    have hb := Metric.isBounded_range_of_tendsto (fun n => f (u n)) (h f)
    rw [Metric.isBounded_iff] at hb
    obtain ⟨C, hC⟩ := hb
    refine ⟨C + ‖f (u 0)‖, fun n => ?_⟩
    simp only [NormedSpace.dual_def]
    have h1 := hC ⟨n, rfl⟩ ⟨0, rfl⟩
    rw [dist_eq_norm] at h1
    calc ‖f (u n)‖ = ‖(f (u n) - f (u 0)) + f (u 0)‖ := by rw [sub_add_cancel]
      _ ≤ ‖f (u n) - f (u 0)‖ + ‖f (u 0)‖ := norm_add_le _ _
      _ ≤ C + ‖f (u 0)‖ := by linarith
  obtain ⟨C, hC⟩ := banach_steinhaus (𝕜 := 𝕜) (E := StrongDual 𝕜 E) (F := 𝕜)
    (g := fun n => NormedSpace.inclusionInDoubleDual 𝕜 E (u n)) hpoint
  refine ⟨C, ?_⟩
  rintro _ ⟨n, rfl⟩
  show ‖u n‖ ≤ C
  have hnorm : ‖NormedSpace.inclusionInDoubleDual 𝕜 E (u n)‖ = ‖u n‖ :=
    (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E)).norm_map (u n)
  rw [← hnorm]
  exact hC n

/-- **Weak lower semicontinuity of the norm.** If `u n` converges weakly
to `x`, then `‖x‖ ≤ liminf ‖u n‖`. -/
theorem norm_le_liminf_norm_of_forall_tendsto {u : ℕ → E} {x : E}
    (h : ∀ f : StrongDual 𝕜 E, Tendsto (fun n => f (u n)) atTop (𝓝 (f x))) :
    ‖x‖ ≤ liminf (fun n => ‖u n‖) atTop := by
  obtain ⟨g, hg1, hg2⟩ := exists_dual_vector'' 𝕜 x
  obtain ⟨C, hC⟩ := bddAbove_norm_range_of_forall_tendsto (𝕜 := 𝕜) (E := E) h
  have hlim : Tendsto (fun n => ‖g (u n)‖) atTop (𝓝 ‖x‖) := by
    have hgT : Tendsto (fun n => g (u n)) atTop (𝓝 (g x)) := h g
    have hgn := hgT.norm
    rw [hg2] at hgn
    simpa using hgn
  rw [← hlim.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun n => ?_) hlim.isBoundedUnder_ge
    (isCoboundedUnder_ge_of_le atTop fun n => hC ⟨n, rfl⟩)
  calc ‖g (u n)‖ ≤ ‖g‖ * ‖u n‖ := g.le_opNorm _
    _ ≤ 1 * ‖u n‖ := by gcongr
    _ = ‖u n‖ := one_mul _

/-- **Bounded operators preserve weak convergence.** If `u n` converges
weakly to `x`, then `T (u n)` converges weakly to `T x` for every bounded
linear operator `T`. -/
theorem tendsto_apply_of_forall_tendsto {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {u : ℕ → E} {x : E} (T : E →L[𝕜] F)
    (h : ∀ f : StrongDual 𝕜 E, Tendsto (fun n => f (u n)) atTop (𝓝 (f x))) :
    ∀ g : StrongDual 𝕜 F, Tendsto (fun n => g (T (u n))) atTop (𝓝 (g (T x))) := by
  intro g
  simpa using h (g.comp T)

/-- Weak convergence in `toWeakSpace` form implies the all-functionals form. -/
theorem forall_tendsto_of_tendsto_weakSpace {u : ℕ → E} {x : E}
    (h : Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x))) :
    ∀ f : StrongDual 𝕜 E, Tendsto (fun n => f (u n)) atTop (𝓝 (f x)) := by
  have hinj : Function.Injective (LinearMap.flip (topDualPairing 𝕜 E)) := by
    intro a b hab
    exact SeparatingDual.eq_iff_forall_dual_eq.mpr fun f =>
      congrFun (congrArg DFunLike.coe hab) f
  exact (WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing 𝕜 E).flip hinj).mp h

/-- The all-functionals form implies weak convergence in `toWeakSpace` form. -/
theorem tendsto_weakSpace_of_forall_tendsto {u : ℕ → E} {x : E}
    (h : ∀ f : StrongDual 𝕜 E, Tendsto (fun n => f (u n)) atTop (𝓝 (f x))) :
    Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)) := by
  have hinj : Function.Injective (LinearMap.flip (topDualPairing 𝕜 E)) := by
    intro a b hab
    exact SeparatingDual.eq_iff_forall_dual_eq.mpr fun f =>
      congrFun (congrArg DFunLike.coe hab) f
  exact (WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing 𝕜 E).flip hinj).mpr h

/-- Boundedness of weakly convergent sequences, `toWeakSpace` form. -/
theorem bddAbove_norm_range_of_tendsto_weakSpace {u : ℕ → E} {x : E}
    (h : Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x))) :
    BddAbove (Set.range fun n => ‖u n‖) :=
  bddAbove_norm_range_of_forall_tendsto (forall_tendsto_of_tendsto_weakSpace h)

/-- Weak lower semicontinuity of the norm, `toWeakSpace` form. -/
theorem norm_le_liminf_norm_of_tendsto_weakSpace {u : ℕ → E} {x : E}
    (h : Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x))) :
    ‖x‖ ≤ liminf (fun n => ‖u n‖) atTop :=
  norm_le_liminf_norm_of_forall_tendsto (forall_tendsto_of_tendsto_weakSpace h)

/-- Preservation of weak convergence by bounded operators, `toWeakSpace` form. -/
theorem tendsto_weakSpace_apply_of_tendsto_weakSpace {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {u : ℕ → E} {x : E} (T : E →L[𝕜] F)
    (h : Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x))) :
    Tendsto (fun n => toWeakSpace 𝕜 F (T (u n))) atTop (𝓝 (toWeakSpace 𝕜 F (T x))) :=
  tendsto_weakSpace_of_forall_tendsto
    (tendsto_apply_of_forall_tendsto T (forall_tendsto_of_tendsto_weakSpace h))

end MathlibExt.Analysis.Normed.Module.WeakConvergence
