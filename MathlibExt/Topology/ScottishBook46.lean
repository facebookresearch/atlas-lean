/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Topology.Connected.Basic

import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.UrysohnsLemma

/-!
# Unicoherence of the unit sphere in an infinite-dimensional Banach space

We prove that two closed connected sets covering the unit sphere have connected intersection.
The proof contracts loops in the punctured space and uses uniqueness of continuous logarithms.
-/

public section

namespace MathlibExt.Topology.ScottishBook46Wanted

open Set Metric NormedSpace
open scoped ContinuousMap unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem continuousOn_normalize_punctured :
    ContinuousOn (normalize : E → E) ({0}ᶜ : Set E) := by
  intro x hx
  have hx₀ : x ≠ 0 := by simpa using hx
  exact ((continuousAt_id.norm.inv₀ (norm_ne_zero_iff.mpr hx₀)).smul
    continuousAt_id).continuousWithinAt

private theorem not_isCompact_unitSphere (h : ¬ Module.Finite ℝ E)
    (hne : (sphere (0 : E) 1).Nonempty) : ¬ IsCompact (sphere (0 : E) 1) := by
  intro hs
  let f : ℝ × E → E := fun p ↦ p.1 • p.2
  have hball : f '' (Icc (0 : ℝ) 1 ×ˢ sphere (0 : E) 1) = closedBall (0 : E) 1 := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨r, x⟩, ⟨hr, hx⟩, rfl⟩
      rw [mem_closedBall_zero_iff]
      simpa [f, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1,
        mem_sphere_zero_iff_norm.mp hx] using hr.2
    · intro x hx
      by_cases hx₀ : x = 0
      · obtain ⟨y, hy⟩ := hne
        exact ⟨(0, y), ⟨by simp, hy⟩, by simp [f, hx₀]⟩
      · exact ⟨(‖x‖, normalize x),
          ⟨⟨norm_nonneg _, mem_closedBall_zero_iff.mp hx⟩,
            mem_sphere_zero_iff_norm.mpr (norm_normalize hx₀)⟩,
          norm_smul_normalize x⟩
  exact h (FiniteDimensional.of_isCompact_closedBall ℝ one_pos
    (hball ▸ ((isCompact_Icc.prod hs).image (by fun_prop : Continuous f))))

private theorem starConvex_compl_ray {v : E} (hv : v ≠ 0) :
    StarConvex ℝ (-v) {x : E | ∀ r : ℝ, 0 ≤ r → x ≠ r • v} := by
  intro x hx a b ha hb hab r hr he
  by_cases hb₀ : b = 0
  · have ha₁ : a = 1 := by simpa [hb₀] using hab
    have he' : (-1 : ℝ) • v = r • v := by simpa [ha₁, hb₀] using he
    have := smul_left_injective ℝ hv he'
    linarith
  · have he' : b • x = (r + a) • v := by
      rw [add_comm r a, add_smul, ← neg_add_eq_iff_eq_add, ← smul_neg]
      exact he
    have hx' := (eq_inv_smul_iff₀ hb₀).mpr he'
    rw [smul_smul] at hx'
    exact hx _ (mul_nonneg (inv_nonneg.mpr hb) (add_nonneg hr ha)) hx'

private theorem simplyConnected_punctured (h : ¬ Module.Finite ℝ E)
    (hrank : 1 < Module.rank ℝ E) : IsSimplyConnected ({0}ᶜ : Set E) := by
  let D : Set E := {0}ᶜ
  change SimplyConnectedSpace D
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_compl_singleton_of_one_lt_rank hrank 0), ?_⟩
  intro x γ
  let d : I → E := fun t ↦ normalize (γ t : E)
  have hd : Continuous d := continuousOn_normalize_punctured.comp_continuous
    (continuous_subtype_val.comp γ.continuous) (fun t ↦ (γ t).property)
  have hγ₀ (t : I) : (γ t : E) ≠ 0 := by
    simpa only [D, mem_compl_iff, mem_singleton_iff] using (γ t).property
  have hsubset : range d ⊆ sphere (0 : E) 1 := by
    rintro _ ⟨t, rfl⟩
    exact mem_sphere_zero_iff_norm.mpr (norm_normalize (hγ₀ t))
  have hs := (isPathConnected_sphere hrank (0 : E) zero_le_one).nonempty
  have hmissing : ¬ sphere (0 : E) 1 ⊆ range d := fun hcover ↦
    not_isCompact_unitSphere h hs ((Subset.antisymm hsubset hcover) ▸ isCompact_range hd)
  obtain ⟨v, hv, hvd⟩ := not_subset.mp hmissing
  have hv₀ := ne_of_mem_sphere hv (one_ne_zero : (1 : ℝ) ≠ 0)
  -- The loop misses the entire ray through the omitted direction.
  let U : Set E := {y : E | ∀ r : ℝ, 0 ≤ r → y ≠ r • v}
  have hγ : ∀ t, (γ t : E) ∈ U := by
    intro t r hr he
    have hr₀ : r ≠ 0 := fun hr₀ ↦ hγ₀ t (by simpa [hr₀] using he)
    apply hvd
    exact ⟨t, by
      dsimp [d]
      rw [he, normalize_smul_of_pos (lt_of_le_of_ne hr hr₀.symm),
        normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp hv)]⟩
  have hx : (x : E) ∈ U := by simpa only [Path.source] using hγ 0
  let x' : U := ⟨x, hx⟩
  let γ' : Path x' x' :=
    { toFun := fun t ↦ ⟨γ t, hγ t⟩
      continuous_toFun := (continuous_subtype_val.comp γ.continuous).subtype_mk _
      source' := Subtype.ext (congrArg (fun z : D ↦ (z : E)) γ.source)
      target' := Subtype.ext (congrArg (fun z : D ↦ (z : E)) γ.target) }
  have hUD : U ⊆ D := fun y hy ↦ by simpa [D] using hy 0 le_rfl
  let i : C(U, D) := ⟨Set.inclusion hUD, continuous_inclusion hUD⟩
  let := (starConvex_compl_ray hv₀).contractibleSpace ⟨x, hx⟩
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic γ' (Path.refl x')
  have hmap : γ'.map i.continuous = γ := by
    ext t
    rfl
  have hrefl : (Path.refl x').map i.continuous = Path.refl x := by
    ext t
    rfl
  exact ⟨hmap ▸ hrefl ▸ F.map i⟩

private theorem eqOn_of_exp_eqOn {X : Type*} [TopologicalSpace X]
    {A : Set X} {f g : X → ℂ} {x : X}
    (hA : IsPreconnected A) (hf : ContinuousOn f A) (hg : ContinuousOn g A)
    (he : EqOn (Complex.exp ∘ f) (Complex.exp ∘ g) A)
    (hx : x ∈ A) (hfg : f x = g x) : EqOn f g A := by
  exact Complex.isCoveringMap_exp.eqOn_of_comp_eqOn hA hf hg
    (fun _ hy ↦ Subtype.ext (he hy)) hx hfg

/--
**Unit spheres of infinite-dimensional Banach spaces are unicoherent.** Let $E$ be a real
Banach space that is not finite-dimensional, and let $S = \{x \in E : \|x\| = 1\}$ be its unit
sphere. If $A$ and $B$ are closed connected subsets of $S$ with $A \cup B = S$, then $A \cap B$ is
connected. Here connected sets are nonempty by definition.

This answers Banach's Problem 46 of the Scottish Book: is the sphere in a space of type (B)
uni-coherent, that is, whenever it is the union of two continua $A$ and $B$, is $A \cap B$
connected? Continua are read as closed connected sets, the meaning of uni-coherence for
non-compact spaces: in infinite dimensions the sphere is not compact, so two compact sets could
not cover it. The statement is restricted to infinite-dimensional spaces; in dimension $1$ the
sphere is two points and in dimension $2$ it is a circle, and neither is uni-coherent (two
semicircles cover the circle and meet in two points). In infinite dimensions the sphere is an
absolute retract, and the affirmative answer follows from the theorems of Borsuk and Eilenberg
recorded in the addendum.

Source: S. Banach, Problem 46 of the Scottish Book; addendum in the
Scottish Book citing Borsuk and Eilenberg, Fund. Math. 26, p. 61; see the
commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser,
2015).
-/
theorem sphere_in_banach_space_is_unicoherent :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
      ¬ Module.Finite ℝ E →
      ∀ A B : Set E, A ⊆ Metric.sphere (0 : E) 1 → B ⊆ Metric.sphere (0 : E) 1 →
        A ∪ B = Metric.sphere (0 : E) 1 → IsClosed A → IsConnected A →
        IsClosed B → IsConnected B → IsConnected (A ∩ B) := by
  classical
  intro E _ _ _ h A B hAS hBS hcover hAc hA hBc hB
  have hrank : 1 < Module.rank ℝ E :=
    Cardinal.one_lt_aleph0.trans_le
      (le_of_not_gt fun hlt ↦ h (Module.rank_lt_aleph0_iff.mp hlt))
  have hS := (isPathConnected_sphere hrank (0 : E) zero_le_one).isConnected
  refine ⟨?_, ?_⟩
  · obtain ⟨x, _, hx⟩ := isPreconnected_closed_iff.mp hS.isPreconnected A B hAc hBc
      hcover.ge (by simpa [inter_eq_right.mpr hAS] using hA.nonempty)
      (by simpa [inter_eq_right.mpr hBS] using hB.nonempty)
    exact ⟨x, hx⟩
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed (hAc.inter hBc)]
  intro U V hU hV hUV hdisj
  by_contra! hsep
  obtain ⟨x₀, hx₀, hx₀V⟩ := not_subset.mp hsep.2
  obtain ⟨x₁, hx₁, hx₁U⟩ := not_subset.mp hsep.1
  obtain ⟨f, hf₀, hf₁, -⟩ := exists_continuous_zero_one_of_isClosed hU hV hdisj
  let c : ℂ := 2 * Real.pi * Complex.I
  let g : E → ℂ := fun x ↦ c * (f x : ℂ)
  have hg : Continuous g := by fun_prop
  have hg₀ : g x₀ = 0 := by simp [g, hf₀ ((hUV hx₀).resolve_right hx₀V)]
  have hg₁ : g x₁ = c := by simp [g, hf₁ ((hUV hx₁).resolve_left hx₁U)]
  have h_exp : ∀ x ∈ A ∩ B, Complex.exp (g x) = 1 := by
    intro x hx
    rcases hUV hx with hxU | hxV
    · simp [g, hf₀ hxU]
    · simp [g, hf₁ hxV, c]
  -- The two local logarithms exponentiate to a single continuous map on the sphere.
  let F : E → ℂ := A.piecewise (Complex.exp ∘ g) 1
  have hFA : EqOn F (Complex.exp ∘ g) A := fun x hx ↦ by simp [F, hx]
  have hFB : EqOn F 1 B := by
    intro x hx
    by_cases hxA : x ∈ A
    · simpa [F, hxA] using h_exp x ⟨hxA, hx⟩
    · simp [F, hxA]
  have hF : ContinuousOn F (sphere (0 : E) 1) := by
    rw [← hcover]
    exact ((Complex.continuous_exp.comp hg).continuousOn.congr hFA).union_of_isClosed
      (continuousOn_const.congr hFB) hAc hBc
  let D : Set E := {0}ᶜ
  have hSD : sphere (0 : E) 1 ⊆ D := fun x hx ↦ by
    simpa [D] using ne_of_mem_sphere hx (one_ne_zero : (1 : ℝ) ≠ 0)
  have hnS : MapsTo (normalize : E → E) D (sphere (0 : E) 1) := fun x hx ↦
    mem_sphere_zero_iff_norm.mpr (norm_normalize (by simpa [D] using hx))
  obtain ⟨L, hL, hLF⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    (simplyConnected_punctured h hrank) isOpen_compl_singleton
    (hF.comp continuousOn_normalize_punctured hnS : ContinuousOn (F ∘ normalize) D) (by
      rintro ⟨x, hx, hFx⟩
      rw [Function.comp_apply] at hFx
      rcases (show normalize x ∈ A ∪ B from hcover.symm ▸ hnS hx) with hAx | hBx
      · exact (Complex.exp_ne_zero _) ((hFA hAx).symm.trans hFx)
      · exact one_ne_zero ((hFB hBx).symm.trans hFx))
  have hLF' : EqOn (Complex.exp ∘ L) F (sphere (0 : E) 1) := by
    intro x hx
    simpa [Function.comp_def, normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp hx)]
      using hLF (hSD hx)
  have hx₀S := hAS hx₀.1
  have hbase : Complex.exp (L x₀) = 1 := (hLF' hx₀S).trans (hFB hx₀.2)
  let L₀ : E → ℂ := fun x ↦ L x - L x₀
  have hL₀ : ContinuousOn L₀ D := hL.sub continuousOn_const
  have hL₀F : EqOn (Complex.exp ∘ L₀) F (sphere (0 : E) 1) := fun x hx ↦ by
    simpa [L₀, Complex.exp_sub, hbase] using hLF' hx
  -- Uniqueness of logarithms on each connected set forces incompatible values at x₁.
  have hLA : EqOn L₀ g A := eqOn_of_exp_eqOn hA.isPreconnected (hL₀.mono (hAS.trans hSD))
    hg.continuousOn (fun _ hx ↦ (hL₀F (hAS hx)).trans (hFA hx)) hx₀.1 (by simp [L₀, hg₀])
  have hLB : EqOn L₀ (fun _ ↦ 0) B := eqOn_of_exp_eqOn hB.isPreconnected
    (hL₀.mono (hBS.trans hSD)) continuousOn_const
    (fun _ hx ↦ by simpa using (hL₀F (hBS hx)).trans (hFB hx)) hx₀.2 (by simp [L₀])
  have hc : c ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  exact hc (hg₁.symm.trans ((hLA hx₁.1).symm.trans (hLB hx₁.2)))

end MathlibExt.Topology.ScottishBook46Wanted
