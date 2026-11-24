/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Sheaf.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Constructible
import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

/-!
# Hadamard–Caccioppoli global inverse theorem

A proper `C^∞` local diffeomorphism `ℝⁿ → ℝⁿ` is a global `C^∞`
diffeomorphism.
-/

noncomputable section

open scoped Manifold ContDiff

namespace MathlibExt.Geometry.Manifold.HadamardGlobalInverseWanted

/-- A covering map over a simply connected base with path-connected total space is
injective: two points over the same base point are joined by a path whose projection is a
loop, hence null-homotopic; the lifts of the two homotopic paths from the same starting
point agree at the endpoint. -/
private theorem injective_of_isCoveringMap_of_simplyConnected
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PathConnectedSpace E] [SimplyConnectedSpace X]
    {p : E → X} (cov : IsCoveringMap p) : Function.Injective p := by
  intro a b hab
  let γ : Path a b := PathConnectedSpace.somePath a b
  let β : Path (p a) (p a) := (γ.map cov.continuous).cast rfl hab
  have hhom : β.Homotopic (Path.refl (p a)) := SimplyConnectedSpace.paths_homotopic _ _
  have hβ0 : β.toContinuousMap 0 = p a := β.source
  have hrefl0 : (Path.refl (p a)).toContinuousMap 0 = p a := (Path.refl _).source
  have hlift : cov.liftPath β.toContinuousMap a hβ0 = γ.toContinuousMap :=
    ((cov.eq_liftPath_iff' hβ0).mpr ⟨rfl, γ.source⟩).symm
  have hlift_refl : cov.liftPath (Path.refl (p a)).toContinuousMap a hrefl0 =
      ContinuousMap.const _ a :=
    ((cov.eq_liftPath_iff' hrefl0).mpr ⟨rfl, rfl⟩).symm
  have hend := cov.liftPath_apply_one_eq_of_homotopicRel hhom a hβ0 hrefl0
  rw [hlift, hlift_refl] at hend
  have h1 : γ.toContinuousMap 1 = b := γ.target
  rw [h1] at hend
  exact hend.symm

/--
**Hadamard–Caccioppoli global inverse theorem.** Let $n \in \mathbb{N}$ and let
$f : \mathbb{R}^n \to \mathbb{R}^n$ be a proper map that is a $C^\infty$ local diffeomorphism.
Then $f$ is a global $C^\infty$ diffeomorphism: there is a $C^\infty$ diffeomorphism
$\Phi : \mathbb{R}^n \to \mathbb{R}^n$ whose underlying map is $f$.

Source: J. Hadamard, Bull. Soc. Math. France 34 (1906) 71–84; R. Caccioppoli, Rend. Sem. Mat.
Univ. Padova 3 (1932); F.-C. Plastock, Trans. Amer. Math. Soc. 200 (1974) extension to Banach
spaces; J. Lee, Riemannian Manifolds? Lean states Euclidean `ℝⁿ = EuclideanSpace ℝ (Fin n)`
specialization with `IsProperMap` and `IsLocalDiffeomorph` hypotheses.
Proves `Wanted` entry `hadamard_caccioppoli_global_inverse`.
-/
theorem hadamard_caccioppoli_global_inverse
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf_proper : IsProperMap f)
    (hf_local : IsLocalDiffeomorph (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) f) :
    ∃ (Φ : EuclideanSpace ℝ (Fin n) ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ EuclideanSpace ℝ (Fin n)), ⇑Φ = f := by
  have hhome : IsLocalHomeomorph f := hf_local.isLocalHomeomorph
  have hfin : ∀ x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n))), (f ⁻¹' {x}).Finite := by
    intro x _
    have hdisc_img : IsDiscrete (f '' (f ⁻¹' {x})) := by
      apply Set.Subsingleton.isDiscrete
      intro y hy z hz
      simp only [Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff] at hy hz
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hz
      rw [ha, hb]
    have hdisc : IsDiscrete (f ⁻¹' {x}) :=
      hhome.isLocalHomeomorphOn.isDiscrete_of_image hdisc_img
    exact (hf_proper.isCompact_preimage isCompact_singleton).finite hdisc
  have hcov : IsCoveringMap f :=
    isCoveringMap_iff_isCoveringMapOn_univ.mpr
      (hf_proper.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn hfin
        hhome.isLocalHomeomorphOn)
  have hsurj : Function.Surjective f := by
    have hclopen : IsClopen (Set.range f) := ⟨hf_proper.isClosed_range, hf_local.isOpen_range⟩
    have hne : (Set.range f).Nonempty := ⟨f 0, ⟨0, rfl⟩⟩
    have huniv : Set.range f = Set.univ := hclopen.eq_univ hne
    exact Set.range_eq_univ.mp huniv
  have hinj : Function.Injective f := injective_of_isCoveringMap_of_simplyConnected hcov
  choose g hg using Function.bijective_iff_has_inverse.mp ⟨hinj, hsurj⟩
  refine ⟨
    { toFun := f
      invFun := g
      left_inv := hg.1
      right_inv := hg.2
      contMDiff_toFun := hf_local.contMDiff
      contMDiff_invFun := fun y ↦ ?_ }, rfl⟩
  have h := hf_local (g y)
  rw [← hg.2 y]
  exact h.localInverse_contMDiffAt.congr_of_eventuallyEq
    (h.localInverse_eventuallyEq_right.mono fun y' hy' ↦ (congrArg g hy').symm.trans (hg.1 _))

end MathlibExt.Geometry.Manifold.HadamardGlobalInverseWanted
