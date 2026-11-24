/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Closed range theorem for adjoints on Hilbert spaces

For a bounded operator `T` between Hilbert spaces, the range of `T` is closed
if and only if the range of its adjoint `T†` is closed.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis` (archived; not edited).
The book's adjoint-operator section (April 27, 2021) proves
`(Ran A)⊥ = Null (A*)`, and its Fredholm-alternative section (May 11, 2021)
studies closedness of `Range (μI − A)`. The closed-range theorem for adjoints
is not stated in the book; it is derived here from Mathlib's orthogonality
identities and Banach-space machinery (the anti-Lipschitz characterization of
closed range for injective operators).
-/

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **The range of a bounded operator as a set.** Let $E'$ and $F'$ be Hilbert spaces over
$\mathbb{K}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, and let $S : E' \to F'$ be a
bounded linear operator. The set of values of $S$ equals the underlying set of the range of $S$
regarded as a linear subspace of $F'$.

This lets closedness of the range pass between the anti-Lipschitz criterion, stated for the
set of values, and the adjoint orthogonality identities, stated for the linear subspace. -/
theorem setRange_eq_coe_linearMap_range {E' F' : Type*} [NormedAddCommGroup E']
    [InnerProductSpace 𝕜 E'] [CompleteSpace E'] [NormedAddCommGroup F']
    [InnerProductSpace 𝕜 F'] [CompleteSpace F'] (S : E' →L[𝕜] F') :
    Set.range S = (LinearMap.range S.toLinearMap : Set F') := by
  rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]

omit [CompleteSpace F] in
/-- **Restriction to the orthogonal complement of the kernel keeps the range.** Let $E$ be a
Hilbert space and $F$ an inner product space over $\mathbb{K}$, where $\mathbb{K}$ is
$\mathbb{R}$ or $\mathbb{C}$, and let $T : E \to F$ be a bounded linear operator. Then the
restriction of $T$ to the orthogonal complement $(\ker T)^\perp$ of its kernel has the same
range as $T$: every value $T x$ is attained at the orthogonal projection of $x$ onto
$(\ker T)^\perp$, since the difference lies in $\ker T$. -/
theorem range_comp_subtypeL_orthogonalComplement_ker (S : E →L[𝕜] F) :
    Set.range (S.comp (Submodule.subtypeL (LinearMap.ker S.toLinearMap)ᗮ)) =
      Set.range S := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨(x : E), by simp [ContinuousLinearMap.comp_apply]⟩
  · rintro y ⟨x, rfl⟩
    set x' := (LinearMap.ker S.toLinearMap)ᗮ.starProjection x with hx'
    have hx'_mem : x' ∈ (LinearMap.ker S.toLinearMap)ᗮ :=
      Submodule.starProjection_apply_mem _ _
    have hdiff : x - x' ∈ LinearMap.ker S.toLinearMap := by
      have h := Submodule.sub_starProjection_mem_orthogonal
        (K := (LinearMap.ker S.toLinearMap)ᗮ) x
      rwa [Submodule.orthogonal_orthogonal] at h
    have h0 : S (x - x') = 0 := LinearMap.mem_ker.mp hdiff
    have hSx : S x' = S x := by
      have hsub : S x - S x' = 0 := by rw [← map_sub]; exact h0
      exact (eq_of_sub_eq_zero hsub).symm
    exact ⟨⟨x', hx'_mem⟩, by simp [ContinuousLinearMap.comp_apply, hSx]⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Restriction to the orthogonal complement of the kernel is injective.** Let $E$ and $F$
be inner product spaces over $\mathbb{K}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$,
and let $T : E \to F$ be a bounded linear operator. Then the restriction of $T$ to the
orthogonal complement $(\ker T)^\perp$ of its kernel is injective: a vector lying in both
$\ker T$ and $(\ker T)^\perp$ is zero. -/
theorem injective_comp_subtypeL_orthogonalComplement_ker (S : E →L[𝕜] F) :
    Function.Injective (S.comp (Submodule.subtypeL (LinearMap.ker S.toLinearMap)ᗮ)) := by
  intro a b hab
  have hab' : S (a : E) = S (b : E) := by
    have h := hab
    simp [ContinuousLinearMap.comp_apply] at h
    exact h
  have hsub : ((a : E) - (b : E)) ∈ LinearMap.ker S.toLinearMap := by
    rw [LinearMap.mem_ker]
    show S ((a : E) - (b : E)) = 0
    rw [map_sub, hab', sub_self]
  have horth : ((a : E) - (b : E)) ∈ (LinearMap.ker S.toLinearMap)ᗮ := sub_mem a.2 b.2
  have hbot : ((a : E) - (b : E)) ∈ LinearMap.ker S.toLinearMap ⊓
      (LinearMap.ker S.toLinearMap)ᗮ := ⟨hsub, horth⟩
  rw [Submodule.inf_orthogonal_eq_bot] at hbot
  exact Subtype.ext (eq_of_sub_eq_zero ((Submodule.mem_bot 𝕜).mp hbot))

/-- **Closed range passes to the adjoint.** Let $E$ and $F$ be Hilbert spaces over $\mathbb{K}$,
where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, and let $T : E \to F$ be a bounded linear
operator with adjoint $T^\dagger$. If the range of $T$ is closed in $F$, then the range of
$T^\dagger$ is closed in $E$.

Proof sketch: if the range of $T$ is closed, then $T$ is bounded below on $(\ker T)^\perp$
(the anti-Lipschitz criterion for its injective restriction), say $\|x\| \le C \|T x\|$ there.
Every $y \in (\ker T^\dagger)^\perp$ lies in the range of $T$, because
$(\operatorname{ran} T)^\perp = \ker T^\dagger$ and the range is closed. Writing $y = T x$ with
$x \in (\ker T)^\perp$ gives
$\|y\|^2 = \operatorname{Re} \langle x, T^\dagger y \rangle \le \|x\| \|T^\dagger y\| \le
C \|y\| \|T^\dagger y\|$; cancelling $\|y\|$ shows that $T^\dagger$ is bounded below on
$(\ker T^\dagger)^\perp$, so its range, which is the range of its restriction to
$(\ker T^\dagger)^\perp$, is closed. -/
theorem isClosed_range_adjoint_of_isClosed_range (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range T.toLinearMap : Set F)) :
    IsClosed (LinearMap.range (adjoint T).toLinearMap : Set E) := by
  set T₁ := T.comp (Submodule.subtypeL (LinearMap.ker T.toLinearMap)ᗮ) with hT₁
  have hT₁_inj : Function.Injective T₁ := injective_comp_subtypeL_orthogonalComplement_ker T
  have hT₁_closed : IsClosed (Set.range T₁) := by
    rw [range_comp_subtypeL_orthogonalComplement_ker T, setRange_eq_coe_linearMap_range T]
    exact hT
  obtain ⟨C, hC⟩ := T₁.antilipschitz_of_injective_of_isClosed_range hT₁_inj hT₁_closed
  have hbound : ∀ y : ↥(LinearMap.ker (adjoint T).toLinearMap)ᗮ,
      ‖(y : F)‖ ≤ (C : ℝ) * ‖(adjoint T) (y : F)‖ := by
    intro y
    by_cases hy : (y : F) = 0
    · simp [hy]
    · have hker : (LinearMap.ker (adjoint T).toLinearMap)ᗮ =
          LinearMap.range T.toLinearMap := by
        rw [← ContinuousLinearMap.orthogonal_range T,
          Submodule.orthogonal_orthogonal_eq_closure]
        exact hT.submodule_topologicalClosure_eq
      have hy_range : (y : F) ∈ LinearMap.range T.toLinearMap := hker ▸ y.2
      obtain ⟨x, hx⟩ := hy_range
      set x' := (LinearMap.ker T.toLinearMap)ᗮ.starProjection x with hx'
      have hx'_mem : x' ∈ (LinearMap.ker T.toLinearMap)ᗮ :=
        Submodule.starProjection_apply_mem _ _
      have hTx' : T x' = (y : F) := by
        have hdiff : x - x' ∈ LinearMap.ker T.toLinearMap := by
          have h := Submodule.sub_starProjection_mem_orthogonal
            (K := (LinearMap.ker T.toLinearMap)ᗮ) x
          rwa [Submodule.orthogonal_orthogonal] at h
        have h0 : T (x - x') = 0 := LinearMap.mem_ker.mp hdiff
        have hTx : T x = (y : F) := hx
        have hsub : T x - T x' = 0 := by rw [← map_sub]; exact h0
        rw [hTx] at hsub
        exact (eq_of_sub_eq_zero hsub).symm
      have hanti : ‖x'‖ ≤ (C : ℝ) * ‖T x'‖ := by
        have h := hC.le_mul_dist ⟨x', hx'_mem⟩ (0 : ↥(LinearMap.ker T.toLinearMap)ᗮ)
        simpa [hT₁] using h
      rw [hTx'] at hanti
      have hinner : inner 𝕜 x' ((adjoint T) (y : F)) = inner 𝕜 (y : F) (y : F) := by
        rw [adjoint_inner_right, hTx']
      have hnorm_sq : ‖(y : F)‖ ^ 2 ≤ (C : ℝ) * ‖(y : F)‖ * ‖(adjoint T) (y : F)‖ := by
        calc ‖(y : F)‖ ^ 2 = RCLike.re (inner 𝕜 (y : F) (y : F)) :=
              (inner_self_eq_norm_sq (𝕜 := 𝕜) (y : F)).symm
          _ = RCLike.re (inner 𝕜 x' ((adjoint T) (y : F))) := by rw [hinner]
          _ ≤ |RCLike.re (inner 𝕜 x' ((adjoint T) (y : F)))| := le_abs_self _
          _ ≤ ‖inner 𝕜 x' ((adjoint T) (y : F))‖ := RCLike.abs_re_le_norm _
          _ ≤ ‖x'‖ * ‖(adjoint T) (y : F)‖ := norm_inner_le_norm _ _
          _ ≤ ((C : ℝ) * ‖(y : F)‖) * ‖(adjoint T) (y : F)‖ :=
              mul_le_mul_of_nonneg_right hanti (norm_nonneg _)
          _ = (C : ℝ) * ‖(y : F)‖ * ‖(adjoint T) (y : F)‖ := by ring
      have hpos : 0 < ‖(y : F)‖ := norm_pos_iff.mpr hy
      have h2 : ‖(y : F)‖ * ‖(y : F)‖ ≤
          ‖(y : F)‖ * ((C : ℝ) * ‖(adjoint T) (y : F)‖) := by
        calc ‖(y : F)‖ * ‖(y : F)‖ = ‖(y : F)‖ ^ 2 := (sq _).symm
          _ ≤ (C : ℝ) * ‖(y : F)‖ * ‖(adjoint T) (y : F)‖ := hnorm_sq
          _ = ‖(y : F)‖ * ((C : ℝ) * ‖(adjoint T) (y : F)‖) := by ring
      exact le_of_mul_le_mul_left h2 hpos
  set T₂ := (adjoint T).comp (Submodule.subtypeL (LinearMap.ker (adjoint T).toLinearMap)ᗮ)
    with hT₂
  have hT₂_inj : Function.Injective T₂ :=
    injective_comp_subtypeL_orthogonalComplement_ker (adjoint T)
  have hT₂_anti : ∃ K, AntilipschitzWith K T₂ := by
    refine ⟨C, AntilipschitzWith.of_le_mul_dist ?_⟩
    intro a b
    have h := hbound (a - b)
    rw [dist_eq_norm, dist_eq_norm]
    have h2 : T₂ a - T₂ b = (adjoint T) ((a : F) - (b : F)) := by
      simp [hT₂, map_sub]
    rw [h2]
    simpa [Submodule.coe_sub] using h
  have hT₂_closed : IsClosed (Set.range T₂) :=
    (T₂.isClosed_range_iff_antilipschitz_of_injective hT₂_inj).mpr hT₂_anti
  rw [range_comp_subtypeL_orthogonalComplement_ker (adjoint T),
    setRange_eq_coe_linearMap_range (adjoint T)] at hT₂_closed
  exact hT₂_closed

/-- **Closed range theorem for adjoints.** Let $E$ and $F$ be Hilbert spaces over $\mathbb{K}$,
where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, and let $T : E \to F$ be a bounded linear
operator with adjoint $T^\dagger$. Then the range of $T$ is closed in $F$ if and only if the
range of $T^\dagger$ is closed in $E$.

The reverse direction is the forward direction applied to $T^\dagger$, using
$T^{\dagger\dagger} = T$. -/
theorem isClosed_range_adjoint_iff (T : E →L[𝕜] F) :
    IsClosed (LinearMap.range T.toLinearMap : Set F) ↔
      IsClosed (LinearMap.range (adjoint T).toLinearMap : Set E) :=
  ⟨isClosed_range_adjoint_of_isClosed_range T,
   fun h => by
     have h' := isClosed_range_adjoint_of_isClosed_range (adjoint T) h
     rwa [adjoint_adjoint] at h'⟩

end ContinuousLinearMap
