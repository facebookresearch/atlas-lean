/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The Exact Recovery Condition and the greedy selection step

Let `φ₁, …, φ_m` be the optimal atoms of a sparse representation in an inner product space,
`K = span{φᵢ}` and `P` the orthogonal projection onto `K`. For a nonoptimal atom `ψ`, the
coefficient vector `Φ⁺ψ` lists the coordinates of `Pψ` in the atoms `φᵢ`. Tropp's
**Exact Recovery Condition** (ERC) is `‖Φ⁺ψ‖₁ < 1` for every nonoptimal atom `ψ`.

The key step of the proof of the Exact Recovery Theorem for Orthogonal Matching Pursuit
(J. A. Tropp, *Greed is good: algorithmic results for sparse approximation*, IEEE Trans. Inform.
Theory 50 (2004), 2231–2242, Theorem 3.1 and its proof, the greedy selection ratio (7)) is that
for every residual `r ∈ K`,
`|⟨ψ, r⟩| ≤ ‖Φ⁺ψ‖₁ · maxᵢ |⟨φᵢ, r⟩|`. Under the ERC, a nonzero residual in `K` is therefore
strictly more correlated with some optimal atom than with any nonoptimal atom, so a greedy
selection picks an optimal atom. Since the OMP residual stays in `K` and is orthogonal to the
atoms already chosen, OMP recovers the optimal atoms in `m` steps.

Here the ERC coefficients are any `a` with `∑ aᵢ φᵢ = Pψ`; when the optimal atoms are linearly
independent (as in Tropp's setting) this `a` is unique and equals `Φ⁺ψ`.

## Main declarations

* `MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCondition.norm_inner_le_of_mem_span` :
  the bound `|⟨ψ, r⟩| ≤ ‖a‖₁ · M` whenever `|⟨φᵢ, r⟩| ≤ M` for all `i`.
* `MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCondition.exists_inner_ne_zero_of_mem_span` :
  a nonzero vector of `K` has a nonzero inner product with some atom.
* `MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCondition.norm_inner_lt_sup'_of_erc` :
  under the ERC, `|⟨ψ, r⟩| < maxᵢ |⟨φᵢ, r⟩|` for every nonzero `r ∈ K`.
* `MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCondition.sub_starProjection_mem`,
  `MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCondition.inner_sub_starProjection_eq_zero` :
  the OMP residual stays in `K` and is orthogonal to the atoms already selected.

The full OMP iteration (an algorithm with tie-breaking) is not formalized here.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCondition

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]

omit [Fintype ι] in
/-- **The span of finitely many atoms is finite-dimensional**, so the orthogonal projection onto
it exists. -/
instance finiteDimensional_span_range [Finite ι] (φ : ι → E) :
    FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range φ)) :=
  FiniteDimensional.span_of_finite 𝕜 (Set.finite_range φ)

/-- **Greedy selection bound** (Tropp, *Greed is good*, IEEE Trans. Inform. Theory 50 (2004),
proof of Theorem 3.1). Let `K` be the span of the atoms `φᵢ` and let `a` be coefficients of the
orthogonal projection of `ψ` onto `K`, `∑ aᵢ φᵢ = P_K ψ`. If `r ∈ K` and `|⟨φᵢ, r⟩| ≤ M` for
every `i`, then `|⟨ψ, r⟩| ≤ (∑ᵢ |aᵢ|) · M`. -/
theorem norm_inner_le_of_mem_span (φ : ι → E) (ψ : E) (a : ι → 𝕜)
    (ha : ∑ i, a i • φ i = (Submodule.span 𝕜 (Set.range φ)).starProjection ψ)
    {r : E} (hr : r ∈ Submodule.span 𝕜 (Set.range φ)) {M : ℝ}
    (hM : ∀ i, ‖⟪φ i, r⟫_𝕜‖ ≤ M) :
    ‖⟪ψ, r⟫_𝕜‖ ≤ (∑ i, ‖a i‖) * M := by
  set K := Submodule.span 𝕜 (Set.range φ)
  have hproj : ⟪ψ, r⟫_𝕜 = ⟪∑ i, a i • φ i, r⟫_𝕜 := by
    rw [ha, Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hr]
  rw [hproj, sum_inner, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [inner_smul_left, norm_mul, RCLike.norm_conj]
  exact mul_le_mul_of_nonneg_left (hM i) (norm_nonneg _)

omit [Fintype ι] in
/-- **A nonzero vector of the span sees some atom.** A nonzero vector in the span of the atoms
`φᵢ` has a nonzero inner product with at least one atom (used in Tropp, *Greed is good*, proof of
Theorem 3.1, to make the greedy selection ratio well defined). -/
theorem exists_inner_ne_zero_of_mem_span (φ : ι → E) {r : E}
    (hr : r ∈ Submodule.span 𝕜 (Set.range φ)) (hr0 : r ≠ 0) :
    ∃ i, ⟪φ i, r⟫_𝕜 ≠ 0 := by
  by_contra h
  push Not at h
  have horth : ∀ u ∈ Submodule.span 𝕜 (Set.range φ), ⟪u, r⟫_𝕜 = 0 := by
    intro u hu
    refine Submodule.span_induction (p := fun u _ => ⟪u, r⟫_𝕜 = 0) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨i, rfl⟩
      exact h i
    · simp
    · intro x y _ _ hx hy
      rw [inner_add_left, hx, hy, add_zero]
    · intro c x _ hx
      rw [inner_smul_left, hx, mul_zero]
  exact hr0 (inner_self_eq_zero.mp (horth r hr))

/-- **The Exact Recovery Condition forces a correct greedy choice** (Tropp, *Greed is good*,
IEEE Trans. Inform. Theory 50 (2004), Theorem 3.1, the inequality `ρ(r) < 1` for the greedy
selection ratio (7)). Let `K` be the span of the optimal atoms `φᵢ` (a nonempty family), let
`ψ` be a nonoptimal atom and `a` coefficients of `P_K ψ` with `‖a‖₁ = ∑ᵢ |aᵢ| < 1`. Then for every
nonzero residual `r ∈ K`, `|⟨ψ, r⟩| < maxᵢ |⟨φᵢ, r⟩|`. -/
theorem norm_inner_lt_sup'_of_erc [Nonempty ι] (φ : ι → E) (ψ : E) (a : ι → 𝕜)
    (ha : ∑ i, a i • φ i = (Submodule.span 𝕜 (Set.range φ)).starProjection ψ)
    (herc : ∑ i, ‖a i‖ < 1)
    {r : E} (hr : r ∈ Submodule.span 𝕜 (Set.range φ)) (hr0 : r ≠ 0) :
    ‖⟪ψ, r⟫_𝕜‖ < Finset.univ.sup' Finset.univ_nonempty (fun i => ‖⟪φ i, r⟫_𝕜‖) := by
  set M := Finset.univ.sup' Finset.univ_nonempty (fun i => ‖⟪φ i, r⟫_𝕜‖)
  have hM : ∀ i, ‖⟪φ i, r⟫_𝕜‖ ≤ M := fun i =>
    Finset.le_sup' (fun i => ‖⟪φ i, r⟫_𝕜‖) (Finset.mem_univ i)
  obtain ⟨j, hj⟩ := exists_inner_ne_zero_of_mem_span (𝕜 := 𝕜) φ hr hr0
  have hMpos : 0 < M := (norm_pos_iff.mpr hj).trans_le (hM j)
  calc ‖⟪ψ, r⟫_𝕜‖ ≤ (∑ i, ‖a i‖) * M := norm_inner_le_of_mem_span φ ψ a ha hr hM
    _ < 1 * M := mul_lt_mul_of_pos_right herc hMpos
    _ = M := one_mul M

/-- **OMP residuals stay in the optimal span** (Tropp, *Greed is good*, proof of Theorem 3.1).
If the signal `s` lies in `K` and the atoms selected so far span a subspace `L ≤ K`, then the
residual `s - P_L s` lies in `K`. -/
theorem sub_starProjection_mem {K L : Submodule 𝕜 E} [L.HasOrthogonalProjection] (hLK : L ≤ K)
    {s : E} (hs : s ∈ K) : s - L.starProjection s ∈ K :=
  K.sub_mem hs (hLK (L.starProjection_apply_mem s))

/-- **OMP never selects an atom twice** (Tropp, *Greed is good*, proof of Theorem 3.1). The
residual `s - P_L s` is orthogonal to every vector of `L`, in particular to every atom already
selected. -/
theorem inner_sub_starProjection_eq_zero (L : Submodule 𝕜 E) [L.HasOrthogonalProjection]
    (s : E) {w : E} (hw : w ∈ L) : ⟪w, s - L.starProjection s⟫_𝕜 = 0 := by
  rw [← inner_conj_symm, L.starProjection_inner_eq_zero s w hw, map_zero]

end MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCondition
