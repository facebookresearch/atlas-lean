/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Measure.Basic
public import MathlibExt.Probability.Statistics.PCA

import Mathlib.Tactic.Module

/-!
# EIGENSTRAT: correcting association tests for population stratification

Price et al. (2006) correct a genome-wide association study for population stratification by
computing the top `K` axes of variation of the genotype matrix (Patterson, Price and Reich 2006),
regressing the phenotype and every SNP on those axes, and testing association between the
residuals. This file formalizes the linear algebra of that procedure for `N` individuals, with
vectors in `ℝ^N` (`EuclideanSpace ℝ (Fin N)`):

* Patterson's normalization of the `N × M` genotype matrix `C` (variant-allele counts),
  `(Cᵢⱼ - μⱼ) / √(p̂ⱼ (1 - p̂ⱼ))` with `p̂ⱼ = μⱼ / 2`, the `N × N` matrix
  `Ψ = (normalized C)(normalized C)ᵀ / M`, its ordered eigenvectors (the axes of variation),
  and the span of the top `K` axes.
* Residualization on any subspace `V` (in EIGENSTRAT, the span of the top `K` axes):
  `adjusted V y = y - P_V y`. Residuals are orthogonal to `V`; on an orthonormal family of axes
  the joint regression equals the axis-by-axis regression `y - ∑ₖ ⟪aₖ, y⟫ aₖ` of Price et al.;
  the Frisch–Waugh–Lovell theorem identifies the SNP coefficient of the joint regression of `y`
  on `V` and the SNP `g` with the coefficient of the residual-on-residual regression.
* Adjusting removes stratification in the axis span: adding any vector of `V` to the phenotype
  or to the genotype leaves the residuals, and hence the EIGENSTRAT statistic
  `(N - K - 1) · corr(r_g, r_y)²`, unchanged; only the component of stratification outside `V`
  survives.
* The number of significant axes (Patterson et al. 2006): the sequential rule that counts the
  leading eigenvalue statistics above a threshold, and its type-I error bound conditional on the
  Tracy–Widom approximation for the null law of the statistic, taken as a hypothesis (the limit
  law itself is `WantedExt.Probability.TracyWidomWanted`).

The statistic is written with the uncentered cosine of the residuals; it equals the squared
sample correlation used by Price et al. when the residuals have mean zero (for example when the
all-ones vector lies in `V`, or the phenotype and genotypes are centered and `V ⊥ 1`). This file
does not formalize the asymptotic `χ²₁` null distribution of the statistic.

## Main results

* `adjusted_mem_orthogonal`, `adjusted_span_orthonormal` : residualization.
* `frischWaughLovell`, `exists_frischWaughLovell` : the Frisch–Waugh–Lovell theorem.
* `adjusted_add_of_mem`, `chiSq_add_of_mem` : stratification in the axis span is removed.
* `chiSq_nonneg`, `chiSq_le` : `0 ≤ χ² ≤ N - K - 1`.
* `relatednessMatrix_posSemidef`, `relatednessMatrix_mulVec_one`, `finrank_topAxesSpan` :
  Patterson's matrix and its axes.
* `lt_numSignificant_iff`, `measure_lt_numSignificant_le` : the significance count and its
  conditional error bound.

## References

* A. L. Price, N. J. Patterson, R. M. Plenge, M. E. Weinblatt, N. A. Shadick and D. Reich,
  "Principal components analysis corrects for stratification in genome-wide association
  studies", Nat. Genet. 38 (2006), 904–909.
* N. Patterson, A. L. Price and D. Reich, "Population structure and eigenanalysis", PLoS Genet.
  2 (2006), e190.
* R. Frisch and F. V. Waugh, "Partial time regressions as compared with individual trends",
  Econometrica 1 (1933), 387–401; M. C. Lovell, "Seasonal adjustment of economic time series and
  multiple regression analysis", J. Amer. Statist. Assoc. 58 (1963), 993–1010.
-/

@[expose] public section

namespace MathlibExt.Biology.StatisticalGenetics.Eigenstrat

open scoped InnerProductSpace

/-! ### Residualization on a span of axes -/

section Residual

variable {N : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin N)

/-- The adjusted (residualized) `y`: the residual of the least-squares regression of `y` on the
subspace `V` (`y` minus its orthogonal projection onto `V`). -/
noncomputable def adjusted (V : Submodule ℝ E) (y : E) : E :=
  y - V.starProjection y

/-- Residuals are orthogonal to the adjustment subspace. -/
theorem adjusted_mem_orthogonal (V : Submodule ℝ E) (y : E) : adjusted V y ∈ Vᗮ := by
  exact V.sub_starProjection_mem_orthogonal y

/-- Residuals are orthogonal to every vector of the subspace, in particular to every axis. -/
theorem inner_adjusted_eq_zero (V : Submodule ℝ E) {v : E} (hv : v ∈ V) (y : E) :
    ⟪v, adjusted V y⟫_ℝ = 0 := by
  exact Submodule.inner_right_of_mem_orthogonal hv (adjusted_mem_orthogonal V y)

/-- The residual is the orthogonal projection onto `Vᗮ`. -/
theorem adjusted_eq_starProjection_orthogonal (V : Submodule ℝ E) (y : E) :
    adjusted V y = Vᗮ.starProjection y := by
  exact (Submodule.starProjection_orthogonal_val y).symm

/-- Residualization is additive. -/
theorem adjusted_add (V : Submodule ℝ E) (y z : E) :
    adjusted V (y + z) = adjusted V y + adjusted V z := by
  simp only [adjusted_eq_starProjection_orthogonal, map_add]

/-- Residualization is homogeneous. -/
theorem adjusted_smul (V : Submodule ℝ E) (c : ℝ) (y : E) :
    adjusted V (c • y) = c • adjusted V y := by
  simp only [adjusted_eq_starProjection_orthogonal, map_smul]

/-- The residual vanishes exactly on the subspace. -/
theorem adjusted_eq_zero_iff (V : Submodule ℝ E) (y : E) : adjusted V y = 0 ↔ y ∈ V := by
  rw [adjusted, sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]

/-- Adding a vector of the subspace (stratification lying in the axis span) does not change the
residual. -/
theorem adjusted_add_of_mem (V : Submodule ℝ E) {s : E} (hs : s ∈ V) (z : E) :
    adjusted V (s + z) = adjusted V z := by
  rw [adjusted_add, (adjusted_eq_zero_iff V s).mpr hs, zero_add]

/-- Vectors orthogonal to the subspace are their own residuals: stratification outside the axis
span is not removed. -/
theorem adjusted_of_mem_orthogonal (V : Submodule ℝ E) {y : E} (hy : y ∈ Vᗮ) :
    adjusted V y = y := by
  rw [adjusted_eq_starProjection_orthogonal, Submodule.starProjection_eq_self_iff]
  exact hy

/-- Regressing on an orthonormal family of axes one axis at a time gives the joint residual:
`y - ∑ₖ ⟪aₖ, y⟫ aₖ`. -/
theorem adjusted_span_orthonormal {K : ℕ} (a : Fin K → E) (ha : Orthonormal ℝ a) (y : E) :
    adjusted (Submodule.span ℝ (Set.range a)) y = y - ∑ k, ⟪a k, y⟫_ℝ • a k := by
  classical
  let S := Submodule.span ℝ (Set.range a)
  have hs : (∑ k, ⟪a k, y⟫_ℝ • a k) ∈ S := by
    exact Submodule.sum_mem S fun k _ =>
      S.smul_mem _ (Submodule.subset_span (Set.mem_range_self k))
  have ho : y - ∑ k, ⟪a k, y⟫_ℝ • a k ∈ Sᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [inner_sub_right, ha.inner_right_fintype]
      exact sub_self _
    | zero => simp
    | add x z hx hz hix hiz => simp [inner_add_left, hix, hiz]
    | smul r x hx hix => simp [inner_smul_left, hix]
  exact congrArg (y - ·) (S.eq_starProjection_of_mem_orthogonal hs ho)

/-- Frisch–Waugh–Lovell, uniqueness: in any least-squares decomposition
`y = c + β g + e` with `c ∈ V` and `e ⊥ V ⊔ span {g}`, the coefficient `β` is the
coefficient of the regression of the residualized `y` on the residualized `g`, and the
residual `e` is the residual of that regression. -/
theorem frischWaughLovell (V : Submodule ℝ E) (y g : E) (hg : adjusted V g ≠ 0) {c : E}
    (hc : c ∈ V) (β : ℝ) (he : y - c - β • g ∈ (V ⊔ Submodule.span ℝ {g})ᗮ) :
    β = ⟪adjusted V g, adjusted V y⟫_ℝ / ‖adjusted V g‖ ^ 2 ∧
      y - c - β • g = adjusted V y - β • adjusted V g := by
  have heV : y - c - β • g ∈ Vᗮ := Submodule.orthogonal_le le_sup_left he
  have hfixed : adjusted V (y - c - β • g) = y - c - β • g := by
    unfold adjusted
    rw [← V.starProjection_orthogonal_val, Vᗮ.starProjection_eq_self_iff.mpr heV]
  have hr : y - c - β • g = adjusted V y - β • adjusted V g := by
    rw [← hfixed]
    simp only [adjusted, map_sub, map_smul, V.starProjection_eq_self_iff.mpr hc]
    module
  have hi : ⟪adjusted V g, y - c - β • g⟫_ℝ = 0 := by
    rw [adjusted, inner_sub_left,
      V.inner_right_of_mem_orthogonal (V.starProjection_apply_mem g) heV, sub_zero]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp
      (Submodule.orthogonal_le le_sup_right he)
  have hcoef : ⟪adjusted V g, adjusted V y⟫_ℝ - β * ‖adjusted V g‖ ^ 2 = 0 := by
    rw [hr, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at hi
    exact hi
  have hn : ‖adjusted V g‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hg)
  refine ⟨?_, hr⟩
  apply (eq_div_iff hn).mpr
  linarith

/-- Frisch–Waugh–Lovell, existence: the coefficient of the residual-on-residual regression
gives a least-squares decomposition of `y` on `V ⊔ span {g}`. -/
theorem exists_frischWaughLovell (V : Submodule ℝ E) (y g : E) :
    ∃ c ∈ V, y - c - (⟪adjusted V g, adjusted V y⟫_ℝ / ‖adjusted V g‖ ^ 2) • g ∈
      (V ⊔ Submodule.span ℝ {g})ᗮ := by
  let β := ⟪adjusted V g, adjusted V y⟫_ℝ / ‖adjusted V g‖ ^ 2
  let c := V.starProjection (y - β • g)
  have hr : y - c - β • g = adjusted V y - β • adjusted V g := by
    dsimp [c, adjusted]
    simp only [map_sub, map_smul]
    module
  have heV : y - c - β • g ∈ Vᗮ := by
    convert V.sub_starProjection_mem_orthogonal (y - β • g) using 1
    dsimp [c]
    abel
  have hi : ⟪adjusted V g, adjusted V y - β • adjusted V g⟫_ℝ = 0 := by
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    by_cases hz : adjusted V g = 0
    · simp [β, hz]
    · have hn : ‖adjusted V g‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
      dsimp [β]
      rw [div_mul_cancel₀ _ hn, sub_self]
  have hig : ⟪g, y - c - β • g⟫_ℝ = 0 := by
    calc
      ⟪g, y - c - β • g⟫_ℝ =
          ⟪adjusted V g + V.starProjection g, y - c - β • g⟫_ℝ := by
        congr 1
        exact (sub_add_cancel g (V.starProjection g)).symm
      _ = 0 := by
        rw [inner_add_left,
          V.inner_right_of_mem_orthogonal (V.starProjection_apply_mem g) heV,
          add_zero, hr]
        exact hi
  refine ⟨c, V.starProjection_apply_mem _, ?_⟩
  change y - c - β • g ∈ (V ⊔ Submodule.span ℝ {g})ᗮ
  rw [← Submodule.inf_orthogonal]
  exact ⟨heV, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hig⟩

/-- The EIGENSTRAT association statistic `(N - K - 1) ⟪r_g, r_y⟫² / (‖r_g‖² ‖r_y‖²)` of the
adjusted genotype `r_g` and adjusted phenotype `r_y`: `(N - K - 1)` times their squared cosine,
which is their squared sample correlation when both are centered (Price et al. 2006). When either
adjusted vector is zero the ratio is the junk value `0`. -/
noncomputable def chiSq (V : Submodule ℝ E) (K : ℕ) (y g : E) : ℝ :=
  ((N : ℝ) - K - 1) * (⟪adjusted V g, adjusted V y⟫_ℝ ^ 2 /
    (‖adjusted V g‖ ^ 2 * ‖adjusted V y‖ ^ 2))

/-- **Stratification in the axis span is removed.** Adding vectors of `V` to the phenotype and
the genotype does not change the EIGENSTRAT statistic. -/
theorem chiSq_add_of_mem (V : Submodule ℝ E) (K : ℕ) {s t : E} (hs : s ∈ V) (ht : t ∈ V)
    (y g : E) : chiSq V K (s + y) (t + g) = chiSq V K y g := by
  simp only [chiSq, adjusted_add_of_mem V hs, adjusted_add_of_mem V ht]

/-- The EIGENSTRAT statistic is nonnegative when `K + 1 ≤ N`. -/
theorem chiSq_nonneg (V : Submodule ℝ E) {K : ℕ} (hK : K + 1 ≤ N) (y g : E) :
    0 ≤ chiSq V K y g := by
  have hK' : (0 : ℝ) ≤ (N : ℝ) - K - 1 := by
    have : ((K + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hK
    push_cast at this
    linarith
  unfold chiSq
  positivity

theorem chiSq_le (V : Submodule ℝ E) {K : ℕ} (hK : K + 1 ≤ N) (y g : E) :
    chiSq V K y g ≤ (N : ℝ) - K - 1 := by
  have hfactor : 0 ≤ (N : ℝ) - K - 1 := by
    have hcast : (K : ℝ) + 1 ≤ N := by exact_mod_cast hK
    linarith
  have hcs : ⟪adjusted V g, adjusted V y⟫_ℝ ^ 2 ≤
      ‖adjusted V g‖ ^ 2 * ‖adjusted V y‖ ^ 2 := by
    simpa only [pow_two, real_inner_self_eq_norm_sq] using
      real_inner_mul_inner_self_le (adjusted V g) (adjusted V y)
  exact mul_le_of_le_one_right hfactor (div_le_one_of_le₀ hcs (by positivity))

/-- A genotype lying in the axis span carries no signal after adjustment (its residual is zero,
and the statistic is the junk value `0` of the zero denominator). -/
theorem chiSq_of_mem (V : Submodule ℝ E) (K : ℕ) (y : E) {g : E} (hg : g ∈ V) :
    chiSq V K y g = 0 := by
  simp [chiSq, (adjusted_eq_zero_iff V g).mpr hg]

end Residual

/-! ### Patterson normalization and the axes of variation -/

section Patterson

open Matrix MathlibExt.Probability.Statistics.PCA

variable {N M : ℕ}

/-- The allele-frequency estimate `p̂ⱼ = μⱼ / 2` of marker `j`, where `μⱼ` is the mean
variant-allele count of column `j` (autosomal diploid data, counts in `{0, 1, 2}`). -/
noncomputable def alleleFreq (C : Matrix (Fin N) (Fin M) ℝ) (j : Fin M) : ℝ :=
  colMean C j / 2

/-- Patterson's normalized genotype matrix `(C i j - μⱼ) / √(p̂ⱼ (1 - p̂ⱼ))`. For a
monomorphic marker (`p̂ⱼ ∈ {0, 1}`) the denominator is `0` and the column is the junk value `0`;
Patterson et al. use polymorphic markers only. -/
noncomputable def normalizedGenotype (C : Matrix (Fin N) (Fin M) ℝ) : Matrix (Fin N) (Fin M) ℝ :=
  Matrix.of fun i j => center C i j / √(alleleFreq C j * (1 - alleleFreq C j))

/-- Patterson's `N × N` matrix `Ψ = M Mᵀ / (number of markers)` of the normalized genotypes,
whose top eigenvectors are the axes of variation. -/
noncomputable def relatednessMatrix (C : Matrix (Fin N) (Fin M) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (M : ℝ)⁻¹ • (normalizedGenotype C * (normalizedGenotype C)ᵀ)

/-- Patterson's matrix `Ψ` is positive semidefinite. -/
theorem relatednessMatrix_posSemidef (C : Matrix (Fin N) (Fin M) ℝ) :
    (relatednessMatrix C).PosSemidef := by
  unfold relatednessMatrix
  have h := Matrix.posSemidef_self_mul_conjTranspose (normalizedGenotype C)
  rw [conjTranspose_eq_transpose_of_trivial] at h
  exact h.smul (inv_nonneg.mpr (Nat.cast_nonneg M))

/-- The all-ones vector is in the kernel of `Ψ` (columns of the normalized matrix are centered),
so at most `N - 1` eigenvalues are nonzero. -/
theorem relatednessMatrix_mulVec_one (C : Matrix (Fin N) (Fin M) ℝ) (hN : 0 < N) :
    relatednessMatrix C *ᵥ 1 = 0 := by
  have h : (normalizedGenotype C)ᵀ *ᵥ (1 : Fin N → ℝ) = 0 := by
    ext j
    simp only [mulVec, dotProduct, transpose_apply, normalizedGenotype, of_apply, Pi.one_apply,
      mul_one, Pi.zero_apply, ← Finset.sum_div, sum_center C hN j, zero_div]
  rw [relatednessMatrix, smul_mulVec, ← mulVec_mulVec, h, mulVec_zero, smul_zero]

/-- The axes of variation: an orthonormal eigenbasis of `Ψ`, in decreasing eigenvalue order. -/
noncomputable def axes (C : Matrix (Fin N) (Fin M) ℝ) :
    OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)) :=
  orderedEigenbasis (relatednessMatrix_posSemidef C).isHermitian

/-- The eigenvalues of `Ψ` in decreasing order, matching `axes`. -/
noncomputable def axisEigenvalues (C : Matrix (Fin N) (Fin M) ℝ) : Fin N → ℝ :=
  orderedEigenvalues (relatednessMatrix_posSemidef C).isHermitian

/-- The span of the top `K` axes of variation, the subspace EIGENSTRAT adjusts for. -/
noncomputable def topAxesSpan (C : Matrix (Fin N) (Fin M) ℝ) (K : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
  Submodule.span ℝ (axes C '' {i | i.val < K})

/-- Each of the top `K` axes lies in their span. -/
theorem axes_mem_topAxesSpan (C : Matrix (Fin N) (Fin M) ℝ) {K : ℕ} {i : Fin N} (hi : i.val < K) :
    axes C i ∈ topAxesSpan C K :=
  Submodule.subset_span ⟨i, hi, rfl⟩

/-- The top `K` axes span a `K`-dimensional subspace. -/
theorem finrank_topAxesSpan (C : Matrix (Fin N) (Fin M) ℝ) {K : ℕ} (hK : K ≤ N) :
    Module.finrank ℝ (topAxesSpan C K) = K := by
  have hli : LinearIndependent ℝ (fun i : {i : Fin N // i.val < K} => axes C i.1) :=
    (axes C).orthonormal.linearIndependent.comp _ Subtype.val_injective
  have hrange : axes C '' {i | i.val < K} =
      Set.range fun i : {i : Fin N // i.val < K} => axes C i.1 := by
    ext x
    simp
  rw [topAxesSpan, hrange, finrank_span_eq_card hli, Fintype.card_subtype]
  have : (Finset.univ.filter fun i : Fin N => i.val < K) =
      Finset.univ.map ⟨Fin.castLE hK, Fin.castLE_injective hK⟩ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hi
      exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    · rintro ⟨j, rfl⟩
      simp
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]

end Patterson

/-! ### Number of significant axes -/

section Significance

open MeasureTheory

/-- Patterson's sequential count of significant axes: among the first `K` statistics, the
length of the leading run of statistics exceeding the threshold `t` (testing stops at the first
non-significant one). -/
noncomputable def numSignificant (stat : ℕ → ℝ) (t : ℝ) : ℕ → ℕ
  | 0 => 0
  | K + 1 => open Classical in
      if numSignificant stat t K = K ∧ t < stat K then K + 1 else numSignificant stat t K

/-- At most `K` axes are declared significant. -/
theorem numSignificant_le (stat : ℕ → ℝ) (t : ℝ) (K : ℕ) : numSignificant stat t K ≤ K := by
  induction K with
  | zero => simp [numSignificant]
  | succ K ih =>
    simp only [numSignificant]
    split_ifs <;> omega

/-- The first `numSignificant stat t K` indices are exactly those `k < K` whose statistics and
all earlier ones exceed the threshold. -/
theorem lt_numSignificant_iff {stat : ℕ → ℝ} {t : ℝ} {K k : ℕ} :
    k < numSignificant stat t K ↔ k < K ∧ ∀ i ≤ k, t < stat i := by
  induction K generalizing k with
  | zero => simp [numSignificant]
  | succ K ih =>
    have hle := numSignificant_le stat t K
    simp only [numSignificant]
    split_ifs with hc
    · refine ⟨fun hk => ⟨hk, fun i hi => ?_⟩, fun h => h.1⟩
      rcases Nat.lt_or_ge i K with hiK | hiK
      · exact (ih.mp (by rw [hc.1]; exact hiK)).2 i le_rfl
      · have : i = K := by omega
        exact this ▸ hc.2
    · refine ⟨fun hk => ⟨by omega, (ih.mp hk).2⟩, fun ⟨hk, hall⟩ => ?_⟩
      rcases Nat.lt_or_ge k K with hkK | hkK
      · exact ih.mpr ⟨hkK, hall⟩
      · exfalso
        have hkK' : k = K := by omega
        subst hkK'
        have hn : numSignificant stat t k = k := by
          by_contra hne
          have hlt : numSignificant stat t k < k := lt_of_le_of_ne hle hne
          exact lt_irrefl _ (ih.mpr ⟨hlt, fun i hi => hall i (by omega)⟩)
        exact hc ⟨hn, hall k le_rfl⟩

/-- Every axis counted as significant has a statistic above the threshold. -/
theorem lt_stat_of_lt_numSignificant {stat : ℕ → ℝ} {t : ℝ} {K k : ℕ}
    (h : k < numSignificant stat t K) : t < stat k :=
  (lt_numSignificant_iff.mp h).2 k le_rfl

/-- At least one axis is significant iff the leading statistic exceeds the threshold. -/
theorem numSignificant_pos_iff {stat : ℕ → ℝ} {t : ℝ} {K : ℕ} :
    0 < numSignificant stat t K ↔ 0 < K ∧ t < stat 0 := by
  rw [lt_numSignificant_iff]
  simp

/-- A higher threshold declares no more axes significant. -/
theorem numSignificant_antitone {stat : ℕ → ℝ} {t t' : ℝ} (htt : t ≤ t') (K : ℕ) :
    numSignificant stat t' K ≤ numSignificant stat t K := by
  by_contra h
  rw [not_le] at h
  have h' := lt_numSignificant_iff.mp h
  exact lt_irrefl _ (lt_numSignificant_iff.mpr ⟨h'.1, fun i hi => htt.trans_lt (h'.2 i hi)⟩)

/-- For decreasing statistics (such as ordered eigenvalues compared with a fixed threshold) the
sequential count is the number of statistics above the threshold. -/
theorem numSignificant_eq_card_of_antitone {stat : ℕ → ℝ} (h : Antitone stat) (t : ℝ) (K : ℕ) :
    numSignificant stat t K = ((Finset.range K).filter fun k => t < stat k).card := by
  have hset : ((Finset.range K).filter fun k => t < stat k) =
      Finset.range (numSignificant stat t K) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, lt_numSignificant_iff]
    exact ⟨fun hk => ⟨hk.1, fun i hi => hk.2.trans_le (h hi)⟩,
      fun hk => ⟨hk.1, hk.2 k le_rfl⟩⟩
  rw [hset, Finset.card_range]

/-- **Conditional error bound.** If, under the null hypothesis, the `k`-th statistic exceeds `t`
with probability at most `1 - F t` (the Tracy–Widom approximation with `F` the TW₁ distribution
function, taken here as a hypothesis), then the rule declares more than `k` significant axes with
probability at most `1 - F t`. -/
theorem measure_lt_numSignificant_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (stat : Ω → ℕ → ℝ) (F : ℝ → ℝ) (t : ℝ) (K k : ℕ)
    (hnull : P {ω | t < stat ω k} ≤ ENNReal.ofReal (1 - F t)) :
    P {ω | k < numSignificant (stat ω) t K} ≤ ENNReal.ofReal (1 - F t) :=
  (measure_mono fun _ hω => lt_stat_of_lt_numSignificant hω).trans hnull

end Significance

end MathlibExt.Biology.StatisticalGenetics.Eigenstrat
