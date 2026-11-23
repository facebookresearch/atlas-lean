/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.L1Norm
public import MathlibExt.Analysis.Normed.Field.IsClosestConjugate
import MathlibExt.Algebra.Polynomial.DegreeStability
import MathlibExt.Algebra.Polynomial.RootBound
import Mathlib.Analysis.Normed.Field.Approximation

/-! # Continuity of roots

Small monic coefficient perturbations of an irreducible separable polynomial
have closest corresponding roots generating the same simple extension.
Persistence of irreducibility and separability follows.

## ATLAS source correspondence

ATLAS source: atlas-lean commit `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`.

* Dense monic coefficient approximation:
  [`v1/Atlas/NumberTheoryI/code/LocalGlobal.lean` lines 232-312](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean#L232-L312).
* Perturbation stability (Krasner):
  [`v1/Atlas/NumberTheoryI/code/KrasnerLemma.lean` lines 551-603](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KrasnerLemma.lean#L551-L603).
* N234's use:
  [`v1/Atlas/NumberTheoryI/code/LocalGlobal.lean` lines 624-675](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean#L624-L675).

`exists_monic_and_natDegree_eq_and_l1Norm_sub_lt_and_map_irreducible_and_separable`
maps to, packages, and generalizes N234
[`v1/Atlas/NumberTheoryI/code/LocalGlobal.lean` lines 635-654](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean#L635-L654),
adding arbitrary epsilon by shrinking the stability radius and mapped separability from
`v1/Atlas/NumberTheoryI/code/KrasnerLemma.lean` lines 551-603.

This is only the approximation-and-stability stage: it does not supply the root-level
closest-conjugate/adjoin-equality stage used at lines 661-675.
-/

@[expose] public section

namespace Polynomial

variable {K : Type*} [Ring K] (v : AbsoluteValue K ℝ)

private lemma coeff_le_l1Norm (p : K[X]) (i : ℕ) : v (p.coeff i) ≤ p.l1Norm v := by
  by_cases hi : p.coeff i = 0
  · simp [hi, l1Norm_nonneg v p]
  · have hmem : i ∈ p.support := Polynomial.mem_support_iff.mpr hi
    have hle : v (p.coeff i) ≤ ∑ j ∈ p.support, v (p.coeff j) :=
      Finset.single_le_sum (f := fun j => v (p.coeff j)) (fun j _ => v.nonneg _) hmem
    exact hle

private lemma l1Norm_lt_add_one_of_l1Norm_sub_lt_one (f g : K[X])
    (h : l1Norm v (f - g) < 1) : l1Norm v g < l1Norm v f + 1 := by
  classical
  set fg := f - g
  calc
    l1Norm v g = g.support.sum (fun i => v (g.coeff i)) := rfl
    _ ≤ (f.support ∪ fg.support).sum (fun i => v (g.coeff i)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_union, mem_support_iff]
        rw [mem_support_iff] at hi
        by_contra hall
        push Not at hall
        have heq : g.coeff i = f.coeff i - fg.coeff i := by
          simp [fg, coeff_sub]
        rw [heq, hall.1, hall.2, sub_zero] at hi
        exact hi rfl
      · intro _ _ _
        exact v.nonneg _
    _ ≤ (f.support ∪ fg.support).sum
        (fun i => v (f.coeff i) + v (fg.coeff i)) := by
      apply Finset.sum_le_sum
      intro i _
      have heq : g.coeff i = f.coeff i - fg.coeff i := by
        simp [fg, coeff_sub]
      rw [heq]
      calc
        v (f.coeff i - fg.coeff i) = v (f.coeff i + (-fg.coeff i)) := by
          exact congrArg v (sub_eq_add_neg _ _)
        _ ≤ v (f.coeff i) + v (-fg.coeff i) := v.add_le _ _
        _ = v (f.coeff i) + v (fg.coeff i) := by rw [v.map_neg]
    _ = (f.support ∪ fg.support).sum (fun i => v (f.coeff i)) +
        (f.support ∪ fg.support).sum (fun i => v (fg.coeff i)) :=
      Finset.sum_add_distrib
    _ ≤ l1Norm v f + l1Norm v fg := by
      apply add_le_add
      · rw [l1Norm_def]
        apply (Finset.sum_subset Finset.subset_union_left _).ge
        intro i _ hni
        rw [mem_support_iff] at hni
        push Not at hni
        simp [hni]
      · rw [l1Norm_def]
        apply (Finset.sum_subset Finset.subset_union_right _).ge
        intro i _ hni
        rw [mem_support_iff] at hni
        push Not at hni
        simp [hni]
    _ < l1Norm v f + 1 := by
      dsimp [fg]
      linarith

variable {K' : Type*} [NontriviallyNormedField K']

private lemma exists_pos_root_separation (f : K'[X]) :
    let fL := f.map (algebraMap K' (AlgebraicClosure K'))
    ∃ r > 0, ∀ α α' : AlgebraicClosure K', α ∈ fL.roots → α' ∈ fL.roots →
      α ≠ α' → r ≤ spectralNorm K' (AlgebraicClosure K') (α - α') := by
  intro fL
  classical
  set s : Finset (AlgebraicClosure K') := fL.roots.toFinset with hs
  by_cases hcard : s.card ≤ 1
  · refine ⟨1, one_pos, fun α α' hα hα' hne => ?_⟩
    have hαs : α ∈ s := Multiset.mem_toFinset.mpr hα
    have hαs' : α' ∈ s := Multiset.mem_toFinset.mpr hα'
    rw [Finset.card_le_one_iff] at hcard
    exact absurd (hcard hαs hαs') hne
  · push Not at hcard
    set pairs := (s.product s).filter fun p => p.1 ≠ p.2
    have hpairs_nonempty : pairs.Nonempty := by
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
      exact ⟨(a, b), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩⟩
    set dists := pairs.image fun p => spectralNorm K' (AlgebraicClosure K') (p.1 - p.2)
    have hdists_nonempty : dists.Nonempty := hpairs_nonempty.image _
    set minDist := dists.min' hdists_nonempty
    have hminPos : 0 < minDist := by
      have hmem := Finset.min'_mem dists hdists_nonempty
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a, b⟩, hp, hpd⟩ := hmem
      rw [Finset.mem_filter] at hp
      have hab : a ≠ b := hp.2
      rw [show minDist = spectralNorm K' (AlgebraicClosure K') (a - b) from hpd.symm]
      exact spectralNorm_zero_lt (sub_ne_zero.mpr hab)
        (Algebra.IsAlgebraic.isAlgebraic _)
    refine ⟨minDist, hminPos, fun α α' hα hα' hne => ?_⟩
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨(α, α'),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Multiset.mem_toFinset.mpr hα, Multiset.mem_toFinset.mpr hα'⟩, hne⟩, rfl⟩

variable [IsUltrametricDist K'] [CompleteSpace K']

private lemma exists_delta_match_aroots (f : K'[X]) (hf : f.Monic)
    (hirr : Irreducible f) (r : ℝ) (hr : 0 < r) :
    ∃ δ > 0, ∀ g : K'[X], g.Monic →
      l1Norm (NormedField.toAbsoluteValue K') (f - g) < δ →
      ∀ β : AlgebraicClosure K', aeval β g = 0 →
        ∃ α ∈ f.aroots (AlgebraicClosure K'),
          spectralNorm K' (AlgebraicClosure K') (β - α) < r := by
  let : NormedField (AlgebraicClosure K') := spectralNorm.normedField K' _
  let : NormedAlgebra K' (AlgebraicClosure K') := spectralNorm.normedAlgebra K' _
  have : IsUltrametricDist (AlgebraicClosure K') :=
    IsUltrametricDist.of_normedAlgebra K'
  set v := NormedField.toAbsoluteValue K' with hv
  set n := f.natDegree with hn_def
  set C := l1Norm v f + 1 with hC
  have hn : 0 < n := Irreducible.natDegree_pos hirr
  have hC1 : 1 < C := by
    have h := one_le_l1Norm_of_monic v f hf
    simp only [hC]
    linarith
  have hCpos : 0 < C := by linarith
  set eta := (r / C) ^ n / ((n + 1 : Nat) : Real) with heta
  set delta := min 1 eta with hdelta
  have heta_pos : 0 < eta := by
    apply div_pos _ _
    · exact pow_pos (div_pos hr hCpos) n
    · exact_mod_cast Nat.succ_pos n
  have hdelta_pos : 0 < delta := lt_min one_pos heta_pos
  refine ⟨delta, hdelta_pos, fun g hg hclose β hβ => ?_⟩
  have hlt1 : l1Norm v (f - g) < 1 :=
    lt_of_lt_of_le hclose (min_le_left 1 eta)
  have heta_lt : l1Norm v (f - g) < eta :=
    lt_of_lt_of_le hclose (min_le_right 1 eta)
  have hdeg : f.natDegree = g.natDegree :=
    natDegree_eq_of_monic_of_l1Norm_sub_lt_one v hf hg hlt1
  have hcoeff : ∀ i : ℕ, v (f.coeff i - g.coeff i) < eta := by
    intro i
    rw [← coeff_sub]
    exact (coeff_le_l1Norm v (f - g) i).trans_lt heta_lt
  have hgC : l1Norm v g < C :=
    l1Norm_lt_add_one_of_l1Norm_sub_lt_one v f g hlt1
  set w := NormedField.toAbsoluteValue (AlgebraicClosure K') with hw
  let : AbsoluteValue.LiesOver w v := ⟨by
    ext x
    change ‖algebraMap K' (AlgebraicClosure K') x‖ = ‖x‖
    rw [NormedAlgebra.norm_eq_spectralNorm K', spectralNorm_extends]⟩
  have hβlt := aeval_lt_l1Norm_of_monic_of_aeval_eq_zero v w hg hβ
  change ‖β‖ < l1Norm v g at hβlt
  have hβC : ‖β‖ < C := hβlt.trans hgC
  have hmax : max ‖β‖ 1 < C := max_lt hβC hC1
  have hcoeffNorm : ∀ i : ℕ, ‖f.coeff i - g.coeff i‖ < eta := by
    intro i
    have hi := hcoeff i
    change ‖f.coeff i - g.coeff i‖ < eta at hi
    exact hi
  obtain ⟨α, hαmem, hαineq⟩ :=
    exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      (f := g) (g := f) heta_pos hβ hg hf hdeg hcoeffNorm
      (IsAlgClosed.splits _)
  have hgdeg : g.natDegree = n := hdeg.symm.trans hn_def.symm
  simp only [hgdeg] at hαineq
  have hbase : ((n + 1 : ℝ) * eta) = (r / C) ^ n := by
    simp only [heta]
    have hne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp
    norm_num [Nat.cast_add, Nat.cast_one]
  have hfactor : (((n + 1 : ℝ) * eta) ^ (n : ℝ)⁻¹) = r / C := by
    rw [hbase]
    exact Real.pow_rpow_inv_natCast (div_nonneg hr.le hCpos.le) (ne_of_gt hn)
  rw [hfactor] at hαineq
  have hCne : C ≠ 0 := hCpos.ne'
  have hfin : ‖β - α‖ < r := by
    calc ‖β - α‖ < (r / C) * max ‖β‖ 1 := hαineq
        _ < (r / C) * C :=
          mul_lt_mul_of_pos_left hmax (div_pos hr hCpos)
        _ = r := by field_simp
  refine ⟨α, hαmem, ?_⟩
  have hspec := NormedAlgebra.norm_eq_spectralNorm K' (β - α)
  rw [← hspec]
  exact hfin

/-- **Closest conjugate roots of nearby monic polynomials.** Let $K$ be a complete nontrivially
normed field whose norm is ultrametric, with algebraic closure $\overline{K}$, and let
$f \in K[X]$ be monic, irreducible and separable. Then there is a real $\delta > 0$ such that for
every monic $g \in K[X]$ with $\lVert f - g \rVert_1 < \delta$, where $\lVert \cdot \rVert_1$ is
the $\ell^1$ norm (the sum of the norms of the coefficients), and every root
$\beta \in \overline{K}$ of $g$, there is a root $\alpha \in \overline{K}$ of $f$ such that
$\alpha$ is the closest conjugate to $\beta$ and $K(\alpha) = K(\beta)$. -/
theorem exists_isClosestConjugate_root_of_l1Norm_sub_lt
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (f : K[X]) (hf : f.Monic) (hirr : Irreducible f) (hsep : f.Separable) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : K[X], g.Monic →
      l1Norm (NormedField.toAbsoluteValue K) (f - g) < δ →
      ∀ β : AlgebraicClosure K, aeval β g = 0 →
        ∃ α : AlgebraicClosure K, aeval α f = 0 ∧
          AlgebraicClosure.IsClosestConjugate K α β ∧
          IntermediateField.adjoin K {α} = IntermediateField.adjoin K {β} := by
  let : NormedField (AlgebraicClosure K) := spectralNorm.normedField K _
  let : NormedAlgebra K (AlgebraicClosure K) := spectralNorm.normedAlgebra K _
  have : IsUltrametricDist (AlgebraicClosure K) :=
    IsUltrametricDist.of_normedAlgebra K
  set fL := f.map (algebraMap K (AlgebraicClosure K)) with hfL
  have hfLmonic : fL.Monic := hf.map _
  have hfLne : fL ≠ 0 := hfLmonic.ne_zero
  obtain ⟨r, hr, hsepRoots⟩ := exists_pos_root_separation f
  obtain ⟨delta0, hdelta0, hmatch⟩ := exists_delta_match_aroots f hf hirr r hr
  refine ⟨min delta0 1, lt_min hdelta0 one_pos, fun g hg hclose β hβ => ?_⟩
  have hlt0 : l1Norm (NormedField.toAbsoluteValue K) (f - g) < delta0 :=
    lt_of_lt_of_le hclose (min_le_left _ _)
  have hlt1 : l1Norm (NormedField.toAbsoluteValue K) (f - g) < 1 :=
    lt_of_lt_of_le hclose (min_le_right _ _)
  have hdeg : f.natDegree = g.natDegree :=
    natDegree_eq_of_monic_of_l1Norm_sub_lt_one _ hf hg hlt1
  obtain ⟨α, hαmem, hαclose⟩ := hmatch g hg hlt0 β hβ
  have hαroot : aeval α f = 0 := (Polynomial.mem_aroots.mp hαmem).2
  have hαroots : α ∈ fL.roots := by
    simpa [fL] using hαmem
  have hclosest : AlgebraicClosure.IsClosestConjugate K α β := by
    intro σ hσne
    have hσαroots : σ α ∈ fL.roots := by
      rw [Polynomial.mem_roots hfLne, Polynomial.IsRoot, hfL,
          Polynomial.eval_map, ← Polynomial.aeval_def]
      have h := Polynomial.aeval_algEquiv σ α
      have heval : Polynomial.aeval (σ α) f = σ (Polynomial.aeval α f) := by
        rw [h]
        rfl
      rw [heval, hαroot, map_zero]
    have hne : α ≠ σ α := fun h => hσne h.symm
    have hle := hsepRoots α (σ α) hαroots hσαroots hne
    have hlt : spectralNorm K (AlgebraicClosure K) (β - α) < r := hαclose
    have hlt2 : spectralNorm K (AlgebraicClosure K) (β - α) <
        spectralNorm K (AlgebraicClosure K) (α - σ α) :=
      lt_of_lt_of_le hlt hle
    have hltNorm : ‖β - α‖ < ‖α - σ α‖ := by
      simpa only [NormedAlgebra.norm_eq_spectralNorm K] using hlt2
    rw [← NormedAlgebra.norm_eq_spectralNorm K (β - α),
      ← NormedAlgebra.norm_eq_spectralNorm K (β - σ α)]
    have heq : β - σ α = (β - α) + (α - σ α) := by abel
    have hmax := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (ne_of_lt hltNorm)
    rw [heq, hmax, max_eq_right (le_of_lt hltNorm)]
    exact hltNorm
  have hαint : IsIntegral K α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  have hmin_eq : minpoly K α = f := by
    have hmin_dvd : minpoly K α ∣ f := minpoly.dvd K α hαroot
    exact Polynomial.eq_of_monic_of_associated (minpoly.monic hαint) hf
      ((minpoly.irreducible hαint).associated_of_dvd hirr hmin_dvd)
  have hαsep : IsSeparable K α := by
    unfold IsSeparable
    rw [hmin_eq]
    exact hsep
  have hle : IntermediateField.adjoin K {α} ≤
      IntermediateField.adjoin K {β} := hclosest.adjoin_le hαsep
  have hβint : IsIntegral K β := (Algebra.IsAlgebraic.isAlgebraic β).isIntegral
  have hrankα : Module.finrank K (IntermediateField.adjoin K {α}) = f.natDegree := by
    rw [IntermediateField.adjoin.finrank hαint, hmin_eq]
  have hrankβ_le : Module.finrank K (IntermediateField.adjoin K {β}) ≤ f.natDegree := by
    rw [IntermediateField.adjoin.finrank hβint]
    calc
      (minpoly K β).natDegree ≤ g.natDegree :=
        Polynomial.natDegree_le_of_dvd (minpoly.dvd K β hβ) hg.ne_zero
      _ = f.natDegree := hdeg.symm
  have : FiniteDimensional K (IntermediateField.adjoin K {β}) :=
    IntermediateField.adjoin.finiteDimensional hβint
  have heq := IntermediateField.eq_of_le_of_finrank_le hle (by
    rw [hrankα]
    exact hrankβ_le)
  exact ⟨α, hαroot, hclosest, heq⟩

/-- **Small monic perturbations stay irreducible and separable.** Let $K$ be a complete
nontrivially normed field whose norm is ultrametric, and let $f \in K[X]$ be monic, irreducible
and separable. Then there is a real $\delta > 0$ such that every monic $g \in K[X]$ with
$\lVert f - g \rVert_1 < \delta$, where $\lVert \cdot \rVert_1$ is the $\ell^1$ norm (the sum of
the norms of the coefficients), is irreducible and separable. -/
theorem exists_pos_irreducible_and_separable_of_l1Norm_sub_lt
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (f : K[X]) (hf : f.Monic) (hirr : Irreducible f) (hsep : f.Separable) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : K[X], g.Monic →
      l1Norm (NormedField.toAbsoluteValue K) (f - g) < δ →
      Irreducible g ∧ g.Separable := by
  obtain ⟨delta0, hdelta0, hmain⟩ :=
    exists_isClosestConjugate_root_of_l1Norm_sub_lt K f hf hirr hsep
  refine ⟨min delta0 1, lt_min hdelta0 one_pos, fun g hg hclose => ?_⟩
  have hlt0 : l1Norm (NormedField.toAbsoluteValue K) (f - g) < delta0 :=
    lt_of_lt_of_le hclose (min_le_left _ _)
  have hlt1 : l1Norm (NormedField.toAbsoluteValue K) (f - g) < 1 :=
    lt_of_lt_of_le hclose (min_le_right _ _)
  have hdeg : f.natDegree = g.natDegree :=
    natDegree_eq_of_monic_of_l1Norm_sub_lt_one _ hf hg hlt1
  have hpos : 0 < f.natDegree := Irreducible.natDegree_pos hirr
  have hgpos : 0 < g.natDegree := hdeg ▸ hpos
  have hg_degree_ne : g.degree ≠ 0 :=
    ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hgpos)
  obtain ⟨β, hβ⟩ :=
    IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) g hg_degree_ne
  obtain ⟨α, hαroot, _, hadjoin⟩ := hmain g hg hlt0 β hβ
  have hαint : IsIntegral K α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  have hβint : IsIntegral K β := (Algebra.IsAlgebraic.isAlgebraic β).isIntegral
  have hminα : minpoly K α = f := by
    have hmin_dvd : minpoly K α ∣ f := minpoly.dvd K α hαroot
    exact Polynomial.eq_of_monic_of_associated (minpoly.monic hαint) hf
      ((minpoly.irreducible hαint).associated_of_dvd hirr hmin_dvd)
  have hrankα : Module.finrank K (IntermediateField.adjoin K {α}) = f.natDegree := by
    rw [IntermediateField.adjoin.finrank hαint, hminα]
  have hrankβ : Module.finrank K (IntermediateField.adjoin K {β}) = f.natDegree := by
    rw [← hadjoin]
    exact hrankα
  have hminβdeg : (minpoly K β).natDegree = g.natDegree := by
    have hfr : Module.finrank K (IntermediateField.adjoin K {β}) =
        (minpoly K β).natDegree := IntermediateField.adjoin.finrank hβint
    rw [← hfr, hrankβ, hdeg]
  have hming : minpoly K β ∣ g := minpoly.dvd K β hβ
  have hg_eq_min : g = minpoly K β := by
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβint) hg
      hming (le_of_eq hminβdeg.symm)
  constructor
  · rw [hg_eq_min]
    exact minpoly.irreducible hβint
  · rw [hg_eq_min]
    have hαsep : IsSeparable K α := by
      unfold IsSeparable
      rw [hminα]
      exact hsep
    have : Algebra.IsSeparable K (IntermediateField.adjoin K {α}) :=
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K
        (AlgebraicClosure K)).mpr hαsep
    have : Algebra.IsSeparable K (IntermediateField.adjoin K {β}) :=
      hadjoin ▸ ‹Algebra.IsSeparable K (IntermediateField.adjoin K {α})›
    exact (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K
      (AlgebraicClosure K)).mp
        ‹Algebra.IsSeparable K (IntermediateField.adjoin K {β})›

/-- **Approximation by irreducible separable polynomials over a dense field.** Let $K$ be a field
and $L$ a complete nontrivially normed field whose norm is ultrametric, with a $K$-algebra
structure such that the image of $K$ in $L$ is dense. Let $f \in L[X]$ be monic, irreducible and
separable, and let $\varepsilon > 0$ be real. Then there is a monic $g \in K[X]$ with
$\deg g = \deg f$ such that, writing $\bar g \in L[X]$ for the image of $g$,
$\lVert f - \bar g \rVert_1 < \varepsilon$, where $\lVert \cdot \rVert_1$ is the $\ell^1$ norm
(the sum of the norms of the coefficients), and $\bar g$ is irreducible and separable in
$L[X]$. -/
theorem exists_monic_and_natDegree_eq_and_l1Norm_sub_lt_and_map_irreducible_and_separable
    {K L : Type*} [Field K] [NontriviallyNormedField L]
    [IsUltrametricDist L] [CompleteSpace L] [Algebra K L]
    (hdense : DenseRange (algebraMap K L))
    (f : L[X]) (hf : f.Monic) (hirr : Irreducible f) (hsep : f.Separable)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : K[X], g.Monic ∧ g.natDegree = f.natDegree ∧
      l1Norm (NormedField.toAbsoluteValue L)
        (f - g.map (algebraMap K L)) < ε ∧
      Irreducible (g.map (algebraMap K L)) ∧
      (g.map (algebraMap K L)).Separable := by
  obtain ⟨δ, hδ, hstable⟩ :=
    exists_pos_irreducible_and_separable_of_l1Norm_sub_lt L f hf hirr hsep
  let η := min ε δ / (f.natDegree + 1 : ℕ)
  have hη : 0 < η := div_pos (lt_min hε hδ) (by positivity)
  obtain ⟨g, hg, hdeg, hcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
      hdense hf hη
  let q := f - g.map (algebraMap K L)
  have hqdeg : q.natDegree ≤ f.natDegree := by
    dsimp [q]
    calc
      (f - g.map (algebraMap K L)).natDegree ≤
          max f.natDegree (g.map (algebraMap K L)).natDegree :=
        natDegree_sub_le _ _
      _ = f.natDegree := by
        rw [natDegree_map, ← hdeg, max_self]
  have hsupp : q.support ⊆ Finset.range (f.natDegree + 1) :=
    supp_subset_range (Nat.lt_succ_of_le hqdeg)
  have hsum :
      ∑ i ∈ q.support, (NormedField.toAbsoluteValue L) (q.coeff i) =
        ∑ i ∈ Finset.range (f.natDegree + 1),
          (NormedField.toAbsoluteValue L) (q.coeff i) := by
    apply Finset.sum_subset hsupp
    intro i _ hi
    rw [mem_support_iff, not_not] at hi
    simp [hi]
  have hclose :
      l1Norm (NormedField.toAbsoluteValue L) q < min ε δ := by
    rw [l1Norm_def, hsum]
    calc
      ∑ i ∈ Finset.range (f.natDegree + 1),
          (NormedField.toAbsoluteValue L) (q.coeff i) <
          ∑ _i ∈ Finset.range (f.natDegree + 1), η := by
        apply Finset.sum_lt_sum_of_nonempty
        · exact Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _)
        · intro i _
          change ‖q.coeff i‖ < η
          dsimp [q]
          rw [coeff_sub, norm_sub_rev]
          exact hcoeff i
      _ = min ε δ := by
        rw [Finset.sum_const, Finset.card_range]
        simp only [nsmul_eq_mul]
        dsimp [η]
        field_simp
  obtain ⟨hmapirr, hmapsep⟩ :=
    hstable _ (hg.map _) (hclose.trans_le (min_le_right _ _))
  exact
    ⟨g, hg, hdeg.symm, hclose.trans_le (min_le_left _ _),
      hmapirr, hmapsep⟩

end Polynomial
