/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.FiniteCongruence
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Controlled finite approximation for N406

Weak approximation over finitely many pairwise inequivalent nontrivial absolute
values: prescribed targets at finitely many places can be simultaneously
approximated to any positive tolerance. Used for the finite-place adjustment
step in N406.

This is a supporting step for ATLAS NumberTheoryI N406, Theorem 21.8, Section 21.3,
source [`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L2255-L2568),
declaration `RayClassField.theorem_21_8_quotient_iso`; its weak-approximation
construction is in `weak_approx_coprime_sign_finitePart` (lines 2255--2568), whose finite-target,
valuation, and residue/sign arguments are mapped below. The underlying weak
approximation invocation at source line 2404 is ATLAS N175, Theorem 8.5.
This module packages the N406-specific finite-target valuation/sign consequence
rather than claiming the final N406 quotient theorem is complete.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {F : Type*} [Field F] {ι : Type*} [Finite ι]

/-- Weak approximation for finitely many inequivalent nontrivial absolute values. -/
private theorem exists_forall_abv_sub_lt (v : ι → AbsoluteValue F ℝ)
    (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j => ¬(v i).IsEquiv (v j)) (target : ι → F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : F, ∀ i, v i (x - target i) < ε := by
  classical
  let _ := Fintype.ofFinite ι
  have hdense := AbsoluteValue.denseRange_algebraMap_pi h hv
  rw [Metric.denseRange_iff] at hdense
  obtain ⟨y, hy⟩ :=
    hdense (fun i => WithAbs.toAbs (v i) (target i)) ε hε
  by_cases hempty : IsEmpty ι
  · exact ⟨y, fun i => (hempty.false i).elim⟩
  · let _ : Nonempty ι := not_isEmpty_iff.mp hempty
    rw [dist_pi_lt_iff hε] at hy
    refine ⟨y, fun i => ?_⟩
    have e1 : (algebraMap F ((i : ι) → WithAbs (v i)) y) i
        = WithAbs.toAbs (v i) y := rfl
    have hdist : dist (WithAbs.toAbs (v i) (target i))
        ((algebraMap F ((i : ι) → WithAbs (v i)) y) i) = v i (y - target i) := by
      rw [dist_comm, e1, dist_eq_norm, ← WithAbs.toAbs_sub, WithAbs.norm_toAbs_eq]
    have hi := hy i
    rw [hdist] at hi
    exact hi

/-- Weak approximation with place-dependent positive tolerances.

Reduces pointwise tolerances to a single uniform radius via the finite minimum,
so finite tolerances may genuinely depend on `finiteExponent`. -/
private theorem exists_forall_abv_sub_lt_of_eps (v : ι → AbsoluteValue F ℝ)
    (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j => ¬(v i).IsEquiv (v j)) (target : ι → F)
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ x : F, ∀ i, v i (x - target i) < ε i := by
  classical
  let _ := Fintype.ofFinite ι
  by_cases hempty : IsEmpty ι
  · exact ⟨0, fun i => (hempty.false i).elim⟩
  · have : Nonempty ι := not_isEmpty_iff.mp hempty
    let s := Finset.univ.image ε
    have hs_ne : s.Nonempty :=
      Finset.image_nonempty.mpr Finset.univ_nonempty
    set ε₀ := s.min' hs_ne
    have hε₀_mem : ε₀ ∈ s := Finset.min'_mem s hs_ne
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hε₀_mem
    have hε₀_pos : 0 < ε₀ := hj ▸ hε j
    obtain ⟨x, hx⟩ := exists_forall_abv_sub_lt v h hv target hε₀_pos
    refine ⟨x, fun i => ?_⟩
    exact lt_of_lt_of_le (hx i)
      (Finset.min'_le _ _ (Finset.mem_image_of_mem ε (Finset.mem_univ i)))

variable {K : Type*} [Field K] [NumberField K]

/-- Finite-place absolute value is nontrivial. -/
private theorem adicAbv_isNontrivial
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (HeightOneSpectrum.adicAbv K v).IsNontrivial := by
  obtain ⟨r, hrmem, hr0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hne : algebraMap (𝓞 K) K r ≠ 0 := fun h =>
    hr0 (IsFractionRing.injective (𝓞 K) K (by rw [h, RingHom.map_zero]))
  have hmem : v.adicAbv (HeightOneSpectrum.one_lt_absNorm_nnreal v)
      (algebraMap (𝓞 K) K r) < 1 :=
    (v.adicAbv_coe_lt_one_iff
      (HeightOneSpectrum.one_lt_absNorm_nnreal v) r).mpr hrmem
  exact ⟨_, hne, ne_of_lt hmem⟩

/-- Distinct finite places give inequivalent absolute values. -/
private theorem adicAbv_not_isEquiv_of_ne
    (v w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (h : v ≠ w) :
    ¬ (HeightOneSpectrum.adicAbv K v).IsEquiv
      (HeightOneSpectrum.adicAbv K w) := by
  classical
  intro heq
  have ⟨r, hrv, hrw⟩ : ∃ r : 𝓞 K, r ∈ v.asIdeal ∧ r ∉ w.asIdeal := by
    by_contra! H
    exact h (IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr
      (Ideal.IsMaximal.eq_of_le v.isMaximal Ideal.IsPrime.ne_top' H))
  have hlt : HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K r) < 1 :=
    (v.adicAbv_coe_lt_one_iff
      (HeightOneSpectrum.one_lt_absNorm_nnreal v) r).mpr hrv
  have hone : HeightOneSpectrum.adicAbv K w (algebraMap (𝓞 K) K r) = 1 :=
    (w.adicAbv_coe_eq_one_iff
      (HeightOneSpectrum.one_lt_absNorm_nnreal w) r).mpr hrw
  have hlt' : HeightOneSpectrum.adicAbv K w (algebraMap (𝓞 K) K r) < 1 :=
    heq.lt_one_iff.mp hlt
  rw [hone] at hlt'
  exact lt_irrefl 1 hlt'

/-- A finite-place absolute value is inequivalent to an infinite-place absolute value. -/
private theorem adicAbv_not_isEquiv_infinitePlace
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : NumberField.InfinitePlace K) :
    ¬ (HeightOneSpectrum.adicAbv K v).IsEquiv w.1 := by
  intro heq
  have hna_v : IsNonarchimedean (HeightOneSpectrum.adicAbv K v) := by
    intro a b
    exact HeightOneSpectrum.isNonarchimedean_adicAbv K v a b
  have hna_w : IsNonarchimedean w.1 := by
    intro a b
    have h1 := hna_v a b
    rcases le_total (HeightOneSpectrum.adicAbv K v a)
        (HeightOneSpectrum.adicAbv K v b) with hab | hab
    · exact le_trans ((heq (a + b) b).mp
        (le_trans h1 (sup_le hab le_rfl))) le_sup_right
    · exact le_trans ((heq (a + b) a).mp
        (le_trans h1 (sup_le le_rfl hab))) le_sup_left
  have h2 : w.1 (2 : K) = 2 := by
    rw [show w.1 2 = w 2 from rfl,
      ← NumberField.InfinitePlace.norm_embedding_eq, map_ofNat, Complex.norm_ofNat]
  have hle := hna_w 1 1
  simp only [show (1 : K) + 1 = 2 from by ring] at hle
  rw [h2, map_one] at hle
  simp only [max_self] at hle
  linarith

/-- **Weak approximation with a finite target and prescribed signs.** Let $K$ be a number field
and $\mathfrak m$ a modulus of $K$, with finite part $\mathfrak m_0$ (a nonzero ideal of
$\mathcal O_K$) and infinite part $\mathfrak m_\infty$ (a finite set of real places of $K$). For
a nonzero prime $\mathfrak p$ of $\mathcal O_K$ write $v_{\mathfrak p}$ for the
$\mathfrak p$-adic valuation on $K$ (with $v_{\mathfrak p}(0) = \infty$) and $e_{\mathfrak p}$
for the exponent of $\mathfrak p$ in $\mathfrak m_0$; for a real place $w$ write
$\sigma_w : K \to \mathbb R$ for its real embedding. Let $P$ be any set of places in
$\mathfrak m_\infty$, and let $a \in K$ be nonzero with $v_{\mathfrak p}(a) = 0$ for every
nonzero prime $\mathfrak p$ dividing $\mathfrak m_0$. Then there is a nonzero $x \in K$ such
that $v_{\mathfrak p}(x) = 0$ and $v_{\mathfrak p}(x - a) \ge e_{\mathfrak p}$ for every nonzero
prime $\mathfrak p$ dividing $\mathfrak m_0$, and such that for every $w \in \mathfrak m_\infty$,
$\sigma_w(x) > 0$ if $w \in P$ and $\sigma_w(x) < 0$ if $w \notin P$.

Source: mapping toward ATLAS N406, Theorem 21.8, Section 21.3
(`weak_approx_coprime_sign_finitePart`, lines 2255--2568): the finite target `a`
is lifted at source lines 2267--2275 with supported valuation-one hypothesis at
2277--2292; the finite/infinite index family below is at 2314--2385;
modulus-dependent tolerances at 2388--2404; nonzero witness at 2406--2412;
valuation preservation at 2414--2451; sign control at 2458--2477; and the strict
absolute-value-to-discrete-valuation residue comparison at 2480--2568. -/
theorem exists_ne_zero_with_target_and_sign
    (m : Modulus K) (a : K)
    (pos : {w : RealPlace K // w ∈ m.infinitePart} → Prop)
    (ha0 : a ≠ 0)
    (haval : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      finiteSupported m v → v.valuation K a = 1) :
    ∃ x : K, x ≠ 0 ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        finiteSupported m v →
          v.valuation K x = 1 ∧
          v.valuation K (x - a) ≤ WithZero.exp (-(finiteExponent m v))) ∧
      ∀ (w : RealPlace K) (hw : w ∈ m.infinitePart),
        (pos ⟨w, hw⟩ → 0 < InfinitePlace.embedding_of_isReal w.property x) ∧
        (¬ pos ⟨w, hw⟩ → InfinitePlace.embedding_of_isReal w.property x < 0) := by
  classical
  have hI : (m.finitePart : Ideal (𝓞 K)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp m.finitePart.property
  let S_fin := (Ideal.finite_factors hI).toFinset
  have mem_equiv : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      v ∈ S_fin ↔ finiteSupported m v := by
    intro v
    simp only [S_fin, Set.Finite.mem_toFinset]
    unfold finiteSupported
    exact Ideal.dvd_iff_le
  by_cases hsupp : S_fin.Nonempty ∨ m.infinitePart.Nonempty
  · let absVals : ↥S_fin ⊕ ↥m.infinitePart → AbsoluteValue K ℝ :=
      fun s => s.rec (fun v => HeightOneSpectrum.adicAbv K v.val)
        (fun w => w.val.val.1)
    have hnontriv : ∀ i, (absVals i).IsNontrivial := by
      intro i
      cases i with
      | inl v => exact adicAbv_isNontrivial v.val
      | inr w => exact NumberField.InfinitePlace.isNontrivial w.val.val
    have hpw : Pairwise fun i j => ¬ (absVals i).IsEquiv (absVals j) := by
      intro i j hij
      cases i with
      | inl v =>
        cases j with
        | inl w =>
          have hne : v.val ≠ w.val := by
            intro heq
            apply hij
            congr 1
            exact Subtype.ext heq
          exact adicAbv_not_isEquiv_of_ne v.val w.val hne
        | inr w =>
          exact adicAbv_not_isEquiv_infinitePlace v.val w.val.val
      | inr v =>
        cases j with
        | inl w =>
          intro heq
          exact adicAbv_not_isEquiv_infinitePlace w.val v.val.val heq.symm
        | inr w =>
          intro heq
          apply hij
          have hbase : v.val.val = w.val.val :=
            (NumberField.InfinitePlace.eq_iff_isEquiv).mpr heq
          have hreal : v.val = w.val := Subtype.ext hbase
          exact congrArg Sum.inr (Subtype.ext hreal)
    let target : ↥S_fin ⊕ ↥m.infinitePart → K :=
      fun s => s.rec (fun _ => a)
        (fun w => if pos ⟨w.val, w.property⟩ then 1 else -1)
    let εfun : ↥S_fin ⊕ ↥m.infinitePart → ℝ := fun s => s.rec
      (fun v => min (1 / 2)
        ((((Ideal.absNorm v.val.asIdeal : NNReal) : ℝ) ^
          (-(finiteExponent m v.val) : ℤ))))
      (fun _ => 1 / 2)
    have hεfun_pos : ∀ i, 0 < εfun i := by
      intro i
      cases i with
      | inl v =>
        simp only [εfun]
        apply lt_min (by norm_num)
        apply zpow_pos
        have hne0 := HeightOneSpectrum.absNorm_ne_zero (R := 𝓞 K) v.val
        have hpos : 0 < (Ideal.absNorm v.val.asIdeal : NNReal) :=
          pos_iff_ne_zero.mpr hne0
        exact_mod_cast hpos
      | inr _ =>
        simp only [εfun]
        norm_num
    obtain ⟨x, hx⟩ :=
      exists_forall_abv_sub_lt_of_eps absVals hnontriv hpw target εfun hεfun_pos
    have ha_abv_of : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        finiteSupported m v → HeightOneSpectrum.adicAbv K v a = 1 := by
      intro v hv
      rw [HeightOneSpectrum.adicAbv_def, haval v hv]
      simp
    have hxne : x ≠ 0 := by
      intro h0
      rcases hsupp with h | h
      · obtain ⟨v, hv⟩ := h
        have hlt := hx (Sum.inl ⟨v, hv⟩)
        simp only [absVals, target, εfun] at hlt
        have hsup : finiteSupported m v := (mem_equiv v).mp hv
        have ha_abv := ha_abv_of v hsup
        rw [h0, zero_sub, AbsoluteValue.map_neg] at hlt
        rw [ha_abv] at hlt
        have hle : min (1 / 2 : ℝ)
            ((((Ideal.absNorm v.asIdeal : NNReal) : ℝ) ^
              (-(finiteExponent m v) : ℤ))) ≤
            1 / 2 := min_le_left _ _
        linarith [lt_of_lt_of_le hlt hle]
      · obtain ⟨w, hw⟩ := h
        have hlt := hx (Sum.inr ⟨w, hw⟩)
        simp only [absVals, target, εfun] at hlt
        rw [h0] at hlt
        by_cases hpos : pos ⟨w, hw⟩ <;> simp only [hpos, ite_true, ite_false] at hlt <;>
          simp at hlt <;> linarith
    refine ⟨x, hxne, ?_, ?_⟩
    · intro v hv
      have hmem : v ∈ S_fin := (mem_equiv v).mpr hv
      have hlt := hx (Sum.inl (⟨v, hmem⟩ : ↥S_fin))
      simp only [absVals, target, εfun] at hlt
      have hlt_half : HeightOneSpectrum.adicAbv K v (x - a) < 1 / 2 :=
        lt_of_lt_of_le hlt (min_le_left _ _)
      have hlt_thresh : HeightOneSpectrum.adicAbv K v (x - a) <
          ((((Ideal.absNorm v.asIdeal : NNReal) : ℝ) ^
            (-(finiteExponent m v) : ℤ))) :=
        lt_of_lt_of_le hlt (min_le_right _ _)
      have ha_abv := ha_abv_of v hv
      have hlt1 : HeightOneSpectrum.adicAbv K v (x - a) < 1 :=
        lt_trans hlt_half (by norm_num)
      have hna := HeightOneSpectrum.isNonarchimedean_adicAbv K v
      have hlt_strict : HeightOneSpectrum.adicAbv K v (x - a) <
          HeightOneSpectrum.adicAbv K v a := by rw [ha_abv]; exact hlt1
      have hmax := IsNonarchimedean.add_eq_max_of_ne
        (fun a => AbsoluteValue.map_neg _ a) hna hlt_strict.ne
      rw [sub_add_cancel] at hmax
      have hxeq1 : HeightOneSpectrum.adicAbv K v x = 1 := by
        rw [hmax, ha_abv, max_eq_right (le_of_lt hlt1)]
      have hne0 := HeightOneSpectrum.absNorm_ne_zero (R := 𝓞 K) v
      have hne1 := ne_of_gt (HeightOneSpectrum.one_lt_absNorm_nnreal (R := 𝓞 K) v)
      have hval_one : v.valuation K x = 1 := by
        rw [HeightOneSpectrum.adicAbv_def] at hxeq1
        have hnnr : WithZeroMulInt.toNNReal hne0 (v.valuation K x) = 1 := by
          exact_mod_cast hxeq1
        exact (WithZeroMulInt.toNNReal_eq_one_iff _ hne0 hne1).mp hnnr
      have hval_le : v.valuation K (x - a) ≤
          WithZero.exp (-(finiteExponent m v)) := by
        have hlt1nn := HeightOneSpectrum.one_lt_absNorm_nnreal (R := 𝓞 K) v
        rw [HeightOneSpectrum.adicAbv_def] at hlt_thresh
        have htoNNReal_coe : WithZeroMulInt.toNNReal hne0
            (WithZero.exp (-(finiteExponent m v))) =
            (Ideal.absNorm v.asIdeal : NNReal) ^ (-(finiteExponent m v) : ℤ) := by
          rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
          congr 1
        have hrhs_cast : ((((Ideal.absNorm v.asIdeal : NNReal) : ℝ) ^
            (-(finiteExponent m v) : ℤ))) =
            ((((Ideal.absNorm v.asIdeal : NNReal) ^
              (-(finiteExponent m v) : ℤ)) : NNReal) : ℝ) := by
          rw [NNReal.coe_zpow]
        rw [hrhs_cast, ← htoNNReal_coe] at hlt_thresh
        have hnnr_lt : WithZeroMulInt.toNNReal hne0 (v.valuation K (x - a)) <
            WithZeroMulInt.toNNReal hne0
              (WithZero.exp (-(finiteExponent m v))) := by
          exact_mod_cast hlt_thresh
        exact le_of_lt
          ((WithZeroMulInt.toNNReal_strictMono hlt1nn).lt_iff_lt.mp hnnr_lt)
      exact ⟨hval_one, hval_le⟩
    · intro w hw
      have hlt := hx (Sum.inr (⟨w, hw⟩ : ↥m.infinitePart))
      simp only [absVals, target, εfun] at hlt
      by_cases hpos : pos ⟨w, hw⟩
      · simp only [hpos, ite_true] at hlt
        have hnorm : ‖InfinitePlace.embedding_of_isReal w.property x -
            InfinitePlace.embedding_of_isReal w.property 1‖ < 1 / 2 := by
          have htmp := hlt
          change w.val (x - 1) < 1 / 2 at htmp
          rw [← InfinitePlace.norm_embedding_of_isReal (w := w.val) w.property] at htmp
          simpa [map_sub, Real.norm_eq_abs] using htmp
        rw [map_one, Real.norm_eq_abs, abs_lt] at hnorm
        exact ⟨fun _ => by linarith, fun hcon => (hcon hpos).elim⟩
      · simp only [hpos, ite_false] at hlt
        have hnorm : ‖InfinitePlace.embedding_of_isReal w.property x -
            InfinitePlace.embedding_of_isReal w.property (-1)‖ < 1 / 2 := by
          have htmp := hlt
          change w.val (x - (-1)) < 1 / 2 at htmp
          rw [← InfinitePlace.norm_embedding_of_isReal (w := w.val) w.property] at htmp
          simpa [map_sub, Real.norm_eq_abs] using htmp
        rw [map_neg, map_one, Real.norm_eq_abs, abs_lt] at hnorm
        constructor
        · intro hcon
          exact absurd hcon hpos
        · intro _
          linarith
  · refine ⟨a, ha0, ?_, ?_⟩
    · intro v hv
      have hmem : v ∈ S_fin := (mem_equiv v).mpr hv
      exact (hsupp (Or.inl ⟨v, hmem⟩)).elim
    · intro w hw
      exact (hsupp (Or.inr ⟨w, hw⟩)).elim

/-- **Weak approximation with prescribed signs at a modulus.** Let $K$ be a number field and
$\mathfrak m$ a modulus of $K$, with finite part $\mathfrak m_0$ (a nonzero ideal of
$\mathcal O_K$) and infinite part $\mathfrak m_\infty$ (a finite set of real places of $K$); for
a real place $w$ write $\sigma_w : K \to \mathbb R$ for its real embedding. For every set $P$ of
places in $\mathfrak m_\infty$ there is a nonzero $x \in K$ whose $\mathfrak p$-adic valuation
is $0$ for every nonzero prime $\mathfrak p$ of $\mathcal O_K$ dividing $\mathfrak m_0$, and such
that for every $w \in \mathfrak m_\infty$, $\sigma_w(x) > 0$ if $w \in P$ and $\sigma_w(x) < 0$
if $w \notin P$.

This is the special case of weak approximation with a finite target and prescribed signs in
which the target is $1$. -/
theorem exists_ne_zero_with_valuation_one_and_sign
    (m : Modulus K)
    (pos : {w : RealPlace K // w ∈ m.infinitePart} → Prop) :
    ∃ x : K, x ≠ 0 ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        finiteSupported m v → v.valuation K x = 1) ∧
      ∀ (w : RealPlace K) (hw : w ∈ m.infinitePart),
        (pos ⟨w, hw⟩ → 0 < InfinitePlace.embedding_of_isReal w.property x) ∧
        (¬ pos ⟨w, hw⟩ → InfinitePlace.embedding_of_isReal w.property x < 0) := by
  obtain ⟨x, hxne, hval, hsign⟩ := exists_ne_zero_with_target_and_sign m 1 pos
    one_ne_zero (fun _ _ => map_one _)
  exact ⟨x, hxne, fun v hv => (hval v hv).1, hsign⟩

end Modulus

end NumberField
