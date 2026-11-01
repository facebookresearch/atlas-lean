/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.BanachLimit

open scoped BoundedContinuousFunction

/-!
# Banach limits on bounded real sequences

A Banach limit is a positive shift-invariant continuous real-linear functional
on `ℕ →ᵇ ℝ` extending ordinary limits. Following Banach, the ordinary limit
functional on convergent sequences is dominated by the sublinear functional
`M x = limsup (Cesàro means of x)` and extended by Hahn–Banach
(`exists_extension_of_le_sublinear`); the bound `|L| ≤ ‖·‖` gives continuity,
and shift-invariance holds because the Cesàro means of `Sx - x` telescope to
`(x n - x 0) / n → 0`.

Source: S. Banach, *Théorie des opérations linéaires* (1932); G. G. Lorentz,
"A contribution to the theory of divergent sequences", *Acta Mathematica* 80
(1948), 167–190, DOI `10.1007/BF02393648`.
-/

noncomputable section

private abbrev BoundedSeq := ℕ →ᵇ ℝ

/-- Left shift on bounded real sequences. -/
private def shift : BoundedSeq →ₗ[ℝ] BoundedSeq where
  toFun f := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun n => f (n + 1)) continuous_of_discreteTopology ‖f‖
    (fun n => BoundedContinuousFunction.norm_coe_le_norm f (n + 1))
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro n
    rfl
  map_smul' c f := by
    apply BoundedContinuousFunction.ext
    intro n
    rfl

private lemma shift_apply (f : BoundedSeq) (n : ℕ) : (shift f) n = f (n + 1) := rfl

/-- Cesàro mean of the first `n` values. -/
private def cesMean (x : BoundedSeq) (n : ℕ) : ℝ := (n⁻¹ : ℝ) * ∑ i ∈ Finset.range n, x i

/-- Dominating functional: limsup of Cesàro means. -/
private def limsupCes : BoundedSeq → ℝ := fun x => Filter.limsup (cesMean x) Filter.atTop

private lemma bddAbove_of_le {u : ℕ → ℝ} {C : ℝ} (h : ∀ n, u n ≤ C) :
    Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) Filter.atTop u :=
  Filter.isBoundedUnder_of ⟨C, h⟩

private lemma bddBelow_of_le {u : ℕ → ℝ} {C : ℝ} (h : ∀ n, C ≤ u n) :
    Filter.IsBoundedUnder (fun x1 x2 => x2 ≤ x1) Filter.atTop u :=
  Filter.isBoundedUnder_of ⟨C, h⟩

private lemma cobdd_of_bddBelow {u : ℕ → ℝ} {C : ℝ} (h : ∀ n, C ≤ u n) :
    Filter.IsCoboundedUnder (fun x1 x2 => x1 ≤ x2) Filter.atTop u :=
  (bddBelow_of_le h).isCobounded_flip

private lemma coe_le_norm (f : BoundedSeq) (n : ℕ) : f n ≤ ‖f‖ := by
  calc f n ≤ |f n| := le_abs_self _
    _ = ‖f n‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖f‖ := BoundedContinuousFunction.norm_coe_le_norm f n

/-- Scalar multiples pass through Cesàro means. -/
private lemma cesMean_smul (c : ℝ) (x : BoundedSeq) (n : ℕ) :
    cesMean (c • x) n = c * cesMean x n := by
  unfold cesMean
  simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- Sums pass through Cesàro means. -/
private lemma cesMean_add (x y : BoundedSeq) (n : ℕ) :
    cesMean (x + y) n = cesMean x n + cesMean y n := by
  unfold cesMean
  simp only [BoundedContinuousFunction.add_apply, Finset.sum_add_distrib]
  ring

/-- Negation passes through Cesàro means. -/
private lemma cesMean_neg (x : BoundedSeq) (n : ℕ) : cesMean (-x) n = -cesMean x n := by
  unfold cesMean
  simp only [BoundedContinuousFunction.neg_apply, Finset.sum_neg_distrib, mul_neg]

/-- Cesàro means are bounded above by the norm. -/
private lemma cesMean_le_norm (x : BoundedSeq) (n : ℕ) : cesMean x n ≤ ‖x‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · unfold cesMean
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero]
    exact norm_nonneg _
  · have hsum : ∑ i ∈ Finset.range n, x i ≤ n * ‖x‖ := by
      calc ∑ i ∈ Finset.range n, x i
          ≤ ∑ _i ∈ Finset.range n, ‖x‖ :=
            Finset.sum_le_sum fun i _ => coe_le_norm x i
        _ = n * ‖x‖ := by
            simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc cesMean x n = (n⁻¹ : ℝ) * ∑ i ∈ Finset.range n, x i := rfl
      _ ≤ (n⁻¹ : ℝ) * ((n : ℝ) * ‖x‖) :=
          mul_le_mul_of_nonneg_left hsum
            (inv_nonneg.mpr (Nat.cast_nonneg n))
      _ = ‖x‖ := inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr hn) _

/-- Cesàro means are bounded below by the negated norm. -/
private lemma norm_le_cesMean (x : BoundedSeq) (n : ℕ) : -‖x‖ ≤ cesMean x n := by
  linarith [cesMean_le_norm (-x) n, cesMean_neg x n, norm_neg x]

private lemma cesMeanBddAbove (x : BoundedSeq) :
    Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) Filter.atTop (cesMean x) :=
  bddAbove_of_le (fun n => cesMean_le_norm x n)

private lemma cesMeanBddBelow (x : BoundedSeq) :
    Filter.IsBoundedUnder (fun x1 x2 => x2 ≤ x1) Filter.atTop (cesMean x) :=
  bddBelow_of_le (fun n => norm_le_cesMean x n)

private lemma cesMeanCobdd (x : BoundedSeq) :
    Filter.IsCoboundedUnder (fun x1 x2 => x1 ≤ x2) Filter.atTop (cesMean x) :=
  cobdd_of_bddBelow (fun n => norm_le_cesMean x n)

/-- Positive homogeneity of `limsupCes`. -/
private lemma limsupCes_hom :
    ∀ c : ℝ, 0 < c → ∀ x : BoundedSeq, limsupCes (c • x) = c * limsupCes x := by
  have hle : ∀ c : ℝ, ∀ x : BoundedSeq, 0 < c →
      Filter.limsup (cesMean (c • x)) Filter.atTop
        ≤ c * Filter.limsup (cesMean x) Filter.atTop := by
    intro c x hc
    show Filter.limsup (cesMean (c • x)) Filter.atTop ≤ _
    rw [Filter.limsup_le_iff (cesMeanCobdd (c • x)) (cesMeanBddAbove (c • x))]
    intro y hy
    have hy' : Filter.limsup (cesMean x) Filter.atTop < y / c := by
      rw [lt_div_iff₀ hc, mul_comm]
      exact hy
    have hev := Filter.eventually_lt_of_limsup_lt hy' (cesMeanBddAbove x)
    filter_upwards [hev] with n hn
    rw [cesMean_smul]
    calc c * cesMean x n < c * (y / c) := mul_lt_mul_of_pos_left hn hc
      _ = y := mul_div_cancel₀ _ (ne_of_gt hc)
  intro c hc x
  have h1 := hle c x hc
  have h2 := hle c⁻¹ (c • x) (inv_pos.mpr hc)
  have e2 : cesMean (c⁻¹ • (c • x)) = cesMean x := by
    funext n
    rw [cesMean_smul, cesMean_smul]
    exact inv_mul_cancel_left₀ (ne_of_gt hc) _
  rw [e2] at h2
  have h3 : c * Filter.limsup (cesMean x) Filter.atTop
      ≤ Filter.limsup (cesMean (c • x)) Filter.atTop := by
    have h4 := mul_le_mul_of_nonneg_left h2 hc.le
    rwa [mul_inv_cancel_left₀ (ne_of_gt hc)] at h4
  change Filter.limsup (cesMean (c • x)) Filter.atTop
    = c * Filter.limsup (cesMean x) Filter.atTop
  exact le_antisymm h1 h3

/-- Subadditivity of `limsupCes`. -/
private lemma limsupCes_add :
    ∀ x y : BoundedSeq, limsupCes (x + y) ≤ limsupCes x + limsupCes y := by
  intro x y
  change Filter.limsup (cesMean (x + y)) Filter.atTop
    ≤ Filter.limsup (cesMean x) Filter.atTop
      + Filter.limsup (cesMean y) Filter.atTop
  have e : cesMean (x + y) = (cesMean x + cesMean y) := funext fun n => cesMean_add x y n
  rw [e]
  exact limsup_add_le (cesMeanBddBelow x) (cesMeanBddAbove x) (cesMeanCobdd y)
    (cesMeanBddAbove y)

/-- `limsupCes` is bounded by the norm. -/
private lemma limsupCes_bound (x : BoundedSeq) : limsupCes x ≤ ‖x‖ := by
  change Filter.limsup (cesMean x) Filter.atTop ≤ _
  exact Filter.limsup_le_of_le (cesMeanCobdd x)
    (Filter.Eventually.of_forall fun n => cesMean_le_norm x n)

/-- The subspace of convergent sequences. -/
private def convSub : Submodule ℝ BoundedSeq :=
  { carrier := {x | ∃ a, Filter.Tendsto (fun n => x n) Filter.atTop (nhds a)}
    add_mem' := by
      rintro x y ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a + b, ha.add hb⟩
    zero_mem' := ⟨0, tendsto_const_nhds⟩
    smul_mem' := by
      rintro c x ⟨a, ha⟩
      exact ⟨c * a, ha.const_mul c⟩ }

/-- The limit functional on convergent sequences. -/
private def limFun : convSub →ₗ[ℝ] ℝ where
  toFun x := Classical.choose (x.2 : ∃ a, _)
  map_add' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    have hx' := Classical.choose_spec hx
    have hy' := Classical.choose_spec hy
    have hadd := hx'.add hy'
    have hmem : x + y ∈ convSub := ⟨_, hadd⟩
    exact (tendsto_nhds_unique hadd (Classical.choose_spec hmem)).symm
  map_smul' := by
    rintro c ⟨x, hx⟩
    have hx' := Classical.choose_spec hx
    have hsm := hx'.const_mul c
    have hmem : c • x ∈ convSub := ⟨_, hsm⟩
    exact (tendsto_nhds_unique hsm (Classical.choose_spec hmem)).symm

/-- The limit functional as a partial linear map. -/
private noncomputable def pmap : BoundedSeq →ₗ.[ℝ] ℝ := ⟨convSub, limFun⟩

/-- `limFun` is dominated by `limsupCes`: Cesàro means preserve limits. -/
private lemma limFun_le (x : convSub) : limFun x ≤ limsupCes ↑x := by
  have h := Classical.choose_spec x.2
  have hces : Filter.Tendsto (cesMean ↑x) Filter.atTop (nhds (limFun x)) := h.cesaro
  have heq : Filter.limsup (cesMean ↑x) Filter.atTop = limFun x :=
    Filter.Tendsto.limsup_eq hces
  change limFun x ≤ Filter.limsup (cesMean ↑x) Filter.atTop
  rw [heq]

private lemma pmap_le (x : pmap.domain) : pmap x ≤ limsupCes (x : BoundedSeq) :=
  limFun_le ⟨(x : BoundedSeq), x.2⟩

/-- The dominated extension exists by Hahn–Banach. -/
private noncomputable def extension : BoundedSeq →ₗ[ℝ] ℝ :=
  Classical.choose (exists_extension_of_le_sublinear pmap limsupCes limsupCes_hom
    limsupCes_add pmap_le)

private lemma extension_spec :
    (∀ x : pmap.domain, extension (x : BoundedSeq) = pmap x) ∧ ∀ x, extension x ≤ limsupCes x :=
  Classical.choose_spec
    (exists_extension_of_le_sublinear pmap limsupCes limsupCes_hom
      limsupCes_add pmap_le)

private lemma extension_eq_lim (x : pmap.domain) : extension (x : BoundedSeq) = pmap x :=
  extension_spec.1 x

private lemma extension_le (x : BoundedSeq) : extension x ≤ limsupCes x :=
  extension_spec.2 x

/-- The extension is bounded by the norm. -/
private lemma extension_bound (x : BoundedSeq) : |extension x| ≤ ‖x‖ := by
  have h1 : extension x ≤ limsupCes x := extension_le x
  have h2 : extension (-x) ≤ limsupCes (-x) := extension_le (-x)
  have hNx : limsupCes x ≤ ‖x‖ := limsupCes_bound x
  have hNnx : limsupCes (-x) ≤ ‖x‖ := by
    simpa using limsupCes_bound (-x)
  have hne : extension (-x) = -extension x := map_neg _ _
  rw [abs_le]
  constructor <;> linarith

/-- Telescoping: means of `Sx - x` equal `(x n - x 0) / n`. -/
private lemma cesMean_shift_sub (x : BoundedSeq) (n : ℕ) :
    cesMean (shift x - x) n = (x n - x 0) / (n : ℝ) := by
  have h : (fun i => (shift x) i - x i) = (fun i => x (i + 1) - x i) :=
    funext fun i => by rw [shift_apply]
  have esum : ∑ i ∈ Finset.range n, ((shift x) i - x i) = x n - x 0 := by
    rw [h]
    have t := Finset.sum_range_sub' (fun i => x i) n
    have neg : (∑ i ∈ Finset.range n, (x (i + 1) - x i))
        = -(∑ i ∈ Finset.range n, (x i - x (i + 1))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [neg, t, neg_sub]
  unfold cesMean
  simp only [BoundedContinuousFunction.sub_apply, esum]
  rw [div_eq_mul_inv, mul_comm]

/-- The telescoped means tend to zero. -/
private lemma tendsto_cesMean_shift_sub (x : BoundedSeq) :
    Filter.Tendsto (cesMean (shift x - x)) Filter.atTop (nhds 0) := by
  have e : cesMean (shift x - x) = (fun n => (x n - x 0) / (n : ℝ)) :=
    funext fun n => cesMean_shift_sub x n
  rw [e]
  refine squeeze_zero_norm (fun n => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖x‖))
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hle : ‖x n - x 0‖ ≤ 2 * ‖x‖ := by
      calc ‖x n - x 0‖ ≤ ‖x n‖ + ‖x 0‖ := norm_sub_le _ _
        _ ≤ ‖x‖ + ‖x‖ := by
            gcongr <;>
              exact BoundedContinuousFunction.norm_coe_le_norm _ _
        _ = 2 * ‖x‖ := by ring
    calc ‖(x n - x 0) / (n : ℝ)‖
        = ‖x n - x 0‖ / ‖(n : ℝ)‖ := norm_div _ _
      _ ≤ (2 * ‖x‖) / ‖(n : ℝ)‖ := by gcongr
      _ = (2 * ‖x‖) / (n : ℝ) := by norm_num

/-- A continuous linear functional extending limits, positive and shift-invariant,
exists: the Hahn–Banach extension made continuous by `|L| ≤ ‖·‖`. -/
private theorem exists_banachFunctional : ∃ L : BoundedSeq →L[ℝ] ℝ,
    (∀ x : BoundedSeq, ∀ a : ℝ, Filter.Tendsto (fun n => x n) Filter.atTop (nhds a) →
      L x = a) ∧
    (∀ x : BoundedSeq, (∀ n, 0 ≤ x n) → 0 ≤ L x) ∧
    (∀ x : BoundedSeq, L (shift x - x) = 0) := by
  refine ⟨LinearMap.mkContinuous extension 1 ?_, ?_, ?_, ?_⟩
  · intro x
    have h := extension_bound x
    simp only [one_mul]
    rwa [Real.norm_eq_abs]
  · intro x a h
    have hx : x ∈ convSub := ⟨a, h⟩
    have e1 : extension ((⟨x, hx⟩ : pmap.domain) : BoundedSeq) = pmap ⟨x, hx⟩ :=
      extension_eq_lim _
    have e2 : pmap (⟨x, hx⟩ : pmap.domain) = a :=
      tendsto_nhds_unique (Classical.choose_spec (⟨x, hx⟩ : pmap.domain).2) h
    have hyx : ((⟨x, hx⟩ : pmap.domain) : BoundedSeq) = x := rfl
    change extension x = a
    rw [← hyx, e1]
    exact e2
  · intro x h
    have hle : limsupCes (-x) ≤ 0 := by
      change Filter.limsup (cesMean (-x)) Filter.atTop ≤ _
      apply Filter.limsup_le_of_le (cesMeanCobdd (-x))
      apply Filter.Eventually.of_forall
      intro n
      rw [cesMean_neg]
      have hnn : 0 ≤ cesMean x n := by
        unfold cesMean
        apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
        exact Finset.sum_nonneg fun i _ => h i
      linarith
    have h2 : extension (-x) ≤ limsupCes (-x) := extension_le (-x)
    have hne : extension (-x) = -extension x := map_neg _ _
    change 0 ≤ extension x
    linarith [h2.trans hle]
  · intro x
    have hM0 : limsupCes (shift x - x) = 0 :=
      Filter.Tendsto.limsup_eq (tendsto_cesMean_shift_sub x)
    have hM0' : limsupCes (x - shift x) = 0 := by
      have e : cesMean (x - shift x) = (fun n => -cesMean (shift x - x) n) := by
        funext n
        show cesMean (x - shift x) n = -cesMean (shift x - x) n
        have esub : (x - shift x : BoundedSeq) = -((shift x - x) : BoundedSeq) := (neg_sub _ _).symm
        rw [esub, cesMean_neg]
      have htend : Filter.Tendsto (cesMean (x - shift x)) Filter.atTop (nhds 0) := by
        rw [e]
        simpa using (tendsto_cesMean_shift_sub x).neg
      exact Filter.Tendsto.limsup_eq htend
    have h1 : extension (shift x - x) ≤ limsupCes (shift x - x) := extension_le _
    have h2 : extension (x - shift x) ≤ limsupCes (x - shift x) := extension_le _
    rw [hM0] at h1
    rw [hM0'] at h2
    have hne : extension (x - shift x) = -extension (shift x - x) := by
      have e : (x - shift x : BoundedSeq) = -(shift x - x) := (neg_sub _ _).symm
      rw [e, map_neg]
    change extension (shift x - x) = 0
    linarith

/-- The Banach limit functional. -/
private noncomputable def banachFunctional : BoundedSeq →L[ℝ] ℝ :=
  Classical.choose exists_banachFunctional

private lemma banachFunctional_convergent (x : BoundedSeq) (a : ℝ)
    (h : Filter.Tendsto (fun n => x n) Filter.atTop (nhds a)) :
    banachFunctional x = a :=
  (Classical.choose_spec exists_banachFunctional).1 x a h

private lemma banachFunctional_nonneg (x : BoundedSeq) (h : ∀ n, 0 ≤ x n) :
    0 ≤ banachFunctional x :=
  (Classical.choose_spec exists_banachFunctional).2.1 x h

private lemma banachFunctional_shift (x : BoundedSeq) :
    banachFunctional (shift x - x) = 0 :=
  (Classical.choose_spec exists_banachFunctional).2.2 x

private lemma banachFunctional_one :
    banachFunctional (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1 :=
  banachFunctional_convergent _ _ tendsto_const_nhds

private lemma banachFunctional_shift_eq (f g : BoundedSeq) (h : ∀ n, g n = f (n + 1)) :
    banachFunctional f = banachFunctional g := by
  have e : shift f = g := by
    apply BoundedContinuousFunction.ext
    intro n
    rw [shift_apply]
    exact (h n).symm
  have h0 := banachFunctional_shift f
  rw [e, map_sub] at h0
  exact (sub_eq_zero.mp h0).symm

/--
**Existence of Banach limits.** There is a continuous linear functional $L$ on the real Banach
space $\ell^\infty$ of bounded real sequences with the supremum norm such that $L(f) \ge 0$
whenever $f_n \ge 0$ for every $n$, $L$ maps the constant sequence $1$ to $1$, $L(f) = L(g)$
whenever $g_n = f_{n+1}$ for every $n$, and $L(f) = l$ whenever the sequence $f_n$ converges
to $l$.

Source: S. Banach, Theorie des operations lineaires, 1932, definition of generalised limit; G.
Lorentz, Acta Math. 80 (1948) 167-190; Lean formalizes ℓ∞ via `BoundedContinuousFunction ℕ ℝ` and
real field `ℝ` with all four classical axioms.
-/
public theorem banach_limit :
    ∃ L : BoundedContinuousFunction ℕ ℝ →L[ℝ] ℝ,
      (∀ f : BoundedContinuousFunction ℕ ℝ, (∀ n, 0 ≤ f n) → 0 ≤ L f) ∧
      L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1 ∧
      (∀ (f g : BoundedContinuousFunction ℕ ℝ), (∀ n, g n = f (n + 1)) → L f = L g) ∧
      (∀ (f : BoundedContinuousFunction ℕ ℝ) (l : ℝ),
        Filter.Tendsto (fun n => f n) Filter.atTop (nhds l) → L f = l) :=
  ⟨banachFunctional, banachFunctional_nonneg, banachFunctional_one,
    fun f g h => banachFunctional_shift_eq f g h,
    fun f l h => banachFunctional_convergent f l h⟩

end

end MathlibExt.Analysis.FunctionalAnalysis.BanachLimit
