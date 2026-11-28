/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LanglandsTunnell_exists_gt_and_hermiteSum_GammaR_mul_mellin_
ne_zero_of_shift_ratio_real.lean`
and
`P2M/Sol/S_LanglandsTunnell_exists_gt_and_hermiteSum_GammaR_mul_mellin_
ne_zero_of_shift_ratio_real.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Complex Filter Topology


private theorem eventually_sum_mul_ne_zero {ι α : Type*} (S : Finset ι) (d : ι → ℂ) (G : ι → α → ℂ)
  (l : Filter α)
    (T₀ : ι) (hG₀ : ∀ᶠ x in l, G T₀ x ≠ 0) (κ : ι → ℂ)
    (hlim : ∀ T ∈ S, Tendsto (fun x => G T x / G T₀ x) l (𝓝 (κ T)))
    (hL : ∑ T ∈ S, d T * κ T ≠ 0) :
    ∀ᶠ x in l, ∑ T ∈ S, d T * G T x ≠ 0 := by
  have hsum : Tendsto (fun x => ∑ T ∈ S, d T * (G T x / G T₀ x)) l (𝓝 (∑ T ∈ S, d T * κ T)) :=
    tendsto_finsetSum _ fun T hT => (hlim T hT).const_mul (d T)
  have hne : ∀ᶠ x in l, ∑ T ∈ S, d T * (G T x / G T₀ x) ≠ 0 := hsum.eventually_ne hL
  filter_upwards [hne, hG₀] with x h1 h2
  have : ∑ T ∈ S, d T * G T x = G T₀ x * ∑ T ∈ S, d T * (G T x / G T₀ x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    field_simp
  rw [this]
  exact mul_ne_zero h2 h1

private theorem sum_ne_zero_of_nonneg_re {ι : Type*} (S : Finset ι) (v : ι → ℂ) (T₀ : ι) (hT₀ : T₀
  ∈ S)
    (hre : ∀ T ∈ S, 0 ≤ (v T).re) (h0 : 0 < (v T₀).re) :
    ∑ T ∈ S, v T ≠ 0 := by
  intro h
  have hr : (∑ T ∈ S, v T).re = ∑ T ∈ S, (v T).re := by simp [Complex.re_sum]
  have : 0 < ∑ T ∈ S, (v T).re :=
    lt_of_lt_of_le h0 (Finset.single_le_sum (fun T hT => hre T hT) hT₀)
  rw [← hr, h] at this
  simp at this


open Complex Filter Topology

namespace LanglandsTunnell

/-- **Admissible Hermite indices.** For $m \in \mathbb{N}$, $a_3 \in \mathbb{Z}/2$ and
$e \in \mathbb{Z}$, the finite set of index quadruples $T = ((i, l), (j, k))$ of natural numbers
at most $m$ with $l + j + k + 2i = m$ and $l \equiv e + a_3 \pmod 2$. -/
def hermiteAdmissible (m : ℕ) (a₃ : ZMod 2) (e : ℤ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ
    Finset.range (m + 1))).filter
      (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
        ((T.1.2 : ZMod 2) = (e : ZMod 2) + a₃))

/-- **Hermite coefficient.** For $m \in \mathbb{N}$, $a \in \mathbb{Q}$ and an index
$T = ((i, l), (j, k))$,
$$c_T = (-1)^{j + k} \cdot \frac{(-1)^i \, m! \, a^k}{i! \, l! \, j! \, k! \, (4\pi)^i}.$$ -/
noncomputable def hermiteCoeff (m : ℕ) (a : ℚ) (T : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  (-1 : ℂ) ^ (T.2.1 + T.2.2) *
    ((-1 : ℂ) ^ T.1.1 * (m.factorial : ℂ) * (a : ℂ) ^ T.2.2 /
      ((T.1.1.factorial : ℂ) * (T.1.2.factorial : ℂ) * (T.2.1.factorial : ℂ) *
        (T.2.2.factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ T.1.1))

/-- **Gamma–Mellin weighted Hermite sum.** For a family
$H : \mathbb{N} \to \mathbb{Z}/2 \to \mathbb{R} \to \mathbb{C}$ and a real shift $s$, the sum
over the admissible indices $T = ((i, l), (j, k))$ (`hermiteAdmissible m a₃ e`) of
$$c_T \, \Gamma_{\mathbb{R}}(s + u_3 + l) \, \mathcal{M}(H_{j,\, e + k})(s + k - 1),$$
where $c_T$ is `hermiteCoeff m a T`, the parity $e + k$ is read in $\mathbb{Z}/2$,
$\Gamma_{\mathbb{R}}(z) = \pi^{-z/2} \, \Gamma(z/2)$, and $\mathcal{M}$ is the Mellin transform. -/
noncomputable def hermiteGammaMellinSum (m : ℕ) (a : ℚ) (u₃ : ℂ) (a₃ : ZMod 2) (e : ℤ)
    (H : ℕ → ZMod 2 → ℝ → ℂ) (s : ℝ) : ℂ :=
  ∑ T ∈ hermiteAdmissible m a₃ e, hermiteCoeff m a T *
    Complex.Gammaℝ ((s : ℂ) + u₃ + (T.1.2 : ℂ)) *
      mellin (H T.2.1 ((e : ZMod 2) + (T.2.2 : ZMod 2))) ((s : ℂ) + (T.2.2 : ℂ) - 1)

/-- **Gamma–Mellin Hermite sums are nonzero at arbitrarily large shifts.** Let $m \in \mathbb{N}$,
$a \in \mathbb{Q}$ with $a \neq 0$, $u_3 \in \mathbb{C}$, $a_3 \in \mathbb{Z}/2$ and
$e \in \mathbb{Z}$, and suppose the admissible index set `hermiteAdmissible m a₃ e` is nonempty.
Let $H : \mathbb{N} \to \mathbb{Z}/2 \to \mathbb{R} \to \mathbb{C}$ be a family whose Mellin
transforms $M_{j,b} = \mathcal{M}(H_{j,b})$ satisfy two conditions:

* (`hA`) for every $j$, every parity $b$ and every $\varepsilon > 0$ there is $R$ such that
  for all real $x \ge R$, $M_{j,b}(x) \neq 0$ and
  $$\Bigl\lVert M_{j,b}(x + 2) - \frac{x}{2\pi a^2} \, M_{j,b}(x) \Bigr\rVert
    \le \varepsilon \, x \, \lVert M_{j,b}(x) \rVert;$$
* (`hB`) for every $j$, all parities $b$ and $b'$ and every $\varepsilon > 0$ there is $R$
  such that for all real $x \ge R$,
  $$\lVert M_{j+1,b'}(x - 1) \rVert \le \varepsilon \, \lVert M_{j,b}(x) \rVert.$$

Then for every $\sigma_0 \in \mathbb{R}$ there is a real $s > \sigma_0$ with
`hermiteGammaMellinSum m a u₃ a₃ e H s ≠ 0`. -/
public theorem exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real
    (m : ℕ) (a : ℚ) (ha : a ≠ 0) (u₃ : ℂ) (a₃ : ZMod 2) (e : ℤ)
    (hne : (hermiteAdmissible m a₃ e).Nonempty)
    (H : ℕ → ZMod 2 → ℝ → ℂ)
    (hA : ∀ (j : ℕ) (b : ZMod 2) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      mellin (H j b) (x : ℂ) ≠ 0 ∧
      ‖mellin (H j b) ((x : ℂ) + 2) - (x : ℂ) / (2 * (Real.pi : ℂ) * (a : ℂ) ^ 2) * mellin (H j b)
        (x : ℂ)‖ ≤ ε * x * ‖mellin (H j b) (x : ℂ)‖)
    (hB : ∀ (j : ℕ) (b b' : ZMod 2) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      ‖mellin (H (j + 1) b') ((x : ℂ) - 1)‖ ≤ ε * ‖mellin (H j b) (x : ℂ)‖) :
    ∀ σ₀ : ℝ, ∃ s : ℝ, σ₀ < s ∧ hermiteGammaMellinSum m a u₃ a₃ e H s ≠ 0 := by
  intro σ₀
  classical
  set Adm := hermiteAdmissible m a₃ e
  obtain ⟨T₁, hT₁⟩ := hne
  have hT₁' := (Finset.mem_filter.1 hT₁).2
  set iS : ℕ := T₁.1.2 % 2 with hiS
  have hiS2 : iS < 2 := Nat.mod_lt _ (by norm_num)
  have hiSle : iS ≤ m := by
    have : iS ≤ T₁.1.2 := Nat.mod_le _ _
    omega
  set lS : ℕ := m - iS with hlS
  have hil : iS + lS = m := by omega
  have hiSpar : ((iS : ℕ) : ZMod 2) = (e : ZMod 2) + a₃ := by
    rw [← hT₁'.2, hiS]
    exact (ZMod.natCast_mod T₁.1.2 2).symm ▸ rfl
  set TS : (ℕ × ℕ) × (ℕ × ℕ) := ((0, iS), (0, lS)) with hTS
  have hTS_mem : TS ∈ Adm := by
    refine Finset.mem_filter.2 ⟨?_, ?_, ?_⟩
    · simp only [hTS, Finset.mem_product, Finset.mem_range]; omega
    · simp only [hTS]; omega
    · simpa only [hTS] using hiSpar
  set d := hermiteCoeff m a with hd
  set G : (ℕ × ℕ) × (ℕ × ℕ) → ℝ → ℂ := fun T s =>
    Complex.Gammaℝ ((s : ℂ) + u₃ + (T.1.2 : ℂ)) * mellin (H T.2.1 ((e : ZMod 2) + (T.2.2 : ZMod
      2))) ((s : ℂ) + (T.2.2 : ℂ) - 1) with hG
  set κ : (ℕ × ℕ) × (ℕ × ℕ) → ℂ := fun T => if T.1.1 = 0 ∧ T.2.1 = 0 then ((a : ℂ) ^ 2) ^ ((T.1.2 -
    iS) / 2) else 0 with hκ
  have hpos : (0 : ℝ) < 2 * Real.pi * (a : ℝ) ^ 2 := by positivity
  set A : ℂ := 2 * (Real.pi : ℂ) * (a : ℂ) ^ 2 with hAdef
  have hA0 : A ≠ 0 := by
    simp only [hAdef]; exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast
      Real.pi_ne_zero)) (pow_ne_zero _ (by exact_mod_cast ha))
  have hNZ : ∀ (j : ℕ) (b : ZMod 2), ∀ᶠ x : ℝ in atTop, mellin (H j b) (x : ℂ) ≠ 0 := by
    intro j b
    obtain ⟨R, hR⟩ := hA j b 1 one_pos
    filter_upwards [eventually_ge_atTop R] with x hx using (hR x hx).1
  have hAn : 0 < ‖A‖ := norm_pos_iff.2 hA0
  have hρ : ∀ (j : ℕ) (b : ZMod 2),
      Tendsto (fun x : ℝ => mellin (H j b) ((x : ℂ) + 2) / (((x : ℂ) / A) * mellin (H j b) (x :
        ℂ))) atTop (𝓝 1) := by
    intro j b
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨R, hR⟩ := hA j b (δ / (2 * ‖A‖)) (by positivity)
    refine ⟨max R 1, fun x hx => ?_⟩
    have hxR : R ≤ x := le_trans (le_max_left _ _) hx
    have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
    have hx0 : (0 : ℝ) < x := by linarith
    obtain ⟨hne0, hbd⟩ := hR x hxR
    have hden : ((x : ℂ) / A) * mellin (H j b) (x : ℂ) ≠ 0 :=
      mul_ne_zero (div_ne_zero (by exact_mod_cast hx0.ne') hA0) hne0
    have hnx : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    have hM : 0 < ‖mellin (H j b) (x : ℂ)‖ := norm_pos_iff.2 hne0
    rw [dist_eq_norm, div_sub_one hden, norm_div, norm_mul, norm_div, hnx, div_lt_iff₀ (by
      positivity)]
    have hbd' : ‖mellin (H j b) ((x : ℂ) + 2) - (x : ℂ) / A * mellin (H j b) (x : ℂ)‖ ≤ δ / (2 *
      ‖A‖) * x * ‖mellin (H j b) (x : ℂ)‖ := by
      simpa only [hAdef] using hbd
    have hP : 0 < x / ‖A‖ * ‖mellin (H j b) (x : ℂ)‖ := by positivity
    have heq : δ / (2 * ‖A‖) * x * ‖mellin (H j b) (x : ℂ)‖ = (1 / 2) * (δ * (x / ‖A‖ * ‖mellin (H
      j b) (x : ℂ)‖)) := by
      field_simp
    rw [heq] at hbd'
    nlinarith
  have hθ : ∀ (j : ℕ) (b b' : ZMod 2),
      Tendsto (fun x : ℝ => mellin (H (j + 1) b') ((x : ℂ) - 1) / mellin (H j b) (x : ℂ)) atTop (𝓝
        0) := by
    intro j b b'
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨R, hR⟩ := hB j b b' (δ / 2) (by positivity)
    obtain ⟨R', hR'⟩ := hA j b 1 one_pos
    refine ⟨max R R', fun x hx => ?_⟩
    have hne0 := (hR' x (le_trans (le_max_right _ _) hx)).1
    have hbd := hR x (le_trans (le_max_left _ _) hx)
    have hM : 0 < ‖mellin (H j b) (x : ℂ)‖ := norm_pos_iff.2 hne0
    rw [dist_eq_norm, sub_zero, norm_div, div_lt_iff₀ hM]
    nlinarith
  have hΓ2 : ∀ z : ℂ, z ≠ 0 → Complex.Gammaℝ (z + 2) = z / (2 * (Real.pi : ℂ)) * Complex.Gammaℝ z
    := by
    intro z hz; rw [Complex.Gammaℝ_add_two hz]; ring
  set bS : ZMod 2 := (e : ZMod 2) + (lS : ZMod 2) with hbS
  have hshift : ∀ (f : ℝ → ℂ) (c : ℝ) (L : ℂ), Tendsto f atTop (𝓝 L) → Tendsto (fun s : ℝ => f (s +
    c)) atTop (𝓝 L) :=
    fun f c L h => h.comp (tendsto_atTop_add_const_right _ c tendsto_id)
  have hshiftE : ∀ (P : ℝ → Prop) (c : ℝ), (∀ᶠ x : ℝ in atTop, P x) → ∀ᶠ s : ℝ in atTop, P (s + c)
    :=
    fun P c h => (tendsto_atTop_add_const_right _ c tendsto_id).eventually h
  set Mf : ℕ → ℕ → ℕ → ℝ → ℂ := fun p r j s =>
    mellin (H j (bS + (j : ZMod 2))) (((s + ((lS : ℝ) - 1 - 2 * p - 2 * r - j)) : ℝ) : ℂ) with hMf
  set Γf : ℕ → ℝ → ℂ := fun p s => Complex.Gammaℝ ((s : ℂ) + u₃ + (iS : ℂ) + 2 * (p : ℂ)) with hΓf
  set Rf : ℕ → ℕ → ℕ → ℝ → ℂ := fun p r j s => (Γf p s * Mf p r j s) / (Γf 0 s * Mf 0 0 0 s) with
    hRf
  set κf : ℕ → ℕ → ℕ → ℂ := fun p r j => if r = 0 ∧ j = 0 then ((a : ℂ) ^ 2) ^ p else 0 with hκf
  have hMf_ne : ∀ p r j : ℕ, ∀ᶠ s : ℝ in atTop, Mf p r j s ≠ 0 := by
    intro p r j
    simp only [hMf]
    exact hshiftE (fun x => mellin (H j (bS + (j : ZMod 2))) (x : ℂ) ≠ 0) _ (hNZ j _)
  have hΓf_ne : ∀ p : ℕ, ∀ᶠ s : ℝ in atTop, Γf p s ≠ 0 ∧ (s : ℂ) + u₃ + (iS : ℂ) + 2 * (p : ℂ) ≠ 0
    := by
    intro p
    filter_upwards [eventually_gt_atTop (-u₃.re)] with s hs
    have hre : 0 < ((s : ℂ) + u₃ + (iS : ℂ) + 2 * (p : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re, Complex.mul_re,
        Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero]
      have : (0 : ℝ) ≤ iS := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      linarith
    have hΓ : Γf p s ≠ 0 := by
      simp only [hΓf]
      exact Complex.Gammaℝ_ne_zero_of_re_pos hre
    exact ⟨hΓ, fun h => by rw [h, Complex.zero_re] at hre; exact lt_irrefl _ hre⟩
  have hC0 : Tendsto (Rf 0 0 0) atTop (𝓝 (κf 0 0 0)) := by
    have : κf 0 0 0 = 1 := by simp [hκf]
    rw [this]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hMf_ne 0 0 0, hΓf_ne 0] with s h1 h2
    have h3 : Γf 0 s * Mf 0 0 0 s ≠ 0 := mul_ne_zero h2.1 h1
    simp only [hRf, div_self h3]
  have hcst_j : ∀ p r j : ℕ, ((lS : ℝ) - 1 - 2 * p - 2 * r - ((j + 1 : ℕ) : ℝ)) = ((lS : ℝ) - 1 - 2
    * p - 2 * r - j) - 1 := by
    intro p r j; push_cast; ring
  have hcst_r : ∀ p r j : ℕ, ((lS : ℝ) - 1 - 2 * p - 2 * ((r + 1 : ℕ) : ℝ) - j) = ((lS : ℝ) - 1 - 2
    * p - 2 * r - j) - 2 := by
    intro p r j; push_cast; ring
  have hcst_p : ∀ p r j : ℕ, ((lS : ℝ) - 1 - 2 * ((p + 1 : ℕ) : ℝ) - 2 * r - j) = ((lS : ℝ) - 1 - 2
    * p - 2 * r - j) - 2 := by
    intro p r j; push_cast; ring
  have hTj : ∀ p r j : ℕ, Tendsto (fun s : ℝ => Mf p r (j + 1) s / Mf p r j s) atTop (𝓝 0) := by
    intro p r j
    have h := hshift _ ((lS : ℝ) - 1 - 2 * p - 2 * r - j) _ (hθ j (bS + (j : ZMod 2)) (bS + ((j + 1
      : ℕ) : ZMod 2)))
    refine h.congr' (Eventually.of_forall fun s => ?_)
    simp only [hMf, hcst_j]
    push_cast
    ring_nf
  have hAdiv : Tendsto (fun y : ℝ => A / (y : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : Tendsto (fun y : ℝ => ‖A‖ * y⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul ‖A‖
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy, div_eq_mul_inv]
  have hdown : ∀ (j : ℕ) (b : ZMod 2), Tendsto (fun y : ℝ => mellin (H j b) (y : ℂ) / mellin (H j
    b) ((y : ℂ) + 2)) atTop (𝓝 0) := by
    intro j b
    have h1 := (hρ j b).inv₀ one_ne_zero
    have h2 := hAdiv.mul h1
    rw [inv_one, zero_mul] at h2
    refine h2.congr' ?_
    filter_upwards [hNZ j b, eventually_gt_atTop (0 : ℝ), (tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_id).eventually (hNZ j b)] with y hM hy hM2
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hM2' : mellin (H j b) ((y : ℂ) + 2) ≠ 0 := by push_cast at hM2; exact hM2
    field_simp
  have hTr : ∀ p r j : ℕ, Tendsto (fun s : ℝ => Mf p (r + 1) j s / Mf p r j s) atTop (𝓝 0) := by
    intro p r j
    have h := hshift _ ((lS : ℝ) - 1 - 2 * p - 2 * r - j - 2) _ (hdown j (bS + (j : ZMod 2)))
    refine h.congr' (Eventually.of_forall fun s => ?_)
    simp only [hMf, hcst_r]
    push_cast
    ring_nf
  have hTp' : ∀ p r j : ℕ, Tendsto (fun s : ℝ => Mf (p + 1) r j s / Mf p r j s) atTop (𝓝 0) := by
    intro p r j
    have h := hshift _ ((lS : ℝ) - 1 - 2 * p - 2 * r - j - 2) _ (hdown j (bS + (j : ZMod 2)))
    refine h.congr' (Eventually.of_forall fun s => ?_)
    simp only [hMf, hcst_p]
    push_cast
    ring_nf
  have hcdiv : ∀ C : ℂ, Tendsto (fun y : ℝ => C / (y : ℂ)) atTop (𝓝 0) := by
    intro C
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : Tendsto (fun y : ℝ => ‖C‖ * y⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul ‖C‖
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy, div_eq_mul_inv]
  have hlin : ∀ (α : ℂ) (β : ℝ), Tendsto (fun s : ℝ => ((s : ℂ) + α) / (((s + β : ℝ)) : ℂ)) atTop
    (𝓝 1) := by
    intro α β
    have h := (hshift _ β _ (hcdiv (α - (β : ℂ)))).add_const 1
    rw [zero_add] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (-β)] with s hs
    have : (((s + β : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : s + β ≠ 0)
    field_simp
    push_cast
    ring
  have hTp : ∀ p r j : ℕ, Tendsto (fun s : ℝ => (Γf (p + 1) s / Γf p s) * (Mf (p + 1) r j s / Mf p
    r j s)) atTop (𝓝 ((a : ℂ) ^ 2)) := by
    intro p r j
    set c : ℝ := (lS : ℝ) - 1 - 2 * p - 2 * r - j with hc
    set b : ZMod 2 := bS + (j : ZMod 2) with hb
    have hmodel : Tendsto (fun s : ℝ => (a : ℂ) ^ 2 * ((((s : ℂ) + (u₃ + (iS : ℂ) + 2 * (p : ℂ))) /
      (((s + (c - 2) : ℝ)) : ℂ)) *
        (mellin (H j b) ((((s + (c - 2) : ℝ)) : ℂ) + 2) / (((((s + (c - 2) : ℝ)) : ℂ) / A) * mellin
          (H j b) (((s + (c - 2) : ℝ)) : ℂ)))⁻¹)) atTop (𝓝 ((a : ℂ) ^ 2)) := by
      have h1 := hlin (u₃ + (iS : ℂ) + 2 * (p : ℂ)) (c - 2)
      have h2 := (hshift _ (c - 2) _ (hρ j b)).inv₀ one_ne_zero
      have := (h1.mul h2).const_mul ((a : ℂ) ^ 2)
      rw [inv_one, mul_one, mul_one] at this
      exact this
    refine hmodel.congr' ?_
    filter_upwards [hΓf_ne p, hshiftE _ (c - 2) (hNZ j b), hshiftE _ c (hNZ j b),
      eventually_gt_atTop (2 - c)] with s hz hM hM0 hs
    have hy0 : (((s + (c - 2) : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : s + (c - 2) ≠ 0)
    have hM2 : mellin (H j b) ((((s + (c - 2) : ℝ)) : ℂ) + 2) ≠ 0 := by
      have : ((((s + (c - 2) : ℝ)) : ℂ) + 2) = (((s + c : ℝ)) : ℂ) := by push_cast; ring
      rw [this]; exact hM0
    have hΓ : Γf (p + 1) s = ((s : ℂ) + u₃ + (iS : ℂ) + 2 * (p : ℂ)) / (2 * (Real.pi : ℂ)) * Γf p s
      := by
      have harg : ((s : ℂ) + u₃ + (iS : ℂ) + 2 * ((p + 1 : ℕ) : ℂ)) = ((s : ℂ) + u₃ + (iS : ℂ) + 2
        * (p : ℂ)) + 2 := by push_cast; ring
      simp only [hΓf]
      rw [harg, hΓ2 _ hz.2]
    have hMp1 : Mf (p + 1) r j s = mellin (H j b) (((s + (c - 2) : ℝ)) : ℂ) := by
      simp only [hMf, hb, hc, hcst_p]
    have hMp : Mf p r j s = mellin (H j b) ((((s + (c - 2) : ℝ)) : ℂ) + 2) := by
      simp only [hMf, hb, hc]; congr 1; push_cast; ring
    rw [hΓ, hMp1, hMp]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    have hΓ0 : Γf p s ≠ 0 := hz.1
    simp only [hAdef]
    field_simp
    ring
  have hD_ne : ∀ᶠ s : ℝ in atTop, Γf 0 s * Mf 0 0 0 s ≠ 0 := by
    filter_upwards [hΓf_ne 0, hMf_ne 0 0 0] with s h1 h2 using mul_ne_zero h1.1 h2
  have hEj : ∀ p r j : ℕ, ∀ᶠ s : ℝ in atTop, Rf p r (j + 1) s = Rf p r j s * (Mf p r (j + 1) s / Mf
    p r j s) := by
    intro p r j
    filter_upwards [hD_ne, hMf_ne p r j] with s hD hM
    simp only [hRf]
    field_simp
  have hEr : ∀ p r j : ℕ, ∀ᶠ s : ℝ in atTop, Rf p (r + 1) j s = Rf p r j s * (Mf p (r + 1) j s / Mf
    p r j s) := by
    intro p r j
    filter_upwards [hD_ne, hMf_ne p r j] with s hD hM
    simp only [hRf]
    field_simp
  have hEp : ∀ p r j : ℕ, ∀ᶠ s : ℝ in atTop, Rf (p + 1) r j s = Rf p r j s * ((Γf (p + 1) s / Γf p
    s) * (Mf (p + 1) r j s / Mf p r j s)) := by
    intro p r j
    filter_upwards [hD_ne, hMf_ne p r j, hΓf_ne p] with s hD hM hΓ
    have hΓ' := hΓ.1
    simp only [hRf]
    field_simp
  have hRj : ∀ j : ℕ, Tendsto (Rf 0 0 j) atTop (𝓝 (κf 0 0 j)) := by
    intro j
    induction j with
    | zero => exact hC0
    | succ j ih =>
      have h := ih.mul (hTj 0 0 j)
      rw [mul_zero] at h
      have hk : κf 0 0 (j + 1) = 0 := by simp [hκf]
      rw [hk]
      exact h.congr' ((hEj 0 0 j).mono fun s hs => hs.symm)
  have hRr : ∀ r j : ℕ, Tendsto (Rf 0 r j) atTop (𝓝 (κf 0 r j)) := by
    intro r
    induction r with
    | zero => exact hRj
    | succ r ih =>
      intro j
      have h := (ih j).mul (hTr 0 r j)
      rw [mul_zero] at h
      have hk : κf 0 (r + 1) j = 0 := by simp [hκf]
      rw [hk]
      exact h.congr' ((hEr 0 r j).mono fun s hs => hs.symm)
  have hRp : ∀ p r j : ℕ, Tendsto (Rf p r j) atTop (𝓝 (κf p r j)) := by
    intro p
    induction p with
    | zero => exact hRr
    | succ p ih =>
      intro r j
      have h := (ih r j).mul (hTp p r j)
      have hk : κf (p + 1) r j = κf p r j * (a : ℂ) ^ 2 := by
        simp only [hκf]; split_ifs <;> ring
      rw [hk]
      exact h.congr' ((hEp p r j).mono fun s hs => hs.symm)
  have hG₀ : ∀ᶠ s : ℝ in atTop, G TS s ≠ 0 := by
    filter_upwards [hD_ne] with s hD
    have : G TS s = Γf 0 s * Mf 0 0 0 s := by
      simp only [hG, hΓf, hMf, hTS, hbS]
      congr 1
      · congr 1; push_cast; ring
      · congr 1
        · simp
        · push_cast; ring
    rw [this]; exact hD
  have hlim : ∀ T ∈ Adm, Tendsto (fun s : ℝ => G T s / G TS s) atTop (𝓝 (κ T)) := by
    intro T hT
    obtain ⟨-, hsum, hpar⟩ := Finset.mem_filter.1 hT
    have hpar' : T.1.2 % 2 = iS := by
      have h1 : ((T.1.2 : ℕ) : ZMod 2) = ((iS : ℕ) : ZMod 2) := by rw [hpar, hiSpar]
      have := (ZMod.natCast_eq_natCast_iff' T.1.2 iS 2).1 h1
      rw [this]; exact (Nat.mod_eq_of_lt hiS2)
    obtain ⟨p, hp⟩ : ∃ p, T.1.2 = iS + 2 * p := ⟨T.1.2 / 2, by omega⟩
    have hl : T.2.2 + 2 * p + 2 * T.1.1 + T.2.1 = lS := by omega
    have h2 : (T.1.2 - iS) / 2 = p := by omega
    have hκT : κ T = κf p T.1.1 T.2.1 := by simp only [hκ, hκf, h2]
    rw [hκT]
    refine (hRp p T.1.1 T.2.1).congr' (Eventually.of_forall fun s => ?_)
    have hsheet : (e : ZMod 2) + ((T.2.2 : ℕ) : ZMod 2) = bS + ((T.2.1 : ℕ) : ZMod 2) := by
      have hc := congrArg (Nat.cast : ℕ → ZMod 2) hl
      push_cast at hc
      have h2z : (2 : ZMod 2) = 0 := by decide
      simp only [hbS]
      linear_combination hc - (((p : ℕ) : ZMod 2) + ((T.1.1 : ℕ) : ZMod 2) + ((T.2.1 : ℕ) : ZMod
        2)) * h2z
    have hlR : ((T.2.2 : ℕ) : ℝ) = (lS : ℝ) - 2 * p - 2 * (T.1.1 : ℝ) - (T.2.1 : ℝ) := by
      have hc := congrArg (Nat.cast : ℕ → ℝ) hl
      push_cast at hc
      linarith
    have hiC : ((T.1.2 : ℕ) : ℂ) = (iS : ℂ) + 2 * (p : ℂ) := by rw [hp]; push_cast; ring
    simp only [hG, hRf, hΓf, hMf, hTS, hbS] at *
    congr 1
    · rw [hiC, hsheet]
      congr 1
      · congr 1; ring
      · congr 1
        push_cast
        rw [show ((T.2.2 : ℕ) : ℂ) = ((((T.2.2 : ℕ) : ℝ)) : ℂ) by norm_cast, hlR]
        push_cast; ring
    · congr 1
      · congr 1; push_cast; ring
      · congr 1
        · simp
        · push_cast; ring
  have hL : ∑ T ∈ Adm, d T * κ T ≠ 0 := by
    have hterm : ∀ T ∈ Adm, d T * κ T =
        ((-1 : ℂ) ^ lS * (m.factorial : ℂ) * (a : ℂ) ^ lS) *
          (if T.1.1 = 0 ∧ T.2.1 = 0 then (1 / ((T.1.2.factorial : ℂ) * (T.2.2.factorial : ℂ))) else
            0) := by
      intro T hT
      obtain ⟨-, hsum, hpar⟩ := Finset.mem_filter.1 hT
      simp only [hd, hκ, hermiteCoeff]
      split_ifs with h
      · obtain ⟨hr, hj⟩ := h
        have hpar' : T.1.2 % 2 = iS := by
          have h1 : ((T.1.2 : ℕ) : ZMod 2) = ((iS : ℕ) : ZMod 2) := by rw [hpar, hiSpar]
          have := (ZMod.natCast_eq_natCast_iff' T.1.2 iS 2).1 h1
          rw [this]; exact (Nat.mod_eq_of_lt hiS2)
        obtain ⟨p, hp⟩ : ∃ p, T.1.2 = iS + 2 * p := ⟨T.1.2 / 2, by omega⟩
        have hl : T.2.2 + 2 * p = lS := by omega
        have h2 : (T.1.2 - iS) / 2 = p := by omega
        rw [h2, hr, hj]
        have hl' : lS = T.2.2 + 2 * p := hl.symm
        rw [hl']
        simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, mul_one, zero_add, pow_add,
          pow_mul]
        have ha2 : ((a : ℂ) ^ 2) ^ p ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast ha))
        field_simp
        ring
      · simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast
      (Nat.factorial_ne_zero m))) (pow_ne_zero _ (by exact_mod_cast ha))) ?_
    apply sum_ne_zero_of_nonneg_re Adm _ TS hTS_mem
    · intro T _
      split_ifs
      · simp only [one_div, mul_inv_rev, mul_re, inv_re, natCast_re, normSq_natCast,
          div_self_mul_self', inv_im, natCast_im, neg_zero, zero_div, mul_zero, sub_zero]
        positivity
      · simp
    · simp only [hTS, and_self, ↓reduceIte, one_div, mul_inv_rev, mul_re, inv_re, natCast_re,
        normSq_natCast, div_self_mul_self', inv_im, natCast_im, neg_zero, zero_div, mul_zero,
        sub_zero]
      positivity
  have hev := eventually_sum_mul_ne_zero Adm d G atTop TS hG₀ κ hlim hL
  obtain ⟨s, hsσ, hs⟩ := ((eventually_gt_atTop σ₀).and hev).exists
  refine ⟨s, hsσ, ?_⟩
  have hsum : hermiteGammaMellinSum m a u₃ a₃ e H s = ∑ T ∈ Adm, d T * G T s :=
    Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
  rw [hsum]
  exact hs

end LanglandsTunnell
