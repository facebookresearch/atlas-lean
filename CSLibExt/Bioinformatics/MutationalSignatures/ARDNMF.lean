/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# ARD-NMF (SignatureAnalyzer): monotone updates, the relevance update, and pruning

SignatureAnalyzer (Kim et al. 2016) extracts mutational signatures with the Bayesian NMF of
Tan and Févotte (2013): `V ≈ W H` with `W : F × K` and `H : K × N` nonnegative, the `k`-th
column of `W` and row of `H` sharing a relevance (scale) parameter `λ_k` with an inverse-gamma
prior `IG(a, b)`. With dispersion `φ > 0` and exponential (`ℓ₁`) priors, the negative log
posterior is (Tan–Févotte, Eq. 20)

`C(W, H, λ) = D_β(V | W H) / φ + ∑ k, (‖w_k‖₁ + ‖h_k‖₁ + b) / λ_k + c log λ_k + const`,

with `c = F + N + a + 1`. This file treats the Kullback–Leibler case `β = 1`
(`d(x | y) = x log (x / y) - x + y`), where the `ℓ₁`-ARD update of `H` is
`h_kn ← h_kn (∑_f w_fk v_fn / (W H)_fn) / (∑_f w_fk + φ / λ_k)` (Tan–Févotte, Eq. 32 and
Algorithm 2, `γ(1) = 1`); the `W` update is the same after transposition.

## Main results

* `objectiveH_updateH_le`: the `H` update does not increase the `H`-dependent part
  `D_1(V | W H) / φ + ∑_{k,n} h_kn / λ_k` of `C` (majorization–minimization).
* `objectiveW_updateW_le`: the same for the `W` update.
* `relevance_isMinOn`: the relevance update `λ_k = (‖w_k‖₁ + ‖h_k‖₁ + b) / c` (Eq. 33)
  minimizes `λ ↦ A / λ + c log λ` over `λ > 0`, uniquely (`relevance_unique`).
* `relevance_eq_floor_iff`: `λ_k ≥ b / c`, with equality exactly when the `k`-th column of `W`
  and row of `H` vanish (the pruned components of Tan–Févotte §IV-D).
* `updateH_eq_zero`, `updateW_eq_zero`: the multiplicative updates keep a zero entry at zero,
  so a pruned component stays pruned.

Out of scope: `β ≠ 1`, the half-normal (`ℓ₂`) prior, convergence of the iterates, and the
choice of `b`. The step lemmas assume strictly positive current factors; an update can create
zero entries, so chaining them along a full run needs that positivity re-established (or the
zero entries pruned) at each step.

## References

* V. Y. F. Tan, C. Févotte, *Automatic relevance determination in nonnegative matrix
  factorization with the β-divergence*, IEEE Trans. Pattern Anal. Mach. Intell. 35 (2013),
  1592–1605 (Eqs. 20, 32, 33, Algorithm 2).
* J. Kim et al., *Somatic ERCC2 mutations are associated with a distinct genomic signature in
  urothelial tumors*, Nat. Genet. 48 (2016), 600–606 (SignatureAnalyzer).
* D. D. Lee, H. S. Seung, *Algorithms for non-negative matrix factorization*, NIPS 13 (2001)
  (the KL auxiliary function).
-/

@[expose] public section

namespace Cslib.Bioinformatics.MutationalSignatures.ARDNMF

variable {F K N : Type*} [Fintype F] [Fintype K] [Fintype N]

/-- The Kullback–Leibler `β = 1` divergence `d(x | y) = x log (x / y) - x + y` (Tan–Févotte,
Eq. 4). With Mathlib's `0 * log _ = 0` it gives `d(0 | y) = y`, the correct value; `y > 0` is
needed when `x > 0`. -/
noncomputable def klDiv (x y : ℝ) : ℝ := x * Real.log (x / y) - x + y

/-- The reconstruction `(W H)_fn = ∑_k w_fk h_kn`. -/
def recon (W : F → K → ℝ) (H : K → N → ℝ) (f : F) (n : N) : ℝ := ∑ k, W f k * H k n

/-- The data-fit term `D_1(V | W H) = ∑_{f,n} d(v_fn | (W H)_fn)`. -/
noncomputable def dataFit (V : F → N → ℝ) (W : F → K → ℝ) (H : K → N → ℝ) : ℝ :=
  ∑ f, ∑ n, klDiv (V f n) (recon W H f n)

/-- The `H`-dependent part `D_1(V | W H) / φ + ∑_{k,n} h_kn / λ_k` of the `ℓ₁`-ARD objective
(Tan–Févotte, Eq. 20, `β = 1`). -/
noncomputable def objectiveH (φ : ℝ) (V : F → N → ℝ) (W : F → K → ℝ) (lam : K → ℝ)
    (H : K → N → ℝ) : ℝ :=
  dataFit V W H / φ + ∑ k, ∑ n, H k n / lam k

/-- The `ℓ₁`-ARD multiplicative update of `H` for `β = 1` (Tan–Févotte, Eq. 32, Algorithm 2):
`h_kn ← h_kn (∑_f w_fk v_fn / (W H)_fn) / (∑_f w_fk + φ / λ_k)`. -/
noncomputable def updateH (φ : ℝ) (V : F → N → ℝ) (W : F → K → ℝ) (lam : K → ℝ)
    (H : K → N → ℝ) (k : K) (n : N) : ℝ :=
  H k n * (∑ f, W f k * V f n / recon W H f n) / (∑ f, W f k + φ / lam k)

private theorem weighted_log {ι : Type*} [Fintype ι] (a r : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    (hs : ∀ i, 0 < a i → 0 < r i)
    (hm : 0 < ∑ i, a i * r i) :
    ∑ i, a i * Real.log (r i) ≤ Real.log (∑ i, a i * r i) := by
  classical
  set m := ∑ i, a i * r i
  have hterm : ∀ i, a i * Real.log (r i) - a i * Real.log m
      ≤ a i * (r i / m - 1) := by
    intro i
    rcases (ha i).eq_or_lt with h | h
    · simp [← h]
    · rw [← mul_sub, ← Real.log_div (hs i h).ne' hm.ne']
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos (hs i h) hm)) (ha i)
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib] at hsum
  simp only [← mul_div_assoc, ← Finset.sum_div, ← Finset.sum_mul, ha1, one_mul] at hsum
  change (∑ i, a i * Real.log (r i)) - Real.log m ≤ m / m - 1 at hsum
  rw [div_self hm.ne'] at hsum
  linarith

private theorem scalar_update {p d : ℝ} (hp : 0 ≤ p) (hd : 0 < d) :
    d * (p / d - 1) - p * Real.log (p / d) ≤ 0 := by
  rcases hp.eq_or_lt with h | h
  · simp [← h, hd.le]
  · have hlog := Real.log_le_sub_one_of_pos (div_pos hd h)
    rw [Real.log_div hd.ne' h.ne', Real.log_div h.ne' hd.ne'] at *
    have hmul := mul_le_mul_of_nonneg_left hlog hp
    have hcancel : p * (d / p - 1) = d - p := by field_simp
    rw [hcancel] at hmul
    have hcancel' : d * (p / d - 1) = p - d := by field_simp
    rw [hcancel']
    nlinarith

private theorem kl_majorize {ι : Type*} [Fintype ι] (a r : ι → ℝ) {v : ℝ}
    (hv : 0 ≤ v) (ha : ∀ i, 0 ≤ a i) (hy : 0 < ∑ i, a i)
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ i, 0 < v → 0 < a i → 0 < r i) :
    (v * Real.log (v / (∑ i, a i * r i)) - v + ∑ i, a i * r i) -
      (v * Real.log (v / (∑ i, a i)) - v + ∑ i, a i) ≤
      (∑ i, a i * (r i - 1)) - v * ∑ i, (a i / (∑ j, a j)) * Real.log (r i) := by
  classical
  have hlin : ∑ i, a i * (r i - 1) = (∑ i, a i * r i) - ∑ i, a i := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [hlin]
  rcases hv.eq_or_lt with h | h
  · simp [← h]
  · have hz : 0 < ∑ i, a i * r i := by
      obtain ⟨i, hi, hai⟩ :=
        (Finset.sum_pos_iff_of_nonneg (fun i _ => ha i)).mp hy
      exact Finset.sum_pos' (fun i _ => mul_nonneg (ha i) (hr i))
        ⟨i, hi, mul_pos hai (hs i h hai)⟩
    have hnorm : ∑ i, a i / (∑ j, a j) = 1 := by
      rw [← Finset.sum_div, div_self hy.ne']
    have hmean : ∑ i, a i / (∑ j, a j) * r i =
        (∑ i, a i * r i) / (∑ i, a i) := by
      simp only [div_mul_eq_mul_div, Finset.sum_div]
    have hlog := weighted_log (fun i => a i / (∑ j, a j)) r
      (fun i => div_nonneg (ha i) hy.le) hnorm
      (fun i hi => hs i h ((div_pos_iff_of_pos_right hy).mp hi))
      (by rw [hmean]; exact div_pos hz hy)
    rw [hmean, Real.log_div hz.ne' hy.ne'] at hlog
    rw [Real.log_div h.ne' hz.ne', Real.log_div h.ne' hy.ne']
    have := mul_le_mul_of_nonneg_left hlog hv
    nlinarith

private theorem column_descent {ι κ : Type*} [Fintype ι] [Fintype κ]
    {φ : ℝ} (v : ι → ℝ) (w : ι → κ → ℝ) (lam h : κ → ℝ)
    (hφ : 0 < φ) (hlam : ∀ k, 0 < lam k) (hv : ∀ f, 0 ≤ v f)
    (hw : ∀ f k, 0 ≤ w f k) (hh : ∀ k, 0 < h k)
    (hy : ∀ f, 0 < ∑ k, w f k * h k) :
    let u := fun k => h k * (∑ f, w f k * v f / (∑ j, w f j * h j)) /
      (∑ f, w f k + φ / lam k)
    (∑ f, klDiv (v f) (∑ k, w f k * u k)) + φ * ∑ k, u k / lam k ≤
      (∑ f, klDiv (v f) (∑ k, w f k * h k)) + φ * ∑ k, h k / lam k := by
  classical
  let y := fun f => ∑ k, w f k * h k
  let p := fun k => ∑ f, w f k * v f / y f
  let d := fun k => ∑ f, w f k + φ / lam k
  let r := fun k => p k / d k
  have hp : ∀ k, 0 ≤ p k := fun k =>
    Finset.sum_nonneg fun f _ => div_nonneg (mul_nonneg (hw f k) (hv f)) (hy f).le
  have hd : ∀ k, 0 < d k := fun k =>
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun f _ => hw f k)
      (div_pos hφ (hlam k))
  have hr : ∀ k, 0 ≤ r k := fun k => div_nonneg (hp k) (hd k).le
  have hs : ∀ f k, 0 < v f → 0 < w f k * h k → 0 < r k := by
    intro f k hvf hwk
    have hwk' : 0 < w f k := (mul_pos_iff_of_pos_right (hh k)).mp hwk
    have hpf : 0 < w f k * v f / y f := div_pos (mul_pos hwk' hvf) (hy f)
    have hpk : 0 < p k := hpf.trans_le
      (Finset.single_le_sum
        (fun g _ => div_nonneg (mul_nonneg (hw g k) (hv g)) (hy g).le)
        (Finset.mem_univ f))
    exact div_pos hpk (hd k)
  have hrow : ∀ f,
      klDiv (v f) (∑ k, w f k * (h k * r k)) - klDiv (v f) (y f) ≤
        ∑ k, h k * (w f k * (r k - 1) - (w f k * v f / y f) * Real.log (r k)) := by
    intro f
    have hb := kl_majorize (fun k => w f k * h k) r (hv f)
      (fun k => mul_nonneg (hw f k) (hh k).le) (hy f) hr (hs f)
    change klDiv (v f) (∑ k, w f k * h k * r k) - klDiv (v f) (y f) ≤ _ at hb
    calc
      _ = klDiv (v f) (∑ k, w f k * h k * r k) - klDiv (v f) (y f) := by
        simp only [mul_assoc]
      _ ≤ _ := hb
      _ = _ := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        dsimp [y]
        ring
  have hsum := Finset.sum_le_sum fun f (_ : f ∈ Finset.univ) => hrow f
  have hbound :
      (∑ f, klDiv (v f) (∑ k, w f k * (h k * r k))) -
        (∑ f, klDiv (v f) (y f)) ≤
        ∑ k, h k * ((∑ f, w f k) * (r k - 1) - p k * Real.log (r k)) := by
    calc
      _ ≤ ∑ f, ∑ k,
          h k * (w f k * (r k - 1) - (w f k * v f / y f) * Real.log (r k)) := by
        simpa only [Finset.sum_sub_distrib] using hsum
      _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.mul_sum]
        simp only [p, Finset.sum_sub_distrib, Finset.sum_mul]
  have hcoord : ∑ k, h k * (d k * (r k - 1) - p k * Real.log (r k)) ≤ 0 :=
    Finset.sum_nonpos fun k _ =>
      mul_nonpos_of_nonneg_of_nonpos (hh k).le (scalar_update (hp k) (hd k))
  have hcombine :
      (∑ k, h k * ((∑ f, w f k) * (r k - 1) - p k * Real.log (r k))) +
        φ * ((∑ k, (h k * r k) / lam k) - ∑ k, h k / lam k) =
      ∑ k, h k * (d k * (r k - 1) - p k * Real.log (r k)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp [d]
    ring
  have htotal := add_le_add hbound
    (le_refl (φ * ((∑ k, (h k * r k) / lam k) - ∑ k, h k / lam k)))
  rw [hcombine] at htotal
  have hfinal := htotal.trans hcoord
  have hresult : (∑ f, klDiv (v f) (∑ k, w f k * (h k * r k))) +
      φ * ∑ k, (h k * r k) / lam k ≤
      (∑ f, klDiv (v f) (y f)) + φ * ∑ k, h k / lam k := by
    linarith
  change (∑ f, klDiv (v f) (∑ k, w f k * (h k * p k / d k))) +
    φ * ∑ k, (h k * p k / d k) / lam k ≤ _
  simpa only [r, mul_div_assoc] using hresult

/-- **The `H` update is monotone** (Tan–Févotte 2013, §IV-B, `β = 1`): it does not increase
`D_1(V | W H) / φ + ∑ h_kn / λ_k`, for `φ > 0`, `λ > 0`, `V ≥ 0`, `W ≥ 0` with no zero row, and
`H > 0` entrywise. -/
theorem objectiveH_updateH_le {φ : ℝ} {V : F → N → ℝ} {W : F → K → ℝ} {lam : K → ℝ}
    {H : K → N → ℝ} (hφ : 0 < φ) (hlam : ∀ k, 0 < lam k) (hV : ∀ f n, 0 ≤ V f n)
    (hW : ∀ f k, 0 ≤ W f k) (hWrow : ∀ f, ∃ k, 0 < W f k) (hH : ∀ k n, 0 < H k n) :
    objectiveH φ V W lam (updateH φ V W lam H) ≤ objectiveH φ V W lam H := by
  classical
  have hy : ∀ f n, 0 < recon W H f n := by
    intro f n
    obtain ⟨k, hk⟩ := hWrow f
    exact (mul_pos hk (hH k n)).trans_le
      (Finset.single_le_sum (fun j _ => mul_nonneg (hW f j) (hH j n).le)
        (Finset.mem_univ k))
  have hn : ∀ n,
      (∑ f, klDiv (V f n) (recon W (updateH φ V W lam H) f n)) +
        φ * ∑ k, updateH φ V W lam H k n / lam k ≤
      (∑ f, klDiv (V f n) (recon W H f n)) + φ * ∑ k, H k n / lam k := by
    intro n
    exact column_descent (fun f => V f n) W lam (fun k => H k n)
      hφ hlam (fun f => hV f n) hW (fun k => hH k n) (fun f => hy f n)
  have hsum := Finset.sum_le_sum fun n (_ : n ∈ Finset.univ) => hn n
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [Finset.sum_comm (f := fun n f => klDiv (V f n)
      (recon W (updateH φ V W lam H) f n)),
    Finset.sum_comm (f := fun n f => klDiv (V f n) (recon W H f n)),
    Finset.sum_comm (f := fun n k => updateH φ V W lam H k n / lam k),
    Finset.sum_comm (f := fun n k => H k n / lam k)] at hsum
  have hscaled : φ * objectiveH φ V W lam (updateH φ V W lam H) ≤
      φ * objectiveH φ V W lam H := by
    simpa only [objectiveH, dataFit, mul_add, mul_div_cancel₀ _ hφ.ne'] using hsum
  nlinarith

/-- The `W`-dependent part `D_1(V | W H) / φ + ∑_{f,k} w_fk / λ_k` of the `ℓ₁`-ARD objective
(Tan–Févotte, Eq. 20, `β = 1`). -/
noncomputable def objectiveW (φ : ℝ) (V : F → N → ℝ) (H : K → N → ℝ) (lam : K → ℝ)
    (W : F → K → ℝ) : ℝ :=
  dataFit V W H / φ + ∑ k, ∑ f, W f k / lam k

/-- The `ℓ₁`-ARD multiplicative update of `W` for `β = 1` (Tan–Févotte, Algorithm 2):
`w_fk ← w_fk (∑_n v_fn h_kn / (W H)_fn) / (∑_n h_kn + φ / λ_k)`. -/
noncomputable def updateW (φ : ℝ) (V : F → N → ℝ) (H : K → N → ℝ) (lam : K → ℝ)
    (W : F → K → ℝ) (f : F) (k : K) : ℝ :=
  W f k * (∑ n, V f n * H k n / recon W H f n) / (∑ n, H k n + φ / lam k)

/-- **The `W` update is monotone**: it does not increase
`D_1(V | W H) / φ + ∑ w_fk / λ_k`, for `φ > 0`, `λ > 0`, `V ≥ 0`, `H ≥ 0` with no zero column,
and `W > 0` entrywise (the transpose of `objectiveH_updateH_le`). -/
theorem objectiveW_updateW_le {φ : ℝ} {V : F → N → ℝ} {H : K → N → ℝ} {lam : K → ℝ}
    {W : F → K → ℝ} (hφ : 0 < φ) (hlam : ∀ k, 0 < lam k) (hV : ∀ f n, 0 ≤ V f n)
    (hH : ∀ k n, 0 ≤ H k n) (hHcol : ∀ n, ∃ k, 0 < H k n) (hW : ∀ f k, 0 < W f k) :
    objectiveW φ V H lam (updateW φ V H lam W) ≤ objectiveW φ V H lam W := by
  have key := objectiveH_updateH_le (F := N) (N := F) (V := fun n f => V f n)
    (W := fun n k => H k n) (lam := lam) (H := fun k f => W f k) hφ hlam
    (fun n f => hV f n) (fun n k => hH k n) hHcol (fun k f => hW f k)
  have hrecon : ∀ (W' : F → K → ℝ) f n,
      recon (fun n k => H k n) (fun k f => W' f k) n f = recon W' H f n := fun W' f n => by
    unfold recon; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hfit : ∀ W' : F → K → ℝ,
      dataFit (fun n f => V f n) (fun n k => H k n) (fun k f => W' f k) = dataFit V W' H :=
    fun W' => by
      unfold dataFit
      rw [Finset.sum_comm]
      simp only [hrecon]
  have hupd : updateH φ (fun n f => V f n) (fun n k => H k n) lam (fun k f => W f k) =
      fun k f => updateW φ V H lam W f k := by
    funext k f
    unfold updateH updateW
    simp only [hrecon]
    congr 2
    exact Finset.sum_congr rfl fun n _ => by ring
  have e1 : objectiveH φ (fun n f => V f n) (fun n k => H k n) lam
      (updateH φ (fun n f => V f n) (fun n k => H k n) lam (fun k f => W f k)) =
      objectiveW φ V H lam (updateW φ V H lam W) := by
    unfold objectiveH objectiveW
    rw [hupd, hfit]
  have e2 : objectiveH φ (fun n f => V f n) (fun n k => H k n) lam (fun k f => W f k) =
      objectiveW φ V H lam W := by
    unfold objectiveH objectiveW
    rw [hfit]
  rwa [e1, e2] at key

/-- The relevance update `λ_k = (‖w_k‖₁ + ‖h_k‖₁ + b) / c` (Tan–Févotte, Eq. 33, `ℓ₁` prior;
`c = F + N + a + 1`). -/
noncomputable def relevance (W : F → K → ℝ) (H : K → N → ℝ) (b c : ℝ) (k : K) : ℝ :=
  (∑ f, W f k + ∑ n, H k n + b) / c

/-- **The relevance update is the exact minimizer** (Tan–Févotte, §IV-C): for `A > 0` and
`c > 0`, `λ ↦ A / λ + c log λ` attains its minimum over `λ > 0` at `λ = A / c`. -/
theorem relevance_isMinOn {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    IsMinOn (fun l => A / l + c * Real.log l) (Set.Ioi 0) (A / c) := by
  intro l hl
  have hl : 0 < l := hl
  have hu : 0 < A / (c * l) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hu
  have hsplit : Real.log (A / c) = Real.log (A / (c * l)) + Real.log l := by
    rw [← Real.log_mul hu.ne' hl.ne']; congr 1; field_simp
  change A / (A / c) + c * Real.log (A / c) ≤ A / l + c * Real.log l
  have e1 : A / (A / c) = c := by field_simp
  rw [hsplit, e1]
  have : c * (A / (c * l)) = A / l := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hlog hc.le]

/-- **The minimizer is unique**: if `λ > 0` does as well as `A / c`, then `λ = A / c`. -/
theorem relevance_unique {A c l : ℝ} (hA : 0 < A) (hc : 0 < c) (hl : 0 < l)
    (h : A / l + c * Real.log l ≤ A / (A / c) + c * Real.log (A / c)) : l = A / c := by
  by_contra hne
  have hu : 0 < A / (c * l) := by positivity
  have hu1 : A / (c * l) ≠ 1 := by
    intro h1
    apply hne
    rw [div_eq_one_iff_eq (by positivity)] at h1
    field_simp
    linarith
  have hlog := Real.log_lt_sub_one_of_pos hu hu1
  have hsplit : Real.log (A / c) = Real.log (A / (c * l)) + Real.log l := by
    rw [← Real.log_mul hu.ne' hl.ne']; congr 1; field_simp
  rw [hsplit] at h
  have e1 : A / (A / c) = c := by field_simp
  have : c * (A / (c * l)) = A / l := by field_simp
  nlinarith [mul_lt_mul_of_pos_left hlog hc]

omit [Fintype K] in
/-- The relevance never falls below its floor `b / c` (`W, H ≥ 0`, `c > 0`). -/
theorem div_le_relevance {W : F → K → ℝ} {H : K → N → ℝ} {b c : ℝ} (hc : 0 < c)
    (hW : ∀ f k, 0 ≤ W f k) (hH : ∀ k n, 0 ≤ H k n) (k : K) :
    b / c ≤ relevance W H b c k := by
  unfold relevance
  have h1 : 0 ≤ ∑ f, W f k := Finset.sum_nonneg fun f _ => hW f k
  have h2 : 0 ≤ ∑ n, H k n := Finset.sum_nonneg fun n _ => hH k n
  exact div_le_div_of_nonneg_right (by linarith) hc.le

omit [Fintype K] in
/-- **Pruning** (Tan–Févotte, §IV-D): the relevance equals its floor `b / c` exactly when the
`k`-th column of `W` and the `k`-th row of `H` are zero (`W, H ≥ 0`, `c > 0`). -/
theorem relevance_eq_floor_iff {W : F → K → ℝ} {H : K → N → ℝ} {b c : ℝ} (hc : 0 < c)
    (hW : ∀ f k, 0 ≤ W f k) (hH : ∀ k n, 0 ≤ H k n) (k : K) :
    relevance W H b c k = b / c ↔ (∀ f, W f k = 0) ∧ ∀ n, H k n = 0 := by
  unfold relevance
  rw [div_left_inj' hc.ne']
  have h1 : 0 ≤ ∑ f, W f k := Finset.sum_nonneg fun f _ => hW f k
  have h2 : 0 ≤ ∑ n, H k n := Finset.sum_nonneg fun n _ => hH k n
  constructor
  · intro h
    have e1 : ∑ f, W f k = 0 := by linarith
    have e2 : ∑ n, H k n = 0 := by linarith
    exact ⟨fun f => (Finset.sum_eq_zero_iff_of_nonneg fun f _ => hW f k).1 e1 f
        (Finset.mem_univ f),
      fun n => (Finset.sum_eq_zero_iff_of_nonneg fun n _ => hH k n).1 e2 n (Finset.mem_univ n)⟩
  · rintro ⟨hw, hh⟩
    simp [hw, hh]

omit [Fintype N] in
/-- **A pruned entry stays pruned**: the multiplicative update maps a zero entry of `H` to
zero. -/
theorem updateH_eq_zero (φ : ℝ) (V : F → N → ℝ) (W : F → K → ℝ) (lam : K → ℝ)
    {H : K → N → ℝ} {k : K} {n : N} (h : H k n = 0) : updateH φ V W lam H k n = 0 := by
  simp [updateH, h]

omit [Fintype F] in
/-- **A pruned entry stays pruned**: the multiplicative update maps a zero entry of `W` to
zero. -/
theorem updateW_eq_zero (φ : ℝ) (V : F → N → ℝ) (H : K → N → ℝ) (lam : K → ℝ)
    {W : F → K → ℝ} {f : F} {k : K} (h : W f k = 0) : updateW φ V H lam W f k = 0 := by
  simp [updateW, h]

end Cslib.Bioinformatics.MutationalSignatures.ARDNMF
