/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.WeightedLaplacian
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.LinearAlgebra.Trace

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Effective conductance and Rayleigh's monotonicity law

For a finite multigraph with nonnegative edge weights (conductances) `w`, the effective
conductance between vertices `s` and `t` is the minimum energy
`xᵀ L x = ∑_e w_e (x(end₁ e) - x(end₂ e))²` of a potential `x` with `x(s) = 0` and `x(t) = 1`,
and the effective resistance is its reciprocal (D. A. Spielman, *Spectral and Algebraic Graph
Theory*, draft of 2 April 2025, Section 12.2). This energy definition avoids the pseudo-inverse; its
agreement with `(δ_s - δ_t)ᵀ L⁺ (δ_s - δ_t)` (Spielman, Section 12.1) is
`effectiveResistance_eq_sub_of_laplacian_mulVec`.

* `effectiveConductance_le_energy`: every admissible potential bounds the effective conductance;
* `effectiveConductance_mono`: Rayleigh's monotonicity law, lowering conductances cannot raise
  the effective conductance (Spielman, Theorem 12.3.1);
* `effectiveResistance_anti`: equivalently, raising resistances cannot lower an effective
  resistance;
* `effectiveResistance_eq_sub_of_laplacian_mulVec`: the effective resistance is the potential
  difference `v(s) - v(t)` of any solution of `L v = δ_s - δ_t`;
* `range_laplacian_eq_range_orientedIncidence`: with positive weights and no loops, `L` and the
  oriented incidence matrix have the same range;
* `sum_mul_effectiveResistance`: Foster's identity `∑_e w_e R_eff(e) = n - 1` for connected
  graphs.
-/

@[expose] public section

namespace EndpointMapMultigraph

open Matrix

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E] [Fintype V]
  (end₁ end₂ : E → V)

/-- **Effective conductance.** For edge weights `w`, the infimum of the Laplacian energy
`xᵀ L x` over all potentials `x` with `x s = 0` and `x t = 1`, i.e. twice the minimum spring
energy when `s` and `t` are held at distance one (D. A. Spielman, *Spectral and Algebraic Graph
Theory*, draft of 2 April 2025, Section 12.2, where it is written `C_eff(s, t)`). It is `0` when
`s = t`, where no potential is admissible. -/
noncomputable def effectiveConductance (w : E → ℝ) (s t : V) : ℝ :=
  sInf {q | ∃ x : V → ℝ, x s = 0 ∧ x t = 1 ∧ q = x ⬝ᵥ (laplacian end₁ end₂ w *ᵥ x)}

/-- **Effective resistance.** The reciprocal of the effective conductance (D. A. Spielman,
*Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Section 12.2,
`R_eff(s, t) = 1 / C_eff(s, t)`). With Lean's convention `0⁻¹ = 0` it is `0` when the effective
conductance vanishes, for instance between different connected components. -/
noncomputable def effectiveResistance (w : E → ℝ) (s t : V) : ℝ :=
  (effectiveConductance end₁ end₂ w s t)⁻¹

/-- The energies of admissible potentials are bounded below by `0` for nonnegative weights. -/
private theorem bddBelow_energies {w : E → ℝ} (hw : 0 ≤ w) (s t : V) :
    BddBelow {q | ∃ x : V → ℝ, x s = 0 ∧ x t = 1 ∧ q = x ⬝ᵥ (laplacian end₁ end₂ w *ᵥ x)} := by
  refine ⟨0, ?_⟩
  rintro q ⟨x, -, -, rfl⟩
  rw [dotProduct_mulVec_laplacian]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (hw e) (sq_nonneg _)

/-- **Effective conductance is nonnegative** for nonnegative weights. -/
theorem effectiveConductance_nonneg {w : E → ℝ} (hw : 0 ≤ w) (s t : V) :
    0 ≤ effectiveConductance end₁ end₂ w s t := by
  by_cases hne : {q | ∃ x : V → ℝ, x s = 0 ∧ x t = 1 ∧
      q = x ⬝ᵥ (laplacian end₁ end₂ w *ᵥ x)}.Nonempty
  · refine le_csInf hne ?_
    rintro q ⟨x, -, -, rfl⟩
    rw [dotProduct_mulVec_laplacian]
    exact Finset.sum_nonneg fun e _ => mul_nonneg (hw e) (sq_nonneg _)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [effectiveConductance, hne, Real.sInf_empty]

/-- **Every admissible potential bounds the effective conductance.** For nonnegative weights and
any `x` with `x s = 0` and `x t = 1`, `C_eff(s, t) ≤ xᵀ L x` (D. A. Spielman, *Spectral and
Algebraic Graph Theory*, draft of 2 April 2025, Section 12.2). -/
theorem effectiveConductance_le_energy {w : E → ℝ} (hw : 0 ≤ w) {s t : V} {x : V → ℝ}
    (hs : x s = 0) (ht : x t = 1) :
    effectiveConductance end₁ end₂ w s t ≤ x ⬝ᵥ (laplacian end₁ end₂ w *ᵥ x) :=
  csInf_le (bddBelow_energies end₁ end₂ hw s t) ⟨x, hs, ht, rfl⟩

/-- **Rayleigh's monotonicity law.** If `0 ≤ w ≤ w'` edgewise, then the effective conductance
between any two vertices for the weights `w` is at most that for `w'`: lowering conductances
(raising resistances) cannot increase an effective conductance (D. A. Spielman, *Spectral and
Algebraic Graph Theory*, draft of 2 April 2025, Theorem 12.3.1). -/
theorem effectiveConductance_mono {w w' : E → ℝ} (hw : 0 ≤ w) (hle : w ≤ w') (s t : V) :
    effectiveConductance end₁ end₂ w s t ≤ effectiveConductance end₁ end₂ w' s t := by
  by_cases hne : {q | ∃ x : V → ℝ, x s = 0 ∧ x t = 1 ∧
      q = x ⬝ᵥ (laplacian end₁ end₂ w' *ᵥ x)}.Nonempty
  · refine le_csInf hne ?_
    rintro q ⟨x, hs, ht, rfl⟩
    refine (effectiveConductance_le_energy end₁ end₂ hw hs ht).trans ?_
    rw [dotProduct_mulVec_laplacian, dotProduct_mulVec_laplacian]
    exact Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (hle e) (sq_nonneg _)
  · -- no admissible potential: this happens only when `s = t`
    have hst : s = t := by
      by_contra h
      apply hne
      classical
      exact ⟨_, fun v => if v = t then 1 else 0, by simp [h], by simp, rfl⟩
    subst hst
    have hempty : ∀ u : E → ℝ, {q | ∃ x : V → ℝ, x s = 0 ∧ x s = 1 ∧
        q = x ⬝ᵥ (laplacian end₁ end₂ u *ᵥ x)} = ∅ := by
      intro u
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro x h0 h1
      rw [h0] at h1
      exact absurd h1 zero_ne_one
    rw [effectiveConductance, effectiveConductance, hempty, hempty]

/-- **Rayleigh's monotonicity law for effective resistance.** If `0 ≤ w ≤ w'` edgewise and the
effective conductance between `s` and `t` is positive for `w`, then the effective resistance
between them for `w'` is at most that for `w`: raising resistances cannot decrease an effective
resistance (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, the
remark after Theorem 12.3.1). -/
theorem effectiveResistance_anti {w w' : E → ℝ} (hw : 0 ≤ w) (hle : w ≤ w') {s t : V}
    (hpos : 0 < effectiveConductance end₁ end₂ w s t) :
    effectiveResistance end₁ end₂ w' s t ≤ effectiveResistance end₁ end₂ w s t :=
  inv_anti₀ hpos (effectiveConductance_mono end₁ end₂ hw hle s t)

/-- For nonnegative weights, a vanishing Laplacian energy forces `L v = 0`. -/
private theorem laplacian_mulVec_eq_zero_of_energy_eq_zero {w : E → ℝ} (hw : 0 ≤ w) {v : V → ℝ}
    (h : v ⬝ᵥ (laplacian end₁ end₂ w *ᵥ v) = 0) : laplacian end₁ end₂ w *ᵥ v = 0 := by
  rw [dotProduct_mulVec_laplacian] at h
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun e _ => mul_nonneg (hw e) (sq_nonneg (v (end₁ e) - v (end₂ e))))).1 h
  have hWB : diagonal w *ᵥ (v ᵥ* orientedIncidence end₁ end₂) = 0 := by
    funext e
    rw [mulVec_diagonal, vecMul_orientedIncidence_apply, Pi.zero_apply]
    have he := hterm e (Finset.mem_univ e)
    rcases mul_eq_zero.1 he with h0 | h0
    · rw [h0, zero_mul]
    · rw [pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0, mul_zero]
  rw [laplacian, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, hWB,
    Matrix.mulVec_zero]

/-- **Effective resistance is a potential difference.** For nonnegative weights and distinct
vertices `s` and `t`, if the potentials `v` satisfy `L v = δ_s - δ_t` (one unit of current injected
at `s` and extracted at `t`), then the effective resistance between `s` and `t` is `v(s) - v(t)`,
and this number is positive. Equivalently `R_eff(s, t) = (δ_s - δ_t)ᵀ L⁺ (δ_s - δ_t)`, which is how
D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Section 12.1 defines
it; the computation of Section 12.2 shows that its reciprocal is the minimum energy `C_eff(s, t)`.
No connectivity hypothesis is needed: if `s` and `t` lie in different components, no such `v`
exists. -/
theorem effectiveResistance_eq_sub_of_laplacian_mulVec {w : E → ℝ} (hw : 0 ≤ w) {s t : V}
    (hst : s ≠ t) {v : V → ℝ}
    (hv : laplacian end₁ end₂ w *ᵥ v = Pi.single s 1 - Pi.single t 1) :
    effectiveResistance end₁ end₂ w s t = v s - v t ∧ 0 < v s - v t := by
  classical
  set L := laplacian end₁ end₂ w
  set r := v s - v t
  have hvLv : v ⬝ᵥ (L *ᵥ v) = r := by
    rw [hv, dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one]
  have hr0 : 0 ≤ r := by
    rw [← hvLv, dotProduct_mulVec_laplacian]
    exact Finset.sum_nonneg fun e _ => mul_nonneg (hw e) (sq_nonneg _)
  have hr : 0 < r := by
    refine lt_of_le_of_ne hr0 fun h => ?_
    have hL := laplacian_mulVec_eq_zero_of_energy_eq_zero end₁ end₂ hw (hvLv.trans h.symm)
    rw [hL] at hv
    have := congrFun hv s
    simp [hst] at this
  -- the optimal potential
  set xs : V → ℝ := r⁻¹ • (v s • (1 : V → ℝ) - v) with hxs
  have hLxs : L *ᵥ xs = -(r⁻¹ • (Pi.single s 1 - Pi.single t 1)) := by
    rw [hxs, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, laplacian_mulVec_one,
      smul_zero, zero_sub, hv, smul_neg]
  have hxs_s : xs s = 0 := by simp [hxs]
  have hxs_t : xs t = 1 := by
    simp only [hxs, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hr.ne'
  have hEs : xs ⬝ᵥ (L *ᵥ xs) = r⁻¹ := by
    rw [hLxs, dotProduct_neg, dotProduct_smul, dotProduct_sub, dotProduct_single,
      dotProduct_single, hxs_s, hxs_t, smul_eq_mul]
    ring
  -- every admissible potential has energy at least `r⁻¹`
  have hlow : ∀ x : V → ℝ, x s = 0 → x t = 1 → r⁻¹ ≤ x ⬝ᵥ (L *ᵥ x) := by
    intro x hx0 hx1
    set y := x - xs
    have hy : y ⬝ᵥ (L *ᵥ xs) = 0 := by
      rw [hLxs, dotProduct_neg, dotProduct_smul, dotProduct_sub, dotProduct_single,
        dotProduct_single]
      simp [y, hx0, hx1, hxs_s, hxs_t]
    have hsym : xs ⬝ᵥ (L *ᵥ y) = y ⬝ᵥ (L *ᵥ xs) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, laplacian_transpose,
        dotProduct_comm]
    have hyy : 0 ≤ y ⬝ᵥ (L *ᵥ y) := by
      rw [dotProduct_mulVec_laplacian]
      exact Finset.sum_nonneg fun e _ => mul_nonneg (hw e) (sq_nonneg _)
    have hx : x = xs + y := by simp [y]
    rw [hx, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hsym, hy,
      hEs]
    linarith
  have hC : effectiveConductance end₁ end₂ w s t = r⁻¹ := by
    refine le_antisymm ?_ ?_
    · rw [← hEs]
      exact effectiveConductance_le_energy end₁ end₂ hw hxs_s hxs_t
    · refine le_csInf ⟨_, xs, hxs_s, hxs_t, rfl⟩ ?_
      rintro q ⟨x, hx0, hx1, rfl⟩
      exact hlow x hx0 hx1
  refine ⟨?_, hr⟩
  rw [effectiveResistance, hC, inv_inv]

/-- **Range of the weighted Laplacian.** For a finite loopless multigraph with positive weights,
the weighted Laplacian `L = B diag(w) Bᵀ` and the oriented incidence matrix `B` have the same range:
every net outflow `B θ` of an edge function is the net outflow `L v = B (w · Bᵀ v)` of the current
of some potential `v`. This is the existence part of R. Lyons and Y. Peres, *Probability on Trees
and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026,
Section 2.4, equation (2.9) and the note after Thomson's principle: for every flow `θ` the current
`i = P_⋆ θ` satisfies `d* i = d* θ`. The proof here compares ranks instead
(`rank L = rank B = |V| - #components`). -/
theorem range_laplacian_eq_range_orientedIncidence {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (hloop : ∀ e, end₁ e ≠ end₂ e) :
    LinearMap.range (laplacian end₁ end₂ w).mulVecLin =
      LinearMap.range (orientedIncidence end₁ end₂).mulVecLin := by
  have hle : LinearMap.range (laplacian end₁ end₂ w).mulVecLin ≤
      LinearMap.range (orientedIncidence end₁ end₂).mulVecLin := by
    rw [laplacian, Matrix.mul_assoc, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have h1 := rank_laplacian_add_card_connectedComponent end₁ end₂ hw hloop
  have h2 := rank_orientedIncidence_add_card_connectedComponent end₁ end₂ hloop
  change (laplacian end₁ end₂ w).rank = (orientedIncidence end₁ end₂).rank
  omega

/-- **Foster's identity.** In a connected loopless multigraph with positive weights on `n`
vertices, `∑_e w_e R_eff(e) = n - 1`. The proof follows Spielman and Srivastava, *Graph
sparsification by effective resistances*, SIAM J. Comput. 40 (2011), arXiv:0803.0929,
Lemma 3(iii) and the identity `∑_e w_e R_e = Tr(Π) = n - 1` in the proof of Theorem 1: the
numbers `w_e R_eff(e)` are the diagonal of an idempotent matrix (there
`W^{1/2} B L⁺ Bᵀ W^{1/2}`, here `Bᵀ P W` for any `P` with `L P = B`) whose rank is that of the
incidence matrix, `n - 1`. -/
theorem sum_mul_effectiveResistance {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (hloop : ∀ e, end₁ e ≠ end₂ e) (hconn : (underlyingGraph end₁ end₂).Connected) :
    ∑ e, w e * effectiveResistance end₁ end₂ w (end₁ e) (end₂ e) = (Fintype.card V : ℝ) - 1 := by
  classical
  have hw0 : 0 ≤ w := fun e => (hw e).le
  set B := orientedIncidence end₁ end₂
  set L := laplacian end₁ end₂ w
  -- potentials for a unit current across each edge
  have hex : ∀ e, ∃ v : V → ℝ, L *ᵥ v = B *ᵥ Pi.single e 1 := by
    intro e
    have hmem : B *ᵥ Pi.single e 1 ∈ LinearMap.range L.mulVecLin := by
      rw [range_laplacian_eq_range_orientedIncidence end₁ end₂ hw hloop]
      exact ⟨Pi.single e 1, rfl⟩
    obtain ⟨v, hv⟩ := hmem
    exact ⟨v, hv⟩
  choose v hv using hex
  have hcol : ∀ e, B *ᵥ Pi.single e 1 = Pi.single (end₁ e) 1 - Pi.single (end₂ e) 1 := by
    intro e
    funext u
    rw [Matrix.mulVec_single_one]
    simp [B, orientedIncidence_apply, Pi.single_apply, eq_comm]
  have hR : ∀ e, effectiveResistance end₁ end₂ w (end₁ e) (end₂ e) =
      v e (end₁ e) - v e (end₂ e) := fun e =>
    (effectiveResistance_eq_sub_of_laplacian_mulVec end₁ end₂ hw0 (hloop e)
      ((hv e).trans (hcol e))).1
  -- the matrix of potentials
  set P : Matrix V E ℝ := Matrix.of fun u e => v e u
  have hLP : L * P = B := by
    ext u e
    have := congrFun (hv e) u
    rw [Matrix.mulVec_single_one] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, P] using this
  set N : Matrix E E ℝ := Bᵀ * P * diagonal w
  have hdiag : ∀ e, (Bᵀ * P) e e = v e (end₁ e) - v e (end₂ e) := by
    intro e
    have := vecMul_orientedIncidence_apply end₁ end₂ (v e) e
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, P, B, mul_comm] using this
  have htrace : N.trace = ∑ e, w e * effectiveResistance end₁ end₂ w (end₁ e) (end₂ e) := by
    simp only [N, Matrix.trace, Matrix.diag, Matrix.mul_diagonal, hdiag, hR]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  -- `Bᵀ` kills every matrix whose columns lie in the kernel of `L`
  have hkill : ∀ Z : Matrix V E ℝ, L * Z = 0 → Bᵀ * Z = 0 := by
    intro Z hZ
    ext e f
    have hcolZ : L *ᵥ (fun u => Z u f) = 0 := by
      funext u
      have := congrFun (congrFun hZ u) f
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    have hconst := (laplacian_mulVec_eq_zero_iff end₁ end₂ hw hloop _).1 hcolZ
    have hB := (vecMul_orientedIncidence_eq_zero_iff end₁ end₂ hloop _).2 hconst
    have := congrFun hB e
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, B, mul_comm] using this
  have hBWB : B * diagonal w * Bᵀ = L := rfl
  have hidem : N * N = N := by
    have hZ : L * (P * diagonal w * Bᵀ * P - P) = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hLP,
        hBWB, hLP, sub_self]
    have h := hkill _ hZ
    rw [Matrix.mul_sub, sub_eq_zero] at h
    calc N * N = (Bᵀ * (P * diagonal w * Bᵀ * P)) * diagonal w := by
          simp only [N, Matrix.mul_assoc]
      _ = N := by rw [h]
  -- the rank of `N` is that of `B`
  have hrankB : B.rank = Fintype.card V - 1 := by
    have h := rank_orientedIncidence_add_card_connectedComponent end₁ end₂ hloop
    have hc : Nat.card (underlyingGraph end₁ end₂).ConnectedComponent = 1 := by
      have := hconn.nonempty
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨hconn.preconnected.subsingleton_connectedComponent, inferInstance⟩
    rw [hc] at h
    change B.rank + 1 = _ at h
    omega
  have hD : IsUnit (diagonal w).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun e _ => (hw e).ne'
  have hrankN : N.rank = B.rank := by
    refine le_antisymm ?_ ?_
    · calc N.rank ≤ Bᵀ.rank := by simp only [N, Matrix.mul_assoc]; exact Matrix.rank_mul_le_left _ _
        _ = B.rank := Matrix.rank_transpose _
    · have hBWN : B * diagonal w * N = B * diagonal w := by
        simp only [N]
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBWB, hLP]
      calc B.rank = (B * diagonal w).rank := (Matrix.rank_mul_eq_left_of_isUnit_det _ _ hD).symm
        _ = (B * diagonal w * N).rank := by rw [hBWN]
        _ ≤ N.rank := Matrix.rank_mul_le_right _ _
  -- trace of an idempotent is its rank
  have hidemLin : IsIdempotentElem (Matrix.toLin' N) := by
    change Matrix.toLin' N * Matrix.toLin' N = Matrix.toLin' N
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hidem]
  have htr := LinearMap.IsProj.trace (LinearMap.IsIdempotentElem.isProj_range _ hidemLin)
  rw [Matrix.trace_toLin'_eq] at htr
  have hNrank : Module.finrank ℝ (LinearMap.range (Matrix.toLin' N)) = N.rank := rfl
  rw [← htrace, htr, hNrank, hrankN, hrankB]
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 hconn.nonempty
  push_cast [Nat.cast_sub hpos]
  ring

end EndpointMapMultigraph
