/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

arnovich/asgard-lean, commit
e5e098d5bce80c3907a6acd4e2beb904309a1709,
`Gimle/Asgard/Streams/Tail.lean`. Authors: arnovich.

MIT License

Copyright (c) 2025 Gimle Labs

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.GeometricMajorant
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity

/-!
# Absolute convergence and rectangular tails from coefficient majorants

A geometric bound on every rational coefficient gives absolute convergence on
strictly smaller closed polydiscs. The error after truncating to a coordinate
rectangle is bounded by an explicit rational geometric tail. Evaluation radii
are standard nonnegative rationals; zero radii and zero truncation lengths are
allowed. The dimension-zero case retains its single constant coefficient.

The sum is defined by tsum and does not claim convergence outside the stated
majorant hypotheses. No finite coefficient prefix alone is treated as evidence
of a bound on the remaining coefficients.

Mathematical reference: J. Lebl, Tasty Bits of Several Complex Variables,
version 3.4, Section 1.2, p. 17, https://www.jirka.org/scv/scv-3.4.pdf,
for the product geometric series and absolute convergence on smaller polydiscs.
The rectangular-tail formula is an elementary consequence derived here: bound
an omitted index by the sum of its coordinate-tail indicators and sum each
geometric tail. Overlapping coordinate tails make this a conservative bound.
No analyticity, differentiation, or reciprocal-evaluation theorem is asserted.
-/

@[expose] public section
namespace MvPowerSeries

private theorem hasSum_pi_prod_aux (d : Nat) : ∀ (f : Fin d → ℕ → ℝ) (s : Fin d → ℝ),
    (∀ i, Summable fun k => ‖f i k‖) → (∀ i, HasSum (f i) (s i)) →
    HasSum (fun k : Fin d → ℕ => ∏ i, f i (k i)) (∏ i, s i) ∧
      Summable fun k : Fin d → ℕ => ‖∏ i, f i (k i)‖ := by
  induction d with
  | zero =>
      intro f s _ _
      simp only [Finset.univ_eq_empty, Finset.prod_empty, norm_one]
      have h : HasSum (fun _ : Fin 0 → ℕ => (1 : ℝ)) 1 :=
        hasSum_single (f := fun _ : Fin 0 → ℕ => (1 : ℝ)) Fin.elim0
          (fun b ne => (ne (Subsingleton.elim _ _)).elim)
      exact ⟨h, h.summable⟩
  | succ d ih =>
      intro f s norms sums
      obtain ⟨hs, hn⟩ := ih (fun i => f i.succ) (fun i => s i.succ)
        (fun i => norms i.succ) (fun i => sums i.succ)
      let e : ℕ × (Fin d → ℕ) ≃ (Fin (d + 1) → ℕ) := Fin.consEquiv (fun _ => ℕ)
      have comp : ∀ p : ℕ × (Fin d → ℕ),
          (∏ i, f i (e p i)) = f 0 p.1 * ∏ i : Fin d, f i.succ (p.2 i) := by
        intro p
        rw [Fin.prod_univ_succ]
        rfl
      have prod := (sums 0).mul hs (summable_mul_of_summable_norm (R := ℝ) (f := f 0)
        (g := fun k : Fin d → ℕ => ∏ i : Fin d, f i.succ (k i)) (norms 0) hn)
      have prodn : Summable fun p : ℕ × (Fin d → ℕ) =>
          ‖f 0 p.1‖ * ‖∏ i : Fin d, f i.succ (p.2 i)‖ :=
        summable_mul_of_summable_norm (f := fun k => ‖f 0 k‖)
          (g := fun k : Fin d → ℕ => ‖∏ i : Fin d, f i.succ (k i)‖)
          (by simpa using norms 0) (by simpa using hn)
      refine ⟨?_, ?_⟩
      · rw [Fin.prod_univ_succ, ← e.hasSum_iff]
        exact prod.congr_fun fun p => comp p
      · rw [← e.summable_iff]
        refine prodn.congr fun p => ?_
        simp only [Function.comp_apply, comp p, norm_mul]

/-- A finite product of absolutely summable one-axis families is summable over
multi-indices, to the product of the sums. -/
private theorem hasSum_index_prod {d : Nat} (f : Fin d → ℕ → ℝ) (s : Fin d → ℝ)
    (norms : ∀ i, Summable fun k => ‖f i k‖) (sums : ∀ i, HasSum (f i) (s i)) :
    HasSum (fun α : (Fin d →₀ ℕ) => ∏ i, f i (α i)) (∏ i, s i) := by
  rw [← (Finsupp.equivFunOnFinite (α := Fin d) (M := ℕ)).symm.hasSum_iff]
  exact (hasSum_pi_prod_aux d f s norms sums).1

private theorem hasSum_geometric_index {d : Nat} (q : Fin d → ℝ) (h0 : ∀ i, 0 ≤ q i)
    (h1 : ∀ i, q i < 1) :
    HasSum (fun α : (Fin d →₀ ℕ) => ∏ i, q i ^ α i) (∏ i, (1 - q i)⁻¹) :=
  hasSum_index_prod _ _
    (fun i => by
      simpa [norm_pow, Real.norm_of_nonneg (h0 i)] using summable_geometric_of_lt_one (h0 i) (h1 i))
    (fun i => hasSum_geometric_of_lt_one (h0 i) (h1 i))

/-- The geometric tail `Σ_{k ≥ N} q^k = q^N / (1 − q)` on one axis. -/
private theorem hasSum_geometric_tail {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) (N : ℕ) :
    HasSum (fun k : ℕ => if N ≤ k then q ^ k else 0) (q ^ N * (1 - q)⁻¹) := by
  rw [← hasSum_nat_add_iff' N]
  have zero : ∑ i ∈ Finset.range N, (if N ≤ i then q ^ i else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => ite_eq_right (by simpa using hi)
  rw [zero, sub_zero]
  refine ((hasSum_geometric_of_lt_one h0 h1).mul_left (q ^ N)).congr_fun fun k => ?_
  simp [pow_add, mul_comm]

/-- `q_i = r_i / R_i`. -/
def ratio {d : Nat} (m : GeometricMajorant (Fin d)) (b : Fin d → ℚ≥0) (i : Fin d) : ℚ :=
  (b i : ℚ) / m.radius i

/-- The conservative rational error `M · (Σᵢ q_i^N_i) · ∏ᵢ (1 − q_i)⁻¹`: a union
bound over the axes along which an omitted index leaves the rectangular window. -/
def geometricTailBound {d : Nat} (m : GeometricMajorant (Fin d)) (b : Fin d → ℚ≥0)
    (N : Fin d → ℕ) : ℚ :=
  m.bound * (∑ i, ratio m b i ^ N i) * ∏ i, (1 - ratio m b i)⁻¹

/-! ## The evaluated series and its rectangular window -/

/-- The term `a_α · x^α` of the coefficient series at the real point `x`. -/
noncomputable def seriesTerm {d : Nat} (a : MvPowerSeries (Fin d) ℚ) (x : Fin d → ℝ)
    (α : (Fin d →₀ ℕ)) : ℝ :=
  ((coeff α a : ℚ) : ℝ) * ∏ i, x i ^ α i

/-- The sum of the coefficient series `Σ_α a_α x^α`. It is an unconditional `tsum`, so it is
meaningful only where summability is proved: no convergence follows from the
formal series alone (`hasSum_geometricSum` supplies it). -/
noncomputable def geometricSum {d : Nat} (a : MvPowerSeries (Fin d) ℚ) (x : Fin d → ℝ) : ℝ :=
  ∑' α, seriesTerm a x α

/-- The rectangular window `α_i < N_i` of multi-indices (empty if some `N_i = 0`). -/
noncomputable def rectangularWindow {d : Nat} (N : Fin d → ℕ) : Finset ((Fin d →₀ ℕ)) :=
  (Fintype.piFinset fun i => Finset.range (N i)).map
    (Finsupp.equivFunOnFinite (α := Fin d) (M := ℕ)).symm.toEmbedding

theorem mem_rectangularWindow {d : Nat} (N : Fin d → ℕ) (α : (Fin d →₀ ℕ)) :
    α ∈ rectangularWindow N ↔ ∀ i, α i < N i := by
  simp only [rectangularWindow, Finset.mem_map_equiv, Equiv.symm_symm, Fintype.mem_piFinset,
    Finset.mem_range, Finsupp.equivFunOnFinite_apply]

/-- The finite sum of the coefficient series over the rectangular window. -/
noncomputable def rectangularSum {d : Nat} (N : Fin d → ℕ) (a : MvPowerSeries (Fin d) ℚ)
    (x : Fin d → ℝ) : ℝ :=
  ∑ α ∈ rectangularWindow N, seriesTerm a x α

/-! ## Majorant ⇒ absolute convergence -/

section Bound

variable {d : Nat} {a : MvPowerSeries (Fin d) ℚ} {m : GeometricMajorant (Fin d)} {b : Fin d → ℚ≥0}

private theorem ratio_nonneg (i : Fin d) : (0 : ℝ) ≤ (ratio m b i : ℝ) := by
  exact_mod_cast div_nonneg (NNRat.coe_nonneg (b i)) (m.radius_pos i).le

private theorem ratio_lt_one (inside : ∀ i, (b i : ℚ) < m.radius i) (i : Fin d) :
    (ratio m b i : ℝ) < 1 := by
  exact_mod_cast (div_lt_one (m.radius_pos i)).mpr (inside i)

/-- Each term is dominated by the geometric family `M · ∏ q_i^α_i`. -/
theorem norm_seriesTerm_le (majorizes : IsMajorized a m)
    {x : Fin d → ℝ} (hx : ∀ i, |x i| ≤ ((b i : ℚ) : ℝ))
    (α : (Fin d →₀ ℕ)) :
    ‖seriesTerm a x α‖ ≤ (m.bound : ℝ) * ∏ i, (ratio m b i : ℝ) ^ α i := by
  have coeff : |((coeff α a : ℚ) : ℝ)| ≤ (m.bound : ℝ) * (∏ i, ((m.radius i : ℝ) ^ α i)⁻¹) := by
    have h : ((|coeff α a| : ℚ) : ℝ) ≤
        ((m.bound * (∏ i, (m.radius i ^ α i)⁻¹) : ℚ) : ℝ) := by
      exact_mod_cast majorizes α
    push_cast at h
    exact h
  have mono : ∏ i, |x i| ^ α i ≤ ∏ i, ((b i : ℚ) : ℝ) ^ α i :=
    Finset.prod_le_prod₀ (fun i _ => by positivity)
      (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hx i) _)
  have rhs : (m.bound : ℝ) * (∏ i, ((m.radius i : ℝ) ^ α i)⁻¹) * ∏ i, ((b i : ℚ) : ℝ) ^ α i =
      (m.bound : ℝ) * ∏ i, (ratio m b i : ℝ) ^ α i := by
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [ratio, Rat.cast_div, div_pow]
    ring
  rw [Real.norm_eq_abs, seriesTerm, abs_mul, Finset.abs_prod]
  simp only [abs_pow]
  rw [← rhs]
  have hb : (0 : ℝ) ≤ m.bound := by exact_mod_cast m.bound_nonneg
  refine mul_le_mul coeff mono (Finset.prod_nonneg fun i _ => by positivity) ?_
  refine mul_nonneg hb (Finset.prod_nonneg fun i _ => inv_nonneg.mpr (pow_nonneg ?_ _))
  exact_mod_cast (m.radius_pos i).le

/-- Absolute convergence at every point of the box. -/
theorem summable_norm_seriesTerm (majorizes : IsMajorized a m)
    (inside : ∀ i, (b i : ℚ) < m.radius i)
    {x : Fin d → ℝ} (hx : ∀ i, |x i| ≤ ((b i : ℚ) : ℝ)) :
    Summable fun α => ‖seriesTerm a x α‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_seriesTerm_le majorizes hx)
    ((hasSum_geometric_index _ (fun i => ratio_nonneg (m := m) (b := b) i)
      (ratio_lt_one inside)).summable.mul_left _)

/-- The series of coefficients sums to `geometricSum` on the box. -/
theorem hasSum_geometricSum (majorizes : IsMajorized a m)
    (inside : ∀ i, (b i : ℚ) < m.radius i)
    {x : Fin d → ℝ} (hx : ∀ i, |x i| ≤ ((b i : ℚ) : ℝ)) :
    HasSum (seriesTerm a x) (geometricSum a x) :=
  (summable_norm_seriesTerm majorizes inside hx).of_norm.hasSum

/-- One-axis dominating factor for the part of the tail leaving the rectangular window along `i`. -/
private noncomputable def tailFactor (m : GeometricMajorant (Fin d)) (b : Fin d → ℚ≥0)
    (N : Fin d → ℕ) (i j : Fin d)
    (k : ℕ) : ℝ :=
  if j = i then (if N j ≤ k then (ratio m b j : ℝ) ^ k else 0) else (ratio m b j : ℝ) ^ k

private theorem tailFactor_nonneg
    (N : Fin d → ℕ) (i j : Fin d) (k : ℕ) :
    0 ≤ tailFactor m b N i j k := by
  unfold tailFactor
  have := ratio_nonneg (m := m) (b := b) j
  split_ifs <;> positivity

private theorem hasSum_tailFactor (inside : ∀ i, (b i : ℚ) < m.radius i) (N : Fin d → ℕ)
    (i : Fin d) :
    HasSum (fun α : (Fin d →₀ ℕ) => ∏ j, tailFactor m b N i j (α j))
      ((ratio m b i : ℝ) ^ N i * ∏ j, (1 - (ratio m b j : ℝ))⁻¹) := by
  have sums : ∀ j, HasSum (tailFactor m b N i j)
      (if j = i then (ratio m b j : ℝ) ^ N j * (1 - (ratio m b j : ℝ))⁻¹
        else (1 - (ratio m b j : ℝ))⁻¹) := by
    intro j
    unfold tailFactor
    split_ifs
    · exact hasSum_geometric_tail (ratio_nonneg j) (ratio_lt_one inside j) (N j)
    · exact hasSum_geometric_of_lt_one (ratio_nonneg j) (ratio_lt_one inside j)
  have h := hasSum_index_prod _ _ (fun j => by
      simpa [Real.norm_of_nonneg (tailFactor_nonneg N i j _)] using (sums j).summable) sums
  convert h using 1
  have split : (∏ j, if j = i then (ratio m b j : ℝ) ^ N j * (1 - (ratio m b j : ℝ))⁻¹
      else (1 - (ratio m b j : ℝ))⁻¹) =
      (∏ j, if j = i then (ratio m b j : ℝ) ^ N j else 1) * ∏ j, (1 - (ratio m b j : ℝ))⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by split_ifs <;> simp
  rw [split, Finset.prod_ite_eq']
  simp

/-- **Uniform rectangular truncation bound.** On the box, the summed series and
its rectangular sum differ by at most `geometricTailBound`. -/
theorem abs_geometricSum_sub_rectangularSum_le (majorizes : IsMajorized a m)
    (inside : ∀ i, (b i : ℚ) < m.radius i) (N : Fin d → ℕ)
    {x : Fin d → ℝ} (hx : ∀ i, |x i| ≤ ((b i : ℚ) : ℝ)) :
    |geometricSum a x - rectangularSum N a x| ≤ geometricTailBound m b N := by
  classical
  have hF := hasSum_geometricSum majorizes inside hx
  have hW : HasSum (fun α => if α ∈ rectangularWindow N then seriesTerm a x α else 0)
      (rectangularSum N a x) := by
    have h : HasSum (fun α => if α ∈ rectangularWindow N then seriesTerm a x α else 0)
        (∑ α ∈ rectangularWindow N, if α ∈ rectangularWindow N then seriesTerm a x α else 0) :=
      hasSum_sum_of_ne_finset_zero fun α hα => ite_eq_right hα
    rw [Finset.sum_congr rfl fun α hα => ite_eq_left hα] at h
    exact h
  have hT : HasSum (fun α => if α ∈ rectangularWindow N then 0 else seriesTerm a x α)
      (geometricSum a x - rectangularSum N a x) :=
    (hF.sub hW).congr_fun fun α => by split_ifs <;> simp
  let D : (Fin d →₀ ℕ) → ℝ := fun α =>
    (m.bound : ℝ) * ∑ i, ∏ j, tailFactor m b N i j (α j)
  have hD : HasSum D (geometricTailBound m b N : ℝ) := by
    have h := (hasSum_sum (s := Finset.univ) fun i _ => hasSum_tailFactor inside N i).mul_left
      (m.bound : ℝ)
    have e : (geometricTailBound m b N : ℝ) = (m.bound : ℝ) *
        ∑ i, (ratio m b i : ℝ) ^ N i * ∏ j, (1 - (ratio m b j : ℝ))⁻¹ := by
      simp only [geometricTailBound]
      push_cast
      rw [mul_assoc, Finset.sum_mul]
    rw [e]
    exact h
  have hb : (0 : ℝ) ≤ m.bound := by exact_mod_cast m.bound_nonneg
  have dominated : ∀ α, |if α ∈ rectangularWindow N then 0 else seriesTerm a x α| ≤ D α := by
    intro α
    have D_nonneg : 0 ≤ D α := mul_nonneg hb (Finset.sum_nonneg fun i _ =>
      Finset.prod_nonneg fun j _ => tailFactor_nonneg N i j _)
    split_ifs with hα
    · simpa using D_nonneg
    · rw [mem_rectangularWindow] at hα
      push Not at hα
      obtain ⟨i, hi⟩ := hα
      have exact : ∏ j, (ratio m b j : ℝ) ^ α j = ∏ j, tailFactor m b N i j (α j) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        unfold tailFactor
        split_ifs with h1 h2
        · rfl
        · exact absurd (h1 ▸ hi) h2
        · rfl
      calc |seriesTerm a x α| = ‖seriesTerm a x α‖ := (Real.norm_eq_abs _).symm
        _ ≤ (m.bound : ℝ) * ∏ j, (ratio m b j : ℝ) ^ α j := norm_seriesTerm_le majorizes hx α
        _ ≤ D α := by
          rw [exact]
          refine mul_le_mul_of_nonneg_left ?_ hb
          exact Finset.single_le_sum (f := fun i => ∏ j, tailFactor m b N i j (α j))
            (fun i _ => Finset.prod_nonneg fun j _ => tailFactor_nonneg N i j _)
            (Finset.mem_univ i)
  refine abs_le.mpr ⟨?_, ?_⟩
  · exact hasSum_le (fun α => neg_le_of_abs_le (dominated α)) hD.neg hT
  · exact hasSum_le (fun α => le_of_abs_le (dominated α)) hT hD

end Bound


end MvPowerSeries
