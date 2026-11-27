/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.HomDensity
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Sidorenko's inequality for the four-cycle

Sidorenko's conjecture asserts that for every bipartite graph `F` and every graph `G`,
`t(F, G) ≥ t(K₂, G) ^ |E(F)|` (Lovász, *Subgraph densities in signed graphons and the local
Sidorenko conjecture*, Electron. J. Combin. 18 (2011), §1; its analytic form, inequality (1)
there, allows any bounded measurable kernel `W ≥ 0`, not necessarily symmetric). The four-cycle
`C₄ = K_{2,2}` is the first nontrivial case; here it is proved for finite weighted graphs by two
applications of the Cauchy–Schwarz inequality,
`∑_{a,b,c,d} w(ab) w(bc) w(cd) w(da) = ∑_{a,c} (∑_b w(ab) w(bc))² ≥ |V|⁻² (∑_b d(b)²)²
  ≥ |V|⁻⁴ (∑_{a,b} w(ab))⁴`,
which does not even need `w ≥ 0`.
-/

@[expose] public section

open SimpleGraph (cycleGraph)

namespace MathlibExt.Combinatorics.SimpleGraph.GraphLimits

open Finset

variable {V : Type*} [Fintype V]

-- Sum over maps `Fin (k + 1) → V`, splitting off the image of `0`.
theorem sum_fin_succ_fun {k : ℕ} (f : (Fin (k + 1) → V) → ℝ) :
    ∑ φ, f φ = ∑ a : V, ∑ ψ : Fin k → V, f (Fin.cons a ψ) := by
  rw [← (Fin.consEquiv fun _ => V).sum_comp, Fintype.sum_prod_type]
  rfl

/-- **Edge density as a sum.** The density of an edge, `t(K₂, w) = |V|⁻² ∑_{a, b} w(a, b)`. -/
theorem homDensity_top_fin_two (w : Sym2 V → ℝ) :
    homDensity (⊤ : SimpleGraph (Fin 2)) w =
      (∑ a : V, ∑ b : V, w s(a, b)) / (Fintype.card V : ℝ) ^ 2 := by
  have hE : (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by decide
  simp only [homDensity, homWeight, hE, prod_singleton, Fintype.card_fin]
  congr 1
  rw [sum_fin_succ_fun]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_fin_succ_fun]
  refine sum_congr rfl fun b _ => ?_
  simp [Sym2.map_mk]

/-- **Four-cycle density as a sum.** The density of the four-cycle,
`t(C₄, w) = |V|⁻⁴ ∑_{a,b,c,d} w(a, b) w(b, c) w(c, d) w(d, a)`. -/
theorem homDensity_cycleGraph_four (w : Sym2 V → ℝ) :
    homDensity (cycleGraph 4) w =
      (∑ a : V, ∑ b : V, ∑ c : V, ∑ d : V, w s(a, b) * w s(b, c) * w s(c, d) * w s(d, a)) /
        (Fintype.card V : ℝ) ^ 4 := by
  have hE : (cycleGraph 4).edgeFinset = {s(0, 1), s(1, 2), s(2, 3), s(3, 0)} := by decide
  simp only [homDensity, homWeight, hE, Fintype.card_fin]
  congr 1
  rw [sum_fin_succ_fun]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_fin_succ_fun]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_fin_succ_fun]
  refine sum_congr rfl fun c _ => ?_
  rw [sum_fin_succ_fun]
  refine sum_congr rfl fun d _ => ?_
  rw [Fintype.sum_unique, prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_singleton]
  set φ : Fin 4 → V := Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d default)))
  have h0 : φ 0 = a := rfl
  have h1 : φ 1 = b := rfl
  have h2 : φ 2 = c := rfl
  have h3 : φ 3 = d := rfl
  simp only [Sym2.map_mk, h0, h1, h2, h3]
  ring

/-- **Sidorenko's inequality for the four-cycle.** For every weighted graph `w : Sym2 V → ℝ` on a
finite vertex set, `t(C₄, w) ≥ t(K₂, w) ^ 4`: the four-cycle `C₄ = K_{2,2}` satisfies Sidorenko's
conjecture (Lovász, *Subgraph densities in signed graphons and the local Sidorenko conjecture*,
Electron. J. Combin. 18 (2011), §1, inequality (1), which Sidorenko proved for bigraphs with a
colour class of at most four nodes). The proof (two Cauchy–Schwarz steps) needs no sign
condition on `w`. -/
theorem homDensity_cycleGraph_four_ge (w : Sym2 V → ℝ) :
    homDensity (⊤ : SimpleGraph (Fin 2)) w ^ 4 ≤ homDensity (cycleGraph 4) w := by
  rw [homDensity_top_fin_two, homDensity_cycleGraph_four]
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  rcases (Fintype.card V).eq_zero_or_pos with hn | hn
  · have : n = 0 := by rw [hn_def, hn, Nat.cast_zero]
    simp [this]
  have hnpos : 0 < n := by rw [hn_def]; exact_mod_cast hn
  -- codegrees `M a c = ∑_b w(ab) w(bc)` and degrees `d b = ∑_a w(ab)`
  set M : V → V → ℝ := fun a c => ∑ b, w s(a, b) * w s(b, c) with hM
  set d : V → ℝ := fun b => ∑ a, w s(a, b) with hd
  set S2 := ∑ a : V, ∑ b : V, w s(a, b) with hS2
  have hS4 : ∑ a : V, ∑ b : V, ∑ c : V, ∑ d : V,
      w s(a, b) * w s(b, c) * w s(c, d) * w s(d, a) = ∑ a, ∑ c, M a c ^ 2 := by
    refine sum_congr rfl fun a _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    simp only [hM, sq, sum_mul_sum]
    refine sum_congr rfl fun b _ => sum_congr rfl fun e _ => ?_
    rw [Sym2.eq_swap (a := e) (b := a), Sym2.eq_swap (a := c) (b := e)]
    ring
  have hMsum : ∑ a, ∑ c, M a c = ∑ b, d b ^ 2 := by
    have h : ∀ a, ∑ c, M a c = ∑ b, ∑ c, w s(a, b) * w s(b, c) := fun a => by
      simp only [hM]
      exact sum_comm
    simp only [h]
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    simp only [hd, sq, sum_mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun c _ => ?_
    rw [Sym2.eq_swap (a := b) (b := c)]
  have hdsum : ∑ b, d b = S2 := by
    simp only [hd, hS2]
    exact sum_comm
  -- Cauchy–Schwarz twice
  have cs1 : (∑ a, ∑ c, M a c) ^ 2 ≤ n ^ 2 * ∑ a, ∑ c, M a c ^ 2 := by
    calc (∑ a, ∑ c, M a c) ^ 2 ≤ n * ∑ a, (∑ c, M a c) ^ 2 := by
          simpa [hn_def] using sq_sum_le_card_mul_sum_sq (s := univ) (f := fun a => ∑ c, M a c)
      _ ≤ n * ∑ a, n * ∑ c, M a c ^ 2 := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun a _ => ?_) hnpos.le
          simpa [hn_def] using sq_sum_le_card_mul_sum_sq (s := univ) (f := fun c => M a c)
      _ = n ^ 2 * ∑ a, ∑ c, M a c ^ 2 := by rw [← mul_sum]; ring
  have cs2 : S2 ^ 2 ≤ n * ∑ b, d b ^ 2 := by
    rw [← hdsum]
    simpa [hn_def] using sq_sum_le_card_mul_sum_sq (s := univ) (f := d)
  have hD0 : 0 ≤ ∑ b, d b ^ 2 := sum_nonneg fun b _ => sq_nonneg _
  rw [hS4]
  set S4 := ∑ a, ∑ c, M a c ^ 2 with hS4def
  rw [hMsum] at cs1
  -- `S2 ^ 4 ≤ n ^ 4 * S4`
  have key : S2 ^ 4 ≤ n ^ 4 * S4 := by
    have h1 : (S2 ^ 2) ^ 2 ≤ (n * ∑ b, d b ^ 2) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) cs2 2
    calc S2 ^ 4 = (S2 ^ 2) ^ 2 := by ring
      _ ≤ (n * ∑ b, d b ^ 2) ^ 2 := h1
      _ = n ^ 2 * (∑ b, d b ^ 2) ^ 2 := by ring
      _ ≤ n ^ 2 * (n ^ 2 * S4) := mul_le_mul_of_nonneg_left cs1 (by positivity)
      _ = n ^ 4 * S4 := by ring
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  calc S2 ^ 4 * n ^ 4 ≤ n ^ 4 * S4 * n ^ 4 := mul_le_mul_of_nonneg_right key (by positivity)
    _ = S4 * (n ^ 2) ^ 4 := by ring

end MathlibExt.Combinatorics.SimpleGraph.GraphLimits
