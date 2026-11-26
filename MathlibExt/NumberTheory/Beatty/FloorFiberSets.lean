/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Beatty.FloorFiberIndicator

/-!
# Beatty sets of floor-fiber multiplicities

The explicit indicator formula identifies the larger multiplicity using the floor-increment identity
for Beatty membership. It proves that identity directly and does not need to iterate Polanco's
slope map. Rayleigh's theorem then identifies the smaller multiplicity with the complementary
Beatty set.

## References

* Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*, INTEGERS **25**
  (2025), Article A104, pp. 1–19, Corollaries 1 and 2 and Theorem 1 (Beatty–Rayleigh).
  For the floor-increment identity used by the indicator formula, p. 9 credits:
  * Geremias Polanco, *The logarithm of irrational numbers and Beatty sequences*, Acta Arithmetica
    **179** (2017), pp. 101–123.
  * Jean-Paul Allouche and Jeffrey Shallit, *Automatic Sequences: Theory, Applications,
    Generalizations*, Cambridge University Press (2003), Chapter 9, pp. 283–297, Lemma 9.1.3.
* Samuel Beatty, Problem 3173, *American Mathematical Monthly* **33** (1926), p. 159.
-/

namespace MetaMathlibExt

open Set
open scoped symmDiff

/-- **The values of $\lfloor n\alpha\rfloor$ of each multiplicity form Beatty sets.** Let $k$ be a
positive integer and let $\alpha$ be an irrational number with $1/(k + 1) < \alpha < 1/k$. Then
there are real numbers $\gamma > 0$ and $\delta > 0$ such that the positive integers $t$ that
equal $\lfloor n\alpha\rfloor$ for exactly $k + 1$ positive integers $n$ are exactly the numbers
$\lfloor m\gamma\rfloor$ for positive integers $m$, and the positive integers $t$ that equal
$\lfloor n\alpha\rfloor$ for exactly $k$ positive integers $n$ are exactly the numbers
$\lfloor m\delta\rfloor$ for positive integers $m$.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Corollary 1 (`integers-2025-A104-cor-1`). -/
public theorem beatty_floor_fiber_card_sets_isBeatty {α : ℝ} {k : ℕ}
    (hirr : Irrational α) (h1 : 1 / ((k : ℝ) + 1) < α) (h2 : α < 1 / (k : ℝ)) :
    ∃ γ δ : ℝ, 0 < γ ∧ 0 < δ ∧
      {t : ℤ | 0 < t ∧ {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1} =
        {beattySeq γ m | m > 0} ∧
      {t : ℤ | 0 < t ∧ {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k} =
        {beattySeq δ m | m > 0} := by
  obtain ⟨hγ, hγirr, hcard⟩ := beatty_floor_fiber_card_eq_add_indicator_explicit hirr h1 h2
  let γ : ℝ := (α⁻¹ - (k : ℝ))⁻¹
  let δ : ℝ := (1 - γ⁻¹)⁻¹
  have hconj : γ.HolderConjugate δ := Real.holderConjugate_iff.mpr ⟨hγ, by simp [δ]⟩
  let G : Set ℤ := {beattySeq γ m | m > 0}
  let D : Set ℤ := {beattySeq δ m | m > 0}
  have hpartition : G ∆ D = {t : ℤ | 0 < t} :=
    hγirr.beattySeq_symmDiff_beattySeq_pos hconj
  have hcompl (t : ℤ) (ht : 0 < t) : t ∉ G ↔ t ∈ D := by
    have hmem : t ∈ G ∆ D := by rwa [hpartition]
    rw [mem_symmDiff] at hmem
    tauto
  have hpos {r : ℝ} (hr : 1 ≤ r) {t : ℤ} (ht : t ∈ {beattySeq r m | m > 0}) : 0 < t := by
    obtain ⟨m, hm, rfl⟩ := ht
    rw [beattySeq, Int.floor_pos]
    exact one_le_mul_of_one_le_of_one_le (by norm_cast) hr
  have hcounts (t : ℤ) (ht : 0 < t) :
      ({n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1 ↔ t ∈ G) ∧
      ({n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k ↔ t ∉ G) := by
    lift t to ℕ using ht.le
    have h := hcard t
    change {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = (t : ℤ)}.ncard =
      k + G.indicator (1 : ℤ → ℕ) t at h
    rw [h]
    by_cases hm : (t : ℤ) ∈ G <;> simp [hm]
  refine ⟨γ, δ, hconj.pos, hconj.symm.pos, ?_, ?_⟩
  · ext t
    change (0 < t ∧ _ = k + 1) ↔ t ∈ G
    refine ⟨fun ⟨ht, hc⟩ ↦ (hcounts t ht).1.mp hc, fun hm ↦ ?_⟩
    have ht := hpos hconj.lt.le hm
    exact ⟨ht, (hcounts t ht).1.mpr hm⟩
  · ext t
    change (0 < t ∧ _ = k) ↔ t ∈ D
    refine ⟨fun ⟨ht, hc⟩ ↦ (hcompl t ht).mp ((hcounts t ht).2.mp hc), fun hm ↦ ?_⟩
    have ht := hpos hconj.symm.lt.le hm
    exact ⟨ht, (hcounts t ht).2.mpr ((hcompl t ht).mpr hm)⟩

end MetaMathlibExt
