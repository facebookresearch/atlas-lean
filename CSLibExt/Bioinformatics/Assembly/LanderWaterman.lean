/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Lander–Waterman coverage of a circular genome

Clarke and Carbon (1976) and Lander and Waterman (1988) model shotgun sequencing as `N` reads of
length `L` whose start positions are independent and uniform on a genome of length `G`. With
redundancy (coverage) `c = N L / G`, a fixed base is left uncovered with probability tending to
`e^{-c}`, and the number of reads covering it tends to a Poisson law with mean `c`.

This file states the model exactly on a circular genome `Fin G` (positions mod `G`, so every base
plays the same role and there are no edge effects): a tuple of start positions
`starts : Fin N → Fin G`, drawn uniformly from the `G ^ N` tuples (`uniformProb`), and a read
starting at `s` covers the `L` bases `s, s + 1, …, s + L - 1 (mod G)` (`Covers`), for `L ≤ G`.

## Main results

* `card_uncovered`, `uniformProb_uncovered`: **exact finite coverage**: a fixed base is uncovered
  by all `N` reads for exactly `(G - L) ^ N` of the start tuples, probability `(1 - L / G) ^ N`.
* `card_depth_eq`, `uniformProb_depth_eq`: **exact depth law**: the number of reads covering a
  fixed base is binomial, `N.choose k * (L / G) ^ k * (1 - L / G) ^ (N - k)`.
* `tendsto_uniformProb_uncovered`: **Lander–Waterman limit**: if `N L / G_N → c` as `N → ∞`
  (with `L` fixed and genome lengths `G_N ≥ L`), the uncovered probability tends to `e^{-c}`.
* `tendsto_uniformProb_depth`: **the depth tends to Poisson(`c`)**: probability of depth `k`
  tends to `e^{-c} c^k / k.factorial`.
* `sum_card_noSuccessor`: **expected number of island ends** (exact, `L ≤ G`): the
  expected number of reads with no other read starting in the next `L - 1` positions is
  `N (1 - (L - 1) / G) ^ (N - 1)`, given as the count `N G (G - (L - 1)) ^ (N - 1)` over all
  `G ^ N` start tuples.

`uniformProb_eq_uniformOfFinset` identifies the normalized count with the probability under
Mathlib's uniform law `Measure.uniformOfFinset` on start tuples.

## Not covered

The linear (non-circular) genome with edge effects, the minimum detectable overlap `θ` of
Lander and Waterman, island lengths, and the limit `N e^{-c}` of the expected number of islands.

## References

* L. Clarke and J. Carbon, *A colony bank containing synthetic ColE1 hybrid plasmids
  representative of the entire E. coli genome*, Cell 9 (1976), 91–99.
* E. S. Lander and M. S. Waterman, *Genomic mapping by fingerprinting random clones: a
  mathematical analysis*, Genomics 2 (1988), 231–239.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Assembly.LanderWaterman

open Filter Topology

/-- A read of length `L` starting at position `s` of a circular genome of length `G` covers base
`x` when `x` is one of `s, s + 1, …, s + L - 1 (mod G)`, i.e. `(x - s) mod G < L`. -/
def Covers (G L : ℕ) (s x : Fin G) : Prop :=
  (x.val + G - s.val) % G < L

/-- Coverage is decidable (a comparison of natural numbers). -/
instance (G L : ℕ) (s x : Fin G) : Decidable (Covers G L s x) :=
  inferInstanceAs (Decidable (_ < _))

/-- The depth of coverage of base `x`: the number of reads covering it. -/
def depth {G N : ℕ} (L : ℕ) (starts : Fin N → Fin G) (x : Fin G) : ℕ :=
  (Finset.univ.filter fun j => Covers G L (starts j) x).card

/-- The probability of an event `E` (a set of start tuples) when the `N` start positions are
independent and uniform on `Fin G`: `|E| / G ^ N`. -/
noncomputable def uniformProb {G N : ℕ} (E : Finset (Fin N → Fin G)) : ℝ :=
  (E.card : ℝ) / (G : ℝ) ^ N

private lemma offset_eq {G : ℕ} (a b : Fin G) :
    (a.val + G - b.val) % G = (a - b).val := by
  rw [Fin.val_sub]
  have hb := b.isLt
  have he : a.val + G - b.val = G - b.val + a.val := by omega
  rw [he]

private lemma covers_iff {G L : ℕ} (s x : Fin G) :
    Covers G L s x ↔ (x - s).val < L := by
  rw [Covers, offset_eq]

private lemma card_covering {G L : ℕ} (hL : L ≤ G) (x : Fin G) :
    (Finset.univ.filter fun s => Covers G L s x).card = L := by
  classical
  let : NeZero G := ⟨by have := x.isLt; omega⟩
  calc
    _ = (Finset.univ.filter fun d : Fin G => d.val < L).card := by
      refine Finset.card_bij (fun s _ => x - s) ?_ ?_ ?_
      · intro s hs
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, covers_iff] using hs
      · intro s hs t ht h
        exact sub_right_injective h
      · intro d hd
        refine ⟨x - d, ?_, by simp⟩
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, covers_iff,
          sub_sub_cancel] using hd
    _ = L := by simpa [Nat.min_eq_right hL] using (Fin.card_filter_val_lt (n := G) (m := L))

private lemma card_noncovering {G L : ℕ} (hL : L ≤ G) (x : Fin G) :
    (Finset.univ.filter fun s => ¬ Covers G L s x).card = G - L := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun s => Covers G L s x)
  rw [card_covering hL x, Finset.card_univ, Fintype.card_fin] at h
  omega

private lemma card_support {G L N : ℕ} (hL : L ≤ G) (x : Fin G) (S : Finset (Fin N)) :
    (Finset.univ.filter fun starts : Fin N → Fin G =>
      (Finset.univ.filter fun j => Covers G L (starts j) x) = S).card =
      L ^ S.card * (G - L) ^ (N - S.card) := by
  classical
  have he :
      (Finset.univ.filter fun starts : Fin N → Fin G =>
        (Finset.univ.filter fun j => Covers G L (starts j) x) = S) =
      Fintype.piFinset (fun j => Finset.univ.filter fun s : Fin G =>
        if j ∈ S then Covers G L s x else ¬ Covers G L s x) := by
    ext starts
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j
      have hj : Covers G L (starts j) x ↔ j ∈ S := by
        simpa using (Finset.ext_iff.mp h j)
      split_ifs with hmem
      · exact hj.mpr hmem
      · exact fun hc => hmem (hj.mp hc)
    · intro h
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      specialize h j
      split_ifs at h with hmem <;> simp_all
  rw [he, Fintype.card_piFinset]
  have hc (j : Fin N) :
      (Finset.univ.filter fun s : Fin G =>
        if j ∈ S then Covers G L s x else ¬ Covers G L s x).card =
        if j ∈ S then L else G - L := by
    split_ifs <;> simp only [card_covering hL x, card_noncovering hL x]
  simp_rw [hc]
  rw [Finset.prod_ite]
  have hf : (Finset.univ.filter fun j : Fin N => j ∉ S) = Finset.univ \ S := by
    ext j
    simp
  simp [hf, Finset.card_sdiff]

/-- `uniformProb` is the probability under Mathlib's uniform law `Measure.uniformOfFinset` on all
start tuples. -/
theorem uniformProb_eq_uniformOfFinset {G N : ℕ} (E : Finset (Fin N → Fin G)) :
    uniformProb E = (MeasureTheory.Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin G))
      (E : Set (Fin N → Fin G))).toReal := by
  classical
  rw [MeasureTheory.Measure.uniformOfFinset_apply, ENNReal.toReal_div]
  simp [uniformProb, ENNReal.toReal_natCast, Fintype.card_pi]

/-- **Exact coverage count**: for `L ≤ G`, base `x` is uncovered by all `N` reads for exactly
`(G - L) ^ N` of the `G ^ N` start tuples. -/
theorem card_uncovered {G L N : ℕ} (hL : L ≤ G) (x : Fin G) :
    (Finset.univ.filter fun starts : Fin N → Fin G => ∀ j, ¬ Covers G L (starts j) x).card =
      (G - L) ^ N := by
  have he : (Finset.univ.filter fun starts : Fin N → Fin G =>
      ∀ j, ¬ Covers G L (starts j) x) =
      Fintype.piFinset (fun _ : Fin N =>
        Finset.univ.filter fun s => ¬ Covers G L s x) := by
    ext starts
    simp
  rw [he, Fintype.card_piFinset_const, card_noncovering hL x]

/-- **Exact depth law (count form)**: for `L ≤ G`, base `x` is covered by exactly `k` reads for
`N.choose k * L ^ k * (G - L) ^ (N - k)` of the start tuples. -/
theorem card_depth_eq {G L N : ℕ} (hL : L ≤ G) (x : Fin G) (k : ℕ) :
    (Finset.univ.filter fun starts : Fin N → Fin G => depth L starts x = k).card =
      N.choose k * L ^ k * (G - L) ^ (N - k) := by
  classical
  let support := fun starts : Fin N → Fin G =>
    Finset.univ.filter fun j => Covers G L (starts j) x
  have he : (Finset.univ.filter fun starts : Fin N → Fin G => depth L starts x = k) =
      (Finset.univ.filter fun starts => support starts ∈ Finset.univ.powersetCard k) := by
    ext starts
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [support, depth, Finset.mem_powersetCard]
  rw [he, ← Finset.sum_card_fiberwise_eq_card_filter]
  have hc (S : Finset (Fin N)) (hS : S ∈ Finset.univ.powersetCard k) :
      (Finset.univ.filter fun starts => support starts = S).card =
        L ^ k * (G - L) ^ (N - k) := by
    simpa only [support, (Finset.mem_powersetCard.mp hS).2] using card_support hL x S
  rw [Finset.sum_congr rfl hc]
  simp [Finset.card_powersetCard, Nat.mul_assoc]

/-- **Exact uncovered probability** (Clarke–Carbon, Lander–Waterman, circular genome):
`(1 - L / G) ^ N` for `L ≤ G`. -/
theorem uniformProb_uncovered {G L N : ℕ} (hL : L ≤ G) (x : Fin G) :
    uniformProb (Finset.univ.filter fun starts : Fin N → Fin G =>
        ∀ j, ¬ Covers G L (starts j) x) = (1 - (L : ℝ) / G) ^ N := by
  have hG : (G : ℝ) ≠ 0 := by
    exact_mod_cast (show G ≠ 0 by have := x.isLt; omega)
  rw [uniformProb, card_uncovered hL x, Nat.cast_pow, Nat.cast_sub hL, ← div_pow]
  congr 1
  field_simp

/-- **Exact depth law**: the depth at a fixed base is binomial with `N` trials and success
probability `L / G`, for `L ≤ G`. -/
theorem uniformProb_depth_eq {G L N : ℕ} (hL : L ≤ G) (x : Fin G) (k : ℕ) :
    uniformProb (Finset.univ.filter fun starts : Fin N → Fin G => depth L starts x = k) =
      (N.choose k : ℝ) * ((L : ℝ) / G) ^ k * (1 - (L : ℝ) / G) ^ (N - k) := by
  have hG : (G : ℝ) ≠ 0 := by
    exact_mod_cast (show G ≠ 0 by have := x.isLt; omega)
  rw [uniformProb, card_depth_eq hL x]
  by_cases hk : k ≤ N
  · have hpow : (G : ℝ) ^ N = (G : ℝ) ^ k * (G : ℝ) ^ (N - k) := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    have hf : 1 - (L : ℝ) / G = ((G : ℝ) - L) / G := by field_simp
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hL,
      hpow, hf, div_pow, div_pow]
    field_simp
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- **Lander–Waterman limit for the uncovered fraction**: with read length `L` fixed, genome
lengths `G N ≥ L`, and coverage `N L / G_N → c` as the number of reads `N → ∞`, the probability
that a given base is uncovered tends to `e^{-c}`. -/
theorem tendsto_uniformProb_uncovered (L : ℕ) (G : ℕ → ℕ) (hL : ∀ N, L ≤ G N) (c : ℝ)
    (hc : Tendsto (fun N : ℕ => (N : ℝ) * L / G N) atTop (𝓝 c)) (x : ∀ N, Fin (G N)) :
    Tendsto (fun N => uniformProb (Finset.univ.filter fun starts : Fin N → Fin (G N) =>
        ∀ j, ¬ Covers (G N) L (starts j) (x N))) atTop (𝓝 (Real.exp (-c))) := by
  have hg : Tendsto (fun N : ℕ => (N : ℝ) * -((L : ℝ) / G N)) atTop (𝓝 (-c)) := by
    simpa only [mul_neg, mul_div_assoc] using hc.neg
  have ht := Real.tendsto_one_add_pow_exp_of_tendsto hg
  simpa only [uniformProb_uncovered (hL _) (x _), sub_eq_add_neg] using ht

/-- **The coverage depth tends to Poisson(`c`)**: under the hypotheses of
`tendsto_uniformProb_uncovered`, the probability that a given base is covered by exactly `k`
reads tends to `e^{-c} c^k / k.factorial`. -/
theorem tendsto_uniformProb_depth (L : ℕ) (G : ℕ → ℕ) (hL : ∀ N, L ≤ G N) (c : ℝ)
    (hc : Tendsto (fun N : ℕ => (N : ℝ) * L / G N) atTop (𝓝 c)) (x : ∀ N, Fin (G N)) (k : ℕ) :
    Tendsto (fun N => uniformProb (Finset.univ.filter fun starts : Fin N → Fin (G N) =>
        depth L starts (x N) = k)) atTop
      (𝓝 (Real.exp (-c) * c ^ k / k.factorial)) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) * ((L : ℝ) / G N)) atTop (𝓝 c) := by
    simpa only [mul_div_assoc] using hc
  simpa only [uniformProb_depth_eq (hL _) (x _)] using
    ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop k hp

/-- Read `j` has no successor when no other read starts in the `L - 1` positions after it,
`starts j + 1, …, starts j + L - 1 (mod G)`: in Lander and Waterman's terms read `j` ends an
island (reads starting at the same position are not successors of each other). -/
def NoSuccessor {G N : ℕ} (L : ℕ) (starts : Fin N → Fin G) (j : Fin N) : Prop :=
  ∀ j' ≠ j, ¬ (0 < ((starts j').val + G - (starts j).val) % G ∧
    ((starts j').val + G - (starts j).val) % G < L)

/-- Having no successor is decidable (a finite check over the other reads). -/
instance {G N : ℕ} (L : ℕ) (starts : Fin N → Fin G) (j : Fin N) :
    Decidable (NoSuccessor L starts j) := by
  unfold NoSuccessor; infer_instance

private lemma card_forward {G L : ℕ} (hL : L ≤ G) (x : Fin G) :
    (Finset.univ.filter fun s : Fin G =>
      0 < (s - x).val ∧ (s - x).val < L).card = L - 1 := by
  classical
  let : NeZero G := ⟨by have := x.isLt; omega⟩
  calc
    _ = (Finset.univ.filter fun d : Fin G => 0 < d.val ∧ d.val < L).card := by
      refine Finset.card_bij (fun s _ => s - x) ?_ ?_ ?_
      · intro s hs
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hs
      · intro s hs t ht h
        exact sub_left_injective h
      · intro d hd
        refine ⟨d + x, ?_, by simp⟩
        simpa using hd
    _ = (Finset.univ : Finset (Fin (L - 1))).card := by
      refine Finset.card_bij (fun d hd =>
        ⟨d.val - 1, by have hh := (Finset.mem_filter.mp hd).2; omega⟩) ?_ ?_ ?_
      · intro d hd
        exact Finset.mem_univ _
      · intro d hd e he h
        have hd' := (Finset.mem_filter.mp hd).2
        have he' := (Finset.mem_filter.mp he).2
        have hv := congrArg Fin.val h
        apply Fin.ext
        dsimp at hv
        omega
      · intro d hd
        have h := d.isLt
        refine ⟨⟨d.val + 1, by omega⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        · apply Fin.ext
          simp
    _ = L - 1 := by simp

private lemma card_noSuccessor {G L N : ℕ} (hL : L ≤ G) (j : Fin N) :
    (Finset.univ.filter fun starts : Fin N → Fin G => NoSuccessor L starts j).card =
      G * (G - (L - 1)) ^ (N - 1) := by
  classical
  let event := Finset.univ.filter fun starts : Fin N → Fin G => NoSuccessor L starts j
  have hf (s : Fin G) :
      (event.filter fun starts => starts j = s).card = (G - (L - 1)) ^ (N - 1) := by
    let allowed := Finset.univ.filter fun t : Fin G =>
      ¬ (0 < (t - s).val ∧ (t - s).val < L)
    have ha : allowed.card = G - (L - 1) := by
      have h := Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (fun t : Fin G => 0 < (t - s).val ∧ (t - s).val < L)
      rw [card_forward hL s, Finset.card_univ, Fintype.card_fin] at h
      dsimp [allowed]
      omega
    have he : (event.filter fun starts => starts j = s) =
        Fintype.piFinset (fun i : Fin N => if i = j then {s} else allowed) := by
      ext starts
      simp only [event, Finset.mem_filter, Finset.mem_univ, true_and,
        Fintype.mem_piFinset]
      constructor
      · rintro ⟨h, hj⟩ i
        by_cases hi : i = j
        · subst i
          simp [hj]
        · simp only [ite_eq_right hi, allowed, Finset.mem_filter, Finset.mem_univ, true_and]
          simpa only [NoSuccessor, offset_eq, hj] using h i hi
      · intro h
        have hj : starts j = s := by simpa using h j
        refine ⟨?_, hj⟩
        intro i hi
        have hmem := h i
        simp only [ite_eq_right hi, allowed, Finset.mem_filter, Finset.mem_univ,
          true_and] at hmem
        simpa only [offset_eq, hj] using hmem
    rw [he, Fintype.card_piFinset]
    simp_rw [apply_ite Finset.card, Finset.card_singleton, ha]
    rw [Finset.prod_ite]
    simp [Finset.filter_ne']
  change event.card = _
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun starts : Fin N → Fin G => starts j) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  simp_rw [hf]
  simp

/-- **Expected number of island ends (exact)**: for `L ≤ G`, summed over the
reads, the number of start tuples in which read `j` has no successor is
`N * G * (G - (L - 1)) ^ (N - 1)`; dividing by `G ^ N`, the expected number of reads ending an
island is `N (1 - (L - 1) / G) ^ (N - 1)`. -/
theorem sum_card_noSuccessor {G L N : ℕ} (hL : L ≤ G) :
    ∑ j : Fin N, (Finset.univ.filter fun starts : Fin N → Fin G =>
        NoSuccessor L starts j).card = N * G * (G - (L - 1)) ^ (N - 1) := by
  simp_rw [card_noSuccessor hL]
  simp [Nat.mul_assoc]

end Cslib.Bioinformatics.Assembly.LanderWaterman
