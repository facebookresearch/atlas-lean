/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Assembly.LanderWaterman

/-!
# Lander–Waterman run ends, single-clone islands and gaps: exact finite laws and Poisson limits

`LanderWaterman` places `N` reads of length `L` at independent uniform starts on a circular genome
`Fin G` (all `G ^ N` start tuples equally likely, `normalizedCount`) and proves the per-base
coverage laws. This file adds end statistics for the apparent islands of Lander and Waterman
(1988), Proposition 1, as exact finite identities in that model, their limits under sparsity, gap
counts, and the per-base coverage law of a linear genome with its boundary effect.

## Run ends (end statistic for apparent islands)

Lander and Waterman declare two clones overlapping when they share at least `T` bases, with
`1 ≤ T ≤ L`. When `2 * L ≤ G + 1`, two reads starting at `p` and `p + d` (`0 < d < L`) share the
single interval of `L - d` bases, so the overlap is detected exactly when `d ≤ W := L - T`. On a
shorter circle two reads can share bases in two pieces (across the wrap), and the window rule then
separates reads whose total shared length reaches `T`; the window statements hold in every case,
but read as detected overlaps only under the single-piece condition.

`EndsRun W starts p` holds when some read starts at `p` and no read starts at a positive offset
`1, …, W` after `p` (mod `G`): `p` is the last start of an apparent island. These are positions,
not reads (co-located reads count once; `NoSuccessor` of `LanderWaterman` counts reads), and the
count is an end statistic, not a count of islands: when at least one end exists every apparent
island has exactly one, but a circle on which every gap between consecutive starts is at most `W`
(and `N > 0`) has one island and no end. `IsolatedRead W` marks a position holding exactly one read
with no other read within `W` positions on either side: an apparent island of exactly one clone.
No theorem here counts islands, contigs or connected components.

* `sum_card_endsRun`, `expected_endsRun`: exactly `G ((G - V) ^ N - (G - V - 1) ^ N)` pairs of an
  end position and a start tuple, i.e. expectation `G ((1 - V / G) ^ N - (1 - (V + 1) / G) ^ N)`.
* `sum_card_isolatedRead`, `expected_isolatedRead`: `G N (G - 2W - 1) ^ (N - 1)` pairs, i.e.
  expectation `N (1 - (2W + 1) / G) ^ (N - 1)`.
* `tendsto_expected_endsRun_div`, `tendsto_expected_isolatedRead_div`: if `N V_N / G_N → a` and
  the sparsity condition `N / G_N → 0` holds, the expectations divided by `N` tend to `e^{-a}` and
  `e^{-2a}`. With `V_N = W_N`, `W_N / L_N → σ` and `N L_N / G_N → c`, `a = cσ`: the normalized forms
  of Lander and Waterman's `N e^{-cσ}` apparent islands (i) (the circular correction of at most
  one island is lost after dividing by `N`) and of the `N e^{-2cσ}` single-clone islands in (ii').
  Sparsity is required, and it is not the same as `L_N → ∞`: if `N / G_N → λ > 0` the limits are
  `e^{-a} (1 - e^{-λ}) / λ` and `e^{-2a - λ}` instead.

## Gaps

For `0 < m`, `GapAtLeast L m starts x` marks the last base `x` of a maximal uncovered run of length
at least `m` that is followed by a covered base; each such run is marked exactly once. An entirely
uncovered circle (for example `N = 0`) has no covered base and no mark. `sum_card_gapAtLeast`: for
`0 < L`, `0 < m` and `L + m ≤ G`, exactly `G ((G - (L + m - 1)) ^ N - (G - (L + m)) ^ N)` pairs
(`m = 1` counts the gaps). No gap limit theorem is stated.

## Linear genome

On a linear genome `Fin G` reads lie inside the genome, so a start is in `Fin (G - L + 1)`, and a
read starting at `s` covers `x` when `s ≤ x < s + L`. `card_linCoveringStarts` counts the starts
covering `x`: `min x (G - L) + 1 - (x + 1 - L)`, which is `L` for interior bases
(`L - 1 ≤ x` and `x + L ≤ G`, `linCoveringStarts_interior`) and smaller near either end
(`linCoveringStarts_lt_of_boundary`); `linUncovered` gives the exact uncovered probability.

## Not covered

Counts of islands, contigs or components; the number of islands with exactly `j ≥ 2` clones, the
expected number of clones per island, the expected island length and the conditional ocean law
(Proposition 1(ii), (iii), (iv), (vi)).

## References

* E. S. Lander and M. S. Waterman, *Genomic mapping by fingerprinting random clones: a
  mathematical analysis*, Genomics 2 (1988), 231–239, Proposition 1.
* L. Clarke and J. Carbon, Cell 9 (1976), 91–99.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Assembly.LanderWaterman

open Filter Topology

/-- Some read starts at position `p` and no read starts at a positive offset `1, …, V` after `p`
(mod `G`). With `V = W` and the single-piece overlap condition, `p` is the last start of an
apparent island; this is an end statistic, not an island count. -/
def EndsRun {G N : ℕ} (V : ℕ) (starts : Fin N → Fin G) (p : Fin G) : Prop :=
  (∃ j, starts j = p) ∧
    ∀ j, ¬ (0 < ((starts j).val + G - p.val) % G ∧ ((starts j).val + G - p.val) % G ≤ V)

instance {G N : ℕ} (V : ℕ) (starts : Fin N → Fin G) (p : Fin G) :
    Decidable (EndsRun V starts p) := by
  unfold EndsRun; infer_instance

/-- Exactly one read starts at `p`, and every other read starts more than `W` positions after
`p` and more than `W` positions before it (circularly). With `W = L - T` and the single-piece
overlap condition `2 * L ≤ G + 1`, this is a read alone in its apparent island. -/
def IsolatedRead {G N : ℕ} (W : ℕ) (starts : Fin N → Fin G) (p : Fin G) : Prop :=
  (Finset.univ.filter fun j => starts j = p).card = 1 ∧
    ∀ j, starts j ≠ p → W < ((starts j).val + G - p.val) % G ∧ W < (p.val + G - (starts j).val) % G

instance {G N : ℕ} (W : ℕ) (starts : Fin N → Fin G) (p : Fin G) :
    Decidable (IsolatedRead W starts p) := by
  unfold IsolatedRead; infer_instance

/-- The `m` bases ending at `x` (those `y` with `(x - y) mod G < m`) are covered by no read, and
the base after `x` is covered by some read: for `0 < m`, `x` is the last base of a maximal gap of
length at least `m` followed by coverage. For `m = 0` only the base after `x` must be covered;
for `G = 1` no base has a successor at offset `1`, so no base is marked. -/
def GapAtLeast {G N : ℕ} (L m : ℕ) (starts : Fin N → Fin G) (x : Fin G) : Prop :=
  (∀ y : Fin G, (x.val + G - y.val) % G < m → ∀ j, ¬ Covers G L (starts j) y) ∧
    ∃ y : Fin G, (y.val + G - x.val) % G = 1 ∧ ∃ j, Covers G L (starts j) y

instance {G N : ℕ} (L m : ℕ) (starts : Fin N → Fin G) (x : Fin G) :
    Decidable (GapAtLeast L m starts x) := by
  unfold GapAtLeast; infer_instance

private lemma circular_offset {G : ℕ} (s p : Fin G) :
    (s.val + G - p.val) % G = (s - p).val := by
  rw [Fin.val_sub]
  have hp := p.isLt
  congr 1
  omega

private lemma card_translate {G : ℕ} (p : Fin G) (P : Fin G → Prop)
    [DecidablePred P] :
    (Finset.univ.filter fun s => P (s - p)).card = (Finset.univ.filter P).card := by
  classical
  let : NeZero G := ⟨by have := p.isLt; omega⟩
  refine Finset.card_bij (fun s _ => s - p) ?_ ?_ ?_
  · intro s hs
    simpa using hs
  · intro s hs t ht h
    exact sub_left_injective h
  · intro d hd
    refine ⟨d + p, ?_, by simp⟩
    simpa using hd

private lemma card_all_starts {G N : ℕ} (P : Fin G → Prop) [DecidablePred P] :
    (Finset.univ.filter fun starts : Fin N → Fin G => ∀ j, P (starts j)).card =
      (Finset.univ.filter P).card ^ N := by
  have he : (Finset.univ.filter fun starts : Fin N → Fin G => ∀ j, P (starts j)) =
      Fintype.piFinset (fun _ : Fin N => Finset.univ.filter P) := by
    ext starts
    simp
  rw [he, Fintype.card_piFinset_const]

private lemma card_forward_window {G V : ℕ} (hV : V + 1 ≤ G) (p : Fin G) :
    (Finset.univ.filter fun s : Fin G =>
      0 < (s - p).val ∧ (s - p).val ≤ V).card = V := by
  rw [card_translate p (fun d => 0 < d.val ∧ d.val ≤ V)]
  calc
    _ = (Finset.univ : Finset (Fin V)).card := by
      refine Finset.card_bij (fun d hd =>
        ⟨d.val - 1, by have := (Finset.mem_filter.mp hd).2; omega⟩) ?_ ?_ ?_
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
        have hd' := d.isLt
        refine ⟨⟨d.val + 1, by omega⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        · apply Fin.ext
          simp
    _ = V := by simp

private lemma card_closed_window {G V : ℕ} (hV : V + 1 ≤ G) (p : Fin G) :
    (Finset.univ.filter fun s : Fin G => (s - p).val ≤ V).card = V + 1 := by
  rw [card_translate p (fun d => d.val ≤ V)]
  simpa only [Nat.lt_succ_iff, Nat.min_eq_right hV] using
    (Fin.card_filter_val_lt (n := G) (m := V + 1))

private lemma card_run_end {G N V : ℕ} (hV : V + 1 ≤ G) (p : Fin G) :
    (Finset.univ.filter fun starts : Fin N → Fin G => EndsRun V starts p).card =
      (G - V) ^ N - (G - V - 1) ^ N := by
  classical
  let : NeZero G := ⟨by omega⟩
  let A := Finset.univ.filter fun starts : Fin N → Fin G =>
    ∀ j, ¬ (0 < (starts j - p).val ∧ (starts j - p).val ≤ V)
  let B := Finset.univ.filter fun starts : Fin N → Fin G =>
    ∀ j, ¬ ((starts j - p).val ≤ V)
  have hBA : B ⊆ A := by
    intro starts hs
    simp only [B, A, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    intro j hj
    exact hs j hj.2
  have he : (Finset.univ.filter fun starts : Fin N → Fin G => EndsRun V starts p) =
      A \ B := by
    ext starts
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      A, B, EndsRun, circular_offset]
    constructor
    · rintro ⟨⟨j, hj⟩, h⟩
      refine ⟨h, ?_⟩
      intro hb
      simpa [hj] using hb j
    · rintro ⟨h, hb⟩
      obtain ⟨j, hj⟩ := not_forall.mp hb
      have hz : (starts j - p).val = 0 := by
        have hh := h j
        omega
      refine ⟨⟨j, ?_⟩, h⟩
      have heq : starts j - p = 0 := Fin.ext hz
      exact sub_eq_zero.mp heq
  have hA : A.card = (G - V) ^ N := by
    dsimp [A]
    rw [card_all_starts (G := G) (N := N) (fun s : Fin G => ¬ (0 < (s - p).val ∧ (s - p).val ≤ V))]
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun s : Fin G => 0 < (s - p).val ∧ (s - p).val ≤ V)
    rw [card_forward_window hV p, Finset.card_univ, Fintype.card_fin] at hc
    congr 1
    omega
  have hB : B.card = (G - V - 1) ^ N := by
    dsimp [B]
    rw [card_all_starts (G := G) (N := N) (fun s : Fin G => ¬ ((s - p).val ≤ V))]
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun s : Fin G => (s - p).val ≤ V)
    rw [card_closed_window hV p, Finset.card_univ, Fintype.card_fin] at hc
    congr 1
    omega
  rw [he, Finset.card_sdiff, Finset.inter_eq_left.mpr hBA, hA, hB]

/-- **Exact count of run ends**: for `V + 1 ≤ G`, summed over positions, the number of start
tuples in which a run ends at `p` is `G ((G - V) ^ N - (G - V - 1) ^ N)`. -/
theorem sum_card_endsRun {G N V : ℕ} (hV : V + 1 ≤ G) :
    ∑ p : Fin G, (Finset.univ.filter fun starts : Fin N → Fin G => EndsRun V starts p).card =
      G * ((G - V) ^ N - (G - V - 1) ^ N) := by
  simp_rw [card_run_end hV]
  simp

/-- **Expected number of run ends (exact)**: for `V + 1 ≤ G`, summed over positions, the
normalized counts of run ends are `G ((1 - V / G) ^ N - (1 - (V + 1) / G) ^ N)`, the expected
number of run-end positions for independent uniform starts. -/
theorem expected_endsRun {G N V : ℕ} (hV : V + 1 ≤ G) :
    ∑ p : Fin G, normalizedCount (Finset.univ.filter fun starts : Fin N → Fin G =>
        EndsRun V starts p) =
      (G : ℝ) * ((1 - (V : ℝ) / G) ^ N - (1 - ((V : ℝ) + 1) / G) ^ N) := by
  have hG : (G : ℝ) ≠ 0 := by exact_mod_cast (show G ≠ 0 by omega)
  have hv : V ≤ G := by omega
  have hv1 : 1 ≤ G - V := by omega
  have hp : (G - V - 1) ^ N ≤ (G - V) ^ N :=
    Nat.pow_le_pow_left (Nat.sub_le (G - V) 1) N
  have hf : 1 - (V : ℝ) / G = ((G : ℝ) - V) / G := by field_simp
  have hf1 : 1 - ((V : ℝ) + 1) / G = ((G : ℝ) - V - 1) / G := by
    field_simp
    ring
  simp only [normalizedCount, ← Finset.sum_div]
  rw [← Nat.cast_sum, sum_card_endsRun hV, Nat.cast_mul, Nat.cast_sub hp,
    Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hv1, Nat.cast_sub hv, Nat.cast_one,
    hf, hf1, div_pow, div_pow]
  ring

private lemma card_between (G a b : ℕ) (hb : b ≤ G) :
    (Finset.univ.filter fun s : Fin G => a ≤ s.val ∧ s.val < b).card = b - a := by
  classical
  calc
    _ = (Finset.Ico a b).card := by
      refine Finset.card_bij (fun s _ => s.val) ?_ ?_ ?_
      · intro s hs
        simpa using hs
      · intro s hs t ht h
        exact Fin.ext h
      · intro n hn
        have hn' := Finset.mem_Ico.mp hn
        refine ⟨⟨n, by omega⟩, ?_, rfl⟩
        simpa using hn
    _ = _ := Nat.card_Ico _ _

private lemma card_separated {G W : ℕ} (hW : 2 * W + 1 ≤ G) (p : Fin G) :
    (Finset.univ.filter fun s : Fin G =>
      s ≠ p ∧ W < (s - p).val ∧ W < (p - s).val).card = G - (2 * W + 1) := by
  classical
  let : NeZero G := ⟨by omega⟩
  have he : (Finset.univ.filter fun s : Fin G =>
      s ≠ p ∧ W < (s - p).val ∧ W < (p - s).val) =
      Finset.univ.filter fun s : Fin G => W + 1 ≤ (s - p).val ∧ (s - p).val < G - W := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hn : p - s = -(s - p) := by abel
    rw [hn, Fin.val_neg]
    by_cases hs : s = p
    · subst s
      simp
    · have hz : s - p ≠ 0 := sub_ne_zero.mpr hs
      rw [ite_eq_right hz]
      have hd := (s - p).isLt
      omega
  rw [he, card_translate p (fun d => W + 1 ≤ d.val ∧ d.val < G - W),
    card_between G (W + 1) (G - W) (Nat.sub_le _ _)]
  omega

private lemma card_isolated {G N W : ℕ} (hW : 2 * W + 1 ≤ G) (p : Fin G) :
    (Finset.univ.filter fun starts : Fin N → Fin G => IsolatedRead W starts p).card =
      N * (G - (2 * W + 1)) ^ (N - 1) := by
  classical
  let event := Finset.univ.filter fun starts : Fin N → Fin G => IsolatedRead W starts p
  let support := fun starts : Fin N → Fin G => Finset.univ.filter fun j => starts j = p
  let allowed := Finset.univ.filter fun s : Fin G =>
    s ≠ p ∧ W < (s - p).val ∧ W < (p - s).val
  have ha : allowed.card = G - (2 * W + 1) := card_separated hW p
  have hf (j : Fin N) : (event.filter fun starts => support starts = {j}).card =
      (G - (2 * W + 1)) ^ (N - 1) := by
    have he : (event.filter fun starts => support starts = {j}) =
        Fintype.piFinset (fun i : Fin N => if i = j then {p} else allowed) := by
      ext starts
      simp only [event, Finset.mem_filter, Finset.mem_univ, true_and,
        Fintype.mem_piFinset]
      constructor
      · rintro ⟨h, hs⟩ i
        have hj : starts j = p := by
          have hm : j ∈ support starts := by rw [hs]; simp
          simpa [support] using hm
        by_cases hi : i = j
        · subst i
          simp [hj]
        · have hip : starts i ≠ p := by
            intro hip
            have hm : i ∈ support starts := by simp [support, hip]
            rw [hs] at hm
            exact hi (Finset.mem_singleton.mp hm)
          simp only [ite_eq_right hi, allowed, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨hip, by simpa only [circular_offset] using h.2 i hip⟩
      · intro h
        have hj : starts j = p := by simpa using h j
        have ho (i : Fin N) (hi : i ≠ j) :
            starts i ≠ p ∧ W < (starts i - p).val ∧ W < (p - starts i).val := by
          simpa only [ite_eq_right hi, allowed, Finset.mem_filter, Finset.mem_univ,
            true_and] using h i
        have hs : support starts = {j} := by
          ext i
          simp only [support, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton]
          by_cases hi : i = j
          · simp [hi, hj]
          · simp [hi, (ho i hi).1]
        refine ⟨⟨?_, ?_⟩, hs⟩
        · change (support starts).card = 1
          rw [hs, Finset.card_singleton]
        · intro i hip
          have hi : i ≠ j := by rintro rfl; exact hip hj
          simpa only [circular_offset] using (ho i hi).2
    rw [he, Fintype.card_piFinset]
    simp_rw [apply_ite Finset.card, Finset.card_singleton, ha]
    rw [Finset.prod_ite]
    simp [Finset.filter_ne']
  change event.card = _
  rw [Finset.card_eq_sum_card_fiberwise (f := support)
    (t := Finset.univ.powersetCard 1) (by
      intro starts hs
      exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, (Finset.mem_filter.mp hs).2.1⟩)]
  have hc (S : Finset (Fin N)) (hS : S ∈ Finset.univ.powersetCard 1) :
      (event.filter fun starts => support starts = S).card =
        (G - (2 * W + 1)) ^ (N - 1) := by
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hS).2
    exact hf j
  rw [Finset.sum_congr rfl hc]
  simp [Finset.card_powersetCard]

/-- **Exact count of isolated reads**: for `2 W + 1 ≤ G`, summed over positions, the number of
start tuples with an isolated read at `p` is `G N (G - 2 W - 1) ^ (N - 1)`, where `N - 1` is
natural subtraction (for `N = 0` the factor `N` makes it `0`). -/
theorem sum_card_isolatedRead {G N W : ℕ} (hW : 2 * W + 1 ≤ G) :
    ∑ p : Fin G, (Finset.univ.filter fun starts : Fin N → Fin G =>
        IsolatedRead W starts p).card = G * N * (G - (2 * W + 1)) ^ (N - 1) := by
  simp_rw [card_isolated hW]
  simp [Nat.mul_assoc]

/-- **Expected number of isolated reads (exact)**: for `2 W + 1 ≤ G`, summed over positions,
the normalized counts of isolated reads are `N (1 - (2 W + 1) / G) ^ (N - 1)`, where `N - 1` is
natural subtraction (for `N = 0` the factor `N` makes it `0`); for independent uniform starts
this is the expected number of isolated reads, of single-read islands under the single-piece
condition with `W = L - T`. -/
theorem expected_isolatedRead {G N W : ℕ} (hW : 2 * W + 1 ≤ G) :
    ∑ p : Fin G, normalizedCount (Finset.univ.filter fun starts : Fin N → Fin G =>
        IsolatedRead W starts p) =
      (N : ℝ) * (1 - (2 * (W : ℝ) + 1) / G) ^ (N - 1) := by
  have hG : (G : ℝ) ≠ 0 := by exact_mod_cast (show G ≠ 0 by omega)
  simp only [normalizedCount, ← Finset.sum_div]
  rw [← Nat.cast_sum, sum_card_isolatedRead hW]
  cases N with
  | zero => simp
  | succ n =>
    have hf : 1 - (2 * (W : ℝ) + 1) / G = ((G : ℝ) - (2 * W + 1)) / G := by
      field_simp
    simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hW,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    rw [hf, div_pow, pow_succ]
    field_simp

private lemma tendsto_small (u : ℕ → ℝ) (b : ℝ)
    (hb : Tendsto (fun N : ℕ => (N : ℝ) * u N) atTop (𝓝 b)) :
    Tendsto u atTop (𝓝 0) := by
  have ht := hb.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp [hn]

private lemma tendsto_pow_pred (u : ℕ → ℝ) (b : ℝ)
    (hb : Tendsto (fun N : ℕ => (N : ℝ) * u N) atTop (𝓝 b)) :
    Tendsto (fun N => (1 + u N) ^ (N - 1)) atTop (𝓝 (Real.exp b)) := by
  have hu := tendsto_small u b hb
  have hshift := (hb.comp (tendsto_add_atTop_nat 1)).sub
    (hu.comp (tendsto_add_atTop_nat 1))
  have hg : Tendsto (fun N : ℕ => (N : ℝ) * u (N + 1)) atTop (𝓝 b) := by
    convert hshift using 1
    · ext N
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      ring_nf
    · simp
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.add_sub_cancel] using Real.tendsto_one_add_pow_exp_of_tendsto hg

private lemma pow_difference_bounds (x y : ℝ) (hy : 0 ≤ y) (hxy : y ≤ x)
    (N : ℕ) :
    (N : ℝ) * y ^ (N - 1) * (x - y) ≤ x ^ N - y ^ N ∧
      x ^ N - y ^ N ≤ (N : ℝ) * x ^ (N - 1) * (x - y) := by
  have hx : 0 ≤ x := hy.trans hxy
  have ht (k : ℕ) (hk : k ∈ Finset.range N) :
      y ^ (N - 1) ≤ x ^ k * y ^ (N - 1 - k) ∧
        x ^ k * y ^ (N - 1 - k) ≤ x ^ (N - 1) := by
    have hk' := Finset.mem_range.mp hk
    have he : k + (N - 1 - k) = N - 1 := by omega
    constructor
    · calc
        _ = y ^ k * y ^ (N - 1 - k) := by rw [← pow_add, he]
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy hxy k)
          (pow_nonneg hy _)
    · calc
        _ ≤ x ^ k * x ^ (N - 1 - k) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hxy _) (pow_nonneg hx _)
        _ = _ := by rw [← pow_add, he]
  have hl := Finset.sum_le_sum (s := Finset.range N) (fun k hk => (ht k hk).1)
  have hu := Finset.sum_le_sum (s := Finset.range N) (fun k hk => (ht k hk).2)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hl hu
  rw [← geom_sum₂_mul]
  exact ⟨mul_le_mul_of_nonneg_right hl (sub_nonneg.mpr hxy),
    mul_le_mul_of_nonneg_right hu (sub_nonneg.mpr hxy)⟩

private lemma normalized_difference_bounds (x y : ℝ) (hy : 0 ≤ y) (hxy : y < x)
    (N : ℕ) (hN : 0 < N) :
    y ^ (N - 1) ≤ (x ^ N - y ^ N) / ((N : ℝ) * (x - y)) ∧
      (x ^ N - y ^ N) / ((N : ℝ) * (x - y)) ≤ x ^ (N - 1) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : 0 < (N : ℝ) * (x - y) := mul_pos hn (sub_pos.mpr hxy)
  have hb := pow_difference_bounds x y hy hxy.le N
  constructor
  · apply (le_div_iff₀ hd).mpr
    convert hb.1 using 1; ring
  · apply (div_le_iff₀ hd).mpr
    convert hb.2 using 1; ring

/-- **Expected run ends per read tend to `e^{-a}` under sparsity**: if `V_N + 1 ≤ G_N` for
every `N`, `N V_N / G_N → a` and `N / G_N → 0`, the expected number of run ends divided by `N`
tends to `e^{-a}`. -/
theorem tendsto_expected_endsRun_div (V G : ℕ → ℕ) (hV : ∀ N, V N + 1 ≤ G N) (a : ℝ)
    (ha : Tendsto (fun N : ℕ => (N : ℝ) * V N / G N) atTop (𝓝 a))
    (h0 : Tendsto (fun N : ℕ => (N : ℝ) / G N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ p : Fin (G N), normalizedCount
        (Finset.univ.filter fun starts : Fin N → Fin (G N) => EndsRun (V N) starts p)) / N)
      atTop (𝓝 (Real.exp (-a))) := by
  have hg : Tendsto (fun N : ℕ => (N : ℝ) * -((V N : ℝ) / G N))
      atTop (𝓝 (-a)) := by
    simpa only [mul_neg, mul_div_assoc] using ha.neg
  have hg1 : Tendsto (fun N : ℕ => (N : ℝ) * -(((V N : ℝ) + 1) / G N))
      atTop (𝓝 (-a)) := by
    have ht := (ha.add h0).neg
    convert ht using 1
    · ext N
      ring_nf
    · simp
  have hx := tendsto_pow_pred (fun N => -((V N : ℝ) / G N)) (-a) hg
  have hy := tendsto_pow_pred (fun N => -(((V N : ℝ) + 1) / G N)) (-a) hg1
  simp only [← sub_eq_add_neg] at hx hy
  have hb : ∀ᶠ N : ℕ in atTop,
      (1 - ((V N : ℝ) + 1) / G N) ^ (N - 1) ≤
        (∑ p : Fin (G N), normalizedCount
          (Finset.univ.filter fun starts : Fin N → Fin (G N) => EndsRun (V N) starts p)) / N ∧
      (∑ p : Fin (G N), normalizedCount
          (Finset.univ.filter fun starts : Fin N → Fin (G N) => EndsRun (V N) starts p)) / N ≤
        (1 - (V N : ℝ) / G N) ^ (N - 1) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hgn : (0 : ℝ) < G N := by
      exact_mod_cast (show 0 < G N by have := hV N; omega)
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hvn : (V N : ℝ) + 1 ≤ G N := by exact_mod_cast hV N
    have hy0 : 0 ≤ 1 - ((V N : ℝ) + 1) / G N := by
      exact sub_nonneg.mpr ((div_le_one hgn).mpr hvn)
    have hdiff : (1 - (V N : ℝ) / G N) - (1 - ((V N : ℝ) + 1) / G N) =
        1 / G N := by ring
    have hlt : 1 - ((V N : ℝ) + 1) / G N < 1 - (V N : ℝ) / G N := by
      apply sub_pos.mp
      rw [hdiff]
      positivity
    have he : (∑ p : Fin (G N), normalizedCount
        (Finset.univ.filter fun starts : Fin N → Fin (G N) => EndsRun (V N) starts p)) / N =
        ((1 - (V N : ℝ) / G N) ^ N - (1 - ((V N : ℝ) + 1) / G N) ^ N) /
          ((N : ℝ) * ((1 - (V N : ℝ) / G N) - (1 - ((V N : ℝ) + 1) / G N))) := by
      rw [expected_endsRun (hV N), hdiff]
      field_simp
    rw [he]
    exact normalized_difference_bounds _ _ hy0 hlt N (by omega)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hy hx
    (hb.mono fun N h => h.1) (hb.mono fun N h => h.2)

/-- **Expected isolated reads per read tend to `e^{-2a}` under sparsity**: if
`2 W_N + 1 ≤ G_N` for every `N`, `N W_N / G_N → a` and `N / G_N → 0`, the expected number of
isolated reads divided by `N` tends to `e^{-2a}`. -/
theorem tendsto_expected_isolatedRead_div (W G : ℕ → ℕ) (hW : ∀ N, 2 * W N + 1 ≤ G N) (a : ℝ)
    (ha : Tendsto (fun N : ℕ => (N : ℝ) * W N / G N) atTop (𝓝 a))
    (h0 : Tendsto (fun N : ℕ => (N : ℝ) / G N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ p : Fin (G N), normalizedCount
        (Finset.univ.filter fun starts : Fin N → Fin (G N) => IsolatedRead (W N) starts p)) / N)
      atTop (𝓝 (Real.exp (-2 * a))) := by
  have hg : Tendsto (fun N : ℕ => (N : ℝ) * -((2 * (W N : ℝ) + 1) / G N))
      atTop (𝓝 (-2 * a)) := by
    have ht := ((ha.const_mul 2).add h0).neg
    convert ht using 1
    · ext N
      ring_nf
    · ring_nf
  have ht := tendsto_pow_pred (fun N => -((2 * (W N : ℝ) + 1) / G N)) (-2 * a) hg
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [expected_isolatedRead (hW N)]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp [sub_eq_add_neg, hn]

private lemma uncovered_block_iff {G L m : ℕ} (hL : 0 < L) (hm : 0 < m)
    (hLm : L + m ≤ G) (s x : Fin G) :
    (∀ y : Fin G, (x - y).val < m → ¬ ((y - s).val < L)) ↔
      L + m - 1 ≤ (x - s).val := by
  classical
  let : NeZero G := ⟨by omega⟩
  constructor
  · intro h
    by_contra hb
    by_cases hd : (x - s).val < L
    · have hc := h x (by simpa using hm)
      exact hc hd
    · let d : Fin G := ⟨L - 1, by omega⟩
      let y := s + d
      have hy : (y - s).val < L := by
        simpa only [y, add_sub_cancel_left, d] using (show L - 1 < L by omega)
      have hx : (x - y).val < m := by
        have he : x - y = (x - s) - d := by dsimp [y]; abel
        rw [he, Fin.val_sub]
        have hv := (x - s).isLt
        change (G - (L - 1) + (x - s).val) % G < m
        rw [show G - (L - 1) + (x - s).val = G + ((x - s).val - (L - 1)) by omega,
          Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod,
          Nat.mod_eq_of_lt (show (x - s).val - (L - 1) < G by omega)]
        omega
      exact h y hx hy
  · intro h y hy hc
    have he : x - s = (x - y) + (y - s) := by abel
    have hs : (x - s).val ≤ (x - y).val + (y - s).val := by
      rw [he, Fin.val_add]
      exact Nat.mod_le _ _
    omega

private lemma gap_iff {G N L m : ℕ} (hL : 0 < L) (hm : 0 < m)
    (hLm : L + m ≤ G) (starts : Fin N → Fin G) (x : Fin G) :
    GapAtLeast L m starts x ↔
      (∀ j, L + m - 1 ≤ (x - starts j).val) ∧
        ∃ j, (x - starts j).val = G - 1 := by
  classical
  let : NeZero G := ⟨by omega⟩
  let one : Fin G := ⟨1, by omega⟩
  have hu : (∀ y : Fin G, (x - y).val < m → ∀ j, ¬ ((y - starts j).val < L)) ↔
      ∀ j, L + m - 1 ≤ (x - starts j).val := by
    constructor
    · intro h j
      exact (uncovered_block_iff hL hm hLm (starts j) x).mp (fun y hy => h y hy j)
    · intro h y hy j
      exact (uncovered_block_iff hL hm hLm (starts j) x).mpr (h j) y hy
  simp only [GapAtLeast, Covers, circular_offset]
  constructor
  · rintro ⟨h, y, hy, j, hj⟩
    have ha := hu.mp h
    refine ⟨ha, j, ?_⟩
    have hye : y - x = one := Fin.ext hy
    have he : y - starts j = (x - starts j) + one := by rw [← hye]; abel
    rw [he, Fin.val_add] at hj
    change ((x - starts j).val + 1) % G < L at hj
    have hd := (x - starts j).isLt
    have hj' := ha j
    by_cases ht : (x - starts j).val + 1 < G
    · rw [Nat.mod_eq_of_lt ht] at hj
      omega
    · omega
  · rintro ⟨ha, j, hj⟩
    refine ⟨hu.mpr ha, x + one, ?_, j, ?_⟩
    · simp [one]
    · have he : x + one - starts j = (x - starts j) + one := by abel
      rw [he, Fin.val_add]
      change ((x - starts j).val + 1) % G < L
      rw [hj, show G - 1 + 1 = G by omega, Nat.mod_self]
      exact hL

private lemma card_gap {G N L m : ℕ} (hL : 0 < L) (hm : 0 < m)
    (hLm : L + m ≤ G) (x : Fin G) :
    (Finset.univ.filter fun starts : Fin N → Fin G => GapAtLeast L m starts x).card =
      (G - (L + m - 1)) ^ N - (G - (L + m)) ^ N := by
  classical
  let : NeZero G := ⟨by omega⟩
  let A := Finset.univ.filter fun starts : Fin N → Fin G =>
    ∀ j, L + m - 1 ≤ (x - starts j).val
  let B := Finset.univ.filter fun starts : Fin N → Fin G =>
    ∀ j, L + m - 1 ≤ (x - starts j).val ∧ (x - starts j).val < G - 1
  have hBA : B ⊆ A := by
    intro starts hs
    simp only [B, A, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact fun j => (hs j).1
  have he : (Finset.univ.filter fun starts : Fin N → Fin G => GapAtLeast L m starts x) =
      A \ B := by
    ext starts
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      A, B, gap_iff hL hm hLm]
    constructor
    · rintro ⟨ha, j, hj⟩
      refine ⟨ha, ?_⟩
      intro hb
      have hh := (hb j).2
      omega
    · rintro ⟨ha, hb⟩
      refine ⟨ha, ?_⟩
      obtain ⟨j, hj⟩ := not_forall.mp hb
      have hd := (x - starts j).isLt
      have hh := ha j
      exact ⟨j, by omega⟩
  have ht (a b : ℕ) (hb : b ≤ G) :
      (Finset.univ.filter fun s : Fin G => a ≤ (x - s).val ∧ (x - s).val < b).card =
        b - a := by
    calc
      _ = (Finset.univ.filter fun d : Fin G => a ≤ d.val ∧ d.val < b).card := by
        refine Finset.card_bij (fun s _ => x - s) ?_ ?_ ?_
        · intro s hs
          simpa using hs
        · intro s hs t ht h
          exact sub_right_injective h
        · intro d hd
          refine ⟨x - d, ?_, by simp⟩
          simpa using hd
      _ = _ := card_between G a b hb
  have hA : A.card = (G - (L + m - 1)) ^ N := by
    dsimp [A]
    rw [card_all_starts (G := G) (N := N) (fun s : Fin G => L + m - 1 ≤ (x - s).val)]
    have hc : (Finset.univ.filter fun s : Fin G => L + m - 1 ≤ (x - s).val).card =
        G - (L + m - 1) := by
      have he : (Finset.univ.filter fun s : Fin G => L + m - 1 ≤ (x - s).val) =
          Finset.univ.filter fun s : Fin G =>
            L + m - 1 ≤ (x - s).val ∧ (x - s).val < G := by
        ext s
        simp
      rw [he, ht _ _ le_rfl]
    rw [hc]
  have hB : B.card = (G - (L + m)) ^ N := by
    dsimp [B]
    rw [card_all_starts (G := G) (N := N)
      (fun s : Fin G => L + m - 1 ≤ (x - s).val ∧ (x - s).val < G - 1),
      ht _ _ (Nat.sub_le _ _)]
    congr 1
    omega
  rw [he, Finset.card_sdiff_of_subset hBA, hA, hB]

/-- **Exact count of gaps of length at least `m`**: for `0 < L`, `0 < m` and `L + m ≤ G`,
summed over positions, `G ((G - (L + m - 1)) ^ N - (G - (L + m)) ^ N)`. -/
theorem sum_card_gapAtLeast {G N L m : ℕ} (hL : 0 < L) (hm : 0 < m) (hLm : L + m ≤ G) :
    ∑ x : Fin G, (Finset.univ.filter fun starts : Fin N → Fin G =>
        GapAtLeast L m starts x).card =
      G * ((G - (L + m - 1)) ^ N - (G - (L + m)) ^ N) := by
  simp_rw [card_gap hL hm hLm]
  simp

/-- **Number of read starts covering a base of a linear genome**: for `L ≤ G`, the number of
starts `s ∈ Fin (G - L + 1)` with `s ≤ x < s + L` is `min x (G - L) + 1 - (x + 1 - L)`, where
`x + 1 - L` is natural subtraction (`0` when `x + 1 < L`); the outer subtraction never
truncates, and for `L = 0` the count is `0`. -/
theorem card_linCoveringStarts {G L : ℕ} (hL : L ≤ G) (x : Fin G) :
    (Finset.univ.filter fun s : Fin (G - L + 1) => s.val ≤ x.val ∧ x.val < s.val + L).card =
      min x.val (G - L) + 1 - (x.val + 1 - L) := by
  classical
  calc
    _ = (Finset.Ico (x.val + 1 - L) (min x.val (G - L) + 1)).card := by
      refine Finset.card_bij (fun s _ => s.val) ?_ ?_ ?_
      · intro s hs
        have hs' := (Finset.mem_filter.mp hs).2
        have ht := s.isLt
        simp only [Finset.mem_Ico]
        omega
      · intro s hs t ht h
        exact Fin.ext h
      · intro n hn
        have hn' := Finset.mem_Ico.mp hn
        refine ⟨⟨n, by omega⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
    _ = _ := by simp

/-- **Interior bases of a linear genome are covered by exactly `L` starts**: a base with
`L - 1 ≤ x` and `x + L ≤ G` is covered by exactly `L` starts (`L - 1` is natural subtraction;
for `L = 0` every base qualifies and the count is `0`). -/
theorem linCoveringStarts_interior {G L : ℕ} (x : Fin G) (h1 : L - 1 ≤ x.val)
    (h2 : x.val + L ≤ G) :
    (Finset.univ.filter fun s : Fin (G - L + 1) => s.val ≤ x.val ∧ x.val < s.val + L).card = L := by
  rw [card_linCoveringStarts (by omega)]
  omega

/-- **Linear genome, boundary bases**: for `L ≤ G`, a base within `L - 1` of either end
(`x + 1 < L` or `G < x + L`) is covered by fewer than `L` starts. -/
theorem linCoveringStarts_lt_of_boundary {G L : ℕ} (hL : L ≤ G) (x : Fin G)
    (h : x.val + 1 < L ∨ G < x.val + L) :
    (Finset.univ.filter fun s : Fin (G - L + 1) => s.val ≤ x.val ∧ x.val < s.val + L).card < L := by
  rw [card_linCoveringStarts hL]
  have hx := x.isLt
  omega

/-- **Exact uncovered probability of a base of a linear genome**: for `L ≤ G`, with independent
starts uniform on `Fin (G - L + 1)`, base `x` is uncovered with probability
`(1 - k / (G - L + 1)) ^ N`, where `k = min x (G - L) + 1 - (x + 1 - L)` is the number of
starts covering `x`. -/
theorem linUncovered {G L N : ℕ} (hL : L ≤ G) (x : Fin G) :
    normalizedCount (Finset.univ.filter fun starts : Fin N → Fin (G - L + 1) =>
        ∀ j, ¬ ((starts j).val ≤ x.val ∧ x.val < (starts j).val + L)) =
      (1 - ((min x.val (G - L) + 1 - (x.val + 1 - L) : ℕ) : ℝ) / ((G - L + 1 : ℕ) : ℝ)) ^ N := by
  classical
  let k := min x.val (G - L) + 1 - (x.val + 1 - L)
  have hk : k ≤ G - L + 1 := by
    have hc := Finset.card_filter_le (s := (Finset.univ : Finset (Fin (G - L + 1))))
      (p := fun s => s.val ≤ x.val ∧ x.val < s.val + L)
    rw [card_linCoveringStarts hL x, Finset.card_univ, Fintype.card_fin] at hc
    exact hc
  have hc : (Finset.univ.filter fun s : Fin (G - L + 1) =>
      ¬ (s.val ≤ x.val ∧ x.val < s.val + L)).card = G - L + 1 - k := by
    have hc := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (fun s : Fin (G - L + 1) => s.val ≤ x.val ∧ x.val < s.val + L)
    rw [card_linCoveringStarts hL x, Finset.card_univ, Fintype.card_fin] at hc
    dsimp [k]
    omega
  have he : (Finset.univ.filter fun starts : Fin N → Fin (G - L + 1) =>
      ∀ j, ¬ ((starts j).val ≤ x.val ∧ x.val < (starts j).val + L)) =
      Fintype.piFinset (fun _ : Fin N => Finset.univ.filter fun s : Fin (G - L + 1) =>
        ¬ (s.val ≤ x.val ∧ x.val < s.val + L)) := by
    ext starts
    simp
  have hG : ((G - L + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show G - L + 1 ≠ 0 by omega)
  rw [normalizedCount, he, Fintype.card_piFinset_const, hc, Nat.cast_pow,
    Nat.cast_sub hk, ← div_pow]
  congr 1
  dsimp [k]
  field_simp

end Cslib.Bioinformatics.Assembly.LanderWaterman
