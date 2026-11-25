/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Convenient.StdSimplexProductCell

@[expose] public section

open Set Finset Topology

/-!
# Finite gluing layer for affine shuffle cells in `Δ^n × Δ^m`

Dependency-forward companion to `StdSimplexProductCell` (one-cell package:
cell map, continuity, fiber-sum formulas, injectivity, closed embedding,
cumulative bounds, forward range implications). This module adds the
finite-gluing layer needed for the representable-prism theorem:

* cumulative endpoints and order facts (`shuffleCumBefore_zero`,
  `shuffleCumThrough_last`, monotonicity, successor identities);
* shuffle lattice combinatorics (level-sum invariant, every level visited);
* explicit reverse source reconstruction (`shuffleCut`, `shuffleCellSourceFun`,
  `shuffleCellSource`): the common-cut difference construction, always a valid
  source point, recovering `(x, y)` under the overlap hypotheses;
* exact range characterizations (`shuffleCell_mem_range_iff`): membership in
  `Set.range (shuffleCell S)` holds exactly when the two families of cumulative
  overlap inequalities (`shuffleCumOverlap`) hold;
* coverage (`exists_shuffleCell_mem_range`,
  `iUnion_shuffleCell_range_eq_univ`): every `(x, y)` lies in some shuffle
  cell, via a greedy lattice-path construction; the indexing family is finite;
* closed-cover gluing (`shuffleGluingCoverMap` and its continuity, closed-map,
  surjectivity, and quotient lemmas): the sigma cover map over all shuffles is
  a finite closed quotient cover;
* intersection and face compatibility (`isClosed_shuffleCellRange`,
  `isClosed_shuffleCellRange_inter`, `shuffleCell_inter_imp_commonCut`):
  ranges and pairwise intersections are closed, and distinct cells meet only
  over a common cumulative cut value.

Architecture reuse: the proof pattern follows the accepted interval
prism/range/gluing development (`StdSimplexPrism`, `StdSimplexPrismRange`,
`StdSimplexPrismGluing`): explicit source function, nonnegativity and sum
checks, coordinate recovery, range equivalence, greedy coverage, and a finite
closed quotient cover. No public name from those modules is reused here.

Forward status and nonclaims: this is a proved, accepted finite-gluing layer
for the representable-prism theorem. It proves no `SSet`, `DeltaGenerated`, colimit
homeomorphism, full adjacent-transposition face factorization with explicit
face maps and fiber equivalences, or model-category claim.

Assumption inventory: none. Every declaration in this file is proved; the file
introduces no new foundational principles and contains no placeholders.
-/

section CumEnds

variable {d : ℕ}

/-- Strict cumulative mass below level `0` vanishes. -/
theorem shuffleCumBefore_zero (x : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    shuffleCumBefore x 0 = 0 := by
  unfold shuffleCumBefore
  have hempty :
      Finset.univ.filter (fun j : Fin (d + 1) => j.val < (0 : ℕ)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro j _
    exact Nat.not_lt_zero _
  rw [hempty, Finset.sum_empty]

/-- Weak cumulative mass through the last level is the total mass `1`. -/
theorem shuffleCumThrough_last (x : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    shuffleCumThrough x d = 1 := by
  unfold shuffleCumThrough
  have huniv :
      Finset.univ.filter (fun j : Fin (d + 1) => j.val ≤ d) = Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_of_true (Nat.lt_succ_iff.mp j.isLt) trivial
  rw [huniv, x.total_of_fintype]

/-- Strict cumulative mass is monotone in the level. -/
theorem shuffleCumBefore_mono (x : Convexity.StdSimplex ℝ (Fin (d + 1))) {u w : ℕ}
    (h : u ≤ w) :
    shuffleCumBefore x u ≤ shuffleCumBefore x w := by
  unfold shuffleCumBefore
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    omega
  · intro j _ _
    exact x.weights_nonneg j

/-- Weak cumulative mass is monotone in the level. -/
theorem shuffleCumThrough_mono (x : Convexity.StdSimplex ℝ (Fin (d + 1))) {u w : ℕ}
    (h : u ≤ w) :
    shuffleCumThrough x u ≤ shuffleCumThrough x w := by
  unfold shuffleCumThrough
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    omega
  · intro j _ _
    exact x.weights_nonneg j

/-- Strict mass below `u + 1` is weak mass through `u`. -/
theorem shuffleCumBefore_succ_eq_through (x : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (u : ℕ) :
    shuffleCumBefore x (u + 1) = shuffleCumThrough x u := by
  have hset :
      Finset.univ.filter (fun j : Fin (d + 1) => j.val < u + 1) =
        Finset.univ.filter (fun j : Fin (d + 1) => j.val ≤ u) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.lt_succ_iff]
  unfold shuffleCumBefore shuffleCumThrough
  rw [hset]

/-- Weak mass through `i` splits as strict mass below `i` plus the atom. -/
theorem shuffleCumThrough_eq_before_add (x : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (i : Fin (d + 1)) :
    shuffleCumThrough x i.val =
      shuffleCumBefore x i.val + x.weights i := by
  unfold shuffleCumThrough shuffleCumBefore
  have hi :
      i ∈ Finset.univ.filter (fun j : Fin (d + 1) => j.val ≤ i.val) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, le_refl]
  have herase :
      (Finset.univ.filter (fun j : Fin (d + 1) => j.val ≤ i.val)).erase i =
        Finset.univ.filter (fun j : Fin (d + 1) => j.val < i.val) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hne, hle⟩
      by_contra hlt
      have heq : j.val = i.val := le_antisymm hle (not_lt.mp hlt)
      exact hne (Fin.ext heq)
    · intro hlt
      refine ⟨?_, by omega⟩
      intro heq
      rw [heq] at hlt
      exact lt_irrefl _ hlt
  have hadd :=
    Finset.add_sum_erase _ (fun j => x.weights j) hi
  rw [herase] at hadd
  linarith [hadd]

end CumEnds

section ShuffleCombo

variable {n m : ℕ}

/-- First-projection values are monotone along the chain. -/
private lemma shuffleProjA_val_mono (S : ProdSimplexShuffle n m) :
    Monotone (fun k : Fin (n + m + 1) => (S.projA k).val) := by
  intro a b hab
  exact Fin.le_def.mp (S.monoA hab)

/-- Second-projection values are monotone along the chain. -/
private lemma shuffleProjB_val_mono (S : ProdSimplexShuffle n m) :
    Monotone (fun k : Fin (n + m + 1) => (S.projB k).val) := by
  intro a b hab
  exact Fin.le_def.mp (S.monoB hab)

/-- The chain coordinates sum to the vertex index: every step advances exactly
one factor by one, starting from `(0, 0)`. -/
private lemma shuffleLevelSum (S : ProdSimplexShuffle n m)
    (k : Fin (n + m + 1)) :
    (S.projA k).val + (S.projB k).val = k.val := by
  suffices H : ∀ v : ℕ, ∀ j : Fin (n + m + 1), j.val = v →
      (S.projA j).val + (S.projB j).val = v by
    exact H _ k rfl
  intro v
  induction v with
  | zero =>
    intro j hj
    have hj0 : j = 0 := Fin.ext (by rw [hj]; rfl)
    subst hj0
    rw [S.firstA, S.firstB]
    rfl
  | succ v IH =>
    intro j hj
    have hjlt := j.isLt
    by_cases hlt : v < n + m
    · obtain ⟨q, hq⟩ : ∃ q : Fin (n + m), q.val = v := ⟨⟨v, hlt⟩, rfl⟩
      have hqs : q.succ = j := Fin.ext (by rw [Fin.val_succ, hq, hj])
      have hqc : q.castSucc.val = v := by rw [Fin.val_castSucc, hq]
      have hIH := IH q.castSucc hqc
      subst hqs
      rcases S.step q with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;> omega
    · omega

/-- Discrete intermediate-value principle: an `ℕ` function starting at `0`,
ending at `T`, with unit steps hits every intermediate value. -/
private lemma nat_hit_of_mono_step (g : ℕ → ℕ) (N T : ℕ)
    (g0 : g 0 = 0) (gN : g N = T)
    (hstep : ∀ w : ℕ, w < N → g (w + 1) ≤ g w + 1)
    (t : ℕ) (ht : t ≤ T) : ∃ v : ℕ, v ≤ N ∧ g v = t := by
  classical
  by_cases ht0 : t = 0
  · subst ht0
    exact ⟨0, Nat.zero_le N, g0⟩
  · have hNmem : t ≤ g N := by omega
    have hex : ∃ v, t ≤ g v := ⟨N, hNmem⟩
    set v₀ := Nat.find hex with hv₀def
    have hmem : t ≤ g v₀ := Nat.find_spec hex
    have hmin : ∀ w, t ≤ g w → v₀ ≤ w := fun w hw => Nat.find_min' hex hw
    have hleN : v₀ ≤ N := hmin N hNmem
    by_cases heq : g v₀ = t
    · exact ⟨v₀, hleN, heq⟩
    · have hlt : t < g v₀ := lt_of_le_of_ne hmem (Ne.symm heq)
      have hpos : 0 < v₀ := by
        by_contra hz
        have hzz : v₀ = 0 := by omega
        rw [hzz, g0] at hlt
        omega
      have hpred : g (v₀ - 1) < t := by
        by_contra hle
        have hle' := hmin (v₀ - 1) (not_lt.mp hle)
        omega
      have hstep' : g v₀ ≤ g (v₀ - 1) + 1 := by
        have h1 : v₀ - 1 + 1 = v₀ := by omega
        have h2 := hstep (v₀ - 1) (by omega)
        rwa [h1] at h2
      omega

/-- Every first-factor level is visited by the chain. -/
private lemma shuffleVisitsA (S : ProdSimplexShuffle n m)
    (i : Fin (n + 1)) : ∃ k : Fin (n + m + 1), S.projA k = i := by
  classical
  set g : ℕ → ℕ :=
    fun v => if h : v < n + m + 1 then (S.projA ⟨v, h⟩).val else n with hg
  have g0 : g 0 = 0 := by
    simp only [hg]
    rw [dite_eq_left (by omega : (0 : ℕ) < n + m + 1)]
    have hfin : S.projA ⟨0, by omega⟩ = (0 : Fin (n + 1)) := by
      have h0 : (⟨0, by omega⟩ : Fin (n + m + 1)) = 0 := Fin.ext (by rfl)
      rw [h0, S.firstA]
    rw [hfin]
    rfl
  have gN : g (n + m) = n := by
    simp only [hg]
    rw [dite_eq_left (by omega : n + m < n + m + 1)]
    have hlast : (⟨n + m, by omega⟩ : Fin (n + m + 1)) = Fin.last (n + m) :=
      Fin.ext (by rfl)
    rw [hlast, S.lastA]
    rfl
  have hstep : ∀ w : ℕ, w < n + m → g (w + 1) ≤ g w + 1 := by
    intro w hw
    have hw1 : w + 1 < n + m + 1 := by omega
    have hw0 : w < n + m + 1 := by omega
    simp only [hg, dite_eq_left hw1, dite_eq_left hw0]
    obtain ⟨q, hq⟩ : ∃ q : Fin (n + m), q.val = w := ⟨⟨w, hw⟩, rfl⟩
    have f1 : q.succ = (⟨w + 1, hw1⟩ : Fin (n + m + 1)) :=
      Fin.ext (by rw [Fin.val_succ, hq])
    have f0 : q.castSucc = (⟨w, hw0⟩ : Fin (n + m + 1)) :=
      Fin.ext (by rw [Fin.val_castSucc, hq])
    rcases S.step q with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · rw [← f1, ← f0]; omega
    · rw [← f1, ← f0]; omega
  obtain ⟨v, hvN, hgv⟩ :=
    nat_hit_of_mono_step g (n + m) n g0 gN hstep i.val (by omega)
  have hvlt : v < n + m + 1 := by omega
  refine ⟨⟨v, hvlt⟩, ?_⟩
  apply Fin.ext
  have hpos :
      (if h : v < n + m + 1 then (S.projA ⟨v, h⟩).val else n) = i.val := hgv
  rw [dite_eq_left hvlt] at hpos
  exact hpos

/-- Every second-factor level is visited by the chain. -/
private lemma shuffleVisitsB (S : ProdSimplexShuffle n m)
    (j : Fin (m + 1)) : ∃ k : Fin (n + m + 1), S.projB k = j := by
  classical
  set g : ℕ → ℕ :=
    fun v => if h : v < n + m + 1 then (S.projB ⟨v, h⟩).val else m with hg
  have g0 : g 0 = 0 := by
    simp only [hg]
    rw [dite_eq_left (by omega : (0 : ℕ) < n + m + 1)]
    have hfin : S.projB ⟨0, by omega⟩ = (0 : Fin (m + 1)) := by
      have h0 : (⟨0, by omega⟩ : Fin (n + m + 1)) = 0 := Fin.ext (by rfl)
      rw [h0, S.firstB]
    rw [hfin]
    rfl
  have gN : g (n + m) = m := by
    simp only [hg]
    rw [dite_eq_left (by omega : n + m < n + m + 1)]
    have hlast : (⟨n + m, by omega⟩ : Fin (n + m + 1)) = Fin.last (n + m) :=
      Fin.ext (by rfl)
    rw [hlast, S.lastB]
    rfl
  have hstep : ∀ w : ℕ, w < n + m → g (w + 1) ≤ g w + 1 := by
    intro w hw
    have hw1 : w + 1 < n + m + 1 := by omega
    have hw0 : w < n + m + 1 := by omega
    simp only [hg, dite_eq_left hw1, dite_eq_left hw0]
    obtain ⟨q, hq⟩ : ∃ q : Fin (n + m), q.val = w := ⟨⟨w, hw⟩, rfl⟩
    have f1 : q.succ = (⟨w + 1, hw1⟩ : Fin (n + m + 1)) :=
      Fin.ext (by rw [Fin.val_succ, hq])
    have f0 : q.castSucc = (⟨w, hw0⟩ : Fin (n + m + 1)) :=
      Fin.ext (by rw [Fin.val_castSucc, hq])
    rcases S.step q with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · rw [← f1, ← f0]; omega
    · rw [← f1, ← f0]; omega
  obtain ⟨v, hvN, hgv⟩ :=
    nat_hit_of_mono_step g (n + m) m g0 gN hstep j.val (by omega)
  have hvlt : v < n + m + 1 := by omega
  refine ⟨⟨v, hvlt⟩, ?_⟩
  apply Fin.ext
  have hpos :
      (if h : v < n + m + 1 then (S.projB ⟨v, h⟩).val else m) = j.val := hgv
  rw [dite_eq_left hvlt] at hpos
  exact hpos

end ShuffleCombo

section NatProj

variable {n m : ℕ}

/-- First-projection value at a `ℕ` index, junk `n + 1` out of range. -/
private def shuffleAProj (S : ProdSimplexShuffle n m) (v : ℕ) : ℕ :=
  if h : v < n + m + 1 then (S.projA ⟨v, h⟩).val else n + 1

/-- Second-projection value at a `ℕ` index, junk `m + 1` out of range. -/
private def shuffleBProj (S : ProdSimplexShuffle n m) (v : ℕ) : ℕ :=
  if h : v < n + m + 1 then (S.projB ⟨v, h⟩).val else m + 1

/-- The `ℕ` first projection agrees with the `Fin` one in range. -/
private lemma shuffleAProj_val (S : ProdSimplexShuffle n m)
    (k : Fin (n + m + 1)) :
    shuffleAProj S k.val = (S.projA k).val := by
  have hk : k.val < n + m + 1 := k.isLt
  have heta : (⟨k.val, hk⟩ : Fin (n + m + 1)) = k := Fin.ext rfl
  simp only [shuffleAProj, dite_eq_left hk, heta]

/-- The `ℕ` second projection agrees with the `Fin` one in range. -/
private lemma shuffleBProj_val (S : ProdSimplexShuffle n m)
    (k : Fin (n + m + 1)) :
    shuffleBProj S k.val = (S.projB k).val := by
  have hk : k.val < n + m + 1 := k.isLt
  have heta : (⟨k.val, hk⟩ : Fin (n + m + 1)) = k := Fin.ext rfl
  simp only [shuffleBProj, dite_eq_left hk, heta]

/-- The `ℕ` projections sum to the index in range. -/
private lemma shuffleABProj_sum (S : ProdSimplexShuffle n m)
    (v : ℕ) (h : v < n + m + 1) :
    shuffleAProj S v + shuffleBProj S v = v := by
  have hA : shuffleAProj S v = (S.projA ⟨v, h⟩).val := by
    simp only [shuffleAProj, dite_eq_left h]
  have hB : shuffleBProj S v = (S.projB ⟨v, h⟩).val := by
    simp only [shuffleBProj, dite_eq_left h]
  rw [hA, hB]
  have hsum := shuffleLevelSum S ⟨v, h⟩
  simpa using hsum

/-- The `ℕ` first projection is bounded by `n + 1`. -/
private lemma shuffleAProj_le (S : ProdSimplexShuffle n m) (v : ℕ) :
    shuffleAProj S v ≤ n + 1 := by
  by_cases h : v < n + m + 1
  · rw [shuffleAProj]
    rw [dite_eq_left h]
    have hle : (S.projA ⟨v, h⟩).val < n + 1 := (S.projA ⟨v, h⟩).isLt
    omega
  · simp only [shuffleAProj, dite_eq_right h, le_refl]

/-- The `ℕ` second projection is bounded by `m + 1`. -/
private lemma shuffleBProj_le (S : ProdSimplexShuffle n m) (v : ℕ) :
    shuffleBProj S v ≤ m + 1 := by
  by_cases h : v < n + m + 1
  · rw [shuffleBProj]
    rw [dite_eq_left h]
    have hle : (S.projB ⟨v, h⟩).val < m + 1 := (S.projB ⟨v, h⟩).isLt
    omega
  · simp only [shuffleBProj, dite_eq_right h, le_refl]

/-- The `ℕ` first projection is monotone. -/
private lemma shuffleAProj_mono (S : ProdSimplexShuffle n m) :
    Monotone (shuffleAProj S) := by
  intro a b hab
  by_cases hb : b < n + m + 1
  · have ha : a < n + m + 1 := by omega
    have hA : shuffleAProj S a = (S.projA ⟨a, ha⟩).val := by
      simp only [shuffleAProj, dite_eq_left ha]
    have hB : shuffleAProj S b = (S.projA ⟨b, hb⟩).val := by
      simp only [shuffleAProj, dite_eq_left hb]
    rw [hA, hB]
    have hle : (⟨a, ha⟩ : Fin (n + m + 1)) ≤ ⟨b, hb⟩ :=
      Fin.le_def.mpr (by simpa using hab)
    exact Fin.le_def.mp (S.monoA hle)
  · have hB : shuffleAProj S b = n + 1 := by
      simp only [shuffleAProj, dite_eq_right hb]
    rw [hB]
    exact shuffleAProj_le S a

/-- The `ℕ` second projection is monotone. -/
private lemma shuffleBProj_mono (S : ProdSimplexShuffle n m) :
    Monotone (shuffleBProj S) := by
  intro a b hab
  by_cases hb : b < n + m + 1
  · have ha : a < n + m + 1 := by omega
    have hA : shuffleBProj S a = (S.projB ⟨a, ha⟩).val := by
      simp only [shuffleBProj, dite_eq_left ha]
    have hB : shuffleBProj S b = (S.projB ⟨b, hb⟩).val := by
      simp only [shuffleBProj, dite_eq_left hb]
    rw [hA, hB]
    have hle : (⟨a, ha⟩ : Fin (n + m + 1)) ≤ ⟨b, hb⟩ :=
      Fin.le_def.mpr (by simpa using hab)
    exact Fin.le_def.mp (S.monoB hle)
  · have hB : shuffleBProj S b = m + 1 := by
      unfold shuffleBProj
      rw [dite_eq_right hb]
    rw [hB]
    exact shuffleBProj_le S a

end NatProj

section Overlap

variable {n m : ℕ}

/-- Cumulative overlap description for one shuffle cell: at every chain vertex
the strict mass below the chain level in each factor is at most the weak mass
through the chain level in the other factor. By the forward implications this
is necessary for range membership; the range equivalence shows it is also
sufficient. -/
def shuffleCumOverlap (S : ProdSimplexShuffle n m)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (y : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    Prop :=
  ∀ k : Fin (n + m + 1),
    shuffleCumBefore x (S.projA k).val ≤ shuffleCumThrough y (S.projB k).val ∧
    shuffleCumBefore y (S.projB k).val ≤ shuffleCumThrough x (S.projA k).val

end Overlap

section Source

variable {n m : ℕ}

/-- Common cumulative cut at a chain vertex: the shared mass level of the two
weak cumulative sums. -/
private noncomputable def shuffleCut (S : ProdSimplexShuffle n m)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (y : Convexity.StdSimplex ℝ (Fin (m + 1)))
    (k : Fin (n + m + 1)) : ℝ :=
  min (shuffleCumThrough x (S.projA k).val)
    (shuffleCumThrough y (S.projB k).val)

/-- Common cut at a `ℕ` index, junk `0` out of range. -/
private noncomputable def shuffleCutExt (S : ProdSimplexShuffle n m)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (y : Convexity.StdSimplex ℝ (Fin (m + 1)))
    (v : ℕ) : ℝ :=
  if h : v < n + m + 1 then shuffleCut S x y ⟨v, h⟩ else 0

/-- The common cut agrees with the `Fin` cut in range. -/
private lemma shuffleCutExt_eq (S : ProdSimplexShuffle n m)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (y : Convexity.StdSimplex ℝ (Fin (m + 1)))
    (v : ℕ) (h : v < n + m + 1) :
    shuffleCutExt S x y v = shuffleCut S x y ⟨v, h⟩ := by
  simp only [shuffleCutExt, dite_eq_left h]

/-- The common cut is nonnegative. -/
private lemma shuffleCut_nonneg (S : ProdSimplexShuffle n m)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (y : Convexity.StdSimplex ℝ (Fin (m + 1)))
    (k : Fin (n + m + 1)) : 0 ≤ shuffleCut S x y k := by
  unfold shuffleCut
  exact le_min (shuffleCumThrough_nonneg x _) (shuffleCumThrough_nonneg y _)

/-- The common cut is monotone along the chain. -/
private lemma shuffleCut_mono_val (S : ProdSimplexShuffle n m)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (y : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    Monotone (fun k : Fin (n + m + 1) => shuffleCut S x y k) := by
  intro a b hab
  unfold shuffleCut
  apply min_le_min
  · exact shuffleCumThrough_mono x (Fin.le_def.mp (S.monoA hab))
  · exact shuffleCumThrough_mono y (Fin.le_def.mp (S.monoB hab))

/-- The common cut at the last vertex is `1`. -/
private lemma shuffleCut_last (S : ProdSimplexShuffle n m)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (y : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    shuffleCut S x y (Fin.last (n + m)) = 1 := by
  have hA : (S.projA (Fin.last (n + m))).val = n := shufA_last S
  have hB : (S.projB (Fin.last (n + m))).val = m := shufB_last S
  unfold shuffleCut
  rw [hA, hB, shuffleCumThrough_last, shuffleCumThrough_last, min_self]

/-- Reconstructed source coordinate: common-cut difference. -/
private noncomputable def shuffleCellSourceFun (S : ProdSimplexShuffle n m)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (y : Convexity.StdSimplex ℝ (Fin (m + 1)))
    (k : Fin (n + m + 1)) : ℝ :=
  shuffleCutExt S x y k.val -
    (if _ : 0 < k.val then shuffleCutExt S x y (k.val - 1) else 0)

/-- Reconstructed coordinates are nonnegative. -/
private lemma shuffleCellSourceFun_nonneg (S : ProdSimplexShuffle n m)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (y : Convexity.StdSimplex ℝ (Fin (m + 1)))
    (k : Fin (n + m + 1)) : 0 ≤ shuffleCellSourceFun S x y k := by
  unfold shuffleCellSourceFun
  by_cases hk : 0 < k.val
  · rw [dite_eq_left hk]
    have hklt := k.isLt
    have hle : k.val - 1 < n + m + 1 := by omega
    rw [shuffleCutExt_eq S x y _ hle]
    have hj : (⟨k.val - 1, hle⟩ : Fin (n + m + 1)) ≤ k :=
      Fin.le_def.mpr (Nat.sub_le _ _)
    have hcut := shuffleCut_mono_val S x y hj
    have heq : shuffleCutExt S x y k.val = shuffleCut S x y k := by
      have hkk : k.val < n + m + 1 := k.isLt
      have heta : (⟨k.val, hkk⟩ : Fin (n + m + 1)) = k := Fin.ext rfl
      simp only [shuffleCutExt, dite_eq_left hkk, heta]
    rw [heq]
    linarith [hcut]
  · rw [dite_eq_right hk]
    have hkk : k.val < n + m + 1 := k.isLt
    have heta : (⟨k.val, hkk⟩ : Fin (n + m + 1)) = k := Fin.ext rfl
    have hcut := shuffleCut_nonneg S x y k
    have heq : shuffleCutExt S x y k.val = shuffleCut S x y k := by
      simp only [shuffleCutExt, dite_eq_left hkk, heta]
    rw [heq]
    linarith [hcut]

/-- A `Fin` filter sum by index value is a `ℕ` range sum. -/
private lemma sum_filter_val_eq_sum_range (N : ℕ) (g : ℕ → ℝ)
    (P : ℕ → Prop) [DecidablePred P] (f : Fin (N + 1) → ℝ)
    (hf : ∀ k : Fin (N + 1), f k = g k.val) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin (N + 1) => P k.val), f k =
      ∑ v ∈ (Finset.range (N + 1)).filter P, g v := by
  simp only [hf]
  apply Finset.sum_bij (fun k _ => k.val)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range] at hk ⊢
    exact ⟨k.isLt, hk⟩
  · intro a₁ _ a₂ _ h
    exact Fin.ext h
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_range] at hv
    obtain ⟨hvN, hPv⟩ := hv
    exact ⟨⟨v, hvN⟩, by simpa using hPv, rfl⟩
  · intro k _
    rfl

/-- Telescoping of cut differences over a `ℕ` range. -/
private lemma sum_range_cutDiff (c : ℕ → ℝ) (N : ℕ) :
    ∑ v ∈ Finset.range (N + 1),
        (c v - (if _ : 0 < v then c (v - 1) else 0)) = c N := by
  induction N with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_zero,
      dite_eq_right (Nat.not_lt_zero 0), sub_zero, zero_add]
  | succ N IH =>
    have hterm :
        c (N + 1) - (if _ : 0 < N + 1 then c (N + 1 - 1) else 0) =
          c (N + 1) - c N := by
      rw [dite_eq_left (by omega : 0 < N + 1), Nat.add_sub_cancel]
    rw [Finset.sum_range_succ, IH, hterm]
    ring

/-- Telescoping of cut differences over a `ℕ` interval. -/
private lemma sum_Icc_cutDiff (c : ℕ → ℝ) (lo hi : ℕ) (h : lo ≤ hi) :
    ∑ v ∈ Finset.Icc lo hi,
        (c v - (if _ : 0 < v then c (v - 1) else 0)) =
      c hi - (if _ : 0 < lo then c (lo - 1) else 0) := by
  induction hi, h using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton]
  | succ hi hle IH =>
    have hset : Finset.Icc lo (hi + 1) = insert (hi + 1) (Finset.Icc lo hi) := by
      ext v
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hmem : hi + 1 ∉ Finset.Icc lo hi := by
      simp only [Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert hmem, IH]
    have hpos : (if _ : 0 < hi + 1 then c (hi + 1 - 1) else 0) = c hi := by
      rw [dite_eq_left (by omega : 0 < hi + 1), Nat.add_sub_cancel]
    rw [hpos]
    ring

/-- Reconstructed coordinates sum to `1`. -/
private lemma shuffleCellSourceFun_sum (S : ProdSimplexShuffle n m)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (y : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    ∑ k : Fin (n + m + 1), shuffleCellSourceFun S x y k = 1 := by
  have huniv : (Finset.univ : Finset (Fin (n + m + 1))) =
      Finset.univ.filter (fun _ : Fin (n + m + 1) => True) := by simp
  rw [huniv]
  have htrans := sum_filter_val_eq_sum_range (n + m)
    (fun v => shuffleCutExt S x y v -
      (if _ : 0 < v then shuffleCutExt S x y (v - 1) else 0))
    (fun _ => True) (shuffleCellSourceFun S x y) (fun k => rfl)
  rw [htrans] at *
  have htrue : (Finset.range (n + m + 1)).filter (fun _ => True) =
      Finset.range (n + m + 1) :=
    Finset.filter_true_of_mem (fun v _ => trivial)
  rw [htrue]
  have htel := sum_range_cutDiff (shuffleCutExt S x y) (n + m)
  rw [htel]
  have hlast : n + m < n + m + 1 := by omega
  have heq : shuffleCutExt S x y (n + m) =
      shuffleCut S x y (Fin.last (n + m)) := by
    rw [shuffleCutExt_eq S x y _ hlast]
    congr 1
  rw [heq, shuffleCut_last]

/-- The packaged reconstructed source point. -/
private noncomputable def shuffleCellSource (S : ProdSimplexShuffle n m)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (y : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    Convexity.StdSimplex ℝ (Fin (n + m + 1)) :=
  { weights := Finsupp.equivFunOnFinite.symm (shuffleCellSourceFun S x y)
    nonneg m := by simpa using shuffleCellSourceFun_nonneg S x y m
    total := by
      simpa [Finsupp.sum_fintype] using shuffleCellSourceFun_sum S x y }

end Source

section RecoveryA

variable {n m : ℕ}

/-- First-factor fiber sum of the reconstructed source is the atom. The fiber
is the index interval between its first and last occurrence; the sum
telescopes to the common cut at the last occurrence minus the cut before the
first, identified by the overlap hypotheses as weak minus strict mass. -/
private lemma shuffleFiberA_sum (S : ProdSimplexShuffle n m)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (y : Convexity.StdSimplex ℝ (Fin (m + 1)))
    (h : shuffleCumOverlap S x y) (i : Fin (n + 1)) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin (n + m + 1) => S.projA k = i),
        shuffleCellSourceFun S x y k =
      x.weights i := by
  have hfib : Finset.univ.filter (fun k : Fin (n + m + 1) => S.projA k = i) =
      Finset.univ.filter
        (fun k : Fin (n + m + 1) => shuffleAProj S k.val = i.val) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hkk
      rw [shuffleAProj_val S k, congrArg Fin.val hkk]
    · intro hkk
      have hkkv : (S.projA k).val = i.val := by
        rw [← shuffleAProj_val S k, hkk]
      exact Fin.ext hkkv
  rw [hfib]
  have htrans := sum_filter_val_eq_sum_range (n + m)
    (fun v => shuffleCutExt S x y v -
      (if _ : 0 < v then shuffleCutExt S x y (v - 1) else 0))
    (fun v => shuffleAProj S v = i.val) (shuffleCellSourceFun S x y) (fun k => rfl)
  rw [htrans]
  have hQ : ∃ v, v < n + m + 1 ∧ shuffleAProj S v = i.val := by
    obtain ⟨k, hk⟩ := shuffleVisitsA S i
    exact ⟨k.val, k.isLt, by rw [shuffleAProj_val S k, congrArg Fin.val hk]⟩
  classical
  set lo := Nat.find hQ with hlo_def
  have hlo_mem : lo < n + m + 1 ∧ shuffleAProj S lo = i.val :=
    Nat.find_spec hQ
  have hlo_min : ∀ w, w < n + m + 1 → shuffleAProj S w = i.val → lo ≤ w := by
    intro w hw haw
    exact Nat.find_min' hQ ⟨hw, haw⟩
  obtain ⟨lo_lt, lo_eq⟩ := hlo_mem
  set S₁ := (Finset.range (n + m + 1)).filter
    (fun v => shuffleAProj S v = i.val) with hS₁def
  have hne : S₁.Nonempty := ⟨lo, by simp [hS₁def, lo_lt, lo_eq]⟩
  set hi := Finset.max' S₁ hne with hhi_def
  have hhi_mem : hi ∈ S₁ := Finset.max'_mem S₁ hne
  have hhi_max : ∀ w ∈ S₁, w ≤ hi := fun w hw => Finset.le_max' S₁ w hw
  have hhi_lt : hi < n + m + 1 := by
    have hmem : hi ∈ (Finset.range (n + m + 1)).filter
        (fun v => shuffleAProj S v = i.val) := hhi_mem
    simp only [Finset.mem_filter, Finset.mem_range] at hmem
    exact hmem.1
  have hhi_eq : shuffleAProj S hi = i.val := by
    have hmem : hi ∈ (Finset.range (n + m + 1)).filter
        (fun v => shuffleAProj S v = i.val) := hhi_mem
    simp only [Finset.mem_filter] at hmem
    exact hmem.2
  have hset : (Finset.range (n + m + 1)).filter
      (fun v => shuffleAProj S v = i.val) = Finset.Icc lo hi := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, hS₁def] at *
    constructor
    · intro hv
      obtain ⟨hvN, hav⟩ := hv
      exact ⟨hlo_min v hvN hav, hhi_max v (by simp [hvN, hav])⟩
    · intro hv
      obtain ⟨hlv, hvh⟩ := hv
      have hvN : v < n + m + 1 := by omega
      refine ⟨hvN, ?_⟩
      have h1 : shuffleAProj S lo ≤ shuffleAProj S v :=
        shuffleAProj_mono S hlv
      have h2 : shuffleAProj S v ≤ shuffleAProj S hi :=
        shuffleAProj_mono S hvh
      omega
  rw [hS₁def, hset, sum_Icc_cutDiff _ _ _ (by
    have hle : lo ≤ hi := hhi_max lo (by simp [hS₁def, lo_lt, lo_eq])
    exact hle)]
  have hhi_cut : shuffleCutExt S x y hi = shuffleCumThrough x i.val := by
    rw [shuffleCutExt_eq S x y _ hhi_lt]
    unfold shuffleCut
    have hAi : shuffleCumThrough x i.val ≤
        shuffleCumThrough y (shuffleBProj S hi) := by
      by_cases hN : hi < n + m
      · have hqN : hi < n + m := hN
        have harr : hi + 1 < n + m + 1 := by omega
        have hAi1 : shuffleAProj S (hi + 1) = i.val + 1 := by
          have hne' : shuffleAProj S (hi + 1) ≠ i.val := by
            intro hcon
            have hmem' : hi + 1 ∈ S₁ := by
              simp [hS₁def, Finset.mem_filter, harr, hcon]
            have := hhi_max (hi + 1) hmem'
            omega
          have hge : i.val ≤ shuffleAProj S (hi + 1) := by
            have hle : hi ≤ hi + 1 := by omega
            have hmono := shuffleAProj_mono S hle
            omega
          have hle1 : shuffleAProj S (hi + 1) ≤ shuffleAProj S hi + 1 := by
            obtain ⟨q, hq⟩ : ∃ q : Fin (n + m), q.val = hi := ⟨⟨hi, hqN⟩, rfl⟩
            have f1 : q.succ = (⟨hi + 1, harr⟩ : Fin (n + m + 1)) :=
              Fin.ext (by rw [Fin.val_succ, hq])
            have f0 : q.castSucc = (⟨hi, hhi_lt⟩ : Fin (n + m + 1)) :=
              Fin.ext (by rw [Fin.val_castSucc, hq])
            have g1 : shuffleAProj S (hi + 1) = (S.projA q.succ).val := by
              have e1 : shuffleAProj S (hi + 1) =
                  (S.projA ⟨hi + 1, harr⟩).val := by
                simp only [shuffleAProj, dite_eq_left harr]
              rw [e1, f1]
            have g0 : shuffleAProj S hi = (S.projA q.castSucc).val := by
              have e0 : shuffleAProj S hi =
                  (S.projA ⟨hi, hhi_lt⟩).val := by
                simp only [shuffleAProj, dite_eq_left hhi_lt]
              rw [e0, f0]
            rcases S.step q with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;> omega
          omega
        have hBsame : shuffleBProj S (hi + 1) = shuffleBProj S hi := by
          obtain ⟨q, hq⟩ : ∃ q : Fin (n + m), q.val = hi := ⟨⟨hi, hqN⟩, rfl⟩
          have f1 : q.succ = (⟨hi + 1, harr⟩ : Fin (n + m + 1)) :=
            Fin.ext (by rw [Fin.val_succ, hq])
          have f0 : q.castSucc = (⟨hi, hhi_lt⟩ : Fin (n + m + 1)) :=
            Fin.ext (by rw [Fin.val_castSucc, hq])
          have g1 : shuffleBProj S (hi + 1) = (S.projB q.succ).val := by
            have e1 : shuffleBProj S (hi + 1) =
                (S.projB ⟨hi + 1, harr⟩).val := by
              simp only [shuffleBProj, dite_eq_left harr]
            rw [e1, f1]
          have g0 : shuffleBProj S hi = (S.projB q.castSucc).val := by
            have e0 : shuffleBProj S hi =
                (S.projB ⟨hi, hhi_lt⟩).val := by
              simp only [shuffleBProj, dite_eq_left hhi_lt]
            rw [e0, f0]
          rcases S.step q with ⟨hA, hB⟩ | ⟨hA, hB⟩
          · omega
          · exfalso
            have g1A : shuffleAProj S (hi + 1) = (S.projA q.succ).val := by
              have e1 : shuffleAProj S (hi + 1) =
                  (S.projA ⟨hi + 1, harr⟩).val := by
                simp only [shuffleAProj, dite_eq_left harr]
              rw [e1, f1]
            have g0A : shuffleAProj S hi = (S.projA q.castSucc).val := by
              have e0 : shuffleAProj S hi =
                  (S.projA ⟨hi, hhi_lt⟩).val := by
                simp only [shuffleAProj, dite_eq_left hhi_lt]
              rw [e0, f0]
            have hAeq : shuffleAProj S (hi + 1) = shuffleAProj S hi := by
              omega
            omega
        obtain ⟨karr, hkarr⟩ : ∃ karr : Fin (n + m + 1),
            karr.val = hi + 1 := ⟨⟨hi + 1, harr⟩, rfl⟩
        have hov := h (⟨hi + 1, harr⟩)
        obtain ⟨hovAB, -⟩ := hov
        have eA : (S.projA ⟨hi + 1, harr⟩).val = i.val + 1 := by
          have : shuffleAProj S (hi + 1) = (S.projA ⟨hi + 1, harr⟩).val := by
            simp only [shuffleAProj, dite_eq_left harr]
          omega
        have eB : (S.projB ⟨hi + 1, harr⟩).val = shuffleBProj S hi := by
          have : shuffleBProj S (hi + 1) =
              (S.projB ⟨hi + 1, harr⟩).val := by
            simp only [shuffleBProj, dite_eq_left harr]
          omega
        rw [eA, eB] at hovAB
        rw [shuffleCumBefore_succ_eq_through] at hovAB
        exact hovAB
      · have hN : hi = n + m := by omega
        have hsum := shuffleABProj_sum S hi hhi_lt
        have hnm : n + m < n + m + 1 := by omega
        have hlast : (⟨n + m, hnm⟩ : Fin (n + m + 1)) = Fin.last (n + m) :=
          Fin.ext (by rfl)
        have hbi : shuffleBProj S hi = m := by
          have e : shuffleBProj S hi = shuffleBProj S (n + m) := by rw [hN]
          have e2 : shuffleBProj S (n + m) = (S.projB ⟨n + m, hnm⟩).val := by
            simp only [shuffleBProj, dite_eq_left hnm]
          rw [e, e2, hlast, shufB_last]
        have hai : i.val = n := by omega
        rw [hai, hbi, shuffleCumThrough_last, shuffleCumThrough_last]
    have hAeq : (S.projA ⟨hi, hhi_lt⟩).val = i.val := by
      have : shuffleAProj S hi = (S.projA ⟨hi, hhi_lt⟩).val := by
        simp only [shuffleAProj, dite_eq_left hhi_lt]
      omega
    have hBeq : shuffleBProj S hi = (S.projB ⟨hi, hhi_lt⟩).val := by
      simp only [shuffleBProj, dite_eq_left hhi_lt]
    rw [hAeq, ← hBeq, min_eq_left hAi]
  have hlo_pred : (if _ : 0 < lo then shuffleCutExt S x y (lo - 1) else 0) =
      shuffleCumBefore x i.val := by
    by_cases hlo0 : lo = 0
    · rw [hlo0]
      rw [dite_eq_right (lt_irrefl 0)]
      have hi0 : i.val = 0 := by
        have h0 : shuffleAProj S 0 = 0 := by
          have hz : (0 : ℕ) < n + m + 1 := by omega
          have e0 : shuffleAProj S 0 = (S.projA ⟨0, hz⟩).val := by
            simp only [shuffleAProj, dite_eq_left hz]
          have z0 : (⟨0, hz⟩ : Fin (n + m + 1)) = 0 := by
            apply Fin.ext
            simp
          rw [e0, z0, S.firstA]
          rfl
        rw [← lo_eq, hlo0, h0]
      rw [hi0, shuffleCumBefore_zero]
    · have hpos : 0 < lo := by omega
      rw [dite_eq_left hpos]
      have hlo1 : lo - 1 < n + m + 1 := by omega
      rw [shuffleCutExt_eq S x y _ hlo1]
      unfold shuffleCut
      have ha' : shuffleAProj S (lo - 1) = i.val - 1 := by
        have hlt1 : shuffleAProj S (lo - 1) < i.val := by
          by_contra hle
          have hge : i.val ≤ shuffleAProj S (lo - 1) := not_lt.mp hle
          have hle2 : shuffleAProj S (lo - 1) ≤ shuffleAProj S lo :=
            shuffleAProj_mono S (by omega)
          have heq2 : shuffleAProj S (lo - 1) = i.val := by omega
          have hmem' : lo - 1 < n + m + 1 ∧
              shuffleAProj S (lo - 1) = i.val := ⟨by omega, heq2⟩
          have := hlo_min (lo - 1) hmem'.1 hmem'.2
          omega
        have hge1 : i.val - 1 ≤ shuffleAProj S (lo - 1) := by
          have hstep : shuffleAProj S lo ≤ shuffleAProj S (lo - 1) + 1 := by
            have hN : lo - 1 < n + m := by omega
            obtain ⟨q, hq⟩ : ∃ q : Fin (n + m), q.val = lo - 1 :=
              ⟨⟨lo - 1, hN⟩, rfl⟩
            have harr : lo < n + m + 1 := lo_lt
            have hlo_eq : lo - 1 + 1 = lo := by omega
            have f1 : q.succ = (⟨lo, harr⟩ : Fin (n + m + 1)) := by
              apply Fin.ext
              rw [Fin.val_succ, hq, hlo_eq]
            have f0 : q.castSucc = (⟨lo - 1, hlo1⟩ : Fin (n + m + 1)) := by
              apply Fin.ext
              rw [Fin.val_castSucc, hq]
            have g1 : shuffleAProj S lo = (S.projA q.succ).val := by
              have e1 : shuffleAProj S lo =
                  (S.projA ⟨lo, harr⟩).val := by
                simp only [shuffleAProj, dite_eq_left harr]
              rw [e1, f1]
            have g0 : shuffleAProj S (lo - 1) =
                (S.projA q.castSucc).val := by
              have e0 : shuffleAProj S (lo - 1) =
                  (S.projA ⟨lo - 1, hlo1⟩).val := by
                simp only [shuffleAProj, dite_eq_left hlo1]
              rw [e0, f0]
            rcases S.step q with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;> omega
          omega
        omega
      have hb' : shuffleBProj S (lo - 1) = shuffleBProj S lo := by
        have hN : lo - 1 < n + m := by omega
        obtain ⟨q, hq⟩ : ∃ q : Fin (n + m), q.val = lo - 1 :=
          ⟨⟨lo - 1, hN⟩, rfl⟩
        have harr : lo < n + m + 1 := lo_lt
        have hlo_eq : lo - 1 + 1 = lo := by omega
        have f1 : q.succ = (⟨lo, harr⟩ : Fin (n + m + 1)) :=
          Fin.ext (by rw [Fin.val_succ, hq, hlo_eq])
        have f0 : q.castSucc = (⟨lo - 1, hlo1⟩ : Fin (n + m + 1)) :=
          Fin.ext (by rw [Fin.val_castSucc, hq])
        have g1 : shuffleAProj S lo = (S.projA q.succ).val := by
          have e1 : shuffleAProj S lo =
              (S.projA ⟨lo, harr⟩).val := by
            simp only [shuffleAProj, dite_eq_left harr]
          rw [e1, f1]
        have g0 : shuffleAProj S (lo - 1) = (S.projA q.castSucc).val := by
          have e0 : shuffleAProj S (lo - 1) =
              (S.projA ⟨lo - 1, hlo1⟩).val := by
            simp only [shuffleAProj, dite_eq_left hlo1]
          rw [e0, f0]
        have hB1 : shuffleBProj S lo = (S.projB q.succ).val := by
          have e1 : shuffleBProj S lo =
              (S.projB ⟨lo, harr⟩).val := by
            simp only [shuffleBProj, dite_eq_left harr]
          rw [e1, f1]
        have hB0 : shuffleBProj S (lo - 1) = (S.projB q.castSucc).val := by
          have e0 : shuffleBProj S (lo - 1) =
              (S.projB ⟨lo - 1, hlo1⟩).val := by
            simp only [shuffleBProj, dite_eq_left hlo1]
          rw [e0, f0]
        rcases S.step q with ⟨hA, hB⟩ | ⟨hA, hB⟩
        · omega
        · exfalso
          have hAeq' : shuffleAProj S (lo - 1) = i.val := by omega
          have hle := hlo_min (lo - 1) hlo1 hAeq'
          omega
      have hiv : 0 < i.val := by
        by_contra hle
        have hi0 : i.val = 0 := by omega
        have h0mem : (0 : ℕ) < n + m + 1 ∧ shuffleAProj S 0 = i.val := by
          refine ⟨by omega, ?_⟩
          have hz : (0 : ℕ) < n + m + 1 := by omega
          have e0 : shuffleAProj S 0 = (S.projA ⟨0, hz⟩).val := by
            simp only [shuffleAProj, dite_eq_left hz]
          have z0 : (⟨0, hz⟩ : Fin (n + m + 1)) = 0 := Fin.ext (by rfl)
          rw [e0, z0, S.firstA, hi0]
          rfl
        have := hlo_min 0 h0mem.1 h0mem.2
        omega
      have hmin_eq : min (shuffleCumThrough x (shuffleAProj S (lo - 1)))
          (shuffleCumThrough y (shuffleBProj S (lo - 1))) =
          shuffleCumThrough x (i.val - 1) := by
        have hov := h (⟨lo, lo_lt⟩)
        obtain ⟨hovAB, -⟩ := hov
        have eA : (S.projA ⟨lo, lo_lt⟩).val = i.val := by
          have : shuffleAProj S lo = (S.projA ⟨lo, lo_lt⟩).val := by
            simp only [shuffleAProj, dite_eq_left lo_lt]
          omega
        have eB : (S.projB ⟨lo, lo_lt⟩).val = shuffleBProj S lo := by
          simp only [shuffleBProj, dite_eq_left lo_lt]
        rw [eA, eB] at hovAB
        have hbs : shuffleCumBefore x i.val =
            shuffleCumThrough x (i.val - 1) := by
          have hsucc : i.val - 1 + 1 = i.val := by omega
          have hbs2 := shuffleCumBefore_succ_eq_through x (i.val - 1)
          rwa [hsucc] at hbs2
        rw [hbs] at hovAB
        rw [ha', hb']
        exact min_eq_left hovAB
      have hAeq2 : (S.projA ⟨lo - 1, hlo1⟩).val =
          shuffleAProj S (lo - 1) := by
        simp only [shuffleAProj, dite_eq_left hlo1]
      have hBeq2 : (S.projB ⟨lo - 1, hlo1⟩).val =
          shuffleBProj S (lo - 1) := by
        simp only [shuffleBProj, dite_eq_left hlo1]
      rw [hAeq2, hBeq2, hmin_eq]
      have hbs : shuffleCumBefore x i.val =
          shuffleCumThrough x (i.val - 1) := by
        have hsucc : i.val - 1 + 1 = i.val := by omega
        have hbs2 := shuffleCumBefore_succ_eq_through x (i.val - 1)
        rwa [hsucc] at hbs2
      exact hbs.symm
  rw [hhi_cut, hlo_pred]
  have hsplit := shuffleCumThrough_eq_before_add x i
  linarith [hsplit]

end RecoveryA

section RecoveryB

variable {n m : ℕ}

/-- Second-factor fiber sum of the reconstructed source is the atom. Symmetric
to the first-factor recovery with the roles of the projections exchanged. -/
private lemma shuffleFiberB_sum (S : ProdSimplexShuffle n m)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (y : Convexity.StdSimplex ℝ (Fin (m + 1)))
    (h : shuffleCumOverlap S x y) (j : Fin (m + 1)) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin (n + m + 1) => S.projB k = j),
        shuffleCellSourceFun S x y k =
      y.weights j := by
  have hfib : Finset.univ.filter (fun k : Fin (n + m + 1) => S.projB k = j) =
      Finset.univ.filter
        (fun k : Fin (n + m + 1) => shuffleBProj S k.val = j.val) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hkk
      rw [shuffleBProj_val S k, congrArg Fin.val hkk]
    · intro hkk
      have hkkv : (S.projB k).val = j.val := by
        rw [← shuffleBProj_val S k, hkk]
      exact Fin.ext hkkv
  rw [hfib]
  have htrans := sum_filter_val_eq_sum_range (n + m)
    (fun v => shuffleCutExt S x y v -
      (if _ : 0 < v then shuffleCutExt S x y (v - 1) else 0))
    (fun v => shuffleBProj S v = j.val) (shuffleCellSourceFun S x y) (fun k => rfl)
  rw [htrans]
  have hQ : ∃ v, v < n + m + 1 ∧ shuffleBProj S v = j.val := by
    obtain ⟨k, hk⟩ := shuffleVisitsB S j
    exact ⟨k.val, k.isLt, by rw [shuffleBProj_val S k, congrArg Fin.val hk]⟩
  classical
  set lo := Nat.find hQ with hlo_def
  have hlo_mem : lo < n + m + 1 ∧ shuffleBProj S lo = j.val :=
    Nat.find_spec hQ
  have hlo_min : ∀ w, w < n + m + 1 → shuffleBProj S w = j.val → lo ≤ w := by
    intro w hw haw
    exact Nat.find_min' hQ ⟨hw, haw⟩
  obtain ⟨lo_lt, lo_eq⟩ := hlo_mem
  set S₁ := (Finset.range (n + m + 1)).filter
    (fun v => shuffleBProj S v = j.val) with hS₁def
  have hne : S₁.Nonempty := ⟨lo, by simp [hS₁def, lo_lt, lo_eq]⟩
  set hi := Finset.max' S₁ hne with hhi_def
  have hhi_mem : hi ∈ S₁ := Finset.max'_mem S₁ hne
  have hhi_max : ∀ w ∈ S₁, w ≤ hi := fun w hw => Finset.le_max' S₁ w hw
  have hhi_lt : hi < n + m + 1 := by
    have hmem : hi ∈ (Finset.range (n + m + 1)).filter
        (fun v => shuffleBProj S v = j.val) := hhi_mem
    simp only [Finset.mem_filter, Finset.mem_range] at hmem
    exact hmem.1
  have hhi_eq : shuffleBProj S hi = j.val := by
    have hmem : hi ∈ (Finset.range (n + m + 1)).filter
        (fun v => shuffleBProj S v = j.val) := hhi_mem
    simp only [Finset.mem_filter] at hmem
    exact hmem.2
  have hset : (Finset.range (n + m + 1)).filter
      (fun v => shuffleBProj S v = j.val) = Finset.Icc lo hi := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, hS₁def] at *
    constructor
    · intro hv
      obtain ⟨hvN, hav⟩ := hv
      exact ⟨hlo_min v hvN hav, hhi_max v (by simp [hvN, hav])⟩
    · intro hv
      obtain ⟨hlv, hvh⟩ := hv
      have hvN : v < n + m + 1 := by omega
      refine ⟨hvN, ?_⟩
      have h1 : shuffleBProj S lo ≤ shuffleBProj S v :=
        shuffleBProj_mono S hlv
      have h2 : shuffleBProj S v ≤ shuffleBProj S hi :=
        shuffleBProj_mono S hvh
      omega
  rw [hS₁def, hset, sum_Icc_cutDiff _ _ _ (by
    have hle : lo ≤ hi := hhi_max lo (by simp [hS₁def, lo_lt, lo_eq])
    exact hle)]
  have hhi_cut : shuffleCutExt S x y hi = shuffleCumThrough y j.val := by
    rw [shuffleCutExt_eq S x y _ hhi_lt]
    unfold shuffleCut
    have hBi : shuffleCumThrough y j.val ≤
        shuffleCumThrough x (shuffleAProj S hi) := by
      by_cases hN : hi < n + m
      · have hqN : hi < n + m := hN
        have harr : hi + 1 < n + m + 1 := by omega
        have hBi1 : shuffleBProj S (hi + 1) = j.val + 1 := by
          have hne' : shuffleBProj S (hi + 1) ≠ j.val := by
            intro hcon
            have hmem' : hi + 1 ∈ S₁ := by
              simp [hS₁def, Finset.mem_filter, harr, hcon]
            have := hhi_max (hi + 1) hmem'
            omega
          have hge : j.val ≤ shuffleBProj S (hi + 1) := by
            have hle : hi ≤ hi + 1 := by omega
            have hmono := shuffleBProj_mono S hle
            omega
          have hle1 : shuffleBProj S (hi + 1) ≤ shuffleBProj S hi + 1 := by
            obtain ⟨q, hq⟩ : ∃ q : Fin (n + m), q.val = hi := ⟨⟨hi, hqN⟩, rfl⟩
            have f1 : q.succ = (⟨hi + 1, harr⟩ : Fin (n + m + 1)) :=
              Fin.ext (by rw [Fin.val_succ, hq])
            have f0 : q.castSucc = (⟨hi, hhi_lt⟩ : Fin (n + m + 1)) :=
              Fin.ext (by rw [Fin.val_castSucc, hq])
            have g1 : shuffleBProj S (hi + 1) = (S.projB q.succ).val := by
              have e1 : shuffleBProj S (hi + 1) =
                  (S.projB ⟨hi + 1, harr⟩).val := by
                simp only [shuffleBProj, dite_eq_left harr]
              rw [e1, f1]
            have g0 : shuffleBProj S hi = (S.projB q.castSucc).val := by
              have e0 : shuffleBProj S hi =
                  (S.projB ⟨hi, hhi_lt⟩).val := by
                simp only [shuffleBProj, dite_eq_left hhi_lt]
              rw [e0, f0]
            rcases S.step q with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;> omega
          omega
        have hAsame : shuffleAProj S (hi + 1) = shuffleAProj S hi := by
          obtain ⟨q, hq⟩ : ∃ q : Fin (n + m), q.val = hi := ⟨⟨hi, hqN⟩, rfl⟩
          have f1 : q.succ = (⟨hi + 1, harr⟩ : Fin (n + m + 1)) :=
            Fin.ext (by rw [Fin.val_succ, hq])
          have f0 : q.castSucc = (⟨hi, hhi_lt⟩ : Fin (n + m + 1)) :=
            Fin.ext (by rw [Fin.val_castSucc, hq])
          have g1 : shuffleAProj S (hi + 1) = (S.projA q.succ).val := by
            have e1 : shuffleAProj S (hi + 1) =
                (S.projA ⟨hi + 1, harr⟩).val := by
              simp only [shuffleAProj, dite_eq_left harr]
            rw [e1, f1]
          have g0 : shuffleAProj S hi = (S.projA q.castSucc).val := by
            have e0 : shuffleAProj S hi =
                (S.projA ⟨hi, hhi_lt⟩).val := by
              simp only [shuffleAProj, dite_eq_left hhi_lt]
            rw [e0, f0]
          rcases S.step q with ⟨hA, hB⟩ | ⟨hA, hB⟩
          · exfalso
            have g1B : shuffleBProj S (hi + 1) = (S.projB q.succ).val := by
              have e1 : shuffleBProj S (hi + 1) =
                  (S.projB ⟨hi + 1, harr⟩).val := by
                simp only [shuffleBProj, dite_eq_left harr]
              rw [e1, f1]
            have g0B : shuffleBProj S hi = (S.projB q.castSucc).val := by
              have e0 : shuffleBProj S hi =
                  (S.projB ⟨hi, hhi_lt⟩).val := by
                simp only [shuffleBProj, dite_eq_left hhi_lt]
              rw [e0, f0]
            have hBeq : shuffleBProj S (hi + 1) = shuffleBProj S hi := by
              omega
            omega
          · omega
        obtain ⟨karr, hkarr⟩ : ∃ karr : Fin (n + m + 1),
            karr.val = hi + 1 := ⟨⟨hi + 1, harr⟩, rfl⟩
        have hov := h (⟨hi + 1, harr⟩)
        obtain ⟨-, hovBA⟩ := hov
        have eB : (S.projB ⟨hi + 1, harr⟩).val = j.val + 1 := by
          have : shuffleBProj S (hi + 1) = (S.projB ⟨hi + 1, harr⟩).val := by
            simp only [shuffleBProj, dite_eq_left harr]
          omega
        have eA : (S.projA ⟨hi + 1, harr⟩).val = shuffleAProj S hi := by
          have : shuffleAProj S (hi + 1) =
              (S.projA ⟨hi + 1, harr⟩).val := by
            simp only [shuffleAProj, dite_eq_left harr]
          omega
        rw [eA, eB] at hovBA
        rw [shuffleCumBefore_succ_eq_through] at hovBA
        exact hovBA
      · have hN : hi = n + m := by omega
        have hsum := shuffleABProj_sum S hi hhi_lt
        have hnm : n + m < n + m + 1 := by omega
        have hlast : (⟨n + m, hnm⟩ : Fin (n + m + 1)) = Fin.last (n + m) :=
          Fin.ext (by rfl)
        have hai : shuffleAProj S hi = n := by
          have e : shuffleAProj S hi = shuffleAProj S (n + m) := by rw [hN]
          have e2 : shuffleAProj S (n + m) = (S.projA ⟨n + m, hnm⟩).val := by
            simp only [shuffleAProj, dite_eq_left hnm]
          rw [e, e2, hlast, shufA_last]
        have hbj : j.val = m := by omega
        rw [hbj, hai, shuffleCumThrough_last, shuffleCumThrough_last]
    have hAeq : (S.projA ⟨hi, hhi_lt⟩).val = shuffleAProj S hi := by
      simp only [shuffleAProj, dite_eq_left hhi_lt]
    have hBeq : (S.projB ⟨hi, hhi_lt⟩).val = j.val := by
      have : shuffleBProj S hi = (S.projB ⟨hi, hhi_lt⟩).val := by
        simp only [shuffleBProj, dite_eq_left hhi_lt]
      omega
    rw [hAeq, hBeq, min_eq_right hBi]
  have hlo_pred : (if _ : 0 < lo then shuffleCutExt S x y (lo - 1) else 0) =
      shuffleCumBefore y j.val := by
    by_cases hlo0 : lo = 0
    · rw [hlo0]
      rw [dite_eq_right (lt_irrefl 0)]
      have hj0 : j.val = 0 := by
        have h0 : shuffleBProj S 0 = 0 := by
          have hz : (0 : ℕ) < n + m + 1 := by omega
          have e0 : shuffleBProj S 0 = (S.projB ⟨0, hz⟩).val := by
            simp only [shuffleBProj, dite_eq_left hz]
          have z0 : (⟨0, hz⟩ : Fin (n + m + 1)) = 0 := by
            apply Fin.ext
            simp
          rw [e0, z0, S.firstB]
          rfl
        rw [← lo_eq, hlo0, h0]
      rw [hj0, shuffleCumBefore_zero]
    · have hpos : 0 < lo := by omega
      rw [dite_eq_left hpos]
      have hlo1 : lo - 1 < n + m + 1 := by omega
      rw [shuffleCutExt_eq S x y _ hlo1]
      unfold shuffleCut
      have hb' : shuffleBProj S (lo - 1) = j.val - 1 := by
        have hlt1 : shuffleBProj S (lo - 1) < j.val := by
          by_contra hle
          have hge : j.val ≤ shuffleBProj S (lo - 1) := not_lt.mp hle
          have hle2 : shuffleBProj S (lo - 1) ≤ shuffleBProj S lo :=
            shuffleBProj_mono S (by omega)
          have heq2 : shuffleBProj S (lo - 1) = j.val := by omega
          have hmem' : lo - 1 < n + m + 1 ∧
              shuffleBProj S (lo - 1) = j.val := ⟨by omega, heq2⟩
          have := hlo_min (lo - 1) hmem'.1 hmem'.2
          omega
        have hge1 : j.val - 1 ≤ shuffleBProj S (lo - 1) := by
          have hstep : shuffleBProj S lo ≤ shuffleBProj S (lo - 1) + 1 := by
            have hN : lo - 1 < n + m := by omega
            obtain ⟨q, hq⟩ : ∃ q : Fin (n + m), q.val = lo - 1 :=
              ⟨⟨lo - 1, hN⟩, rfl⟩
            have harr : lo < n + m + 1 := lo_lt
            have hlo_eq : lo - 1 + 1 = lo := by omega
            have f1 : q.succ = (⟨lo, harr⟩ : Fin (n + m + 1)) := by
              apply Fin.ext
              rw [Fin.val_succ, hq, hlo_eq]
            have f0 : q.castSucc = (⟨lo - 1, hlo1⟩ : Fin (n + m + 1)) := by
              apply Fin.ext
              rw [Fin.val_castSucc, hq]
            have g1 : shuffleBProj S lo = (S.projB q.succ).val := by
              have e1 : shuffleBProj S lo =
                  (S.projB ⟨lo, harr⟩).val := by
                simp only [shuffleBProj, dite_eq_left harr]
              rw [e1, f1]
            have g0 : shuffleBProj S (lo - 1) =
                (S.projB q.castSucc).val := by
              have e0 : shuffleBProj S (lo - 1) =
                  (S.projB ⟨lo - 1, hlo1⟩).val := by
                simp only [shuffleBProj, dite_eq_left hlo1]
              rw [e0, f0]
            rcases S.step q with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;> omega
          omega
        omega
      have ha' : shuffleAProj S (lo - 1) = shuffleAProj S lo := by
        have hN : lo - 1 < n + m := by omega
        obtain ⟨q, hq⟩ : ∃ q : Fin (n + m), q.val = lo - 1 :=
          ⟨⟨lo - 1, hN⟩, rfl⟩
        have harr : lo < n + m + 1 := lo_lt
        have hlo_eq : lo - 1 + 1 = lo := by omega
        have f1 : q.succ = (⟨lo, harr⟩ : Fin (n + m + 1)) :=
          Fin.ext (by rw [Fin.val_succ, hq, hlo_eq])
        have f0 : q.castSucc = (⟨lo - 1, hlo1⟩ : Fin (n + m + 1)) :=
          Fin.ext (by rw [Fin.val_castSucc, hq])
        have g1 : shuffleAProj S lo = (S.projA q.succ).val := by
          have e1 : shuffleAProj S lo =
              (S.projA ⟨lo, harr⟩).val := by
            simp only [shuffleAProj, dite_eq_left harr]
          rw [e1, f1]
        have g0 : shuffleAProj S (lo - 1) = (S.projA q.castSucc).val := by
          have e0 : shuffleAProj S (lo - 1) =
              (S.projA ⟨lo - 1, hlo1⟩).val := by
            simp only [shuffleAProj, dite_eq_left hlo1]
          rw [e0, f0]
        have hB1 : shuffleBProj S lo = (S.projB q.succ).val := by
          have e1 : shuffleBProj S lo =
              (S.projB ⟨lo, harr⟩).val := by
            simp only [shuffleBProj, dite_eq_left harr]
          rw [e1, f1]
        have hB0 : shuffleBProj S (lo - 1) = (S.projB q.castSucc).val := by
          have e0 : shuffleBProj S (lo - 1) =
              (S.projB ⟨lo - 1, hlo1⟩).val := by
            simp only [shuffleBProj, dite_eq_left hlo1]
          rw [e0, f0]
        rcases S.step q with ⟨hA, hB⟩ | ⟨hA, hB⟩
        · exfalso
          have hBeq' : shuffleBProj S (lo - 1) = j.val := by omega
          have hle := hlo_min (lo - 1) hlo1 hBeq'
          omega
        · omega
      have hjv : 0 < j.val := by
        by_contra hle
        have hj0 : j.val = 0 := by omega
        have h0mem : (0 : ℕ) < n + m + 1 ∧ shuffleBProj S 0 = j.val := by
          refine ⟨by omega, ?_⟩
          have hz : (0 : ℕ) < n + m + 1 := by omega
          have e0 : shuffleBProj S 0 = (S.projB ⟨0, hz⟩).val := by
            simp only [shuffleBProj, dite_eq_left hz]
          have z0 : (⟨0, hz⟩ : Fin (n + m + 1)) = 0 := Fin.ext (by rfl)
          rw [e0, z0, S.firstB, hj0]
          rfl
        have := hlo_min 0 h0mem.1 h0mem.2
        omega
      have hmin_eq : min (shuffleCumThrough x (shuffleAProj S (lo - 1)))
          (shuffleCumThrough y (shuffleBProj S (lo - 1))) =
          shuffleCumThrough y (j.val - 1) := by
        have hov := h (⟨lo, lo_lt⟩)
        obtain ⟨-, hovBA⟩ := hov
        have eB : (S.projB ⟨lo, lo_lt⟩).val = j.val := by
          have : shuffleBProj S lo = (S.projB ⟨lo, lo_lt⟩).val := by
            simp only [shuffleBProj, dite_eq_left lo_lt]
          omega
        have eA : (S.projA ⟨lo, lo_lt⟩).val = shuffleAProj S lo := by
          simp only [shuffleAProj, dite_eq_left lo_lt]
        rw [eA, eB] at hovBA
        have hbs : shuffleCumBefore y j.val =
            shuffleCumThrough y (j.val - 1) := by
          have hsucc : j.val - 1 + 1 = j.val := by omega
          have hbs2 := shuffleCumBefore_succ_eq_through y (j.val - 1)
          rwa [hsucc] at hbs2
        rw [hbs] at hovBA
        rw [ha', hb']
        exact min_eq_right hovBA
      have hAeq2 : (S.projA ⟨lo - 1, hlo1⟩).val =
          shuffleAProj S (lo - 1) := by
        simp only [shuffleAProj, dite_eq_left hlo1]
      have hBeq2 : (S.projB ⟨lo - 1, hlo1⟩).val =
          shuffleBProj S (lo - 1) := by
        simp only [shuffleBProj, dite_eq_left hlo1]
      rw [hAeq2, hBeq2, hmin_eq]
      have hbs : shuffleCumBefore y j.val =
          shuffleCumThrough y (j.val - 1) := by
        have hsucc : j.val - 1 + 1 = j.val := by omega
        have hbs2 := shuffleCumBefore_succ_eq_through y (j.val - 1)
        rwa [hsucc] at hbs2
      exact hbs.symm
  rw [hhi_cut, hlo_pred]
  have hsplit := shuffleCumThrough_eq_before_add y j
  linarith [hsplit]

end RecoveryB

section RangeIff

variable {n m : ℕ}

/-- First-coordinate recovery: the cell sends the reconstructed source back
to `x`. -/
private lemma shuffleCell_fst_source_eq (S : ProdSimplexShuffle n m)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (y : Convexity.StdSimplex ℝ (Fin (m + 1)))
    (h : shuffleCumOverlap S x y) :
    (shuffleCell S (shuffleCellSource S x y)).1 = x := by
  apply Convexity.StdSimplex.ext
  ext i
  have hfib := shuffleCell_fst_fiber S (shuffleCellSource S x y) i
  have hrec := shuffleFiberA_sum S x y h i
  have hcongr : (∑ k ∈ Finset.univ.filter (fun k : Fin (n + m + 1) => S.projA k = i),
      (shuffleCellSource S x y).weights k) =
      (∑ k ∈ Finset.univ.filter (fun k : Fin (n + m + 1) => S.projA k = i),
        shuffleCellSourceFun S x y k) :=
    Finset.sum_congr rfl (fun k _ => rfl)
  rw [hfib, hcongr]
  exact hrec

/-- Second-coordinate recovery: the cell sends the reconstructed source back
to `y`. -/
private lemma shuffleCell_snd_source_eq (S : ProdSimplexShuffle n m)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (y : Convexity.StdSimplex ℝ (Fin (m + 1)))
    (h : shuffleCumOverlap S x y) :
    (shuffleCell S (shuffleCellSource S x y)).2 = y := by
  apply Convexity.StdSimplex.ext
  ext j
  have hfib := shuffleCell_snd_fiber S (shuffleCellSource S x y) j
  have hrec := shuffleFiberB_sum S x y h j
  have hcongr : (∑ k ∈ Finset.univ.filter (fun k : Fin (n + m + 1) => S.projB k = j),
      (shuffleCellSource S x y).weights k) =
      (∑ k ∈ Finset.univ.filter (fun k : Fin (n + m + 1) => S.projB k = j),
        shuffleCellSourceFun S x y k) :=
    Finset.sum_congr rfl (fun k _ => rfl)
  rw [hfib, hcongr]
  exact hrec

/-- Exact range characterization for one shuffle cell: `(x, y)` lies in
`Set.range (shuffleCell S)` exactly when the cumulative overlap inequalities
hold at every chain vertex. The forward direction is the one-cell package;
the reverse direction uses the explicit reconstructed source. -/
theorem shuffleCell_mem_range_iff (S : ProdSimplexShuffle n m)
    {x : Convexity.StdSimplex ℝ (Fin (n + 1))} {y : Convexity.StdSimplex ℝ (Fin (m + 1))} :
    (x, y) ∈ Set.range (shuffleCell S) ↔ shuffleCumOverlap S x y := by
  constructor
  · intro h k
    exact ⟨shuffleCell_mem_range_imp_cumAB S h k,
      shuffleCell_mem_range_imp_cumBA S h k⟩
  · intro h
    have hfst := shuffleCell_fst_source_eq S x y h
    have hsnd := shuffleCell_snd_source_eq S x y h
    exact ⟨shuffleCellSource S x y, Prod.ext hfst hsnd⟩

end RangeIff

section Coverage

variable {n m : ℕ}

/-- Greedy lattice-path step: at `(a, b)` take a first-factor step unless the
second weak cut is strictly below the first, or the first factor is exhausted;
symmetrically for the second factor. -/
private noncomputable def shuffleCovNext (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (y : Convexity.StdSimplex ℝ (Fin (m + 1))) (a b : ℕ) : ℕ × ℕ := by
  classical
  exact if a = n then (n, b + 1)
    else if b = m then (a + 1, m)
    else if _ : shuffleCumThrough y b < shuffleCumThrough x a then
      (a, b + 1)
    else (a + 1, b)

/-- Greedy lattice-path construction by recursion. -/
private noncomputable def shuffleCovPair (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (y : Convexity.StdSimplex ℝ (Fin (m + 1))) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | v + 1 =>
    if (shuffleCovPair x y v).1 = n ∧ (shuffleCovPair x y v).2 = m then
      shuffleCovPair x y v
    else shuffleCovNext x y (shuffleCovPair x y v).1
      (shuffleCovPair x y v).2

/-- One greedy step preserves the lattice invariant and overlap. -/
private lemma shuffleCovNext_spec (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (y : Convexity.StdSimplex ℝ (Fin (m + 1))) (a b : ℕ)
    (ha : a ≤ n) (hb : b ≤ m) (hsum : a + b < n + m)
    (hov : shuffleCumBefore x a ≤ shuffleCumThrough y b ∧
      shuffleCumBefore y b ≤ shuffleCumThrough x a) :
    let p := shuffleCovNext x y a b
    (p.1 = a + 1 ∧ p.2 = b ∨ p.1 = a ∧ p.2 = b + 1) ∧
      p.1 + p.2 = a + b + 1 ∧ p.1 ≤ n ∧ p.2 ≤ m ∧
      (shuffleCumBefore x p.1 ≤ shuffleCumThrough y p.2 ∧
        shuffleCumBefore y p.2 ≤ shuffleCumThrough x p.1) := by
  simp only [shuffleCovNext]
  by_cases h1 : a = n
  · have hb_lt : b < m := by omega
    have h1' : a = n := h1
    rw [ite_eq_left h1']
    refine ⟨Or.inr ⟨h1.symm, rfl⟩, by omega, le_refl n, by omega, ?_, ?_⟩
    · calc shuffleCumBefore x n ≤ shuffleCumThrough y b :=
            h1 ▸ hov.1
        _ ≤ shuffleCumThrough y (b + 1) :=
            shuffleCumThrough_mono y (by omega)
    · calc shuffleCumBefore y (b + 1) = shuffleCumThrough y b :=
            shuffleCumBefore_succ_eq_through y b
        _ ≤ 1 := shuffleCumThrough_le_one y b
        _ = shuffleCumThrough x n := (shuffleCumThrough_last x).symm
  · by_cases h2 : b = m
    · have ha_lt : a < n := by omega
      have h2' : b = m := h2
      rw [ite_eq_right (by simpa using h1), ite_eq_left h2']
      refine ⟨Or.inl ⟨rfl, h2.symm⟩, by omega, by omega, le_refl m, ?_, ?_⟩
      · calc shuffleCumBefore x (a + 1) = shuffleCumThrough x a :=
              shuffleCumBefore_succ_eq_through x a
          _ ≤ 1 := shuffleCumThrough_le_one x a
          _ = shuffleCumThrough y m :=
              (shuffleCumThrough_last y).symm
      · calc shuffleCumBefore y m ≤ shuffleCumThrough x a :=
              h2 ▸ hov.2
          _ ≤ shuffleCumThrough x (a + 1) :=
              shuffleCumThrough_mono x (by omega)
    · have h1' : ¬ a = n := h1
      have h2' : ¬ b = m := h2
      rw [ite_eq_right h1', ite_eq_right h2']
      by_cases hcmp : shuffleCumThrough y b < shuffleCumThrough x a
      · rw [dite_eq_left hcmp]
        refine ⟨Or.inr ⟨rfl, rfl⟩, by omega, by omega, by omega, ?_, ?_⟩
        · calc shuffleCumBefore x a ≤ shuffleCumThrough y b :=
                hov.1
            _ ≤ shuffleCumThrough y (b + 1) :=
                shuffleCumThrough_mono y (by omega)
        · calc shuffleCumBefore y (b + 1) = shuffleCumThrough y b :=
                shuffleCumBefore_succ_eq_through y b
            _ ≤ shuffleCumThrough x a := le_of_lt hcmp
      · rw [dite_eq_right hcmp]
        have hle : shuffleCumThrough x a ≤ shuffleCumThrough y b :=
          le_of_not_gt hcmp
        refine ⟨Or.inl ⟨rfl, rfl⟩, by omega, by omega, by omega, ?_, ?_⟩
        · calc shuffleCumBefore x (a + 1) = shuffleCumThrough x a :=
                shuffleCumBefore_succ_eq_through x a
            _ ≤ shuffleCumThrough y b := hle
        · calc shuffleCumBefore y b ≤ shuffleCumThrough x a :=
                hov.2
            _ ≤ shuffleCumThrough x (a + 1) :=
                shuffleCumThrough_mono x (by omega)

/-- The greedy path stays on the lattice with overlap up to `n + m`. -/
private lemma shuffleCovPair_invariant (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (y : Convexity.StdSimplex ℝ (Fin (m + 1))) (v : ℕ) (hv : v ≤ n + m) :
    (shuffleCovPair x y v).1 + (shuffleCovPair x y v).2 = v ∧
      (shuffleCovPair x y v).1 ≤ n ∧ (shuffleCovPair x y v).2 ≤ m ∧
      shuffleCumBefore x (shuffleCovPair x y v).1 ≤
        shuffleCumThrough y (shuffleCovPair x y v).2 ∧
      shuffleCumBefore y (shuffleCovPair x y v).2 ≤
        shuffleCumThrough x (shuffleCovPair x y v).1 := by
  induction v with
  | zero =>
    simp only [shuffleCovPair]
    refine ⟨trivial, Nat.zero_le n, Nat.zero_le m, ?_, ?_⟩
    · rw [shuffleCumBefore_zero]
      exact shuffleCumThrough_nonneg y _
    · rw [shuffleCumBefore_zero]
      exact shuffleCumThrough_nonneg x _
  | succ v IH =>
    have hv' : v ≤ n + m := by omega
    obtain ⟨hsum, hle1, hle2, hov1, hov2⟩ := IH hv'
    simp only [shuffleCovPair]
    set p := shuffleCovPair x y v with hp
    by_cases hterm : p.1 = n ∧ p.2 = m
    · exfalso
      omega
    · rw [ite_eq_right hterm]
      have hsum' : p.1 + p.2 < n + m := by omega
      have hspec := shuffleCovNext_spec x y p.1 p.2 hle1 hle2 hsum' ⟨hov1, hov2⟩
      simpa [hsum] using hspec.2

/-- Coverage: every `(x, y)` lies in some shuffle cell. The greedy path gives
a shuffle whose overlap inequalities hold by construction; the range
equivalence turns overlap into membership. -/
theorem exists_shuffleCell_mem_range (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (y : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    ∃ S : ProdSimplexShuffle n m, (x, y) ∈ Set.range (shuffleCell S) := by
  have Hinv := shuffleCovPair_invariant x y
  have hN : n + m ≤ n + m := le_refl _
  have hfin : ∀ v : ℕ, v ≤ n + m →
      (shuffleCovPair x y v).1 ≤ n ∧ (shuffleCovPair x y v).2 ≤ m :=
    fun v hv => ⟨(Hinv v hv).2.1, (Hinv v hv).2.2.1⟩
  have hstep : ∀ v : ℕ, v < n + m →
      (((shuffleCovPair x y (v + 1)).1 = (shuffleCovPair x y v).1 + 1 ∧
        (shuffleCovPair x y (v + 1)).2 = (shuffleCovPair x y v).2) ∨
      ((shuffleCovPair x y (v + 1)).1 = (shuffleCovPair x y v).1 ∧
        (shuffleCovPair x y (v + 1)).2 = (shuffleCovPair x y v).2 + 1)) := by
    intro v hv
    have hv1 : v + 1 ≤ n + m := by omega
    have hv0 : v ≤ n + m := by omega
    have Hv := Hinv v hv0
    simp only [shuffleCovPair]
    set p := shuffleCovPair x y v with hp
    have hterm : ¬ (p.1 = n ∧ p.2 = m) := by
      rintro ⟨h1, h2⟩
      omega
    rw [ite_eq_right hterm]
    have hspec := shuffleCovNext_spec x y p.1 p.2 Hv.2.1 Hv.2.2.1
      (by omega) ⟨Hv.2.2.2.1, Hv.2.2.2.2⟩
    simpa using hspec.1
  have hmonoA : ∀ u w : ℕ, u ≤ w → w ≤ n + m →
      (shuffleCovPair x y u).1 ≤ (shuffleCovPair x y w).1 := by
    intro u w huw
    induction w, huw using Nat.le_induction with
    | base =>
      intro _
      exact le_refl _
    | succ k hle IH =>
      intro hwb
      have hkN : k < n + m := by omega
      have hst := hstep k hkN
      have hle' : k ≤ n + m := by omega
      have hIH := IH hle'
      omega
  have hmonoB : ∀ u w : ℕ, u ≤ w → w ≤ n + m →
      (shuffleCovPair x y u).2 ≤ (shuffleCovPair x y w).2 := by
    intro u w huw
    induction w, huw using Nat.le_induction with
    | base =>
      intro _
      exact le_refl _
    | succ k hle IH =>
      intro hwb
      have hkN : k < n + m := by omega
      have hst := hstep k hkN
      have hle' : k ≤ n + m := by omega
      have hIH := IH hle'
      omega
  have hlast1 : (shuffleCovPair x y (n + m)).1 = n := by
    have H := Hinv (n + m) le_rfl
    omega
  have hlast2 : (shuffleCovPair x y (n + m)).2 = m := by
    have H := Hinv (n + m) le_rfl
    omega
  have hS : ∃ S : ProdSimplexShuffle n m, ∀ k : Fin (n + m + 1),
      (S.projA k).val = (shuffleCovPair x y k.val).1 ∧
        (S.projB k).val = (shuffleCovPair x y k.val).2 := by
    refine ⟨{
      projA := fun k => ⟨(shuffleCovPair x y k.val).1, by
        have h := (hfin k.val (by have hlt := k.isLt; omega)).1
        omega⟩,
      projB := fun k => ⟨(shuffleCovPair x y k.val).2, by
        have h := (hfin k.val (by have hlt := k.isLt; omega)).2
        omega⟩,
      monoA := by
        intro a b hab
        apply Fin.le_def.mpr
        change (shuffleCovPair x y a.val).1 ≤ (shuffleCovPair x y b.val).1
        exact hmonoA a.val b.val (Fin.le_def.mp hab)
          (by have hlt := b.isLt; omega),
      monoB := by
        intro a b hab
        apply Fin.le_def.mpr
        change (shuffleCovPair x y a.val).2 ≤ (shuffleCovPair x y b.val).2
        exact hmonoB a.val b.val (Fin.le_def.mp hab)
          (by have hlt := b.isLt; omega),
      firstA := by
        apply Fin.ext
        change (shuffleCovPair x y 0).1 = 0
        rfl,
      lastA := by
        apply Fin.ext
        change (shuffleCovPair x y (n + m)).1 = n
        exact hlast1,
      firstB := by
        apply Fin.ext
        change (shuffleCovPair x y 0).2 = 0
        rfl,
      lastB := by
        apply Fin.ext
        change (shuffleCovPair x y (n + m)).2 = m
        exact hlast2,
      step := by
        intro q
        have hqv : q.val < n + m := q.isLt
        have hst := hstep q.val hqv
        have e1 : (q.succ).val = q.val + 1 := by rw [Fin.val_succ]
        have e0 : q.castSucc.val = q.val := by rw [Fin.val_castSucc]
        change ((shuffleCovPair x y (q.succ).val).1 =
              (shuffleCovPair x y q.castSucc.val).1 + 1 ∧
            (shuffleCovPair x y (q.succ).val).2 =
              (shuffleCovPair x y q.castSucc.val).2) ∨
          ((shuffleCovPair x y (q.succ).val).1 =
              (shuffleCovPair x y q.castSucc.val).1 ∧
            (shuffleCovPair x y (q.succ).val).2 =
              (shuffleCovPair x y q.castSucc.val).2 + 1)
        rw [e1, e0]
        exact hst }, fun k => ⟨rfl, rfl⟩⟩
  obtain ⟨S, hSval⟩ := hS
  have hoverlap : shuffleCumOverlap S x y := by
    intro k
    have H := Hinv k.val (by have hlt := k.isLt; omega)
    obtain ⟨_, _, _, hov1, hov2⟩ := H
    obtain ⟨hA, hB⟩ := hSval k
    rw [hA, hB]
    exact ⟨hov1, hov2⟩
  exact ⟨S, (shuffleCell_mem_range_iff S).mpr hoverlap⟩

/-- Set-level coverage: the shuffle-cell ranges cover the whole product.
Follows elementwise from `exists_shuffleCell_mem_range`. -/
theorem iUnion_shuffleCell_range_eq_univ :
    ⋃ S : ProdSimplexShuffle n m, Set.range (shuffleCell S) = Set.univ := by
  ext y
  constructor
  · intro _
    exact Set.mem_univ y
  · intro _
    rcases y with ⟨x, y⟩
    obtain ⟨S, hS⟩ := exists_shuffleCell_mem_range x y
    exact Set.mem_iUnion.mpr ⟨S, hS⟩

end Coverage

section ShuffleGluing

variable {n m : ℕ}

/-- Index embedding of a shuffle into its projection pair. -/
private def shuffleToPair (S : ProdSimplexShuffle n m) :
    (Fin (n + m + 1) → Fin (n + 1)) × (Fin (n + m + 1) → Fin (m + 1)) :=
  (S.projA, S.projB)

/-- The index embedding is injective: a shuffle is determined by its two
projections, the remaining fields being propositions. -/
private theorem shuffleToPair_injective (n m : ℕ) :
    Function.Injective (shuffleToPair (n := n) (m := m)) := by
  intro S T h
  have hA : S.projA = T.projA := congrArg Prod.fst h
  have hB : S.projB = T.projB := congrArg Prod.snd h
  obtain ⟨a1, b1, _, _, _, _, _, _, _⟩ := S
  obtain ⟨a2, b2, _, _, _, _, _, _, _⟩ := T
  dsimp only at hA hB
  subst hA
  subst hB
  rfl

/-- The shuffle index type is finite. -/
instance : Finite (ProdSimplexShuffle n m) :=
  Finite.of_injective (shuffleToPair (n := n) (m := m))
    (shuffleToPair_injective n m)

/-- Discrete index topology for the sigma cover. -/
instance : TopologicalSpace (ProdSimplexShuffle n m) := ⊥

/-- The index topology is discrete. -/
instance : DiscreteTopology (ProdSimplexShuffle n m) := ⟨rfl⟩

/-- The finite coproduct cover map from `Σ S, Δ^{n+m}` onto `Δ^n × Δ^m`.

For each shuffle `S`, the fiber over `S` is sent by the affine shuffle cell
`shuffleCell S`. The domain uses the sigma topology where the finite shuffle
index is discrete. This is the reusable finite closed-cover gluing map for the
product decomposition; downstream colimit/homeomorphism arguments will use its
quotient property. -/
noncomputable def shuffleGluingCoverMap (n m : ℕ) :
    (Σ _ : ProdSimplexShuffle n m, Convexity.StdSimplex ℝ (Fin (n + m + 1))) →
      Convexity.StdSimplex ℝ (Fin (n + 1)) × Convexity.StdSimplex ℝ (Fin (m + 1)) :=
  fun ⟨S, s⟩ => shuffleCell S s

/-- Application formula for `shuffleGluingCoverMap`. -/
@[simp]
theorem shuffleGluingCoverMap_apply (n m : ℕ) (S : ProdSimplexShuffle n m)
    (s : Convexity.StdSimplex ℝ (Fin (n + m + 1))) :
    shuffleGluingCoverMap n m ⟨S, s⟩ = shuffleCell S s :=
  rfl

/-- Continuity of the cover map via the sigma topology. -/
theorem continuous_shuffleGluingCoverMap (n m : ℕ) :
    Continuous (shuffleGluingCoverMap n m) := by
  rw [continuous_sigma_iff]
  intro S
  have h_eq : (fun a => shuffleGluingCoverMap n m ⟨S, a⟩) = shuffleCell S := by
    funext s
    rfl
  rw [h_eq]
  exact continuous_shuffleCell S

/-- The precise finite-union image identity used for the closed-map argument. -/
theorem shuffleGluingCoverMap_image_eq_iUnion (n m : ℕ)
    (C : Set (Σ _ : ProdSimplexShuffle n m, Convexity.StdSimplex ℝ (Fin (n + m + 1)))) :
    shuffleGluingCoverMap n m '' C =
      ⋃ S : ProdSimplexShuffle n m,
        shuffleCell S ''
          (Sigma.mk (β := fun _ : ProdSimplexShuffle n m =>
            Convexity.StdSimplex ℝ (Fin (n + m + 1))) S ⁻¹' C) := by
  ext y
  constructor
  · rintro ⟨⟨S, s⟩, hmem, rfl⟩
    have hmem_slice :
        s ∈ Sigma.mk (β := fun _ : ProdSimplexShuffle n m =>
          Convexity.StdSimplex ℝ (Fin (n + m + 1))) S ⁻¹' C := hmem
    exact Set.mem_iUnion.mpr ⟨S, ⟨s, hmem_slice, rfl⟩⟩
  · rintro hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨S, ⟨s, hs_slice, rfl⟩⟩ := hy
    have hmem : (⟨S, s⟩ : Σ _ : ProdSimplexShuffle n m,
      Convexity.StdSimplex ℝ (Fin (n + m + 1))) ∈ C := hs_slice
    exact ⟨⟨S, s⟩, hmem, rfl⟩

/-- Surjectivity of the cover map via `exists_shuffleCell_mem_range`. -/
theorem surjective_shuffleGluingCoverMap (n m : ℕ) :
    Function.Surjective (shuffleGluingCoverMap n m) := by
  rintro ⟨x, y⟩
  obtain ⟨S, hS⟩ := exists_shuffleCell_mem_range x y
  obtain ⟨s, hs⟩ := hS
  exact ⟨⟨S, s⟩, hs⟩

/-- Finite closed-cover argument: `shuffleGluingCoverMap` is a closed map. -/
theorem isClosedMap_shuffleGluingCoverMap (n m : ℕ) :
    IsClosedMap (shuffleGluingCoverMap n m) := by
  intro C hC
  have h_slices : ∀ S : ProdSimplexShuffle n m,
      IsClosed (Sigma.mk (β := fun _ : ProdSimplexShuffle n m =>
        Convexity.StdSimplex ℝ (Fin (n + m + 1))) S ⁻¹' C) :=
    (isClosed_sigma_iff.mp hC)
  have h_each : ∀ S : ProdSimplexShuffle n m,
      IsClosed
        (shuffleCell S ''
          (Sigma.mk (β := fun _ : ProdSimplexShuffle n m =>
            Convexity.StdSimplex ℝ (Fin (n + m + 1))) S ⁻¹' C)) := by
    intro S
    exact (isClosedEmbedding_shuffleCell S).isClosedMap _ (h_slices S)
  have h_eq : shuffleGluingCoverMap n m '' C =
      ⋃ S : ProdSimplexShuffle n m,
        shuffleCell S ''
          (Sigma.mk (β := fun _ : ProdSimplexShuffle n m =>
            Convexity.StdSimplex ℝ (Fin (n + m + 1))) S ⁻¹' C) :=
    shuffleGluingCoverMap_image_eq_iUnion n m C
  rw [h_eq]
  exact isClosed_iUnion_of_finite h_each

/-- Consequently, the finite cell cover is a quotient map. -/
theorem isQuotientMap_shuffleGluingCoverMap (n m : ℕ) :
    Topology.IsQuotientMap (shuffleGluingCoverMap n m) :=
  IsClosedMap.isQuotientMap (isClosedMap_shuffleGluingCoverMap n m)
    (continuous_shuffleGluingCoverMap n m) (surjective_shuffleGluingCoverMap n m)

/-- Each shuffle-cell range is closed, via the one-cell closed embedding. -/
theorem isClosed_shuffleCellRange (S : ProdSimplexShuffle n m) :
    IsClosed (Set.range (shuffleCell S)) := by
  have h := (isClosedEmbedding_shuffleCell S).isClosedMap _ isClosed_univ
  rwa [Set.image_univ] at h

/-- Pairwise intersections of shuffle-cell ranges are closed. -/
theorem isClosed_shuffleCellRange_inter (S T : ProdSimplexShuffle n m) :
    IsClosed (Set.range (shuffleCell S) ∩ Set.range (shuffleCell T)) :=
  (isClosed_shuffleCellRange S).inter (isClosed_shuffleCellRange T)

/-- Intersection compatibility: a point in two shuffle-cell ranges satisfies
both cells' cumulative overlap descriptions. Shared faces correspond to
equality cases of these inequalities; the full adjacent-transposition face
factorization with explicit face maps is explicitly not claimed here. -/
theorem shuffleCell_inter_imp_commonCut {S T : ProdSimplexShuffle n m}
    {x : Convexity.StdSimplex ℝ (Fin (n + 1))} {y : Convexity.StdSimplex ℝ (Fin (m + 1))}
    (hS : (x, y) ∈ Set.range (shuffleCell S))
    (hT : (x, y) ∈ Set.range (shuffleCell T)) :
    shuffleCumOverlap S x y ∧ shuffleCumOverlap T x y :=
  ⟨(shuffleCell_mem_range_iff S).mp hS, (shuffleCell_mem_range_iff T).mp hT⟩

end ShuffleGluing
