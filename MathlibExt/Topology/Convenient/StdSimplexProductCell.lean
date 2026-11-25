/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Analysis.Convex.StdSimplex
public import MathlibExt.Analysis.Convex.StdSimplex

@[expose] public section

open Set Finset Topology

/-!
# One affine shuffle cell in `Δ^n × Δ^m`

For `n m : ℕ`, a `ProdSimplexShuffle n m` is one maximal lattice chain from
`(0, 0)` to `(n, m)` with unit steps, presented as two monotone projections
`projA : Fin (n + m + 1) → Fin (n + 1)` and
`projB : Fin (n + m + 1) → Fin (m + 1)` running from `0` to the last vertex,
such that at every step exactly one projection advances by one. This is the
finite shuffle/indexing object for a single nondegenerate `(n + m)`-simplex
of the standard triangulation of `Δ^n × Δ^m`: the chain vertices are the
images of the domain vertices, consecutive vertices differ in exactly one
factor, and every level of each factor is visited.

The affine cell map `shuffleCell S : Δ^{n+m} → Δ^n × Δ^m` applies
`Convexity.StdSimplex.map` to each projection. This module proves the reusable
one-cell package: projection simp lemmas, continuity, fiber-sum coordinate
formulas for both factors, injectivity (prefix recovery: at each step the
advancing factor determines the next source coordinate, and the last
coordinate follows from the total sum), hence a closed embedding, plus
cumulative-sum bounds and the forward range implications comparing strict
cumulative mass in one factor against weak cumulative mass in the other.

This generalizes the interval construction in `StdSimplexPrism`
(`Δ^p × Δ^1`, binary cut at one index) to an arbitrary shuffle in
`Δ^n × Δ^m`. The interval API is preserved untouched; nothing here
duplicates it.

Later finite gluing will index one such cell per shuffle, use the closed
embeddings to topologize each cell, and use the cumulative inequalities to
identify shared faces: a point lies on the face shared with a neighboring
shuffle exactly when one of the cumulative comparisons is an equality.
That gluing needs, beyond this file, the reverse range implication
(explicit shuffle source reconstruction from cumulative data), the range
equivalence, coverage of `Δ^n × Δ^m` by all `(n + m)! / (n! * m!)` shuffle
cells, and the face-intersection description.

It does not prove the reverse range implication, a range equivalence,
reconstruction, coverage, intersections, finite gluing, `SSet`,
`DeltaGenerated`, or model-category claims.
-/

section Shuffle

/-- One shuffle cell index for `Δ^n × Δ^m`: a maximal unit-step chain from
`(0, 0)` to `(n, m)` via two monotone projections with exclusive steps. -/
structure ProdSimplexShuffle (n m : ℕ) where
  /-- First projection of the chain. -/
  projA : Fin (n + m + 1) → Fin (n + 1)
  /-- Second projection of the chain. -/
  projB : Fin (n + m + 1) → Fin (m + 1)
  /-- First projection is monotone. -/
  monoA : Monotone projA
  /-- Second projection is monotone. -/
  monoB : Monotone projB
  /-- First projection starts at `0`. -/
  firstA : projA 0 = 0
  /-- First projection ends at the last vertex. -/
  lastA : projA (Fin.last (n + m)) = Fin.last n
  /-- Second projection starts at `0`. -/
  firstB : projB 0 = 0
  /-- Second projection ends at the last vertex. -/
  lastB : projB (Fin.last (n + m)) = Fin.last m
  /-- At every step exactly one projection advances by one. -/
  step : ∀ k : Fin (n + m),
    ((projA k.succ).val = (projA k.castSucc).val + 1 ∧
      (projB k.succ).val = (projB k.castSucc).val) ∨
    ((projA k.succ).val = (projA k.castSucc).val ∧
      (projB k.succ).val = (projB k.castSucc).val + 1)

variable {n m : ℕ}

/-- First projection starts at value `0`. -/
@[simp]
theorem shufA_zero (S : ProdSimplexShuffle n m) : (S.projA 0).val = 0 := by
  rw [S.firstA]
  rfl

/-- First projection ends at value `n`. -/
@[simp]
theorem shufA_last (S : ProdSimplexShuffle n m) :
    (S.projA (Fin.last (n + m))).val = n := by
  rw [S.lastA]
  rfl

/-- Second projection starts at value `0`. -/
@[simp]
theorem shufB_zero (S : ProdSimplexShuffle n m) : (S.projB 0).val = 0 := by
  rw [S.firstB]
  rfl

/-- Second projection ends at value `m`. -/
@[simp]
theorem shufB_last (S : ProdSimplexShuffle n m) :
    (S.projB (Fin.last (n + m))).val = m := by
  rw [S.lastB]
  rfl

/-- A strict inequality of monotone image values descends to a strict
inequality of source values. -/
private lemma val_lt_of_map_val_lt {d N : ℕ} {f : Fin (N + 1) → Fin (d + 1)}
    (hf : Monotone f) {a b : Fin (N + 1)} (h : (f a).val < (f b).val) :
    a.val < b.val := by
  by_contra hle
  have hba : b ≤ a := Fin.le_def.mpr (le_of_not_gt hle)
  have hle' := Fin.le_def.mp (hf hba)
  omega

/-- Members of a first-projection fiber over the departure level of an
advancing first-factor step lie at or before that step. -/
private lemma fiberA_val_le_of_stepA (S : ProdSimplexShuffle n m)
    (q : Fin (n + m)) (j : Fin (n + m + 1)) (hq : q.castSucc = j)
    (hA : (S.projA q.succ).val = (S.projA q.castSucc).val + 1)
    (k' : Fin (n + m + 1)) (hk' : S.projA k' = S.projA j) :
    k'.val ≤ q.val := by
  have h1 : (S.projA k').val = (S.projA j).val := congrArg Fin.val hk'
  have h2 : (S.projA j).val = (S.projA q.castSucc).val :=
    (congrArg (fun a => (S.projA a).val) hq).symm
  have hlt : (S.projA k').val < (S.projA q.succ).val := by omega
  have hlt' : k'.val < (q.succ).val := val_lt_of_map_val_lt S.monoA hlt
  have hqs : (q.succ).val = q.val + 1 := by rw [Fin.val_succ]
  omega

/-- Members of a second-projection fiber over the departure level of an
advancing second-factor step lie at or before that step. -/
private lemma fiberB_val_le_of_stepB (S : ProdSimplexShuffle n m)
    (q : Fin (n + m)) (j : Fin (n + m + 1)) (hq : q.castSucc = j)
    (hB : (S.projB q.succ).val = (S.projB q.castSucc).val + 1)
    (k' : Fin (n + m + 1)) (hk' : S.projB k' = S.projB j) :
    k'.val ≤ q.val := by
  have h1 : (S.projB k').val = (S.projB j).val := congrArg Fin.val hk'
  have h2 : (S.projB j).val = (S.projB q.castSucc).val :=
    (congrArg (fun a => (S.projB a).val) hq).symm
  have hlt : (S.projB k').val < (S.projB q.succ).val := by omega
  have hlt' : k'.val < (q.succ).val := val_lt_of_map_val_lt S.monoB hlt
  have hqs : (q.succ).val = q.val + 1 := by rw [Fin.val_succ]
  omega

/-- A strict first-projection level comparison forces a weak
second-projection comparison. -/
private lemma fiberA_mem_imp_B_le (S : ProdSimplexShuffle n m)
    (k j : Fin (n + m + 1))
    (h : (S.projA j).val < (S.projA k).val) :
    (S.projB j).val ≤ (S.projB k).val := by
  have hjk : j.val ≤ k.val := by
    by_contra hle
    have hlt : k < j := Fin.lt_def.mpr (lt_of_not_ge hle)
    have hle' := Fin.le_def.mp (S.monoA (le_of_lt hlt))
    omega
  exact Fin.le_def.mp (S.monoB (Fin.le_def.mpr hjk))

/-- A strict second-projection level comparison forces a weak
first-projection comparison. -/
private lemma fiberB_mem_imp_A_le (S : ProdSimplexShuffle n m)
    (k j : Fin (n + m + 1))
    (h : (S.projB j).val < (S.projB k).val) :
    (S.projA j).val ≤ (S.projA k).val := by
  have hjk : j.val ≤ k.val := by
    by_contra hle
    have hlt : k < j := Fin.lt_def.mpr (lt_of_not_ge hle)
    have hle' := Fin.le_def.mp (S.monoB (le_of_lt hlt))
    omega
  exact Fin.le_def.mp (S.monoA (Fin.le_def.mpr hjk))

/-- The chain coordinates sum to the vertex index: every step advances exactly
one factor by one, starting from `(0, 0)`. -/
theorem shuffleLevelSum_public (S : ProdSimplexShuffle n m)
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

end Shuffle

section CellDef

variable {n m : ℕ}

/-- The affine shuffle cell `Δ^{n+m} → Δ^n × Δ^m` for one shuffle. -/
noncomputable def shuffleCell (S : ProdSimplexShuffle n m) :
    Convexity.StdSimplex ℝ (Fin (n + m + 1)) →
      Convexity.StdSimplex ℝ (Fin (n + 1)) ×
        Convexity.StdSimplex ℝ (Fin (m + 1)) :=
  fun s => (Convexity.StdSimplex.map S.projA s,
    Convexity.StdSimplex.map S.projB s)

/-- First projection of `shuffleCell S` is new-carrier `map S.projA`. -/
@[simp]
theorem shuffleCell_fst (S : ProdSimplexShuffle n m)
    (s : Convexity.StdSimplex ℝ (Fin (n + m + 1))) :
    (shuffleCell S s).1 = Convexity.StdSimplex.map S.projA s :=
  rfl

/-- Second projection of `shuffleCell S` is new-carrier `map S.projB`. -/
@[simp]
theorem shuffleCell_snd (S : ProdSimplexShuffle n m)
    (s : Convexity.StdSimplex ℝ (Fin (n + m + 1))) :
    (shuffleCell S s).2 = Convexity.StdSimplex.map S.projB s :=
  rfl

/-- `shuffleCell S` is continuous as a product of continuous simplex maps. -/
theorem continuous_shuffleCell (S : ProdSimplexShuffle n m) :
    Continuous (shuffleCell S) :=
  (Convexity.StdSimplex.continuous_map ℝ _).prodMk
    (Convexity.StdSimplex.continuous_map ℝ _)

/-- First-component coordinate as a fiber sum over `projA`. -/
theorem shuffleCell_fst_fiber (S : ProdSimplexShuffle n m)
    (s : Convexity.StdSimplex ℝ (Fin (n + m + 1))) (i : Fin (n + 1)) :
    (shuffleCell S s).1.weights i =
      ∑ k ∈ Finset.univ.filter (fun k : Fin (n + m + 1) => S.projA k = i),
        s.weights k := by
  change (Convexity.StdSimplex.map S.projA s).weights i = _
  exact Convexity.StdSimplex.weights_map_apply s S.projA i

/-- Second-component coordinate as a fiber sum over `projB`. -/
theorem shuffleCell_snd_fiber (S : ProdSimplexShuffle n m)
    (s : Convexity.StdSimplex ℝ (Fin (n + m + 1))) (j : Fin (m + 1)) :
    (shuffleCell S s).2.weights j =
      ∑ k ∈ Finset.univ.filter (fun k : Fin (n + m + 1) => S.projB k = j),
        s.weights k := by
  change (Convexity.StdSimplex.map S.projB s).weights j = _
  exact Convexity.StdSimplex.weights_map_apply s S.projB j

/-- The affine shuffle cell is injective: source coordinates are recovered
by strong induction on the vertex index. At each step index the advancing
factor's fiber ends at the current vertex, so its coordinate equation
determines the next source value from strictly earlier ones; the last
coordinate follows from the total sum. -/
theorem shuffleCell_injective (S : ProdSimplexShuffle n m) :
    Function.Injective (shuffleCell S) := by
  intro s t h
  have hfst : (shuffleCell S s).1 = (shuffleCell S t).1 := congrArg Prod.fst h
  have hsnd : (shuffleCell S s).2 = (shuffleCell S t).2 := congrArg Prod.snd h
  have hX : ∀ i : Fin (n + 1),
      (shuffleCell S s).1.weights i =
      (shuffleCell S t).1.weights i := fun i => by rw [hfst]
  have hY : ∀ j : Fin (m + 1),
      (shuffleCell S s).2.weights j =
      (shuffleCell S t).2.weights j := fun j => by rw [hsnd]
  have hsumA : ∀ i : Fin (n + 1),
      ∑ k ∈ Finset.univ.filter (fun k : Fin (n + m + 1) => S.projA k = i),
        s.weights k =
      ∑ k ∈ Finset.univ.filter (fun k : Fin (n + m + 1) => S.projA k = i),
        t.weights k := by
    intro i
    rw [← shuffleCell_fst_fiber S s i, ← shuffleCell_fst_fiber S t i, hX i]
  have hsumB : ∀ j : Fin (m + 1),
      ∑ k ∈ Finset.univ.filter (fun k : Fin (n + m + 1) => S.projB k = j),
        s.weights k =
      ∑ k ∈ Finset.univ.filter (fun k : Fin (n + m + 1) => S.projB k = j),
        t.weights k := by
    intro j
    rw [← shuffleCell_snd_fiber S s j, ← shuffleCell_snd_fiber S t j, hY j]
  suffices H : ∀ v : ℕ, ∀ j : Fin (n + m + 1),
      j.val < v →
        s.weights j = t.weights j by
    have hfun : s.weights = t.weights := by
      ext k
      exact H _ k (by have hk := k.isLt; omega)
    exact Convexity.StdSimplex.ext hfun
  intro v
  induction v with
  | zero =>
    intro j hj
    omega
  | succ v IH =>
    intro j hj
    by_cases hjv : j.val < v
    · exact IH j hjv
    · have hjveq : j.val = v := by omega
      by_cases hvm : v < n + m
      · obtain ⟨q, hq⟩ : ∃ q : Fin (n + m), q.val = v := ⟨⟨v, hvm⟩, rfl⟩
        have hqcast : q.castSucc = j := by
          apply Fin.ext
          simp [Fin.val_castSucc, hq, hjveq]
        rcases S.step q with ⟨hA, hB⟩ | ⟨hA, hB⟩
        · have hsum := hsumA (S.projA j)
          have hmem : ∀ k' ∈ Finset.univ.filter
              (fun k' : Fin (n + m + 1) => S.projA k' = S.projA j),
              k'.val ≤ v := by
            intro k' hk'
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk'
            have hle := fiberA_val_le_of_stepA S q j hqcast hA k' hk'
            omega
          have hjF : j ∈ Finset.univ.filter
              (fun k' : Fin (n + m + 1) => S.projA k' = S.projA j) := by simp
          have hrest : ∑ k' ∈ (Finset.univ.filter
              (fun k' : Fin (n + m + 1) => S.projA k' = S.projA j)).erase j,
              s.weights k' =
            ∑ k' ∈ (Finset.univ.filter
              (fun k' : Fin (n + m + 1) => S.projA k' = S.projA j)).erase j,
              t.weights k' := by
            apply Finset.sum_congr rfl
            intro k' hk'
            have hk'F := Finset.mem_of_mem_erase hk'
            have hk'ne := Finset.ne_of_mem_erase hk'
            have hle := hmem k' hk'F
            have hlt : k'.val < v := by
              by_contra hc
              have heq : k'.val = v := by omega
              exact hk'ne (Fin.ext (by omega))
            exact IH k' hlt
          have hinsert : insert j ((Finset.univ.filter
              (fun k' : Fin (n + m + 1) => S.projA k' = S.projA j)).erase j) =
              Finset.univ.filter
                (fun k' : Fin (n + m + 1) => S.projA k' = S.projA j) :=
            Finset.insert_erase hjF
          have hnotmem : j ∉ (Finset.univ.filter
              (fun k' : Fin (n + m + 1) => S.projA k' = S.projA j)).erase j :=
            Finset.notMem_erase j _
          have hSs : ∑ k' ∈ Finset.univ.filter
                (fun k' : Fin (n + m + 1) => S.projA k' = S.projA j),
                s.weights k' =
              s.weights j + ∑ k' ∈ (Finset.univ.filter
                (fun k' : Fin (n + m + 1) => S.projA k' = S.projA j)).erase j,
                s.weights k' := by
            conv_lhs => rw [← hinsert, Finset.sum_insert hnotmem]
          have hTs : ∑ k' ∈ Finset.univ.filter
                (fun k' : Fin (n + m + 1) => S.projA k' = S.projA j),
                t.weights k' =
              t.weights j + ∑ k' ∈ (Finset.univ.filter
                (fun k' : Fin (n + m + 1) => S.projA k' = S.projA j)).erase j,
                t.weights k' := by
            conv_lhs => rw [← hinsert, Finset.sum_insert hnotmem]
          rw [hrest, hsum] at hSs
          linarith
        · have hsum := hsumB (S.projB j)
          have hmem : ∀ k' ∈ Finset.univ.filter
              (fun k' : Fin (n + m + 1) => S.projB k' = S.projB j),
              k'.val ≤ v := by
            intro k' hk'
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk'
            have hle := fiberB_val_le_of_stepB S q j hqcast hB k' hk'
            omega
          have hjF : j ∈ Finset.univ.filter
              (fun k' : Fin (n + m + 1) => S.projB k' = S.projB j) := by simp
          have hrest : ∑ k' ∈ (Finset.univ.filter
              (fun k' : Fin (n + m + 1) => S.projB k' = S.projB j)).erase j,
              s.weights k' =
            ∑ k' ∈ (Finset.univ.filter
              (fun k' : Fin (n + m + 1) => S.projB k' = S.projB j)).erase j,
              t.weights k' := by
            apply Finset.sum_congr rfl
            intro k' hk'
            have hk'F := Finset.mem_of_mem_erase hk'
            have hk'ne := Finset.ne_of_mem_erase hk'
            have hle := hmem k' hk'F
            have hlt : k'.val < v := by
              by_contra hc
              have heq : k'.val = v := by omega
              exact hk'ne (Fin.ext (by omega))
            exact IH k' hlt
          have e1 := Finset.add_sum_erase _ (fun k' => s.weights k') hjF
          have e2 := Finset.add_sum_erase _ (fun k' => t.weights k') hjF
          rw [hrest, hsum] at e1
          linarith
      · have hvn : v = n + m := by
          have hjlt := j.isLt
          omega
        have htot : ∑ k ∈ Finset.univ, s.weights k =
            ∑ k ∈ Finset.univ, t.weights k := by
          rw [s.total_of_fintype, t.total_of_fintype]
        have hjU : j ∈ (Finset.univ : Finset (Fin (n + m + 1))) :=
          Finset.mem_univ j
        have hrest : ∑ k' ∈ Finset.univ.erase j,
            s.weights k' =
          ∑ k' ∈ Finset.univ.erase j,
            t.weights k' := by
          apply Finset.sum_congr rfl
          intro k' hk'
          have hk'ne := Finset.ne_of_mem_erase hk'
          have hlt : k'.val < v := by
            have hle : k'.val ≤ v := by
              have hk := k'.isLt
              omega
            by_contra hc
            have heq : k'.val = v := by omega
            exact hk'ne (Fin.ext (by omega))
          exact IH k' hlt
        have e1 := Finset.add_sum_erase _ (fun k' => s.weights k') hjU
        have e2 := Finset.add_sum_erase _ (fun k' => t.weights k') hjU
        rw [hrest, htot] at e1
        linarith

/-- The affine shuffle cell is a closed embedding (continuous injective from
compact to Hausdorff). -/
theorem isClosedEmbedding_shuffleCell (S : ProdSimplexShuffle n m) :
    IsClosedEmbedding (shuffleCell S) := by
  have hcont : Continuous (shuffleCell S) := continuous_shuffleCell S
  have hinj : Function.Injective (shuffleCell S) := shuffleCell_injective S
  have : CompactSpace (Convexity.StdSimplex ℝ (Fin (n + m + 1))) :=
    inferInstance
  have : T2Space (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).t2Space
  have : T2Space (Convexity.StdSimplex ℝ (Fin (m + 1))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).t2Space
  have hclosed : IsClosedMap (shuffleCell S) := hcont.isClosedMap
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap hcont hinj hclosed

end CellDef

section Cumulative

variable {d : ℕ}

/-- Strict cumulative sum: mass of `x` at levels with value `< u`. -/
def shuffleCumBefore (x : Convexity.StdSimplex ℝ (Fin (d + 1))) (u : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (d + 1) => i.val < u),
    x.weights i

/-- Weak cumulative sum: mass of `x` at levels with value `≤ u`. -/
def shuffleCumThrough (x : Convexity.StdSimplex ℝ (Fin (d + 1))) (u : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (d + 1) => i.val ≤ u),
    x.weights i

/-- The strict cumulative sum is nonnegative. -/
theorem shuffleCumBefore_nonneg
    (x : Convexity.StdSimplex ℝ (Fin (d + 1))) (u : ℕ) :
    0 ≤ shuffleCumBefore x u := by
  unfold shuffleCumBefore
  exact Finset.sum_nonneg fun j _ => x.weights_nonneg j

/-- The weak cumulative sum is nonnegative. -/
theorem shuffleCumThrough_nonneg
    (x : Convexity.StdSimplex ℝ (Fin (d + 1))) (u : ℕ) :
    0 ≤ shuffleCumThrough x u := by
  unfold shuffleCumThrough
  exact Finset.sum_nonneg fun j _ => x.weights_nonneg j

/-- The strict cumulative sum is at most `1` since the total simplex sum
is `1`. -/
theorem shuffleCumBefore_le_one
    (x : Convexity.StdSimplex ℝ (Fin (d + 1))) (u : ℕ) :
    shuffleCumBefore x u ≤ 1 := by
  have hsum : ∑ j : Fin (d + 1), x.weights j = 1 :=
    x.total_of_fintype
  have hnonneg : 0 ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin (d + 1) => ¬ j.val < u),
        x.weights j :=
    Finset.sum_nonneg fun j _ => x.weights_nonneg j
  have hle : shuffleCumBefore x u +
      ∑ j ∈ Finset.univ.filter (fun j : Fin (d + 1) => ¬ j.val < u),
        x.weights j = 1 := by
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j : Fin (d + 1) => j.val < u)
        (fun j => x.weights j)
    unfold shuffleCumBefore
    linarith
  linarith

/-- The weak cumulative sum is at most `1` since the total simplex sum
is `1`. -/
theorem shuffleCumThrough_le_one
    (x : Convexity.StdSimplex ℝ (Fin (d + 1))) (u : ℕ) :
    shuffleCumThrough x u ≤ 1 := by
  have hsum : ∑ j : Fin (d + 1), x.weights j = 1 :=
    x.total_of_fintype
  have hnonneg : 0 ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin (d + 1) => ¬ j.val ≤ u),
        x.weights j :=
    Finset.sum_nonneg fun j _ => x.weights_nonneg j
  have hle : shuffleCumThrough x u +
      ∑ j ∈ Finset.univ.filter (fun j : Fin (d + 1) => ¬ j.val ≤ u),
        x.weights j = 1 := by
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j : Fin (d + 1) => j.val ≤ u)
        (fun j => x.weights j)
    unfold shuffleCumThrough
    linarith
  linarith

/-- Strict cumulative mass is at most weak cumulative mass. -/
theorem shuffleCumBefore_le_through
    (x : Convexity.StdSimplex ℝ (Fin (d + 1))) (u : ℕ) :
    shuffleCumBefore x u ≤ shuffleCumThrough x u := by
  unfold shuffleCumBefore shuffleCumThrough
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    omega
  · intro j _ _
    exact x.weights_nonneg j

end Cumulative

section Preimage

variable {n m : ℕ}

/-- A strict cumulative sum of a cell image is the source mass over the
strict sublevel preimage of `projA`. -/
theorem shuffleCumBefore_eq_preimage (S : ProdSimplexShuffle n m)
    (s : Convexity.StdSimplex ℝ (Fin (n + m + 1))) (u : ℕ) :
    shuffleCumBefore ((shuffleCell S s).1) u =
      ∑ j ∈ Finset.univ.filter
        (fun j : Fin (n + m + 1) => (S.projA j).val < u),
        s.weights j := by
  unfold shuffleCumBefore
  calc ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i.val < u),
          ((shuffleCell S s).1.weights i)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i.val < u),
          ∑ j ∈ Finset.univ.filter
            (fun j : Fin (n + m + 1) => S.projA j = i),
            s.weights j := by
        apply Finset.sum_congr rfl
        intro i _
        exact shuffleCell_fst_fiber S s i
    _ = ∑ j ∈ Finset.univ.filter (fun j : Fin (n + m + 1) =>
            S.projA j ∈ Finset.univ.filter (fun i : Fin (n + 1) => i.val < u)),
          s.weights j :=
        Finset.sum_fiberwise_eq_sum_filter _ _ _ _
    _ = ∑ j ∈ Finset.univ.filter
          (fun j : Fin (n + m + 1) => (S.projA j).val < u),
          s.weights j := by
        have hset : Finset.univ.filter (fun j : Fin (n + m + 1) =>
            S.projA j ∈ Finset.univ.filter (fun i : Fin (n + 1) => i.val < u)) =
          Finset.univ.filter
            (fun j : Fin (n + m + 1) => (S.projA j).val < u) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hset]

/-- A weak cumulative sum of a cell image is the source mass over the weak
sublevel preimage of `projA`. -/
theorem shuffleCumThrough_eq_preimage (S : ProdSimplexShuffle n m)
    (s : Convexity.StdSimplex ℝ (Fin (n + m + 1))) (u : ℕ) :
    shuffleCumThrough ((shuffleCell S s).1) u =
      ∑ j ∈ Finset.univ.filter
        (fun j : Fin (n + m + 1) => (S.projA j).val ≤ u),
        s.weights j := by
  unfold shuffleCumThrough
  calc ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i.val ≤ u),
          ((shuffleCell S s).1.weights i)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i.val ≤ u),
          ∑ j ∈ Finset.univ.filter
            (fun j : Fin (n + m + 1) => S.projA j = i),
            s.weights j := by
        apply Finset.sum_congr rfl
        intro i _
        exact shuffleCell_fst_fiber S s i
    _ = ∑ j ∈ Finset.univ.filter (fun j : Fin (n + m + 1) =>
            S.projA j ∈ Finset.univ.filter (fun i : Fin (n + 1) => i.val ≤ u)),
          s.weights j :=
        Finset.sum_fiberwise_eq_sum_filter _ _ _ _
    _ = ∑ j ∈ Finset.univ.filter
          (fun j : Fin (n + m + 1) => (S.projA j).val ≤ u),
          s.weights j := by
        have hset : Finset.univ.filter (fun j : Fin (n + m + 1) =>
            S.projA j ∈ Finset.univ.filter (fun i : Fin (n + 1) => i.val ≤ u)) =
          Finset.univ.filter
            (fun j : Fin (n + m + 1) => (S.projA j).val ≤ u) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hset]

/-- A strict cumulative sum of a second-factor cell image is the source mass
over the strict sublevel preimage of `projB`. -/
theorem shuffleSndCumBefore_eq_preimage (S : ProdSimplexShuffle n m)
    (s : Convexity.StdSimplex ℝ (Fin (n + m + 1))) (u : ℕ) :
    shuffleCumBefore ((shuffleCell S s).2) u =
      ∑ j ∈ Finset.univ.filter
        (fun j : Fin (n + m + 1) => (S.projB j).val < u),
        s.weights j := by
  unfold shuffleCumBefore
  calc ∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => i.val < u),
          ((shuffleCell S s).2.weights i)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => i.val < u),
          ∑ j ∈ Finset.univ.filter
            (fun j : Fin (n + m + 1) => S.projB j = i),
            s.weights j := by
        apply Finset.sum_congr rfl
        intro i _
        exact shuffleCell_snd_fiber S s i
    _ = ∑ j ∈ Finset.univ.filter (fun j : Fin (n + m + 1) =>
            S.projB j ∈ Finset.univ.filter (fun i : Fin (m + 1) => i.val < u)),
          s.weights j :=
        Finset.sum_fiberwise_eq_sum_filter _ _ _ _
    _ = ∑ j ∈ Finset.univ.filter
          (fun j : Fin (n + m + 1) => (S.projB j).val < u),
          s.weights j := by
        have hset : Finset.univ.filter (fun j : Fin (n + m + 1) =>
            S.projB j ∈ Finset.univ.filter (fun i : Fin (m + 1) => i.val < u)) =
          Finset.univ.filter
            (fun j : Fin (n + m + 1) => (S.projB j).val < u) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hset]

/-- A weak cumulative sum of a second-factor cell image is the source mass
over the weak sublevel preimage of `projB`. -/
theorem shuffleSndCumThrough_eq_preimage (S : ProdSimplexShuffle n m)
    (s : Convexity.StdSimplex ℝ (Fin (n + m + 1))) (u : ℕ) :
    shuffleCumThrough ((shuffleCell S s).2) u =
      ∑ j ∈ Finset.univ.filter
        (fun j : Fin (n + m + 1) => (S.projB j).val ≤ u),
        s.weights j := by
  unfold shuffleCumThrough
  calc ∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => i.val ≤ u),
          ((shuffleCell S s).2.weights i)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => i.val ≤ u),
          ∑ j ∈ Finset.univ.filter
            (fun j : Fin (n + m + 1) => S.projB j = i),
            s.weights j := by
        apply Finset.sum_congr rfl
        intro i _
        exact shuffleCell_snd_fiber S s i
    _ = ∑ j ∈ Finset.univ.filter (fun j : Fin (n + m + 1) =>
            S.projB j ∈ Finset.univ.filter (fun i : Fin (m + 1) => i.val ≤ u)),
          s.weights j :=
        Finset.sum_fiberwise_eq_sum_filter _ _ _ _
    _ = ∑ j ∈ Finset.univ.filter
          (fun j : Fin (n + m + 1) => (S.projB j).val ≤ u),
          s.weights j := by
        have hset : Finset.univ.filter (fun j : Fin (n + m + 1) =>
            S.projB j ∈ Finset.univ.filter (fun i : Fin (m + 1) => i.val ≤ u)) =
          Finset.univ.filter
            (fun j : Fin (n + m + 1) => (S.projB j).val ≤ u) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hset]

end Preimage

section Range

variable {n m : ℕ}

/-- Forward range implication: membership in `Set.range (shuffleCell S)`
forces strict first-factor cumulative mass below the chain level to be at
most weak second-factor cumulative mass through the chain level. -/
theorem shuffleCell_mem_range_imp_cumAB (S : ProdSimplexShuffle n m)
    {x : Convexity.StdSimplex ℝ (Fin (n + 1))}
    {y : Convexity.StdSimplex ℝ (Fin (m + 1))}
    (h : (x, y) ∈ Set.range (shuffleCell S)) (k : Fin (n + m + 1)) :
    shuffleCumBefore x (S.projA k).val ≤
      shuffleCumThrough y (S.projB k).val := by
  obtain ⟨s, hs⟩ := h
  have hfst : (shuffleCell S s).1 = x := congrArg Prod.fst hs
  have hsnd : (shuffleCell S s).2 = y := congrArg Prod.snd hs
  rw [← hfst, ← hsnd, shuffleCumBefore_eq_preimage,
    shuffleSndCumThrough_eq_preimage]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact fiberA_mem_imp_B_le S k j hj
  · intro j _ _
    exact s.weights_nonneg j

/-- Forward range implication: membership in `Set.range (shuffleCell S)`
forces strict second-factor cumulative mass below the chain level to be at
most weak first-factor cumulative mass through the chain level. -/
theorem shuffleCell_mem_range_imp_cumBA (S : ProdSimplexShuffle n m)
    {x : Convexity.StdSimplex ℝ (Fin (n + 1))}
    {y : Convexity.StdSimplex ℝ (Fin (m + 1))}
    (h : (x, y) ∈ Set.range (shuffleCell S)) (k : Fin (n + m + 1)) :
    shuffleCumBefore y (S.projB k).val ≤
      shuffleCumThrough x (S.projA k).val := by
  obtain ⟨s, hs⟩ := h
  have hfst : (shuffleCell S s).1 = x := congrArg Prod.fst hs
  have hsnd : (shuffleCell S s).2 = y := congrArg Prod.snd hs
  rw [← hfst, ← hsnd, shuffleSndCumBefore_eq_preimage,
    shuffleCumThrough_eq_preimage]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact fiberB_mem_imp_A_le S k j hj
  · intro j _ _
    exact s.weights_nonneg j

end Range
