/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Admixture.TreeAdditivity
public import MathlibExt.Biology.Phylogenetics.Buneman

/-!
# Tests for shift, stem and rerooting invariance

The examples check rerooting a four-leaf tree at an internal node, stem invariance on a
three-leaf star, and a binary-loading square that is not a tree metric. A local
realization of weights and nonnegative lengths as a drift model supplies the concrete
models.
-/

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
open scoped symmDiff

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.TreeAdditivity

open MathlibExt.Biology.PopulationGenetics.FStatistics.DriftModel

open MathlibExt.Biology.PopulationGenetics.FStatistics.DriftModel

/-- Local realization of arbitrary weights and nonnegative lengths (counting measure on the
edge set, increment `√(len e)` on the atom `e`): shows every hypothesis below is satisfiable
with any lengths. -/
noncomputable def modelOfLen {P E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E]
    [DiscreteMeasurableSpace E]
    (w : P → E → ℝ) (len : E → ℝ) (hlen : ∀ e, 0 ≤ len e) :
    DriftModel (Measure.count : Measure E) E P where
  root _ := 1 / 2
  incr e ω := if ω = e then √(len e) else 0
  len := len
  weight := w
  memLp_root := memLp_const _
  memLp_incr _ := MemLp.of_discrete
  inner_incr e f hef := by
    rw [integral_count]
    refine Finset.sum_eq_zero fun ω _ => ?_
    by_cases h : ω = e
    · subst h; simp [hef]
    · simp [h]
  sq_incr e := by
    rw [integral_count, Finset.sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
    simp [Real.sq_sqrt (hlen e)]

/-! #### Acceptance 1: rerooting a 4-leaf tree at an internal node gives the same f2 matrix.

Rooted tree `((A, B), (C, D))` with root `r`, internal nodes `u` (parent of `A`, `B`) and `v`
(parent of `C`, `D`). Edges: `0 = ru`, `1 = rv`, `2 = uA`, `3 = uB`, `4 = vC`, `5 = vD`.
Populations `0 = A`, `1 = B`, `2 = C`, `3 = D`. Rerooted at `u`: the edge `ru` reverses, so the
lineages change by `∆ {0}`. -/

def linOrig : Fin 4 → Finset (Fin 6) := ![{0, 2}, {0, 3}, {1, 4}, {1, 5}]
def linReroot : Fin 4 → Finset (Fin 6) := ![{2}, {3}, {0, 1, 4}, {0, 1, 5}]

theorem linReroot_eq : ∀ X, linReroot X = linOrig X ∆ {0} := by decide

noncomputable def wOf (L : Fin 4 → Finset (Fin 6)) : Fin 4 → Fin 6 → ℝ :=
  fun X e => if e ∈ L X then 1 else 0

theorem lineage_ofLen (L : Fin 4 → Finset (Fin 6)) (len : Fin 6 → ℝ) (hlen : ∀ e, 0 ≤ len e)
    (X : Fin 4) : (modelOfLen (wOf L) len hlen).lineage X = L X := by
  ext e
  by_cases h : e ∈ L X <;> simp [lineage, modelOfLen, wOf, h]

theorem binary_ofLen (L : Fin 4 → Finset (Fin 6)) (len : Fin 6 → ℝ) (hlen : ∀ e, 0 ≤ len e) :
    (modelOfLen (wOf L) len hlen).HasBinaryLoadings := fun X e => by
  by_cases h : e ∈ L X <;> simp [modelOfLen, wOf, h]

/-- The rerooted tree has the same `f2` matrix, for every choice of edge lengths. -/
theorem reroot_f2 (len : Fin 6 → ℝ) (hlen : ∀ e, 0 ≤ len e) (X Y : Fin 4) :
    f2 Measure.count (modelOfLen (wOf linReroot) len hlen).freq X Y =
      f2 Measure.count (modelOfLen (wOf linOrig) len hlen).freq X Y :=
  f2_eq_of_lineage_eq_symmDiff (modelOfLen (wOf linOrig) len hlen) (modelOfLen (wOf linReroot) len hlen)
    (binary_ofLen _ len hlen) (binary_ofLen _ len hlen) rfl {0}
    (fun X => by rw [lineage_ofLen, lineage_ofLen, linReroot_eq]) X Y

/-- The two rootings are genuinely different models (the root-relative lineages differ), and
`f2 A C = ℓ_ru + ℓ_rv + ℓ_uA + ℓ_vC` in both: the root splits the path `u – v` but
`f2` only sees the path length. -/
theorem reroot_distinct : linReroot 0 ≠ linOrig 0 := by decide

theorem reroot_f2_AC (len : Fin 6 → ℝ) (hlen : ∀ e, 0 ≤ len e) :
    f2 Measure.count (modelOfLen (wOf linReroot) len hlen).freq 0 2 = len 0 + len 1 + len 2 + len 4 := by
  rw [f2_freq]
  simp [modelOfLen, wOf, linReroot, Fin.sum_univ_succ]
  ring

/-! #### Stem invariance on a concrete tree: a root stem edge `0` above `u`, `v`. -/

/-- Star tree with a root stem: edge `0` is traversed by every population, edge `X.succ` is the
private edge of population `X`. -/
noncomputable def stemModel (len : Fin 4 → ℝ) (hlen : ∀ e, 0 ≤ len e) :
    DriftModel (Measure.count : Measure (Fin 4)) (Fin 4) (Fin 3) :=
  modelOfLen (fun X e => if e = 0 ∨ e = X.succ then 1 else 0) len hlen

theorem len7_nonneg : ∀ e, 0 ≤ (![7, 1, 2, 3] : Fin 4 → ℝ) e := by
  intro e; fin_cases e <;> norm_num
theorem len1_nonneg : ∀ e, 0 ≤ (![1, 1, 2, 3] : Fin 4 → ℝ) e := by
  intro e; fin_cases e <;> norm_num

/-- Changing the stem length (here `1` to `7`) changes no `f4`. -/
theorem stem_invariance (A B C D : Fin 3) :
    f4 Measure.count (stemModel ![7, 1, 2, 3] len7_nonneg).freq A B C D =
      f4 Measure.count (stemModel ![1, 1, 2, 3] len1_nonneg).freq A B C D := by
  refine f4_eq_of_len_eq_of_weight_const (stemModel ![1, 1, 2, 3] len1_nonneg)
    (stemModel ![7, 1, 2, 3] len7_nonneg) rfl (fun e he X Y => ?_) A B C D
  fin_cases e
  · simp [stemModel, modelOfLen]
  all_goals simp [stemModel, modelOfLen] at he

/-! #### Acceptance 2: binary loadings without tree structure (the `HasBinaryLoadings` square).

Two edges of length `1`, four populations with weight vectors `00`, `10`, `01`, `11`. -/

noncomputable def square : DriftModel (Measure.count : Measure (Fin 2)) (Fin 2) (Fin 4) :=
  modelOfLen (fun X e => ![![0, 0], ![1, 0], ![0, 1], ![1, 1]] X e) (fun _ => 1) (fun _ => zero_le_one)

theorem square_binary : square.HasBinaryLoadings := by
  intro X e
  fin_cases X <;> fin_cases e <;> simp [square, modelOfLen]

theorem square_f2 (X Y : Fin 4) :
    f2 Measure.count square.freq X Y =
      ![![0, 1, 1, 2], ![1, 0, 2, 1], ![1, 2, 0, 1], ![2, 1, 1, 0]] X Y := by
  rw [f2_freq]
  fin_cases X <;> fin_cases Y <;> simp [square, modelOfLen, Fin.sum_univ_two] <;> norm_num

/-- The square violates the four-point condition, so its `f2` is not a tree metric even though
its loadings are binary. -/
theorem square_not_fourPoint :
    ¬ ∀ x y z w : Fin 4, f2 Measure.count square.freq x y + f2 Measure.count square.freq z w ≤
      max (f2 Measure.count square.freq x z + f2 Measure.count square.freq y w)
        (f2 Measure.count square.freq x w + f2 Measure.count square.freq y z) := by
  intro h
  have := h 0 3 1 2
  simp only [square_f2] at this
  norm_num at this

/-- With Atlas's Buneman API: the square's `f2` is not a tree metric (it fails the four-point
condition that every tree metric satisfies). -/
theorem square_not_isTreeMetric :
    ¬ MathlibExt.Biology.Phylogenetics.Buneman.IsTreeMetric
      (fun x y : Fin 4 => f2 Measure.count square.freq x y) := fun h =>
  square_not_fourPoint (h.fourPointCondition)

/-! #### Endpoints -/

/-- Zero shift (`c = 0`, `s = 1`): any two models with the same weights and lengths agree. -/
example {Ω Ω' P E : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
    {μ' : Measure Ω'} [Fintype E] (M : DriftModel μ E P) (M' : DriftModel μ' E P)
    (hlen : M'.len = M.len) (hw : M'.weight = M.weight) (A B C D : P) :
    f4 μ' M'.freq A B C D = f4 μ M.freq A B C D :=
  f4_eq_of_weight_eq_add M M' hlen 0 (fun X => by simp [hw]) A B C D

/-- A non-sign scaling is not allowed: with `s = 2` the statement fails (one edge, `w A = 1`,
`w B = 0`, `len = 1`: `f2` becomes `4`, not `1`). -/
example : f2 Measure.count (modelOfLen (P := Fin 2) (E := Fin 1) (fun X _ => 2 * ![1, 0] X)
      (fun _ => 1) (fun _ => zero_le_one)).freq 0 1 ≠
    f2 Measure.count (modelOfLen (P := Fin 2) (E := Fin 1) (fun X _ => ![1, 0] X)
      (fun _ => 1) (fun _ => zero_le_one)).freq 0 1 := by
  rw [f2_freq, f2_freq]
  simp [modelOfLen]
  norm_num

/-- Empty edge set: every model has all f-statistics `0`, and the statements are trivial. -/
example {Ω P : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} (M : DriftModel μ Empty P)
    (A B C D : P) : f4 μ M.freq A B C D = 0 := by
  simp [M.f4_freq]


#print axioms MathlibExt.Biology.PopulationGenetics.FStatistics.DriftModel.f4_eq_of_weight_eq_mul_add
#print axioms MathlibExt.Biology.PopulationGenetics.FStatistics.DriftModel.f4_eq_of_len_eq_of_weight_const
#print axioms MathlibExt.Biology.PopulationGenetics.FStatistics.DriftModel.f2_eq_of_lineage_eq_symmDiff

end MathlibExtTest.Biology.PopulationGenetics.Admixture.TreeAdditivity
