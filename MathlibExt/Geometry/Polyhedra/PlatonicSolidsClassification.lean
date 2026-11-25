/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Classification of the Platonic solids

This file classifies the Platonic solids up to their count tuple `(p, q, V, E, F)` and proves that
each of the five tuples is realized. Euler's formula and the two incidence-count equations imply
`1 / p + 1 / q > 1 / 2`, leaving only the five classical count tuples; explicit Euclidean
coordinates realize every tuple. Classification up to combinatorial equivalence or Euclidean
congruence is not proved here.
-/

@[expose] public section

namespace MetaMathlibExt

section

/-- Purely arithmetic core of the Platonic solids classification:
from `2 * E = p * F`, `2 * E = q * V` and the Euler relation
`V - E + F = 2` (with `3 ≤ p`, `3 ≤ q` and positivity),
only the five classical `(p, q, V, E, F)` tuples are possible. -/
private theorem platonic_count_classification (V E F p q : ℕ)
    (_hV : 0 < V) (hE : 0 < E) (hF : 0 < F)
    (hp : 3 ≤ p) (hq : 3 ≤ q)
    (h1 : 2 * E = p * F) (h2 : 2 * E = q * V)
    (hEuler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2) :
    ((p = 3 ∧ q = 3 ∧ V = 4 ∧ E = 6 ∧ F = 4) ∨
     (p = 4 ∧ q = 3 ∧ V = 8 ∧ E = 12 ∧ F = 6) ∨
     (p = 3 ∧ q = 4 ∧ V = 6 ∧ E = 12 ∧ F = 8) ∨
     (p = 5 ∧ q = 3 ∧ V = 20 ∧ E = 30 ∧ F = 12) ∨
     (p = 3 ∧ q = 5 ∧ V = 12 ∧ E = 30 ∧ F = 20)) := by
  have h1z : 2 * (E : ℤ) = (p : ℤ) * (F : ℤ) := by exact_mod_cast h1
  have h2z : 2 * (E : ℤ) = (q : ℤ) * (V : ℤ) := by exact_mod_cast h2
  have hEz : (0 : ℤ) < (E : ℤ) := by exact_mod_cast hE
  have hpz : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have hqz : (3 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have hppos : (0 : ℤ) < (p : ℤ) := by omega
  have hqpos : (0 : ℤ) < (q : ℤ) := by omega
  -- Key identity: E * (2p + 2q - pq) = 2pq, from Euler scaled by pq.
  have hkey : (E : ℤ) * (2 * (p : ℤ) + 2 * (q : ℤ) - (p : ℤ) * (q : ℤ))
      = 2 * (p : ℤ) * (q : ℤ) := by
    linear_combination (p : ℤ) * (q : ℤ) * hEuler + (p : ℤ) * h2z + (q : ℤ) * h1z
  have h2pq : (0 : ℤ) < 2 * (p : ℤ) * (q : ℤ) := by
    have hmul : (0 : ℤ) < (p : ℤ) * (q : ℤ) := mul_pos hppos hqpos
    linarith
  -- Hence 2p + 2q - pq > 0, i.e. (p - 2) * (q - 2) < 4.
  have hpos : (0 : ℤ) < 2 * (p : ℤ) + 2 * (q : ℤ) - (p : ℤ) * (q : ℤ) :=
    pos_of_mul_pos_right (hkey ▸ h2pq) (le_of_lt hEz)
  have hp5 : (p : ℤ) ≤ 5 := by
    by_contra h
    have h6 : (6 : ℤ) ≤ (p : ℤ) := by omega
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - 6 by omega)
      (show (0 : ℤ) ≤ (q : ℤ) - 3 by omega)]
  have hq5 : (q : ℤ) ≤ 5 := by
    by_contra h
    have h6 : (6 : ℤ) ≤ (q : ℤ) := by omega
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - 3 by omega)
      (show (0 : ℤ) ≤ (q : ℤ) - 6 by omega)]
  have hp5n : p ≤ 5 := by omega
  have hq5n : q ≤ 5 := by omega
  interval_cases p <;> interval_cases q <;> omega

/-- Regular tetrahedron vertices (symmetric `±1` coordinates). -/
private def tetVert : Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 1, 1], !₂[1, -1, -1], !₂[-1, 1, -1], !₂[-1, -1, 1]]

private lemma tet_dist_aux : dist (1 : ℝ) (-1 : ℝ) = 2 := by
  rw [dist_eq_norm]
  norm_num

private lemma tet_dist_aux2 : dist (-1 : ℝ) (1 : ℝ) = 2 := by
  rw [dist_comm]
  exact tet_dist_aux

private lemma sqrt8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  have h : (8 : ℝ) = 2 ^ 2 * 2 := by norm_num
  rw [h, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- All tetrahedron edges have uniform length `2 * Real.sqrt 2`. -/
private lemma tet_dist (i j : Fin 4) (h : i ≠ j) :
    dist (tetVert i) (tetVert j) = 2 * Real.sqrt 2 := by
  rw [← sqrt8]
  fin_cases i <;> fin_cases j <;> try (exact False.elim (h rfl))
  all_goals
    simp only [tetVert, EuclideanSpace.dist_eq, Fin.sum_univ_three, Fin.reduceFinMk,
      Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      tet_dist_aux, tet_dist_aux2, dist_self]
  all_goals norm_num

/-- Three vertex differences spanning the tetrahedron. -/
private def tetD : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![tetVert 1 - tetVert 0, tetVert 2 - tetVert 0, tetVert 3 - tetVert 0]

private lemma tet_gram_det : (Matrix.gram ℝ tetD).det = 256 := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.gram_apply, tetD, tetVert, PiLp.inner_apply,
    Real.inner_apply, Fin.sum_univ_three, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three]
  norm_num

private lemma tetD_indep : LinearIndependent ℝ tetD := by
  rw [← Matrix.det_gram_ne_zero_iff_linearIndependent, tet_gram_det]
  norm_num

private lemma tet_span_top :
    Submodule.span ℝ (Set.range tetD) = ⊤ :=
  LinearIndependent.span_eq_top_of_card_eq_finrank tetD_indep
    (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])

/-- Full-dimensionality for the tetrahedron vertex set. -/
private lemma tet_finrank : Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
    ∃ i j : Fin 4, d = tetVert i - tetVert j}) = 3 := by
  have hle : Submodule.span ℝ (Set.range tetD) ≤
      Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 4, d = tetVert i - tetVert j} := by
    apply Submodule.span_mono
    rintro x ⟨k, rfl⟩
    fin_cases k
    · exact ⟨1, 0, rfl⟩
    · exact ⟨2, 0, rfl⟩
    · exact ⟨3, 0, rfl⟩
  rw [tet_span_top] at hle
  have hSeq : Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
      ∃ i j : Fin 4, d = tetVert i - tetVert j} = ⊤ := top_le_iff.mp hle
  have hfin : Module.finrank ℝ ↥(⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := Submodule.topEquiv.finrank_eq
  rw [hSeq, hfin, finrank_euclideanSpace_fin]

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear functional `x ↦ inner n x` is linear. -/
private lemma isLinearMap_inner_left (n : E) :
    IsLinearMap ℝ (fun x : E => inner (𝕜 := ℝ) n x) where
  map_add x y := inner_add_right n x y
  map_smul c x := inner_smul_right n x c

/-- Convex hull preserves a linear upper bound. -/
private lemma inner_le_of_mem_convexHull {S : Set E} {n : E} {c : ℝ}
    (h : ∀ s ∈ S, inner (𝕜 := ℝ) n s ≤ c) {x : E}
    (hx : x ∈ convexHull ℝ S) : inner (𝕜 := ℝ) n x ≤ c := by
  have hsub : convexHull ℝ S ⊆ {w : E | inner (𝕜 := ℝ) n w ≤ c} :=
    convexHull_min (fun s hs => h s hs) (convex_halfSpace_le (isLinearMap_inner_left n) c)
  exact hsub hx

/-- Convex hull preserves a linear lower bound. -/
private lemma inner_ge_of_mem_convexHull {S : Set E} {n : E} {c : ℝ}
    (h : ∀ s ∈ S, c ≤ inner (𝕜 := ℝ) n s) {x : E}
    (hx : x ∈ convexHull ℝ S) : c ≤ inner (𝕜 := ℝ) n x := by
  have hsub : convexHull ℝ S ⊆ {w : E | c ≤ inner (𝕜 := ℝ) n w} :=
    convexHull_min (fun s hs => h s hs) (convex_halfSpace_ge (isLinearMap_inner_left n) c)
  exact hsub hx

/-- Convex hull preserves a linear equation. -/
private lemma inner_eq_of_mem_convexHull {S : Set E} {n : E} {c : ℝ}
    (h : ∀ s ∈ S, inner (𝕜 := ℝ) n s = c) {x : E}
    (hx : x ∈ convexHull ℝ S) : inner (𝕜 := ℝ) n x = c := by
  have hle : inner (𝕜 := ℝ) n x ≤ c :=
    inner_le_of_mem_convexHull (fun s hs => (h s hs).le) hx
  have hge : c ≤ inner (𝕜 := ℝ) n x :=
    inner_ge_of_mem_convexHull (fun s hs => (h s hs).ge) hx
  linarith

/-- A point achieving equality in a supporting halfspace is not interior. -/
private lemma not_mem_interior_of_support {B : Set E} {n : E} {c : ℝ} {y : E}
    (hle : ∀ x ∈ B, inner (𝕜 := ℝ) n x ≤ c)
    (heq : inner (𝕜 := ℝ) n y = c) (hn : n ≠ 0) :
    y ∉ interior B := by
  intro hy
  obtain ⟨ε, hε_pos, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hy)
  have hnorm_pos : 0 < ‖n‖ := norm_pos_iff.mpr hn
  set α : ℝ := ε / (2 * ‖n‖) with hα
  have hα_pos : 0 < α := by
    rw [hα]
    positivity
  set z : E := y + α • n with hz
  have hdist : dist z y < ε := by
    rw [hz, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hα_pos]
    have hne : ‖n‖ ≠ 0 := ne_of_gt hnorm_pos
    rw [hα]
    field_simp
    linarith
  have hzB : z ∈ B := by
    have hzball : z ∈ Metric.ball y ε := Metric.mem_ball.mpr hdist
    exact interior_subset (hball hzball)
  have hle_z : inner (𝕜 := ℝ) n z ≤ c := hle z hzB
  have hinner : inner (𝕜 := ℝ) n z = c + α * (‖n‖ ^ 2) := by
    rw [hz, inner_add_right, heq, inner_smul_right, real_inner_self_eq_norm_sq]
  have hpos : 0 < α * (‖n‖ ^ 2) := by positivity
  linarith

/-- A point of `B` on a supporting hyperplane lies in the frontier. -/
private lemma mem_frontier_of_support {B : Set E} {n : E} {c : ℝ} {y : E}
    (hyB : y ∈ B) (hle : ∀ x ∈ B, inner (𝕜 := ℝ) n x ≤ c)
    (heq : inner (𝕜 := ℝ) n y = c) (hn : n ≠ 0) :
    y ∈ frontier B := by
  rw [mem_frontier_iff_notMem_interior hyB]
  exact not_mem_interior_of_support hle heq hn

/-- Strict linear separation keeps a point outside a convex hull. -/
private lemma not_mem_convexHull_of_separation {S : Set E} {n : E} {c : ℝ} {y : E}
    (h : ∀ s ∈ S, inner (𝕜 := ℝ) n s ≤ c)
    (hy : c < inner (𝕜 := ℝ) n y) :
    y ∉ convexHull ℝ S := by
  intro hmem
  have hle := inner_le_of_mem_convexHull h hmem
  linarith

/-- The span of two vectors has finrank at most two. -/
private lemma finrank_span_pair_le (a b : E) :
    Module.finrank ℝ (Submodule.span ℝ ({a, b} : Set E)) ≤ 2 := by
  classical
  have hcoe : ({a, b} : Set E) = ↑({a, b} : Finset E) := by
    simp only [Finset.coe_insert, Finset.coe_singleton]
  rw [hcoe]
  have hle : Set.finrank ℝ (↑({a, b} : Finset E) : Set E) ≤ ({a, b} : Finset E).card :=
    finrank_span_finset_le_card _
  have hcard : ({a, b} : Finset E).card ≤ 2 := by
    calc ({a, b} : Finset E).card ≤ ({b} : Finset E).card + 1 :=
          Finset.card_insert_le a ({b} : Finset E)
      _ = 2 := by simp only [Finset.card_singleton]
  have hfin : Module.finrank ℝ (Submodule.span ℝ (↑({a, b} : Finset E) : Set E)) =
      Set.finrank ℝ (↑({a, b} : Finset E) : Set E) := rfl
  rw [hfin]
  exact hle.trans hcard

/-- Differences of three points span a space of finrank at most two. -/
private lemma finrank_triangle_le (f : Fin 3 → E) :
    Module.finrank ℝ (Submodule.span ℝ {d : E | ∃ i j : Fin 3, d = f i - f j}) ≤ 2 := by
  classical
  have hsub : Submodule.span ℝ {d : E | ∃ i j : Fin 3, d = f i - f j} ≤
      Submodule.span ℝ ({f 1 - f 0, f 2 - f 0} : Set E) := by
    rw [Submodule.span_le]
    rintro d ⟨i, j, rfl⟩
    have hmem : ∀ k : Fin 3, f k - f 0 ∈
        Submodule.span ℝ ({f 1 - f 0, f 2 - f 0} : Set E) := by
      intro k
      fin_cases k
      · change f 0 - f 0 ∈ Submodule.span ℝ ({f 1 - f 0, f 2 - f 0} : Set E)
        rw [sub_self]
        exact Submodule.zero_mem _
      · change f 1 - f 0 ∈ Submodule.span ℝ ({f 1 - f 0, f 2 - f 0} : Set E)
        exact Submodule.subset_span (by simp)
      · change f 2 - f 0 ∈ Submodule.span ℝ ({f 1 - f 0, f 2 - f 0} : Set E)
        exact Submodule.subset_span (by simp)
    have heq : f i - f j = (f i - f 0) - (f j - f 0) := by abel
    rw [heq]
    exact Submodule.sub_mem _ (hmem i) (hmem j)
  have hfin : Module.Finite ℝ ↥(Submodule.span ℝ ({f 1 - f 0, f 2 - f 0} : Set E)) :=
    FiniteDimensional.span_of_finite ℝ
      (Set.Finite.insert (f 1 - f 0) (Set.finite_singleton (f 2 - f 0)))
  exact (@Submodule.finrank_mono ℝ E _ _ _ _ _ _ hfin hsub).trans (finrank_span_pair_le _ _)

/-- A finite H-representation is contained in a convex set when every radial boundary point is. -/
private lemma mem_of_mem_all_halfspaces
    {ι : Type*} [Finite ι] [Nonempty ι]
    (n : ι → E) (c : ℝ) (hc : 0 < c) (K : Set E)
    (hconv : Convex ℝ K) (hzero : 0 ∈ K)
    (hpos : ∀ x : E, x ≠ 0 → ∃ i : ι, 0 < inner (𝕜 := ℝ) (n i) x)
    (hface : ∀ (i : ι) (x : E),
      (∀ j : ι, inner (𝕜 := ℝ) (n j) x ≤ c) →
      inner (𝕜 := ℝ) (n i) x = c → x ∈ K)
    {x : E} (hx : ∀ i : ι, inner (𝕜 := ℝ) (n i) x ≤ c) : x ∈ K := by
  classical
  let _ := Fintype.ofFinite ι
  by_cases hx0 : x = 0
  · simpa only [hx0] using hzero
  let s : Finset ℝ := Finset.univ.image (fun i => inner (𝕜 := ℝ) (n i) x)
  have hs : s.Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨inner (𝕜 := ℝ) (n i) x,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let m : ℝ := s.max' hs
  have hm_mem : m ∈ s := Finset.max'_mem s hs
  obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hm_mem
  have hle_m (g : ι) : inner (𝕜 := ℝ) (n g) x ≤ m := by
    apply Finset.le_max' s
    exact Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩
  have hm_pos : 0 < m := by
    obtain ⟨g, hg⟩ := hpos x hx0
    exact hg.trans_le (hle_m g)
  have hm_le : m ≤ c := by
    apply Finset.max'_le s hs c
    intro y hy
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hy
    exact hx g
  let y : E := (c / m) • x
  have hyall (g : ι) : inner (𝕜 := ℝ) (n g) y ≤ c := by
    simp only [y, inner_smul_right]
    have hmul := mul_le_mul_of_nonneg_left (hle_m g) (le_of_lt (div_pos hc hm_pos))
    rwa [div_mul_cancel₀ c hm_pos.ne'] at hmul
  have hyeq : inner (𝕜 := ℝ) (n f) y = c := by
    simp only [y, inner_smul_right, hf, div_mul_cancel₀ c hm_pos.ne']
  have hyK : y ∈ K := hface f y hyall hyeq
  have ht : m / c ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hc).mpr hm_le
  have hline := hconv.lineMap_mem hzero hyK ht
  have hprod : (m / c) * (c / m) = 1 := by
    field_simp
  simpa only [AffineMap.lineMap_apply_module, y, smul_zero, zero_add, smul_smul,
    hprod, one_smul] using hline

end Helpers

section Tetrahedron

/-- Tetrahedron edge endpoints (all six unordered vertex pairs). -/
private def tetEdge : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- Tetrahedron faces: face `f` omits vertex `f`. -/
private def tetFace : Fin 4 → Fin 3 → Fin 4 :=
  ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

/-- Face-local separating normals (coordinate directions). -/
private def tetFaceSepN : Fin 4 → Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![![!₂[(1 : ℝ), 0, 0], !₂[0, 1, 0], !₂[0, 0, 1]],
    ![!₂[(1 : ℝ), 0, 0], !₂[0, 0, -1], !₂[0, -1, 0]],
    ![!₂[(0 : ℝ), 1, 0], !₂[0, 0, -1], !₂[-1, 0, 0]],
    ![!₂[(0 : ℝ), 0, 1], !₂[0, -1, 0], !₂[-1, 0, 0]]]

/-- Supporting-plane normals (negated vertices). -/
private def tetSuppN : Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(-1 : ℝ), -1, -1], !₂[-1, 1, 1], !₂[1, -1, 1], !₂[1, 1, -1]]

/-- For each vertex, a face containing it. -/
private def tetVertFace : Fin 4 → Fin 4 := ![1, 2, 3, 0]

/-- Index witnessing the vertex-face membership above. -/
private def tetVertFaceIdx : Fin 4 → Fin 3 := ![0, 1, 2, 2]

/-- Tetrahedron edge lengths. -/
private lemma tet_edge_length (e : Fin 6) :
    dist (tetVert (tetEdge e).1) (tetVert (tetEdge e).2) = 2 * Real.sqrt 2 := by
  fin_cases e <;> exact tet_dist _ _ (by decide)

/-- Tetrahedron face edges. -/
private lemma tet_face_edge (f : Fin 4) (i j : Fin 3) (h : j.val = (i.val + 1) % 3) :
    dist (tetVert (tetFace f i)) (tetVert (tetFace f j)) = 2 * Real.sqrt 2 := by
  fin_cases f <;> fin_cases i <;> fin_cases j
  all_goals try (norm_num at h)
  all_goals exact tet_dist _ _ (by decide)

/-- Tetrahedron face diagonals (equal to edges for triangles). -/
private lemma tet_face_diag (f : Fin 4) (h0 i j : Fin 3)
    (h1 : h0.val = (i.val + 3 - 1) % 3) (h2 : j.val = (i.val + 1) % 3) :
    dist (tetVert (tetFace f h0)) (tetVert (tetFace f j)) = 2 * Real.sqrt 2 := by
  fin_cases f <;> fin_cases h0 <;> fin_cases i <;> fin_cases j
  all_goals try (norm_num at h1)
  all_goals try (norm_num at h2)
  all_goals exact tet_dist _ _ (by decide)

/-- Tetrahedron faces are injective. -/
private lemma tet_face_inj (f : Fin 4) : Function.Injective (tetFace f) := by
  fin_cases f <;> decide

/-- Every tetrahedron face edge is a graph edge. -/
private lemma tet_face_edge_exists (f : Fin 4) (i j : Fin 3)
    (h : j.val = (i.val + 1) % 3) :
    ∃ e : Fin 6, tetEdge e = (tetFace f i, tetFace f j) ∨
      tetEdge e = (tetFace f j, tetFace f i) := by
  fin_cases f <;> fin_cases i <;> fin_cases j
  all_goals try (norm_num at h)
  all_goals decide

/-- Every tetrahedron graph edge is a face edge. -/
private lemma tet_edge_face_exists (e : Fin 6) :
    ∃ f : Fin 4, ∃ i j : Fin 3, j.val = (i.val + 1) % 3 ∧
      (tetEdge e = (tetFace f i, tetFace f j) ∨
        tetEdge e = (tetFace f j, tetFace f i)) := by
  fin_cases e <;> decide

/-- Tetrahedron edges are duplicate-free. -/
private lemma tet_edge_dup (e₁ e₂ : Fin 6)
    (h : tetEdge e₁ = tetEdge e₂ ∨ tetEdge e₁ = (tetEdge e₂).swap) :
    e₁ = e₂ := by
  revert h
  fin_cases e₁ <;> fin_cases e₂ <;> decide

/-- Cyclic edge pairs with disjoint endpoints are impossible for triangles. -/
private lemma tet_disjoint_neg :
    ∀ i₁ j₁ i₂ j₂ : Fin 3,
    ¬(j₁.val = (i₁.val + 1) % 3 ∧ j₂.val = (i₂.val + 1) % 3 ∧
      i₁ ≠ i₂ ∧ i₁ ≠ j₂ ∧ j₁ ≠ i₂ ∧ j₁ ≠ j₂) := by
  decide

/-- The two faces containing each tetrahedron edge. -/
private def tetEdgeFaces : Fin 6 → Fin 4 × Fin 4 :=
  ![(2, 3), (1, 3), (1, 2), (0, 3), (0, 2), (0, 1)]

/-- Each tetrahedron edge lies in exactly two faces. -/
private lemma tet_two_face (e : Fin 6) :
    Set.ncard {f : Fin 4 | ∃ i j : Fin 3, j.val = (i.val + 1) % 3 ∧
      (tetEdge e = (tetFace f i, tetFace f j) ∨
        tetEdge e = (tetFace f j, tetFace f i))} = 2 := by
  have hset : ∀ e : Fin 6, {f : Fin 4 | ∃ i j : Fin 3, j.val = (i.val + 1) % 3 ∧
      (tetEdge e = (tetFace f i, tetFace f j) ∨
        tetEdge e = (tetFace f j, tetFace f i))} =
      {(tetEdgeFaces e).1, (tetEdgeFaces e).2} := by
    intro e
    ext f
    fin_cases e <;> fin_cases f <;> decide
  have hne : ∀ e : Fin 6, (tetEdgeFaces e).1 ≠ (tetEdgeFaces e).2 := by decide
  rw [hset e]
  exact Set.ncard_pair (hne e)

/-- The three faces containing each tetrahedron vertex. -/
private def tetVertFaces : Fin 4 → Fin 4 × Fin 4 × Fin 4 :=
  ![(1, 2, 3), (0, 2, 3), (0, 1, 3), (0, 1, 2)]

/-- Each tetrahedron vertex lies in exactly three faces. -/
private lemma tet_vert_face_count (v : Fin 4) :
    Set.ncard {f : Fin 4 | ∃ i : Fin 3, tetFace f i = v} = 3 := by
  have hset : ∀ v : Fin 4, {f : Fin 4 | ∃ i : Fin 3, tetFace f i = v} =
      {(tetVertFaces v).1, (tetVertFaces v).2.1, (tetVertFaces v).2.2} := by
    intro v
    ext f
    fin_cases v <;> fin_cases f <;> decide
  have hne : ∀ v : Fin 4, (tetVertFaces v).1 ≠ (tetVertFaces v).2.1 ∧
      (tetVertFaces v).1 ≠ (tetVertFaces v).2.2 ∧
      (tetVertFaces v).2.1 ≠ (tetVertFaces v).2.2 := by decide
  rw [hset v]
  obtain ⟨h1, h2, h3⟩ := hne v
  have hmem : (tetVertFaces v).1 ∉
      ({(tetVertFaces v).2.1, (tetVertFaces v).2.2} : Set (Fin 4)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1, h2⟩
  have hfin : ({(tetVertFaces v).2.1, (tetVertFaces v).2.2} : Set (Fin 4)).Finite :=
    Set.Finite.insert _ (Set.finite_singleton _)
  rw [Set.ncard_insert_of_notMem hmem hfin, Set.ncard_pair h3]

/-- Tetrahedron faces are duplicate-free. -/
private lemma tet_face_dup (f₁ f₂ : Fin 4)
    (h : Set.range (tetFace f₁) = Set.range (tetFace f₂)) : f₁ = f₂ := by
  have c1 : ∀ f : Fin 4, Set.range (tetFace f) =
      ↑(Finset.univ.image (tetFace f)) := by
    intro f
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [c1 f₁, c1 f₂] at h
  have hfin : Finset.univ.image (tetFace f₁) =
      Finset.univ.image (tetFace f₂) := Finset.coe_injective h
  have hne : ∀ a b : Fin 4, a ≠ b →
      Finset.univ.image (tetFace a) ≠ Finset.univ.image (tetFace b) := by decide
  by_cases heq : f₁ = f₂
  · exact heq
  · exact False.elim (hne f₁ f₂ heq hfin)

/-- Tetrahedron vertices are in convex position. -/
private lemma tet_convex_pos (v : Fin 4) :
    tetVert v ∉ convexHull ℝ (tetVert '' {u : Fin 4 | u ≠ v}) := by
  apply not_mem_convexHull_of_separation (n := tetVert v) (c := -1)
  · intro s hs
    obtain ⟨u, hu, rfl⟩ := hs
    simp only [Set.mem_ofPred_eq] at hu
    fin_cases v <;> fin_cases u
    all_goals try (exact False.elim (hu rfl))
    all_goals
      simp only [tetVert, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two,
        Matrix.cons_val_three]
    all_goals norm_num
  · fin_cases v
    all_goals
      simp only [tetVert, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two,
        Matrix.cons_val_three]
    all_goals norm_num

/-- Tetrahedron face vertices are in convex position within each face. -/
private lemma tet_face_convex_pos (f : Fin 4) (k : Fin 3) :
    tetVert (tetFace f k) ∉ convexHull ℝ
      (tetVert '' (Set.range (tetFace f) \ {tetFace f k})) := by
  apply not_mem_convexHull_of_separation (n := tetFaceSepN f k) (c := -1)
  · intro s hs
    obtain ⟨a, ⟨hrange, hne⟩, rfl⟩ := hs
    obtain ⟨i, rfl⟩ := hrange
    simp only [Set.mem_singleton_iff] at hne
    fin_cases f <;> fin_cases k <;> fin_cases i
    all_goals try (norm_num at hne)
    all_goals
      simp only [tetVert, tetFace, tetFaceSepN, PiLp.inner_apply, Real.inner_apply,
        Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val_two, Matrix.cons_val_three]
    all_goals norm_num
  · fin_cases f <;> fin_cases k
    all_goals
      simp only [tetVert, tetFace, tetFaceSepN, PiLp.inner_apply, Real.inner_apply,
        Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val_two, Matrix.cons_val_three]
    all_goals norm_num

/-- Supporting-plane upper bounds for tetrahedron faces. -/
private lemma tet_supp_le (f : Fin 4) (v : Fin 4) :
    inner (𝕜 := ℝ) (tetSuppN f) (tetVert v) ≤ (1 : ℝ) := by
  fin_cases f <;> fin_cases v
  all_goals
    simp only [tetVert, tetSuppN, PiLp.inner_apply, Real.inner_apply,
      Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_two, Matrix.cons_val_three]
  all_goals norm_num

/-- Supporting-plane equalities on tetrahedron face vertices. -/
private lemma tet_supp_eq (f : Fin 4) (i : Fin 3) :
    inner (𝕜 := ℝ) (tetSuppN f) (tetVert (tetFace f i)) = (1 : ℝ) := by
  fin_cases f <;> fin_cases i
  all_goals
    simp only [tetVert, tetFace, tetSuppN, PiLp.inner_apply, Real.inner_apply,
      Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_two, Matrix.cons_val_three]
  all_goals norm_num

/-- Tetrahedron supporting normals are nonzero. -/
private lemma tet_supp_ne (f : Fin 4) : tetSuppN f ≠ 0 := by
  fin_cases f
  all_goals
    (intro hcon
     have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x 0) hcon
     simp only [tetSuppN, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
       Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
       Matrix.cons_val_two, Matrix.cons_val_three] at h0
     norm_num at h0)

/-- Each tetrahedron vertex lies in its assigned face. -/
private lemma tet_vert_mem_face :
    ∀ v : Fin 4, tetFace (tetVertFace v) (tetVertFaceIdx v) = v := by decide

/-- Supporting planes exist for tetrahedron faces. -/
private lemma tet_supp_exists (f : Fin 4) :
    ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
      n ≠ 0 ∧ (∀ x ∈ convexHull ℝ (Set.range tetVert), inner (𝕜 := ℝ) n x ≤ c) ∧
        (∀ i : Fin 3, inner (𝕜 := ℝ) n (tetVert (tetFace f i)) = c) := by
  refine ⟨tetSuppN f, 1, tet_supp_ne f, ?_, fun i => tet_supp_eq f i⟩
  intro x hx
  apply inner_le_of_mem_convexHull _ hx
  intro s hs
  obtain ⟨v, rfl⟩ := hs
  exact tet_supp_le f v

/-- Tetrahedron vertices lie in the frontier. -/
private lemma tet_vert_frontier (v : Fin 4) :
    tetVert v ∈ frontier (convexHull ℝ (Set.range tetVert)) := by
  have hmem : tetVert v ∈ convexHull ℝ (Set.range tetVert) :=
    subset_convexHull ℝ _ (Set.mem_range_self v)
  have hle : ∀ x ∈ convexHull ℝ (Set.range tetVert),
      inner (𝕜 := ℝ) (tetSuppN (tetVertFace v)) x ≤ 1 := by
    intro x hx
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact tet_supp_le _ u
  have heq : inner (𝕜 := ℝ) (tetSuppN (tetVertFace v)) (tetVert v) = 1 := by
    have h := tet_supp_eq (tetVertFace v) (tetVertFaceIdx v)
    rw [tet_vert_mem_face v] at h
    exact h
  exact mem_frontier_of_support hmem hle heq (tet_supp_ne _)

/-- Tetrahedron edge hulls lie in the frontier. -/
private lemma tet_edge_frontier (e : Fin 6) :
    convexHull ℝ {tetVert (tetEdge e).1, tetVert (tetEdge e).2} ⊆
      frontier (convexHull ℝ (Set.range tetVert)) := by
  obtain ⟨f, i, j, _, heq⟩ := tet_edge_face_exists e
  have hsub : ({tetVert (tetEdge e).1, tetVert (tetEdge e).2} :
      Set (EuclideanSpace ℝ (Fin 3))) ⊆ Set.range tetVert := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    cases hz with
    | inl h => rw [h]; exact Set.mem_range_self _
    | inr h => rw [h]; exact Set.mem_range_self _
  have hle : ∀ x ∈ convexHull ℝ (Set.range tetVert),
      inner (𝕜 := ℝ) (tetSuppN f) x ≤ 1 := by
    intro x hx
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact tet_supp_le f u
  have ha : inner (𝕜 := ℝ) (tetSuppN f) (tetVert (tetEdge e).1) = 1 := by
    cases heq with
    | inl h =>
      have h1 : (tetEdge e).1 = tetFace f i := congrArg Prod.fst h
      rw [h1]
      exact tet_supp_eq f i
    | inr h =>
      have h1 : (tetEdge e).1 = tetFace f j := congrArg Prod.fst h
      rw [h1]
      exact tet_supp_eq f j
  have hb : inner (𝕜 := ℝ) (tetSuppN f) (tetVert (tetEdge e).2) = 1 := by
    cases heq with
    | inl h =>
      have h2 : (tetEdge e).2 = tetFace f j := congrArg Prod.snd h
      rw [h2]
      exact tet_supp_eq f j
    | inr h =>
      have h2 : (tetEdge e).2 = tetFace f i := congrArg Prod.snd h
      rw [h2]
      exact tet_supp_eq f i
  intro y hy
  have hyB : y ∈ convexHull ℝ (Set.range tetVert) := convexHull_mono hsub hy
  have heq_y : inner (𝕜 := ℝ) (tetSuppN f) y = 1 := by
    apply inner_eq_of_mem_convexHull _ hy
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    cases hs with
    | inl h => rw [h]; exact ha
    | inr h => rw [h]; exact hb
  exact mem_frontier_of_support hyB hle heq_y (tet_supp_ne f)

/-- Tetrahedron face hulls lie in the frontier. -/
private lemma tet_face_frontier (f : Fin 4) :
    convexHull ℝ (tetVert '' Set.range (tetFace f)) ⊆
      frontier (convexHull ℝ (Set.range tetVert)) := by
  have hsub : tetVert '' Set.range (tetFace f) ⊆ Set.range tetVert := by
    rintro z ⟨x, ⟨i, rfl⟩, rfl⟩
    exact Set.mem_range_self _
  have hle : ∀ x ∈ convexHull ℝ (Set.range tetVert),
      inner (𝕜 := ℝ) (tetSuppN f) x ≤ 1 := by
    intro x hx
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact tet_supp_le f u
  intro y hy
  have hyB : y ∈ convexHull ℝ (Set.range tetVert) := convexHull_mono hsub hy
  have heq_y : inner (𝕜 := ℝ) (tetSuppN f) y = 1 := by
    apply inner_eq_of_mem_convexHull _ hy
    intro s hs
    obtain ⟨x, ⟨i, rfl⟩, rfl⟩ := hs
    exact tet_supp_eq f i
  exact mem_frontier_of_support hyB hle heq_y (tet_supp_ne f)

/-- Tetrahedron halfspaces (H-representation). -/
private def tetHalf (f : Fin 4) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | inner (𝕜 := ℝ) (tetSuppN f) x ≤ 1}

/-- Tetrahedron barycentric weights from coordinates. -/
private noncomputable def tetW (x : EuclideanSpace ℝ (Fin 3)) : Fin 4 → ℝ :=
  ![(x 0 + x 1 + x 2 + 1) / 4, (x 0 - x 1 - x 2 + 1) / 4,
    (-x 0 + x 1 - x 2 + 1) / 4, (-x 0 - x 1 + x 2 + 1) / 4]

/-- Barycentric weights are nonnegative on the H-representation. -/
private lemma tet_bary_nonneg (x : EuclideanSpace ℝ (Fin 3))
    (h : ∀ f : Fin 4, x ∈ tetHalf f) (v : Fin 4) : 0 ≤ tetW x v := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [tetHalf, tetSuppN, Set.mem_ofPred_eq, PiLp.inner_apply, Real.inner_apply,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three] at h0 h1 h2 h3
  fin_cases v
  all_goals
    simp only [tetW, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_two, Matrix.cons_val_three]
  all_goals linarith

/-- Barycentric weights sum to one. -/
private lemma tet_bary_sum (x : EuclideanSpace ℝ (Fin 3)) : ∑ v, tetW x v = 1 := by
  rw [Fin.sum_univ_four]
  simp only [tetW, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three]
  ring

/-- Barycentric combination recovers the point. -/
private lemma tet_bary_center (x : EuclideanSpace ℝ (Fin 3)) :
    ∑ v, tetW x v • tetVert v = x := by
  ext k
  fin_cases k
  all_goals
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.sum_univ_four,
      tetW, tetVert, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_two, Matrix.cons_val_three]
  all_goals ring

/-- The H-representation is contained in the convex hull. -/
private lemma tet_inter_subset_hull :
    (⋂ f, tetHalf f) ⊆ convexHull ℝ (Set.range tetVert) := by
  intro x hx
  simp only [Set.mem_iInter] at hx
  apply mem_convexHull_of_exists_fintype (tetW x) tetVert
      (tet_bary_nonneg x hx) (tet_bary_sum x)
  · intro v
    exact Set.mem_range_self v
  · exact tet_bary_center x

/-- The convex hull equals the H-representation intersection. -/
private lemma tet_hull_eq_inter :
    convexHull ℝ (Set.range tetVert) = ⋂ f, tetHalf f := by
  apply le_antisymm
  · intro x hx
    simp only [Set.mem_iInter]
    intro f
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨v, rfl⟩ := hs
    exact tet_supp_le f v
  · exact tet_inter_subset_hull

/-- A halfspace point outside the interior achieves equality. -/
private lemma tet_half_eq_of_mem_of_not_mem_interior (f : Fin 4)
    (x : EuclideanSpace ℝ (Fin 3)) (hmem : x ∈ tetHalf f)
    (hnot : x ∉ interior (tetHalf f)) :
    inner (𝕜 := ℝ) (tetSuppN f) x = 1 := by
  simp only [tetHalf, Set.mem_ofPred_eq] at hmem
  by_contra hne
  have hlt : inner (𝕜 := ℝ) (tetSuppN f) x < 1 := lt_of_le_of_ne hmem hne
  have hcont : Continuous
      (fun y : EuclideanSpace ℝ (Fin 3) => inner (𝕜 := ℝ) (tetSuppN f) y) :=
    continuous_const.inner continuous_id
  have hopen : IsOpen
      {y : EuclideanSpace ℝ (Fin 3) | inner (𝕜 := ℝ) (tetSuppN f) y < 1} := by
    have hIio : IsOpen (Set.Iio (1 : ℝ)) := isOpen_Iio
    have hpre := hIio.preimage hcont
    simpa only [Set.preimage, Set.mem_Iio] using hpre
  have hsub : {y : EuclideanSpace ℝ (Fin 3) |
      inner (𝕜 := ℝ) (tetSuppN f) y < 1} ⊆ tetHalf f := by
    intro y hy
    simp only [tetHalf, Set.mem_ofPred_eq, Set.mem_ofPred_eq] at hy ⊢
    linarith
  have hmem_int : x ∈ interior (tetHalf f) :=
    (hopen.subset_interior_iff).mpr hsub hlt
  exact hnot hmem_int

/-- A point of the H-representation with face equality lies in that face hull. -/
private lemma tet_mem_face_of_eq (f : Fin 4) (x : EuclideanSpace ℝ (Fin 3))
    (hall : ∀ g : Fin 4, x ∈ tetHalf g)
    (heq : inner (𝕜 := ℝ) (tetSuppN f) x = 1) :
    x ∈ convexHull ℝ (tetVert '' Set.range (tetFace f)) := by
  fin_cases f
  · -- Face 0 omits vertex 0.
    have heq0 : inner (𝕜 := ℝ) (tetSuppN 0) x = 1 := heq
    simp only [tetSuppN, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_two] at heq0
    have hz : tetW x 0 = 0 := by
      simp only [tetW, Matrix.cons_val_zero] at ⊢
      linarith
    have hsum := tet_bary_sum x
    rw [Fin.sum_univ_four] at hsum
    have htot := tet_bary_center x
    rw [Fin.sum_univ_four] at htot
    have hz_smul : tetW x 0 • tetVert 0 = 0 := by rw [hz]; exact zero_smul _ _
    rw [hz_smul, zero_add] at htot
    apply mem_convexHull_of_exists_fintype (fun i : Fin 3 => tetW x (tetFace 0 i))
      (fun i : Fin 3 => tetVert (tetFace 0 i))
    · intro i
      exact tet_bary_nonneg x hall _
    · rw [Fin.sum_univ_three]
      simp only [tetFace, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_two]
      linarith
    · intro i
      exact Set.mem_image_of_mem _ (Set.mem_range_self i)
    · rw [Fin.sum_univ_three]
      simp only [tetFace, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_two]
      exact htot
  · -- Face 1 omits vertex 1.
    have heq1 : inner (𝕜 := ℝ) (tetSuppN 1) x = 1 := heq
    simp only [tetSuppN, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_two] at heq1
    have hz : tetW x 1 = 0 := by
      simp only [tetW, Matrix.cons_val_zero, Matrix.cons_val_one] at ⊢
      linarith
    have hsum := tet_bary_sum x
    rw [Fin.sum_univ_four] at hsum
    have htot := tet_bary_center x
    rw [Fin.sum_univ_four] at htot
    have hz_smul : tetW x 1 • tetVert 1 = 0 := by rw [hz]; exact zero_smul _ _
    rw [hz_smul, add_zero] at htot
    apply mem_convexHull_of_exists_fintype (fun i : Fin 3 => tetW x (tetFace 1 i))
      (fun i : Fin 3 => tetVert (tetFace 1 i))
    · intro i
      exact tet_bary_nonneg x hall _
    · rw [Fin.sum_univ_three]
      simp only [tetFace, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_two]
      linarith
    · intro i
      exact Set.mem_image_of_mem _ (Set.mem_range_self i)
    · rw [Fin.sum_univ_three]
      simp only [tetFace, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_two]
      exact htot
  · -- Face 2 omits vertex 2.
    have heq2 : inner (𝕜 := ℝ) (tetSuppN 2) x = 1 := heq
    simp only [tetSuppN, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_two] at heq2
    have hz : tetW x 2 = 0 := by
      simp only [tetW, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val_two] at ⊢
      linarith
    have hsum := tet_bary_sum x
    rw [Fin.sum_univ_four] at hsum
    have htot := tet_bary_center x
    rw [Fin.sum_univ_four] at htot
    have hz_smul : tetW x 2 • tetVert 2 = 0 := by rw [hz]; exact zero_smul _ _
    rw [hz_smul, add_zero] at htot
    apply mem_convexHull_of_exists_fintype (fun i : Fin 3 => tetW x (tetFace 2 i))
      (fun i : Fin 3 => tetVert (tetFace 2 i))
    · intro i
      exact tet_bary_nonneg x hall _
    · rw [Fin.sum_univ_three]
      simp only [tetFace, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_two]
      linarith
    · intro i
      exact Set.mem_image_of_mem _ (Set.mem_range_self i)
    · rw [Fin.sum_univ_three]
      simp only [tetFace, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_two]
      exact htot
  · -- Face 3 omits vertex 3.
    have heq3 : inner (𝕜 := ℝ) (tetSuppN 3) x = 1 := heq
    simp only [tetSuppN, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_two, Matrix.cons_val_three] at heq3
    have hz : tetW x 3 = 0 := by
      simp only [tetW, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_three] at ⊢
      linarith
    have hsum := tet_bary_sum x
    rw [Fin.sum_univ_four] at hsum
    have htot := tet_bary_center x
    rw [Fin.sum_univ_four] at htot
    have hz_smul : tetW x 3 • tetVert 3 = 0 := by rw [hz]; exact zero_smul _ _
    rw [hz_smul, add_zero] at htot
    apply mem_convexHull_of_exists_fintype (fun i : Fin 3 => tetW x (tetFace 3 i))
      (fun i : Fin 3 => tetVert (tetFace 3 i))
    · intro i
      exact tet_bary_nonneg x hall _
    · rw [Fin.sum_univ_three]
      simp only [tetFace, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three]
      linarith
    · intro i
      exact Set.mem_image_of_mem _ (Set.mem_range_self i)
    · rw [Fin.sum_univ_three]
      simp only [tetFace, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three]
      exact htot

/-- Tetrahedron frontier is covered by faces. -/
private lemma tet_cover (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ frontier (convexHull ℝ (Set.range tetVert))) :
    ∃ f : Fin 4, x ∈ convexHull ℝ (tetVert '' Set.range (tetFace f)) := by
  classical
  have hclosed : IsClosed (convexHull ℝ (Set.range tetVert)) :=
    (Set.finite_range tetVert).isClosed_convexHull ℝ
  have hmem : x ∈ convexHull ℝ (Set.range tetVert) := hclosed.frontier_subset hx
  have hnot : x ∉ interior (convexHull ℝ (Set.range tetVert)) := by
    have h := (mem_frontier_iff_notMem_interior hmem).mp hx
    exact h
  rw [tet_hull_eq_inter] at hmem hnot
  simp only [interior_iInter_of_finite, Set.mem_iInter] at hmem hnot
  have hex : ∃ f : Fin 4, x ∉ interior (tetHalf f) := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hnot hcon
  obtain ⟨f, hf⟩ := hex
  have heq := tet_half_eq_of_mem_of_not_mem_interior f x (hmem f) hf
  exact ⟨f, tet_mem_face_of_eq f x hmem heq⟩

/-- Tetrahedron realization exists. -/
private theorem tet_exists :
    ∃ (w : Fin 4 → EuclideanSpace ℝ (Fin 3)) (ee : Fin 6 → Fin 4 × Fin 4)
      (fv : Fin 4 → Fin 3 → Fin 4) (b : Set (EuclideanSpace ℝ (Fin 3)))
      (ll dd : ℝ),
      0 < ll ∧ 0 < dd ∧
      b = convexHull ℝ (Set.range w) ∧
      Convex ℝ b ∧
      (∀ v : Fin 4, w v ∈ frontier b) ∧
      (∀ v : Fin 4, w v ∉ convexHull ℝ (w '' {u : Fin 4 | u ≠ v})) ∧
      (Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 4, d = w i - w j}) = 3) ∧
      (∀ e : Fin 6, dist (w (ee e).1) (w (ee e).2) = ll) ∧
      (∀ (f : Fin 4) (i j : Fin 3), j.val = (i.val + 1) % 3 →
        dist (w (fv f i)) (w (fv f j)) = ll) ∧
      (∀ (f : Fin 4) (h i j : Fin 3), h.val = (i.val + 3 - 1) % 3 →
        j.val = (i.val + 1) % 3 → dist (w (fv f h)) (w (fv f j)) = dd) ∧
      (∀ f : Fin 4, Function.Injective (fv f)) ∧
      (∀ (f : Fin 4) (k : Fin 3), w (fv f k) ∉ convexHull ℝ
        (w '' (Set.range (fv f) \ {fv f k}))) ∧
      (∀ (f : Fin 4) (i₁ j₁ i₂ j₂ : Fin 3),
        j₁.val = (i₁.val + 1) % 3 →
        j₂.val = (i₂.val + 1) % 3 →
        i₁ ≠ i₂ → i₁ ≠ j₂ → j₁ ≠ i₂ → j₁ ≠ j₂ →
        Disjoint (convexHull ℝ {w (fv f i₁), w (fv f j₁)})
          (convexHull ℝ {w (fv f i₂), w (fv f j₂)})) ∧
      (∀ (f : Fin 4) (i j : Fin 3), j.val = (i.val + 1) % 3 →
        ∃ e : Fin 6, ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i)) ∧
      (∀ e : Fin 6, ∃ f : Fin 4, ∃ i j : Fin 3,
        j.val = (i.val + 1) % 3 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))) ∧
      (∀ e : Fin 6, Set.ncard {f : Fin 4 | ∃ i j : Fin 3,
        j.val = (i.val + 1) % 3 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))} = 2) ∧
      (∀ f : Fin 4, Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 3, d = w (fv f i) - w (fv f j)}) ≤ 2) ∧
      (∀ f : Fin 4, ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
        n ≠ 0 ∧ (∀ x ∈ b, inner (𝕜 := ℝ) n x ≤ c) ∧
        (∀ i : Fin 3, inner (𝕜 := ℝ) n (w (fv f i)) = c)) ∧
      (∀ e₁ e₂ : Fin 6, (ee e₁ = ee e₂ ∨ ee e₁ = (ee e₂).swap) → e₁ = e₂) ∧
      (∀ f₁ f₂ : Fin 4, Set.range (fv f₁) = Set.range (fv f₂) → f₁ = f₂) ∧
      (∀ e : Fin 6, convexHull ℝ {w (ee e).1, w (ee e).2} ⊆ frontier b) ∧
      (∀ f : Fin 4, convexHull ℝ (w '' Set.range (fv f)) ⊆ frontier b) ∧
      (∀ x ∈ frontier b, ∃ f : Fin 4,
        x ∈ convexHull ℝ (w '' Set.range (fv f))) ∧
      (∀ v : Fin 4, Set.ncard {f : Fin 4 | ∃ i : Fin 3, fv f i = v} = 3) ∧
      2 * 6 = 3 * 4 ∧ 2 * 6 = 3 * 4 ∧ (4 : ℤ) - (6 : ℤ) + (4 : ℤ) = 2 := by
  refine ⟨tetVert, tetEdge, tetFace, convexHull ℝ (Set.range tetVert),
    2 * Real.sqrt 2, 2 * Real.sqrt 2, ?_, ?_, rfl, convex_convexHull ℝ _,
    tet_vert_frontier, tet_convex_pos, tet_finrank, tet_edge_length,
    tet_face_edge, tet_face_diag, tet_face_inj, tet_face_convex_pos, ?_,
    tet_face_edge_exists, tet_edge_face_exists, tet_two_face, ?_,
    tet_supp_exists, tet_edge_dup, tet_face_dup, tet_edge_frontier,
    tet_face_frontier, tet_cover, tet_vert_face_count, rfl, rfl, rfl⟩
  · positivity
  · positivity
  · intro f i₁ j₁ i₂ j₂ h1 h2 d1 d2 d3 d4
    exact False.elim (tet_disjoint_neg i₁ j₁ i₂ j₂ ⟨h1, h2, d1, d2, d3, d4⟩)
  · intro f
    exact finrank_triangle_le (fun i => tetVert (tetFace f i))

end Tetrahedron

section Cube

/-- Cube vertices (all `±1` corners). -/
private def cubeVert : Fin 8 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 1, 1], !₂[1, 1, -1], !₂[1, -1, 1], !₂[1, -1, -1],
    !₂[(-1 : ℝ), 1, 1], !₂[-1, 1, -1], !₂[-1, -1, 1], !₂[-1, -1, -1]]

/-- Cube edge endpoints (pairs differing in one coordinate). -/
private def cubeEdge : Fin 12 → Fin 8 × Fin 8 :=
  ![(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3),
    (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7)]

/-- Cube faces as cyclic vertex lists. -/
private def cubeFace : Fin 6 → Fin 4 → Fin 8 :=
  ![![0, 1, 3, 2], ![4, 5, 7, 6], ![0, 1, 5, 4],
    ![2, 3, 7, 6], ![0, 2, 6, 4], ![1, 3, 7, 5]]

/-- Face-local separating normals (in-plane diagonals). -/
private def cubeFaceSepN : Fin 6 → Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  ![![!₂[(0 : ℝ), 1, 1], !₂[0, 1, -1], !₂[0, -1, -1], !₂[0, -1, 1]],
    ![!₂[(0 : ℝ), 1, 1], !₂[0, 1, -1], !₂[0, -1, -1], !₂[0, -1, 1]],
    ![!₂[(1 : ℝ), 0, 1], !₂[1, 0, -1], !₂[-1, 0, -1], !₂[-1, 0, 1]],
    ![!₂[(1 : ℝ), 0, 1], !₂[1, 0, -1], !₂[-1, 0, -1], !₂[-1, 0, 1]],
    ![!₂[(1 : ℝ), 1, 0], !₂[1, -1, 0], !₂[-1, -1, 0], !₂[-1, 1, 0]],
    ![!₂[(1 : ℝ), 1, 0], !₂[1, -1, 0], !₂[-1, -1, 0], !₂[-1, 1, 0]]]

/-- Supporting-plane normals (coordinate directions). -/
private def cubeSuppN : Fin 6 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 0, 0], !₂[-1, 0, 0], !₂[0, 1, 0],
    !₂[(0 : ℝ), -1, 0], !₂[0, 0, 1], !₂[0, 0, -1]]

/-- For each vertex, a face containing it. -/
private def cubeVertFace : Fin 8 → Fin 6 := ![0, 0, 0, 0, 1, 1, 1, 1]

/-- Index witnessing the vertex-face membership above. -/
private def cubeVertFaceIdx : Fin 8 → Fin 4 := ![0, 1, 3, 2, 0, 1, 3, 2]

/-- The two faces containing each cube edge. -/
private def cubeEdgeFaces : Fin 12 → Fin 6 × Fin 6 :=
  ![(0, 2), (0, 4), (2, 4), (0, 5), (2, 5), (0, 3),
    (3, 4), (3, 5), (1, 2), (1, 4), (1, 5), (1, 3)]

/-- The three faces containing each cube vertex. -/
private def cubeVertFaces : Fin 8 → Fin 6 × Fin 6 × Fin 6 :=
  ![(0, 2, 4), (0, 2, 5), (0, 3, 4), (0, 3, 5),
    (1, 2, 4), (1, 2, 5), (1, 3, 4), (1, 3, 5)]

private lemma cube_sqrt4 : Real.sqrt 4 = 2 := by
  have h : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h, Real.sqrt_sq (by norm_num)]

/-- Cube edge lengths. -/
private lemma cube_edge_length (e : Fin 12) :
    dist (cubeVert (cubeEdge e).1) (cubeVert (cubeEdge e).2) = 2 := by
  fin_cases e
  all_goals
    simp only [cubeVert, cubeEdge, EuclideanSpace.dist_eq, Fin.sum_univ_three,
      Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val,
      dist_self, tet_dist_aux]
  all_goals norm_num
  all_goals exact cube_sqrt4

/-- Cube face edges. -/
private lemma cube_face_edge (f : Fin 6) (i j : Fin 4) (h : j.val = (i.val + 1) % 4) :
    dist (cubeVert (cubeFace f i)) (cubeVert (cubeFace f j)) = 2 := by
  fin_cases f <;> fin_cases i <;> fin_cases j
  all_goals try (norm_num at h)
  all_goals
    simp only [cubeVert, cubeFace, EuclideanSpace.dist_eq, Fin.sum_univ_three,
      Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val,
      dist_self, tet_dist_aux, tet_dist_aux2]
  all_goals norm_num
  all_goals exact cube_sqrt4

/-- Cube face diagonals. -/
private lemma cube_face_diag (f : Fin 6) (h0 i j : Fin 4)
    (h1 : h0.val = (i.val + 4 - 1) % 4) (h2 : j.val = (i.val + 1) % 4) :
    dist (cubeVert (cubeFace f h0)) (cubeVert (cubeFace f j)) = 2 * Real.sqrt 2 := by
  rw [← sqrt8]
  fin_cases f <;> fin_cases h0 <;> fin_cases i <;> fin_cases j
  all_goals try (norm_num at h1)
  all_goals try (norm_num at h2)
  all_goals
    simp only [cubeVert, cubeFace, EuclideanSpace.dist_eq, Fin.sum_univ_three,
      Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val,
      dist_self, tet_dist_aux, tet_dist_aux2]
  all_goals norm_num

/-- Cube faces are injective. -/
private lemma cube_face_inj (f : Fin 6) : Function.Injective (cubeFace f) := by
  fin_cases f <;> decide

/-- Every cube face edge is a graph edge. -/
private lemma cube_face_edge_exists (f : Fin 6) (i j : Fin 4)
    (h : j.val = (i.val + 1) % 4) :
    ∃ e : Fin 12, cubeEdge e = (cubeFace f i, cubeFace f j) ∨
      cubeEdge e = (cubeFace f j, cubeFace f i) := by
  fin_cases f <;> fin_cases i <;> fin_cases j
  all_goals try (norm_num at h)
  all_goals decide

/-- Every cube graph edge is a face edge. -/
private lemma cube_edge_face_exists (e : Fin 12) :
    ∃ f : Fin 6, ∃ i j : Fin 4, j.val = (i.val + 1) % 4 ∧
      (cubeEdge e = (cubeFace f i, cubeFace f j) ∨
        cubeEdge e = (cubeFace f j, cubeFace f i)) := by
  fin_cases e <;> decide

/-- Cube edges are duplicate-free. -/
private lemma cube_edge_dup (e₁ e₂ : Fin 12)
    (h : cubeEdge e₁ = cubeEdge e₂ ∨ cubeEdge e₁ = (cubeEdge e₂).swap) :
    e₁ = e₂ := by
  revert h
  fin_cases e₁ <;> fin_cases e₂ <;> decide

/-- Each cube edge lies in exactly two faces. -/
private lemma cube_two_face (e : Fin 12) :
    Set.ncard {f : Fin 6 | ∃ i j : Fin 4, j.val = (i.val + 1) % 4 ∧
      (cubeEdge e = (cubeFace f i, cubeFace f j) ∨
        cubeEdge e = (cubeFace f j, cubeFace f i))} = 2 := by
  have hset : ∀ e : Fin 12, {f : Fin 6 | ∃ i j : Fin 4, j.val = (i.val + 1) % 4 ∧
      (cubeEdge e = (cubeFace f i, cubeFace f j) ∨
        cubeEdge e = (cubeFace f j, cubeFace f i))} =
      {(cubeEdgeFaces e).1, (cubeEdgeFaces e).2} := by
    intro e
    ext f
    fin_cases e <;> fin_cases f <;> decide
  have hne : ∀ e : Fin 12, (cubeEdgeFaces e).1 ≠ (cubeEdgeFaces e).2 := by decide
  rw [hset e]
  exact Set.ncard_pair (hne e)

/-- Each cube vertex lies in exactly three faces. -/
private lemma cube_vert_face_count (v : Fin 8) :
    Set.ncard {f : Fin 6 | ∃ i : Fin 4, cubeFace f i = v} = 3 := by
  have hset : ∀ v : Fin 8, {f : Fin 6 | ∃ i : Fin 4, cubeFace f i = v} =
      {(cubeVertFaces v).1, (cubeVertFaces v).2.1, (cubeVertFaces v).2.2} := by
    intro v
    ext f
    fin_cases v <;> fin_cases f <;> decide
  have hne : ∀ v : Fin 8, (cubeVertFaces v).1 ≠ (cubeVertFaces v).2.1 ∧
      (cubeVertFaces v).1 ≠ (cubeVertFaces v).2.2 ∧
      (cubeVertFaces v).2.1 ≠ (cubeVertFaces v).2.2 := by decide
  rw [hset v]
  obtain ⟨h1, h2, h3⟩ := hne v
  have hmem : (cubeVertFaces v).1 ∉
      ({(cubeVertFaces v).2.1, (cubeVertFaces v).2.2} : Set (Fin 6)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1, h2⟩
  have hfin : ({(cubeVertFaces v).2.1, (cubeVertFaces v).2.2} : Set (Fin 6)).Finite :=
    Set.Finite.insert _ (Set.finite_singleton _)
  rw [Set.ncard_insert_of_notMem hmem hfin, Set.ncard_pair h3]

/-- Cube faces are duplicate-free. -/
private lemma cube_face_dup (f₁ f₂ : Fin 6)
    (h : Set.range (cubeFace f₁) = Set.range (cubeFace f₂)) : f₁ = f₂ := by
  have c1 : ∀ f : Fin 6, Set.range (cubeFace f) =
      ↑(Finset.univ.image (cubeFace f)) := by
    intro f
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [c1 f₁, c1 f₂] at h
  have hfin : Finset.univ.image (cubeFace f₁) =
      Finset.univ.image (cubeFace f₂) := Finset.coe_injective h
  have hne : ∀ a b : Fin 6, a ≠ b →
      Finset.univ.image (cubeFace a) ≠ Finset.univ.image (cubeFace b) := by decide
  by_cases heq : f₁ = f₂
  · exact heq
  · exact False.elim (hne f₁ f₂ heq hfin)

/-- Each cube vertex lies in its assigned face. -/
private lemma cube_vert_mem_face :
    ∀ v : Fin 8, cubeFace (cubeVertFace v) (cubeVertFaceIdx v) = v := by decide

/-- Cube vertices are in convex position. -/
private lemma cube_convex_pos (v : Fin 8) :
    cubeVert v ∉ convexHull ℝ (cubeVert '' {u : Fin 8 | u ≠ v}) := by
  apply not_mem_convexHull_of_separation (n := cubeVert v) (c := 1)
  · intro s hs
    obtain ⟨u, hu, rfl⟩ := hs
    simp only [Set.mem_ofPred_eq] at hu
    fin_cases v <;> fin_cases u
    all_goals try (exact False.elim (hu rfl))
    all_goals
      simp only [cubeVert, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val]
    all_goals norm_num
  · fin_cases v
    all_goals
      simp only [cubeVert, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val]
    all_goals norm_num

/-- Cube face vertices are in convex position within each face. -/
private lemma cube_face_convex_pos (f : Fin 6) (k : Fin 4) :
    cubeVert (cubeFace f k) ∉ convexHull ℝ
      (cubeVert '' (Set.range (cubeFace f) \ {cubeFace f k})) := by
  apply not_mem_convexHull_of_separation (n := cubeFaceSepN f k) (c := 0)
  · intro s hs
    obtain ⟨a, ⟨hrange, hne⟩, rfl⟩ := hs
    obtain ⟨i, rfl⟩ := hrange
    simp only [Set.mem_singleton_iff] at hne
    fin_cases f <;> fin_cases k <;> fin_cases i
    all_goals try (norm_num at hne)
    all_goals
      simp only [cubeVert, cubeFace, cubeFaceSepN, PiLp.inner_apply, Real.inner_apply,
        Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
        Matrix.cons_val]
    all_goals norm_num
  · fin_cases f <;> fin_cases k
    all_goals
      simp only [cubeVert, cubeFace, cubeFaceSepN, PiLp.inner_apply, Real.inner_apply,
        Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
        Matrix.cons_val]
    all_goals norm_num

/-- Supporting-plane upper bounds for cube faces. -/
private lemma cube_supp_le (f : Fin 6) (v : Fin 8) :
    inner (𝕜 := ℝ) (cubeSuppN f) (cubeVert v) ≤ (1 : ℝ) := by
  fin_cases f <;> fin_cases v
  all_goals
    simp only [cubeVert, cubeSuppN, PiLp.inner_apply, Real.inner_apply,
      Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val]
  all_goals norm_num

/-- Supporting-plane equalities on cube face vertices. -/
private lemma cube_supp_eq (f : Fin 6) (i : Fin 4) :
    inner (𝕜 := ℝ) (cubeSuppN f) (cubeVert (cubeFace f i)) = (1 : ℝ) := by
  fin_cases f <;> fin_cases i
  all_goals
    simp only [cubeVert, cubeFace, cubeSuppN, PiLp.inner_apply, Real.inner_apply,
      Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val]
  all_goals norm_num

/-- Cube supporting normals are nonzero. -/
private lemma cube_supp_ne (f : Fin 6) : cubeSuppN f ≠ 0 := by
  have h1 : ∀ g : Fin 6, inner (𝕜 := ℝ) (cubeSuppN g) (cubeSuppN g) = 1 := by
    intro g
    fin_cases g
    all_goals
      simp only [cubeSuppN, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val]
    all_goals norm_num
  intro hcon
  have h := h1 f
  rw [hcon] at h
  simp only [inner_zero_left] at h
  norm_num at h

/-- Three vertex differences spanning the cube. -/
private def cubeD : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![cubeVert 1 - cubeVert 0, cubeVert 2 - cubeVert 0, cubeVert 4 - cubeVert 0]

private lemma cube_gram_det : (Matrix.gram ℝ cubeD).det = 64 := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.gram_apply, cubeD, cubeVert, PiLp.inner_apply,
    Real.inner_apply, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val]
  norm_num

private lemma cubeD_indep : LinearIndependent ℝ cubeD := by
  rw [← Matrix.det_gram_ne_zero_iff_linearIndependent, cube_gram_det]
  norm_num

private lemma cube_span_top :
    Submodule.span ℝ (Set.range cubeD) = ⊤ :=
  LinearIndependent.span_eq_top_of_card_eq_finrank cubeD_indep
    (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])

/-- Full-dimensionality for the cube vertex set. -/
private lemma cube_finrank : Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
    ∃ i j : Fin 8, d = cubeVert i - cubeVert j}) = 3 := by
  have hle : Submodule.span ℝ (Set.range cubeD) ≤
      Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 8, d = cubeVert i - cubeVert j} := by
    apply Submodule.span_mono
    rintro x ⟨k, rfl⟩
    fin_cases k
    · exact ⟨1, 0, rfl⟩
    · exact ⟨2, 0, rfl⟩
    · exact ⟨4, 0, rfl⟩
  rw [cube_span_top] at hle
  have hSeq : Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
      ∃ i j : Fin 8, d = cubeVert i - cubeVert j} = ⊤ := top_le_iff.mp hle
  have hfin : Module.finrank ℝ ↥(⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := Submodule.topEquiv.finrank_eq
  rw [hSeq, hfin, finrank_euclideanSpace_fin]

/-- Supporting planes exist for cube faces. -/
private lemma cube_supp_exists (f : Fin 6) :
    ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
      n ≠ 0 ∧ (∀ x ∈ convexHull ℝ (Set.range cubeVert), inner (𝕜 := ℝ) n x ≤ c) ∧
        (∀ i : Fin 4, inner (𝕜 := ℝ) n (cubeVert (cubeFace f i)) = c) := by
  refine ⟨cubeSuppN f, 1, cube_supp_ne f, ?_, fun i => cube_supp_eq f i⟩
  intro x hx
  apply inner_le_of_mem_convexHull _ hx
  intro s hs
  obtain ⟨v, rfl⟩ := hs
  exact cube_supp_le f v

/-- Cube vertices lie in the frontier. -/
private lemma cube_vert_frontier (v : Fin 8) :
    cubeVert v ∈ frontier (convexHull ℝ (Set.range cubeVert)) := by
  have hmem : cubeVert v ∈ convexHull ℝ (Set.range cubeVert) :=
    subset_convexHull ℝ _ (Set.mem_range_self v)
  have hle : ∀ x ∈ convexHull ℝ (Set.range cubeVert),
      inner (𝕜 := ℝ) (cubeSuppN (cubeVertFace v)) x ≤ 1 := by
    intro x hx
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact cube_supp_le _ u
  have heq : inner (𝕜 := ℝ) (cubeSuppN (cubeVertFace v)) (cubeVert v) = 1 := by
    have h := cube_supp_eq (cubeVertFace v) (cubeVertFaceIdx v)
    rw [cube_vert_mem_face v] at h
    exact h
  exact mem_frontier_of_support hmem hle heq (cube_supp_ne _)

/-- Cube edge hulls lie in the frontier. -/
private lemma cube_edge_frontier (e : Fin 12) :
    convexHull ℝ {cubeVert (cubeEdge e).1, cubeVert (cubeEdge e).2} ⊆
      frontier (convexHull ℝ (Set.range cubeVert)) := by
  obtain ⟨f, i, j, _, heq⟩ := cube_edge_face_exists e
  have hsub : ({cubeVert (cubeEdge e).1, cubeVert (cubeEdge e).2} :
      Set (EuclideanSpace ℝ (Fin 3))) ⊆ Set.range cubeVert := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    cases hz with
    | inl h => rw [h]; exact Set.mem_range_self _
    | inr h => rw [h]; exact Set.mem_range_self _
  have hle : ∀ x ∈ convexHull ℝ (Set.range cubeVert),
      inner (𝕜 := ℝ) (cubeSuppN f) x ≤ 1 := by
    intro x hx
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact cube_supp_le f u
  have ha : inner (𝕜 := ℝ) (cubeSuppN f) (cubeVert (cubeEdge e).1) = 1 := by
    cases heq with
    | inl h =>
      have h1 : (cubeEdge e).1 = cubeFace f i := congrArg Prod.fst h
      rw [h1]
      exact cube_supp_eq f i
    | inr h =>
      have h1 : (cubeEdge e).1 = cubeFace f j := congrArg Prod.fst h
      rw [h1]
      exact cube_supp_eq f j
  have hb : inner (𝕜 := ℝ) (cubeSuppN f) (cubeVert (cubeEdge e).2) = 1 := by
    cases heq with
    | inl h =>
      have h2 : (cubeEdge e).2 = cubeFace f j := congrArg Prod.snd h
      rw [h2]
      exact cube_supp_eq f j
    | inr h =>
      have h2 : (cubeEdge e).2 = cubeFace f i := congrArg Prod.snd h
      rw [h2]
      exact cube_supp_eq f i
  intro y hy
  have hyB : y ∈ convexHull ℝ (Set.range cubeVert) := convexHull_mono hsub hy
  have heq_y : inner (𝕜 := ℝ) (cubeSuppN f) y = 1 := by
    apply inner_eq_of_mem_convexHull _ hy
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    cases hs with
    | inl h => rw [h]; exact ha
    | inr h => rw [h]; exact hb
  exact mem_frontier_of_support hyB hle heq_y (cube_supp_ne f)

/-- Cube face hulls lie in the frontier. -/
private lemma cube_face_frontier (f : Fin 6) :
    convexHull ℝ (cubeVert '' Set.range (cubeFace f)) ⊆
      frontier (convexHull ℝ (Set.range cubeVert)) := by
  have hsub : cubeVert '' Set.range (cubeFace f) ⊆ Set.range cubeVert := by
    rintro z ⟨x, ⟨i, rfl⟩, rfl⟩
    exact Set.mem_range_self _
  have hle : ∀ x ∈ convexHull ℝ (Set.range cubeVert),
      inner (𝕜 := ℝ) (cubeSuppN f) x ≤ 1 := by
    intro x hx
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact cube_supp_le f u
  intro y hy
  have hyB : y ∈ convexHull ℝ (Set.range cubeVert) := convexHull_mono hsub hy
  have heq_y : inner (𝕜 := ℝ) (cubeSuppN f) y = 1 := by
    apply inner_eq_of_mem_convexHull _ hy
    intro s hs
    obtain ⟨x, ⟨i, rfl⟩, rfl⟩ := hs
    exact cube_supp_eq f i
  exact mem_frontier_of_support hyB hle heq_y (cube_supp_ne f)

/-- Face-plane basis vectors (first). -/
private def cubeFaceB1 : Fin 6 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(0 : ℝ), 1, 0], !₂[0, 1, 0], !₂[1, 0, 0],
    !₂[(1 : ℝ), 0, 0], !₂[1, 0, 0], !₂[1, 0, 0]]

/-- Face-plane basis vectors (second). -/
private def cubeFaceB2 : Fin 6 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(0 : ℝ), 0, 1], !₂[0, 0, 1], !₂[0, 0, 1],
    !₂[(0 : ℝ), 0, 1], !₂[0, 1, 0], !₂[0, 1, 0]]

/-- Vectors with zero x-coordinate lie in the yz-plane span. -/
private lemma mem_span_yz (v : EuclideanSpace ℝ (Fin 3)) (h : v 0 = 0) :
    v ∈ Submodule.span ℝ ({!₂[(0 : ℝ), 1, 0], !₂[(0 : ℝ), 0, 1]} :
      Set (EuclideanSpace ℝ (Fin 3))) := by
  have heq : v = (v 1) • !₂[(0 : ℝ), 1, 0] + (v 2) • !₂[(0 : ℝ), 0, 1] := by
    ext k
    fin_cases k
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Fin.isValue, Fin.mk_zero, Matrix.cons_val]
      rw [h]
      ring
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Fin.isValue, Fin.mk_one, Matrix.cons_val]
      ring
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      ring
  rw [heq]
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    exact Submodule.subset_span (by simp)
  · apply Submodule.smul_mem
    exact Submodule.subset_span (by simp)

/-- Vectors with zero y-coordinate lie in the xz-plane span. -/
private lemma mem_span_xz (v : EuclideanSpace ℝ (Fin 3)) (h : v 1 = 0) :
    v ∈ Submodule.span ℝ ({!₂[(1 : ℝ), 0, 0], !₂[(0 : ℝ), 0, 1]} :
      Set (EuclideanSpace ℝ (Fin 3))) := by
  have heq : v = (v 0) • !₂[(1 : ℝ), 0, 0] + (v 2) • !₂[(0 : ℝ), 0, 1] := by
    ext k
    fin_cases k
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Fin.isValue, Fin.mk_zero, Matrix.cons_val]
      ring
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Fin.isValue, Fin.mk_one, Matrix.cons_val]
      rw [h]
      ring
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      ring
  rw [heq]
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    exact Submodule.subset_span (by simp)
  · apply Submodule.smul_mem
    exact Submodule.subset_span (by simp)

/-- Vectors with zero z-coordinate lie in the xy-plane span. -/
private lemma mem_span_xy (v : EuclideanSpace ℝ (Fin 3)) (h : v 2 = 0) :
    v ∈ Submodule.span ℝ ({!₂[(1 : ℝ), 0, 0], !₂[(0 : ℝ), 1, 0]} :
      Set (EuclideanSpace ℝ (Fin 3))) := by
  have heq : v = (v 0) • !₂[(1 : ℝ), 0, 0] + (v 1) • !₂[(0 : ℝ), 1, 0] := by
    ext k
    fin_cases k
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Fin.isValue, Fin.mk_zero, Matrix.cons_val]
      ring
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Fin.isValue, Fin.mk_one, Matrix.cons_val]
      ring
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      rw [h]
      ring
  rw [heq]
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    exact Submodule.subset_span (by simp)
  · apply Submodule.smul_mem
    exact Submodule.subset_span (by simp)

/-- Cube faces are planar (finrank at most two). -/
private lemma cube_face_planar (f : Fin 6) :
    Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
      ∃ i j : Fin 4, d = cubeVert (cubeFace f i) - cubeVert (cubeFace f j)}) ≤ 2 := by
  classical
  have hsub : Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 4, d = cubeVert (cubeFace f i) - cubeVert (cubeFace f j)} ≤
      Submodule.span ℝ ({cubeFaceB1 f, cubeFaceB2 f} :
        Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [Submodule.span_le]
    rintro d ⟨i, j, rfl⟩
    have hinner : inner (𝕜 := ℝ) (cubeSuppN f)
        (cubeVert (cubeFace f i) - cubeVert (cubeFace f j)) = 0 := by
      rw [inner_sub_right, cube_supp_eq f i, cube_supp_eq f j, sub_self]
    fin_cases f
    all_goals
      simp only [cubeSuppN, cubeFaceB1, cubeFaceB2, PiLp.inner_apply, Real.inner_apply,
        Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
        Matrix.cons_val, PiLp.sub_apply] at hinner ⊢
    all_goals
      (first
        | (refine mem_span_yz _ ?_; simp only [PiLp.sub_apply]; linarith)
        | (refine mem_span_xz _ ?_; simp only [PiLp.sub_apply]; linarith)
        | (refine mem_span_xy _ ?_; simp only [PiLp.sub_apply]; linarith))
  have hfin : Module.Finite ℝ ↥(Submodule.span ℝ ({cubeFaceB1 f, cubeFaceB2 f} :
      Set (EuclideanSpace ℝ (Fin 3)))) :=
    FiniteDimensional.span_of_finite ℝ
      (Set.Finite.insert _ (Set.finite_singleton _))
  exact (@Submodule.finrank_mono ℝ _ _ _ _ _ _ _ hfin hsub).trans
    (finrank_span_pair_le _ _)

/-- Segments in distinct parallel hyperplanes are disjoint. -/
private lemma disjoint_of_separated (p₁ q₁ p₂ q₂ n : EuclideanSpace ℝ (Fin 3))
    (h2 : inner (𝕜 := ℝ) n q₁ = inner (𝕜 := ℝ) n p₁)
    (h4 : inner (𝕜 := ℝ) n q₂ = inner (𝕜 := ℝ) n p₂)
    (hne : inner (𝕜 := ℝ) n p₁ ≠ inner (𝕜 := ℝ) n p₂) :
    Disjoint (convexHull ℝ ({p₁, q₁} : Set (EuclideanSpace ℝ (Fin 3))))
      (convexHull ℝ ({p₂, q₂} : Set (EuclideanSpace ℝ (Fin 3)))) := by
  rw [Set.disjoint_left]
  rintro x hx1 hx2
  have e1 : inner (𝕜 := ℝ) n x = inner (𝕜 := ℝ) n p₁ := by
    apply inner_eq_of_mem_convexHull _ hx1
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    cases hs with
    | inl h => rw [h]
    | inr h => rw [h]; exact h2
  have e2 : inner (𝕜 := ℝ) n x = inner (𝕜 := ℝ) n p₂ := by
    apply inner_eq_of_mem_convexHull _ hx2
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    cases hs with
    | inl h => rw [h]
    | inr h => rw [h]; exact h4
  exact hne (e1.symm.trans e2)

/-- Opposite cube face edges are disjoint. -/
private lemma cube_edge_disjoint (f : Fin 6) (i₁ j₁ i₂ j₂ : Fin 4)
    (h1 : j₁.val = (i₁.val + 1) % 4) (h2 : j₂.val = (i₂.val + 1) % 4)
    (d1 : i₁ ≠ i₂) (d2 : i₁ ≠ j₂) (d3 : j₁ ≠ i₂) (d4 : j₁ ≠ j₂) :
    Disjoint (convexHull ℝ {cubeVert (cubeFace f i₁), cubeVert (cubeFace f j₁)})
      (convexHull ℝ {cubeVert (cubeFace f i₂), cubeVert (cubeFace f j₂)}) := by
  fin_cases f <;> fin_cases i₁ <;> fin_cases j₁ <;> fin_cases i₂ <;> fin_cases j₂
  all_goals try (norm_num at h1)
  all_goals try (norm_num at h2)
  all_goals try (first
    | exact False.elim (d1 rfl)
    | exact False.elim (d2 rfl)
    | exact False.elim (d3 rfl)
    | exact False.elim (d4 rfl))
  case «0».«0».«1».«2».«3» =>
    refine disjoint_of_separated _ _ _ _ !₂[(0 : ℝ), 1, 0] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «0».«2».«3».«0».«1» =>
    refine disjoint_of_separated _ _ _ _ !₂[(0 : ℝ), 1, 0] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «0».«1».«2».«3».«0» =>
    refine disjoint_of_separated _ _ _ _ !₂[(0 : ℝ), 0, 1] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «0».«3».«0».«1».«2» =>
    refine disjoint_of_separated _ _ _ _ !₂[(0 : ℝ), 0, 1] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «1».«0».«1».«2».«3» =>
    refine disjoint_of_separated _ _ _ _ !₂[(0 : ℝ), 1, 0] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «1».«2».«3».«0».«1» =>
    refine disjoint_of_separated _ _ _ _ !₂[(0 : ℝ), 1, 0] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «1».«1».«2».«3».«0» =>
    refine disjoint_of_separated _ _ _ _ !₂[(0 : ℝ), 0, 1] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «1».«3».«0».«1».«2» =>
    refine disjoint_of_separated _ _ _ _ !₂[(0 : ℝ), 0, 1] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «2».«0».«1».«2».«3» =>
    refine disjoint_of_separated _ _ _ _ !₂[(1 : ℝ), 0, 0] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «2».«2».«3».«0».«1» =>
    refine disjoint_of_separated _ _ _ _ !₂[(1 : ℝ), 0, 0] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «2».«1».«2».«3».«0» =>
    refine disjoint_of_separated _ _ _ _ !₂[(0 : ℝ), 0, 1] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «2».«3».«0».«1».«2» =>
    refine disjoint_of_separated _ _ _ _ !₂[(0 : ℝ), 0, 1] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «3».«0».«1».«2».«3» =>
    refine disjoint_of_separated _ _ _ _ !₂[(1 : ℝ), 0, 0] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «3».«2».«3».«0».«1» =>
    refine disjoint_of_separated _ _ _ _ !₂[(1 : ℝ), 0, 0] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «3».«1».«2».«3».«0» =>
    refine disjoint_of_separated _ _ _ _ !₂[(0 : ℝ), 0, 1] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «3».«3».«0».«1».«2» =>
    refine disjoint_of_separated _ _ _ _ !₂[(0 : ℝ), 0, 1] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «4».«0».«1».«2».«3» =>
    refine disjoint_of_separated _ _ _ _ !₂[(1 : ℝ), 0, 0] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «4».«2».«3».«0».«1» =>
    refine disjoint_of_separated _ _ _ _ !₂[(1 : ℝ), 0, 0] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «4».«1».«2».«3».«0» =>
    refine disjoint_of_separated _ _ _ _ !₂[(0 : ℝ), 1, 0] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «4».«3».«0».«1».«2» =>
    refine disjoint_of_separated _ _ _ _ !₂[(0 : ℝ), 1, 0] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «5».«0».«1».«2».«3» =>
    refine disjoint_of_separated _ _ _ _ !₂[(1 : ℝ), 0, 0] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «5».«2».«3».«0».«1» =>
    refine disjoint_of_separated _ _ _ _ !₂[(1 : ℝ), 0, 0] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «5».«1».«2».«3».«0» =>
    refine disjoint_of_separated _ _ _ _ !₂[(0 : ℝ), 1, 0] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num
  case «5».«3».«0».«1».«2» =>
    refine disjoint_of_separated _ _ _ _ !₂[(0 : ℝ), 1, 0] ?_ ?_ ?_ <;>
      simp only [cubeVert, cubeFace, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] <;> norm_num

/-- Cube H-representation halfspaces. -/
private def cubeHalf (f : Fin 6) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | inner (𝕜 := ℝ) (cubeSuppN f) x ≤ 1}

/-- Cube barycentric weights (trilinear interpolation). -/
private noncomputable def cubeW (x : EuclideanSpace ℝ (Fin 3)) : Fin 8 → ℝ :=
  ![(1 + x 0) * (1 + x 1) * (1 + x 2) / 8, (1 + x 0) * (1 + x 1) * (1 - x 2) / 8,
    (1 + x 0) * (1 - x 1) * (1 + x 2) / 8, (1 + x 0) * (1 - x 1) * (1 - x 2) / 8,
    (1 - x 0) * (1 + x 1) * (1 + x 2) / 8, (1 - x 0) * (1 + x 1) * (1 - x 2) / 8,
    (1 - x 0) * (1 - x 1) * (1 + x 2) / 8, (1 - x 0) * (1 - x 1) * (1 - x 2) / 8]

/-- Barycentric weights are nonnegative on the H-representation. -/
private lemma cube_bary_nonneg (x : EuclideanSpace ℝ (Fin 3))
    (h : ∀ f : Fin 6, x ∈ cubeHalf f) (v : Fin 8) : 0 ≤ cubeW x v := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  simp only [cubeHalf, cubeSuppN, Set.mem_ofPred_eq, PiLp.inner_apply, Real.inner_apply,
    Fin.sum_univ_three, Fin.isValue, Matrix.cons_val] at h0 h1 h2 h3 h4 h5
  have g0 : 0 ≤ 1 + x 0 := by linarith
  have g1 : 0 ≤ 1 - x 0 := by linarith
  have g2 : 0 ≤ 1 + x 1 := by linarith
  have g3 : 0 ≤ 1 - x 1 := by linarith
  have g4 : 0 ≤ 1 + x 2 := by linarith
  have g5 : 0 ≤ 1 - x 2 := by linarith
  fin_cases v
  all_goals
    simp only [cubeW, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val]
  all_goals positivity

/-- Barycentric weights sum to one. -/
private lemma cube_bary_sum (x : EuclideanSpace ℝ (Fin 3)) : ∑ v, cubeW x v = 1 := by
  rw [Fin.sum_univ_eight]
  simp only [cubeW, Fin.isValue, Matrix.cons_val]
  ring

/-- Barycentric combination recovers the point. -/
private lemma cube_bary_center (x : EuclideanSpace ℝ (Fin 3)) :
    ∑ v, cubeW x v • cubeVert v = x := by
  ext k
  fin_cases k
  all_goals
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
      cubeW, cubeVert, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val]
  all_goals ring

/-- The H-representation is contained in the convex hull. -/
private lemma cube_inter_subset_hull :
    (⋂ f, cubeHalf f) ⊆ convexHull ℝ (Set.range cubeVert) := by
  intro x hx
  simp only [Set.mem_iInter] at hx
  apply mem_convexHull_of_exists_fintype (cubeW x) cubeVert
      (cube_bary_nonneg x hx) (cube_bary_sum x)
  · intro v
    exact Set.mem_range_self v
  · exact cube_bary_center x

/-- The convex hull equals the H-representation intersection. -/
private lemma cube_hull_eq_inter :
    convexHull ℝ (Set.range cubeVert) = ⋂ f, cubeHalf f := by
  apply le_antisymm
  · intro x hx
    simp only [Set.mem_iInter]
    intro f
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨v, rfl⟩ := hs
    exact cube_supp_le f v
  · exact cube_inter_subset_hull

/-- A halfspace point outside the interior achieves equality. -/
private lemma cube_half_eq_of_mem_of_not_mem_interior (f : Fin 6)
    (x : EuclideanSpace ℝ (Fin 3)) (hmem : x ∈ cubeHalf f)
    (hnot : x ∉ interior (cubeHalf f)) :
    inner (𝕜 := ℝ) (cubeSuppN f) x = 1 := by
  simp only [cubeHalf, Set.mem_ofPred_eq] at hmem
  by_contra hne
  have hlt : inner (𝕜 := ℝ) (cubeSuppN f) x < 1 := lt_of_le_of_ne hmem hne
  have hcont : Continuous
      (fun y : EuclideanSpace ℝ (Fin 3) => inner (𝕜 := ℝ) (cubeSuppN f) y) :=
    continuous_const.inner continuous_id
  have hopen : IsOpen
      {y : EuclideanSpace ℝ (Fin 3) | inner (𝕜 := ℝ) (cubeSuppN f) y < 1} := by
    have hIio : IsOpen (Set.Iio (1 : ℝ)) := isOpen_Iio
    have hpre := hIio.preimage hcont
    simpa only [Set.preimage, Set.mem_Iio] using hpre
  have hsub : {y : EuclideanSpace ℝ (Fin 3) |
      inner (𝕜 := ℝ) (cubeSuppN f) y < 1} ⊆ cubeHalf f := by
    intro y hy
    simp only [cubeHalf, Set.mem_ofPred_eq, Set.mem_ofPred_eq] at hy ⊢
    linarith
  have hmem_int : x ∈ interior (cubeHalf f) :=
    (hopen.subset_interior_iff).mpr hsub hlt
  exact hnot hmem_int

/-- A point of the H-representation with face equality lies in that face hull. -/
private lemma cube_mem_face_of_eq (f : Fin 6) (x : EuclideanSpace ℝ (Fin 3))
    (hall : ∀ g : Fin 6, x ∈ cubeHalf g)
    (heq : inner (𝕜 := ℝ) (cubeSuppN f) x = 1) :
    x ∈ convexHull ℝ (cubeVert '' Set.range (cubeFace f)) := by
  fin_cases f
  · -- Face 0 omits vertices 4, 5, 6, 7.
    have heq0 : inner (𝕜 := ℝ) (cubeSuppN 0) x = 1 := heq
    simp only [cubeSuppN, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
      Fin.isValue, Matrix.cons_val] at heq0
    have hx : x 0 = 1 := by linarith
    have hz4 : cubeW x 4 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz5 : cubeW x 5 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz6 : cubeW x 6 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz7 : cubeW x 7 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hsum := cube_bary_sum x
    rw [Fin.sum_univ_eight] at hsum
    have htot := cube_bary_center x
    rw [Fin.sum_univ_eight] at htot
    rw [hz4, hz5, hz6, hz7] at hsum
    have hz4s : cubeW x 4 • cubeVert 4 = 0 := by rw [hz4]; exact zero_smul _ _
    have hz5s : cubeW x 5 • cubeVert 5 = 0 := by rw [hz5]; exact zero_smul _ _
    have hz6s : cubeW x 6 • cubeVert 6 = 0 := by rw [hz6]; exact zero_smul _ _
    have hz7s : cubeW x 7 • cubeVert 7 = 0 := by rw [hz7]; exact zero_smul _ _
    rw [hz4s, hz5s, hz6s, hz7s] at htot
    apply mem_convexHull_of_exists_fintype (fun i : Fin 4 => cubeW x (cubeFace 0 i))
      (fun i : Fin 4 => cubeVert (cubeFace 0 i))
    · intro i
      exact cube_bary_nonneg x hall _
    · rw [Fin.sum_univ_four]
      simp only [cubeFace, Fin.isValue, Matrix.cons_val]
      linarith
    · intro i
      exact Set.mem_image_of_mem _ (Set.mem_range_self i)
    · rw [Fin.sum_univ_four]
      simp only [cubeFace, Fin.isValue, Matrix.cons_val]
      convert htot using 1
      abel
  · -- Face 1 omits vertices 0, 1, 2, 3.
    have heq1 : inner (𝕜 := ℝ) (cubeSuppN 1) x = 1 := heq
    simp only [cubeSuppN, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
      Fin.isValue, Matrix.cons_val] at heq1
    have hx : x 0 = -1 := by linarith
    have hz0 : cubeW x 0 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz1 : cubeW x 1 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz2 : cubeW x 2 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz3 : cubeW x 3 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hsum := cube_bary_sum x
    rw [Fin.sum_univ_eight] at hsum
    have htot := cube_bary_center x
    rw [Fin.sum_univ_eight] at htot
    rw [hz0, hz1, hz2, hz3] at hsum
    have hz0s : cubeW x 0 • cubeVert 0 = 0 := by rw [hz0]; exact zero_smul _ _
    have hz1s : cubeW x 1 • cubeVert 1 = 0 := by rw [hz1]; exact zero_smul _ _
    have hz2s : cubeW x 2 • cubeVert 2 = 0 := by rw [hz2]; exact zero_smul _ _
    have hz3s : cubeW x 3 • cubeVert 3 = 0 := by rw [hz3]; exact zero_smul _ _
    rw [hz0s, hz1s, hz2s, hz3s] at htot
    apply mem_convexHull_of_exists_fintype (fun i : Fin 4 => cubeW x (cubeFace 1 i))
      (fun i : Fin 4 => cubeVert (cubeFace 1 i))
    · intro i
      exact cube_bary_nonneg x hall _
    · rw [Fin.sum_univ_four]
      simp only [cubeFace, Fin.isValue, Matrix.cons_val]
      linarith
    · intro i
      exact Set.mem_image_of_mem _ (Set.mem_range_self i)
    · rw [Fin.sum_univ_four]
      simp only [cubeFace, Fin.isValue, Matrix.cons_val]
      convert htot using 1
      abel
  · -- Face 2 omits vertices 2, 3, 6, 7.
    have heq2 : inner (𝕜 := ℝ) (cubeSuppN 2) x = 1 := heq
    simp only [cubeSuppN, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
      Fin.isValue, Matrix.cons_val] at heq2
    have hx : x 1 = 1 := by linarith
    have hz2 : cubeW x 2 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz3 : cubeW x 3 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz6 : cubeW x 6 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz7 : cubeW x 7 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hsum := cube_bary_sum x
    rw [Fin.sum_univ_eight] at hsum
    have htot := cube_bary_center x
    rw [Fin.sum_univ_eight] at htot
    rw [hz2, hz3, hz6, hz7] at hsum
    have hz2s : cubeW x 2 • cubeVert 2 = 0 := by rw [hz2]; exact zero_smul _ _
    have hz3s : cubeW x 3 • cubeVert 3 = 0 := by rw [hz3]; exact zero_smul _ _
    have hz6s : cubeW x 6 • cubeVert 6 = 0 := by rw [hz6]; exact zero_smul _ _
    have hz7s : cubeW x 7 • cubeVert 7 = 0 := by rw [hz7]; exact zero_smul _ _
    rw [hz2s, hz3s, hz6s, hz7s] at htot
    apply mem_convexHull_of_exists_fintype (fun i : Fin 4 => cubeW x (cubeFace 2 i))
      (fun i : Fin 4 => cubeVert (cubeFace 2 i))
    · intro i
      exact cube_bary_nonneg x hall _
    · rw [Fin.sum_univ_four]
      simp only [cubeFace, Fin.isValue, Matrix.cons_val]
      linarith
    · intro i
      exact Set.mem_image_of_mem _ (Set.mem_range_self i)
    · rw [Fin.sum_univ_four]
      simp only [cubeFace, Fin.isValue, Matrix.cons_val]
      convert htot using 1
      abel
  · -- Face 3 omits vertices 0, 1, 4, 5.
    have heq3 : inner (𝕜 := ℝ) (cubeSuppN 3) x = 1 := heq
    simp only [cubeSuppN, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
      Fin.isValue, Matrix.cons_val] at heq3
    have hx : x 1 = -1 := by linarith
    have hz0 : cubeW x 0 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz1 : cubeW x 1 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz4 : cubeW x 4 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz5 : cubeW x 5 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hsum := cube_bary_sum x
    rw [Fin.sum_univ_eight] at hsum
    have htot := cube_bary_center x
    rw [Fin.sum_univ_eight] at htot
    rw [hz0, hz1, hz4, hz5] at hsum
    have hz0s : cubeW x 0 • cubeVert 0 = 0 := by rw [hz0]; exact zero_smul _ _
    have hz1s : cubeW x 1 • cubeVert 1 = 0 := by rw [hz1]; exact zero_smul _ _
    have hz4s : cubeW x 4 • cubeVert 4 = 0 := by rw [hz4]; exact zero_smul _ _
    have hz5s : cubeW x 5 • cubeVert 5 = 0 := by rw [hz5]; exact zero_smul _ _
    rw [hz0s, hz1s, hz4s, hz5s] at htot
    apply mem_convexHull_of_exists_fintype (fun i : Fin 4 => cubeW x (cubeFace 3 i))
      (fun i : Fin 4 => cubeVert (cubeFace 3 i))
    · intro i
      exact cube_bary_nonneg x hall _
    · rw [Fin.sum_univ_four]
      simp only [cubeFace, Fin.isValue, Matrix.cons_val]
      linarith
    · intro i
      exact Set.mem_image_of_mem _ (Set.mem_range_self i)
    · rw [Fin.sum_univ_four]
      simp only [cubeFace, Fin.isValue, Matrix.cons_val]
      convert htot using 1
      abel
  · -- Face 4 omits vertices 1, 3, 5, 7.
    have heq4 : inner (𝕜 := ℝ) (cubeSuppN 4) x = 1 := heq
    simp only [cubeSuppN, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
      Fin.isValue, Matrix.cons_val] at heq4
    have hx : x 2 = 1 := by linarith
    have hz1 : cubeW x 1 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz3 : cubeW x 3 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz5 : cubeW x 5 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz7 : cubeW x 7 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hsum := cube_bary_sum x
    rw [Fin.sum_univ_eight] at hsum
    have htot := cube_bary_center x
    rw [Fin.sum_univ_eight] at htot
    rw [hz1, hz3, hz5, hz7] at hsum
    have hz1s : cubeW x 1 • cubeVert 1 = 0 := by rw [hz1]; exact zero_smul _ _
    have hz3s : cubeW x 3 • cubeVert 3 = 0 := by rw [hz3]; exact zero_smul _ _
    have hz5s : cubeW x 5 • cubeVert 5 = 0 := by rw [hz5]; exact zero_smul _ _
    have hz7s : cubeW x 7 • cubeVert 7 = 0 := by rw [hz7]; exact zero_smul _ _
    rw [hz1s, hz3s, hz5s, hz7s] at htot
    apply mem_convexHull_of_exists_fintype (fun i : Fin 4 => cubeW x (cubeFace 4 i))
      (fun i : Fin 4 => cubeVert (cubeFace 4 i))
    · intro i
      exact cube_bary_nonneg x hall _
    · rw [Fin.sum_univ_four]
      simp only [cubeFace, Fin.isValue, Matrix.cons_val]
      linarith
    · intro i
      exact Set.mem_image_of_mem _ (Set.mem_range_self i)
    · rw [Fin.sum_univ_four]
      simp only [cubeFace, Fin.isValue, Matrix.cons_val]
      convert htot using 1
      abel
  · -- Face 5 omits vertices 0, 2, 4, 6.
    have heq5 : inner (𝕜 := ℝ) (cubeSuppN 5) x = 1 := heq
    simp only [cubeSuppN, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
      Fin.isValue, Matrix.cons_val] at heq5
    have hx : x 2 = -1 := by linarith
    have hz0 : cubeW x 0 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz2 : cubeW x 2 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz4 : cubeW x 4 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hz6 : cubeW x 6 = 0 := by
      simp only [cubeW, Fin.isValue, Matrix.cons_val]
      rw [hx]
      ring
    have hsum := cube_bary_sum x
    rw [Fin.sum_univ_eight] at hsum
    have htot := cube_bary_center x
    rw [Fin.sum_univ_eight] at htot
    rw [hz0, hz2, hz4, hz6] at hsum
    have hz0s : cubeW x 0 • cubeVert 0 = 0 := by rw [hz0]; exact zero_smul _ _
    have hz2s : cubeW x 2 • cubeVert 2 = 0 := by rw [hz2]; exact zero_smul _ _
    have hz4s : cubeW x 4 • cubeVert 4 = 0 := by rw [hz4]; exact zero_smul _ _
    have hz6s : cubeW x 6 • cubeVert 6 = 0 := by rw [hz6]; exact zero_smul _ _
    rw [hz0s, hz2s, hz4s, hz6s] at htot
    apply mem_convexHull_of_exists_fintype (fun i : Fin 4 => cubeW x (cubeFace 5 i))
      (fun i : Fin 4 => cubeVert (cubeFace 5 i))
    · intro i
      exact cube_bary_nonneg x hall _
    · rw [Fin.sum_univ_four]
      simp only [cubeFace, Fin.isValue, Matrix.cons_val]
      linarith
    · intro i
      exact Set.mem_image_of_mem _ (Set.mem_range_self i)
    · rw [Fin.sum_univ_four]
      simp only [cubeFace, Fin.isValue, Matrix.cons_val]
      convert htot using 1
      abel

/-- Cube frontier is covered by faces. -/
private lemma cube_cover (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ frontier (convexHull ℝ (Set.range cubeVert))) :
    ∃ f : Fin 6, x ∈ convexHull ℝ (cubeVert '' Set.range (cubeFace f)) := by
  classical
  have hclosed : IsClosed (convexHull ℝ (Set.range cubeVert)) :=
    (Set.finite_range cubeVert).isClosed_convexHull ℝ
  have hmem : x ∈ convexHull ℝ (Set.range cubeVert) := hclosed.frontier_subset hx
  have hnot : x ∉ interior (convexHull ℝ (Set.range cubeVert)) := by
    exact (mem_frontier_iff_notMem_interior hmem).mp hx
  rw [cube_hull_eq_inter] at hmem hnot
  simp only [interior_iInter_of_finite, Set.mem_iInter] at hmem hnot
  have hex : ∃ f : Fin 6, x ∉ interior (cubeHalf f) := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hnot hcon
  obtain ⟨f, hf⟩ := hex
  have heq := cube_half_eq_of_mem_of_not_mem_interior f x (hmem f) hf
  exact ⟨f, cube_mem_face_of_eq f x hmem heq⟩

/-- Cube realization exists. -/
private theorem cube_exists :
    ∃ (w : Fin 8 → EuclideanSpace ℝ (Fin 3)) (ee : Fin 12 → Fin 8 × Fin 8)
      (fv : Fin 6 → Fin 4 → Fin 8) (b : Set (EuclideanSpace ℝ (Fin 3)))
      (ll dd : ℝ),
      0 < ll ∧ 0 < dd ∧
      b = convexHull ℝ (Set.range w) ∧
      Convex ℝ b ∧
      (∀ v : Fin 8, w v ∈ frontier b) ∧
      (∀ v : Fin 8, w v ∉ convexHull ℝ (w '' {u : Fin 8 | u ≠ v})) ∧
      (Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 8, d = w i - w j}) = 3) ∧
      (∀ e : Fin 12, dist (w (ee e).1) (w (ee e).2) = ll) ∧
      (∀ (f : Fin 6) (i j : Fin 4), j.val = (i.val + 1) % 4 →
        dist (w (fv f i)) (w (fv f j)) = ll) ∧
      (∀ (f : Fin 6) (h i j : Fin 4), h.val = (i.val + 4 - 1) % 4 →
        j.val = (i.val + 1) % 4 → dist (w (fv f h)) (w (fv f j)) = dd) ∧
      (∀ f : Fin 6, Function.Injective (fv f)) ∧
      (∀ (f : Fin 6) (k : Fin 4), w (fv f k) ∉ convexHull ℝ
        (w '' (Set.range (fv f) \ {fv f k}))) ∧
      (∀ (f : Fin 6) (i₁ j₁ i₂ j₂ : Fin 4),
        j₁.val = (i₁.val + 1) % 4 →
        j₂.val = (i₂.val + 1) % 4 →
        i₁ ≠ i₂ → i₁ ≠ j₂ → j₁ ≠ i₂ → j₁ ≠ j₂ →
        Disjoint (convexHull ℝ {w (fv f i₁), w (fv f j₁)})
          (convexHull ℝ {w (fv f i₂), w (fv f j₂)})) ∧
      (∀ (f : Fin 6) (i j : Fin 4), j.val = (i.val + 1) % 4 →
        ∃ e : Fin 12, ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i)) ∧
      (∀ e : Fin 12, ∃ f : Fin 6, ∃ i j : Fin 4,
        j.val = (i.val + 1) % 4 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))) ∧
      (∀ e : Fin 12, Set.ncard {f : Fin 6 | ∃ i j : Fin 4,
        j.val = (i.val + 1) % 4 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))} = 2) ∧
      (∀ f : Fin 6, Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 4, d = w (fv f i) - w (fv f j)}) ≤ 2) ∧
      (∀ f : Fin 6, ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
        n ≠ 0 ∧ (∀ x ∈ b, inner (𝕜 := ℝ) n x ≤ c) ∧
        (∀ i : Fin 4, inner (𝕜 := ℝ) n (w (fv f i)) = c)) ∧
      (∀ e₁ e₂ : Fin 12, (ee e₁ = ee e₂ ∨ ee e₁ = (ee e₂).swap) → e₁ = e₂) ∧
      (∀ f₁ f₂ : Fin 6, Set.range (fv f₁) = Set.range (fv f₂) → f₁ = f₂) ∧
      (∀ e : Fin 12, convexHull ℝ {w (ee e).1, w (ee e).2} ⊆ frontier b) ∧
      (∀ f : Fin 6, convexHull ℝ (w '' Set.range (fv f)) ⊆ frontier b) ∧
      (∀ x ∈ frontier b, ∃ f : Fin 6,
        x ∈ convexHull ℝ (w '' Set.range (fv f))) ∧
      (∀ v : Fin 8, Set.ncard {f : Fin 6 | ∃ i : Fin 4, fv f i = v} = 3) ∧
      2 * 12 = 4 * 6 ∧ 2 * 12 = 3 * 8 ∧ (8 : ℤ) - (12 : ℤ) + (6 : ℤ) = 2 := by
  refine ⟨cubeVert, cubeEdge, cubeFace, convexHull ℝ (Set.range cubeVert),
    2, 2 * Real.sqrt 2, by norm_num, ?_, rfl, convex_convexHull ℝ _,
    cube_vert_frontier, cube_convex_pos, cube_finrank, cube_edge_length,
    cube_face_edge, cube_face_diag, cube_face_inj, cube_face_convex_pos,
    cube_edge_disjoint, cube_face_edge_exists, cube_edge_face_exists, cube_two_face,
    cube_face_planar, cube_supp_exists, cube_edge_dup, cube_face_dup,
    cube_edge_frontier, cube_face_frontier, cube_cover, cube_vert_face_count,
    rfl, rfl, rfl⟩
  positivity

end Cube

section Octahedron

/-- Octahedron vertices, the positive and negative coordinate vectors. -/
private def octVert : Fin 6 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 0, 0], !₂[-1, 0, 0], !₂[0, 1, 0],
    !₂[(0 : ℝ), -1, 0], !₂[0, 0, 1], !₂[0, 0, -1]]

/-- Octahedron edge endpoints, all non-antipodal pairs of vertices. -/
private def octEdge : Fin 12 → Fin 6 × Fin 6 :=
  ![(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3),
    (1, 4), (1, 5), (2, 4), (2, 5), (3, 4), (3, 5)]

/-- Octahedron faces as cyclic vertex lists. -/
private def octFace : Fin 8 → Fin 3 → Fin 6 :=
  ![![0, 2, 4], ![0, 5, 2], ![0, 4, 3], ![0, 3, 5],
    ![1, 4, 2], ![1, 2, 5], ![1, 3, 4], ![1, 5, 3]]

/-- Supporting-plane normals for the octahedron faces. -/
private def octSuppN : Fin 8 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 1, 1], !₂[1, 1, -1], !₂[1, -1, 1], !₂[1, -1, -1],
    !₂[(-1 : ℝ), 1, 1], !₂[-1, 1, -1], !₂[-1, -1, 1], !₂[-1, -1, -1]]

/-- For each octahedron vertex, a face containing it. -/
private def octVertFace : Fin 6 → Fin 8 := ![0, 4, 0, 2, 0, 1]

/-- Index witnessing the assigned octahedron vertex-face membership. -/
private def octVertFaceIdx : Fin 6 → Fin 3 := ![0, 0, 1, 2, 2, 1]

/-- The two faces containing each octahedron edge. -/
private def octEdgeFaces : Fin 12 → Fin 8 × Fin 8 :=
  ![(0, 1), (2, 3), (0, 2), (1, 3), (4, 5), (6, 7),
    (4, 6), (5, 7), (0, 4), (1, 5), (2, 6), (3, 7)]

/-- The four faces containing each octahedron vertex. -/
private def octVertFaces : Fin 6 → Fin 8 × Fin 8 × Fin 8 × Fin 8 :=
  ![(0, 1, 2, 3), (4, 5, 6, 7), (0, 1, 4, 5),
    (2, 3, 6, 7), (0, 2, 4, 6), (1, 3, 5, 7)]

/-- Octahedron edge lengths. -/
private lemma oct_edge_length (e : Fin 12) :
    dist (octVert (octEdge e).1) (octVert (octEdge e).2) = Real.sqrt 2 := by
  fin_cases e
  all_goals
    simp only [octVert, octEdge, EuclideanSpace.dist_eq, Fin.sum_univ_three,
      Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val,
      Real.dist_eq]
  all_goals norm_num

/-- Octahedron face edges. -/
private lemma oct_face_edge (f : Fin 8) (i j : Fin 3)
    (h : j.val = (i.val + 1) % 3) :
    dist (octVert (octFace f i)) (octVert (octFace f j)) = Real.sqrt 2 := by
  fin_cases f <;> fin_cases i <;> fin_cases j
  all_goals try (norm_num at h)
  all_goals
    simp only [octVert, octFace, EuclideanSpace.dist_eq, Fin.sum_univ_three,
      Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val,
      Real.dist_eq]
  all_goals norm_num

/-- The opposite-neighbor diagonal in each triangular octahedron face. -/
private lemma oct_face_diag (f : Fin 8) (h i j : Fin 3)
    (hh : h.val = (i.val + 3 - 1) % 3)
    (hj : j.val = (i.val + 1) % 3) :
    dist (octVert (octFace f h)) (octVert (octFace f j)) = Real.sqrt 2 := by
  fin_cases f <;> fin_cases h <;> fin_cases i <;> fin_cases j
  all_goals try (norm_num at hh)
  all_goals try (norm_num at hj)
  all_goals
    simp only [octVert, octFace, EuclideanSpace.dist_eq, Fin.sum_univ_three,
      Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val,
      Real.dist_eq]
  all_goals norm_num

/-- Octahedron faces are injective. -/
private lemma oct_face_inj (f : Fin 8) : Function.Injective (octFace f) := by
  fin_cases f <;> decide

/-- Every octahedron face edge is a graph edge. -/
private lemma oct_face_edge_exists (f : Fin 8) (i j : Fin 3)
    (h : j.val = (i.val + 1) % 3) :
    ∃ e : Fin 12, octEdge e = (octFace f i, octFace f j) ∨
      octEdge e = (octFace f j, octFace f i) := by
  fin_cases f <;> fin_cases i <;> fin_cases j
  all_goals try (norm_num at h)
  all_goals decide

/-- Every octahedron graph edge is a face edge. -/
private lemma oct_edge_face_exists (e : Fin 12) :
    ∃ f : Fin 8, ∃ i j : Fin 3, j.val = (i.val + 1) % 3 ∧
      (octEdge e = (octFace f i, octFace f j) ∨
        octEdge e = (octFace f j, octFace f i)) := by
  fin_cases e <;> decide

/-- Octahedron edges are duplicate-free. -/
private lemma oct_edge_dup (e₁ e₂ : Fin 12)
    (h : octEdge e₁ = octEdge e₂ ∨ octEdge e₁ = (octEdge e₂).swap) :
    e₁ = e₂ := by
  revert h
  fin_cases e₁ <;> fin_cases e₂ <;> decide

/-- Octahedron faces are duplicate-free. -/
private lemma oct_face_dup (f₁ f₂ : Fin 8)
    (h : Set.range (octFace f₁) = Set.range (octFace f₂)) : f₁ = f₂ := by
  have hrange : ∀ f : Fin 8, Set.range (octFace f) =
      ↑(Finset.univ.image (octFace f)) := by
    intro f
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [hrange f₁, hrange f₂] at h
  have hfin : Finset.univ.image (octFace f₁) =
      Finset.univ.image (octFace f₂) := Finset.coe_injective h
  have hne : ∀ a b : Fin 8, a ≠ b →
      Finset.univ.image (octFace a) ≠ Finset.univ.image (octFace b) := by decide
  by_cases heq : f₁ = f₂
  · exact heq
  · exact False.elim (hne f₁ f₂ heq hfin)

/-- Each octahedron edge lies in exactly two faces. -/
private lemma oct_two_face (e : Fin 12) :
    Set.ncard {f : Fin 8 | ∃ i j : Fin 3, j.val = (i.val + 1) % 3 ∧
      (octEdge e = (octFace f i, octFace f j) ∨
        octEdge e = (octFace f j, octFace f i))} = 2 := by
  have hset : ∀ e : Fin 12, {f : Fin 8 | ∃ i j : Fin 3,
      j.val = (i.val + 1) % 3 ∧
      (octEdge e = (octFace f i, octFace f j) ∨
        octEdge e = (octFace f j, octFace f i))} =
      {(octEdgeFaces e).1, (octEdgeFaces e).2} := by
    intro e
    ext f
    fin_cases e <;> fin_cases f <;> decide
  have hne : ∀ e : Fin 12, (octEdgeFaces e).1 ≠ (octEdgeFaces e).2 := by decide
  rw [hset e]
  exact Set.ncard_pair (hne e)

/-- Each octahedron vertex lies in exactly four faces. -/
private lemma oct_vert_face_count (v : Fin 6) :
    Set.ncard {f : Fin 8 | ∃ i : Fin 3, octFace f i = v} = 4 := by
  have hset : ∀ v : Fin 6, {f : Fin 8 | ∃ i : Fin 3, octFace f i = v} =
      {(octVertFaces v).1, (octVertFaces v).2.1,
        (octVertFaces v).2.2.1, (octVertFaces v).2.2.2} := by
    intro v
    ext f
    fin_cases v <;> fin_cases f <;> decide
  have hne : ∀ v : Fin 6,
      (octVertFaces v).1 ≠ (octVertFaces v).2.1 ∧
      (octVertFaces v).1 ≠ (octVertFaces v).2.2.1 ∧
      (octVertFaces v).1 ≠ (octVertFaces v).2.2.2 ∧
      (octVertFaces v).2.1 ≠ (octVertFaces v).2.2.1 ∧
      (octVertFaces v).2.1 ≠ (octVertFaces v).2.2.2 ∧
      (octVertFaces v).2.2.1 ≠ (octVertFaces v).2.2.2 := by decide
  rw [hset v]
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := hne v
  have ha : (octVertFaces v).1 ∉
      ({(octVertFaces v).2.1, (octVertFaces v).2.2.1,
        (octVertFaces v).2.2.2} : Set (Fin 8)) := by simp [hab, hac, had]
  have hb : (octVertFaces v).2.1 ∉
      ({(octVertFaces v).2.2.1, (octVertFaces v).2.2.2} : Set (Fin 8)) := by
    simp [hbc, hbd]
  have hfin3 : ({(octVertFaces v).2.1, (octVertFaces v).2.2.1,
      (octVertFaces v).2.2.2} : Set (Fin 8)).Finite := Set.toFinite _
  have hfin2 : ({(octVertFaces v).2.2.1,
      (octVertFaces v).2.2.2} : Set (Fin 8)).Finite := Set.toFinite _
  rw [Set.ncard_insert_of_notMem ha hfin3, Set.ncard_insert_of_notMem hb hfin2,
    Set.ncard_pair hcd]

/-- Supporting-plane upper bounds for octahedron faces. -/
private lemma oct_supp_le (f : Fin 8) (v : Fin 6) :
    inner (𝕜 := ℝ) (octSuppN f) (octVert v) ≤ (1 : ℝ) := by
  fin_cases f <;> fin_cases v
  all_goals
    simp only [octVert, octSuppN, PiLp.inner_apply, Real.inner_apply,
      Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val]
  all_goals norm_num

/-- Supporting-plane equalities on octahedron face vertices. -/
private lemma oct_supp_eq (f : Fin 8) (i : Fin 3) :
    inner (𝕜 := ℝ) (octSuppN f) (octVert (octFace f i)) = (1 : ℝ) := by
  fin_cases f <;> fin_cases i
  all_goals
    simp only [octVert, octFace, octSuppN, PiLp.inner_apply, Real.inner_apply,
      Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val]
  all_goals norm_num

/-- Octahedron supporting normals are nonzero. -/
private lemma oct_supp_ne (f : Fin 8) : octSuppN f ≠ 0 := by
  have hnorm : ∀ g : Fin 8,
      inner (𝕜 := ℝ) (octSuppN g) (octSuppN g) = 3 := by
    intro g
    fin_cases g
    all_goals
      simp only [octSuppN, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val]
    all_goals norm_num
  intro hcon
  have h := hnorm f
  rw [hcon] at h
  simp only [inner_zero_left] at h
  norm_num at h

/-- Supporting planes exist for octahedron faces. -/
private lemma oct_supp_exists (f : Fin 8) :
    ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
      n ≠ 0 ∧
      (∀ x ∈ convexHull ℝ (Set.range octVert), inner (𝕜 := ℝ) n x ≤ c) ∧
      (∀ i : Fin 3, inner (𝕜 := ℝ) n (octVert (octFace f i)) = c) := by
  refine ⟨octSuppN f, 1, oct_supp_ne f, ?_, fun i => oct_supp_eq f i⟩
  intro x hx
  apply inner_le_of_mem_convexHull _ hx
  intro s hs
  obtain ⟨v, rfl⟩ := hs
  exact oct_supp_le f v

/-- Octahedron vertices are in convex position. -/
private lemma oct_convex_pos (v : Fin 6) :
    octVert v ∉ convexHull ℝ (octVert '' {u : Fin 6 | u ≠ v}) := by
  apply not_mem_convexHull_of_separation (n := octVert v) (c := 0)
  · intro s hs
    obtain ⟨u, hu, rfl⟩ := hs
    simp only [Set.mem_ofPred_eq] at hu
    fin_cases v <;> fin_cases u
    all_goals try (exact False.elim (hu rfl))
    all_goals
      simp only [octVert, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val]
    all_goals norm_num
  · fin_cases v
    all_goals
      simp only [octVert, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
        Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val]
    all_goals norm_num

/-- Octahedron face vertices are in convex position within each face. -/
private lemma oct_face_convex_pos (f : Fin 8) (k : Fin 3) :
    octVert (octFace f k) ∉ convexHull ℝ
      (octVert '' (Set.range (octFace f) \ {octFace f k})) := by
  apply not_mem_convexHull_of_separation (n := octVert (octFace f k)) (c := 0)
  · intro s hs
    obtain ⟨a, ⟨hrange, hne⟩, rfl⟩ := hs
    obtain ⟨i, rfl⟩ := hrange
    simp only [Set.mem_singleton_iff] at hne
    fin_cases f <;> fin_cases k <;> fin_cases i
    all_goals try (norm_num at hne)
    all_goals
      simp only [octVert, octFace, PiLp.inner_apply, Real.inner_apply,
        Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
        Matrix.cons_val]
    all_goals norm_num
  · fin_cases f <;> fin_cases k
    all_goals
      simp only [octVert, octFace, PiLp.inner_apply, Real.inner_apply,
        Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
        Matrix.cons_val]
    all_goals norm_num

/-- Three vertex differences spanning the octahedron. -/
private def octD : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![octVert 0 - octVert 1, octVert 2 - octVert 3, octVert 4 - octVert 5]

private lemma oct_gram_det : (Matrix.gram ℝ octD).det = 64 := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.gram_apply, octD, octVert, PiLp.inner_apply,
    Real.inner_apply, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val]
  norm_num

private lemma octD_indep : LinearIndependent ℝ octD := by
  rw [← Matrix.det_gram_ne_zero_iff_linearIndependent, oct_gram_det]
  norm_num

private lemma oct_span_top : Submodule.span ℝ (Set.range octD) = ⊤ :=
  LinearIndependent.span_eq_top_of_card_eq_finrank octD_indep
    (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])

/-- Full-dimensionality for the octahedron vertex set. -/
private lemma oct_finrank : Module.finrank ℝ (Submodule.span ℝ
    {d : EuclideanSpace ℝ (Fin 3) | ∃ i j : Fin 6, d = octVert i - octVert j}) = 3 := by
  have hle : Submodule.span ℝ (Set.range octD) ≤ Submodule.span ℝ
      {d : EuclideanSpace ℝ (Fin 3) | ∃ i j : Fin 6, d = octVert i - octVert j} := by
    apply Submodule.span_mono
    rintro x ⟨k, rfl⟩
    fin_cases k
    · exact ⟨0, 1, rfl⟩
    · exact ⟨2, 3, rfl⟩
    · exact ⟨4, 5, rfl⟩
  rw [oct_span_top] at hle
  have hspan : Submodule.span ℝ
      {d : EuclideanSpace ℝ (Fin 3) | ∃ i j : Fin 6, d = octVert i - octVert j} = ⊤ :=
    top_le_iff.mp hle
  have hfin : Module.finrank ℝ ↥(⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := Submodule.topEquiv.finrank_eq
  rw [hspan, hfin, finrank_euclideanSpace_fin]

/-- Each octahedron vertex lies in its assigned face. -/
private lemma oct_vert_mem_face :
    ∀ v : Fin 6, octFace (octVertFace v) (octVertFaceIdx v) = v := by
  decide

/-- Octahedron vertices lie in the frontier. -/
private lemma oct_vert_frontier (v : Fin 6) :
    octVert v ∈ frontier (convexHull ℝ (Set.range octVert)) := by
  have hmem : octVert v ∈ convexHull ℝ (Set.range octVert) :=
    subset_convexHull ℝ _ (Set.mem_range_self v)
  have hle : ∀ x ∈ convexHull ℝ (Set.range octVert),
      inner (𝕜 := ℝ) (octSuppN (octVertFace v)) x ≤ 1 := by
    intro x hx
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact oct_supp_le _ u
  have heq : inner (𝕜 := ℝ) (octSuppN (octVertFace v)) (octVert v) = 1 := by
    have h := oct_supp_eq (octVertFace v) (octVertFaceIdx v)
    rw [oct_vert_mem_face v] at h
    exact h
  exact mem_frontier_of_support hmem hle heq (oct_supp_ne _)

/-- Octahedron edge hulls lie in the frontier. -/
private lemma oct_edge_frontier (e : Fin 12) :
    convexHull ℝ {octVert (octEdge e).1, octVert (octEdge e).2} ⊆
      frontier (convexHull ℝ (Set.range octVert)) := by
  obtain ⟨f, i, j, _, heq⟩ := oct_edge_face_exists e
  have hsub : ({octVert (octEdge e).1, octVert (octEdge e).2} :
      Set (EuclideanSpace ℝ (Fin 3))) ⊆ Set.range octVert := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    cases hz with
    | inl h => rw [h]; exact Set.mem_range_self _
    | inr h => rw [h]; exact Set.mem_range_self _
  have hle : ∀ x ∈ convexHull ℝ (Set.range octVert),
      inner (𝕜 := ℝ) (octSuppN f) x ≤ 1 := by
    intro x hx
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact oct_supp_le f u
  have ha : inner (𝕜 := ℝ) (octSuppN f) (octVert (octEdge e).1) = 1 := by
    cases heq with
    | inl h =>
      have h1 : (octEdge e).1 = octFace f i := congrArg Prod.fst h
      rw [h1]
      exact oct_supp_eq f i
    | inr h =>
      have h1 : (octEdge e).1 = octFace f j := congrArg Prod.fst h
      rw [h1]
      exact oct_supp_eq f j
  have hb : inner (𝕜 := ℝ) (octSuppN f) (octVert (octEdge e).2) = 1 := by
    cases heq with
    | inl h =>
      have h2 : (octEdge e).2 = octFace f j := congrArg Prod.snd h
      rw [h2]
      exact oct_supp_eq f j
    | inr h =>
      have h2 : (octEdge e).2 = octFace f i := congrArg Prod.snd h
      rw [h2]
      exact oct_supp_eq f i
  intro y hy
  have hyB : y ∈ convexHull ℝ (Set.range octVert) := convexHull_mono hsub hy
  have heq_y : inner (𝕜 := ℝ) (octSuppN f) y = 1 := by
    apply inner_eq_of_mem_convexHull _ hy
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    cases hs with
    | inl h => rw [h]; exact ha
    | inr h => rw [h]; exact hb
  exact mem_frontier_of_support hyB hle heq_y (oct_supp_ne f)

/-- Octahedron face hulls lie in the frontier. -/
private lemma oct_face_frontier (f : Fin 8) :
    convexHull ℝ (octVert '' Set.range (octFace f)) ⊆
      frontier (convexHull ℝ (Set.range octVert)) := by
  have hsub : octVert '' Set.range (octFace f) ⊆ Set.range octVert := by
    rintro z ⟨x, ⟨i, rfl⟩, rfl⟩
    exact Set.mem_range_self _
  have hle : ∀ x ∈ convexHull ℝ (Set.range octVert),
      inner (𝕜 := ℝ) (octSuppN f) x ≤ 1 := by
    intro x hx
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact oct_supp_le f u
  intro y hy
  have hyB : y ∈ convexHull ℝ (Set.range octVert) := convexHull_mono hsub hy
  have heq_y : inner (𝕜 := ℝ) (octSuppN f) y = 1 := by
    apply inner_eq_of_mem_convexHull _ hy
    intro s hs
    obtain ⟨x, ⟨i, rfl⟩, rfl⟩ := hs
    exact oct_supp_eq f i
  exact mem_frontier_of_support hyB hle heq_y (oct_supp_ne f)

/-- The halfspace determined by an octahedron face. -/
private def octHalf (f : Fin 8) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | inner (𝕜 := ℝ) (octSuppN f) x ≤ 1}

/-- Barycentric weights for the cross-polytope H-representation. -/
private noncomputable def octW (x : EuclideanSpace ℝ (Fin 3)) : Fin 6 → ℝ :=
  ![(1 + x 0 - |x 1| - |x 2|) / 2,
    (1 - x 0 - |x 1| - |x 2|) / 2,
    (x 1 + |x 1|) / 2, (-x 1 + |x 1|) / 2,
    (x 2 + |x 2|) / 2, (-x 2 + |x 2|) / 2]

/-- Octahedron barycentric weights are nonnegative on the H-representation. -/
private lemma oct_bary_nonneg (x : EuclideanSpace ℝ (Fin 3))
    (h : ∀ f : Fin 8, x ∈ octHalf f) (v : Fin 6) : 0 ≤ octW x v := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  simp only [octHalf, octSuppN, Set.mem_ofPred_eq, PiLp.inner_apply,
    Real.inner_apply, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6 h7
  fin_cases v
  all_goals
    simp only [octW, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val]
  all_goals
    rcases le_total 0 (x 1) with hy | hy <;>
      rcases le_total 0 (x 2) with hz | hz
  all_goals simp_all only [abs_of_nonneg, abs_of_nonpos]
  all_goals linarith

/-- Octahedron barycentric weights sum to one. -/
private lemma oct_bary_sum (x : EuclideanSpace ℝ (Fin 3)) : ∑ v, octW x v = 1 := by
  rw [Fin.sum_univ_six]
  simp only [octW, Fin.isValue, Matrix.cons_val]
  ring

/-- The octahedron barycentric combination recovers the point. -/
private lemma oct_bary_center (x : EuclideanSpace ℝ (Fin 3)) :
    ∑ v, octW x v • octVert v = x := by
  ext k
  fin_cases k
  all_goals
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.sum_univ_six,
      octW, octVert, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val]
  all_goals ring

/-- The octahedron H-representation is contained in its convex hull. -/
private lemma oct_inter_subset_hull :
    (⋂ f, octHalf f) ⊆ convexHull ℝ (Set.range octVert) := by
  intro x hx
  simp only [Set.mem_iInter] at hx
  apply mem_convexHull_of_exists_fintype (octW x) octVert
      (oct_bary_nonneg x hx) (oct_bary_sum x)
  · intro v
    exact Set.mem_range_self v
  · exact oct_bary_center x

/-- The octahedron convex hull equals its H-representation. -/
private lemma oct_hull_eq_inter :
    convexHull ℝ (Set.range octVert) = ⋂ f, octHalf f := by
  apply le_antisymm
  · intro x hx
    simp only [Set.mem_iInter]
    intro f
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨v, rfl⟩ := hs
    exact oct_supp_le f v
  · exact oct_inter_subset_hull

/-- A halfspace point outside its interior achieves equality. -/
private lemma oct_half_eq_of_mem_of_not_mem_interior (f : Fin 8)
    (x : EuclideanSpace ℝ (Fin 3)) (hmem : x ∈ octHalf f)
    (hnot : x ∉ interior (octHalf f)) :
    inner (𝕜 := ℝ) (octSuppN f) x = 1 := by
  simp only [octHalf, Set.mem_ofPred_eq] at hmem
  by_contra hne
  have hlt : inner (𝕜 := ℝ) (octSuppN f) x < 1 := lt_of_le_of_ne hmem hne
  have hcont : Continuous
      (fun y : EuclideanSpace ℝ (Fin 3) => inner (𝕜 := ℝ) (octSuppN f) y) :=
    continuous_const.inner continuous_id
  have hopen : IsOpen
      {y : EuclideanSpace ℝ (Fin 3) | inner (𝕜 := ℝ) (octSuppN f) y < 1} := by
    have hIio : IsOpen (Set.Iio (1 : ℝ)) := isOpen_Iio
    have hpre := hIio.preimage hcont
    simpa only [Set.preimage, Set.mem_Iio] using hpre
  have hsub : {y : EuclideanSpace ℝ (Fin 3) |
      inner (𝕜 := ℝ) (octSuppN f) y < 1} ⊆ octHalf f := by
    intro y hy
    simp only [octHalf, Set.mem_ofPred_eq, Set.mem_ofPred_eq] at hy ⊢
    linarith
  exact hnot ((hopen.subset_interior_iff).mpr hsub hlt)

/-- Face-local barycentric weights for the octahedron. -/
private def octFaceW (f : Fin 8) (x : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ :=
  ![![x 0, x 1, x 2], ![x 0, -x 2, x 1],
    ![x 0, x 2, -x 1], ![x 0, -x 1, -x 2],
    ![-x 0, x 2, x 1], ![-x 0, x 1, -x 2],
    ![-x 0, -x 1, x 2], ![-x 0, -x 2, -x 1]] f

/-- Face-local octahedron weights are nonnegative on a supporting face. -/
private lemma oct_face_bary_nonneg (f : Fin 8) (x : EuclideanSpace ℝ (Fin 3))
    (hall : ∀ g : Fin 8, x ∈ octHalf g)
    (heq : inner (𝕜 := ℝ) (octSuppN f) x = 1) (i : Fin 3) :
    0 ≤ octFaceW f x i := by
  have h0 := hall 0
  have h1 := hall 1
  have h2 := hall 2
  have h3 := hall 3
  have h4 := hall 4
  have h5 := hall 5
  have h6 := hall 6
  have h7 := hall 7
  simp only [octHalf, octSuppN, Set.mem_ofPred_eq, PiLp.inner_apply,
    Real.inner_apply, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6 h7
  fin_cases f <;> fin_cases i
  all_goals
    simp only [octFaceW, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val]
  all_goals
    simp only [octSuppN, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
      Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] at heq
  all_goals linarith

/-- Face-local octahedron weights sum to one. -/
private lemma oct_face_bary_sum (f : Fin 8) (x : EuclideanSpace ℝ (Fin 3))
    (heq : inner (𝕜 := ℝ) (octSuppN f) x = 1) :
    ∑ i, octFaceW f x i = 1 := by
  fin_cases f
  all_goals rw [Fin.sum_univ_three]
  all_goals simp [octFaceW]
  all_goals
    simp only [octSuppN, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
      Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] at heq
  all_goals linarith

/-- The face-local octahedron barycentric combination recovers the point. -/
private lemma oct_face_bary_center (f : Fin 8) (x : EuclideanSpace ℝ (Fin 3)) :
    ∑ i, octFaceW f x i • octVert (octFace f i) = x := by
  ext k
  fin_cases f <;> fin_cases k
  all_goals
    simp [Fin.sum_univ_three, octFaceW, octVert, octFace, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]

/-- A point of the H-representation on a face plane lies in that face hull. -/
private lemma oct_mem_face_of_eq (f : Fin 8) (x : EuclideanSpace ℝ (Fin 3))
    (hall : ∀ g : Fin 8, x ∈ octHalf g)
    (heq : inner (𝕜 := ℝ) (octSuppN f) x = 1) :
    x ∈ convexHull ℝ (octVert '' Set.range (octFace f)) := by
  apply mem_convexHull_of_exists_fintype (octFaceW f x)
      (fun i : Fin 3 => octVert (octFace f i))
      (oct_face_bary_nonneg f x hall heq) (oct_face_bary_sum f x heq)
  · intro i
    exact Set.mem_image_of_mem _ (Set.mem_range_self i)
  · exact oct_face_bary_center f x

/-- Octahedron frontier is covered by faces. -/
private lemma oct_cover (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ frontier (convexHull ℝ (Set.range octVert))) :
    ∃ f : Fin 8, x ∈ convexHull ℝ (octVert '' Set.range (octFace f)) := by
  classical
  have hclosed : IsClosed (convexHull ℝ (Set.range octVert)) :=
    (Set.finite_range octVert).isClosed_convexHull ℝ
  have hmem : x ∈ convexHull ℝ (Set.range octVert) := hclosed.frontier_subset hx
  have hnot : x ∉ interior (convexHull ℝ (Set.range octVert)) :=
    (mem_frontier_iff_notMem_interior hmem).mp hx
  rw [oct_hull_eq_inter] at hmem hnot
  simp only [interior_iInter_of_finite, Set.mem_iInter] at hmem hnot
  have hex : ∃ f : Fin 8, x ∉ interior (octHalf f) := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hnot hcon
  obtain ⟨f, hf⟩ := hex
  have heq := oct_half_eq_of_mem_of_not_mem_interior f x (hmem f) hf
  exact ⟨f, oct_mem_face_of_eq f x hmem heq⟩

/-- Octahedron realization exists. -/
private theorem oct_exists :
    ∃ (w : Fin 6 → EuclideanSpace ℝ (Fin 3)) (ee : Fin 12 → Fin 6 × Fin 6)
      (fv : Fin 8 → Fin 3 → Fin 6) (b : Set (EuclideanSpace ℝ (Fin 3)))
      (ll dd : ℝ),
      0 < ll ∧ 0 < dd ∧
      b = convexHull ℝ (Set.range w) ∧
      Convex ℝ b ∧
      (∀ v : Fin 6, w v ∈ frontier b) ∧
      (∀ v : Fin 6, w v ∉ convexHull ℝ (w '' {u : Fin 6 | u ≠ v})) ∧
      (Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 6, d = w i - w j}) = 3) ∧
      (∀ e : Fin 12, dist (w (ee e).1) (w (ee e).2) = ll) ∧
      (∀ (f : Fin 8) (i j : Fin 3), j.val = (i.val + 1) % 3 →
        dist (w (fv f i)) (w (fv f j)) = ll) ∧
      (∀ (f : Fin 8) (h i j : Fin 3), h.val = (i.val + 3 - 1) % 3 →
        j.val = (i.val + 1) % 3 → dist (w (fv f h)) (w (fv f j)) = dd) ∧
      (∀ f : Fin 8, Function.Injective (fv f)) ∧
      (∀ (f : Fin 8) (k : Fin 3), w (fv f k) ∉ convexHull ℝ
        (w '' (Set.range (fv f) \ {fv f k}))) ∧
      (∀ (f : Fin 8) (i₁ j₁ i₂ j₂ : Fin 3),
        j₁.val = (i₁.val + 1) % 3 →
        j₂.val = (i₂.val + 1) % 3 →
        i₁ ≠ i₂ → i₁ ≠ j₂ → j₁ ≠ i₂ → j₁ ≠ j₂ →
        Disjoint (convexHull ℝ {w (fv f i₁), w (fv f j₁)})
          (convexHull ℝ {w (fv f i₂), w (fv f j₂)})) ∧
      (∀ (f : Fin 8) (i j : Fin 3), j.val = (i.val + 1) % 3 →
        ∃ e : Fin 12, ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i)) ∧
      (∀ e : Fin 12, ∃ f : Fin 8, ∃ i j : Fin 3,
        j.val = (i.val + 1) % 3 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))) ∧
      (∀ e : Fin 12, Set.ncard {f : Fin 8 | ∃ i j : Fin 3,
        j.val = (i.val + 1) % 3 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))} = 2) ∧
      (∀ f : Fin 8, Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 3, d = w (fv f i) - w (fv f j)}) ≤ 2) ∧
      (∀ f : Fin 8, ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
        n ≠ 0 ∧ (∀ x ∈ b, inner (𝕜 := ℝ) n x ≤ c) ∧
        (∀ i : Fin 3, inner (𝕜 := ℝ) n (w (fv f i)) = c)) ∧
      (∀ e₁ e₂ : Fin 12, (ee e₁ = ee e₂ ∨ ee e₁ = (ee e₂).swap) → e₁ = e₂) ∧
      (∀ f₁ f₂ : Fin 8, Set.range (fv f₁) = Set.range (fv f₂) → f₁ = f₂) ∧
      (∀ e : Fin 12, convexHull ℝ {w (ee e).1, w (ee e).2} ⊆ frontier b) ∧
      (∀ f : Fin 8, convexHull ℝ (w '' Set.range (fv f)) ⊆ frontier b) ∧
      (∀ x ∈ frontier b, ∃ f : Fin 8,
        x ∈ convexHull ℝ (w '' Set.range (fv f))) ∧
      (∀ v : Fin 6, Set.ncard {f : Fin 8 | ∃ i : Fin 3, fv f i = v} = 4) ∧
      2 * 12 = 3 * 8 ∧ 2 * 12 = 4 * 6 ∧ (6 : ℤ) - (12 : ℤ) + (8 : ℤ) = 2 := by
  refine ⟨octVert, octEdge, octFace, convexHull ℝ (Set.range octVert),
    Real.sqrt 2, Real.sqrt 2, ?_, ?_, rfl, convex_convexHull ℝ _,
    oct_vert_frontier, oct_convex_pos, oct_finrank, oct_edge_length,
    oct_face_edge, oct_face_diag, oct_face_inj, oct_face_convex_pos, ?_,
    oct_face_edge_exists, oct_edge_face_exists, oct_two_face, ?_,
    oct_supp_exists, oct_edge_dup, oct_face_dup, oct_edge_frontier,
    oct_face_frontier, oct_cover, oct_vert_face_count, rfl, rfl, rfl⟩
  · positivity
  · positivity
  · intro f i₁ j₁ i₂ j₂ h1 h2 d1 d2 d3 d4
    exact False.elim (tet_disjoint_neg i₁ j₁ i₂ j₂ ⟨h1, h2, d1, d2, d3, d4⟩)
  · intro f
    exact finrank_triangle_le (fun i => octVert (octFace f i))

end Octahedron

section GoldenSolids

private noncomputable def gold : ℝ := Real.goldenRatio

local notation "φ" => gold

/-- Icosahedron vertices in the standard golden-ratio coordinates. -/
private noncomputable def icoVert : Fin 12 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(0 : ℝ), 1, φ], !₂[0, 1, -φ], !₂[0, -1, φ], !₂[0, -1, -φ],
    !₂[(1 : ℝ), φ, 0], !₂[1, -φ, 0], !₂[-1, φ, 0], !₂[-1, -φ, 0],
    !₂[(φ : ℝ), 0, 1], !₂[φ, 0, -1], !₂[-φ, 0, 1], !₂[-φ, 0, -1]]

/-- Icosahedron edge endpoints. -/
private def icoEdge : Fin 30 → Fin 12 × Fin 12 :=
  ![(0, 2), (0, 4), (0, 6), (0, 8), (0, 10),
    (1, 3), (1, 4), (1, 6), (1, 9), (1, 11),
    (2, 5), (2, 7), (2, 8), (2, 10),
    (3, 5), (3, 7), (3, 9), (3, 11),
    (4, 6), (4, 8), (4, 9), (5, 7), (5, 8), (5, 9),
    (6, 10), (6, 11), (7, 10), (7, 11), (8, 9), (10, 11)]

/-- Icosahedron faces as cyclic vertex lists. -/
private def icoFace : Fin 20 → Fin 3 → Fin 12 :=
  ![![0, 2, 8], ![0, 2, 10], ![0, 4, 6], ![0, 4, 8], ![0, 6, 10],
    ![1, 3, 9], ![1, 3, 11], ![1, 4, 6], ![1, 4, 9], ![1, 6, 11],
    ![2, 5, 7], ![2, 5, 8], ![2, 7, 10], ![3, 5, 7], ![3, 5, 9],
    ![3, 7, 11], ![4, 8, 9], ![5, 8, 9], ![6, 10, 11], ![7, 10, 11]]

/-- Dodecahedron vertices, scaled by `φ` so their edge length is two.
The order is dual to `icoFace`. -/
private noncomputable def dodVert : Fin 20 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 0, φ ^ 2], !₂[-1, 0, φ ^ 2], !₂[0, φ ^ 2, 1],
    !₂[(φ : ℝ), φ, φ], !₂[-φ, φ, φ], !₂[1, 0, -(φ ^ 2)],
    !₂[(-1 : ℝ), 0, -(φ ^ 2)], !₂[0, φ ^ 2, -1], !₂[φ, φ, -φ],
    !₂[(-φ : ℝ), φ, -φ], !₂[0, -(φ ^ 2), 1], !₂[φ, -φ, φ],
    !₂[(-φ : ℝ), -φ, φ], !₂[0, -(φ ^ 2), -1], !₂[φ, -φ, -φ],
    !₂[(-φ : ℝ), -φ, -φ], !₂[φ ^ 2, 1, 0], !₂[φ ^ 2, -1, 0],
    !₂[-(φ ^ 2), 1, 0], !₂[-(φ ^ 2), -1, 0]]

/-- Dodecahedron edge endpoints. -/
private def dodEdge : Fin 30 → Fin 20 × Fin 20 :=
  ![(0, 1), (0, 3), (0, 11), (1, 4), (1, 12),
    (2, 3), (2, 4), (2, 7), (3, 16), (4, 18),
    (5, 6), (5, 8), (5, 14), (6, 9), (6, 15),
    (7, 8), (7, 9), (8, 16), (9, 18),
    (10, 11), (10, 12), (10, 13), (11, 17), (12, 19),
    (13, 14), (13, 15), (14, 17), (15, 19), (16, 17), (18, 19)]

/-- Dodecahedron faces as cyclic vertex lists. -/
private def dodFace : Fin 12 → Fin 5 → Fin 20 :=
  ![![0, 1, 4, 2, 3], ![5, 6, 9, 7, 8], ![0, 1, 12, 10, 11],
    ![5, 6, 15, 13, 14], ![2, 3, 16, 8, 7], ![10, 11, 17, 14, 13],
    ![2, 4, 18, 9, 7], ![10, 12, 19, 15, 13], ![0, 3, 16, 17, 11],
    ![5, 8, 16, 17, 14], ![1, 4, 18, 19, 12], ![6, 9, 18, 19, 15]]

section Icosahedron

/-- The common support value for the dual golden-ratio coordinate systems. -/
private noncomputable def goldC : ℝ := 2 * φ + 1

private lemma gold_sq : φ ^ 2 = φ + 1 := by
  exact Real.goldenRatio_sq

private lemma gold_pos : 0 < φ := Real.goldenRatio_pos

private lemma gold_one_lt : 1 < φ := Real.one_lt_goldenRatio

private lemma gold_cube : φ ^ 3 = 2 * φ + 1 := by
  calc
    φ ^ 3 = φ * φ ^ 2 := by ring
    _ = φ * (φ + 1) := by rw [gold_sq]
    _ = 2 * φ + 1 := by nlinarith [gold_sq]

private lemma gold_four : φ ^ 4 = 3 * φ + 2 := by
  calc
    φ ^ 4 = φ * φ ^ 3 := by ring
    _ = φ * (2 * φ + 1) := by rw [gold_cube]
    _ = 3 * φ + 2 := by nlinarith [gold_sq]

private lemma gold_sq_mul (x : ℝ) : φ ^ 2 * x = (φ + 1) * x := by
  rw [gold_sq]

private lemma gold_cube_mul (x : ℝ) : φ ^ 3 * x = (2 * φ + 1) * x := by
  rw [gold_cube]

private lemma goldC_pos : 0 < goldC := by
  rw [goldC]
  nlinarith [gold_pos]

/-- Supporting-plane normals for the icosahedron faces. -/
private noncomputable def icoSuppN : Fin 20 → EuclideanSpace ℝ (Fin 3) := dodVert

/-- For each icosahedron vertex, a face containing it. -/
private def icoVertFace : Fin 12 → Fin 20 :=
  ![0, 5, 0, 5, 2, 10, 2, 10, 0, 5, 1, 6]

/-- Index witnessing the assigned icosahedron vertex-face membership. -/
private def icoVertFaceIdx : Fin 12 → Fin 3 :=
  ![0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]

/-- The two faces containing each icosahedron edge. -/
private def icoEdgeFaces : Fin 30 → Fin 20 × Fin 20 :=
  ![(0, 1), (2, 3), (2, 4), (0, 3), (1, 4),
    (5, 6), (7, 8), (7, 9), (5, 8), (6, 9),
    (10, 11), (10, 12), (0, 11), (1, 12),
    (13, 14), (13, 15), (5, 14), (6, 15),
    (2, 7), (3, 16), (8, 16), (10, 13), (11, 17), (14, 17),
    (4, 18), (9, 18), (12, 19), (15, 19), (16, 17), (18, 19)]

/-- The five faces containing each icosahedron vertex. -/
private def icoVertFaces : Fin 12 → Fin 5 → Fin 20 :=
  ![![0, 1, 2, 3, 4], ![5, 6, 7, 8, 9], ![0, 1, 10, 11, 12],
    ![5, 6, 13, 14, 15], ![2, 3, 7, 8, 16], ![10, 11, 13, 14, 17],
    ![2, 4, 7, 9, 18], ![10, 12, 13, 15, 19], ![0, 3, 11, 16, 17],
    ![5, 8, 14, 16, 17], ![1, 4, 12, 18, 19], ![6, 9, 15, 18, 19]]

/-- Icosahedron edge lengths. -/
private lemma ico_edge_length (e : Fin 30) :
    dist (icoVert (icoEdge e).1) (icoVert (icoEdge e).2) = 2 := by
  fin_cases e
  all_goals
    simp only [icoVert, icoEdge, EuclideanSpace.dist_eq, Fin.sum_univ_three,
      Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val,
      Real.dist_eq]
  all_goals rw [sq_abs, sq_abs, sq_abs]
  all_goals ring_nf
  all_goals first
    | exact cube_sqrt4
    | rw [show 2 - φ * 2 + φ ^ 2 * 2 = 4 by nlinarith [gold_sq]]
      exact cube_sqrt4

/-- Icosahedron faces are injective. -/
private lemma ico_face_inj (f : Fin 20) : Function.Injective (icoFace f) := by
  fin_cases f <;> decide

/-- Every distinct pair of vertices of an icosahedron face is a graph edge. -/
private lemma ico_face_pair_edge (f : Fin 20) (i j : Fin 3) (h : i ≠ j) :
    ∃ e : Fin 30, icoEdge e = (icoFace f i, icoFace f j) ∨
      icoEdge e = (icoFace f j, icoFace f i) := by
  fin_cases f <;> fin_cases i <;> fin_cases j
  all_goals try (exact False.elim (h rfl))
  all_goals decide

/-- Distinct vertices of an icosahedron face are at distance two. -/
private lemma ico_face_pair_length (f : Fin 20) (i j : Fin 3) (h : i ≠ j) :
    dist (icoVert (icoFace f i)) (icoVert (icoFace f j)) = 2 := by
  obtain ⟨e, he | he⟩ := ico_face_pair_edge f i j h
  · have hlen := ico_edge_length e
    rw [he] at hlen
    exact hlen
  · have hlen := ico_edge_length e
    rw [he] at hlen
    rw [dist_comm]
    exact hlen

/-- Icosahedron face edges. -/
private lemma ico_face_edge (f : Fin 20) (i j : Fin 3)
    (h : j.val = (i.val + 1) % 3) :
    dist (icoVert (icoFace f i)) (icoVert (icoFace f j)) = 2 := by
  fin_cases i <;> fin_cases j
  all_goals try (norm_num at h)
  all_goals exact ico_face_pair_length f _ _ (by decide)

/-- The opposite-neighbor diagonal in each triangular icosahedron face. -/
private lemma ico_face_diag (f : Fin 20) (h i j : Fin 3)
    (hh : h.val = (i.val + 3 - 1) % 3)
    (hj : j.val = (i.val + 1) % 3) :
    dist (icoVert (icoFace f h)) (icoVert (icoFace f j)) = 2 := by
  fin_cases h <;> fin_cases i <;> fin_cases j
  all_goals try (norm_num at hh)
  all_goals try (norm_num at hj)
  all_goals exact ico_face_pair_length f _ _ (by decide)

/-- Every icosahedron face edge is a graph edge. -/
private lemma ico_face_edge_exists (f : Fin 20) (i j : Fin 3)
    (h : j.val = (i.val + 1) % 3) :
    ∃ e : Fin 30, icoEdge e = (icoFace f i, icoFace f j) ∨
      icoEdge e = (icoFace f j, icoFace f i) := by
  fin_cases i <;> fin_cases j
  all_goals try (norm_num at h)
  all_goals exact ico_face_pair_edge f _ _ (by decide)

/-- Every icosahedron graph edge is a face edge. -/
private lemma ico_edge_face_exists (e : Fin 30) :
    ∃ f : Fin 20, ∃ i j : Fin 3, j.val = (i.val + 1) % 3 ∧
      (icoEdge e = (icoFace f i, icoFace f j) ∨
        icoEdge e = (icoFace f j, icoFace f i)) := by
  fin_cases e <;> decide

/-- Icosahedron edges are duplicate-free. -/
private lemma ico_edge_dup (e₁ e₂ : Fin 30)
    (h : icoEdge e₁ = icoEdge e₂ ∨ icoEdge e₁ = (icoEdge e₂).swap) :
    e₁ = e₂ := by
  revert h
  fin_cases e₁ <;> fin_cases e₂ <;> decide

/-- Icosahedron faces are duplicate-free. -/
private lemma ico_face_dup (f₁ f₂ : Fin 20)
    (h : Set.range (icoFace f₁) = Set.range (icoFace f₂)) : f₁ = f₂ := by
  have hrange : ∀ f : Fin 20, Set.range (icoFace f) =
      ↑(Finset.univ.image (icoFace f)) := by
    intro f
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [hrange f₁, hrange f₂] at h
  have hfin : Finset.univ.image (icoFace f₁) =
      Finset.univ.image (icoFace f₂) := Finset.coe_injective h
  have hne : ∀ a b : Fin 20, a ≠ b →
      Finset.univ.image (icoFace a) ≠ Finset.univ.image (icoFace b) := by decide
  by_cases heq : f₁ = f₂
  · exact heq
  · exact False.elim (hne f₁ f₂ heq hfin)

/-- Each icosahedron edge lies in exactly two faces. -/
private lemma ico_two_face (e : Fin 30) :
    Set.ncard {f : Fin 20 | ∃ i j : Fin 3, j.val = (i.val + 1) % 3 ∧
      (icoEdge e = (icoFace f i, icoFace f j) ∨
        icoEdge e = (icoFace f j, icoFace f i))} = 2 := by
  have hset : ∀ e : Fin 30, {f : Fin 20 | ∃ i j : Fin 3,
      j.val = (i.val + 1) % 3 ∧
      (icoEdge e = (icoFace f i, icoFace f j) ∨
        icoEdge e = (icoFace f j, icoFace f i))} =
      {(icoEdgeFaces e).1, (icoEdgeFaces e).2} := by
    intro e
    ext f
    fin_cases e <;> fin_cases f <;> decide
  have hne : ∀ e : Fin 30, (icoEdgeFaces e).1 ≠ (icoEdgeFaces e).2 := by decide
  rw [hset e]
  exact Set.ncard_pair (hne e)

/-- Each icosahedron vertex lies in exactly five faces. -/
private lemma ico_vert_face_count (v : Fin 12) :
    Set.ncard {f : Fin 20 | ∃ i : Fin 3, icoFace f i = v} = 5 := by
  have hset : ∀ v : Fin 12, {f : Fin 20 | ∃ i : Fin 3, icoFace f i = v} =
      Set.range (icoVertFaces v) := by
    intro u
    ext f
    fin_cases u <;> fin_cases f <;> decide
  have hinj : ∀ u : Fin 12, Function.Injective (icoVertFaces u) := by
    intro u
    fin_cases u <;> decide
  rw [hset v, Set.ncard_range_of_injective (hinj v)]
  exact Nat.card_fin 5

/-- Supporting-plane upper bounds for icosahedron faces. -/
private lemma ico_supp_le (f : Fin 20) (v : Fin 12) :
    inner (𝕜 := ℝ) (icoSuppN f) (icoVert v) ≤ goldC := by
  fin_cases f <;> fin_cases v
  all_goals
    simp only [icoSuppN, dodVert, icoVert, PiLp.inner_apply, Real.inner_apply,
      Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val, goldC]
  all_goals ring_nf
  all_goals nlinarith [gold_sq, gold_cube, gold_pos]

/-- Supporting-plane equalities on icosahedron face vertices. -/
private lemma ico_supp_eq (f : Fin 20) (i : Fin 3) :
    inner (𝕜 := ℝ) (icoSuppN f) (icoVert (icoFace f i)) = goldC := by
  fin_cases f <;> fin_cases i
  all_goals
    simp only [icoSuppN, dodVert, icoVert, icoFace, PiLp.inner_apply,
      Real.inner_apply, Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue,
      Fin.mk_zero, Fin.mk_one, Matrix.cons_val, goldC]
  all_goals ring_nf
  all_goals nlinarith [gold_sq, gold_cube]

/-- Icosahedron supporting normals are nonzero. -/
private lemma ico_supp_ne (f : Fin 20) : icoSuppN f ≠ 0 := by
  intro hzero
  have h := ico_supp_eq f 0
  rw [hzero] at h
  simp only [inner_zero_left] at h
  nlinarith [goldC_pos]

/-- Supporting planes exist for icosahedron faces. -/
private lemma ico_supp_exists (f : Fin 20) :
    ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
      n ≠ 0 ∧
      (∀ x ∈ convexHull ℝ (Set.range icoVert), inner (𝕜 := ℝ) n x ≤ c) ∧
      (∀ i : Fin 3, inner (𝕜 := ℝ) n (icoVert (icoFace f i)) = c) := by
  refine ⟨icoSuppN f, goldC, ico_supp_ne f, ?_, fun i => ico_supp_eq f i⟩
  intro x hx
  apply inner_le_of_mem_convexHull _ hx
  intro s hs
  obtain ⟨v, rfl⟩ := hs
  exact ico_supp_le f v

/-- Icosahedron vertices are in convex position. -/
private lemma ico_convex_pos (v : Fin 12) :
    icoVert v ∉ convexHull ℝ (icoVert '' {u : Fin 12 | u ≠ v}) := by
  apply not_mem_convexHull_of_separation (n := icoVert v) (c := φ)
  · intro s hs
    obtain ⟨u, hu, rfl⟩ := hs
    simp only [Set.mem_ofPred_eq] at hu
    fin_cases v <;> fin_cases u
    all_goals try (exact False.elim (hu rfl))
    all_goals
      simp only [icoVert, PiLp.inner_apply, Real.inner_apply,
        Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero,
        Fin.mk_one, Matrix.cons_val]
    all_goals ring_nf
    all_goals nlinarith [gold_sq, gold_pos]
  · fin_cases v
    all_goals
      simp only [icoVert, PiLp.inner_apply, Real.inner_apply,
        Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero,
        Fin.mk_one, Matrix.cons_val]
    all_goals ring_nf
    all_goals nlinarith [gold_sq, gold_pos]

/-- Icosahedron face vertices are in convex position within each face. -/
private lemma ico_face_convex_pos (f : Fin 20) (k : Fin 3) :
    icoVert (icoFace f k) ∉ convexHull ℝ
      (icoVert '' (Set.range (icoFace f) \ {icoFace f k})) := by
  intro hmem
  apply ico_convex_pos (icoFace f k)
  apply convexHull_mono ?_ hmem
  rintro z ⟨u, hu, rfl⟩
  refine ⟨u, ?_, rfl⟩
  simp only [Set.mem_ofPred_eq]
  simpa only [Set.mem_singleton_iff] using hu.2

/-- Three vertex differences spanning the icosahedron. -/
private noncomputable def icoD : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![icoVert 0 - icoVert 1, icoVert 4 - icoVert 5,
    icoVert 8 - icoVert 10]

private lemma ico_gram_det : (Matrix.gram ℝ icoD).det = 64 * φ ^ 6 := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.gram_apply, icoD, icoVert, PiLp.inner_apply,
    Real.inner_apply, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val,
    PiLp.sub_apply]
  ring

private lemma icoD_indep : LinearIndependent ℝ icoD := by
  rw [← Matrix.det_gram_ne_zero_iff_linearIndependent, ico_gram_det]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 6 (ne_of_gt gold_pos))

private lemma ico_span_top : Submodule.span ℝ (Set.range icoD) = ⊤ :=
  LinearIndependent.span_eq_top_of_card_eq_finrank icoD_indep
    (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])

/-- Full-dimensionality for the icosahedron vertex set. -/
private lemma ico_finrank : Module.finrank ℝ (Submodule.span ℝ
    {d : EuclideanSpace ℝ (Fin 3) | ∃ i j : Fin 12,
      d = icoVert i - icoVert j}) = 3 := by
  have hle : Submodule.span ℝ (Set.range icoD) ≤ Submodule.span ℝ
      {d : EuclideanSpace ℝ (Fin 3) | ∃ i j : Fin 12,
        d = icoVert i - icoVert j} := by
    apply Submodule.span_mono
    rintro x ⟨k, rfl⟩
    fin_cases k
    · exact ⟨0, 1, rfl⟩
    · exact ⟨4, 5, rfl⟩
    · exact ⟨8, 10, rfl⟩
  rw [ico_span_top] at hle
  have hspan : Submodule.span ℝ
      {d : EuclideanSpace ℝ (Fin 3) | ∃ i j : Fin 12,
        d = icoVert i - icoVert j} = ⊤ := top_le_iff.mp hle
  have hfin : Module.finrank ℝ
      ↥(⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) :=
    Submodule.topEquiv.finrank_eq
  rw [hspan, hfin, finrank_euclideanSpace_fin]

/-- Each icosahedron vertex lies in its assigned face. -/
private lemma ico_vert_mem_face :
    ∀ v : Fin 12, icoFace (icoVertFace v) (icoVertFaceIdx v) = v := by
  decide

/-- Icosahedron vertices lie in the frontier. -/
private lemma ico_vert_frontier (v : Fin 12) :
    icoVert v ∈ frontier (convexHull ℝ (Set.range icoVert)) := by
  have hmem : icoVert v ∈ convexHull ℝ (Set.range icoVert) :=
    subset_convexHull ℝ _ (Set.mem_range_self v)
  have hle : ∀ x ∈ convexHull ℝ (Set.range icoVert),
      inner (𝕜 := ℝ) (icoSuppN (icoVertFace v)) x ≤ goldC := by
    intro x hx
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact ico_supp_le _ u
  have heq : inner (𝕜 := ℝ) (icoSuppN (icoVertFace v)) (icoVert v) =
      goldC := by
    have h := ico_supp_eq (icoVertFace v) (icoVertFaceIdx v)
    rw [ico_vert_mem_face v] at h
    exact h
  exact mem_frontier_of_support hmem hle heq (ico_supp_ne _)

/-- Icosahedron edge hulls lie in the frontier. -/
private lemma ico_edge_frontier (e : Fin 30) :
    convexHull ℝ {icoVert (icoEdge e).1, icoVert (icoEdge e).2} ⊆
      frontier (convexHull ℝ (Set.range icoVert)) := by
  obtain ⟨f, i, j, _, heq⟩ := ico_edge_face_exists e
  have hsub : ({icoVert (icoEdge e).1, icoVert (icoEdge e).2} :
      Set (EuclideanSpace ℝ (Fin 3))) ⊆ Set.range icoVert := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    cases hz with
    | inl h => rw [h]; exact Set.mem_range_self _
    | inr h => rw [h]; exact Set.mem_range_self _
  have hle : ∀ x ∈ convexHull ℝ (Set.range icoVert),
      inner (𝕜 := ℝ) (icoSuppN f) x ≤ goldC := by
    intro x hx
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact ico_supp_le f u
  have ha : inner (𝕜 := ℝ) (icoSuppN f) (icoVert (icoEdge e).1) =
      goldC := by
    cases heq with
    | inl h =>
      have h1 : (icoEdge e).1 = icoFace f i := congrArg Prod.fst h
      rw [h1]
      exact ico_supp_eq f i
    | inr h =>
      have h1 : (icoEdge e).1 = icoFace f j := congrArg Prod.fst h
      rw [h1]
      exact ico_supp_eq f j
  have hb : inner (𝕜 := ℝ) (icoSuppN f) (icoVert (icoEdge e).2) =
      goldC := by
    cases heq with
    | inl h =>
      have h2 : (icoEdge e).2 = icoFace f j := congrArg Prod.snd h
      rw [h2]
      exact ico_supp_eq f j
    | inr h =>
      have h2 : (icoEdge e).2 = icoFace f i := congrArg Prod.snd h
      rw [h2]
      exact ico_supp_eq f i
  intro y hy
  have hyB : y ∈ convexHull ℝ (Set.range icoVert) := convexHull_mono hsub hy
  have heq_y : inner (𝕜 := ℝ) (icoSuppN f) y = goldC := by
    apply inner_eq_of_mem_convexHull _ hy
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    cases hs with
    | inl h => rw [h]; exact ha
    | inr h => rw [h]; exact hb
  exact mem_frontier_of_support hyB hle heq_y (ico_supp_ne f)

/-- Icosahedron face hulls lie in the frontier. -/
private lemma ico_face_frontier (f : Fin 20) :
    convexHull ℝ (icoVert '' Set.range (icoFace f)) ⊆
      frontier (convexHull ℝ (Set.range icoVert)) := by
  have hsub : icoVert '' Set.range (icoFace f) ⊆ Set.range icoVert := by
    rintro z ⟨x, ⟨i, rfl⟩, rfl⟩
    exact Set.mem_range_self _
  have hle : ∀ x ∈ convexHull ℝ (Set.range icoVert),
      inner (𝕜 := ℝ) (icoSuppN f) x ≤ goldC := by
    intro x hx
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact ico_supp_le f u
  intro y hy
  have hyB : y ∈ convexHull ℝ (Set.range icoVert) := convexHull_mono hsub hy
  have heq_y : inner (𝕜 := ℝ) (icoSuppN f) y = goldC := by
    apply inner_eq_of_mem_convexHull _ hy
    intro s hs
    obtain ⟨x, ⟨i, rfl⟩, rfl⟩ := hs
    exact ico_supp_eq f i
  exact mem_frontier_of_support hyB hle heq_y (ico_supp_ne f)

/-- The halfspace determined by an icosahedron face. -/
private def icoHalf (f : Fin 20) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | inner (𝕜 := ℝ) (icoSuppN f) x ≤ goldC}

/-- Across each edge opposite a local face vertex, the adjacent face. -/
private def icoFaceOpp : Fin 20 → Fin 3 → Fin 20 :=
  ![![11, 3, 1], ![12, 4, 0], ![7, 4, 3], ![16, 0, 2],
    ![18, 1, 2], ![14, 8, 6], ![15, 9, 5], ![2, 9, 8],
    ![16, 5, 7], ![18, 6, 7], ![13, 12, 11], ![17, 0, 10],
    ![19, 1, 10], ![10, 15, 14], ![17, 5, 13], ![19, 6, 13],
    ![17, 8, 3], ![16, 14, 11], ![19, 9, 4], ![18, 15, 12]]

private lemma gold_face_threshold :
    goldC - (φ - 1) * goldC = φ := by
  rw [goldC]
  nlinarith [gold_sq, gold_cube]

private lemma gold_face_coefficient : (φ - 1) * goldC = φ ^ 2 := by
  nlinarith [gold_face_threshold, gold_sq]

private lemma gold_face_coefficient_mul (x : ℝ) :
    ((φ - 1) * goldC) * x = φ ^ 2 * x := by
  rw [gold_face_coefficient]

/-- A face vertex is the difference of its face normal and a positive
multiple of the normal across the opposite edge. -/
private lemma ico_face_normal_relation (f : Fin 20) (i : Fin 3) :
    icoVert (icoFace f i) =
      icoSuppN f - (φ - 1) • icoSuppN (icoFaceOpp f i) := by
  ext k
  fin_cases f <;> fin_cases i <;> fin_cases k
  all_goals
    simp only [icoVert, icoFace, icoSuppN, dodVert, icoFaceOpp,
      PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Fin.reduceFinMk,
      Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val]
  all_goals ring_nf
  all_goals nlinarith [gold_sq]

private lemma ico_face_inner_relation (f : Fin 20) (i : Fin 3)
    (x : EuclideanSpace ℝ (Fin 3)) :
    inner (𝕜 := ℝ) (icoVert (icoFace f i)) x =
      inner (𝕜 := ℝ) (icoSuppN f) x -
        (φ - 1) * inner (𝕜 := ℝ) (icoSuppN (icoFaceOpp f i)) x := by
  rw [ico_face_normal_relation]
  simp [inner_sub_left, inner_smul_left]

/-- The three face vertices sum to a multiple of the face normal. -/
private lemma ico_face_vertex_sum (f : Fin 20) :
    ∑ i, icoVert (icoFace f i) = φ • icoSuppN f := by
  ext k
  fin_cases f <;> fin_cases k
  all_goals
    simp only [Fin.sum_univ_three, icoVert, icoFace, icoSuppN, dodVert,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.reduceFinMk,
      Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val]
  all_goals ring_nf
  all_goals nlinarith [gold_sq, gold_cube]

set_option maxHeartbeats 1000000 in
-- Expanding the 20 coordinate frames exceeds the default elaboration budget.
/-- The frame operator of each triangular face. -/
private lemma ico_face_frame (f : Fin 20) (x : EuclideanSpace ℝ (Fin 3)) :
    ∑ i, inner (𝕜 := ℝ) (icoVert (icoFace f i)) x •
        icoVert (icoFace f i) =
      2 • x + ((φ - 1) * inner (𝕜 := ℝ) (icoSuppN f) x) • icoSuppN f := by
  ext k
  fin_cases f <;> fin_cases k
  all_goals
    simp only [Fin.sum_univ_three, icoVert, icoFace, icoSuppN, dodVert,
      PiLp.inner_apply, Real.inner_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val]
  all_goals ring_nf
  all_goals nlinarith [gold_sq, gold_cube, gold_sq_mul (x 0),
    gold_sq_mul (x 1), gold_sq_mul (x 2), gold_cube_mul (x 0),
    gold_cube_mul (x 1), gold_cube_mul (x 2)]

/-- Face-local barycentric weights for the icosahedron. -/
private noncomputable def icoFaceW (f : Fin 20)
    (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) : ℝ :=
  (inner (𝕜 := ℝ) (icoVert (icoFace f i)) x - φ) / 2

/-- Face-local icosahedron weights are nonnegative on a supporting face. -/
private lemma ico_face_bary_nonneg (f : Fin 20)
    (x : EuclideanSpace ℝ (Fin 3))
    (hall : ∀ g : Fin 20, x ∈ icoHalf g)
    (heq : inner (𝕜 := ℝ) (icoSuppN f) x = goldC) (i : Fin 3) :
    0 ≤ icoFaceW f x i := by
  have hg := hall (icoFaceOpp f i)
  simp only [icoHalf, Set.mem_ofPred_eq] at hg
  rw [icoFaceW]
  apply div_nonneg
  · apply sub_nonneg.mpr
    rw [ico_face_inner_relation, heq]
    have hcoeff : 0 ≤ φ - 1 := le_of_lt (sub_pos.mpr gold_one_lt)
    have hmul := mul_le_mul_of_nonneg_left hg hcoeff
    calc
      φ = goldC - (φ - 1) * goldC := gold_face_threshold.symm
      _ ≤ goldC - (φ - 1) *
          inner (𝕜 := ℝ) (icoSuppN (icoFaceOpp f i)) x :=
        sub_le_sub_left hmul goldC
  · norm_num

/-- Face-local icosahedron weights sum to one. -/
private lemma ico_face_bary_sum (f : Fin 20)
    (x : EuclideanSpace ℝ (Fin 3))
    (heq : inner (𝕜 := ℝ) (icoSuppN f) x = goldC) :
    ∑ i, icoFaceW f x i = 1 := by
  have heqφ := congrArg (fun t : ℝ => φ * t) heq
  rw [Fin.sum_univ_three]
  fin_cases f
  all_goals
    simp only [icoFaceW, icoSuppN, dodVert, icoVert, icoFace,
      PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
      Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val, goldC] at heq heqφ ⊢
  all_goals ring_nf at heq heqφ ⊢
  all_goals nlinarith [gold_sq, gold_cube, gold_sq_mul (x 0),
    gold_sq_mul (x 1), gold_sq_mul (x 2), gold_cube_mul (x 0),
    gold_cube_mul (x 1), gold_cube_mul (x 2)]

/-- The face-local icosahedron barycentric combination recovers the point. -/
private lemma ico_face_bary_center (f : Fin 20)
    (x : EuclideanSpace ℝ (Fin 3))
    (heq : inner (𝕜 := ℝ) (icoSuppN f) x = goldC) :
    ∑ i, icoFaceW f x i • icoVert (icoFace f i) = x := by
  have hframe := ico_face_frame f x
  have hsum := ico_face_vertex_sum f
  ext k
  have hframek := congrArg (fun y : EuclideanSpace ℝ (Fin 3) => y k) hframe
  have hsumk := congrArg (fun y : EuclideanSpace ℝ (Fin 3) => y k) hsum
  have hsumkφ := congrArg (fun t : ℝ => φ * t) hsumk
  have hcoeffk := gold_face_coefficient_mul ((icoSuppN f) k)
  rw [heq] at hframek
  fin_cases k
  all_goals
    simp only [Fin.sum_univ_three, icoFaceW, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, Fin.reduceFinMk, Fin.isValue,
      Fin.mk_zero, Fin.mk_one] at hframek hsumk hsumkφ hcoeffk ⊢
  all_goals ring_nf at hframek hsumkφ hcoeffk ⊢
  all_goals nlinarith [hframek, hsumk, hsumkφ, hcoeffk]

/-- A point of all halfspaces on a face plane lies in that face hull. -/
private lemma ico_mem_face_of_eq (f : Fin 20)
    (x : EuclideanSpace ℝ (Fin 3))
    (hall : ∀ g : Fin 20, x ∈ icoHalf g)
    (heq : inner (𝕜 := ℝ) (icoSuppN f) x = goldC) :
    x ∈ convexHull ℝ (icoVert '' Set.range (icoFace f)) := by
  apply mem_convexHull_of_exists_fintype (icoFaceW f x)
      (fun i : Fin 3 => icoVert (icoFace f i))
      (ico_face_bary_nonneg f x hall heq) (ico_face_bary_sum f x heq)
  · intro i
    exact Set.mem_image_of_mem _ (Set.mem_range_self i)
  · exact ico_face_bary_center f x heq

/-- The origin lies in the icosahedron hull. -/
private lemma ico_zero_mem :
    0 ∈ convexHull ℝ (Set.range icoVert) := by
  have h0 : icoVert 0 ∈ convexHull ℝ (Set.range icoVert) :=
    subset_convexHull ℝ _ (Set.mem_range_self 0)
  have h3 : icoVert 3 ∈ convexHull ℝ (Set.range icoVert) :=
    subset_convexHull ℝ _ (Set.mem_range_self 3)
  have ht : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hline := (convex_convexHull ℝ (Set.range icoVert)).lineMap_mem h0 h3 ht
  rw [AffineMap.lineMap_apply_module] at hline
  have hmid : (1 - (1 / 2 : ℝ)) • icoVert 0 +
      (1 / 2 : ℝ) • icoVert 3 = 0 := by
    ext k
    fin_cases k <;> simp [icoVert] <;> ring
  rw [hmid] at hline
  exact hline

/-- Some icosahedron face normal is positive on every nonzero direction. -/
private lemma ico_normals_positive (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ≠ 0) : ∃ f : Fin 20, 0 < inner (𝕜 := ℝ) (icoSuppN f) x := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have h0 := hcon 0
  have h1 := hcon 1
  have h2 := hcon 2
  have h5 := hcon 5
  have h6 := hcon 6
  have h13 := hcon 13
  simp only [icoSuppN, dodVert, PiLp.inner_apply, Real.inner_apply,
    Fin.sum_univ_three, Fin.isValue, Matrix.cons_val] at h0 h1 h2 h5 h6 h13
  ring_nf at h0 h1 h2 h5 h6 h13
  have ha : x 0 + φ ^ 2 * x 2 = 0 := by linarith
  have hb : -x 0 + φ ^ 2 * x 2 = 0 := by linarith
  have hx0 : x 0 = 0 := by linarith
  have hzprod : φ ^ 2 * x 2 = 0 := by linarith
  have hz : x 2 = 0 :=
    (mul_eq_zero.mp hzprod).resolve_left (pow_ne_zero 2 (ne_of_gt gold_pos))
  have hc : φ ^ 2 * x 1 + x 2 = 0 := by linarith
  have hyprod : φ ^ 2 * x 1 = 0 := by linarith
  have hy : x 1 = 0 :=
    (mul_eq_zero.mp hyprod).resolve_left (pow_ne_zero 2 (ne_of_gt gold_pos))
  apply hx
  ext k
  fin_cases k
  · exact hx0
  · exact hy
  · exact hz

/-- The icosahedron H-representation is contained in its convex hull. -/
private lemma ico_inter_subset_hull :
    (⋂ f, icoHalf f) ⊆ convexHull ℝ (Set.range icoVert) := by
  intro x hx
  simp only [Set.mem_iInter, icoHalf, Set.mem_ofPred_eq] at hx
  apply mem_of_mem_all_halfspaces icoSuppN goldC goldC_pos
      (convexHull ℝ (Set.range icoVert)) (convex_convexHull ℝ _)
      ico_zero_mem ico_normals_positive ?_ hx
  intro f y hall heq
  apply convexHull_mono ?_ (ico_mem_face_of_eq f y ?_ heq)
  · rintro z ⟨u, ⟨i, rfl⟩, rfl⟩
    exact Set.mem_range_self _
  · intro g
    simpa only [icoHalf, Set.mem_ofPred_eq] using hall g

/-- The icosahedron convex hull equals its H-representation. -/
private lemma ico_hull_eq_inter :
    convexHull ℝ (Set.range icoVert) = ⋂ f, icoHalf f := by
  apply le_antisymm
  · intro x hx
    simp only [Set.mem_iInter]
    intro f
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨v, rfl⟩ := hs
    exact ico_supp_le f v
  · exact ico_inter_subset_hull

/-- A halfspace point outside its interior achieves equality. -/
private lemma ico_half_eq_of_mem_of_not_mem_interior (f : Fin 20)
    (x : EuclideanSpace ℝ (Fin 3)) (hmem : x ∈ icoHalf f)
    (hnot : x ∉ interior (icoHalf f)) :
    inner (𝕜 := ℝ) (icoSuppN f) x = goldC := by
  simp only [icoHalf, Set.mem_ofPred_eq] at hmem
  by_contra hne
  have hlt : inner (𝕜 := ℝ) (icoSuppN f) x < goldC :=
    lt_of_le_of_ne hmem hne
  have hcont : Continuous
      (fun y : EuclideanSpace ℝ (Fin 3) => inner (𝕜 := ℝ) (icoSuppN f) y) :=
    continuous_const.inner continuous_id
  have hopen : IsOpen
      {y : EuclideanSpace ℝ (Fin 3) |
        inner (𝕜 := ℝ) (icoSuppN f) y < goldC} := by
    have hIio : IsOpen (Set.Iio goldC) := isOpen_Iio
    have hpre := hIio.preimage hcont
    simpa only [Set.preimage, Set.mem_Iio] using hpre
  have hsub : {y : EuclideanSpace ℝ (Fin 3) |
      inner (𝕜 := ℝ) (icoSuppN f) y < goldC} ⊆ icoHalf f := by
    intro y hy
    simp only [icoHalf, Set.mem_ofPred_eq, Set.mem_ofPred_eq] at hy ⊢
    exact hy.le
  exact hnot ((hopen.subset_interior_iff).mpr hsub hlt)

/-- Icosahedron frontier is covered by faces. -/
private lemma ico_cover (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ frontier (convexHull ℝ (Set.range icoVert))) :
    ∃ f : Fin 20, x ∈ convexHull ℝ (icoVert '' Set.range (icoFace f)) := by
  classical
  have hclosed : IsClosed (convexHull ℝ (Set.range icoVert)) :=
    (Set.finite_range icoVert).isClosed_convexHull ℝ
  have hmem : x ∈ convexHull ℝ (Set.range icoVert) := hclosed.frontier_subset hx
  have hnot : x ∉ interior (convexHull ℝ (Set.range icoVert)) :=
    (mem_frontier_iff_notMem_interior hmem).mp hx
  rw [ico_hull_eq_inter] at hmem hnot
  simp only [interior_iInter_of_finite, Set.mem_iInter] at hmem hnot
  have hex : ∃ f : Fin 20, x ∉ interior (icoHalf f) := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hnot hcon
  obtain ⟨f, hf⟩ := hex
  have heq := ico_half_eq_of_mem_of_not_mem_interior f x (hmem f) hf
  exact ⟨f, ico_mem_face_of_eq f x hmem heq⟩

/-- Icosahedron realization exists. -/
private theorem ico_exists :
    ∃ (w : Fin 12 → EuclideanSpace ℝ (Fin 3))
      (ee : Fin 30 → Fin 12 × Fin 12)
      (fv : Fin 20 → Fin 3 → Fin 12)
      (b : Set (EuclideanSpace ℝ (Fin 3))) (ll dd : ℝ),
      0 < ll ∧ 0 < dd ∧
      b = convexHull ℝ (Set.range w) ∧
      Convex ℝ b ∧
      (∀ v : Fin 12, w v ∈ frontier b) ∧
      (∀ v : Fin 12, w v ∉ convexHull ℝ (w '' {u : Fin 12 | u ≠ v})) ∧
      (Module.finrank ℝ (Submodule.span ℝ
        {d : EuclideanSpace ℝ (Fin 3) | ∃ i j : Fin 12, d = w i - w j}) = 3) ∧
      (∀ e : Fin 30, dist (w (ee e).1) (w (ee e).2) = ll) ∧
      (∀ (f : Fin 20) (i j : Fin 3), j.val = (i.val + 1) % 3 →
        dist (w (fv f i)) (w (fv f j)) = ll) ∧
      (∀ (f : Fin 20) (h i j : Fin 3), h.val = (i.val + 3 - 1) % 3 →
        j.val = (i.val + 1) % 3 →
        dist (w (fv f h)) (w (fv f j)) = dd) ∧
      (∀ f : Fin 20, Function.Injective (fv f)) ∧
      (∀ (f : Fin 20) (k : Fin 3), w (fv f k) ∉ convexHull ℝ
        (w '' (Set.range (fv f) \ {fv f k}))) ∧
      (∀ (f : Fin 20) (i₁ j₁ i₂ j₂ : Fin 3),
        j₁.val = (i₁.val + 1) % 3 →
        j₂.val = (i₂.val + 1) % 3 →
        i₁ ≠ i₂ → i₁ ≠ j₂ → j₁ ≠ i₂ → j₁ ≠ j₂ →
        Disjoint (convexHull ℝ {w (fv f i₁), w (fv f j₁)})
          (convexHull ℝ {w (fv f i₂), w (fv f j₂)})) ∧
      (∀ (f : Fin 20) (i j : Fin 3), j.val = (i.val + 1) % 3 →
        ∃ e : Fin 30, ee e = (fv f i, fv f j) ∨
          ee e = (fv f j, fv f i)) ∧
      (∀ e : Fin 30, ∃ f : Fin 20, ∃ i j : Fin 3,
        j.val = (i.val + 1) % 3 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))) ∧
      (∀ e : Fin 30, Set.ncard {f : Fin 20 | ∃ i j : Fin 3,
        j.val = (i.val + 1) % 3 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))} = 2) ∧
      (∀ f : Fin 20, Module.finrank ℝ (Submodule.span ℝ
        {d : EuclideanSpace ℝ (Fin 3) |
          ∃ i j : Fin 3, d = w (fv f i) - w (fv f j)}) ≤ 2) ∧
      (∀ f : Fin 20, ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
        n ≠ 0 ∧ (∀ x ∈ b, inner (𝕜 := ℝ) n x ≤ c) ∧
        (∀ i : Fin 3, inner (𝕜 := ℝ) n (w (fv f i)) = c)) ∧
      (∀ e₁ e₂ : Fin 30,
        (ee e₁ = ee e₂ ∨ ee e₁ = (ee e₂).swap) → e₁ = e₂) ∧
      (∀ f₁ f₂ : Fin 20,
        Set.range (fv f₁) = Set.range (fv f₂) → f₁ = f₂) ∧
      (∀ e : Fin 30,
        convexHull ℝ {w (ee e).1, w (ee e).2} ⊆ frontier b) ∧
      (∀ f : Fin 20,
        convexHull ℝ (w '' Set.range (fv f)) ⊆ frontier b) ∧
      (∀ x ∈ frontier b, ∃ f : Fin 20,
        x ∈ convexHull ℝ (w '' Set.range (fv f))) ∧
      (∀ v : Fin 12,
        Set.ncard {f : Fin 20 | ∃ i : Fin 3, fv f i = v} = 5) ∧
      2 * 30 = 3 * 20 ∧ 2 * 30 = 5 * 12 ∧
      (12 : ℤ) - (30 : ℤ) + (20 : ℤ) = 2 := by
  refine ⟨icoVert, icoEdge, icoFace, convexHull ℝ (Set.range icoVert),
    2, 2, by norm_num, by norm_num, rfl, convex_convexHull ℝ _,
    ico_vert_frontier, ico_convex_pos, ico_finrank, ico_edge_length,
    ico_face_edge, ico_face_diag, ico_face_inj, ico_face_convex_pos, ?_,
    ico_face_edge_exists, ico_edge_face_exists, ico_two_face, ?_,
    ico_supp_exists, ico_edge_dup, ico_face_dup, ico_edge_frontier,
    ico_face_frontier, ico_cover, ico_vert_face_count, rfl, rfl, rfl⟩
  · intro f i₁ j₁ i₂ j₂ h1 h2 d1 d2 d3 d4
    exact False.elim
      (tet_disjoint_neg i₁ j₁ i₂ j₂ ⟨h1, h2, d1, d2, d3, d4⟩)
  · intro f
    exact finrank_triangle_le (fun i => icoVert (icoFace f i))

end Icosahedron

section Dodecahedron

/-- Supporting-plane normals for the dodecahedron faces. -/
private noncomputable def dodSuppN : Fin 12 → EuclideanSpace ℝ (Fin 3) :=
  icoVert

/-- For each dodecahedron vertex, a face containing it. -/
private def dodVertFace : Fin 20 → Fin 12 :=
  ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 5, 6, 7]

/-- Index witnessing the assigned dodecahedron vertex-face membership. -/
private def dodVertFaceIdx : Fin 20 → Fin 5 :=
  ![0, 1, 3, 4, 2, 0, 1, 3, 4, 2, 3, 4, 2, 3, 4, 2, 2, 2, 2, 2]

/-- The two faces containing each dodecahedron edge. -/
private def dodEdgeFaces : Fin 30 → Fin 12 × Fin 12 :=
  ![(0, 2), (0, 8), (2, 8), (0, 10), (2, 10),
    (0, 4), (0, 6), (4, 6), (4, 8), (6, 10),
    (1, 3), (1, 9), (3, 9), (1, 11), (3, 11),
    (1, 4), (1, 6), (4, 9), (6, 11), (2, 5),
    (2, 7), (5, 7), (5, 8), (7, 10), (3, 5),
    (3, 7), (5, 9), (7, 11), (8, 9), (10, 11)]

/-- The three faces containing each dodecahedron vertex. -/
private def dodVertFaces : Fin 20 → Fin 3 → Fin 12 := icoFace

private lemma gold_sqrt_four_sq : Real.sqrt (4 * φ ^ 2) = 2 * φ := by
  rw [show 4 * φ ^ 2 = (2 * φ) ^ 2 by ring, Real.sqrt_sq_eq_abs,
    abs_of_pos (mul_pos (by norm_num) gold_pos)]

private lemma gold_edge_radicand :
    1 - φ * 2 + φ ^ 2 * 3 - φ ^ 3 * 2 + φ ^ 4 = 4 := by
  nlinarith [gold_sq, gold_cube, gold_four]

private lemma gold_diag_radicand_one :
    1 + φ * 2 + φ ^ 2 * 3 - φ ^ 3 * 2 + φ ^ 4 = 4 * φ ^ 2 := by
  nlinarith [gold_sq, gold_cube, gold_four]

private lemma gold_diag_radicand_two :
    2 - φ ^ 2 * 2 + φ ^ 4 * 2 = 4 * φ ^ 2 := by
  nlinarith [gold_sq, gold_four]

/-- Dodecahedron edge lengths. -/
private lemma dod_edge_length (e : Fin 30) :
    dist (dodVert (dodEdge e).1) (dodVert (dodEdge e).2) = 2 := by
  fin_cases e
  all_goals
    simp only [dodVert, dodEdge, EuclideanSpace.dist_eq, Fin.sum_univ_three,
      Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val,
      Real.dist_eq]
  all_goals rw [sq_abs, sq_abs, sq_abs]
  all_goals ring_nf
  all_goals first
    | exact cube_sqrt4
    | rw [gold_edge_radicand]
      exact cube_sqrt4

/-- Dodecahedron faces are injective. -/
private lemma dod_face_inj (f : Fin 12) : Function.Injective (dodFace f) := by
  fin_cases f <;> decide

/-- Every cyclic dodecahedron face edge is a graph edge. -/
private lemma dod_face_edge_exists (f : Fin 12) (i j : Fin 5)
    (h : j.val = (i.val + 1) % 5) :
    ∃ e : Fin 30, dodEdge e = (dodFace f i, dodFace f j) ∨
      dodEdge e = (dodFace f j, dodFace f i) := by
  fin_cases f <;> fin_cases i <;> fin_cases j
  all_goals try (norm_num at h)
  all_goals decide

/-- Dodecahedron face edges have the common edge length. -/
private lemma dod_face_edge (f : Fin 12) (i j : Fin 5)
    (h : j.val = (i.val + 1) % 5) :
    dist (dodVert (dodFace f i)) (dodVert (dodFace f j)) = 2 := by
  obtain ⟨e, he | he⟩ := dod_face_edge_exists f i j h
  · have hlen := dod_edge_length e
    rw [he] at hlen
    exact hlen
  · have hlen := dod_edge_length e
    rw [he] at hlen
    rw [dist_comm]
    exact hlen

/-- Dodecahedron face diagonals have length `2φ`. -/
private lemma dod_face_diag (f : Fin 12) (h i j : Fin 5)
    (hh : h.val = (i.val + 5 - 1) % 5)
    (hj : j.val = (i.val + 1) % 5) :
    dist (dodVert (dodFace f h)) (dodVert (dodFace f j)) = 2 * φ := by
  fin_cases i <;> fin_cases h <;> fin_cases j
  all_goals try (norm_num at hh)
  all_goals try (norm_num at hj)
  all_goals fin_cases f
  all_goals
    simp only [dodVert, dodFace, EuclideanSpace.dist_eq, Fin.sum_univ_three,
      Fin.reduceFinMk, Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val,
      Real.dist_eq]
  all_goals simp only [sq_abs]
  all_goals ring_nf
  all_goals first
    | simpa [mul_comm] using gold_sqrt_four_sq
    | rw [gold_diag_radicand_one]
      simpa [mul_comm] using gold_sqrt_four_sq
    | rw [gold_diag_radicand_two]
      simpa [mul_comm] using gold_sqrt_four_sq

/-- Every dodecahedron graph edge is a face edge. -/
private lemma dod_edge_face_exists (e : Fin 30) :
    ∃ f : Fin 12, ∃ i j : Fin 5, j.val = (i.val + 1) % 5 ∧
      (dodEdge e = (dodFace f i, dodFace f j) ∨
        dodEdge e = (dodFace f j, dodFace f i)) := by
  fin_cases e <;> decide

/-- Dodecahedron edges are duplicate-free. -/
private lemma dod_edge_dup (e₁ e₂ : Fin 30)
    (h : dodEdge e₁ = dodEdge e₂ ∨ dodEdge e₁ = (dodEdge e₂).swap) :
    e₁ = e₂ := by
  revert h
  fin_cases e₁ <;> fin_cases e₂ <;> decide

/-- Dodecahedron faces are duplicate-free. -/
private lemma dod_face_dup (f₁ f₂ : Fin 12)
    (h : Set.range (dodFace f₁) = Set.range (dodFace f₂)) : f₁ = f₂ := by
  have hrange : ∀ f : Fin 12, Set.range (dodFace f) =
      ↑(Finset.univ.image (dodFace f)) := by
    intro f
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [hrange f₁, hrange f₂] at h
  have hfin : Finset.univ.image (dodFace f₁) =
      Finset.univ.image (dodFace f₂) := Finset.coe_injective h
  have hne : ∀ a b : Fin 12, a ≠ b →
      Finset.univ.image (dodFace a) ≠ Finset.univ.image (dodFace b) := by
    decide
  by_cases heq : f₁ = f₂
  · exact heq
  · exact False.elim (hne f₁ f₂ heq hfin)

/-- Each dodecahedron edge lies in exactly two faces. -/
private lemma dod_two_face (e : Fin 30) :
    Set.ncard {f : Fin 12 | ∃ i j : Fin 5,
      j.val = (i.val + 1) % 5 ∧
      (dodEdge e = (dodFace f i, dodFace f j) ∨
        dodEdge e = (dodFace f j, dodFace f i))} = 2 := by
  have hset : ∀ e : Fin 30, {f : Fin 12 | ∃ i j : Fin 5,
      j.val = (i.val + 1) % 5 ∧
      (dodEdge e = (dodFace f i, dodFace f j) ∨
        dodEdge e = (dodFace f j, dodFace f i))} =
      {(dodEdgeFaces e).1, (dodEdgeFaces e).2} := by
    intro a
    ext f
    fin_cases a <;> fin_cases f <;> decide
  have hne : ∀ a : Fin 30, (dodEdgeFaces a).1 ≠ (dodEdgeFaces a).2 := by
    decide
  rw [hset e]
  exact Set.ncard_pair (hne e)

/-- Each dodecahedron vertex lies in exactly three faces. -/
private lemma dod_vert_face_count (v : Fin 20) :
    Set.ncard {f : Fin 12 | ∃ i : Fin 5, dodFace f i = v} = 3 := by
  have hset : ∀ u : Fin 20, {f : Fin 12 | ∃ i : Fin 5, dodFace f i = u} =
      Set.range (dodVertFaces u) := by
    intro u
    ext f
    fin_cases u <;> fin_cases f <;> decide
  have hinj : ∀ u : Fin 20, Function.Injective (dodVertFaces u) := by
    intro u
    fin_cases u <;> decide
  rw [hset v, Set.ncard_range_of_injective (hinj v)]
  exact Nat.card_fin 3

/-- Supporting-plane upper bounds for dodecahedron faces. -/
private lemma dod_supp_le (f : Fin 12) (v : Fin 20) :
    inner (𝕜 := ℝ) (dodSuppN f) (dodVert v) ≤ goldC := by
  fin_cases f <;> fin_cases v
  all_goals
    simp only [dodSuppN, icoVert, dodVert, PiLp.inner_apply,
      Real.inner_apply, Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue,
      Fin.mk_zero, Fin.mk_one, Matrix.cons_val, goldC]
  all_goals ring_nf
  all_goals nlinarith [gold_sq, gold_cube, gold_pos]

/-- Supporting-plane equalities on dodecahedron face vertices. -/
private lemma dod_supp_eq (f : Fin 12) (i : Fin 5) :
    inner (𝕜 := ℝ) (dodSuppN f) (dodVert (dodFace f i)) = goldC := by
  fin_cases f <;> fin_cases i
  all_goals
    simp only [dodSuppN, icoVert, dodVert, dodFace, PiLp.inner_apply,
      Real.inner_apply, Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue,
      Fin.mk_zero, Fin.mk_one, Matrix.cons_val, goldC]
  all_goals ring_nf
  all_goals nlinarith [gold_sq, gold_cube]

/-- Dodecahedron supporting normals are nonzero. -/
private lemma dod_supp_ne (f : Fin 12) : dodSuppN f ≠ 0 := by
  intro hzero
  have h := dod_supp_eq f 0
  rw [hzero] at h
  simp only [inner_zero_left] at h
  nlinarith [goldC_pos]

/-- Supporting planes exist for dodecahedron faces. -/
private lemma dod_supp_exists (f : Fin 12) :
    ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
      n ≠ 0 ∧
      (∀ x ∈ convexHull ℝ (Set.range dodVert), inner (𝕜 := ℝ) n x ≤ c) ∧
      (∀ i : Fin 5, inner (𝕜 := ℝ) n (dodVert (dodFace f i)) = c) := by
  refine ⟨dodSuppN f, goldC, dod_supp_ne f, ?_, fun i => dod_supp_eq f i⟩
  intro x hx
  apply inner_le_of_mem_convexHull _ hx
  intro s hs
  obtain ⟨v, rfl⟩ := hs
  exact dod_supp_le f v

set_option maxHeartbeats 1000000 in
-- The 20-by-20 explicit vertex separation table exceeds the default budget.
/-- Dodecahedron vertices are in convex position. -/
private lemma dod_convex_pos (v : Fin 20) :
    dodVert v ∉ convexHull ℝ (dodVert '' {u : Fin 20 | u ≠ v}) := by
  apply not_mem_convexHull_of_separation (n := dodVert v) (c := 3 * φ + 1)
  · intro s hs
    obtain ⟨u, hu, rfl⟩ := hs
    simp only [Set.mem_ofPred_eq] at hu
    fin_cases v <;> fin_cases u
    all_goals try (exact False.elim (hu rfl))
    all_goals
      simp only [dodVert, PiLp.inner_apply, Real.inner_apply,
        Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero,
        Fin.mk_one, Matrix.cons_val]
    all_goals ring_nf
    all_goals nlinarith [gold_sq, gold_cube, gold_four, gold_pos]
  · fin_cases v
    all_goals
      simp only [dodVert, PiLp.inner_apply, Real.inner_apply,
        Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.mk_zero,
        Fin.mk_one, Matrix.cons_val]
    all_goals ring_nf
    all_goals nlinarith [gold_sq, gold_cube, gold_four, gold_pos]

/-- Dodecahedron face vertices are in convex position within each face. -/
private lemma dod_face_convex_pos (f : Fin 12) (k : Fin 5) :
    dodVert (dodFace f k) ∉ convexHull ℝ
      (dodVert '' (Set.range (dodFace f) \ {dodFace f k})) := by
  intro hmem
  apply dod_convex_pos (dodFace f k)
  apply convexHull_mono ?_ hmem
  rintro z ⟨u, hu, rfl⟩
  refine ⟨u, ?_, rfl⟩
  simp only [Set.mem_ofPred_eq]
  simpa only [Set.mem_singleton_iff] using hu.2

/-- Three vertex differences spanning the dodecahedron. -/
private noncomputable def dodD : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![dodVert 0 - dodVert 1, dodVert 16 - dodVert 17,
    dodVert 2 - dodVert 7]

private lemma dod_gram_det : (Matrix.gram ℝ dodD).det = 64 := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.gram_apply, dodD, dodVert, PiLp.inner_apply,
    Real.inner_apply, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val,
    PiLp.sub_apply]
  norm_num

private lemma dodD_indep : LinearIndependent ℝ dodD := by
  rw [← Matrix.det_gram_ne_zero_iff_linearIndependent, dod_gram_det]
  norm_num

private lemma dod_span_top : Submodule.span ℝ (Set.range dodD) = ⊤ :=
  LinearIndependent.span_eq_top_of_card_eq_finrank dodD_indep
    (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])

/-- Full-dimensionality for the dodecahedron vertex set. -/
private lemma dod_finrank : Module.finrank ℝ (Submodule.span ℝ
    {d : EuclideanSpace ℝ (Fin 3) | ∃ i j : Fin 20,
      d = dodVert i - dodVert j}) = 3 := by
  have hle : Submodule.span ℝ (Set.range dodD) ≤ Submodule.span ℝ
      {d : EuclideanSpace ℝ (Fin 3) | ∃ i j : Fin 20,
        d = dodVert i - dodVert j} := by
    apply Submodule.span_mono
    rintro x ⟨k, rfl⟩
    fin_cases k
    · exact ⟨0, 1, rfl⟩
    · exact ⟨16, 17, rfl⟩
    · exact ⟨2, 7, rfl⟩
  rw [dod_span_top] at hle
  have hspan : Submodule.span ℝ
      {d : EuclideanSpace ℝ (Fin 3) | ∃ i j : Fin 20,
        d = dodVert i - dodVert j} = ⊤ := top_le_iff.mp hle
  have hfin : Module.finrank ℝ
      ↥(⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) :=
    Submodule.topEquiv.finrank_eq
  rw [hspan, hfin, finrank_euclideanSpace_fin]

/-- Dodecahedron faces are planar. -/
private lemma dod_face_planar (f : Fin 12) :
    Module.finrank ℝ (Submodule.span ℝ
      {d : EuclideanSpace ℝ (Fin 3) | ∃ i j : Fin 5,
        d = dodVert (dodFace f i) - dodVert (dodFace f j)}) ≤ 2 := by
  let L : Module.Dual ℝ (EuclideanSpace ℝ (Fin 3)) :=
    (innerSL ℝ (dodSuppN f)).toLinearMap
  have hL : L ≠ 0 := by
    intro hzero
    apply dod_supp_ne f
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    change L (dodSuppN f) = 0
    simp only [hzero, LinearMap.zero_apply]
  have hsub : Submodule.span ℝ
      {d : EuclideanSpace ℝ (Fin 3) | ∃ i j : Fin 5,
        d = dodVert (dodFace f i) - dodVert (dodFace f j)} ≤
      LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro d ⟨i, j, rfl⟩
    change L (dodVert (dodFace f i) - dodVert (dodFace f j)) = 0
    change inner (𝕜 := ℝ) (dodSuppN f)
      (dodVert (dodFace f i) - dodVert (dodFace f j)) = 0
    rw [inner_sub_right, dod_supp_eq f i, dod_supp_eq f j, sub_self]
  have hrank := Module.Dual.finrank_ker_add_one_of_ne_zero hL
  have hambient : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 :=
    finrank_euclideanSpace_fin
  have hker : Module.finrank ℝ (LinearMap.ker L) = 2 := by omega
  exact (Submodule.finrank_mono hsub).trans_eq hker

/-- A dodecahedron vertex outside a face lies strictly below its support plane. -/
private lemma dod_supp_lt_of_not_mem (f : Fin 12) (v : Fin 20)
    (hnot : ¬ ∃ i : Fin 5, dodFace f i = v) :
    inner (𝕜 := ℝ) (dodSuppN f) (dodVert v) < goldC := by
  fin_cases f <;> fin_cases v
  all_goals first
    | exact False.elim (hnot (by decide))
    | simp only [dodSuppN, icoVert, dodVert, PiLp.inner_apply,
        Real.inner_apply, Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue,
        Fin.mk_zero, Fin.mk_one, Matrix.cons_val, goldC]
      ring_nf
      nlinarith [gold_sq, gold_cube, gold_four, gold_pos]

/-- Equality in a dodecahedron support inequality characterizes face vertices. -/
private lemma dod_supp_eq_iff (f : Fin 12) (v : Fin 20) :
    inner (𝕜 := ℝ) (dodSuppN f) (dodVert v) = goldC ↔
      ∃ i : Fin 5, dodFace f i = v := by
  constructor
  · intro heq
    by_contra hnot
    exact (ne_of_lt (dod_supp_lt_of_not_mem f v hnot)) heq
  · rintro ⟨i, rfl⟩
    exact dod_supp_eq f i

/-- The halfspace determined by a dodecahedron face. -/
private def dodHalf (f : Fin 12) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | inner (𝕜 := ℝ) (dodSuppN f) x ≤ goldC}

/-- The origin lies in the dodecahedron hull. -/
private lemma dod_zero_mem :
    0 ∈ convexHull ℝ (Set.range dodVert) := by
  have h0 : dodVert 0 ∈ convexHull ℝ (Set.range dodVert) :=
    subset_convexHull ℝ _ (Set.mem_range_self 0)
  have h6 : dodVert 6 ∈ convexHull ℝ (Set.range dodVert) :=
    subset_convexHull ℝ _ (Set.mem_range_self 6)
  have ht : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hline := (convex_convexHull ℝ (Set.range dodVert)).lineMap_mem h0 h6 ht
  rw [AffineMap.lineMap_apply_module] at hline
  have hmid : (1 - (1 / 2 : ℝ)) • dodVert 0 +
      (1 / 2 : ℝ) • dodVert 6 = 0 := by
    ext k
    fin_cases k <;> simp [dodVert] <;> ring
  rw [hmid] at hline
  exact hline

/-- The dodecahedron H-representation is contained in its convex hull. -/
private lemma dod_inter_subset_hull :
    (⋂ f, dodHalf f) ⊆ convexHull ℝ (Set.range dodVert) := by
  intro x hx
  simp only [Set.mem_iInter, dodHalf, Set.mem_ofPred_eq] at hx
  by_contra hnot
  have hclosed : IsClosed (convexHull ℝ (Set.range dodVert)) :=
    (Set.finite_range dodVert).isClosed_convexHull ℝ
  obtain ⟨F, u, hFu, hux⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (Set.range dodVert)) hclosed hnot
  let n : EuclideanSpace ℝ (Fin 3) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm F
  have hn (z : EuclideanSpace ℝ (Fin 3)) :
      inner (𝕜 := ℝ) n z = F z := by
    simpa only [n] using
      (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := z) (y := F))
  have hu_pos : 0 < u := by
    have h0 := hFu 0 dod_zero_mem
    simpa using h0
  let y : EuclideanSpace ℝ (Fin 3) := (goldC / u) • n
  have hy : y ∈ convexHull ℝ (Set.range icoVert) := by
    rw [ico_hull_eq_inter]
    simp only [Set.mem_iInter, icoHalf, Set.mem_ofPred_eq]
    intro k
    have hk := hFu (dodVert k)
      (subset_convexHull ℝ _ (Set.mem_range_self k))
    have hscale : 0 ≤ goldC / u := (div_pos goldC_pos hu_pos).le
    calc
      inner (𝕜 := ℝ) (icoSuppN k) y =
          (goldC / u) * F (dodVert k) := by
        simp only [icoSuppN, y, inner_smul_right]
        rw [real_inner_comm, hn]
      _ ≤ (goldC / u) * u := mul_le_mul_of_nonneg_left hk.le hscale
      _ = goldC := div_mul_cancel₀ goldC hu_pos.ne'
  have hyx : inner (𝕜 := ℝ) y x ≤ goldC := by
    rw [real_inner_comm]
    apply inner_le_of_mem_convexHull _ hy
    intro s hs
    obtain ⟨f, rfl⟩ := hs
    rw [real_inner_comm]
    exact hx f
  have hyx' : (goldC / u) * inner (𝕜 := ℝ) n x ≤ goldC := by
    simpa only [y, inner_smul_left, conj_trivial, smul_eq_mul] using hyx
  have hscale_pos : 0 < goldC / u := div_pos goldC_pos hu_pos
  have hprod : (goldC / u) * u = goldC :=
    div_mul_cancel₀ goldC hu_pos.ne'
  have hmul : (goldC / u) * inner (𝕜 := ℝ) n x ≤
      (goldC / u) * u := by
    rwa [hprod]
  have hnx : inner (𝕜 := ℝ) n x ≤ u :=
    le_of_mul_le_mul_of_pos_left hmul hscale_pos
  rw [hn] at hnx
  exact (not_lt_of_ge hnx) hux

/-- The dodecahedron convex hull equals its H-representation. -/
private lemma dod_hull_eq_inter :
    convexHull ℝ (Set.range dodVert) = ⋂ f, dodHalf f := by
  apply le_antisymm
  · intro x hx
    simp only [Set.mem_iInter]
    intro f
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨v, rfl⟩ := hs
    exact dod_supp_le f v
  · exact dod_inter_subset_hull

/-- A point of a finite convex hull attaining a linear maximum lies in the
convex hull of the generators attaining that maximum. -/
private lemma mem_exposed_convexHull_of_mem_convexHull
    {S T : Set (EuclideanSpace ℝ (Fin 3))}
    {n : EuclideanSpace ℝ (Fin 3)} {c : ℝ}
    (hT : T.Nonempty)
    (hle : ∀ z ∈ S, inner (𝕜 := ℝ) n z ≤ c)
    (heqmem : ∀ z ∈ S, inner (𝕜 := ℝ) n z = c ↔ z ∈ T)
    {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ convexHull ℝ S) (heq : inner (𝕜 := ℝ) n x = c) :
    x ∈ convexHull ℝ T := by
  classical
  obtain ⟨ι, hι, w, z, hw0, hw1, hz, hcenter⟩ :=
    (mem_convexHull_iff_exists_fintype.mp hx)
  let _ := hι
  obtain ⟨z0, hz0⟩ := hT
  have hinner : ∑ i, w i * inner (𝕜 := ℝ) n (z i) = c := by
    rw [← heq, ← hcenter, inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_smul_right]
  have hslack : ∑ i, w i * (c - inner (𝕜 := ℝ) n (z i)) = 0 := by
    calc
      ∑ i, w i * (c - inner (𝕜 := ℝ) n (z i)) =
          ∑ i, (c * w i - w i * inner (𝕜 := ℝ) n (z i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, c * w i) - ∑ i, w i * inner (𝕜 := ℝ) n (z i) :=
        by
          simpa only [] using
            (Finset.sum_sub_distrib (s := Finset.univ)
              (fun i : ι => c * w i)
              (fun i : ι => w i * inner (𝕜 := ℝ) n (z i)))
      _ = c * (∑ i, w i) - ∑ i, w i * inner (𝕜 := ℝ) n (z i) := by
        rw [Finset.mul_sum]
      _ = 0 := by rw [hw1, hinner]; ring
  have hterm (i : ι) :
      w i * (c - inner (𝕜 := ℝ) n (z i)) = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hslack i
      (Finset.mem_univ i)
    intro j hj
    exact mul_nonneg (hw0 j) (sub_nonneg.mpr (hle (z j) (hz j)))
  let z' : ι → EuclideanSpace ℝ (Fin 3) :=
    fun i => if w i = 0 then z0 else z i
  have hz' (i : ι) : z' i ∈ T := by
    by_cases hwi : w i = 0
    · change (if w i = 0 then z0 else z i) ∈ T
      rw [ite_eq_left hwi]
      exact hz0
    · have hslack_i : c - inner (𝕜 := ℝ) n (z i) = 0 :=
        (mul_eq_zero.mp (hterm i)).resolve_left hwi
      have heq_i : inner (𝕜 := ℝ) n (z i) = c := by linarith
      change (if w i = 0 then z0 else z i) ∈ T
      rw [ite_eq_right hwi]
      exact (heqmem (z i) (hz i)).mp heq_i
  have hcenter' : ∑ i, w i • z' i = x := by
    rw [← hcenter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hwi : w i = 0 <;> simp [z', hwi]
  exact mem_convexHull_of_exists_fintype w z' hw0 hw1 hz' hcenter'

/-- A point of all dodecahedron halfspaces on a face plane lies in that face hull. -/
private lemma dod_mem_face_of_eq (f : Fin 12)
    (x : EuclideanSpace ℝ (Fin 3))
    (hall : ∀ g : Fin 12, x ∈ dodHalf g)
    (heq : inner (𝕜 := ℝ) (dodSuppN f) x = goldC) :
    x ∈ convexHull ℝ (dodVert '' Set.range (dodFace f)) := by
  have hx : x ∈ convexHull ℝ (Set.range dodVert) := by
    rw [dod_hull_eq_inter]
    simpa only [Set.mem_iInter] using hall
  apply mem_exposed_convexHull_of_mem_convexHull
      (S := Set.range dodVert) (T := dodVert '' Set.range (dodFace f))
      (n := dodSuppN f) (c := goldC) ?_ ?_ ?_ hx heq
  · exact ⟨dodVert (dodFace f 0),
      Set.mem_image_of_mem _ (Set.mem_range_self 0)⟩
  · intro z hz
    obtain ⟨v, rfl⟩ := hz
    exact dod_supp_le f v
  · intro z hz
    constructor
    · intro heqz
      obtain ⟨v, rfl⟩ := hz
      obtain ⟨i, hi⟩ := (dod_supp_eq_iff f v).mp heqz
      refine ⟨dodFace f i, Set.mem_range_self i, ?_⟩
      rw [hi]
    · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
      exact dod_supp_eq f i

/-- Each dodecahedron vertex lies in its assigned face. -/
private lemma dod_vert_mem_face :
    ∀ v : Fin 20, dodFace (dodVertFace v) (dodVertFaceIdx v) = v := by
  decide

/-- Dodecahedron vertices lie in the frontier. -/
private lemma dod_vert_frontier (v : Fin 20) :
    dodVert v ∈ frontier (convexHull ℝ (Set.range dodVert)) := by
  have hmem : dodVert v ∈ convexHull ℝ (Set.range dodVert) :=
    subset_convexHull ℝ _ (Set.mem_range_self v)
  have hle : ∀ x ∈ convexHull ℝ (Set.range dodVert),
      inner (𝕜 := ℝ) (dodSuppN (dodVertFace v)) x ≤ goldC := by
    intro x hx
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact dod_supp_le _ u
  have heq : inner (𝕜 := ℝ) (dodSuppN (dodVertFace v)) (dodVert v) =
      goldC := by
    have h := dod_supp_eq (dodVertFace v) (dodVertFaceIdx v)
    rw [dod_vert_mem_face v] at h
    exact h
  exact mem_frontier_of_support hmem hle heq (dod_supp_ne _)

/-- Dodecahedron edge hulls lie in the frontier. -/
private lemma dod_edge_frontier (e : Fin 30) :
    convexHull ℝ {dodVert (dodEdge e).1, dodVert (dodEdge e).2} ⊆
      frontier (convexHull ℝ (Set.range dodVert)) := by
  obtain ⟨f, i, j, _, heq⟩ := dod_edge_face_exists e
  have hsub : ({dodVert (dodEdge e).1, dodVert (dodEdge e).2} :
      Set (EuclideanSpace ℝ (Fin 3))) ⊆ Set.range dodVert := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    cases hz with
    | inl h => rw [h]; exact Set.mem_range_self _
    | inr h => rw [h]; exact Set.mem_range_self _
  have hle : ∀ x ∈ convexHull ℝ (Set.range dodVert),
      inner (𝕜 := ℝ) (dodSuppN f) x ≤ goldC := by
    intro x hx
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact dod_supp_le f u
  have ha : inner (𝕜 := ℝ) (dodSuppN f) (dodVert (dodEdge e).1) =
      goldC := by
    cases heq with
    | inl h =>
      have h1 : (dodEdge e).1 = dodFace f i := congrArg Prod.fst h
      rw [h1]
      exact dod_supp_eq f i
    | inr h =>
      have h1 : (dodEdge e).1 = dodFace f j := congrArg Prod.fst h
      rw [h1]
      exact dod_supp_eq f j
  have hb : inner (𝕜 := ℝ) (dodSuppN f) (dodVert (dodEdge e).2) =
      goldC := by
    cases heq with
    | inl h =>
      have h2 : (dodEdge e).2 = dodFace f j := congrArg Prod.snd h
      rw [h2]
      exact dod_supp_eq f j
    | inr h =>
      have h2 : (dodEdge e).2 = dodFace f i := congrArg Prod.snd h
      rw [h2]
      exact dod_supp_eq f i
  intro y hy
  have hyB : y ∈ convexHull ℝ (Set.range dodVert) := convexHull_mono hsub hy
  have heq_y : inner (𝕜 := ℝ) (dodSuppN f) y = goldC := by
    apply inner_eq_of_mem_convexHull _ hy
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    cases hs with
    | inl h => rw [h]; exact ha
    | inr h => rw [h]; exact hb
  exact mem_frontier_of_support hyB hle heq_y (dod_supp_ne f)

/-- Dodecahedron face hulls lie in the frontier. -/
private lemma dod_face_frontier (f : Fin 12) :
    convexHull ℝ (dodVert '' Set.range (dodFace f)) ⊆
      frontier (convexHull ℝ (Set.range dodVert)) := by
  have hsub : dodVert '' Set.range (dodFace f) ⊆ Set.range dodVert := by
    rintro z ⟨x, ⟨i, rfl⟩, rfl⟩
    exact Set.mem_range_self _
  have hle : ∀ x ∈ convexHull ℝ (Set.range dodVert),
      inner (𝕜 := ℝ) (dodSuppN f) x ≤ goldC := by
    intro x hx
    apply inner_le_of_mem_convexHull _ hx
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact dod_supp_le f u
  intro y hy
  have hyB : y ∈ convexHull ℝ (Set.range dodVert) := convexHull_mono hsub hy
  have heq_y : inner (𝕜 := ℝ) (dodSuppN f) y = goldC := by
    apply inner_eq_of_mem_convexHull _ hy
    intro s hs
    obtain ⟨x, ⟨i, rfl⟩, rfl⟩ := hs
    exact dod_supp_eq f i
  exact mem_frontier_of_support hyB hle heq_y (dod_supp_ne f)

/-- A halfspace point outside its interior achieves equality. -/
private lemma dod_half_eq_of_mem_of_not_mem_interior (f : Fin 12)
    (x : EuclideanSpace ℝ (Fin 3)) (hmem : x ∈ dodHalf f)
    (hnot : x ∉ interior (dodHalf f)) :
    inner (𝕜 := ℝ) (dodSuppN f) x = goldC := by
  simp only [dodHalf, Set.mem_ofPred_eq] at hmem
  by_contra hne
  have hlt : inner (𝕜 := ℝ) (dodSuppN f) x < goldC :=
    lt_of_le_of_ne hmem hne
  have hcont : Continuous
      (fun y : EuclideanSpace ℝ (Fin 3) => inner (𝕜 := ℝ) (dodSuppN f) y) :=
    continuous_const.inner continuous_id
  have hopen : IsOpen
      {y : EuclideanSpace ℝ (Fin 3) |
        inner (𝕜 := ℝ) (dodSuppN f) y < goldC} := by
    have hIio : IsOpen (Set.Iio goldC) := isOpen_Iio
    have hpre := hIio.preimage hcont
    simpa only [Set.preimage, Set.mem_Iio] using hpre
  have hsub : {y : EuclideanSpace ℝ (Fin 3) |
      inner (𝕜 := ℝ) (dodSuppN f) y < goldC} ⊆ dodHalf f := by
    intro y hy
    simp only [dodHalf, Set.mem_ofPred_eq, Set.mem_ofPred_eq] at hy ⊢
    exact hy.le
  exact hnot ((hopen.subset_interior_iff).mpr hsub hlt)

/-- Dodecahedron frontier is covered by faces. -/
private lemma dod_cover (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ frontier (convexHull ℝ (Set.range dodVert))) :
    ∃ f : Fin 12, x ∈ convexHull ℝ (dodVert '' Set.range (dodFace f)) := by
  classical
  have hclosed : IsClosed (convexHull ℝ (Set.range dodVert)) :=
    (Set.finite_range dodVert).isClosed_convexHull ℝ
  have hmem : x ∈ convexHull ℝ (Set.range dodVert) := hclosed.frontier_subset hx
  have hnot : x ∉ interior (convexHull ℝ (Set.range dodVert)) :=
    (mem_frontier_iff_notMem_interior hmem).mp hx
  rw [dod_hull_eq_inter] at hmem hnot
  simp only [interior_iInter_of_finite, Set.mem_iInter] at hmem hnot
  have hex : ∃ f : Fin 12, x ∉ interior (dodHalf f) := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hnot hcon
  obtain ⟨f, hf⟩ := hex
  have heq := dod_half_eq_of_mem_of_not_mem_interior f x (hmem f) hf
  exact ⟨f, dod_mem_face_of_eq f x hmem heq⟩

set_option maxHeartbeats 1000000 in
-- The finite check covers 120 ordered pairs of nonincident pentagon edges.
/-- Nonincident cyclic edges of a dodecahedron face are disjoint. -/
private lemma dod_edge_disjoint (f : Fin 12) (i₁ j₁ i₂ j₂ : Fin 5)
    (h1 : j₁.val = (i₁.val + 1) % 5)
    (h2 : j₂.val = (i₂.val + 1) % 5)
    (d1 : i₁ ≠ i₂) (d2 : i₁ ≠ j₂) (d3 : j₁ ≠ i₂) (d4 : j₁ ≠ j₂) :
    Disjoint
      (convexHull ℝ {dodVert (dodFace f i₁), dodVert (dodFace f j₁)})
      (convexHull ℝ {dodVert (dodFace f i₂), dodVert (dodFace f j₂)}) := by
  fin_cases i₁ <;> fin_cases j₁ <;> fin_cases i₂ <;> fin_cases j₂
  all_goals try (norm_num at h1)
  all_goals try (norm_num at h2)
  all_goals try (exact False.elim (d1 rfl))
  all_goals try (exact False.elim (d2 rfl))
  all_goals try (exact False.elim (d3 rfl))
  all_goals fin_cases f
  all_goals
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [convexHull_pair, segment_eq_image_lineMap] at hx1 hx2
    obtain ⟨t, ht, rfl⟩ := hx1
    obtain ⟨s, hs, heq⟩ := hx2
    have heq0 := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 0) heq
    have heq1 := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 1) heq
    have heq2 := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 2) heq
    simp only [AffineMap.lineMap_apply_module, dodVert, dodFace,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.reduceFinMk,
      Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.cons_val] at heq0 heq1 heq2
    ring_nf at heq0 heq1 heq2
    rcases ht with ⟨ht0, ht1⟩
    rcases hs with ⟨hs0, hs1⟩
    nlinarith [gold_sq, gold_cube, gold_four, gold_pos,
      gold_sq_mul t, gold_sq_mul s, gold_cube_mul t, gold_cube_mul s]

/-- Dodecahedron realization exists. -/
private theorem dod_exists :
    ∃ (w : Fin 20 → EuclideanSpace ℝ (Fin 3))
      (ee : Fin 30 → Fin 20 × Fin 20)
      (fv : Fin 12 → Fin 5 → Fin 20)
      (b : Set (EuclideanSpace ℝ (Fin 3))) (ll dd : ℝ),
      0 < ll ∧ 0 < dd ∧
      b = convexHull ℝ (Set.range w) ∧
      Convex ℝ b ∧
      (∀ v : Fin 20, w v ∈ frontier b) ∧
      (∀ v : Fin 20, w v ∉ convexHull ℝ (w '' {u : Fin 20 | u ≠ v})) ∧
      (Module.finrank ℝ (Submodule.span ℝ
        {d : EuclideanSpace ℝ (Fin 3) | ∃ i j : Fin 20, d = w i - w j}) = 3) ∧
      (∀ e : Fin 30, dist (w (ee e).1) (w (ee e).2) = ll) ∧
      (∀ (f : Fin 12) (i j : Fin 5), j.val = (i.val + 1) % 5 →
        dist (w (fv f i)) (w (fv f j)) = ll) ∧
      (∀ (f : Fin 12) (h i j : Fin 5), h.val = (i.val + 5 - 1) % 5 →
        j.val = (i.val + 1) % 5 →
        dist (w (fv f h)) (w (fv f j)) = dd) ∧
      (∀ f : Fin 12, Function.Injective (fv f)) ∧
      (∀ (f : Fin 12) (k : Fin 5), w (fv f k) ∉ convexHull ℝ
        (w '' (Set.range (fv f) \ {fv f k}))) ∧
      (∀ (f : Fin 12) (i₁ j₁ i₂ j₂ : Fin 5),
        j₁.val = (i₁.val + 1) % 5 →
        j₂.val = (i₂.val + 1) % 5 →
        i₁ ≠ i₂ → i₁ ≠ j₂ → j₁ ≠ i₂ → j₁ ≠ j₂ →
        Disjoint (convexHull ℝ {w (fv f i₁), w (fv f j₁)})
          (convexHull ℝ {w (fv f i₂), w (fv f j₂)})) ∧
      (∀ (f : Fin 12) (i j : Fin 5), j.val = (i.val + 1) % 5 →
        ∃ e : Fin 30, ee e = (fv f i, fv f j) ∨
          ee e = (fv f j, fv f i)) ∧
      (∀ e : Fin 30, ∃ f : Fin 12, ∃ i j : Fin 5,
        j.val = (i.val + 1) % 5 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))) ∧
      (∀ e : Fin 30, Set.ncard {f : Fin 12 | ∃ i j : Fin 5,
        j.val = (i.val + 1) % 5 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))} = 2) ∧
      (∀ f : Fin 12, Module.finrank ℝ (Submodule.span ℝ
        {d : EuclideanSpace ℝ (Fin 3) |
          ∃ i j : Fin 5, d = w (fv f i) - w (fv f j)}) ≤ 2) ∧
      (∀ f : Fin 12, ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
        n ≠ 0 ∧ (∀ x ∈ b, inner (𝕜 := ℝ) n x ≤ c) ∧
        (∀ i : Fin 5, inner (𝕜 := ℝ) n (w (fv f i)) = c)) ∧
      (∀ e₁ e₂ : Fin 30,
        (ee e₁ = ee e₂ ∨ ee e₁ = (ee e₂).swap) → e₁ = e₂) ∧
      (∀ f₁ f₂ : Fin 12,
        Set.range (fv f₁) = Set.range (fv f₂) → f₁ = f₂) ∧
      (∀ e : Fin 30,
        convexHull ℝ {w (ee e).1, w (ee e).2} ⊆ frontier b) ∧
      (∀ f : Fin 12,
        convexHull ℝ (w '' Set.range (fv f)) ⊆ frontier b) ∧
      (∀ x ∈ frontier b, ∃ f : Fin 12,
        x ∈ convexHull ℝ (w '' Set.range (fv f))) ∧
      (∀ v : Fin 20,
        Set.ncard {f : Fin 12 | ∃ i : Fin 5, fv f i = v} = 3) ∧
      2 * 30 = 5 * 12 ∧ 2 * 30 = 3 * 20 ∧
      (20 : ℤ) - (30 : ℤ) + (12 : ℤ) = 2 := by
  refine ⟨dodVert, dodEdge, dodFace, convexHull ℝ (Set.range dodVert),
    2, 2 * φ, by norm_num, ?_, rfl, convex_convexHull ℝ _,
    dod_vert_frontier, dod_convex_pos, dod_finrank, dod_edge_length,
    dod_face_edge, dod_face_diag, dod_face_inj, dod_face_convex_pos,
    dod_edge_disjoint, dod_face_edge_exists, dod_edge_face_exists, dod_two_face,
    dod_face_planar, dod_supp_exists, dod_edge_dup, dod_face_dup,
    dod_edge_frontier, dod_face_frontier, dod_cover, dod_vert_face_count,
    rfl, rfl, rfl⟩
  exact mul_pos (by norm_num) gold_pos

end Dodecahedron
end GoldenSolids

/-- **Classification of the Platonic solids.** Let $V, E, F, p, q$ be natural numbers with
$V, E, F > 0$ and $p, q \ge 3$, and let $l > 0$ and $d > 0$ be real numbers. Let
$x_0, \dots, x_{V-1}$ be points of the Euclidean space $\mathbb{R}^3$, let $K$ be their convex
hull and let $\partial K$ be its topological boundary. Let each edge $e < E$ be an ordered pair
$(a_e, b_e)$ of point indices, with segment $[x_{a_e}, x_{b_e}]$, and let each face $f < F$ be a
list $\phi_f(0), \dots, \phi_f(p-1)$ of point indices, read cyclically: positions are taken
modulo $p$, the sides of $f$ are the pairs $(\phi_f(i), \phi_f(i+1))$, and the filled face is
the convex hull of $x_{\phi_f(0)}, \dots, x_{\phi_f(p-1)}$. An edge $e$ lies on side $i$ of $f$
when $(a_e, b_e)$ equals $(\phi_f(i), \phi_f(i+1))$ or $(\phi_f(i+1), \phi_f(i))$. Assume:
$K$ is convex and contains every $x_i$; no $x_i$ lies in the convex hull of the $x_j$ with
$j \ne i$; the differences $x_i - x_j$ span a space of dimension $3$; every edge segment has
length $l$; for every face $f$ and position $i$,
$\operatorname{dist}(x_{\phi_f(i)}, x_{\phi_f(i+1)}) = l$ and
$\operatorname{dist}(x_{\phi_f(i-1)}, x_{\phi_f(i+1)}) = d$; the indices
$\phi_f(0), \dots, \phi_f(p-1)$ of each face are distinct; no vertex $x_{\phi_f(k)}$ of a face
lies in the convex hull of the other vertices of that face; two sides $(i_1, i_1+1)$ and
$(i_2, i_2+1)$ of a face whose four endpoint positions are all different have disjoint
segments; some edge lies on each side of every face, and every edge lies on a side of some face;
every edge lies on a side of exactly two faces; every edge segment and every filled face is
contained in $K$; the differences of the vertices of each face span a space of dimension at
most $2$; for every face $f$ there are a nonzero vector $n$ and a real $c$ with
$\langle n, x \rangle \le c$ for all $x \in K$ and $\langle n, x_{\phi_f(i)} \rangle = c$ for
every position $i$; two edges $e_1, e_2$ with $(a_{e_1}, b_{e_1})$ equal to
$(a_{e_2}, b_{e_2})$ or $(b_{e_2}, a_{e_2})$ are equal; two faces with the same set of indices
are equal; every $x_i$, every edge segment and every filled face is contained in $\partial K$;
every point of $\partial K$ lies in some filled face; every point index occurs in exactly $q$
faces; and $2E = pF$, $2E = qV$ and $V - E + F = 2$. Then $(p, q, V, E, F)$ is one of
$(3, 3, 4, 6, 4)$ (tetrahedron), $(4, 3, 8, 12, 6)$ (cube), $(3, 4, 6, 12, 8)$ (octahedron),
$(5, 3, 20, 30, 12)$ (dodecahedron) or $(3, 5, 12, 30, 20)$ (icosahedron).

Conversely, each of these five tuples $(p, q, V, E, F)$ is realized: there are points, edges,
faces and reals $l, d > 0$ satisfying all the conditions above, except that the points, edge
segments and filled faces are required to lie in $\partial K$ but not separately in $K$.

Euler's relation $V - E + F = 2$ and the incidence counts $2E = pF$, $2E = qV$ are hypotheses,
and the classification is up to the tuple $(p, q, V, E, F)$, not up to congruence. Together they
give $1/p + 1/q > 1/2$, which leaves the five tuples; explicit coordinates realize each one.

Source: https://en.wikipedia.org/wiki/Platonic_solid (statement `platonic-solids-s1`); proves
`Wanted` entry `platonic_solids_classification`.
-/
theorem platonic_solids_classification :
    ((∀ (V E F p q : ℕ) (verts : Fin V → EuclideanSpace ℝ (Fin 3))
      (edgeEnds : Fin E → Fin V × Fin V) (faceVerts : Fin F → Fin p → Fin V)
      (body : Set (EuclideanSpace ℝ (Fin 3))) (l angleDiag : ℝ),
      0 < V → 0 < E → 0 < F → 3 ≤ p → 3 ≤ q → 0 < l → 0 < angleDiag →
      body = convexHull ℝ (Set.range verts) →
      Convex ℝ body →
      (∀ v : Fin V, verts v ∈ body) →
      (∀ v : Fin V, verts v ∉ convexHull ℝ (verts '' {w : Fin V | w ≠ v})) →
      (Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin V, d = verts i - verts j}) = 3) →
      (∀ e : Fin E, dist (verts (edgeEnds e).1) (verts (edgeEnds e).2) = l) →
      (∀ f : Fin F, ∀ i j : Fin p,
        j.val = (i.val + 1) % p →
        dist (verts (faceVerts f i)) (verts (faceVerts f j)) = l) →
      (∀ f : Fin F, ∀ h i j : Fin p,
        h.val = (i.val + p - 1) % p → j.val = (i.val + 1) % p →
        dist (verts (faceVerts f h)) (verts (faceVerts f j)) = angleDiag) →
      (∀ f : Fin F, Function.Injective (faceVerts f)) →
      (∀ f : Fin F, ∀ k : Fin p,
        verts (faceVerts f k) ∉ convexHull ℝ
          (verts '' (Set.range (faceVerts f) \ {faceVerts f k}))) →
      (∀ f : Fin F, ∀ i₁ j₁ i₂ j₂ : Fin p,
        j₁.val = (i₁.val + 1) % p → j₂.val = (i₂.val + 1) % p →
        i₁ ≠ i₂ → i₁ ≠ j₂ → j₁ ≠ i₂ → j₁ ≠ j₂ →
        Disjoint (convexHull ℝ {verts (faceVerts f i₁), verts (faceVerts f j₁)})
          (convexHull ℝ {verts (faceVerts f i₂), verts (faceVerts f j₂)})) →
      (∀ f : Fin F, ∀ i j : Fin p,
        j.val = (i.val + 1) % p →
        ∃ e : Fin E, edgeEnds e = (faceVerts f i, faceVerts f j) ∨
          edgeEnds e = (faceVerts f j, faceVerts f i)) →
      (∀ e : Fin E, ∃ f : Fin F, ∃ i j : Fin p,
        j.val = (i.val + 1) % p ∧
        (edgeEnds e = (faceVerts f i, faceVerts f j) ∨
          edgeEnds e = (faceVerts f j, faceVerts f i))) →
      (∀ e : Fin E, Set.ncard {f : Fin F | ∃ i j : Fin p,
        j.val = (i.val + 1) % p ∧
        (edgeEnds e = (faceVerts f i, faceVerts f j) ∨
          edgeEnds e = (faceVerts f j, faceVerts f i))} = 2) →
      (∀ e : Fin E, convexHull ℝ {verts (edgeEnds e).1, verts (edgeEnds e).2} ⊆ body) →
      (∀ f : Fin F, convexHull ℝ (verts '' Set.range (faceVerts f)) ⊆ body) →
      (∀ f : Fin F, Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin p, d = verts (faceVerts f i) - verts (faceVerts f j)}) ≤ 2) →
      (∀ f : Fin F, ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
        n ≠ 0 ∧ (∀ x ∈ body, inner (𝕜 := ℝ) n x ≤ c) ∧
        (∀ i : Fin p, inner (𝕜 := ℝ) n (verts (faceVerts f i)) = c)) →
      (∀ e₁ e₂ : Fin E,
        (edgeEnds e₁ = edgeEnds e₂ ∨ edgeEnds e₁ = (edgeEnds e₂).swap) → e₁ = e₂) →
      (∀ f₁ f₂ : Fin F, Set.range (faceVerts f₁) = Set.range (faceVerts f₂) → f₁ = f₂) →
      (∀ v : Fin V, verts v ∈ frontier body) →
      (∀ e : Fin E, convexHull ℝ {verts (edgeEnds e).1, verts (edgeEnds e).2} ⊆ frontier body) →
      (∀ f : Fin F, convexHull ℝ (verts '' Set.range (faceVerts f)) ⊆ frontier body) →
      (∀ x ∈ frontier body, ∃ f : Fin F,
        x ∈ convexHull ℝ (verts '' Set.range (faceVerts f))) →
      (∀ v : Fin V, Set.ncard {f : Fin F | ∃ i, faceVerts f i = v} = q) →
      2 * E = p * F → 2 * E = q * V →
      (V : ℤ) - (E : ℤ) + (F : ℤ) = 2 →
      ((p = 3 ∧ q = 3 ∧ V = 4 ∧ E = 6 ∧ F = 4) ∨
      (p = 4 ∧ q = 3 ∧ V = 8 ∧ E = 12 ∧ F = 6) ∨
      (p = 3 ∧ q = 4 ∧ V = 6 ∧ E = 12 ∧ F = 8) ∨
      (p = 5 ∧ q = 3 ∧ V = 20 ∧ E = 30 ∧ F = 12) ∨
      (p = 3 ∧ q = 5 ∧ V = 12 ∧ E = 30 ∧ F = 20))) ∧
    ((∃ (w : Fin 4 → EuclideanSpace ℝ (Fin 3)) (ee : Fin 6 → Fin 4 × Fin 4)
      (fv : Fin 4 → Fin 3 → Fin 4) (b : Set (EuclideanSpace ℝ (Fin 3)))
      (ll dd : ℝ),
      0 < ll ∧ 0 < dd ∧
      b = convexHull ℝ (Set.range w) ∧
      Convex ℝ b ∧
      (∀ v : Fin 4, w v ∈ frontier b) ∧
      (∀ v : Fin 4, w v ∉ convexHull ℝ (w '' {u : Fin 4 | u ≠ v})) ∧
      (Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 4, d = w i - w j}) = 3) ∧
      (∀ e : Fin 6, dist (w (ee e).1) (w (ee e).2) = ll) ∧
      (∀ (f : Fin 4) (i j : Fin 3), j.val = (i.val + 1) % 3 →
        dist (w (fv f i)) (w (fv f j)) = ll) ∧
      (∀ (f : Fin 4) (h i j : Fin 3), h.val = (i.val + 3 - 1) % 3 →
        j.val = (i.val + 1) % 3 → dist (w (fv f h)) (w (fv f j)) = dd) ∧
      (∀ f : Fin 4, Function.Injective (fv f)) ∧
      (∀ (f : Fin 4) (k : Fin 3), w (fv f k) ∉ convexHull ℝ
        (w '' (Set.range (fv f) \ {fv f k}))) ∧
      (∀ (f : Fin 4) (i₁ j₁ i₂ j₂ : Fin 3),
        j₁.val = (i₁.val + 1) % 3 →
        j₂.val = (i₂.val + 1) % 3 →
        i₁ ≠ i₂ → i₁ ≠ j₂ → j₁ ≠ i₂ → j₁ ≠ j₂ →
        Disjoint (convexHull ℝ {w (fv f i₁), w (fv f j₁)})
          (convexHull ℝ {w (fv f i₂), w (fv f j₂)})) ∧
      (∀ (f : Fin 4) (i j : Fin 3), j.val = (i.val + 1) % 3 →
        ∃ e : Fin 6, ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i)) ∧
      (∀ e : Fin 6, ∃ f : Fin 4, ∃ i j : Fin 3,
        j.val = (i.val + 1) % 3 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))) ∧
      (∀ e : Fin 6, Set.ncard {f : Fin 4 | ∃ i j : Fin 3,
        j.val = (i.val + 1) % 3 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))} = 2) ∧
      (∀ f : Fin 4, Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 3, d = w (fv f i) - w (fv f j)}) ≤ 2) ∧
      (∀ f : Fin 4, ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
        n ≠ 0 ∧ (∀ x ∈ b, inner (𝕜 := ℝ) n x ≤ c) ∧
        (∀ i : Fin 3, inner (𝕜 := ℝ) n (w (fv f i)) = c)) ∧
      (∀ e₁ e₂ : Fin 6, (ee e₁ = ee e₂ ∨ ee e₁ = (ee e₂).swap) → e₁ = e₂) ∧
      (∀ f₁ f₂ : Fin 4, Set.range (fv f₁) = Set.range (fv f₂) → f₁ = f₂) ∧
      (∀ e : Fin 6, convexHull ℝ {w (ee e).1, w (ee e).2} ⊆ frontier b) ∧
      (∀ f : Fin 4, convexHull ℝ (w '' Set.range (fv f)) ⊆ frontier b) ∧
      (∀ x ∈ frontier b, ∃ f : Fin 4,
        x ∈ convexHull ℝ (w '' Set.range (fv f))) ∧
      (∀ v : Fin 4, Set.ncard {f : Fin 4 | ∃ i : Fin 3, fv f i = v} = 3) ∧
      2 * 6 = 3 * 4 ∧ 2 * 6 = 3 * 4 ∧ (4 : ℤ) - (6 : ℤ) + (4 : ℤ) = 2) ∧
    (∃ (w : Fin 8 → EuclideanSpace ℝ (Fin 3)) (ee : Fin 12 → Fin 8 × Fin 8)
      (fv : Fin 6 → Fin 4 → Fin 8) (b : Set (EuclideanSpace ℝ (Fin 3)))
      (ll dd : ℝ),
      0 < ll ∧ 0 < dd ∧
      b = convexHull ℝ (Set.range w) ∧
      Convex ℝ b ∧
      (∀ v : Fin 8, w v ∈ frontier b) ∧
      (∀ v : Fin 8, w v ∉ convexHull ℝ (w '' {u : Fin 8 | u ≠ v})) ∧
      (Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 8, d = w i - w j}) = 3) ∧
      (∀ e : Fin 12, dist (w (ee e).1) (w (ee e).2) = ll) ∧
      (∀ (f : Fin 6) (i j : Fin 4), j.val = (i.val + 1) % 4 →
        dist (w (fv f i)) (w (fv f j)) = ll) ∧
      (∀ (f : Fin 6) (h i j : Fin 4), h.val = (i.val + 4 - 1) % 4 →
        j.val = (i.val + 1) % 4 → dist (w (fv f h)) (w (fv f j)) = dd) ∧
      (∀ f : Fin 6, Function.Injective (fv f)) ∧
      (∀ (f : Fin 6) (k : Fin 4), w (fv f k) ∉ convexHull ℝ
        (w '' (Set.range (fv f) \ {fv f k}))) ∧
      (∀ (f : Fin 6) (i₁ j₁ i₂ j₂ : Fin 4),
        j₁.val = (i₁.val + 1) % 4 →
        j₂.val = (i₂.val + 1) % 4 →
        i₁ ≠ i₂ → i₁ ≠ j₂ → j₁ ≠ i₂ → j₁ ≠ j₂ →
        Disjoint (convexHull ℝ {w (fv f i₁), w (fv f j₁)})
          (convexHull ℝ {w (fv f i₂), w (fv f j₂)})) ∧
      (∀ (f : Fin 6) (i j : Fin 4), j.val = (i.val + 1) % 4 →
        ∃ e : Fin 12, ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i)) ∧
      (∀ e : Fin 12, ∃ f : Fin 6, ∃ i j : Fin 4,
        j.val = (i.val + 1) % 4 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))) ∧
      (∀ e : Fin 12, Set.ncard {f : Fin 6 | ∃ i j : Fin 4,
        j.val = (i.val + 1) % 4 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))} = 2) ∧
      (∀ f : Fin 6, Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 4, d = w (fv f i) - w (fv f j)}) ≤ 2) ∧
      (∀ f : Fin 6, ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
        n ≠ 0 ∧ (∀ x ∈ b, inner (𝕜 := ℝ) n x ≤ c) ∧
        (∀ i : Fin 4, inner (𝕜 := ℝ) n (w (fv f i)) = c)) ∧
      (∀ e₁ e₂ : Fin 12, (ee e₁ = ee e₂ ∨ ee e₁ = (ee e₂).swap) → e₁ = e₂) ∧
      (∀ f₁ f₂ : Fin 6, Set.range (fv f₁) = Set.range (fv f₂) → f₁ = f₂) ∧
      (∀ e : Fin 12, convexHull ℝ {w (ee e).1, w (ee e).2} ⊆ frontier b) ∧
      (∀ f : Fin 6, convexHull ℝ (w '' Set.range (fv f)) ⊆ frontier b) ∧
      (∀ x ∈ frontier b, ∃ f : Fin 6,
        x ∈ convexHull ℝ (w '' Set.range (fv f))) ∧
      (∀ v : Fin 8, Set.ncard {f : Fin 6 | ∃ i : Fin 4, fv f i = v} = 3) ∧
      2 * 12 = 4 * 6 ∧ 2 * 12 = 3 * 8 ∧ (8 : ℤ) - (12 : ℤ) + (6 : ℤ) = 2) ∧
    (∃ (w : Fin 6 → EuclideanSpace ℝ (Fin 3)) (ee : Fin 12 → Fin 6 × Fin 6)
      (fv : Fin 8 → Fin 3 → Fin 6) (b : Set (EuclideanSpace ℝ (Fin 3)))
      (ll dd : ℝ),
      0 < ll ∧ 0 < dd ∧
      b = convexHull ℝ (Set.range w) ∧
      Convex ℝ b ∧
      (∀ v : Fin 6, w v ∈ frontier b) ∧
      (∀ v : Fin 6, w v ∉ convexHull ℝ (w '' {u : Fin 6 | u ≠ v})) ∧
      (Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 6, d = w i - w j}) = 3) ∧
      (∀ e : Fin 12, dist (w (ee e).1) (w (ee e).2) = ll) ∧
      (∀ (f : Fin 8) (i j : Fin 3), j.val = (i.val + 1) % 3 →
        dist (w (fv f i)) (w (fv f j)) = ll) ∧
      (∀ (f : Fin 8) (h i j : Fin 3), h.val = (i.val + 3 - 1) % 3 →
        j.val = (i.val + 1) % 3 → dist (w (fv f h)) (w (fv f j)) = dd) ∧
      (∀ f : Fin 8, Function.Injective (fv f)) ∧
      (∀ (f : Fin 8) (k : Fin 3), w (fv f k) ∉ convexHull ℝ
        (w '' (Set.range (fv f) \ {fv f k}))) ∧
      (∀ (f : Fin 8) (i₁ j₁ i₂ j₂ : Fin 3),
        j₁.val = (i₁.val + 1) % 3 →
        j₂.val = (i₂.val + 1) % 3 →
        i₁ ≠ i₂ → i₁ ≠ j₂ → j₁ ≠ i₂ → j₁ ≠ j₂ →
        Disjoint (convexHull ℝ {w (fv f i₁), w (fv f j₁)})
          (convexHull ℝ {w (fv f i₂), w (fv f j₂)})) ∧
      (∀ (f : Fin 8) (i j : Fin 3), j.val = (i.val + 1) % 3 →
        ∃ e : Fin 12, ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i)) ∧
      (∀ e : Fin 12, ∃ f : Fin 8, ∃ i j : Fin 3,
        j.val = (i.val + 1) % 3 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))) ∧
      (∀ e : Fin 12, Set.ncard {f : Fin 8 | ∃ i j : Fin 3,
        j.val = (i.val + 1) % 3 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))} = 2) ∧
      (∀ f : Fin 8, Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 3, d = w (fv f i) - w (fv f j)}) ≤ 2) ∧
      (∀ f : Fin 8, ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
        n ≠ 0 ∧ (∀ x ∈ b, inner (𝕜 := ℝ) n x ≤ c) ∧
        (∀ i : Fin 3, inner (𝕜 := ℝ) n (w (fv f i)) = c)) ∧
      (∀ e₁ e₂ : Fin 12, (ee e₁ = ee e₂ ∨ ee e₁ = (ee e₂).swap) → e₁ = e₂) ∧
      (∀ f₁ f₂ : Fin 8, Set.range (fv f₁) = Set.range (fv f₂) → f₁ = f₂) ∧
      (∀ e : Fin 12, convexHull ℝ {w (ee e).1, w (ee e).2} ⊆ frontier b) ∧
      (∀ f : Fin 8, convexHull ℝ (w '' Set.range (fv f)) ⊆ frontier b) ∧
      (∀ x ∈ frontier b, ∃ f : Fin 8,
        x ∈ convexHull ℝ (w '' Set.range (fv f))) ∧
      (∀ v : Fin 6, Set.ncard {f : Fin 8 | ∃ i : Fin 3, fv f i = v} = 4) ∧
      2 * 12 = 3 * 8 ∧ 2 * 12 = 4 * 6 ∧ (6 : ℤ) - (12 : ℤ) + (8 : ℤ) = 2) ∧
    (∃ (w : Fin 20 → EuclideanSpace ℝ (Fin 3)) (ee : Fin 30 → Fin 20 × Fin 20)
      (fv : Fin 12 → Fin 5 → Fin 20) (b : Set (EuclideanSpace ℝ (Fin 3)))
      (ll dd : ℝ),
      0 < ll ∧ 0 < dd ∧
      b = convexHull ℝ (Set.range w) ∧
      Convex ℝ b ∧
      (∀ v : Fin 20, w v ∈ frontier b) ∧
      (∀ v : Fin 20, w v ∉ convexHull ℝ (w '' {u : Fin 20 | u ≠ v})) ∧
      (Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 20, d = w i - w j}) = 3) ∧
      (∀ e : Fin 30, dist (w (ee e).1) (w (ee e).2) = ll) ∧
      (∀ (f : Fin 12) (i j : Fin 5), j.val = (i.val + 1) % 5 →
        dist (w (fv f i)) (w (fv f j)) = ll) ∧
      (∀ (f : Fin 12) (h i j : Fin 5), h.val = (i.val + 5 - 1) % 5 →
        j.val = (i.val + 1) % 5 → dist (w (fv f h)) (w (fv f j)) = dd) ∧
      (∀ f : Fin 12, Function.Injective (fv f)) ∧
      (∀ (f : Fin 12) (k : Fin 5), w (fv f k) ∉ convexHull ℝ
        (w '' (Set.range (fv f) \ {fv f k}))) ∧
      (∀ (f : Fin 12) (i₁ j₁ i₂ j₂ : Fin 5),
        j₁.val = (i₁.val + 1) % 5 →
        j₂.val = (i₂.val + 1) % 5 →
        i₁ ≠ i₂ → i₁ ≠ j₂ → j₁ ≠ i₂ → j₁ ≠ j₂ →
        Disjoint (convexHull ℝ {w (fv f i₁), w (fv f j₁)})
          (convexHull ℝ {w (fv f i₂), w (fv f j₂)})) ∧
      (∀ (f : Fin 12) (i j : Fin 5), j.val = (i.val + 1) % 5 →
        ∃ e : Fin 30, ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i)) ∧
      (∀ e : Fin 30, ∃ f : Fin 12, ∃ i j : Fin 5,
        j.val = (i.val + 1) % 5 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))) ∧
      (∀ e : Fin 30, Set.ncard {f : Fin 12 | ∃ i j : Fin 5,
        j.val = (i.val + 1) % 5 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))} = 2) ∧
      (∀ f : Fin 12, Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 5, d = w (fv f i) - w (fv f j)}) ≤ 2) ∧
      (∀ f : Fin 12, ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
        n ≠ 0 ∧ (∀ x ∈ b, inner (𝕜 := ℝ) n x ≤ c) ∧
        (∀ i : Fin 5, inner (𝕜 := ℝ) n (w (fv f i)) = c)) ∧
      (∀ e₁ e₂ : Fin 30, (ee e₁ = ee e₂ ∨ ee e₁ = (ee e₂).swap) → e₁ = e₂) ∧
      (∀ f₁ f₂ : Fin 12, Set.range (fv f₁) = Set.range (fv f₂) → f₁ = f₂) ∧
      (∀ e : Fin 30, convexHull ℝ {w (ee e).1, w (ee e).2} ⊆ frontier b) ∧
      (∀ f : Fin 12, convexHull ℝ (w '' Set.range (fv f)) ⊆ frontier b) ∧
      (∀ x ∈ frontier b, ∃ f : Fin 12,
        x ∈ convexHull ℝ (w '' Set.range (fv f))) ∧
      (∀ v : Fin 20, Set.ncard {f : Fin 12 | ∃ i : Fin 5, fv f i = v} = 3) ∧
      2 * 30 = 5 * 12 ∧ 2 * 30 = 3 * 20 ∧ (20 : ℤ) - (30 : ℤ) + (12 : ℤ) = 2) ∧
    (∃ (w : Fin 12 → EuclideanSpace ℝ (Fin 3)) (ee : Fin 30 → Fin 12 × Fin 12)
      (fv : Fin 20 → Fin 3 → Fin 12) (b : Set (EuclideanSpace ℝ (Fin 3)))
      (ll dd : ℝ),
      0 < ll ∧ 0 < dd ∧
      b = convexHull ℝ (Set.range w) ∧
      Convex ℝ b ∧
      (∀ v : Fin 12, w v ∈ frontier b) ∧
      (∀ v : Fin 12, w v ∉ convexHull ℝ (w '' {u : Fin 12 | u ≠ v})) ∧
      (Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 12, d = w i - w j}) = 3) ∧
      (∀ e : Fin 30, dist (w (ee e).1) (w (ee e).2) = ll) ∧
      (∀ (f : Fin 20) (i j : Fin 3), j.val = (i.val + 1) % 3 →
        dist (w (fv f i)) (w (fv f j)) = ll) ∧
      (∀ (f : Fin 20) (h i j : Fin 3), h.val = (i.val + 3 - 1) % 3 →
        j.val = (i.val + 1) % 3 → dist (w (fv f h)) (w (fv f j)) = dd) ∧
      (∀ f : Fin 20, Function.Injective (fv f)) ∧
      (∀ (f : Fin 20) (k : Fin 3), w (fv f k) ∉ convexHull ℝ
        (w '' (Set.range (fv f) \ {fv f k}))) ∧
      (∀ (f : Fin 20) (i₁ j₁ i₂ j₂ : Fin 3),
        j₁.val = (i₁.val + 1) % 3 →
        j₂.val = (i₂.val + 1) % 3 →
        i₁ ≠ i₂ → i₁ ≠ j₂ → j₁ ≠ i₂ → j₁ ≠ j₂ →
        Disjoint (convexHull ℝ {w (fv f i₁), w (fv f j₁)})
          (convexHull ℝ {w (fv f i₂), w (fv f j₂)})) ∧
      (∀ (f : Fin 20) (i j : Fin 3), j.val = (i.val + 1) % 3 →
        ∃ e : Fin 30, ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i)) ∧
      (∀ e : Fin 30, ∃ f : Fin 20, ∃ i j : Fin 3,
        j.val = (i.val + 1) % 3 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))) ∧
      (∀ e : Fin 30, Set.ncard {f : Fin 20 | ∃ i j : Fin 3,
        j.val = (i.val + 1) % 3 ∧
        (ee e = (fv f i, fv f j) ∨ ee e = (fv f j, fv f i))} = 2) ∧
      (∀ f : Fin 20, Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
        ∃ i j : Fin 3, d = w (fv f i) - w (fv f j)}) ≤ 2) ∧
      (∀ f : Fin 20, ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
        n ≠ 0 ∧ (∀ x ∈ b, inner (𝕜 := ℝ) n x ≤ c) ∧
        (∀ i : Fin 3, inner (𝕜 := ℝ) n (w (fv f i)) = c)) ∧
      (∀ e₁ e₂ : Fin 30, (ee e₁ = ee e₂ ∨ ee e₁ = (ee e₂).swap) → e₁ = e₂) ∧
      (∀ f₁ f₂ : Fin 20, Set.range (fv f₁) = Set.range (fv f₂) → f₁ = f₂) ∧
      (∀ e : Fin 30, convexHull ℝ {w (ee e).1, w (ee e).2} ⊆ frontier b) ∧
      (∀ f : Fin 20, convexHull ℝ (w '' Set.range (fv f)) ⊆ frontier b) ∧
      (∀ x ∈ frontier b, ∃ f : Fin 20,
        x ∈ convexHull ℝ (w '' Set.range (fv f))) ∧
      (∀ v : Fin 12, Set.ncard {f : Fin 20 | ∃ i : Fin 3, fv f i = v} = 5) ∧
      2 * 30 = 3 * 20 ∧ 2 * 30 = 5 * 12 ∧ (12 : ℤ) - (30 : ℤ) + (20 : ℤ) = 2))) := by
  constructor
  · -- Classification: only the counting hypotheses and Euler are needed.
    intro V E F p q verts edgeEnds faceVerts body l angleDiag
      hV hE hF hp hq hl hdiag hbody hconv hmem hconvexpos hdim hedge hfaceedge
      hdiag2 hinj hfaceconv hdisj hfaceedge2 hedgeface htwoface hedgebody
      hfacebody hplanar hsupp hedgedup hfacedup hfront hfrontedge hfrontface
      hcover hcount hcount1 hcount2 hEuler
    exact platonic_count_classification V E F p q hV hE hF hp hq hcount1 hcount2 hEuler
  · exact ⟨tet_exists, cube_exists, oct_exists, dod_exists, ico_exists⟩

end
end MetaMathlibExt
