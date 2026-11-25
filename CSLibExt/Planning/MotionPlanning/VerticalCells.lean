/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.ConfigurationSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

@[expose] public section

/-!
Supplied trapezoidal decomposition of open free space in the Euclidean plane:
open trapezoid/triangle 2-cells and open vertical-segment 1-cells (walls),
following LaValle, Planning Algorithms, Sec. 6.2.2 ("Defining the vertical
decomposition" and "General position issues"). Part 1: cell model basics
(nonempty, convex, open carriers), unique cell per point, and wall-in-closure
of incident trapezoids.
-/

namespace Cslib.Planning.MotionPlanning


namespace VerticalCells

/-- An affine endomap of `ℝ` preserves affine combinations. -/
lemma affine_combo (f : ℝ →ᵃ[ℝ] ℝ) (a b u v : ℝ) (hab : a + b = 1) :
    f (a * u + b * v) = a * f u + b * f v := by
  have ha : a = 1 - b := by linarith
  conv_lhs => rw [ha]
  rw [← AffineMap.lineMap_apply_ring, AffineMap.apply_lineMap,
    AffineMap.lineMap_apply_ring, ← ha]

/-- Strict inequalities are preserved under convex combinations in `ℝ`. -/
lemma combo_lt {a b u u' v v' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hu : u < u') (hv : v < v') : a * u + b * v < a * u' + b * v' := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    rw [hb1]
    simpa using hv
  · rcases eq_or_lt_of_le hb with rfl | hb'
    · have ha1 : a = 1 := by linarith
      rw [ha1]
      simpa using hu
    · exact add_lt_add (mul_lt_mul_of_pos_left hu ha') (mul_lt_mul_of_pos_left hv hb')

/-- Every affine endomap of `ℝ` is continuous. -/
lemma affineContinuous (f : ℝ →ᵃ[ℝ] ℝ) : Continuous f := by
  have h : ∀ t : ℝ, f t = f 0 + t * (f 1 - f 0) := by
    intro t
    have h := affine_combo f (1 - t) t 0 1 (by ring)
    simp only [mul_zero, mul_one, zero_add] at h
    rw [h]
    ring
  have hc : Continuous fun t : ℝ => f 0 + t * (f 1 - f 0) :=
    continuous_const.add (continuous_id.mul continuous_const)
  exact hc.congr (fun t => (h t).symm)

/-- Distance from a point to a `!₂` point sharing its second coordinate. -/
lemma dist_mkPoint (t : ℝ) (q : plane) : dist q (!₂[t, q 1] : plane) = |q 0 - t| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, dist_self, Real.dist_eq]
  norm_num [Real.sqrt_sq_eq_abs]

/-- Open trapezoid with vertical sides `x = x₁`, `x = x₂` and lower/upper sides on the
affine lines `bot`, `top`; a triangle when the lines meet at exactly one end.
LaValle, Planning Algorithms, Sec. 6.2.2: 2-cells are such open interiors. -/
structure VTrap where
  x₁ : ℝ
  x₂ : ℝ
  bot : ℝ →ᵃ[ℝ] ℝ
  top : ℝ →ᵃ[ℝ] ℝ
  x₁_lt_x₂ : x₁ < x₂
  bot_le_top₁ : bot x₁ ≤ top x₁
  bot_le_top₂ : bot x₂ ≤ top x₂
  nondegenerate : bot x₁ < top x₁ ∨ bot x₂ < top x₂

/-- The open region of the trapezoid/triangle. -/
def VTrap.carrier (T : VTrap) : Set plane :=
  {p | T.x₁ < p 0 ∧ p 0 < T.x₂ ∧ T.bot (p 0) < p 1 ∧ p 1 < T.top (p 0)}
def VTrap.lowerSide (T : VTrap) : Set plane :=
  {p | T.x₁ ≤ p 0 ∧ p 0 ≤ T.x₂ ∧ p 1 = T.bot (p 0)}
def VTrap.upperSide (T : VTrap) : Set plane :=
  {p | T.x₁ ≤ p 0 ∧ p 0 ≤ T.x₂ ∧ p 1 = T.top (p 0)}

/-- Open vertical segment `{x} × (y₁, y₂)`: a 1-cell (wall).
LaValle, Planning Algorithms, Sec. 6.2.2: 1-cells are such open interiors. -/
structure VSeg where
  x : ℝ
  y₁ : ℝ
  y₂ : ℝ
  y₁_lt_y₂ : y₁ < y₂

def VSeg.carrier (s : VSeg) : Set plane := {p | p 0 = s.x ∧ s.y₁ < p 1 ∧ p 1 < s.y₂}

/-- Wall `s` lies on the closed right side of `T` (`T` is left of the wall). -/
def VTrap.HasOnRight (T : VTrap) (s : VSeg) : Prop :=
  T.x₂ = s.x ∧ T.bot T.x₂ ≤ s.y₁ ∧ s.y₂ ≤ T.top T.x₂
/-- Wall `s` lies on the closed left side of `T`. -/
def VTrap.HasOnLeft (T : VTrap) (s : VSeg) : Prop :=
  T.x₁ = s.x ∧ T.bot T.x₁ ≤ s.y₁ ∧ s.y₂ ≤ T.top T.x₁

/-- A supplied trapezoidal decomposition of `F`: a finite cover by pairwise-disjoint
open 2-cells and 1-cells. Incidence/side facts are PROVED later, not fields.
LaValle, Planning Algorithms, Sec. 6.2.2. -/
structure TrapDecomp (F : Set plane) where
  m : ℕ
  k : ℕ
  trap : Fin m → VTrap
  wall : Fin k → VSeg
  pairwise_disjoint :
    Pairwise (Function.onFun Disjoint
      (Sum.elim (fun i => (trap i).carrier) (fun j => (wall j).carrier)))
  iUnion_eq : (⋃ i, (trap i).carrier) ∪ (⋃ j, (wall j).carrier) = F

/-- Index type of the cells of a decomposition: traps (`inl`) and walls (`inr`). -/
def TrapDecomp.Cell {F : Set plane} (D : TrapDecomp F) : Type := Fin D.m ⊕ Fin D.k

/-- Carrier of a cell, by cases. -/
def TrapDecomp.carrier {F : Set plane} (D : TrapDecomp F) : D.Cell → Set plane
  | .inl i => (D.trap i).carrier
  | .inr j => (D.wall j).carrier

/-- The case-split carrier agrees with the `Sum.elim` carrier in `pairwise_disjoint`. -/
lemma TrapDecomp.carrier_eq_elim {F : Set plane} (D : TrapDecomp F) (c : D.Cell) :
    D.carrier c = Sum.elim (fun i => (D.trap i).carrier)
      (fun j => (D.wall j).carrier) c := by
  cases c <;> rfl

/-- Restatement of `pairwise_disjoint` for the case-split carrier. -/
lemma TrapDecomp.carrier_disjoint {F : Set plane} (D : TrapDecomp F) (c₁ c₂ : D.Cell)
    (hne : c₁ ≠ c₂) : Disjoint (D.carrier c₁) (D.carrier c₂) := by
  rw [D.carrier_eq_elim c₁, D.carrier_eq_elim c₂]
  exact D.pairwise_disjoint hne

theorem VTrap.carrier_nonempty (T : VTrap) : T.carrier.Nonempty := by
  have hxm : (T.x₁ + T.x₂) / 2 = 1 / 2 * T.x₁ + 1 / 2 * T.x₂ := by ring
  have hbot : T.bot ((T.x₁ + T.x₂) / 2) = (T.bot T.x₁ + T.bot T.x₂) / 2 := by
    rw [hxm, affine_combo _ _ _ _ _ (by norm_num)]
    ring
  have htop : T.top ((T.x₁ + T.x₂) / 2) = (T.top T.x₁ + T.top T.x₂) / 2 := by
    rw [hxm, affine_combo _ _ _ _ _ (by norm_num)]
    ring
  have hlt : T.bot ((T.x₁ + T.x₂) / 2) < T.top ((T.x₁ + T.x₂) / 2) := by
    rw [hbot, htop]
    rcases T.nondegenerate with h | h
    · have h' := add_lt_add_of_lt_of_le h T.bot_le_top₂
      linarith
    · have h' := add_lt_add_of_le_of_lt T.bot_le_top₁ h
      linarith
  simp only [VTrap.carrier]
  refine ⟨!₂[(T.x₁ + T.x₂) / 2,
    (T.bot ((T.x₁ + T.x₂) / 2) + T.top ((T.x₁ + T.x₂) / 2)) / 2], ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.cons_val_zero]
    linarith [T.x₁_lt_x₂]
  · simp only [Matrix.cons_val_zero]
    linarith [T.x₁_lt_x₂]
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith [hlt]
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith [hlt]

theorem VTrap.convex_carrier (T : VTrap) : Convex ℝ T.carrier := by
  intro x hx y hy a b ha hb hab
  simp only [VTrap.carrier] at hx hy ⊢
  obtain ⟨hx1, hx2, hxb, hxt⟩ := hx
  obtain ⟨hy1, hy2, hyb, hyt⟩ := hy
  have h0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have h1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h0]
    have h := (convex_Ioi T.x₁) hx1 hy1 ha hb hab
    simpa [Set.mem_Ioi, smul_eq_mul] using h
  · rw [h0]
    have h := (convex_Iio T.x₂) hx2 hy2 ha hb hab
    simpa [Set.mem_Iio, smul_eq_mul] using h
  · rw [h0, h1, affine_combo T.bot a b _ _ hab]
    exact combo_lt ha hb hab hxb hyb
  · rw [h0, h1, affine_combo T.top a b _ _ hab]
    exact combo_lt ha hb hab hxt hyt

theorem VTrap.isOpen_carrier (T : VTrap) : IsOpen T.carrier := by
  have hc0 : Continuous fun p : plane => p 0 := PiLp.continuous_apply 2 _ 0
  have hc1 : Continuous fun p : plane => p 1 := PiLp.continuous_apply 2 _ 1
  have hbot : Continuous fun p : plane => T.bot (p 0) :=
    (affineContinuous T.bot).comp hc0
  have htop : Continuous fun p : plane => T.top (p 0) :=
    (affineContinuous T.top).comp hc0
  have h1 : IsOpen {p : plane | T.x₁ < p 0} := isOpen_lt continuous_const hc0
  have h2 : IsOpen {p : plane | p 0 < T.x₂} := isOpen_lt hc0 continuous_const
  have h3 : IsOpen {p : plane | T.bot (p 0) < p 1} := isOpen_lt hbot hc1
  have h4 : IsOpen {p : plane | p 1 < T.top (p 0)} := isOpen_lt hc1 htop
  simp only [VTrap.carrier, Set.ofPred_and]
  exact h1.and (h2.and (h3.and h4))

theorem VSeg.carrier_nonempty (s : VSeg) : s.carrier.Nonempty := by
  simp only [VSeg.carrier]
  refine ⟨!₂[s.x, (s.y₁ + s.y₂) / 2], ?_, ?_, ?_⟩
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith [s.y₁_lt_y₂]
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith [s.y₁_lt_y₂]

theorem VSeg.convex_carrier (s : VSeg) : Convex ℝ s.carrier := by
  intro x hx y hy a b ha hb hab
  simp only [VSeg.carrier] at hx hy ⊢
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hy0, hy1, hy2⟩ := hy
  have h0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have h1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [h0, hx0, hy0, ← add_mul, hab, one_mul]
  · rw [h1]
    have h := (convex_Ioi s.y₁) hx1 hy1 ha hb hab
    simpa [Set.mem_Ioi, smul_eq_mul] using h
  · rw [h1]
    have h := (convex_Iio s.y₂) hx2 hy2 ha hb hab
    simpa [Set.mem_Iio, smul_eq_mul] using h

theorem TrapDecomp.existsUnique_cell {F : Set plane} (D : TrapDecomp F) (p : plane) (hp : p ∈ F) :
    ∃! c : D.Cell, p ∈ D.carrier c := by
  have huniq : ∀ {c₁ c₂ : D.Cell}, p ∈ D.carrier c₁ → p ∈ D.carrier c₂ → c₁ = c₂ := by
    intro c₁ c₂ h₁ h₂
    by_contra hne
    have hd := D.carrier_disjoint c₁ c₂ hne
    exact (Set.disjoint_left.mp hd h₁) h₂
  rw [← D.iUnion_eq] at hp
  simp only [Set.mem_union, Set.mem_iUnion] at hp
  obtain (⟨i, hi⟩ | ⟨j, hj⟩) := hp
  · exact ⟨.inl i, hi, fun c hc => huniq hc hi⟩
  · exact ⟨.inr j, hj, fun c hc => huniq hc hj⟩

theorem TrapDecomp.cell_nonempty {F : Set plane} (D : TrapDecomp F) (c : D.Cell) :
    (D.carrier c).Nonempty := by
  cases c with
  | inl i => exact (D.trap i).carrier_nonempty
  | inr j => exact (D.wall j).carrier_nonempty

theorem TrapDecomp.wall_subset_closure_of_hasOnRight {F : Set plane} (D : TrapDecomp F)
    {i : Fin D.m} {j : Fin D.k} (h : (D.trap i).HasOnRight (D.wall j)) :
    (D.wall j).carrier ⊆ closure (D.trap i).carrier := by
  obtain ⟨hx, hbot, htop⟩ := h
  intro q hq
  simp only [VSeg.carrier] at hq
  obtain ⟨hq0, hqy1, hqy2⟩ := hq
  have hq0' : q 0 = (D.trap i).x₂ := by rw [hq0, hx]
  -- The wall carrier is open, so the endpoint cases `q 1 = s.y₁`/`q 1 = s.y₂` are
  -- excluded: the strict `s.y₁ < q 1 < s.y₂` below leaves a positive buffer to the
  -- trapezoid's lower/upper sides at the wall line.
  have g1 : (D.trap i).bot ((D.trap i).x₂) < q 1 := lt_of_le_of_lt hbot hqy1
  have g2 : q 1 < (D.trap i).top ((D.trap i).x₂) := lt_of_lt_of_le hqy2 htop
  have hcb := Metric.continuousAt_iff.mp ((affineContinuous (D.trap i).bot).continuousAt (x := (D.trap i).x₂))
  have hct := Metric.continuousAt_iff.mp ((affineContinuous (D.trap i).top).continuousAt (x := (D.trap i).x₂))
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hcb (q 1 - (D.trap i).bot ((D.trap i).x₂)) (by linarith)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hct ((D.trap i).top ((D.trap i).x₂) - q 1) (by linarith)
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ := min δ₁ (min δ₂ (min ((D.trap i).x₂ - (D.trap i).x₁) ε)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    simp only [lt_min_iff]
    exact ⟨hδ₁pos, hδ₂pos, sub_pos.mpr (D.trap i).x₁_lt_x₂, hε⟩
  have hδ1 : δ ≤ δ₁ := by rw [hδ]; exact min_le_left _ _
  have hδ2 : δ ≤ δ₂ := by
    rw [hδ]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hδx : δ ≤ (D.trap i).x₂ - (D.trap i).x₁ := by
    rw [hδ]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδε : δ ≤ ε := by
    rw [hδ]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- Approximating point strictly left of the wall line.
  set t : ℝ := (D.trap i).x₂ - δ / 2 with ht
  have ht_lt : t < (D.trap i).x₂ := by rw [ht]; linarith
  have ht_gt : (D.trap i).x₁ < t := by rw [ht]; linarith
  have habs : |t - (D.trap i).x₂| = δ / 2 := by
    have e : t - (D.trap i).x₂ = -(δ / 2) := by rw [ht]; ring
    rw [e, abs_neg, abs_of_pos (half_pos hδpos)]
  have hdist0 : dist t ((D.trap i).x₂) < δ₁ := by
    rw [Real.dist_eq, habs]
    linarith
  have hdist0' : dist t ((D.trap i).x₂) < δ₂ := by
    rw [Real.dist_eq, habs]
    linarith
  have hblt : (D.trap i).bot t < q 1 := by
    have h := hδ₁ hdist0
    rw [Real.dist_eq] at h
    have h2 := (abs_lt.mp h).2
    linarith
  have hblt' : q 1 < (D.trap i).top t := by
    have h := hδ₂ hdist0'
    rw [Real.dist_eq] at h
    have h2 := (abs_lt.mp h).1
    linarith
  refine ⟨!₂[t, q 1], ?_, ?_⟩
  · simp only [VTrap.carrier]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Matrix.cons_val_zero]
      exact ht_gt
    · simp only [Matrix.cons_val_zero]
      exact ht_lt
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact hblt
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact hblt'
  · rw [dist_mkPoint, hq0']
    have habs2 : |(D.trap i).x₂ - t| = δ / 2 := by
      have e : (D.trap i).x₂ - t = δ / 2 := by rw [ht]; ring
      rw [e, abs_of_pos (half_pos hδpos)]
    rw [habs2]
    linarith

theorem TrapDecomp.wall_subset_closure_of_hasOnLeft {F : Set plane} (D : TrapDecomp F)
    {i : Fin D.m} {j : Fin D.k} (h : (D.trap i).HasOnLeft (D.wall j)) :
    (D.wall j).carrier ⊆ closure (D.trap i).carrier := by
  obtain ⟨hx, hbot, htop⟩ := h
  intro q hq
  simp only [VSeg.carrier] at hq
  obtain ⟨hq0, hqy1, hqy2⟩ := hq
  have hq0' : q 0 = (D.trap i).x₁ := by rw [hq0, hx]
  -- The wall carrier is open, so the endpoint cases `q 1 = s.y₁`/`q 1 = s.y₂` are
  -- excluded: the strict `s.y₁ < q 1 < s.y₂` below leaves a positive buffer to the
  -- trapezoid's lower/upper sides at the wall line.
  have g1 : (D.trap i).bot ((D.trap i).x₁) < q 1 := lt_of_le_of_lt hbot hqy1
  have g2 : q 1 < (D.trap i).top ((D.trap i).x₁) := lt_of_lt_of_le hqy2 htop
  have hcb := Metric.continuousAt_iff.mp ((affineContinuous (D.trap i).bot).continuousAt (x := (D.trap i).x₁))
  have hct := Metric.continuousAt_iff.mp ((affineContinuous (D.trap i).top).continuousAt (x := (D.trap i).x₁))
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hcb (q 1 - (D.trap i).bot ((D.trap i).x₁)) (by linarith)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hct ((D.trap i).top ((D.trap i).x₁) - q 1) (by linarith)
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ := min δ₁ (min δ₂ (min ((D.trap i).x₂ - (D.trap i).x₁) ε)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    simp only [lt_min_iff]
    exact ⟨hδ₁pos, hδ₂pos, sub_pos.mpr (D.trap i).x₁_lt_x₂, hε⟩
  have hδ1 : δ ≤ δ₁ := by rw [hδ]; exact min_le_left _ _
  have hδ2 : δ ≤ δ₂ := by
    rw [hδ]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hδx : δ ≤ (D.trap i).x₂ - (D.trap i).x₁ := by
    rw [hδ]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδε : δ ≤ ε := by
    rw [hδ]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- Approximating point strictly right of the wall line.
  set t : ℝ := (D.trap i).x₁ + δ / 2 with ht
  have ht_lt : t < (D.trap i).x₂ := by rw [ht]; linarith
  have ht_gt : (D.trap i).x₁ < t := by rw [ht]; linarith
  have habs : |t - (D.trap i).x₁| = δ / 2 := by
    have e : t - (D.trap i).x₁ = δ / 2 := by rw [ht]; ring
    rw [e, abs_of_pos (half_pos hδpos)]
  have hdist0 : dist t ((D.trap i).x₁) < δ₁ := by
    rw [Real.dist_eq, habs]
    linarith
  have hdist0' : dist t ((D.trap i).x₁) < δ₂ := by
    rw [Real.dist_eq, habs]
    linarith
  have hblt : (D.trap i).bot t < q 1 := by
    have h := hδ₁ hdist0
    rw [Real.dist_eq] at h
    have h2 := (abs_lt.mp h).2
    linarith
  have hblt' : q 1 < (D.trap i).top t := by
    have h := hδ₂ hdist0'
    rw [Real.dist_eq] at h
    have h2 := (abs_lt.mp h).1
    linarith
  refine ⟨!₂[t, q 1], ?_, ?_⟩
  · simp only [VTrap.carrier]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Matrix.cons_val_zero]
      exact ht_gt
    · simp only [Matrix.cons_val_zero]
      exact ht_lt
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact hblt
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact hblt'
  · rw [dist_mkPoint, hq0']
    have habs2 : |(D.trap i).x₁ - t| = δ / 2 := by
      have e : (D.trap i).x₁ - t = -(δ / 2) := by rw [ht]; ring
      rw [e, abs_neg, abs_of_pos (half_pos hδpos)]
    rw [habs2]
    linarith

/-- On the open `x`-interval the upper side is strictly above the lower side.
LaValle, Planning Algorithms, Sec. 6.2.2. -/
theorem VTrap.interior_bot_lt_top (T : VTrap) (x : ℝ) (hx₁ : T.x₁ < x)
    (hx₂ : x < T.x₂) : T.bot x < T.top x := by
  have hw : 0 < T.x₂ - T.x₁ := sub_pos.mpr T.x₁_lt_x₂
  have hwne : T.x₂ - T.x₁ ≠ 0 := ne_of_gt hw
  have ha_pos : 0 < (T.x₂ - x) / (T.x₂ - T.x₁) := div_pos (by linarith) hw
  have hb_pos : 0 < (x - T.x₁) / (T.x₂ - T.x₁) := div_pos (by linarith) hw
  have hab : (T.x₂ - x) / (T.x₂ - T.x₁) + (x - T.x₁) / (T.x₂ - T.x₁) = 1 := by
    rw [← add_div]
    have hnum : T.x₂ - x + (x - T.x₁) = T.x₂ - T.x₁ := by ring
    rw [hnum, div_self hwne]
  have hxeq : (T.x₂ - x) / (T.x₂ - T.x₁) * T.x₁
      + (x - T.x₁) / (T.x₂ - T.x₁) * T.x₂ = x := by
    field_simp
    ring
  have hbot := affine_combo T.bot _ _ T.x₁ T.x₂ hab
  have htop := affine_combo T.top _ _ T.x₁ T.x₂ hab
  rw [hxeq] at hbot htop
  rcases T.nondegenerate with h | h
  · rw [hbot, htop]
    exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h ha_pos)
      (mul_le_mul_of_nonneg_left T.bot_le_top₂ (le_of_lt hb_pos))
  · rw [hbot, htop]
    exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left T.bot_le_top₁ (le_of_lt ha_pos))
      (mul_lt_mul_of_pos_left h hb_pos)

/-- Distance between `!₂` points sharing the first coordinate. -/
lemma dist_mkPoint_left (x a b : ℝ) :
    dist (!₂[x, a] : plane) (!₂[x, b] : plane) = |a - b| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, dist_self, Real.dist_eq]
  norm_num [Real.sqrt_sq_eq_abs]

/-- Distance from a `!₂` point sharing a point's first coordinate. -/
lemma dist_mkPoint_fst (y : ℝ) (q : plane) :
    dist (!₂[q 0, y] : plane) q = |y - q 1| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, dist_self, Real.dist_eq]
  norm_num [Real.sqrt_sq_eq_abs]

/-- A trapezoid carrier is contained in the decomposed set. -/
theorem TrapDecomp.trap_carrier_subset {F : Set plane} (D : TrapDecomp F) (i : Fin D.m) :
    (D.trap i).carrier ⊆ F := by
  intro p hp
  rw [← D.iUnion_eq]
  simp only [Set.mem_union, Set.mem_iUnion]
  exact Or.inl ⟨i, hp⟩

/-- A wall carrier is contained in the decomposed set. -/
theorem TrapDecomp.wall_carrier_subset {F : Set plane} (D : TrapDecomp F) (j : Fin D.k) :
    (D.wall j).carrier ⊆ F := by
  intro p hp
  rw [← D.iUnion_eq]
  simp only [Set.mem_union, Set.mem_iUnion]
  exact Or.inr ⟨j, hp⟩

/-- A lower-side point strictly inside the `x`-range and off every wall line is in no
cell, hence outside `F`. LaValle, Planning Algorithms, Sec. 6.2.2. -/
theorem TrapDecomp.lowerSide_generic_not_mem {F : Set plane} (D : TrapDecomp F)
    (i : Fin D.m) (q : plane) (hq : q ∈ (D.trap i).lowerSide)
    (hx₁ : (D.trap i).x₁ < q 0) (hx₂ : q 0 < (D.trap i).x₂)
    (hwall : ∀ j : Fin D.k, q 0 ≠ (D.wall j).x) : q ∉ F := by
  intro hF
  obtain ⟨c, hc, -⟩ := D.existsUnique_cell q hF
  cases c with
  | inl i' =>
    have hc' : q ∈ (D.trap i').carrier := hc
    by_cases heq : i' = i
    · subst heq
      simp only [VTrap.carrier] at hc'
      simp only [VTrap.lowerSide] at hq
      obtain ⟨_, _, hbot, _⟩ := hc'
      obtain ⟨_, _, hside⟩ := hq
      linarith
    · have hopen := (D.trap i').isOpen_carrier
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen q hc'
      simp only [VTrap.lowerSide] at hq
      obtain ⟨_, _, hside⟩ := hq
      have hgap : 0 < (D.trap i).top (q 0) - q 1 := by
        have h := (D.trap i).interior_bot_lt_top (q 0) hx₁ hx₂
        linarith
      have htε : min (ε / 2) (((D.trap i).top (q 0) - q 1) / 2) < ε :=
        lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
      have htgap : min (ε / 2) (((D.trap i).top (q 0) - q 1) / 2)
          < (D.trap i).top (q 0) - q 1 :=
        lt_of_le_of_lt (min_le_right _ _) (half_lt_self hgap)
      have htpos : 0 < min (ε / 2) (((D.trap i).top (q 0) - q 1) / 2) :=
        lt_min (half_pos hε) (half_pos hgap)
      set t : ℝ := min (ε / 2) (((D.trap i).top (q 0) - q 1) / 2) with ht
      have hr_mem_i' : (!₂[q 0, q 1 + t] : plane) ∈ (D.trap i').carrier := by
        apply hball
        rw [Metric.mem_ball, dist_mkPoint_fst]
        have habs : |q 1 + t - q 1| = t := by
          rw [add_sub_cancel_left, abs_of_pos htpos]
        rw [habs]
        exact htε
      have hr_mem_i : (!₂[q 0, q 1 + t] : plane) ∈ (D.trap i).carrier := by
        simp only [VTrap.carrier]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [Matrix.cons_val_zero]
          exact hx₁
        · simp only [Matrix.cons_val_zero]
          exact hx₂
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
      have hne : (Sum.inl i : D.Cell) ≠ Sum.inl i' := by
        intro h
        simp only [Sum.inl.injEq] at h
        exact heq h.symm
      have hd := D.carrier_disjoint (Sum.inl i) (Sum.inl i') hne
      exact (Set.disjoint_left.mp hd hr_mem_i) hr_mem_i'
  | inr j =>
    have hc' : q ∈ (D.wall j).carrier := hc
    simp only [VSeg.carrier] at hc'
    obtain ⟨hq0, _, _⟩ := hc'
    exact hwall j hq0

/-- Near any lower-side point there are generic lower-side points: strictly inside
the `x`-range and off every wall line. LaValle, Planning Algorithms, Sec. 6.2.2. -/
theorem TrapDecomp.exists_lowerSide_generic_near {F : Set plane} (D : TrapDecomp F)
    (i : Fin D.m) (p : plane) (hp : p ∈ (D.trap i).lowerSide) (δ : ℝ) (hδ : 0 < δ) :
    ∃ q : plane, q ∈ (D.trap i).lowerSide ∧ dist q p < δ ∧
      (D.trap i).x₁ < q 0 ∧ q 0 < (D.trap i).x₂ ∧ ∀ j : Fin D.k, q 0 ≠ (D.wall j).x := by
  simp only [VTrap.lowerSide] at hp
  obtain ⟨hp1, hp2, hpbot⟩ := hp
  have hcb := Metric.continuousAt_iff.mp
    ((affineContinuous (D.trap i).bot).continuousAt (x := p 0))
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hcb (δ / 2) (half_pos hδ)
  have hρpos : 0 < min δ₁ (δ / 2) := lt_min hδ₁pos (half_pos hδ)
  have hρ1 : min δ₁ (δ / 2) ≤ δ₁ := min_le_left _ _
  have hρ2 : min δ₁ (δ / 2) ≤ δ / 2 := min_le_right _ _
  set ρ : ℝ := min δ₁ (δ / 2) with hρ
  have hI : max (D.trap i).x₁ (p 0 - ρ) < min (D.trap i).x₂ (p 0 + ρ) := by
    simp only [max_lt_iff, lt_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact (D.trap i).x₁_lt_x₂
    · linarith
    · linarith
    · linarith
  have hInf := Set.Ioo_infinite hI
  have hFin := Set.finite_range (fun j : Fin D.k => (D.wall j).x)
  have hDiff := hInf.sdiff hFin
  obtain ⟨x, hx⟩ := hDiff.nonempty
  simp only [Set.mem_sdiff, Set.mem_Ioo, Set.mem_range] at hx
  obtain ⟨⟨hxlo, hxhi⟩, hxavoid⟩ := hx
  have hx1 : (D.trap i).x₁ < x := lt_of_le_of_lt (le_max_left _ _) hxlo
  have hx2 : x < (D.trap i).x₂ := lt_of_lt_of_le hxhi (min_le_left _ _)
  have hxp_lo : p 0 - ρ < x := lt_of_le_of_lt (le_max_right _ _) hxlo
  have hxp_hi : x < p 0 + ρ := lt_of_lt_of_le hxhi (min_le_right _ _)
  have hxdist : dist x (p 0) < ρ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hxbot : |(D.trap i).bot x - (D.trap i).bot (p 0)| < δ / 2 := by
    have h := hδ₁ (lt_of_lt_of_le hxdist hρ1)
    rwa [Real.dist_eq] at h
  have hxabs : |x - p 0| < δ / 2 := lt_of_lt_of_le (by rwa [Real.dist_eq] at hxdist) hρ2
  refine ⟨!₂[x, (D.trap i).bot x], ?_, ?_, hx1, hx2, ?_⟩
  · simp only [VTrap.lowerSide]
    refine ⟨?_, ?_, ?_⟩
    · simp only [Matrix.cons_val_zero]
      exact le_of_lt hx1
    · simp only [Matrix.cons_val_zero]
      exact le_of_lt hx2
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  · have htri := dist_triangle (!₂[x, (D.trap i).bot x] : plane) (!₂[x, p 1] : plane) p
    have hd1 : dist (!₂[x, (D.trap i).bot x] : plane) (!₂[x, p 1] : plane)
        = |(D.trap i).bot x - p 1| := dist_mkPoint_left x _ _
    have hd2 : dist (!₂[x, p 1] : plane) p = |x - p 0| := by
      rw [dist_comm, dist_mkPoint]
      exact abs_sub_comm _ _
    rw [hd1, hd2, hpbot] at htri
    linarith
  · intro j hj
    simp only [Matrix.cons_val_zero] at hj
    exact hxavoid ⟨j, hj.symm⟩

theorem TrapDecomp.lowerSide_disjoint {F : Set plane} (D : TrapDecomp F) (hF : IsOpen F)
    (i : Fin D.m) : Disjoint (D.trap i).lowerSide F := by
  rw [Set.disjoint_left]
  intro p hp hpF
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hF p hpF
  obtain ⟨q, hqside, hqdist, hqx1, hqx2, hqavoid⟩ :=
    D.exists_lowerSide_generic_near i p hp ε hε
  have hqF : q ∈ F := hball (Metric.mem_ball.mpr hqdist)
  exact (D.lowerSide_generic_not_mem i q hqside hqx1 hqx2 hqavoid) hqF

/-- An upper-side point strictly inside the `x`-range and off every wall line is in no
cell, hence outside `F`. LaValle, Planning Algorithms, Sec. 6.2.2. -/
theorem TrapDecomp.upperSide_generic_not_mem {F : Set plane} (D : TrapDecomp F)
    (i : Fin D.m) (q : plane) (hq : q ∈ (D.trap i).upperSide)
    (hx₁ : (D.trap i).x₁ < q 0) (hx₂ : q 0 < (D.trap i).x₂)
    (hwall : ∀ j : Fin D.k, q 0 ≠ (D.wall j).x) : q ∉ F := by
  intro hF
  obtain ⟨c, hc, -⟩ := D.existsUnique_cell q hF
  cases c with
  | inl i' =>
    have hc' : q ∈ (D.trap i').carrier := hc
    by_cases heq : i' = i
    · subst heq
      simp only [VTrap.carrier] at hc'
      simp only [VTrap.upperSide] at hq
      obtain ⟨_, _, _, htop⟩ := hc'
      obtain ⟨_, _, hside⟩ := hq
      linarith
    · have hopen := (D.trap i').isOpen_carrier
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen q hc'
      simp only [VTrap.upperSide] at hq
      obtain ⟨_, _, hside⟩ := hq
      have hgap : 0 < q 1 - (D.trap i).bot (q 0) := by
        have h := (D.trap i).interior_bot_lt_top (q 0) hx₁ hx₂
        linarith
      have htε : min (ε / 2) ((q 1 - (D.trap i).bot (q 0)) / 2) < ε :=
        lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
      have htgap : min (ε / 2) ((q 1 - (D.trap i).bot (q 0)) / 2)
          < q 1 - (D.trap i).bot (q 0) :=
        lt_of_le_of_lt (min_le_right _ _) (half_lt_self hgap)
      have htpos : 0 < min (ε / 2) ((q 1 - (D.trap i).bot (q 0)) / 2) :=
        lt_min (half_pos hε) (half_pos hgap)
      set t : ℝ := min (ε / 2) ((q 1 - (D.trap i).bot (q 0)) / 2) with ht
      have hr_mem_i' : (!₂[q 0, q 1 - t] : plane) ∈ (D.trap i').carrier := by
        apply hball
        rw [Metric.mem_ball, dist_mkPoint_fst]
        have habs : |q 1 - t - q 1| = t := by
          have he : q 1 - t - q 1 = -t := by ring
          rw [he, abs_neg, abs_of_pos htpos]
        rw [habs]
        exact htε
      have hr_mem_i : (!₂[q 0, q 1 - t] : plane) ∈ (D.trap i).carrier := by
        simp only [VTrap.carrier]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [Matrix.cons_val_zero]
          exact hx₁
        · simp only [Matrix.cons_val_zero]
          exact hx₂
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
      have hne : (Sum.inl i : D.Cell) ≠ Sum.inl i' := by
        intro h
        simp only [Sum.inl.injEq] at h
        exact heq h.symm
      have hd := D.carrier_disjoint (Sum.inl i) (Sum.inl i') hne
      exact (Set.disjoint_left.mp hd hr_mem_i) hr_mem_i'
  | inr j =>
    have hc' : q ∈ (D.wall j).carrier := hc
    simp only [VSeg.carrier] at hc'
    obtain ⟨hq0, _, _⟩ := hc'
    exact hwall j hq0

/-- Near any upper-side point there are generic upper-side points: strictly inside
the `x`-range and off every wall line. LaValle, Planning Algorithms, Sec. 6.2.2. -/
theorem TrapDecomp.exists_upperSide_generic_near {F : Set plane} (D : TrapDecomp F)
    (i : Fin D.m) (p : plane) (hp : p ∈ (D.trap i).upperSide) (δ : ℝ) (hδ : 0 < δ) :
    ∃ q : plane, q ∈ (D.trap i).upperSide ∧ dist q p < δ ∧
      (D.trap i).x₁ < q 0 ∧ q 0 < (D.trap i).x₂ ∧ ∀ j : Fin D.k, q 0 ≠ (D.wall j).x := by
  simp only [VTrap.upperSide] at hp
  obtain ⟨hp1, hp2, hptop⟩ := hp
  have hcb := Metric.continuousAt_iff.mp
    ((affineContinuous (D.trap i).top).continuousAt (x := p 0))
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hcb (δ / 2) (half_pos hδ)
  have hρpos : 0 < min δ₁ (δ / 2) := lt_min hδ₁pos (half_pos hδ)
  have hρ1 : min δ₁ (δ / 2) ≤ δ₁ := min_le_left _ _
  have hρ2 : min δ₁ (δ / 2) ≤ δ / 2 := min_le_right _ _
  set ρ : ℝ := min δ₁ (δ / 2) with hρ
  have hI : max (D.trap i).x₁ (p 0 - ρ) < min (D.trap i).x₂ (p 0 + ρ) := by
    simp only [max_lt_iff, lt_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact (D.trap i).x₁_lt_x₂
    · linarith
    · linarith
    · linarith
  have hInf := Set.Ioo_infinite hI
  have hFin := Set.finite_range (fun j : Fin D.k => (D.wall j).x)
  have hDiff := hInf.sdiff hFin
  obtain ⟨x, hx⟩ := hDiff.nonempty
  simp only [Set.mem_sdiff, Set.mem_Ioo, Set.mem_range] at hx
  obtain ⟨⟨hxlo, hxhi⟩, hxavoid⟩ := hx
  have hx1 : (D.trap i).x₁ < x := lt_of_le_of_lt (le_max_left _ _) hxlo
  have hx2 : x < (D.trap i).x₂ := lt_of_lt_of_le hxhi (min_le_left _ _)
  have hxp_lo : p 0 - ρ < x := lt_of_le_of_lt (le_max_right _ _) hxlo
  have hxp_hi : x < p 0 + ρ := lt_of_lt_of_le hxhi (min_le_right _ _)
  have hxdist : dist x (p 0) < ρ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hxtop : |(D.trap i).top x - (D.trap i).top (p 0)| < δ / 2 := by
    have h := hδ₁ (lt_of_lt_of_le hxdist hρ1)
    rwa [Real.dist_eq] at h
  have hxabs : |x - p 0| < δ / 2 := lt_of_lt_of_le (by rwa [Real.dist_eq] at hxdist) hρ2
  refine ⟨!₂[x, (D.trap i).top x], ?_, ?_, hx1, hx2, ?_⟩
  · simp only [VTrap.upperSide]
    refine ⟨?_, ?_, ?_⟩
    · simp only [Matrix.cons_val_zero]
      exact le_of_lt hx1
    · simp only [Matrix.cons_val_zero]
      exact le_of_lt hx2
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  · have htri := dist_triangle (!₂[x, (D.trap i).top x] : plane) (!₂[x, p 1] : plane) p
    have hd1 : dist (!₂[x, (D.trap i).top x] : plane) (!₂[x, p 1] : plane)
        = |(D.trap i).top x - p 1| := dist_mkPoint_left x _ _
    have hd2 : dist (!₂[x, p 1] : plane) p = |x - p 0| := by
      rw [dist_comm, dist_mkPoint]
      exact abs_sub_comm _ _
    rw [hd1, hd2, hptop] at htri
    linarith
  · intro j hj
    simp only [Matrix.cons_val_zero] at hj
    exact hxavoid ⟨j, hj.symm⟩

theorem TrapDecomp.upperSide_disjoint {F : Set plane} (D : TrapDecomp F) (hF : IsOpen F)
    (i : Fin D.m) : Disjoint (D.trap i).upperSide F := by
  rw [Set.disjoint_left]
  intro p hp hpF
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hF p hpF
  obtain ⟨q, hqside, hqdist, hqx1, hqx2, hqavoid⟩ :=
    D.exists_upperSide_generic_near i p hp ε hε
  have hqF : q ∈ F := hball (Metric.mem_ball.mpr hqdist)
  exact (D.upperSide_generic_not_mem i q hqside hqx1 hqx2 hqavoid) hqF

/-- The closure of a trapezoid carrier lies in the closed trapezoid.
LaValle, Planning Algorithms, Sec. 6.2.2. -/
theorem TrapDecomp.closure_carrier_subset_closedTrap {F : Set plane} (D : TrapDecomp F)
    (i : Fin D.m) :
    closure (D.trap i).carrier ⊆
      {p | (D.trap i).x₁ ≤ p 0 ∧ p 0 ≤ (D.trap i).x₂ ∧
        (D.trap i).bot (p 0) ≤ p 1 ∧ p 1 ≤ (D.trap i).top (p 0)} := by
  refine closure_minimal ?_ ?_
  · intro p hp
    simp only [VTrap.carrier] at hp
    simp only [Set.mem_ofPred_eq]
    obtain ⟨hx1, hx2, hbot, htop⟩ := hp
    exact ⟨le_of_lt hx1, le_of_lt hx2, le_of_lt hbot, le_of_lt htop⟩
  · have hc0 : Continuous fun p : plane => p 0 := PiLp.continuous_apply 2 _ 0
    have hc1 : Continuous fun p : plane => p 1 := PiLp.continuous_apply 2 _ 1
    have hbot : Continuous fun p : plane => (D.trap i).bot (p 0) :=
      (affineContinuous (D.trap i).bot).comp hc0
    have htop : Continuous fun p : plane => (D.trap i).top (p 0) :=
      (affineContinuous (D.trap i).top).comp hc0
    have h1 : IsClosed {p : plane | (D.trap i).x₁ ≤ p 0} :=
      isClosed_le continuous_const hc0
    have h2 : IsClosed {p : plane | p 0 ≤ (D.trap i).x₂} :=
      isClosed_le hc0 continuous_const
    have h3 : IsClosed {p : plane | (D.trap i).bot (p 0) ≤ p 1} :=
      isClosed_le hbot hc1
    have h4 : IsClosed {p : plane | p 1 ≤ (D.trap i).top (p 0)} :=
      isClosed_le hc1 htop
    exact h1.and (h2.and (h3.and h4))

/-- A point of `F` on the open right side of a trapezoid lies in an incident wall.
LaValle, Planning Algorithms, Sec. 6.2.2. -/
theorem TrapDecomp.mem_wall_of_mem_closure_rightSide {F : Set plane} (D : TrapDecomp F)
    (hF : IsOpen F) (i : Fin D.m) (p : plane) (hp0 : p 0 = (D.trap i).x₂)
    (hbot : (D.trap i).bot (p 0) < p 1) (htop : p 1 < (D.trap i).top (p 0))
    (hpF : p ∈ F) :
    ∃ j : Fin D.k, ((D.trap i).HasOnRight (D.wall j) ∨ (D.trap i).HasOnLeft (D.wall j)) ∧
      p ∈ (D.wall j).carrier := by
  rw [hp0] at hbot htop
  obtain ⟨c, hc, -⟩ := D.existsUnique_cell p hpF
  cases c with
  | inl i' =>
    have hc' : p ∈ (D.trap i').carrier := hc
    exfalso
    have hopen := (D.trap i').isOpen_carrier
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen p hc'
    have hcb := Metric.continuousAt_iff.mp
      ((affineContinuous (D.trap i).bot).continuousAt (x := (D.trap i).x₂))
    have hct := Metric.continuousAt_iff.mp
      ((affineContinuous (D.trap i).top).continuousAt (x := (D.trap i).x₂))
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hcb (p 1 - (D.trap i).bot ((D.trap i).x₂)) (by linarith)
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hct ((D.trap i).top ((D.trap i).x₂) - p 1) (by linarith)
    have hρpos : 0 < min δ₁ (min δ₂ (min ((D.trap i).x₂ - (D.trap i).x₁) ε)) :=
      lt_min hδ₁pos (lt_min hδ₂pos (lt_min (sub_pos.mpr (D.trap i).x₁_lt_x₂) hε))
    have hρ1 : min δ₁ (min δ₂ (min ((D.trap i).x₂ - (D.trap i).x₁) ε)) ≤ δ₁ :=
      min_le_left _ _
    have hρ2 : min δ₁ (min δ₂ (min ((D.trap i).x₂ - (D.trap i).x₁) ε)) ≤ δ₂ :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hρx : min δ₁ (min δ₂ (min ((D.trap i).x₂ - (D.trap i).x₁) ε))
        ≤ (D.trap i).x₂ - (D.trap i).x₁ :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hρε : min δ₁ (min δ₂ (min ((D.trap i).x₂ - (D.trap i).x₁) ε)) ≤ ε :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    set ρ : ℝ := min δ₁ (min δ₂ (min ((D.trap i).x₂ - (D.trap i).x₁) ε)) with hρ
    have hs1 : (D.trap i).x₁ < (D.trap i).x₂ - ρ / 2 := by linarith
    have hs2 : (D.trap i).x₂ - ρ / 2 < (D.trap i).x₂ := by linarith
    have hsdist1 : dist ((D.trap i).x₂ - ρ / 2) ((D.trap i).x₂) < δ₁ := by
      rw [Real.dist_eq]
      have he : (D.trap i).x₂ - ρ / 2 - (D.trap i).x₂ = -(ρ / 2) := by ring
      rw [he, abs_neg, abs_of_pos (half_pos hρpos)]
      linarith
    have hsdist2 : dist ((D.trap i).x₂ - ρ / 2) ((D.trap i).x₂) < δ₂ := by
      rw [Real.dist_eq]
      have he : (D.trap i).x₂ - ρ / 2 - (D.trap i).x₂ = -(ρ / 2) := by ring
      rw [he, abs_neg, abs_of_pos (half_pos hρpos)]
      linarith
    have hblt : (D.trap i).bot ((D.trap i).x₂ - ρ / 2) < p 1 := by
      have h := hδ₁ hsdist1
      rw [Real.dist_eq] at h
      have h2 := (abs_lt.mp h).2
      linarith
    have hblt' : p 1 < (D.trap i).top ((D.trap i).x₂ - ρ / 2) := by
      have h := hδ₂ hsdist2
      rw [Real.dist_eq] at h
      have h2 := (abs_lt.mp h).1
      linarith
    have hr_mem_i : (!₂[(D.trap i).x₂ - ρ / 2, p 1] : plane) ∈ (D.trap i).carrier := by
      simp only [VTrap.carrier]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [Matrix.cons_val_zero]
        exact hs1
      · simp only [Matrix.cons_val_zero]
        exact hs2
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        exact hblt
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        exact hblt'
    have hr_mem_i' : (!₂[(D.trap i).x₂ - ρ / 2, p 1] : plane) ∈ (D.trap i').carrier := by
      apply hball
      rw [Metric.mem_ball, dist_comm, dist_mkPoint, hp0]
      have he : (D.trap i).x₂ - ((D.trap i).x₂ - ρ / 2) = ρ / 2 := by ring
      rw [he, abs_of_pos (half_pos hρpos)]
      linarith
    by_cases heq : i' = i
    · subst heq
      simp only [VTrap.carrier] at hc'
      obtain ⟨_, hpx2', _, _⟩ := hc'
      linarith
    · have hne : (Sum.inl i : D.Cell) ≠ Sum.inl i' := by
        intro h
        simp only [Sum.inl.injEq] at h
        exact heq h.symm
      have hd := D.carrier_disjoint (Sum.inl i) (Sum.inl i') hne
      exact (Set.disjoint_left.mp hd hr_mem_i) hr_mem_i'
  | inr j =>
    have hcmem : p ∈ (D.wall j).carrier := hc
    have hc' : p ∈ (D.wall j).carrier := hc
    simp only [VSeg.carrier] at hc'
    obtain ⟨hq0, hqy1, hqy2⟩ := hc'
    have hwx : (D.wall j).x = (D.trap i).x₂ := by
      rw [← hq0]
      exact hp0
    have hlow : (D.trap i).bot ((D.trap i).x₂) ≤ (D.wall j).y₁ := by
      by_contra hcon
      have hcon : (D.wall j).y₁ < (D.trap i).bot ((D.trap i).x₂) := lt_of_not_ge hcon
      have hcorner_wall : (!₂[(D.trap i).x₂, (D.trap i).bot ((D.trap i).x₂)] : plane) ∈
          (D.wall j).carrier := by
        simp only [VSeg.carrier]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Matrix.cons_val_zero]
          exact hwx.symm
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          exact hcon
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
      have hcorner_side : (!₂[(D.trap i).x₂, (D.trap i).bot ((D.trap i).x₂)] : plane) ∈
          (D.trap i).lowerSide := by
        simp only [VTrap.lowerSide]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Matrix.cons_val_zero]
          exact le_of_lt (D.trap i).x₁_lt_x₂
        · simp only [Matrix.cons_val_zero]
          exact le_rfl
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hcornerF : (!₂[(D.trap i).x₂, (D.trap i).bot ((D.trap i).x₂)] : plane) ∈ F :=
        D.wall_carrier_subset j hcorner_wall
      exact (Set.disjoint_left.mp (D.lowerSide_disjoint hF i) hcorner_side) hcornerF
    have hhigh : (D.wall j).y₂ ≤ (D.trap i).top ((D.trap i).x₂) := by
      by_contra hcon
      have hcon : (D.trap i).top ((D.trap i).x₂) < (D.wall j).y₂ := lt_of_not_ge hcon
      have hcorner_wall : (!₂[(D.trap i).x₂, (D.trap i).top ((D.trap i).x₂)] : plane) ∈
          (D.wall j).carrier := by
        simp only [VSeg.carrier]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Matrix.cons_val_zero]
          exact hwx.symm
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          exact hcon
      have hcorner_side : (!₂[(D.trap i).x₂, (D.trap i).top ((D.trap i).x₂)] : plane) ∈
          (D.trap i).upperSide := by
        simp only [VTrap.upperSide]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Matrix.cons_val_zero]
          exact le_of_lt (D.trap i).x₁_lt_x₂
        · simp only [Matrix.cons_val_zero]
          exact le_rfl
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hcornerF : (!₂[(D.trap i).x₂, (D.trap i).top ((D.trap i).x₂)] : plane) ∈ F :=
        D.wall_carrier_subset j hcorner_wall
      exact (Set.disjoint_left.mp (D.upperSide_disjoint hF i) hcorner_side) hcornerF
    exact ⟨j, Or.inl ⟨hwx.symm, hlow, hhigh⟩, hcmem⟩

/-- A point of `F` on the open left side of a trapezoid lies in an incident wall.
LaValle, Planning Algorithms, Sec. 6.2.2. -/
theorem TrapDecomp.mem_wall_of_mem_closure_leftSide {F : Set plane} (D : TrapDecomp F)
    (hF : IsOpen F) (i : Fin D.m) (p : plane) (hp0 : p 0 = (D.trap i).x₁)
    (hbot : (D.trap i).bot (p 0) < p 1) (htop : p 1 < (D.trap i).top (p 0))
    (hpF : p ∈ F) :
    ∃ j : Fin D.k, ((D.trap i).HasOnRight (D.wall j) ∨ (D.trap i).HasOnLeft (D.wall j)) ∧
      p ∈ (D.wall j).carrier := by
  rw [hp0] at hbot htop
  obtain ⟨c, hc, -⟩ := D.existsUnique_cell p hpF
  cases c with
  | inl i' =>
    have hc' : p ∈ (D.trap i').carrier := hc
    exfalso
    have hopen := (D.trap i').isOpen_carrier
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen p hc'
    have hcb := Metric.continuousAt_iff.mp
      ((affineContinuous (D.trap i).bot).continuousAt (x := (D.trap i).x₁))
    have hct := Metric.continuousAt_iff.mp
      ((affineContinuous (D.trap i).top).continuousAt (x := (D.trap i).x₁))
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hcb (p 1 - (D.trap i).bot ((D.trap i).x₁)) (by linarith)
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hct ((D.trap i).top ((D.trap i).x₁) - p 1) (by linarith)
    have hρpos : 0 < min δ₁ (min δ₂ (min ((D.trap i).x₂ - (D.trap i).x₁) ε)) :=
      lt_min hδ₁pos (lt_min hδ₂pos (lt_min (sub_pos.mpr (D.trap i).x₁_lt_x₂) hε))
    have hρ1 : min δ₁ (min δ₂ (min ((D.trap i).x₂ - (D.trap i).x₁) ε)) ≤ δ₁ :=
      min_le_left _ _
    have hρ2 : min δ₁ (min δ₂ (min ((D.trap i).x₂ - (D.trap i).x₁) ε)) ≤ δ₂ :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hρx : min δ₁ (min δ₂ (min ((D.trap i).x₂ - (D.trap i).x₁) ε))
        ≤ (D.trap i).x₂ - (D.trap i).x₁ :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hρε : min δ₁ (min δ₂ (min ((D.trap i).x₂ - (D.trap i).x₁) ε)) ≤ ε :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    set ρ : ℝ := min δ₁ (min δ₂ (min ((D.trap i).x₂ - (D.trap i).x₁) ε)) with hρ
    have hs1 : (D.trap i).x₁ < (D.trap i).x₁ + ρ / 2 := by linarith
    have hs2 : (D.trap i).x₁ + ρ / 2 < (D.trap i).x₂ := by linarith
    have hsdist1 : dist ((D.trap i).x₁ + ρ / 2) ((D.trap i).x₁) < δ₁ := by
      rw [Real.dist_eq]
      have he : (D.trap i).x₁ + ρ / 2 - (D.trap i).x₁ = ρ / 2 := by ring
      rw [he, abs_of_pos (half_pos hρpos)]
      linarith
    have hsdist2 : dist ((D.trap i).x₁ + ρ / 2) ((D.trap i).x₁) < δ₂ := by
      rw [Real.dist_eq]
      have he : (D.trap i).x₁ + ρ / 2 - (D.trap i).x₁ = ρ / 2 := by ring
      rw [he, abs_of_pos (half_pos hρpos)]
      linarith
    have hblt : (D.trap i).bot ((D.trap i).x₁ + ρ / 2) < p 1 := by
      have h := hδ₁ hsdist1
      rw [Real.dist_eq] at h
      have h2 := (abs_lt.mp h).2
      linarith
    have hblt' : p 1 < (D.trap i).top ((D.trap i).x₁ + ρ / 2) := by
      have h := hδ₂ hsdist2
      rw [Real.dist_eq] at h
      have h2 := (abs_lt.mp h).1
      linarith
    have hr_mem_i : (!₂[(D.trap i).x₁ + ρ / 2, p 1] : plane) ∈ (D.trap i).carrier := by
      simp only [VTrap.carrier]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [Matrix.cons_val_zero]
        exact hs1
      · simp only [Matrix.cons_val_zero]
        exact hs2
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        exact hblt
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        exact hblt'
    have hr_mem_i' : (!₂[(D.trap i).x₁ + ρ / 2, p 1] : plane) ∈ (D.trap i').carrier := by
      apply hball
      rw [Metric.mem_ball, dist_comm, dist_mkPoint, hp0]
      have he : (D.trap i).x₁ - ((D.trap i).x₁ + ρ / 2) = -(ρ / 2) := by ring
      rw [he, abs_neg, abs_of_pos (half_pos hρpos)]
      linarith
    by_cases heq : i' = i
    · subst heq
      simp only [VTrap.carrier] at hc'
      obtain ⟨hpx1', _, _, _⟩ := hc'
      linarith
    · have hne : (Sum.inl i : D.Cell) ≠ Sum.inl i' := by
        intro h
        simp only [Sum.inl.injEq] at h
        exact heq h.symm
      have hd := D.carrier_disjoint (Sum.inl i) (Sum.inl i') hne
      exact (Set.disjoint_left.mp hd hr_mem_i) hr_mem_i'
  | inr j =>
    have hcmem : p ∈ (D.wall j).carrier := hc
    have hc' : p ∈ (D.wall j).carrier := hc
    simp only [VSeg.carrier] at hc'
    obtain ⟨hq0, hqy1, hqy2⟩ := hc'
    have hwx : (D.wall j).x = (D.trap i).x₁ := by
      rw [← hq0]
      exact hp0
    have hlow : (D.trap i).bot ((D.trap i).x₁) ≤ (D.wall j).y₁ := by
      by_contra hcon
      have hcon : (D.wall j).y₁ < (D.trap i).bot ((D.trap i).x₁) := lt_of_not_ge hcon
      have hcorner_wall : (!₂[(D.trap i).x₁, (D.trap i).bot ((D.trap i).x₁)] : plane) ∈
          (D.wall j).carrier := by
        simp only [VSeg.carrier]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Matrix.cons_val_zero]
          exact hwx.symm
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          exact hcon
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
      have hcorner_side : (!₂[(D.trap i).x₁, (D.trap i).bot ((D.trap i).x₁)] : plane) ∈
          (D.trap i).lowerSide := by
        simp only [VTrap.lowerSide]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Matrix.cons_val_zero]
          exact le_rfl
        · simp only [Matrix.cons_val_zero]
          exact le_of_lt (D.trap i).x₁_lt_x₂
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hcornerF : (!₂[(D.trap i).x₁, (D.trap i).bot ((D.trap i).x₁)] : plane) ∈ F :=
        D.wall_carrier_subset j hcorner_wall
      exact (Set.disjoint_left.mp (D.lowerSide_disjoint hF i) hcorner_side) hcornerF
    have hhigh : (D.wall j).y₂ ≤ (D.trap i).top ((D.trap i).x₁) := by
      by_contra hcon
      have hcon : (D.trap i).top ((D.trap i).x₁) < (D.wall j).y₂ := lt_of_not_ge hcon
      have hcorner_wall : (!₂[(D.trap i).x₁, (D.trap i).top ((D.trap i).x₁)] : plane) ∈
          (D.wall j).carrier := by
        simp only [VSeg.carrier]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Matrix.cons_val_zero]
          exact hwx.symm
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          exact hcon
      have hcorner_side : (!₂[(D.trap i).x₁, (D.trap i).top ((D.trap i).x₁)] : plane) ∈
          (D.trap i).upperSide := by
        simp only [VTrap.upperSide]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Matrix.cons_val_zero]
          exact le_rfl
        · simp only [Matrix.cons_val_zero]
          exact le_of_lt (D.trap i).x₁_lt_x₂
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hcornerF : (!₂[(D.trap i).x₁, (D.trap i).top ((D.trap i).x₁)] : plane) ∈ F :=
        D.wall_carrier_subset j hcorner_wall
      exact (Set.disjoint_left.mp (D.upperSide_disjoint hF i) hcorner_side) hcornerF
    exact ⟨j, Or.inr ⟨hwx.symm, hlow, hhigh⟩, hcmem⟩

theorem TrapDecomp.closure_carrier_inter_subset {F : Set plane} (D : TrapDecomp F)
    (hF : IsOpen F) (i : Fin D.m) :
    closure (D.trap i).carrier ∩ F ⊆ (D.trap i).carrier ∪
      ⋃ (j : Fin D.k) (_ : (D.trap i).HasOnRight (D.wall j) ∨ (D.trap i).HasOnLeft (D.wall j)),
        (D.wall j).carrier := by
  intro p hp
  simp only [Set.mem_inter_iff, Set.mem_union] at hp ⊢
  obtain ⟨hpclo, hpF⟩ := hp
  have hmem := D.closure_carrier_subset_closedTrap i hpclo
  simp only [Set.mem_ofPred_eq] at hmem
  obtain ⟨hpx1, hpx2, hpbot, hptop⟩ := hmem
  rcases lt_or_ge (D.trap i).x₁ (p 0) with hx1lt | hx1le
  · rcases lt_or_ge (p 0) (D.trap i).x₂ with hx2lt | hx2le
    · rcases lt_or_ge ((D.trap i).bot (p 0)) (p 1) with hyblt | hyble
      · rcases lt_or_ge (p 1) ((D.trap i).top (p 0)) with hytlt | hytle
        · exact Or.inl ⟨hx1lt, hx2lt, hyblt, hytlt⟩
        · exfalso
          have heq : p 1 = (D.trap i).top (p 0) := le_antisymm hptop hytle
          have hside : p ∈ (D.trap i).upperSide := ⟨hpx1, hpx2, heq⟩
          exact (Set.disjoint_left.mp (D.upperSide_disjoint hF i) hside) hpF
      · exfalso
        have heq : p 1 = (D.trap i).bot (p 0) := le_antisymm hyble hpbot
        have hside : p ∈ (D.trap i).lowerSide := ⟨hpx1, hpx2, heq⟩
        exact (Set.disjoint_left.mp (D.lowerSide_disjoint hF i) hside) hpF
    · have hp0 : p 0 = (D.trap i).x₂ := le_antisymm hpx2 hx2le
      rcases lt_or_ge ((D.trap i).bot (p 0)) (p 1) with hyblt | hyble
      · rcases lt_or_ge (p 1) ((D.trap i).top (p 0)) with hytlt | hytle
        · right
          simp only [Set.mem_iUnion]
          obtain ⟨j, hj, hmem⟩ :=
            D.mem_wall_of_mem_closure_rightSide hF i p hp0 hyblt hytlt hpF
          exact ⟨j, hj, hmem⟩
        · exfalso
          have heq : p 1 = (D.trap i).top (p 0) := le_antisymm hptop hytle
          have hside : p ∈ (D.trap i).upperSide := ⟨hpx1, hpx2, heq⟩
          exact (Set.disjoint_left.mp (D.upperSide_disjoint hF i) hside) hpF
      · exfalso
        have heq : p 1 = (D.trap i).bot (p 0) := le_antisymm hyble hpbot
        have hside : p ∈ (D.trap i).lowerSide := ⟨hpx1, hpx2, heq⟩
        exact (Set.disjoint_left.mp (D.lowerSide_disjoint hF i) hside) hpF
  · have hp0 : p 0 = (D.trap i).x₁ := le_antisymm hx1le hpx1
    rcases lt_or_ge ((D.trap i).bot (p 0)) (p 1) with hyblt | hyble
    · rcases lt_or_ge (p 1) ((D.trap i).top (p 0)) with hytlt | hytle
      · right
        simp only [Set.mem_iUnion]
        obtain ⟨j, hj, hmem⟩ :=
          D.mem_wall_of_mem_closure_leftSide hF i p hp0 hyblt hytlt hpF
        exact ⟨j, hj, hmem⟩
      · exfalso
        have heq : p 1 = (D.trap i).top (p 0) := le_antisymm hptop hytle
        have hside : p ∈ (D.trap i).upperSide := ⟨hpx1, hpx2, heq⟩
        exact (Set.disjoint_left.mp (D.upperSide_disjoint hF i) hside) hpF
    · exfalso
      have heq : p 1 = (D.trap i).bot (p 0) := le_antisymm hyble hpbot
      have hside : p ∈ (D.trap i).lowerSide := ⟨hpx1, hpx2, heq⟩
      exact (Set.disjoint_left.mp (D.lowerSide_disjoint hF i) hside) hpF

/-- A wall's lower endpoint is outside `F`.
LaValle, Planning Algorithms, Sec. 6.2.2. -/
theorem TrapDecomp.wall_lower_endpoint_not_mem {F : Set plane} (D : TrapDecomp F)
    (j : Fin D.k) :
    (!₂[(D.wall j).x, (D.wall j).y₁] : plane) ∉ F := by
  intro heF
  obtain ⟨c, hc, -⟩ := D.existsUnique_cell _ heF
  cases c with
  | inl i' =>
    have hc' : (!₂[(D.wall j).x, (D.wall j).y₁] : plane) ∈ (D.trap i').carrier := hc
    exfalso
    have hopen := (D.trap i').isOpen_carrier
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen _ hc'
    have hgap : 0 < (D.wall j).y₂ - (D.wall j).y₁ := by
      have h := (D.wall j).y₁_lt_y₂
      linarith
    have htε : min (ε / 2) (((D.wall j).y₂ - (D.wall j).y₁) / 2) < ε :=
      lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
    have htgap : min (ε / 2) (((D.wall j).y₂ - (D.wall j).y₁) / 2)
        < (D.wall j).y₂ - (D.wall j).y₁ :=
      lt_of_le_of_lt (min_le_right _ _) (half_lt_self hgap)
    have htpos : 0 < min (ε / 2) (((D.wall j).y₂ - (D.wall j).y₁) / 2) :=
      lt_min (half_pos hε) (half_pos hgap)
    set t : ℝ := min (ε / 2) (((D.wall j).y₂ - (D.wall j).y₁) / 2) with ht
    have hr_mem_i' : (!₂[(D.wall j).x, (D.wall j).y₁ + t] : plane) ∈
        (D.trap i').carrier := by
      apply hball
      rw [Metric.mem_ball]
      have hd : dist (!₂[(D.wall j).x, (D.wall j).y₁ + t] : plane)
          (!₂[(D.wall j).x, (D.wall j).y₁] : plane)
          = |(D.wall j).y₁ + t - (D.wall j).y₁| :=
        dist_mkPoint_left _ _ _
      rw [hd]
      have habs : |(D.wall j).y₁ + t - (D.wall j).y₁| = t := by
        rw [add_sub_cancel_left, abs_of_pos htpos]
      rw [habs]
      exact htε
    have hr_mem_j : (!₂[(D.wall j).x, (D.wall j).y₁ + t] : plane) ∈
        (D.wall j).carrier := by
      simp only [VSeg.carrier]
      refine ⟨?_, ?_, ?_⟩
      · simp only [Matrix.cons_val_zero]
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith
    have hd := D.carrier_disjoint (Sum.inl i') (Sum.inr j) Sum.inl_ne_inr
    exact (Set.disjoint_left.mp hd hr_mem_i') hr_mem_j
  | inr j' =>
    have hc' : (!₂[(D.wall j).x, (D.wall j).y₁] : plane) ∈ (D.wall j').carrier := hc
    exfalso
    simp only [VSeg.carrier] at hc'
    obtain ⟨hx0, hy1, hy2⟩ := hc'
    have hx0' : (D.wall j).x = (D.wall j').x := hx0
    have hy1' : (D.wall j').y₁ < (D.wall j).y₁ := hy1
    have hy2' : (D.wall j).y₁ < (D.wall j').y₂ := hy2
    by_cases heq : j' = j
    · subst heq
      linarith
    · have hgap1 : 0 < (D.wall j).y₂ - (D.wall j).y₁ := by
        have h := (D.wall j).y₁_lt_y₂
        linarith
      have hgap2 : 0 < (D.wall j').y₂ - (D.wall j).y₁ := by linarith
      have htpos : 0 < min (((D.wall j).y₂ - (D.wall j).y₁) / 2)
          (((D.wall j').y₂ - (D.wall j).y₁) / 2) :=
        lt_min (half_pos hgap1) (half_pos hgap2)
      have htgap1 : min (((D.wall j).y₂ - (D.wall j).y₁) / 2)
          (((D.wall j').y₂ - (D.wall j).y₁) / 2) < (D.wall j).y₂ - (D.wall j).y₁ :=
        lt_of_le_of_lt (min_le_left _ _) (half_lt_self hgap1)
      have htgap2 : min (((D.wall j).y₂ - (D.wall j).y₁) / 2)
          (((D.wall j').y₂ - (D.wall j).y₁) / 2) < (D.wall j').y₂ - (D.wall j).y₁ :=
        lt_of_le_of_lt (min_le_right _ _) (half_lt_self hgap2)
      set t : ℝ := min (((D.wall j).y₂ - (D.wall j).y₁) / 2)
        (((D.wall j').y₂ - (D.wall j).y₁) / 2) with ht
      have hr_mem_j : (!₂[(D.wall j).x, (D.wall j).y₁ + t] : plane) ∈
          (D.wall j).carrier := by
        simp only [VSeg.carrier]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Matrix.cons_val_zero]
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
      have hr_mem_j' : (!₂[(D.wall j).x, (D.wall j).y₁ + t] : plane) ∈
          (D.wall j').carrier := by
        simp only [VSeg.carrier]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Matrix.cons_val_zero]
          exact hx0'
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
      have hne : (Sum.inr j : D.Cell) ≠ Sum.inr j' := by
        intro h
        simp only [Sum.inr.injEq] at h
        exact heq h.symm
      have hd := D.carrier_disjoint (Sum.inr j) (Sum.inr j') hne
      exact (Set.disjoint_left.mp hd hr_mem_j) hr_mem_j'

/-- A wall's upper endpoint is outside `F`.
LaValle, Planning Algorithms, Sec. 6.2.2. -/
theorem TrapDecomp.wall_upper_endpoint_not_mem {F : Set plane} (D : TrapDecomp F)
    (j : Fin D.k) :
    (!₂[(D.wall j).x, (D.wall j).y₂] : plane) ∉ F := by
  intro heF
  obtain ⟨c, hc, -⟩ := D.existsUnique_cell _ heF
  cases c with
  | inl i' =>
    have hc' : (!₂[(D.wall j).x, (D.wall j).y₂] : plane) ∈ (D.trap i').carrier := hc
    exfalso
    have hopen := (D.trap i').isOpen_carrier
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen _ hc'
    have hgap : 0 < (D.wall j).y₂ - (D.wall j).y₁ := by
      have h := (D.wall j).y₁_lt_y₂
      linarith
    have htε : min (ε / 2) (((D.wall j).y₂ - (D.wall j).y₁) / 2) < ε :=
      lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
    have htgap : min (ε / 2) (((D.wall j).y₂ - (D.wall j).y₁) / 2)
        < (D.wall j).y₂ - (D.wall j).y₁ :=
      lt_of_le_of_lt (min_le_right _ _) (half_lt_self hgap)
    have htpos : 0 < min (ε / 2) (((D.wall j).y₂ - (D.wall j).y₁) / 2) :=
      lt_min (half_pos hε) (half_pos hgap)
    set t : ℝ := min (ε / 2) (((D.wall j).y₂ - (D.wall j).y₁) / 2) with ht
    have hr_mem_i' : (!₂[(D.wall j).x, (D.wall j).y₂ - t] : plane) ∈
        (D.trap i').carrier := by
      apply hball
      rw [Metric.mem_ball]
      have hd : dist (!₂[(D.wall j).x, (D.wall j).y₂ - t] : plane)
          (!₂[(D.wall j).x, (D.wall j).y₂] : plane)
          = |(D.wall j).y₂ - t - (D.wall j).y₂| :=
        dist_mkPoint_left _ _ _
      rw [hd]
      have habs : |(D.wall j).y₂ - t - (D.wall j).y₂| = t := by
        have he : (D.wall j).y₂ - t - (D.wall j).y₂ = -t := by ring
        rw [he, abs_neg, abs_of_pos htpos]
      rw [habs]
      exact htε
    have hr_mem_j : (!₂[(D.wall j).x, (D.wall j).y₂ - t] : plane) ∈
        (D.wall j).carrier := by
      simp only [VSeg.carrier]
      refine ⟨?_, ?_, ?_⟩
      · simp only [Matrix.cons_val_zero]
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith
    have hd := D.carrier_disjoint (Sum.inl i') (Sum.inr j) Sum.inl_ne_inr
    exact (Set.disjoint_left.mp hd hr_mem_i') hr_mem_j
  | inr j' =>
    have hc' : (!₂[(D.wall j).x, (D.wall j).y₂] : plane) ∈ (D.wall j').carrier := hc
    exfalso
    simp only [VSeg.carrier] at hc'
    obtain ⟨hx0, hy1, hy2⟩ := hc'
    have hx0' : (D.wall j).x = (D.wall j').x := hx0
    have hy1' : (D.wall j').y₁ < (D.wall j).y₂ := hy1
    have hy2' : (D.wall j).y₂ < (D.wall j').y₂ := hy2
    by_cases heq : j' = j
    · subst heq
      linarith
    · have hgap1 : 0 < (D.wall j).y₂ - (D.wall j).y₁ := by
        have h := (D.wall j).y₁_lt_y₂
        linarith
      have hgap3 : 0 < (D.wall j).y₂ - (D.wall j').y₁ := by linarith
      have htpos : 0 < min (((D.wall j).y₂ - (D.wall j).y₁) / 2)
          (((D.wall j).y₂ - (D.wall j').y₁) / 2) :=
        lt_min (half_pos hgap1) (half_pos hgap3)
      have htgap1 : min (((D.wall j).y₂ - (D.wall j).y₁) / 2)
          (((D.wall j).y₂ - (D.wall j').y₁) / 2) < (D.wall j).y₂ - (D.wall j).y₁ :=
        lt_of_le_of_lt (min_le_left _ _) (half_lt_self hgap1)
      have htgap3 : min (((D.wall j).y₂ - (D.wall j).y₁) / 2)
          (((D.wall j).y₂ - (D.wall j').y₁) / 2) < (D.wall j).y₂ - (D.wall j').y₁ :=
        lt_of_le_of_lt (min_le_right _ _) (half_lt_self hgap3)
      set t : ℝ := min (((D.wall j).y₂ - (D.wall j).y₁) / 2)
        (((D.wall j).y₂ - (D.wall j').y₁) / 2) with ht
      have hr_mem_j : (!₂[(D.wall j).x, (D.wall j).y₂ - t] : plane) ∈
          (D.wall j).carrier := by
        simp only [VSeg.carrier]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Matrix.cons_val_zero]
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
      have hr_mem_j' : (!₂[(D.wall j).x, (D.wall j).y₂ - t] : plane) ∈
          (D.wall j').carrier := by
        simp only [VSeg.carrier]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Matrix.cons_val_zero]
          exact hx0'
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
      have hne : (Sum.inr j : D.Cell) ≠ Sum.inr j' := by
        intro h
        simp only [Sum.inr.injEq] at h
        exact heq h.symm
      have hd := D.carrier_disjoint (Sum.inr j) (Sum.inr j') hne
      exact (Set.disjoint_left.mp hd hr_mem_j) hr_mem_j'

theorem TrapDecomp.wall_endpoints_not_mem {F : Set plane} (D : TrapDecomp F)
    (j : Fin D.k) :
    (!₂[(D.wall j).x, (D.wall j).y₁] : plane) ∉ F ∧
    (!₂[(D.wall j).x, (D.wall j).y₂] : plane) ∉ F :=
  ⟨D.wall_lower_endpoint_not_mem j, D.wall_upper_endpoint_not_mem j⟩

open scoped Topology

/-- Coordinates of `plane` points are 1-Lipschitz in each component. -/
lemma abs_coord_sub_le_dist (p r : plane) (i : Fin 2) : |p i - r i| ≤ dist p r := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq]
  fin_cases i
  · exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))
  · exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg _))

/-- A `plane` point equals the `!₂` point of its coordinates. -/
lemma mkPoint_eq_self (p : plane) : p = !₂[p 0, p 1] := by
  ext i
  fin_cases i
  · rfl
  · rfl

/-- Membership in `(0, δ)` is eventually true in `𝓝[>] 0`. -/
lemma eventually_Ioo_nhdsWithin_Ioi (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioo 0 δ := by
  have h1 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioi (0 : ℝ) :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => ht)
  have h2 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Iio δ :=
    Filter.eventually_of_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ))
      (fun t ht => ht)
  exact (h1.and h2).mono (fun t ht => ⟨ht.1, ht.2⟩)

/-- Near a wall's `x`-coordinate, nearby `x`-coordinates hit no other wall line.
LaValle, Planning Algorithms, Sec. 6.2.2: finitely many 1-cells. -/
lemma TrapDecomp.exists_wall_x_gap {F : Set plane} (D : TrapDecomp F) (j : Fin D.k) :
    ∃ δ₂ > 0, ∀ t : ℝ, 0 < t → t < δ₂ → ∀ j' : Fin D.k,
      (D.wall j).x - t ≠ (D.wall j').x ∧ (D.wall j).x + t ≠ (D.wall j').x := by
  classical
  set S : Finset ℝ := Finset.univ.image (fun j' : Fin D.k =>
    if (D.wall j').x = (D.wall j).x then (1 : ℝ) else |(D.wall j).x - (D.wall j').x|) with hS
  have hSne : S.Nonempty := by
    refine ⟨(fun j' : Fin D.k =>
      if (D.wall j').x = (D.wall j).x then (1 : ℝ) else |(D.wall j).x - (D.wall j').x|) j, ?_⟩
    rw [hS]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have hpos : ∀ r ∈ S, 0 < r := by
    intro r hr
    rw [hS, Finset.mem_image] at hr
    obtain ⟨j', -, rfl⟩ := hr
    show 0 < (if (D.wall j').x = (D.wall j).x then (1 : ℝ) else |(D.wall j).x - (D.wall j').x|)
    by_cases h : (D.wall j').x = (D.wall j).x
    · rw [ite_eq_left h]; exact zero_lt_one
    · rw [ite_eq_right h]; exact abs_pos.mpr (sub_ne_zero.mpr (fun he => h he.symm))
  refine ⟨S.min' hSne, hpos _ (Finset.min'_mem S hSne), ?_⟩
  intro t ht0 ht j'
  have hle : S.min' hSne ≤ (fun j' : Fin D.k =>
      if (D.wall j').x = (D.wall j).x then (1 : ℝ) else |(D.wall j).x - (D.wall j').x|) j' :=
    Finset.min'_le S _ (by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ j'))
  have hflt : t < (if (D.wall j').x = (D.wall j).x then (1 : ℝ) else |(D.wall j).x - (D.wall j').x|) :=
    lt_of_lt_of_le ht hle
  by_cases h : (D.wall j').x = (D.wall j).x
  · rw [ite_eq_left h] at hflt
    rw [h]
    constructor
    · intro he
      have h0 : t = 0 := by linarith
      linarith
    · intro he
      have h0 : t = 0 := by linarith
      linarith
  · rw [ite_eq_right h] at hflt
    constructor
    · intro he
      have heq : (D.wall j).x - (D.wall j').x = t := by linarith
      rw [heq, abs_of_pos ht0] at hflt
      linarith
    · intro he
      have heq : (D.wall j).x - (D.wall j').x = -t := by linarith
      rw [heq, abs_neg, abs_of_pos ht0] at hflt
      linarith

/-- Accumulation core (LaValle, Planning Algorithms, Sec. 6.2.2): points of `F`
approaching from beside a wall frequently lie in a single trapezoid. -/
lemma TrapDecomp.exists_freq_trap_of_seq {F : Set plane} (D : TrapDecomp F)
    (g : ℝ → plane) (δ : ℝ) (hδ : 0 < δ)
    (hgF : ∀ t ∈ Set.Ioo 0 δ, g t ∈ F)
    (hgwall : ∀ t ∈ Set.Ioo 0 δ, ∀ j : Fin D.k, g t ∉ (D.wall j).carrier) :
    ∃ i : Fin D.m, ∃ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), g t ∈ (D.trap i).carrier := by
  have hIoo : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioo 0 δ :=
    eventually_Ioo_nhdsWithin_Ioi δ hδ
  have hall : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∃ i : Fin D.m, g t ∈ (D.trap i).carrier := by
    apply hIoo.mono
    intro t ht
    obtain ⟨c, hc, -⟩ := D.existsUnique_cell (g t) (hgF t ht)
    cases c with
    | inl i => exact ⟨i, hc⟩
    | inr j => exact absurd hc (hgwall t ht j)
  by_contra hcon
  rw [not_exists] at hcon
  simp only [Filter.not_frequently] at hcon
  have hnone : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i : Fin D.m, g t ∉ (D.trap i).carrier :=
    Filter.eventually_all.mpr hcon
  have hfalse : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), False :=
    (hall.and hnone).mono (fun t ht => by obtain ⟨i, hi⟩ := ht.1; exact ht.2 i hi)
  obtain ⟨t, ht⟩ := hfalse.frequently.exists
  exact ht

/-- Every wall has a trapezoid on its left (LaValle, Planning Algorithms,
Sec. 6.2.2: every 1-cell borders two 2-cells). -/
lemma TrapDecomp.exists_hasOnRight_of_wall {F : Set plane} (D : TrapDecomp F)
    (hF : IsOpen F) (j : Fin D.k) : ∃ i : Fin D.m, (D.trap i).HasOnRight (D.wall j) := by
  obtain ⟨q, hq⟩ := (D.wall j).carrier_nonempty
  have hqF : q ∈ F := D.wall_carrier_subset j hq
  have qx : q 0 = (D.wall j).x := hq.1
  have hy₁ : (D.wall j).y₁ < q 1 := hq.2.1
  have hy₂ : q 1 < (D.wall j).y₂ := hq.2.2
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hF q hqF
  obtain ⟨δ₂, hδ₂, hgap⟩ := D.exists_wall_x_gap j
  have hδmin : 0 < min δ δ₂ := lt_min hδ hδ₂
  have hdist : ∀ t : ℝ, 0 < t →
      dist (!₂[(D.wall j).x - t, q 1] : plane) q = t := by
    intro t ht
    have h1 := dist_mkPoint ((D.wall j).x - t) q
    rw [dist_comm, h1, qx, show (D.wall j).x - ((D.wall j).x - t) = t from by ring, abs_of_pos ht]
  have hgF : ∀ t ∈ Set.Ioo 0 (min δ δ₂),
      (fun t : ℝ => !₂[(D.wall j).x - t, q 1] : ℝ → plane) t ∈ F := by
    intro t ht
    rw [Set.mem_Ioo] at ht
    obtain ⟨ht0, htδ⟩ := ht
    show !₂[(D.wall j).x - t, q 1] ∈ F
    apply hball
    rw [Metric.mem_ball, hdist t ht0]
    exact lt_of_lt_of_le htδ (min_le_left _ _)
  have hgwall : ∀ t ∈ Set.Ioo 0 (min δ δ₂), ∀ j' : Fin D.k,
      (fun t : ℝ => !₂[(D.wall j).x - t, q 1] : ℝ → plane) t ∉ (D.wall j').carrier := by
    intro t ht j' hmem
    rw [Set.mem_Ioo] at ht
    obtain ⟨ht0, htδ⟩ := ht
    change !₂[(D.wall j).x - t, q 1] ∈ (D.wall j').carrier at hmem
    have h0 : (!₂[(D.wall j).x - t, q 1] : plane) 0 = (D.wall j).x - t := rfl
    obtain ⟨hx, -, -⟩ := hmem
    rw [h0] at hx
    exact (hgap t ht0 (lt_of_lt_of_le htδ (min_le_right _ _)) j').1 hx
  obtain ⟨i, hfreq⟩ := D.exists_freq_trap_of_seq
    (fun t : ℝ => !₂[(D.wall j).x - t, q 1]) (min δ δ₂) hδmin hgF hgwall
  have hclosure : q ∈ closure (D.trap i).carrier := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨t, htmem, htε⟩ :=
      (hfreq.and_eventually (eventually_Ioo_nhdsWithin_Ioi ε hε)).exists
    rw [Set.mem_Ioo] at htε
    refine ⟨(fun t : ℝ => !₂[(D.wall j).x - t, q 1] : ℝ → plane) t, htmem, ?_⟩
    have hdist' : dist q ((fun t : ℝ => !₂[(D.wall j).x - t, q 1] : ℝ → plane) t) = t := by
      show dist q !₂[(D.wall j).x - t, q 1] = t
      have h1 := dist_mkPoint ((D.wall j).x - t) q
      rw [h1, qx, show (D.wall j).x - ((D.wall j).x - t) = t from by ring, abs_of_pos htε.1]
    rw [hdist']
    exact htε.2
  have hmem := D.closure_carrier_inter_subset hF i ⟨hclosure, hqF⟩
  rw [Set.mem_union] at hmem
  cases hmem with
  | inl hcarrier =>
      exfalso
      have hdisj := D.carrier_disjoint (Sum.inl i) (Sum.inr j)
        (show Sum.inl i ≠ Sum.inr j from by simp)
      rw [Set.disjoint_left] at hdisj
      exact hdisj hcarrier hq
  | inr hwall =>
      rw [Set.mem_iUnion] at hwall
      obtain ⟨j', hwall2⟩ := hwall
      rw [Set.mem_iUnion] at hwall2
      obtain ⟨hinc, hqj'⟩ := hwall2
      have hj'j : j' = j := by
        by_contra hne
        have hdisj := D.carrier_disjoint (Sum.inr j') (Sum.inr j)
          (fun h => hne (Sum.inr_injective h))
        rw [Set.disjoint_left] at hdisj
        exact hdisj hqj' hq
      rw [hj'j] at hinc
      cases hinc with
      | inl hright => exact ⟨i, hright⟩
      | inr hleft =>
          obtain ⟨t₀, ht₀mem, ht₀ε⟩ :=
            (hfreq.and_eventually (eventually_Ioo_nhdsWithin_Ioi 1 one_pos)).exists
          rw [Set.mem_Ioo] at ht₀ε
          obtain ⟨ht₀0, -⟩ := ht₀ε
          obtain ⟨hx₁, -, -, -⟩ := ht₀mem
          have h0 : ((fun t : ℝ => !₂[(D.wall j).x - t, q 1] : ℝ → plane) t₀) 0 =
              (D.wall j).x - t₀ := rfl
          rw [h0] at hx₁
          obtain ⟨hxeq, -, -⟩ := hleft
          rw [hxeq] at hx₁
          linarith

/-- Points just left of a wall eventually lie in any trapezoid on its left
(LaValle, Planning Algorithms, Sec. 6.2.2). -/
lemma TrapDecomp.eventually_mem_trap_of_hasOnRight {F : Set plane} (D : TrapDecomp F)
    {i : Fin D.m} {j : Fin D.k} (h : (D.trap i).HasOnRight (D.wall j))
    (q : plane) (hq : q ∈ (D.wall j).carrier) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (fun t : ℝ => !₂[(D.wall j).x - t, q 1] : ℝ → plane) t ∈ (D.trap i).carrier := by
  have qx : q 0 = (D.wall j).x := hq.1
  have hy₁ : (D.wall j).y₁ < q 1 := hq.2.1
  have hy₂ : q 1 < (D.wall j).y₂ := hq.2.2
  obtain ⟨hx₂, hbot, htop⟩ := h
  have hx₁lt : (D.trap i).x₁ < (D.wall j).x := by
    rw [← hx₂]; exact (D.trap i).x₁_lt_x₂
  have hbot0 : (D.trap i).bot (D.wall j).x < q 1 := by
    rw [← hx₂]; exact lt_of_le_of_lt hbot hy₁
  have htop0 : q 1 < (D.trap i).top (D.wall j).x := by
    rw [← hx₂]; exact lt_of_lt_of_le hy₂ htop
  have hsub : ContinuousAt (fun t : ℝ => (D.wall j).x - t) (0 : ℝ) :=
    continuousAt_const.sub continuousAt_id
  have hevbot : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (D.trap i).bot ((D.wall j).x - t) < q 1 := by
    have hcont : ContinuousAt (fun t : ℝ => (D.trap i).bot ((D.wall j).x - t)) (0 : ℝ) :=
      (affineContinuous (D.trap i).bot).continuousAt.comp hsub
    have hmem : Set.Iio (q 1) ∈ nhds ((D.trap i).bot ((D.wall j).x - 0)) :=
      IsOpen.mem_nhds isOpen_Iio (by simpa using hbot0)
    have hev : ∀ᶠ t in nhds (0 : ℝ),
        (fun t : ℝ => (D.trap i).bot ((D.wall j).x - t)) t < q 1 :=
      Filter.Tendsto.eventually hcont
        (Filter.eventually_of_mem hmem (fun y hy => hy))
    exact eventually_nhdsWithin_of_eventually_nhds hev
  have hevtop : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      q 1 < (D.trap i).top ((D.wall j).x - t) := by
    have hcont : ContinuousAt (fun t : ℝ => (D.trap i).top ((D.wall j).x - t)) (0 : ℝ) :=
      (affineContinuous (D.trap i).top).continuousAt.comp hsub
    have hmem : Set.Ioi (q 1) ∈ nhds ((D.trap i).top ((D.wall j).x - 0)) :=
      IsOpen.mem_nhds isOpen_Ioi (by simpa using htop0)
    have hev : ∀ᶠ t in nhds (0 : ℝ),
        q 1 < (fun t : ℝ => (D.trap i).top ((D.wall j).x - t)) t :=
      Filter.Tendsto.eventually hcont
        (Filter.eventually_of_mem hmem (fun y hy => hy))
    exact eventually_nhdsWithin_of_eventually_nhds hev
  have hxlo : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (D.trap i).x₁ < (D.wall j).x - t := by
    have hIoo := eventually_Ioo_nhdsWithin_Ioi ((D.wall j).x - (D.trap i).x₁)
      (by linarith [hx₁lt])
    exact hIoo.mono (fun t ht => by rw [Set.mem_Ioo] at ht; linarith [ht.2])
  have hxhi : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (D.wall j).x - t < (D.trap i).x₂ := by
    have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioi (0 : ℝ) :=
      Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => ht)
    exact hpos.mono (fun t ht => by rw [hx₂]; have ht0 : (0 : ℝ) < t := ht; linarith)
  refine ((((hxlo.and hxhi).and hevbot).and hevtop).mono (fun t ht => ?_))
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := ht
  show !₂[(D.wall j).x - t, q 1] ∈ (D.trap i).carrier
  have h0 : (!₂[(D.wall j).x - t, q 1] : plane) 0 = (D.wall j).x - t := rfl
  have h1c : (!₂[(D.wall j).x - t, q 1] : plane) 1 = q 1 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h0]; exact h1
  · rw [h0]; exact h2
  · rw [h0, h1c]; exact h3
  · rw [h0, h1c]; exact h4

theorem TrapDecomp.existsUnique_hasOnRight {F : Set plane} (D : TrapDecomp F)
    (hF : IsOpen F) (j : Fin D.k) :
    ∃! i : Fin D.m, (D.trap i).HasOnRight (D.wall j) := by
  obtain ⟨q, hq⟩ := (D.wall j).carrier_nonempty
  obtain ⟨i, hi⟩ := D.exists_hasOnRight_of_wall hF j
  refine ⟨i, hi, ?_⟩
  intro i' hi'
  have h1 := D.eventually_mem_trap_of_hasOnRight hi q hq
  have h2 := D.eventually_mem_trap_of_hasOnRight hi' q hq
  have hboth := (h1.and h2).frequently
  obtain ⟨t₀, ht₀, ht₀'⟩ := hboth.exists
  by_contra hne
  have hdisj := D.carrier_disjoint (Sum.inl i) (Sum.inl i')
    (fun h => hne (Sum.inl_injective h).symm)
  have hnd : ¬ Disjoint (D.carrier (Sum.inl i)) (D.carrier (Sum.inl i')) :=
    Set.not_disjoint_iff.mpr ⟨_, ht₀, ht₀'⟩
  exact hnd hdisj

/-- Every wall has a trapezoid on its right (LaValle, Planning Algorithms,
Sec. 6.2.2: every 1-cell borders two 2-cells). -/
lemma TrapDecomp.exists_hasOnLeft_of_wall {F : Set plane} (D : TrapDecomp F)
    (hF : IsOpen F) (j : Fin D.k) : ∃ i : Fin D.m, (D.trap i).HasOnLeft (D.wall j) := by
  obtain ⟨q, hq⟩ := (D.wall j).carrier_nonempty
  have hqF : q ∈ F := D.wall_carrier_subset j hq
  have qx : q 0 = (D.wall j).x := hq.1
  have hy₁ : (D.wall j).y₁ < q 1 := hq.2.1
  have hy₂ : q 1 < (D.wall j).y₂ := hq.2.2
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hF q hqF
  obtain ⟨δ₂, hδ₂, hgap⟩ := D.exists_wall_x_gap j
  have hδmin : 0 < min δ δ₂ := lt_min hδ hδ₂
  have hdist : ∀ t : ℝ, 0 < t →
      dist (!₂[(D.wall j).x + t, q 1] : plane) q = t := by
    intro t ht
    have h1 := dist_mkPoint ((D.wall j).x + t) q
    rw [dist_comm, h1, qx, show (D.wall j).x - ((D.wall j).x + t) = -t from by ring,
      abs_neg, abs_of_pos ht]
  have hgF : ∀ t ∈ Set.Ioo 0 (min δ δ₂),
      (fun t : ℝ => !₂[(D.wall j).x + t, q 1] : ℝ → plane) t ∈ F := by
    intro t ht
    rw [Set.mem_Ioo] at ht
    obtain ⟨ht0, htδ⟩ := ht
    show !₂[(D.wall j).x + t, q 1] ∈ F
    apply hball
    rw [Metric.mem_ball, hdist t ht0]
    exact lt_of_lt_of_le htδ (min_le_left _ _)
  have hgwall : ∀ t ∈ Set.Ioo 0 (min δ δ₂), ∀ j' : Fin D.k,
      (fun t : ℝ => !₂[(D.wall j).x + t, q 1] : ℝ → plane) t ∉ (D.wall j').carrier := by
    intro t ht j' hmem
    rw [Set.mem_Ioo] at ht
    obtain ⟨ht0, htδ⟩ := ht
    change !₂[(D.wall j).x + t, q 1] ∈ (D.wall j').carrier at hmem
    have h0 : (!₂[(D.wall j).x + t, q 1] : plane) 0 = (D.wall j).x + t := rfl
    obtain ⟨hx, -, -⟩ := hmem
    rw [h0] at hx
    exact (hgap t ht0 (lt_of_lt_of_le htδ (min_le_right _ _)) j').2 hx
  obtain ⟨i, hfreq⟩ := D.exists_freq_trap_of_seq
    (fun t : ℝ => !₂[(D.wall j).x + t, q 1]) (min δ δ₂) hδmin hgF hgwall
  have hclosure : q ∈ closure (D.trap i).carrier := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨t, htmem, htε⟩ :=
      (hfreq.and_eventually (eventually_Ioo_nhdsWithin_Ioi ε hε)).exists
    rw [Set.mem_Ioo] at htε
    refine ⟨(fun t : ℝ => !₂[(D.wall j).x + t, q 1] : ℝ → plane) t, htmem, ?_⟩
    have hdist' : dist q ((fun t : ℝ => !₂[(D.wall j).x + t, q 1] : ℝ → plane) t) = t := by
      show dist q !₂[(D.wall j).x + t, q 1] = t
      have h1 := dist_mkPoint ((D.wall j).x + t) q
      rw [h1, qx, show (D.wall j).x - ((D.wall j).x + t) = -t from by ring,
        abs_neg, abs_of_pos htε.1]
    rw [hdist']
    exact htε.2
  have hmem := D.closure_carrier_inter_subset hF i ⟨hclosure, hqF⟩
  rw [Set.mem_union] at hmem
  cases hmem with
  | inl hcarrier =>
      exfalso
      have hdisj := D.carrier_disjoint (Sum.inl i) (Sum.inr j)
        (show Sum.inl i ≠ Sum.inr j from by simp)
      rw [Set.disjoint_left] at hdisj
      exact hdisj hcarrier hq
  | inr hwall =>
      rw [Set.mem_iUnion] at hwall
      obtain ⟨j', hwall2⟩ := hwall
      rw [Set.mem_iUnion] at hwall2
      obtain ⟨hinc, hqj'⟩ := hwall2
      have hj'j : j' = j := by
        by_contra hne
        have hdisj := D.carrier_disjoint (Sum.inr j') (Sum.inr j)
          (fun h => hne (Sum.inr_injective h))
        rw [Set.disjoint_left] at hdisj
        exact hdisj hqj' hq
      rw [hj'j] at hinc
      cases hinc with
      | inr hleft => exact ⟨i, hleft⟩
      | inl hright =>
          obtain ⟨t₀, ht₀mem, ht₀ε⟩ :=
            (hfreq.and_eventually (eventually_Ioo_nhdsWithin_Ioi 1 one_pos)).exists
          rw [Set.mem_Ioo] at ht₀ε
          obtain ⟨ht₀0, -⟩ := ht₀ε
          obtain ⟨-, hx₂, -, -⟩ := ht₀mem
          have h0 : ((fun t : ℝ => !₂[(D.wall j).x + t, q 1] : ℝ → plane) t₀) 0 =
              (D.wall j).x + t₀ := rfl
          rw [h0] at hx₂
          obtain ⟨hxeq, -, -⟩ := hright
          rw [hxeq] at hx₂
          linarith

/-- Points just right of a wall eventually lie in any trapezoid on its right
(LaValle, Planning Algorithms, Sec. 6.2.2). -/
lemma TrapDecomp.eventually_mem_trap_of_hasOnLeft {F : Set plane} (D : TrapDecomp F)
    {i : Fin D.m} {j : Fin D.k} (h : (D.trap i).HasOnLeft (D.wall j))
    (q : plane) (hq : q ∈ (D.wall j).carrier) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (fun t : ℝ => !₂[(D.wall j).x + t, q 1] : ℝ → plane) t ∈ (D.trap i).carrier := by
  have qx : q 0 = (D.wall j).x := hq.1
  have hy₁ : (D.wall j).y₁ < q 1 := hq.2.1
  have hy₂ : q 1 < (D.wall j).y₂ := hq.2.2
  obtain ⟨hx₁, hbot, htop⟩ := h
  have hx₂gt : (D.wall j).x < (D.trap i).x₂ := by
    rw [← hx₁]; exact (D.trap i).x₁_lt_x₂
  have hbot0 : (D.trap i).bot (D.wall j).x < q 1 := by
    rw [← hx₁]; exact lt_of_le_of_lt hbot hy₁
  have htop0 : q 1 < (D.trap i).top (D.wall j).x := by
    rw [← hx₁]; exact lt_of_lt_of_le hy₂ htop
  have hsub : ContinuousAt (fun t : ℝ => (D.wall j).x + t) (0 : ℝ) :=
    continuousAt_const.add continuousAt_id
  have hevbot : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (D.trap i).bot ((D.wall j).x + t) < q 1 := by
    have hcont : ContinuousAt (fun t : ℝ => (D.trap i).bot ((D.wall j).x + t)) (0 : ℝ) :=
      (affineContinuous (D.trap i).bot).continuousAt.comp hsub
    have hmem : Set.Iio (q 1) ∈ nhds ((D.trap i).bot ((D.wall j).x + 0)) :=
      IsOpen.mem_nhds isOpen_Iio (by simpa using hbot0)
    have hev : ∀ᶠ t in nhds (0 : ℝ),
        (fun t : ℝ => (D.trap i).bot ((D.wall j).x + t)) t < q 1 :=
      Filter.Tendsto.eventually hcont
        (Filter.eventually_of_mem hmem (fun y hy => hy))
    exact eventually_nhdsWithin_of_eventually_nhds hev
  have hevtop : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      q 1 < (D.trap i).top ((D.wall j).x + t) := by
    have hcont : ContinuousAt (fun t : ℝ => (D.trap i).top ((D.wall j).x + t)) (0 : ℝ) :=
      (affineContinuous (D.trap i).top).continuousAt.comp hsub
    have hmem : Set.Ioi (q 1) ∈ nhds ((D.trap i).top ((D.wall j).x + 0)) :=
      IsOpen.mem_nhds isOpen_Ioi (by simpa using htop0)
    have hev : ∀ᶠ t in nhds (0 : ℝ),
        q 1 < (fun t : ℝ => (D.trap i).top ((D.wall j).x + t)) t :=
      Filter.Tendsto.eventually hcont
        (Filter.eventually_of_mem hmem (fun y hy => hy))
    exact eventually_nhdsWithin_of_eventually_nhds hev
  have hxhi : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (D.wall j).x + t < (D.trap i).x₂ := by
    have hIoo := eventually_Ioo_nhdsWithin_Ioi ((D.trap i).x₂ - (D.wall j).x)
      (by linarith [hx₂gt])
    exact hIoo.mono (fun t ht => by rw [Set.mem_Ioo] at ht; linarith [ht.2])
  have hxlo : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (D.trap i).x₁ < (D.wall j).x + t := by
    have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioi (0 : ℝ) :=
      Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => ht)
    exact hpos.mono (fun t ht => by rw [hx₁]; have ht0 : (0 : ℝ) < t := ht; linarith)
  refine ((((hxlo.and hxhi).and hevbot).and hevtop).mono (fun t ht => ?_))
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := ht
  show !₂[(D.wall j).x + t, q 1] ∈ (D.trap i).carrier
  have h0 : (!₂[(D.wall j).x + t, q 1] : plane) 0 = (D.wall j).x + t := rfl
  have h1c : (!₂[(D.wall j).x + t, q 1] : plane) 1 = q 1 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h0]; exact h1
  · rw [h0]; exact h2
  · rw [h0, h1c]; exact h3
  · rw [h0, h1c]; exact h4

theorem TrapDecomp.existsUnique_hasOnLeft {F : Set plane} (D : TrapDecomp F)
    (hF : IsOpen F) (j : Fin D.k) :
    ∃! i : Fin D.m, (D.trap i).HasOnLeft (D.wall j) := by
  obtain ⟨q, hq⟩ := (D.wall j).carrier_nonempty
  obtain ⟨i, hi⟩ := D.exists_hasOnLeft_of_wall hF j
  refine ⟨i, hi, ?_⟩
  intro i' hi'
  have h1 := D.eventually_mem_trap_of_hasOnLeft hi q hq
  have h2 := D.eventually_mem_trap_of_hasOnLeft hi' q hq
  have hboth := (h1.and h2).frequently
  obtain ⟨t₀, ht₀, ht₀'⟩ := hboth.exists
  by_contra hne
  have hdisj := D.carrier_disjoint (Sum.inl i) (Sum.inl i')
    (fun h => hne (Sum.inl_injective h).symm)
  have hnd : ¬ Disjoint (D.carrier (Sum.inl i)) (D.carrier (Sum.inl i')) :=
    Set.not_disjoint_iff.mpr ⟨_, ht₀, ht₀'⟩
  exact hnd hdisj

theorem TrapDecomp.wall_neighborhood {F : Set plane} (D : TrapDecomp F)
    (hF : IsOpen F) (j : Fin D.k) (p : plane) (hp : p ∈ (D.wall j).carrier) :
    ∃ U ∈ 𝓝 p, U ⊆ (D.wall j).carrier ∪
      ⋃ (i : Fin D.m) (_ : (D.trap i).HasOnRight (D.wall j) ∨ (D.trap i).HasOnLeft (D.wall j)),
        (D.trap i).carrier := by
  classical
  have px : p 0 = (D.wall j).x := hp.1
  have hy₁ : (D.wall j).y₁ < p 1 := hp.2.1
  have hy₂ : p 1 < (D.wall j).y₂ := hp.2.2
  have hpF : p ∈ F := D.wall_carrier_subset j hp
  have hFev : ∀ᶠ r in 𝓝 p, r ∈ F :=
    Filter.eventually_of_mem (hF.mem_nhds hpF) (fun r hr => hr)
  have htrap : ∀ᶠ r in 𝓝 p, ∀ i : Fin D.m,
      r ∈ (D.trap i).carrier →
        (D.trap i).HasOnRight (D.wall j) ∨ (D.trap i).HasOnLeft (D.wall j) := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hinc : (D.trap i).HasOnRight (D.wall j) ∨ (D.trap i).HasOnLeft (D.wall j)
    · exact Filter.Eventually.of_forall (fun r _ => hinc)
    · have hnot : p ∉ closure (D.trap i).carrier := by
        intro hcl
        have hmem := D.closure_carrier_inter_subset hF i ⟨hcl, hpF⟩
        rw [Set.mem_union] at hmem
        cases hmem with
        | inl hcarrier =>
            have hdisj := D.carrier_disjoint (Sum.inl i) (Sum.inr j)
              (show Sum.inl i ≠ Sum.inr j from by simp)
            rw [Set.disjoint_left] at hdisj
            exact hdisj hcarrier hp
        | inr hwall =>
            rw [Set.mem_iUnion] at hwall
            obtain ⟨j', hwall2⟩ := hwall
            rw [Set.mem_iUnion] at hwall2
            obtain ⟨hinc', hqj'⟩ := hwall2
            have hj'j : j' = j := by
              by_contra hne
              have hdisj := D.carrier_disjoint (Sum.inr j') (Sum.inr j)
                (fun h => hne (Sum.inr_injective h))
              rw [Set.disjoint_left] at hdisj
              exact hdisj hqj' hp
            rw [hj'j] at hinc'
            exact hinc hinc'
      have hcompl : (closure (D.trap i).carrier)ᶜ ∈ 𝓝 p :=
        IsClosed.compl_mem_nhds isClosed_closure hnot
      exact (Filter.eventually_of_mem hcompl (fun r hr => hr)).mono
        (fun r hr hmem => by rw [Set.mem_compl_iff] at hr; exact (hr (subset_closure hmem)).elim)
  have hwall : ∀ᶠ r in 𝓝 p, ∀ j' : Fin D.k, r ∈ (D.wall j').carrier → j' = j := by
    apply Filter.eventually_all.mpr
    intro j'
    by_cases hjj : j' = j
    · rw [hjj]
      exact Filter.Eventually.of_forall (fun r _ => rfl)
    · by_cases hxx : (D.wall j).x = (D.wall j').x
      · have hdisj := D.carrier_disjoint (Sum.inr j') (Sum.inr j)
          (fun h => hjj (Sum.inr_injective h))
        rw [Set.disjoint_left] at hdisj
        rcases lt_or_ge (p 1) (D.wall j').y₁ with hlt | hle
        · have hη : (0 : ℝ) < (D.wall j').y₁ - p 1 := by linarith [hlt]
          have hballmem : Metric.ball p ((D.wall j').y₁ - p 1) ∈ 𝓝 p :=
            Metric.ball_mem_nhds p hη
          apply Filter.eventually_of_mem hballmem
          intro r hrball hrmem
          exfalso
          obtain ⟨-, hrlo, -⟩ := hrmem
          have hdist : dist r p < (D.wall j').y₁ - p 1 := Metric.mem_ball.mp hrball
          have hcoord := abs_coord_sub_le_dist r p 1
          have hle2 : r 1 - p 1 ≤ |r 1 - p 1| := le_abs_self _
          linarith [hdist, hcoord, hle2, hrlo]
        · have hle' : (D.wall j').y₁ ≤ p 1 := hle
          rcases le_or_gt (p 1) (D.wall j').y₂ with hle2 | hgt2
          · exfalso
            rcases eq_or_lt_of_le hle' with heq | hlt'
            · have hp_eq : p = !₂[(D.wall j').x, (D.wall j').y₁] := by
                rw [mkPoint_eq_self p, px, hxx, ← heq]
              have hne := D.wall_lower_endpoint_not_mem j'
              rw [← hp_eq] at hne
              exact hne hpF
            · rcases eq_or_lt_of_le hle2 with heq2 | hlt2'
              · have hp_eq : p = !₂[(D.wall j').x, (D.wall j').y₂] := by
                  rw [mkPoint_eq_self p, px, hxx, heq2]
                have hne := D.wall_upper_endpoint_not_mem j'
                rw [← hp_eq] at hne
                exact hne hpF
              · have hmem' : p ∈ (D.wall j').carrier := ⟨by rw [px, hxx], hlt', hlt2'⟩
                exact hdisj hmem' hp
          · have hη : (0 : ℝ) < p 1 - (D.wall j').y₂ := by linarith [hgt2]
            have hballmem : Metric.ball p (p 1 - (D.wall j').y₂) ∈ 𝓝 p :=
              Metric.ball_mem_nhds p hη
            apply Filter.eventually_of_mem hballmem
            intro r hrball hrmem
            exfalso
            obtain ⟨-, -, hrhi⟩ := hrmem
            have hdist : dist r p < p 1 - (D.wall j').y₂ := Metric.mem_ball.mp hrball
            have hcoord := abs_coord_sub_le_dist r p 1
            have hle2 : -(r 1 - p 1) ≤ |r 1 - p 1| := neg_le_abs _
            linarith [hdist, hcoord, hle2, hrhi]
      · have hη : (0 : ℝ) < |(D.wall j).x - (D.wall j').x| :=
          abs_pos.mpr (sub_ne_zero.mpr hxx)
        have hballmem : Metric.ball p |(D.wall j).x - (D.wall j').x| ∈ 𝓝 p :=
          Metric.ball_mem_nhds p hη
        apply Filter.eventually_of_mem hballmem
        intro r hrball hrmem
        exfalso
        obtain ⟨hrx, -, -⟩ := hrmem
        have hdist : dist r p < |(D.wall j).x - (D.wall j').x| := Metric.mem_ball.mp hrball
        have hcoord := abs_coord_sub_le_dist r p 0
        have habs : |r 0 - p 0| = |(D.wall j).x - (D.wall j').x| := by
          rw [hrx, px, abs_sub_comm]
        linarith [hdist, hcoord, habs]
  have hkey : ∀ᶠ r in 𝓝 p, r ∈ F ∧
      (∀ i : Fin D.m, r ∈ (D.trap i).carrier →
        (D.trap i).HasOnRight (D.wall j) ∨ (D.trap i).HasOnLeft (D.wall j)) ∧
      (∀ j' : Fin D.k, r ∈ (D.wall j').carrier → j' = j) :=
    ((hFev.and htrap).and hwall).mono (fun r hr => ⟨hr.1.1, hr.1.2, hr.2⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hkey
  refine ⟨Metric.ball p ε, Metric.ball_mem_nhds p hε, ?_⟩
  intro r hr
  have hdist : dist r p < ε := Metric.mem_ball.mp hr
  obtain ⟨hrF, htr, hwl⟩ := hball hdist
  obtain ⟨c, hc, -⟩ := D.existsUnique_cell r hrF
  cases c with
  | inl i =>
      have hinc := htr i hc
      exact Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hinc, hc⟩⟩)
  | inr j' =>
      have hjj : j' = j := hwl j' hc
      rw [hjj] at hc
      exact Or.inl hc

end VerticalCells

end Cslib.Planning.MotionPlanning
