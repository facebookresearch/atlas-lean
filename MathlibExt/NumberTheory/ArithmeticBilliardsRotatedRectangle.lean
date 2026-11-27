/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Data.ZMod.Basic

/-!
# Arithmetic billiards in a tilted rectangle

For a prime `p ≡ 1 (mod 4)` and an even `l`, a billiard path in the tilted rectangle
determined by `p` and `l` exists, and every such path visits each integer point of the
boundary of the rectangle exactly once, ends at `(m, 0)`, and is symmetric under swapping
coordinates.
-/

namespace MetaMathlibExt

@[expose] public section

namespace ArithmeticBilliardsRotatedRectangle

/-- **Boundary points of the tilted rectangle, in integer coordinates.** A point
`q = (x, y)` of `ℤ × ℤ` lies on the boundary of the tilted rectangle when, with
`s = x + y` and `d = x - y`, the inequalities `m ≤ s ≤ p - m` and `-m ≤ d ≤ m` hold
and one of the four equalities `s = m`, `s = p - m`, `d = m`, `d = -m` holds. -/
private def bdry (p m : ℕ) (q : ℤ × ℤ) : Prop :=
  (m : ℤ) ≤ q.1 + q.2 ∧ q.1 + q.2 ≤ (p : ℤ) - m ∧ -(m : ℤ) ≤ q.1 - q.2 ∧
    q.1 - q.2 ≤ (m : ℤ) ∧
    (q.1 + q.2 = (m : ℤ) ∨ q.1 + q.2 = (p : ℤ) - m ∨ q.1 - q.2 = (m : ℤ) ∨
      q.1 - q.2 = -(m : ℤ))

/-- **Horizontal partner on the boundary.** The other boundary point sharing the second
coordinate with `q`: its sum `s' = x' + y` is the other endpoint of the interval of
sums attainable on the horizontal line through `q`. -/
private def horizPartner (p m : ℕ) (q : ℤ × ℤ) : ℤ × ℤ :=
  (max (m : ℤ) (2 * q.2 - m) + min ((p : ℤ) - m) (2 * q.2 + m) - (q.1 + q.2) - q.2, q.2)

/-- **Vertical partner on the boundary.** The other boundary point sharing the first
coordinate with `q`: its sum `s' = x + y'` is the other endpoint of the interval of
sums attainable on the vertical line through `q`. -/
private def vertPartner (p m : ℕ) (q : ℤ × ℤ) : ℤ × ℤ :=
  (q.1, max (m : ℤ) (2 * q.1 - m) + min ((p : ℤ) - m) (2 * q.1 + m) - (q.1 + q.2) - q.1)

/-- **Sign of a boundary point.** The sign is `-1` on the two edges `s = m` and
`d = m` (the left and top edges in `(s, d)` coordinates) and `1` on the other two
edges. -/
private def sgn (m : ℕ) (q : ℤ × ℤ) : ℤ :=
  if q.1 + q.2 = (m : ℤ) ∨ q.1 - q.2 = (m : ℤ) then -1 else 1

/-- The tilted rectangle is the set of points whose `(s, d)` coordinates lie in the
interval rectangle. -/
private theorem convexHull_eq_rectangle (p m : ℕ) (c : ℝ)
    (hm : (0 : ℝ) < (m : ℝ)) (h2m : 2 * (m : ℝ) < (p : ℝ)) (hc : c = (p : ℝ) / 2 - (m : ℝ)) :
    convexHull ℝ ({((0 : ℝ), (m : ℝ)), ((m : ℝ), (0 : ℝ)), ((p : ℝ) / 2, c),
        (c, (p : ℝ) / 2)} : Set (ℝ × ℝ)) =
      {q : ℝ × ℝ | (m : ℝ) ≤ q.1 + q.2 ∧ q.1 + q.2 ≤ (p : ℝ) - m ∧
        -(m : ℝ) ≤ q.1 - q.2 ∧ q.1 - q.2 ≤ (m : ℝ)} := by
  subst hc
  have hden : (0 : ℝ) < (p : ℝ) - 2 * (m : ℝ) := by linarith
  apply le_antisymm
  · apply convexHull_min
    · intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · intro x hx y hy a b ha hb hab
      simp only [Set.mem_ofPred_eq] at hx hy ⊢
      obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
      obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
      have e1 : (a • x + b • y).1 = a * x.1 + b * y.1 := by simp
      have e2 : (a • x + b • y).2 = a * x.2 + b * y.2 := by simp
      rw [e1, e2]
      have hsum : (a * x.1 + b * y.1) + (a * x.2 + b * y.2)
          = a * (x.1 + x.2) + b * (y.1 + y.2) := by ring
      have hdiff : (a * x.1 + b * y.1) - (a * x.2 + b * y.2)
          = a * (x.1 - x.2) + b * (y.1 - y.2) := by ring
      rw [hsum, hdiff]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hab]
  · intro q hq
    simp only [Set.mem_ofPred_eq] at hq
    obtain ⟨hs1, hs2, hd1, hd2⟩ := hq
    set α : ℝ := (q.1 + q.2 - (m : ℝ)) / ((p : ℝ) - 2 * (m : ℝ)) with hαdef
    set β : ℝ := (q.1 - q.2 + (m : ℝ)) / (2 * (m : ℝ)) with hβdef
    have hα0 : 0 ≤ α := by rw [hαdef]; apply div_nonneg <;> linarith
    have hα1 : α ≤ 1 := by rw [hαdef, div_le_one hden]; linarith
    have hβ0 : 0 ≤ β := by rw [hβdef]; apply div_nonneg <;> linarith
    have hβ1 : β ≤ 1 := by rw [hβdef, div_le_one (by linarith)]; linarith
    have hαmul : α * ((p : ℝ) - 2 * (m : ℝ)) = q.1 + q.2 - (m : ℝ) := by
      rw [hαdef, div_mul_cancel₀ _ (ne_of_gt hden)]
    have hβmul : β * (2 * (m : ℝ)) = q.1 - q.2 + (m : ℝ) := by
      rw [hβdef, div_mul_cancel₀ _ (by positivity)]
    have hβm : β * (m : ℝ) = (q.1 - q.2 + (m : ℝ)) / 2 := by
      have h : 2 * (β * (m : ℝ)) = q.1 - q.2 + (m : ℝ) := by rw [← hβmul]; ring
      linarith
    have hαm : α * ((p : ℝ) / 2 - (m : ℝ)) = (q.1 + q.2 - (m : ℝ)) / 2 := by
      have h : 2 * (α * ((p : ℝ) / 2 - (m : ℝ))) = q.1 + q.2 - (m : ℝ) := by
        have hα' := hαmul; nlinarith [hα']
      linarith
    let w : Fin 4 → ℝ := ![ (1 - α) * (1 - β), (1 - α) * β, α * β, α * (1 - β) ]
    let z : Fin 4 → ℝ × ℝ :=
      ![ ((0 : ℝ), (m : ℝ)), ((m : ℝ), (0 : ℝ)), ((p : ℝ) / 2, (p : ℝ) / 2 - (m : ℝ)),
        ((p : ℝ) / 2 - (m : ℝ), (p : ℝ) / 2) ]
    have hw0 : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intro i _; fin_cases i <;> simp [w] <;> nlinarith
    have hsum : ∑ i, w i = 1 := by simp [w, Fin.sum_univ_four]; ring
    have hz : ∀ i ∈ Finset.univ, z i ∈
        ({((0 : ℝ), (m : ℝ)), ((m : ℝ), (0 : ℝ)), ((p : ℝ) / 2, (p : ℝ) / 2 - (m : ℝ)),
          ((p : ℝ) / 2 - (m : ℝ), (p : ℝ) / 2)} : Set (ℝ × ℝ)) := by
      intro i _; fin_cases i <;> simp [z]
    have hmem := Finset.centerMass_mem_convexHull Finset.univ hw0 (by rw [hsum]; norm_num) hz
    have hcm : Finset.centerMass Finset.univ w z = q := by
      rw [Finset.centerMass_eq_of_sum_1 (hw := hsum), Fin.sum_univ_four]
      simp only [w, z, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
      rw [Prod.ext_iff]
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul]
      constructor
      · have e1 : (1 - α) * (1 - β) * 0 + (1 - α) * β * (m : ℝ) +
            α * β * ((p : ℝ) / 2) + α * (1 - β) * ((p : ℝ) / 2 - (m : ℝ))
              = β * (m : ℝ) + α * ((p : ℝ) / 2 - (m : ℝ)) := by ring
        rw [e1, hβm, hαm]; ring
      · have e2 : (1 - α) * (1 - β) * (m : ℝ) + (1 - α) * β * 0 +
            α * β * ((p : ℝ) / 2 - (m : ℝ)) + α * (1 - β) * ((p : ℝ) / 2)
              = (m : ℝ) - β * (m : ℝ) + α * ((p : ℝ) / 2 - (m : ℝ)) := by ring
        rw [e2, hβm, hαm]; ring
    rw [← hcm]; exact hmem

/-- A point of the rectangle with a boundary equality is not in its interior: a small
ball around it meets points outside the rectangle. -/
private theorem not_mem_interior_of_boundary (p m : ℕ) (c : ℝ)
    (hm : (0 : ℝ) < (m : ℝ)) (h2m : 2 * (m : ℝ) < (p : ℝ)) (hc : c = (p : ℝ) / 2 - (m : ℝ))
    (q : ℝ × ℝ)
    (hbd : q.1 + q.2 = (m : ℝ) ∨ q.1 + q.2 = (p : ℝ) - m ∨ q.1 - q.2 = (m : ℝ) ∨
      q.1 - q.2 = -(m : ℝ)) :
    q ∉ interior (convexHull ℝ ({((0 : ℝ), (m : ℝ)), ((m : ℝ), (0 : ℝ)), ((p : ℝ) / 2, c),
        (c, (p : ℝ) / 2)} : Set (ℝ × ℝ))) := by
  rw [convexHull_eq_rectangle p m c hm h2m hc]
  intro hmem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hmem)
  have hball' : ∀ r : ℝ × ℝ, dist r q < ε →
      (m : ℝ) ≤ r.1 + r.2 ∧ r.1 + r.2 ≤ (p : ℝ) - m ∧ -(m : ℝ) ≤ r.1 - r.2 ∧
        r.1 - r.2 ≤ (m : ℝ) := by
    intro r hr
    have hr' : r ∈ Metric.ball q ε := Metric.mem_ball.mpr hr
    have hr'' := hball hr'
    simpa only [Set.mem_ofPred_eq] using hr''
  have hdist : ∀ a b : ℝ, dist (q.1 + a, q.2 + b) q = max |a| |b| := by
    intro a b
    rw [Prod.dist_eq]
    simp only [Real.dist_eq]
    rw [show q.1 + a - q.1 = a by ring, show q.2 + b - q.2 = b by ring]
  have hlt : max (ε / 2) (ε / 2) < ε := by rw [max_self]; linarith
  rcases hbd with hs | hs | hd | hd
  · have hpt := hball' (q.1 + -(ε / 2), q.2 + -(ε / 2)) (by
      rw [hdist, abs_neg, abs_of_pos (half_pos hε)]; exact hlt)
    obtain ⟨hlo, -, -, -⟩ := hpt
    have hsum : (q.1 + -(ε / 2)) + (q.2 + -(ε / 2)) = (m : ℝ) - ε := by linarith [hs]
    linarith
  · have hpt := hball' (q.1 + ε / 2, q.2 + ε / 2) (by
      rw [hdist, abs_of_pos (half_pos hε)]; exact hlt)
    obtain ⟨-, hhi, -, -⟩ := hpt
    have hsum : (q.1 + ε / 2) + (q.2 + ε / 2) = ((p : ℝ) - m) + ε := by linarith [hs]
    linarith
  · have hpt := hball' (q.1 + ε / 2, q.2 + -(ε / 2)) (by
      rw [hdist, abs_neg, abs_of_pos (half_pos hε)]; exact hlt)
    obtain ⟨-, -, -, hhi⟩ := hpt
    have hdiff : (q.1 + ε / 2) - (q.2 + -(ε / 2)) = (m : ℝ) + ε := by linarith [hd]
    linarith
  · have hpt := hball' (q.1 + -(ε / 2), q.2 + ε / 2) (by
      rw [hdist, abs_neg, abs_of_pos (half_pos hε)]; exact hlt)
    obtain ⟨-, -, hlo, -⟩ := hpt
    have hdiff : (q.1 + -(ε / 2)) - (q.2 + ε / 2) = -(m : ℝ) - ε := by linarith [hd]
    linarith

/-- Membership in the frontier of the tilted rectangle, in coordinates. -/
private theorem mem_frontier_iff (p m : ℕ) (c : ℝ)
    (hm : (0 : ℝ) < (m : ℝ)) (h2m : 2 * (m : ℝ) < (p : ℝ)) (hc : c = (p : ℝ) / 2 - (m : ℝ))
    (q : ℝ × ℝ) :
    q ∈ frontier (convexHull ℝ ({((0 : ℝ), (m : ℝ)), ((m : ℝ), (0 : ℝ)), ((p : ℝ) / 2, c),
        (c, (p : ℝ) / 2)} : Set (ℝ × ℝ))) ↔
      ((m : ℝ) ≤ q.1 + q.2 ∧ q.1 + q.2 ≤ (p : ℝ) - m ∧ -(m : ℝ) ≤ q.1 - q.2 ∧
        q.1 - q.2 ≤ (m : ℝ) ∧
        (q.1 + q.2 = (m : ℝ) ∨ q.1 + q.2 = (p : ℝ) - m ∨ q.1 - q.2 = (m : ℝ) ∨
          q.1 - q.2 = -(m : ℝ))) := by
  have hclosed : IsClosed (convexHull ℝ ({((0 : ℝ), (m : ℝ)), ((m : ℝ), (0 : ℝ)),
      ((p : ℝ) / 2, c), (c, (p : ℝ) / 2)} : Set (ℝ × ℝ))) :=
    (Set.Finite.insert _ (Set.Finite.insert _
      (Set.Finite.insert _ (Set.finite_singleton _)))).isClosed_convexHull ℝ
  have hrect := convexHull_eq_rectangle p m c hm h2m hc
  have hInt : interior (convexHull ℝ ({((0 : ℝ), (m : ℝ)), ((m : ℝ), (0 : ℝ)),
      ((p : ℝ) / 2, c), (c, (p : ℝ) / 2)} : Set (ℝ × ℝ))) =
      {q : ℝ × ℝ | (m : ℝ) < q.1 + q.2 ∧ q.1 + q.2 < (p : ℝ) - m ∧
        -(m : ℝ) < q.1 - q.2 ∧ q.1 - q.2 < (m : ℝ)} := by
    apply le_antisymm
    · intro q hq
      rw [hrect] at hq
      have hb : q ∈ {q : ℝ × ℝ | (m : ℝ) ≤ q.1 + q.2 ∧ q.1 + q.2 ≤ (p : ℝ) - m ∧
          -(m : ℝ) ≤ q.1 - q.2 ∧ q.1 - q.2 ≤ (m : ℝ)} := interior_subset hq
      simp only [Set.mem_ofPred_eq] at hb
      obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
      simp only [Set.mem_ofPred_eq]
      by_cases hs : q.1 + q.2 = (m : ℝ)
      · exfalso
        exact not_mem_interior_of_boundary p m c hm h2m hc q (Or.inl hs)
          (by rw [hrect]; exact hq)
      · by_cases hs2 : q.1 + q.2 = (p : ℝ) - m
        · exfalso
          exact not_mem_interior_of_boundary p m c hm h2m hc q (Or.inr (Or.inl hs2))
            (by rw [hrect]; exact hq)
        · by_cases hd : q.1 - q.2 = (m : ℝ)
          · exfalso
            exact not_mem_interior_of_boundary p m c hm h2m hc q
              (Or.inr (Or.inr (Or.inl hd))) (by rw [hrect]; exact hq)
          · by_cases hd2 : q.1 - q.2 = -(m : ℝ)
            · exfalso
              exact not_mem_interior_of_boundary p m c hm h2m hc q
                (Or.inr (Or.inr (Or.inr hd2))) (by rw [hrect]; exact hq)
            · exact ⟨lt_of_le_of_ne hb1 (Ne.symm hs), lt_of_le_of_ne hb2 hs2,
                lt_of_le_of_ne hb3 (Ne.symm hd2), lt_of_le_of_ne hb4 hd⟩
    · intro q hq
      simp only [Set.mem_ofPred_eq] at hq
      obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
      have hopen : IsOpen {q : ℝ × ℝ | (m : ℝ) < q.1 + q.2 ∧ q.1 + q.2 < (p : ℝ) - m ∧
          -(m : ℝ) < q.1 - q.2 ∧ q.1 - q.2 < (m : ℝ)} := by
        have h1 : IsOpen {q : ℝ × ℝ | (m : ℝ) < q.1 + q.2} :=
          isOpen_lt continuous_const (continuous_fst.add continuous_snd)
        have h2 : IsOpen {q : ℝ × ℝ | q.1 + q.2 < (p : ℝ) - m} :=
          isOpen_lt (continuous_fst.add continuous_snd) continuous_const
        have h3 : IsOpen {q : ℝ × ℝ | -(m : ℝ) < q.1 - q.2} :=
          isOpen_lt continuous_const (continuous_fst.sub continuous_snd)
        have h4 : IsOpen {q : ℝ × ℝ | q.1 - q.2 < (m : ℝ)} :=
          isOpen_lt (continuous_fst.sub continuous_snd) continuous_const
        have hset : {q : ℝ × ℝ | (m : ℝ) < q.1 + q.2 ∧ q.1 + q.2 < (p : ℝ) - m ∧
            -(m : ℝ) < q.1 - q.2 ∧ q.1 - q.2 < (m : ℝ)}
            = {q : ℝ × ℝ | (m : ℝ) < q.1 + q.2} ∩ {q : ℝ × ℝ | q.1 + q.2 < (p : ℝ) - m} ∩
              {q : ℝ × ℝ | -(m : ℝ) < q.1 - q.2} ∩ {q : ℝ × ℝ | q.1 - q.2 < (m : ℝ)} := by
          ext r; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
        rw [hset]
        exact ((h1.inter h2).inter h3).inter h4
      refine mem_interior.mpr ⟨_, ?_, hopen, ⟨hq1, hq2, hq3, hq4⟩⟩
      intro r hr
      simp only [Set.mem_ofPred_eq] at hr
      obtain ⟨hr1, hr2, hr3, hr4⟩ := hr
      rw [hrect]
      simp only [Set.mem_ofPred_eq]
      exact ⟨hr1.le, hr2.le, hr3.le, hr4.le⟩
  have hInt' : interior {q : ℝ × ℝ | (m : ℝ) ≤ q.1 + q.2 ∧ q.1 + q.2 ≤ (p : ℝ) - m ∧
      -(m : ℝ) ≤ q.1 - q.2 ∧ q.1 - q.2 ≤ (m : ℝ)} =
      {q : ℝ × ℝ | (m : ℝ) < q.1 + q.2 ∧ q.1 + q.2 < (p : ℝ) - m ∧
        -(m : ℝ) < q.1 - q.2 ∧ q.1 - q.2 < (m : ℝ)} := by
    rw [← hrect]; exact hInt
  rw [IsClosed.frontier_eq hclosed, hrect, hInt']
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hb1, hb2, hb3, hb4⟩, hnot⟩
    refine ⟨hb1, hb2, hb3, hb4, ?_⟩
    by_cases hs : q.1 + q.2 = (m : ℝ)
    · exact Or.inl hs
    · by_cases hs2 : q.1 + q.2 = (p : ℝ) - m
      · exact Or.inr (Or.inl hs2)
      · by_cases hd : q.1 - q.2 = (m : ℝ)
        · exact Or.inr (Or.inr (Or.inl hd))
        · by_cases hd2 : q.1 - q.2 = -(m : ℝ)
          · exact Or.inr (Or.inr (Or.inr hd2))
          · exfalso
            exact hnot ⟨lt_of_le_of_ne hb1 (Ne.symm hs), lt_of_le_of_ne hb2 hs2,
              lt_of_le_of_ne hb3 (Ne.symm hd2), lt_of_le_of_ne hb4 hd⟩
  · rintro ⟨hb1, hb2, hb3, hb4, hbd⟩
    refine ⟨⟨hb1, hb2, hb3, hb4⟩, ?_⟩
    intro hstrict
    have hmem : q ∈ interior (convexHull ℝ ({((0 : ℝ), (m : ℝ)), ((m : ℝ), (0 : ℝ)),
        ((p : ℝ) / 2, c), (c, (p : ℝ) / 2)} : Set (ℝ × ℝ))) := by
      rw [hInt]; exact hstrict
    exact not_mem_interior_of_boundary p m c hm h2m hc q hbd hmem

/-- Membership in the frontier for integer points, in integer coordinates. -/
private theorem mem_frontier_int_iff (p m : ℕ) (c : ℝ)
    (hm : (0 : ℝ) < (m : ℝ)) (h2m : 2 * (m : ℝ) < (p : ℝ)) (hc : c = (p : ℝ) / 2 - (m : ℝ))
    (q : ℤ × ℤ) :
    ((q.1 : ℝ), (q.2 : ℝ)) ∈ frontier (convexHull ℝ ({((0 : ℝ), (m : ℝ)), ((m : ℝ), (0 : ℝ)),
        ((p : ℝ) / 2, c), (c, (p : ℝ) / 2)} : Set (ℝ × ℝ))) ↔ bdry p m q := by
  rw [mem_frontier_iff p m c hm h2m hc]
  dsimp only
  unfold bdry
  constructor <;> rintro ⟨h1, h2, h3, h4, h5⟩ <;>
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3,
      by exact_mod_cast h4, by exact_mod_cast h5⟩

/-- The horizontal partner of a boundary point is a boundary point. -/
private theorem horizPartner_bdry (p m : ℕ) (q : ℤ × ℤ) (hq : bdry p m q) :
    bdry p m (horizPartner p m q) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hq
  have e1 : (horizPartner p m q).1 =
      max (m : ℤ) (2 * q.2 - m) + min ((p : ℤ) - m) (2 * q.2 + m) - (q.1 + q.2) - q.2 := rfl
  have e2 : (horizPartner p m q).2 = q.2 := rfl
  unfold bdry
  simp only [e1, e2]
  constructor <;> omega

/-- The vertical partner of a boundary point is a boundary point. -/
private theorem vertPartner_bdry (p m : ℕ) (q : ℤ × ℤ) (hq : bdry p m q) :
    bdry p m (vertPartner p m q) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hq
  have e1 : (vertPartner p m q).1 = q.1 := rfl
  have e2 : (vertPartner p m q).2 =
      max (m : ℤ) (2 * q.1 - m) + min ((p : ℤ) - m) (2 * q.1 + m) - (q.1 + q.2) - q.1 := rfl
  unfold bdry
  simp only [e1, e2]
  constructor <;> omega

/-- Uniqueness of the horizontal partner: any other boundary point sharing the second
coordinate is the horizontal partner. -/
private theorem horizPartner_unique (p m : ℕ) (q r : ℤ × ℤ) (hq : bdry p m q)
    (hr : bdry p m r) (h2 : r.2 = q.2) (hne : r ≠ q) : r = horizPartner p m q := by
  obtain ⟨hq1, hq2, hq3, hq4, hq5⟩ := hq
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hr
  have hne1 : r.1 ≠ q.1 := fun h => hne (Prod.ext h h2)
  have e1 : (horizPartner p m q).1 =
      max (m : ℤ) (2 * q.2 - m) + min ((p : ℤ) - m) (2 * q.2 + m) - (q.1 + q.2) - q.2 := rfl
  have e2 : (horizPartner p m q).2 = q.2 := rfl
  apply Prod.ext
  · omega
  · omega

/-- Uniqueness of the vertical partner: any other boundary point sharing the first
coordinate is the vertical partner. -/
private theorem vertPartner_unique (p m : ℕ) (q r : ℤ × ℤ) (hq : bdry p m q)
    (hr : bdry p m r) (h1 : r.1 = q.1) (hne : r ≠ q) : r = vertPartner p m q := by
  obtain ⟨h1', h2, h3, h4, h5⟩ := hq
  obtain ⟨g1, g2, g3, g4, g5⟩ := hr
  have hne2 : r.2 ≠ q.2 := fun h => hne (Prod.ext h1 h)
  have e1 : (vertPartner p m q).1 = q.1 := rfl
  have e2 : (vertPartner p m q).2 =
      max (m : ℤ) (2 * q.1 - m) + min ((p : ℤ) - m) (2 * q.1 + m) - (q.1 + q.2) - q.1 := rfl
  apply Prod.ext
  · omega
  · omega

/-- A boundary point sharing the first coordinate with `q` is either `q` or its
vertical partner. -/
private theorem vertPartner_or_eq (p m : ℕ) (q r : ℤ × ℤ) (hq : bdry p m q)
    (hr : bdry p m r) (h1 : r.1 = q.1) : r = q ∨ r = vertPartner p m q := by
  obtain ⟨h1', h2, h3, h4, h5⟩ := hq
  obtain ⟨g1, g2, g3, g4, g5⟩ := hr
  have e1 : (vertPartner p m q).1 = q.1 := rfl
  have e2 : (vertPartner p m q).2 =
      max (m : ℤ) (2 * q.1 - m) + min ((p : ℤ) - m) (2 * q.1 + m) - (q.1 + q.2) - q.1 := rfl
  have hendq : q.1 + q.2 = max (m : ℤ) (2 * q.1 - m) ∨
      q.1 + q.2 = min ((p : ℤ) - m) (2 * q.1 + m) := by omega
  have hendr : r.1 + r.2 = max (m : ℤ) (2 * q.1 - m) ∨
      r.1 + r.2 = min ((p : ℤ) - m) (2 * q.1 + m) := by omega
  rcases hendq with hq' | hq' <;> rcases hendr with hr' | hr'
  · left; apply Prod.ext <;> omega
  · right; apply Prod.ext <;> omega
  · right; apply Prod.ext <;> omega
  · left; apply Prod.ext <;> omega

/-- The horizontal partner is an involution. -/
private theorem horizPartner_involutive (p m : ℕ) (q : ℤ × ℤ) :
    horizPartner p m (horizPartner p m q) = q := by
  apply Prod.ext
  · have e2 : (horizPartner p m q).2 = q.2 := rfl
    have e1 : (horizPartner p m q).1 =
        max (m : ℤ) (2 * q.2 - m) + min ((p : ℤ) - m) (2 * q.2 + m) - (q.1 + q.2) - q.2 := rfl
    have e3 : (horizPartner p m (horizPartner p m q)).1 =
        max (m : ℤ) (2 * (horizPartner p m q).2 - m) +
        min ((p : ℤ) - m) (2 * (horizPartner p m q).2 + m) -
        ((horizPartner p m q).1 + (horizPartner p m q).2) - (horizPartner p m q).2 := rfl
    rw [e3]; omega
  · rfl

/-- The vertical partner is an involution. -/
private theorem vertPartner_involutive (p m : ℕ) (q : ℤ × ℤ) :
    vertPartner p m (vertPartner p m q) = q := by
  apply Prod.ext
  · rfl
  · have e1 : (vertPartner p m q).1 = q.1 := rfl
    have e2 : (vertPartner p m q).2 =
        max (m : ℤ) (2 * q.1 - m) + min ((p : ℤ) - m) (2 * q.1 + m) - (q.1 + q.2) - q.1 := rfl
    have e3 : (vertPartner p m (vertPartner p m q)).2 =
        max (m : ℤ) (2 * (vertPartner p m q).1 - m) +
        min ((p : ℤ) - m) (2 * (vertPartner p m q).1 + m) -
        ((vertPartner p m q).1 + (vertPartner p m q).2) - (vertPartner p m q).1 := rfl
    rw [e3]; omega

/-- The horizontal partner differs from the point, except at `(m, 0)`. -/
private theorem horizPartner_ne (p m : ℕ) (hp4 : p % 4 = 1) (hm : 0 < m) (_h2m : 2 * m < p)
    (q : ℤ × ℤ) (hq : bdry p m q) (hne : q ≠ ((m : ℤ), 0)) :
    horizPartner p m q ≠ q := by
  intro hEq
  have h1 : (horizPartner p m q).1 = q.1 := congrArg Prod.fst hEq
  have hHP1 : (horizPartner p m q).1 =
      max (m : ℤ) (2 * q.2 - m) + min ((p : ℤ) - m) (2 * q.2 + m) - (q.1 + q.2) - q.2 := rfl
  obtain ⟨h2', h3, h4, h5, h6⟩ := hq
  have hqeq : q = ((m : ℤ), 0) := by apply Prod.ext <;> omega
  exact hne hqeq

/-- The vertical partner differs from the point, except at `(0, m)`. -/
private theorem vertPartner_ne (p m : ℕ) (hp4 : p % 4 = 1) (hm : 0 < m) (_h2m : 2 * m < p)
    (q : ℤ × ℤ) (hq : bdry p m q) (hne : q ≠ ((0 : ℤ), (m : ℤ))) :
    vertPartner p m q ≠ q := by
  intro hEq
  have h2 : (vertPartner p m q).2 = q.2 := congrArg Prod.snd hEq
  have hVP2 : (vertPartner p m q).2 =
      max (m : ℤ) (2 * q.1 - m) + min ((p : ℤ) - m) (2 * q.1 + m) - (q.1 + q.2) - q.1 := rfl
  obtain ⟨h2', h3, h4, h5, h6⟩ := hq
  have hqeq : q = ((0 : ℤ), (m : ℤ)) := by apply Prod.ext <;> omega
  exact hne hqeq

/-- Swapping coordinates exchanges boundary points. -/
private theorem bdry_swap (p m : ℕ) (q : ℤ × ℤ) : bdry p m q.swap ↔ bdry p m q := by
  unfold bdry
  simp only [Prod.swap]
  constructor <;> intro h <;> obtain ⟨h1, h2, h3, h4, h5⟩ := h <;>
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Swapping coordinates exchanges the two partners. -/
private theorem swap_horizPartner (p m : ℕ) (q : ℤ × ℤ) :
    (horizPartner p m q).swap = vertPartner p m q.swap := by
  ext <;> simp [horizPartner, vertPartner, Prod.swap, add_comm]

/-- Swapping coordinates exchanges the two partners. -/
private theorem swap_vertPartner (p m : ℕ) (q : ℤ × ℤ) :
    (vertPartner p m q).swap = horizPartner p m q.swap := by
  ext <;> simp [horizPartner, vertPartner, Prod.swap, add_comm]

/-- The sign is `-1` on the left and top edges. -/
private theorem sgn_eq_neg {m : ℕ} {r : ℤ × ℤ}
    (h : r.1 + r.2 = (m : ℤ) ∨ r.1 - r.2 = (m : ℤ)) : sgn m r = -1 := by
  simp [sgn, h]

/-- The sign is `1` on the bottom and right edges. -/
private theorem sgn_eq_one {m : ℕ} {r : ℤ × ℤ}
    (h : ¬ (r.1 + r.2 = (m : ℤ) ∨ r.1 - r.2 = (m : ℤ))) : sgn m r = 1 := by
  simp [sgn, h]

/-- The vertical partner flips the signed coordinate: `sgn * x` changes sign. -/
private theorem sgn_vertPartner (p m : ℕ) (hp4 : p % 4 = 1) (hm : 0 < m) (_h2m : 2 * m < p)
    (q : ℤ × ℤ) (hq : bdry p m q) :
    sgn m (vertPartner p m q) * (vertPartner p m q).1 = -(sgn m q * q.1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hq
  have hVP1 : (vertPartner p m q).1 = q.1 := rfl
  set lo : ℤ := max (m : ℤ) (2 * q.1 - m) with hlo_def
  set hi : ℤ := min ((p : ℤ) - m) (2 * q.1 + m) with hhi_def
  have hlo : lo = (m : ℤ) ∨ lo = 2 * q.1 - (m : ℤ) := by rw [hlo_def]; omega
  have hhi : hi = (p : ℤ) - (m : ℤ) ∨ hi = 2 * q.1 + (m : ℤ) := by rw [hhi_def]; omega
  have hlo_le : lo ≤ q.1 + q.2 := by rw [hlo_def]; omega
  have hhi_ge : q.1 + q.2 ≤ hi := by rw [hhi_def]; omega
  have hlo_ge1 : (m : ℤ) ≤ lo := by rw [hlo_def]; omega
  have hlo_ge2 : 2 * q.1 - (m : ℤ) ≤ lo := by rw [hlo_def]; omega
  have hhi_le1 : hi ≤ (p : ℤ) - (m : ℤ) := by rw [hhi_def]; omega
  have hhi_le2 : hi ≤ 2 * q.1 + (m : ℤ) := by rw [hhi_def]; omega
  have hVP2 : (vertPartner p m q).2 = lo + hi - (q.1 + q.2) - q.1 := by
    change max (m : ℤ) (2 * q.1 - m) + min ((p : ℤ) - m) (2 * q.1 + m) - (q.1 + q.2) - q.1
      = lo + hi - (q.1 + q.2) - q.1
    rw [hlo_def, hhi_def]
  have hvp : (vertPartner p m q).1 + (vertPartner p m q).2 = lo + hi - (q.1 + q.2) := by omega
  have hend : q.1 + q.2 = lo ∨ q.1 + q.2 = hi := by omega
  have hendVP : (vertPartner p m q).1 + (vertPartner p m q).2 = lo ∨
      (vertPartner p m q).1 + (vertPartner p m q).2 = hi := by omega
  by_cases hdeg : lo = hi
  · have hx0 : q.1 = 0 := by omega
    have hVPeq : vertPartner p m q = q := by apply Prod.ext <;> omega
    rw [hVPeq, hx0]; simp
  · have hlt : lo < hi := lt_of_le_of_ne (le_trans hlo_le hhi_ge) hdeg
    rcases hend with hs | hs <;> rcases hendVP with ht | ht
    · exfalso; omega
    · have hVP : ¬ ((vertPartner p m q).1 + (vertPartner p m q).2 = (m : ℤ) ∨
          (vertPartner p m q).1 - (vertPartner p m q).2 = (m : ℤ)) := by omega
      have hq' : q.1 + q.2 = (m : ℤ) ∨ q.1 - q.2 = (m : ℤ) := by omega
      rw [sgn_eq_one hVP, sgn_eq_neg hq', hVP1]; omega
    · have hVP : (vertPartner p m q).1 + (vertPartner p m q).2 = (m : ℤ) ∨
          (vertPartner p m q).1 - (vertPartner p m q).2 = (m : ℤ) := by omega
      have hq' : ¬ (q.1 + q.2 = (m : ℤ) ∨ q.1 - q.2 = (m : ℤ)) := by omega
      rw [sgn_eq_neg hVP, sgn_eq_one hq', hVP1]; omega
    · exfalso; omega

/-- The horizontal partner shifts the signed coordinate by `-2m` modulo `p`: as integers,
the sum `sgn * x' + sgn * x + 2m` is `0`, `p`, `-p` or `2p`. -/
private theorem horizPartner_sgn_sum (p m : ℕ) (hp4 : p % 4 = 1) (hm : 0 < m)
    (h2m : 2 * m < p) (q : ℤ × ℤ) (hq : bdry p m q) :
    sgn m (horizPartner p m q) * (horizPartner p m q).1 + sgn m q * q.1 + 2 * (m : ℤ) = 0 ∨
      sgn m (horizPartner p m q) * (horizPartner p m q).1 + sgn m q * q.1 + 2 * (m : ℤ) =
        (p : ℤ) ∨
      sgn m (horizPartner p m q) * (horizPartner p m q).1 + sgn m q * q.1 + 2 * (m : ℤ) =
        -(p : ℤ) ∨
      sgn m (horizPartner p m q) * (horizPartner p m q).1 + sgn m q * q.1 + 2 * (m : ℤ) =
        2 * (p : ℤ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hq
  have hHP2 : (horizPartner p m q).2 = q.2 := rfl
  set lo : ℤ := max (m : ℤ) (2 * q.2 - m) with hlo_def
  set hi : ℤ := min ((p : ℤ) - m) (2 * q.2 + m) with hhi_def
  have hlo : lo = (m : ℤ) ∨ lo = 2 * q.2 - (m : ℤ) := by rw [hlo_def]; omega
  have hhi : hi = (p : ℤ) - (m : ℤ) ∨ hi = 2 * q.2 + (m : ℤ) := by rw [hhi_def]; omega
  have hlo_le : lo ≤ q.1 + q.2 := by rw [hlo_def]; omega
  have hhi_ge : q.1 + q.2 ≤ hi := by rw [hhi_def]; omega
  have hlo_ge1 : (m : ℤ) ≤ lo := by rw [hlo_def]; omega
  have hlo_ge2 : 2 * q.2 - (m : ℤ) ≤ lo := by rw [hlo_def]; omega
  have hhi_le1 : hi ≤ (p : ℤ) - (m : ℤ) := by rw [hhi_def]; omega
  have hhi_le2 : hi ≤ 2 * q.2 + (m : ℤ) := by rw [hhi_def]; omega
  have hHP1 : (horizPartner p m q).1 = lo + hi - (q.1 + q.2) - q.2 := by
    change max (m : ℤ) (2 * q.2 - m) + min ((p : ℤ) - m) (2 * q.2 + m) - (q.1 + q.2) - q.2
      = lo + hi - (q.1 + q.2) - q.2
    rw [hlo_def, hhi_def]
  have hhp : (horizPartner p m q).1 + (horizPartner p m q).2 = lo + hi - (q.1 + q.2) := by omega
  have hend : q.1 + q.2 = lo ∨ q.1 + q.2 = hi := by omega
  have hendHP : (horizPartner p m q).1 + (horizPartner p m q).2 = lo ∨
      (horizPartner p m q).1 + (horizPartner p m q).2 = hi := by omega
  by_cases hdeg : lo = hi
  · have hqeq : horizPartner p m q = q := by apply Prod.ext <;> omega
    by_cases hHPc : (horizPartner p m q).1 + (horizPartner p m q).2 = (m : ℤ) ∨
        (horizPartner p m q).1 - (horizPartner p m q).2 = (m : ℤ)
    · by_cases hqc : q.1 + q.2 = (m : ℤ) ∨ q.1 - q.2 = (m : ℤ)
      · rw [sgn_eq_neg hHPc, sgn_eq_neg hqc, hqeq]; omega
      · rw [sgn_eq_neg hHPc, sgn_eq_one hqc, hqeq]; omega
    · by_cases hqc : q.1 + q.2 = (m : ℤ) ∨ q.1 - q.2 = (m : ℤ)
      · rw [sgn_eq_one hHPc, sgn_eq_neg hqc, hqeq]; omega
      · rw [sgn_eq_one hHPc, sgn_eq_one hqc, hqeq]; omega
  · have hlt : lo < hi := lt_of_le_of_ne (le_trans hlo_le hhi_ge) hdeg
    rcases hend with hs | hs <;> rcases hendHP with ht | ht
    · exfalso; omega
    · by_cases hHPc : (horizPartner p m q).1 + (horizPartner p m q).2 = (m : ℤ) ∨
        (horizPartner p m q).1 - (horizPartner p m q).2 = (m : ℤ)
      · by_cases hqc : q.1 + q.2 = (m : ℤ) ∨ q.1 - q.2 = (m : ℤ)
        · rw [sgn_eq_neg hHPc, sgn_eq_neg hqc]; omega
        · rw [sgn_eq_neg hHPc, sgn_eq_one hqc]; omega
      · by_cases hqc : q.1 + q.2 = (m : ℤ) ∨ q.1 - q.2 = (m : ℤ)
        · rw [sgn_eq_one hHPc, sgn_eq_neg hqc]; omega
        · rw [sgn_eq_one hHPc, sgn_eq_one hqc]; omega
    · by_cases hHPc : (horizPartner p m q).1 + (horizPartner p m q).2 = (m : ℤ) ∨
        (horizPartner p m q).1 - (horizPartner p m q).2 = (m : ℤ)
      · by_cases hqc : q.1 + q.2 = (m : ℤ) ∨ q.1 - q.2 = (m : ℤ)
        · rw [sgn_eq_neg hHPc, sgn_eq_neg hqc]; omega
        · rw [sgn_eq_neg hHPc, sgn_eq_one hqc]; omega
      · by_cases hqc : q.1 + q.2 = (m : ℤ) ∨ q.1 - q.2 = (m : ℤ)
        · rw [sgn_eq_one hHPc, sgn_eq_neg hqc]; omega
        · rw [sgn_eq_one hHPc, sgn_eq_one hqc]; omega
    · exfalso; omega

/-- The signed coordinate of a boundary point, in `ZMod p`: the sign times the first
coordinate, taken modulo `p`. -/
private def kval (p m : ℕ) (q : ℤ × ℤ) : ZMod p := ((sgn m q * q.1 : ℤ) : ZMod p)

/-- The vertical partner negates the signed coordinate. -/
private theorem kval_vertPartner (p m : ℕ) (hp4 : p % 4 = 1) (hm : 0 < m) (h2m : 2 * m < p)
    (q : ℤ × ℤ) (hq : bdry p m q) :
    kval p m (vertPartner p m q) = -kval p m q := by
  change ((sgn m (vertPartner p m q) * (vertPartner p m q).1 : ℤ) : ZMod p) =
    -((sgn m q * q.1 : ℤ) : ZMod p)
  rw [sgn_vertPartner p m hp4 hm h2m q hq]
  simp

/-- The horizontal partner shifts the signed coordinate by `-2m` modulo `p`. -/
private theorem kval_horizPartner (p m : ℕ) (hp4 : p % 4 = 1) (hm : 0 < m) (h2m : 2 * m < p)
    (q : ℤ × ℤ) (hq : bdry p m q) :
    kval p m (horizPartner p m q) = -kval p m q - 2 * (m : ZMod p) := by
  have hdisj := horizPartner_sgn_sum p m hp4 hm h2m q hq
  have hA0 : ((sgn m (horizPartner p m q) * (horizPartner p m q).1 + sgn m q * q.1 +
      2 * (m : ℤ) : ℤ) : ZMod p) = 0 := by
    rcases hdisj with h | h | h | h <;> rw [h] <;> simp
  change ((sgn m (horizPartner p m q) * (horizPartner p m q).1 : ℤ) : ZMod p) =
    -((sgn m q * q.1 : ℤ) : ZMod p) - 2 * (m : ZMod p)
  push_cast at hA0 ⊢
  linear_combination hA0

/-- Two billiard steps shift the signed coordinate by `2m` modulo `p`. -/
private theorem kval_twoStep (p m : ℕ) (hp4 : p % 4 = 1) (hm : 0 < m) (h2m : 2 * m < p)
    (q : ℤ × ℤ) (hq : bdry p m q) :
    kval p m (vertPartner p m (horizPartner p m q)) = kval p m q + 2 * (m : ZMod p) := by
  rw [kval_vertPartner p m hp4 hm h2m _ (horizPartner_bdry p m q hq),
    kval_horizPartner p m hp4 hm h2m q hq]
  ring

/-- The billiard path: start at `(0, m)`, then alternate horizontal and vertical
partners. -/
private def billiardPath (p m : ℕ) : ℕ → ℤ × ℤ
  | 0 => (0, (m : ℤ))
  | n + 1 => if Even n then horizPartner p m (billiardPath p m n)
      else vertPartner p m (billiardPath p m n)

/-- The first point of the billiard path. -/
private theorem billiardPath_zero (p m : ℕ) : billiardPath p m 0 = (0, (m : ℤ)) := rfl

/-- The successor step of the billiard path. -/
private theorem billiardPath_succ (p m : ℕ) (n : ℕ) :
    billiardPath p m (n + 1) = if Even n then horizPartner p m (billiardPath p m n)
      else vertPartner p m (billiardPath p m n) := rfl

/-- Every point of the billiard path is a boundary point. -/
private theorem billiardPath_bdry (p m : ℕ) (hm : 0 < m) (h2m : 2 * m < p) (n : ℕ) :
    bdry p m (billiardPath p m n) := by
  induction n with
  | zero =>
    rw [billiardPath_zero]
    unfold bdry
    refine ⟨by omega, by omega, by omega, by omega, Or.inl (by omega)⟩
  | succ n ih =>
    rw [billiardPath_succ]
    split_ifs with hEv
    · exact horizPartner_bdry p m _ ih
    · exact vertPartner_bdry p m _ ih

/-- The signed coordinate of the even points of the billiard path. -/
private theorem kval_billiardPath_even (p m : ℕ) (hp4 : p % 4 = 1) (hm : 0 < m)
    (h2m : 2 * m < p) (j : ℕ) :
    kval p m (billiardPath p m (2 * j)) = (j : ZMod p) * (2 * (m : ZMod p)) := by
  induction j with
  | zero =>
    simp [billiardPath_zero, kval]
  | succ j ih =>
    have h1 : billiardPath p m (2 * (j + 1)) =
        vertPartner p m (horizPartner p m (billiardPath p m (2 * j))) := by
      rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, billiardPath_succ]
      have hne : ¬ Even (2 * j + 1) := by
        intro hEv; obtain ⟨k, hk⟩ := hEv; omega
      rw [ite_eq_right hne, billiardPath_succ]
      have hev : Even (2 * j) := ⟨j, by ring⟩
      rw [ite_eq_left hev]
    rw [h1, kval_twoStep p m hp4 hm h2m _ (billiardPath_bdry p m hm h2m (2 * j)), ih]
    push_cast
    ring

/-- The signed coordinate of the odd points of the billiard path. -/
private theorem kval_billiardPath_odd (p m : ℕ) (hp4 : p % 4 = 1) (hm : 0 < m)
    (h2m : 2 * m < p) (j : ℕ) :
    kval p m (billiardPath p m (2 * j + 1)) =
      -((j + 1 : ℕ) : ZMod p) * (2 * (m : ZMod p)) := by
  have h1 : billiardPath p m (2 * j + 1) =
      vertPartner p m (billiardPath p m (2 * (j + 1))) := by
    have h2 : billiardPath p m (2 * (j + 1)) =
        vertPartner p m (billiardPath p m (2 * j + 1)) := by
      rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, billiardPath_succ]
      have hne : ¬ Even (2 * j + 1) := by
        intro hEv; obtain ⟨k, hk⟩ := hEv; omega
      rw [ite_eq_right hne]
    have h3 : vertPartner p m (billiardPath p m (2 * (j + 1))) =
        billiardPath p m (2 * j + 1) := by
      rw [h2, vertPartner_involutive]
    exact h3.symm
  rw [h1, kval_vertPartner p m hp4 hm h2m _ (billiardPath_bdry p m hm h2m (2 * (j + 1))),
    kval_billiardPath_even p m hp4 hm h2m (j + 1)]
  push_cast
  ring

/-- If two integers are equal in `ZMod p` and their difference is strictly between `-p`
and `p`, then they are equal. -/
private theorem int_eq_of_zmod_eq {p : ℕ} {a b : ℤ} (h : (a : ZMod p) = (b : ZMod p))
    (hb : -(p : ℤ) < a - b) (hb2 : a - b < (p : ℤ)) : a = b := by
  have hmod : a ≡ b [ZMOD (p : ℤ)] := (ZMod.intCast_eq_intCast_iff a b p).mp h
  have hdvd : (p : ℤ) ∣ (b - a) := (Int.modEq_iff_dvd).mp hmod
  have hna : (b - a).natAbs < ((p : ℤ)).natAbs := by
    rw [Int.natAbs_natCast]
    omega
  have h0 : b - a = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hna
  omega

/-- An integer whose cast to `ZMod p` is zero and whose absolute value is below `p`
is zero. -/
private theorem int_eq_zero_of_zmod_eq_zero {p : ℕ} {a : ℤ} (h : (a : ZMod p) = 0)
    (hb : a.natAbs < p) : a = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h (by simpa using hb)

/-- Bounds on the first coordinate of a boundary point. -/
private theorem bdry_first_bounds (p m : ℕ) (hp4 : p % 4 = 1) (q : ℤ × ℤ) (hq : bdry p m q) :
    0 ≤ q.1 ∧ 2 * q.1 ≤ (p : ℤ) - 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hq
  constructor <;> omega

/-- Bounds on the second coordinate of a boundary point. -/
private theorem bdry_second_bounds (p m : ℕ) (hp4 : p % 4 = 1) (q : ℤ × ℤ) (hq : bdry p m q) :
    0 ≤ q.2 ∧ 2 * q.2 ≤ (p : ℤ) - 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hq
  constructor <;> omega

/-- The sign of a boundary point is `-1` or `1`. -/
private theorem sgn_cases (m : ℕ) (r : ℤ × ℤ) : sgn m r = -1 ∨ sgn m r = 1 := by
  by_cases h : r.1 + r.2 = (m : ℤ) ∨ r.1 - r.2 = (m : ℤ)
  · exact Or.inl (sgn_eq_neg h)
  · exact Or.inr (sgn_eq_one h)

/-- The signed coordinate of the starting point is zero. -/
private theorem kval_start (p m : ℕ) : kval p m (0, (m : ℤ)) = 0 := by
  simp [kval]

/-- The signed coordinate of the final point is `-m`. -/
private theorem kval_final (p m : ℕ) : kval p m ((m : ℤ), 0) = -(m : ZMod p) := by
  change ((sgn m ((m : ℤ), 0) * (m : ℤ) : ℤ) : ZMod p) = -(m : ZMod p)
  rw [sgn_eq_neg (Or.inl (by simp))]
  push_cast
  ring

/-- A boundary point whose signed coordinate is `-m` is the final point `(m, 0)`. -/
private theorem eq_of_kval_eq_neg (p m : ℕ) (hp4 : p % 4 = 1) (hm : 0 < m) (_h2m : 2 * m < p)
    (q : ℤ × ℤ) (hq : bdry p m q) (hqk : kval p m q = -(m : ZMod p)) :
    q = ((m : ℤ), 0) := by
  have hb1 := (bdry_first_bounds p m hp4 q hq).1
  have hb2 := (bdry_first_bounds p m hp4 q hq).2
  obtain ⟨hq1, hq2, hq3, hq4, hq5⟩ := hq
  have hcast : ((sgn m q * q.1 : ℤ) : ZMod p) = ((-(m : ℤ) : ℤ) : ZMod p) := by
    change kval p m q = ((-(m : ℤ) : ℤ) : ZMod p)
    rw [hqk]
    push_cast
    ring
  have heq : sgn m q * q.1 = -(m : ℤ) := by
    rcases sgn_cases m q with hs | hs <;> rw [hs] <;> rw [hs] at hcast <;>
      apply int_eq_of_zmod_eq hcast <;> omega
  have hsgn : sgn m q = -1 := by
    rcases sgn_cases m q with hs | hs
    · exact hs
    · exfalso; rw [hs] at heq; omega
  have hx : q.1 = (m : ℤ) := by rw [hsgn] at heq; omega
  have hcond : q.1 + q.2 = (m : ℤ) ∨ q.1 - q.2 = (m : ℤ) := by
    by_contra h
    have h1 := sgn_eq_one h
    omega
  apply Prod.ext hx
  rcases hcond with h | h <;> omega

/-- The horizontal partner of the final point is itself. -/
private theorem horizPartner_self_final (p m : ℕ) (hm : 0 < m) (h2m : 2 * m < p) :
    horizPartner p m ((m : ℤ), 0) = ((m : ℤ), 0) := by
  apply Prod.ext
  · change max (m : ℤ) (2 * (0 : ℤ) - m) + min ((p : ℤ) - m) (2 * (0 : ℤ) + m) -
      ((m : ℤ) + 0) - 0 = (m : ℤ)
    omega
  · rfl

/-- A natural number below a prime is nonzero in `ZMod p`. -/
private theorem cast_ne_zero_of_lt (p : ℕ) (_hp : p.Prime) (a : ℕ) (ha0 : 0 < a) (hap : a < p) :
    (a : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => absurd (Nat.le_of_dvd ha0 h) (by omega)

/-- The step `2m` is nonzero in `ZMod p`. -/
private theorem two_mul_cast_ne_zero (p m : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hm : 0 < m) (h2m : 2 * m < p) : (2 : ZMod p) * (m : ZMod p) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 < p := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · have h1 := hp.one_lt
      omega
  apply mul_ne_zero
  · simpa using cast_ne_zero_of_lt p hp 2 (by omega) hp2
  · exact cast_ne_zero_of_lt p hp m hm (by omega)

/-- The horizontal partner of the final point is itself, via the vertical
involution applied to the final step. -/
private theorem billiardPath_ne_final_even (p m : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hm : 0 < m) (h2m : 2 * m < p) (j : ℕ) (hj : 2 * j < p - 1) :
    billiardPath p m (2 * j) ≠ ((m : ℤ), 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hEq
  have hK := kval_billiardPath_even p m hp4 hm h2m j
  rw [hEq, kval_final] at hK
  have h0 : (((2 * j + 1 : ℕ) : ZMod p) * (m : ZMod p)) = 0 := by
    push_cast
    linear_combination -hK
  rcases mul_eq_zero.mp h0 with h' | h'
  · rw [ZMod.natCast_eq_zero_iff] at h'
    have hle := Nat.le_of_dvd (by omega : 0 < 2 * j + 1) h'
    omega
  · exact cast_ne_zero_of_lt p hp m hm (by omega) h'

/-- No point of the billiard path before the last is the final point. -/
private theorem billiardPath_ne_final (p m : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hm : 0 < m) (h2m : 2 * m < p) (i : ℕ) (hi : i < p - 1) :
    billiardPath p m i ≠ ((m : ℤ), 0) := by
  rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hi2 : i = 2 * j := by omega
    rw [hi2]
    exact billiardPath_ne_final_even p m hp hp4 hm h2m j (by omega)
  · have hi2 : i = 2 * j + 1 := by omega
    rw [hi2]
    intro hEq
    have hstep : billiardPath p m (2 * j + 1) =
        horizPartner p m (billiardPath p m (2 * j)) := by
      rw [billiardPath_succ, ite_eq_left ⟨j, by ring⟩]
    have hprev : billiardPath p m (2 * j) = ((m : ℤ), 0) := by
      have h1 : horizPartner p m (billiardPath p m (2 * j + 1)) =
          billiardPath p m (2 * j) := by
        rw [hstep, horizPartner_involutive]
      rw [hEq, horizPartner_self_final p m hm h2m] at h1
      exact h1.symm
    exact billiardPath_ne_final_even p m hp hp4 hm h2m j (by omega) hprev

/-- A positive even point of the billiard path is not the starting point. -/
private theorem billiardPath_ne_start_even (p m : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hm : 0 < m) (h2m : 2 * m < p) (j : ℕ) (hj : 0 < j) (hj2 : 2 * j < p - 1) :
    billiardPath p m (2 * j) ≠ (0, (m : ℤ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hEq
  have hK := kval_billiardPath_even p m hp4 hm h2m j
  rw [hEq, kval_start] at hK
  have h0 : (j : ZMod p) = 0 := by
    rcases mul_eq_zero.mp hK.symm with h' | h'
    · exact h'
    · exact absurd h' (two_mul_cast_ne_zero p m hp hp4 hm h2m)
  rw [ZMod.natCast_eq_zero_iff] at h0
  have hle := Nat.le_of_dvd hj h0
  omega

/-- No positive point of the billiard path before the last is the starting point. -/
private theorem billiardPath_ne_start (p m : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hm : 0 < m) (h2m : 2 * m < p) (i : ℕ) (hi0 : 0 < i) (hi : i < p - 1) :
    billiardPath p m i ≠ (0, (m : ℤ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hi2 : i = 2 * j := by omega
    rw [hi2]
    exact billiardPath_ne_start_even p m hp hp4 hm h2m j (by omega) (by omega)
  · have hi2 : i = 2 * j + 1 := by omega
    rw [hi2]
    intro hEq
    have hstep : billiardPath p m (2 * j + 1) =
        horizPartner p m (billiardPath p m (2 * j)) := by
      rw [billiardPath_succ, ite_eq_left ⟨j, by ring⟩]
    have hbd : bdry p m (0, (m : ℤ)) := by
      rw [← billiardPath_zero]
      exact billiardPath_bdry p m hm h2m 0
    have hprevK : kval p m (billiardPath p m (2 * j)) = -(2 * (m : ZMod p)) := by
      have h1 : horizPartner p m (billiardPath p m (2 * j + 1)) =
          billiardPath p m (2 * j) := by
        rw [hstep, horizPartner_involutive]
      have h2 : billiardPath p m (2 * j) = horizPartner p m (0, (m : ℤ)) := by
        rw [← h1, hEq]
      rw [h2, kval_horizPartner p m hp4 hm h2m _ hbd, kval_start]
      ring
    have hK := kval_billiardPath_even p m hp4 hm h2m j
    rw [hprevK] at hK
    have h0 : (((j + 1 : ℕ) : ZMod p) * (2 * (m : ZMod p))) = 0 := by
      push_cast
      linear_combination -hK
    rcases mul_eq_zero.mp h0 with h' | h'
    · rw [ZMod.natCast_eq_zero_iff] at h'
      have hle := Nat.le_of_dvd (by omega : 0 < j + 1) h'
      omega
    · exact absurd h' (two_mul_cast_ne_zero p m hp hp4 hm h2m)

/-- The last point of the billiard path is the final point. -/
private theorem billiardPath_final (p m : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hm : 0 < m) (h2m : 2 * m < p) :
    billiardPath p m (p - 1) = ((m : ℤ), 0) := by
  obtain ⟨t, ht⟩ := hp.odd_of_ne_two (by omega)
  have hpj : p - 1 = 2 * t := by omega
  rw [hpj]
  apply eq_of_kval_eq_neg p m hp4 hm h2m _ (billiardPath_bdry p m hm h2m (2 * t))
  rw [kval_billiardPath_even p m hp4 hm h2m t]
  have h2t : ((2 * t : ℕ) : ZMod p) = -1 := by
    rw [show (2 * t : ℕ) = p - 1 by omega, Nat.cast_sub (by omega : 1 ≤ p)]
    simp
  have hcast : (t : ZMod p) * (2 * (m : ZMod p)) =
      ((2 * t : ℕ) : ZMod p) * (m : ZMod p) := by
    push_cast
    ring
  rw [hcast, h2t]
  ring

/-- Determinism: any sequence satisfying the billiard step conditions agrees with
the billiard path up to index `p - 1`. -/
private theorem eq_billiardPath_of (p m : ℕ) (_hp4 : p % 4 = 1) (hm : 0 < m)
    (h2m : 2 * m < p) (Q : ℕ → ℤ × ℤ) (h0 : Q 0 = (0, (m : ℤ)))
    (hstep : ∀ i < p - 1, bdry p m (Q (i + 1)) ∧ Q (i + 1) ≠ Q i ∧
      (if Even i then (Q (i + 1)).2 = (Q i).2 else (Q (i + 1)).1 = (Q i).1)) :
    ∀ i ≤ p - 1, Q i = billiardPath p m i := by
  intro i
  induction i with
  | zero => intro _; rw [h0, billiardPath_zero]
  | succ i ih =>
    intro hi
    have hi' : i ≤ p - 1 := by omega
    have hQi := ih hi'
    obtain ⟨hbd, hne, hcoord⟩ := hstep i (by omega)
    have hQbd : bdry p m (Q i) := by rw [hQi]; exact billiardPath_bdry p m hm h2m i
    rw [billiardPath_succ]
    by_cases hEv : Even i
    · have hcoord' : (Q (i + 1)).2 = (Q i).2 := by
        rw [ite_eq_left hEv] at hcoord; exact hcoord
      rw [ite_eq_left hEv, ← hQi]
      exact horizPartner_unique p m (Q i) (Q (i + 1)) hQbd hbd hcoord' hne
    · have hcoord' : (Q (i + 1)).1 = (Q i).1 := by
        rw [ite_eq_right hEv] at hcoord; exact hcoord
      rw [ite_eq_right hEv, ← hQi]
      exact vertPartner_unique p m (Q i) (Q (i + 1)) hQbd hbd hcoord' hne

/-- The billiard path is symmetric under swapping coordinates. -/
private theorem billiardPath_symm (p m : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hm : 0 < m) (h2m : 2 * m < p) (i : ℕ) (hi : i ≤ p - 1) :
    billiardPath p m (p - 1 - i) = (billiardPath p m i).swap := by
  obtain ⟨t, ht⟩ := hp.odd_of_ne_two (by omega)
  have hdet := eq_billiardPath_of p m hp4 hm h2m
    (fun n => (billiardPath p m (p - 1 - n)).swap)
    (by
      show (billiardPath p m (p - 1 - 0)).swap = (0, (m : ℤ))
      rw [show p - 1 - 0 = p - 1 by omega, billiardPath_final p m hp hp4 hm h2m]
      rfl)
    (by
      intro n hn
      show bdry p m (billiardPath p m (p - 1 - (n + 1))).swap ∧
        (billiardPath p m (p - 1 - (n + 1))).swap ≠
          (billiardPath p m (p - 1 - n)).swap ∧
        (if Even n then ((billiardPath p m (p - 1 - (n + 1))).swap).2 =
          ((billiardPath p m (p - 1 - n)).swap).2
        else ((billiardPath p m (p - 1 - (n + 1))).swap).1 =
          ((billiardPath p m (p - 1 - n)).swap).1)
      have e1 : p - 1 - (n + 1) = p - 2 - n := by omega
      have e2 : p - 1 - n = (p - 2 - n) + 1 := by omega
      rw [e1, e2]
      have hbd : bdry p m (billiardPath p m (p - 2 - n)) :=
        billiardPath_bdry p m hm h2m (p - 2 - n)
      have hbd' : bdry p m (billiardPath p m ((p - 2 - n) + 1)) :=
        billiardPath_bdry p m hm h2m ((p - 2 - n) + 1)
      have hne : billiardPath p m ((p - 2 - n) + 1) ≠ billiardPath p m (p - 2 - n) := by
        rw [billiardPath_succ]
        by_cases hEv : Even (p - 2 - n)
        · rw [ite_eq_left hEv]
          exact horizPartner_ne p m hp4 hm h2m _ hbd
            (billiardPath_ne_final p m hp hp4 hm h2m (p - 2 - n) (by omega))
        · rw [ite_eq_right hEv]
          exact vertPartner_ne p m hp4 hm h2m _ hbd
            (billiardPath_ne_start p m hp hp4 hm h2m (p - 2 - n)
              (by
                have h0 : p - 2 - n ≠ 0 := by
                  intro h0
                  rw [h0] at hEv
                  exact hEv ⟨0, rfl⟩
                omega) (by omega))
      have hstep : billiardPath p m ((p - 2 - n) + 1) =
          if Even (p - 2 - n) then horizPartner p m (billiardPath p m (p - 2 - n))
          else vertPartner p m (billiardPath p m (p - 2 - n)) := billiardPath_succ _ _ _
      have hpar : Even (p - 2 - n) ↔ ¬ Even n := by
        simp only [Nat.even_iff]
        omega
      refine ⟨(bdry_swap p m _).mpr hbd, ?_, ?_⟩
      · intro hEq
        apply hne
        have := Prod.swap_injective hEq
        exact this.symm
      · by_cases hEv : Even n
        · have hnj : ¬ Even (p - 2 - n) := fun h => (hpar.mp h) hEv
          rw [ite_eq_left hEv, Prod.swap, Prod.swap]
          change (billiardPath p m (p - 2 - n)).1 =
            (billiardPath p m ((p - 2 - n) + 1)).1
          rw [hstep, ite_eq_right hnj]
          rfl
        · have hj : Even (p - 2 - n) := hpar.mpr hEv
          rw [ite_eq_right hEv, Prod.swap, Prod.swap]
          change (billiardPath p m (p - 2 - n)).2 =
            (billiardPath p m ((p - 2 - n) + 1)).2
          rw [hstep, ite_eq_left hj]
          rfl)
  have h := hdet (p - 1 - i) (by omega)
  change (billiardPath p m (p - 1 - (p - 1 - i))).swap = billiardPath p m (p - 1 - i) at h
  rw [show p - 1 - (p - 1 - i) = i by omega] at h
  exact h.symm

/-- A boundary point whose signed coordinate is zero is the starting point. -/
private theorem eq_start_of_kval_eq_zero (p m : ℕ) (hp4 : p % 4 = 1) (_hm : 0 < m)
    (_h2m : 2 * m < p) (q : ℤ × ℤ) (hq : bdry p m q) (hqk : kval p m q = 0) :
    q = (0, (m : ℤ)) := by
  have hcast0 : ((sgn m q * q.1 : ℤ) : ZMod p) = 0 := hqk
  have hb1 := (bdry_first_bounds p m hp4 q hq).1
  have hb2 := (bdry_first_bounds p m hp4 q hq).2
  have hna : (sgn m q * q.1).natAbs < p := by
    have hsgn_abs : ((sgn m q * q.1).natAbs : ℤ) = (q.1.natAbs : ℤ) := by
      rcases sgn_cases m q with hs | hs <;> rw [hs] <;> simp
    have hlt : (q.1.natAbs : ℤ) < (p : ℤ) := by
      rw [Int.natAbs_of_nonneg hb1]
      omega
    have hlt' : ((sgn m q * q.1).natAbs : ℤ) < ((p : ℕ) : ℤ) := by
      rw [hsgn_abs]
      exact_mod_cast hlt
    exact_mod_cast hlt'
  have hprod0 := int_eq_zero_of_zmod_eq_zero hcast0 hna
  have hx0 : q.1 = 0 := by
    rcases sgn_cases m q with hs | hs <;> rw [hs] at hprod0 <;> omega
  obtain ⟨hq1, hq2, hq3, hq4, hq5⟩ := hq
  apply Prod.ext hx0
  omega

/-- Two boundary points with the same signed coordinate coincide, unless the first
is the starting point. -/
private theorem eq_of_kval_eq (p m : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (hm : 0 < m)
    (h2m : 2 * m < p) (q r : ℤ × ℤ) (hq : bdry p m q) (hr : bdry p m r)
    (hk : kval p m q = kval p m r) (hqA : q ≠ (0, (m : ℤ))) : q = r := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hq1, hq2, hq3, hq4, hq5⟩ := hq
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hr
  have hbq1 : 0 ≤ q.1 := by omega
  have hbq2 : 2 * q.1 ≤ (p : ℤ) - 1 := by omega
  have hbr1 : 0 ≤ r.1 := by omega
  have hbr2 : 2 * r.1 ≤ (p : ℤ) - 1 := by omega
  have hcast : ((sgn m q * q.1 : ℤ) : ZMod p) = ((sgn m r * r.1 : ℤ) : ZMod p) := hk
  have heq : sgn m q * q.1 = sgn m r * r.1 := by
    rcases sgn_cases m q with hs | hs <;> rcases sgn_cases m r with hs' | hs' <;>
      rw [hs, hs'] <;> rw [hs, hs'] at hcast <;>
      apply int_eq_of_zmod_eq hcast <;> omega
  have hcases : (q.1 = r.1) ∨ (q.1 = 0 ∧ r.1 = 0) := by
    rcases sgn_cases m q with hs | hs <;> rcases sgn_cases m r with hs' | hs' <;>
      rw [hs, hs'] at heq <;> omega
  rcases hcases with h | ⟨h0q, h0r⟩
  · rcases vertPartner_or_eq p m q r ⟨hq1, hq2, hq3, hq4, hq5⟩
      ⟨hr1, hr2, hr3, hr4, hr5⟩ h.symm with h' | h'
    · exact h'.symm
    · exfalso
      have hkv : kval p m r = -kval p m q := by
        rw [h']
        exact kval_vertPartner p m hp4 hm h2m q ⟨hq1, hq2, hq3, hq4, hq5⟩
      have h2ne : (2 : ZMod p) ≠ 0 := by
        have hp2 : 2 < p := by
          rcases hp.eq_two_or_odd with hh | hh
          · omega
          · have h1 := hp.one_lt
            omega
        simpa using cast_ne_zero_of_lt p hp 2 (by omega) hp2
      have h2 : (2 : ZMod p) * kval p m q = 0 := by linear_combination hk + hkv
      rcases mul_eq_zero.mp h2 with h2' | h2'
      · exact absurd h2' h2ne
      · have h0 : kval p m q = 0 := h2'
        exact hqA (eq_start_of_kval_eq_zero p m hp4 hm h2m q
          ⟨hq1, hq2, hq3, hq4, hq5⟩ h0)
  · exfalso
    apply hqA
    apply Prod.ext h0q
    omega

/-- The signed index of a step: `j` for step `2 * j` and `-(j + 1)` for step
`2 * j + 1`. -/
private def eIndex (i : ℕ) : ℤ := if Even i then (i / 2 : ℤ) else -(((i + 1) / 2 : ℕ) : ℤ)

/-- The signed index is bounded by half the step number. -/
private theorem eIndex_range (i : ℕ) :
    -(((i + 1) / 2 : ℕ) : ℤ) ≤ eIndex i ∧ eIndex i ≤ (((i + 1) / 2 : ℕ) : ℤ) := by
  unfold eIndex
  split_ifs with hEv
  · have h0 : (0 : ℤ) ≤ ((i / 2 : ℕ) : ℤ) := by positivity
    have hle : ((i / 2 : ℕ) : ℤ) ≤ (((i + 1) / 2 : ℕ) : ℤ) := by
      exact_mod_cast Nat.div_le_div_right (by omega : i ≤ i + 1)
    constructor <;> omega
  · have h0 : (0 : ℤ) ≤ (((i + 1) / 2 : ℕ) : ℤ) := by positivity
    constructor <;> omega

/-- The signed coordinate of every point of the billiard path. -/
private theorem kval_billiardPath (p m : ℕ) (hp4 : p % 4 = 1) (hm : 0 < m)
    (h2m : 2 * m < p) (i : ℕ) :
    kval p m (billiardPath p m i) =
      (2 * (m : ZMod p)) * ((eIndex i : ℤ) : ZMod p) := by
  rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hi2 : i = 2 * j := by omega
    have he : eIndex i = (j : ℤ) := by
      unfold eIndex
      rw [ite_eq_left ⟨j, by omega⟩]
      norm_cast
      omega
    rw [he, hi2, kval_billiardPath_even p m hp4 hm h2m j]
    push_cast
    ring
  · have hi2 : i = 2 * j + 1 := by omega
    have he : eIndex i = -((j + 1 : ℕ) : ℤ) := by
      unfold eIndex
      rw [ite_eq_right (by intro hEv; obtain ⟨k, hk⟩ := hEv; omega)]
      congr 1
      norm_cast
      omega
    rw [he, hi2, kval_billiardPath_odd p m hp4 hm h2m j]
    push_cast
    ring

/-- The billiard path is injective on indices up to `p - 1`. -/
private theorem billiardPath_injective (p m : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hm : 0 < m) (h2m : 2 * m < p) {i i' : ℕ} (hi : i ≤ p - 1) (hi' : i' ≤ p - 1)
    (h : billiardPath p m i = billiardPath p m i') : i = i' := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := hp.odd_of_ne_two (by omega)
  have hK : kval p m (billiardPath p m i) = kval p m (billiardPath p m i') := by rw [h]
  rw [kval_billiardPath p m hp4 hm h2m i, kval_billiardPath p m hp4 hm h2m i'] at hK
  have h2m0 := two_mul_cast_ne_zero p m hp hp4 hm h2m
  have he : ((eIndex i : ℤ) : ZMod p) = ((eIndex i' : ℤ) : ZMod p) :=
    mul_left_cancel₀ h2m0 hK
  have hei : eIndex i = eIndex i' := by
    apply int_eq_of_zmod_eq he
    all_goals
      have hr1 := eIndex_range i
      have hr2 := eIndex_range i'
      have h1i : i + 1 ≤ 2 * t + 1 := by omega
      have h1i' : i' + 1 ≤ 2 * t + 1 := by omega
      have ht2 : ((i + 1) / 2 : ℕ) ≤ t := by omega
      have ht2' : ((i' + 1) / 2 : ℕ) ≤ t := by omega
      omega
  rcases Nat.even_or_odd i with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
    rcases Nat.even_or_odd i' with ⟨b, hb⟩ | ⟨b, hb⟩
  · have heiA : eIndex i = (a : ℤ) := by
      unfold eIndex
      rw [ite_eq_left ⟨a, ha⟩]
      norm_cast
      omega
    have heiB : eIndex i' = (b : ℤ) := by
      unfold eIndex
      rw [ite_eq_left ⟨b, hb⟩]
      norm_cast
      omega
    rw [heiA, heiB] at hei
    omega
  · have heiA : eIndex i = (a : ℤ) := by
      unfold eIndex
      rw [ite_eq_left ⟨a, ha⟩]
      norm_cast
      omega
    have heiB : eIndex i' = -((b + 1 : ℕ) : ℤ) := by
      unfold eIndex
      rw [ite_eq_right (by intro hEv; obtain ⟨k, hk⟩ := hEv; omega)]
      congr 1
      norm_cast
      omega
    rw [heiA, heiB] at hei
    omega
  · have heiA : eIndex i = -((a + 1 : ℕ) : ℤ) := by
      unfold eIndex
      rw [ite_eq_right (by intro hEv; obtain ⟨k, hk⟩ := hEv; omega)]
      congr 1
      norm_cast
      omega
    have heiB : eIndex i' = (b : ℤ) := by
      unfold eIndex
      rw [ite_eq_left ⟨b, hb⟩]
      norm_cast
      omega
    rw [heiA, heiB] at hei
    omega
  · have heiA : eIndex i = -((a + 1 : ℕ) : ℤ) := by
      unfold eIndex
      rw [ite_eq_right (by intro hEv; obtain ⟨k, hk⟩ := hEv; omega)]
      congr 1
      norm_cast
      omega
    have heiB : eIndex i' = -((b + 1 : ℕ) : ℤ) := by
      unfold eIndex
      rw [ite_eq_right (by intro hEv; obtain ⟨k, hk⟩ := hEv; omega)]
      congr 1
      norm_cast
      omega
    rw [heiA, heiB] at hei
    omega

/-- Every boundary point other than the two corners is visited by the billiard
path before the last index. -/
private theorem billiardPath_surj (p m : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hm : 0 < m) (h2m : 2 * m < p) (q : ℤ × ℤ) (hq : bdry p m q)
    (hqA : q ≠ (0, (m : ℤ))) (hqF : q ≠ ((m : ℤ), 0)) :
    ∃ i, 1 ≤ i ∧ i ≤ p - 2 ∧ billiardPath p m i = q := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := hp.odd_of_ne_two (by omega)
  haveI : NeZero p := ⟨by omega⟩
  set a : ZMod p := 2 * (m : ZMod p) with ha_def
  have ha0 : a ≠ 0 := two_mul_cast_ne_zero p m hp hp4 hm h2m
  set v : ZMod p := kval p m q with hv_def
  set j0 : ℕ := (v * a⁻¹).val with hj0_def
  have hj0lt : j0 < p := by rw [hj0_def]; exact ZMod.val_lt (v * a⁻¹)
  have hj0eq : ((j0 : ℕ) : ZMod p) * a = v := by
    have hval : ((j0 : ℕ) : ZMod p) = v * a⁻¹ := by
      rw [hj0_def]
      exact ZMod.natCast_zmod_val (v * a⁻¹)
    rw [hval, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
  by_cases hjle : j0 ≤ t
  · have hj0ne : j0 ≠ 0 := by
      intro h0
      rw [h0] at hj0eq
      simp at hj0eq
      exact hqA (eq_start_of_kval_eq_zero p m hp4 hm h2m q hq
        (by rw [← hv_def]; exact hj0eq.symm))
    refine ⟨2 * j0, by omega, ?_, ?_⟩
    · rcases lt_or_ge (p - 2) (2 * j0) with h | h
      · exfalso
        have hfin : billiardPath p m (2 * j0) = ((m : ℤ), 0) := by
          have h2j : 2 * j0 = p - 1 := by omega
          rw [h2j]
          exact billiardPath_final p m hp hp4 hm h2m
        have hkv : kval p m (billiardPath p m (2 * j0)) = -(m : ZMod p) := by
          rw [hfin, kval_final]
        rw [kval_billiardPath_even p m hp4 hm h2m j0] at hkv
        have hqk : kval p m q = -(m : ZMod p) := by
          rw [← hv_def, ← hj0eq]
          exact hkv
        exact hqF (eq_of_kval_eq_neg p m hp4 hm h2m q hq hqk)
      · exact h
    · apply (eq_of_kval_eq p m hp hp4 hm h2m q (billiardPath p m (2 * j0)) hq
        (billiardPath_bdry p m hm h2m (2 * j0)) ?_ hqA).symm
      rw [← hv_def, kval_billiardPath_even p m hp4 hm h2m j0]
      exact hj0eq.symm
  · have hjgt : t < j0 := by omega
    set j1 : ℕ := p - 1 - j0 with hj1_def
    have hj1lt : j1 < t := by omega
    refine ⟨2 * j1 + 1, by omega, ?_, ?_⟩
    · omega
    · apply (eq_of_kval_eq p m hp hp4 hm h2m q (billiardPath p m (2 * j1 + 1)) hq
        (billiardPath_bdry p m hm h2m (2 * j1 + 1)) ?_ hqA).symm
      rw [← hv_def, kval_billiardPath_odd p m hp4 hm h2m j1]
      have hcast : (((j1 + 1 : ℕ) : ZMod p)) = -((j0 : ℕ) : ZMod p) := by
        have hsum : j1 + 1 = p - j0 := by omega
        rw [hsum, Nat.cast_sub (by omega : j0 ≤ p)]
        simp
      rw [hcast, neg_neg]
      exact hj0eq.symm

end ArithmeticBilliardsRotatedRectangle

/-- **Arithmetic billiards in a tilted rectangle.** Let $p$ be a prime with $p \equiv 1 \pmod 4$
and let $l$ be an even natural number with $l + 3 \le p$. Put $m = l + 1$ if $2l + 5 \le p$ and
$m = p - (l + 1)$ otherwise, and let $R \subseteq \mathbb{R}^2$ be the convex hull of the four
points $(0, m)$, $(m, 0)$, $(p/2, p/2 - m)$ and $(p/2 - m, p/2)$. Let $L$ be the set of integer
points on the boundary of $R$ other than $(0, m)$ and $(m, 0)$. Call a sequence $P_0, P_1, \ldots$
of integer points a billiard path if $P_0 = (0, m)$ and, for every $i < p - 1$, the point
$P_{i+1}$ lies on the boundary of $R$, differs from $P_i$, and has the same second coordinate as
$P_i$ when $i$ is even and the same first coordinate as $P_i$ when $i$ is odd. Then a billiard
path exists, and every billiard path $P$ maps $\{1, \ldots, p - 2\}$ bijectively onto $L$,
satisfies $P_{p-1} = (m, 0)$, and satisfies $P_{p-1-i} = (y_i, x_i)$ for every $i \le p - 1$,
where $P_i = (x_i, y_i)$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Lemma 16
(`lem:billiards`). -/
public theorem arithmetic_billiards_rotated_rectangle (p l : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) (hl : Even l) (hlp : l + 3 ≤ p) :
    let m : ℕ := if 2 * l + 5 ≤ p then l + 1 else p - (l + 1)
    let c : ℝ := if 2 * l + 5 ≤ p then (p : ℝ) / 2 - (l + 1) else (l + 1 : ℝ) - p / 2
    let R : Set (ℝ × ℝ) :=
      convexHull ℝ {((0 : ℝ), (m : ℝ)), ((m : ℝ), (0 : ℝ)), ((p : ℝ) / 2, c), (c, (p : ℝ) / 2)}
    let L : Set (ℤ × ℤ) :=
      {z | ((z.1 : ℝ), (z.2 : ℝ)) ∈ frontier R} \ {((0 : ℤ), (m : ℤ)), ((m : ℤ), (0 : ℤ))}
    let IsPath : (ℕ → ℤ × ℤ) → Prop := fun P =>
      P 0 = (0, (m : ℤ)) ∧ ∀ i < p - 1,
        (((P (i + 1)).1 : ℝ), ((P (i + 1)).2 : ℝ)) ∈ frontier R ∧ P (i + 1) ≠ P i ∧
          if Even i then (P (i + 1)).2 = (P i).2 else (P (i + 1)).1 = (P i).1
    (∃ P, IsPath P) ∧ ∀ P, IsPath P →
      Set.BijOn P (Set.Icc 1 (p - 2)) L ∧ P (p - 1) = ((m : ℤ), 0) ∧
        ∀ i ≤ p - 1, P (p - 1 - i) = (P i).swap := by
  dsimp only
  have hl2 : l % 2 = 0 := Nat.even_iff.mp hl
  set m : ℕ := if 2 * l + 5 ≤ p then l + 1 else p - (l + 1) with hm_def
  set c : ℝ := if 2 * l + 5 ≤ p then (p : ℝ) / 2 - (l + 1) else (l + 1 : ℝ) - p / 2
    with hc_def
  have hm0 : 0 < m := by
    by_cases h : 2 * l + 5 ≤ p <;> simp only [hm_def, h, ite_true, ite_false] <;> omega
  have h2m : 2 * m < p := by
    by_cases h : 2 * l + 5 ≤ p <;> simp only [hm_def, h, ite_true, ite_false] <;> omega
  have hc : c = (p : ℝ) / 2 - (m : ℝ) := by
    by_cases h : 2 * l + 5 ≤ p
    · simp only [hc_def, hm_def, h, ite_true]
      push_cast
      ring
    · have hle : l + 1 ≤ p := by omega
      simp only [hc_def, hm_def, h, ite_false]
      rw [Nat.cast_sub hle]
      push_cast
      ring
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have h2mR : 2 * (m : ℝ) < (p : ℝ) := by exact_mod_cast h2m
  have hfront : ∀ q : ℤ × ℤ,
      ((q.1 : ℝ), (q.2 : ℝ)) ∈ frontier (convexHull ℝ ({((0 : ℝ), (m : ℝ)),
        ((m : ℝ), (0 : ℝ)), ((p : ℝ) / 2, c), (c, (p : ℝ) / 2)} : Set (ℝ × ℝ))) ↔
        ArithmeticBilliardsRotatedRectangle.bdry p m q :=
    fun q => ArithmeticBilliardsRotatedRectangle.mem_frontier_int_iff p m c hmR h2mR hc q
  constructor
  · refine ⟨ArithmeticBilliardsRotatedRectangle.billiardPath p m,
      ArithmeticBilliardsRotatedRectangle.billiardPath_zero p m, fun i hi => ?_⟩
    refine ⟨(hfront _).mpr
      (ArithmeticBilliardsRotatedRectangle.billiardPath_bdry p m hm0 h2m (i + 1)), ?_, ?_⟩
    · rw [ArithmeticBilliardsRotatedRectangle.billiardPath_succ]
      by_cases hEv : Even i
      · rw [ite_eq_left hEv]
        exact ArithmeticBilliardsRotatedRectangle.horizPartner_ne p m hp4 hm0 h2m _
          (ArithmeticBilliardsRotatedRectangle.billiardPath_bdry p m hm0 h2m i)
          (ArithmeticBilliardsRotatedRectangle.billiardPath_ne_final p m hp hp4 hm0 h2m i hi)
      · rw [ite_eq_right hEv]
        exact ArithmeticBilliardsRotatedRectangle.vertPartner_ne p m hp4 hm0 h2m _
          (ArithmeticBilliardsRotatedRectangle.billiardPath_bdry p m hm0 h2m i)
          (ArithmeticBilliardsRotatedRectangle.billiardPath_ne_start p m hp hp4 hm0 h2m i
            (by
              have hi0 : i ≠ 0 := by
                intro h0
                rw [h0] at hEv
                exact hEv ⟨0, rfl⟩
              omega) hi)
    · rw [ArithmeticBilliardsRotatedRectangle.billiardPath_succ]
      split_ifs with hEv <;> rfl
  · intro P hP
    obtain ⟨hP0, hPstep⟩ := hP
    have hdet : ∀ i ≤ p - 1, P i = ArithmeticBilliardsRotatedRectangle.billiardPath p m i := by
      apply ArithmeticBilliardsRotatedRectangle.eq_billiardPath_of p m hp4 hm0 h2m P hP0
      intro i hi
      obtain ⟨hfr, hne, hcoord⟩ := hPstep i hi
      exact ⟨(hfront _).mp hfr, hne, hcoord⟩
    refine ⟨?_, ?_, ?_⟩
    · have hBij : Set.BijOn (ArithmeticBilliardsRotatedRectangle.billiardPath p m)
        (Set.Icc 1 (p - 2))
        ({z : ℤ × ℤ | ((z.1 : ℝ), (z.2 : ℝ)) ∈ frontier (convexHull ℝ
          ({((0 : ℝ), (m : ℝ)), ((m : ℝ), (0 : ℝ)), ((p : ℝ) / 2, c),
            (c, (p : ℝ) / 2)} : Set (ℝ × ℝ)))} \
          {((0 : ℤ), (m : ℤ)), ((m : ℤ), (0 : ℤ))}) := by
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          simp only [Set.mem_Icc] at hx
          have hbd := ArithmeticBilliardsRotatedRectangle.billiardPath_bdry p m hm0 h2m x
          have hneA : ArithmeticBilliardsRotatedRectangle.billiardPath p m x ≠ (0, (m : ℤ)) :=
            ArithmeticBilliardsRotatedRectangle.billiardPath_ne_start p m hp hp4 hm0 h2m x
              (by omega) (by omega)
          have hneF : ArithmeticBilliardsRotatedRectangle.billiardPath p m x ≠ ((m : ℤ), 0) :=
            ArithmeticBilliardsRotatedRectangle.billiardPath_ne_final p m hp hp4 hm0 h2m x
              (by omega)
          simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨(hfront _).mpr hbd, hneA, hneF⟩
        · intro x hx y hy hxy
          simp only [Set.mem_Icc] at hx hy
          exact ArithmeticBilliardsRotatedRectangle.billiardPath_injective p m hp hp4 hm0 h2m
            (by omega) (by omega) hxy
        · intro q hq
          simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hq
          obtain ⟨hfr, hneA, hneF⟩ := hq
          have hbd := (hfront q).mp hfr
          obtain ⟨i, hi1, hi2, hiq⟩ :=
            ArithmeticBilliardsRotatedRectangle.billiardPath_surj p m hp hp4 hm0 h2m q hbd
              hneA hneF
          exact ⟨i, Set.mem_Icc.mpr ⟨hi1, hi2⟩, hiq⟩
      exact Set.BijOn.congr hBij (fun x hx => by
        simp only [Set.mem_Icc] at hx
        exact (hdet x (by omega)).symm)
    · rw [hdet (p - 1) le_rfl,
        ArithmeticBilliardsRotatedRectangle.billiardPath_final p m hp hp4 hm0 h2m]
    · intro i hi
      rw [hdet (p - 1 - i) (by omega), hdet i hi,
        ArithmeticBilliardsRotatedRectangle.billiardPath_symm p m hp hp4 hm0 h2m i hi]

end

end MetaMathlibExt
