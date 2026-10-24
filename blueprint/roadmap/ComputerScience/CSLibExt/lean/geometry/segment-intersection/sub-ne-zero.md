---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Geometry.Straddles.sub_ne_zero
---

# Sub ne zero

CLRS's use of `ON-SEGMENT`: a point collinear with `p` and `q` and inside their bounding box
lies on the segment. -/
theorem mem_segment_of_direction_eq_zero {p q r : 𝕜 × 𝕜} (hd : direction p q r = 0)
    (hb : onSegment p q r = true) : r ∈ segment 𝕜 p q := by
  simp only [onSegment, decide_eq_true_eq] at hb
  obtain ⟨hx1, hx2, hy1, hy2⟩ := hb
  simp only [direction, cross, Prod.fst_sub, Prod.snd_sub] at hd
  rcases lt_trichotomy p.1 q.1 with hx | hx | hx
  · -- parameter from the x coordinate
    rw [min_eq_left hx.le] at hx1
    rw [max_eq_right hx.le] at hx2
    have hv : q.1 - p.1 ≠ 0 := sub_ne_zero.2 hx.ne'
    refine mem_segment_of_param ((r.1 - p.1) / (q.1 - p.1))
      (div_nonneg (by linarith) (by linarith)) ((div_le_one (by linarith)).2 (by linarith))
      (by rw [div_mul_cancel₀ _ hv]; ring) ?_
    have : r.2 - p.2 = (r.1 - p.1) / (q.1 - p.1) * (q.2 - p.2) := by
      rw [div_mul_eq_mul_div, eq_div_iff hv]
      linear_combination (-1 : 𝕜) * hd
    linarith
  · rcases lt_trichotomy p.2 q.2 with hy | hy | hy
    · rw [min_eq_left hy.le] at hy1
      rw [max_eq_right hy.le] at hy2
      have hv : q.2 - p.2 ≠ 0 := sub_ne_zero.2 hy.ne'
      have hr1 : r.1 = p.1 := by
        rw [← hx, min_self] at hx1; rw [← hx, max_self] at hx2; linarith
      refine mem_segment_of_param ((r.2 - p.2) / (q.2 - p.2))
        (div_nonneg (by linarith) (by linarith)) ((div_le_one (by linarith)).2 (by linarith))
        (by rw [hr1, ← hx]; ring) (by rw [div_mul_cancel₀ _ hv]; ring)
    · have hr1 : r.1 = p.1 := by
        rw [← hx, min_self] at hx1; rw [← hx, max_self] at hx2; linarith
      have hr2 : r.2 = p.2 := by
        rw [← hy, min_self] at hy1; rw [← hy, max_self] at hy2; linarith
      exact mem_segment_of_param 0 le_rfl zero_le_one (by rw [hr1]; ring) (by rw [hr2]; ring)
    · rw [min_eq_right hy.le] at hy1
      rw [max_eq_left hy.le] at hy2
      have hv : q.2 - p.2 ≠ 0 := sub_ne_zero.2 hy.ne
      have hr1 : r.1 = p.1 := by
        rw [← hx, min_self] at hx1; rw [← hx, max_self] at hx2; linarith
      refine mem_segment_of_param ((r.2 - p.2) / (q.2 - p.2))
        (div_nonneg_of_nonpos (by linarith) (by linarith))
        ((div_le_one_of_neg (by linarith)).2 (by linarith))
        (by rw [hr1, ← hx]; ring) (by rw [div_mul_cancel₀ _ hv]; ring)
  · rw [min_eq_right hx.le] at hx1
    rw [max_eq_left hx.le] at hx2
    have hv : q.1 - p.1 ≠ 0 := sub_ne_zero.2 hx.ne
    refine mem_segment_of_param ((r.1 - p.1) / (q.1 - p.1))
      (div_nonneg_of_nonpos (by linarith) (by linarith))
      ((div_le_one_of_neg (by linarith)).2 (by linarith)) (by rw [div_mul_cancel₀ _ hv]; ring) ?_
    have : r.2 - p.2 = (r.1 - p.1) / (q.1 - p.1) * (q.2 - p.2) := by
      rw [div_mul_eq_mul_div, eq_div_iff hv]
      linear_combination (-1 : 𝕜) * hd
    linarith

/-! ## Straddling

## Depends on

- [Straddles](straddles.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Geometry.SegmentIntersection](../../../../../../sources/v2/CSLibExt.md)
