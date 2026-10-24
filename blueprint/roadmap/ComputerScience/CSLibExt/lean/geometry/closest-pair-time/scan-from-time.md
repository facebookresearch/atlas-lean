---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Geometry.scanFrom_time
---

# Scan From time

CLRS's packing bound: at most seven strip points follow `p` within `y` gap `√δ`. -/
theorem length_le_seven {δ xmid : ℝ} (p : Tagged) (Z : List Tagged)
    (hpair : (p :: Z).Pairwise (SameSideFar δ))
    (hstrip : ∀ a ∈ p :: Z, InStrip δ xmid a)
    (hy : ∀ a ∈ Z, p.1.2 ≤ a.1.2 ∧ (a.1.2 - p.1.2) ^ 2 < δ) :
    Z.length ≤ 7 := by
  by_contra hlen
  have hδ : 0 < δ := lt_of_le_of_lt (sq_nonneg _) (hstrip p List.mem_cons_self).1
  set s := √δ with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hδ
  have hss : s ^ 2 = δ := Real.sq_sqrt hδ.le
  -- every point is in the rectangle
  have hbox : ∀ a ∈ p :: Z, |a.1.1 - xmid| < s ∧ 0 ≤ a.1.2 - p.1.2 ∧ a.1.2 - p.1.2 < s := by
    intro a ha
    refine ⟨(Real.lt_sqrt (abs_nonneg _)).2 (by rw [sq_abs]; exact (hstrip a ha).1), ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · simp [hs0]
    · obtain ⟨h1, h2⟩ := hy a ha
      refine ⟨by linarith, ?_⟩
      have := (Real.lt_sqrt (abs_nonneg _)).2 (by rw [sq_abs]; exact h2)
      rwa [abs_of_nonneg (by linarith)] at this
  -- eight cells
  let L := p :: Z
  let cell : Fin L.length → Bool × Bool × Bool := fun i =>
    (L[i].2, decide (|L[i].1.1 - xmid| ≤ s / 2), decide (L[i].1.2 - p.1.2 ≤ s / 2))
  have hcard : Fintype.card (Bool × Bool × Bool) < Fintype.card (Fin L.length) := by
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, L, List.length_cons]
    omega
  obtain ⟨i, j, hij, hcell⟩ := Fintype.exists_ne_map_eq_of_card_lt cell hcard
  have hpw := List.pairwise_iff_getElem.1 hpair
  -- the two points in one cell
  have key : ∀ i j : Fin L.length, i < j → cell i = cell j → False := by
    intro i j hlt hc
    simp only [cell, Prod.mk.injEq, decide_eq_decide] at hc
    obtain ⟨hside, hcx, hcy⟩ := hc
    have hfar := hpw i j i.isLt j.isLt hlt hside
    have hai : L[i] ∈ L := List.getElem_mem _
    have haj : L[j] ∈ L := List.getElem_mem _
    obtain ⟨hxi, hyi0, hyi1⟩ := hbox _ hai
    obtain ⟨hxj, hyj0, hyj1⟩ := hbox _ haj
    have hsi := hstrip _ hai
    have hsj := hstrip _ haj
    have hle := dist2_le_of_same_cell hxi hxj hside hsi.2.1 hsi.2.2 hsj.2.1 hsj.2.2
      ⟨hyi0, hyi1⟩ ⟨hyj0, hyj1⟩ hcx hcy
    rw [hss] at hle
    have hfar' : δ ≤ dist2 L[i].1 L[j].1 := hfar
    linarith
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hcell
  · exact key j i h hcell.symm

/-! ## The strip scan

## Depends on

- [Scan From](../closest-pair/scan-from.md)

## Proof depends on

- [Dist2](../closest-pair/dist2.md)
- [Omin](../../data-structures/part-03/sparse-table/omin.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Geometry.ClosestPairTime](../../../../../../sources/v2/CSLibExt.md)
