/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.PenultsOfTak
import all MathlibExt.GameTheory.PenultsOfTakImpartialTakNotFirstPlayerWinsOfEven
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Variable Diamonds and L-Snakes in Impartial Tak

For `n ≥ 4`, the L-Snakes give penults with `(n - 2)^2 + 2` and `(n - 2)^2 + 3`
tokens. For `n ≥ 4`, `3 ≤ k ≤ n - 1` and `3 ≤ l ≤ n - 1`, the Variable Diamond gives a
penult with `n^2 - 2*n - k - l + 6` tokens. These boards realize every count from
`n^2 - 4*(n - 2) - 2` through `n^2 - 2*n`.

## References

* Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda,
  *The Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*,
  INTEGERS 25 (2025), Article G1, pp. 1–18, Proposition 6 and Figure 7.
* The path arguments reuse `Walk`, `walk_mem`, `walk_reverse` and `adjacent_symm` from
  `MathlibExt.GameTheory.PenultsOfTakImpartialTakNotFirstPlayerWinsOfEven`, and
  `impartialTak_isGreatest_penult_card.road_of_full_row` from `MathlibExt.GameTheory.PenultsOfTak`.
-/

namespace MetaMathlibExt

local notation "r₀[" p "]" => (p.1 : ℕ)
local notation "c₀[" p "]" => (p.2 : ℕ)

private theorem swap_walk {n : ℕ} {S T : Finset (Cell n)} {a b : Cell n}
    (h : ∀ p ∈ S, p.swap ∈ T) (w : Walk S a b) : Walk T a.swap b.swap :=
  w.lift Prod.swap fun _ _ step => ⟨step.1.symm, h _ step.2⟩

private theorem road_of_full_col {n : ℕ} {S : Finset (Cell n)} (c : Fin n)
    (h : ∀ r, (r, c) ∈ S) : takHasRoad S := by
  let T := S.map (Equiv.prodComm (Fin n) (Fin n)).toEmbedding
  have hT (p) (hp : p ∈ T) : p.swap ∈ S := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
    exact hq
  obtain ⟨a, ha, b, w, ends⟩ := impartialTak_isGreatest_penult_card.road_of_full_row
    (S := T) c fun r => Finset.mem_map.mpr ⟨(r, c), h r, rfl⟩
  exact ⟨a.swap, hT _ ha, b.swap, swap_walk hT w, ends.symm⟩

private theorem penult_of_replies {n : ℕ} (hn : 0 < n) {S : Finset (Cell n)}
    (safe : ∀ p, ¬ takHasRoad (insert p S))
    (reply : ∀ p ∉ S, ∃ q ∉ insert p S, takHasRoad (insert q (insert p S))) :
    placementPenult takHasRoad S := by
  let z : Fin n := ⟨0, hn⟩
  have not_full (p : Cell n) (h : insert p S = Finset.univ) : False :=
    safe p <| impartialTak_isGreatest_penult_card.road_of_full_row z
      fun c => h ▸ Finset.mem_univ (z, c)
  refine ⟨?_, fun p hp => ⟨?_, ?_⟩⟩
  · rintro (⟨a, ha, b, w, ends⟩ | h)
    · exact safe (z, z) ⟨a, Finset.mem_insert_of_mem ha, b,
        w.mono (fun _ _ step => ⟨step.1, Finset.mem_insert_of_mem step.2⟩) _ _, ends⟩
    · exact not_full (z, z) (by rw [h]; simp)
  · exact fun h => h.elim (safe p) (not_full p)
  · obtain ⟨q, hq, road⟩ := reply p hp
    exact ⟨q, hq, Or.inl road⟩

-- A region of the original board can block a road from one edge if the new cell
-- lies neither on that edge nor next to the region.
private theorem sealed_edge {n : ℕ} {S : Finset (Cell n)} {p a b : Cell n}
    {region edge opposite : Cell n → Prop}
    (edge_region : ∀ x ∈ S, edge x → region x)
    (region_off : ∀ x, region x → ¬ opposite x)
    (closed : ∀ x y, region x → y ∈ S → takAdjacent x y → region y)
    (hp : ¬ (edge p ∨ ∃ x, region x ∧ takAdjacent x p))
    (ha : a ∈ insert p S) (w : Walk (insert p S) a b) (he : edge a) (ho : opposite b) : False := by
  have start : region a := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact (hp (Or.inl he)).elim
    · exact edge_region a ha he
  have reach {z : Cell n} (v : Walk (insert p S) a z) : region z := by
    induction v with
    | refl => exact start
    | @tail x y _ hxy ih =>
      rcases Finset.mem_insert.mp hxy.2 with rfl | hy
      · exact (hp (Or.inr ⟨x, ih, hxy.1⟩)).elim
      · exact closed x y ih hy hxy.1
  exact region_off b (reach w) ho

section Diamond

-- The upper-right chain consists of a top rail and one clamped diagonal cell
-- in each interior row. The other chain is its transpose, with parameter l.
private def neHole {n : ℕ} (k : ℕ) (p : Cell n) : Prop :=
  (r₀[p] = 0 ∧ 0 < c₀[p] ∧ c₀[p] < k) ∨
    (0 < r₀[p] ∧ r₀[p] + 1 < n ∧ c₀[p] = min (r₀[p] + k - 1) (n - 1))

private noncomputable def diamond (n k l : ℕ) : Finset (Cell n) := by
  classical exact Finset.univ.filter fun p => ¬ neHole k p ∧ ¬ neHole l p.swap

private theorem mem_diamond {n k l : ℕ} {p : Cell n} :
    p ∈ diamond n k l ↔ ¬ neHole k p ∧ ¬ neHole l p.swap := by
  classical simp [diamond]

private theorem diamond_swap {n k l : ℕ} {p : Cell n} (h : p ∈ diamond n k l) :
    p.swap ∈ diamond n l k := by
  simpa only [mem_diamond, Prod.swap_swap, and_comm] using h

private def diamondTop {n : ℕ} (k : ℕ) (p : Cell n) : Prop :=
  (r₀[p] = 0 ∧ c₀[p] = 0) ∨ r₀[p] + k ≤ c₀[p]

private def diamondBottom {n : ℕ} (l : ℕ) (p : Cell n) : Prop :=
  (r₀[p] + 1 = n ∧ c₀[p] + 1 = n) ∨ c₀[p] + l ≤ r₀[p]

private def diamondCenter {n : ℕ} (k l : ℕ) (p : Cell n) : Prop :=
  0 < r₀[p] ∧ r₀[p] + 1 < n ∧ 0 < c₀[p] ∧ c₀[p] + 1 < n ∧
    c₀[p] + 1 < r₀[p] + k ∧ r₀[p] + 1 < c₀[p] + l

private theorem diamond_regions {n k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l) {p : Cell n}
    (hp : p ∈ diamond n k l) : diamondTop k p ∨ diamondBottom l p ∨ diamondCenter k l p := by
  have hr := p.1.isLt
  have hc := p.2.isLt
  simp only [mem_diamond, neHole, Prod.fst_swap, Prod.snd_swap] at hp
  unfold diamondTop diamondBottom diamondCenter
  omega

private theorem diamond_top_closed {n k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l)
    (x y : Cell n) (hx : diamondTop k x) (hy : y ∈ diamond n k l)
    (hxy : takAdjacent x y) : diamondTop k y := by
  have h := diamond_regions hk hl hy
  have hxr := x.1.isLt
  have hxc := x.2.isLt
  have hyr := y.1.isLt
  have hyc := y.2.isLt
  simp only [diamondTop, diamondBottom, diamondCenter] at h hx ⊢
  simp only [takAdjacent, Fin.ext_iff] at hxy
  omega

private theorem diamond_bottom_closed {n k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l)
    (x y : Cell n) (hx : diamondBottom l x) (hy : y ∈ diamond n k l)
    (hxy : takAdjacent x y) : diamondBottom l y := by
  have h := diamond_regions hk hl hy
  have hxr := x.1.isLt
  have hxc := x.2.isLt
  have hyr := y.1.isLt
  have hyc := y.2.isLt
  simp only [diamondTop, diamondBottom, diamondCenter] at h hx ⊢
  simp only [takAdjacent, Fin.ext_iff] at hxy
  omega

private theorem diamond_no_vertical {n k l : ℕ} (hn : 4 ≤ n) (hk : 3 ≤ k) (hl : 3 ≤ l)
    {p a b : Cell n} (ha : a ∈ insert p (diamond n k l))
    (w : Walk (insert p (diamond n k l)) a b) (ht : r₀[a] = 0) (hb : r₀[b] + 1 = n) : False := by
  let top (x : Cell n) := r₀[x] = 0
  let bottom (x : Cell n) := r₀[x] + 1 = n
  have opp_top (x : Cell n) (hx : diamondTop k x) : ¬ bottom x := by
    have := x.2.isLt
    unfold diamondTop at hx
    dsimp only [bottom]
    omega
  have opp_bottom (x : Cell n) (hx : diamondBottom l x) : ¬ top x := by
    unfold diamondBottom at hx
    dsimp only [top]
    omega
  by_cases h : top p ∨ ∃ x, diamondTop k x ∧ takAdjacent x p
  · refine sealed_edge (edge := bottom) (opposite := top) ?_ opp_bottom
      (diamond_bottom_closed hk hl) ?_ (walk_mem ha w) (walk_reverse ha w) hb ht
    · intro x hx he
      have hregion := diamond_regions hk hl hx
      have := x.2.isLt
      simp only [diamondTop, diamondCenter] at hregion
      dsimp only [bottom] at he
      exact (hregion.resolve_left (by omega)).resolve_right (by omega)
    · intro h'
      -- The top and bottom regions are too far apart to both touch the new cell.
      have hpr := p.1.isLt
      have hpc := p.2.isLt
      have hnearTop : r₀[p] = 0 ∨ r₀[p] + c₀[p] ≤ 1 ∨ r₀[p] + k ≤ c₀[p] + 1 := by
        rcases h with he | ⟨x, hx, hxp⟩
        · exact Or.inl he
        · simp only [diamondTop] at hx
          simp only [takAdjacent, Fin.ext_iff] at hxp
          omega
      have hnearBottom : r₀[p] + 1 = n ∨ 2 * n ≤ r₀[p] + c₀[p] + 3 ∨
          c₀[p] + l ≤ r₀[p] + 1 := by
        rcases h' with he | ⟨x, hx, hxp⟩
        · exact Or.inl he
        · simp only [diamondBottom] at hx
          simp only [takAdjacent, Fin.ext_iff] at hxp
          omega
      omega
  · refine sealed_edge (edge := top) (opposite := bottom) ?_ opp_top
      (diamond_top_closed hk hl) h ha w ht hb
    intro x hx he
    have hregion := diamond_regions hk hl hx
    simp only [diamondBottom, diamondCenter] at hregion
    dsimp only [top] at he
    exact hregion.resolve_right (by omega)

private theorem diamond_no_road {n k l : ℕ} (hn : 4 ≤ n) (hk : 3 ≤ k) (hl : 3 ≤ l)
    (p : Cell n) : ¬ takHasRoad (insert p (diamond n k l)) := by
  rintro ⟨a, ha, b, w, ⟨hle, hri⟩ | ⟨hto, hbo⟩⟩
  · have hswap (x) (hx : x ∈ insert p (diamond n k l)) :
        x.swap ∈ insert p.swap (diamond n l k) := by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_insert_self ..
      · exact Finset.mem_insert_of_mem (diamond_swap hx)
    exact diamond_no_vertical hn hl hk (hswap _ ha) (swap_walk hswap w) hle hri
  · exact diamond_no_vertical hn hk hl ha w hto hbo

private theorem diamond_row_holes {n k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l) (r c : Fin n)
    (hr : 0 < r.val) (hr' : r.val + 1 < n) :
    (r, c) ∉ diamond n k l ↔
      c.val = min (r.val + k - 1) (n - 1) ∨ c.val = r.val + 1 - l := by
  have hc := c.isLt
  simp only [mem_diamond, neHole, Prod.fst_swap, Prod.snd_swap]
  omega

private theorem diamond_row_reply {n k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l)
    {r c : Fin n} (hr : 0 < r.val) (hr' : r.val + 1 < n) (hp : (r, c) ∉ diamond n k l) :
    ∃ q ∉ insert (r, c) (diamond n k l), ∀ j,
      (r, j) ∈ insert q (insert (r, c) (diamond n k l)) := by
  let u : Fin n := ⟨min (r.val + k - 1) (n - 1), by omega⟩
  let d : Fin n := ⟨r.val + 1 - l, by omega⟩
  have hud : u ≠ d := by
    simp only [ne_eq, Fin.ext_iff, u, d]
    omega
  have holes (j : Fin n) : (r, j) ∉ diamond n k l ↔ j = u ∨ j = d := by
    rw [diamond_row_holes hk hl r j hr hr']
    simp only [Fin.ext_iff, u, d]
  have fill (a b : Fin n) (ha : a ≠ b) (hb : (r, b) ∉ diamond n k l)
      (h : ∀ j, (r, j) ∉ diamond n k l → j = a ∨ j = b) :
      ∃ q ∉ insert (r, a) (diamond n k l), ∀ j,
        (r, j) ∈ insert q (insert (r, a) (diamond n k l)) := by
    refine ⟨(r, b), by simp [ha.symm, hb], fun j => ?_⟩
    by_cases hj : (r, j) ∈ diamond n k l
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj)
    · rcases h j hj with rfl | rfl <;> simp
  rcases (holes c).mp hp with rfl | rfl
  · exact fill u d hud ((holes d).mpr (Or.inr rfl)) fun j => (holes j).mp
  · exact fill d u hud.symm ((holes u).mpr (Or.inl rfl)) fun j hj => ((holes j).mp hj).symm

private theorem diamond_penult {n k l : ℕ} (hn : 4 ≤ n) (hk : 3 ≤ k) (hl : 3 ≤ l)
    (hk' : k < n) (hl' : l < n) : placementPenult takHasRoad (diamond n k l) := by
  apply penult_of_replies (by omega) (diamond_no_road hn hk hl)
  rintro ⟨r, c⟩ hp
  by_cases hr : 0 < r.val ∧ r.val + 1 < n
  · obtain ⟨q, hq, hfull⟩ := diamond_row_reply hk hl hr.1 hr.2 hp
    exact ⟨q, hq, impartialTak_isGreatest_penult_card.road_of_full_row r hfull⟩
  · have hc : 0 < c.val ∧ c.val + 1 < n := by
      have hrl := r.isLt
      have hcl := c.isLt
      simp only [mem_diamond, neHole, Prod.fst_swap, Prod.snd_swap] at hp
      omega
    have hp' : (c, r) ∉ diamond n l k := fun h => hp (diamond_swap h)
    obtain ⟨q, hq, hfull⟩ := diamond_row_reply hl hk hc.1 hc.2 hp'
    refine ⟨q.swap, ?_, road_of_full_col c fun j => ?_⟩
    · intro h
      apply hq
      rcases Finset.mem_insert.mp h with he | he
      · exact Finset.mem_insert.mpr (Or.inl (by simpa using congrArg Prod.swap he))
      · exact Finset.mem_insert_of_mem (diamond_swap he)
    · rcases Finset.mem_insert.mp (hfull j) with he | hj
      · exact Finset.mem_insert.mpr (Or.inl (congrArg Prod.swap he))
      · rcases Finset.mem_insert.mp hj with he | hj
        · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl
            (congrArg Prod.swap he)))
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (diamond_swap hj))

open Classical in
private theorem neHole_card {n k : ℕ} (hn : 4 ≤ n) (hkn : k < n) :
    (Finset.univ.filter (neHole (n := n) k)).card = (k - 1) + (n - 2) := by
  let rail : Cell n → Prop := fun p => r₀[p] = 0 ∧ 0 < c₀[p] ∧ c₀[p] < k
  let diagonal : Cell n → Prop := fun p =>
    0 < r₀[p] ∧ r₀[p] + 1 < n ∧ c₀[p] = min (r₀[p] + k - 1) (n - 1)
  have hrail : (Finset.univ.filter rail).card = k - 1 := by
    have hcard : (Finset.Ioo 0 k).card = k - 1 := by simp
    rw [← hcard]
    apply Finset.card_bij (fun p _ => c₀[p])
    · intro p hp
      exact Finset.mem_Ioo.mpr (Finset.mem_filter.mp hp).2.2
    · intro a ha b hb he
      have ha' := (Finset.mem_filter.mp ha).2.1
      have hb' := (Finset.mem_filter.mp hb).2.1
      exact Prod.ext (Fin.ext (ha'.trans hb'.symm)) (Fin.ext he)
    · intro c hc
      have h := Finset.mem_Ioo.mp hc
      refine ⟨(⟨0, by omega⟩, ⟨c, by omega⟩), ?_, rfl⟩
      simpa [rail] using h
  have hdiag : (Finset.univ.filter diagonal).card = n - 2 := by
    have hcard := Nat.card_Ioo (a := 0) (b := n - 1)
    have hcard' : (Finset.Ioo 0 (n - 1)).card = n - 2 := by omega
    rw [← hcard']
    apply Finset.card_bij (fun p _ => r₀[p])
    · intro p hp
      have h := (Finset.mem_filter.mp hp).2
      dsimp only [diagonal] at h
      exact Finset.mem_Ioo.mpr ⟨h.1, by omega⟩
    · intro a ha b hb he
      have ha' := (Finset.mem_filter.mp ha).2.2.2
      have hb' := (Finset.mem_filter.mp hb).2.2.2
      exact Prod.ext (Fin.ext he) (Fin.ext (by rw [ha', hb', he]))
    · intro r hr
      have h := Finset.mem_Ioo.mp hr
      refine ⟨(⟨r, by omega⟩, ⟨min (r + k - 1) (n - 1), by omega⟩), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, diagonal, and_true]
      omega
  have hsplit : Finset.univ.filter (neHole (n := n) k) =
      Finset.univ.filter rail ∪ Finset.univ.filter diagonal := by
    ext p
    simp [neHole, rail, diagonal]
  rw [hsplit, Finset.card_union_of_disjoint, hrail, hdiag]
  apply Finset.disjoint_left.mpr
  intro p h₁ h₂
  have h₁' := (Finset.mem_filter.mp h₁).2.1
  have h₂' := (Finset.mem_filter.mp h₂).2.1
  exact h₂'.ne' h₁'

-- Use the number of holes, rather than subtraction from the full board, to
-- keep the cardinality formula in natural numbers.
private theorem diamond_card {n k l : ℕ} (hn : 4 ≤ n) (hk : 3 ≤ k) (hl : 3 ≤ l)
    (hk' : k < n) (hl' : l < n) : (diamond n k l).card + (2 * n + k + l - 6) = n ^ 2 := by
  classical
  let NE := Finset.univ.filter (neHole (n := n) k)
  let SW := Finset.univ.filter fun p : Cell n => neHole l p.swap
  have hNE : NE.card = (k - 1) + (n - 2) := neHole_card hn hk'
  have hSW : SW.card = (l - 1) + (n - 2) := by
    let swap := Equiv.prodComm (Fin n) (Fin n)
    have hmap : SW = (Finset.univ.filter (neHole (n := n) l)).map swap.toEmbedding := by
      ext p
      simp [SW, swap]
    rw [hmap, Finset.card_map, neHole_card hn hl']
  have hd : Disjoint NE SW := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have hr := p.1.isLt
    have hc := p.2.isLt
    simp only [neHole, Prod.fst_swap, Prod.snd_swap] at hp' hq'
    omega
  have hcompl : (diamond n k l)ᶜ = NE ∪ SW := by
    ext p
    simp only [mem_diamond, NE, SW, Finset.mem_compl, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    simp only [not_and_or, not_not]
  have hcard := Finset.card_add_card_compl (diamond n k l)
  rw [hcompl, Finset.card_union_of_disjoint hd, hNE, hSW, Fintype.card_prod, Fintype.card_fin,
    ← sq] at hcard
  omega

end Diamond

section LSnake

private def snakeBlock {n : ℕ} (p : Cell n) : Prop := 2 ≤ r₀[p] ∧ c₀[p] + 2 < n

-- The token at (1, n-2) of the two-token shape is not joined to either edge.
private def snakeOuter {n : ℕ} (three : Bool) (p : Cell n) : Prop :=
  (r₀[p] = 0 ∧ c₀[p] + 1 = n) ∨
    (three = true ∧ ((r₀[p] = 0 ∧ c₀[p] + 2 = n) ∨ (r₀[p] = 1 ∧ c₀[p] + 1 = n)))

private def snakeTip {n : ℕ} (three : Bool) (p : Cell n) : Prop :=
  three = false ∧ r₀[p] = 1 ∧ c₀[p] + 2 = n

private noncomputable def snake (n : ℕ) (three : Bool) : Finset (Cell n) := by
  classical exact Finset.univ.filter fun p => snakeBlock p ∨ snakeOuter three p ∨ snakeTip three p

private theorem mem_snake {n : ℕ} {three : Bool} {p : Cell n} :
    p ∈ snake n three ↔ snakeBlock p ∨ snakeOuter three p ∨ snakeTip three p := by
  classical simp [snake]

private theorem snake_block_closed {n : ℕ} {three : Bool} (x y : Cell n) (hx : snakeBlock x)
    (hy : y ∈ snake n three) (hxy : takAdjacent x y) : snakeBlock y := by
  rcases mem_snake.mp hy with h | h | h
  · exact h
  · simp only [snakeOuter, snakeBlock, takAdjacent, Fin.ext_iff] at h hx hxy
    omega
  · simp only [snakeTip, snakeBlock, takAdjacent, Fin.ext_iff] at h hx hxy
    omega

private theorem snake_outer_closed {n : ℕ} {three : Bool} (x y : Cell n)
    (hx : snakeOuter three x) (hy : y ∈ snake n three) (hxy : takAdjacent x y) :
    snakeOuter three y := by
  rcases mem_snake.mp hy with h | h | h
  · exact (by
      simp only [snakeOuter, snakeBlock, takAdjacent, Fin.ext_iff] at hx h hxy
      omega : False).elim
  · exact h
  · obtain ⟨rfl, hy₁, hy₂⟩ := h
    have hx' : r₀[x] = 0 ∧ c₀[x] + 1 = n := by simpa [snakeOuter] using hx
    simp only [takAdjacent, Fin.ext_iff] at hxy
    omega

-- The anti-diagonal reflection preserves both L-Snakes and interchanges the
-- vertical and horizontal crossing problems.
private def antiDiag {n : ℕ} (p : Cell n) : Cell n := (p.2.rev, p.1.rev)

private theorem snake_reflect {n : ℕ} {three : Bool} {p : Cell n} (h : p ∈ snake n three) :
    antiDiag p ∈ snake n three := by
  have hr := p.1.isLt
  have hc := p.2.isLt
  rw [mem_snake] at h ⊢
  have hrow : r₀[antiDiag p] = n - (c₀[p] + 1) := Fin.val_rev _
  have hcol : c₀[antiDiag p] = n - (r₀[p] + 1) := Fin.val_rev _
  cases three <;>
    simp only [snakeBlock, snakeOuter, snakeTip, hrow, hcol, Bool.false_eq_true,
      Bool.true_eq_false, false_and, true_and, or_false] at h ⊢ <;> omega

private theorem snake_no_vertical {n : ℕ} {three : Bool} (hn : 4 ≤ n) {p a b : Cell n}
    (ha : a ∈ insert p (snake n three)) (w : Walk (insert p (snake n three)) a b)
    (ht : r₀[a] = 0) (hb : r₀[b] + 1 = n) : False := by
  let top (x : Cell n) := r₀[x] = 0
  let bottom (x : Cell n) := r₀[x] + 1 = n
  by_cases h : top p ∨ ∃ x, snakeOuter three x ∧ takAdjacent x p
  · refine sealed_edge (edge := bottom) (opposite := top) ?_ ?_ snake_block_closed ?_
      (walk_mem ha w) (walk_reverse ha w) hb ht
    · intro x hx he
      rcases mem_snake.mp hx with h | h | h
      · exact h
      · simp only [bottom] at he
        unfold snakeOuter at h
        omega
      · simp only [bottom] at he
        unfold snakeTip at h
        omega
    · intro x hx he
      exact hx.1.not_gt (show r₀[x] < 2 by dsimp only [top] at he; omega)
    · intro h'
      have htop : r₀[p] = 0 ∨ r₀[p] ≤ 1 ∧ n ≤ c₀[p] + 3 ∨
          r₀[p] = 2 ∧ c₀[p] + 1 = n := by
        rcases h with he | ⟨x, hx, hxp⟩
        · exact Or.inl he
        · simp only [snakeOuter, takAdjacent, Fin.ext_iff] at hx hxp
          omega
      -- For a point in row 1 to touch the block it must already have a block column.
      have hbottom : r₀[p] + 1 = n ∨ 2 ≤ r₀[p] ∧ c₀[p] + 1 < n ∨
          r₀[p] = 1 ∧ c₀[p] + 2 < n := by
        rcases h' with he | ⟨x, hx, hxp⟩
        · exact Or.inl he
        · simp only [snakeBlock, takAdjacent, Fin.ext_iff] at hx hxp
          omega
      -- The loose first bound for row 1 can meet the block only at column n-3;
      -- an outer token cannot touch that cell in one orthogonal step.
      have hsharp : r₀[p] = 1 → c₀[p] + 2 ≥ n := by
        intro hrow
        rcases h with he | ⟨x, hx, hxp⟩
        · dsimp only [top] at he
          omega
        · simp only [snakeOuter, takAdjacent, Fin.ext_iff] at hx hxp
          omega
      omega
  · refine sealed_edge (edge := top) (opposite := bottom) ?_ ?_ snake_outer_closed h ha w ht hb
    · intro x hx he
      rcases mem_snake.mp hx with h | h | h
      · exact (by dsimp only [top] at he; have := h.1; omega : False).elim
      · exact h
      · exact (by dsimp only [top] at he; have := h.2.1; omega : False).elim
    · intro x hx he
      simp only [bottom] at he
      unfold snakeOuter at hx
      omega

private theorem snake_no_road {n : ℕ} (hn : 4 ≤ n) (three : Bool) (p : Cell n) :
    ¬ takHasRoad (insert p (snake n three)) := by
  rintro ⟨a, ha, b, w, ⟨hle, hri⟩ | ⟨hto, hbo⟩⟩
  · have hmem (x) (hx : x ∈ insert p (snake n three)) :
        antiDiag x ∈ insert (antiDiag p) (snake n three) := by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_insert_self ..
      · exact Finset.mem_insert_of_mem (snake_reflect hx)
    have w' : Walk (insert (antiDiag p) (snake n three)) (antiDiag a) (antiDiag b) := by
      apply w.lift antiDiag
      rintro x y ⟨hxy, hy⟩
      refine ⟨?_, hmem y hy⟩
      have hxr := x.1.isLt
      have hxc := x.2.isLt
      have hyr := y.1.isLt
      have hyc := y.2.isLt
      simp only [takAdjacent, Fin.ext_iff, antiDiag, Fin.val_rev] at hxy ⊢
      omega
    apply snake_no_vertical hn (hmem _ (walk_mem ha w)) (walk_reverse (hmem a ha) w')
    · simp only [antiDiag, Fin.val_rev]
      omega
    · simp only [antiDiag, Fin.val_rev]
      omega
  · exact snake_no_vertical hn ha w hto hbo

-- The reply in the corner case joins (1,n-2) to the solid block via (2,n-2).
private theorem snake_reply_corner {n : ℕ} (hn : 4 ≤ n) (three : Bool) {p : Cell n}
    (hp : p ∉ snake n three) (hr : r₀[p] < 2) (hc : n ≤ c₀[p] + 2) :
    ∃ q ∉ insert p (snake n three), takHasRoad (insert q (insert p (snake n three))) := by
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  let t : Fin n := ⟨2, by omega⟩
  let l : Fin n := ⟨n - 3, by omega⟩
  let m : Fin n := ⟨n - 2, by omega⟩
  let e : Fin n := ⟨n - 1, by omega⟩
  let q : Cell n := (t, m)
  let T := insert q (insert p (snake n three))
  have hpc := p.2.isLt
  have hp' := hp
  simp only [mem_snake, snakeBlock, snakeOuter, snakeTip] at hp'
  have hq : q ∉ insert p (snake n three) := by
    simp only [Finset.mem_insert, mem_snake, snakeBlock, snakeOuter, snakeTip, q, t, m]
    intro h
    rcases h with he | he
    · have he' := congrArg Prod.fst he
      have hval := congrArg Fin.val he'
      dsimp only at hval
      omega
    · omega
  have hm (a : Cell n) (h : a ∈ snake n three) : a ∈ T :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
  have hpin : p ∈ T := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
  have hqmem : q ∈ T := Finset.mem_insert_self ..
  have block (i : Fin n) (hi : 2 ≤ i.val) : (i, l) ∈ T :=
    hm _ (mem_snake.mpr (Or.inl ⟨hi, by dsimp [l]; omega⟩))
  have diagonal : Walk T (o, m) q :=
    .single ⟨Or.inr ⟨rfl, Or.inl rfl⟩, hqmem⟩
  have enter : Walk T q (t, l) :=
    .single ⟨Or.inl ⟨rfl, Or.inr (by change n - 3 + 1 = n - 2; omega)⟩, block t (by rfl)⟩
  have toBottom (j : ℕ) (hlo : 2 ≤ j) (hhi : j < n) : Walk T (t, l) (⟨j, hhi⟩, l) := by
    induction j, hlo using Nat.le_induction with
    | base => exact .refl
    | succ j hle ih =>
      refine (ih (by omega)).tail ⟨Or.inr ⟨rfl, Or.inl rfl⟩, block _ ?_⟩
      change 2 ≤ j + 1
      omega
  have finish (c : Fin n) (hstart : (z, c) ∈ T) (w : Walk T (z, c) (o, m)) : takHasRoad T :=
    ⟨(z, c), hstart, (e, l), w.trans (diagonal.trans (enter.trans (toBottom _ (by dsimp [e]; omega)
      e.isLt))), Or.inr ⟨rfl, by dsimp [e]; omega⟩⟩
  refine ⟨q, hq, ?_⟩
  cases three
  · simp at hp'
    have htip : (o, m) ∈ T := hm _ (mem_snake.mpr (Or.inr (Or.inr
      ⟨rfl, rfl, by dsimp [m]; omega⟩)))
    by_cases h : r₀[p] = 0
    · have he : p = (z, m) := Prod.ext (Fin.ext h) (Fin.ext (by dsimp [m]; omega))
      exact finish m (he ▸ hpin) (.single ⟨Or.inr ⟨rfl, Or.inl rfl⟩, htip⟩)
    · have he : p = (o, e) := Prod.ext
        (Fin.ext (by change r₀[p] = 1; omega)) (Fin.ext (by change c₀[p] = n - 1; omega))
      have hstart : (z, e) ∈ T := hm _ (mem_snake.mpr (Or.inr (Or.inl (Or.inl
        ⟨rfl, by dsimp [e]; omega⟩))))
      have step : Walk T (z, e) (o, e) := .single ⟨Or.inr ⟨rfl, Or.inl rfl⟩, he ▸ hpin⟩
      exact finish e hstart <| step.tail
        ⟨Or.inl ⟨rfl, Or.inr (by change n - 2 + 1 = n - 1; omega)⟩, htip⟩
  · simp at hp'
    have he : p = (o, m) := Prod.ext
      (Fin.ext (by change r₀[p] = 1; omega)) (Fin.ext (by change c₀[p] = n - 2; omega))
    have hstart : (z, m) ∈ T := hm _ (mem_snake.mpr (Or.inr (Or.inl (Or.inr
      ⟨rfl, Or.inl ⟨rfl, by dsimp [m]; omega⟩⟩))))
    exact finish m hstart (.single ⟨Or.inr ⟨rfl, Or.inl rfl⟩, he ▸ hpin⟩)

private theorem snake_penult {n : ℕ} (hn : 4 ≤ n) (three : Bool) :
    placementPenult takHasRoad (snake n three) := by
  apply penult_of_replies (by omega) (snake_no_road hn three)
  rintro ⟨r, c⟩ hp
  have hrn := r.isLt
  have hcn := c.isLt
  by_cases hr : r.val < 2
  · by_cases hc : c.val + 2 < n
    · let s : Fin n := ⟨1 - r.val, by omega⟩
      have hsr : s ≠ r := by
        simp only [ne_eq, Fin.ext_iff, s]
        omega
      have hs : (s, c) ∉ snake n three := by
        simp only [mem_snake, snakeBlock, snakeTip, snakeOuter, s]
        omega
      refine ⟨(s, c), by simp [hsr, hs], road_of_full_col c fun j => ?_⟩
      by_cases hj : 2 ≤ j.val
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (mem_snake.mpr (Or.inl ⟨hj, hc⟩)))
      · have he : j = s ∨ j = r := by simp only [Fin.ext_iff, s]; omega
        rcases he with rfl | rfl <;> simp
    · exact snake_reply_corner hn three hp hr (by change n ≤ c.val + 2; omega)
  · have hc : n ≤ c.val + 2 := by
      by_contra! hc
      exact hp (mem_snake.mpr (Or.inl ⟨by change 2 ≤ r.val; omega, hc⟩))
    let d : Fin n := ⟨2 * n - 3 - c.val, by omega⟩
    have hdc : d ≠ c := by
      simp only [ne_eq, Fin.ext_iff, d]
      omega
    have hd : (r, d) ∉ snake n three := by
      simp only [mem_snake, snakeBlock, snakeTip, snakeOuter, d]
      omega
    refine ⟨(r, d), by simp [hdc, hd],
      impartialTak_isGreatest_penult_card.road_of_full_row r fun j => ?_⟩
    by_cases hj : j.val + 2 < n
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (mem_snake.mpr (Or.inl ⟨by change 2 ≤ r.val; omega, hj⟩)))
    · have hjn := j.isLt
      have he : j = d ∨ j = c := by simp only [Fin.ext_iff, d]; omega
      rcases he with rfl | rfl <;> simp

private theorem snake_card {n : ℕ} (hn : 4 ≤ n) (three : Bool) :
    (snake n three).card = (n - 2) ^ 2 + (if three then 3 else 2) := by
  classical
  let B := Finset.univ.filter (snakeBlock (n := n))
  let C := Finset.univ.filter fun p : Cell n => snakeOuter three p ∨ snakeTip three p
  have hB : B.card = (n - 2) ^ 2 := by
    have hcard : ((Finset.Ico 2 n) ×ˢ Finset.range (n - 2)).card = (n - 2) ^ 2 := by
      simp [sq]
    rw [← hcard]
    apply Finset.card_bij (fun p _ => (r₀[p], c₀[p]))
    · intro p hp
      have h := (Finset.mem_filter.mp hp).2
      simp only [snakeBlock] at h
      have hr := p.1.isLt
      simp only [Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
      exact ⟨⟨h.1, hr⟩, by omega⟩
    · intro p _ q _ h
      exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
    · rintro ⟨r, c⟩ h
      simp only [Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at h
      exact ⟨(⟨r, h.1.2⟩, ⟨c, by omega⟩), by simpa [B, snakeBlock] using
        (show 2 ≤ r ∧ c + 2 < n from ⟨h.1.1, by omega⟩), rfl⟩
  have hC : C.card = (if three then 3 else 2) := by
    let z : Fin n := ⟨0, by omega⟩
    let o : Fin n := ⟨1, by omega⟩
    let m : Fin n := ⟨n - 2, by omega⟩
    let e : Fin n := ⟨n - 1, by omega⟩
    have hzo : z ≠ o := by simp [z, o, Fin.ext_iff]
    have hme : m ≠ e := by simp only [m, e, ne_eq, Fin.ext_iff]; omega
    cases three
    · have hset : C = {(z, e), (o, m)} := by
        ext ⟨r, c⟩
        have hc := c.isLt
        simp [C, snakeOuter, snakeTip, Prod.mk.injEq, Fin.ext_iff, z, o, m, e]
        omega
      rw [hset]
      simp [hzo]
    · have hset : C = {(z, e), (z, m), (o, e)} := by
        ext ⟨r, c⟩
        have hc := c.isLt
        simp [C, snakeOuter, snakeTip, Prod.mk.injEq, Fin.ext_iff, z, o, m, e]
        omega
      rw [hset]
      simp [hzo, hme.symm, Finset.card_insert_of_notMem]
  have hunion : snake n three = B ∪ C := by ext p; simp [B, C, mem_snake]
  have hdisj : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hb := (Finset.mem_filter.mp hp).2.1
    have hc := (Finset.mem_filter.mp hq).2
    simp only [snakeOuter, snakeTip] at hc
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisj, hB, hC]

end LSnake

/-- **Impartial Tak penults of every size from $n^2 - 4(n - 2) - 2$ to $n^2 - 2n$.** Impartial Tak
is the placement game on the $n \times n$ board whose play ends once the tokens contain a road. Let
$n \ge 4$ and let $x$ be a natural number with $n^2 - 4(n - 2) - 2 \le x \le n^2 - 2n$. Then there
is an Impartial Tak penult on the $n \times n$ board with exactly $x$ tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 6 (`integers-2025-G1-prop-6`). -/
public theorem impartialTak_exists_penult_card {n x : ℕ} (hn : 4 ≤ n)
    (hlo : n ^ 2 - 4 * (n - 2) - 2 ≤ x) (hhi : x ≤ n ^ 2 - 2 * n) :
    ∃ S : Finset (Fin n × Fin n), placementPenult takHasRoad S ∧ S.card = x := by
  have expand : n ^ 2 = (n - 2) ^ 2 + 4 * (n - 2) + 4 := calc
    _ = ((n - 2) + 2) ^ 2 := congrArg (fun t : ℕ => t ^ 2) (by omega)
    _ = _ := by ring
  by_cases htwo : x = (n - 2) ^ 2 + 2
  · exact ⟨snake n false, snake_penult hn false, (snake_card hn false).trans htwo.symm⟩
  by_cases hthree : x = (n - 2) ^ 2 + 3
  · exact ⟨snake n true, snake_penult hn true, (snake_card hn true).trans hthree.symm⟩
  let d := n ^ 2 - 2 * n + 6 - x
  let k := min (n - 1) (d - 3)
  let l := d - k
  have bounds : 6 ≤ d ∧ d ≤ 2 * (n - 1) := by dsimp [d]; omega
  have hk : 3 ≤ k := by dsimp [k]; omega
  have hl : 3 ≤ l := by dsimp [l, k]; omega
  have hk' : k < n := by dsimp [k]; omega
  have hl' : l < n := by dsimp [l, k]; omega
  have he : k + l = d := by
    have hk₀ : k ≤ d := by dsimp [k]; omega
    exact Nat.add_sub_of_le hk₀
  have card := diamond_card hn hk hl hk' hl'
  refine ⟨diamond n k l, diamond_penult hn hk hl hk' hl', ?_⟩
  have hdn : d = n ^ 2 - 2 * n + 6 - x := rfl
  omega

end MetaMathlibExt
