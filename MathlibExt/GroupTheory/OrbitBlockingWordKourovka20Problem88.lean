/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Words blocking the automorphic orbit of a free group element (Kourovka Notebook Problem 20.88)

Kourovka Notebook, Problem 20.88 (V. Shpilrain), marked solved in the 21st issue: let `u` be an
element of a free group `F_r`. Is it true that there is `v ∈ F_r` (that depends on `u`) that cannot
be a subword of any cyclically reduced word `φ(u)`, where `φ` is an automorphism of `F_r`?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.88 (V. Shpilrain). UnsolvedMath record
UM-00701746 (`KOU-20.88`), dataset ulamai/UnsolvedMath v1.8.0.

Elements are compared through their reduced words `FreeGroup.toWord`; subword means contiguous
factor (`List.IsInfix`), and cyclically reduced is Mathlib's `FreeGroup.IsCyclicallyReduced`. The
rank is `r ≥ 1`: in the trivial group `F₀` the only candidate `v = 1` has the empty word, a subword
of every word.

The theorem `existsOrbitBlockingWord_holds` has a direct proof by counting translates of paths
in the Cayley tree. Fix an edge at the identity. A word of length `m` can take at most `2m`
starting vertices across the cut determined by the edge. Color each vertex by the side of the
cut containing its preimage under the automorphism.
Outside a finite ball the color of a vertex is constant on reduced extensions, and a longest
prefix with extensions of both colors gives two directions with opposite colors.

Choose a cyclically reduced word containing every turn up to reversal. Translating any occurrence
of the turn between those two directions to the branching vertex gives a crossing, provided the
path extends far enough to either side. If a cyclically reduced image contained `2m + 1` consecutive
copies of the chosen word, its powers would supply at least `2m + 1` crossings per interior period.
The upper bound grows by only `2m` per period.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.OrbitBlockingWordKourovka20Problem88Wanted

/-- **Kourovka Problem 20.88 (statement).** The statement that for every $r \ge 1$ and every
element $u$ of the free group $F_r$ on $r$ generators there is $v \in F_r$ such that, for every
automorphism $\varphi$ of $F_r$ for which the reduced word of $\varphi(u)$ is cyclically reduced,
the reduced word of $v$ is not a subword (a contiguous factor) of the reduced word of $\varphi(u)$.
-/
def existsOrbitBlockingWord : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ u : FreeGroup (Fin r), ∃ v : FreeGroup (Fin r),
    ∀ φ : MulAut (FreeGroup (Fin r)), FreeGroup.IsCyclicallyReduced (φ u).toWord →
      ¬ v.toWord <:+: (φ u).toWord

open FreeGroup

variable {α : Type} [DecidableEq α]

private abbrev Letter (α : Type) := α × Bool
private abbrev Word (α : Type) := List (Letter α)
private abbrev flip (a : Letter α) : Letter α := (a.1, !a.2)

-- Test the half-tree on the positive side of the edge at the chosen generator.
private def side (a : α) (g : FreeGroup α) : Bool :=
  g.toWord.head? == some (a, true)

private theorem side_step (a : α) (l : Letter α) (g : FreeGroup α)
    (h : side a g ≠ side a (g * mk [l])) : g = 1 ∨ g = of a := by
  obtain ⟨b, s⟩ := l
  unfold side at h
  rw [toWord_mul_mk_eq] at h
  generalize hw : g.toWord = w at h
  have hg : mk w = g := hw ▸ mk_toWord (x := g)
  cases w with
  | nil => exact Or.inl hg.symm
  | cons c w =>
    cases w with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      split at h
      · have : c = (a, true) := by simpa using h
        exact Or.inr (hg.symm.trans (by rw [this]; rfl))
      · simp at h
    | cons d w =>
      split at h <;> simp at h

-- A word of length m changes sides at no more than 2m starting vertices.
private theorem crossings (a : α) (w : Word α) :
    ∃ s : Finset (FreeGroup α), s.card ≤ 2 * w.length ∧
      ∀ g, side a g ≠ side a (g * mk w) → g ∈ s := by
  classical
  induction w with
  | nil => exact ⟨∅, by simp, by simp [← one_eq_mk]⟩
  | cons l w ih =>
    obtain ⟨s, hs, hc⟩ := ih
    let t := s.image (· * (mk [l])⁻¹)
    refine ⟨{1, of a} ∪ t, ?_, ?_⟩
    · have ht : t.card ≤ s.card := Finset.card_image_le
      have h₂ : ({1, of a} : Finset _).card ≤ 2 :=
        (Finset.card_insert_le _ _).trans (by simp)
      have := Finset.card_union_le ({1, of a} : Finset _) t
      simp only [List.length_cons]
      omega
    · intro g h
      change side a g ≠ side a (g * (mk [l] * mk w)) at h
      by_cases hh : side a g = side a (g * mk [l])
      · rw [hh, ← mul_assoc] at h
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨_, hc _ h, mul_inv_cancel_right _ _⟩)
      · rcases side_step a l g hh with rfl | rfl <;> simp

private abbrev color (a : α) (e : MulAut (FreeGroup α)) (w : Word α) : Bool :=
  side a (e.symm (mk w))

-- Outside a finite ball the color is constant on reduced extensions.
private theorem stable_radius [Finite α] (a : α) (e : MulAut (FreeGroup α)) :
    ∃ N : ℕ, ∀ (p q : Word α), N ≤ p.length → IsReduced (p ++ q) →
      color a e (p ++ q) = color a e p := by
  classical
  let := Fintype.ofFinite α
  choose S _ hS using fun l : Letter α => crossings a (e.symm (mk [l])).toWord
  let bound := (Finset.univ.biUnion S).sup (fun x => (e x).toWord.length)
  refine ⟨bound + 1, ?_⟩
  have step (p : Word α) (l : Letter α) (hp : IsReduced p) (hlen : bound < p.length) :
      color a e (p ++ [l]) = color a e p := by
    by_contra! hn
    have hs := hS l (e.symm (mk p)) (by
      rw [mk_toWord, ← e.symm.map_mul, mul_mk]
      exact Ne.symm hn)
    have hb := Finset.le_sup (s := Finset.univ.biUnion S) (f := fun x => (e x).toWord.length)
      (Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, hs⟩)
    simp only [MulEquiv.apply_symm_apply, toWord_mk, hp.reduce_eq] at hb
    exact (Nat.not_le_of_lt hlen) hb
  intro p q hp hr
  induction q using List.reverseRecOn with
  | nil => simp
  | append_singleton q l ih =>
    rw [← List.append_assoc] at hr ⊢
    have hred := hr.infix (List.prefix_append (p ++ q) [l]).isInfix
    rw [step _ _ hred (by simp; omega), ih hred]

-- Images of sufficiently large positive and negative powers give both colors at large radii.
private theorem long_colors [Finite α] (a : α) (e : MulAut (FreeGroup α)) (N : ℕ) :
    ∃ p q : Word α, IsReduced p ∧ IsReduced q ∧ N ≤ p.length ∧ N ≤ q.length ∧
      color a e p ≠ color a e q := by
  classical
  let := Fintype.ofFinite α
  let C := Finset.univ.sup (fun l : Letter α => norm (e.symm (mk [l])))
  have bound (w : Word α) : norm (e.symm (mk w)) ≤ C * w.length := by
    induction w with
    | nil => simp [← one_eq_mk]
    | cons l w ih =>
      change norm (e.symm (mk [l] * mk w)) ≤ C * (w.length + 1)
      rw [e.symm.map_mul, Nat.mul_add, Nat.mul_one]
      have := Finset.le_sup (f := fun l : Letter α => norm (e.symm (mk [l])))
        (Finset.mem_univ l)
      exact (FreeGroup.norm_mul_le _ _).trans (by dsimp [C] at *; omega)
  let k := C * N + 1
  let x := e (of a ^ k)
  have hx : N ≤ x.toWord.length := by
    have hh := bound x.toWord
    simp only [mk_toWord, x, MulEquiv.symm_apply_apply, norm_of_pow] at hh
    by_contra! h
    have := Nat.mul_le_mul_left C h.le
    change C * N + 1 ≤ C * x.toWord.length at hh
    omega
  refine ⟨x.toWord, x⁻¹.toWord, isReduced_toWord, isReduced_toWord, hx, ?_, ?_⟩
  · simpa using hx
  · simp only [color, side, mk_toWord, x, e.symm.map_inv, MulEquiv.symm_apply_apply]
    simp [toWord_inv, invRev, k, List.head?_replicate]

private abbrev Opposed (a : α) (e : MulAut (FreeGroup α)) (N : ℕ)
    (t : Word α) (b c : Letter α) :=
  ∀ (x y : Word α), N ≤ x.length → N ≤ y.length →
    IsReduced (t ++ b :: x) → IsReduced (t ++ c :: y) →
    color a e (t ++ b :: x) ≠ color a e (t ++ c :: y)

-- A longest prefix with long extensions in both colors branches into monochromatic cones.
private theorem opposed_cones [Finite α] (a : α) (e : MulAut (FreeGroup α)) :
    ∃ (N : ℕ) (t : Word α) (b c : Letter α), b ≠ c ∧
      IsReduced (t ++ [b]) ∧ IsReduced (t ++ [c]) ∧
      Opposed a e N t b c := by
  classical
  obtain ⟨N, hN⟩ := stable_radius a e
  let Mixed (p : Word α) := ∃ x y : Word α,
    IsReduced (p ++ x) ∧ IsReduced (p ++ y) ∧
    N ≤ (p ++ x).length ∧ N ≤ (p ++ y).length ∧ color a e (p ++ x) ≠ color a e (p ++ y)
  have short {p : Word α} (h : Mixed p) : p.length < N := by
    obtain ⟨x, y, hx, hy, _, _, hne⟩ := h
    by_contra! hh
    exact hne ((hN p x hh hx).trans (hN p y hh hy).symm)
  have root : Mixed [] := by simpa [Mixed] using long_colors a e N
  let P (k : ℕ) := ∃ p : Word α, p.length = k ∧ Mixed p
  have h0 : P 0 := ⟨[], rfl, root⟩
  obtain ⟨t, ht, hmix⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le N) h0
  have hlen := short hmix
  have maximal (l : Letter α) : ¬ Mixed (t ++ [l]) := by
    intro hh
    have := Nat.le_findGreatest (P := P) (Nat.le_of_lt (short hh))
      (show P (t ++ [l]).length from ⟨_, rfl, hh⟩)
    simp only [List.length_append, List.length_singleton] at this
    omega
  obtain ⟨x, y, hx, hy, hxl, hyl, hxy⟩ := hmix
  cases x with
  | nil => simp_all
  | cons b x =>
    cases y with
    | nil => simp_all
    | cons c y =>
      have uniq (l : Letter α) (x y : Word α)
          (hx : IsReduced (t ++ l :: x)) (hy : IsReduced (t ++ l :: y))
          (hl : N ≤ (t ++ l :: x).length) (hr : N ≤ (t ++ l :: y).length) :
          color a e (t ++ l :: x) = color a e (t ++ l :: y) := by
        by_contra hn
        apply maximal l
        exact ⟨x, y, by simpa using hx, by simpa using hy, by simpa using hl, by simpa using hr,
          by simpa using hn⟩
      refine ⟨N, t, b, c, ?_, ?_, ?_, ?_⟩
      · rintro rfl
        exact hxy (uniq _ _ _ hx hy hxl hyl)
      · exact hx.infix ⟨[], x, by simp⟩
      · exact hy.infix ⟨[], y, by simp⟩
      · intro v w hv hw hrv hrw
        rwa [uniq b v x hrv hx (by simp; omega) hxl,
          uniq c w y hrw hy (by simp; omega) hyl]

section Tiles
omit [DecidableEq α]

private theorem compatible_iff (x y : Letter α) :
    (x.1 = y.1 → x.2 = y.2) ↔ x ≠ flip y := by
  obtain ⟨i, b⟩ := x
  obtain ⟨j, c⟩ := y
  cases b <;> cases c <;> simp [flip]

-- Each tile starts and ends with the same positive letter, so tiles can be concatenated.
private def Tile (z : Letter α) (w : Word α) : Prop :=
  IsReduced w ∧ w.head? = some z ∧ w.getLast? = some z

private theorem tile_single (z : Letter α) : Tile z [z] :=
  ⟨IsReduced.singleton, rfl, rfl⟩

private theorem tile_append {z : Letter α} {v w : Word α} (hv : Tile z v) (hw : Tile z w) :
    Tile z (v ++ w) := by
  obtain ⟨hr, hf, hl⟩ := hv
  obtain ⟨hs, hg, hm⟩ := hw
  have hv : v ≠ [] := by rintro rfl; simp at hf
  have hw : w ≠ [] := by rintro rfl; simp at hg
  refine ⟨List.IsChain.append hr hs ?_, ?_, ?_⟩
  · simp [hl, hg]
  · simpa [List.head?_append_of_ne_nil _ hv] using hf
  · simpa [List.getLast?_append_of_ne_nil _ hw] using hm

private theorem tile_cyclic {z : Letter α} {w : Word α} (h : Tile z w) : IsCyclicallyReduced w :=
  ⟨h.1, by simp [h.2.1, h.2.2]⟩

private def HasTurn (w : Word α) (b c : Letter α) := [flip b, c] <:+: w

private theorem tile_turn {r : ℕ} (hr : 2 ≤ r) (z b c : Letter (Fin r)) (hbc : b ≠ c) :
    ∃ w, Tile z w ∧ HasTurn w b c := by
  classical
  have spare (x y : Letter (Fin r)) : ∃ d : Letter (Fin r), d ≠ x ∧ d ≠ y := by
    have h : ({x, y} : Finset (Letter (Fin r))).card <
        (Finset.univ : Finset (Letter (Fin r))).card := by
      have := Finset.card_insert_le x ({y} : Finset _)
      simp only [Finset.card_singleton] at this
      simp
      omega
    obtain ⟨d, _, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card h
    exact ⟨d, by simpa using hd⟩
  obtain ⟨d, hd, hb⟩ := spare (flip z) b
  obtain ⟨f, hc, hf⟩ := spare (flip c) (flip z)
  refine ⟨[z, d, flip b, c, f, z], ⟨?_, rfl, rfl⟩, ⟨[z, d], [f, z], rfl⟩⟩
  simp only [isReduced_cons_cons, IsReduced.singleton, and_true]
  have flip_ne (x y : Letter (Fin r)) : x ≠ flip y ↔ y ≠ flip x := by
    obtain ⟨i, a⟩ := x
    obtain ⟨j, b⟩ := y
    cases a <;> cases b <;> simp [flip, eq_comm]
  refine ⟨(compatible_iff _ _).2 ((flip_ne _ _).mpr hd), (compatible_iff d (flip b)).2 ?_,
    (compatible_iff (flip b) c).2 ?_, (compatible_iff _ _).2 ((flip_ne _ _).mpr hc),
    (compatible_iff _ _).2 hf⟩
  · simpa only [flip, Bool.not_not, Prod.mk.eta] using hb
  · intro he
    exact hbc (by simpa [flip] using congrArg flip he)

private theorem universal_tile (r : ℕ) (hr : 1 ≤ r) :
    ∃ w : Word (Fin r), IsCyclicallyReduced w ∧
      ∀ b c, b ≠ c → HasTurn w b c ∨ HasTurn w c b := by
  classical
  let z : Letter (Fin r) := (⟨0, hr⟩, true)
  by_cases h : 2 ≤ r
  · let Good (s : Finset (Letter (Fin r) × Letter (Fin r))) :=
      ∃ w, Tile z w ∧ ∀ p ∈ s, p.1 ≠ p.2 → HasTurn w p.1 p.2
    have all (s) : Good s := by
      induction s using Finset.induction_on with
      | empty => exact ⟨[z], tile_single z, by simp⟩
      | insert p s _ ih =>
        obtain ⟨v, hv, hvs⟩ := ih
        by_cases hp : p.1 = p.2
        · exact ⟨v, hv, by simpa [hp] using hvs⟩
        obtain ⟨w, hw, ht⟩ := tile_turn h z p.1 p.2 hp
        refine ⟨v ++ w, tile_append hv hw, ?_⟩
        intro q hq hne
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact ht.trans (List.suffix_append v w).isInfix
        · exact (hvs q hq hne).trans (List.prefix_append v w).isInfix
    obtain ⟨w, hw, hall⟩ := all Finset.univ
    exact ⟨w, tile_cyclic hw, fun b c hn => Or.inl (hall (b, c) (by simp) hn)⟩
  · obtain rfl : r = 1 := by omega
    refine ⟨[z, z], tile_cyclic (tile_append (tile_single z) (tile_single z)), ?_⟩
    rintro ⟨i, a⟩ ⟨j, b⟩ hn
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    cases a <;> cases b <;> simp_all [HasTurn, flip, z]

end Tiles

private abbrev copies (w : Word α) (n : ℕ) := (List.replicate n w).flatten

omit [DecidableEq α] in
private theorem copies_length (w : Word α) (n : ℕ) : (copies w n).length = n * w.length := by
  simp [copies, List.length_flatten]

omit [DecidableEq α] in
private theorem copies_split (w : Word α) {i j n : ℕ} (h : i + 1 + j = n) :
    copies w n = copies w i ++ w ++ copies w j := by
  subst n
  simp [copies, List.replicate_add, List.append_assoc]

private def originAt (t x : Word α) (b : Letter α) : FreeGroup α :=
  mk t * (mk (x ++ [flip b]))⁻¹

-- Translating the turn to the branching vertex puts its two ends on opposite sides.
private theorem turn_crosses {a : α} {e : MulAut (FreeGroup α)} {N : ℕ} {t x y : Word α}
    {b c : Letter α} (hb : IsReduced (t ++ [b])) (hc : IsReduced (t ++ [c]))
    (hop : Opposed a e N t b c) (hx : N ≤ x.length) (hy : N ≤ y.length)
    (hr : IsReduced (x ++ flip b :: c :: y)) :
    side a (e.symm (originAt t x b)) ≠
      side a (e.symm (originAt t x b * mk (x ++ flip b :: c :: y))) := by
  have hleft : IsReduced (x ++ [flip b]) := hr.infix ⟨[], c :: y, by simp⟩
  have hright : IsReduced (c :: y) := hr.infix ⟨x ++ [flip b], [], by simp⟩
  have hinv : invRev (x ++ [flip b]) = b :: invRev x := by
    simp [invRev, flip]
  have hrev : IsReduced (b :: invRev x) := by
    rw [← hinv]
    exact .of_reduce_eq (by rw [reduce_invRev, hleft.reduce_eq])
  have hstart : originAt t x b = mk (t ++ b :: invRev x) := by
    rw [originAt, inv_mk, hinv, mul_mk]
  have hfinish : originAt t x b * mk (x ++ flip b :: c :: y) = mk (t ++ c :: y) := by
    change (mk t * (mk (x ++ [flip b]))⁻¹) * mk (x ++ flip b :: c :: y) = _
    rw [show mk (x ++ flip b :: c :: y) = mk (x ++ [flip b]) * mk (c :: y) by
      simp [mul_mk],
      mul_assoc, inv_mul_cancel_left, mul_mk]
  rw [hfinish, hstart]
  exact hop _ _ (by simpa using hx) hy
    (by simpa using IsReduced.append_overlap hb (L₃ := invRev x) hrev (by simp))
    (by simpa using IsReduced.append_overlap hc (L₃ := y) hright (by simp))

-- Distinct positions in a reduced word give distinct translates of its path.
omit [DecidableEq α] in
private theorem originAt_inj_length {t x y : Word α} {b : Letter α}
    (hx : IsReduced (x ++ [flip b])) (hy : IsReduced (y ++ [flip b]))
    (h : originAt t x b = originAt t y b) : x.length = y.length := by
  classical
  have he : mk (x ++ [flip b]) = mk (y ++ [flip b]) :=
    inv_injective (mul_left_cancel (by exact h : mk t * _ = mk t * _))
  simpa only [toWord_mk, hx.reduce_eq, hy.reduce_eq, List.length_append,
    Nat.add_right_cancel_iff] using congrArg (fun g => g.toWord.length) he

-- In the middle n periods, each of the k tiles supplies a distinct crossing.
private theorem period_bound {a : α} {e : MulAut (FreeGroup α)} {N k n : ℕ}
    {t v L R A B : Word α} {b c : Letter α} (u : FreeGroup α)
    (hb : IsReduced (t ++ [b])) (hc : IsReduced (t ++ [c])) (hop : Opposed a e N t b c)
    (hv : L ++ [flip b, c] ++ R = v) (hk : 0 < k)
    (hword : A ++ copies v k ++ B = (e u).toWord) (hcyc : IsCyclicallyReduced (e u).toWord) :
    n * k ≤ 2 * ((N + n + N) * u.toWord.length) := by
  classical
  let w := (e u).toWord
  let m := N + n + N
  have vpos : 0 < v.length := by simp [← hv]
  have wlen : w.length = A.length + k * v.length + B.length := by
    simp [w, ← hword, Nat.add_assoc]
  have wpos : 0 < w.length := by have := Nat.mul_pos hk vpos; omega
  -- The first and last N periods leave long extensions at both ends of each chosen turn.
  let before (j : Fin n) (i : Fin k) := copies w (N + j) ++ A ++ copies v i ++ L
  let after (j : Fin n) (i : Fin k) := R ++ copies v (k - 1 - i) ++ B ++ copies w (n - 1 - j + N)
  have splitAt (j : Fin n) (i : Fin k) :
      copies w m = before j i ++ flip b :: c :: after j i := by
    have hw := copies_split w (i := N + j.val) (j := n - 1 - j.val + N) (n := m) (by
      dsimp [m]; omega)
    have ht := copies_split v (i := i.val) (j := k - 1 - i.val) (n := k) (by omega)
    calc
      copies w m = copies w (N + j) ++ (A ++ (copies v i ++ v ++ copies v (k - 1 - i)) ++ B)
          ++ copies w (n - 1 - j + N) := by
        rw [← ht, hword]
        exact hw
      _ = _ := by
        simp only [before, after, ← hv, List.append_assoc, List.cons_append, List.nil_append]
  have red (j : Fin n) (i : Fin k) : IsReduced (before j i ++ flip b :: c :: after j i) :=
    splitAt j i ▸ (hcyc.flatten_replicate m).1
  obtain ⟨s, hs, hcross⟩ := crossings a (copies u.toWord m)
  have prod_eq : e.symm (mk (copies w m)) = mk (copies u.toWord m) := by
    simp only [copies, ← pow_mk, w, mk_toWord, _root_.map_pow, MulEquiv.symm_apply_apply]
  let f (p : Fin n × Fin k) := e.symm (originAt t (before p.1 p.2) b)
  have mem (p : Fin n × Fin k) : f p ∈ s := by
    obtain ⟨j, i⟩ := p
    apply hcross
    rw [← prod_eq, ← e.symm.map_mul, splitAt j i]
    apply turn_crosses hb hc hop _ _ (red j i)
    · have h := Nat.mul_le_mul_left (N + j.val) wpos
      simp [before]
      omega
    · have h := Nat.mul_le_mul_left (n - 1 - j.val + N) wpos
      simp [after]
      omega
  have off (i : Fin k) : A.length + i * v.length + L.length < w.length := by
    have := Nat.mul_le_mul_right v.length i.isLt
    rw [Nat.succ_mul] at this
    have hL : L.length < v.length := by simp [← hv]
    omega
  -- Dividing a prefix length by the period length recovers its period index.
  have inj : Function.Injective f := by
    rintro ⟨j, i⟩ ⟨j', i'⟩ h
    have pr (j : Fin n) (i : Fin k) : IsReduced (before j i ++ [flip b]) :=
      (red j i).infix ⟨[], c :: after j i, by simp⟩
    have he := originAt_inj_length (pr j i) (pr j' i') (e.symm.injective h)
    let offset (i : Fin k) := A.length + i * v.length + L.length
    have heq : w.length * (N + j) + offset i = w.length * (N + j') + offset i' := by
      simpa only [before, List.length_append, copies_length, Nat.add_assoc, offset,
        Nat.mul_comm (N + _) w.length] using he
    have hj := congrArg (· / w.length) heq
    have ho (p : Fin k) : offset p / w.length = 0 := Nat.div_eq_of_lt (off p)
    simp only [Nat.mul_add_div wpos, ho, Nat.add_zero,
      Nat.add_left_cancel_iff] at hj
    obtain rfl : j = j' := Fin.ext hj
    have hi : i.val * v.length = i'.val * v.length := by simpa [offset] using heq
    obtain rfl : i = i' := Fin.ext (Nat.eq_of_mul_eq_mul_right vpos hi)
    rfl
  have bound := Fintype.card_le_of_injective (fun p => (⟨f p, mem p⟩ : s))
    (fun _ _ h => inj (congrArg Subtype.val h))
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at bound
  exact bound.trans (by simpa [copies_length, m] using hs)

/--
**Orbit-blocking words exist (Kourovka Problem 20.88).** For every $r \ge 1$ and every element $u$
of the free group $F_r$ on $r$ generators there is $v \in F_r$ such that, for every automorphism
$\varphi$ of $F_r$ for which the reduced word of $\varphi(u)$ is cyclically reduced, the reduced
word of $v$ is not a subword (a contiguous factor) of the reduced word of $\varphi(u)$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.88 (V. Shpilrain); resolution: L.
Koch-Hyde, S. O'Connor, É. Olive and V. Shpilrain, Orbit-blocking words in free groups, preprint,
arXiv:2505.00477 (2025), Theorem 6.1 and Section 6: for every w ∈ F_r there are w-orbit-blocking
words, i.e. words v that are not subwords of the cyclic reduction of φ(w) for any automorphism φ
(built from primitivity-blocking words such as x₁² ⋯ x_r² x₁); Kourovka Notebook (21st issue),
Problem 20.88: Yes, it is true, https://arxiv.org/abs/2505.00477.
-/
public theorem existsOrbitBlockingWord_holds : existsOrbitBlockingWord := by
  intro r hr u
  obtain ⟨v, hv, hturn⟩ := universal_tile r hr
  let k := 2 * u.toWord.length + 1
  refine ⟨mk (copies v k), ?_⟩
  intro e hcyc hin
  rw [toWord_mk, (hv.flatten_replicate k).1.reduce_eq] at hin
  obtain ⟨A, B, hword⟩ := hin
  let a : Fin r := ⟨0, hr⟩
  obtain ⟨N, t, b, c, hbc, hb, hc, hcones⟩ := opposed_cones a e
  have impossible {d f : Letter (Fin r)} (hd : IsReduced (t ++ [d]))
      (hf : IsReduced (t ++ [f])) (ho : Opposed a e N t d f) (ht : HasTurn v d f) : False := by
    obtain ⟨L, R, he⟩ := ht
    have h := period_bound (n := 4 * N * u.toWord.length + 1) u hd hf ho he
      (by dsimp [k]; omega) hword hcyc
    dsimp [k] at h
    nlinarith only [h]
  rcases hturn b c hbc with h | h
  · exact impossible hb hc hcones h
  · exact impossible hc hb (fun x y hx hy h₁ h₂ => (hcones y x hy hx h₂ h₁).symm) h

end MathlibExt.GroupTheory.OrbitBlockingWordKourovka20Problem88Wanted
