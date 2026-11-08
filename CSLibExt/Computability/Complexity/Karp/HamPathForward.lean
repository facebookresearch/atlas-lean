/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPath

/-!
# SAT ≤ HAMPATH: the forward direction

Component of the SAT ≤ HAMPATH reduction specified in
`CSLibExt.Computability.Complexity.Karp.HamPath` (Sipser, Theorem 7.46): a satisfiable formula
gives a Hamiltonian path of its construction, `exists_isHamPath_of_cnfSat`.

Fix a satisfying assignment `σ` and, for every clause `j`, a diamond `c j` whose variable has a
literal of clause `j` true under `σ`. The path visits the diamonds in order. Diamond `i` runs its
row left to right when `σ` makes its variable true and right to left otherwise, and it picks up
every clause `j` with `c j = i` between the two vertices of the pair of `j`.

* `hfRow m i c`: the row of diamond `i` left to right, with clause `j` inserted after
  `hpR m i (3 j + 1)` when `c j = i`. A right-to-left traversal is its reverse: the reversed row
  visits `hpR m i (3 j + 2)`, `j`, `hpR m i (3 j + 1)`, the detour of a negative literal.
* `hfPath m k c d`: the path through `k` diamonds, `d i` the direction of diamond `i`.
* `hfPath_perm`: `hfPath` lists `0, …, hpT m k` once each, when `c` sends every clause to a
  diamond; this gives `Nodup`, the length and the vertex bounds.
* `isChain_hfPath`, `isChain_hfDiamond`, `isChain_hfRow`: consecutive vertices are related by
  any relation that holds on the frame, row and detour arcs used.
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL
open scoped List

/-! ### The path -/

/-- The row of diamond `i` left to right, with clause `j` inserted right after
`hpR m i (3 j + 1)` when `c j = i`. -/
def hfRow (m i : ℕ) (c : ℕ → ℕ) : List ℕ :=
  (List.range (3 * m + 1)).flatMap fun l =>
    hpR m i l :: if l % 3 = 1 ∧ c (l / 3) = i then [l / 3] else []

/-- The clause vertices of `hfRow m i c`, in row order. -/
def hfPicks (m i : ℕ) (c : ℕ → ℕ) : List ℕ :=
  (List.range (3 * m + 1)).flatMap fun l => if l % 3 = 1 ∧ c (l / 3) = i then [l / 3] else []

/-- Diamond `i`: its top, then its row left to right if `b`, right to left otherwise. -/
def hfDiamond (m i : ℕ) (c : ℕ → ℕ) (b : Bool) : List ℕ :=
  hpT m i :: if b then hfRow m i c else (hfRow m i c).reverse

/-- The path through the first `k` diamonds in the directions `d`, ending at `hpT m k`. -/
def hfPath (m k : ℕ) (c : ℕ → ℕ) (d : ℕ → Bool) : List ℕ :=
  (List.range k).flatMap (fun i => hfDiamond m i c (d i)) ++ [hpT m k]

/-! ### Vertex bookkeeping -/

/-- The clause vertices of a row are the clauses sent to its diamond. -/
theorem mem_hfPicks {m i v : ℕ} {c : ℕ → ℕ} : v ∈ hfPicks m i c ↔ v < m ∧ c v = i := by
  simp only [hfPicks, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨l, hl, hv⟩
    split at hv
    · next h =>
      rw [List.mem_singleton] at hv
      subst hv
      exact ⟨by omega, h.2⟩
    · simp at hv
  · rintro ⟨hv, rfl⟩
    have h1 : (3 * v + 1) % 3 = 1 := by omega
    have h2 : (3 * v + 1) / 3 = v := by omega
    exact ⟨3 * v + 1, by omega, by simp [h1, h2]⟩

/-- No clause vertex appears twice in a row. -/
theorem nodup_hfPicks (m i : ℕ) (c : ℕ → ℕ) : (hfPicks m i c).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun l _ => ?_, List.pairwise_lt_range.imp fun {l l'} hll' => ?_⟩
  · split <;> simp
  · intro v hv hv'
    simp only at hv hv'
    split at hv
    · next h =>
      split at hv'
      · next h' =>
        rw [List.mem_singleton] at hv hv'
        omega
      · simp at hv'
    · simp at hv

/-- Over all diamonds, the rows pick up every clause exactly once. -/
theorem flatMap_hfPicks_perm {m k : ℕ} {c : ℕ → ℕ} (hc : ∀ j < m, c j < k) :
    (List.range k).flatMap (fun i => hfPicks m i c) ~ List.range m := by
  refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 fun j => ?_
  · refine List.nodup_flatMap.2 ⟨fun i _ => nodup_hfPicks m i c,
      List.pairwise_lt_range.imp fun {i i'} hii' => ?_⟩
    intro v hv hv'
    rw [mem_hfPicks] at hv hv'
    omega
  · simp only [List.mem_flatMap, List.mem_range, mem_hfPicks]
    constructor
    · rintro ⟨i, -, hj, -⟩
      exact hj
    · intro hj
      exact ⟨c j, hc j hj, hj, rfl⟩

/-- A row is its row vertices followed by its clause vertices, up to order. -/
theorem hfRow_perm (m i : ℕ) (c : ℕ → ℕ) :
    hfRow m i c ~ List.range' (hpR m i 0) (3 * m + 1) ++ hfPicks m i c := by
  have h1 : (List.range (3 * m + 1)).flatMap (fun l => [hpR m i l]) =
      List.range' (hpR m i 0) (3 * m + 1) := by
    rw [← List.map_eq_flatMap, List.range'_eq_map_range]
    rfl
  rw [← h1]
  exact (List.flatMap_append_perm (List.range (3 * m + 1)) (fun l => [hpR m i l])
    fun l => if l % 3 = 1 ∧ c (l / 3) = i then [l / 3] else []).symm

/-- A diamond is a block of consecutive vertices followed by its clause vertices, up to
order. -/
theorem hfDiamond_perm (m i : ℕ) (c : ℕ → ℕ) (b : Bool) :
    hfDiamond m i c b ~ List.range' (hpT m i) (3 * m + 2) ++ hfPicks m i c := by
  have hrow : (if b then hfRow m i c else (hfRow m i c).reverse) ~ hfRow m i c := by
    cases b
    · exact List.reverse_perm _
    · exact List.Perm.refl _
  have h0 : hpR m i 0 = hpT m i + 1 := rfl
  rw [List.range'_succ, ← h0, List.cons_append]
  exact (hrow.trans (hfRow_perm m i c)).cons _

/-- The tops and rows of the first `t` diamonds are the vertices `m, …, hpT m t - 1`. -/
theorem flatMap_range'_hpT (m t : ℕ) :
    (List.range t).flatMap (fun i => List.range' (hpT m i) (3 * m + 2)) =
      List.range' m (t * (3 * m + 2)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton, hpT,
      List.range'_append_1, Nat.add_one_mul t]

/-- The path lists every vertex `0, …, hpT m k` once, when every clause goes to a diamond. -/
theorem hfPath_perm {m k : ℕ} {c : ℕ → ℕ} (d : ℕ → Bool) (hc : ∀ j < m, c j < k) :
    hfPath m k c d ~ List.range (hpT m k + 1) := by
  have h1 : (List.range k).flatMap (fun i => hfDiamond m i c (d i)) ~
      List.range' m (k * (3 * m + 2)) ++ (List.range k).flatMap (fun i => hfPicks m i c) := by
    rw [← flatMap_range'_hpT]
    exact (List.Perm.flatMap_left _ fun i _ => hfDiamond_perm m i c (d i)).trans
      (List.flatMap_append_perm _ _ _).symm
  have h2 : List.range (hpT m k + 1) = List.range m ++ List.range' m (k * (3 * m + 2) + 1) := by
    have h := @List.range'_append_1 0 m (k * (3 * m + 2) + 1)
    rw [Nat.zero_add] at h
    rw [List.range_eq_range', List.range_eq_range', h, hpT, Nat.add_assoc]
  have h3 : List.range' m (k * (3 * m + 2) + 1) = List.range' m (k * (3 * m + 2)) ++ [hpT m k] :=
    List.range'_1_concat
  rw [hfPath, h2, h3]
  calc _ ~ (List.range' m (k * (3 * m + 2)) ++ (List.range k).flatMap (fun i => hfPicks m i c)) ++
          [hpT m k] := h1.append_right _
    _ ~ List.range' m (k * (3 * m + 2)) ++ ([hpT m k] ++
          (List.range k).flatMap (fun i => hfPicks m i c)) := by
        rw [List.append_assoc]
        exact List.Perm.append_left _ List.perm_append_comm
    _ ~ (List.range' m (k * (3 * m + 2)) ++ [hpT m k]) ++ List.range m := by
        rw [← List.append_assoc]
        exact List.Perm.append_left _ (flatMap_hfPicks_perm hc)
    _ ~ _ := List.perm_append_comm

/-! ### Arcs along the path -/

/-- The row is a chain for any relation holding on its forward row arcs and on the detours
`hpR m i (3 j + 1) → j → hpR m i (3 j + 2)` of the clauses `j` sent to diamond `i`. -/
theorem isChain_hfRow {R : ℕ → ℕ → Prop} {m i : ℕ} {c : ℕ → ℕ}
    (hrow : ∀ l < 3 * m, R (hpR m i l) (hpR m i (l + 1)))
    (hdet : ∀ j < m, c j = i → R (hpR m i (3 * j + 1)) j ∧ R j (hpR m i (3 * j + 2))) :
    (hfRow m i c).IsChain R := by
  unfold hfRow
  rw [List.flatMap_def, List.isChain_flatten (by simp), List.isChain_map, List.isChain_range]
  refine ⟨?_, fun l hl => ?_⟩
  · simp only [List.mem_map, List.mem_range]
    rintro _ ⟨l, hl, rfl⟩
    split
    · next h =>
      obtain ⟨j, rfl⟩ : ∃ j, l = 3 * j + 1 := ⟨l / 3, by omega⟩
      have hj : (3 * j + 1) / 3 = j := by omega
      rw [hj] at h ⊢
      exact List.isChain_pair.2 (hdet j (by omega) h.2).1
    · exact List.isChain_singleton _
  · simp only [Nat.add_sub_cancel] at hl
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq', Nat.succ_eq_add_one]
    split
    · next h =>
      obtain ⟨j, rfl⟩ : ∃ j, l = 3 * j + 1 := ⟨l / 3, by omega⟩
      have hj : (3 * j + 1) / 3 = j := by omega
      rw [hj] at h ⊢
      simpa using (hdet j (by omega) h.2).2
    · simpa using hrow l hl

/-- The row starts at its left end. -/
theorem head?_hfRow (m i : ℕ) (c : ℕ → ℕ) : (hfRow m i c).head? = some (hpR m i 0) := by
  simp [hfRow, List.range_succ_eq_map]

/-- The row ends at its right end. -/
theorem getLast?_hfRow (m i : ℕ) (c : ℕ → ℕ) :
    (hfRow m i c).getLast? = some (hpR m i (3 * m)) := by
  simp [hfRow, List.range_succ]

/-- A diamond followed by the next top is a chain for any relation holding on the frame arcs,
the row arcs in both directions, and the detours of its direction. -/
theorem isChain_hfDiamond {R : ℕ → ℕ → Prop} {m i : ℕ} {c : ℕ → ℕ} {b : Bool}
    (hT0 : R (hpT m i) (hpR m i 0)) (hT3 : R (hpT m i) (hpR m i (3 * m)))
    (hB0 : R (hpR m i 0) (hpT m (i + 1))) (hB3 : R (hpR m i (3 * m)) (hpT m (i + 1)))
    (hrow : ∀ l < 3 * m, R (hpR m i l) (hpR m i (l + 1)) ∧ R (hpR m i (l + 1)) (hpR m i l))
    (hpos : b = true → ∀ j < m, c j = i →
      R (hpR m i (3 * j + 1)) j ∧ R j (hpR m i (3 * j + 2)))
    (hneg : b = false → ∀ j < m, c j = i →
      R (hpR m i (3 * j + 2)) j ∧ R j (hpR m i (3 * j + 1))) :
    (hfDiamond m i c b ++ [hpT m (i + 1)]).IsChain R := by
  rw [hfDiamond, List.cons_append, List.isChain_cons, List.isChain_append]
  cases b
  · simp only [Bool.false_eq_true, ite_false, List.head?_append, List.head?_reverse,
      getLast?_hfRow, List.getLast?_reverse, head?_hfRow, Option.some_or, Option.mem_def,
      Option.some.injEq, forall_eq', List.head?_cons, List.isChain_singleton, true_and]
    refine ⟨hT3, List.isChain_reverse.2 (isChain_hfRow (fun l hl => (hrow l hl).2) ?_), hB0⟩
    intro j hj hcj
    exact ⟨(hneg rfl j hj hcj).2, (hneg rfl j hj hcj).1⟩
  · simp only [ite_true, List.head?_append, getLast?_hfRow, head?_hfRow, Option.some_or,
      Option.mem_def, Option.some.injEq, forall_eq', List.head?_cons, List.isChain_singleton,
      true_and]
    exact ⟨hT0, isChain_hfRow (fun l hl => (hrow l hl).1) (hpos rfl), hB3⟩

/-- The path is a chain when every diamond followed by the next top is. -/
theorem isChain_hfPath {R : ℕ → ℕ → Prop} {m k : ℕ} {c : ℕ → ℕ} {d : ℕ → Bool}
    (hD : ∀ i < k, (hfDiamond m i c (d i) ++ [hpT m (i + 1)]).IsChain R) :
    (hfPath m k c d).IsChain R := by
  induction k with
  | zero => simp [hfPath]
  | succ t ih =>
    have h1 := List.isChain_append.1 (ih fun i hi => hD i (by omega))
    rw [hfPath, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine List.isChain_append.2 ⟨h1.1, hD t (by omega), fun x hx y hy => ?_⟩
    simp only [hfDiamond, List.cons_append, List.head?_cons, Option.mem_def,
      Option.some.injEq] at hy
    subst hy
    exact h1.2.2 x hx _ rfl

/-- The path starts at the first top. -/
theorem head?_hfPath (m k : ℕ) (c : ℕ → ℕ) (d : ℕ → Bool) :
    (hfPath m k c d).head? = some (hpT m 0) := by
  cases k with
  | zero => simp [hfPath]
  | succ k => simp [hfPath, List.range_succ_eq_map, hfDiamond]

/-- The path ends at the last top. -/
theorem getLast?_hfPath (m k : ℕ) (c : ℕ → ℕ) (d : ℕ → Bool) :
    (hfPath m k c d).getLast? = some (hpT m k) := by
  simp [hfPath]

/-! ### The arcs of the construction -/

/-- An arc of a diamond of the construction is an arc of the construction. -/
theorem mem_hamEdges_of_mem_diamondEdges {φ : CNF} {e : ℕ × ℕ} {i : ℕ} (hi : i < (hamVars φ).length)
    (h : e ∈ diamondEdges φ i ((hamVars φ).getD i 0)) : e ∈ hamEdges φ :=
  List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, h⟩

/-- The four frame arcs of a diamond. -/
theorem mem_diamondEdges_frame (φ : CNF) (i x : ℕ) :
    (hpT φ.length i, hpR φ.length i 0) ∈ diamondEdges φ i x ∧
      (hpT φ.length i, hpR φ.length i (3 * φ.length)) ∈ diamondEdges φ i x ∧
      (hpR φ.length i 0, hpT φ.length (i + 1)) ∈ diamondEdges φ i x ∧
      (hpR φ.length i (3 * φ.length), hpT φ.length (i + 1)) ∈ diamondEdges φ i x := by
  simp [diamondEdges]

/-- The row arcs of a diamond, in both directions. -/
theorem mem_diamondEdges_row (φ : CNF) (i x : ℕ) {l : ℕ} (hl : l < 3 * φ.length) :
    (hpR φ.length i l, hpR φ.length i (l + 1)) ∈ diamondEdges φ i x ∧
      (hpR φ.length i (l + 1), hpR φ.length i l) ∈ diamondEdges φ i x := by
  simp only [diamondEdges]
  constructor <;>
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨l, List.mem_range.2 hl, by simp⟩))

/-- The detour of a positive occurrence: `hpR (3 j + 1) → j → hpR (3 j + 2)`. -/
theorem mem_diamondEdges_pos {φ : CNF} {i x j : ℕ} (hj : j < φ.length)
    (h : (x, true) ∈ φ.getD j []) :
    (hpR φ.length i (3 * j + 1), j) ∈ diamondEdges φ i x ∧
      (j, hpR φ.length i (3 * j + 2)) ∈ diamondEdges φ i x := by
  simp only [diamondEdges]
  constructor <;>
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, by
      simp only [h, ↓reduceIte]
      simp⟩)

/-- The detour of a negative occurrence: `hpR (3 j + 2) → j → hpR (3 j + 1)`. -/
theorem mem_diamondEdges_neg {φ : CNF} {i x j : ℕ} (hj : j < φ.length)
    (h : (x, false) ∈ φ.getD j []) :
    (hpR φ.length i (3 * j + 2), j) ∈ diamondEdges φ i x ∧
      (j, hpR φ.length i (3 * j + 1)) ∈ diamondEdges φ i x := by
  simp only [diamondEdges]
  constructor <;>
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, by
      simp only [h, ↓reduceIte]
      simp⟩)

/-! ### The forward direction -/

/-- The path for an assignment `σ` and a clause-to-diamond choice `c` (each clause `j` goes to a
diamond whose variable, valued by `σ`, is a literal of clause `j`) is Hamiltonian. -/
theorem isHamPath_hfPath {φ : CNF} {σ : ℕ → Bool} {c : ℕ → ℕ}
    (hc : ∀ j < φ.length, c j < (hamVars φ).length ∧
      ((hamVars φ).getD (c j) 0, σ ((hamVars φ).getD (c j) 0)) ∈ φ.getD j []) :
    IsHamPath (hpT φ.length (hamVars φ).length + 1) (hamEdges φ) (hpT φ.length 0)
      (hpT φ.length (hamVars φ).length)
      (hfPath φ.length (hamVars φ).length c fun i => σ ((hamVars φ).getD i 0)) := by
  have hp := hfPath_perm (fun i => σ ((hamVars φ).getD i 0)) fun j hj => (hc j hj).1
  refine ⟨hp.nodup_iff.2 List.nodup_range, hp.length_eq.trans List.length_range,
    fun v hv => List.mem_range.1 (hp.subset hv), head?_hfPath .., getLast?_hfPath .., ?_⟩
  refine isChain_hfPath fun i hi => ?_
  have hTk : ∀ i' ≤ (hamVars φ).length,
      hpT φ.length i' < hpT φ.length (hamVars φ).length + 1 :=
    fun i' hi' => Nat.lt_succ_of_le (hpT_mono hi')
  have hR : ∀ l ≤ 3 * φ.length, hpR φ.length i l < hpT φ.length (hamVars φ).length + 1 :=
    fun l hl => (hpR_lt_hpT_succ hl).trans (hTk _ hi)
  have hJ : ∀ j < φ.length, j < hpT φ.length (hamVars φ).length + 1 := fun j hj =>
    hj.trans_le ((Nat.le_add_right _ _).trans (hTk _ (Nat.zero_le _)).le)
  have arc : ∀ {u v}, (u, v) ∈ diamondEdges φ i ((hamVars φ).getD i 0) →
      u < hpT φ.length (hamVars φ).length + 1 → v < hpT φ.length (hamVars φ).length + 1 →
      Path.arc (hpT φ.length (hamVars φ).length + 1) (hamEdges φ) u v :=
    fun h hu hv => ⟨mem_hamEdges_of_mem_diamondEdges hi h, hu, hv⟩
  obtain ⟨f1, f2, f3, f4⟩ := mem_diamondEdges_frame φ i ((hamVars φ).getD i 0)
  refine isChain_hfDiamond (arc f1 (hTk i hi.le) (hR 0 (Nat.zero_le _)))
    (arc f2 (hTk i hi.le) (hR _ le_rfl)) (arc f3 (hR 0 (Nat.zero_le _)) (hTk _ hi))
    (arc f4 (hR _ le_rfl) (hTk _ hi)) (fun l hl => ?_) (fun hb j hj hcj => ?_)
    (fun hb j hj hcj => ?_)
  · obtain ⟨e1, e2⟩ := mem_diamondEdges_row φ i ((hamVars φ).getD i 0) hl
    exact ⟨arc e1 (hR l (by omega)) (hR (l + 1) (by omega)),
      arc e2 (hR (l + 1) (by omega)) (hR l (by omega))⟩
  · have hmem := (hc j hj).2
    rw [hcj, hb] at hmem
    obtain ⟨e1, e2⟩ := mem_diamondEdges_pos (i := i) hj hmem
    exact ⟨arc e1 (hR _ (by omega)) (hJ j hj), arc e2 (hJ j hj) (hR _ (by omega))⟩
  · have hmem := (hc j hj).2
    rw [hcj, hb] at hmem
    obtain ⟨e1, e2⟩ := mem_diamondEdges_neg (i := i) hj hmem
    exact ⟨arc e1 (hR _ (by omega)) (hJ j hj), arc e2 (hJ j hj) (hR _ (by omega))⟩

/-- Forward direction of SAT ≤ HAMPATH: a satisfiable formula yields a Hamiltonian path of
its construction. -/
theorem exists_isHamPath_of_cnfSat {φ : CNF} (h : CNFSat φ) :
    ∃ p, IsHamPath (hpT φ.length (hamVars φ).length + 1) (hamEdges φ)
      (hpT φ.length 0) (hpT φ.length (hamVars φ).length) p := by
  obtain ⟨σ, hσ⟩ := h
  have hex : ∀ j, ∃ i, j < φ.length → i < (hamVars φ).length ∧
      ((hamVars φ).getD i 0, σ ((hamVars φ).getD i 0)) ∈ φ.getD j [] := by
    intro j
    by_cases hj : j < φ.length
    · have hC : φ.getD j [] ∈ φ := by
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      obtain ⟨x, b, hxb, hσx⟩ := hσ _ hC
      obtain ⟨i, hi, hx⟩ : ∃ i, ∃ h : i < (hamVars φ).length, (hamVars φ)[i] = x :=
        List.mem_iff_getElem.1 (List.mem_dedup.2 (mem_varsOf hxb hC))
      refine ⟨i, fun _ => ⟨hi, ?_⟩⟩
      rw [List.getD_eq_getElem _ _ hi, hx, hσx]
      exact hxb
    · exact ⟨0, fun h => absurd h hj⟩
  choose c hc using hex
  exact ⟨_, isHamPath_hfPath fun j hj => hc j hj⟩

end Cslib.Complexity.Karp
