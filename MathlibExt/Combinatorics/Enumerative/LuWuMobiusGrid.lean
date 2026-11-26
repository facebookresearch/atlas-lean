/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Finset.Sort
import Mathlib.FieldTheory.KummerExtension
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Lu–Wu formula for perfect matchings of the Möbius grid

This file defines the $2M \times N$ Möbius grid: its vertices are the pairs $(a, b)$ with
$a < 2M$ and $b < N$, its edges are the horizontal and vertical edges of the grid and the seam
edges joining $(i, N - 1)$ to $(2M - 1 - i, 0)$, and its perfect matchings are counted as sets
of labeled edges. The main result, `MetaMathlibExt.lu_wu_mobius_grid_perfect_matching_count`,
is the Lu–Wu formula: for $M \ge 1$ and odd $N$ the number of perfect matchings is
$\operatorname{Re}\big[(1 - i) \prod_{s=1}^{M} \prod_{r=1}^{N}
\big(2i(-1)^{M+s+1} \sin\frac{(4r-1)\pi}{2N} + 2\cos\frac{s\pi}{2M+1}\big)\big]$.

## Proof

The proof is a transfer-matrix argument rather than the Pfaffian method of the source.

1. A perfect matching is determined by the rows whose horizontal or seam edge it uses in each
   gap between consecutive columns; the vertical edges of each column are then determined.
2. Complement these crossing sets on one colour class of each column (the grid is bipartite
   because $N$ is odd). The number of ways to complete a column is then the minor of the
   $2M \times 2M$ matrix $X = 1 + H$ with rows and columns given by the two crossing sets,
   where $H$ lets a particle on a white row hop to an adjacent row.
3. The Cauchy–Binet formula turns the sum over all crossing sets into
   $\sum_K (-1)^{|K|(|K|-1)/2} \det (Q^N)_{K,K}$, where $Q = PX$ and $P$ reverses the rows;
   the sign comes from the reversal in the seam. Since
   $(-1)^{k(k-1)/2} = \operatorname{Re}[(1 - i) i^k]$, the sum of principal minors gives
   $\operatorname{Re}[(1 - i) \det(1 + i Q^N)]$.
4. For $1 \le s \le M$, the vectors $a \mapsto c_{a \bmod 2} \sin\frac{s(a+1)\pi}{2M+1}$
   are eigenvectors of $Q$ whose eigenvalues are the roots of
   $\lambda^2 - (-1)^{s+1} 2\cos\frac{s\pi}{2M+1} \lambda - 1$. Factoring $1 + i t^N$ over
   the $N$-th roots of $-i$ gives the product formula.

## Source

Primary source: Wentao T. Lu and F. Y. Wu, "Close-packed dimers on
nonorientable surfaces", arXiv:cond-mat/0110035v3
(<https://arxiv.org/abs/cond-mat/0110035>).
Grid/generating-function display (gen), lines 145-163;
odd-column Mobius-grid formula (Mob-2), lines 184-188;
M-even Mobius-strip setup with grid dimensions (2M, N) and the twisted
adjacency matrix, lines 264-311.
Only the unweighted odd-column Mobius-grid formula is formalized here;
the Klein-bottle and even-N variants are not encoded.
-/

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

/-- **Vertices of the Möbius grid.** For natural numbers $M$ and $N$, the vertices of the
$2M \times N$ Möbius grid are the pairs $(a, b)$ of natural numbers with $a < 2M$ and $b < N$. -/
def MobiusGridVertex (M N : ℕ) : Type :=
  Fin (2 * M) × Fin N

/-- **Edges of the Möbius grid.** For natural numbers $M$ and $N$, the labeled edges of the
$2M \times N$ Möbius grid are of three kinds: a horizontal edge $h(i, j)$ for each row $i < 2M$
and column $j < N - 1$, a vertical edge $v(i, j)$ for each row $i < 2M - 1$ and column $j < N$,
and a seam edge $\sigma(i)$ for each row $i < 2M$.

Edges with different labels are different, even when small dimensions make two of them join the
same pair of vertices; this keeps the edge-labeled dimer multiplicities of the source. -/
inductive MobiusGridEdge (M N : ℕ) where
  | horizontal (row : Fin (2 * M)) (col : Fin (N - 1)) : MobiusGridEdge M N
  | vertical (row : Fin (2 * M - 1)) (col : Fin N) : MobiusGridEdge M N
  | seam (row : Fin (2 * M)) : MobiusGridEdge M N
deriving DecidableEq, Fintype

/-- **Incidence in the Möbius grid.** For natural numbers $M$ and $N$, write a vertex of the
$2M \times N$ Möbius grid as $(a, b)$ with row $a < 2M$ and column $b < N$. The vertex $(a, b)$
is incident to the horizontal edge $h(i, j)$ (with $i < 2M$, $j < N - 1$) exactly when $a = i$
and $b \in \{j, j + 1\}$; to the vertical edge $v(i, j)$ (with $i < 2M - 1$, $j < N$) exactly
when $b = j$ and $a \in \{i, i + 1\}$; and to the seam edge $\sigma(i)$ (with $i < 2M$) exactly
when $(a, b) = (i, N - 1)$ or $(a, b) = (2M - 1 - i, 0)$. -/
def MobiusGridIncident {M N : ℕ} (e : MobiusGridEdge M N)
    (v : MobiusGridVertex M N) : Prop :=
  match e with
  | .horizontal row col =>
      v.1.val = row.val ∧ (v.2.val = col.val ∨ v.2.val = col.val + 1)
  | .vertical row col =>
      v.2.val = col.val ∧ (v.1.val = row.val ∨ v.1.val = row.val + 1)
  | .seam row =>
      (v.1.val = row.val ∧ v.2.val = N - 1) ∨
        (v.1.val = 2 * M - 1 - row.val ∧ v.2.val = 0)

/-- **Perfect matchings of the Möbius grid.** For natural numbers $M$ and $N$, a finite set $S$
of labeled edges of the $2M \times N$ Möbius grid is a perfect matching when every vertex of the
grid is incident to exactly one edge of $S$. -/
def IsMobiusGridPerfectMatching {M N : ℕ}
    (S : Finset (MobiusGridEdge M N)) : Prop :=
  ∀ v : MobiusGridVertex M N, ∃! e, e ∈ S ∧ MobiusGridIncident e v

/-- **Number of perfect matchings of the Möbius grid.** For natural numbers $M$ and $N$, this is
the number of perfect matchings of the $2M \times N$ Möbius grid, counted as sets of labeled
edges. -/
noncomputable def mobiusGridPerfectMatchingCount (M N : ℕ) : ℕ :=
  by
    classical
    exact Fintype.card
      {S : Finset (MobiusGridEdge M N) //
        IsMobiusGridPerfectMatching (M := M) (N := N) S}

/-! ### Colours, hop matrices, minors and column counts -/

namespace LuWuMobiusGrid

open Finset

/-- White rows of a column of parity `p`: rows `a` with `a + p` odd. -/
private def white (M p : ℕ) : Finset (Fin (2 * M)) := univ.filter (fun a => (a.val + p) % 2 = 1)

/-- Black rows of a column of parity `p`: rows `a` with `a + p` even. -/
private def black (M p : ℕ) : Finset (Fin (2 * M)) := univ.filter (fun a => (a.val + p) % 2 = 0)

/-- The one-column hop matrix `1 + H_p`: a particle on a white row may hop to an adjacent row. -/
private def hopMat (M p : ℕ) : Matrix (Fin (2 * M)) (Fin (2 * M)) ℤ :=
  Matrix.of fun a b => if a = b then 1 else
    if (a.val + p) % 2 = 1 ∧ (b.val = a.val + 1 ∨ a.val = b.val + 1) then 1 else 0

/-- The minor of `A` with rows `I` and columns `J`, both listed in increasing order; it is zero
when `I` and `J` have different sizes. -/
private def minor {n : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R)
    (I J : Finset (Fin n)) : R :=
  if h : J.card = I.card then (A.submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin h)).det else 0

/-- Column condition: each row `a` is covered exactly once, by a left crossing edge (`a ∈ L`),
a right crossing edge (`a ∈ R`) or a vertical edge `i ∈ V` joining rows `i` and `i + 1`. -/
private def ColOK (M : ℕ) (L R : Finset (Fin (2 * M))) (V : Finset (Fin (2 * M - 1))) : Prop :=
  ∀ a : Fin (2 * M), (if a ∈ L then 1 else 0) + (if a ∈ R then 1 else 0) +
    (V.filter (fun i => a.val = i.val ∨ a.val = i.val + 1)).card = 1

private instance instDecidablePredColOK (M : ℕ) (L R : Finset (Fin (2 * M))) :
    DecidablePred (ColOK M L R) := fun V => by
  unfold ColOK; infer_instance

/-- Number of ways to complete a column with crossing sets `L`, `R` by vertical edges. -/
private def colCount (M : ℕ) (L R : Finset (Fin (2 * M))) : ℕ :=
  (univ.filter (fun V : Finset (Fin (2 * M - 1)) => ColOK M L R V)).card

/-- Previous state in a cyclic chain of length `N`; the state before position `0` is `g` of the
last state. -/
private def prevState {ι : Type*} {N : ℕ} (g : ι → ι) (K : Fin N → ι) (c : Fin N) : ι :=
  if h : c.val = 0 then g (K ⟨N - 1, by have := c.isLt; omega⟩)
  else K ⟨c.val - 1, by have := c.isLt; omega⟩

/-- Row reversal of a set of rows. -/
private def revSet {n : ℕ} (S : Finset (Fin n)) : Finset (Fin n) := S.map Fin.revPerm.toEmbedding

/-- The twisted one-column matrix `Q = P (1 + H_0)`, `P` the row reversal. -/
private def Qmat (M : ℕ) : Matrix (Fin (2 * M)) (Fin (2 * M)) ℤ :=
  Matrix.of fun a b => hopMat M 0 (Fin.rev a) b

/-- Sign of the reversal of `n` elements. -/
private def sgnRev (n : ℕ) : ℤ := (-1) ^ (n * (n - 1) / 2)

/-- The compound matrix of `A`: the matrix of all its minors, indexed by sets of rows. -/
private def cpd {n : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) R :=
  Matrix.of fun I J => minor A I J

end LuWuMobiusGrid

/-! ### Perfect matchings as sums of products of column counts -/

namespace LuWuMobiusGrid.Match

open Finset

variable {M N : ℕ}

/-- The crossing edge leaving column `c` to the right at row `a`. -/
private def rightEdge (a : Fin (2 * M)) (c : Fin N) : MobiusGridEdge M N :=
  if h : c.val < N - 1 then .horizontal a ⟨c.val, h⟩ else .seam a

/-- The crossing edge entering column `c` from the left at row `a`. -/
private def leftEdge (a : Fin (2 * M)) (c : Fin N) : MobiusGridEdge M N :=
  if h : c.val = 0 then .seam (Fin.rev a)
  else .horizontal a ⟨c.val - 1, by have := c.isLt; omega⟩

private theorem incident_iff (e : MobiusGridEdge M N) (a : Fin (2 * M)) (c : Fin N) :
    MobiusGridIncident e ((a, c) : MobiusGridVertex M N) ↔
      e = rightEdge a c ∨ e = leftEdge a c ∨
        ∃ i : Fin (2 * M - 1), e = .vertical i c ∧ (a.val = i.val ∨ a.val = i.val + 1) := by
  have hc := c.isLt
  cases e with
  | horizontal r j =>
    have hj := j.isLt
    simp only [MobiusGridIncident, rightEdge, leftEdge]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · left
        rw [dite_eq_left (by omega)]
        simp only [MobiusGridEdge.horizontal.injEq, Fin.ext_iff]
        omega
      · right; left
        rw [dite_eq_right (by omega)]
        simp only [MobiusGridEdge.horizontal.injEq, Fin.ext_iff]
        omega
    · rintro (h | h | ⟨i, h, -⟩)
      · split_ifs at h with h'
        · simp only [MobiusGridEdge.horizontal.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, Or.inl rfl⟩
      · split_ifs at h with h'
        · simp only [MobiusGridEdge.horizontal.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨rfl, Or.inr ?_⟩
          simp only
          omega
      · cases h
  | vertical r j =>
    simp only [MobiusGridIncident, rightEdge, leftEdge]
    constructor
    · rintro ⟨h1, h2⟩
      right; right
      exact ⟨r, by rw [Fin.ext h1.symm], h2⟩
    · rintro (h | h | ⟨i, h, h2⟩)
      · split_ifs at h
      · split_ifs at h
      · simp only [MobiusGridEdge.vertical.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, h2⟩
  | seam r =>
    have hr := r.isLt
    simp only [MobiusGridIncident, rightEdge, leftEdge]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left
        rw [dite_eq_right (by omega)]
        congr 1
        ext
        omega
      · right; left
        rw [dite_eq_left h2]
        congr 1
        ext
        simp only [Fin.val_rev]
        omega
    · rintro (h | h | ⟨i, h, -⟩)
      · split_ifs at h with h'
        simp only [MobiusGridEdge.seam.injEq] at h
        subst h
        exact Or.inl ⟨rfl, by omega⟩
      · split_ifs at h with h'
        simp only [MobiusGridEdge.seam.injEq] at h
        subst h
        refine Or.inr ⟨?_, h'⟩
        simp only [Fin.val_rev]
        omega
      · cases h

/-- Crossing data (per gap) and vertical data (per column) of a set of edges. -/
private def toData (S : Finset (MobiusGridEdge M N)) :
    (Fin N → Finset (Fin (2 * M))) × (Fin N → Finset (Fin (2 * M - 1))) :=
  (fun c => univ.filter (fun a => rightEdge a c ∈ S),
    fun c => univ.filter (fun i => MobiusGridEdge.vertical i c ∈ S))

/-- Membership of an edge in the edge set with given crossing and vertical data. -/
private def edgeMem (hN : 0 < N)
    (p : (Fin N → Finset (Fin (2 * M))) × (Fin N → Finset (Fin (2 * M - 1)))) :
    MobiusGridEdge M N → Prop
  | .horizontal a j => a ∈ p.1 ⟨j.val, by have := j.isLt; omega⟩
  | .vertical i c => i ∈ p.2 c
  | .seam a => a ∈ p.1 ⟨N - 1, by omega⟩

private instance instDecidablePredEdgeMem (hN : 0 < N)
    (p : (Fin N → Finset (Fin (2 * M))) × (Fin N → Finset (Fin (2 * M - 1)))) :
    DecidablePred (edgeMem hN p)
  | .horizontal _ _ => inferInstanceAs (Decidable (_ ∈ _))
  | .vertical _ _ => inferInstanceAs (Decidable (_ ∈ _))
  | .seam _ => inferInstanceAs (Decidable (_ ∈ _))

private theorem rightEdge_of_lt (a : Fin (2 * M)) (c : Fin N) (h : c.val < N - 1) :
    rightEdge a c = .horizontal a ⟨c.val, h⟩ :=
  dite_eq_left h

private theorem rightEdge_of_not_lt (a : Fin (2 * M)) (c : Fin N) (h : ¬c.val < N - 1) :
    rightEdge a c = .seam a :=
  dite_eq_right h

private theorem mem_toData_fst (S : Finset (MobiusGridEdge M N)) (a : Fin (2 * M)) (c : Fin N) :
    a ∈ (toData S).1 c ↔ rightEdge a c ∈ S := by
  simp [toData]

private theorem mem_toData_snd (S : Finset (MobiusGridEdge M N)) (i : Fin (2 * M - 1)) (c : Fin N) :
    i ∈ (toData S).2 c ↔ MobiusGridEdge.vertical i c ∈ S := by
  simp [toData]

/-- Edge sets correspond to crossing and vertical data. -/
private def dataEquiv (hN : 0 < N) :
    Finset (MobiusGridEdge M N) ≃
      (Fin N → Finset (Fin (2 * M))) × (Fin N → Finset (Fin (2 * M - 1))) where
  toFun := toData
  invFun p := univ.filter (edgeMem hN p)
  left_inv S := by
    ext e
    rw [mem_filter]
    simp only [mem_univ, true_and]
    cases e with
    | horizontal a j =>
      change a ∈ (toData S).1 _ ↔ _
      rw [mem_toData_fst, rightEdge_of_lt a _ j.isLt]
    | vertical i c =>
      change i ∈ (toData S).2 c ↔ _
      rw [mem_toData_snd]
    | seam a =>
      change a ∈ (toData S).1 _ ↔ _
      rw [mem_toData_fst, rightEdge_of_not_lt a _ (by simp)]
  right_inv p := by
    ext c a
    · rw [mem_toData_fst, mem_filter]
      simp only [mem_univ, true_and]
      by_cases h : c.val < N - 1
      · rw [rightEdge_of_lt a c h]
        exact Iff.rfl
      · rw [rightEdge_of_not_lt a c h]
        have hc : (⟨N - 1, by omega⟩ : Fin N) = c := by
          ext; simp only; have := c.isLt; omega
        change a ∈ p.1 ⟨N - 1, by omega⟩ ↔ a ∈ p.1 c
        rw [hc]
    · rw [mem_toData_snd, mem_filter]
      simp only [mem_univ, true_and]
      exact Iff.rfl

private theorem leftEdge_ne_rightEdge (a : Fin (2 * M)) (c : Fin N) :
    leftEdge a c ≠ rightEdge a c := by
  unfold leftEdge rightEdge
  split_ifs with h1 h2 h2
  · simp
  · simp only [ne_eq, MobiusGridEdge.seam.injEq, Fin.ext_iff, Fin.val_rev]
    omega
  · simp only [ne_eq, MobiusGridEdge.horizontal.injEq, true_and, Fin.ext_iff]
    omega
  · simp

private theorem rightEdge_mem_iff (S : Finset (MobiusGridEdge M N)) (a : Fin (2 * M)) (c : Fin N) :
    rightEdge a c ∈ S ↔ a ∈ (toData S).1 c :=
  (mem_toData_fst S a c).symm

private theorem leftEdge_mem_iff (S : Finset (MobiusGridEdge M N)) (a : Fin (2 * M)) (c : Fin N) :
    leftEdge a c ∈ S ↔ a ∈ prevState revSet (toData S).1 c := by
  unfold leftEdge prevState
  split_ifs with h
  · simp only [revSet, mem_map, Equiv.toEmbedding_apply, Fin.revPerm_apply, mem_toData_fst]
    constructor
    · intro hS
      refine ⟨Fin.rev a, ?_, Fin.rev_rev a⟩
      rwa [rightEdge_of_not_lt _ _ (by simp)]
    · rintro ⟨b, hb, rfl⟩
      rwa [rightEdge_of_not_lt _ _ (by simp), ← Fin.rev_rev b] at hb
  · rw [mem_toData_fst, rightEdge_of_lt _ _ (by simp only; have := c.isLt; omega)]

private theorem existsUnique_iff_card_filter {α : Type*} (S : Finset α) (P : α → Prop)
    [DecidablePred P] : (∃! e, e ∈ S ∧ P e) ↔ (S.filter P).card = 1 := by
  rw [card_eq_one]
  constructor
  · rintro ⟨x, ⟨hxS, hxP⟩, huniq⟩
    refine ⟨x, ?_⟩
    ext y
    simp only [mem_filter, mem_singleton]
    exact ⟨fun h => huniq y h, fun h => h ▸ ⟨hxS, hxP⟩⟩
  · rintro ⟨x, hx⟩
    have hmem : ∀ y, y ∈ S ∧ P y ↔ y = x := fun y => by rw [← mem_filter, hx, mem_singleton]
    exact ⟨x, (hmem x).2 rfl, fun y hy => (hmem y).1 hy⟩

private theorem card_filter_incident (S : Finset (MobiusGridEdge M N)) (a : Fin (2 * M)) (c : Fin N)
    [DecidablePred fun e => MobiusGridIncident e ((a, c) : MobiusGridVertex M N)] :
    (S.filter fun e => MobiusGridIncident e ((a, c) : MobiusGridVertex M N)).card =
      (if a ∈ prevState revSet (toData S).1 c then 1 else 0) +
        (if a ∈ (toData S).1 c then 1 else 0) +
        ((toData S).2 c |>.filter (fun i => a.val = i.val ∨ a.val = i.val + 1)).card := by
  classical
  let vemb : Fin (2 * M - 1) ↪ MobiusGridEdge M N :=
    ⟨fun i => .vertical i c, fun i j h => by simpa using h⟩
  have hset : (S.filter fun e => MobiusGridIncident e ((a, c) : MobiusGridVertex M N)) =
      (S.filter (· = leftEdge a c) ∪ S.filter (· = rightEdge a c)) ∪
        ((toData S).2 c |>.filter (fun i => a.val = i.val ∨ a.val = i.val + 1)).map vemb := by
    ext e
    simp only [mem_filter, incident_iff, mem_union, mem_map, vemb, toData, mem_univ, true_and]
    constructor
    · rintro ⟨hS, h | h | ⟨i, rfl, hi⟩⟩
      · exact Or.inl (Or.inr ⟨hS, h⟩)
      · exact Or.inl (Or.inl ⟨hS, h⟩)
      · exact Or.inr ⟨i, ⟨hS, hi⟩, rfl⟩
    · rintro ((⟨hS, h⟩ | ⟨hS, h⟩) | ⟨i, ⟨hS, hi⟩, rfl⟩)
      · exact ⟨hS, Or.inr (Or.inl h)⟩
      · exact ⟨hS, Or.inl h⟩
      · exact ⟨hS, Or.inr (Or.inr ⟨i, rfl, hi⟩)⟩
  have hdisj1 : Disjoint (S.filter (· = leftEdge a c)) (S.filter (· = rightEdge a c)) := by
    rw [disjoint_filter]
    intro e _ h1 h2
    exact leftEdge_ne_rightEdge a c (h1 ▸ h2)
  have hdisj2 : Disjoint (S.filter (· = leftEdge a c) ∪ S.filter (· = rightEdge a c))
      (((toData S).2 c |>.filter (fun i => a.val = i.val ∨ a.val = i.val + 1)).map vemb) := by
    rw [disjoint_left]
    intro e he he'
    simp only [mem_union, mem_filter, mem_map, vemb] at he he'
    obtain ⟨i, -, rfl⟩ := he'
    rcases he with ⟨-, h⟩ | ⟨-, h⟩
    · unfold leftEdge at h
      split_ifs at h
    · unfold rightEdge at h
      split_ifs at h
  rw [hset, card_union_of_disjoint hdisj2, card_union_of_disjoint hdisj1, card_map,
    filter_eq', filter_eq']
  simp only [← leftEdge_mem_iff, ← rightEdge_mem_iff]
  split_ifs <;> simp

private theorem perfect_iff (S : Finset (MobiusGridEdge M N)) :
    IsMobiusGridPerfectMatching S ↔
      ∀ c, ColOK M (prevState revSet (toData S).1 c) ((toData S).1 c) ((toData S).2 c) := by
  classical
  unfold IsMobiusGridPerfectMatching ColOK
  constructor
  · intro h c a
    rw [← card_filter_incident, ← existsUnique_iff_card_filter]
    exact h (a, c)
  · intro h v
    obtain ⟨a, c⟩ := v
    rw [existsUnique_iff_card_filter, card_filter_incident]
    exact h c a

end LuWuMobiusGrid.Match

namespace LuWuMobiusGrid

open Finset

private theorem count_eq_sum_prod (M N : ℕ) (hN : 0 < N) :
    mobiusGridPerfectMatchingCount M N =
      ∑ χ : Fin N → Finset (Fin (2 * M)), ∏ c : Fin N, colCount M (prevState revSet χ c) (χ c) := by
  classical
  unfold mobiusGridPerfectMatchingCount
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr ((Match.dataEquiv hN).subtypeEquiv (p := IsMobiusGridPerfectMatching)
      (q := fun d => ∀ c, ColOK M (prevState revSet d.1 c) (d.1 c) (d.2 c))
      fun S => Match.perfect_iff S),
    Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      fun (χ : Fin N → Finset (Fin (2 * M))) (ν : Fin N → Finset (Fin (2 * M - 1))) =>
        ∀ c, ColOK M (prevState revSet χ c) (χ c) (ν c)),
    Nat.card_sigma]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Nat.card_congr Equiv.subtypePiEquivPi, Nat.card_pi]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, colCount]

end LuWuMobiusGrid

/-! ### The one-column identity: column counts are minors of the hop matrix -/

namespace LuWuMobiusGrid

open Finset

namespace Col

/-- The relation behind the nonzero entries of `hopMat`: equal rows, or a white row next to
the other row. -/
private def Good (p a b : ℕ) : Prop := a = b ∨ ((a + p) % 2 = 1 ∧ (b = a + 1 ∨ a = b + 1))

private instance instDecidableGood (p a b : ℕ) : Decidable (Good p a b) := by
  unfold Good; infer_instance

private theorem hopMat_apply (M p : ℕ) (a b : Fin (2 * M)) :
    hopMat M p a b = if Good p a.val b.val then 1 else 0 := by
  unfold hopMat Good
  simp only [Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> tauto

private theorem not_cross {p a b u v : ℕ} (hab : b < a) (huv : u < v) (h1 : Good p a u)
    (h2 : Good p b v) : False := by
  unfold Good at h1 h2
  omega

/-- A permutation of `Fin k` other than the identity has an inversion. -/
private theorem exists_inversion {k : ℕ} (σ : Equiv.Perm (Fin k)) (hσ : σ ≠ 1) :
    ∃ i j, i < j ∧ σ j < σ i := by
  by_contra h
  push Not at h
  have hmono : Monotone σ := by
    intro i j hij
    rcases hij.lt_or_eq with hlt | rfl
    · exact h i j hlt
    · exact le_rfl
  have hsm : StrictMono σ := hmono.strictMono_of_injective σ.injective
  have h1 : (σ : Fin k → Fin k) = (univ : Finset (Fin k)).orderEmbOfFin (card_fin k) :=
    orderEmbOfFin_unique (card_fin k) (fun _ => mem_univ _) hsm
  have h2 : (id : Fin k → Fin k) = (univ : Finset (Fin k)).orderEmbOfFin (card_fin k) :=
    orderEmbOfFin_unique (card_fin k) (fun _ => mem_univ _) strictMono_id
  apply hσ
  ext x
  have hx : σ x = x := by simpa using congrFun (h1.trans h2.symm) x
  simp [hx]

/-- The minor of `hopMat` along two increasing enumerations is the product of the diagonal
entries: no other permutation contributes. -/
private theorem det_submatrix_eq_prod (M p : ℕ) {k : ℕ} (e f : Fin k → Fin (2 * M))
    (he : StrictMono e) (hf : StrictMono f) :
    ((hopMat M p).submatrix e f).det = ∏ i, hopMat M p (e i) (f i) := by
  rw [Matrix.det_apply', Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    obtain ⟨i, j, hij, hσij⟩ := exists_inversion σ hσ
    have hzero : hopMat M p (e (σ i)) (f i) = 0 ∨ hopMat M p (e (σ j)) (f j) = 0 := by
      by_contra hne
      push Not at hne
      rw [hopMat_apply, hopMat_apply] at hne
      split_ifs at hne with h1 h2
      · exact not_cross (he hσij) (hf hij) h1 h2
      · exact hne.2 rfl
      · exact hne.1 rfl
      · exact hne.1 rfl
    have hprod : ∏ x, (hopMat M p).submatrix e f (σ x) x = 0 := by
      rcases hzero with h | h
      · exact Finset.prod_eq_zero (mem_univ i) (by simpa using h)
      · exact Finset.prod_eq_zero (mem_univ j) (by simpa using h)
    rw [hprod, mul_zero]
  · intro h
    exact absurd (mem_univ _) h

/-- Number of vertical edges of `V` covering row `a`. -/
private def cov (M : ℕ) (V : Finset (Fin (2 * M - 1))) (a : Fin (2 * M)) : ℕ :=
  (V.filter (fun i => a.val = i.val ∨ a.val = i.val + 1)).card

private theorem one_le_cov {M : ℕ} {V : Finset (Fin (2 * M - 1))} {a : Fin (2 * M)}
    {e : Fin (2 * M - 1)} (he : e ∈ V) (h : a.val = e.val ∨ a.val = e.val + 1) :
    1 ≤ cov M V a :=
  Finset.card_pos.mpr ⟨e, mem_filter.mpr ⟨he, h⟩⟩

private theorem two_le_cov {M : ℕ} {V : Finset (Fin (2 * M - 1))} {a : Fin (2 * M)}
    {e e' : Fin (2 * M - 1)} (he : e ∈ V) (he' : e' ∈ V) (hne : e ≠ e')
    (h : a.val = e.val ∨ a.val = e.val + 1) (h' : a.val = e'.val ∨ a.val = e'.val + 1) :
    2 ≤ cov M V a :=
  Finset.one_lt_card.mpr ⟨e, mem_filter.mpr ⟨he, h⟩, e', mem_filter.mpr ⟨he', h'⟩, hne⟩

private theorem exists_of_cov_pos {M : ℕ} {V : Finset (Fin (2 * M - 1))} {a : Fin (2 * M)}
    (h : 0 < cov M V a) : ∃ e ∈ V, a.val = e.val ∨ a.val = e.val + 1 := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp h
  exact ⟨e, (mem_filter.mp he).1, (mem_filter.mp he).2⟩

private theorem ind_sum (M p : ℕ) (I J : Finset (Fin (2 * M))) (a : Fin (2 * M)) :
    (if a ∈ symmDiff I (white M p) then 1 else 0) +
        (if a ∈ symmDiff J (black M p) then 1 else 0) =
      if (a.val + p) % 2 = 1 then (if a ∈ I then 0 else 1) + (if a ∈ J then 1 else 0)
      else (if a ∈ I then 1 else 0) + (if a ∈ J then 0 else 1) := by
  rcases Nat.mod_two_eq_zero_or_one (a.val + p) with hw | hw <;>
    by_cases hI : a ∈ I <;> by_cases hJ : a ∈ J <;> simp [mem_symmDiff, white, black, hI, hJ, hw]

private theorem row_valid {M p : ℕ} {I J : Finset (Fin (2 * M))} {V : Finset (Fin (2 * M - 1))}
    (hV : ColOK M (symmDiff I (white M p)) (symmDiff J (black M p)) V) (a : Fin (2 * M)) :
    (if (a.val + p) % 2 = 1 then (if a ∈ I then 0 else 1) + (if a ∈ J then 1 else 0)
      else (if a ∈ I then 1 else 0) + (if a ∈ J then 0 else 1)) + cov M V a = 1 := by
  rw [← ind_sum]
  exact hV a

private theorem colOK_of_rows {M p : ℕ} {I J : Finset (Fin (2 * M))} {V : Finset (Fin (2 * M - 1))}
    (h : ∀ a : Fin (2 * M),
      (if (a.val + p) % 2 = 1 then (if a ∈ I then 0 else 1) + (if a ∈ J then 1 else 0)
        else (if a ∈ I then 1 else 0) + (if a ∈ J then 0 else 1)) + cov M V a = 1) :
    ColOK M (symmDiff I (white M p)) (symmDiff J (black M p)) V := by
  intro a
  have := h a
  rw [← ind_sum] at this
  exact this

/-- If `V` and `V'` agree below the edge `i`, which lies in `V` only, the row `i` is covered
once more by `V` than by `V'`. -/
private theorem cov_eq_succ {M : ℕ} {V V' : Finset (Fin (2 * M - 1))} {i : Fin (2 * M - 1)}
    (hi : i ∈ V) (hi' : i ∉ V') (hagree : ∀ j : Fin (2 * M - 1), j < i → (j ∈ V ↔ j ∈ V'))
    (a : Fin (2 * M)) (ha : a.val = i.val) :
    cov M V a = cov M V' a + 1 := by
  unfold cov
  have hfilt : V.filter (fun j => a.val = j.val ∨ a.val = j.val + 1) =
      insert i (V'.filter (fun j => a.val = j.val ∨ a.val = j.val + 1)) := by
    ext j
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨hj, hcov⟩
      rcases hcov with h | h
      · exact Or.inl (Fin.ext (by omega))
      · exact Or.inr ⟨(hagree j (Fin.lt_def.mpr (by omega))).mp hj, Or.inr h⟩
    · rintro (rfl | ⟨hj, hcov⟩)
      · exact ⟨hi, Or.inl ha⟩
      · rcases hcov with h | h
        · have hji : j = i := Fin.ext (by omega)
          subst hji
          exact absurd hj hi'
        · exact ⟨(hagree j (Fin.lt_def.mpr (by omega))).mpr hj, Or.inr h⟩
  rw [hfilt, card_insert_of_notMem]
  simp [hi']

/-- The vertical completion of a column is unique. -/
private theorem colOK_unique {M : ℕ} {L R : Finset (Fin (2 * M))} {V V' : Finset (Fin (2 * M - 1))}
    (hV : ColOK M L R V) (hV' : ColOK M L R V') : V = V' := by
  by_contra hne
  have hS : (symmDiff V V').Nonempty := Finset.symmDiff_nonempty.mpr hne
  have hiS : (symmDiff V V').min' hS ∈ symmDiff V V' := min'_mem _ _
  have hagree : ∀ j, j < (symmDiff V V').min' hS → (j ∈ V ↔ j ∈ V') := by
    intro j hj
    by_contra h
    have hj' : j ∈ symmDiff V V' := by
      rw [mem_symmDiff]
      tauto
    exact absurd (min'_le _ _ hj') (not_le.mpr hj)
  set i := (symmDiff V V').min' hS
  have hi_lt : i.val < 2 * M := by have := i.isLt; omega
  have e1 : _ + _ + cov M V ⟨i.val, hi_lt⟩ = 1 := hV ⟨i.val, hi_lt⟩
  have e2 : _ + _ + cov M V' ⟨i.val, hi_lt⟩ = 1 := hV' ⟨i.val, hi_lt⟩
  rcases mem_symmDiff.mp hiS with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := cov_eq_succ h1 h2 hagree ⟨i.val, hi_lt⟩ rfl
    omega
  · have := cov_eq_succ h1 h2 (fun j hj => (hagree j hj).symm) ⟨i.val, hi_lt⟩ rfl
    omega

private theorem pair_unique {p x y x' y' a : ℕ} (h : Good p x y) (h' : Good p x' y')
    (hne : x ≠ y) (hne' : x' ≠ y') (ha : a = x ∨ a = y) (ha' : a = x' ∨ a = y') :
    x = x' ∨ y = y' := by
  unfold Good at h h'
  omega

/-- If the increasing enumerations of `I` and `J` pair up along nonzero entries of `hopMat`,
the column has a vertical completion. -/
private theorem colOK_of_good {M p : ℕ} {I J : Finset (Fin (2 * M))} (hcard : J.card = I.card)
    (hP : ∀ i, Good p (I.orderEmbOfFin rfl i).val (J.orderEmbOfFin hcard i).val) :
    ∃ V, ColOK M (symmDiff I (white M p)) (symmDiff J (black M p)) V := by
  set e := I.orderEmbOfFin rfl with he_def
  set f := J.orderEmbOfFin hcard with hf_def
  have heI : ∀ i, e i ∈ I := fun i => orderEmbOfFin_mem I rfl i
  have hfJ : ∀ i, f i ∈ J := fun i => orderEmbOfFin_mem J hcard i
  have hIe : ∀ a ∈ I, ∃ i, e i = a := by
    intro a ha
    have : a ∈ Set.range e := by rw [he_def, range_orderEmbOfFin]; exact ha
    exact this
  have hJf : ∀ a ∈ J, ∃ i, f i = a := by
    intro a ha
    have : a ∈ Set.range f := by rw [hf_def, range_orderEmbOfFin]; exact ha
    exact this
  have heinj : ∀ i j, (e i).val = (e j).val → i = j := fun i j h => e.injective (Fin.ext h)
  have hfinj : ∀ i j, (f i).val = (f j).val → i = j := fun i j h => f.injective (Fin.ext h)
  refine ⟨univ.filter (fun v : Fin (2 * M - 1) =>
    ∃ i, e i ≠ f i ∧ v.val = min (e i).val (f i).val), colOK_of_rows fun a => ?_⟩
  by_cases hA : ∃ i, e i ≠ f i ∧ (a.val = (e i).val ∨ a.val = (f i).val)
  · obtain ⟨i0, hne0, ha0⟩ := hA
    have hne0' : (e i0).val ≠ (f i0).val := fun h => hne0 (Fin.ext h)
    have hg0 := (hP i0).resolve_left hne0'
    have hlt0 : min (e i0).val (f i0).val < 2 * M - 1 := by
      have := (f i0).isLt
      have := (e i0).isLt
      omega
    have hcov : cov M (univ.filter (fun v : Fin (2 * M - 1) =>
        ∃ i, e i ≠ f i ∧ v.val = min (e i).val (f i).val)) a = 1 := by
      unfold cov
      rw [Finset.card_eq_one]
      refine ⟨⟨min (e i0).val (f i0).val, hlt0⟩, ?_⟩
      ext v
      simp only [mem_filter, mem_singleton, mem_univ, true_and]
      constructor
      · rintro ⟨⟨i, hne, hv⟩, hcv⟩
        have hne' : (e i).val ≠ (f i).val := fun h => hne (Fin.ext h)
        have hg := (hP i).resolve_left hne'
        have hai : a.val = (e i).val ∨ a.val = (f i).val := by omega
        have hii : i = i0 := by
          rcases pair_unique (hP i) (hP i0) hne' hne0' hai ha0 with h | h
          · exact heinj _ _ h
          · exact hfinj _ _ h
        subst hii
        exact Fin.ext hv
      · rintro rfl
        exact ⟨⟨i0, hne0, rfl⟩, by simp only; omega⟩
    rw [hcov]
    rcases ha0 with ha | ha
    · have haI : a ∈ I := by
        have : a = e i0 := Fin.ext ha
        rw [this]
        exact heI i0
      have haJ : a ∉ J := by
        intro haJ
        obtain ⟨j, hj⟩ := hJf a haJ
        have hjv : (f j).val = a.val := by rw [hj]
        by_cases hjj : (e j).val = (f j).val
        · have hji : j = i0 := heinj _ _ (by omega)
          subst hji
          omega
        · have hg := (hP j).resolve_left hjj
          omega
      have hw : (a.val + p) % 2 = 1 := by omega
      simp [haI, haJ, hw]
    · have haJ : a ∈ J := by
        have : a = f i0 := Fin.ext ha
        rw [this]
        exact hfJ i0
      have haI : a ∉ I := by
        intro haI
        obtain ⟨j, hj⟩ := hIe a haI
        have hjv : (e j).val = a.val := by rw [hj]
        by_cases hjj : (e j).val = (f j).val
        · have hji : j = i0 := hfinj _ _ (by omega)
          subst hji
          omega
        · have hg := (hP j).resolve_left hjj
          omega
      have hw : (a.val + p) % 2 = 0 := by omega
      simp [haI, haJ, hw]
  · push Not at hA
    have hcov : cov M (univ.filter (fun v : Fin (2 * M - 1) =>
        ∃ i, e i ≠ f i ∧ v.val = min (e i).val (f i).val)) a = 0 := by
      unfold cov
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v hv hcv
      simp only [mem_filter, mem_univ, true_and] at hv
      obtain ⟨i, hne, hvv⟩ := hv
      have hne' : (e i).val ≠ (f i).val := fun h => hne (Fin.ext h)
      have hg := (hP i).resolve_left hne'
      have := hA i hne
      omega
    rw [hcov]
    by_cases haI : a ∈ I
    · obtain ⟨i, hi⟩ := hIe a haI
      have heq : e i = f i := by
        by_contra hne
        exact (hA i hne).1 (by rw [hi])
      have haJ : a ∈ J := by
        rw [← hi, heq]
        exact hfJ i
      rcases Nat.mod_two_eq_zero_or_one (a.val + p) with hw | hw <;> simp [haI, haJ, hw]
    · have haJ : a ∉ J := by
        intro haJ
        obtain ⟨j, hj⟩ := hJf a haJ
        have heq : e j = f j := by
          by_contra hne
          exact (hA j hne).2 (by rw [hj])
        exact haI (by rw [← hj, ← heq]; exact heI j)
      rcases Nat.mod_two_eq_zero_or_one (a.val + p) with hw | hw <;> simp [haI, haJ, hw]

/-- The partner of a row along the vertical edges of `V`; an uncovered row is its own
partner. -/
private def psi (M : ℕ) (V : Finset (Fin (2 * M - 1))) (a : Fin (2 * M)) : Fin (2 * M) :=
  if h : ∃ e ∈ V, e.val = a.val then
    ⟨a.val + 1, by obtain ⟨e, -, he⟩ := h; have := e.isLt; omega⟩
  else if ∃ e ∈ V, e.val + 1 = a.val then ⟨a.val - 1, by have := a.isLt; omega⟩
  else a

private theorem psi_val_of_up {M : ℕ} {V : Finset (Fin (2 * M - 1))} {a : Fin (2 * M)}
    (h : ∃ e ∈ V, e.val = a.val) : (psi M V a).val = a.val + 1 := by
  unfold psi
  rw [dite_eq_left h]

private theorem psi_val_of_down {M : ℕ} {V : Finset (Fin (2 * M - 1))} {a : Fin (2 * M)}
    (h1 : ¬∃ e ∈ V, e.val = a.val) (h2 : ∃ e ∈ V, e.val + 1 = a.val) :
    (psi M V a).val = a.val - 1 := by
  unfold psi
  rw [dite_eq_right h1, ite_eq_left h2]

private theorem psi_of_none {M : ℕ} {V : Finset (Fin (2 * M - 1))} {a : Fin (2 * M)}
    (h1 : ¬∃ e ∈ V, e.val = a.val) (h2 : ¬∃ e ∈ V, e.val + 1 = a.val) : psi M V a = a := by
  unfold psi
  rw [dite_eq_right h1, ite_eq_right h2]

/-- When every row is covered at most once, `psi` fixes the uncovered rows and swaps the two
ends of each vertical edge. -/
private theorem psi_spec {M : ℕ} {V : Finset (Fin (2 * M - 1))} (hle : ∀ a, cov M V a ≤ 1)
    (a : Fin (2 * M)) :
    (cov M V a = 0 ∧ psi M V a = a) ∨
      (cov M V a = 1 ∧ ((psi M V a).val = a.val + 1 ∨ (psi M V a).val + 1 = a.val) ∧
        cov M V (psi M V a) = 1 ∧ psi M V (psi M V a) = a) := by
  by_cases h0 : cov M V a = 0
  · left
    refine ⟨h0, psi_of_none ?_ ?_⟩
    · rintro ⟨e, he, hea⟩
      have := one_le_cov he (Or.inl hea.symm)
      omega
    · rintro ⟨e, he, hea⟩
      have := one_le_cov he (Or.inr hea.symm)
      omega
  · right
    have h1 : cov M V a = 1 := by have := hle a; omega
    refine ⟨h1, ?_⟩
    by_cases hA : ∃ e ∈ V, e.val = a.val
    · obtain ⟨e, he, hea⟩ := hA
      have hv := psi_val_of_up ⟨e, he, hea⟩
      have hcb : cov M V (psi M V a) = 1 := by
        have := one_le_cov (a := psi M V a) he (Or.inr (by omega))
        have := hle (psi M V a)
        omega
      refine ⟨Or.inl hv, hcb, Fin.ext ?_⟩
      have hnot : ¬∃ e' ∈ V, e'.val = (psi M V a).val := by
        rintro ⟨e', he', he'v⟩
        have hne : e' ≠ e := by
          intro h
          rw [h] at he'v
          omega
        have := two_le_cov (a := psi M V a) he' he hne (Or.inl he'v.symm) (Or.inr (by omega))
        omega
      rw [psi_val_of_down hnot ⟨e, he, by omega⟩]
      omega
    · by_cases hB : ∃ e ∈ V, e.val + 1 = a.val
      · obtain ⟨e, he, hea⟩ := hB
        have hv := psi_val_of_down hA ⟨e, he, hea⟩
        have hcb : cov M V (psi M V a) = 1 := by
          have := one_le_cov (a := psi M V a) he (Or.inl (by omega))
          have := hle (psi M V a)
          omega
        refine ⟨Or.inr (by omega), hcb, Fin.ext ?_⟩
        rw [psi_val_of_up ⟨e, he, by omega⟩]
        omega
      · exfalso
        obtain ⟨e, he, hcv⟩ := exists_of_cov_pos (M := M) (V := V) (a := a) (by omega)
        rcases hcv with h | h
        · exact hA ⟨e, he, h.symm⟩
        · exact hB ⟨e, he, h.symm⟩

private theorem cov_le_one {M p : ℕ} {I J : Finset (Fin (2 * M))} {V : Finset (Fin (2 * M - 1))}
    (hV : ColOK M (symmDiff I (white M p)) (symmDiff J (black M p)) V) (a : Fin (2 * M)) :
    cov M V a ≤ 1 := by
  have := hV a
  unfold cov
  omega

/-- Under a vertical completion, the partner of a row of `I` is a row of `J`; a row of `I`
that moves is white and its partner is a black row outside `I`. -/
private theorem psi_mem {M p : ℕ} {I J : Finset (Fin (2 * M))} {V : Finset (Fin (2 * M - 1))}
    (hV : ColOK M (symmDiff I (white M p)) (symmDiff J (black M p)) V) {a : Fin (2 * M)}
    (ha : a ∈ I) :
    (psi M V a = a ∧ a ∈ J) ∨
      ((a.val + p) % 2 = 1 ∧ ((psi M V a).val = a.val + 1 ∨ (psi M V a).val + 1 = a.val) ∧
        psi M V a ∈ J ∧ psi M V a ∉ I ∧ psi M V (psi M V a) = a) := by
  rcases psi_spec (cov_le_one hV) a with ⟨h0, hpa⟩ | ⟨h1, hadj, hcb, hinv⟩
  · left
    refine ⟨hpa, ?_⟩
    by_contra haJ
    have := row_valid hV a
    rcases Nat.mod_two_eq_zero_or_one (a.val + p) with hw | hw <;> simp [ha, haJ, hw, h0] at this
  · right
    have hw : (a.val + p) % 2 = 1 := by
      by_contra hw
      have hw0 : (a.val + p) % 2 = 0 := by omega
      have := row_valid hV a
      simp [ha, hw0, h1] at this
    have hwb : ((psi M V a).val + p) % 2 = 0 := by omega
    have hrow := row_valid hV (psi M V a)
    rw [hcb] at hrow
    simp only [hwb, zero_ne_one, ite_false] at hrow
    refine ⟨hw, hadj, ?_, ?_, hinv⟩
    · by_contra hJ
      by_cases hI : psi M V a ∈ I <;> simp [hI, hJ] at hrow
    · intro hI
      simp [hI] at hrow

private theorem psi_lt {M p : ℕ} {I J : Finset (Fin (2 * M))} {V : Finset (Fin (2 * M - 1))}
    (hV : ColOK M (symmDiff I (white M p)) (symmDiff J (black M p)) V) {a a' : Fin (2 * M)}
    (ha : a ∈ I) (ha' : a' ∈ I) (hlt : a < a') : psi M V a < psi M V a' := by
  have hlt' := Fin.lt_def.mp hlt
  rw [Fin.lt_def]
  rcases psi_mem hV ha with ⟨hpa, -⟩ | ⟨hw, hadj, -, hnI, hinv⟩ <;>
    rcases psi_mem hV ha' with ⟨hpa', -⟩ | ⟨hw', hadj', -, hnI', hinv'⟩
  · rw [hpa, hpa']
    exact hlt'
  · rw [hpa]
    by_contra hcon
    have heq : psi M V a' = a := Fin.ext (by omega)
    exact hnI' (heq ▸ ha)
  · rw [hpa']
    by_contra hcon
    have heq : psi M V a = a' := Fin.ext (by omega)
    exact hnI (heq ▸ ha')
  · by_contra hcon
    have heq : psi M V a = psi M V a' := Fin.ext (by omega)
    have : a = a' := by rw [← hinv, heq, hinv']
    exact absurd this (ne_of_lt hlt)

private theorem card_le_of_colOK {M p : ℕ} {I J : Finset (Fin (2 * M))}
    {V : Finset (Fin (2 * M - 1))}
    (hV : ColOK M (symmDiff I (white M p)) (symmDiff J (black M p)) V) : I.card ≤ J.card := by
  refine card_le_card_of_injOn (psi M V) (fun a ha => ?_) (fun a ha a' ha' h => ?_)
  · rcases psi_mem hV ha with ⟨hpa, haJ⟩ | ⟨-, -, hJ, -⟩
    · rw [hpa]
      exact haJ
    · exact hJ
  · rcases lt_trichotomy a a' with hlt | heq | hlt
    · exact absurd h (ne_of_lt (psi_lt hV ha ha' hlt))
    · exact heq
    · exact absurd h (ne_of_gt (psi_lt hV ha' ha hlt))

private theorem colOK_swap {M p : ℕ} {I J : Finset (Fin (2 * M))} {V : Finset (Fin (2 * M - 1))}
    (hV : ColOK M (symmDiff I (white M p)) (symmDiff J (black M p)) V) :
    ColOK M (symmDiff J (white M (p + 1))) (symmDiff I (black M (p + 1))) V := by
  have hw : white M (p + 1) = black M p := by
    ext a
    simp only [white, black, mem_filter, mem_univ, true_and]
    omega
  have hb : black M (p + 1) = white M p := by
    ext a
    simp only [white, black, mem_filter, mem_univ, true_and]
    omega
  rw [hw, hb]
  intro a
  have := hV a
  omega

/-- A vertical completion forces `I` and `J` to have the same size and their increasing
enumerations to pair up along nonzero entries of `hopMat`. -/
private theorem good_of_colOK {M p : ℕ} {I J : Finset (Fin (2 * M))} {V : Finset (Fin (2 * M - 1))}
    (hV : ColOK M (symmDiff I (white M p)) (symmDiff J (black M p)) V) :
    ∃ hcard : J.card = I.card,
      ∀ i, Good p (I.orderEmbOfFin rfl i).val (J.orderEmbOfFin hcard i).val := by
  have hcard : J.card = I.card := le_antisymm (card_le_of_colOK (colOK_swap hV))
    (card_le_of_colOK hV)
  refine ⟨hcard, fun i => ?_⟩
  have hfeq : (fun i => psi M V (I.orderEmbOfFin rfl i)) = ⇑(J.orderEmbOfFin hcard) := by
    refine orderEmbOfFin_unique hcard (fun x => ?_) (fun x y hxy => ?_)
    · rcases psi_mem hV (orderEmbOfFin_mem I rfl x) with ⟨hpa, haJ⟩ | ⟨-, -, hJ, -⟩
      · rw [hpa]
        exact haJ
      · exact hJ
    · exact psi_lt hV (orderEmbOfFin_mem I rfl x) (orderEmbOfFin_mem I rfl y)
        ((I.orderEmbOfFin rfl).strictMono hxy)
  rw [← congrFun hfeq i]
  rcases psi_mem hV (orderEmbOfFin_mem I rfl i) with ⟨hpa, -⟩ | ⟨hw, hadj, -⟩
  · rw [hpa]
    exact Or.inl rfl
  · exact Or.inr ⟨hw, by omega⟩

end Col

/-- **One-column identity.** The number of vertical completions of a column whose crossing
sets are `I ∆ white` and `J ∆ black` is the minor of `hopMat` with rows `I` and columns `J`. -/
private theorem colCount_symmDiff_eq_minor (M p : ℕ) (I J : Finset (Fin (2 * M))) :
    (colCount M (symmDiff I (white M p)) (symmDiff J (black M p)) : ℤ) =
      minor (hopMat M p) I J := by
  unfold minor colCount
  split_ifs with hcard
  · rw [Col.det_submatrix_eq_prod M p _ _ (I.orderEmbOfFin rfl).strictMono
      (J.orderEmbOfFin hcard).strictMono]
    by_cases hP : ∀ i, Col.Good p (I.orderEmbOfFin rfl i).val (J.orderEmbOfFin hcard i).val
    · have hprod : ∏ i, hopMat M p (I.orderEmbOfFin rfl i) (J.orderEmbOfFin hcard i) = 1 := by
        refine Finset.prod_eq_one fun i _ => ?_
        rw [Col.hopMat_apply, ite_eq_left (hP i)]
      obtain ⟨V, hV⟩ := Col.colOK_of_good hcard hP
      have hc : (univ.filter (fun V : Finset (Fin (2 * M - 1)) =>
          ColOK M (symmDiff I (white M p)) (symmDiff J (black M p)) V)).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨V, ?_⟩
        ext V'
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        exact ⟨fun h => Col.colOK_unique h hV, fun h => h ▸ hV⟩
      rw [hprod, hc, Nat.cast_one]
    · push Not at hP
      obtain ⟨i, hi⟩ := hP
      have hprod : ∏ i, hopMat M p (I.orderEmbOfFin rfl i) (J.orderEmbOfFin hcard i) = 0 :=
        Finset.prod_eq_zero (mem_univ i) (by rw [Col.hopMat_apply, ite_eq_right hi])
      have hc : (univ.filter (fun V : Finset (Fin (2 * M - 1)) =>
          ColOK M (symmDiff I (white M p)) (symmDiff J (black M p)) V)).card = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]
        intro V _ hV
        obtain ⟨hcard', hP'⟩ := Col.good_of_colOK hV
        exact hi (hP' i)
      rw [hprod, hc, Nat.cast_zero]
  · have hc : (univ.filter (fun V : Finset (Fin (2 * M - 1)) =>
        ColOK M (symmDiff I (white M p)) (symmDiff J (black M p)) V)).card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      intro V _ hV
      obtain ⟨hcard', -⟩ := Col.good_of_colOK hV
      exact hcard hcard'
    rw [hc, Nat.cast_zero]

end LuWuMobiusGrid

/-! ### The Cauchy–Binet formula for minors -/

namespace LuWuMobiusGrid

namespace CB

open Finset

variable {R : Type*} [CommRing R]

/-- Expansion of the determinant of a product of a `k × m` and an `m × k` matrix as a sum over
all maps `Fin k → m`. -/
private theorem det_mul_eq_sum_fun {m : Type*} [Fintype m] {k : ℕ}
    (A : Matrix (Fin k) m R) (B : Matrix m (Fin k) R) :
    (A * B).det = ∑ f : Fin k → m, (∏ i, B (f i) i) * (A.submatrix id f).det := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
    Fintype.piFinset_univ, Matrix.submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/-- Selecting columns along a non-injective map gives a matrix with two equal columns. -/
private theorem det_submatrix_eq_zero_of_not_injective {m : Type*} {k : ℕ} (A : Matrix (Fin k) m R)
    (f : Fin k → m) (hf : ¬ Function.Injective f) : (A.submatrix id f).det = 0 := by
  simp only [Function.Injective, not_forall] at hf
  obtain ⟨i, j, hij, hne⟩ := hf
  exact Matrix.det_zero_of_column_eq hne fun r => by simp [hij]

/-- Rectangular Cauchy–Binet formula. -/
private theorem det_mul_rect {n k : ℕ} (A : Matrix (Fin k) (Fin n) R)
    (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ K : Finset (Fin n), if h : K.card = k then
      (A.submatrix id (K.orderEmbOfFin h)).det * (B.submatrix (K.orderEmbOfFin h) id).det
      else 0 := by
  set F : (Fin k → Fin n) → R := fun f => (∏ i, B (f i) i) * (A.submatrix id f).det with hF
  have hF0 : ∀ f, ¬ Function.Injective f → F f = 0 := fun f hf => by
    simp only [hF, det_submatrix_eq_zero_of_not_injective A f hf, mul_zero]
  have hcard : ∀ f : Fin k → Fin n, Function.Injective f → (univ.image f).card = k :=
    fun f hf => by rw [card_image_of_injective _ hf, card_univ, Fintype.card_fin]
  calc (A * B).det = ∑ f : Fin k → Fin n, F f := det_mul_eq_sum_fun A B
    _ = ∑ K : Finset (Fin n), ∑ f ∈ univ with univ.image f = K, F f :=
        (sum_fiberwise univ (fun f : Fin k → Fin n => univ.image f) F).symm
    _ = _ := by
      refine sum_congr rfl fun K _ => ?_
      split_ifs with hK
      · rw [sum_subset (s₂ := univ.filter (fun f : Fin k → Fin n => ∀ i, f i ∈ K))]
        · rw [← Matrix.det_mul, det_mul_eq_sum_fun]
          symm
          refine sum_nbij' (fun f' => K.orderEmbOfFin hK ∘ f')
            (fun f x => if h : f x ∈ K then (K.orderIsoOfFin hK).symm ⟨f x, h⟩ else x)
            ?_ ?_ ?_ ?_ ?_
          · intro f' _
            simp [orderEmbOfFin_mem]
          · intro f _
            simp
          · intro f' _
            funext x
            simp only [Function.comp_apply, orderEmbOfFin_mem, dite_true]
            rw [OrderIso.symm_apply_eq]
            exact Subtype.ext (coe_orderIsoOfFin_apply K hK (f' x)).symm
          · intro f hf
            funext x
            simp only [mem_filter, mem_univ, true_and] at hf
            simp only [Function.comp_apply, hf x, dite_true, ← coe_orderIsoOfFin_apply,
              OrderIso.apply_symm_apply]
          · intro f' _
            simp [hF, Matrix.submatrix_submatrix]
        · intro f hf
          simp only [mem_filter, mem_univ, true_and] at hf ⊢
          intro i
          rw [← hf]
          exact mem_image_of_mem f (mem_univ i)
        · intro f hf hnot
          apply hF0
          intro hinj
          apply hnot
          simp only [mem_filter, mem_univ, true_and] at hf ⊢
          apply eq_of_subset_of_card_le
          · intro x hx
            obtain ⟨i, _, rfl⟩ := mem_image.mp hx
            exact hf i
          · rw [hcard f hinj, hK]
      · refine sum_eq_zero fun f hf => hF0 f fun hinj => hK ?_
        simp only [mem_filter, mem_univ, true_and] at hf
        rw [← hf, hcard f hinj]

/-- The determinant of a submatrix along increasing enumerations does not depend on the
cardinality bookkeeping. -/
private theorem det_submatrix_orderEmbOfFin_congr {n : ℕ} (B : Matrix (Fin n) (Fin n) R)
    (s t : Finset (Fin n)) {k k' : ℕ} (h1 : s.card = k) (h2 : t.card = k) (h1' : s.card = k')
    (h2' : t.card = k') :
    (B.submatrix (s.orderEmbOfFin h1) (t.orderEmbOfFin h2)).det =
      (B.submatrix (s.orderEmbOfFin h1') (t.orderEmbOfFin h2')).det := by
  obtain rfl : k = k' := h1.symm.trans h1'
  rfl

end CB

open Finset in
private theorem minor_mul {n : ℕ} {R : Type*} [CommRing R] (A B : Matrix (Fin n) (Fin n) R)
    (I J : Finset (Fin n)) :
    minor (A * B) I J = ∑ K : Finset (Fin n), minor A I K * minor B K J := by
  unfold minor
  by_cases h : J.card = I.card
  · rw [dite_eq_left h]
    have hsub : (A * B).submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin h) =
        A.submatrix (I.orderEmbOfFin rfl) id * B.submatrix id (J.orderEmbOfFin h) := by
      ext i j
      simp [Matrix.mul_apply]
    rw [hsub, CB.det_mul_rect]
    refine sum_congr rfl fun K _ => ?_
    by_cases hK : K.card = I.card
    · rw [dite_eq_left hK, dite_eq_left hK, dite_eq_left (h.trans hK.symm),
        CB.det_submatrix_orderEmbOfFin_congr B K J rfl (h.trans hK.symm) hK h]
      rfl
    · rw [dite_eq_right hK, dite_eq_right hK, zero_mul]
  · rw [dite_eq_right h]
    symm
    refine sum_eq_zero fun K _ => ?_
    by_cases hK : K.card = I.card
    · rw [dite_eq_right (show ¬ J.card = K.card from fun h' => h (h'.trans hK)), mul_zero]
    · rw [dite_eq_right hK, zero_mul]

namespace CB

variable {R : Type*} [CommRing R]

/-- The compound matrix is multiplicative (Cauchy–Binet). -/
private theorem cpd_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) : cpd (A * B) = cpd A * cpd B := by
  ext I J
  simp only [cpd, Matrix.of_apply, Matrix.mul_apply, minor_mul]

/-- The compound matrix of the product of a nonempty list of matrices. -/
private theorem cpd_list_prod {n : ℕ} (a : Matrix (Fin n) (Fin n) R)
    (L : List (Matrix (Fin n) (Fin n) R)) :
    ((a :: L).map cpd).prod = cpd (a :: L).prod := by
  induction L generalizing a with
  | nil => simp
  | cons b L ih =>
    change cpd a * ((b :: L).map cpd).prod = cpd (a * (b :: L).prod)
    rw [ih, cpd_mul]

end CB

private theorem cpd_prod_range {n : ℕ} {R : Type*} [CommRing R] (N : ℕ) (hN : 0 < N)
    (A : ℕ → Matrix (Fin n) (Fin n) R) :
    ((List.range N).map (fun c => cpd (A c))).prod = cpd ((List.range N).map A).prod := by
  have h1 : (List.range N).map (fun c => cpd (A c)) = ((List.range N).map A).map cpd := by
    rw [List.map_map]
    rfl
  rw [h1]
  obtain ⟨a, L, hL⟩ : ∃ a L, (List.range N).map A = a :: L := by
    cases h : (List.range N).map A with
    | nil =>
      simp only [List.map_eq_nil_iff, List.range_eq_nil] at h
      omega
    | cons a L => exact ⟨a, L, rfl⟩
  rw [hL, CB.cpd_list_prod]

end LuWuMobiusGrid

/-! ### Chains of transfer matrices, the seam reversal and principal minors -/

namespace LuWuMobiusGrid.Chain

open Finset Equiv

/-- Previous state in a chain started at `i`. -/
private def prevI {ι : Type*} {n : ℕ} (i : ι) (K : Fin n → ι) (c : Fin n) : ι :=
  if h : c.val = 0 then i else K ⟨c.val - 1, by have := c.isLt; omega⟩

private theorem prevI_zero {ι : Type*} {n : ℕ} (i : ι) (K : Fin (n + 1) → ι) : prevI i K 0 = i := by
  simp [prevI]

private theorem prevI_cons_succ {ι : Type*} {n : ℕ} (i x : ι) (K : Fin (n + 1) → ι)
    (c : Fin (n + 1)) :
    prevI i (Fin.cons x K : Fin (n + 2) → ι) c.succ = prevI x K c := by
  unfold prevI
  split_ifs with h1 h2 h2
  · simp at h1
  · simp at h1
  · have : (⟨c.succ.val - 1, by omega⟩ : Fin (n + 2)) = 0 := Fin.ext (by simp [h2])
    rw [this, Fin.cons_zero]
  · have : (⟨c.succ.val - 1, by omega⟩ : Fin (n + 2)) =
        (⟨c.val - 1, by omega⟩ : Fin (n + 1)).succ := Fin.ext (by simp; omega)
    rw [this, Fin.cons_succ]

private theorem prevState_eq_prevI {ι : Type*} {n : ℕ} (g : ι → ι) (K : Fin (n + 1) → ι)
    (c : Fin (n + 1)) : prevState g K c = prevI (g (K (Fin.last n))) K c := by
  unfold prevState prevI
  split_ifs
  · rfl
  · rfl

section Paths

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

private theorem prod_range_apply (A : ℕ → Matrix ι ι R) (n : ℕ) (i j : ι) :
    ((List.range (n + 1)).map A).prod i j =
      ∑ K : Fin (n + 1) → ι, if K (Fin.last n) = j then
        ∏ c : Fin (n + 1), A c.val (prevI i K c) (K c) else 0 := by
  induction n generalizing A i with
  | zero =>
    rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    simp [prevI]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.prod_cons, Matrix.mul_apply]
    rw [← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ih (A ∘ Nat.succ) x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun K _ => ?_
    simp only [Fin.consEquiv_apply, Function.comp_apply]
    rw [← Fin.succ_last]
    simp only [Fin.cons_succ, Fin.prod_univ_succ, Fin.cons_zero, prevI_zero, prevI_cons_succ,
      Fin.val_succ, Fin.val_zero, Nat.succ_eq_add_one]
    split_ifs <;> simp

end Paths

private theorem hopMat_mod_two (M p : ℕ) : hopMat M p = hopMat M (p % 2) := by
  ext a b
  simp only [hopMat, Matrix.of_apply]
  have : (a.val + p) % 2 = (a.val + p % 2) % 2 := by omega
  rw [this]

private theorem hopMat_succ_apply (M p : ℕ) (a b : Fin (2 * M)) :
    hopMat M (p + 1) a b = hopMat M p (Fin.rev a) (Fin.rev b) := by
  have ha := a.isLt
  have hb := b.isLt
  have h : ((a.val + (p + 1)) % 2 = 1 ∧ (b.val = a.val + 1 ∨ a.val = b.val + 1)) ↔
      (((Fin.rev a).val + p) % 2 = 1 ∧ ((Fin.rev b).val = (Fin.rev a).val + 1 ∨
        (Fin.rev a).val = (Fin.rev b).val + 1)) := by
    simp only [Fin.val_rev]
    omega
  simp only [hopMat, Matrix.of_apply, Fin.rev_inj, h]

private theorem Qmat_mul_self (M : ℕ) : Qmat M * Qmat M = hopMat M 1 * hopMat M 0 := by
  ext a b
  simp only [Matrix.mul_apply, Qmat, Matrix.of_apply]
  have h1 : ∀ k, hopMat M 1 a k = hopMat M 0 (Fin.rev a) (Fin.rev k) :=
    fun k => hopMat_succ_apply M 0 a k
  simp only [h1]
  rw [← Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)]
  simp only [Fin.revPerm_apply, Fin.rev_rev]

private theorem of_rev_mul {n : ℕ} {R : Type*} [CommRing R] (B C : Matrix (Fin n) (Fin n) R) :
    (Matrix.of fun a b => (B * C) (Fin.rev a) b) = (Matrix.of fun a b => B (Fin.rev a) b) * C := by
  ext a b
  simp [Matrix.mul_apply]

private theorem rev_prod_hopMat_aux (M t : ℕ) :
    (Matrix.of fun a b => ((List.range (2 * t + 1)).map (hopMat M)).prod (Fin.rev a) b) =
      Qmat M ^ (2 * t + 1) := by
  induction t with
  | zero =>
    ext a b
    simp [Qmat]
  | succ t ih =>
    have e : 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 := by ring
    rw [e, List.range_succ, List.map_append, List.prod_append, List.range_succ, List.map_append,
      List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [of_rev_mul, of_rev_mul, ih, hopMat_mod_two M (2 * t + 1), hopMat_mod_two M (2 * t + 1 + 1)]
    have h1 : (2 * t + 1) % 2 = 1 := by omega
    have h2 : (2 * t + 1 + 1) % 2 = 0 := by omega
    rw [h1, h2, mul_assoc, ← Qmat_mul_self, ← mul_assoc, ← pow_succ, ← pow_succ]

private theorem sgnRev_succ (k : ℕ) : sgnRev (k + 1) = (-1) ^ k * sgnRev k := by
  unfold sgnRev
  rw [← pow_add]
  congr 1
  rcases k with _ | j
  · rfl
  · have h : (j + 1 + 1) * (j + 1) = (j + 1) * j + 2 * (j + 1) := by ring
    simp only [Nat.add_sub_cancel]
    rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2), Nat.add_comm]

private theorem revPerm_succ_eq (k : ℕ) : (Fin.revPerm : Perm (Fin (k + 1))) =
    (finRotate (k + 1)).symm * Perm.decomposeFin.symm (0, Fin.revPerm) := by
  ext x
  refine Fin.cases ?_ (fun y => ?_) x
  · simp only [Fin.revPerm_apply, Perm.coe_mul, Function.comp_apply,
      Perm.decomposeFin_symm_apply_zero]
    have : (finRotate (k + 1)).symm 0 = Fin.last k := by
      rw [Equiv.symm_apply_eq, finRotate_last]
    rw [this]
    simp
  · simp only [Fin.revPerm_apply, Perm.coe_mul, Function.comp_apply,
      Perm.decomposeFin_symm_apply_succ, swap_self, Equiv.refl_apply, Fin.rev_succ]
    have : (finRotate (k + 1)).symm (Fin.rev y).succ = (Fin.rev y).castSucc := by
      rw [Equiv.symm_apply_eq]
      ext
      rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last _).ne]
      simp
    rw [this]

private theorem sign_revPerm (k : ℕ) :
    ((Perm.sign (Fin.revPerm : Perm (Fin k)) : ℤˣ) : ℤ) = sgnRev k := by
  induction k with
  | zero => simp [sgnRev, Subsingleton.elim (Fin.revPerm : Perm (Fin 0)) 1]
  | succ k ih =>
    rw [revPerm_succ_eq, Perm.sign_mul, Perm.sign_symm, sign_finRotate,
      Perm.decomposeFin.symm_sign, sgnRev_succ, ← ih]
    simp

private theorem orderEmbOfFin_revSet {n : ℕ} (K : Finset (Fin n)) {k : ℕ} (h1 : (revSet K).card = k)
    (h2 : K.card = k) (i : Fin k) :
    (revSet K).orderEmbOfFin h1 i = Fin.rev (K.orderEmbOfFin h2 (Fin.rev i)) := by
  have hf := Finset.orderEmbOfFin_unique h1
    (f := fun i => Fin.rev (K.orderEmbOfFin h2 (Fin.rev i)))
    (fun x => by
      simp only [revSet, mem_map, Equiv.toEmbedding_apply, Fin.revPerm_apply]
      exact ⟨_, K.orderEmbOfFin_mem h2 _, rfl⟩)
    (fun i j hij => by
      simp only [Fin.rev_lt_rev]
      exact (K.orderEmbOfFin h2).strictMono (Fin.rev_lt_rev.mpr hij))
  exact (congrFun hf i).symm

private theorem det_submatrix_orderEmbOfFin_congr {n : ℕ} {R : Type*} [CommRing R]
    (B : Matrix (Fin n) (Fin n) R) (S T : Finset (Fin n)) {k k' : ℕ} (hk : k = k')
    (h1 : S.card = k) (h2 : T.card = k) (h1' : S.card = k') (h2' : T.card = k') :
    (B.submatrix (S.orderEmbOfFin h1) (T.orderEmbOfFin h2)).det =
      (B.submatrix (S.orderEmbOfFin h1') (T.orderEmbOfFin h2')).det := by
  subst hk
  rfl

private theorem det_revSet {n : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R)
    (K : Finset (Fin n)) {k : ℕ} (h1 : (revSet K).card = k) (h2 : K.card = k) :
    (A.submatrix ((revSet K).orderEmbOfFin h1) (K.orderEmbOfFin h2)).det =
      (sgnRev k : R) * ((Matrix.of fun a b => A (Fin.rev a) b).submatrix
        (K.orderEmbOfFin h2) (K.orderEmbOfFin h2)).det := by
  have h : A.submatrix ((revSet K).orderEmbOfFin h1) (K.orderEmbOfFin h2) =
      ((Matrix.of fun a b => A (Fin.rev a) b).submatrix (K.orderEmbOfFin h2)
        (K.orderEmbOfFin h2)).submatrix Fin.revPerm id := by
    ext i j
    simp [orderEmbOfFin_revSet K h1 h2]
  rw [h, Matrix.det_permute, sign_revPerm]

private theorem det_one_add_eq_sum {n : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R) :
    (1 + M).det =
      ∑ s : Finset (Fin n), (M.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
  rw [add_comm]
  change Matrix.detRowAlternating (fun i => M i + (1 : Matrix (Fin n) (Fin n) R) i) = _
  rw [show (fun i => M i + (1 : Matrix (Fin n) (Fin n) R) i) =
      (fun i => M i) + (fun i => (1 : Matrix (Fin n) (Fin n) R) i) from rfl,
    AlternatingMap.map_add_univ]
  exact Finset.sum_congr rfl fun s _ => Matrix.det_piecewise_one_eq_submatrix_det M s

private theorem minor_self_eq {n : ℕ} {R : Type*} [CommRing R] (Z : Matrix (Fin n) (Fin n) R)
    (s : Finset (Fin n)) :
    minor Z s s = (Z.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
  unfold minor
  rw [dite_eq_left rfl,
    ← Matrix.det_submatrix_equiv_self (s.orderIsoOfFin rfl).toEquiv
      (Z.submatrix (Subtype.val : s → Fin n) Subtype.val)]
  congr 1

private theorem one_sub_I_mul_I_pow (k : ℕ) :
    (1 - Complex.I) * Complex.I ^ k = (sgnRev k : ℂ) * (1 - (-1) ^ k * Complex.I) := by
  induction k with
  | zero => simp [sgnRev]
  | succ k ih =>
    have hu : ((-1 : ℂ) ^ k) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      simp
    rw [pow_succ, ← mul_assoc, ih, sgnRev_succ]
    push_cast
    linear_combination (-((sgnRev k : ℂ) * (-1) ^ k)) * Complex.I_sq -
      (sgnRev k : ℂ) * Complex.I * hu

private theorem re_one_sub_I_mul_I_pow (k : ℕ) :
    ((1 - Complex.I) * Complex.I ^ k).re = sgnRev k := by
  rw [one_sub_I_mul_I_pow]
  rcases neg_one_pow_eq_or ℂ k with h | h <;> simp [h]

end LuWuMobiusGrid.Chain

namespace LuWuMobiusGrid

open Finset

private theorem sum_prod_prevState {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (N : ℕ) (hN : 0 < N) (A : ℕ → Matrix ι ι R) (g : ι → ι) :
    ∑ K : Fin N → ι, ∏ c : Fin N, A c.val (prevState g K c) (K c) =
      ∑ k : ι, ((List.range N).map A).prod (g k) k := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  simp only [Chain.prod_range_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [mem_univ, ite_true, Chain.prevState_eq_prevI]

private theorem rev_prod_hopMat (M N : ℕ) (hN : Odd N) :
    (Matrix.of fun a b => ((List.range N).map (hopMat M)).prod (Fin.rev a) b) = Qmat M ^ N := by
  obtain ⟨t, rfl⟩ := hN
  exact Chain.rev_prod_hopMat_aux M t

private theorem minor_revSet_left {n : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R)
    (K : Finset (Fin n)) :
    minor A (revSet K) K =
      (sgnRev K.card : R) * minor (Matrix.of fun a b => A (Fin.rev a) b) K K := by
  have hc : (revSet K).card = K.card := Finset.card_map _
  unfold minor
  rw [dite_eq_left hc.symm, dite_eq_left rfl, Chain.det_revSet A K rfl hc.symm,
    Chain.det_submatrix_orderEmbOfFin_congr _ K K hc hc.symm hc.symm rfl rfl, hc]

private theorem sum_sgnRev_minor (n : ℕ) (Z : Matrix (Fin n) (Fin n) ℤ) :
    (((∑ k : Finset (Fin n), sgnRev k.card * minor Z k k : ℤ)) : ℝ) =
      Complex.re ((1 - Complex.I) * (1 + Complex.I • Z.map (Int.cast : ℤ → ℂ)).det) := by
  rw [Chain.det_one_add_eq_sum, Finset.mul_sum, Complex.re_sum]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  have h : (Complex.I • Z.map (Int.cast : ℤ → ℂ)).submatrix (Subtype.val : s → Fin n)
      (Subtype.val : s → Fin n) = Complex.I • (Z.submatrix (Subtype.val : s → Fin n)
        (Subtype.val : s → Fin n)).map (Int.cast : ℤ → ℂ) := rfl
  rw [h, Matrix.det_smul, Fintype.card_coe, ← mul_assoc, ← Int.cast_det, ← Complex.ofReal_intCast,
    Complex.re_mul_ofReal, Chain.re_one_sub_I_mul_I_pow, Chain.minor_self_eq]

end LuWuMobiusGrid

/-! ### The eigenvalues of the twisted one-column matrix -/

namespace LuWuMobiusGrid.Spec

open Finset Matrix

/-- If `A` has eigenvectors `v i` with distinct eigenvalues `μ i`, as many as its size, then
`det (1 + c • A ^ N) = ∏ i, (1 + c * μ i ^ N)`. -/
private theorem det_one_add_smul_pow {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (A : Matrix n n ℂ) (μ : ι → ℂ) (hμ : Function.Injective μ)
    (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0) (hAv : ∀ i, A *ᵥ v i = μ i • v i)
    (hcard : Fintype.card ι = Fintype.card n) (c : ℂ) (N : ℕ) :
    (1 + c • A ^ N).det = ∏ i, (1 + c * μ i ^ N) := by
  classical
  have hpow : ∀ i (k : ℕ), A ^ k *ᵥ v i = μ i ^ k • v i := by
    intro i k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) μ hμ v fun i =>
      Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (by rw [Matrix.toLin'_apply, hAv]), hv i⟩
  let b := basisOfLinearIndependentOfCardEqFinrank' v hli (by simp [hcard])
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  rw [← LinearMap.det_toLin', ← LinearMap.det_toMatrix b]
  have hdiag : LinearMap.toMatrix b b (Matrix.toLin' (1 + c • A ^ N)) =
      Matrix.diagonal fun i => 1 + c * μ i ^ N := by
    ext i j
    have hj : (1 + c • A ^ N) *ᵥ b j = (1 + c * μ j ^ N) • b j := by
      rw [hb, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hpow, smul_smul,
        add_smul, one_smul]
    rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, hj, map_smul, b.repr_self,
      Matrix.diagonal_apply, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs with h1 h2 h2
    · subst h1; simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  rw [hdiag, Matrix.det_diagonal]

/-- The angle `φ_r = (4r - 1) π / (2N)`. -/
private noncomputable def phi (N r : ℕ) : ℝ := ((4 * r - 1 : ℕ) : ℝ) * Real.pi / (2 * (N : ℝ))

/-- The root `z_r = exp (i φ_r)` of `z ^ N = -i`. -/
private noncomputable def zz (N r : ℕ) : ℂ := Complex.exp (↑(phi N r) * Complex.I)

private theorem prod_Icc_one_eq_prod_range {β : Type*} [CommMonoid β] (f : ℕ → β) (N : ℕ) :
    ∏ r ∈ Icc 1 N, f r = ∏ i ∈ range N, f (i + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

private theorem zz_succ (N i : ℕ) (hN : 0 < N) :
    Complex.exp (2 * Real.pi * Complex.I / N) ^ i * zz N 1 = zz N (i + 1) := by
  rw [zz, zz, ← Complex.exp_nat_mul, ← Complex.exp_add, phi, phi,
    show 4 * (i + 1) - 1 = 4 * i + 3 by omega, show 4 * 1 - 1 = 3 by omega]
  congr 1
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp
  ring

private theorem zz_one_pow (N : ℕ) (hN : 0 < N) : zz N 1 ^ N = -Complex.I := by
  rw [zz, ← Complex.exp_nat_mul, phi, show 4 * 1 - 1 = 3 by omega]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have : (N : ℂ) * (↑((3 : ℕ) * Real.pi / (2 * (N : ℝ))) * Complex.I) =
      ↑Real.pi * Complex.I + ↑Real.pi / 2 * Complex.I := by
    push_cast
    field_simp
    ring
  rw [this, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]
  ring

private theorem pow_add_I_eq_prod (N : ℕ) (hN : 0 < N) (x : ℂ) :
    x ^ N + Complex.I = ∏ r ∈ Icc 1 N, (x - zz N r) := by
  have h := X_pow_sub_C_eq_prod (Complex.isPrimitiveRoot_exp N hN.ne') hN (zz_one_pow N hN)
  have h2 := congrArg (Polynomial.eval x) h
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_prod] at h2
  rw [prod_Icc_one_eq_prod_range, sub_neg_eq_add] at *
  rw [h2]
  exact prod_congr rfl fun i _ => by rw [zz_succ N i hN]

private theorem prod_neg_zz (N : ℕ) (hN : 0 < N) : ∏ r ∈ Icc 1 N, (-zz N r) = Complex.I := by
  have h := pow_add_I_eq_prod N hN 0
  rw [zero_pow hN.ne', zero_add] at h
  rw [h]
  simp

private theorem prod_one_sub_zz_mul (N : ℕ) (hN : 0 < N) (t : ℂ) (ht : t ≠ 0) :
    ∏ r ∈ Icc 1 N, (1 - zz N r * t) = 1 + Complex.I * t ^ N := by
  have h := pow_add_I_eq_prod N hN t⁻¹
  have hc : ∏ _r ∈ Icc 1 N, t = t ^ N := by simp
  calc ∏ r ∈ Icc 1 N, (1 - zz N r * t) = ∏ r ∈ Icc 1 N, (t * (t⁻¹ - zz N r)) := by
        refine prod_congr rfl fun r _ => ?_
        field_simp
    _ = t ^ N * (t⁻¹ ^ N + Complex.I) := by rw [prod_mul_distrib, hc, h]
    _ = 1 + Complex.I * t ^ N := by
        rw [mul_add, ← mul_pow, mul_inv_cancel₀ ht, one_pow, mul_comm]

private theorem zz_sub_inv (N r : ℕ) :
    zz N r - (zz N r)⁻¹ = 2 * Complex.I * ↑(Real.sin (phi N r)) := by
  rw [zz, ← Complex.exp_neg, Complex.ofReal_sin, Complex.sin]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem zz_ne_zero (N r : ℕ) : zz N r ≠ 0 := Complex.exp_ne_zero _

/-- For the two roots of `λ ^ 2 - c λ - 1 = 0`, the product `(1 + i λ₊ ^ N)(1 + i λ₋ ^ N)`
factors over the roots `z_r`. -/
private theorem pair_prod (N : ℕ) (hN : 0 < N) (lp lm c : ℂ) (hlp : lp ≠ 0) (hlm : lm ≠ 0)
    (hmul : lp * lm = -1) (hadd : lp + lm = c) :
    (1 + Complex.I * lp ^ N) * (1 + Complex.I * lm ^ N) =
      Complex.I * ∏ r ∈ Icc 1 N, (2 * Complex.I * ↑(Real.sin (phi N r)) + c) := by
  calc (1 + Complex.I * lp ^ N) * (1 + Complex.I * lm ^ N)
      = ∏ r ∈ Icc 1 N, ((1 - zz N r * lp) * (1 - zz N r * lm)) := by
        rw [← prod_one_sub_zz_mul N hN lp hlp, ← prod_one_sub_zz_mul N hN lm hlm,
          ← prod_mul_distrib]
    _ = ∏ r ∈ Icc 1 N, ((-zz N r) * (2 * Complex.I * ↑(Real.sin (phi N r)) + c)) := by
        refine prod_congr rfl fun r _ => ?_
        rw [← zz_sub_inv]
        have hz := zz_ne_zero N r
        field_simp
        linear_combination (zz N r) ^ 2 * hmul - zz N r * hadd
    _ = Complex.I * ∏ r ∈ Icc 1 N, (2 * Complex.I * ↑(Real.sin (phi N r)) + c) := by
        rw [prod_mul_distrib, prod_neg_zz N hN]

end LuWuMobiusGrid.Spec

namespace LuWuMobiusGrid.Spec

open Finset Matrix

/-- The angle `π / (2M + 1)`. -/
private noncomputable def ang (M : ℕ) : ℝ := Real.pi / (2 * (M : ℝ) + 1)

/-- The coefficient `c_s = (-1) ^ (s + 1) · 2 cos (s π / (2M + 1))`. -/
private noncomputable def cc (M s : ℕ) : ℝ :=
  (-1) ^ (s + 1) * (2 * Real.cos ((s : ℝ) * Real.pi / (2 * (M : ℝ) + 1)))

/-- The two roots of `λ ^ 2 - c_s λ - 1 = 0`. -/
private noncomputable def lam (M s : ℕ) (b : Bool) : ℝ :=
  if b then (cc M s + Real.sqrt (cc M s ^ 2 + 4)) / 2
  else (cc M s - Real.sqrt (cc M s ^ 2 + 4)) / 2

/-- The eigenvector entries, as a function of the row index. -/
private noncomputable def F (M s : ℕ) (b : Bool) (k : ℕ) : ℝ :=
  (if k % 2 = 0 then lam M s b * (-1) ^ (s + 1) else 1) *
    Real.sin ((s : ℝ) * ((k : ℝ) + 1) * ang M)

private theorem sq_sqrt_cc (M s : ℕ) : Real.sqrt (cc M s ^ 2 + 4) ^ 2 = cc M s ^ 2 + 4 :=
  Real.sq_sqrt (by positivity)

private theorem abs_cc_lt_sqrt (M s : ℕ) : |cc M s| < Real.sqrt (cc M s ^ 2 + 4) := by
  rw [Real.lt_sqrt (abs_nonneg _), sq_abs]
  linarith

private theorem lam_sq (M s : ℕ) (b : Bool) : lam M s b ^ 2 = cc M s * lam M s b + 1 := by
  have hq := sq_sqrt_cc M s
  cases b
  · simp only [lam, Bool.false_eq_true, ↓reduceIte]
    linear_combination (1 / 4 : ℝ) * hq
  · simp only [lam, ↓reduceIte]
    linear_combination (1 / 4 : ℝ) * hq

private theorem lam_mul (M s : ℕ) : lam M s true * lam M s false = -1 := by
  have hq := sq_sqrt_cc M s
  simp only [lam, Bool.false_eq_true, ↓reduceIte]
  linear_combination (-1 / 4 : ℝ) * hq

private theorem lam_add (M s : ℕ) : lam M s true + lam M s false = cc M s := by
  simp only [lam, Bool.false_eq_true, ↓reduceIte]
  ring

private theorem lam_true_pos (M s : ℕ) : 0 < lam M s true := by
  have h := abs_cc_lt_sqrt M s
  have := neg_abs_le (cc M s)
  simp only [lam, ↓reduceIte]
  linarith

private theorem lam_false_neg (M s : ℕ) : lam M s false < 0 := by
  have h := abs_cc_lt_sqrt M s
  have := le_abs_self (cc M s)
  simp only [lam, Bool.false_eq_true, ↓reduceIte]
  linarith

private theorem lam_ne_zero (M s : ℕ) (b : Bool) : lam M s b ≠ 0 := by
  cases b
  · exact (lam_false_neg M s).ne
  · exact (lam_true_pos M s).ne'

private theorem cc_eq_of_lam (M s : ℕ) (b : Bool) : cc M s = lam M s b - (lam M s b)⁻¹ := by
  have h := lam_sq M s b
  have h0 := lam_ne_zero M s b
  field_simp
  linear_combination -h

private theorem arg_pos (M s : ℕ) (hs : 1 ≤ s) : 0 < (s : ℝ) * Real.pi / (2 * (M : ℝ) + 1) := by
  have : (1 : ℝ) ≤ s := by exact_mod_cast hs
  positivity

private theorem arg_lt (M s : ℕ) (hsM : s ≤ M) :
    (s : ℝ) * Real.pi / (2 * (M : ℝ) + 1) < Real.pi / 2 := by
  have hs : (s : ℝ) ≤ M := by exact_mod_cast hsM
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Real.pi_pos]

private theorem cos_arg_pos (M s : ℕ) (hs : 1 ≤ s) (hsM : s ≤ M) :
    0 < Real.cos ((s : ℝ) * Real.pi / (2 * (M : ℝ) + 1)) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · linarith [arg_pos M s hs, Real.pi_pos]
  · exact arg_lt M s hsM

private theorem cc_inj (M s s' : ℕ) (hs : 1 ≤ s) (hsM : s ≤ M) (hs' : 1 ≤ s') (hsM' : s' ≤ M)
    (h : cc M s = cc M s') : s = s' := by
  have hsq : ∀ k : ℕ, ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have h2 : (2 * Real.cos ((s : ℝ) * Real.pi / (2 * (M : ℝ) + 1))) ^ 2 =
      (2 * Real.cos ((s' : ℝ) * Real.pi / (2 * (M : ℝ) + 1))) ^ 2 := by
    have := congrArg (· ^ 2) h
    simp only [cc, mul_pow, hsq, one_mul] at this
    rw [mul_pow, mul_pow]
    exact this
  have hc := cos_arg_pos M s hs hsM
  have hc' := cos_arg_pos M s' hs' hsM'
  have h3 : Real.cos ((s : ℝ) * Real.pi / (2 * (M : ℝ) + 1)) =
      Real.cos ((s' : ℝ) * Real.pi / (2 * (M : ℝ) + 1)) := by
    have := (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp h2
    linarith
  have h4 := Real.injOn_cos ⟨(arg_pos M s hs).le, by linarith [arg_lt M s hsM, Real.pi_pos]⟩
    ⟨(arg_pos M s' hs').le, by linarith [arg_lt M s' hsM', Real.pi_pos]⟩ h3
  have hpos : (0 : ℝ) < 2 * (M : ℝ) + 1 := by positivity
  field_simp at h4
  exact_mod_cast h4

end LuWuMobiusGrid.Spec

namespace LuWuMobiusGrid.Spec

open Finset Matrix

private theorem sum_fin_ite (n k : ℕ) (f : ℕ → ℝ) :
    ∑ b : Fin n, (if b.val = k then f b.val else 0) = if k < n then f k else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i = k then f i else 0) n, Finset.sum_ite_eq']
  simp

private theorem sum_hopMat_mul (M : ℕ) (f : ℕ → ℝ) (hf : f (2 * M) = 0) (a : Fin (2 * M)) :
    ∑ b : Fin (2 * M), (hopMat M 0 a b : ℝ) * f b.val =
      f a.val + if a.val % 2 = 1 then f (a.val + 1) + f (a.val - 1) else 0 := by
  have hsummand : ∀ b : Fin (2 * M), (hopMat M 0 a b : ℝ) * f b.val =
      (if b.val = a.val then f b.val else 0) +
        (if a.val % 2 = 1 then (if b.val = a.val + 1 then f b.val else 0) +
          (if b.val = a.val - 1 then f b.val else 0) else 0) := by
    intro b
    simp only [hopMat, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | omega | (push_cast; ring)
  simp only [hsummand]
  rw [Finset.sum_add_distrib, sum_fin_ite]
  have ha := a.isLt
  split_ifs with h
  · rw [Finset.sum_add_distrib, sum_fin_ite, sum_fin_ite,
      ite_eq_left (by omega : a.val - 1 < 2 * M)]
    by_cases h' : a.val + 1 < 2 * M
    · rw [ite_eq_left h']
    · rw [ite_eq_right h', show a.val + 1 = 2 * M by omega, hf]
  · simp

private theorem F_even (M s : ℕ) (b : Bool) (k : ℕ) (hk : k % 2 = 0) :
    F M s b k = lam M s b * (-1) ^ (s + 1) * Real.sin ((s : ℝ) * ((k : ℝ) + 1) * ang M) := by
  rw [F, ite_eq_left hk]

private theorem F_odd (M s : ℕ) (b : Bool) (k : ℕ) (hk : k % 2 = 1) :
    F M s b k = Real.sin ((s : ℝ) * ((k : ℝ) + 1) * ang M) := by
  rw [F, ite_eq_right (by omega), one_mul]

private theorem sin_two_mul_add_one (M s : ℕ) :
    Real.sin ((s : ℝ) * (((2 * M : ℕ) : ℝ) + 1) * ang M) = 0 := by
  have : (s : ℝ) * (((2 * M : ℕ) : ℝ) + 1) * ang M = (s : ℕ) * Real.pi := by
    rw [ang]
    push_cast
    field_simp
  rw [this, Real.sin_nat_mul_pi]

private theorem F_two_mul (M s : ℕ) (b : Bool) : F M s b (2 * M) = 0 := by
  rw [F, sin_two_mul_add_one, mul_zero]

/-- Reflection symmetry of the sine profile. -/
private theorem sin_rev (M s k : ℕ) (hk : k < 2 * M) :
    Real.sin ((s : ℝ) * (((2 * M - (k + 1) : ℕ) : ℝ) + 1) * ang M) =
      (-1) ^ (s + 1) * Real.sin ((s : ℝ) * ((k : ℝ) + 1) * ang M) := by
  have hcast : ((2 * M - (k + 1) : ℕ) : ℝ) = 2 * (M : ℝ) - ((k : ℝ) + 1) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have : (s : ℝ) * (((2 * M - (k + 1) : ℕ) : ℝ) + 1) * ang M =
      (s : ℕ) * Real.pi - (s : ℝ) * ((k : ℝ) + 1) * ang M := by
    rw [hcast, ang]
    field_simp
    ring
  rw [this, Real.sin_nat_mul_pi_sub, pow_succ]
  ring

/-- The three-term recurrence of the sine profile. -/
private theorem sin_three_term (M s j : ℕ) (hj : 1 ≤ j) :
    Real.sin ((s : ℝ) * (((j + 1 : ℕ) : ℝ) + 1) * ang M) +
        Real.sin ((s : ℝ) * (((j - 1 : ℕ) : ℝ) + 1) * ang M) =
      2 * Real.cos ((s : ℝ) * Real.pi / (2 * (M : ℝ) + 1)) *
        Real.sin ((s : ℝ) * ((j : ℝ) + 1) * ang M) := by
  have h1 : (s : ℝ) * (((j + 1 : ℕ) : ℝ) + 1) * ang M =
      (s : ℝ) * ((j : ℝ) + 1) * ang M + (s : ℝ) * Real.pi / (2 * (M : ℝ) + 1) := by
    rw [ang]
    push_cast
    ring
  have h2 : (s : ℝ) * (((j - 1 : ℕ) : ℝ) + 1) * ang M =
      (s : ℝ) * ((j : ℝ) + 1) * ang M - (s : ℝ) * Real.pi / (2 * (M : ℝ) + 1) := by
    rw [ang, Nat.cast_sub hj]
    push_cast
    ring
  rw [h1, h2, Real.sin_add, Real.sin_sub]
  ring

private theorem Qmat_eigen (M s : ℕ) (b : Bool) (a : Fin (2 * M)) :
    ∑ c : Fin (2 * M), (Qmat M a c : ℝ) * F M s b c.val = lam M s b * F M s b a.val := by
  have hQ : ∀ c, Qmat M a c = hopMat M 0 (Fin.rev a) c := fun c => rfl
  simp only [hQ]
  rw [sum_hopMat_mul M (F M s b) (F_two_mul M s b) (Fin.rev a), Fin.val_rev]
  have ha := a.isLt
  have hl := lam_sq M s b
  have hη : ((-1 : ℝ) ^ (s + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hrev := sin_rev M s a.val ha
  rcases Nat.mod_two_eq_zero_or_one a.val with h | h
  · -- `a` even, its reflection odd
    have h' : (2 * M - (a.val + 1)) % 2 = 1 := by omega
    rw [ite_eq_left h', F_odd _ _ _ _ h',
      F_even _ _ _ _ (by omega : (2 * M - (a.val + 1) + 1) % 2 = 0),
      F_even _ _ _ _ (by omega : (2 * M - (a.val + 1) - 1) % 2 = 0), F_even _ _ _ _ h]
    have h3 := sin_three_term M s (2 * M - (a.val + 1)) (by omega)
    rw [hrev] at h3 ⊢
    simp only [cc] at hl
    linear_combination (lam M s b * (-1) ^ (s + 1)) * h3 -
      ((-1) ^ (s + 1) * Real.sin ((s : ℝ) * ((a.val : ℝ) + 1) * ang M)) * hl
  · -- `a` odd, its reflection even
    have h' : (2 * M - (a.val + 1)) % 2 = 0 := by omega
    rw [ite_eq_right (by omega), add_zero, F_even _ _ _ _ h', F_odd _ _ _ _ h, hrev]
    linear_combination (lam M s b * Real.sin ((s : ℝ) * ((a.val : ℝ) + 1) * ang M)) * hη

end LuWuMobiusGrid.Spec

namespace LuWuMobiusGrid.Spec

open Finset Matrix

private theorem F_zero_ne (M s : ℕ) (b : Bool) (hs : 1 ≤ s) (hsM : s ≤ M) : F M s b 0 ≠ 0 := by
  rw [F_even M s b 0 rfl]
  have hsin : 0 < Real.sin ((s : ℝ) * (((0 : ℕ) : ℝ) + 1) * ang M) := by
    have h1 := arg_pos M s hs
    have h2 := arg_lt M s hsM
    rw [Nat.cast_zero, zero_add, mul_one, ang, ← mul_div_assoc]
    exact Real.sin_pos_of_pos_of_lt_pi h1 (by linarith [Real.pi_pos])
  exact mul_ne_zero (mul_ne_zero (lam_ne_zero M s b) (pow_ne_zero _ (by norm_num))) hsin.ne'

private theorem det_Qmat_pow (M N : ℕ) (hM : 0 < M) :
    (1 + Complex.I • ((Qmat M).map (Int.cast : ℤ → ℂ)) ^ N).det =
      ∏ s ∈ Icc 1 M, ((1 + Complex.I * (lam M s true : ℂ) ^ N) *
        (1 + Complex.I * (lam M s false : ℂ) ^ N)) := by
  let μ : ↥(Icc 1 M) × Bool → ℂ := fun i => (lam M i.1 i.2 : ℂ)
  let v : ↥(Icc 1 M) × Bool → Fin (2 * M) → ℂ := fun i a => (F M i.1 i.2 a.val : ℂ)
  have hμ : Function.Injective μ := by
    rintro ⟨⟨s, hs⟩, b⟩ ⟨⟨s', hs'⟩, b'⟩ h
    simp only [μ, Complex.ofReal_inj] at h
    rw [Finset.mem_Icc] at hs hs'
    have hcc : cc M s = cc M s' := by rw [cc_eq_of_lam M s b, cc_eq_of_lam M s' b', h]
    have hss := cc_inj M s s' hs.1 hs.2 hs'.1 hs'.2 hcc
    subst hss
    have hbb : b = b' := by
      cases b <;> cases b'
      · rfl
      · exact absurd h ((lam_false_neg M s).trans (lam_true_pos M s)).ne
      · exact absurd h ((lam_false_neg M s).trans (lam_true_pos M s)).ne'
      · rfl
    rw [hbb]
  have hv : ∀ i, v i ≠ 0 := by
    rintro ⟨⟨s, hs⟩, b⟩ h
    rw [Finset.mem_Icc] at hs
    have h0 := congrFun h ⟨0, by omega⟩
    simp only [v, Pi.zero_apply, Complex.ofReal_eq_zero] at h0
    exact F_zero_ne M s b hs.1 hs.2 h0
  have hAv : ∀ i, (Qmat M).map (Int.cast : ℤ → ℂ) *ᵥ v i = μ i • v i := by
    rintro ⟨⟨s, hs⟩, b⟩
    ext a
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul, v, μ]
    have h := congrArg Complex.ofReal (Qmat_eigen M s b a)
    push_cast at h
    exact h
  have hcard : Fintype.card (↥(Icc 1 M) × Bool) = Fintype.card (Fin (2 * M)) := by
    simp only [Fintype.card_prod, Fintype.card_coe, Nat.card_Icc, Fintype.card_bool,
      Fintype.card_fin]
    omega
  rw [det_one_add_smul_pow _ μ hμ v hv hAv hcard, Fintype.prod_prod_type]
  simp only [Fintype.prod_bool, μ]
  exact Finset.prod_coe_sort (Icc 1 M) fun s =>
    (1 + Complex.I * (lam M s true : ℂ) ^ N) * (1 + Complex.I * (lam M s false : ℂ) ^ N)

private theorem inner_prod (N : ℕ) (hNodd : Odd N) (η x : ℂ) (hη : η ^ 2 = 1) (f : ℕ → ℂ) :
    ∏ r ∈ Icc 1 N, (2 * Complex.I * f r + η * x) =
      η * ∏ r ∈ Icc 1 N, (2 * Complex.I * η * f r + x) := by
  have hfac : ∀ r ∈ Icc 1 N, 2 * Complex.I * f r + η * x = η * (2 * Complex.I * η * f r + x) :=
    fun r _ => by linear_combination (-2 * Complex.I * f r) * hη
  rw [prod_congr rfl hfac, prod_mul_distrib, prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  obtain ⟨k, rfl⟩ := hNodd
  rw [pow_succ, pow_mul, hη, one_pow, one_mul]

private theorem I_pow_mul_prod_sign (M : ℕ) :
    Complex.I ^ M * ∏ s ∈ Icc 1 M, (-1 : ℂ) ^ (s + 1) = if Even M then 1 else Complex.I := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.prod_Icc_succ_top (by omega), pow_succ,
      show Complex.I ^ M * Complex.I * ((∏ s ∈ Icc 1 M, (-1 : ℂ) ^ (s + 1)) * (-1) ^ (M + 1 + 1))
        = (Complex.I ^ M * ∏ s ∈ Icc 1 M, (-1 : ℂ) ^ (s + 1)) *
          (Complex.I * (-1) ^ (M + 1 + 1)) by ring, ih]
    rcases Nat.even_or_odd M with h | h
    · have h1 : ¬Even (M + 1) := Nat.even_add_one.not.mpr (not_not.mpr h)
      rw [ite_eq_left h, ite_eq_right h1, pow_succ, pow_succ, h.neg_one_pow]
      ring
    · have h1 : Even (M + 1) := Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr h)
      rw [ite_eq_right (Nat.not_even_iff_odd.mpr h), ite_eq_left h1, pow_succ, pow_succ,
        h.neg_one_pow]
      ring_nf
      rw [Complex.I_sq]
      ring

end LuWuMobiusGrid.Spec

namespace LuWuMobiusGrid

open Finset Spec

private theorem re_det_Qmat_pow (M N : ℕ) (hM : 0 < M) (hN : 0 < N) (hNodd : Odd N) :
    Complex.re ((1 - Complex.I) *
        (1 + Complex.I • ((Qmat M).map (Int.cast : ℤ → ℂ)) ^ N).det) =
      Complex.re
        ((1 - Complex.I) *
          ∏ s ∈ Finset.Icc 1 M, ∏ r ∈ Finset.Icc 1 N,
            (2 * Complex.I * (-1 : ℂ) ^ (M + s + 1) *
                ↑(Real.sin ((((4 * r - 1 : ℕ) : ℝ)) * Real.pi / (2 * (N : ℝ)))) +
              2 * ↑(Real.cos ((s : ℝ) * Real.pi / (2 * (M : ℝ) + 1))))) := by
  rw [det_Qmat_pow M N hM]
  have hpair : ∀ s ∈ Icc 1 M, (1 + Complex.I * (lam M s true : ℂ) ^ N) *
      (1 + Complex.I * (lam M s false : ℂ) ^ N) =
      Complex.I * ((-1 : ℂ) ^ (s + 1) * ∏ r ∈ Icc 1 N, (2 * Complex.I * (-1 : ℂ) ^ (s + 1) *
        ↑(Real.sin (phi N r)) + 2 * ↑(Real.cos ((s : ℝ) * Real.pi / (2 * (M : ℝ) + 1))))) := by
    intro s _
    rw [pair_prod N hN _ _ (cc M s : ℂ) (by exact_mod_cast lam_ne_zero M s true)
      (by exact_mod_cast lam_ne_zero M s false) (by exact_mod_cast lam_mul M s)
      (by exact_mod_cast lam_add M s)]
    congr 1
    have hcc : (cc M s : ℂ) = (-1 : ℂ) ^ (s + 1) *
        (2 * ↑(Real.cos ((s : ℝ) * Real.pi / (2 * (M : ℝ) + 1)))) := by
      simp only [cc]
      push_cast
      ring
    rw [hcc, inner_prod N hNodd _ _ (by rw [← pow_mul, mul_comm, pow_mul]; norm_num)]
  rw [prod_congr rfl hpair]
  have hsplit : ∏ s ∈ Icc 1 M, (Complex.I * ((-1 : ℂ) ^ (s + 1) * ∏ r ∈ Icc 1 N,
      (2 * Complex.I * (-1 : ℂ) ^ (s + 1) * ↑(Real.sin (phi N r)) +
        2 * ↑(Real.cos ((s : ℝ) * Real.pi / (2 * (M : ℝ) + 1)))))) =
      (Complex.I ^ M * ∏ s ∈ Icc 1 M, (-1 : ℂ) ^ (s + 1)) * ∏ s ∈ Icc 1 M, ∏ r ∈ Icc 1 N,
        (2 * Complex.I * (-1 : ℂ) ^ (s + 1) * ↑(Real.sin (phi N r)) +
          2 * ↑(Real.cos ((s : ℝ) * Real.pi / (2 * (M : ℝ) + 1)))) := by
    simp only [← mul_assoc]
    rw [prod_mul_distrib, prod_mul_distrib, prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [hsplit, I_pow_mul_prod_sign]
  set P := ∏ s ∈ Finset.Icc 1 M, ∏ r ∈ Finset.Icc 1 N,
          (2 * Complex.I * (-1 : ℂ) ^ (M + s + 1) *
              ↑(Real.sin ((((4 * r - 1 : ℕ) : ℝ)) * Real.pi / (2 * (N : ℝ)))) +
            2 * ↑(Real.cos ((s : ℝ) * Real.pi / (2 * (M : ℝ) + 1)))) with hP
  rcases Nat.even_or_odd M with hMe | hMo
  · have hprod : ∏ s ∈ Icc 1 M, ∏ r ∈ Icc 1 N,
        (2 * Complex.I * (-1 : ℂ) ^ (s + 1) * ↑(Real.sin (phi N r)) +
          2 * ↑(Real.cos ((s : ℝ) * Real.pi / (2 * (M : ℝ) + 1)))) = P := by
      rw [hP]
      refine prod_congr rfl fun s _ => prod_congr rfl fun r _ => ?_
      rw [phi, show (-1 : ℂ) ^ (M + s + 1) = (-1) ^ M * (-1) ^ (s + 1) by
        rw [add_assoc, pow_add], hMe.neg_one_pow, one_mul]
    rw [ite_eq_left hMe, one_mul, hprod]
  · have hconj : ∏ s ∈ Icc 1 M, ∏ r ∈ Icc 1 N,
        (2 * Complex.I * (-1 : ℂ) ^ (s + 1) * ↑(Real.sin (phi N r)) +
          2 * ↑(Real.cos ((s : ℝ) * Real.pi / (2 * (M : ℝ) + 1)))) = (starRingEnd ℂ) P := by
      rw [hP, map_prod]
      refine prod_congr rfl fun s _ => ?_
      rw [map_prod]
      refine prod_congr rfl fun r _ => ?_
      rw [phi, show (-1 : ℂ) ^ (M + s + 1) = (-1) ^ M * (-1) ^ (s + 1) by
        rw [add_assoc, pow_add], hMo.neg_one_pow]
      simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_pow, map_neg,
        map_one, map_ofNat]
      ring
    rw [ite_eq_right (Nat.not_even_iff_odd.mpr hMo), hconj]
    have h : (1 - Complex.I) * (Complex.I * (starRingEnd ℂ) P) =
        (starRingEnd ℂ) ((1 - Complex.I) * P) := by
      simp only [map_mul, map_sub, map_one, Complex.conj_I]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [h, Complex.conj_re]

end LuWuMobiusGrid

/-! ### Assembly of the proof -/

namespace LuWuMobiusGrid

open Finset

private theorem black_pred_eq_white (M c : ℕ) (hc : c ≠ 0) : black M (c - 1) = white M c := by
  ext a
  simp only [black, white, mem_filter, mem_univ, true_and]
  omega

private theorem revSet_black_eq_white (M N : ℕ) (hN : Odd N) :
    revSet (black M (N - 1)) = white M 0 := by
  ext a
  obtain ⟨k, rfl⟩ := hN
  simp only [revSet, black, white, mem_map, mem_filter, mem_univ, true_and,
    Equiv.toEmbedding_apply, Fin.revPerm_apply]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simp only [Fin.val_rev] at hb ⊢
    omega
  · intro ha
    refine ⟨Fin.rev a, ?_, Fin.rev_rev a⟩
    simp only [Fin.val_rev]
    omega

private theorem revSet_symmDiff {n : ℕ} (S T : Finset (Fin n)) :
    revSet (symmDiff S T) = symmDiff (revSet S) (revSet T) := by
  simp only [revSet, map_eq_image]
  exact image_symmDiff _ _ (Equiv.injective _)

private theorem prevState_symmDiff (M N : ℕ) (hN : Odd N) (χ : Fin N → Finset (Fin (2 * M)))
    (c : Fin N) :
    symmDiff (prevState revSet χ c) (white M c) =
      prevState revSet (fun d => symmDiff (χ d) (black M d)) c := by
  unfold prevState
  split_ifs with h
  · rw [revSet_symmDiff, h, ← revSet_black_eq_white M N hN]
  · rw [← black_pred_eq_white M c h]

end LuWuMobiusGrid

open LuWuMobiusGrid

/-- **Lu–Wu formula for perfect matchings of the Möbius grid.** Let $M \ge 1$ and let $N \ge 1$
be odd. Then the number of perfect matchings of the $2M \times N$ Möbius grid equals

$$
\operatorname{Re}\Big[(1 - i) \prod_{s=1}^{M} \prod_{r=1}^{N}
\Big(2i\,(-1)^{M+s+1} \sin\frac{(4r-1)\pi}{2N} + 2\cos\frac{s\pi}{2M+1}\Big)\Big].
$$

This is the unweighted formula for an odd number of columns. -/
theorem lu_wu_mobius_grid_perfect_matching_count {M N : ℕ}
    (hM : 0 < M) (hN : 0 < N) (hNodd : Odd N) :
    (mobiusGridPerfectMatchingCount M N : ℝ) =
      Complex.re
        ((1 - Complex.I) *
          ∏ s ∈ Finset.Icc 1 M, ∏ r ∈ Finset.Icc 1 N,
            (2 * Complex.I * (-1 : ℂ) ^ (M + s + 1) *
                ↑(Real.sin ((((4 * r - 1 : ℕ) : ℝ)) * Real.pi / (2 * (N : ℝ)))) +
              2 * ↑(Real.cos ((s : ℝ) * Real.pi / (2 * (M : ℝ) + 1))))) := by
  rw [← re_det_Qmat_pow M N hM hN hNodd]
  have hpow : (Qmat M).map (Int.cast : ℤ → ℂ) ^ N = (Qmat M ^ N).map (Int.cast : ℤ → ℂ) :=
    (Matrix.map_pow (Qmat M) (Int.castRingHom ℂ) N).symm
  rw [hpow, ← sum_sgnRev_minor, ← Int.cast_natCast]
  congr 1
  -- What remains is an identity between integers. First, each column count is a minor.
  have h1 : (mobiusGridPerfectMatchingCount M N : ℤ) =
      ∑ χ : Fin N → Finset (Fin (2 * M)), ∏ c : Fin N,
        minor (hopMat M c) (symmDiff (prevState revSet χ c) (white M c))
          (symmDiff (χ c) (black M c)) := by
    rw [count_eq_sum_prod M N hN]
    push_cast
    refine Finset.sum_congr rfl fun χ _ => Finset.prod_congr rfl fun c _ => ?_
    rw [← colCount_symmDiff_eq_minor, symmDiff_symmDiff_cancel_right,
      symmDiff_symmDiff_cancel_right]
  -- Change variables from the crossing sets to the particle sets.
  let e : (Fin N → Finset (Fin (2 * M))) ≃ (Fin N → Finset (Fin (2 * M))) :=
    { toFun := fun χ d => symmDiff (χ d) (black M d)
      invFun := fun χ d => symmDiff (χ d) (black M d)
      left_inv := fun χ => by funext d; simp
      right_inv := fun χ => by funext d; simp }
  have h2 : (mobiusGridPerfectMatchingCount M N : ℤ) =
      ∑ K : Fin N → Finset (Fin (2 * M)), ∏ c : Fin N,
        cpd (hopMat M c.val) (prevState revSet K c) (K c) := by
    rw [h1]
    refine Fintype.sum_equiv e _ _ fun χ => ?_
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [prevState_symmDiff M N hNodd]
    rfl
  -- Cauchy–Binet along the chain of columns, then the reversal at the seam.
  rw [h2, sum_prod_prevState N hN (fun c => cpd (hopMat M c)) revSet, cpd_prod_range N hN]
  have h3 : ∀ k : Finset (Fin (2 * M)),
      cpd ((List.range N).map (hopMat M)).prod (revSet k) k =
        sgnRev k.card * minor (Qmat M ^ N) k k := by
    intro k
    simp only [cpd, Matrix.of_apply]
    rw [minor_revSet_left, rev_prod_hopMat M N hNodd, Int.cast_id]
  simp only [h3]

end MetaMathlibExt
