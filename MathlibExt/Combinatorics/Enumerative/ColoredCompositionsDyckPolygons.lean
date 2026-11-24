/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Composition
public import MathlibExt.Combinatorics.Enumerative.DyckPeakDescents
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Sum
import MathlibExt.Combinatorics.Lists.RaneyCycleLemma

/-!
# Colored compositions, Dyck paths, and polygon partitions

We prove the binomial identity `choose_mul_coloredDyckPathCount_eq` of
Gil, Hoover, and Shearer, *Bijections Between Colored
Compositions, Dyck Paths, and Polygon Partitions*, Journal of Integer Sequences
27 (2024), Article 24.5.2. The color of a part depends only on its positive size `j`,
which has `γ j` choices for a coloring sequence `γ : ℕ → ℕ`.

* `coloredCompositionCount γ n k` (`c_{n,k}(γ)`): compositions of `n` with `k`
  parts, part `j` taking `γ j` colors.
* `coloredDyckPathCount γ n k` (`d_{n,k}(γ)`): Dyck paths (Mathlib's `DyckWord`)
  of semilength `n` with `k` peaks, the primitive block `U D^j` formed by a peak
  and its maximal descent taking `γ j` colors.
* `coloredPolygonDissectionCount γ n k` (`p_{n,k}(γ)`): partitions of a rooted
  convex `(n+2)`-gon by `k - 1` noncrossing diagonals into `k` polygons, each
  `(j+2)`-gon taking `γ j` colors. The vertices are `0, …, n+1` in cyclic order
  and the root (base) side is `(0, n+1)`.

## Proof of the counting identity

Encode both families by a list of pairs `(a, b)`, stored in reverse chronological order.
For a Dyck path, prepend one up step and read each run `U^a D^b`. For a polygon, read the
non-base boundary edges from left to right. Each pair advances by `a` edges and then closes
a face with `b + 2` vertices. Several faces can close at the same vertex, so polygons allow
`a = 0`. In both encodings the color factor of the pair is `γ b`.

The rises sum to `n + 1` and the falls to `n`. At the end of each chronological block the
running excess of rises over falls must be positive. Raney's cycle lemma picks out exactly
one of the `k` rotations of any word with these totals. Counting the possible rises by
stars and bars leaves the same weighted sum over falls for both families.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Number of colored compositions.** Let $\gamma = (\gamma_1, \gamma_2, \dots)$ be a sequence
of natural numbers and let $n, k$ be natural numbers. The number $c_{n,k}(\gamma)$ of
$\gamma$-colored compositions of $n$ with $k$ parts counts the compositions of $n$ with exactly $k$
parts in which each part equal to $j$ carries one of $\gamma_j$ colors: it is the sum, over all
compositions $(a_1, \dots, a_k)$ of $n$ into $k$ positive parts, of
$\gamma_{a_1} \cdots \gamma_{a_k}$.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Compositions). -/
public def coloredCompositionCount (γ : ℕ → ℕ) (n k : ℕ) : ℕ :=
  ∑ c : Composition n with c.length = k, (c.blocks.map γ).prod

/-- **Compositions of 3 into two parts.** With one color for every part ($\gamma_j = 1$ for all
$j$), the number of colored compositions of $3$ with $2$ parts is $c_{3,2}(\gamma) = 2$: the
compositions $(1,2)$ and $(2,1)$.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2. -/
public theorem coloredCompositionCount_one_three_two :
    coloredCompositionCount (fun _ => 1) 3 2 = 2 := by
  decide +kernel

/-- **Number of colored Dyck paths.** Let $\gamma = (\gamma_1, \gamma_2, \dots)$ be a sequence of
natural numbers and let $n, k$ be natural numbers. In a Dyck path, each peak $UD$ together with the
maximal run of $D$ steps starting at its $D$ forms a primitive block $UD^j$. The number
$d_{n,k}(\gamma)$ counts the Dyck paths of semilength $n$ with exactly $k$ peaks in which each
primitive block $UD^j$ carries one of $\gamma_j$ colors: it is the sum, over all Dyck paths of
semilength $n$ with $k$ peaks, of the product of $\gamma_j$ over their primitive blocks $UD^j$.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Dyck paths). -/
public def coloredDyckPathCount (γ : ℕ → ℕ) (n k : ℕ) : ℕ :=
  ∑ p : {p : DyckWord // p.semilength = n} with (dyckPeakDescents p.1.toList).length = k,
    ((dyckPeakDescents p.1.toList).map γ).prod

/-- **Dyck paths of semilength 3 with two peaks.** With one color for every block ($\gamma_j = 1$
for all $j$), the number of colored Dyck paths of semilength $3$ with $2$ peaks is
$d_{3,2}(\gamma) = 3$, a Narayana number.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2. -/
public theorem coloredDyckPathCount_one_three_two :
    coloredDyckPathCount (fun _ => 1) 3 2 = 3 := by
  decide +kernel

/-- **Diagonals of a convex polygon.** For $n \in \mathbb{N}$, label the vertices of the convex
$(n+2)$-gon $0, 1, \dots, n+1$ in cyclic order. Its diagonals are the pairs $(a, b)$ of natural
numbers with $a + 2 \le b \le n + 1$ and $(a, b) \ne (0, n+1)$; the excluded pair is the side
joining the vertices $0$ and $n+1$.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Polygon partitions). -/
public def polygonDiagonals (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 2) ×ˢ Finset.range (n + 2)).filter fun e =>
    e.1 + 2 ≤ e.2 ∧ e ≠ (0, n + 1)

/-- **Noncrossing sets of diagonals.** A finite set $D$ of pairs of natural numbers is
noncrossing when there are no $(a, b) \in D$ and $(c, d) \in D$ with $a < c < b < d$. For
diagonals $(a, b)$ with $a < b$ of a convex polygon whose vertices are labelled by natural numbers
in cyclic order, this says that no two diagonals of $D$ cross in the interior of the polygon.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Polygon partitions). -/
public def IsNoncrossingDiagonalSet (D : Finset (ℕ × ℕ)) : Prop :=
  ∀ e ∈ D, ∀ f ∈ D, ¬ (e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2)

/-- Noncrossing is decidable.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2. -/
public instance : DecidablePred IsNoncrossingDiagonalSet := fun D => by
  unfold IsNoncrossingDiagonalSet
  infer_instance

/-- **Size of the polygon under a chord.** Let $D$ be a finite set of pairs of natural numbers
and let $e = (a, b)$ be a pair of natural numbers. The face size of $e$ in $D$ is $2$ plus the
number of natural numbers $v$ with $a < v < b$ for which there is no pair $(c, d) \in D$ other
than $e$ with $a \le c < v < d \le b$. When $D$ is a noncrossing set of diagonals of the convex
$(n+2)$-gon with vertices $0, \dots, n+1$ in cyclic order and $e$ is a diagonal in $D$ or the root
side $(0, n+1)$, this is the number of vertices of the polygon of the dissection that lies
directly under $e$, on the side of the vertices $a, \dots, b$: the endpoints $a$ and $b$ and the
vertices between them that no other chord of $D$ under $e$ cuts off. Every polygon of the
dissection lies directly under exactly one such chord.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Polygon partitions). -/
public def dissectionFaceSize (D : Finset (ℕ × ℕ)) (e : ℕ × ℕ) : ℕ :=
  2 + ((Finset.Ioo e.1 e.2).filter fun v =>
    ∀ f ∈ D, f ≠ e → ¬ (e.1 ≤ f.1 ∧ f.1 < v ∧ v < f.2 ∧ f.2 ≤ e.2)).card

/-- **Colored polygon dissection count.** Let $\gamma : \mathbb{N} \to \mathbb{N}$ and
$n, k \in \mathbb{N}$. For $n \ge 1$, label the vertices of the convex $(n+2)$-gon $0, \dots, n+1$
in cyclic order, with root side $(0, n+1)$. Then $p_{n,k}(\gamma)$ is the sum, over all sets $D$ of
$k - 1$ pairwise noncrossing diagonals of this polygon, of the product, over the root side and
the diagonals $e$ of $D$, of $\gamma(j_e)$, where $j_e + 2$ is the number of vertices of the
polygon of the dissection lying directly under $e$. Every polygon of the dissection lies directly
under exactly one of these chords, so $p_{n,k}(\gamma)$ counts the partitions of the rooted
$(n+2)$-gon into $k$ polygons by $k - 1$ noncrossing diagonals in which each $(j+2)$-gon is
colored in one of $\gamma(j)$ ways. For $k = 0$ the sum is empty, so $p_{n,0}(\gamma) = 0$.
For $n = 0$ (a degenerate $2$-gon) the count is set to $p_{0,k}(\gamma) = 0$, so $\gamma(0)$
never enters.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Polygon partitions). -/
public def coloredPolygonDissectionCount (γ : ℕ → ℕ) (n k : ℕ) : ℕ :=
  if n = 0 then 0 else
  ∑ D ∈ (polygonDiagonals n).powerset with IsNoncrossingDiagonalSet D ∧ D.card + 1 = k,
    ∏ e ∈ insert (0, n + 1) D, γ (dissectionFaceSize D e - 2)

/-- **Dissections of a pentagon into two polygons.** With one color for every polygon, that is
$\gamma(j) = 1$ for all $j$, the colored polygon dissection count satisfies $p_{3,2}(\gamma) = 5$:
a convex pentagon has five diagonals, and each one cuts it into two polygons.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2. -/
public theorem coloredPolygonDissectionCount_one_three_two :
    coloredPolygonDissectionCount (fun _ => 1) 3 2 = 5 := by
  decide +kernel

/-- **Colored dissections of a hexagon by one diagonal.** Let $\gamma_1 = 2$, $\gamma_2 = 3$,
$\gamma_3 = 5$ and $\gamma_j = 0$ for every other $j$. The number of partitions of a rooted convex
hexagon by one diagonal into $2$ polygons in which each $(j+2)$-gon carries one of $\gamma_j$
colors is $p_{4,2}(\gamma) = 87$: three diagonals cut the hexagon into two quadrilaterals and six
cut it into a triangle and a pentagon, giving $3 \cdot 3^2 + 6 \cdot 2 \cdot 5 = 87$.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2. -/
public theorem coloredPolygonDissectionCount_hexagon_two :
    coloredPolygonDissectionCount (fun j => if j = 1 then 2 else if j = 2 then 3
      else if j = 3 then 5 else 0) 4 2 = 87 := by
  decide +kernel

namespace choose_mul_coloredDyckPathCount_eq

open Finset

private abbrev Chords := Finset (ℕ × ℕ)

private def exposedAt (D : Chords) (v : ℕ) : Prop :=
  ∀ e ∈ D, ¬ (e.1 < v ∧ v < e.2)

private instance exposedAtDecidable (D : Chords) (v : ℕ) : Decidable (exposedAt D v) := by
  unfold exposedAt
  infer_instance

-- The exposed vertices below r are the left ends of the still available boundary edges.
private def frontier (r : ℕ) (D : Chords) : Finset ℕ :=
  (range r).filter (exposedAt D)

private lemma mem_frontier {r v : ℕ} {D : Chords} :
    v ∈ frontier r D ↔ v < r ∧ exposedAt D v := by simp [frontier]

private lemma extend_leaf {r : ℕ} {D : Chords} (hb : ∀ e ∈ D, e.2 ≤ r) :
    frontier (r + 1) D = insert r (frontier r D) := by
  have h : exposedAt D r := fun e he ⟨_, hr⟩ => (hb e he).not_gt hr
  simp [frontier, range_add_one, filter_insert, h]

private lemma frontier_close {r s : ℕ} {D : Chords} :
    frontier r (insert (s, r) D) = (frontier r D).filter (· ≤ s) := by
  ext v
  simp only [mem_frontier, mem_filter, exposedAt, forall_mem_insert]
  exact ⟨fun ⟨h, h₁, h₂⟩ => ⟨⟨h, h₂⟩, by omega⟩,
    fun ⟨⟨h, h₂⟩, h₁⟩ => ⟨h, by omega, h₂⟩⟩

private lemma noncrossing_close {r s : ℕ} {D : Chords} (hD : IsNoncrossingDiagonalSet D)
    (hb : ∀ e ∈ D, e.2 ≤ r) (hs : s ∈ frontier r D) :
    IsNoncrossingDiagonalSet (insert (s, r) D) := by
  obtain ⟨_, hs⟩ := mem_frontier.mp hs
  rintro e he f hf
  rcases mem_insert.mp he with rfl | he <;> rcases mem_insert.mp hf with rfl | hf
  · simp
  · exact fun h => (hb _ hf).not_gt h.2.2
  · exact fun h => hs e he ⟨h.1, h.2.1⟩
  · exact hD e he f hf

private lemma size_new {r s : ℕ} {D : Chords} (hs : s ∈ frontier r D)
    (hb : ∀ e ∈ D, e.2 ≤ r) (hne : (s, r) ∉ D) :
    dissectionFaceSize (insert (s, r) D) (s, r) - 2 =
      ((frontier r D).filter (s < ·)).card := by
  obtain ⟨_, hs⟩ := mem_frontier.mp hs
  simp only [dissectionFaceSize, forall_mem_insert, ne_eq, not_true_eq_false, false_implies,
    true_and, Nat.add_sub_cancel_left]
  congr 1
  ext v
  simp only [mem_filter, mem_Ioo, mem_frontier]
  constructor
  · rintro ⟨⟨hsv, hvr⟩, hv⟩
    refine ⟨⟨hvr, ?_⟩, hsv⟩
    intro f hf hvf
    have hsf : s ≤ f.1 := by
      by_contra! h
      exact hs f hf ⟨h, by omega⟩
    exact hv f hf (fun h => hne (h ▸ hf)) ⟨hsf, hvf.1, hvf.2, hb f hf⟩
  · rintro ⟨⟨hvr, hv⟩, hsv⟩
    exact ⟨⟨hsv, hvr⟩, fun f hf _ h => hv f hf ⟨h.2.1, h.2.2.1⟩⟩

private lemma size_old {r s t : ℕ} {D : Chords} (hst : s < t) (ht : t ∈ frontier r D)
    {e : ℕ × ℕ} (he : e ∈ D) :
    dissectionFaceSize (insert (s, r) D) e = dissectionFaceSize D e := by
  obtain ⟨htr, ht⟩ := mem_frontier.mp ht
  unfold dissectionFaceSize
  congr 2
  ext v
  simp only [mem_filter, forall_mem_insert]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · rintro ⟨hv, h⟩
    refine ⟨hv, ⟨?_, h⟩⟩
    rintro _ ⟨h₁, _, _, h₂⟩
    exact ht e he ⟨by omega, by omega⟩

-- To undo a closure, erase the longest chord ending at r. At least one vertex strictly
-- between its ends becomes exposed, so the recovered fall is positive.
private lemma expose_after_erase {s r : ℕ} {D : Chords} (hm : (s, r) ∈ D)
    (hnc : IsNoncrossingDiagonalSet D) (hlen : s + 2 ≤ r) (hb : ∀ e ∈ D, e.2 ≤ r)
    (hmin : ∀ i, (i, r) ∈ D → s ≤ i) :
    s ∈ frontier r (D.erase (s, r)) ∧ ∃ t ∈ frontier r (D.erase (s, r)), s < t := by
  have hs : exposedAt (D.erase (s, r)) s := by
    intro f hf h
    obtain ⟨_, hf⟩ := mem_erase.mp hf
    by_cases hr : f.2 = r
    · have := hmin f.1 (by simpa [← hr] using hf)
      omega
    · exact hnc f hf (s, r) hm ⟨h.1, h.2, lt_of_le_of_ne (hb f hf) hr⟩
  refine ⟨mem_frontier.mpr ⟨by omega, hs⟩, ?_⟩
  let A := (D.erase (s, r)).filter (fun f => f.1 = s)
  let t := max (s + 1) (A.sup Prod.snd)
  have hmt (f) (hf : f ∈ A) : f.2 ≤ t :=
    (Finset.le_sup (f := Prod.snd) hf).trans (Nat.le_max_right _ _)
  have hst : s < t := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
  have htr : t < r := by
    apply max_lt (by omega)
    apply (Finset.sup_lt_iff (by omega : 0 < r)).mpr
    intro f hf
    obtain ⟨hf, he⟩ := mem_filter.mp hf
    obtain ⟨hne, hf⟩ := mem_erase.mp hf
    exact lt_of_le_of_ne (hb f hf) (fun h => hne (Prod.ext he h))
  refine ⟨t, mem_frontier.mpr ⟨htr, ?_⟩, hst⟩
  intro f hf ⟨hft, htf⟩
  have hsf : s ≤ f.1 := by
    by_contra! h
    exact hs f hf ⟨h, by omega⟩
  by_cases he : f.1 = s
  · exact htf.not_ge (hmt _ (mem_filter.mpr ⟨hf, he⟩))
  have hst' : s + 1 < t := by omega
  have hsup : A.sup Prod.snd = t := by dsimp [t] at *; omega
  obtain ⟨e, he, heq⟩ := exists_mem_eq_sup A
    (show A.Nonempty by
      by_contra! hem
      simp [hem] at hsup
      omega) Prod.snd
  obtain ⟨heD, he₁⟩ := mem_filter.mp he
  apply hnc e (mem_of_mem_erase heD) f (mem_of_mem_erase hf)
  exact ⟨by omega, by omega, by omega⟩

private lemma rank_count {S : Finset ℕ} {i : Fin S.card} :
    (S.filter (S.orderEmbOfFin rfl i < ·)).card = S.card - 1 - i.val := by
  let f := S.orderEmbOfFin rfl
  have he : S.filter (f i < ·) = (Ioi i).map f.toEmbedding := by
    ext a
    simp only [mem_filter, mem_map, mem_Ioi]
    constructor
    · rintro ⟨ha, h⟩
      obtain ⟨j, rfl⟩ := show a ∈ Set.range (S.orderEmbOfFin rfl) by
        rwa [S.range_orderEmbOfFin]
      exact ⟨j, f.lt_iff_lt.mp h, rfl⟩
    · rintro ⟨j, hij, rfl⟩
      exact ⟨S.orderEmbOfFin_mem rfl _, f.strictMono hij⟩
  change (S.filter (f i < ·)).card = _
  simp [he, Fin.card_Ioi]

private lemma rank_unique (S : Finset ℕ) {b : ℕ} (h : b < S.card) :
    ∃! s, s ∈ S ∧ (S.filter (s < ·)).card = b := by
  let i : Fin S.card := ⟨S.card - 1 - b, by omega⟩
  refine ⟨S.orderEmbOfFin rfl i, ⟨S.orderEmbOfFin_mem rfl _, ?_⟩, ?_⟩
  · rw [rank_count]
    dsimp [i]
    omega
  · rintro y ⟨hy, hcard⟩
    obtain ⟨j, rfl⟩ := show y ∈ Set.range (S.orderEmbOfFin rfl) by
      rwa [S.range_orderEmbOfFin]
    rw [rank_count] at hcard
    congr 1
    apply Fin.ext
    dsimp [i]
    omega

private abbrev Word := List (ℕ × ℕ)

private def rises (w : Word) := (w.map Prod.fst).sum
private def falls (w : Word) := (w.map Prod.snd).sum
private def weight (γ : ℕ → ℕ) (w : Word) := (w.map (fun e => γ e.2)).prod

private def Valid : Word → Prop
  | [] => True
  | e :: w => Valid w ∧ 0 < e.2 ∧ falls (e :: w) < rises (e :: w)

-- Reading a block appends a boundary segment of length a and closes a face. Its left
-- endpoint is the unique exposed vertex with exactly b exposed vertices to its right.
private inductive Traces : Word → Chords → Prop where
  | nil : Traces [] ∅
  | cons {w D a b s} (prev : Traces w D) (hb : 0 < b)
      (hs : s ∈ frontier (a + rises w) D)
      (hrank : ((frontier (a + rises w) D).filter (s < ·)).card = b) :
      Traces ((a, b) :: w) (insert (s, a + rises w) D)

private def rightEnd (D : Chords) := D.sup Prod.snd

private lemma extend_count {r : ℕ} {D : Chords} (hb : ∀ e ∈ D, e.2 ≤ r) (a : ℕ) :
    (frontier (a + r) D).card = a + (frontier r D).card := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, extend_leaf (fun e he => (hb e he).trans (by omega)), card_insert_of_notMem,
      ih]
    · omega
    · exact fun h => (mem_frontier.mp h).1.false

private structure TraceStats (w : Word) (D : Chords) : Prop where
  valid : Valid w
  balanced : (frontier (rises w) D).card + falls w = rises w
  ending : rightEnd D = rises w
  length : D.card = w.length
  spans : ∀ e ∈ D, e.1 + 2 ≤ e.2
  compatible : IsNoncrossingDiagonalSet D
  colors : ∀ γ, (∏ e ∈ D, γ (dissectionFaceSize D e - 2)) = weight γ w

private lemma trace_stats {w D} (h : Traces w D) : TraceStats w D := by
  induction h with
  | nil =>
    constructor <;> simp [Valid, frontier, falls, rises, rightEnd, IsNoncrossingDiagonalSet, weight]
  | @cons w D a b s _ hb hs hrank ih =>
    let r := a + rises w
    have hbound (e) (he : e ∈ D) : e.2 ≤ rises w := ih.ending ▸
      (Finset.le_sup (s := D) (f := Prod.snd) he)
    have hbr (e) (he : e ∈ D) : e.2 ≤ r := (hbound e he).trans (Nat.le_add_left ..)
    have hex : ((frontier r D).filter (s < ·)).Nonempty := card_pos.mp (hrank ▸ hb)
    obtain ⟨t, ht⟩ := hex
    obtain ⟨ht, hst⟩ := mem_filter.mp ht
    have htr := (mem_frontier.mp ht).1
    have hne : (s, r) ∉ D := fun hm => (mem_frontier.mp ht).2 _ hm ⟨hst, htr⟩
    have hsplit := card_filter_add_card_filter_not (s := frontier r D) (p := (s < ·))
    simp only [not_lt] at hsplit
    have hg := ih.balanced
    have hr := extend_count hbound a
    change s ∈ frontier r D at hs
    change ((frontier r D).filter (s < ·)).card = b at hrank
    change (frontier r D).card = _ at hr
    have hpos : 0 < ((frontier r D).filter (· ≤ s)).card :=
      card_pos.mpr ⟨s, mem_filter.mpr ⟨hs, le_rfl⟩⟩
    constructor
    · exact ⟨ih.valid, hb, by simpa [rises, falls, ← Nat.add_assoc] using
        (show b + falls w < a + rises w by omega)⟩
    · change (frontier r (insert (s, r) D)).card + (b + falls w) = r
      rw [frontier_close]
      omega
    · change (insert (s, r) D).sup Prod.snd = r
      rw [sup_insert]
      apply max_eq_left
      change rightEnd D ≤ a + rises w
      rw [ih.ending]
      omega
    · change (insert (s, r) D).card = w.length + 1
      rw [card_insert_of_notMem hne, ih.length]
    · intro e he
      rcases mem_insert.mp he with rfl | he
      · change s + 2 ≤ r
        omega
      · exact ih.spans e he
    · exact noncrossing_close ih.compatible hbr hs
    · intro γ
      rw [prod_insert hne, size_new hs hbr hne, hrank]
      change γ b * _ = γ b * weight γ w
      congr 1
      rw [← ih.colors]
      exact prod_congr rfl fun e he => by rw [size_old hst ht he]

private lemma exists_trace {w : Word} (hv : Valid w) : ∃! D, Traces w D := by
  induction w with
  | nil => exact ⟨∅, .nil, fun D h => by cases h; rfl⟩
  | cons e w ih =>
    obtain ⟨a, b⟩ := e
    obtain ⟨hv, hb, hbal⟩ := hv
    obtain ⟨D, hD, uniq⟩ := ih hv
    have st := trace_stats hD
    have hbound (e) (he : e ∈ D) : e.2 ≤ rises w := st.ending ▸
      (Finset.le_sup (s := D) (f := Prod.snd) he)
    have hext := extend_count hbound a
    have := st.balanced
    change b + falls w < a + rises w at hbal
    obtain ⟨s, ⟨hs, hr⟩, unique⟩ := rank_unique (frontier (a + rises w) D)
      (show b < (frontier (a + rises w) D).card by omega)
    refine ⟨_, .cons hD hb hs hr, ?_⟩
    intro D' hD'
    cases hD' with
    | @cons _ E _ _ t hE _ ht ht' =>
      obtain rfl := uniq E hE
      rw [unique _ ⟨ht, ht'⟩]

-- The rightmost endpoint, then the least left endpoint there, determine the last block.
private lemma peel_trace {r s D w} (hw : Traces w D) (hr : rightEnd D = r)
    (hm : (s, r) ∈ D) (hmin : ∀ i, (i, r) ∈ D → s ≤ i) :
    ∃ w', Traces w' (D.erase (s, r)) ∧
      w = (r - rises w', ((frontier r (D.erase (s, r))).filter (s < ·)).card) :: w' := by
  cases hw with
  | nil => simp at hm
  | @cons w E a b t hp hb ht hrank =>
    have h := trace_stats (Traces.cons hp hb ht hrank)
    have hEnd : r = a + rises w := hr.symm.trans h.ending
    rw [hEnd] at hm hmin ⊢
    obtain ⟨v, hv⟩ := card_pos.mp (hrank ▸ hb)
    obtain ⟨hv, htv⟩ := mem_filter.mp hv
    obtain ⟨hvr, hv⟩ := mem_frontier.mp hv
    have hst := hmin t (mem_insert_self ..)
    have ht' : (t, a + rises w) ∉ E := fun hf => hv _ hf ⟨htv, hvr⟩
    have hs : s = t := by
      rcases mem_insert.mp hm with h | h
      · exact congrArg Prod.fst h
      · exact (hv _ h ⟨by dsimp; omega, hvr⟩).elim
    subst t
    rw [erase_insert ht']
    exact ⟨w, hp, by simp [hrank]⟩

private lemma exists_word (D : Chords) (hD : IsNoncrossingDiagonalSet D)
    (hl : ∀ e ∈ D, e.1 + 2 ≤ e.2) : ∃! w, Traces w D := by
  induction D using Finset.strongInductionOn with
  | _ D ih =>
    rcases D.eq_empty_or_nonempty with rfl | hne
    · exact ⟨[], .nil, fun w h => List.length_eq_zero_iff.mp (by simpa using
        (trace_stats h).length.symm)⟩
    let r := rightEnd D
    have hb (e) (he : e ∈ D) : e.2 ≤ r := Finset.le_sup (f := Prod.snd) he
    obtain ⟨f, hf, hfr⟩ := D.exists_mem_eq_sup hne Prod.snd
    have hex : (D.filter (·.2 = r)).Nonempty := ⟨f, mem_filter.mpr ⟨hf, hfr.symm⟩⟩
    obtain ⟨⟨s, t⟩, hst, hmin⟩ := (D.filter (·.2 = r)).exists_min_image Prod.fst hex
    obtain ⟨hm, ht⟩ := mem_filter.mp hst
    change t = r at ht
    subst t
    have hleast (i) (hi : (i, r) ∈ D) : s ≤ i := hmin _ (mem_filter.mpr ⟨hi, rfl⟩)
    let E := D.erase (s, r)
    obtain ⟨w, hw, unique⟩ := ih E (erase_ssubset hm)
      (fun e he f hf => hD e (mem_of_mem_erase he) f (mem_of_mem_erase hf))
      (fun e he => hl e (mem_of_mem_erase he))
    obtain ⟨hs, t, ht, hst⟩ := expose_after_erase hm hD (hl _ hm) hb hleast
    let b := ((frontier r E).filter (s < ·)).card
    have hbpos : 0 < b := card_pos.mpr ⟨t, mem_filter.mpr ⟨ht, hst⟩⟩
    have heq : (r - rises w) + rises w = r := Nat.sub_add_cancel <| by
      rw [← (trace_stats hw).ending]
      exact Finset.sup_le (fun e he => hb e (mem_of_mem_erase he))
    refine ⟨(r - rises w, b) :: w, ?_, ?_⟩
    · have hmake := @Traces.cons w E (r - rises w) b s hw hbpos
        (by rwa [heq]) (by rw [heq])
      simpa [heq, E, hm] using hmake
    · intro v hv
      obtain ⟨w', hw', rfl⟩ := peel_trace hv rfl hm hleast
      rw [unique w' hw']

-- All lists of k entries at least m, with n units above those minima.
private def parts (m : ℕ) : ℕ → ℕ → Finset (List ℕ)
  | 0, n => if n = 0 then {[]} else ∅
  | k + 1, n => (range (n + 1)).biUnion fun i =>
      (parts m k i).image (List.cons (m + (n - i)))

private lemma mem_parts {m k n : ℕ} {l : List ℕ} :
    l ∈ parts m k n ↔ l.length = k ∧ l.sum = n + k * m ∧ ∀ x ∈ l, m ≤ x := by
  induction k generalizing n l with
  | zero =>
    cases l <;> by_cases h : n = 0 <;> simp [parts, h, eq_comm]
  | succ k ih =>
    cases l with
    | nil => simp [parts]
    | cons a l =>
      simp only [parts, mem_biUnion, mem_range, mem_image, List.cons.injEq,
        exists_eq_right_right, ih, List.length_cons, Nat.succ.injEq, List.sum_cons,
        List.forall_mem_cons, Nat.succ_mul]
      constructor
      · rintro ⟨i, hi, ⟨hl, hs, hv⟩, heq⟩
        exact ⟨hl, by omega, by omega, hv⟩
      · rintro ⟨hl, hs, ha, hv⟩
        have hmin : k * m ≤ l.sum := by
          rw [← hl]
          clear * - hv
          induction l with
          | nil => simp
          | cons x xs ih =>
            rw [List.length_cons, Nat.succ_mul, List.sum_cons]
            have := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
            have := hv x List.mem_cons_self
            omega
        exact ⟨l.sum - k * m, by omega, ⟨hl, by omega, hv⟩, by omega⟩

private lemma card_parts (m n k : ℕ) :
    (parts m (k + 1) n).card = (n + k).choose k := by
  induction k generalizing n with
  | zero =>
    have : parts m 1 n = {[n + m]} := by
      ext l
      rw [mem_parts]
      cases l with
      | nil => simp
      | cons a l =>
        cases l <;> simp [and_iff_left_of_imp]
        omega
    simp [this]
  | succ k ih =>
    rw [parts, card_biUnion]
    · simp_rw [card_image_of_injective _ List.cons_injective, ih]
      simpa [Nat.add_assoc] using Nat.sum_range_add_choose n k
    · intro i hi j hj hne
      apply Finset.disjoint_left.mpr
      rintro l hl hl'
      obtain ⟨a, _, rfl⟩ := mem_image.mp hl
      obtain ⟨b, _, h⟩ := mem_image.mp hl'
      have := (List.cons.inj h).1
      have := mem_range.mp hi
      have := mem_range.mp hj
      omega

-- A rise has minimum m and a fall has minimum one. The parameters x and y
-- record the remaining rise and fall units.
private def words (m k x y : ℕ) : Finset Word :=
  ((parts m k x) ×ˢ (parts 1 k y)).image (fun p => p.1.zip p.2)

private lemma mem_words {m k x y : ℕ} {w : Word} :
    w ∈ words m k x y ↔
      w.length = k ∧ rises w = x + k * m ∧ falls w = y + k ∧
      ∀ e ∈ w, m ≤ e.1 ∧ 0 < e.2 := by
  simp only [words, mem_image, mem_product, mem_parts, Nat.mul_one, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨⟨ha, hsa, hma⟩, hb, hsb, hmb⟩, rfl⟩
    have heq : a.length = b.length := ha.trans hb.symm
    refine ⟨by simp [ha, hb], ?_, ?_, ?_⟩
    · simpa [rises, List.map_fst_zip heq.le] using hsa
    · simpa [falls, List.map_snd_zip heq.ge] using hsb
    · intro e he
      exact ⟨hma _ (List.of_mem_zip he).1, hmb _ (List.of_mem_zip he).2⟩
  · rintro ⟨hlen, hr, hf, h⟩
    refine ⟨w.map Prod.fst, w.map Prod.snd, ⟨⟨by simpa, hr, ?_⟩, by simpa, hf, ?_⟩, ?_⟩
    · simpa using fun e he => (h e he).1
    · intro j hj
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hj
      exact (h e he).2
    · exact (List.zip_of_prod rfl rfl).symm

private lemma words_weight (γ : ℕ → ℕ) (m k x y : ℕ) :
    ∑ w ∈ words m k x y, weight γ w =
      (parts m k x).card * ∑ b ∈ parts 1 k y, (b.map γ).prod := by
  unfold words
  rw [sum_image]
  · rw [sum_product]
    have f {a b : List ℕ} (ha : a ∈ parts m k x) (hb : b ∈ parts 1 k y) :
        weight γ (a.zip b) = (b.map γ).prod := by
      have hlen : b.length ≤ a.length := by rw [(mem_parts.mp ha).1, (mem_parts.mp hb).1]
      simpa only [weight, List.map_map, Function.comp_def] using
        congrArg (fun l => (l.map γ).prod) (List.map_snd_zip hlen)
    calc
      _ = ∑ _a ∈ parts m k x, ∑ b ∈ parts 1 k y, (b.map γ).prod :=
        sum_congr rfl fun _ ha => sum_congr rfl fun _ hb => f ha hb
      _ = _ := by simp
  · rintro ⟨a, b⟩ hab ⟨u, v⟩ huv heq
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    obtain ⟨hu, hv⟩ := mem_product.mp huv
    have h₁ : a.length = b.length := (mem_parts.mp ha).1.trans (mem_parts.mp hb).1.symm
    have h₂ : u.length = v.length := (mem_parts.mp hu).1.trans (mem_parts.mp hv).1.symm
    change a.zip b = u.zip v at heq
    apply Prod.ext
    · simpa [List.map_fst_zip h₁.le, List.map_fst_zip h₂.le] using congrArg (List.map Prod.fst) heq
    · simpa [List.map_snd_zip h₁.ge, List.map_snd_zip h₂.ge] using congrArg (List.map Prod.snd) heq

private def delta (e : ℕ × ℕ) : ℤ := (e.2 : ℤ) - e.1

private lemma delta_sum (w : Word) : (w.map delta).sum = (falls w : ℤ) - rises w := by
  induction w with
  | nil => simp [falls, rises]
  | cons e w ih =>
    simp only [List.map_cons, List.sum_cons, ih, falls, rises, Nat.cast_add, delta]
    omega

private lemma valid_suffix {w : Word} (hp : ∀ e ∈ w, 0 < e.2) :
    Valid w ↔ ∀ t < w.length, falls (w.drop t) < rises (w.drop t) := by
  induction w with
  | nil => simp [Valid]
  | cons e w ih =>
    specialize ih fun x hx => hp x (List.mem_cons_of_mem _ hx)
    rw [Valid, ih]
    constructor
    · rintro ⟨ht, _, h₀⟩ (_ | t) h
      · exact h₀
      · exact ht _ (Nat.lt_of_succ_lt_succ h)
    · intro h
      exact ⟨fun t ht => h (t + 1) (Nat.succ_lt_succ ht), hp e List.mem_cons_self,
        h 0 (by simp)⟩

private lemma valid_prefix {w : Word} (hp : ∀ e ∈ w, 0 < e.2) (hs : rises w = falls w + 1) :
    Valid w ↔ ∀ t < w.length, 0 ≤ ((w.map delta).take t).sum := by
  rw [valid_suffix hp]
  apply forall_congr'
  intro t
  apply forall_congr'
  intro _
  have h := List.sum_take_add_sum_drop (w.map delta) t
  rw [← List.map_drop, delta_sum, delta_sum] at h
  omega

private lemma rotate_unique {w : Word} (hp : ∀ e ∈ w, 0 < e.2) (hs : rises w = falls w + 1) :
    ∃! i : Fin w.length, Valid (w.rotate i.val) := by
  let d := w.map delta
  have hlen : d.length = w.length := by simp [d]
  have hsum : d.sum = -1 := by dsimp [d]; rw [delta_sum, hs]; omega
  obtain ⟨i, hi, hu⟩ := raney_cycle_lemma_sum_neg_one_general d hsum
  have key (j : ℕ) : Valid (w.rotate j) ↔ ∀ t < d.length, 0 ≤ ((d.rotate j).take t).sum := by
    rw [valid_prefix (fun e he => hp e (List.mem_rotate.mp he)), List.map_rotate, hlen,
      List.length_rotate]
    rw [show rises (w.rotate j) = rises w from ((w.rotate_perm j).map Prod.fst).sum_eq,
      show falls (w.rotate j) = falls w from ((w.rotate_perm j).map Prod.snd).sum_eq, hs]
  refine ⟨Fin.cast hlen i, (key _).2 hi, ?_⟩
  intro j hj
  have he := hu (Fin.cast hlen.symm j) ((key _).1 hj)
  exact Fin.ext (congrArg (fun i : Fin d.length => i.val) he)

private lemma rotate_mem {w : Word} {m k x y : ℕ} (hw : w ∈ words m k x y) (i : ℕ) :
    w.rotate i ∈ words m k x y := by
  obtain ⟨hl, hr, hf, hp⟩ := mem_words.mp hw
  exact mem_words.mpr ⟨(List.length_rotate ..).trans hl,
    (((w.rotate_perm i).map Prod.fst).sum_eq).trans hr,
    (((w.rotate_perm i).map Prod.snd).sum_eq).trans hf, fun e he => hp e (List.mem_rotate.mp he)⟩

private noncomputable def good (m k x y : ℕ) : Finset Word := by
  classical exact (words m k x y).filter Valid

private lemma mem_good {m k x y : ℕ} {w : Word} :
    w ∈ good m k x y ↔ w ∈ words m k x y ∧ Valid w := by classical exact Finset.mem_filter

-- Sum over pairs of a word and a cut making it valid. Each word has one such cut.
-- For each fixed cut, rotation gives all valid words with the same weights.
private lemma cycle_weight (γ : ℕ → ℕ) {m k x y : ℕ} (hs : x + k * m = y + k + 1) :
    k * ∑ w ∈ good m k x y, weight γ w = ∑ w ∈ words m k x y, weight γ w := by
  classical
  let S := words m k x y
  let F (w : Word) := if Valid w then weight γ w else 0
  have h₁ {w} (hw : w ∈ S) : ∑ i ∈ range k, F (w.rotate i) = weight γ w := by
    obtain ⟨hl, hr, hf, hp⟩ := mem_words.mp hw
    obtain ⟨j, hj, hu⟩ := rotate_unique (fun e he => (hp e he).2) (hr.trans (hs.trans (by omega)))
    rw [sum_eq_single j.val]
    · simp only [F, hj, ite_true]
      exact ((w.rotate_perm j).map (fun e : ℕ × ℕ => γ e.2)).prod_eq
    · intro i hi hne
      apply ite_eq_right
      intro h
      exact hne (congrArg Fin.val (hu ⟨i, by have := mem_range.mp hi; omega⟩ h))
    · exact fun h => False.elim (h (mem_range.mpr (hl ▸ j.isLt)))
  have h₂ (i : ℕ) (hi : i < k) : ∑ w ∈ S, F (w.rotate i) = ∑ w ∈ S, F w := by
    apply sum_nbij' (fun w => List.rotate w i) (fun w => List.rotate w (k - i))
    · exact fun w hw => rotate_mem hw _
    · exact fun w hw => rotate_mem hw _
    · intro w hw
      rw [List.rotate_rotate, Nat.add_sub_cancel' hi.le, ← (mem_words.mp hw).1, List.rotate_length]
    · intro w hw
      rw [List.rotate_rotate, Nat.sub_add_cancel hi.le, ← (mem_words.mp hw).1, List.rotate_length]
    · exact fun _ _ => rfl
  calc
    _ = ∑ i ∈ range k, ∑ w ∈ S, F w := by simp [F, S, good, sum_filter]
    _ = ∑ i ∈ range k, ∑ w ∈ S, F (w.rotate i) :=
      sum_congr rfl fun i hi => (h₂ i (mem_range.mp hi)).symm
    _ = _ := by rw [sum_comm]; exact sum_congr rfl fun _ hw => h₁ hw

private def dissections (n k : ℕ) : Finset Chords :=
  (polygonDiagonals n).powerset.filter (fun D => IsNoncrossingDiagonalSet D ∧ D.card + 1 = k)

private lemma polygon_diagonal {n : ℕ} {e : ℕ × ℕ} :
    e ∈ polygonDiagonals n ↔ e.1 + 2 ≤ e.2 ∧ e.2 ≤ n + 1 ∧ e ≠ (0, n + 1) := by
  rcases e with ⟨i, j⟩
  simp only [polygonDiagonals, mem_filter, mem_product, mem_range, ne_eq, Prod.mk.injEq]
  omega

private lemma root_frontier {D : Chords} {r : ℕ} (hr : 0 < r) (hm : (0, r) ∈ D) :
    frontier r D = {0} := by
  ext t
  rw [mem_frontier, mem_singleton]
  constructor
  · rintro ⟨htr, ht⟩
    by_contra! h
    exact ht _ hm ⟨Nat.pos_of_ne_zero h, htr⟩
  · rintro rfl
    exact ⟨hr, fun f _ => by simp⟩

private lemma root_mem_of_trace {w E} (h : Traces w E) (hs : rises w = falls w + 1) :
    (0, rises w) ∈ E := by
  cases h with
  | nil => simp [rises, falls] at hs
  | @cons w D a b s prev hb hmem hrank =>
    have st := trace_stats (Traces.cons prev hb hmem hrank)
    let r := a + rises w
    have hc : (frontier r (insert (s, r) D)).card = 1 := by
      have := st.balanced
      change (frontier r (insert (s, r) D)).card + _ = _ at this
      omega
    have hs' := (mem_frontier.mp hmem).1
    have h₀ : 0 ∈ frontier r (insert (s, r) D) := mem_frontier.mpr
      ⟨by dsimp [r]; omega, fun f _ => by simp⟩
    have h₁ : s ∈ frontier r (insert (s, r) D) := by
      rw [frontier_close]
      exact mem_filter.mpr ⟨hmem, le_rfl⟩
    obtain rfl : s = 0 := card_le_one.mp hc.le _ h₁ _ h₀
    exact mem_insert_self ..

private lemma polygon_to_word {n k : ℕ} (hn : 1 ≤ n) (hkn : k ≤ n) {D : Chords}
    (hD : D ∈ dissections n k) :
    ∃ w ∈ good 0 k (n + 1) (n - k), Traces w (insert (0, n + 1) D) := by
  obtain ⟨hsub, hnc, hc⟩ := mem_filter.mp hD
  have he e (he : e ∈ D) := polygon_diagonal.mp (mem_powerset.mp hsub he)
  let r := n + 1
  have hne : (0, r) ∉ D := fun h => (he _ h).2.2 rfl
  let E := insert (0, r) D
  have hE : IsNoncrossingDiagonalSet E := by
    intro e he' f hf
    rcases mem_insert.mp he' with rfl | he' <;> rcases mem_insert.mp hf with rfl | hf
    · simp
    · exact fun h => (he _ hf).2.1.not_gt h.2.2
    · simp
    · exact hnc _ he' _ hf
  obtain ⟨w, hw, _⟩ := exists_word E hE (fun e he' => by
    rcases mem_insert.mp he' with rfl | h
    · change 0 + 2 ≤ n + 1
      omega
    · exact (he _ h).1)
  have st := trace_stats hw
  have hr : rises w = r := by
    rw [← st.ending, rightEnd, sup_insert]
    exact max_eq_left (Finset.sup_le fun e h => (he e h).2.1)
  have hlen : w.length = k := by
    rw [← st.length, card_insert_of_notMem hne, hc]
  have hf := st.balanced
  rw [hr, root_frontier (by simp [r]) (mem_insert_self ..), card_singleton] at hf
  have hp {l : Word} (h : Valid l) : ∀ e ∈ l, 0 < e.2 := by
    induction l with
    | nil => simp
    | cons e l ih => exact List.forall_mem_cons.mpr ⟨h.2.1, ih h.1⟩
  refine ⟨w, mem_good.mpr ⟨mem_words.mpr ⟨hlen, by simpa [r] using hr, ?_, ?_⟩, st.valid⟩, hw⟩
  · dsimp [r] at hf
    omega
  · exact fun e he => ⟨Nat.zero_le _, hp st.valid _ he⟩

private lemma word_to_polygon {w : Word} {n k : ℕ} (hkn : k ≤ n)
    (hw : w ∈ good 0 k (n + 1) (n - k)) :
    ∃ D ∈ dissections n k, Traces w (insert (0, n + 1) D) := by
  obtain ⟨hmem, hv⟩ := mem_good.mp hw
  obtain ⟨hlen, hr, hf, _⟩ := mem_words.mp hmem
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_add_cancel hkn] at hr hf
  obtain ⟨E, hE, _⟩ := exists_trace hv
  have st := trace_stats hE
  have hroot := root_mem_of_trace hE (by omega)
  rw [hr] at hroot
  refine ⟨E.erase (0, n + 1), mem_filter.mpr ⟨mem_powerset.mpr ?_, ?_, ?_⟩, ?_⟩
  · intro e he
    obtain ⟨hne, he⟩ := mem_erase.mp he
    refine polygon_diagonal.mpr ⟨st.spans e he, ?_, hne⟩
    rw [← hr, ← st.ending]
    exact Finset.le_sup (f := Prod.snd) he
  · exact fun e he f hf => st.compatible e (mem_of_mem_erase he) f (mem_of_mem_erase hf)
  · rw [card_erase_add_one hroot, st.length, hlen]
  · simpa [insert_erase hroot] using hE

private lemma polygon_count (γ : ℕ → ℕ) {n k : ℕ} (hn : 1 ≤ n) (hkn : k ≤ n) :
    coloredPolygonDissectionCount γ n k =
      ∑ w ∈ good 0 k (n + 1) (n - k), weight γ w := by
  classical
  rw [coloredPolygonDissectionCount, ite_eq_right (by omega)]
  let S := dissections n k
  let w (D) (hD : D ∈ S) := (polygon_to_word hn hkn hD).choose
  have spec (D) (hD : D ∈ S) := (polygon_to_word hn hkn hD).choose_spec
  apply sum_bij w (fun D hD => (spec D hD).1)
  · intro D hD D' hD' heq
    have h := (spec D hD).2
    change Traces (w D hD) _ at h
    rw [heq] at h
    have he := (exists_trace (trace_stats h).valid).unique h (spec D' hD').2
    have hnmem (A) (ha : A ∈ S) : (0, n + 1) ∉ A := fun h =>
      (polygon_diagonal.mp (mem_powerset.mp (mem_filter.mp ha).1 h)).2.2 rfl
    simpa only [erase_insert (hnmem D hD), erase_insert (hnmem D' hD')] using
      congrArg (fun A : Chords => A.erase (0, n + 1)) he
  · intro l hl
    obtain ⟨D, hD, h⟩ := word_to_polygon hkn hl
    refine ⟨D, hD, ?_⟩
    have st := trace_stats h
    exact (exists_word _ st.compatible st.spans).unique (spec D hD).2 h
  · intro D hD
    rw [← (trace_stats (spec D hD).2).colors γ]
    apply prod_congr rfl
    intro e he
    have hb : e.2 ≤ n + 1 := by
      rcases mem_insert.mp he with rfl | he
      · rfl
      · exact (polygon_diagonal.mp (mem_powerset.mp (mem_filter.mp hD).1 he)).2.1
    apply congrArg (fun i => γ (i - 2))
    unfold dissectionFaceSize
    congr 2
    ext v
    simp only [mem_filter, forall_mem_insert]
    constructor
    · rintro ⟨hv, h⟩
      refine ⟨hv, ⟨?_, h⟩⟩
      rintro hne ⟨h₁, _, _, h₂⟩
      apply hne
      exact Prod.ext (by dsimp at *; omega) (by dsimp at *; omega)
    · exact fun h => ⟨h.1, h.2.2⟩

open DyckStep
open List (replicate)

private def positive (w : Word) := ∀ e ∈ w, 0 < e.1 ∧ 0 < e.2

-- In chronological order the pairs spell runs of up steps followed by down steps.
private def spell (w : Word) : List DyckStep :=
  w.flatMap (fun e => replicate e.1 U ++ replicate e.2 D)

private lemma spell_head {w : Word} (hp : positive w) :
    (spell w).head? ≠ some D := by
  cases w with
  | nil => simp [spell]
  | cons e w =>
    obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (hp e List.mem_cons_self).1.ne'
    simp [spell, ha, List.replicate_succ]

private lemma spell_parts (l : List DyckStep) (hend : l = [] ∨ l.getLast? = some D) :
    ∃ d w, positive w ∧ l = replicate d D ++ spell w := by
  induction l with
  | nil => exact ⟨0, [], by simp [positive], rfl⟩
  | cons x l ih =>
    cases l with
    | nil =>
      have hx : x = D := by simpa using hend
      subst x
      exact ⟨1, [], by simp [positive], rfl⟩
    | cons y l =>
      have hlast : (y :: l).getLast? = some D := by simpa using hend
      obtain ⟨d, w, hw, h⟩ := ih (Or.inr hlast)
      cases x with
      | D => exact ⟨d + 1, w, hw, by simp [List.replicate_succ, ← h]⟩
      | U =>
        cases d with
        | succ d =>
          refine ⟨0, (1, d + 1) :: w, List.forall_mem_cons.mpr ⟨by simp, hw⟩, ?_⟩
          rw [h]
          simp [spell]
        | zero =>
          simp only [List.replicate_zero, List.nil_append] at h
          cases w with
          | nil => simp [spell] at h
          | cons e w =>
            refine ⟨0, (e.1 + 1, e.2) :: w, List.forall_mem_cons.mpr
              ⟨⟨by omega, (hw _ List.mem_cons_self).2⟩, (List.forall_mem_cons.mp hw).2⟩, ?_⟩
            rw [h]
            simp [spell, List.replicate_succ]

private lemma prefix_run (s : DyckStep) {l : List DyckStep} (hn : l.head? ≠ some s) (n : ℕ) :
    ((replicate n s ++ l).takeWhile (· == s)).length = n := by
  induction n with
  | zero =>
    cases l with
    | nil => rfl
    | cons t l =>
      have ht : t ≠ s := by simpa using hn
      simp [ht]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, List.takeWhile_cons_of_pos (by simp),
      List.length_cons, ih]

private lemma spell_inj {w v : Word} (hw : positive w) (hv : positive v)
    (h : spell w = spell v) : w = v := by
  induction w generalizing v with
  | nil =>
    cases v with
    | nil => rfl
    | cons f v =>
      have := (hv _ List.mem_cons_self).1
      simp [spell] at h
      omega
  | cons e w ih =>
    obtain ⟨⟨ha, hb⟩, hwp⟩ := List.forall_mem_cons.mp hw
    cases v with
    | nil =>
      simp [spell] at h
      omega
    | cons f v =>
      obtain ⟨⟨ha', hb'⟩, hvp⟩ := List.forall_mem_cons.mp hv
      change (replicate e.1 U ++ replicate e.2 D) ++ spell w =
        (replicate f.1 U ++ replicate f.2 D) ++ spell v at h
      simp only [List.append_assoc] at h
      have hd (b) (h : 0 < b) (l : List DyckStep) : (replicate b D ++ l).head? ≠ some U := by
        cases b with
        | zero => omega
        | succ b => simp [List.replicate_succ]
      have h₁ := congrArg (fun l : List DyckStep => (l.takeWhile (· == U)).length) h
      rw [prefix_run _ (hd _ hb _), prefix_run _ (hd _ hb' _)] at h₁
      rw [h₁, List.append_cancel_left_eq] at h
      have h₂ := congrArg (fun l : List DyckStep => (l.takeWhile (· == D)).length) h
      rw [prefix_run _ (spell_head hwp), prefix_run _ (spell_head hvp)] at h₂
      rw [h₂, List.append_cancel_left_eq] at h
      exact congrArg₂ List.cons (Prod.ext h₁ h₂) (ih hwp hvp h)

private lemma peaks_cons (s : DyckStep) (l : List DyckStep) :
    dyckPeakDescents (s :: l) =
      (if s = U ∧ l.head? = some D then [(l.takeWhile (· == D)).length] else []) ++
        dyckPeakDescents l := by
  simp only [dyckPeakDescents, List.length_cons, List.range_succ_eq_map, List.filter_cons,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
  split <;> simp_all [List.filter_map, List.map_map, Function.comp_def, List.head?_eq_getElem?]

private lemma peaks_block {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (l : List DyckStep) (hh : l.head? ≠ some D) :
    dyckPeakDescents (replicate a U ++ (replicate b D ++ l)) = b :: dyckPeakDescents l := by
  have hd (d : ℕ) : dyckPeakDescents (replicate d D ++ l) = dyckPeakDescents l := by
    induction d with
    | zero => simp
    | succ d ih => simp [List.replicate_succ, peaks_cons, ih]
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  induction a with
  | zero =>
    have hfirst : (replicate b D ++ l).head? = some D := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
      simp [List.replicate_succ]
    change dyckPeakDescents (U :: (replicate b D ++ l)) = _
    rw [peaks_cons, ite_eq_left ⟨rfl, hfirst⟩, prefix_run _ hh, hd]
    rfl
  | succ a ih =>
    rw [List.replicate_succ, List.cons_append, peaks_cons]
    simpa [List.replicate_succ] using ih (by omega)

private lemma spell_peaks {w : Word} (hw : positive w) :
    dyckPeakDescents (spell w) = w.map Prod.snd := by
  induction w with
  | nil => rfl
  | cons e w ih =>
    obtain ⟨⟨he₁, he₂⟩, hw⟩ := List.forall_mem_cons.mp hw
    change dyckPeakDescents ((replicate e.1 U ++ replicate e.2 D) ++ spell w) = _
    rw [List.append_assoc, peaks_block he₁ he₂ _ (spell_head hw), ih hw, List.map_cons]

private def steps (w : Word) := spell w.reverse

private lemma steps_cons (e : ℕ × ℕ) (w : Word) : steps (e :: w) =
    steps w ++ (replicate e.1 U ++ replicate e.2 D) := by simp [steps, spell]

private lemma steps_count (w : Word) :
    (steps w).count U = rises w ∧ (steps w).count D = falls w := by
  induction w with
  | nil => simp [steps, spell, rises, falls]
  | cons e w ih => simp only [steps_cons, List.count_append, List.count_replicate, ih, rises, falls,
      List.map_cons, List.sum_cons]; cases e; simp [Nat.add_comm]

private def StrictPath (l : List DyckStep) : Prop :=
  ∀ i, 0 < i → i ≤ l.length → (l.take i).count D < (l.take i).count U

private lemma strict_block (l : List DyckStep) {a b : ℕ} (ha : 0 < a) :
    StrictPath (l ++ (replicate a U ++ replicate b D)) ↔
      StrictPath l ∧ l.count D + b < l.count U + a := by
  constructor
  · intro h
    constructor
    · intro i hi hle
      have := h i hi (hle.trans (by simp))
      simpa [List.take_append, Nat.sub_eq_zero_of_le hle] using this
    · have := h _ (by simp; omega) le_rfl
      rw [List.take_length] at this
      simpa [List.count_replicate] using this
  · rintro ⟨h, hend⟩ i hi _
    by_cases hle : i ≤ l.length
    · simpa [List.take_append, Nat.sub_eq_zero_of_le hle] using h i hi hle
    have hbase : l.count D ≤ l.count U := by
      rcases l with _ | ⟨x, l⟩
      · simp
      · exact le_of_lt (by simpa using h _ (show 0 < (x :: l).length by simp) le_rfl)
    rw [List.take_append, List.take_of_length_le (by omega : l.length ≤ i),
      List.take_append, List.take_replicate, List.take_replicate]
    simp only [List.count_append, List.count_replicate]
    simp
    omega

private lemma valid_steps {w : Word} (hp : positive w) : Valid w ↔ StrictPath (steps w) := by
  induction w with
  | nil => simp [steps, spell, StrictPath, Valid]; omega
  | cons e w ih =>
    obtain ⟨⟨ha, hb⟩, hp⟩ := List.forall_mem_cons.mp hp
    rw [steps_cons, strict_block _ ha, Valid, ih hp]
    simp [hb, rises, falls, (steps_count w).1, (steps_count w).2, Nat.add_comm]

private lemma strict_extend (p : DyckWord) : StrictPath (U :: p.toList) := by
  rintro (_ | i) hi _
  · omega
  · simpa [List.count_cons] using Nat.lt_succ_of_le (p.count_D_le_count_U i)

private lemma strict_tail {l : List DyckStep} (hs : StrictPath (U :: l))
    (eq : l.count U = l.count D) : ∀ i, (l.take i).count D ≤ (l.take i).count U := by
  intro i
  by_cases h : i ≤ l.length
  · have ht := hs (i + 1) (by omega) (Nat.succ_le_succ h)
    simp at ht
    omega
  · simp [List.take_of_length_le (by omega : l.length ≤ i), eq]

private lemma word_from_path {n : ℕ} (hn : 1 ≤ n) (p : {p : DyckWord // p.semilength = n}) :
    ∃ w : Word, positive w ∧ steps w = U :: p.val.toList := by
  have hne : p.val ≠ 0 := fun hz => by have := p.property; rw [hz] at this; simp at this; omega
  have hnlist := DyckWord.toList_ne_nil.mpr hne
  have hlast : (U :: p.val.toList).getLast? = some D := by
    rw [List.getLast?_eq_some_getLast (by simp), List.getLast_cons hnlist,
      p.val.getLast_eq_D hnlist]
  obtain ⟨d, v, hv, h⟩ := spell_parts (U :: p.val.toList) (Or.inr hlast)
  cases d with
  | zero => exact ⟨v.reverse, by simpa [positive] using hv, by simpa [steps] using h.symm⟩
  | succ d => simp [List.replicate_succ] at h

private lemma path_from_word {w : Word} {n : ℕ} (hp : positive w) (h : Valid w)
    (hr : rises w = n + 1) (hf : falls w = n) :
    ∃ p : {p : DyckWord // p.semilength = n}, steps w = U :: p.val.toList := by
  have hs := (valid_steps hp).mp h
  have ⟨hu, hd⟩ := steps_count w
  cases he : steps w with
  | nil => simp [he, hr] at hu
  | cons x l =>
    rw [he] at hu hd hs
    cases x with
    | D => have := hs 1 (by decide) (by simp); simp at this
    | U =>
      simp at hu hd
      have eq : l.count U = l.count D := by omega
      exact ⟨⟨⟨l, eq, strict_tail hs eq⟩, by change l.count U = n; omega⟩, rfl⟩

private lemma encoded_peaks {w : Word} {p : DyckWord} (h : steps w = U :: p.toList)
    (hp : positive w) : dyckPeakDescents p.toList = (w.map Prod.snd).reverse := by
  have hh : p.toList.head? ≠ some D := by
    by_cases hz : p = 0
    · subst p; decide
    · have hn := DyckWord.toList_ne_nil.mpr hz
      rw [List.head?_eq_some_head hn, p.head_eq_U hn]
      decide
  have hpeaks := spell_peaks (w := w.reverse) (by simpa [positive] using hp)
  change dyckPeakDescents (steps w) = _ at hpeaks
  simpa [h, peaks_cons, hh] using hpeaks

private lemma dyck_count (γ : ℕ → ℕ) {n k : ℕ} (hn : 1 ≤ n) (hkn : k ≤ n) :
    coloredDyckPathCount γ n k =
      ∑ w ∈ good 1 k (n + 1 - k) (n - k), weight γ w := by
  classical
  let S := good 1 k (n + 1 - k) (n - k)
  have data (w) (hw : w ∈ S) :
      positive w ∧ Valid w ∧ rises w = n + 1 ∧ falls w = n ∧ w.length = k := by
    obtain ⟨hm, hv⟩ := mem_good.mp hw
    obtain ⟨hl, hr, hf, hp⟩ := mem_words.mp hm
    exact ⟨hp, hv, by simpa [Nat.sub_add_cancel (show k ≤ n + 1 by omega)] using hr,
      by omega, hl⟩
  have path (w) (hw : w ∈ S) := path_from_word (data w hw).1 (data w hw).2.1
    (data w hw).2.2.1 (data w hw).2.2.2.1
  let f (w) (hw : w ∈ S) := (path w hw).choose
  have spec (w) (hw : w ∈ S) : steps w = U :: (f w hw).val.toList := (path w hw).choose_spec
  have peaks (w) (hw : w ∈ S) := encoded_peaks (spec w hw) (data w hw).1
  symm
  apply sum_bij f
  · intro w hw
    exact mem_filter.mpr ⟨mem_univ _, by simpa [peaks w hw] using (data w hw).2.2.2.2⟩
  · intro w hw v hv heq
    have he : steps w = steps v := by rw [spec w hw, spec v hv, heq]
    have hinj := spell_inj (w := w.reverse) (v := v.reverse)
      (by simpa [positive] using (data w hw).1) (by simpa [positive] using (data v hv).1) he
    simpa using congrArg List.reverse hinj
  · intro p hpm
    have hk := (mem_filter.mp hpm).2
    obtain ⟨w, hp, heq⟩ := word_from_path hn p
    have hpk := encoded_peaks heq hp
    have ⟨hu, hd⟩ := steps_count w
    have hsemi : p.val.toList.count U = n := p.property
    have hd' := p.val.count_U_eq_count_D
    simp only [heq, List.count_cons, beq_self_eq_true, ↓reduceIte] at hu hd
    have hr : rises w = n + 1 := by simpa [hsemi] using hu.symm
    have hf : falls w = n := by simpa [← hd', hsemi] using hd.symm
    have hlen : w.length = k := by simpa [hpk] using hk
    have hw : w ∈ S := mem_good.mpr ⟨mem_words.mpr
      ⟨hlen, by omega, by omega, hp⟩, (valid_steps hp).mpr (heq ▸ strict_extend p.val)⟩
    refine ⟨w, hw, Subtype.ext (DyckWord.ext ?_)⟩
    exact (List.cons.inj ((spec w hw).symm.trans heq)).2
  · intro w hw
    rw [peaks w hw, List.map_reverse, List.prod_reverse, List.map_map]
    rfl

private lemma binomial_factors (n t : ℕ) :
    (n + (t + 1)).choose (t + 1) * n.choose t =
      (n + 1).choose (t + 1) * (n + (t + 1)).choose t := by
  apply Nat.eq_of_mul_eq_mul_right (show 0 < t + 1 by omega)
  have h := Nat.choose_succ_right_eq (n + (t + 1)) t
  rw [show n + (t + 1) - t = n + 1 by omega] at h
  calc
    _ = ((n + (t + 1)).choose (t + 1) * (t + 1)) * n.choose t := by ac_rfl
    _ = ((n + 1) * n.choose t) * (n + (t + 1)).choose t := by rw [h]; ac_rfl
    _ = _ := by rw [Nat.add_one_mul_choose_eq]; ac_rfl

end choose_mul_coloredDyckPathCount_eq

open choose_mul_coloredDyckPathCount_eq

/-- **Colored Dyck paths and colored polygon partitions.** Let
$\gamma = (\gamma_1, \gamma_2, \dots)$ be a sequence of natural numbers. Let $d_{n,k}(\gamma)$ be
the number of Dyck paths of semilength $n$ with $k$ peaks in which each block $UD^j$, formed by a
peak and the maximal run of $D$ steps starting at its $D$, carries one of $\gamma_j$ colors, and
let $p_{n,k}(\gamma)$ be the number of partitions of a rooted convex $(n+2)$-gon by $k - 1$
noncrossing diagonals into $k$ polygons in which each $(j+2)$-gon carries one of $\gamma_j$
colors. For all natural numbers $n$ and $k$ with $1 \le k \le n$,
$$\binom{n+k}{k} d_{n,k}(\gamma) = \binom{n+1}{k} p_{n,k}(\gamma).$$

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Theorem 6 (`jis-2024-24.5.2-thm-6`). -/
public theorem choose_mul_coloredDyckPathCount_eq (γ : ℕ → ℕ) {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n + k).choose k * coloredDyckPathCount γ n k =
      (n + 1).choose k * coloredPolygonDissectionCount γ n k := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hd := cycle_weight γ (m := 1) (k := t + 1) (x := n + 1 - (t + 1)) (y := n - (t + 1))
    (by omega)
  have hp := cycle_weight γ (m := 0) (k := t + 1) (x := n + 1) (y := n - (t + 1)) (by omega)
  rw [← dyck_count γ (hk.trans hkn) hkn, words_weight, card_parts,
    show n + 1 - (t + 1) + t = n by omega] at hd
  rw [← polygon_count γ (hk.trans hkn) hkn, words_weight, card_parts,
    show n + 1 + t = n + (t + 1) by omega] at hp
  apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos t)
  rw [Nat.mul_left_comm, hd, ← Nat.mul_assoc, binomial_factors,
    Nat.mul_left_comm (t + 1), hp, Nat.mul_assoc]

end

end MetaMathlibExt
