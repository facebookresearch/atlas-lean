/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.RationalSimplicialHomologyShared
import Mathlib.Data.Finset.Powerset

/-!
# Interval decompositions of complexes with acyclic low-dimensional links (Stanley, Problem 5)

An eight-vertex complex refutes Stanley's interval-decomposition conjecture at rank two.
Its empty-face and vertex links are rationally acyclic. Every edge belongs to a missing
triangle, which obstructs a partition with a subcomplex of bottoms.

R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics, Problem 5: suppose
that the link of every face `F` of the finite simplicial complex `Δ` of dimension at most `j`
(including `link(∅) = Δ`) is acyclic over `ℚ`. Can `Δ` be partitioned into intervals `[F, F']` such
that (a) `dim F' - dim F = j + 2` and (b) the bottom elements `F` form a subcomplex of `Δ`?

Source: R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics (1999),
Problem 5 (interval decompositions of complexes with acyclic links). UnsolvedMath record UM-00801178
(`AMR-156-0004`), dataset ulamai/UnsolvedMath v1.8.0.

Written with `k = j + 2 ≥ 1` (Doolittle–Goeckner's "`k`-fold acyclic": the link of every face with
fewer than `k` vertices is acyclic); `j = -1` is Stanley's theorem on acyclic complexes. Complexes,
links and acyclicity over `ℚ` (all reduced rational Betti numbers zero) are those of
`WantedExt/Combinatorics/RationalSimplicialHomologyShared.lean`. A decomposition is a family `B` of
bottoms closed under subsets with tops `top F ∈ K`, `|top F| = |F| + k`, every face in exactly one
interval. Doolittle–Goeckner work over an arbitrary field; acyclicity over any field implies
acyclicity over `ℚ` (universal coefficients), so their counterexample applies.

The shared homology definitions are imported from
`MathlibExt.Combinatorics.RationalSimplicialHomologyShared`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.AcyclicLinksIntervalDecompositionAMR156Problem0004Wanted

open MathlibExt.Combinatorics.RationalSimplicialHomologyShared

/-- **Rank-$k$ interval decomposition with a subcomplex of bottoms.** For a natural number $k$, a
finite family $K$ of finite subsets of $\mathbb{N}$ has a rank-$k$ interval decomposition with a
subcomplex of bottoms if there are a finite family $B$ of finite subsets of $\mathbb{N}$, closed
under taking subsets, and an assignment of a finite set $\mathrm{top}(F) \subseteq \mathbb{N}$ to
each finite set $F \subseteq \mathbb{N}$, such that every $F \in B$ satisfies
$F \subseteq \mathrm{top}(F)$, $|\mathrm{top}(F)| = |F| + k$ and $\mathrm{top}(F) \in K$, and every
$\sigma \in K$ lies in the interval $[F, \mathrm{top}(F)] = \{G : F \subseteq G \subseteq
\mathrm{top}(F)\}$ for exactly one $F \in B$. -/
def HasRankIntervalDecomposition (K : Finset (Finset ℕ)) (k : ℕ) : Prop :=
  ∃ (B : Finset (Finset ℕ)) (top : Finset ℕ → Finset ℕ), (∀ F ∈ B, ∀ G ⊆ F, G ∈ B) ∧
    (∀ F ∈ B, F ⊆ top F ∧ (top F).card = F.card + k ∧ top F ∈ K) ∧
    ∀ σ ∈ K, ∃! F, F ∈ B ∧ F ⊆ σ ∧ σ ⊆ top F

/-- **Stanley's interval-decomposition conjecture for complexes with acyclic links.** The statement
that for every integer $k \ge 1$ and every finite simplicial complex $K$ on the vertex set
$\mathbb{N}$ (a finite family of finite subsets of $\mathbb{N}$ closed under taking subsets): if the
link $\mathrm{lk}_K(F) = \{G \in K : G \cap F = \emptyset,\ G \cup F \in K\}$ of every face
$F \in K$ with fewer than $k$ vertices (including $\mathrm{lk}_K(\emptyset) = K$) is acyclic over
$\mathbb{Q}$ (all of its reduced rational homology vanishes), then $K$ has a rank-$k$ interval
decomposition with a subcomplex of bottoms: there are a family $B$ of finite subsets of
$\mathbb{N}$, closed under taking subsets, and faces $\mathrm{top}(F) \in K$ for $F \in B$ with
$F \subseteq \mathrm{top}(F)$ and $|\mathrm{top}(F)| = |F| + k$, such that every face of $K$ lies
in the interval $[F, \mathrm{top}(F)]$ for exactly one $F \in B$.

This is Stanley's Problem 5 (Positivity Problems; Conjecture 2.4 of Stanley, Discrete Math. 120
(1993)) with $k = j + 2$: the faces with fewer than $k$ vertices are the faces of dimension at most
$j$, and for an interval $[F, F']$ with $F' = \mathrm{top}(F)$, the condition $|F'| = |F| + k$
means $\dim F' - \dim F = k$. -/
def acyclicLinksIntervalDecomposition : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ K : Finset (Finset ℕ), IsSimplicialComplex K →
    (∀ F ∈ K, F.card < k → IsRationallyAcyclic (link K F)) → HasRankIntervalDecomposition K k

private abbrev Face := Finset ℕ

private def facets : Finset Face :=
  {{0, 1, 2, 3}, {0, 2, 3, 7}, {1, 3, 4, 5}, {0, 2, 3, 6}, {0, 1, 3, 7},
   {1, 3, 5, 7}, {1, 2, 3, 4}, {1, 2, 4, 5}, {0, 1, 2, 4}, {2, 3, 4, 7},
   {0, 3, 5, 7}, {0, 3, 5, 6}, {3, 4, 5, 6}, {0, 2, 6, 7}, {0, 1, 6, 7}}

private def complex : Finset Face := facets.biUnion Finset.powerset

private theorem simplicial : IsSimplicialComplex complex := by
  intro s hs t ht
  obtain ⟨f, hf, hs⟩ := Finset.mem_biUnion.mp hs
  exact Finset.mem_biUnion.mpr
    ⟨f, hf, Finset.mem_powerset.mpr (ht.trans (Finset.mem_powerset.mp hs))⟩

private theorem exists_missing_triangle :
    ∀ e ∈ complex, e.card = 2 → ∃ v ∈ Finset.range 8, v ∉ e ∧
      insert v e ∉ complex ∧ ∀ w ∈ e, {v, w} ∈ complex := by decide +kernel

-- Neither endpoint of top ∅ can itself be a bottom. For a common neighbor v of its endpoints,
-- both incident edges must therefore belong to the interval with bottom {v}.
private theorem no_partition : ¬ HasRankIntervalDecomposition complex 2 := by
  rintro ⟨B, top, hdown, htop, hcover⟩
  have h0 : ∅ ∈ complex := by decide +kernel
  obtain ⟨F, ⟨hF, hsub, _⟩, _⟩ := hcover ∅ h0
  obtain rfl := Finset.subset_empty.mp hsub
  have htop0 := htop ∅ hF
  obtain ⟨v, _, hv, htri, hedges⟩ :=
    exists_missing_triangle (top ∅) htop0.2.2 (by simpa using htop0.2.1)
  have hvertex (w : ℕ) (hw : w ∈ top ∅) : {w} ∉ B := by
    intro h
    have hface := simplicial _ htop0.2.2 {w} (Finset.singleton_subset_iff.mpr hw)
    have heq : (∅ : Face) = {w} := (hcover {w} hface).unique
      (show ∅ ∈ B ∧ (∅ : Face) ⊆ {w} ∧ {w} ⊆ top ∅ from
        ⟨hF, Finset.empty_subset _, Finset.singleton_subset_iff.mpr hw⟩)
      (show {w} ∈ B ∧ ({w} : Face) ⊆ {w} ∧ {w} ⊆ top {w} from ⟨h, le_rfl, (htop _ h).1⟩)
    simp at heq
  have hforced (w : ℕ) (hw : w ∈ top ∅) : {v} ∈ B ∧ {v, w} ⊆ top {v} := by
    obtain ⟨G, ⟨hG, hGe, he⟩, _⟩ := hcover _ (hedges w hw)
    have hwG : w ∉ G := fun h => hvertex w hw (hdown _ hG _ (Finset.singleton_subset_iff.mpr h))
    have hne : G ≠ ∅ := by
      rintro rfl
      exact hv (he (Finset.mem_insert_self ..))
    have h : G ⊆ {v} := by
      intro x hx
      rcases Finset.mem_insert.mp (hGe hx) with h | h
      · simpa using h
      · exact (hwG ((Finset.mem_singleton.mp h) ▸ hx)).elim
    obtain rfl := (Finset.subset_singleton_iff.mp h).resolve_left hne
    exact ⟨hG, he⟩
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < (top ∅).card by omega)
  have htopv := htop {v} (hforced w hw).1
  apply htri
  apply simplicial _ htopv.2.2
  exact Finset.insert_subset (htopv.1 (Finset.mem_singleton_self _))
    (fun x hx => (hforced x hx).2 (by simp))

private def sign (s : Face) (v : ℕ) : ℚ := (-1) ^ (s.filter (· < v)).card

private def incidence (r c : Face) : ℚ :=
  ∑ v ∈ c, if c.erase v = r then sign c v else 0

-- Expand the second boundary by deleting one vertex of the column face at a time.
private theorem chain {K : Finset Face} (hK : IsSimplicialComplex K) (k : ℕ)
    (h : ∀ c ∈ facesOfCard K (k + 2), ∀ r ∈ facesOfCard K k,
      ∑ v ∈ c, incidence r (c.erase v) * sign c v = 0) :
    boundaryMatrix K k * boundaryMatrix K (k + 1) = 0 := by
  ext r c
  rw [Matrix.mul_apply, Matrix.zero_apply]
  change ∑ b : facesOfCard K (k + 1), incidence r.val b.val *
    (∑ v ∈ c.val, if c.val.erase v = b.val then sign c.val v else 0) = 0
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  convert h c.val c.property r.val r.property using 1
  apply Finset.sum_congr rfl
  intro v hv
  obtain ⟨hc, hcard⟩ := Finset.mem_filter.mp c.property
  let b : facesOfCard K (k + 1) := ⟨c.val.erase v, Finset.mem_filter.mpr
    ⟨hK _ hc _ (Finset.erase_subset ..), by rw [Finset.card_erase_of_mem hv, hcard]; rfl⟩⟩
  rw [Finset.sum_eq_single b]
  · simp [b]
  · intro a _ hne
    have hne' : c.val.erase v ≠ a.val := fun e => hne (Subtype.ext e.symm)
    simp [hne']
  · simp

-- Extract a triangular minor from an ordered list of incident face pairs.
private theorem rank_lower {K : Finset Face} {k : ℕ} (pairs : List (Face × Face))
    (hmem : ∀ p ∈ pairs, p.1 ∈ facesOfCard K k ∧ p.2 ∈ facesOfCard K (k + 1))
    (hdiag : ∀ p ∈ pairs, incidence p.1 p.2 ≠ 0)
    (htri : pairs.Pairwise fun p q => incidence p.1 q.2 = 0) :
    pairs.length ≤ (boundaryMatrix K k).rank := by
  let row (i : Fin pairs.length) : facesOfCard K k :=
    ⟨(pairs.get i).1, (hmem _ (List.get_mem ..)).1⟩
  let col (i : Fin pairs.length) : facesOfCard K (k + 1) :=
    ⟨(pairs.get i).2, (hmem _ (List.get_mem ..)).2⟩
  let M := (boundaryMatrix K k).submatrix row col
  have hM : M.IsLowerTriangular := by
    intro i j hij
    exact (List.pairwise_iff_get.mp htri) i j hij
  have hd (i) : M.diag i ≠ 0 := hdiag _ (List.get_mem ..)
  have hr := M.rank_mul_eq_right_of_isLowerTriangular
    (1 : Matrix (Fin pairs.length) (Fin pairs.length) ℚ) hM hd
  simp only [Matrix.mul_one, Matrix.rank_one, Fintype.card_fin] at hr
  exact hr ▸ (boundaryMatrix K k).rank_submatrix_le row col

private theorem incidence_zero {r c : Face} (h : ¬ r ⊆ c) : incidence r c = 0 := by
  unfold incidence
  apply Finset.sum_eq_zero
  intro v _
  have hne : c.erase v ≠ r := fun e => h (e ▸ Finset.erase_subset v c)
  simp [hne]

private theorem incidence_insert (r : Face) {v : ℕ} (hv : v ∉ r) :
    incidence r (insert v r) = sign (insert v r) v := by
  unfold incidence
  rw [Finset.sum_eq_single v]
  · simp [hv]
  · intro w hw hwv
    have hwr : w ∈ r := (Finset.mem_insert.mp hw).resolve_left hwv
    exact ite_eq_right (fun e => Finset.notMem_erase w _ (e ▸ hwr))
  · simp

-- Deleting a then b and deleting b then a contribute opposite signs.
private theorem cancel_two (r : Face) (a b : ℕ) (ha : a ∉ r) (hb : b ∉ r) (hab : a < b) :
    let c := insert a (insert b r)
    ∑ v ∈ c, incidence r (c.erase v) * sign c v = 0 := by
  dsimp only
  have ha' : a ∉ insert b r := by simp [hab.ne, ha]
  rw [Finset.sum_insert ha', Finset.sum_insert hb, Finset.erase_insert ha',
    Finset.erase_insert_of_ne hab.ne, Finset.erase_insert hb,
    incidence_insert r hb, incidence_insert r ha]
  have hz : ∀ v ∈ r, incidence r ((insert a (insert b r)).erase v) *
      sign (insert a (insert b r)) v = 0 := by
    intro v hv
    rw [incidence_zero (fun hs => Finset.notMem_erase v _ (hs hv)), zero_mul]
  rw [Finset.sum_eq_zero hz]
  simp [sign, Finset.filter_insert, hab, Nat.not_lt_of_ge hab.le, ha, pow_succ]
  ring

private theorem boundary_sq (K : Finset Face) (hK : IsSimplicialComplex K) (k : ℕ) :
    boundaryMatrix K k * boundaryMatrix K (k + 1) = 0 := by
  apply chain hK
  intro c hc r hr
  by_cases hrc : r ⊆ c
  · have hc' := (Finset.mem_filter.mp hc).2
    have hr' := (Finset.mem_filter.mp hr).2
    obtain ⟨a, b, hne, heq⟩ := Finset.card_eq_two.mp (show (c \ r).card = 2 by
      rw [Finset.card_sdiff_of_subset hrc, hc', hr']; omega)
    have hab : a ∈ c \ r := heq ▸ Finset.mem_insert_self ..
    have hba : b ∈ c \ r := heq ▸ (by simp)
    have ha := (Finset.mem_sdiff.mp hab).2
    have hb := (Finset.mem_sdiff.mp hba).2
    have hf : c = insert a (insert b r) := by
      rw [← Finset.sdiff_union_of_subset hrc, heq]; simp
    rw [hf]
    rcases hne.lt_or_gt with h | h
    · exact cancel_two r a b ha hb h
    · rw [Finset.insert_comm a b]
      exact cancel_two r b a hb ha h
  · apply Finset.sum_eq_zero
    intro v _
    rw [incidence_zero (fun hs => hrc (hs.trans (Finset.erase_subset ..))), zero_mul]

private theorem link_simplicial {K : Finset Face} (hK : IsSimplicialComplex K) (f : Face) :
    IsSimplicialComplex (link K f) := by
  intro s hs t ht
  obtain ⟨hsK, hdis, hunion⟩ := Finset.mem_filter.mp hs
  exact Finset.mem_filter.mpr ⟨hK _ hsK _ ht, hdis.mono_left ht,
    hK _ hunion _ (Finset.union_subset_union_left ht)⟩

-- The pivot search uses the bits of a natural number to represent a face.
private def mask (s : Face) : ℕ := ∑ v ∈ s, 2 ^ v

private def vertices (m : ℕ) : Face := (Finset.range 8).filter (fun v => m.testBit v)

-- At each step remove a face with a unique strict coface, together with that coface.
private def collapsePairs : ℕ → List ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | fuel + 1, remaining =>
    let freePair (r : ℕ) := match remaining.filter (fun c => c != r && (r &&& c) == r) with
      | [c] => some (r, c)
      | _ => none
    match remaining.findSome? freePair with
    | none => []
    | some (r, c) =>
      (r, c) :: collapsePairs fuel (remaining.filter (fun s => s != r && s != c))

private def pairsFor (f : Face) : List (Face × Face) :=
  let face := mask f
  let tops := facets.image mask
  let masks := (List.range 256).filter fun m =>
    (m &&& face) == 0 && decide (∃ t ∈ tops, ((m ||| face) &&& t) = (m ||| face))
  (collapsePairs (masks.length / 2) masks).map (fun (r, c) => (vertices r, vertices c))

private def pivots (f : Face) (k : ℕ) : List (Face × Face) :=
  (pairsFor f).filter (fun p => p.1.card = k)

-- Each collapse pair supplies a pivot. Later columns vanish in its row, so in each
-- degree the selected rows and columns form a triangular matrix.
private def CertifiesMinor (K : Finset Face) (k : ℕ) (pairs : List (Face × Face)) : Prop :=
  (∀ p ∈ pairs, p.1 ∈ facesOfCard K k ∧ p.2 ∈ facesOfCard K (k + 1)) ∧
  (∀ p ∈ pairs, incidence p.1 p.2 ≠ 0) ∧
  pairs.Pairwise (fun p q => ¬ p.1 ⊆ q.2)

private instance decidableCertifiesMinor (K : Finset Face) (k : ℕ) (pairs : List (Face × Face)) :
    Decidable (CertifiesMinor K k pairs) := by unfold CertifiesMinor; infer_instance

private def CertifiesDegree (f : Face) (k : ℕ) : Prop :=
  CertifiesMinor (link complex f) k (pivots f k) ∧
    (facesOfCard (link complex f) k).card =
      (if k = 0 then 0 else (pivots f (k - 1)).length) + (pivots f k).length

private instance decidableCertifiesDegree (f : Face) (k : ℕ) : Decidable (CertifiesDegree f k) := by
  unfold CertifiesDegree
  infer_instance

private theorem pivot_check :
    ∀ f ∈ complex, f.card < 2 → ∀ k ∈ Finset.range 5, CertifiesDegree f k := by decide +kernel

-- The two adjacent triangular minors together account for every face of this size.
-- Their lower bounds meet the upper bound from the vanishing boundary composition.
private theorem acyclic_link (f : Face) (hf : f ∈ complex) (hsize : f.card < 2) :
    IsRationallyAcyclic (link complex f) := by
  let L := link complex f
  have lower (k : ℕ) (hk : k < 5) : (pivots f k).length ≤ (boundaryMatrix L k).rank := by
    obtain ⟨hm, hd, ht⟩ := (pivot_check f hf hsize k (Finset.mem_range.mpr hk)).1
    exact rank_lower _ hm hd (ht.imp (fun h => incidence_zero h))
  intro k
  change reducedBetti L k = 0
  unfold reducedBetti
  by_cases hk : k < 5
  · have hn := (pivot_check f hf hsize k (Finset.mem_range.mpr hk)).2
    change (facesOfCard L k).card = _ at hn
    have hcurr := lower k hk
    cases k with
    | zero =>
      have hle := (boundaryMatrix L 0).rank_le_card_height
      rw [Fintype.card_coe] at hle
      simp only [ite_eq_left, Nat.zero_add] at hn
      simp only [ite_eq_left, sub_zero]
      omega
    | succ j =>
      have hprev := lower j (by omega)
      have hle := Matrix.rank_add_rank_le_card_of_mul_eq_zero
        (boundary_sq L (link_simplicial simplicial f) j)
      rw [Fintype.card_coe] at hle
      simp only [Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one] at hn ⊢
      omega
  · have maxSize : ∀ s ∈ complex, s.card ≤ 4 := by decide +kernel
    have he : facesOfCard L k = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro s hs
      obtain ⟨hsL, heq⟩ := Finset.mem_filter.mp hs
      have hsK := (Finset.mem_filter.mp hsL).1
      have := maxSize s hsK
      omega
    have hcurr := (boundaryMatrix L k).rank_le_card_height
    have hprev := (boundaryMatrix L (k - 1)).rank_le_card_width
    have hcard := Finset.card_eq_zero.mpr he
    rw [Fintype.card_coe, hcard] at hcurr
    have hcprev : (facesOfCard L (k - 1 + 1)).card = 0 := by
      rwa [show k - 1 + 1 = k by omega]
    rw [Fintype.card_coe, hcprev] at hprev
    rw [hcard, Nat.eq_zero_of_le_zero hcurr, Nat.eq_zero_of_le_zero hprev]
    simp

/--
**Stanley's interval-decomposition conjecture for complexes with acyclic links is false.** It is
not true that for every integer $k \ge 1$ and every finite simplicial complex $K$ on the vertex set
$\mathbb{N}$ (a finite family of finite subsets of $\mathbb{N}$ closed under taking subsets) such
that the link $\mathrm{lk}_K(F) = \{G \in K : G \cap F = \emptyset,\ G \cup F \in K\}$ of every
face $F \in K$ with fewer than $k$ vertices is acyclic over $\mathbb{Q}$ (all of its reduced
rational homology vanishes), there are a family $B$ of finite subsets of $\mathbb{N}$, closed under
taking subsets, and faces $\mathrm{top}(F) \in K$ for $F \in B$ with $F \subseteq \mathrm{top}(F)$
and $|\mathrm{top}(F)| = |F| + k$, such that every face of $K$ lies in the interval
$[F, \mathrm{top}(F)]$ for exactly one $F \in B$.

Doolittle and Goeckner constructed a complex with $k = 2$ (a $2$-fold acyclic complex) that cannot
be partitioned into intervals $[F, F']$ with $|F'| = |F| + 2$ at all; the case $k = 1$ is
Stanley's theorem.

Source: R. P. Stanley,
Positivity Problems and Conjectures in Algebraic Combinatorics (1999), Problem 5 (interval
decompositions of complexes with acyclic links); resolution: J. Doolittle and B. Goeckner, Resolving
Stanley's conjecture on k-fold acyclic complexes, FPSAC 2019 (Sém. Lothar. Combin. 82B, Article 46),
arXiv:1811.08518, §3: Theorem 3.2 (gluing N copies of Δ along Γ preserves k-fold acyclicity and
non-decomposability for N > ℓ/2^k) with Theorem 3.4 (Φ = (Δ, Γ) is not rank 2 boolean decomposable);
"Ω₁₇ is a counterexample to Conjecture 1.3" (Stanley's Conjecture 2.4 = Problem 5 of the 1999 list,
k = 2), https://arxiv.org/abs/1811.08518.
-/
theorem acyclicLinksIntervalDecomposition_refuted :
    ¬ acyclicLinksIntervalDecomposition := by
  intro h
  exact no_partition (h 2 (by decide) complex simplicial acyclic_link)

end MathlibExt.Combinatorics.AcyclicLinksIntervalDecompositionAMR156Problem0004Wanted
