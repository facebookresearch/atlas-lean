/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Filter.AtTopBot.Defs
public import MathlibExt.Combinatorics.HypergraphColoringShared
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.NormNum

/-!
# Edges of hypergraphs with given chromatic number (Erdős Problem 832)

Erdős Problem 832: let `r ≥ 3` and `k` be sufficiently large in terms of `r`. Does every `r`-uniform
hypergraph with chromatic number `k` have at least `C((r - 1)(k - 1) + 1, r)` edges, with equality
only for the complete hypergraph on `(r - 1)(k - 1) + 1` vertices?

We use the covering argument of Alon's Proposition 1 with an explicit cover for `r = 15`,
rather than the general Turán number estimate in the paper. The construction yields strictly
fewer edges than the benchmark for all `k ≥ 1301` at that uniformity.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.HypergraphChromaticEdgeCountErdosProblem832Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #832, https://www.erdosproblems.com/832 (status
DISPROVED). UnsolvedMath record UM-30007052 (`EP-832`), dataset ulamai/UnsolvedMath v1.8.0.

Hypergraphs are finite sets of `r`-element edges on `Fin n`; chromatic number `k` means
`k`-colorable and not `(k - 1)`-colorable, a coloring being proper when no edge is monochromatic.
The complete hypergraph on `S` is `S.powersetCard r`. Compared with the formal-conjectures statement
`ErdosProblems/832.lean` (equivalent; no code imported).
-/

open MathlibExt.Combinatorics.HypergraphColoringShared

/-- **Erdős Problem 832.** The statement that for every integer $r \ge 3$ there is a $K$ such that
for every $k \ge K$, every $n$ and every $r$-uniform hypergraph $H$ on the vertex set
$\{0, \dots, n-1\}$ with chromatic number $k$ (it is $k$-colorable but not $(k-1)$-colorable),
$H$ has at least $\binom{(r-1)(k-1)+1}{r}$ edges, and if it has exactly that many edges then it is
the complete $r$-uniform hypergraph on some set of $(r-1)(k-1)+1$ of its vertices. -/
def chromaticEdgeLowerBound : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ᶠ k : ℕ in Filter.atTop, ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
    (∀ e ∈ H, e.card = r) → HypergraphColorable H k → ¬ HypergraphColorable H (k - 1) →
      ((r - 1) * (k - 1) + 1).choose r ≤ H.card ∧
        (H.card = ((r - 1) * (k - 1) + 1).choose r →
          ∃ S : Finset (Fin n), S.card = (r - 1) * (k - 1) + 1 ∧ H = S.powersetCard r)

open Finset

/-- Split `Fin (3 * q)` into three labeled classes of size `q`, with labels added modulo three. -/
private def label {q : ℕ} (v : Fin (3 * q)) : Fin 3 :=
  (finProdFinEquiv.symm v : Fin 3 × Fin q).1

private noncomputable def coveringEdges (q : ℕ) : Finset (Finset (Fin (3 * q))) := by
  classical
  exact (univ.powersetCard 15).filter fun e =>
    (∑ v ∈ e, label v) = 0 ∨ ∃ a : Fin 3, ∀ v ∈ e, label v ≠ a

private lemma mem_coveringEdges {q : ℕ} {e : Finset (Fin (3 * q))} :
    e ∈ coveringEdges q ↔
      e.card = 15 ∧ ((∑ v ∈ e, label v) = 0 ∨ ∃ a : Fin 3, ∀ v ∈ e, label v ≠ a) := by
  classical
  simp [coveringEdges, mem_powersetCard]

-- If all three labels occur, delete a vertex with the same label as the total sum.
private lemma coveringEdges_covers {q : ℕ} {s : Finset (Fin (3 * q))} (hs : s.card = 16) :
    ∃ e ∈ coveringEdges q, e ⊆ s := by
  classical
  have eraseCard (v : Fin (3 * q)) (hv : v ∈ s) : (s.erase v).card = 15 := by
    rw [card_erase_of_mem hv, hs]
  by_cases hall : ∀ a : Fin 3, ∃ v ∈ s, label v = a
  · obtain ⟨v, hv, hl⟩ := hall (∑ w ∈ s, label w)
    refine ⟨s.erase v, mem_coveringEdges.mpr ⟨eraseCard v hv, Or.inl ?_⟩, erase_subset _ _⟩
    exact add_right_cancel (b := label v) ((sum_erase_add s label hv).trans (hl.symm.trans
      (zero_add _).symm))
  · push Not at hall
    obtain ⟨a, ha⟩ := hall
    obtain ⟨v, hv⟩ : s.Nonempty := card_pos.mp (by omega)
    exact ⟨s.erase v, mem_coveringEdges.mpr ⟨eraseCard v hv, Or.inr
      ⟨a, fun w hw => ha w (erase_subset _ _ hw)⟩⟩, erase_subset _ _⟩

private lemma not_colorable_coveringEdges (m : ℕ) :
    ¬ HypergraphColorable (coveringEdges (5 * m + 1)) m := by
  rintro ⟨c, hc⟩
  have hlarge : Fintype.card (Fin m) * 15 < Fintype.card (Fin (3 * (5 * m + 1))) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨a, ha⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card c hlarge
  obtain ⟨s, hs, hcard⟩ := exists_subset_card_eq (show 16 ≤ _ from ha)
  obtain ⟨e, he, hes⟩ := coveringEdges_covers hcard
  obtain ⟨u, hu, v, hv, huv⟩ := hc e he
  exact huv ((mem_filter.mp (hs (hes hu))).2.trans (mem_filter.mp (hs (hes hv))).2.symm)

private lemma exists_critical_subfamily {n m r : ℕ} {E : Finset (Finset (Fin n))}
    (hm : 0 < m) (hr : 2 ≤ r) (huniform : ∀ e ∈ E, e.card = r)
    (hE : ¬ HypergraphColorable E m) :
    ∃ H ⊆ E, HypergraphColorable H (m + 1) ∧ ¬ HypergraphColorable H m := by
  classical
  have hex : ∃ d : ℕ, ∃ H ⊆ E, H.card = d ∧ ¬ HypergraphColorable H m :=
    ⟨E.card, E, Subset.rfl, rfl, hE⟩
  obtain ⟨H, hHE, hmin, hH⟩ := Nat.find_spec hex
  have hnonempty : H.Nonempty := by
    by_contra! h
    apply hH
    refine ⟨fun _ => ⟨0, hm⟩, ?_⟩
    intro e he
    have he' : e ∈ (∅ : Finset (Finset (Fin n))) := h ▸ he
    exact (notMem_empty e he').elim
  obtain ⟨e, he⟩ := hnonempty
  have hdel : HypergraphColorable (H.erase e) m := by
    by_contra hd
    have hleast := Nat.find_min' hex ⟨H.erase e, (erase_subset _ _).trans hHE, rfl, hd⟩
    exact (not_le_of_gt (card_erase_lt_of_mem he)) (hmin.trans_le hleast)
  obtain ⟨c, hc⟩ := hdel
  have heCard := huniform e (hHE he)
  obtain ⟨x, hx⟩ : e.Nonempty := card_pos.mp (by omega)
  let c' (v : Fin n) : Fin (m + 1) := if v = x then Fin.last m else (c v).castSucc
  refine ⟨H, hHE, ⟨c', ?_⟩, hH⟩
  intro d hd
  by_cases hxd : x ∈ d
  · have hdCard := huniform d (hHE hd)
    obtain ⟨y, hy⟩ : (d.erase x).Nonempty := card_pos.mp (by rw [card_erase_of_mem hxd]; omega)
    obtain ⟨hyx, hyd⟩ := mem_erase.mp hy
    refine ⟨x, hxd, y, hyd, ?_⟩
    simpa [c', hyx] using (Fin.castSucc_lt_last (c y)).ne.symm
  · have hde : d ≠ e := fun h => hxd (h.symm ▸ hx)
    obtain ⟨u, hu, v, hv, huv⟩ := hc d (mem_erase.mpr ⟨hde, hd⟩)
    have hux : u ≠ x := fun h => hxd (h ▸ hu)
    have hvx : v ≠ x := fun h => hxd (h ▸ hv)
    exact ⟨u, hu, v, hv, by simpa [c', hux, hvx] using huv⟩

private lemma card_label_fiber (q : ℕ) (a : Fin 3) :
    Fintype.card {v : Fin (3 * q) // label v = a} = q := by
  let e : {v : Fin (3 * q) // label v = a} ≃ Fin q :=
    { toFun := fun v => (finProdFinEquiv.symm v.val : Fin 3 × Fin q).2
      invFun := fun i => ⟨finProdFinEquiv (a, i), by simp [label]⟩
      left_inv := by
        intro v
        apply Subtype.ext
        change finProdFinEquiv (a, (finProdFinEquiv.symm v.val : Fin 3 × Fin q).2) = v.val
        calc
          finProdFinEquiv (a, (finProdFinEquiv.symm v.val : Fin 3 × Fin q).2) =
              finProdFinEquiv (finProdFinEquiv.symm v.val) :=
            congrArg finProdFinEquiv (Prod.ext v.property.symm rfl)
          _ = v.val := finProdFinEquiv.apply_symm_apply v.val
      right_inv := fun i => by simp }
  simpa using Fintype.card_congr e

private lemma card_zeroSumTuples_le (q : ℕ) :
    Fintype.card {f : Fin 15 → Fin (3 * q) // (∑ i, label (f i)) = 0} ≤ (3 * q) ^ 14 * q := by
  let lastCoord : Fin (3 * q) → Fin q := fun v => (finProdFinEquiv.symm v : Fin 3 × Fin q).2
  let encode (f : {f : Fin 15 → Fin (3 * q) // (∑ i, label (f i)) = 0}) :
      (Fin 14 → Fin (3 * q)) × Fin q := (fun i => f.val i.castSucc, lastCoord (f.val (Fin.last 14)))
  refine (Fintype.card_le_of_injective encode ?_).trans_eq ?_
  · intro f g h
    have hinit (i : Fin 14) : f.val i.castSucc = g.val i.castSucc :=
      congrArg (fun p => p.1 i) h
    have hlast := congrArg Prod.snd h
    have hf := f.property
    have hg := g.property
    rw [Fin.sum_univ_castSucc] at hf hg
    simp only [hinit] at hf
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ hinit i
    apply finProdFinEquiv.symm.injective
    exact Prod.ext (add_left_cancel (hf.trans hg.symm)) hlast
  · simp

private lemma card_avoidingTuples_le (q : ℕ) (a : Fin 3) :
    Fintype.card {f : Fin 15 → Fin (3 * q) // ∀ i, label (f i) ≠ a} ≤ (2 * q) ^ 15 := by
  have hcard : Fintype.card {v : Fin (3 * q) // label v ≠ a} = 2 * q := by
    rw [Fintype.card_subtype_compl (fun v : Fin (3 * q) => label v = a), card_label_fiber,
      Fintype.card_fin]
    omega
  let restrict (f : {f : Fin 15 → Fin (3 * q) // ∀ i, label (f i) ≠ a}) :
      Fin 15 → {v : Fin (3 * q) // label v ≠ a} := fun i => ⟨f.val i, f.property i⟩
  refine (Fintype.card_le_of_injective restrict ?_).trans_eq ?_
  · intro f g h
    exact Subtype.ext (funext fun i => congrArg (fun t => (t i).val) h)
  · rw [Fintype.card_pi_const, hcard]

private lemma card_missingLabelTuples_le (q : ℕ) :
    Fintype.card {f : Fin 15 → Fin (3 * q) // ∃ a : Fin 3, ∀ i, label (f i) ≠ a} ≤
      3 * (2 * q) ^ 15 := by
  classical
  let encode (f : {f : Fin 15 → Fin (3 * q) // ∃ a : Fin 3, ∀ i, label (f i) ≠ a}) :
      Σ a : Fin 3, {f : Fin 15 → Fin (3 * q) // ∀ i, label (f i) ≠ a} :=
    ⟨f.property.choose, f.val, f.property.choose_spec⟩
  calc
    _ ≤ Fintype.card (Σ a : Fin 3, {f : Fin 15 → Fin (3 * q) // ∀ i, label (f i) ≠ a}) :=
      Fintype.card_le_of_injective encode fun _ _ h =>
        Subtype.ext (congrArg (fun p => p.2.val) h)
    _ ≤ _ := by
      rw [Fintype.card_sigma]
      simpa using sum_le_sum (s := (univ : Finset (Fin 3))) (fun a _ => card_avoidingTuples_le q a)

-- Each edge contributes 15! different listings. Allow repeated vertices only in the upper bound.
private lemma factorial_mul_card_coveringEdges_le (q : ℕ) :
    Nat.factorial 15 * (coveringEdges q).card ≤ (3 * q) ^ 14 * q + 3 * (2 * q) ^ 15 := by
  classical
  let Listing := Σ e : ↥(coveringEdges q), (Fin 15 ≃ ↥e.val)
  let Good := {f : Fin 15 → Fin (3 * q) //
    (∑ i, label (f i)) = 0 ∨ ∃ a : Fin 3, ∀ i, label (f i) ≠ a}
  have hlist : Fintype.card Listing = Nat.factorial 15 * (coveringEdges q).card := by
    have hc (e : ↥(coveringEdges q)) : Fintype.card (Fin 15 ≃ ↥e.val) = Nat.factorial 15 := by
      let f : Fin 15 ≃ ↥e.val := Fintype.equivOfCardEq (by
        rw [Fintype.card_fin, Fintype.card_coe, (mem_coveringEdges.mp e.property).1])
      simpa only [Fintype.card_fin] using Fintype.card_equiv f
    change Fintype.card (Σ e : ↥(coveringEdges q), (Fin 15 ≃ ↥e.val)) = _
    rw [Fintype.card_sigma]
    simp [hc, Nat.mul_comm]
  let encode (p : Listing) : Good := ⟨fun i => (p.2 i).val, by
    rcases (mem_coveringEdges.mp p.1.property).2 with hsum | ⟨a, ha⟩
    · left
      calc
        (∑ i, label ((p.2 i).val)) = ∑ v : ↥p.1.val, label v.val :=
          Equiv.sum_comp p.2 (fun v : ↥p.1.val => label v.val)
        _ = 0 := (sum_subtype p.1.val (fun _ => Iff.rfl) label).symm.trans hsum
    · exact Or.inr ⟨a, fun i => ha _ (p.2 i).property⟩⟩
  have hinj : Function.Injective encode := by
    rintro ⟨e, f⟩ ⟨d, g⟩ h
    have hfg (i : Fin 15) : (f i).val = (g i).val := congrArg (fun t => t.val i) h
    have mem_of_listing {E : Finset (Fin (3 * q))} (F : Fin 15 ≃ ↥E) (x : Fin (3 * q)) :
        x ∈ E ↔ ∃ i, (F i).val = x := by
      constructor
      · intro hx
        obtain ⟨i, hi⟩ := F.surjective ⟨x, hx⟩
        exact ⟨i, congrArg Subtype.val hi⟩
      · rintro ⟨i, rfl⟩
        exact (F i).property
    have hed : e = d := Subtype.ext (Finset.ext fun x => by
      rw [mem_of_listing f, mem_of_listing g]
      simp only [hfg])
    subst d
    have heq : f = g := Equiv.ext fun i => Subtype.ext (hfg i)
    rw [heq]
  rw [← hlist]
  calc
    Fintype.card Listing ≤ Fintype.card Good := Fintype.card_le_of_injective encode hinj
    _ ≤ _ := (Fintype.card_subtype_or _ _).trans
      (Nat.add_le_add (card_zeroSumTuples_le q) (card_missingLabelTuples_le q))

private lemma coveringEdges_card_lt_choose (m : ℕ) (hm : 1300 ≤ m) :
    (coveringEdges (5 * m + 1)).card < (14 * m + 1).choose 15 := by
  let q := 5 * m + 1
  let b := 14 * m - 13
  have hn : 100 * (3 * q) ≤ 1501 * m := by dsimp [q]; omega
  have htwo : 100 * (2 * q) ≤ 1001 * m := by dsimp [q]; omega
  have hb : 1399 * m ≤ 100 * b := by dsimp [b]; omega
  have hp : 100 ^ 15 * (3 * q) ^ 15 ≤ 1501 ^ 15 * m ^ 15 := by
    simpa only [← Nat.mul_pow] using Nat.pow_le_pow_left hn 15
  have ht : 100 ^ 15 * (2 * q) ^ 15 ≤ 1001 ^ 15 * m ^ 15 := by
    simpa only [← Nat.mul_pow] using Nat.pow_le_pow_left htwo 15
  have hbp : 1399 ^ 15 * m ^ 15 ≤ 100 ^ 15 * b ^ 15 := by
    simpa only [← Nat.mul_pow] using Nat.pow_le_pow_left hb 15
  have hcert : (1501 : ℕ) ^ 15 + 9 * 1001 ^ 15 < 3 * 1399 ^ 15 := by norm_num
  have hscaled : 100 ^ 15 * ((3 * q) ^ 15 + 9 * (2 * q) ^ 15) < 100 ^ 15 * (3 * b ^ 15) := calc
    _ = 100 ^ 15 * (3 * q) ^ 15 + 9 * (100 ^ 15 * (2 * q) ^ 15) := by
      rw [Nat.mul_add, mul_left_comm (100 ^ 15) 9]
    _ ≤ 1501 ^ 15 * m ^ 15 + 9 * (1001 ^ 15 * m ^ 15) :=
      Nat.add_le_add hp (Nat.mul_le_mul_left 9 ht)
    _ = (1501 ^ 15 + 9 * 1001 ^ 15) * m ^ 15 := by rw [Nat.add_mul, mul_assoc]
    _ < (3 * 1399 ^ 15) * m ^ 15 := Nat.mul_lt_mul_of_pos_right hcert (Nat.pow_pos (by omega))
    _ = 3 * (1399 ^ 15 * m ^ 15) := by rw [mul_assoc]
    _ ≤ 3 * (100 ^ 15 * b ^ 15) := Nat.mul_le_mul_left 3 hbp
    _ = _ := mul_left_comm _ _ _
  have hstrict := (Nat.mul_lt_mul_left (Nat.pow_pos (by decide) : 0 < 100 ^ 15)).mp hscaled
  have hdesc : b ^ 15 ≤ (14 * m + 1).descFactorial 15 := by
    have heq : b = 14 * m + 1 + 1 - 15 := by dsimp [b]; omega
    rw [heq]
    exact Nat.pow_sub_le_descFactorial _ _
  have hcount := Nat.mul_le_mul_left 3 (factorial_mul_card_coveringEdges_le q)
  have hlt : 3 * (Nat.factorial 15 * (coveringEdges q).card) <
      3 * (Nat.factorial 15 * (14 * m + 1).choose 15) := calc
    _ ≤ 3 * ((3 * q) ^ 14 * q + 3 * (2 * q) ^ 15) := hcount
    _ = (3 * q) ^ 15 + 9 * (2 * q) ^ 15 := by
      rw [Nat.mul_add, mul_left_comm 3 ((3 * q) ^ 14), ← pow_succ (3 * q) 14, ← mul_assoc]
      rfl
    _ < 3 * b ^ 15 := hstrict
    _ ≤ _ := by rw [← Nat.descFactorial_eq_factorial_mul_choose]; exact Nat.mul_le_mul_left 3 hdesc
  exact (Nat.mul_lt_mul_left (Nat.factorial_pos _)).mp ((Nat.mul_lt_mul_left (by decide)).mp hlt)

private lemma exists_counterexample (m : ℕ) (hm : 1300 ≤ m) :
    ∃ H : Finset (Finset (Fin (3 * (5 * m + 1)))), (∀ e ∈ H, e.card = 15) ∧
      HypergraphColorable H (m + 1) ∧ ¬ HypergraphColorable H m ∧
      H.card < (14 * m + 1).choose 15 := by
  have hr : ∀ e ∈ coveringEdges (5 * m + 1), e.card = 15 :=
    fun _ he => (mem_coveringEdges.mp he).1
  obtain ⟨H, hH, hc, hnc⟩ :=
    exists_critical_subfamily (by omega) (by decide) hr (not_colorable_coveringEdges m)
  exact ⟨H, fun e he => hr e (hH he), hc, hnc,
    (card_le_card hH).trans_lt (coveringEdges_card_lt_choose m hm)⟩

/-- **Alon's refutation of Erdős Problem 832.** There is an integer $r \ge 3$ such that for
infinitely many $k$ there are an $n$ and an $r$-uniform hypergraph $H$ on the vertex set
$\{0, \dots, n-1\}$ with chromatic number $k$ (it is $k$-colorable but not $(k-1)$-colorable)
that either has fewer than $\binom{(r-1)(k-1)+1}{r}$ edges, or has exactly that many edges but is
not the complete $r$-uniform hypergraph on any set of $(r-1)(k-1)+1$ of its vertices.

Alon deduced this from an upper bound through Turán numbers: for an absolute constant $C$, every
$r \ge C$ and every $k \ge Cr$, some $r$-uniform hypergraph with chromatic number at least $k$ has
at most $(7/8)^r \binom{(r-1)(k-1)+1}{r}$ edges, and an edge-minimal one among these has
chromatic number exactly $k$. Known Turán bounds disprove the conjecture for every $r \ge 4$; the
case $r = 3$ is open.

Source: T. F. Bloom, Erdős Problems, Problem #832,
https://www.erdosproblems.com/832 (status DISPROVED); resolution: N. Alon, Hypergraphs with high
chromatic number, Graphs Combin. 1 (1985), 387-389, with f(k, s) the least number of edges of a
k-uniform hypergraph of chromatic number at least s: 'Erdős and Hajnal conjectured that for every
fixed k, if s > s_0(k) then equality holds in (2)' (f(k, s) = C((s - 1)(k - 1) + 1, k)), and 'This
conjecture is false, as easily follows from' Proposition 1 (an upper bound for f(k, s) through Turán
numbers); erdosproblems.com/832: for an absolute C, r ≥ C and k ≥ C r there is an r-uniform
hypergraph with chromatic number at least k and at most (7/8)^r C((r - 1)(k - 1) + 1, r) edges,
known Turán bounds disprove the conjecture for every r ≥ 4, and r = 3 remains open,
https://web.math.princeton.edu/~nalon/PDFS/Publications/Hypergraphs%20with%20high%20chromatic%20number.pdf.
-/
theorem chromaticEdgeLowerBound_refuted : ¬ chromaticEdgeLowerBound := by
  intro h
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (h 15 (by decide))
  let m := max K 1300
  have hm : 1300 ≤ m := le_max_right _ _
  have hk : K ≤ m + 1 := (le_max_left K 1300).trans (Nat.le_succ m)
  obtain ⟨H, hr, hc, hnc, hlt⟩ := exists_counterexample m hm
  have hbound := (hK (m + 1) hk _ H hr hc (by simpa using hnc)).1
  exact (not_le_of_gt hlt) (by simpa using hbound)

end MathlibExt.Combinatorics.HypergraphChromaticEdgeCountErdosProblem832Wanted
