/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Convert

/-!
# Containment of simultaneous core partitions

Every simultaneous core for two coprime positive moduli is contained in any simultaneous core
of maximum cardinality. We compare the positions of the first gaps in the residue classes of
the finite beta sets of the diagrams. In an `s`-core, each residue class modulo `s` is occupied
up to its first gap. In a simultaneous core the sorted first gaps differ by at most `t`, whereas
the containing core has its first gaps spaced by exactly `t`. At each cut of the beta set we
can therefore inject either the beads above the cut or the gaps below it into the corresponding
positions for the containing core. Both comparisons give the required row-length inequality.

Source: J. B. Olsson (joint with D. Stanton, C. Bessenrodt, G. Navarro, P. H. Tiep), On block
identities and block inclusions, in Representations of Finite Groups, Oberwolfach Reports 3 (2006),
no. 15, p. 912 ff., section 2 (Block identities), DOI 10.4171/OWR/2006/15. UnsolvedMath record
UM-30000448 (`OWR-1265-006`), dataset ulamai/UnsolvedMath v1.8.0.

Young diagrams are Mathlib's `YoungDiagram` (finite down-sets of `ℕ × ℕ`, containment is `≤`, size
is `card`); an `s`-core is a diagram with no hook length divisible by `s`. The report itself defines
`κ_pq` as the simultaneous core of maximum size, so the target quantifies over every simultaneous
`s`- and `t`-core `κ` of maximum size (there is one, since only finitely many simultaneous cores
exist for coprime `s`, `t`); by the report it is `κ_pq`. The hypotheses are those of the problem and
of Fayers's theorem (coprime positive integers); the cases `s = 1` or `t = 1` are included and
trivial (the only `1`-core is the empty diagram).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimultaneousCoreContainmentOWR1265Problem006Wanted

/-- **$s$-cores of Young diagrams.** Let $s$ be a natural number and $\mu$ a Young diagram, with
rows and columns numbered from $0$; write $r_i$ for the length of row $i$ of $\mu$ and $c_j$ for
the length of column $j$ of $\mu$. The hook length of the cell $(i, j)$ of $\mu$ (row $i$, column
$j$) is $(r_i - j) + (c_j - i) - 1$: the cells to its right in row $i$, the cells below it in
column $j$, and the cell itself (both differences count the cell, so one is subtracted). The
diagram $\mu$ is an *$s$-core* if no cell of $\mu$ has hook length divisible by $s$. -/
def IsCore (s : ℕ) (μ : YoungDiagram) : Prop :=
  ∀ c ∈ μ, ¬ s ∣ (μ.rowLen c.1 - c.2) + (μ.colLen c.2 - c.1) - 1

/-- **Containment of simultaneous cores (Olsson–Stanton question).** The proposition that for all
coprime positive integers $s$ and $t$ and every Young diagram $\kappa$ that is both an $s$-core and
a $t$-core and has at least as many cells as every Young diagram that is both an $s$-core and a
$t$-core, every Young diagram that is both an $s$-core and a $t$-core is contained in $\kappa$,
that is, each of its cells is a cell of $\kappa$.

The proposition does not assert that such a $\kappa$ exists. In the report, $\kappa_{s,t}$ is the
partition of maximum size that is both an $s$-core and a $t$-core, and the question is whether
the Young diagram of every such partition is contained in that of $\kappa_{s,t}$. -/
def simultaneousCoreContainment : Prop :=
  ∀ s t : ℕ, 0 < s → 0 < t → Nat.Coprime s t →
    ∀ κ : YoungDiagram, IsCore s κ → IsCore t κ →
      (∀ ν : YoungDiagram, IsCore s ν → IsCore t ν → ν.card ≤ κ.card) →
        ∀ μ : YoungDiagram, IsCore s μ → IsCore t μ → μ ≤ κ

open Finset YoungDiagram

-- Number the padded rows from bottom to top, so their beta numbers increase.
private def bead (μ : YoungDiagram) {n : ℕ} (i : Fin n) : ℕ :=
  i + μ.rowLen (n - 1 - i)

private lemma bead_strict (μ : YoungDiagram) (n : ℕ) : StrictMono (bead μ (n := n)) := by
  intro i j hij
  have h : i.val < j.val := hij
  have := μ.rowLen_anti (n - 1 - j) (n - 1 - i) (by omega)
  simp only [bead]
  omega

private def beads (μ : YoungDiagram) (n : ℕ) : Finset ℕ := univ.image (bead μ (n := n))

private lemma card_beads (μ : YoungDiagram) (n : ℕ) : (beads μ n).card = n := by
  simp [beads, card_image_of_injective _ (bead_strict μ n).injective]

private def gap (μ : YoungDiagram) (n j : ℕ) : ℕ := j + (n - μ.colLen j)

private lemma gap_lt_bead {μ : YoungDiagram} {n j : ℕ} (hn : μ.colLen 0 ≤ n) (i : Fin n) :
    gap μ n j < bead μ i ↔ (n - 1 - i.val, j) ∈ μ := by
  have hc0 := μ.colLen_anti 0 j (Nat.zero_le _)
  have hi := i.isLt
  by_cases h : (n - 1 - i.val, j) ∈ μ
  · rw [iff_true_intro h, iff_true]
    have hcj := mem_iff_lt_colLen.mp h
    have hr := mem_iff_lt_rowLen.mp h
    simp only [gap, bead]
    omega
  · rw [iff_false_intro h, iff_false]
    have h₁ := mt mem_iff_lt_colLen.mpr h
    have h₂ := mt mem_iff_lt_rowLen.mpr h
    simp only [gap, bead]
    omega

private lemma gap_notMem {μ : YoungDiagram} {n : ℕ} (hn : μ.colLen 0 ≤ n) (j : ℕ) :
    gap μ n j ∉ beads μ n := by
  simp only [beads, mem_image, mem_univ, true_and, not_exists]
  intro i he
  have hi := i.isLt
  have h := (gap_lt_bead hn i (j := j)).not.mp (by omega)
  have h₁ := mt mem_iff_lt_colLen.mpr h
  have h₂ := mt mem_iff_lt_rowLen.mpr h
  simp only [gap, bead] at he
  omega

private lemma exists_gap {μ : YoungDiagram} {n x : ℕ} (hn : μ.colLen 0 ≤ n)
    (hx : x ∉ beads μ n) : ∃ j, gap μ n j = x := by
  -- A sufficiently long initial interval is filled by the row and column positions.
  let w := x + μ.rowLen 0 + 1
  let G := (range w).image (gap μ n)
  have hG : StrictMono (gap μ n) := by
    intro i j hij
    have hc0 := μ.colLen_anti i j hij.le
    simp only [gap]
    omega
  have hd : Disjoint (beads μ n) G := by
    rw [disjoint_left]
    intro a ha hb
    obtain ⟨j, _, rfl⟩ := mem_image.mp hb
    exact gap_notMem hn j ha
  have he : beads μ n ∪ G = range (n + w) := by
    apply eq_of_subset_of_card_le
    · intro a ha
      rcases mem_union.mp ha with h | h
      · obtain ⟨i, _, rfl⟩ := mem_image.mp h
        have := μ.rowLen_anti 0 (n - 1 - i) (Nat.zero_le _)
        have := i.isLt
        simp only [mem_range, bead, w]
        omega
      · obtain ⟨j, hj, rfl⟩ := mem_image.mp h
        simp only [mem_range, gap] at *
        omega
    · simp [card_union_of_disjoint hd, card_beads, G, card_image_of_injective _ hG.injective]
  have : x ∈ beads μ n ∪ G := he ▸ mem_range.mpr (by dsimp [w]; omega)
  obtain ⟨j, _, hj⟩ := mem_image.mp ((mem_union.mp this).resolve_left hx)
  exact ⟨j, hj⟩

private def Closed (s : ℕ) (B : Finset ℕ) : Prop := ∀ x ∉ B, x + s ∉ B

private lemma Closed.add_mul {s : ℕ} {B : Finset ℕ} (hc : Closed s B) {x : ℕ} (hx : x ∉ B)
    (k : ℕ) : x + s * k ∉ B := by
  induction k with
  | zero => simpa using hx
  | succ k ih => simpa [Nat.mul_succ, Nat.add_assoc] using hc _ ih

-- The hook at a cell is the distance from its column gap to its row bead.
private lemma core_iff_closed (μ : YoungDiagram) {n : ℕ} (hn : μ.colLen 0 ≤ n) (s : ℕ) :
    IsCore s μ ↔ Closed s (beads μ n) := by
  constructor
  · intro hc x hx hxs
    obtain ⟨j, rfl⟩ := exists_gap hn hx
    obtain ⟨i, _, hi⟩ := mem_image.mp hxs
    have hs : 0 < s := by by_contra! hz; simp_all
    have hcell := (gap_lt_bead (j := j) hn i).mp (by omega)
    apply hc _ hcell
    have hr := mem_iff_lt_rowLen.mp hcell
    have hcj := mem_iff_lt_colLen.mp hcell
    have hc0 := μ.colLen_anti 0 j (Nat.zero_le _)
    have := i.isLt
    convert dvd_refl s using 1
    simp only [bead, gap] at hi ⊢
    omega
  · intro hcl ⟨r, j⟩ hc hd
    have hr := mem_iff_lt_colLen.mp hc
    have hj := mem_iff_lt_rowLen.mp hc
    have hcol := μ.colLen_anti 0 j (Nat.zero_le _)
    let i : Fin n := ⟨n - 1 - r, by omega⟩
    have hi : n - 1 - i.val = r := by dsimp [i]; omega
    obtain ⟨k, hk⟩ := hd
    have he : bead μ i = gap μ n j + s * k := by
      simp only [bead, hi, gap]
      change μ.rowLen r - j + (μ.colLen j - r) - 1 = s * k at hk
      change n - 1 - r + _ = _
      omega
    apply hcl.add_mul (gap_notMem hn j) k
    exact he ▸ mem_image_of_mem _ (mem_univ i)

private lemma exists_diagram (B : Finset ℕ) :
    ∃ μ : YoungDiagram, μ.colLen 0 ≤ B.card ∧ beads μ B.card = B := by
  generalize hcard : B.card = n
  let f : Fin n ↪o ℕ := B.orderEmbOfFin hcard
  have hle (i : Fin n) : i.val ≤ f i := by
    cases n with
    | zero => exact i.elim0
    | succ m =>
      induction i using Fin.induction with
      | zero => exact Nat.zero_le _
      | succ k ih => exact Nat.succ_le_of_lt (ih.trans_lt (f.strictMono k.castSucc_lt_succ))
  have hmono : Monotone (fun i : Fin n => f i - i.val) := by
    cases n with
    | zero => intro i; exact i.elim0
    | succ m =>
      apply Fin.monotone_iff_le_succ.mpr
      intro i
      have := f.strictMono i.castSucc_lt_succ
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
  let w := List.ofFn fun i : Fin n => f i.rev - i.rev.val
  have hw : w.SortedGE := List.sortedGE_ofFn_iff.mpr fun _ _ hij => hmono (Fin.rev_le_rev.mpr hij)
  let μ := ofRowLens w hw
  have hn : w.length = n := List.length_ofFn
  refine ⟨μ, ?_, ?_⟩
  · by_contra! h
    have hm : (n, 0) ∈ μ := mem_iff_lt_colLen.mpr h
    obtain ⟨h', _⟩ := mem_ofRowLens.mp hm
    omega
  · have hb (i : Fin n) : bead μ i = f i := by
      have hh := rowLen_ofRowLens (hw := hw) (⟨i.rev.val, hn.symm ▸ i.rev.isLt⟩ : Fin w.length)
      have hv : n - 1 - i.val = i.rev.val := by rw [Fin.val_rev]; omega
      simp only [bead, hv, μ, hh]
      change i.val + w[i.rev.val]'(hn.symm ▸ i.rev.isLt) = f i
      have hw' : w[i.rev.val]'(hn.symm ▸ i.rev.isLt) = f i - i.val := by
        simp only [w, List.getElem_ofFn]
        change f i.rev.rev - i.rev.rev.val = _
        rw [Fin.rev_rev]
      rw [hw']
      exact Nat.add_sub_of_le (hle i)
    change univ.image (bead μ (n := n)) = B
    simpa only [funext hb] using B.image_orderEmbOfFin_univ hcard

private def above (B : Finset ℕ) (x : ℕ) := B.filter (x ≤ ·)
private def below (B : Finset ℕ) (x : ℕ) := range x \ B

private lemma balance (B : Finset ℕ) (x : ℕ) :
    (above B x).card + x = (below B x).card + B.card := by
  have h : B \ range x = above B x := by ext; simp [above]
  have h₁ := card_sdiff_add_card_inter B (range x)
  have h₂ := card_sdiff_add_card_inter (range x) B
  rw [h] at h₁
  rw [inter_comm, card_range] at h₂
  dsimp [below]
  omega

private lemma le_of_above {μ ν : YoungDiagram} {n : ℕ} (hn : μ.colLen 0 ≤ n)
    (h : ∀ x, (above (beads μ n) x).card ≤ (above (beads ν n) x).card) : μ ≤ ν := by
  rintro ⟨r, j⟩ hc
  have hcol := μ.colLen_anti 0 j (Nat.zero_le _)
  have hr := mem_iff_lt_colLen.mp hc
  have hj := mem_iff_lt_rowLen.mp hc
  let i : Fin n := ⟨n - 1 - r, by omega⟩
  have hi : n - 1 - i.val = r := by dsimp [i]; omega
  suffices bead μ i ≤ bead ν i by
    rw [mem_iff_lt_rowLen]
    simp only [bead, hi] at this
    omega
  by_contra! hn'
  have sub : above (beads ν n) (bead μ i) ⊆ (Ioi i).image (bead ν) := by
    intro a ha
    obtain ⟨ha', hle⟩ := mem_filter.mp ha
    obtain ⟨k, _, rfl⟩ := mem_image.mp ha'
    exact mem_image.mpr ⟨k, mem_Ioi.mpr ((bead_strict ν n).lt_iff_lt.mp (hn'.trans_le hle)), rfl⟩
  have sub' : (Ici i).image (bead μ) ⊆ above (beads μ n) (bead μ i) := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := mem_image.mp ha
    exact mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ _),
      (bead_strict μ n).monotone (mem_Ici.mp hk)⟩
  have hc' := (card_le_card sub').trans ((h _).trans (card_le_card sub))
  rw [card_image_of_injective _ (bead_strict μ n).injective,
    card_image_of_injective _ (bead_strict ν n).injective, Fin.card_Ici, Fin.card_Ioi] at hc'
  have := i.isLt
  omega

-- Each runner is specified by its first unoccupied position.
private structure Runners (s : ℕ) (B : Finset ℕ) where
  first : Fin s → ℕ
  distinct : ∀ {i j}, first i ≡ first j [MOD s] → i = j
  occupied : ∀ i x, x ≡ first i [MOD s] → (x ∈ B ↔ x < first i)

private noncomputable def residuePerm {s : ℕ} (hs : 0 < s) (p : Fin s → ℕ)
    (hd : ∀ {i j}, p i ≡ p j [MOD s] → i = j) : Fin s ≃ Fin s := by
  let f (i : Fin s) : Fin s := ⟨p i % s, Nat.mod_lt _ hs⟩
  have hf : Function.Injective f := fun _ _ h => hd (congrArg Fin.val h)
  exact Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩

private noncomputable def Runners.index {s : ℕ} {B : Finset ℕ} (R : Runners s B) (hs : 0 < s)
    (x : ℕ) : Fin s := (residuePerm hs R.first R.distinct).symm ⟨x % s, Nat.mod_lt _ hs⟩

private lemma Runners.index_eq {s : ℕ} {B : Finset ℕ} (R : Runners s B) (hs : 0 < s)
    (x : ℕ) (i : Fin s) : R.index hs x = i ↔ x ≡ R.first i [MOD s] := by
  rw [Runners.index, Equiv.symm_apply_eq]
  exact Fin.ext_iff

private lemma exists_runners {s : ℕ} (hs : 0 < s) (B : Finset ℕ) (hc : Closed s B) :
    ∃ R : Runners s B, StrictMono R.first := by
  have ex (r : Fin s) : ∃ x, x ≡ r.val [MOD s] ∧ x ∉ B := by
    let k := B.sup id + 1
    refine ⟨s * k + r, Nat.ModEq.modulus_mul_add, fun h => ?_⟩
    have hb := le_sup (f := id) h
    change s * k + r.val ≤ B.sup id at hb
    have : k ≤ s * k := Nat.le_mul_of_pos_left _ hs
    dsimp [k] at *
    omega
  let g (r : Fin s) := Nat.find (ex r)
  have hg (r : Fin s) : g r ≡ r.val [MOD s] ∧ g r ∉ B := Nat.find_spec (ex r)
  have inj : Function.Injective g := by
    intro i j h
    have hh := (hg i).1.symm.trans (h ▸ (hg j).1 : g i ≡ j.val [MOD s])
    exact Fin.ext (by simpa [Nat.ModEq, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hh)
  let A := univ.image g
  have hcard : A.card = s := by simp [A, card_image_of_injective _ inj]
  let p := A.orderEmbOfFin hcard
  have memp (i : Fin s) : ∃ r, g r = p i := by
    simpa only [A, mem_image, mem_univ, true_and] using A.orderEmbOfFin_mem hcard i
  refine ⟨⟨p, ?_, ?_⟩, p.strictMono⟩
  · intro i j hij
    obtain ⟨a, ha⟩ := memp i
    obtain ⟨b, hb⟩ := memp j
    rw [← ha, ← hb] at hij
    have hh := (hg a).1.symm.trans (hij.trans (hg b).1)
    have he : a = b := Fin.ext (by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using hh)
    exact p.injective (ha.symm.trans (he ▸ hb))
  · intro i x hres
    obtain ⟨r, hr⟩ := memp i
    rw [← hr] at hres ⊢
    constructor
    · intro hx
      by_contra! hle
      obtain ⟨k, rfl⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hres.symm
      exact hc.add_mul (hg r).2 k hx
    · intro hlt
      by_contra hx
      exact (Nat.find_min' (ex r) ⟨hres.trans (hg r).1, hx⟩).not_gt hlt

private lemma progression_distinct {s t : ℕ} (h : s.Coprime t) (a : ℕ) {i j : Fin s}
    (he : a + i.val * t ≡ a + j.val * t [MOD s]) : i = j := by
  have hh := Nat.ModEq.cancel_right_of_coprime h ((Nat.ModEq.refl a).add_left_cancel he)
  exact Fin.ext (by simpa [Nat.ModEq, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hh)

-- Choose equally spaced first gaps. Padding by a ensures at least a beads.
private lemma canonical {s t : ℕ} (hs : 0 < s) (hc : s.Coprime t) (a : ℕ) :
    ∃ (C : Finset ℕ) (Q : Runners s C), a ≤ C.card ∧ Closed s C ∧ Closed t C ∧
      ∀ i, Q.first i = a + i.val * t := by
  let q (i : Fin s) := a + i.val * t
  let e := residuePerm hs q (progression_distinct hc a)
  let idx (x : ℕ) := e.symm ⟨x % s, Nat.mod_lt _ hs⟩
  have hi (x : ℕ) (i : Fin s) : idx x = i ↔ x ≡ q i [MOD s] := by
    change e.symm _ = _ ↔ _
    rw [Equiv.symm_apply_eq]
    exact Fin.ext_iff
  let C := (range (a + s * t)).filter fun x => x < q (idx x)
  have hC (x : ℕ) : x ∈ C ↔ x < q (idx x) := by
    simp only [C, mem_filter, mem_range, and_iff_right_iff_imp]
    have h := Nat.mul_le_mul_right t (idx x).isLt.le
    dsimp [q]
    omega
  let Q : Runners s C := ⟨q, progression_distinct hc a, fun i x hx => ((hi x i).mpr hx) ▸ hC x⟩
  refine ⟨C, Q, ?_, ?_, ?_, fun _ => rfl⟩
  · rw [← card_range a]
    apply card_le_card
    intro x hx
    exact (hC x).mpr (lt_of_lt_of_le (mem_range.mp hx) (Nat.le_add_right _ _))
  · intro x hx
    rw [hC] at *
    have he : idx (x + s) = idx x := (hi _ _).mpr
      (Nat.add_modulus_modEq_iff.mpr ((hi x _).mp rfl))
    rw [he]
    omega
  · intro x hx
    rw [hC] at *
    let i := idx x
    have hr := (hi x i).mp rfl
    have hnext : q (idx (x + t)) ≤ q i + t := by
      by_cases hl : i.val + 1 < s
      · let j : Fin s := ⟨i.val + 1, hl⟩
        have hj : idx (x + t) = j := (hi _ _).mpr (by
          simpa [q, j, Nat.succ_mul, Nat.add_assoc] using hr.add_right t)
        rw [hj]
        simp [q, j, Nat.succ_mul, Nat.add_assoc]
      · have hv : i.val + 1 = s := by have := i.isLt; omega
        let z : Fin s := ⟨0, hs⟩
        have hz : idx (x + t) = z := (hi _ _).mpr (by
          have hh := hr.add_right t
          change x + t ≡ a + i.val * t + t [MOD s] at hh
          rw [Nat.add_assoc, ← Nat.succ_mul, Nat.succ_eq_add_one, hv] at hh
          simpa [q, z] using Nat.modEq_add_modulus_mul_iff.mp hh)
        rw [hz]
        simp only [q, z, Nat.zero_mul, Nat.add_zero]
        omega
    change ¬ x < q i at hx
    omega

-- A gap wider than t in the sorted list would separate a nonempty proper union of
-- residue classes preserved by addition of t. Coprimality makes that impossible.
private lemma adjacent_bound {s t : ℕ} {B : Finset ℕ} (hs : 0 < s) (hc : s.Coprime t)
    (R : Runners s B) (hp : StrictMono R.first) (hcl : Closed t B)
    (i j : Fin s) (hij : j.val = i.val + 1) : R.first j ≤ R.first i + t := by
  by_contra! hbig
  have step (k : ℕ) : R.first (R.index hs (R.first i + k * t)) ≤ R.first i := by
    induction k with
    | zero => simp [(R.index_eq hs (R.first i) i).mpr (Nat.ModEq.refl _)]
    | succ k ih =>
      let x := R.first i + k * t
      let l := R.index hs x
      let m := R.index hs (x + t)
      have hl := (R.index_eq hs x l).mp rfl
      have hm := (R.index_eq hs (x + t) m).mp rfl
      have hn : R.first l ∉ B := by simp [R.occupied l _ (Nat.ModEq.refl _)]
      have hres := (hl.symm.add_right t).trans hm
      have hm' := (R.occupied m (R.first l + t) hres).not.mp (hcl _ hn)
      have hlt : R.first m < R.first j := by
        change R.first l ≤ R.first i at ih
        omega
      have hmj : m.val < j.val := hp.lt_iff_lt.mp hlt
      have hmi : m ≤ i := by change m.val ≤ i.val; omega
      simpa only [m, x, Nat.succ_mul, Nat.add_assoc] using hp.monotone hmi
  let f (k : Fin s) := R.index hs (R.first i + k.val * t)
  have hf : Function.Injective f := by
    intro u v huv
    apply progression_distinct hc (R.first i)
    have hu := (R.index_eq hs _ (f u)).mp rfl
    have hv := (R.index_eq hs _ (f v)).mp rfl
    exact hu.trans (huv ▸ hv.symm)
  obtain ⟨k, hk⟩ := Finite.surjective_of_injective hf j
  have h := step k
  change R.first (f k) ≤ _ at h
  rw [hk] at h
  omega

-- Above a cut, move a bead by the change in its runner's first gap.
private lemma compare_above {s : ℕ} {B C : Finset ℕ} (hs : 0 < s)
    (P : Runners s B) (Q : Runners s C) (x : ℕ)
    (h : ∀ i, x < P.first i → P.first i ≤ Q.first i) :
    (above B x).card ≤ (above C x).card := by
  let i := P.index hs
  let shift (b : ℕ) := Q.first (i b) - P.first (i b)
  let f (b : ℕ) := b + shift b
  have move (b : ℕ) (hb : b ∈ above B x) :
      Q.index hs (f b) = i b ∧ f b ∈ above C x := by
    obtain ⟨hB, hxb⟩ := mem_filter.mp hb
    have hr := (P.index_eq hs b (i b)).mp rfl
    have hb' := (P.occupied _ _ hr).mp hB
    have hpq := h _ (hxb.trans_lt hb')
    have he : P.first (i b) + shift b = Q.first (i b) := Nat.add_sub_of_le hpq
    have hq : f b ≡ Q.first (i b) [MOD s] := he ▸ hr.add_right (shift b)
    refine ⟨(Q.index_eq hs _ _).mpr hq, mem_filter.mpr ⟨(Q.occupied _ _ hq).mpr ?_, ?_⟩⟩
    · dsimp [f]; omega
    · exact hxb.trans (Nat.le_add_right _ _)
  apply card_le_card_of_injOn f (fun b hb => (move b hb).2)
  intro b hb c hc he
  have hij := (move b hb).1.symm.trans (he ▸ (move c hc).1)
  change b + (Q.first (i b) - P.first (i b)) = c + (Q.first (i c) - P.first (i c)) at he
  rwa [hij, Nat.add_right_cancel_iff] at he

-- Below the cut use unoccupied positions instead, moving them down on each runner.
private lemma compare_below {s : ℕ} {B C : Finset ℕ} (hs : 0 < s)
    (P : Runners s B) (Q : Runners s C) (x : ℕ)
    (h : ∀ i, P.first i < x → Q.first i ≤ P.first i) :
    (below B x).card ≤ (below C x).card := by
  let i := P.index hs
  let f (b : ℕ) := Q.first (i b) + (b - P.first (i b))
  have move (b : ℕ) (hb : b ∈ below B x) :
      Q.index hs (f b) = i b ∧ f b ∈ below C x ∧ P.first (i b) ≤ b := by
    obtain ⟨hbx, hB⟩ := mem_sdiff.mp hb
    have hlt := mem_range.mp hbx
    have hr := (P.index_eq hs b (i b)).mp rfl
    have hpb := le_of_not_gt ((P.occupied _ _ hr).not.mp hB)
    have hqp := h _ (hpb.trans_lt hlt)
    have hq : f b ≡ Q.first (i b) [MOD s] :=
      Nat.add_modEq_left_iff.mpr ((Nat.modEq_iff_dvd' hpb).mp hr.symm)
    refine ⟨(Q.index_eq hs _ _).mpr hq, mem_sdiff.mpr ⟨mem_range.mpr ?_, ?_⟩, hpb⟩
    · dsimp [f]; omega
    · exact (Q.occupied _ _ hq).not.mpr (Nat.le_add_right _ _).not_gt
  apply card_le_card_of_injOn f (fun b hb => (move b hb).2.1)
  intro b hb c hc he
  have hij := (move b hb).1.symm.trans (he ▸ (move c hc).1)
  have hb' := (move b hb).2.2
  have hc' := (move c hc).2.2
  dsimp [f] at he
  rw [hij] at he hb'
  omega

private lemma compare {s t : ℕ} {B C : Finset ℕ} (hs : 0 < s) (hc : s.Coprime t)
    (hcard : B.card = C.card) (P : Runners s B) (Q : Runners s C) (hp : StrictMono P.first)
    (hcl : Closed t B) (a : ℕ) (hq : ∀ i, Q.first i = a + i.val * t) (x : ℕ) :
    (above B x).card ≤ (above C x).card := by
  -- The difference of the two sorted first-gap sequences is nondecreasing.
  have mono : Monotone (fun i => (Q.first i : ℤ) - P.first i) := by
    cases s with
    | zero => omega
    | succ n =>
      apply Fin.monotone_iff_le_succ.mpr
      intro i
      have hd := adjacent_bound hs hc P hp hcl i.castSucc i.succ rfl
      simp only [hq, Fin.val_castSucc, Fin.val_succ, Nat.succ_mul]
      omega
  by_cases h : ∀ i, x < P.first i → P.first i ≤ Q.first i
  · exact compare_above hs P Q x h
  · push Not at h
    obtain ⟨i, hxi, hi⟩ := h
    have hlow := compare_below hs P Q x fun j hj => by
      have hh := mono (hp.le_iff_le.mp (hj.trans hxi).le)
      dsimp only at hh
      omega
    have := balance B x
    have hC := balance C x
    omega

/--
**Fayers–Vandehey containment theorem for simultaneous cores.** Call a Young diagram an
$s$-core when none of its cells has hook length divisible by $s$. For all coprime positive
integers $s$ and $t$, if $\kappa$ is a Young diagram that is both an $s$-core and a $t$-core and
has at least as many cells as every Young diagram that is both an $s$-core and a $t$-core, then
every Young diagram that is both an $s$-core and a $t$-core is contained in $\kappa$ (each of its
cells is a cell of $\kappa$).

Fayers (Theorem 5.1, first proved by Vandehey) shows that for coprime positive integers $s$ and
$t$ every simultaneous $s$- and $t$-core is contained in $\kappa_{s,t}$, the simultaneous core of
the largest size $(s^2 - 1)(t^2 - 1)/24$, answering the question of Olsson and Stanton. A
simultaneous core $\kappa$ of maximum size is then contained in $\kappa_{s,t}$ and has at least as
many cells, so it equals $\kappa_{s,t}$ and contains every simultaneous core.

Source: J. B. Olsson (joint with D. Stanton, C. Bessenrodt, G. Navarro, P. H.
Tiep), On block identities and block inclusions, in Representations of Finite Groups, Oberwolfach
Reports 3 (2006), no. 15, p. 912 ff., section 2 (Block identities), DOI 10.4171/OWR/2006/15;
resolution: M. Fayers, The t-core of an s-core, J. Combin. Theory Ser. A 118 (2011), 1525-1539, DOI
10.1016/j.jcta.2011.01.004, arXiv:1007.1071, Section 5, Theorem 5.1 ("Suppose s and t are coprime
positive integers, and λ is an (s, t)-core. Then [λ] ⊆ [κ_{s,t}]"), proved in Proposition 5.5,
https://arxiv.org/abs/1007.1071; Fayers cites the first proof as J. Vandehey, Containment in
(s, t)-core partitions, arXiv:0809.2134, Theorem 2.4, https://arxiv.org/abs/0809.2134.
-/
theorem simultaneousCoreContainment_holds : simultaneousCoreContainment := by
  intro s t hs _ hc κ hκs hκt hmax μ hμs hμt
  let a := max (κ.colLen 0) (μ.colLen 0)
  obtain ⟨C, Q, ha, hCs, hCt, hQ⟩ := canonical hs hc a
  obtain ⟨ν, hν, he⟩ := exists_diagram C
  have contain (η : YoungDiagram) (hn : η.colLen 0 ≤ C.card)
      (h₁ : IsCore s η) (h₂ : IsCore t η) : η ≤ ν := by
    obtain ⟨P, hp⟩ := exists_runners hs _ ((core_iff_closed η hn s).mp h₁)
    apply le_of_above hn
    intro x
    rw [he]
    exact compare hs hc (card_beads _ _) P Q hp ((core_iff_closed η hn t).mp h₂) a hQ x
  have hκ := contain κ ((le_max_left _ _).trans ha) hκs hκt
  have hνs := (core_iff_closed ν hν s).mpr (he.symm ▸ hCs)
  have hνt := (core_iff_closed ν hν t).mpr (he.symm ▸ hCt)
  have heq : κ = ν := YoungDiagram.ext (eq_of_subset_of_card_le hκ (hmax ν hνs hνt))
  exact heq ▸ contain μ ((le_max_right _ _).trans ha) hμs hμt

end MathlibExt.Combinatorics.SimultaneousCoreContainmentOWR1265Problem006Wanted
