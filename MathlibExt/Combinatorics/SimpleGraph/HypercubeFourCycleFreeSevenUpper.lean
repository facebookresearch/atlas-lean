/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/HypercubeC4/README.md` (leansolving/SqueezeBench):
Copyright the SqueezeBench contributors.
Authors: P. Manrique, H. Xia, S. Szeider.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The theorem statement uses the seven-cube upper bound from the “Known values” section at
commit e2e19eef093a77882da57f348def029533ec2d5e.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import MathlibExt.Combinatorics.SimpleGraph.HypercubeExtremal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# An upper bound for four-cycle-free subgraphs of the seven-cube

We prove `hypercubeTuranNumber_seven_cycleGraph_four_le` by counting rooted configurations
of two squares that share an edge. Each such pair belongs to a unique three-dimensional face.
The integer weights below satisfy two finite inequalities, one on a three-cube and one on
the six squares incident to a directed edge.

For a root edge with indicator `r` and two square labels `s, t`, assign the score
`32 * r - 22 - weight r s t`. The 24 scores in any square-free three-cube sum to at most
zero. Around any directed edge, the 15 weights for pairs of its six squares also sum to at
most zero. Each rooted pair occurs once in each count, so the proportion of present edges
is at most `22 / 32`. The seven-cube has 448 edges.

The two weight matrices are a finite certificate. Their entries were found by imposing
the two local inequalities as linear constraints and choosing integer weights. The proof
checks all three-cube edge patterns and all multisets of six admissible square labels.
-/

namespace MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted

open _root_.SimpleGraph

-- For a directed edge xy and a second direction, record the two transverse edges
-- (at x and y, respectively), then the edge opposite xy.
private def label (a b c : Bool) : Fin 8 :=
  ⟨4 * a.toNat + 2 * b.toNat + c.toNat, by cases a <;> cases b <;> cases c <;> decide⟩

-- The matrices are indexed by the labels of two squares incident to the same directed edge.
-- The first matrix is for an absent edge and the second is for a present edge.
private def weight : Bool → Fin 8 → Fin 8 → ℤ
  | false =>
    ![![-22, -25, 4, 4, 4, 4, 15, -5],
      ![-25, -20, -15, -9, -15, -9, -12, 4],
      ![4, -15, -36, -27, 4, 4, -13, 1],
      ![4, -9, -27, -22, 4, 4, -13, 1],
      ![4, -15, 4, 4, -36, -27, -13, 1],
      ![4, -9, 4, 4, -27, -22, -13, 1],
      ![15, -12, -13, -13, -13, -13, -27, 2],
      ![-5, 4, 1, 1, 1, 1, 2, -2]]
  | true =>
    ![![-22, -26, -6, -6, -6, -6, 10, 0],
      ![-26, -8, -11, 0, -11, 0, -9, 0],
      ![-6, -11, -16, -15, 10, 10, 0, 0],
      ![-6, 0, -15, -16, 10, 10, 0, 0],
      ![-6, -11, 10, 10, -16, -15, 0, 0],
      ![-6, 0, 10, 10, -15, -16, 0, 0],
      ![10, -9, 0, 0, 0, 0, -10, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]]

private def score (r : Bool) (s t : Fin 8) : ℤ :=
  32 * (r.toNat : ℤ) - 22 - weight r s t

private abbrev Plane := Bool → Bool → Bool

-- In a three-cube the edges in each of the three directions form a two-by-two array.
private def admissible (a b c : Plane) : Prop :=
  (∀ w, !(a false w && a true w && b false w && b true w) = true) ∧
  (∀ v, !(a v false && a v true && c false v && c true v) = true) ∧
  (∀ u, !(b u false && b u true && c u false && c u true) = true)

private instance decidableAdmissible (a b c : Plane) : Decidable (admissible a b c) := by
  unfold admissible
  infer_instance

private def cubeScore (a b c : Plane) (u v w : Bool) : ℤ :=
  score (a v w) (label (b u w) (b (!u) w) (a (!v) w)) (label (c u v) (c (!u) v) (a v (!w))) +
  score (b u w) (label (a v w) (a (!v) w) (b (!u) w)) (label (c u v) (c u (!v)) (b u (!w))) +
  score (c u v) (label (a v w) (a v (!w)) (c (!u) v)) (label (b u w) (b u (!w)) (c u (!v)))

private def planeOfBits (n : Fin 16) (u v : Bool) : Bool :=
  n.val.testBit (2 * u.toNat + v.toNat)

private theorem plane_cover : ∀ a : Plane, ∃ n : Fin 16, a = planeOfBits n := by decide +kernel

set_option maxRecDepth 4000 in
private theorem cube_check_bits : ∀ i j k : Fin 16,
    admissible (planeOfBits i) (planeOfBits j) (planeOfBits k) →
    ∑ u, ∑ v, ∑ w, cubeScore (planeOfBits i) (planeOfBits j) (planeOfBits k) u v w ≤ 0 := by
  simp only [Fintype.sum_bool]
  decide +kernel

private theorem cube_check (a b c : Plane) (hf : admissible a b c) :
    ∑ u, ∑ v, ∑ w, cubeScore a b c u v w ≤ 0 := by
  obtain ⟨i, rfl⟩ := plane_cover a
  obtain ⟨j, rfl⟩ := plane_cover b
  obtain ⟨k, rfl⟩ := plane_cover c
  exact cube_check_bits i j k hf

private def pairSum {α : Type} (f : α → α → ℤ) : List α → ℤ
  | [] => 0
  | x :: xs => (xs.map (f x)).sum + pairSum f xs

private theorem weight_symm : ∀ r s t, weight r s t = weight r t s := by decide +kernel

private theorem pairSum_perm {α : Type} {f : α → α → ℤ} (hf : ∀ s t, f s t = f t s)
    {xs ys : List α} (h : xs.Perm ys) : pairSum f xs = pairSum f ys := by
  induction h with
  | nil => rfl
  | cons x h ih => simp only [pairSum, (h.map _).sum_eq, ih]
  | swap x y l => simp [pairSum, hf x y, add_assoc, add_left_comm]
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

-- Sorting reduces the finite check to unordered multisets of six labels.
private def checkSorted (r : Bool) (hi : Nat) (xs : List (Fin 8)) : Nat → Bool
  | 0 => decide (pairSum (weight r) xs ≤ 0)
  | n + 1 => (List.finRange 8).all fun s =>
    if s.val ≤ hi ∧ (r = true → s.val < 7) then checkSorted r s.val (s :: xs) n else true

set_option maxRecDepth 8000 in
private theorem edge_check : ∀ r, checkSorted r 7 [] 6 = true := by decide +kernel

private theorem checkSorted_sound (r : Bool) (xs : List (Fin 8))
    (hgood : ∀ s ∈ xs, r = true → s.val < 7)
    (hsort : xs.Pairwise (fun a b => b ≤ a)) (hi : ℕ) (hhi : ∀ s ∈ xs, s.val ≤ hi)
    (acc : List (Fin 8)) (hc : checkSorted r hi acc xs.length = true) :
    pairSum (weight r) (xs.reverse ++ acc) ≤ 0 := by
  induction xs generalizing hi acc with
  | nil => simpa [checkSorted] using hc
  | cons s xs ih =>
    have hb := List.all_eq_true.mp hc s (List.mem_finRange _)
    have hs := List.pairwise_cons.mp hsort
    have h := ih (fun t ht => hgood t (.tail _ ht)) hs.2 s.val hs.1 (s :: acc)
      (by rwa [ite_eq_left ⟨hhi s (.head _), hgood s (.head _)⟩] at hb)
    simpa using h

private theorem edge_inequality (r : Bool) (xs : List (Fin 8)) (hn : xs.length = 6)
    (hgood : ∀ s ∈ xs, r = true → s.val < 7) : pairSum (weight r) xs ≤ 0 := by
  let ys := xs.mergeSort (fun a b => decide (b ≤ a))
  have hp : ys.Perm xs := List.mergeSort_perm _ _
  have hs : ys.Pairwise (fun a b => b ≤ a) := by
    simpa [ys] using List.pairwise_mergeSort (le := fun a b : Fin 8 => decide (b ≤ a))
      (by simp only [decide_eq_true_eq]; exact fun _ _ _ h h' => h'.trans h)
      (by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact fun _ _ => le_total _ _) xs
  have h := checkSorted_sound r ys (fun s h => hgood s (hp.mem_iff.mp h)) hs 7
    (fun s _ => by omega) [] (by rw [hp.length_eq, hn]; exact edge_check r)
  simpa [pairSum_perm (weight_symm r) ((List.reverse_perm ys).trans hp)] using h

private abbrev Dir := Fin 7
private abbrev Vertex := Dir → Bool
private abbrev Triple := Dir × Dir × Dir

private def flip (x : Vertex) (i : Dir) : Vertex := fun d => x d ^^ decide (d = i)

private theorem flip_twice (x : Vertex) (i : Dir) : flip (flip x i) i = x := by
  funext d
  simp [flip]

private theorem flip_comm (x : Vertex) (i j : Dir) :
    flip (flip x i) j = flip (flip x j) i := by
  funext d
  by_cases hi : d = i <;> by_cases hj : d = j <;> simp [flip, hi, hj]

private abbrev Edges := Vertex → Dir → Bool

private def squareFree (E : Edges) : Prop :=
  ∀ x i j, i ≠ j → !(E x i && E (flip x j) i && E x j && E (flip x i) j) = true

private def squareLabel (E : Edges) (x : Vertex) (i j : Dir) :=
  label (E x j) (E (flip x i) j) (E (flip x j) i)

private def rootedScore (E : Edges) (x : Vertex) (p : Triple) : ℤ :=
  score (E x p.1) (squareLabel E x p.1 p.2.1) (squareLabel E x p.1 p.2.2)

-- Translation by the chosen three bits runs over a three-dimensional face.
private def shift (x : Vertex) (i j k : Dir) (u v w : Bool) : Vertex := fun d =>
  x d ^^ ((decide (d = i) && u) ^^ (decide (d = j) && v) ^^ (decide (d = k) && w))

private theorem flip_shift₁ (x : Vertex) (i j k : Dir) (u v w : Bool) :
    flip (shift x i j k u v w) i = shift x i j k (!u) v w := by
  funext d
  by_cases h : d = i <;> simp [flip, shift, h]

private theorem flip_shift₂ (x : Vertex) (i j k : Dir) (u v w : Bool) :
    flip (shift x i j k u v w) j = shift x i j k u (!v) w := by
  funext d
  by_cases h : d = j <;> simp [flip, shift, h]

private theorem flip_shift₃ (x : Vertex) (i j k : Dir) (u v w : Bool) :
    flip (shift x i j k u v w) k = shift x i j k u v (!w) := by
  funext d
  by_cases h : d = k <;> simp [flip, shift, h]

private theorem sum_shift (f : Vertex → ℤ) (i j k : Dir) (u v w : Bool) :
    (∑ x : Vertex, f (shift x i j k u v w)) = ∑ x, f x := by
  let e x := shift x i j k u v w
  have h : Function.Involutive e := by intro x; funext d; simp [e, shift]
  exact Equiv.sum_comp h.toPerm f

private theorem cube_at (E : Edges) (hs : ∀ x i, E (flip x i) i = E x i) (hf : squareFree E)
    (x : Vertex) {i j k : Dir} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ u, ∑ v, ∑ w, (rootedScore E (shift x i j k u v w) (i,j,k) +
      rootedScore E (shift x i j k u v w) (j,i,k) +
      rootedScore E (shift x i j k u v w) (k,i,j)) ≤ 0 := by
  let a v w := E (shift x i j k false v w) i
  let b u w := E (shift x i j k u false w) j
  let c u v := E (shift x i j k u v false) k
  have ha (u v w) : E (shift x i j k u v w) i = a v w := by
    cases u with
    | false => rfl
    | true => exact flip_shift₁ x i j k false v w ▸ hs _ i
  have hb (u v w) : E (shift x i j k u v w) j = b u w := by
    cases v with
    | false => rfl
    | true => exact flip_shift₂ x i j k u false w ▸ hs _ j
  have hc (u v w) : E (shift x i j k u v w) k = c u v := by
    cases w with
    | false => rfl
    | true => exact flip_shift₃ x i j k u v false ▸ hs _ k
  have hadm : admissible a b c := by
    refine ⟨fun w => ?_, fun v => ?_, fun u => ?_⟩
    · simpa only [flip_shift₁, flip_shift₂, ha, hb, Bool.not_false] using
        hf (shift x i j k false false w) i j hij
    · simpa only [flip_shift₁, flip_shift₃, ha, hc, Bool.not_false] using
        hf (shift x i j k false v false) i k hik
    · simpa only [flip_shift₂, flip_shift₃, hb, hc, Bool.not_false] using
        hf (shift x i j k u false false) j k hjk
  simpa only [rootedScore, squareLabel, flip_shift₁, flip_shift₂, flip_shift₃, ha, hb, hc,
    cubeScore] using cube_check a b c hadm

private def totalScore (E : Edges) (p : Triple) := ∑ x, rootedScore E x p

private theorem cube_bound (E : Edges) (hs : ∀ x i, E (flip x i) i = E x i) (hf : squareFree E)
    {i j k : Dir} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    totalScore E (i,j,k) + totalScore E (j,i,k) + totalScore E (k,i,j) ≤ 0 := by
  have h := Finset.sum_nonpos (s := Finset.univ)
    (fun x _ => cube_at E hs hf x hij hik hjk)
  have ht (u v w : Bool) (p : Triple) :
      (∑ x, rootedScore E (shift x i j k u v w) p) = ∑ x, rootedScore E x p :=
    sum_shift (fun x => rootedScore E x p) i j k u v w
  simp only [Fintype.sum_bool, Finset.sum_add_distrib, ht] at h
  unfold totalScore
  omega

private def pairs {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (x, ·) ++ pairs xs

private def others (i : Dir) := (List.finRange 7).filter (· != i)

private def fan (i : Dir) : List Triple := (pairs (others i)).map (i, ·)

private def triples : List Triple := (List.finRange 7).flatMap fun i =>
  (pairs (others i)).filterMap fun (j,k) => if i < j then some (i,j,k) else none

private def roots (p : Triple) : List Triple :=
  let (i,j,k) := p
  [(i,j,k), (j,i,k), (k,i,j)]

private theorem distinct_triples : ∀ p ∈ triples,
    p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 := by decide +kernel

-- The 35 direction triples, rooted in each of their three directions, are exactly
-- the 15 pairs of other directions at each of the seven possible roots.
set_option maxRecDepth 4000 in
private theorem regroup : (triples.flatMap roots).Perm ((List.finRange 7).flatMap fan) := by
  decide +kernel

private theorem sum_flat {α β : Type} (xs : List α) (f : α → List β) (g : β → ℤ) :
    ((xs.flatMap f).map g).sum = (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem sum_pairs {α : Type} (xs : List α) (f : α → Fin 8) (r : Bool) :
    ((pairs xs).map (fun (j,k) => weight r (f j) (f k))).sum =
      pairSum (weight r) (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pairs, pairSum, ih, Function.comp_def]

private theorem sum_offset {α : Type} (xs : List α) (a : ℤ) (f : α → ℤ) :
    (xs.map (fun x => a - f x)).sum = xs.length * a - (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_mul]; omega

private theorem fan_bound (E : Edges) (hf : squareFree E) (x : Vertex) (i : Dir) :
    15 * (32 * ((E x i).toNat : ℤ) - 22) ≤ ((fan i).map (rootedScore E x)).sum := by
  have lens : ∀ i, (others i).length = 6 ∧ (pairs (others i)).length = 15 := by decide +kernel
  have hg : ∀ s ∈ (others i).map (squareLabel E x i), E x i = true → s.val < 7 := by
    intro s h hr
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    have hne : i ≠ j := by simpa [others, ne_comm] using (List.mem_filter.mp hj).2
    have h := hf x i j hne
    unfold squareLabel
    cases h₁ : E x j <;> cases h₂ : E (flip x i) j <;> cases h₃ : E (flip x j) i <;>
      first | decide | simp [hr,h₁,h₂,h₃] at h
  have h := edge_inequality (E x i) _ (by simpa using (lens i).1) hg
  rw [← sum_pairs] at h
  simp only [fan, List.map_map, Function.comp_def, rootedScore, score]
  rw [sum_offset, (lens i).2]
  norm_num
  linarith

private theorem total_list (E : Edges) (ts : List Triple) :
    (ts.map (totalScore E)).sum = ∑ x, (ts.map (rootedScore E x)).sum := by
  induction ts with
  | nil => simp
  | cons p ts ih => simp [totalScore, ih, Finset.sum_add_distrib]

private theorem bit_bound (E : Edges) (hs : ∀ x i, E (flip x i) i = E x i) (hf : squareFree E) :
    (∑ x : Vertex, ∑ i : Dir, ((E x i).toNat : ℤ)) ≤ 616 := by
  have ht : ((triples.flatMap roots).map (totalScore E)).sum ≤ 0 := by
    rw [sum_flat]
    apply le_trans (List.sum_le_sum (g := fun _ => (0 : ℤ)) ?_) (by simp)
    rintro ⟨i,j,k⟩ hp
    obtain ⟨hij,hik,hjk⟩ := distinct_triples _ hp
    simpa [roots, add_assoc] using cube_bound E hs hf hij hik hjk
  rw [(regroup.map _).sum_eq, total_list] at ht
  have hx (x : Vertex) : (∑ i, 15 * (32 * ((E x i).toNat : ℤ) - 22)) ≤
      (((List.finRange 7).flatMap fan).map (rootedScore E x)).sum := by
    rw [sum_flat, ← List.sum_ofFn, List.ofFn_eq_map]
    exact List.sum_le_sum fun i _ => fan_bound E hf x i
  have h := (Finset.sum_le_sum (s := Finset.univ) (fun x _ => hx x)).trans ht
  have hn : Fintype.card Vertex = 128 := by simp [Vertex, Dir, Fintype.card_pi]
  simp only [mul_sub, ← mul_assoc, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, hn, nsmul_eq_mul] at h
  omega

private noncomputable def retained (S : (hypercubeGraph 7).Subgraph) (x : Vertex) (i : Dir) :
    Bool := by
  classical
  exact decide (S.Adj x (flip x i))

private theorem retained_iff (S : (hypercubeGraph 7).Subgraph) (x : Vertex) (i : Dir) :
    retained S x i = true ↔ S.Adj x (flip x i) := by
  classical
  simp [retained]

private theorem retained_symm (S : (hypercubeGraph 7).Subgraph) (x : Vertex) (i : Dir) :
    retained S (flip x i) i = retained S x i := by
  apply Bool.eq_iff_iff.mpr
  rw [retained_iff, retained_iff, flip_twice]
  exact S.adj_comm _ _

private theorem square_copy {V : Type} {G : _root_.SimpleGraph V} (a b c d : V)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : (cycleGraph 4) ⊑ G := by
  let f : Fin 4 → V := [a,b,c,d].get
  have hrel : ∀ {p q}, (cycleGraph 4).Adj p q → G.Adj (f p) (f q) := by
    intro p q h
    fin_cases p <;> fin_cases q <;> first
      | exact False.elim ((by decide : ¬ _) h)
      | assumption
      | exact hab.symm
      | exact hbc.symm
      | exact hcd.symm
      | exact hda.symm
  have hd : [a,b,c,d].Nodup := by simp [hab.ne,hac,hda.ne',hbc.ne,hbd,hcd.ne]
  exact ⟨⟨⟨f, hrel⟩, List.nodup_iff_injective_get.mp hd⟩⟩

private theorem retained_free (S : (hypercubeGraph 7).Subgraph) (hf : (cycleGraph 4).Free S.coe) :
    squareFree (retained S) := by
  intro x i j hij
  have missing : ∀ a b c d : Bool, (a = true → b = true → c = true → d = true → False) →
      !(a && b && c && d) = true := by decide
  apply missing
  intro ha hb hc hd
  simp only [retained_iff] at ha hb hc hd
  rw [flip_comm x j i] at hb
  apply hf
  let a : S.verts := ⟨x, S.edge_vert ha⟩
  let b : S.verts := ⟨flip x i, S.edge_vert hd⟩
  let c : S.verts := ⟨flip (flip x i) j, S.edge_vert hd.symm⟩
  let d : S.verts := ⟨flip x j, S.edge_vert hb⟩
  apply square_copy (G := S.coe) a b c d ha hd hb.symm hc.symm
  · intro he
    have hh := congrArg (fun z : S.verts => z.val i) he
    simp [a,c,flip,hij] at hh
  · intro he
    have hh := congrArg (fun z : S.verts => z.val i) he
    simp [b,d,flip,hij] at hh

open scoped Classical in
private theorem sum_retained (S : (hypercubeGraph 7).Subgraph) (x : Vertex) :
    (∑ i, (retained S x i).toNat) = S.spanningCoe.degree x := by
  classical
  let dirs := Finset.univ.filter fun i => S.Adj x (flip x i)
  have hdirs : dirs.card = ∑ i, (retained S x i).toNat := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : S.Adj x (flip x i) <;> simp [retained,h]
  have himg : dirs.image (flip x) = S.spanningCoe.neighborFinset x := by
    ext y
    rw [mem_neighborFinset]
    constructor
    · rintro hy
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hi).2
    · intro hy
      obtain ⟨i,hi,huniq⟩ := (hypercubeGraph_adj _ _ _).mp (S.adj_sub hy)
      have he : flip x i = y := by
        funext j
        by_cases hj : j = i
        · subst j
          simpa [flip] using (Bool.eq_not_of_ne hi.symm).symm
        · have heq : x j = y j := by
            by_contra h
            exact hj (huniq j h)
          simp [flip,hj,heq]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he ▸ hy⟩, he⟩
  have hinj : Function.Injective (flip x) := by
    intro i j h
    by_contra hij
    have hh := congrFun h i
    simp [flip,hij] at hh
  rw [← hdirs, ← card_neighborFinset_eq_degree, ← himg, Finset.card_image_of_injective _ hinj]

private theorem subgraph_bound (S : (hypercubeGraph 7).Subgraph)
    (hf : (cycleGraph 4).Free S.coe) : S.edgeSet.ncard ≤ 308 := by
  classical
  have h := bit_bound (retained S) (retained_symm S) (retained_free S hf)
  have hnat : (∑ x, ∑ i, (retained S x i).toNat) ≤ 616 := by exact_mod_cast h
  simp_rw [sum_retained, S.spanningCoe.sum_degrees_eq_twice_card_edges] at hnat
  have he : S.edgeSet.ncard = S.spanningCoe.edgeFinset.card := by
    rw [← S.edgeSet_spanningCoe, Set.ncard_eq_toFinset_card']
    rfl
  omega

/-- **Upper bound for four-cycle-free subgraphs of the seven-dimensional hypercube.** Let $Q_7$
be the $7$-dimensional hypercube and $C_4$ the cycle on four vertices. The largest number
$\mathrm{ex}(Q_7, C_4)$ of edges of a subgraph of $Q_7$ that contains no copy of $C_4$ is at
most $308$.

The bound comes from averaging over the fourteen facets of $Q_7$: each is a copy of $Q_6$ and
each edge lies in six of them, so $\mathrm{ex}(Q_7, C_4) \le 14 \cdot \mathrm{ex}(Q_6, C_4) / 6 =
14 \cdot 132 / 6 = 308$.

Source: the averaging bound applied to `ex(Q₆, C₄) = 132` (Harborth and
Nienborg 1994), as stated in SqueezeBench
`SqueezeBench/Problems/HypercubeC4/README.md`. -/
public theorem hypercubeTuranNumber_seven_cycleGraph_four_le :
    hypercubeTuranNumber 7 (cycleGraph 4) ≤ 308 := by
  classical
  apply Finset.sup_le
  intro m hm
  obtain ⟨S,hS,rfl⟩ := (Finset.mem_filter.mp hm).2
  exact subgraph_bound S hS

end MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted
