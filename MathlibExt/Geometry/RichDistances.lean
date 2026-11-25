/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/756.lean` (the definitions and problem statement):
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
-/
module

public import MathlibExt.Geometry.Metric
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bhowmick's theorem on rich distances

Gluing regular polygons along vertices and edges gives the lower bounds on the number
of rich distances in `conjecture_holds`.
-/

@[expose] public section

open Filter
open scoped Asymptotics

namespace MathlibExt.Geometry.ErdosProblem756Wanted

/-- **Rich distances.** For a finite set $A$ of points in the Euclidean plane and a natural number
$k$, the rich distances of $A$ at level $k$ are the distances $d$ between two distinct points of
$A$ such that at least $k$ unordered pairs of distinct points of $A$ are at distance $d$. -/
noncomputable def richDistances (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (k : ℕ) : Finset ℝ :=
  (distanceSet A).filter fun d => k ≤ distanceMultiplicity A d

/-- **Maximal number of rich distances.** For a natural number $n$, this is the largest, over all
sets $A$ of $n$ points in the Euclidean plane, of the number of rich distances of $A$ at level
$n + 1$, that is, of distances that occur for at least $n + 1$ unordered pairs of distinct points
of $A$. -/
noncomputable def maxRichDistances (n : ℕ) : ℕ :=
  sSup {(richDistances A (n + 1)).card | (A : Finset (EuclideanSpace ℝ (Fin 2))) (_ : A.card = n)}

/-- **Statement of Erdős Problem 756 on rich distances.** For a finite set $A$ of points in the
Euclidean plane, call a distance $k$-rich for $A$ if at least $k$ unordered pairs of distinct points
of $A$ lie at that distance, and let $f(n)$ be the largest number of $(n+1)$-rich distances of a
set of $n$ points. This is the assertion that there is a constant $C$ with $n \le C f(n)$ for all
sufficiently large $n$; that for every $n$ there is a set of $n$ points with at least
$\lfloor n/4 \rfloor$ distances that are $(n+1)$-rich; and that for every $m \ge 1$ there is an
$N$ such that for every $n \ge N$ there is a set of $n$ points with at least
$\lfloor n/(2(m+1)) \rfloor$ distances that are $(n+m)$-rich. -/
def conjecture : Prop :=
  ((fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (maxRichDistances n : ℝ))) ∧
  (∀ n : ℕ, ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.card = n ∧ n / 4 ≤ (richDistances A (n + 1)).card) ∧
  (∀ m : ℕ, 1 ≤ m → ∀ᶠ n : ℕ in atTop, ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.card = n ∧ n / (2 * (m + 1)) ≤ (richDistances A (n + m)).card)

open scoped ComplexConjugate
open Finset

private noncomputable def pairs {X : Type*} [MetricSpace X] (A : Finset X) (d : ℝ) :=
  A.offDiag.filter fun p => dist p.1 p.2 = d

private lemma mem_pairs {X : Type*} [MetricSpace X] {A : Finset X} {d : ℝ} {x y : X} :
    (x, y) ∈ pairs A d ↔ x ∈ A ∧ y ∈ A ∧ x ≠ y ∧ dist x y = d := by
  simp [pairs, and_assoc]

private lemma pairs_mono {X : Type*} [MetricSpace X] {A B : Finset X} (h : A ⊆ B) (d : ℝ) :
    pairs A d ⊆ pairs B d := filter_subset_filter _ (offDiag_mono h)

private lemma pairs_isometry {X Y : Type*} [MetricSpace X] [MetricSpace Y] [DecidableEq Y]
    {f : X → Y} (hf : Isometry f) (A : Finset X) (d : ℝ) :
    (pairs A d).card ≤ (pairs (A.image f) d).card := by
  classical
  apply card_le_card_of_injOn (Prod.map f f)
  · rintro ⟨x, y⟩ hp
    obtain ⟨hx, hy, hne, hd⟩ := mem_pairs.mp hp
    exact mem_pairs.mpr ⟨mem_image_of_mem _ hx, mem_image_of_mem _ hy,
      hf.injective.ne hne, (hf.dist_eq _ _).trans hd⟩
  · exact (hf.injective.prodMap hf.injective).injOn

-- Two unit vectors with a prescribed nonzero sum are unique up to interchange.
private lemma chord_ends {a b x y : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hs : x + y = a + b) (hn : a + b ≠ 0) :
    x = a ∨ x = b := by
  have hc := congrArg (fun z : ℂ => conj z) hs
  simp only [map_add, ← Complex.inv_eq_conj ha, ← Complex.inv_eq_conj hb,
    ← Complex.inv_eq_conj hx, ← Complex.inv_eq_conj hy] at hc
  have nz (z : ℂ) (h : ‖z‖ = 1) : z ≠ 0 := by rintro rfl; simp at h
  field_simp [nz _ ha, nz _ hb, nz _ hx, nz _ hy] at hc
  have hp : (a + b) * (a * b - x * y) = 0 := by linear_combination hc - a * b * hs
  have hprod := (mul_eq_zero.mp hp).resolve_left hn
  have : (x - a) * (x - b) = 0 := by linear_combination x * hs + hprod
  simpa [sub_eq_zero] using mul_eq_zero.mp this

private noncomputable def vertices (q : ℕ) (u : ℂ) : Finset ℂ :=
  (range q).image (u ^ ·)

private noncomputable def lengths (q : ℕ) (u : ℂ) : Finset ℝ :=
  (range ((q - 1) / 2)).image fun i => dist 1 (u ^ (i + 1))

private lemma vertex_norm {q : ℕ} {u x : ℂ} (hu : ‖u‖ = 1) (hx : x ∈ vertices q u) :
    ‖x‖ = 1 := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hx
  simp [norm_pow, hu]

private lemma vertex_pow {q : ℕ} {u : ℂ} (hq : 0 < q) (hu : IsPrimitiveRoot u q) (i : ℕ) :
    u ^ i ∈ vertices q u := by
  apply mem_image.mpr
  exact ⟨i % q, mem_range.mpr (Nat.mod_lt _ hq), by rw [hu.eq_orderOf, pow_mod_orderOf]⟩

private lemma vertices_card {q : ℕ} {u : ℂ} (hu : IsPrimitiveRoot u q) :
    (vertices q u).card = q := by
  rw [vertices, card_image_of_injOn, card_range]
  exact fun _ hi _ hj h => hu.pow_inj (mem_range.mp hi) (mem_range.mp hj) h

-- Chords from 1 to the first half of the polygon have different lengths. Equal lengths
-- force the endpoints to coincide or to be complex conjugates.
private lemma lengths_card {q : ℕ} {u : ℂ} (hq : 0 < q) (hu : IsPrimitiveRoot u q) :
    (lengths q u).card = (q - 1) / 2 := by
  classical
  rw [lengths, card_image_of_injOn, card_range]
  intro i hi j hj h
  change dist 1 (u ^ (i + 1)) = dist 1 (u ^ (j + 1)) at h
  replace hi := mem_range.mp hi
  replace hj := mem_range.mp hj
  let x := u ^ (i + 1)
  let y := u ^ (j + 1)
  have hx : ‖x‖ = 1 := by simp [x, norm_pow, hu.norm'_eq_one hq.ne']
  have hy : ‖y‖ = 1 := by simp [y, norm_pow, hu.norm'_eq_one hq.ne']
  change dist 1 x = dist 1 y at h
  rw [dist_eq_norm, dist_eq_norm] at h
  have hs := congrArg (· ^ 2) h
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im] at hs
  have hn (z : ℂ) (hz : ‖z‖ = 1) : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz, one_pow]
  have hr : x.re = y.re := by nlinarith [hn x hx, hn y hy]
  have him : x.im = y.im ∨ x.im = -y.im := by
    apply eq_or_eq_neg_of_sq_eq_sq
    nlinarith [hn x hx, hn y hy, congrArg (· ^ 2) hr]
  rcases him with he | he
  · have e : x = y := Complex.ext hr he
    have := hu.pow_inj (i := i + 1) (j := j + 1) (by omega) (by omega) e
    omega
  · have e : x = conj y := Complex.ext hr he
    have hp : u ^ (i + 1 + (j + 1)) = 1 := by
      rw [pow_add]; change x * y = 1
      rw [e, ← Complex.inv_eq_conj hy, inv_mul_cancel₀]
      intro h0; simp [h0] at hy
    have hd := Nat.le_of_dvd (by omega : 0 < i + 1 + (j + 1)) ((hu.pow_eq_one_iff_dvd _).mp hp)
    omega

-- Multiplication by a fixed root steps around the polygon. Its directed edges and their
-- reversals are disjoint because the step is shorter than half a turn.
private lemma polygon_pairs {q : ℕ} {u : ℂ} (hq : 0 < q) (hu : IsPrimitiveRoot u q)
    {d : ℝ} (hd : d ∈ lengths q u) : 2 * q ≤ (pairs (vertices q u) d).card := by
  classical
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hd
  replace hi := mem_range.mp hi
  let w := u ^ (i + 1)
  have hw : w ≠ 1 := by
    intro h
    have := Nat.le_of_dvd (by omega : 0 < i + 1) ((hu.pow_eq_one_iff_dvd _).mp h)
    omega
  have hw₂ : w * w ≠ 1 := by
    change u ^ (i + 1) * u ^ (i + 1) ≠ 1
    rw [← pow_add]
    intro h
    have := Nat.le_of_dvd (by omega : 0 < i + 1 + (i + 1)) ((hu.pow_eq_one_iff_dvd _).mp h)
    omega
  let V := vertices q u
  let f (x : ℂ) := (x, x * w)
  let g (x : ℂ) := (x * w, x)
  have hxu {x : ℂ} (hx : x ∈ V) := vertex_norm (hu.norm'_eq_one hq.ne') hx
  have hn {x : ℂ} (hx : x ∈ V) : x ≠ 0 := by
    intro h; simpa [h] using hxu hx
  have hd (x : ℂ) (hx : x ∈ V) : (x, x * w) ∈ pairs V (dist 1 w) := by
    apply mem_pairs.mpr
    refine ⟨hx, ?_, ?_, ?_⟩
    · obtain ⟨j, _, rfl⟩ := mem_image.mp hx
      exact pow_add u j (i + 1) ▸ vertex_pow hq hu (j + (i + 1))
    · intro h
      exact hw (mul_left_cancel₀ (hn hx) (h.symm.trans (mul_one x).symm))
    · rw [dist_eq_norm, dist_eq_norm, show x - x * w = x * (1 - w) by ring,
        norm_mul, hxu hx, one_mul]
  have hsub : V.image f ∪ V.image g ⊆ pairs V (dist 1 w) := by
    apply union_subset
    · exact image_subset_iff.mpr hd
    · apply image_subset_iff.mpr
      intro x hx
      obtain ⟨h₁, h₂, h₃, h₄⟩ := mem_pairs.mp (hd x hx)
      exact mem_pairs.mpr ⟨h₂, h₁, h₃.symm, (dist_comm ..).trans h₄⟩
  have dis : Disjoint (V.image f) (V.image g) := by
    rw [disjoint_left]
    intro _ h₁ h₂
    obtain ⟨x, hx, rfl⟩ := mem_image.mp h₁
    obtain ⟨y, _, he⟩ := mem_image.mp h₂
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
    change y * w = x at h₁
    change y = x * w at h₂
    rw [h₂, mul_assoc] at h₁
    exact hw₂ (mul_left_cancel₀ (hn hx) (h₁.trans (mul_one x).symm))
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint dis,
    card_image_of_injective _ (f := f) (fun _ _ h => congrArg Prod.fst h),
    card_image_of_injective _ (f := g) (fun _ _ h => congrArg Prod.snd h),
    vertices_card hu] at hcard
  simpa [two_mul] using hcard

-- A half-turn about the midpoint of a common chord glues two congruent polygons.
private lemma glue {A V : Finset ℂ} (hV : V ⊆ A) {a b : ℂ} (ha : a ∈ V) (hb : b ∈ V)
    (unit : ∀ x ∈ V, ‖x‖ = 1) (hne : a + b ≠ 0)
    (apart : ∀ x ∈ A, x ∉ V → a + b - x ∉ V) :
    let B := A.image (fun x => a + b - x)
    (V ∪ B).card + ({a, b} : Finset ℂ).card = A.card + V.card ∧
    ∀ d, (pairs V d).card + (pairs A d).card ≤
      (pairs (V ∪ B) d).card + ({a, b} : Finset ℂ).offDiag.card := by
  classical
  let f (x : ℂ) := a + b - x
  have iso : Isometry f := Isometry.of_dist_eq fun x y => by
    simpa [f, dist_eq_norm] using norm_sub_rev y x
  let B := A.image f
  have inter : V ∩ B = {a, b} := by
    ext x
    simp only [mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hx, hx'⟩
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx'
      have hyV : y ∈ V := by by_contra h; exact apart y hy h hx
      exact chord_ends (unit a ha) (unit b hb) (unit _ hx) (unit _ hyV)
        (by simp [f]) hne
    · rintro (rfl | rfl)
      · exact ⟨ha, mem_image.mpr ⟨b, hV hb, by simp [f]⟩⟩
      · exact ⟨hb, mem_image.mpr ⟨a, hV ha, by simp [f]⟩⟩
  constructor
  · simpa [← inter, B, card_image_of_injective _ iso.injective, add_comm] using
      card_union_add_card_inter V B
  · intro d
    have h₁ : pairs V d ∪ pairs B d ⊆ pairs (V ∪ B) d :=
      union_subset (pairs_mono subset_union_left _) (pairs_mono subset_union_right _)
    have h₂ : pairs V d ∩ pairs B d ⊆ (V ∩ B).offDiag := by
      rintro ⟨x, y⟩ hp
      obtain ⟨h₁, h₂⟩ := mem_inter.mp hp
      obtain ⟨hx, hy, hxy, _⟩ := mem_pairs.mp h₁
      obtain ⟨hx', hy', _⟩ := mem_pairs.mp h₂
      exact mem_offDiag.mpr ⟨mem_inter.mpr ⟨hx, hx'⟩, mem_inter.mpr ⟨hy, hy'⟩, hxy⟩
    rw [inter] at h₂
    have h := card_union_add_card_inter (pairs V d) (pairs B d)
    have hi : (pairs A d).card ≤ (pairs B d).card := pairs_isometry iso A d
    exact (Nat.add_le_add_left hi _).trans (h ▸ Nat.add_le_add (card_le_card h₁) (card_le_card h₂))

private noncomputable def root (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)

private lemma root_re (q i : ℕ) :
    ((root q) ^ i).re = Real.cos (2 * Real.pi * i / q) := by
  rw [root, ← Complex.exp_nat_mul,
    show (i : ℂ) * (2 * Real.pi * Complex.I / q) =
      ((2 * Real.pi * i / q : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

-- For a long chain we need two possible gluing vertices on each side of the centre.
private lemma caps {q : ℕ} (hq : 12 ≤ q) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    ∃ a ∈ vertices q (root q), ∃ b ∈ vertices q (root q),
      a ≠ b ∧ 1 / 2 < s * a.re ∧ 1 / 2 < s * b.re := by
  have hpos : 0 < q := by omega
  have hu := Complex.isPrimitiveRoot_exp q hpos.ne'
  change IsPrimitiveRoot (root q) q at hu
  have memb := vertex_pow hpos hu
  have hqR : 0 < (q : ℝ) := by positivity
  have hr (i j : ℕ) (hi : i < q) (hj : j < q) (hn : i ≠ j) :
      (root q) ^ i ≠ (root q) ^ j := fun h => hn (hu.pow_inj hi hj h)
  rcases hs with rfl | rfl
  · refine ⟨_, memb 0, _, memb 1, hr _ _ (by omega) (by omega) (by decide), ?_, ?_⟩
    · norm_num
    · rw [one_mul, root_re, ← Real.cos_pi_div_three]
      apply Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
      rw [div_lt_iff₀ hqR]
      have h : (6 : ℝ) < q := by exact_mod_cast (by omega : 6 < q)
      nlinarith [mul_pos (sub_pos.mpr h) Real.pi_pos]
  · have bound (i : ℕ) (hi : q < 3 * i) (hj : 2 * i ≤ q) :
        1 / 2 < -1 * ((root q) ^ i).re := by
      rw [root_re, neg_one_mul]
      suffices h : Real.cos (2 * Real.pi * i / q) < -(1 / 2) by linarith
      rw [← Real.cos_pi_div_three, ← Real.cos_pi_sub]
      apply Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
      · apply (div_le_iff₀ hqR).mpr
        have h : 2 * (i : ℝ) ≤ q := by exact_mod_cast hj
        nlinarith [mul_nonneg (sub_nonneg.mpr h) Real.pi_pos.le]
      · apply (lt_div_iff₀ hqR).mpr
        have h : (q : ℝ) < 3 * i := by exact_mod_cast hi
        nlinarith [mul_pos (sub_pos.mpr h) Real.pi_pos]
    refine ⟨_, memb (q / 2), _, memb (q / 2 - 1), hr _ _ (by omega) (by omega) (by omega),
      bound _ (by omega) (by omega), bound _ (by omega) (by omega)⟩

private lemma signed_re_le {x : ℂ} (hx : ‖x‖ = 1) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    s * x.re ≤ 1 := by
  have h := Complex.abs_re_le_norm x
  rw [hx, abs_le] at h
  rcases hs with rfl | rfl <;> linarith

-- Glue m + 1 polygons, using t shared edges and m - t shared vertices. Each attachment
-- increases the multiplicity minus the vertex count by at least one. In the coordinates
-- of the last polygon, the sign s records which side contains all earlier vertices.
private lemma chain {q : ℕ} (hq : 12 ≤ q) (m t : ℕ) (ht : t ≤ m)
    {s : ℝ} (hs : s = 1 ∨ s = -1) :
    let V := vertices q (root q)
    ∃ A : Finset ℂ, V ⊆ A ∧ (∀ x ∈ A, x ∉ V → 0 < s * x.re) ∧
      A.card + m + t = (m + 1) * q ∧
      ∀ d ∈ lengths q (root q), 2 * (A.card + m) ≤ (pairs A d).card := by
  classical
  let V := vertices q (root q)
  have hpos : 0 < q := by omega
  have hu : IsPrimitiveRoot (root q) q := Complex.isPrimitiveRoot_exp q hpos.ne'
  have unit (x : ℂ) (hx : x ∈ V) := vertex_norm (hu.norm'_eq_one hpos.ne') hx
  have hc : V.card = q := vertices_card hu
  induction m generalizing t s with
  | zero =>
    have : t = 0 := by omega
    exact ⟨V, Subset.rfl, fun x hx h => (h hx).elim, by simp [this, hc], by
      simpa [hc] using fun d => @polygon_pairs q _ hpos hu d⟩
  | succ m ih =>
    let k := t - min t m
    have hk : k = 0 ∨ k = 1 := by dsimp [k]; omega
    have hsum : t = min t m + k := by dsimp [k]; omega
    have hs' : -s = 1 ∨ -s = -1 := by rcases hs with rfl | rfl <;> norm_num
    obtain ⟨A, hVA, side, hcard, hcount⟩ := ih (min t m) (min_le_right ..) hs'
    obtain ⟨a, ha, b', hb', hne, hra, hrb'⟩ := caps hq hs
    let b := if k = 0 then a else b'
    have hb : b ∈ V := by dsimp [b]; split <;> assumption
    have hrb : 1 / 2 < s * b.re := by dsimp [b]; split <;> assumption
    have hr : 1 < s * (a + b).re := by rw [Complex.add_re, mul_add]; linarith
    have nz : a + b ≠ 0 := by intro h; norm_num [h] at hr
    have apart (x : ℂ) (hx : x ∈ A) (hn : x ∉ V) (hy : a + b - x ∈ V) : False := by
      have h := signed_re_le (unit _ hy) hs
      rw [Complex.sub_re, mul_sub] at h
      linarith [side x hx hn]
    let B := A.image (fun x => a + b - x)
    obtain ⟨hsize, hpairs⟩ := glue hVA ha hb unit nz apart
    have hc₂ : ({a, b} : Finset ℂ).card = 1 + k := by
      rcases hk with h | h <;> simp [b, h, hne]
    have hdiag : ({a, b} : Finset ℂ).offDiag.card = 2 * k := by
      rw [offDiag_card, hc₂]; rcases hk with h | h <;> simp [h]
    refine ⟨V ∪ B, subset_union_left, ?_, ?_, ?_⟩
    · intro x hx hn
      obtain ⟨y, hy, rfl⟩ := mem_image.mp ((mem_union.mp hx).resolve_left hn)
      have hy' : s * y.re ≤ 1 := by
        by_cases h : y ∈ V
        · exact signed_re_le (unit y h) hs
        · linarith [side y hy h]
      rw [Complex.sub_re, mul_sub]; linarith
    · change (V ∪ B).card + _ = A.card + V.card at hsize
      rw [hc₂, hc] at hsize
      rw [Nat.add_mul (m + 1) 1 q, one_mul]
      omega
    · intro d hd
      have h := hpairs d
      change (pairs V d).card + (pairs A d).card ≤ (pairs (V ∪ B) d).card + _ at h
      change (V ∪ B).card + _ = A.card + V.card at hsize
      rw [hc₂, hc] at hsize
      rw [hdiag] at h
      have hp : 2 * q ≤ (pairs V d).card := polygon_pairs hpos hu hd
      have := hcount d hd
      omega

-- Transfer the polygon counts to the Euclidean plane and forget the ordering of each pair.
private lemma plane_witness {q n m : ℕ} {u : ℂ} (hq : 0 < q) (hu : IsPrimitiveRoot u q)
    (A : Finset ℂ) (hcard : A.card = n) (hn : 0 < n + m)
    (hc : ∀ d ∈ lengths q u, 2 * (n + m) ≤ (pairs A d).card) :
    ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧
      (q - 1) / 2 ≤ (richDistances P (n + m)).card := by
  classical
  let e := Complex.orthonormalBasisOneI.repr
  let P := A.image e
  refine ⟨P, (card_image_of_injective _ e.injective).trans hcard, ?_⟩
  rw [← lengths_card hq hu]
  apply card_le_card
  intro d hd
  have h := (hc d hd).trans (pairs_isometry e.isometry A d)
  change 2 * (n + m) ≤ (pairs P d).card at h
  obtain ⟨⟨x, y⟩, hp⟩ := card_pos.mp (by omega : 0 < (pairs P d).card)
  obtain ⟨hoff, hdist⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_image.mpr ⟨(x, y), hoff, hdist⟩, by
    change n + m ≤ (pairs P d).card / 2
    omega⟩

private lemma all_sizes (n : ℕ) : ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧
    n / 4 ≤ (richDistances P (n + 1)).card := by
  classical
  by_cases small : n < 4
  · obtain ⟨P, hp⟩ := exists_card_eq (α := EuclideanSpace ℝ (Fin 2)) n
    exact ⟨P, hp, by omega⟩
  let q := n / 2 + 1
  have hq : 2 < q := by dsimp [q]; omega
  have hpos : 0 < q := by omega
  let u := root q
  have hu : IsPrimitiveRoot u q := Complex.isPrimitiveRoot_exp q hpos.ne'
  let V := vertices q u
  have h₁ : 1 ∈ V := by simpa using vertex_pow hpos hu 0
  have h₂ : u ∈ V := by simpa using vertex_pow hpos hu 1
  have hne : 1 ≠ u := by
    intro h
    have hpow : u ^ 0 = u ^ 1 := by simpa using h
    have := hu.pow_inj (by omega) (by omega) hpow
    omega
  let b := if n % 2 = 0 then u else 1
  have hb : b ∈ V := by dsimp [b]; split <;> assumption
  have hnz : 1 + b ≠ 0 := by
    dsimp [b]; split
    · intro h
      have hm : u = -1 := by linear_combination h
      have hpow : u ^ 0 = u ^ 2 := by simp [hm]
      have := hu.pow_inj (by omega) (by omega) hpow
      omega
    · norm_num
  let P := V ∪ V.image (fun x => 1 + b - x)
  obtain ⟨hs, hc⟩ := glue (A := V) Subset.rfl h₁ hb
    (fun _ => vertex_norm (hu.norm'_eq_one hpos.ne')) hnz (fun _ h h' => (h' h).elim)
  change P.card + _ = V.card + V.card at hs
  have hsize : ({1, b} : Finset ℂ).card + n % 2 = 2 := by
    by_cases h : n % 2 = 0 <;> simp [b, h, hne]; omega
  have hdiag : ({1, b} : Finset ℂ).offDiag.card + 2 * (n % 2) = 2 := by
    by_cases h : n % 2 = 0 <;> simp [offDiag_card, b, h, hne]; omega
  have hv : V.card = q := vertices_card hu
  have hP : P.card = n := by dsimp [q] at hv; omega
  obtain ⟨S, hs', hd⟩ := plane_witness (m := 1) hpos hu P hP (by omega) (by
    intro d hd
    have h := hc d
    change (pairs V d).card + (pairs V d).card ≤ (pairs P d).card + _ at h
    have hp : 2 * q ≤ (pairs V d).card := polygon_pairs hpos hu hd
    dsimp [q] at hp
    omega)
  exact ⟨S, hs', by dsimp [q] at hd; omega⟩

private lemma many_sizes (m : ℕ) (hm : 1 ≤ m) :
    ∀ᶠ n : ℕ in atTop, ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧
      n / (2 * (m + 1)) ≤ (richDistances P (n + m)).card := by
  filter_upwards [eventually_ge_atTop (12 * (m + 1) + 2)] with n hn
  -- Divide n - 2 by the number of copies to choose the polygon size and the overlaps.
  let p := m + 1
  let k := (n - 2) / p
  let r := (n - 2) % p
  let q := k + 2
  have hp : 0 < p := Nat.succ_pos _
  have hr : r < p := Nat.mod_lt _ hp
  have hdiv : r + p * k = n - 2 := Nat.mod_add_div _ _
  have hk : 12 ≤ k := (Nat.le_div_iff_mul_le hp).mpr (by dsimp [p]; omega)
  have hq : 12 ≤ q := by dsimp [q]; omega
  obtain ⟨A, _, _, hs, hc⟩ := chain hq m (m - r) (by omega) (s := 1) (Or.inl rfl)
  change A.card + m + (m - r) = p * (k + 2) at hs
  rw [Nat.mul_add] at hs
  have hr' : r ≤ m := by dsimp [p] at hr; omega
  have hA : A.card = n := by dsimp [p] at hs hdiv; omega
  have hpos : 0 < q := by omega
  obtain ⟨P, hP, hd⟩ := plane_witness (u := root q) hpos
    (Complex.isPrimitiveRoot_exp q hpos.ne') A hA (by omega) (hA ▸ hc)
  refine ⟨P, hP, le_trans ?_ hd⟩
  change n / (2 * p) ≤ (k + 2 - 1) / 2
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * p)).mpr
  have h₁ : k + 2 ≤ ((k + 2 - 1) / 2 + 1) * 2 := by omega
  have h₂ := Nat.mul_le_mul_right p h₁
  rw [Nat.add_mul, Nat.mul_comm k p] at h₂
  rw [← Nat.mul_assoc]
  dsimp [p] at hr hdiv h₂ ⊢
  omega

/--
**Bhowmick's theorem on rich distances.** For a finite set $A$ of points in the Euclidean plane,
call a distance $k$-rich for $A$ if at least $k$ unordered pairs of distinct points of $A$ lie at
that distance, and let $f(n)$ be the largest number of $(n+1)$-rich distances of a set of $n$
points. Then there is a constant $C$ with $n \le C f(n)$ for all sufficiently large $n$; for every
$n$ there is a set of $n$ points with at least $\lfloor n/4 \rfloor$ distances that are
$(n+1)$-rich; and for every $m \ge 1$ there is an $N$ such that for every $n \ge N$ there is a set
of $n$ points with at least $\lfloor n/(2(m+1)) \rfloor$ distances that are $(n+m)$-rich.

Source: K. Bhowmick, A problem of Erdős
about rich distances, arXiv:2407.01174 (2024), https://arxiv.org/abs/2407.01174; External Lean
proof of Erdős Problem 756,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos756.lean.
Moved from `OpenConjectures/Geometry/ErdosProblem756`.
-/
public theorem conjecture_holds : conjecture := by
  refine ⟨Asymptotics.isBigO_iff.mpr ⟨8, ?_⟩, all_sizes, many_sizes⟩
  filter_upwards [eventually_ge_atTop 4] with n hn
  obtain ⟨P, hP, hd⟩ := all_sizes n
  have bound : BddAbove {(richDistances A (n + 1)).card |
      (A : Finset (EuclideanSpace ℝ (Fin 2))) (_ : A.card = n)} := by
    refine ⟨n * n, ?_⟩
    rintro _ ⟨A, hA, rfl⟩
    calc
      _ ≤ (distanceSet A).card := card_filter_le ..
      _ ≤ A.offDiag.card := card_image_le
      _ ≤ n * n := by rw [offDiag_card, hA]; omega
  have hmax : (richDistances P (n + 1)).card ≤ maxRichDistances n :=
    le_csSup bound ⟨P, hP, rfl⟩
  have h : n ≤ 8 * maxRichDistances n := by omega
  simpa [Real.norm_eq_abs, abs_of_nonneg] using
    (show (n : ℝ) ≤ 8 * (maxRichDistances n : ℝ) by exact_mod_cast h)

end MathlibExt.Geometry.ErdosProblem756Wanted
