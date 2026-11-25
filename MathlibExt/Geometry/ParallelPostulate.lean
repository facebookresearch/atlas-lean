/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Geometry/ParallelPostulate.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), problem `parallel_postulate_independent`, at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/parallel_postulate_independent.toml`, rev 1, submitter Kim Morrison, status
archived): the definitions `TarskiAbsolute` and `Euclidean` and the statement of
`parallel_postulate_independent`, with the docstrings and comments they had in the former wanted
module `WantedExt/Geometry/ParallelPostulateWanted.lean`, and the paragraphs of the module
documentation taken from that module (from "Theorem #12" to the list of the two formalizations
it was cross-checked against).
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: converted each
`@[eval_problem]` theorem into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, inlined any
`LeanEval` helper modules, and placed the declarations in the
`MathlibExt.Geometry.ParallelPostulateWanted` namespace. Mathematical statements are unchanged.
Later change (ATLAS, 2026): the `theorem_wanted` was proved and the declarations moved from
`WantedExt/Geometry/ParallelPostulateWanted.lean` to this `MathlibExt` module with unchanged
names, statements and docstrings, and the import of `Batteries.Util.ProofWanted` was replaced by
the Mathlib imports the proof needs.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of
`parallel_postulate_independent`, the two models and the private lemmas it uses, the first
paragraph, proof outline, implementation notes and references of the module documentation, and
the linter options.
-/
module

public import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Independence of the parallel postulate

This module proves `parallel_postulate_independent`: Tarski's Euclidean axiom `A10` is
independent of his axioms of absolute plane geometry. The real coordinate plane is a model of
absolute plane geometry satisfying `A10`, and the Klein–Beltrami disk model of the hyperbolic
plane is one refuting it.

Theorem #12 on Freek Wiedijk's *Formalizing 100 Theorems* list
(<https://www.cs.ru.nl/~freek/100/>). Euclid's parallel postulate is
logically independent of the remaining axioms of plane geometry: there is a
model of absolute (neutral) geometry in which the postulate holds and one in
which it fails, so neither it nor its negation follows from the other axioms.

We use Tarski's axiomatization. `TarskiAbsolute` bundles the betweenness (`B`)
and congruence (`C`) primitives with axioms `A1`–`A9` and the continuity
axiom `A11` — everything except the parallel postulate — following
Schwabhäuser–Szmielew–Tarski. The **Euclidean axiom** `A10` is kept separate
as a `Prop`. `parallel_postulate_independent` then asserts both that some
model satisfies `A10` (the real coordinate plane) and that some model refutes
it (the Klein–Beltrami disk model of the hyperbolic plane).

This formalization was cross-checked against the two existing formalizations
recorded on Freek's list:

* **HOL Light**, John Harrison — `Multivariate/tarski.ml` (axioms hold in
  `ℝ²`) and `100/independence.ml` (the Klein model satisfies `A1`–`A9`, `A11`
  but not `A10`). Axioms `A1`–`A10` match Harrison's `TARSKI_AXIOM_n`
  character-for-character; `A11` is Harrison's second-order continuity axiom.
* **Isabelle/AFP**, Tim Makarios — entry `Tarskis_Geometry`, which builds the
  Klein–Beltrami model and proves it satisfies every Tarski axiom except the
  Euclidean one.

## Proof outline

The points of both models are points of `ℝ × ℝ`, and betweenness is Mathlib's `Wbtw ℝ`. The
axioms that mention only betweenness are therefore proved once, in the plane: inner Pasch (`A7`)
with an explicit intersection point, and continuity (`A11`) with a supremum taken along the line
through the given points. Three points on a line `n · z = κ` with `n ≠ 0` always have one of
them between the other two, which gives the upper-dimension axiom (`A9`) once the points
equidistant from two distinct points are shown to lie on such a line.

* **The real coordinate plane.** Segments are congruent when their squared Euclidean lengths
  agree. If `b` lies between `a` and `c` and `a ≠ b`, then `c = b + λ (b - a)` with `λ ≥ 0`, and
  expanding `|c - d|²` proves the five-segment axiom (`A5`). The Euclidean axiom holds by an
  explicit construction: if `d = a + s (t - a)`, the points `x = a + (b - a) / s` and
  `y = a + (c - a) / s` work.
* **The Klein–Beltrami disk.** The points are those of the open unit disk, and `ab` is
  congruent to `cd` when `(1 - a·b)² / ((1 - |a|²) (1 - |b|²))`, the squared hyperbolic cosine
  of the hyperbolic distance from `a` to `b`, takes the same value for both pairs. Rotations
  about the centre and hyperbolic translations along the first axis preserve betweenness and
  this quantity, and any two points can be moved so that the second is the centre and the
  first lies on the closed negative first half-axis; in that position segment construction
  (`A4`) and the five-segment axiom are direct computations. The Euclidean axiom fails for
  `a = (0, 0)`, `b = (1/2, 0)`, `c = (0, 1/2)`, `d = (1/4, 1/4)` and `t = (3/5, 3/5)`: every
  segment of the disk from the ray `ab` to the ray `ac` lies in the half-plane `x + y < 1`,
  which does not contain `t`.

## Implementation notes

The definitions `TarskiAbsolute` and `Euclidean` and the theorem keep the full names they had in
the former wanted module, so the namespace still reads `ParallelPostulateWanted` and repeats
`Geometry`; the `dupNamespace` linter is turned off for these three declarations only. The two
models and the lemmas about them are private to this module.

## References

* W. Schwabhäuser, W. Szmielew, A. Tarski, *Metamathematische Methoden in der Geometrie*,
  Springer (1983), for Tarski's axioms.
* E. Beltrami (1868) and F. Klein (1871), for the disk model of the hyperbolic plane.
* T. J. M. Makarios, *A Mechanical Verification of the Independence of Tarski's Euclidean
  Axiom*, MSc thesis, Victoria University of Wellington (2012); Isabelle/AFP entry
  `Tarskis_Geometry`.

These are the sources cited by the former wanted module, which took the definitions and the
statement from problem `parallel_postulate_independent` of the lean-eval benchmark
(leanprover/lean-eval).
-/

@[expose] public section

namespace MathlibExt.Geometry.ParallelPostulateWanted
namespace Geometry

set_option linter.dupNamespace false in
/-- **Tarski's absolute plane geometry.** A model of Tarski's absolute plane geometry is a type
$M$ of points with a betweenness relation $B$ and a congruence relation $C$, where $B(a, b, c)$
means that $b$ lies between $a$ and $c$ (allowing $b = a$ or $b = c$) and $C(a, b, c, d)$ means
that the segment $ab$ is congruent to the segment $cd$, satisfying the following axioms, in which
unbound variables range over all points of $M$ (axioms A1–A9 and A11 of
Schwabhäuser–Szmielew–Tarski, that is, all of Tarski's axioms except the Euclidean axiom A10):
(A1) $C(a, b, b, a)$;
(A2) if $C(a, b, c, d)$ and $C(a, b, e, f)$, then $C(c, d, e, f)$;
(A3) if $C(a, b, c, c)$, then $a = b$;
(A4) there is a point $x$ with $B(a, b, x)$ and $C(b, x, c, d)$;
(A5) if $a \ne b$, $B(a, b, c)$, $B(a', b', c')$, $C(a, b, a', b')$, $C(b, c, b', c')$,
$C(a, d, a', d')$ and $C(b, d, b', d')$, then $C(c, d, c', d')$;
(A6) if $B(a, b, a)$, then $a = b$;
(A7) if $B(a, p, c)$ and $B(b, q, c)$, then there is a point $x$ with $B(p, x, b)$ and
$B(q, x, a)$;
(A8) there are points $a, b, c$ such that none of $B(a, b, c)$, $B(b, c, a)$ and
$B(c, a, b)$ holds;
(A9) if $p \ne q$, $C(p, a, q, a)$, $C(p, b, q, b)$ and $C(p, c, q, c)$, then $B(a, b, c)$,
$B(b, c, a)$ or $B(c, a, b)$;
(A11) for all sets $X, Y \subseteq M$, if there is a point $a$ with $B(a, x, y)$ for all
$x \in X$ and $y \in Y$, then there is a point $b$ with $B(x, b, y)$ for all $x \in X$ and
$y \in Y$. -/
class TarskiAbsolute (M : Type*) where
  /-- Betweenness: `B a b c` says `b` lies between `a` and `c` (collinear; the
  non-strict convention, allowing `b = a` or `b = c`). -/
  B : M → M → M → Prop
  /-- Congruence of segments: `C a b c d` says `ab` is congruent to `cd`. -/
  C : M → M → M → M → Prop
  /-- **A1** Reflexivity of congruence. -/
  congr_refl : ∀ a b, C a b b a
  /-- **A2** Transitivity of congruence. -/
  congr_trans : ∀ a b c d e f, C a b c d → C a b e f → C c d e f
  /-- **A3** Identity of congruence: a zero-length segment has equal endpoints. -/
  congr_id : ∀ a b c, C a b c c → a = b
  /-- **A4** Segment construction: any segment can be extended to match a given length. -/
  segment_construction : ∀ a b c d, ∃ x, B a b x ∧ C b x c d
  /-- **A5** Five-segment axiom (a substitute for SAS congruence). -/
  five_segment : ∀ a b c d a' b' c' d', a ≠ b →
    B a b c → B a' b' c' →
    C a b a' b' → C b c b' c' → C a d a' d' → C b d b' d' →
    C c d c' d'
  /-- **A6** Identity of betweenness. -/
  betw_id : ∀ a b, B a b a → a = b
  /-- **A7** Inner Pasch. -/
  inner_pasch : ∀ a b c p q, B a p c → B b q c → ∃ x, B p x b ∧ B q x a
  /-- **A8** Lower-dimension axiom: there exist three non-collinear points. -/
  lower_dim : ∃ a b c, ¬ B a b c ∧ ¬ B b c a ∧ ¬ B c a b
  /-- **A9** Upper-dimension axiom (2D): three points equidistant from two
  distinct points are collinear. -/
  upper_dim : ∀ a b c p q, p ≠ q → C p a q a → C p b q b → C p c q c →
    B a b c ∨ B b c a ∨ B c a b
  /-- **A11** Continuity (second-order form): if some point `a` precedes the
  whole of `Y` as seen from `X` — every `x ∈ X` lies between `a` and every
  `y ∈ Y` — then some point `b` lies between every `x ∈ X` and every
  `y ∈ Y`. -/
  continuity : ∀ X Y : Set M,
    (∃ a, ∀ x ∈ X, ∀ y ∈ Y, B a x y) → (∃ b, ∀ x ∈ X, ∀ y ∈ Y, B x b y)

set_option linter.dupNamespace false in
/-- **Tarski's Euclidean axiom.** For a model $M$ of Tarski's absolute plane geometry with
betweenness relation $B$, where $B(a, b, c)$ means that $b$ lies between $a$ and $c$ (allowing
$b = a$ or $b = c$), the Euclidean axiom A10 holds in $M$ when for all points $a, b, c, d, t$ of
$M$ with $B(a, d, t)$, $B(b, d, c)$ and $a \ne d$ there are points $x$ and $y$ of $M$ with
$B(a, b, x)$, $B(a, c, y)$ and $B(x, t, y)$.

In the presence of the other axioms of absolute geometry, this axiom is equivalent to Euclid's
parallel postulate. -/
def Euclidean (M : Type*) (T : TarskiAbsolute M) : Prop :=
  ∀ a b c d t : M, T.B a d t → T.B b d c → a ≠ d →
    ∃ x y : M, T.B a b x ∧ T.B a c y ∧ T.B x t y

/-! ### Betweenness in the coordinate plane -/

/-- Betweenness in `ℝ × ℝ`, in coordinates. -/
private lemma wbtw_iff_coord {a b c : ℝ × ℝ} :
    Wbtw ℝ a b c ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ b.1 = a.1 + t * (c.1 - a.1) ∧
      b.2 = a.2 + t * (c.2 - a.2) := by
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    refine ⟨t, h0, h1, ?_, ?_⟩ <;>
      simp only [AffineMap.lineMap_apply_module', Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;> ring
  · rintro ⟨t, h0, h1, h₁, h₂⟩
    refine ⟨t, ⟨h0, h1⟩, ?_⟩
    ext <;> simp only [AffineMap.lineMap_apply_module', Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul, h₁, h₂] <;> ring

/-- Inner Pasch (axiom A7) in `ℝ × ℝ`. -/
private lemma inner_pasch_plane {a b c p q : ℝ × ℝ} (hp : Wbtw ℝ a p c)
    (hq : Wbtw ℝ b q c) : ∃ x, Wbtw ℝ p x b ∧ Wbtw ℝ q x a := by
  obtain ⟨s, hs0, hs1, hp1, hp2⟩ := wbtw_iff_coord.1 hp
  obtain ⟨t, ht0, ht1, hq1, hq2⟩ := wbtw_iff_coord.1 hq
  rcases eq_or_lt_of_le (show 0 ≤ s * (1 - t) + t by nlinarith) with hD | hD
  · have ht : t = 0 := by nlinarith
    have hs : s = 0 := by subst ht; simpa using hD.symm
    subst ht hs
    have hpa : p = a := Prod.ext (by simpa using hp1) (by simpa using hp2)
    have hqb : q = b := Prod.ext (by simpa using hq1) (by simpa using hq2)
    exact ⟨a, hpa ▸ wbtw_self_left _ _ _, hqb ▸ wbtw_self_right _ _ _⟩
  · set D := s * (1 - t) + t
    refine ⟨(p.1 + s * (1 - t) / D * (b.1 - p.1), p.2 + s * (1 - t) / D * (b.2 - p.2)), ?_, ?_⟩
    · refine wbtw_iff_coord.2 ⟨s * (1 - t) / D, by positivity, ?_, rfl, rfl⟩
      rw [div_le_one hD]; linarith
    · have : 0 ≤ 1 - s := by linarith
      refine wbtw_iff_coord.2 ⟨t * (1 - s) / D, by positivity, ?_, ?_, ?_⟩
      · rw [div_le_one hD]; nlinarith
      · rw [hp1, hq1]; field_simp; ring
      · rw [hp2, hq2]; field_simp; ring

/-- Continuity (axiom A11) in `ℝ × ℝ`: all the points lie on one line through `a`, and the
supremum of the parameters of the points of `X` gives the point `b`. -/
private lemma continuity_plane (X Y : Set (ℝ × ℝ))
    (h : ∃ a, ∀ x ∈ X, ∀ y ∈ Y, Wbtw ℝ a x y) : ∃ b, ∀ x ∈ X, ∀ y ∈ Y, Wbtw ℝ x b y := by
  obtain ⟨a, ha⟩ := h
  by_cases hX : ∀ x ∈ X, x = a
  · exact ⟨a, fun x hx y _ => (hX x hx) ▸ wbtw_self_left _ _ _⟩
  push Not at hX
  obtain ⟨x₀, hx₀X, hx₀a⟩ := hX
  rcases Y.eq_empty_or_nonempty with hY | ⟨y₀, hy₀⟩
  · exact ⟨a, fun x _ y hy => by simp [hY] at hy⟩
  have hay₀ : a ≠ y₀ := (ha x₀ hx₀X y₀ hy₀).left_ne_right_of_ne_left hx₀a
  set L : ℝ →ᵃ[ℝ] ℝ × ℝ := AffineMap.lineMap a y₀ with hL
  have hLinj : Function.Injective L := AffineMap.lineMap_injective ℝ hay₀
  have hL0 : L 0 = a := AffineMap.lineMap_apply_zero _ _
  have hL1 : L 1 = y₀ := AffineMap.lineMap_apply_one _ _
  have hXL : ∀ x ∈ X, ∃ s, L s = x := fun x hx => by
    obtain ⟨s, -, hs⟩ := ha x hx y₀ hy₀
    exact ⟨s, hs⟩
  obtain ⟨s₀, hs₀⟩ := hXL x₀ hx₀X
  have hYL : ∀ y ∈ Y, ∃ r, L r = y := fun y hy => by
    obtain ⟨r, -, hr⟩ := (ha x₀ hx₀X y hy).right_mem_image_Ici_of_left_ne hx₀a.symm
    refine ⟨s₀ * r, ?_⟩
    rw [← hr, ← hs₀, hL]
    ext <;> simp only [AffineMap.lineMap_apply_module', Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;> ring
  have hbet : ∀ s r, L s ∈ X → L r ∈ Y → Wbtw ℝ 0 s r := fun s r hs hr => by
    have := ha _ hs _ hr
    rwa [← hL0, hLinj.wbtw_map_iff] at this
  have hs₀pos : 0 < s₀ := by
    have h01 := hbet s₀ 1 (hs₀ ▸ hx₀X) (hL1 ▸ hy₀)
    rw [wbtw_iff_of_le zero_le_one] at h01
    refine lt_of_le_of_ne h01.1 ?_
    rintro rfl
    exact hx₀a (hs₀ ▸ hL0)
  have key : ∀ s r, L s ∈ X → L r ∈ Y → s ≤ r := fun s r hs hr => by
    have hr0 : 0 ≤ r := by
      by_contra hneg
      push Not at hneg
      have := hbet s₀ r (hs₀ ▸ hx₀X) hr
      rw [wbtw_comm, wbtw_iff_of_le hneg.le] at this
      linarith [this.2]
    exact ((wbtw_iff_of_le hr0).1 (hbet s r hs hr)).2
  have hSne : (L ⁻¹' X).Nonempty := ⟨s₀, by simp [hs₀, hx₀X]⟩
  have hSbdd : BddAbove (L ⁻¹' X) := ⟨1, fun s hs => key s 1 hs (hL1 ▸ hy₀)⟩
  refine ⟨L (sSup (L ⁻¹' X)), fun x hx y hy => ?_⟩
  obtain ⟨s, rfl⟩ := hXL x hx
  obtain ⟨r, rfl⟩ := hYL y hy
  exact (Wbtw.of_le_of_le (le_csSup hSbdd hx)
    (csSup_le hSne fun s' hs' => key s' r hs' hy)).map L

/-- Of three points on a line `n · z = κ` with `n ≠ 0`, one lies between the other two. -/
private lemma wbtw_trichotomy_of_dot {a b c : ℝ × ℝ} {n₁ n₂ κ : ℝ}
    (hn : n₁ ^ 2 + n₂ ^ 2 ≠ 0) (ha : a.1 * n₁ + a.2 * n₂ = κ) (hb : b.1 * n₁ + b.2 * n₂ = κ)
    (hc : c.1 * n₁ + c.2 * n₂ = κ) :
    Wbtw ℝ a b c ∨ Wbtw ℝ b c a ∨ Wbtw ℝ c a b := by
  apply Collinear.wbtw_or_wbtw_or_wbtw
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  refine ⟨(-n₂, n₁), fun p hp => ?_⟩
  have hp' : p.1 * n₁ + p.2 * n₂ = κ := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> assumption
  refine ⟨((p.2 - a.2) * n₁ - (p.1 - a.1) * n₂) / (n₁ ^ 2 + n₂ ^ 2), ?_⟩
  ext
  · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    field_simp
    linear_combination n₁ * (hp' - ha)
  · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    field_simp
    linear_combination n₂ * (hp' - ha)

/-- The points `(0, 0)`, `(r, 0)` and `(0, r)` with `r ≠ 0` are not collinear. -/
private lemma not_wbtw_axes {r : ℝ} (hr : r ≠ 0) :
    ¬ Wbtw ℝ ((0, 0) : ℝ × ℝ) (r, 0) (0, r) ∧ ¬ Wbtw ℝ ((r, 0) : ℝ × ℝ) (0, r) (0, 0) ∧
      ¬ Wbtw ℝ ((0, r) : ℝ × ℝ) (0, 0) (r, 0) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    obtain ⟨t, -, -, h1, h2⟩ := wbtw_iff_coord.1 h <;> simp only at h1 h2
  · exact hr (by linarith)
  · exact hr (by linarith)
  · exact hr (by linear_combination -h1 - h2)

/-! ### The real coordinate plane -/

/-- The squared Euclidean distance in `ℝ × ℝ`. -/
private def sqDist (p q : ℝ × ℝ) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

private lemma sqDist_nonneg (p q : ℝ × ℝ) : 0 ≤ sqDist p q := by
  unfold sqDist; positivity

private lemma sqDist_pos {p q : ℝ × ℝ} (h : p ≠ q) : 0 < sqDist p q := by
  unfold sqDist
  rcases ne_or_eq p.1 q.1 with h1 | h1
  · have := pow_pos (abs_pos.2 (sub_ne_zero.2 h1)) 2
    rw [sq_abs] at this
    positivity
  · have h2 : p.2 ≠ q.2 := fun h2 => h (Prod.ext h1 h2)
    have := pow_pos (abs_pos.2 (sub_ne_zero.2 h2)) 2
    rw [sq_abs] at this
    positivity

/-- A point `c` with `b` between `a ≠ b` and `c` is `b + l (b - a)` for some `l ≥ 0`. -/
private lemma exists_extension {a b c : ℝ × ℝ} (hab : a ≠ b) (h : Wbtw ℝ a b c) :
    ∃ l : ℝ, 0 ≤ l ∧ c.1 = b.1 + l * (b.1 - a.1) ∧ c.2 = b.2 + l * (b.2 - a.2) := by
  obtain ⟨t, ht0, ht1, h1, h2⟩ := wbtw_iff_coord.1 h
  have ht : t ≠ 0 := by
    rintro rfl
    exact hab (Prod.ext (by simpa using h1.symm) (by simpa using h2.symm))
  refine ⟨(1 - t) / t, div_nonneg (by linarith) ht0, ?_, ?_⟩
  · rw [h1]; field_simp; ring
  · rw [h2]; field_simp; ring

private lemma sqDist_extension {a b c d : ℝ × ℝ} {l : ℝ} (h1 : c.1 = b.1 + l * (b.1 - a.1))
    (h2 : c.2 = b.2 + l * (b.2 - a.2)) :
    sqDist c d = l ^ 2 * sqDist a b + l * (sqDist a b + sqDist b d - sqDist a d) + sqDist b d := by
  unfold sqDist; rw [h1, h2]; ring

/-- The real coordinate plane, with betweenness `Wbtw ℝ` and congruence of segments given by
equality of squared Euclidean lengths. -/
@[instance_reducible]
private noncomputable def euclideanPlane : TarskiAbsolute (ℝ × ℝ) where
  B a b c := Wbtw ℝ a b c
  C a b c d := sqDist a b = sqDist c d
  congr_refl a b := by unfold sqDist; ring
  congr_trans _ _ _ _ _ _ h1 h2 := h1.symm.trans h2
  congr_id a b c h := by
    by_contra hab
    have h0 : sqDist c c = 0 := by simp [sqDist]
    linarith [sqDist_pos hab]
  segment_construction a b c d := by
    by_cases hab : a = b
    · subst hab
      refine ⟨(a.1 + √(sqDist c d), a.2), wbtw_self_left _ _ _, ?_⟩
      have : sqDist a (a.1 + √(sqDist c d), a.2) = √(sqDist c d) ^ 2 := by unfold sqDist; ring
      rw [this, Real.sq_sqrt (sqDist_nonneg c d)]
    · have hS := sqDist_pos hab
      set k := √(sqDist c d / sqDist a b)
      have hk0 : 0 ≤ k := Real.sqrt_nonneg _
      have hk2 : k ^ 2 = sqDist c d / sqDist a b :=
        Real.sq_sqrt (div_nonneg (sqDist_nonneg c d) hS.le)
      refine ⟨(b.1 + k * (b.1 - a.1), b.2 + k * (b.2 - a.2)), ?_, ?_⟩
      · refine wbtw_iff_coord.2 ⟨1 / (1 + k), by positivity, ?_, ?_, ?_⟩
        · rw [div_le_one (by positivity)]; linarith
        · field_simp; ring
        · field_simp; ring
      · have : sqDist b (b.1 + k * (b.1 - a.1), b.2 + k * (b.2 - a.2)) = k ^ 2 * sqDist a b := by
          unfold sqDist; ring
        rw [this, hk2]
        field_simp
  five_segment a b c d a' b' c' d' hab h1 h2 h3 h4 h5 h6 := by
    have hS := sqDist_pos hab
    have hab' : a' ≠ b' := fun h => by
      have : sqDist b' b' = 0 := by simp [sqDist]
      rw [h, this] at h3
      linarith
    obtain ⟨l, hl, hc1, hc2⟩ := exists_extension hab h1
    obtain ⟨l', hl', hc1', hc2'⟩ := exists_extension hab' h2
    have hbc : sqDist b c = l ^ 2 * sqDist a b := by unfold sqDist; rw [hc1, hc2]; ring
    have hbc' : sqDist b' c' = l' ^ 2 * sqDist a' b' := by unfold sqDist; rw [hc1', hc2']; ring
    have hll : l = l' := by
      refine (sq_eq_sq₀ hl hl').1 ?_
      rw [← h4, ← h3, hbc] at hbc'
      exact mul_right_cancel₀ hS.ne' hbc'
    rw [sqDist_extension hc1 hc2, sqDist_extension hc1' hc2', h3, h5, h6, hll]
  betw_id _ _ h := ((wbtw_self_iff ℝ).1 h).symm
  inner_pasch _ _ _ _ _ h1 h2 := inner_pasch_plane h1 h2
  lower_dim := ⟨(0, 0), (1, 0), (0, 1), not_wbtw_axes one_ne_zero⟩
  upper_dim a b c p q hpq h1 h2 h3 := by
    have hn : (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 ≠ 0 := (sqDist_pos (Ne.symm hpq)).ne'
    refine wbtw_trichotomy_of_dot (κ := (q.1 ^ 2 + q.2 ^ 2 - p.1 ^ 2 - p.2 ^ 2) / 2) hn ?_ ?_ ?_
    · unfold sqDist at h1; linear_combination h1 / 2
    · unfold sqDist at h2; linear_combination h2 / 2
    · unfold sqDist at h3; linear_combination h3 / 2
  continuity X Y h := continuity_plane X Y h

/-- The Euclidean axiom holds in the real coordinate plane. -/
private lemma euclidean_euclideanPlane : Euclidean (ℝ × ℝ) euclideanPlane := by
  intro a b c d t hadt hbdc had
  change Wbtw ℝ a d t at hadt
  change Wbtw ℝ b d c at hbdc
  obtain ⟨s, hs0, hs1, hd1, hd2⟩ := wbtw_iff_coord.1 hadt
  obtain ⟨u, hu0, hu1, hd1', hd2'⟩ := wbtw_iff_coord.1 hbdc
  have hs : s ≠ 0 := by
    rintro rfl
    exact had (Prod.ext (by simpa using hd1.symm) (by simpa using hd2.symm))
  refine ⟨(a.1 + (b.1 - a.1) / s, a.2 + (b.2 - a.2) / s),
    (a.1 + (c.1 - a.1) / s, a.2 + (c.2 - a.2) / s), ?_, ?_, ?_⟩
  · refine wbtw_iff_coord.2 ⟨s, hs0, hs1, ?_, ?_⟩ <;> field_simp <;> ring
  · refine wbtw_iff_coord.2 ⟨s, hs0, hs1, ?_, ?_⟩ <;> field_simp <;> ring
  · refine wbtw_iff_coord.2 ⟨u, hu0, hu1, ?_, ?_⟩
    · field_simp
      linear_combination hd1' - hd1
    · field_simp
      linear_combination hd2' - hd2

/-! ### The Klein–Beltrami disk: congruence -/

/-- The squared hyperbolic cosine `(1 - p·q)² / ((1 - |p|²) (1 - |q|²))` of the hyperbolic
distance between two points `p` and `q` of the Klein–Beltrami disk. -/
private noncomputable def coshSq (p q : ℝ × ℝ) : ℝ :=
  (1 - (p.1 * q.1 + p.2 * q.2)) ^ 2 / ((1 - (p.1 ^ 2 + p.2 ^ 2)) * (1 - (q.1 ^ 2 + q.2 ^ 2)))

private lemma coshSq_comm (p q : ℝ × ℝ) : coshSq p q = coshSq q p := by unfold coshSq; ring

private lemma one_sub_dot_pos {p q : ℝ × ℝ} (hp : p.1 ^ 2 + p.2 ^ 2 < 1)
    (hq : q.1 ^ 2 + q.2 ^ 2 < 1) : 0 < 1 - (p.1 * q.1 + p.2 * q.2) := by
  nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]

private lemma coshSq_identity (p q : ℝ × ℝ) :
    (1 - (p.1 * q.1 + p.2 * q.2)) ^ 2 - (1 - (p.1 ^ 2 + p.2 ^ 2)) * (1 - (q.1 ^ 2 + q.2 ^ 2)) =
      (p.1 * (q.1 - p.1) + p.2 * (q.2 - p.2)) ^ 2 +
        (1 - (p.1 ^ 2 + p.2 ^ 2)) * ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) := by ring

private lemma one_le_coshSq {p q : ℝ × ℝ} (hp : p.1 ^ 2 + p.2 ^ 2 < 1)
    (hq : q.1 ^ 2 + q.2 ^ 2 < 1) : 1 ≤ coshSq p q := by
  unfold coshSq
  rw [le_div_iff₀ (mul_pos (by linarith) (by linarith)), one_mul, ← sub_nonneg,
    coshSq_identity]
  have : 0 ≤ 1 - (p.1 ^ 2 + p.2 ^ 2) := by linarith
  positivity

private lemma eq_of_coshSq_eq_one {p q : ℝ × ℝ} (hp : p.1 ^ 2 + p.2 ^ 2 < 1)
    (hq : q.1 ^ 2 + q.2 ^ 2 < 1) (h : coshSq p q = 1) : p = q := by
  unfold coshSq at h
  rw [div_eq_one_iff_eq (mul_pos (by linarith) (by linarith)).ne', ← sub_eq_zero,
    coshSq_identity] at h
  have h0 : 0 < 1 - (p.1 ^ 2 + p.2 ^ 2) := by linarith
  have h1 : (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (p.1 * (q.1 - p.1) + p.2 * (q.2 - p.2)), sq_nonneg (q.1 - p.1),
      sq_nonneg (q.2 - p.2), mul_nonneg h0.le (add_nonneg (sq_nonneg (q.1 - p.1))
        (sq_nonneg (q.2 - p.2)))]
  have e1 : q.1 - p.1 = 0 := by nlinarith [sq_nonneg (q.1 - p.1), sq_nonneg (q.2 - p.2)]
  have e2 : q.2 - p.2 = 0 := by nlinarith [sq_nonneg (q.1 - p.1), sq_nonneg (q.2 - p.2)]
  exact Prod.ext (by linarith) (by linarith)

private lemma coshSq_self {p : ℝ × ℝ} (hp : p.1 ^ 2 + p.2 ^ 2 < 1) : coshSq p p = 1 := by
  unfold coshSq
  rw [div_eq_one_iff_eq (mul_pos (by linarith) (by linarith)).ne']
  ring

private lemma coshSq_zero_left (q : ℝ × ℝ) :
    coshSq (0, 0) q = 1 / (1 - (q.1 ^ 2 + q.2 ^ 2)) := by
  simp [coshSq]

private lemma coshSq_zero_right (p : ℝ × ℝ) :
    coshSq p (0, 0) = 1 / (1 - (p.1 ^ 2 + p.2 ^ 2)) := by
  simp [coshSq]

/-! ### The Klein–Beltrami disk: rotations and hyperbolic translations -/

/-- The rotation `p ↦ (c p₁ - s p₂, s p₁ + c p₂)` of `ℝ × ℝ`, for `c² + s² = 1`. -/
private def rotate (c s : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (c * p.1 - s * p.2, s * p.1 + c * p.2)

private lemma rotate_dot {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (p q : ℝ × ℝ) :
    (rotate c s p).1 * (rotate c s q).1 + (rotate c s p).2 * (rotate c s q).2 =
      p.1 * q.1 + p.2 * q.2 := by
  simp only [rotate]; linear_combination (p.1 * q.1 + p.2 * q.2) * h

private lemma rotate_normSq {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (p : ℝ × ℝ) :
    (rotate c s p).1 ^ 2 + (rotate c s p).2 ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  simp only [rotate]; linear_combination (p.1 ^ 2 + p.2 ^ 2) * h

private lemma coshSq_rotate {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (p q : ℝ × ℝ) :
    coshSq (rotate c s p) (rotate c s q) = coshSq p q := by
  unfold coshSq; rw [rotate_dot h, rotate_normSq h, rotate_normSq h]

private lemma rotate_neg_rotate {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (p : ℝ × ℝ) :
    rotate c (-s) (rotate c s p) = p := by
  ext <;> simp only [rotate]
  · linear_combination p.1 * h
  · linear_combination p.2 * h

private lemma rotate_wbtw (c s : ℝ) {a b d : ℝ × ℝ} (h : Wbtw ℝ a b d) :
    Wbtw ℝ (rotate c s a) (rotate c s b) (rotate c s d) := by
  obtain ⟨t, ht0, ht1, h1, h2⟩ := wbtw_iff_coord.1 h
  refine wbtw_iff_coord.2 ⟨t, ht0, ht1, ?_, ?_⟩ <;> simp only [rotate, h1, h2] <;> ring

/-- The hyperbolic translation `p ↦ ((p₁ - s) / (1 - s p₁), σ p₂ / (1 - s p₁))` of the
Klein–Beltrami disk along the first axis, for `s² < 1` and `σ² = 1 - s²`; it maps `(s, 0)` to
the centre. -/
private noncomputable def boost (s σ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 - s) / (1 - s * p.1), σ * p.2 / (1 - s * p.1))

private lemma boost_den_pos {s : ℝ} {p : ℝ × ℝ} (hs : s ^ 2 < 1)
    (hp : p.1 ^ 2 + p.2 ^ 2 < 1) : 0 < 1 - s * p.1 := by
  nlinarith [sq_nonneg (s - p.1), sq_nonneg p.2]

private lemma one_sub_boost_dot {s σ : ℝ} (hσ : σ ^ 2 = 1 - s ^ 2) {p q : ℝ × ℝ}
    (hp : 1 - s * p.1 ≠ 0) (hq : 1 - s * q.1 ≠ 0) :
    1 - ((boost s σ p).1 * (boost s σ q).1 + (boost s σ p).2 * (boost s σ q).2) =
      (1 - s ^ 2) * (1 - (p.1 * q.1 + p.2 * q.2)) / ((1 - s * p.1) * (1 - s * q.1)) := by
  have hp' : 1 - p.1 * s ≠ 0 := by rwa [mul_comm]
  have hq' : 1 - q.1 * s ≠ 0 := by rwa [mul_comm]
  simp only [boost]
  field_simp
  linear_combination (-(p.2 * q.2)) * hσ

private lemma one_sub_boost_normSq {s σ : ℝ} (hσ : σ ^ 2 = 1 - s ^ 2) {p : ℝ × ℝ}
    (hp : 1 - s * p.1 ≠ 0) :
    1 - ((boost s σ p).1 ^ 2 + (boost s σ p).2 ^ 2) =
      (1 - s ^ 2) * (1 - (p.1 ^ 2 + p.2 ^ 2)) / (1 - s * p.1) ^ 2 := by
  have hp' : 1 - p.1 * s ≠ 0 := by rwa [mul_comm]
  simp only [boost]
  field_simp
  linear_combination (-(p.2 ^ 2)) * hσ

private lemma boost_mem_disk {s σ : ℝ} (hs : s ^ 2 < 1) (hσ : σ ^ 2 = 1 - s ^ 2)
    {p : ℝ × ℝ} (hp : p.1 ^ 2 + p.2 ^ 2 < 1) :
    (boost s σ p).1 ^ 2 + (boost s σ p).2 ^ 2 < 1 := by
  have hD := boost_den_pos hs hp
  have := one_sub_boost_normSq hσ hD.ne'
  have h1 : 0 < (1 - s ^ 2) * (1 - (p.1 ^ 2 + p.2 ^ 2)) / (1 - s * p.1) ^ 2 :=
    div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  linarith

private lemma coshSq_boost {s σ : ℝ} (hs : s ^ 2 < 1) (hσ : σ ^ 2 = 1 - s ^ 2)
    {p q : ℝ × ℝ} (hp : p.1 ^ 2 + p.2 ^ 2 < 1) (hq : q.1 ^ 2 + q.2 ^ 2 < 1) :
    coshSq (boost s σ p) (boost s σ q) = coshSq p q := by
  have hDp := boost_den_pos hs hp
  have hDq := boost_den_pos hs hq
  unfold coshSq
  rw [one_sub_boost_dot hσ hDp.ne' hDq.ne', one_sub_boost_normSq hσ hDp.ne',
    one_sub_boost_normSq hσ hDq.ne']
  have h1 : 1 - s ^ 2 ≠ 0 := by linarith
  have h2 : 1 - (p.1 ^ 2 + p.2 ^ 2) ≠ 0 := by linarith
  have h3 : 1 - (q.1 ^ 2 + q.2 ^ 2) ≠ 0 := by linarith
  field_simp

private lemma boost_neg_boost {s σ : ℝ} (hs : s ^ 2 < 1) (hσ : σ ^ 2 = 1 - s ^ 2)
    {p : ℝ × ℝ} (hp : 1 - s * p.1 ≠ 0) : boost (-s) σ (boost s σ p) = p := by
  have h1 : 1 - s ^ 2 ≠ 0 := by linarith
  have hp' : 1 - p.1 * s ≠ 0 := by rwa [mul_comm]
  have e : 1 - -s * ((p.1 - s) / (1 - s * p.1)) = (1 - s ^ 2) / (1 - s * p.1) := by
    field_simp; ring
  simp only [boost]
  rw [e]
  ext
  · field_simp; ring
  · field_simp; linear_combination p.2 * hσ

/-- The identity behind the fact that projective maps preserve betweenness. -/
private lemma proj_identity {La Ld Da Dd Db t : ℝ} (hDa : Da ≠ 0) (hDd : Dd ≠ 0)
    (hDb : Db ≠ 0) (h : Db = Da + t * (Dd - Da)) :
    (La + t * (Ld - La)) / Db = La / Da + t * Dd / Db * (Ld / Dd - La / Da) := by
  field_simp
  linear_combination (-La) * h

private lemma boost_wbtw {s σ : ℝ} {a b d : ℝ × ℝ} (ha : 0 < 1 - s * a.1)
    (hb : 0 < 1 - s * b.1) (hd : 0 < 1 - s * d.1) (h : Wbtw ℝ a b d) :
    Wbtw ℝ (boost s σ a) (boost s σ b) (boost s σ d) := by
  obtain ⟨t, ht0, ht1, h1, h2⟩ := wbtw_iff_coord.1 h
  have hDb : 1 - s * b.1 = (1 - s * a.1) + t * ((1 - s * d.1) - (1 - s * a.1)) := by
    rw [h1]; ring
  refine wbtw_iff_coord.2 ⟨t * (1 - s * d.1) / (1 - s * b.1), by positivity, ?_, ?_, ?_⟩
  · rw [div_le_one hb]; nlinarith
  · simp only [boost]
    rw [show b.1 - s = (a.1 - s) + t * ((d.1 - s) - (a.1 - s)) by rw [h1]; ring]
    exact proj_identity ha.ne' hd.ne' hb.ne' hDb
  · simp only [boost]
    rw [show σ * b.2 = σ * a.2 + t * (σ * d.2 - σ * a.2) by rw [h2]; ring]
    exact proj_identity ha.ne' hd.ne' hb.ne' hDb

/-! ### The Klein–Beltrami disk: motions -/

/-- The points of the Klein–Beltrami disk: the open unit disk of `ℝ × ℝ`. -/
private abbrev KleinPoint : Type := {p : ℝ × ℝ // p.1 ^ 2 + p.2 ^ 2 < 1}

/-- A motion of the Klein–Beltrami disk: a bijection preserving betweenness and `coshSq`. -/
private structure IsMotion (f : KleinPoint → KleinPoint) : Prop where
  bijective : Function.Bijective f
  wbtw_iff : ∀ a b c : KleinPoint, Wbtw ℝ (f a).1 (f b).1 (f c).1 ↔ Wbtw ℝ a.1 b.1 c.1
  coshSq_eq : ∀ p q : KleinPoint, coshSq (f p).1 (f q).1 = coshSq p.1 q.1

private lemma IsMotion.comp {f g : KleinPoint → KleinPoint} (hg : IsMotion g)
    (hf : IsMotion f) : IsMotion (g ∘ f) :=
  ⟨hg.bijective.comp hf.bijective, fun a b c => (hg.wbtw_iff _ _ _).trans (hf.wbtw_iff a b c),
    fun p q => (hg.coshSq_eq _ _).trans (hf.coshSq_eq p q)⟩

private lemma IsMotion.of_inverse {f g : KleinPoint → KleinPoint} (hgf : ∀ p, g (f p) = p)
    (hfg : ∀ p, f (g p) = p)
    (hf : ∀ a b c : KleinPoint, Wbtw ℝ a.1 b.1 c.1 → Wbtw ℝ (f a).1 (f b).1 (f c).1)
    (hg : ∀ a b c : KleinPoint, Wbtw ℝ a.1 b.1 c.1 → Wbtw ℝ (g a).1 (g b).1 (g c).1)
    (hk : ∀ p q : KleinPoint, coshSq (f p).1 (f q).1 = coshSq p.1 q.1) : IsMotion f :=
  ⟨⟨Function.LeftInverse.injective hgf, Function.RightInverse.surjective hfg⟩,
    fun a b c => ⟨fun h => by simpa only [hgf] using hg _ _ _ h, hf a b c⟩, hk⟩

/-- A rotation of the Klein–Beltrami disk about its centre. -/
private def rotateK (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (p : KleinPoint) : KleinPoint :=
  ⟨rotate c s p.1, by rw [rotate_normSq h]; exact p.2⟩

private lemma isMotion_rotateK {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    IsMotion (rotateK c s h) := by
  have h' : c ^ 2 + (-s) ^ 2 = 1 := by rw [neg_sq]; exact h
  refine IsMotion.of_inverse (g := rotateK c (-s) h')
    (fun p => Subtype.ext (rotate_neg_rotate h p.1)) (fun p => Subtype.ext ?_)
    (fun a b d hw => rotate_wbtw c s hw) (fun a b d hw => rotate_wbtw c (-s) hw)
    (fun p q => coshSq_rotate h p.1 q.1)
  change rotate c s (rotate c (-s) p.1) = p.1
  simpa using rotate_neg_rotate h' p.1

/-- A hyperbolic translation of the Klein–Beltrami disk along the first axis. -/
private noncomputable def boostK (s σ : ℝ) (hs : s ^ 2 < 1) (hσ : σ ^ 2 = 1 - s ^ 2)
    (p : KleinPoint) : KleinPoint :=
  ⟨boost s σ p.1, boost_mem_disk hs hσ p.2⟩

private lemma isMotion_boostK {s σ : ℝ} (hs : s ^ 2 < 1) (hσ : σ ^ 2 = 1 - s ^ 2) :
    IsMotion (boostK s σ hs hσ) := by
  have hs' : (-s) ^ 2 < 1 := by rwa [neg_sq]
  have hσ' : σ ^ 2 = 1 - (-s) ^ 2 := by rwa [neg_sq]
  refine IsMotion.of_inverse (g := boostK (-s) σ hs' hσ')
    (fun p => Subtype.ext (boost_neg_boost hs hσ (boost_den_pos hs p.2).ne'))
    (fun p => Subtype.ext ?_)
    (fun a b d hw => boost_wbtw (boost_den_pos hs a.2) (boost_den_pos hs b.2)
      (boost_den_pos hs d.2) hw)
    (fun a b d hw => boost_wbtw (boost_den_pos hs' a.2) (boost_den_pos hs' b.2)
      (boost_den_pos hs' d.2) hw)
    (fun p q => coshSq_boost hs hσ p.2 q.2)
  change boost s σ (boost (-s) σ p.1) = p.1
  simpa using boost_neg_boost hs' hσ' (boost_den_pos hs' p.2).ne'

/-- Every vector of `ℝ × ℝ` can be rotated onto the closed negative first half-axis. -/
private lemma exists_rotate (v : ℝ × ℝ) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ (rotate c s v).2 = 0 ∧ (rotate c s v).1 ≤ 0 := by
  rcases eq_or_lt_of_le (add_nonneg (sq_nonneg v.1) (sq_nonneg v.2)) with hv | hv
  · have h1 : v.1 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg v.2]
    have h2 : v.2 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg v.2]
    exact ⟨1, 0, by norm_num, by simp [rotate, h1, h2], by simp [rotate, h1, h2]⟩
  · set r := √(v.1 ^ 2 + v.2 ^ 2)
    have hr0 : 0 < r := Real.sqrt_pos.2 hv
    have hr2 : r ^ 2 = v.1 ^ 2 + v.2 ^ 2 := Real.sq_sqrt hv.le
    refine ⟨-v.1 / r, v.2 / r, ?_, ?_, ?_⟩
    · field_simp; linear_combination -hr2
    · simp only [rotate]; field_simp; ring
    · simp only [rotate]
      have : -v.1 / r * v.1 - v.2 / r * v.2 = -r := by
        field_simp; linear_combination hr2
      rw [this]; linarith

/-- Any two points of the Klein–Beltrami disk can be moved by a motion so that the second goes
to the centre and the first to the closed negative first half-axis. -/
private lemma exists_normalize (a b : KleinPoint) :
    ∃ f, IsMotion f ∧ (f b).1 = (0, 0) ∧ (f a).1.2 = 0 ∧ (f a).1.1 ≤ 0 := by
  obtain ⟨c₁, s₁, h₁, hb2, -⟩ := exists_rotate b.1
  set b' := rotateK c₁ s₁ h₁ b
  have hb'2 : b'.1.2 = 0 := hb2
  have hr : b'.1.1 ^ 2 < 1 := by nlinarith [b'.2, sq_nonneg b'.1.2]
  have hσ : (√(1 - b'.1.1 ^ 2)) ^ 2 = 1 - b'.1.1 ^ 2 := Real.sq_sqrt (by linarith)
  set g := boostK (b'.1.1) (√(1 - b'.1.1 ^ 2)) hr hσ with hg
  have hgb : (g b').1 = (0, 0) := by
    simp only [hg, boostK, boost, hb'2, sub_self, mul_zero, zero_div]
  obtain ⟨c₂, s₂, h₂, ha2, ha1⟩ := exists_rotate (g (rotateK c₁ s₁ h₁ a)).1
  refine ⟨rotateK c₂ s₂ h₂ ∘ g ∘ rotateK c₁ s₁ h₁,
    (isMotion_rotateK h₂).comp ((isMotion_boostK hr hσ).comp (isMotion_rotateK h₁)), ?_, ha2,
    ha1⟩
  change rotate c₂ s₂ (g b').1 = (0, 0)
  rw [hgb]; simp [rotate]

/-! ### The Klein–Beltrami disk: the axioms -/

/-- The open unit disk is convex. -/
private lemma mem_disk_of_wbtw {x b y : ℝ × ℝ} (hx : x.1 ^ 2 + x.2 ^ 2 < 1)
    (hy : y.1 ^ 2 + y.2 ^ 2 < 1) (h : Wbtw ℝ x b y) : b.1 ^ 2 + b.2 ^ 2 < 1 := by
  obtain ⟨t, ht0, ht1, h1, h2⟩ := wbtw_iff_coord.1 h
  rcases eq_or_lt_of_le ht1 with rfl | ht1'
  · rw [h1, h2]; simpa using hy
  · rw [h1, h2]
    nlinarith [mul_pos (sub_pos.2 ht1') (sub_pos.2 hx), mul_nonneg ht0 (sub_pos.2 hy).le,
      mul_nonneg (mul_nonneg ht0 (sub_pos.2 ht1').le)
        (add_nonneg (sq_nonneg (x.1 - y.1)) (sq_nonneg (x.2 - y.2)))]

private lemma wbtw_axis {A : ℝ × ℝ} {γ : ℝ} (hA2 : A.2 = 0) (hA1 : A.1 ≤ 0) (hγ : 0 ≤ γ) :
    Wbtw ℝ A (0, 0) (γ, 0) := by
  rcases eq_or_lt_of_le (show 0 ≤ γ - A.1 by linarith) with h | h
  · have hA : A = (0, 0) := Prod.ext (by linarith) hA2
    rw [hA]; exact wbtw_self_left _ _ _
  · refine wbtw_iff_coord.2 ⟨-A.1 / (γ - A.1), div_nonneg (by linarith) h.le, ?_, ?_, ?_⟩
    · rw [div_le_one h]; linarith
    · simp only; field_simp; ring
    · simp [hA2]

/-- Segment construction (axiom A4) in the Klein–Beltrami disk. -/
private lemma klein_segment_construction (a b c d : KleinPoint) :
    ∃ x : KleinPoint, Wbtw ℝ a.1 b.1 x.1 ∧ coshSq b.1 x.1 = coshSq c.1 d.1 := by
  have hk := one_le_coshSq c.2 d.2
  set k := coshSq c.1 d.1
  have hk0 : 0 < k := by linarith
  have h1k : 0 ≤ 1 - 1 / k := by rw [sub_nonneg, div_le_one hk0]; exact hk
  set γ := √(1 - 1 / k)
  have hγ0 : 0 ≤ γ := Real.sqrt_nonneg _
  have hγ2 : γ ^ 2 = 1 - 1 / k := Real.sq_sqrt h1k
  have hγ1 : (γ, (0 : ℝ)).1 ^ 2 + (γ, (0 : ℝ)).2 ^ 2 < 1 := by
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    rw [hγ2]
    have : 0 < 1 / k := by positivity
    linarith
  obtain ⟨f, hf, hfb, hfa2, hfa1⟩ := exists_normalize a b
  obtain ⟨x, hx⟩ := hf.bijective.2 ⟨(γ, 0), hγ1⟩
  refine ⟨x, ?_, ?_⟩
  · rw [← hf.wbtw_iff, hx, hfb]
    exact wbtw_axis hfa2 hfa1 hγ0
  · rw [← hf.coshSq_eq, hx, hfb, coshSq_zero_left]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    rw [hγ2, sub_sub_cancel, one_div_one_div]

private lemma ray_of_wbtw {A C : ℝ × ℝ} (hA2 : A.2 = 0) (hA1 : A.1 < 0)
    (h : Wbtw ℝ A (0, 0) C) : C.2 = 0 ∧ 0 ≤ C.1 := by
  obtain ⟨t, ht0, ht1, h1, h2⟩ := wbtw_iff_coord.1 h
  simp only [hA2] at h1 h2
  have ht : 0 < t := by
    refine lt_of_le_of_ne ht0 ?_
    rintro rfl
    simp only [zero_mul, add_zero] at h1
    linarith
  refine ⟨?_, ?_⟩
  · have : t * C.2 = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left ht.ne'
  · nlinarith [mul_nonneg (sub_nonneg.2 ht1) (neg_nonneg.2 hA1.le)]

/-- The five-segment axiom (A5) in the Klein–Beltrami disk, in the normalized position where
`b = b'` is the centre and `a`, `a'` lie on the closed negative first half-axis. -/
private lemma five_segment_normal {A C D A' C' D' : ℝ × ℝ}
    (hA : A.1 ^ 2 + A.2 ^ 2 < 1) (hC : C.1 ^ 2 + C.2 ^ 2 < 1) (hD : D.1 ^ 2 + D.2 ^ 2 < 1)
    (hA' : A'.1 ^ 2 + A'.2 ^ 2 < 1) (hC' : C'.1 ^ 2 + C'.2 ^ 2 < 1)
    (hD' : D'.1 ^ 2 + D'.2 ^ 2 < 1)
    (hA2 : A.2 = 0) (hA1 : A.1 ≤ 0) (hA'2 : A'.2 = 0) (hA'1 : A'.1 ≤ 0) (hA0 : A ≠ (0, 0))
    (h1 : Wbtw ℝ A (0, 0) C) (h2 : Wbtw ℝ A' (0, 0) C')
    (h3 : coshSq A (0, 0) = coshSq A' (0, 0)) (h4 : coshSq (0, 0) C = coshSq (0, 0) C')
    (h5 : coshSq A D = coshSq A' D') (h6 : coshSq (0, 0) D = coshSq (0, 0) D') :
    coshSq C D = coshSq C' D' := by
  have hA1' : A.1 < 0 := lt_of_le_of_ne hA1 fun h => hA0 (Prod.ext h hA2)
  -- the first points agree
  rw [coshSq_zero_right, coshSq_zero_right, hA2, hA'2] at h3
  have hAA : A.1 = A'.1 := by
    have h1A : 1 - (A.1 ^ 2 + 0 ^ 2) ≠ 0 := by rw [← hA2]; linarith
    have h1A' : 1 - (A'.1 ^ 2 + 0 ^ 2) ≠ 0 := by rw [← hA'2]; linarith
    rw [div_eq_div_iff h1A h1A'] at h3
    have := (sq_eq_sq₀ (neg_nonneg.2 hA1) (neg_nonneg.2 hA'1)).1
      (by rw [neg_sq, neg_sq]; linarith)
    linarith
  -- the third points agree
  obtain ⟨hC2, hC1⟩ := ray_of_wbtw hA2 hA1' h1
  obtain ⟨hC'2, hC'1⟩ := ray_of_wbtw hA'2 (hAA ▸ hA1') h2
  rw [coshSq_zero_left, coshSq_zero_left, hC2, hC'2] at h4
  have hCC : C.1 = C'.1 := by
    have h1C : 1 - (C.1 ^ 2 + 0 ^ 2) ≠ 0 := by rw [← hC2]; linarith
    have h1C' : 1 - (C'.1 ^ 2 + 0 ^ 2) ≠ 0 := by rw [← hC'2]; linarith
    rw [div_eq_div_iff h1C h1C'] at h4
    exact (sq_eq_sq₀ hC1 hC'1).1 (by linarith)
  -- the fourth points have the same norm and the same first coordinate
  rw [coshSq_zero_left, coshSq_zero_left] at h6
  have hDD : D.1 ^ 2 + D.2 ^ 2 = D'.1 ^ 2 + D'.2 ^ 2 := by
    rw [div_eq_div_iff (by linarith) (by linarith)] at h6
    linarith
  have hD1 : D.1 = D'.1 := by
    unfold coshSq at h5
    rw [hA2, hA'2, ← hAA, ← hDD] at h5
    have hden : (1 - (A.1 ^ 2 + 0 ^ 2)) * (1 - (D.1 ^ 2 + D.2 ^ 2)) ≠ 0 :=
      mul_ne_zero (by rw [← hA2]; linarith) (by linarith)
    rw [div_left_inj₀ hden] at h5
    have hp : 0 < 1 - (A.1 * D.1 + 0 * D.2) := by
      have := one_sub_dot_pos hA hD; rwa [hA2] at this
    have hp' : 0 < 1 - (A.1 * D'.1 + 0 * D'.2) := by
      have := one_sub_dot_pos hA hD'; rwa [hA2] at this
    have := (sq_eq_sq₀ hp.le hp'.le).1 h5
    apply mul_left_cancel₀ hA1'.ne
    linarith
  -- conclude
  have hCC' : C' = C := Prod.ext hCC.symm (hC'2.trans hC2.symm)
  rw [hCC']
  unfold coshSq
  rw [hDD, hC2, hD1]
  ring

/-- The five-segment axiom (A5) in the Klein–Beltrami disk. -/
private lemma klein_five_segment (a b c d a' b' c' d' : KleinPoint) (hab : a ≠ b)
    (h1 : Wbtw ℝ a.1 b.1 c.1) (h2 : Wbtw ℝ a'.1 b'.1 c'.1)
    (h3 : coshSq a.1 b.1 = coshSq a'.1 b'.1) (h4 : coshSq b.1 c.1 = coshSq b'.1 c'.1)
    (h5 : coshSq a.1 d.1 = coshSq a'.1 d'.1) (h6 : coshSq b.1 d.1 = coshSq b'.1 d'.1) :
    coshSq c.1 d.1 = coshSq c'.1 d'.1 := by
  obtain ⟨f, hf, hfb, hfa2, hfa1⟩ := exists_normalize a b
  obtain ⟨g, hg, hgb, hga2, hga1⟩ := exists_normalize a' b'
  rw [← hf.wbtw_iff, hfb] at h1
  rw [← hg.wbtw_iff, hgb] at h2
  rw [← hf.coshSq_eq a b, ← hg.coshSq_eq a' b', hfb, hgb] at h3
  rw [← hf.coshSq_eq b c, ← hg.coshSq_eq b' c', hfb, hgb] at h4
  rw [← hf.coshSq_eq a d, ← hg.coshSq_eq a' d'] at h5
  rw [← hf.coshSq_eq b d, ← hg.coshSq_eq b' d', hfb, hgb] at h6
  rw [← hf.coshSq_eq c d, ← hg.coshSq_eq c' d']
  have hA0 : (f a).1 ≠ (0, 0) := fun h =>
    hab (hf.bijective.1 (Subtype.ext (h.trans hfb.symm)))
  exact five_segment_normal (f a).2 (f c).2 (f d).2 (g a').2 (g c').2 (g d').2 hfa2 hfa1 hga2
    hga1 hA0 h1 h2 h3 h4 h5 h6

/-- The upper-dimension axiom (A9) in the Klein–Beltrami disk: the points `z` with
`coshSq p z = coshSq q z` lie on the line `z · (Q p - P q) = Q - P`, where
`P = √(1 - |p|²)` and `Q = √(1 - |q|²)`. -/
private lemma klein_upper_dim (a b c p q : KleinPoint) (hpq : p ≠ q)
    (h1 : coshSq p.1 a.1 = coshSq q.1 a.1) (h2 : coshSq p.1 b.1 = coshSq q.1 b.1)
    (h3 : coshSq p.1 c.1 = coshSq q.1 c.1) :
    Wbtw ℝ a.1 b.1 c.1 ∨ Wbtw ℝ b.1 c.1 a.1 ∨ Wbtw ℝ c.1 a.1 b.1 := by
  obtain ⟨⟨p1, p2⟩, hp⟩ := p
  obtain ⟨⟨q1, q2⟩, hq⟩ := q
  simp only at hp hq h1 h2 h3
  set P := √(1 - (p1 ^ 2 + p2 ^ 2)) with hPdef
  set Q := √(1 - (q1 ^ 2 + q2 ^ 2)) with hQdef
  have hP : 0 < P := Real.sqrt_pos.2 (by linarith)
  have hQ : 0 < Q := Real.sqrt_pos.2 (by linarith)
  have hP2 : P ^ 2 = 1 - (p1 ^ 2 + p2 ^ 2) := Real.sq_sqrt (by linarith)
  have hQ2 : Q ^ 2 = 1 - (q1 ^ 2 + q2 ^ 2) := Real.sq_sqrt (by linarith)
  have key : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → coshSq (p1, p2) z = coshSq (q1, q2) z →
      z.1 * (Q * p1 - P * q1) + z.2 * (Q * p2 - P * q2) = Q - P := by
    intro z hz h
    have hz' : 0 < 1 - (z.1 ^ 2 + z.2 ^ 2) := by linarith
    unfold coshSq at h
    simp only at h
    rw [div_eq_div_iff (mul_pos (by linarith) hz').ne' (mul_pos (by linarith) hz').ne'] at h
    have h' : ((1 - (p1 * z.1 + p2 * z.2)) * Q) ^ 2 =
        ((1 - (q1 * z.1 + q2 * z.2)) * P) ^ 2 := by
      rw [mul_pow, mul_pow, hP2, hQ2]
      apply mul_right_cancel₀ hz'.ne'
      linear_combination h
    have hpz : 0 < 1 - (p1 * z.1 + p2 * z.2) := one_sub_dot_pos (p := (p1, p2)) hp hz
    have hqz : 0 < 1 - (q1 * z.1 + q2 * z.2) := one_sub_dot_pos (p := (q1, q2)) hq hz
    have := (sq_eq_sq₀ (by positivity) (by positivity)).1 h'
    linear_combination -this
  have hn : (Q * p1 - P * q1) ^ 2 + (Q * p2 - P * q2) ^ 2 ≠ 0 := by
    intro h0
    have h00 := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).1 h0
    have e1 : Q * p1 = P * q1 := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h00.1)
    have e2 : Q * p2 = P * q2 := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h00.2)
    have hnorm : p1 ^ 2 + p2 ^ 2 = q1 ^ 2 + q2 ^ 2 := by
      have : Q ^ 2 * (p1 ^ 2 + p2 ^ 2) = P ^ 2 * (q1 ^ 2 + q2 ^ 2) := by
        linear_combination (Q * p1 + P * q1) * e1 + (Q * p2 + P * q2) * e2
      rw [hP2, hQ2] at this
      linear_combination this
    have hPQ : P = Q := by rw [hPdef, hQdef, hnorm]
    rw [hPQ] at e1 e2
    exact hpq (Subtype.ext (Prod.ext (mul_left_cancel₀ hQ.ne' e1) (mul_left_cancel₀ hQ.ne' e2)))
  exact wbtw_trichotomy_of_dot hn (key a.1 a.2 h1) (key b.1 b.2 h2) (key c.1 c.2 h3)

/-- Continuity (axiom A11) in the Klein–Beltrami disk, from continuity in the plane and the
convexity of the disk. -/
private lemma klein_continuity (X Y : Set KleinPoint)
    (h : ∃ a : KleinPoint, ∀ x ∈ X, ∀ y ∈ Y, Wbtw ℝ a.1 x.1 y.1) :
    ∃ b : KleinPoint, ∀ x ∈ X, ∀ y ∈ Y, Wbtw ℝ x.1 b.1 y.1 := by
  obtain ⟨a, ha⟩ := h
  by_cases hXY : X.Nonempty ∧ Y.Nonempty
  · obtain ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩ := hXY
    obtain ⟨b, hb⟩ := continuity_plane (Subtype.val '' X) (Subtype.val '' Y)
      ⟨a.1, by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; exact ha x hx y hy⟩
    exact ⟨⟨b, mem_disk_of_wbtw x₀.2 y₀.2 (hb _ ⟨x₀, hx₀, rfl⟩ _ ⟨y₀, hy₀, rfl⟩)⟩,
      fun x hx y hy => hb _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩⟩
  · exact ⟨a, fun x hx y hy => absurd ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ hXY⟩

/-- The Klein–Beltrami disk model of the hyperbolic plane: the open unit disk, with betweenness
`Wbtw ℝ` and congruence of segments given by equality of `coshSq`. -/
@[instance_reducible]
private noncomputable def kleinDisk : TarskiAbsolute KleinPoint where
  B a b c := Wbtw ℝ a.1 b.1 c.1
  C a b c d := coshSq a.1 b.1 = coshSq c.1 d.1
  congr_refl _ _ := coshSq_comm _ _
  congr_trans _ _ _ _ _ _ h1 h2 := h1.symm.trans h2
  congr_id a b c h := Subtype.ext (eq_of_coshSq_eq_one a.2 b.2 (h.trans (coshSq_self c.2)))
  segment_construction a b c d := klein_segment_construction a b c d
  five_segment a b c d a' b' c' d' hab h1 h2 h3 h4 h5 h6 :=
    klein_five_segment a b c d a' b' c' d' hab h1 h2 h3 h4 h5 h6
  betw_id _ _ h := Subtype.ext ((wbtw_self_iff ℝ).1 h).symm
  inner_pasch _ b _ p _ h1 h2 := by
    obtain ⟨x, hx1, hx2⟩ := inner_pasch_plane h1 h2
    exact ⟨⟨x, mem_disk_of_wbtw p.2 b.2 hx1⟩, hx1, hx2⟩
  lower_dim := ⟨⟨(0, 0), by norm_num⟩, ⟨(1 / 2, 0), by norm_num⟩, ⟨(0, 1 / 2), by norm_num⟩,
    not_wbtw_axes (by norm_num)⟩
  upper_dim a b c p q hpq h1 h2 h3 := klein_upper_dim a b c p q hpq h1 h2 h3
  continuity X Y h := klein_continuity X Y h

/-- The Euclidean axiom fails in the Klein–Beltrami disk. -/
private lemma not_euclidean_kleinDisk : ¬ Euclidean KleinPoint kleinDisk := by
  intro h
  obtain ⟨x, y, hx, hy, hxy⟩ := h ⟨(0, 0), by norm_num⟩ ⟨(1 / 2, 0), by norm_num⟩
    ⟨(0, 1 / 2), by norm_num⟩ ⟨(1 / 4, 1 / 4), by norm_num⟩ ⟨(3 / 5, 3 / 5), by norm_num⟩
    (wbtw_iff_coord.2 ⟨5 / 12, by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (wbtw_iff_coord.2 ⟨1 / 2, by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (fun h => by simp [Prod.ext_iff] at h)
  obtain ⟨s₁, hs₁0, hs₁1, e1, e2⟩ := wbtw_iff_coord.1 hx
  obtain ⟨s₂, hs₂0, hs₂1, f1, f2⟩ := wbtw_iff_coord.1 hy
  obtain ⟨u, hu0, hu1, g1, g2⟩ := wbtw_iff_coord.1 hxy
  have hxD := x.2
  have hyD := y.2
  simp only [sub_zero, zero_add] at e1 e2 f1 f2 g1 g2
  have hs₁ : s₁ ≠ 0 := by rintro rfl; norm_num at e1
  have hs₂ : s₂ ≠ 0 := by rintro rfl; norm_num at f2
  have hx2 : x.1.2 = 0 := (mul_eq_zero.1 e2.symm).resolve_left hs₁
  have hy1 : y.1.1 = 0 := (mul_eq_zero.1 f1.symm).resolve_left hs₂
  rw [hx2] at hxD g2
  rw [hy1] at hyD g1
  have hx1 : x.1.1 < 1 := by nlinarith
  have hy2 : y.1.2 < 1 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 hx1.le),
    mul_nonneg hu0 (sub_nonneg.2 hy2.le)]

/- **Independence of the parallel postulate** (Freek #12). The Euclidean
axiom `A10` is logically independent of Tarski's absolute axioms `A1`–`A9`
and `A11`: there is a model of the absolute axioms in which the parallel
postulate holds (the real coordinate plane) and one in which it fails (the
Klein–Beltrami disk, or any other hyperbolic-plane model). -/
set_option linter.dupNamespace false in
/-- **Independence of the parallel postulate.** Tarski's Euclidean axiom A10 is independent of
Tarski's axioms of absolute plane geometry: there is a model of absolute plane geometry in which
the Euclidean axiom holds, and there is a model of absolute plane geometry in which it fails.

Source: Independence of Euclid's parallel postulate; the hyperbolic-plane models are due to E.
Beltrami (1868) and F. Klein (1871). Tarski's axiomatization: W. Schwabhäuser, W. Szmielew, A.
Tarski, Metamathematische Methoden in der Geometrie, Springer (1983). Formalized in HOL Light by
John Harrison and in Isabelle by Tim Makarios (T.J.M. Makarios, A Mechanical Verification of the
Independence of Tarski's Euclidean Axiom, MSc thesis, Victoria University of Wellington, 2012;
Isabelle/AFP entry Tarskis_Geometry). Via leanprover/lean-eval@38361be, problem
`parallel_postulate_independent`. -/
theorem parallel_postulate_independent :
    (∃ (M : Type) (T : TarskiAbsolute M), Euclidean M T) ∧
    (∃ (M : Type) (T : TarskiAbsolute M), ¬ Euclidean M T) :=
  ⟨⟨ℝ × ℝ, euclideanPlane, euclidean_euclideanPlane⟩,
    ⟨KleinPoint, kleinDisk, not_euclidean_kleinDisk⟩⟩

end Geometry

end MathlibExt.Geometry.ParallelPostulateWanted
